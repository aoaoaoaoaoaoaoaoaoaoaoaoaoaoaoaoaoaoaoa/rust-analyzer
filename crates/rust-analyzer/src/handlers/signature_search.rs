//! The private signature protocol projects one owned analysis result.

use std::collections::BTreeMap;

use ide::{
    SignatureAnchor, SignatureCandidateSource, SignatureInputPredicate, SignaturePatternInput,
    SignatureSearchScope,
};
use lsp_types::Uri;
use syntax::{TextRange, TextSize};

use super::imports::{WitnessUse, configuration_witness, ready, stamp_digest, text_digest};

#[derive(Default)]
struct SourceRevisions {
    entries: BTreeMap<String, String>,
    bytes: usize,
}

fn record_source(
    snap: &GlobalStateSnapshot,
    file: ide::FileId,
    revisions: &mut SourceRevisions,
) -> anyhow::Result<String> {
    let uri = snap.file_id_to_url(file).to_string();
    if let Some(hash) = revisions.entries.get(&uri) {
        return Ok(hash.clone());
    }
    let text = snap.analysis.file_text(file)?;
    revisions.bytes = revisions
        .bytes
        .checked_add(text.len())
        .ok_or_else(|| anyhow::anyhow!("source revision byte overflow"))?;
    anyhow::ensure!(
        revisions.bytes <= 64 * 1024 * 1024,
        "selected source revision bytes exceed64MiB; narrow scope/max_candidates"
    );
    let hash = text_digest(&text);
    revisions.entries.insert(uri, hash.clone());
    Ok(hash)
}
use crate::{
    global_state::GlobalStateSnapshot,
    lsp::{signature as wire, to_proto},
};

pub(crate) fn handle_sem_signature_search(
    snap: GlobalStateSnapshot,
    query: wire::SignatureQuery,
) -> anyhow::Result<wire::SignatureBatch> {
    ready(&snap)?;
    configuration_witness(&snap, WitnessUse::Assessment)?;
    let input_stamp = snap.analysis.input_stamp()?;
    let stamp = stamp_digest(&snap, input_stamp);
    let mut revisions = SourceRevisions::default();
    fn anchor(
        snap: &GlobalStateSnapshot,
        anchor: wire::SourceAnchor,
        revisions: &mut SourceRevisions,
        stamp: &str,
    ) -> anyhow::Result<SignatureAnchor> {
        anyhow::ensure!(
            anchor.sha256.len() == 64
                && anchor.sha256.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
            "anchor sha256 must be lowercase SHA256 hex"
        );
        let uri = anchor.uri.parse::<Uri>()?;
        let file_id = snap
            .url_to_file_id(&uri)?
            .ok_or_else(|| anyhow::anyhow!("anchor URI is absent from provider VFS"))?;
        anyhow::ensure!(
            record_source(snap, file_id, revisions)? == anchor.sha256,
            "anchor text differs from expected sha256"
        );
        let text = snap.analysis.file_text(file_id)?;
        let range = anchor
            .range
            .map(|range| {
                let (start, end) = (range.start as usize, range.end as usize);
                anyhow::ensure!(
                    start <= end
                        && end <= text.len()
                        && text.is_char_boundary(start)
                        && text.is_char_boundary(end),
                    "anchor range is not a valid UTF-8 byte range"
                );
                Ok(TextRange::new(TextSize::from(range.start), TextSize::from(range.end)))
            })
            .transpose()?;
        let context_id = anchor
            .context_id
            .map(|id| {
                id.strip_prefix(&format!("{stamp}:")).map(str::to_owned).ok_or_else(|| {
                    anyhow::anyhow!("context_id belongs to a different provider snapshot")
                })
            })
            .transpose()?;
        Ok(SignatureAnchor { file_id, range, context_id })
    }
    fn pattern(
        snap: &GlobalStateSnapshot,
        pattern: wire::TypePattern,
        revisions: &mut SourceRevisions,
        stamp: &str,
    ) -> anyhow::Result<SignaturePatternInput> {
        Ok(match pattern {
            wire::TypePattern::Type(text) => SignaturePatternInput::Type(text),
            wire::TypePattern::Implements { implements } => {
                SignaturePatternInput::Implements(implements)
            }
            wire::TypePattern::Of { of } => {
                anyhow::ensure!(
                    of.range.is_some(),
                    "type-of anchor requires a selected point or range"
                );
                SignaturePatternInput::Of(anchor(snap, of, revisions, stamp)?)
            }
        })
    }
    let context = anchor(&snap, query.context, &mut revisions, &stamp)?;
    let context_sha256 = record_source(&snap, context.file_id, &mut revisions)?;
    let inputs = query
        .inputs
        .map(|inputs| {
            let mut convert = |patterns: Vec<wire::TypePattern>| {
                patterns
                    .into_iter()
                    .map(|p| pattern(&snap, p, &mut revisions, &stamp))
                    .collect::<anyhow::Result<Vec<_>>>()
            };
            match inputs {
                wire::InputPredicate::Any(patterns) => {
                    convert(patterns).map(SignatureInputPredicate::Any)
                }
                wire::InputPredicate::All(patterns) => {
                    convert(patterns).map(SignatureInputPredicate::All)
                }
                wire::InputPredicate::Exact(patterns) => {
                    convert(patterns).map(SignatureInputPredicate::Exact)
                }
            }
        })
        .transpose()?;
    let output = query.output.map(|p| pattern(&snap, p, &mut revisions, &stamp)).transpose()?;
    let scope = match query.scope {
        wire::SearchScope::Workspace => SignatureSearchScope::Workspace,
        wire::SearchScope::Regions { regions } => {
            anyhow::ensure!(
                !regions.is_empty() && regions.len() <= 4096,
                "regions must contain between1 and4096 entries"
            );
            let mut resolved = Vec::new();
            for region in regions {
                let uri = region.uri.parse::<Uri>()?;
                let file = snap
                    .url_to_file_id(&uri)?
                    .ok_or_else(|| anyhow::anyhow!("scope URI absent from provider VFS"))?;
                anyhow::ensure!(
                    record_source(&snap, file, &mut revisions)? == region.sha256,
                    "scope source differs from expected sha256"
                );
                let range = region
                    .range
                    .map(|range| {
                        let text = snap.analysis.file_text(file)?;
                        anyhow::ensure!(
                            range.start <= range.end
                                && range.end as usize <= text.len()
                                && text.is_char_boundary(range.start as usize)
                                && text.is_char_boundary(range.end as usize),
                            "scope range is invalid"
                        );
                        Ok::<_, anyhow::Error>(TextRange::new(range.start.into(), range.end.into()))
                    })
                    .transpose()?;
                resolved.push((file, range));
            }
            SignatureSearchScope::Regions(resolved)
        }
    };
    let engine = ide::SignatureQuery {
        context,
        inputs,
        output,
        scope,
        dependencies: match query.dependencies {
            wire::DependencyPolicy::Exclude => ide::SignatureDependencyPolicy::Exclude,
            wire::DependencyPolicy::Include => ide::SignatureDependencyPolicy::Include,
            wire::DependencyPolicy::Only => ide::SignatureDependencyPolicy::Only,
        },
        references: match query.references {
            wire::ReferencePolicy::Outer => hir::ReferencePolicy::Outer,
            wire::ReferencePolicy::Exact => hir::ReferencePolicy::Exact,
        },
        deref: query.deref,
        include_receiver: query.receiver == wire::ReceiverPolicy::Include,
        awaited: query.result == wire::ResultPolicy::Awaited,
        max_candidates: query.max_candidates,
    };
    let batch = snap.analysis.sem_signature_search(engine)?.map_err(|error| match error {
        ide::SignatureError::Query(message) => anyhow::anyhow!(message),
        ide::SignatureError::AmbiguousContext { choices } => anyhow::anyhow!(
            "ambiguous module context; select context_id from: {}",
            choices
                .into_iter()
                .map(|choice| format!(
                    "{}::{} => {}:{}",
                    choice.crate_name, choice.module, stamp, choice.id
                ))
                .collect::<Vec<_>>()
                .join("; ")
        ),
    })?;
    fn slot(slot: ide::SignatureInputSlot) -> wire::InputSlot {
        match slot {
            ide::SignatureInputSlot::Receiver => wire::InputSlot::Receiver,
            ide::SignatureInputSlot::Parameter { index } => wire::InputSlot::Parameter { index },
        }
    }
    fn ty(ty: ide::SignatureTypeDescription) -> wire::TypeDescription {
        wire::TypeDescription {
            display: ty.display,
            form: match ty.form {
                hir::TypeShape::Concrete => wire::TypeForm::Concrete,
                hir::TypeShape::Generic => wire::TypeForm::Generic,
                hir::TypeShape::Opaque => wire::TypeForm::Opaque,
                hir::TypeShape::Dynamic => wire::TypeForm::Dynamic,
                hir::TypeShape::Mixed => wire::TypeForm::Mixed,
                hir::TypeShape::Unknown => wire::TypeForm::Unknown,
            },
        }
    }
    let candidates = batch
        .candidates
        .into_iter()
        .map(|candidate| {
            let source = match candidate.source {
                SignatureCandidateSource::Physical { range, name_offset } => {
                    let uri = snap.file_id_to_url(range.file_id);
                    let sha256 = record_source(&snap, range.file_id, &mut revisions)?;
                    let index = snap.analysis.file_line_index(range.file_id)?;
                    let point = index
                        .to_wide(
                            ide_db::line_index::WideEncoding::Utf16,
                            index.line_col(name_offset),
                        )
                        .ok_or_else(|| anyhow::anyhow!("invalid UTF16 source point"))?;
                    wire::CandidateSource::Physical {
                        source: wire::SignatureSource {
                            uri: uri.to_string(),
                            range: wire::ByteRange {
                                start: range.range.start().into(),
                                end: range.range.end().into(),
                            },
                            name_offset: name_offset.into(),
                            line: point.line + 1,
                            column: point.col + 1,
                            sha256,
                        },
                    }
                }
                SignatureCandidateSource::Nonphysical { file_id, reason, .. } => {
                    wire::CandidateSource::Nonphysical {
                        uri: file_id.map(|file| snap.file_id_to_url(file).to_string()),
                        reason,
                    }
                }
            };
            let matches = candidate
                .matches
                .into_iter()
                .map(|evidence| {
                    let mut steps = Vec::new();
                    if evidence.evidence.outer_references > 0 {
                        steps.push(wire::MatchStep::OuterReferences {
                            removed: evidence.evidence.outer_references,
                        });
                    }
                    if evidence.evidence.deref_steps > 0 {
                        steps.push(wire::MatchStep::Deref { steps: evidence.evidence.deref_steps });
                    }
                    if evidence.evidence.wildcard {
                        steps.push(wire::MatchStep::Wildcard);
                    }
                    if evidence.evidence.trait_proof {
                        steps.push(wire::MatchStep::TraitProof {
                            bounds: evidence.bounds.unwrap_or_default(),
                        });
                    }
                    if let Some(resolved) = evidence.resolved {
                        steps.push(wire::MatchStep::ResolvedType {
                            written: resolved.written,
                            resolved: ty(resolved.ty),
                        });
                    }
                    if steps.is_empty() {
                        steps.push(wire::MatchStep::Exact);
                    }
                    wire::MatchEvidence {
                        role: match evidence.role {
                            ide::SignatureEvidenceRole::Input { pattern, slot: input } => {
                                wire::EvidenceRole::Input { pattern, slot: slot(input) }
                            }
                            ide::SignatureEvidenceRole::Output => wire::EvidenceRole::Output,
                        },
                        actual_type: ty(evidence.actual_type),
                        matched_type: ty(evidence.matched_type),
                        steps,
                    }
                })
                .collect();
            Ok::<_, anyhow::Error>(wire::SignatureCandidate {
                id: candidate.id,
                qualified_name: candidate.qualified_name,
                signature: candidate.signature,
                crate_name: candidate.crate_name,
                kind: match candidate.kind {
                    ide::SignatureCallableKind::Function => wire::CallableKind::Function,
                    ide::SignatureCallableKind::AssociatedFunction => {
                        wire::CallableKind::AssociatedFunction
                    }
                    ide::SignatureCallableKind::Method => wire::CallableKind::Method,
                    ide::SignatureCallableKind::TraitMethod => wire::CallableKind::TraitMethod,
                    ide::SignatureCallableKind::TupleStructConstructor => {
                        wire::CallableKind::TupleStructConstructor
                    }
                    ide::SignatureCallableKind::EnumVariantConstructor => {
                        wire::CallableKind::EnumVariantConstructor
                    }
                },
                provenance: wire::SignatureProvenance {
                    crate_instance: candidate.crate_instance,
                    origin: if candidate.workspace {
                        wire::CrateOrigin::Workspace
                    } else {
                        wire::CrateOrigin::Dependency
                    },
                },
                parameters: candidate
                    .parameters
                    .into_iter()
                    .map(|parameter| wire::Parameter {
                        slot: slot(parameter.slot),
                        ty: ty(parameter.ty),
                    })
                    .collect(),
                output: ty(candidate.output),
                matches,
                source,
            })
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    let config_revisions = snap
        .configuration_witness
        .iter()
        .flat_map(|witness| witness.file_revisions())
        .map(|(path, hash)| wire::SourceRevision {
            uri: to_proto::url_from_abs_path(path).to_string(),
            sha256: hash.iter().map(|byte| format!("{byte:02x}")).collect(),
        })
        .collect();
    let result = wire::SignatureBatch {
        context_sha256,
        stamp,
        source_revisions: revisions
            .entries
            .into_iter()
            .map(|(uri, sha256)| wire::SourceRevision { uri, sha256 })
            .collect(),
        config_revisions,
        candidates,
        coverage: wire::SignatureCoverage {
            examined: batch.coverage.examined,
            matched: batch.coverage.matched,
            unknown: batch.coverage.unknown,
            unknown_reasons: batch
                .coverage
                .unknown_reasons
                .into_iter()
                .map(|(reason, count)| wire::UnknownReason { reason, count })
                .collect(),
            unsearched: batch.coverage.unsearched,
            warnings: batch.coverage.warnings,
            complete: batch.coverage.complete,
        },
    };
    anyhow::ensure!(
        serde_json::to_vec(&result)?.len() <= 16 * 1024 * 1024,
        "signature result exceeds16MiB; narrow scope/max_candidates"
    );
    configuration_witness(&snap, WitnessUse::Assessment)?;
    anyhow::ensure!(
        snap.analysis.input_stamp()? == input_stamp,
        "analysis inputs changed during signature search"
    );
    Ok(result)
}
