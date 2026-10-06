//! The private signature protocol projects one owned analysis result.

use ide::{SignatureInputPredicate, SignaturePatternInput};

use super::semantic_search::{SourceRevisions, anchor, record_source, scope, source};

use super::imports::{WitnessUse, configuration_witness, ready, stamp_digest};

use crate::{global_state::GlobalStateSnapshot, lsp::signature as wire};

pub(crate) fn handle_sem_signature_search(
    snap: GlobalStateSnapshot,
    query: wire::SignatureQuery,
) -> anyhow::Result<wire::SignatureBatch> {
    ready(&snap)?;
    configuration_witness(&snap, WitnessUse::Assessment)?;
    let input_stamp = snap.analysis.input_stamp()?;
    let stamp = stamp_digest(&snap, input_stamp);
    let mut revisions = SourceRevisions::default();
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
    let scope = scope(&snap, query.scope, &mut revisions)?;
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
                    "{}::{} root_uri={} context_id={}:{}",
                    choice.crate_name,
                    choice.module,
                    snap.file_id_to_url(choice.file_id),
                    stamp,
                    choice.id
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
            let source = source(&snap, candidate.source, &mut revisions)?;
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
                name: candidate.name,
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
    let result = wire::SignatureBatch {
        context_sha256,
        stamp,
        source_revisions: revisions
            .entries
            .into_iter()
            .map(|(uri, sha256)| wire::SourceRevision { uri, sha256 })
            .collect(),
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
