//! Projects declaration similarity with source and configuration guards.

use super::{
    imports::{WitnessUse, configuration_witness, ready, stamp_digest},
    semantic_search::{self, SourceRevisions},
};
use crate::{
    global_state::GlobalStateSnapshot,
    lsp::{signature, similar as wire},
};

fn kind(kind: ide::SimilarKind) -> wire::SimilarKind {
    match kind {
        ide::SimilarKind::Struct => wire::SimilarKind::Struct,
        ide::SimilarKind::Enum => wire::SimilarKind::Enum,
        ide::SimilarKind::Union => wire::SimilarKind::Union,
        ide::SimilarKind::Trait => wire::SimilarKind::Trait,
        ide::SimilarKind::TypeAlias => wire::SimilarKind::TypeAlias,
    }
}

fn member(member: ide::SimilarMember) -> wire::SimilarMember {
    wire::SimilarMember {
        name: member.name,
        signature: member.signature,
        resolution: match member.resolution {
            ide::MemberResolution::Resolved => wire::MemberResolution::Resolved,
            ide::MemberResolution::Unresolved { reason } => {
                wire::MemberResolution::Unresolved { reason }
            }
        },
    }
}

pub(crate) fn handle_sem_similar_types(
    snap: GlobalStateSnapshot,
    query: wire::SimilarQuery,
) -> anyhow::Result<wire::SimilarBatch> {
    ready(&snap)?;
    configuration_witness(&snap, WitnessUse::Assessment)?;
    let input_stamp = snap.analysis.input_stamp()?;
    let stamp = stamp_digest(&snap, input_stamp);
    let mut revisions = SourceRevisions::default();
    let context = query
        .context
        .map(|anchor| semantic_search::anchor(&snap, anchor, &mut revisions, &stamp))
        .transpose()?;
    let query_input = match query.query {
        wire::SimilarInput::Draft { source } => ide::SimilarInput::Draft(source),
        wire::SimilarInput::Target { target } => ide::SimilarInput::Target(
            semantic_search::anchor(&snap, target, &mut revisions, &stamp)?,
        ),
    };
    let scope = semantic_search::scope(&snap, query.scope, &mut revisions)?;
    let engine = ide::SimilarQuery {
        context,
        query: query_input,
        scope,
        dependencies: match query.dependencies {
            signature::DependencyPolicy::Exclude => ide::SignatureDependencyPolicy::Exclude,
            signature::DependencyPolicy::Include => ide::SignatureDependencyPolicy::Include,
            signature::DependencyPolicy::Only => ide::SignatureDependencyPolicy::Only,
        },
        kinds: query.kinds.map(|kinds| {
            kinds
                .into_iter()
                .map(|kind| match kind {
                    wire::SimilarKind::Struct => ide::SimilarKind::Struct,
                    wire::SimilarKind::Enum => ide::SimilarKind::Enum,
                    wire::SimilarKind::Union => ide::SimilarKind::Union,
                    wire::SimilarKind::Trait => ide::SimilarKind::Trait,
                    wire::SimilarKind::TypeAlias => ide::SimilarKind::TypeAlias,
                })
                .collect()
        }),
        min_score: query.min_score,
        max_candidates: query.max_candidates,
    };
    let batch=snap.analysis.sem_similar_types(engine)?.map_err(|error|match error {
        ide::SignatureError::Query(message)=>anyhow::anyhow!(message),
        ide::SignatureError::AmbiguousContext {choices}=>anyhow::anyhow!("ambiguous resolution context; set at to a crate/module file and context_id if necessary: {}",choices.into_iter().map(|choice|format!("{}::{} root_uri={} context_id={}:{}",choice.crate_name,choice.module,snap.file_id_to_url(choice.file_id),stamp,choice.id)).collect::<Vec<_>>().join("; ")),
    })?;
    let context_uri = snap.file_id_to_url(batch.context_file).to_string();
    let context_sha256 = semantic_search::record_source(&snap, batch.context_file, &mut revisions)?;
    let candidates = batch
        .candidates
        .into_iter()
        .map(|candidate| {
            Ok(wire::SimilarCandidate {
                id: candidate.id,
                name: candidate.name,
                qualified_name: candidate.qualified_name,
                crate_name: candidate.crate_name,
                kind: kind(candidate.kind),
                visibility: candidate.visibility,
                provenance: signature::SignatureProvenance {
                    crate_instance: candidate.crate_instance,
                    origin: if candidate.workspace {
                        signature::CrateOrigin::Workspace
                    } else {
                        signature::CrateOrigin::Dependency
                    },
                },
                score: candidate.score,
                relation: match candidate.relation {
                    ide::SimilarRelation::Equal => wire::SimilarRelation::Equal,
                    ide::SimilarRelation::QueryWithinCandidate => {
                        wire::SimilarRelation::QueryWithinCandidate
                    }
                    ide::SimilarRelation::CandidateWithinQuery => {
                        wire::SimilarRelation::CandidateWithinQuery
                    }
                    ide::SimilarRelation::Overlap => wire::SimilarRelation::Overlap,
                },
                name_overlap: candidate.name_overlap,
                type_token_overlap: candidate.type_token_overlap,
                members: candidate.members.into_iter().map(member).collect(),
                shared: candidate
                    .shared
                    .into_iter()
                    .map(|shared| wire::SimilarShared {
                        query: shared.query,
                        candidate: shared.candidate,
                        evidence: match shared.evidence {
                            ide::SimilarEvidence::Semantic => wire::SimilarEvidence::Semantic,
                            ide::SimilarEvidence::UnresolvedText => {
                                wire::SimilarEvidence::UnresolvedText
                            }
                        },
                    })
                    .collect(),
                query_only: candidate.query_only,
                candidate_only: candidate.candidate_only,
                query_unresolved: candidate.query_unresolved,
                candidate_unresolved: candidate.candidate_unresolved,
                text_matches: candidate.text_matches,
                source: semantic_search::source(&snap, candidate.source, &mut revisions)?,
            })
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    let result = wire::SimilarBatch {
        context_uri,
        context_sha256,
        stamp,
        source_revisions: revisions
            .entries
            .into_iter()
            .map(|(uri, sha256)| signature::SourceRevision { uri, sha256 })
            .collect(),
        query: wire::SimilarDeclaration {
            kind: kind(batch.query.kind),
            members: batch.query.members.into_iter().map(member).collect(),
        },
        candidates,
        coverage: wire::SimilarCoverage {
            examined: batch.coverage.examined,
            matched: batch.coverage.matched,
            query_unresolved: batch.coverage.query_unresolved,
            candidate_unresolved: batch.coverage.candidate_unresolved,
            text_matches: batch.coverage.text_matches,
            unknown: batch.coverage.unknown,
            unknown_reasons: batch
                .coverage
                .unknown_reasons
                .into_iter()
                .map(|(reason, count)| signature::UnknownReason { reason, count })
                .collect(),
            unsearched: batch.coverage.unsearched,
            warnings: batch.coverage.warnings,
            complete: batch.coverage.complete,
        },
    };
    anyhow::ensure!(
        serde_json::to_vec(&result)?.len() <= 16 * 1024 * 1024,
        "similar result exceeds16MiB; narrow scope/max_candidates"
    );
    configuration_witness(&snap, WitnessUse::Assessment)?;
    anyhow::ensure!(
        snap.analysis.input_stamp()? == input_stamp,
        "analysis inputs changed during similar search"
    );
    Ok(result)
}
