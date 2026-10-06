//! Version-one wire types for private declaration similarity.

use serde::{Deserialize, Serialize};

use super::signature::{
    CandidateSource, DependencyPolicy, SearchScope, SignatureProvenance, SourceAnchor,
    SourceRevision, UnknownReason,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SimilarKind {
    Struct,
    Enum,
    Union,
    Trait,
    TypeAlias,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SimilarInput {
    Draft { source: String },
    Target { target: SourceAnchor },
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SimilarQuery {
    pub context: Option<SourceAnchor>,
    pub query: SimilarInput,
    pub scope: SearchScope,
    pub dependencies: DependencyPolicy,
    pub kinds: Option<Vec<SimilarKind>>,
    pub min_score: f64,
    pub max_candidates: u32,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MemberResolution {
    Resolved,
    Unresolved { reason: String },
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SimilarMember {
    pub name: String,
    pub signature: String,
    pub resolution: MemberResolution,
}

#[derive(Debug, Clone, Copy, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SimilarRelation {
    Equal,
    QueryWithinCandidate,
    CandidateWithinQuery,
    Overlap,
}

#[derive(Debug, Clone, Copy, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SimilarEvidence {
    Semantic,
    UnresolvedText,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SimilarShared {
    pub query: u32,
    pub candidate: u32,
    pub evidence: SimilarEvidence,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SimilarDeclaration {
    pub kind: SimilarKind,
    pub members: Vec<SimilarMember>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SimilarCandidate {
    pub id: String,
    pub name: String,
    pub qualified_name: String,
    #[serde(rename = "crate")]
    pub crate_name: String,
    pub kind: SimilarKind,
    pub visibility: String,
    pub provenance: SignatureProvenance,
    pub score: f64,
    pub relation: SimilarRelation,
    pub name_overlap: f64,
    pub type_token_overlap: f64,
    pub members: Vec<SimilarMember>,
    pub shared: Vec<SimilarShared>,
    pub query_only: Vec<u32>,
    pub candidate_only: Vec<u32>,
    pub query_unresolved: u32,
    pub candidate_unresolved: u32,
    pub text_matches: u32,
    pub source: CandidateSource,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SimilarCoverage {
    pub examined: u32,
    pub matched: u32,
    pub query_unresolved: u32,
    pub candidate_unresolved: u32,
    pub text_matches: u32,
    pub unknown: u32,
    pub unknown_reasons: Vec<UnknownReason>,
    pub unsearched: Vec<String>,
    pub warnings: Vec<String>,
    pub complete: bool,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SimilarBatch {
    pub context_uri: String,
    pub context_sha256: String,
    pub stamp: String,
    pub source_revisions: Vec<SourceRevision>,
    pub query: SimilarDeclaration,
    pub candidates: Vec<SimilarCandidate>,
    pub coverage: SimilarCoverage,
}
