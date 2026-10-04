use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
pub struct ByteRange {
    pub start: u32,
    pub end: u32,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SourceAnchor {
    pub uri: String,
    pub range: Option<ByteRange>,
    pub sha256: String,
    pub context_id: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(untagged)]
pub enum TypePattern {
    Type(String),
    Of { of: SourceAnchor },
    Implements { implements: String },
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum InputPredicate {
    Any(Vec<TypePattern>),
    All(Vec<TypePattern>),
    Exact(Vec<TypePattern>),
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ReferencePolicy {
    #[default]
    Outer,
    Exact,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ReceiverPolicy {
    #[default]
    Include,
    Exclude,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ResultPolicy {
    #[default]
    Direct,
    Awaited,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DependencyPolicy {
    #[default]
    Exclude,
    Include,
    Only,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SourceRegion {
    pub uri: String,
    pub range: Option<ByteRange>,
    pub sha256: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SearchScope {
    Workspace,
    Regions { regions: Vec<SourceRegion> },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignatureQuery {
    pub context: SourceAnchor,
    pub inputs: Option<InputPredicate>,
    pub output: Option<TypePattern>,
    pub scope: SearchScope,
    pub dependencies: DependencyPolicy,
    pub references: ReferencePolicy,
    pub deref: bool,
    pub receiver: ReceiverPolicy,
    pub result: ResultPolicy,
    pub max_candidates: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceRevision {
    pub uri: String,
    pub sha256: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignatureSource {
    pub uri: String,
    pub range: ByteRange,
    pub name_offset: u32,
    pub line: u32,
    pub column: u32,
    pub sha256: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Parameter {
    pub slot: InputSlot,
    #[serde(rename = "type")]
    pub ty: TypeDescription,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchEvidence {
    pub role: EvidenceRole,
    pub actual_type: TypeDescription,
    pub matched_type: TypeDescription,
    pub steps: Vec<MatchStep>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EvidenceRole {
    Input { pattern: u32, slot: InputSlot },
    Output,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum InputSlot {
    Receiver,
    Parameter { index: u32 },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MatchStep {
    Exact,
    OuterReferences { removed: u32 },
    Deref { steps: u32 },
    Wildcard,
    TraitProof { bounds: String },
    ResolvedType { written: Option<String>, resolved: TypeDescription },
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TypeForm {
    Concrete,
    Generic,
    Opaque,
    Dynamic,
    Mixed,
    Unknown,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDescription {
    pub display: String,
    pub form: TypeForm,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CallableKind {
    Function,
    AssociatedFunction,
    Method,
    TraitMethod,
    TupleStructConstructor,
    EnumVariantConstructor,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CandidateSource {
    Physical { source: SignatureSource },
    Nonphysical { uri: Option<String>, reason: String },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignatureCandidate {
    pub id: String,
    pub qualified_name: String,
    pub signature: String,
    #[serde(rename = "crate")]
    pub crate_name: String,
    pub kind: CallableKind,
    pub provenance: SignatureProvenance,
    pub parameters: Vec<Parameter>,
    pub output: TypeDescription,
    pub matches: Vec<MatchEvidence>,
    pub source: CandidateSource,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignatureProvenance {
    pub crate_instance: String,
    pub origin: CrateOrigin,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CrateOrigin {
    Workspace,
    Dependency,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnknownReason {
    pub reason: String,
    pub count: u32,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SignatureCoverage {
    pub examined: u32,
    pub matched: u32,
    pub unknown: u32,
    pub unknown_reasons: Vec<UnknownReason>,
    pub unsearched: Vec<String>,
    pub warnings: Vec<String>,
    pub complete: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignatureBatch {
    pub context_sha256: String,
    pub stamp: String,
    pub source_revisions: Vec<SourceRevision>,
    pub config_revisions: Vec<SourceRevision>,
    pub candidates: Vec<SignatureCandidate>,
    pub coverage: SignatureCoverage,
}
