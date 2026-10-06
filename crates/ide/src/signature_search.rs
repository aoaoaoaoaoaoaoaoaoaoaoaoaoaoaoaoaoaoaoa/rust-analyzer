//! Declaration discovery over one active semantic snapshot.

use std::collections::BTreeMap;

use hir::{
    Adt, AsAssocItem, AssocItem, AssocItemContainer, Crate, DefWithBody, Function, HasCrate,
    HirDisplay, Module, ModuleDef, ReferencePolicy, Semantics, SignaturePattern, StructKind, Type,
    TypeMatch, TypeMatchEvidence, TypeMatchUnknown, TypeShape,
};
use ide_db::{FileId, FileRange, FxHashSet, RootDatabase};
use syntax::{AstNode, TextRange, ast::HasGenericParams};

#[derive(Debug, Clone)]
pub struct SignatureAnchor {
    pub file_id: FileId,
    pub range: Option<TextRange>,
    pub context_id: Option<String>,
}
#[derive(Debug, Clone)]
pub enum PatternInput {
    Type(String),
    Of(SignatureAnchor),
    Implements(String),
}
#[derive(Debug, Clone)]
pub enum InputPredicate {
    Any(Vec<PatternInput>),
    All(Vec<PatternInput>),
    Exact(Vec<PatternInput>),
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DependencyPolicy {
    Exclude,
    Include,
    Only,
}
#[derive(Debug, Clone)]
pub enum SearchScope {
    Workspace,
    Regions(Vec<(FileId, Option<TextRange>)>),
}
#[derive(Debug, Clone)]
pub struct SignatureQuery {
    pub context: SignatureAnchor,
    pub inputs: Option<InputPredicate>,
    pub output: Option<PatternInput>,
    pub scope: SearchScope,
    pub dependencies: DependencyPolicy,
    pub references: ReferencePolicy,
    pub deref: bool,
    pub include_receiver: bool,
    pub awaited: bool,
    pub max_candidates: u32,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallableKind {
    Function,
    AssociatedFunction,
    Method,
    TraitMethod,
    TupleStructConstructor,
    EnumVariantConstructor,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InputSlot {
    Receiver,
    Parameter { index: u32 },
}
#[derive(Debug, Clone)]
pub struct TypeDescription {
    pub display: String,
    pub form: TypeShape,
}
#[derive(Debug, Clone)]
pub struct Parameter {
    pub slot: InputSlot,
    pub ty: TypeDescription,
}
#[derive(Debug, Clone)]
pub enum EvidenceRole {
    Input { pattern: u32, slot: InputSlot },
    Output,
}
#[derive(Debug, Clone)]
pub struct MatchEvidence {
    pub role: EvidenceRole,
    pub actual_type: TypeDescription,
    pub matched_type: TypeDescription,
    pub evidence: TypeMatchEvidence,
    pub bounds: Option<String>,
    pub resolved: Option<ResolvedType>,
}

#[derive(Debug, Clone)]
pub struct ResolvedType {
    pub written: Option<String>,
    pub ty: TypeDescription,
}
#[derive(Debug, Clone)]
pub enum CandidateSource {
    Physical { range: FileRange, name_offset: syntax::TextSize },
    Nonphysical { file_id: Option<FileId>, origin: Option<FileRange>, reason: String },
}
#[derive(Debug, Clone)]
pub struct SignatureCandidate {
    pub id: String,
    pub name: String,
    pub qualified_name: String,
    pub signature: String,
    pub crate_name: String,
    pub crate_instance: String,
    pub workspace: bool,
    pub kind: CallableKind,
    pub parameters: Vec<Parameter>,
    pub output: TypeDescription,
    pub matches: Vec<MatchEvidence>,
    pub source: CandidateSource,
}
#[derive(Debug, Clone, Default)]
pub struct SignatureCoverage {
    pub examined: u32,
    pub matched: u32,
    pub unknown: u32,
    pub unknown_reasons: BTreeMap<String, u32>,
    pub unsearched: Vec<String>,
    pub warnings: Vec<String>,
    pub exclusions: BTreeMap<String, u32>,
    pub incomplete_modules: Vec<(hir::ImportBindingUnknown, u32)>,
    pub complete: bool,
}
#[derive(Debug, Clone)]
pub struct SignatureBatch {
    pub candidates: Vec<SignatureCandidate>,
    pub coverage: SignatureCoverage,
}

#[derive(Debug, Clone)]
pub struct ContextChoice {
    pub file_id: FileId,
    pub id: String,
    pub crate_name: String,
    pub module: String,
}

#[derive(Debug, Clone)]
pub enum SignatureError {
    Query(String),
    AmbiguousContext { choices: Vec<ContextChoice> },
}
impl From<String> for SignatureError {
    fn from(message: String) -> Self {
        Self::Query(message)
    }
}
impl From<&str> for SignatureError {
    fn from(message: &str) -> Self {
        Self::Query(message.into())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Declaration {
    Function(Function),
    Struct(hir::Struct),
    Variant(hir::EnumVariant),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum EnumerationBand {
    Workspace,
    DirectDependency,
    Dependency,
    Builtin,
}

#[derive(Default)]
struct EnumerationQueue {
    modules: Vec<Module>,
    bodies: Vec<DefWithBody>,
}

fn enumeration_limit(
    mut batch: SignatureBatch,
    queues: &BTreeMap<EnumerationBand, EnumerationQueue>,
    reason: &str,
) -> SignatureBatch {
    batch.coverage.complete = false;
    batch.coverage.unsearched.push(reason.into());
    if queues.values().any(|queue| !queue.bodies.is_empty()) {
        batch
            .coverage
            .unsearched
            .push("body-local declaration traversal unfinished at enumeration budget".into());
    }
    finish(batch)
}

pub(crate) fn context<'db>(
    sema: &Semantics<'db, RootDatabase>,
    anchor: &SignatureAnchor,
) -> Result<Module, SignatureError> {
    let modules: Vec<_> = sema.file_to_module_defs(anchor.file_id).collect();
    if let Some(id) = &anchor.context_id {
        return modules
            .into_iter()
            .find(|module| format!("{module:?}") == *id)
            .ok_or_else(|| "selected context_id is unavailable in this snapshot".into());
    }
    match modules.as_slice() {
        [module] => Ok(*module),
        [] => Err("anchor file is not part of the active module graph".into()),
        _ => Err(SignatureError::AmbiguousContext {
            choices: modules.iter().map(|module| context_choice(sema.db, *module)).collect(),
        }),
    }
}

fn compile<'db>(
    sema: &Semantics<'db, RootDatabase>,
    context: &SignatureAnchor,
    module: Module,
    input: &PatternInput,
) -> Result<SignaturePattern<'db>, SignatureError> {
    match input {
        PatternInput::Of(anchor) => {
            let range = anchor.range.ok_or("type-of anchor requires a selected point or range")?;
            let module = self::context(sema, anchor)?;
            let file = sema.parse_guess_edition(anchor.file_id);
            let ty = sema
                .signature_anchor_type(module, file.syntax(), range)
                .ok_or("selected anchor has no supported unadjusted semantic type")?;
            if ty.contains_unknown() || ty.signature_shape(sema.db) == TypeShape::Unknown {
                return Err("selected type anchor contains unresolved semantic types".into());
            }
            Ok(SignaturePattern::of(ty))
        }
        PatternInput::Type(text) | PatternInput::Implements(text) => {
            let file = sema.parse_guess_edition(context.file_id);
            let offset = context.range.map(|range| range.start());
            sema.signature_scope_at(module, file.syntax(), offset)
                .signature_pattern(text, matches!(input, PatternInput::Implements(_)))
                .map_err(SignatureError::Query)
        }
    }
}

pub(crate) fn search(
    db: &RootDatabase,
    query: SignatureQuery,
) -> Result<SignatureBatch, SignatureError> {
    if query.inputs.is_none() && query.output.is_none() {
        return Err("at least one input/output predicate is required".into());
    }
    if query.max_candidates == 0 || query.max_candidates > 100_000 {
        return Err("max_candidates must be between 1 and 100000".into());
    }
    if !matches!(query.scope, SearchScope::Workspace)
        && query.dependencies != DependencyPolicy::Exclude
    {
        return Err("dependency inclusion requires workspace scope".into());
    }
    let sema = Semantics::new(db);
    let module = context(&sema, &query.context)?;
    let raw_inputs = match &query.inputs {
        Some(
            InputPredicate::Any(types) | InputPredicate::All(types) | InputPredicate::Exact(types),
        ) => types.as_slice(),
        None => &[],
    };
    if raw_inputs.len() > 64
        || (matches!(&query.inputs, Some(InputPredicate::Any(_) | InputPredicate::All(_)))
            && raw_inputs.is_empty())
    {
        return Err("input predicates require between 1 and64 patterns (exact permits zero)".into());
    }
    let inputs = raw_inputs
        .iter()
        .map(|input| compile(&sema, &query.context, module, input))
        .collect::<Result<Vec<_>, _>>()?;
    let output = query
        .output
        .as_ref()
        .map(|input| compile(&sema, &query.context, module, input))
        .transpose()?;
    let workspace: FxHashSet<_> =
        Crate::all(db).into_iter().filter(|krate| krate.is_workspace_member(db)).collect();
    let direct_dependencies: FxHashSet<_> = workspace
        .iter()
        .flat_map(|krate| krate.dependencies(db).into_iter().map(|dependency| dependency.krate))
        .collect();
    let crates = search_crates(db, query.dependencies);
    let mut queues: BTreeMap<EnumerationBand, EnumerationQueue> = BTreeMap::new();
    for krate in crates {
        let band = if workspace.contains(&krate) {
            EnumerationBand::Workspace
        } else if krate.is_builtin(db) {
            EnumerationBand::Builtin
        } else if direct_dependencies.contains(&krate) {
            EnumerationBand::DirectDependency
        } else {
            EnumerationBand::Dependency
        };
        queues.entry(band).or_default().modules.extend(krate.modules(db));
    }
    for queue in queues.values_mut() {
        queue.modules.sort_by_key(|module| format!("{module:?}"));
        queue.modules.reverse();
    }
    let mut seen_modules = FxHashSet::default();
    let mut seen_declarations = FxHashSet::default();
    let mut batch = SignatureBatch {
        candidates: Vec::new(),
        coverage: SignatureCoverage { complete: true, ..Default::default() },
    };
    while let Some((&band, _)) = queues.first_key_value() {
        let queue = queues.get_mut(&band).unwrap();
        let module = if let Some(module) = queue.modules.pop() {
            module
        } else if !queue.bodies.is_empty() {
            if batch.coverage.examined >= query.max_candidates {
                return Ok(enumeration_limit(
                    batch,
                    &queues,
                    "semantic candidate enumeration budget exhausted",
                ));
            }
            let body = queue.bodies.pop().unwrap();
            queue.modules = body.signature_block_modules(db);
            queue.modules.sort_by_key(|module| format!("{module:?}"));
            queue.modules.reverse();
            continue;
        } else {
            queues.pop_first();
            continue;
        };
        if !seen_modules.insert(module) {
            continue;
        }
        if seen_modules.len() > 100_000 {
            return Ok(enumeration_limit(batch, &queues, "module traversal budget exhausted"));
        }
        if let Err(reason) = module.import_scope_status(db) {
            batch.coverage.complete = false;
            if let Some((_, count)) = batch
                .coverage
                .incomplete_modules
                .iter_mut()
                .find(|(category, _)| *category == reason)
            {
                *count += 1;
            } else {
                batch.coverage.incomplete_modules.push((reason, 1));
            }
        }
        let mut declarations = Vec::new();
        let bodies = module_bodies(db, module);
        for definition in module.declarations(db) {
            match definition {
                ModuleDef::Function(function) => {
                    declarations.push(Declaration::Function(function));
                }
                ModuleDef::Trait(trait_) => {
                    for item in trait_.items(db) {
                        add_assoc(item, &mut declarations);
                    }
                }
                ModuleDef::Adt(Adt::Struct(strukt)) => {
                    if strukt.kind(db) == StructKind::Tuple {
                        declarations.push(Declaration::Struct(strukt));
                    } else {
                        if sema.source(strukt).is_some_and(|source| {
                            in_scope(
                                &query.scope,
                                sema.original_range(source.value.syntax()).into_file_id(db),
                            )
                        }) {
                            *batch.coverage.exclusions.entry("unit/record struct constructors (non-callable construction syntax)".into()).or_default()+=1;
                        }
                    }
                }
                ModuleDef::Adt(Adt::Enum(enum_)) => {
                    for variant in enum_.variants(db) {
                        if variant.kind(db) == StructKind::Tuple {
                            declarations.push(Declaration::Variant(variant));
                        } else {
                            if sema.source(variant).is_some_and(|source| {
                                in_scope(
                                    &query.scope,
                                    sema.original_range(source.value.syntax()).into_file_id(db),
                                )
                            }) {
                                *batch.coverage.exclusions.entry("unit/record enum constructors (non-callable construction syntax)".into()).or_default()+=1;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        for impl_ in hir::Impl::all_in_module(db, module) {
            for item in impl_.items(db) {
                add_assoc(item, &mut declarations);
            }
        }
        queues.get_mut(&band).unwrap().bodies.extend(bodies);
        declarations.sort_by_key(|declaration| format!("{declaration:?}"));
        for declaration in declarations {
            if !seen_declarations.insert(declaration) {
                continue;
            }
            if batch.coverage.examined >= query.max_candidates {
                return Ok(enumeration_limit(
                    batch,
                    &queues,
                    "semantic candidate enumeration budget exhausted",
                ));
            }
            let scoped_source = matches!(query.scope, SearchScope::Regions(_))
                .then(|| declaration_source(&sema, declaration));
            if let SearchScope::Regions(regions) = &query.scope {
                let location = match &scoped_source {
                    Some(CandidateSource::Physical { range, .. }) => Some(*range),
                    Some(CandidateSource::Nonphysical { origin, .. }) => *origin,
                    None => None,
                };
                if location.is_none() {
                    batch.coverage.complete = false;
                    batch.coverage.unsearched.push("nonphysical declaration has no provider source origin for requested narrow scope".into());
                    continue;
                }
                if !regions.iter().any(|(file, range)| {
                    location.is_some_and(|location| {
                        location.file_id == *file
                            && range.is_none_or(|range| range.contains_range(location.range))
                    })
                }) {
                    continue;
                }
            }
            batch.coverage.examined += 1;
            let ty = match declaration {
                Declaration::Function(f) => f.ty(db),
                Declaration::Struct(s) => s.constructor_ty(db),
                Declaration::Variant(v) => v.constructor_ty(db),
            };
            let callable = ty.as_callable(db);
            let Some(callable) = callable else {
                unknown(&mut batch.coverage, TypeMatchUnknown::UnsupportedStructure);
                continue;
            };
            let has_receiver =
                matches!(declaration,Declaration::Function(f) if f.self_param(db).is_some());
            let params: Vec<_> = callable
                .params()
                .into_iter()
                .enumerate()
                .filter_map(|(index, param)| {
                    if has_receiver && index == 0 {
                        query.include_receiver.then_some((InputSlot::Receiver, param.ty().clone()))
                    } else {
                        Some((
                            InputSlot::Parameter { index: index as u32 - u32::from(has_receiver) },
                            param.ty().clone(),
                        ))
                    }
                })
                .collect();
            let direct_output = callable.return_type();
            let result = if query.awaited {
                match declaration {
                    Declaration::Function(f) => {
                        f.async_ret_type(db).or_else(|| direct_output.signature_future_output(db))
                    }
                    _ => direct_output.signature_future_output(db),
                }
            } else {
                Some(direct_output)
            };
            let Some(result) = result else {
                unknown(&mut batch.coverage, TypeMatchUnknown::AssociatedTypeNotProven);
                continue;
            };
            let input_matches = match_inputs(db, &query, &inputs, &params);
            let output_match = output
                .as_ref()
                .map(|pattern| pattern.matches(db, &result, query.references, query.deref));
            if matches!(input_matches, InputsMatch::No)
                || matches!(output_match, Some(TypeMatch::NoMatch))
            {
                continue;
            }
            if let InputsMatch::Unknown(reason) = input_matches {
                unknown(&mut batch.coverage, reason);
                continue;
            }
            if let Some(TypeMatch::Unknown(reason)) = output_match {
                unknown(&mut batch.coverage, reason);
                continue;
            }
            let InputsMatch::Yes(assignments) = input_matches else {
                continue;
            };
            let (name, signature, kind) = declaration_data(&sema, declaration);
            let source = scoped_source.unwrap_or_else(|| declaration_source(&sema, declaration));
            let mut matches = Vec::new();
            for (pattern, index, evidence) in assignments {
                matches.push(render_evidence(
                    db,
                    EvidenceRole::Input { pattern: pattern as u32, slot: params[index].0 },
                    &params[index].1,
                    evidence,
                    raw_inputs.get(pattern),
                    inputs.get(pattern),
                    written_type(&sema, declaration, Some(params[index].0)),
                ));
            }
            if let Some(TypeMatch::Match(evidence)) = output_match {
                matches.push(render_evidence(
                    db,
                    EvidenceRole::Output,
                    &result,
                    evidence,
                    query.output.as_ref(),
                    output.as_ref(),
                    written_type(&sema, declaration, None),
                ));
            }
            let krate = module.krate(db);
            let display_target = krate.to_display_target(db);
            let parameters = params
                .iter()
                .map(|(slot, ty)| Parameter { slot: *slot, ty: describe(db, ty, display_target) })
                .collect();
            if params.iter().any(|(_, ty)| ty.contains_unknown()) || result.contains_unknown() {
                unknown(&mut batch.coverage, TypeMatchUnknown::UnresolvedType);
            }
            batch.candidates.push(SignatureCandidate {
                id: format!("{krate:?}:{declaration:?}"),
                name: match declaration {
                    Declaration::Function(f) => f.name(db),
                    Declaration::Struct(s) => s.name(db),
                    Declaration::Variant(v) => v.name(db),
                }
                .as_str()
                .to_owned(),
                qualified_name: qualified(db, module, &name),
                signature,
                crate_name: krate
                    .display_name(db)
                    .map_or_else(|| format!("{krate:?}"), |name| name.to_string()),
                crate_instance: format!("{krate:?}"),
                workspace: workspace.contains(&krate),
                kind,
                parameters,
                output: describe(db, &result, display_target),
                matches,
                source,
            });
            batch.coverage.matched += 1;
        }
    }
    Ok(finish(batch))
}

fn add_assoc(item: AssocItem, declarations: &mut Vec<Declaration>) {
    match item {
        AssocItem::Function(f) => {
            declarations.push(Declaration::Function(f));
        }
        _ => {}
    }
}
fn unknown(coverage: &mut SignatureCoverage, reason: TypeMatchUnknown) {
    coverage.unknown += 1;
    coverage.complete = false;
    *coverage.unknown_reasons.entry(format!("{reason:?}")).or_default() += 1;
}
pub(crate) fn in_scope(scope: &SearchScope, location: FileRange) -> bool {
    match scope {
        SearchScope::Workspace => true,
        SearchScope::Regions(regions) => regions.iter().any(|(file, range)| {
            location.file_id == *file
                && range.is_none_or(|range| range.contains_range(location.range))
        }),
    }
}
fn finish(mut batch: SignatureBatch) -> SignatureBatch {
    for (reason, count) in &batch.coverage.incomplete_modules {
        batch
            .coverage
            .warnings
            .push(format!("Incomplete module evidence: {reason:?} ({count} modules)."));
    }
    for (reason, count) in &batch.coverage.exclusions {
        batch.coverage.warnings.push(format!("Excluded {count} {reason}."));
    }
    batch.coverage.unsearched.sort();
    batch.coverage.unsearched.dedup();
    batch.coverage.warnings.sort();
    batch.coverage.warnings.dedup();
    batch.candidates.sort_by(|a, b| a.qualified_name.cmp(&b.qualified_name).then(a.id.cmp(&b.id)));
    batch
}
pub(crate) fn qualified(db: &RootDatabase, module: Module, name: &str) -> String {
    let mut modules = Vec::new();
    let mut current = Some(module);
    while let Some(module) = current {
        if let Some(name) = module.name(db) {
            modules.push(name.as_str().to_owned());
        }
        current = module.parent(db);
    }
    modules.reverse();
    modules.push(name.to_owned());
    modules.join("::")
}
fn describe(db: &RootDatabase, ty: &Type<'_>, target: hir::DisplayTarget) -> TypeDescription {
    TypeDescription { display: ty.display(db, target).to_string(), form: ty.signature_shape(db) }
}
fn render_evidence(
    db: &RootDatabase,
    role: EvidenceRole,
    actual: &Type<'_>,
    evidence: TypeMatchEvidence,
    pattern: Option<&PatternInput>,
    compiled: Option<&SignaturePattern<'_>>,
    written: Option<String>,
) -> MatchEvidence {
    let target = actual.krate(db).to_display_target(db);
    let mut matched = actual
        .signature_autoderef(db)
        .nth(evidence.deref_steps as usize)
        .unwrap_or_else(|| actual.clone());
    for _ in 0..evidence.outer_references {
        matched = matched.strip_reference();
    }
    let actual_type = describe(db, actual, target);
    // This compares presentations only after a semantic match; it never decides matching.
    let resolved =
        if written.as_deref().is_some_and(|written| written.trim() != actual_type.display) {
            Some(ResolvedType { written, ty: actual_type.clone() })
        } else if let Some(ty) = compiled.and_then(SignaturePattern::resolved_type) {
            let canonical = describe(db, ty, target);
            match pattern {
                Some(PatternInput::Of(_)) => Some(ResolvedType { written: None, ty: canonical }),
                Some(PatternInput::Type(text)) if text.trim() != canonical.display => {
                    Some(ResolvedType { written: Some(text.clone()), ty: canonical })
                }
                _ => None,
            }
        } else {
            None
        };
    MatchEvidence {
        role,
        actual_type,
        matched_type: describe(db, &matched, target),
        evidence,
        bounds: pattern.and_then(|pattern| {
            if let PatternInput::Implements(bounds) = pattern { Some(bounds.clone()) } else { None }
        }),
        resolved,
    }
}

fn written_type(
    sema: &Semantics<'_, RootDatabase>,
    declaration: Declaration,
    slot: Option<InputSlot>,
) -> Option<String> {
    match declaration {
        Declaration::Function(f) => {
            let function = sema.source(f)?.value;
            match slot {
                Some(InputSlot::Receiver) => Some(function.param_list()?.self_param()?.to_string()),
                Some(InputSlot::Parameter { index }) => {
                    Some(function.param_list()?.params().nth(index as usize)?.ty()?.to_string())
                }
                None => Some(function.ret_type()?.ty()?.to_string()),
            }
        }
        Declaration::Struct(s) => {
            let Some(InputSlot::Parameter { index }) = slot else {
                return None;
            };
            let syntax::ast::FieldList::TupleFieldList(fields) =
                sema.source(s)?.value.field_list()?
            else {
                return None;
            };
            Some(fields.fields().nth(index as usize)?.ty()?.to_string())
        }
        Declaration::Variant(v) => {
            let Some(InputSlot::Parameter { index }) = slot else {
                return None;
            };
            let syntax::ast::FieldList::TupleFieldList(fields) =
                sema.source(v)?.value.field_list()?
            else {
                return None;
            };
            Some(fields.fields().nth(index as usize)?.ty()?.to_string())
        }
    }
}

fn declaration_data<'db>(
    sema: &Semantics<'db, RootDatabase>,
    declaration: Declaration,
) -> (String, String, CallableKind) {
    let db = sema.db;
    match declaration {
        Declaration::Function(f) => {
            let target = f.module(db).krate(db).to_display_target(db);
            let kind = if let Some(assoc) = f.as_assoc_item(db) {
                if matches!(assoc.container(db), AssocItemContainer::Trait(_)) {
                    CallableKind::TraitMethod
                } else if f.self_param(db).is_some() {
                    CallableKind::Method
                } else {
                    CallableKind::AssociatedFunction
                }
            } else {
                CallableKind::Function
            };
            let mut name = f.name(db).as_str().to_owned();
            let mut signature = f.display_with_container_bounds(db, true, target).to_string();
            if let Some(assoc) = f.as_assoc_item(db) {
                match assoc.container(db) {
                    AssocItemContainer::Trait(trait_) => {
                        name = format!("{}::{name}", trait_.name(db).as_str())
                    }
                    AssocItemContainer::Impl(impl_) => {
                        let self_ty = impl_.self_ty(db).display(db, target).to_string();
                        name = if let Some(trait_) = impl_.trait_(db) {
                            format!("<{self_ty} as {}>::{name}", trait_.name(db).as_str())
                        } else {
                            format!("{self_ty}::{name}")
                        };
                        if !signature.starts_with("impl") {
                            signature = format!("impl {self_ty}\n{signature}");
                        }
                    }
                }
            }
            (name, signature, kind)
        }
        Declaration::Struct(s) => {
            let target = s.module(db).krate(db).to_display_target(db);
            (
                s.name(db).as_str().to_owned(),
                s.display(db, target).to_string(),
                CallableKind::TupleStructConstructor,
            )
        }
        Declaration::Variant(v) => {
            let target = v.module(db).krate(db).to_display_target(db);
            let parent = v.parent_enum(db);
            let header = sema
                .source(parent)
                .map(|source| {
                    let params = source
                        .value
                        .generic_param_list()
                        .map_or(String::new(), |params| params.to_string());
                    let predicates = source
                        .value
                        .where_clause()
                        .map_or(String::new(), |clause| format!(" {clause}"));
                    format!("enum {}{params}{predicates}\n", parent.name(db).as_str())
                })
                .unwrap_or_default();
            (
                format!("{}::{}", v.parent_enum(db).name(db).as_str(), v.name(db).as_str()),
                format!("{header}{}", v.display(db, target)),
                CallableKind::EnumVariantConstructor,
            )
        }
    }
}

fn declaration_source(
    sema: &Semantics<'_, RootDatabase>,
    declaration: Declaration,
) -> CandidateSource {
    let db = sema.db;
    let source = match declaration {
        Declaration::Function(f) => sema.source(f).map(|s| s.map(|n| n.syntax().clone())),
        Declaration::Struct(s) => sema.source(s).map(|s| s.map(|n| n.syntax().clone())),
        Declaration::Variant(v) => sema.source(v).map(|s| s.map(|n| n.syntax().clone())),
    };
    match source {
        Some(source) => match source.file_id.file_id() {
            Some(file) => {
                let name_offset = source
                    .value
                    .children()
                    .find_map(syntax::ast::Name::cast)
                    .map_or(source.value.text_range().start(), |name| {
                        name.syntax().text_range().start()
                    });
                CandidateSource::Physical {
                    range: FileRange {
                        file_id: file.file_id(db),
                        range: source.value.text_range(),
                    },
                    name_offset,
                }
            }
            None => CandidateSource::Nonphysical {
                file_id: Some(source.file_id.original_file(db).file_id(db)),
                origin: Some(sema.original_range(&source.value).into_file_id(db)),
                reason: "macro-generated declaration has no exact physical declaration range"
                    .into(),
            },
        },
        None => CandidateSource::Nonphysical {
            file_id: None,
            origin: None,
            reason: "provider declaration has no physical syntax".into(),
        },
    }
}

enum InputsMatch {
    Yes(Vec<(usize, usize, TypeMatchEvidence)>),
    No,
    Unknown(TypeMatchUnknown),
}
fn match_inputs(
    db: &RootDatabase,
    query: &SignatureQuery,
    patterns: &[SignaturePattern<'_>],
    params: &[(InputSlot, Type<'_>)],
) -> InputsMatch {
    let Some(predicate) = &query.inputs else {
        return InputsMatch::Yes(Vec::new());
    };
    if matches!(predicate, InputPredicate::Exact(_)) && patterns.len() != params.len() {
        return InputsMatch::No;
    }
    if patterns.len() > params.len() && matches!(predicate, InputPredicate::All(_)) {
        return InputsMatch::No;
    }
    let edges: Vec<Vec<_>> = patterns
        .iter()
        .map(|pattern| {
            params
                .iter()
                .map(|(_, ty)| pattern.matches(db, ty, query.references, query.deref))
                .collect()
        })
        .collect();
    if matches!(predicate, InputPredicate::Exact(_)) {
        let mut matches = Vec::new();
        let mut uncertain = None;
        for (index, edges) in edges.iter().enumerate() {
            match &edges[index] {
                TypeMatch::Match(evidence) => matches.push((index, index, evidence.clone())),
                TypeMatch::NoMatch => return InputsMatch::No,
                TypeMatch::Unknown(reason) => uncertain = Some(*reason),
            }
        }
        return uncertain.map_or(InputsMatch::Yes(matches), InputsMatch::Unknown);
    }
    if matches!(predicate, InputPredicate::Any(_)) {
        let mut unknown = None;
        for (p, edges) in edges.iter().enumerate() {
            for (i, edge) in edges.iter().enumerate() {
                match edge {
                    TypeMatch::Match(e) => return InputsMatch::Yes(vec![(p, i, e.clone())]),
                    TypeMatch::Unknown(r) => unknown = Some(*r),
                    _ => {}
                }
            }
        }
        return unknown.map_or(InputsMatch::No, InputsMatch::Unknown);
    }
    fn assign(
        pattern: usize,
        edges: &[Vec<TypeMatch>],
        slots: &mut [Option<usize>],
        visited: &mut [bool],
        unknown: bool,
    ) -> bool {
        for (index, edge) in edges[pattern].iter().enumerate() {
            if visited[index]
                || matches!(edge, TypeMatch::NoMatch)
                || (!unknown && !matches!(edge, TypeMatch::Match(_)))
            {
                continue;
            }
            visited[index] = true;
            if slots[index].is_none_or(|old| assign(old, edges, slots, visited, unknown)) {
                slots[index] = Some(pattern);
                return true;
            }
        }
        false
    }
    let mut slots = vec![None; params.len()];
    let mut proven = true;
    for p in 0..patterns.len() {
        if !assign(p, &edges, &mut slots, &mut vec![false; params.len()], false) {
            proven = false;
            break;
        }
    }
    if proven {
        return InputsMatch::Yes(
            slots
                .into_iter()
                .enumerate()
                .filter_map(|(index, p)| {
                    p.and_then(|p| {
                        if let TypeMatch::Match(e) = &edges[p][index] {
                            Some((p, index, e.clone()))
                        } else {
                            None
                        }
                    })
                })
                .collect(),
        );
    }
    slots.fill(None);
    for p in 0..patterns.len() {
        if !assign(p, &edges, &mut slots, &mut vec![false; params.len()], true) {
            return InputsMatch::No;
        }
    }
    InputsMatch::Unknown(
        edges
            .iter()
            .flatten()
            .find_map(
                |edge| if let TypeMatch::Unknown(reason) = edge { Some(*reason) } else { None },
            )
            .unwrap_or(TypeMatchUnknown::UnsupportedStructure),
    )
}

pub(crate) fn search_crates(db: &RootDatabase, policy: DependencyPolicy) -> FxHashSet<Crate> {
    let workspace: FxHashSet<_> =
        Crate::all(db).into_iter().filter(|krate| krate.is_workspace_member(db)).collect();
    let mut crates = workspace.clone();
    if policy != DependencyPolicy::Exclude {
        let mut pending: Vec<_> = workspace.iter().copied().collect();
        while let Some(krate) = pending.pop() {
            for dependency in krate.dependencies(db) {
                if crates.insert(dependency.krate) {
                    pending.push(dependency.krate);
                }
            }
        }
    }
    if policy == DependencyPolicy::Only {
        crates.retain(|krate| !workspace.contains(krate));
    }
    crates
}

pub(crate) fn module_bodies(db: &RootDatabase, module: Module) -> Vec<DefWithBody> {
    let mut bodies = Vec::new();
    let mut assoc = |item: AssocItem| match item {
        AssocItem::Function(it) => bodies.push(DefWithBody::Function(it)),
        AssocItem::Const(it) => bodies.push(DefWithBody::Const(it)),
        _ => {}
    };
    for definition in module.declarations(db) {
        if let ModuleDef::Trait(it) = definition {
            for item in it.items(db) {
                assoc(item);
            }
        }
    }
    for impl_ in hir::Impl::all_in_module(db, module) {
        for item in impl_.items(db) {
            assoc(item);
        }
    }
    for definition in module.declarations(db) {
        match definition {
            ModuleDef::Function(it) => bodies.push(DefWithBody::Function(it)),
            ModuleDef::Const(it) => bodies.push(DefWithBody::Const(it)),
            ModuleDef::Static(it) => bodies.push(DefWithBody::Static(it)),
            ModuleDef::Adt(Adt::Enum(it)) => {
                bodies.extend(it.variants(db).into_iter().map(DefWithBody::EnumVariant))
            }
            _ => {}
        }
    }
    bodies.sort_by_key(|body| format!("{body:?}"));
    bodies.reverse();
    bodies
}

pub(crate) fn context_choice(db: &RootDatabase, module: Module) -> ContextChoice {
    ContextChoice {
        file_id: module.definition_source_range(db).file_id.original_file(db).file_id(db),
        id: format!("{module:?}"),
        crate_name: module
            .krate(db)
            .display_name(db)
            .map_or_else(|| "unnamed crate".into(), |name| name.to_string()),
        module: qualified(db, module, "").trim_end_matches("::").to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixture;

    #[test]
    fn semantic_signature_interactions() {
        let mut change = test_fixture::ChangeFixture::parse(
            r#"
//- minicore: sized, deref, future
//- /lib.rs crate:app deps:dep
$0
use dep::Foo;
type Alias=Foo;
type Wrap<T>=(T,);
struct New(Foo);
trait Visible {}
trait Hidden {}
trait ItemTrait {type Item;}
impl Visible for New {}
impl Hidden for New {}
impl ItemTrait for New {type Item=Wrap<Foo>;}
impl core::ops::Deref for New {type Target=Foo;fn deref(&self)->&Foo {&self.0}}
fn plain()->Foo {loop {}}
fn alias()->Alias {loop {}}
fn borrowed()->&'static Foo {loop {}}
fn generic<T>(x:T)->T {x}
fn bounded<T:Visible>(x:T)->T {x}
fn array<const N:usize>()->[u8;N] {loop {}}
fn injective(a:&Foo,b:Foo) {}
fn duplicate(a:Foo) {}
fn wrapped()->Wrap<Foo> {loop {}}
fn make_new()->New {loop {}}
fn opaque()->impl Visible {New(Foo)}
fn opaque_item()->impl ItemTrait<Item=Wrap<Foo>> {New(Foo)}
async fn later()->Foo {Foo}
fn outer() {fn local()->Foo {Foo}}
impl New {fn method(&self,x:Foo)->Foo {x}}
#[cfg(disabled)] fn excluded()->Foo {Foo}
macro_rules! produce {()=>{fn generated()->Foo {Foo}};}
produce!();
mod damaged_a {unresolved_macro!();}
mod damaged_b {unresolved_macro!();}
pub use plain as reexport;
//- /dep.rs crate:dep
pub struct Foo;
pub fn dependency()->Foo {Foo}
"#,
        );
        let graph = change.change.source_change.crate_graph.as_mut().unwrap();
        let dependency = graph
            .iter()
            .find(|id| {
                graph[*id].extra.display_name.as_ref().is_some_and(|name| name.to_string() == "dep")
            })
            .unwrap();
        assert!(graph[dependency].basic.origin.is_local());
        graph.set_workspace_member(dependency, false);
        let file_id = change.file_position.unwrap().0.file_id();
        let mut host = crate::AnalysisHost::default();
        host.db.enable_proc_attr_macros();
        host.db.apply_change(change.change);
        let analysis = host.analysis();
        let position = crate::FilePosition { file_id, offset: 0.into() };
        let base = SignatureQuery {
            context: SignatureAnchor { file_id: position.file_id, range: None, context_id: None },
            inputs: None,
            output: Some(PatternInput::Type("Foo".into())),
            scope: SearchScope::Workspace,
            dependencies: DependencyPolicy::Exclude,
            references: ReferencePolicy::Outer,
            deref: false,
            include_receiver: true,
            awaited: false,
            max_candidates: 1000,
        };
        let run = |query: SignatureQuery| analysis.sem_signature_search(query).unwrap().unwrap();
        let names = |batch: &SignatureBatch| {
            batch.candidates.iter().map(|c| c.qualified_name.as_str()).collect::<Vec<_>>().join(",")
        };
        let batch = run(base.clone());
        assert!(!batch.coverage.complete);
        assert!(batch.coverage.incomplete_modules.iter().any(|(_, count)| *count >= 2));
        assert_eq!(
            batch
                .coverage
                .warnings
                .iter()
                .filter(|warning| warning.starts_with("Incomplete module evidence:"))
                .count(),
            batch.coverage.incomplete_modules.len()
        );
        for name in ["plain", "alias", "borrowed", "local", "generated", "method"] {
            assert!(
                batch.candidates.iter().any(|c| c.qualified_name.ends_with(name)),
                "{name}: {}",
                names(&batch)
            );
        }
        for name in ["generic", "excluded", "dependency", "make_new", "opaque", "reexport"] {
            assert!(
                !batch.candidates.iter().any(|c| c.qualified_name.ends_with(name)),
                "{name}: {}",
                names(&batch)
            );
        }
        assert_eq!(batch.candidates.iter().filter(|c| c.qualified_name == "plain").count(), 1);
        let generated = batch.candidates.iter().find(|c| c.name == "generated").unwrap();
        assert_eq!(generated.kind, CallableKind::Function);
        assert!(matches!(generated.source, CandidateSource::Nonphysical { .. }));
        let method = batch.candidates.iter().find(|c| c.name == "method").unwrap();
        assert_eq!(method.kind, CallableKind::Method);
        assert_ne!(method.name, method.qualified_name);
        let mut exact = base.clone();
        exact.references = ReferencePolicy::Exact;
        assert!(!run(exact).candidates.iter().any(|c| c.qualified_name == "borrowed"));
        let mut inputs = base.clone();
        inputs.output = None;
        inputs.inputs = Some(InputPredicate::All(vec![
            PatternInput::Type("Foo".into()),
            PatternInput::Type("&Foo".into()),
        ]));
        let matched = run(inputs.clone());
        assert!(
            matched.candidates.iter().any(|c| c.qualified_name == "injective"),
            "{}",
            names(&matched)
        );
        assert!(!matched.candidates.iter().any(|c| c.qualified_name == "duplicate"));
        inputs.inputs = Some(InputPredicate::Exact(vec![
            PatternInput::Type("Foo".into()),
            PatternInput::Type("&Foo".into()),
        ]));
        assert!(!run(inputs).candidates.iter().any(|c| c.qualified_name == "injective"));
        let mut wildcard = base.clone();
        wildcard.output = Some(PatternInput::Type("Wrap<_>".into()));
        assert!(run(wildcard).candidates.iter().any(|c| c.qualified_name == "wrapped"));
        let mut bounds = base.clone();
        bounds.output = Some(PatternInput::Implements("ItemTrait<Item=Wrap<_>>".into()));
        let bounded = run(bounds);
        assert!(
            bounded.candidates.iter().any(|c| c.qualified_name == "make_new"),
            "{}",
            names(&bounded)
        );
        assert!(!bounded.candidates.iter().any(|c| c.qualified_name == "opaque"));
        let mut hidden = base.clone();
        hidden.output = Some(PatternInput::Implements("Hidden".into()));
        assert!(!run(hidden).candidates.iter().any(|c| c.qualified_name == "opaque"));
        let mut visible = base.clone();
        visible.output = Some(PatternInput::Implements("Visible".into()));
        let visible = run(visible);
        assert!(visible.candidates.iter().any(|c| c.qualified_name == "opaque"));
        assert!(visible.candidates.iter().any(|c| c.qualified_name == "bounded"));
        let mut item = base.clone();
        item.output = Some(PatternInput::Implements("ItemTrait<Item=Wrap<_>>".into()));
        assert!(run(item).candidates.iter().any(|c| c.qualified_name == "opaque_item"));
        let mut modifier = base.clone();
        modifier.output = Some(PatternInput::Implements("?Sized".into()));
        assert!(analysis.sem_signature_search(modifier).unwrap().is_err());
        let mut receiver = base.clone();
        receiver.inputs = Some(InputPredicate::Exact(vec![PatternInput::Type("Foo".into())]));
        assert!(
            !run(receiver.clone()).candidates.iter().any(|c| c.qualified_name.ends_with("method"))
        );
        receiver.include_receiver = false;
        assert!(run(receiver).candidates.iter().any(|c| c.qualified_name.ends_with("method")));
        let mut constructor = base.clone();
        constructor.output = Some(PatternInput::Type("New".into()));
        constructor.inputs = Some(InputPredicate::Exact(vec![PatternInput::Type("Foo".into())]));
        assert!(
            run(constructor)
                .candidates
                .iter()
                .any(|c| c.kind == CallableKind::TupleStructConstructor)
        );
        let mut any_output = base.clone();
        any_output.output = Some(PatternInput::Type("_".into()));
        assert_eq!(
            run(any_output)
                .candidates
                .iter()
                .find(|c| c.qualified_name == "array")
                .unwrap()
                .output
                .form,
            TypeShape::Generic
        );
        let mut narrow = base.clone();
        narrow.scope = SearchScope::Regions(vec![(position.file_id, None)]);
        assert!(run(narrow).candidates.iter().any(|c| c.qualified_name == "generated"));
        let mut deref = base.clone();
        deref.deref = true;
        let dereferenced = run(deref);
        assert!(dereferenced.candidates.iter().any(|c| c.qualified_name == "make_new"));
        assert!(!dereferenced.candidates.iter().any(|c| c.qualified_name == "opaque"));
        let mut awaited = base.clone();
        awaited.awaited = true;
        assert!(run(awaited).candidates.iter().any(|c| c.qualified_name == "later"));
        let mut dependencies = base.clone();
        dependencies.dependencies = DependencyPolicy::Only;
        dependencies.max_candidates = 1;
        let dependencies = run(dependencies);
        let dependency =
            dependencies.candidates.iter().find(|c| c.qualified_name == "dependency").unwrap();
        assert!(!dependency.workspace);
        let CandidateSource::Physical { range, name_offset } = dependency.source else {
            panic!("physical dependency fixture")
        };
        let dep_text = analysis.file_text(range.file_id).unwrap();
        let return_start = dep_text.find("->Foo").unwrap() as u32 + 2;
        let mut cross_file = base.clone();
        cross_file.output = Some(PatternInput::Of(SignatureAnchor {
            file_id: range.file_id,
            range: Some(TextRange::new(return_start.into(), (return_start + 3).into())),
            context_id: None,
        }));
        assert!(run(cross_file.clone()).candidates.iter().any(|c| c.qualified_name == "plain"));
        cross_file.output = Some(PatternInput::Of(SignatureAnchor {
            file_id: range.file_id,
            range: Some(TextRange::empty(name_offset)),
            context_id: None,
        }));
        assert!(!run(cross_file).candidates.iter().any(|c| c.qualified_name == "plain"));
        let mut absent = base.clone();
        absent.output = Some(PatternInput::Type("Missing".into()));
        assert!(analysis.sem_signature_search(absent).unwrap().is_err());
        let mut limited = base.clone();
        limited.max_candidates = 1;
        let limited = run(limited);
        assert!(!limited.coverage.complete);
        assert!(!limited.coverage.unsearched.is_empty());
        assert!(limited.coverage.unsearched.iter().any(|reason| reason.contains("body-local")));

        let (clean_analysis, clean) = fixture::position(
            r#"
$0struct Unit;
struct Record {value:u8}
enum Shape {Unit,Record {value:u8},Tuple(u8)}
fn make()->Shape {loop {}}
"#,
        );
        let mut callable_universe = base.clone();
        callable_universe.context =
            SignatureAnchor { file_id: clean.file_id, range: None, context_id: None };
        callable_universe.output = Some(PatternInput::Type("Shape".into()));
        let clean = clean_analysis.sem_signature_search(callable_universe).unwrap().unwrap();
        // Known non-callable construction syntax is counted, not a gap in callable discovery.
        assert!(clean.coverage.complete);
        assert_eq!(clean.coverage.exclusions.values().sum::<u32>(), 4);
        assert_eq!(clean.candidates.len(), 2);
        assert!(clean.candidates.iter().any(|candidate| candidate.name == "make"));
        assert!(
            clean
                .candidates
                .iter()
                .any(|candidate| candidate.kind == CallableKind::EnumVariantConstructor
                    && candidate.name == "Tuple")
        );

        let (generic_analysis, first) = fixture::position("$0fn first<T>(x:T)->T {x}");
        let mut contextual = base.clone();
        contextual.context = SignatureAnchor {
            file_id: first.file_id,
            range: Some(TextRange::empty(0.into())),
            context_id: None,
        };
        contextual.output = Some(PatternInput::Type("T".into()));
        assert!(
            generic_analysis
                .sem_signature_search(contextual.clone())
                .unwrap()
                .unwrap()
                .candidates
                .iter()
                .any(|c| c.qualified_name == "first")
        );
        contextual.context.range = None;
        assert!(generic_analysis.sem_signature_search(contextual).unwrap().is_err());

        let (ambiguous_analysis, shared) = fixture::position(
            r#"
//- /a.rs crate:a
mod shared;
//- /b.rs crate:b
mod shared;
//- /shared.rs
$0fn shared<T>(x:T)->T {fn nested<U>(x:U)->U {x} x}
"#,
        );
        let mut ambiguous = base;
        ambiguous.context = SignatureAnchor {
            file_id: shared.file_id,
            range: Some(TextRange::empty(0.into())),
            context_id: None,
        };
        ambiguous.output = Some(PatternInput::Type("T".into()));
        let SignatureError::AmbiguousContext { choices } =
            ambiguous_analysis.sem_signature_search(ambiguous.clone()).unwrap().unwrap_err()
        else {
            panic!("expected context choices")
        };
        assert_eq!(choices.len(), 2);
        ambiguous.context.context_id = Some(choices[0].id.clone());
        assert_eq!(
            ambiguous_analysis
                .sem_signature_search(ambiguous.clone())
                .unwrap()
                .unwrap()
                .candidates
                .len(),
            1
        );
        let text = ambiguous_analysis.file_text(shared.file_id).unwrap();
        let nested = text.find("fn nested").unwrap() as u32;
        ambiguous.context.range = Some(TextRange::empty(nested.into()));
        ambiguous.output = Some(PatternInput::Type("U".into()));
        let nested = ambiguous_analysis.sem_signature_search(ambiguous).unwrap().unwrap();
        assert_eq!(nested.candidates.len(), 1);
        assert!(nested.candidates[0].qualified_name.ends_with("nested"));
    }
}
