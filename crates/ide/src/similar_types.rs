//! Structural declaration similarity backed by resolved HIR member identities.

use std::collections::{BTreeMap, BTreeSet};

use hir::{HirDisplay, Semantics, SignaturePattern, TypeMatch};
use ide_db::{FxHashSet, RootDatabase};
use syntax::{
    AstNode, SourceFile, SyntaxNode,
    ast::{self, HasModuleItem, HasName},
};

use crate::{
    FileId, FileRange,
    signature_search::{
        self, CandidateSource, DependencyPolicy, SearchScope, SignatureAnchor, SignatureError,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimilarKind {
    Struct,
    Enum,
    Union,
    Trait,
    TypeAlias,
}

#[derive(Debug, Clone)]
pub enum SimilarInput {
    Draft(String),
    Target(SignatureAnchor),
}

#[derive(Debug, Clone)]
pub struct SimilarQuery {
    pub context: Option<SignatureAnchor>,
    pub query: SimilarInput,
    pub scope: SearchScope,
    pub dependencies: DependencyPolicy,
    pub kinds: Option<Vec<SimilarKind>>,
    pub min_score: f64,
    pub max_candidates: u32,
}

#[derive(Debug, Clone)]
pub enum MemberResolution {
    Resolved,
    Unresolved { reason: String },
}

#[derive(Debug, Clone)]
pub struct SimilarMember {
    pub name: String,
    pub signature: String,
    pub resolution: MemberResolution,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimilarRelation {
    Equal,
    QueryWithinCandidate,
    CandidateWithinQuery,
    Overlap,
}

#[derive(Debug, Clone, Copy)]
pub enum SimilarEvidence {
    Semantic,
    UnresolvedText,
}

#[derive(Debug, Clone)]
pub struct SimilarShared {
    pub query: u32,
    pub candidate: u32,
    pub evidence: SimilarEvidence,
}

#[derive(Debug, Clone)]
pub struct SimilarDeclaration {
    pub kind: SimilarKind,
    pub members: Vec<SimilarMember>,
}

#[derive(Debug, Clone)]
pub struct SimilarCandidate {
    pub id: String,
    pub name: String,
    pub qualified_name: String,
    pub crate_name: String,
    pub crate_instance: String,
    pub workspace: bool,
    pub kind: SimilarKind,
    pub visibility: String,
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

#[derive(Debug, Clone, Default)]
pub struct SimilarCoverage {
    pub examined: u32,
    pub matched: u32,
    pub query_unresolved: u32,
    pub candidate_unresolved: u32,
    pub text_matches: u32,
    pub unknown: u32,
    pub unknown_reasons: Vec<(String, u32)>,
    pub unsearched: Vec<String>,
    pub warnings: Vec<String>,
    pub complete: bool,
}

#[derive(Debug, Clone)]
pub struct SimilarBatch {
    pub context_file: FileId,
    pub query: SimilarDeclaration,
    pub candidates: Vec<SimilarCandidate>,
    pub coverage: SimilarCoverage,
}

#[derive(PartialEq, Eq)]
enum MemberShape {
    Type,
    Variant(String),
    Method(usize),
    AssociatedType(String),
    AssociatedConst(String),
    Macro,
}

enum MemberIdentity<'db> {
    Resolved(Vec<hir::Type<'db>>),
    Unresolved { normalized: String, reason: String },
}

struct Member<'db> {
    name: String,
    signature: String,
    shape: MemberShape,
    identity: MemberIdentity<'db>,
}

impl Member<'_> {
    fn into_description(self) -> SimilarMember {
        let resolution = match self.identity {
            MemberIdentity::Resolved(_) => MemberResolution::Resolved,
            MemberIdentity::Unresolved { reason, .. } => MemberResolution::Unresolved { reason },
        };
        SimilarMember { name: self.name, signature: self.signature, resolution }
    }
}

fn normalized(node: &SyntaxNode) -> String {
    node.descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .filter(|it| !it.kind().is_trivia())
        .map(|it| it.text().to_owned())
        .collect::<Vec<_>>()
        .join(" ")
}

fn name_tokens(name: &str) -> BTreeSet<String> {
    let chars: Vec<_> = name.chars().collect();
    let mut tokens = BTreeSet::new();
    let mut token = String::new();
    for (index, ch) in chars.iter().copied().enumerate() {
        if !ch.is_alphanumeric() {
            if !token.is_empty() {
                tokens.insert(std::mem::take(&mut token));
            }
            continue;
        }
        let boundary = index > 0
            && ch.is_uppercase()
            && (chars[index - 1].is_lowercase()
                || chars[index - 1].is_numeric()
                || (chars[index - 1].is_uppercase()
                    && chars.get(index + 1).is_some_and(|next| next.is_lowercase())));
        if boundary && !token.is_empty() {
            tokens.insert(std::mem::take(&mut token));
        }
        token.extend(ch.to_lowercase());
    }
    if !token.is_empty() {
        tokens.insert(token);
    }
    tokens
}

fn member<'db>(
    name: String,
    shape: MemberShape,
    written: Vec<String>,
    types: Result<Vec<hir::Type<'db>>, String>,
) -> Member<'db> {
    let signature = written.join(", ");
    let identity = match types {
        Ok(types) => MemberIdentity::Resolved(types),
        Err(reason) => {
            let parsed = SourceFile::parse(
                &format!("type __Member = ({signature});"),
                syntax::Edition::CURRENT,
            );
            MemberIdentity::Unresolved { normalized: normalized(&parsed.syntax_node()), reason }
        }
    };
    Member { name, signature, shape, identity }
}

fn semantic_member<'db>(
    db: &'db RootDatabase,
    name: String,
    shape: MemberShape,
    types: Vec<hir::Type<'db>>,
    written: Option<Vec<String>>,
    target: hir::DisplayTarget,
) -> Member<'db> {
    let written = written
        .unwrap_or_else(|| types.iter().map(|ty| ty.display(db, target).to_string()).collect());
    let unknown = types
        .iter()
        .any(|ty| ty.contains_unknown() || ty.signature_shape(db) == hir::TypeShape::Unknown);
    member(
        name,
        shape,
        written,
        if unknown { Err("unresolved semantic type".into()) } else { Ok(types) },
    )
}

fn field_members<'db>(
    sema: &Semantics<'db, RootDatabase>,
    fields: Vec<hir::Field>,
    target: hir::DisplayTarget,
) -> Vec<Member<'db>> {
    fields
        .into_iter()
        .map(|field| {
            let written = sema
                .source(field)
                .and_then(|source| match source.value {
                    hir::FieldSource::Named(field) => field.ty(),
                    hir::FieldSource::Pos(field) => field.ty(),
                })
                .map(|ty| vec![ty.syntax().text().to_string()]);
            semantic_member(
                sema.db,
                field.name(sema.db).as_str().to_owned(),
                MemberShape::Type,
                vec![field.ty(sema.db)],
                written,
                target,
            )
        })
        .collect()
}

fn declaration<'db>(
    sema: &Semantics<'db, RootDatabase>,
    definition: hir::ModuleDef,
) -> Option<(SimilarKind, String, hir::Module, Option<SyntaxNode>)> {
    let db = sema.db;
    let (kind, name, module, node) = match definition {
        hir::ModuleDef::Adt(hir::Adt::Struct(it)) => (
            SimilarKind::Struct,
            it.name(db),
            it.module(db),
            sema.source(it).map(|s| s.value.syntax().clone()),
        ),
        hir::ModuleDef::Adt(hir::Adt::Enum(it)) => (
            SimilarKind::Enum,
            it.name(db),
            it.module(db),
            sema.source(it).map(|s| s.value.syntax().clone()),
        ),
        hir::ModuleDef::Adt(hir::Adt::Union(it)) => (
            SimilarKind::Union,
            it.name(db),
            it.module(db),
            sema.source(it).map(|s| s.value.syntax().clone()),
        ),
        hir::ModuleDef::Trait(it) => (
            SimilarKind::Trait,
            it.name(db),
            it.module(db),
            sema.source(it).map(|s| s.value.syntax().clone()),
        ),
        hir::ModuleDef::TypeAlias(it) => (
            SimilarKind::TypeAlias,
            it.name(db),
            it.module(db),
            sema.source(it).map(|s| s.value.syntax().clone()),
        ),
        _ => return None,
    };
    Some((kind, name.as_str().to_owned(), module, node))
}

fn existing_members<'db>(
    sema: &Semantics<'db, RootDatabase>,
    definition: hir::ModuleDef,
    module: hir::Module,
    name: &str,
    node: Option<&SyntaxNode>,
) -> Vec<Member<'db>> {
    let db = sema.db;
    let target = module.krate(db).to_display_target(db);
    match definition {
        hir::ModuleDef::Adt(hir::Adt::Struct(it)) => field_members(sema, it.fields(db), target),
        hir::ModuleDef::Adt(hir::Adt::Union(it)) => field_members(sema, it.fields(db), target),
        hir::ModuleDef::Adt(hir::Adt::Enum(it)) => it
            .variants(db)
            .into_iter()
            .map(|variant| {
                let name = variant.name(db).as_str().to_owned();
                let fields = field_members(sema, variant.fields(db), target);
                let shape = if variant.kind(db) == hir::StructKind::Tuple && fields.len() == 1 {
                    MemberShape::Type
                } else {
                    MemberShape::Variant(name.clone())
                };
                let written = fields.iter().map(|field| field.signature.clone()).collect();
                let types = fields.into_iter().try_fold(Vec::new(), |mut types, field| match field
                    .identity
                {
                    MemberIdentity::Resolved(field_types) => {
                        types.extend(field_types);
                        Ok(types)
                    }
                    MemberIdentity::Unresolved { reason, .. } => Err(reason),
                });
                member(name, shape, written, types)
            })
            .collect(),
        hir::ModuleDef::Trait(it) => it
            .items(db)
            .into_iter()
            .map(|item| match item {
                hir::AssocItem::Function(function) => {
                    let name = function.name(db).as_str().to_owned();
                    if let Some(callable) = function.ty(db).as_callable(db) {
                        let mut types: Vec<_> =
                            callable.params().iter().map(|param| param.ty().clone()).collect();
                        let count = types.len();
                        types.push(callable.return_type());
                        semantic_member(db, name, MemberShape::Method(count), types, None, target)
                    } else {
                        member(
                            name,
                            MemberShape::Method(0),
                            vec!["unsupported callable".into()],
                            Err("unsupported trait method signature".into()),
                        )
                    }
                }
                hir::AssocItem::TypeAlias(item) => {
                    let name = item.name(db).as_str().to_owned();
                    member(name.clone(), MemberShape::AssociatedType(name), vec![], Ok(vec![]))
                }
                hir::AssocItem::Const(item) => {
                    let name =
                        item.name(db).map_or_else(|| "_".into(), |it| it.as_str().to_owned());
                    member(name.clone(), MemberShape::AssociatedConst(name), vec![], Ok(vec![]))
                }
            })
            .collect(),
        hir::ModuleDef::TypeAlias(it) => vec![semantic_member(
            db,
            name.to_owned(),
            MemberShape::Type,
            vec![it.ty(db)],
            node.and_then(|node| ast::TypeAlias::cast(node.clone()))
                .and_then(|it| it.ty())
                .map(|ty| vec![ty.syntax().text().to_string()]),
            target,
        )],
        _ => unreachable!(),
    }
}

fn draft_member<'db>(
    scope: &hir::SemanticsScope<'db>,
    blocked: &FxHashSet<String>,
    name: String,
    shape: MemberShape,
    written: Vec<String>,
) -> Member<'db> {
    let mut reason = None;
    let mut types = Vec::new();
    for text in &written {
        let parsed =
            SourceFile::parse(&format!("type __Member = {text};"), syntax::Edition::CURRENT);
        if parsed.syntax_node().descendants().filter_map(ast::Type::cast).next().is_some_and(|ty| {
            ty.syntax()
                .descendants_with_tokens()
                .filter_map(|it| it.into_token())
                .any(|token| blocked.contains(token.text()))
        }) {
            reason = Some("draft-local binder, Self or declaration identity is unavailable".into());
            break;
        }
        if text.is_empty()
            || parsed.syntax_node().descendants().any(|node| ast::InferType::can_cast(node.kind()))
        {
            reason = Some("missing type or inference placeholder; no wildcard matching".into());
            break;
        }
        match scope.signature_pattern(text, false).and_then(|pattern| {
            pattern.resolved_type().cloned().ok_or("missing resolved identity".into())
        }) {
            Ok(ty) => types.push(ty),
            Err(error) => {
                reason = Some(error);
                break;
            }
        }
    }
    member(name, shape, written, reason.map_or(Ok(types), Err))
}

fn draft<'db>(
    sema: &Semantics<'db, RootDatabase>,
    context: &SignatureAnchor,
    module: hir::Module,
    text: &str,
) -> Result<(SimilarKind, String, Vec<Member<'db>>, Vec<String>), SignatureError> {
    if text.len() > 65_536 {
        return Err("draft exceeds 65536 bytes".into());
    }
    let parsed = SourceFile::parse(text, module.krate(sema.db).edition(sema.db));
    let items: Vec<_> = parsed.tree().items().collect();
    let [item] = items.as_slice() else {
        return Err("draft must contain exactly one supported declaration".into());
    };
    let (kind, name) = match item {
        ast::Item::Struct(it) => (SimilarKind::Struct, it.name()),
        ast::Item::Enum(it) => (SimilarKind::Enum, it.name()),
        ast::Item::Union(it) => (SimilarKind::Union, it.name()),
        ast::Item::Trait(it) => (SimilarKind::Trait, it.name()),
        ast::Item::TypeAlias(it) => (SimilarKind::TypeAlias, it.name()),
        _ => return Err("draft must be a struct, enum, union, trait or type alias".into()),
    };
    let mut blocked: FxHashSet<String> = ["Self".into()].into_iter().collect();
    let name = name.map_or_else(String::new, |name| name.text().to_owned());
    blocked.insert(name.clone());
    for node in item
        .syntax()
        .children()
        .filter_map(ast::GenericParamList::cast)
        .flat_map(|list| list.syntax().children().collect::<Vec<_>>())
    {
        if let Some(name) = node.children().find_map(ast::Name::cast) {
            blocked.insert(name.text().to_owned());
        }
    }
    let file = sema.parse_guess_edition(context.file_id);
    let scope =
        sema.signature_scope_at(module, file.syntax(), context.range.map(|range| range.start()));
    let ty_text =
        |ty: Option<ast::Type>| ty.map_or_else(String::new, |ty| ty.syntax().text().to_string());
    let fields = |list: Option<ast::FieldList>| -> Vec<(String, String)> {
        match list {
            Some(ast::FieldList::RecordFieldList(list)) => list
                .fields()
                .map(|it| {
                    (
                        it.name().map_or_else(String::new, |it| it.text().to_owned()),
                        ty_text(it.ty()),
                    )
                })
                .collect(),
            Some(ast::FieldList::TupleFieldList(list)) => list
                .fields()
                .enumerate()
                .map(|(index, it)| (index.to_string(), ty_text(it.ty())))
                .collect(),
            None => vec![],
        }
    };
    let members = match item {
        ast::Item::Struct(it) => fields(it.field_list())
            .into_iter()
            .map(|(name, ty)| draft_member(&scope, &blocked, name, MemberShape::Type, vec![ty]))
            .collect(),
        ast::Item::Union(it) => it
            .record_field_list()
            .map(|list| fields(Some(ast::FieldList::RecordFieldList(list))))
            .unwrap_or_default()
            .into_iter()
            .map(|(name, ty)| draft_member(&scope, &blocked, name, MemberShape::Type, vec![ty]))
            .collect(),
        ast::Item::Enum(it) => it
            .variant_list()
            .into_iter()
            .flat_map(|list| list.variants())
            .map(|variant| {
                let name = variant.name().map_or_else(String::new, |it| it.text().to_owned());
                let tuple = matches!(variant.field_list(), Some(ast::FieldList::TupleFieldList(_)));
                let fields = fields(variant.field_list());
                let shape = if tuple && fields.len() == 1 {
                    MemberShape::Type
                } else {
                    MemberShape::Variant(name.clone())
                };
                draft_member(
                    &scope,
                    &blocked,
                    name,
                    shape,
                    fields.into_iter().map(|(_, ty)| ty).collect(),
                )
            })
            .collect(),
        ast::Item::TypeAlias(it) => {
            vec![draft_member(
                &scope,
                &blocked,
                name.clone(),
                MemberShape::Type,
                vec![ty_text(it.ty())],
            )]
        }
        ast::Item::Trait(it) => it
            .assoc_item_list()
            .into_iter()
            .flat_map(|list| list.assoc_items())
            .map(|item| match item {
                ast::AssocItem::Fn(function) => {
                    let name = function.name().map_or_else(String::new, |it| it.text().to_owned());
                    let mut blocked = blocked.clone();
                    for name in function
                        .syntax()
                        .children()
                        .filter_map(ast::GenericParamList::cast)
                        .flat_map(|list| {
                            list.syntax()
                                .descendants()
                                .filter_map(ast::Name::cast)
                                .collect::<Vec<_>>()
                        })
                    {
                        blocked.insert(name.text().to_owned());
                    }
                    let mut written = Vec::new();
                    if let Some(list) = function.param_list() {
                        if let Some(receiver) = list.self_param() {
                            written.push(receiver.ty().map_or_else(
                                || {
                                    if receiver.amp_token().is_some() {
                                        if receiver.mut_token().is_some() {
                                            "&mut Self".into()
                                        } else {
                                            "&Self".into()
                                        }
                                    } else {
                                        "Self".into()
                                    }
                                },
                                |ty| ty_text(Some(ty)),
                            ));
                        }
                        written.extend(list.params().map(|it| ty_text(it.ty())));
                    } else {
                        written.push(String::new());
                    }
                    let count = written.len();
                    written.push(
                        function.ret_type().map_or_else(|| "()".into(), |ret| ty_text(ret.ty())),
                    );
                    if function.async_token().is_some() {
                        if let Some(output) = written.last_mut() {
                            *output = format!("async {output}");
                        }
                        member(
                            name,
                            MemberShape::Method(count),
                            written,
                            Err("draft async return opaque identity is unavailable".into()),
                        )
                    } else {
                        draft_member(&scope, &blocked, name, MemberShape::Method(count), written)
                    }
                }
                ast::AssocItem::TypeAlias(it) => {
                    let name = it.name().map_or_else(String::new, |it| it.text().to_owned());
                    draft_member(
                        &scope,
                        &blocked,
                        name.clone(),
                        MemberShape::AssociatedType(name),
                        vec![],
                    )
                }
                ast::AssocItem::Const(it) => {
                    let name = it.name().map_or_else(String::new, |it| it.text().to_owned());
                    draft_member(
                        &scope,
                        &blocked,
                        name.clone(),
                        MemberShape::AssociatedConst(name),
                        vec![],
                    )
                }
                ast::AssocItem::MacroCall(it) => member(
                    String::new(),
                    MemberShape::Macro,
                    vec![it.syntax().text().to_string()],
                    Err("draft associated macro is not expanded".into()),
                ),
            })
            .collect(),
        _ => unreachable!(),
    };
    let mut uncertainties: Vec<_> =
        parsed.errors().into_iter().map(|error| format!("malformed draft: {error}")).collect();
    for attr in item.syntax().descendants().filter_map(ast::Attr::cast) {
        let name = attr.simple_name();
        if !matches!(
            name.as_deref(),
            Some(
                "doc"
                    | "derive"
                    | "repr"
                    | "allow"
                    | "warn"
                    | "deny"
                    | "forbid"
                    | "expect"
                    | "must_use"
                    | "non_exhaustive"
                    | "deprecated"
                    | "inline"
                    | "cold"
                    | "track_caller"
                    | "automatically_derived"
            )
        ) {
            uncertainties
                .push("draft cfg or potentially transforming attribute is not evaluated".into());
        }
    }
    uncertainties.sort();
    uncertainties.dedup();
    Ok((kind, name, members, uncertainties))
}

fn source(sema: &Semantics<'_, RootDatabase>, node: Option<&SyntaxNode>) -> CandidateSource {
    let Some(node) = node else {
        return CandidateSource::Nonphysical {
            file_id: None,
            origin: None,
            reason: "provider declaration has no syntax".into(),
        };
    };
    let file = sema.hir_file_for(node);
    match file.file_id() {
        Some(file) => CandidateSource::Physical {
            range: FileRange { file_id: file.file_id(sema.db), range: node.text_range() },
            name_offset: node
                .children()
                .find_map(ast::Name::cast)
                .map_or(node.text_range().start(), |name| name.syntax().text_range().start()),
        },
        None => CandidateSource::Nonphysical {
            file_id: Some(file.original_file(sema.db).file_id(sema.db)),
            origin: Some(sema.original_range(node).into_file_id(sema.db)),
            reason: "macro-generated declaration has no exact physical declaration range".into(),
        },
    }
}

fn syntax_uncertainty(
    sema: &Semantics<'_, RootDatabase>,
    node: Option<&SyntaxNode>,
) -> Vec<String> {
    let Some(node) = node else {
        return vec!["declaration source syntax is unavailable".into()];
    };
    let Some(file) = sema.hir_file_for(node).file_id() else {
        return Vec::new();
    };
    file.parse(sema.db)
        .errors()
        .into_iter()
        .filter(|error| error.range().intersect(node.text_range()).is_some())
        .map(|error| format!("recovered existing declaration syntax: {error}"))
        .collect()
}

fn unknown(coverage: &mut SimilarCoverage, reason: String) {
    coverage.complete = false;
    coverage.unknown += 1;
    if let Some((_, count)) = coverage.unknown_reasons.iter_mut().find(|(it, _)| *it == reason) {
        *count += 1;
    } else {
        coverage.unknown_reasons.push((reason, 1));
    }
}

fn unresolved(members: &[Member<'_>], coverage: &mut SimilarCoverage) -> u32 {
    let mut count = 0;
    for member in members {
        if let MemberIdentity::Unresolved { reason, .. } = &member.identity {
            count += 1;
            unknown(coverage, reason.clone());
        }
    }
    count
}

fn overlap(query: usize, candidate: usize, shared: usize) -> f64 {
    let union = query + candidate - shared;
    if union == 0 { 1.0 } else { shared as f64 / union as f64 }
}

fn bag_names<'a>(members: &'a [Member<'_>]) -> BTreeMap<&'a str, usize> {
    let mut bag = BTreeMap::new();
    for member in members {
        *bag.entry(member.name.as_str()).or_default() += 1;
    }
    bag
}

pub(crate) fn search(
    db: &RootDatabase,
    query: SimilarQuery,
) -> Result<SimilarBatch, SignatureError> {
    if !query.min_score.is_finite() || !(0.0..=1.0).contains(&query.min_score) {
        return Err("min_score must be finite and between 0 and 1".into());
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
    let context = if let Some(context) = query.context.clone() {
        context
    } else if let SimilarInput::Target(target) = &query.query {
        target.clone()
    } else {
        let mut roots = Vec::new();
        for krate in hir::Crate::all(db).into_iter().filter(|krate| krate.is_workspace_member(db)) {
            let implied = match &query.scope {
                SearchScope::Workspace => true,
                SearchScope::Regions(regions) => regions.iter().any(|(file, _)| {
                    sema.file_to_module_defs(*file).any(|module| module.krate(db) == krate)
                }),
            };
            if implied {
                roots.push(krate.root_module(db));
            }
        }
        if roots.is_empty() {
            return Err(
                "no loaded workspace crate is implied by scope; select at explicitly".into()
            );
        }
        let [module] = roots.as_slice() else {
            return Err(SignatureError::AmbiguousContext {
                choices: roots
                    .iter()
                    .map(|module| signature_search::context_choice(db, *module))
                    .collect(),
            });
        };
        SignatureAnchor {
            file_id: module.definition_source_range(db).file_id.original_file(db).file_id(db),
            range: None,
            context_id: Some(format!("{module:?}")),
        }
    };
    let module = signature_search::context(&sema, &context)?;
    let mut target_source = None;
    let (kind, query_name, members, draft_errors) = match &query.query {
        SimilarInput::Draft(text) => draft(&sema, &context, module, text)?,
        SimilarInput::Target(target) => {
            let range =
                target.range.ok_or("similar target requires a declaration point or range")?;
            let file = sema.parse_guess_edition(target.file_id);
            let node = file
                .syntax()
                .descendants()
                .filter(|node| node.text_range().contains_range(range))
                .filter(|node| ast::Item::can_cast(node.kind()))
                .min_by_key(|node| node.text_range().len())
                .ok_or("target does not select a supported declaration")?;
            let target_module = signature_search::context(&sema, target)?;
            let target_scope =
                sema.signature_scope_at(target_module, file.syntax(), Some(range.start()));
            let (definition, (kind, name, module, source_node)) = target_scope
                .module()
                .declarations(db)
                .into_iter()
                .filter_map(|definition| {
                    declaration(&sema, definition).map(|data| (definition, data))
                })
                .find(|(_, (_, _, _, source_node))| {
                    source_node.as_ref().is_some_and(|source_node| {
                        source_node.text_range() == node.text_range()
                            && sema.hir_file_for(source_node).original_file(db).file_id(db)
                                == target.file_id
                    })
                })
                .ok_or("target is not an active supported type declaration in selected context")?;
            target_source = Some(FileRange { file_id: target.file_id, range: node.text_range() });
            let members = existing_members(&sema, definition, module, &name, source_node.as_ref());
            (kind, name, members, syntax_uncertainty(&sema, source_node.as_ref()))
        }
    };
    let mut coverage=SimilarCoverage {complete:true,warnings:vec!["active configuration only; inactive cfg declarations are outside the semantic universe".into()],..Default::default()};
    for error in draft_errors {
        unknown(&mut coverage, error);
    }
    coverage.query_unresolved = unresolved(&members, &mut coverage);
    let query_names = bag_names(&members);
    let query_tokens = name_tokens(&query_name);
    let crates = signature_search::search_crates(db, query.dependencies);
    let mut modules: Vec<_> = crates.into_iter().flat_map(|krate| krate.modules(db)).collect();
    modules.sort_by_key(|module| format!("{module:?}"));
    modules.reverse();
    let mut bodies: Vec<hir::DefWithBody> = Vec::new();
    let mut seen = FxHashSet::default();
    let mut seen_definitions = FxHashSet::default();
    let mut seen_bodies = FxHashSet::default();
    let mut candidates = Vec::new();
    loop {
        let current = if let Some(module) = modules.pop() {
            module
        } else if let Some(body) = bodies.pop() {
            if !seen_bodies.insert(body) {
                continue;
            }
            if seen_bodies.len() > 100_000 {
                coverage.complete = false;
                coverage.unsearched.push("body traversal budget exhausted".into());
                break;
            }
            modules = body.signature_block_modules(db);
            continue;
        } else {
            break;
        };
        if !seen.insert(current) {
            continue;
        }
        if seen.len() > 100_000 || coverage.examined >= query.max_candidates {
            coverage.complete = false;
            coverage.unsearched.push("semantic traversal budget exhausted".into());
            break;
        }
        if let Err(reason) = current.import_scope_status(db) {
            unknown(&mut coverage, format!("module coverage: {reason:?}"));
        }
        let pending = signature_search::module_bodies(db, current);
        if bodies.len() + pending.len() > 100_000 {
            coverage.complete = false;
            coverage.unsearched.push("pending body traversal budget exhausted".into());
            break;
        }
        bodies.extend(pending);
        let mut definitions = current.declarations(db);
        definitions.sort_by_key(|definition| format!("{definition:?}"));
        for definition in definitions {
            if !seen_definitions.insert(definition) {
                continue;
            }
            let Some((candidate_kind, name, module, node)) = declaration(&sema, definition) else {
                continue;
            };
            if !query
                .kinds
                .as_ref()
                .map_or(candidate_kind == kind, |kinds| kinds.contains(&candidate_kind))
            {
                continue;
            }
            let source = source(&sema, node.as_ref());
            if matches!(&source,CandidateSource::Physical {range,..} if Some(*range)==target_source)
            {
                continue;
            }
            let location = match &source {
                CandidateSource::Physical { range, .. } => Some(*range),
                CandidateSource::Nonphysical { origin, .. } => *origin,
            };
            if matches!(query.scope, SearchScope::Regions(_))
                && !location
                    .is_some_and(|location| signature_search::in_scope(&query.scope, location))
            {
                continue;
            }
            if coverage.examined >= query.max_candidates {
                coverage.complete = false;
                coverage.unsearched.push("semantic candidate enumeration budget exhausted".into());
                break;
            }
            coverage.examined += 1;
            for error in syntax_uncertainty(&sema, node.as_ref()) {
                unknown(&mut coverage, error);
            }
            let candidate_members =
                existing_members(&sema, definition, module, &name, node.as_ref());
            let candidate_unresolved = unresolved(&candidate_members, &mut coverage);
            coverage.candidate_unresolved += candidate_unresolved;
            if matches!(source, CandidateSource::Nonphysical { .. }) {
                coverage.complete = false;
                coverage.unsearched.push(
                    "macro-generated or nonphysical declaration has no guarded syntax projection"
                        .into(),
                );
            }
            let mut used = vec![false; candidate_members.len()];
            let mut shared = Vec::new();
            let mut query_only = Vec::new();
            for (qi, qm) in members.iter().enumerate() {
                let mut found = None;
                for (ci, cm) in candidate_members.iter().enumerate() {
                    if used[ci] || qm.shape != cm.shape {
                        continue;
                    }
                    let evidence = match (&qm.identity, &cm.identity) {
                        (
                            MemberIdentity::Unresolved { normalized: q, .. },
                            MemberIdentity::Unresolved { normalized: c, .. },
                        ) if q == c => Some(SimilarEvidence::UnresolvedText),
                        (MemberIdentity::Resolved(qt), MemberIdentity::Resolved(ct))
                            if qt.len() == ct.len() =>
                        {
                            let mut equal = true;
                            for (q, c) in qt.iter().zip(ct) {
                                match SignaturePattern::of(q.clone()).matches(
                                    db,
                                    c,
                                    hir::ReferencePolicy::Exact,
                                    false,
                                ) {
                                    TypeMatch::Match(_) => {}
                                    TypeMatch::NoMatch => {
                                        equal = false;
                                        break;
                                    }
                                    TypeMatch::Unknown(reason) => {
                                        equal = false;
                                        unknown(
                                            &mut coverage,
                                            format!("type comparison: {reason:?}"),
                                        );
                                        break;
                                    }
                                }
                            }
                            equal.then_some(SimilarEvidence::Semantic)
                        }
                        _ => None,
                    };
                    if let Some(evidence) = evidence {
                        found = Some((ci, evidence));
                        break;
                    }
                }
                if let Some((ci, evidence)) = found {
                    used[ci] = true;
                    shared.push(SimilarShared { query: qi as u32, candidate: ci as u32, evidence });
                } else {
                    query_only.push(qi as u32);
                }
            }
            let score = overlap(members.len(), candidate_members.len(), shared.len());
            if score < query.min_score {
                continue;
            }
            let candidate_only = used
                .iter()
                .enumerate()
                .filter_map(|(index, used)| (!used).then_some(index as u32))
                .collect::<Vec<_>>();
            let relation = match (query_only.is_empty(), candidate_only.is_empty()) {
                (true, true) => SimilarRelation::Equal,
                (true, false) => SimilarRelation::QueryWithinCandidate,
                (false, true) => SimilarRelation::CandidateWithinQuery,
                (false, false) => SimilarRelation::Overlap,
            };
            let candidate_names = bag_names(&candidate_members);
            let name_shared = query_names
                .iter()
                .map(|(name, count)| (*count).min(*candidate_names.get(name).unwrap_or(&0)))
                .sum();
            let name_overlap = overlap(members.len(), candidate_members.len(), name_shared);
            let candidate_tokens = name_tokens(&name);
            let type_token_overlap = overlap(
                query_tokens.len(),
                candidate_tokens.len(),
                query_tokens.intersection(&candidate_tokens).count(),
            );
            let text_matches = shared
                .iter()
                .filter(|shared| matches!(shared.evidence, SimilarEvidence::UnresolvedText))
                .count() as u32;
            coverage.text_matches += text_matches;
            let krate = module.krate(db);
            let visibility = node
                .as_ref()
                .and_then(|node| node.children().find_map(ast::Visibility::cast))
                .map_or_else(|| "private".into(), |it| it.syntax().text().to_string());
            candidates.push(SimilarCandidate {
                id: format!("{krate:?}:{definition:?}"),
                name: name.clone(),
                qualified_name: signature_search::qualified(db, module, &name),
                crate_name: krate
                    .display_name(db)
                    .map_or_else(|| format!("{krate:?}"), |it| it.to_string()),
                crate_instance: format!("{krate:?}"),
                workspace: krate.is_workspace_member(db),
                kind: candidate_kind,
                visibility,
                score,
                relation,
                name_overlap,
                type_token_overlap,
                members: candidate_members.into_iter().map(Member::into_description).collect(),
                shared,
                query_only,
                candidate_only,
                query_unresolved: coverage.query_unresolved,
                candidate_unresolved,
                text_matches,
                source,
            });
        }
    }
    candidates.sort_by(|a, b| {
        b.score
            .total_cmp(&a.score)
            .then_with(|| b.name_overlap.total_cmp(&a.name_overlap))
            .then_with(|| b.type_token_overlap.total_cmp(&a.type_token_overlap))
            .then_with(|| a.qualified_name.cmp(&b.qualified_name))
            .then_with(|| a.id.cmp(&b.id))
    });
    coverage.matched = candidates.len() as u32;
    coverage.unsearched.sort();
    coverage.unsearched.dedup();
    coverage.unknown_reasons.sort();
    Ok(SimilarBatch {
        context_file: context.file_id,
        query: SimilarDeclaration {
            kind,
            members: members.into_iter().map(Member::into_description).collect(),
        },
        candidates,
        coverage,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semantic_member_similarity() {
        let (analysis, position) = crate::fixture::position(
            r#"
//- minicore: sized
$0
struct Atom;
type Alias = Atom;
mod alien { pub struct Atom; }
enum Exact { First(Alias), Second(u32), Third(u32) }
enum Homonym { First(alien::Atom), Second(u32), Third(u32) }
enum Fewer { First(Atom), Second(u32) }
enum Borrowed { First(&'static Atom), Second(u32), Third(u32) }
enum MissingA { First(Missing) }
enum MissingB { Other(Missing) }
struct T;
struct Outer { value: T }
struct RigidA<T> { value: T }
struct RigidB<T> { value: T }
struct Empty;
union Storage { atom: Atom }
trait OuterTrait { fn origin(&self); }
struct Broken {
"#,
        );
        let base = SimilarQuery {
            context: Some(SignatureAnchor {
                file_id: position.file_id,
                range: None,
                context_id: None,
            }),
            query: SimilarInput::Draft("enum Draft { A(Atom), B(u32), C(u32) }".into()),
            scope: SearchScope::Workspace,
            dependencies: DependencyPolicy::Exclude,
            kinds: None,
            min_score: 0.0,
            max_candidates: 1000,
        };
        let run = |query| analysis.sem_similar_types(query).unwrap().unwrap();
        let batch = run(base.clone());
        let find =
            |name: &str| batch.candidates.iter().find(|candidate| candidate.name == name).unwrap();
        assert_eq!(find("Exact").score, 1.0);
        assert_eq!(find("Homonym").score, 0.5);
        assert_eq!(find("Borrowed").score, 0.5);
        assert_eq!(find("Fewer").score, 2.0 / 3.0);
        assert_eq!(find("Fewer").relation, SimilarRelation::CandidateWithinQuery);
        assert!(!batch.coverage.complete);

        let text = analysis.file_text(position.file_id).unwrap();
        let exact = text.find("enum Exact").unwrap() as u32;
        let mut target = base.clone();
        target.context = None;
        target.query = SimilarInput::Target(SignatureAnchor {
            file_id: position.file_id,
            range: Some(syntax::TextRange::empty(exact.into())),
            context_id: None,
        });
        let targeted = run(target);
        assert_eq!(targeted.query.members.len(), 3);
        assert!(targeted.candidates.iter().all(|candidate| candidate.name != "Exact"));
        assert_eq!(
            targeted.candidates.iter().find(|candidate| candidate.name == "Fewer").unwrap().score,
            2.0 / 3.0
        );

        let mut fallback = base.clone();
        fallback.query = SimilarInput::Draft("enum Draft { Renamed(Missing) }".into());
        fallback.min_score = 1.0;
        let fallback = run(fallback);
        assert_eq!(fallback.coverage.query_unresolved, 1);
        assert_eq!(fallback.candidates.len(), 2);
        assert!(fallback.candidates.iter().all(|candidate| candidate.text_matches == 1
            && matches!(candidate.shared[0].evidence, SimilarEvidence::UnresolvedText)));

        let mut rigid = base.clone();
        rigid.query = SimilarInput::Draft("struct Draft<T> { value: T }".into());
        rigid.min_score = 1.0;
        let rigid = run(rigid);
        assert_eq!(rigid.coverage.query_unresolved, 1);
        assert!(rigid.candidates.is_empty());

        let mut own_self = base.clone();
        own_self.context.as_mut().unwrap().range =
            Some(syntax::TextRange::empty((text.find("fn origin").unwrap() as u32).into()));
        own_self.query = SimilarInput::Draft("trait Draft { fn origin(&self); }".into());
        let own_self = run(own_self);
        assert_eq!(own_self.coverage.query_unresolved, 1);
        assert!(
            own_self
                .coverage
                .unknown_reasons
                .iter()
                .any(|(reason, _)| reason.contains("draft-local binder"))
        );

        let mut recovered_existing = base.clone();
        recovered_existing.query = SimilarInput::Draft("struct EmptyDraft;".into());
        recovered_existing.min_score = 1.0;
        let recovered_existing = run(recovered_existing);
        assert!(recovered_existing.candidates.iter().any(|candidate| candidate.name == "Broken"));
        assert!(!recovered_existing.coverage.complete);
        assert!(
            recovered_existing
                .coverage
                .unknown_reasons
                .iter()
                .any(|(reason, _)| reason.contains("recovered existing declaration syntax"))
        );

        let mut malformed = base.clone();
        malformed.query = SimilarInput::Draft("struct Broken {".into());
        assert!(!run(malformed).coverage.complete);
        let mut unevaluated = base.clone();
        unevaluated.query =
            SimilarInput::Draft("#[cfg(disabled)] struct Draft { value: Atom }".into());
        assert!(!run(unevaluated).coverage.complete);

        let mut rigid_target = base.clone();
        rigid_target.query = SimilarInput::Target(SignatureAnchor {
            file_id: position.file_id,
            range: Some(syntax::TextRange::empty(
                (text.find("struct RigidA").unwrap() as u32).into(),
            )),
            context_id: None,
        });
        assert_eq!(
            run(rigid_target)
                .candidates
                .iter()
                .find(|candidate| candidate.name == "RigidB")
                .unwrap()
                .score,
            0.0
        );

        let mut alias = base.clone();
        alias.query = SimilarInput::Draft("type Draft = Atom;".into());
        alias.context = None;
        alias.min_score = 1.0;
        let alias = run(alias);
        assert_eq!(alias.candidates.len(), 1);
        assert_eq!(alias.candidates[0].name, "Alias");

        let (nested_analysis, nested_position) = crate::fixture::position(
            r#"
//- /main.rs
$0
fn main() { #[path="other.rs"] mod nested; }
//- /other.rs
pub struct NestedInOther { pub value: u32 }
pub fn nested_value()->u32 {0}
"#,
        );
        let nested_query = SimilarQuery {
            context: Some(SignatureAnchor {
                file_id: nested_position.file_id,
                range: None,
                context_id: None,
            }),
            query: SimilarInput::Draft("struct Draft { value:u32 }".into()),
            scope: SearchScope::Workspace,
            dependencies: DependencyPolicy::Exclude,
            kinds: None,
            min_score: 1.0,
            max_candidates: 100,
        };
        let nested_batch =
            nested_analysis.sem_similar_types(nested_query.clone()).unwrap().unwrap();
        let nested = nested_batch
            .candidates
            .iter()
            .find(|candidate| candidate.name == "NestedInOther")
            .unwrap();
        let CandidateSource::Physical { range, .. } = nested.source else {
            panic!("expected physical nested module declaration")
        };
        let mut narrow = nested_query;
        narrow.scope = SearchScope::Regions(vec![(range.file_id, None)]);
        let narrow = nested_analysis.sem_similar_types(narrow).unwrap().unwrap();
        assert_eq!(narrow.candidates.len(), 1);
        assert_eq!(narrow.candidates[0].name, "NestedInOther");
        assert!(narrow.coverage.complete);
        let scoped_callable = crate::SignatureQuery {
            context: SignatureAnchor {
                file_id: nested_position.file_id,
                range: None,
                context_id: None,
            },
            inputs: None,
            output: Some(crate::SignaturePatternInput::Type("u32".into())),
            scope: SearchScope::Regions(vec![(range.file_id, None)]),
            dependencies: DependencyPolicy::Exclude,
            references: hir::ReferencePolicy::Exact,
            deref: false,
            include_receiver: true,
            awaited: false,
            max_candidates: 100,
        };
        let scoped_callable =
            nested_analysis.sem_signature_search(scoped_callable).unwrap().unwrap();
        assert_eq!(scoped_callable.candidates.len(), 1);
        assert_eq!(scoped_callable.candidates[0].name, "nested_value");
        assert!(scoped_callable.coverage.complete);

        let mut bound = base;
        bound.max_candidates = 1;
        assert!(!run(bound).coverage.complete);
    }
}
