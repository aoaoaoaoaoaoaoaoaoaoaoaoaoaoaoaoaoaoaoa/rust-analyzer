//! Signature queries consume the same lowered types and proof engine as the IDE.

use std::cell::OnceCell;

use hir_def::{
    ExpressionStoreOwnerId, LoweringMode, expr_store::lower::lower_type_ref, type_ref::TypeRef,
};
use hir_ty::{
    LifetimeElisionKind, LifetimeLoweringMode, Span, TyLoweringContext, TyLoweringInferVarsCtx,
    next_solver::{
        AliasTy, Clause, ClauseKind, Const, DbInterner, EarlyBinder, GenericArgKind, Region, Ty,
        TyKind, TypingMode,
        infer::{
            DbInternerInferExt,
            traits::{Obligation, ObligationCause},
        },
        util::BottomUpFolder,
    },
    traits::structurally_normalize_ty,
};
use rustc_hash::FxHashSet;
use rustc_type_ir::{
    AliasTyKind, PredicatePolarity, TypeFoldable, TypeVisitableExt,
    inherent::{IntoKind, Term as _, Ty as _},
};
use syntax::ast::HasModuleItem;
use syntax::{AstNode, SourceFile, ast};

use crate::{DefWithBody, Module, SemanticsScope, Type, TypeOwnerId, db::HirDatabase};

fn signature_typing_mode<'db>() -> TypingMode<'db> {
    // Signature evidence observes declared opaque contracts, not hidden implementations.
    // PostAnalysis reveals hidden types even for non-auto traits and Deref; rustc's analysis
    // mode keeps them rigid. Use the same policy for proof, projection and autoderef.
    // https://github.com/rust-lang/rust/blob/1.89.0/compiler/rustc_next_trait_solver/src/solve/normalizes_to/opaque_types.rs
    TypingMode::non_body_analysis()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReferencePolicy {
    Outer,
    Exact,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeShape {
    Concrete,
    Generic,
    Opaque,
    Dynamic,
    Mixed,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeMatchUnknown {
    UnresolvedType,
    UnsupportedStructure,
    TraitNotProven,
    AssociatedTypeNotProven,
    WorkLimit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeMatchEvidence {
    pub outer_references: u32,
    pub deref_steps: u32,
    pub wildcard: bool,
    pub trait_proof: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeMatch {
    Match(TypeMatchEvidence),
    NoMatch,
    Unknown(TypeMatchUnknown),
}

#[derive(Debug, Clone)]
pub struct SignaturePattern<'db> {
    kind: PatternKind<'db>,
}

#[derive(Debug, Clone)]
enum PatternKind<'db> {
    Identity { ty: Type<'db>, wildcards: FxHashSet<Ty<'db>> },
    Bounds { clauses: Vec<Clause<'db>>, marker: Ty<'db>, wildcards: FxHashSet<Ty<'db>> },
}

struct QueryHoles<'a, 'db> {
    interner: DbInterner<'db>,
    holes: FxHashSet<Ty<'db>>,
    store: &'a hir_def::expr_store::ExpressionStore,
}

impl<'db> TyLoweringInferVarsCtx<'db> for QueryHoles<'_, 'db> {
    fn next_ty_var(&mut self, span: Span) -> Ty<'db> {
        if !matches!(span,Span::TypeRefId(id) if matches!(self.store[id],TypeRef::Placeholder)) {
            return self.interner.default_types().types.error;
        }
        // FreshTy(0) is reserved by RA for its dyn-trait dummy Self; these never reach a solver.
        let ty = Ty::new_fresh(self.interner, self.holes.len() as u32 + 2);
        self.holes.insert(ty);
        ty
    }
    fn next_const_var(&mut self, _: Span) -> Const<'db> {
        self.interner.default_types().consts.error
    }
    fn next_region_var(&mut self, _: Span) -> Region<'db> {
        self.interner.default_types().regions.erased
    }
}

impl<'db> SemanticsScope<'db> {
    pub fn signature_pattern(
        &self,
        text: &str,
        bounds: bool,
    ) -> Result<SignaturePattern<'db>, String> {
        if text.len() > 16_384 {
            return Err("type query exceeds 16384 bytes".into());
        }
        let wrapped = if bounds {
            format!("type __Query = dyn {text};")
        } else {
            format!("type __Query = {text};")
        };
        let parsed = SourceFile::parse(&wrapped, self.krate().edition(self.db));
        if !parsed.errors().is_empty() {
            return Err("expected one valid Rust type or bounds expression".into());
        }
        let alias = parsed
            .tree()
            .items()
            .next()
            .and_then(|item| match item {
                ast::Item::TypeAlias(alias) => Some(alias),
                _ => None,
            })
            .ok_or("expected a type query")?;
        if parsed.tree().items().count() != 1 {
            return Err("type query must contain exactly one type".into());
        }
        let ast_ty = alias.ty().ok_or("missing query type")?;
        if bounds
            && ast_ty.syntax().descendants().filter_map(ast::TypeBound::cast).any(|bound| {
                bound.question_mark_token().is_some()
                    || bound.const_token().is_some()
                    || bound.async_token().is_some()
                    || bound.use_token().is_some()
                    || bound.lifetime().is_some()
                    || bound.for_binder().is_some()
                    || bound
                        .syntax()
                        .children_with_tokens()
                        .any(|token| token.kind() == syntax::T![!])
            })
        {
            return Err("modified, negative, lifetime, capture and higher-ranked bounds are unsupported in signature queries".into());
        }
        if ast_ty.syntax().descendants().any(|node| {
            ast::MacroType::can_cast(node.kind()) || ast::ImplTraitType::can_cast(node.kind())
        }) {
            return Err("type macros and new opaque impl Trait identities are unsupported in query syntax; use an existing type anchor or implements bounds".into());
        }
        let (store, _, type_ref) = lower_type_ref(
            self.db,
            self.module().id,
            hir_expand::InFile::new(self.file_id(), Some(ast_ty)),
        );
        let mut holes = QueryHoles {
            interner: DbInterner::new_with(self.db, self.krate().id),
            holes: FxHashSet::default(),
            store: &store,
        };
        let generics = OnceCell::new();
        let resolver = self.resolver();
        let mut lower = match resolver.generic_def() {
            Some(def) => TyLoweringContext::new(
                self.db,
                resolver,
                &store,
                resolver.expression_store_owner().unwrap_or(ExpressionStoreOwnerId::Signature(def)),
                def,
                &generics,
                LifetimeElisionKind::Infer,
                LifetimeLoweringMode::Bound,
            ),
            None => TyLoweringContext::new_in_module(self.db, resolver, &store, &generics),
        }
        .with_interning_mode(LoweringMode::Ide)
        .with_infer_vars_behavior(Some(&mut holes));
        if bounds {
            let TypeRef::DynTrait(bounds) = &store[type_ref] else {
                return Err("expected trait bounds".into());
            };
            let marker = Ty::new_fresh(DbInterner::new_with(self.db, self.krate().id), 1);
            let clauses = lower.lower_query_bounds(bounds, marker);
            if lower.has_diagnostics()
                || clauses.iter().any(hir_ty::next_solver::references_non_lt_error)
            {
                return Err("unresolved or unsupported names in trait bounds".into());
            }
            if clauses.is_empty() {
                return Err("bounds produce no supported trait obligations".into());
            }
            drop(lower);
            Ok(SignaturePattern {
                kind: PatternKind::Bounds { clauses, marker, wildcards: holes.holes },
            })
        } else {
            let ty = lower.lower_ty(type_ref);
            if lower.has_diagnostics() || ty.references_non_lt_error() {
                return Err("unresolved or unsupported names in type pattern".into());
            }
            drop(lower);
            let owner = resolver
                .generic_def()
                .map_or(TypeOwnerId::NoParams(self.krate().id), TypeOwnerId::GenericDefId);
            Ok(SignaturePattern {
                kind: PatternKind::Identity {
                    ty: Type { owner, ty: EarlyBinder::bind(ty) },
                    wildcards: holes.holes,
                },
            })
        }
    }
}

impl<'db> SignaturePattern<'db> {
    pub fn of(ty: Type<'db>) -> Self {
        Self { kind: PatternKind::Identity { ty, wildcards: FxHashSet::default() } }
    }

    pub fn resolved_type(&self) -> Option<&Type<'db>> {
        match &self.kind {
            PatternKind::Identity { ty, wildcards } if wildcards.is_empty() => Some(ty),
            _ => None,
        }
    }

    pub fn matches(
        &self,
        db: &'db dyn HirDatabase,
        actual: &Type<'db>,
        references: ReferencePolicy,
        deref: bool,
    ) -> TypeMatch {
        if actual.contains_unknown() {
            return TypeMatch::Unknown(TypeMatchUnknown::UnresolvedType);
        }
        if let PatternKind::Bounds { clauses, marker, wildcards } = &self.kind {
            return bounds_match(db, actual, clauses, *marker, wildcards);
        }
        let PatternKind::Identity { ty, wildcards } = &self.kind else { unreachable!() };
        let mut unknown = None;
        let chain: Box<dyn Iterator<Item = Type<'db>> + '_> = if deref {
            Box::new(actual.signature_autoderef(db))
        } else {
            Box::new(std::iter::once(actual.clone()))
        };
        let query = normalize_identity(db, ty, wildcards);
        for (steps, candidate) in chain.enumerate() {
            if steps >= 64 {
                return TypeMatch::Unknown(TypeMatchUnknown::WorkLimit);
            }
            let normalized = normalize_identity(db, &candidate, &FxHashSet::default());
            let mut candidate = normalized.ty.skip_binder();
            let mut removed = 0;
            if references == ReferencePolicy::Outer
                && !matches!(query.ty.skip_binder().kind(), TyKind::Ref(..))
            {
                while let TyKind::Ref(_, inner, _) = candidate.kind() {
                    candidate = inner;
                    removed += 1;
                }
            }
            match structural_match(candidate, query.ty.skip_binder(), wildcards, 0) {
                Relation::Yes => {
                    return TypeMatch::Match(TypeMatchEvidence {
                        outer_references: removed,
                        deref_steps: steps as u32,
                        wildcard: !wildcards.is_empty(),
                        trait_proof: false,
                    });
                }
                Relation::No => {}
                Relation::Unknown(reason) => unknown = Some(reason),
            }
        }
        unknown.map_or(TypeMatch::NoMatch, TypeMatch::Unknown)
    }
}

impl<'db> Type<'db> {
    pub fn signature_autoderef(
        &self,
        db: &'db dyn HirDatabase,
    ) -> impl Iterator<Item = Type<'db>> + use<'db> {
        let interner = DbInterner::new_no_crate(db);
        let canonical = hir_ty::replace_errors_with_variables(interner, &self.ty.skip_binder());
        let owner = self.owner;
        hir_ty::autoderef::autoderef_in_mode(
            db,
            self.param_env(db),
            canonical,
            signature_typing_mode(),
        )
        .map(move |ty| Type { owner, ty: EarlyBinder::bind(ty) })
    }

    pub fn signature_future_output(&self, db: &'db dyn HirDatabase) -> Option<Type<'db>> {
        let env = self.param_env(db);
        let output = hir_def::lang_item::lang_items(db, env.krate).FutureOutput?;
        let interner = DbInterner::new_with(db, env.krate);
        let projection = Ty::new_projection(interner, output.into(), [self.ty.skip_binder()]);
        let infcx = interner.infer_ctxt().build(signature_typing_mode());
        let ty = structurally_normalize_ty(&infcx, projection, env.param_env);
        if ty == projection || ty.references_non_lt_error() { None } else { Some(self.derived(ty)) }
    }
    pub fn signature_shape(&self, db: &dyn HirDatabase) -> TypeShape {
        if self.contains_unknown() || self.ty.skip_binder().has_non_region_infer() {
            return TypeShape::Unknown;
        }
        let (mut generic, mut opaque, mut dynamic) =
            (self.ty.skip_binder().has_non_region_param(), false, false);
        self.walk(db, |ty| match ty.ty.skip_binder().kind() {
            TyKind::Param(_) => generic = true,
            TyKind::Dynamic(..) => dynamic = true,
            TyKind::Alias(AliasTy { kind: AliasTyKind::Opaque { .. }, .. }) => opaque = true,
            _ => {}
        });
        match (generic, opaque, dynamic) {
            (false, false, false) => TypeShape::Concrete,
            (true, false, false) => TypeShape::Generic,
            (false, true, false) => TypeShape::Opaque,
            (false, false, true) => TypeShape::Dynamic,
            _ => TypeShape::Mixed,
        }
    }
}

fn normalize_identity<'db>(
    db: &'db dyn HirDatabase,
    ty: &Type<'db>,
    holes: &FxHashSet<Ty<'db>>,
) -> Type<'db> {
    let env = ty.param_env(db);
    let interner = DbInterner::new_with(db, env.krate);
    let infcx = interner.infer_ctxt().build(signature_typing_mode());
    let normalized = ty.ty.skip_binder().fold_with(&mut BottomUpFolder {
        interner,
        ty_op: |inner| {
            if !inner.has_non_region_infer()
                && !holes.contains(&inner)
                && matches!(
                    inner.kind(),
                    TyKind::Alias(AliasTy { kind: AliasTyKind::Projection { .. }, .. })
                )
            {
                structurally_normalize_ty(&infcx, inner, env.param_env)
            } else {
                inner
            }
        },
        lt_op: |lt| lt,
        ct_op: |ct| ct,
    });
    ty.derived(normalized)
}

impl DefWithBody {
    pub fn signature_block_modules(self, db: &dyn HirDatabase) -> Vec<Module> {
        let Ok(def) = hir_def::DefWithBodyId::try_from(self) else {
            return Vec::new();
        };
        hir_def::expr_store::Body::of(db, def)
            .blocks(db)
            .flat_map(|(_, map)| map.modules().map(|(id, _)| Module { id }))
            .collect()
    }
}

#[derive(Clone, Copy)]
enum Relation {
    Yes,
    No,
    Unknown(TypeMatchUnknown),
}

fn structural_match<'db>(
    actual: Ty<'db>,
    query: Ty<'db>,
    holes: &FxHashSet<Ty<'db>>,
    depth: u32,
) -> Relation {
    if depth > 64 {
        return Relation::Unknown(TypeMatchUnknown::WorkLimit);
    }
    if actual.references_non_lt_error() {
        return Relation::Unknown(TypeMatchUnknown::UnresolvedType);
    }
    if holes.contains(&query) {
        return Relation::Yes;
    }
    if actual == query && !actual.has_non_region_infer() {
        return Relation::Yes;
    }
    let recur = |a, q| structural_match(a, q, holes, depth + 1);
    match (actual.kind(), query.kind()) {
        (TyKind::Ref(_, a, am), TyKind::Ref(_, q, qm))
        | (TyKind::RawPtr(a, am), TyKind::RawPtr(q, qm)) => {
            if am == qm {
                recur(a, q)
            } else {
                Relation::No
            }
        }
        (TyKind::Slice(a), TyKind::Slice(q)) => recur(a, q),
        (TyKind::Tuple(a), TyKind::Tuple(q)) => {
            combine(a.iter().zip(q.iter()).map(|(a, q)| recur(a, q)), a.len() == q.len())
        }
        (TyKind::Array(a, ac), TyKind::Array(q, qc)) => {
            if ac == qc {
                recur(a, q)
            } else if ac.has_non_region_infer()
                || qc.has_non_region_infer()
                || matches!(ac.kind(), hir_ty::next_solver::ConstKind::Unevaluated(_))
                || matches!(qc.kind(), hir_ty::next_solver::ConstKind::Unevaluated(_))
            {
                Relation::Unknown(TypeMatchUnknown::UnsupportedStructure)
            } else {
                Relation::No
            }
        }
        (TyKind::Adt(a, aa), TyKind::Adt(q, qa)) => {
            if a != q || aa.len() != qa.len() {
                return Relation::No;
            }
            combine(
                aa.iter().zip(qa.iter()).map(|(a, q)| match (a.kind(), q.kind()) {
                    (GenericArgKind::Type(a), GenericArgKind::Type(q)) => recur(a, q),
                    (GenericArgKind::Lifetime(_), GenericArgKind::Lifetime(_)) => Relation::Yes,
                    (GenericArgKind::Const(a), GenericArgKind::Const(q)) if a == q => Relation::Yes,
                    (GenericArgKind::Const(_), GenericArgKind::Const(_)) => {
                        Relation::Unknown(TypeMatchUnknown::UnsupportedStructure)
                    }
                    _ => Relation::No,
                }),
                true,
            )
        }
        (TyKind::Param(a), TyKind::Param(q)) => {
            if a.id == q.id {
                Relation::Yes
            } else {
                Relation::No
            }
        }
        (TyKind::Alias(AliasTy { kind: AliasTyKind::Projection { .. }, .. }), _)
        | (_, TyKind::Alias(AliasTy { kind: AliasTyKind::Projection { .. }, .. })) => {
            Relation::Unknown(TypeMatchUnknown::AssociatedTypeNotProven)
        }
        (TyKind::Infer(_), _) | (_, TyKind::Infer(_)) => {
            Relation::Unknown(TypeMatchUnknown::UnresolvedType)
        }
        (TyKind::Dynamic(..), TyKind::Dynamic(..)) | (TyKind::FnPtr(..), TyKind::FnPtr(..)) => {
            Relation::Unknown(TypeMatchUnknown::UnsupportedStructure)
        }
        _ => Relation::No,
    }
}

fn combine(relations: impl Iterator<Item = Relation>, same_arity: bool) -> Relation {
    if !same_arity {
        return Relation::No;
    }
    let mut unknown = None;
    for relation in relations {
        match relation {
            Relation::No => return Relation::No,
            Relation::Unknown(reason) => unknown = Some(reason),
            Relation::Yes => {}
        }
    }
    unknown.map_or(Relation::Yes, Relation::Unknown)
}

fn bounds_match<'db>(
    db: &'db dyn HirDatabase,
    actual: &Type<'db>,
    clauses: &[Clause<'db>],
    marker: Ty<'db>,
    holes: &FxHashSet<Ty<'db>>,
) -> TypeMatch {
    let env = actual.param_env(db);
    let interner = DbInterner::new_with(db, env.krate);
    let infcx = interner.infer_ctxt().build(signature_typing_mode());
    let mut unknown = None;
    for clause in clauses {
        let clause = clause.fold_with(&mut BottomUpFolder {
            interner,
            ty_op: |ty| if ty == marker { actual.ty.skip_binder() } else { ty },
            lt_op: |lt| lt,
            ct_op: |ct| ct,
        });
        let clause = interner.instantiate_bound_regions_with_erased(clause.kind());
        match clause {
            ClauseKind::Trait(predicate) => {
                if predicate.polarity != PredicatePolarity::Positive {
                    unknown = Some(TypeMatchUnknown::UnsupportedStructure);
                    continue;
                }
                if predicate.trait_ref.args.has_non_region_infer() {
                    unknown = Some(TypeMatchUnknown::UnsupportedStructure);
                    continue;
                }
                let obligation = Obligation::new(
                    interner,
                    ObligationCause::dummy(),
                    env.param_env,
                    predicate.trait_ref,
                );
                if !infcx.predicate_must_hold_modulo_regions(&obligation) {
                    unknown = Some(TypeMatchUnknown::TraitNotProven);
                }
            }
            ClauseKind::Projection(projection) => {
                let Some(expected) = projection.term.as_type() else {
                    unknown = Some(TypeMatchUnknown::UnsupportedStructure);
                    continue;
                };
                if projection.projection_term.args.has_non_region_infer() {
                    unknown = Some(TypeMatchUnknown::UnsupportedStructure);
                    continue;
                }
                let rustc_type_ir::AliasTermKind::ProjectionTy { def_id } =
                    projection.projection_term.kind(interner)
                else {
                    unknown = Some(TypeMatchUnknown::UnsupportedStructure);
                    continue;
                };
                if !crate::GenericDef::TypeAlias(crate::TypeAlias::from(def_id.0))
                    .params(db)
                    .is_empty()
                {
                    unknown = Some(TypeMatchUnknown::UnsupportedStructure);
                    continue;
                }
                let alias = AliasTy::new_from_args(
                    interner,
                    AliasTyKind::Projection { def_id },
                    projection.projection_term.args,
                );
                let normalized = structurally_normalize_ty(
                    &infcx,
                    Ty::new_alias(interner, alias),
                    env.param_env,
                );
                match structural_match(normalized, expected, holes, 0) {
                    Relation::Yes => {}
                    Relation::No => return TypeMatch::NoMatch,
                    Relation::Unknown(reason) => unknown = Some(reason),
                }
            }
            _ => unknown = Some(TypeMatchUnknown::UnsupportedStructure),
        }
    }
    unknown.map_or_else(
        || {
            TypeMatch::Match(TypeMatchEvidence {
                outer_references: 0,
                deref_steps: 0,
                wildcard: !holes.is_empty(),
                trait_proof: true,
            })
        },
        TypeMatch::Unknown,
    )
}
