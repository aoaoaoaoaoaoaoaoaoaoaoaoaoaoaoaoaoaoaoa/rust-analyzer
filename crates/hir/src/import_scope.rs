//! Import binding assessment using rust-analyzer's resolver as authority.
//!
//! Vacancy is an analyzer-reported binding fact, not permission to edit and not
//! an independent proof of rustc-equivalent absence or macro behavior.

use hir_def::{
    ModuleDefId,
    nameres::{
        diagnostics::DefDiagnosticKind,
        import_scope::{ImportPathResolution, resolve_import_path},
    },
    per_ns::PerNs,
    resolver::HasResolver,
};
use hir_expand::{
    MacroCallId,
    mod_path::{ModPath, PathKind},
    name::{AsName, Name},
};
use span::SyntaxContext;
use syntax::{
    SourceFile,
    ast::{self, HasModuleItem as _, HasName as _},
};

use crate::{ItemInNs, Module, db::HirDatabase};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportBindingConflict {
    DifferentIdentity,
    Inaccessible,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportBindingUnknown {
    InvalidSyntax,
    UnsupportedItem,
    UnsupportedPath,
    UnresolvedPath,
    IncompleteResolution,
    Diagnostics,
    OpaqueMacro,
    MacroExpansion,
    WorkLimit,
    PartialAvailability,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportBindingAssessment {
    AlreadyAvailable {
        items: Vec<ItemInNs>,
    },
    /// Necessary binding availability only; the caller owns edit-impact checks.
    Vacant {
        name: Name,
        items: Vec<ItemInNs>,
    },
    Conflict(ImportBindingConflict),
    Unknown(ImportBindingUnknown),
}

impl Module {
    /// Local provider diagnostics and expansion facts, not a transitive audit of
    /// dependency crates, body macros, or compiler completeness.
    pub fn import_scope_status(self, db: &dyn HirDatabase) -> Result<(), ImportBindingUnknown> {
        let map = self.id.def_map(db);
        for (index, diagnostic) in map
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.in_module == self.id)
            .enumerate()
        {
            if index >= 4096 {
                return Err(ImportBindingUnknown::WorkLimit);
            }
            if !matches!(diagnostic.kind, DefDiagnosticKind::UnconfiguredCode { .. }) {
                return Err(ImportBindingUnknown::Diagnostics);
            }
        }
        let Some(file) = self.definition_source_file_id(db).file_id() else {
            return Err(ImportBindingUnknown::OpaqueMacro);
        };
        if !file.parse(db).errors().is_empty() {
            return Err(ImportBindingUnknown::InvalidSyntax);
        }
        for (index, call) in map[self.id].scope.all_macro_calls().enumerate() {
            if index >= 4096 {
                return Err(ImportBindingUnknown::WorkLimit);
            }
            if call
                .parse_macro_expansion_error(db)
                .is_some_and(|error| error.err.is_some() || !error.value.is_empty())
            {
                return Err(ImportBindingUnknown::MacroExpansion);
            }
        }
        Ok(())
    }

    /// Actual item collector calls. Body calls are not included.
    pub fn import_scope_macro_calls(self, db: &dyn HirDatabase) -> Vec<MacroCallId> {
        self.id.def_map(db)[self.id].scope.all_macro_calls().collect()
    }

    /// Assesses current binding identities with existing import-mode and normal
    /// lookup queries. It intentionally inherits the provider's resolution limits.
    pub fn assess_import_binding(
        self,
        db: &dyn HirDatabase,
        path: &str,
        alias: Option<&str>,
    ) -> ImportBindingAssessment {
        use ImportBindingAssessment::{Conflict, Unknown};
        let (path, name) = match parse_request(db, self, path, alias) {
            Ok(request) => request,
            Err(reason) => return Unknown(reason),
        };
        if let Err(reason) = self.import_scope_status(db) {
            return Unknown(reason);
        }
        let mut target = PerNs::none();
        // Ask the same resolver about prefix accessibility, rather than deriving
        // visibility or following import provenance independently.
        for index in 0..path.segments().len() {
            let prefix =
                ModPath::from_segments(path.kind, path.segments()[..=index].iter().cloned());
            let resolution = resolve_import_path(db, self.id, &prefix);
            target = match resolution {
                ImportPathResolution::Resolved(resolved) => resolved,
                ImportPathResolution::Indeterminate => {
                    return Unknown(ImportBindingUnknown::IncompleteResolution);
                }
                ImportPathResolution::Partial | ImportPathResolution::Unresolved => {
                    return Unknown(ImportBindingUnknown::UnresolvedPath);
                }
            };
            if target.types.is_some_and(|item| !item.vis.is_visible_from(db, self.id))
                || (index + 1 == path.segments().len()
                    && target.values.is_some_and(|item| !item.vis.is_visible_from(db, self.id)))
            {
                return Conflict(ImportBindingConflict::Inaccessible);
            }
        }
        if target.macros.is_some()
            || target.types.is_some_and(|item| matches!(item.def, ModuleDefId::TraitId(_)))
        {
            return Unknown(ImportBindingUnknown::UnsupportedItem);
        }
        let existing = self.id.resolver(db).resolve_module_path_in_items(
            db,
            &ModPath::from_segments(PathKind::Plain, [name.clone()]),
        );
        let mut items = Vec::new();
        let mut available = 0;
        for (introduced, current, types) in [
            (target.types.map(|item| item.def), existing.types.map(|item| item.def), true),
            (target.values.map(|item| item.def), existing.values.map(|item| item.def), false),
        ] {
            let Some(introduced) = introduced else { continue };
            if let Some(current) = current {
                if current != introduced {
                    return Conflict(ImportBindingConflict::DifferentIdentity);
                }
                available += 1;
            }
            items.push(if types {
                ItemInNs::Types(introduced.into())
            } else {
                ItemInNs::Values(introduced.into())
            });
        }
        if items.is_empty() {
            Unknown(ImportBindingUnknown::UnresolvedPath)
        } else if available == items.len() {
            ImportBindingAssessment::AlreadyAvailable { items }
        } else if available == 0 {
            ImportBindingAssessment::Vacant { name, items }
        } else {
            Unknown(ImportBindingUnknown::PartialAvailability)
        }
    }
}

fn parse_request(
    db: &dyn HirDatabase,
    module: Module,
    path: &str,
    alias: Option<&str>,
) -> Result<(ModPath, Name), ImportBindingUnknown> {
    if path.len() > 8192 || alias.is_some_and(|alias| alias.len() > 256) {
        return Err(ImportBindingUnknown::WorkLimit);
    }
    let text = match alias {
        Some(alias) => format!("use {path} as {alias};"),
        None => format!("use {path};"),
    };
    let edition = module.krate(db).edition(db);
    let parsed = SourceFile::parse(&text, edition);
    if !parsed.errors().is_empty() {
        return Err(ImportBindingUnknown::InvalidSyntax);
    }
    let file = parsed.tree();
    let mut items = file.items();
    let Some(ast::Item::Use(use_)) = items.next() else {
        return Err(ImportBindingUnknown::InvalidSyntax);
    };
    if items.next().is_some() {
        return Err(ImportBindingUnknown::InvalidSyntax);
    }
    let tree = use_.use_tree().ok_or(ImportBindingUnknown::InvalidSyntax)?;
    if tree.star_token().is_some() || tree.use_tree_list().is_some() {
        return Err(ImportBindingUnknown::UnsupportedItem);
    }
    let rename = tree.rename();
    if rename.is_some() != alias.is_some() {
        return Err(ImportBindingUnknown::InvalidSyntax);
    }
    if rename.as_ref().is_some_and(|rename| rename.underscore_token().is_some()) {
        return Err(ImportBindingUnknown::UnsupportedItem);
    }
    let ast_path = tree.path().ok_or(ImportBindingUnknown::InvalidSyntax)?;
    if ast_path
        .segment()
        .and_then(|segment| segment.kind())
        .is_some_and(|kind| matches!(kind, ast::PathSegmentKind::SelfKw))
    {
        return Err(ImportBindingUnknown::UnsupportedPath);
    }
    let path = ModPath::from_src(db, ast_path, &mut |_| SyntaxContext::root(edition))
        .ok_or(ImportBindingUnknown::UnsupportedPath)?;
    if path.segments().is_empty() || path.segments().len() > 64 {
        return Err(ImportBindingUnknown::UnsupportedPath);
    }
    let name = rename
        .and_then(|rename| rename.name())
        .map(|name| name.as_name())
        .or_else(|| path.segments().last().cloned())
        .ok_or(ImportBindingUnknown::UnsupportedPath)?;
    Ok((path, name))
}

#[cfg(test)]
mod tests {
    use base_db::{
        CrateGraphBuilder, CratesMap, FileSourceRootInput, FileText, Nonce, SourceDatabase,
        SourceRoot, SourceRootId, SourceRootInput, set_all_crates_with_durability,
    };
    use salsa::Durability;
    use test_fixture::WithFixture;
    use triomphe::Arc;

    use super::*;

    // HIR has no fixture database of its own. This is only input storage; every
    // compiler query remains the ordinary SourceDatabase/HirDatabase query.
    #[salsa::db]
    #[derive(Clone)]
    struct TestDB {
        storage: salsa::Storage<Self>,
        files: Arc<base_db::Files>,
        crates: Arc<CratesMap>,
        nonce: Nonce,
    }

    impl std::fmt::Debug for TestDB {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.debug_struct("TestDB").finish()
        }
    }

    impl Default for TestDB {
        fn default() -> Self {
            let mut db = Self {
                storage: Default::default(),
                files: Default::default(),
                crates: Default::default(),
                nonce: Nonce::new(),
            };
            hir_def::set_expand_proc_attr_macros(&mut db, true);
            set_all_crates_with_durability(&mut db, std::iter::empty(), Durability::HIGH);
            _ = base_db::LibraryRoots::builder(Default::default())
                .durability(Durability::MEDIUM)
                .new(&db);
            _ = base_db::LocalRoots::builder(Default::default())
                .durability(Durability::MEDIUM)
                .new(&db);
            CrateGraphBuilder::default().set_in_db(&mut db);
            db
        }
    }

    #[salsa::db]
    impl salsa::Database for TestDB {}

    #[salsa::db]
    impl SourceDatabase for TestDB {
        fn file_text(&self, file: base_db::FileId) -> FileText {
            self.files.file_text(file)
        }
        fn set_file_text(&mut self, file: base_db::FileId, text: &str) {
            self.files.clone().set_file_text(self, file, text);
        }
        fn set_file_text_with_durability(
            &mut self,
            file: base_db::FileId,
            text: &str,
            durability: Durability,
        ) {
            self.files.clone().set_file_text_with_durability(self, file, text, durability);
        }
        fn source_root(&self, root: SourceRootId) -> SourceRootInput {
            self.files.source_root(root)
        }
        fn set_source_root_with_durability(
            &mut self,
            root: SourceRootId,
            source: Arc<SourceRoot>,
            durability: Durability,
        ) {
            self.files.clone().set_source_root_with_durability(self, root, source, durability);
        }
        fn file_source_root(&self, file: base_db::FileId) -> FileSourceRootInput {
            self.files.file_source_root(self, file)
        }
        fn set_file_source_root_with_durability(
            &mut self,
            file: base_db::FileId,
            root: SourceRootId,
            durability: Durability,
        ) {
            self.files.clone().set_file_source_root_with_durability(self, file, root, durability);
        }
        fn crates_map(&self) -> Arc<CratesMap> {
            self.crates.clone()
        }
        fn nonce_and_revision(&self) -> (Nonce, salsa::Revision) {
            (self.nonce, salsa::plumbing::ZalsaDatabase::zalsa(self).current_revision())
        }
        fn line_column(&self, _: base_db::FileId, _: syntax::TextSize) -> Result<(u32, u32), ()> {
            Err(())
        }
    }

    fn assess_in(
        fixture: &str,
        child: Option<&str>,
        path: &str,
        alias: Option<&str>,
    ) -> ImportBindingAssessment {
        let db = TestDB::with_files(fixture);
        let krate = base_db::all_crates(&db)
            .iter()
            .copied()
            .find(|krate| {
                krate
                    .extra_data(&db)
                    .display_name
                    .as_ref()
                    .is_some_and(|name| name.canonical_name().as_str() == "ra_test_fixture")
            })
            .unwrap();
        let map = hir_def::nameres::crate_def_map(&db, krate);
        let module = child.map_or(map.root, |child| map[map.root].children[&Name::new_root(child)]);
        Module { id: module }.assess_import_binding(&db, path, alias)
    }

    fn assess(fixture: &str, path: &str, alias: Option<&str>) -> ImportBindingAssessment {
        assess_in(fixture, None, path, alias)
    }

    #[test]
    fn glob_bindings_and_new_aliases_preserve_namespaces() {
        assert!(matches!(
            assess("enum E { Variant } use E::*;", "E::Variant", None),
            ImportBindingAssessment::AlreadyAvailable { .. }
        ));
        assert!(matches!(assess("mod api { pub struct Token(u8); }", "api::Token", None),
            ImportBindingAssessment::Vacant { items, .. } if items.len() == 1));
        let fixture = "mod api { pub struct Known; pub struct Fresh {} } use api::*;";
        assert!(matches!(assess(fixture, "api::Known", None),
            ImportBindingAssessment::AlreadyAvailable { items } if items.len() == 2));
        assert!(matches!(assess(fixture, "api /* comment */ :: Fresh", Some("r#Alias")),
            ImportBindingAssessment::Vacant { name, items } if name.as_str() == "Alias" && items.len() == 1));
        assert!(matches!(
            assess(fixture, "api::Fresh", Some("Known")),
            ImportBindingAssessment::Conflict(ImportBindingConflict::DifferentIdentity)
        ));
        let prelude = r#"
//- minicore: sized
//- /lib.rs crate:ra_test_fixture
mod api { pub struct Fresh; }
mod client {}
"#;
        assert!(matches!(assess_in(prelude, Some("client"), "crate::api::Fresh", None),
            ImportBindingAssessment::Vacant { items, .. } if items.len() == 2));
    }

    #[test]
    fn missing_and_unsupported_requests_do_not_claim_vacancy() {
        for (fixture, path, alias) in [
            ("mod api {}", "api::Missing", None),
            ("mod api { pub trait Trait {} }", "api::Trait", None),
            ("mod api { pub struct X; }", "api::X", Some("_")),
            ("mod api { pub struct X; }", "api::*", None),
            ("mod api { pub struct X; }", "api::X; use api::X", None),
        ] {
            assert!(matches!(assess(fixture, path, alias), ImportBindingAssessment::Unknown(_)));
        }
        let dual_namespace = "mod api { pub struct X {} pub const X: u8 = 0; }";
        assert!(
            matches!(assess(dual_namespace, "api::X", None), ImportBindingAssessment::Vacant { items, .. } if items.len() == 2)
        );
        let partial = "mod api { pub struct X {} pub const VALUE: u8 = 0; pub use self::VALUE as X; } use api::VALUE as X;";
        assert!(matches!(
            assess(partial, "api::X", None),
            ImportBindingAssessment::Unknown(ImportBindingUnknown::PartialAvailability)
        ));
        assert!(matches!(
            assess("mod api { struct Private {} }", "api::Private", None),
            ImportBindingAssessment::Unknown(ImportBindingUnknown::UnresolvedPath)
        ));
    }
}
