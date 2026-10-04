//! Import assessment against rust-analyzer's active semantic model.
//!
//! Reported binding availability and edit impact are separate checks. A private,
//! non-trait import is checked against its lexical descendants and their reported
//! macro expansions. Macro definitions are excluded because their expansion sites
//! can escape the subtree. This is not an independent validation of the analyzer's
//! resolver or its agreement with rustc. No second analysis database is used.
//!
//! The visibility argument follows rustc's `update_local_resolution` and
//! `resolve_glob_import`: private import visibility bounds propagation.
//! <https://github.com/rust-lang/rust/blob/18ed059b1465ce6195154de3250a668f1dd3b1fa/compiler/rustc_resolve/src/imports.rs>

use hir::{ImportBindingAssessment, ItemInNs, Module, PathResolution, Semantics};
use ide_db::{
    FileId, FxHashSet, RootDatabase,
    defs::{Definition, IdentClass, NameClass, NameRefClass},
};
use syntax::{AstNode, SyntaxKind, SyntaxNode, TextRange, ast};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportAssessment {
    AlreadyAvailable,
    Insert,
    Conflict(String),
    Unknown(String),
}

pub(crate) fn assess_import(
    db: &RootDatabase,
    file_id: FileId,
    scope: TextRange,
    path: &str,
    alias: Option<&str>,
) -> ImportAssessment {
    let sema = Semantics::new(db);
    let source = sema.parse_guess_edition(file_id);
    let mut file_modules = sema.file_to_module_defs(file_id);
    let Some(file_module) = file_modules.next() else {
        return ImportAssessment::Unknown("file is not part of the active module graph".into());
    };
    if file_modules.next().is_some() {
        return ImportAssessment::Unknown("file belongs to multiple module contexts".into());
    }
    let module = if source.syntax().text_range() == scope {
        Some(file_module)
    } else {
        source
            .syntax()
            .descendants()
            .filter(|node| node.text_range() == scope)
            .find_map(ast::ItemList::cast)
            .and_then(|list| list.syntax().parent().and_then(ast::Module::cast))
            .and_then(|module| sema.to_def(&module))
    };
    let Some(module) = module else {
        return ImportAssessment::Unknown("scope is not an exact source module item list".into());
    };
    let (name, items) = match module.assess_import_binding(db, path, alias) {
        ImportBindingAssessment::AlreadyAvailable { .. } => {
            return ImportAssessment::AlreadyAvailable;
        }
        ImportBindingAssessment::Vacant { name, items } => (name, items),
        ImportBindingAssessment::Conflict(reason) => {
            return ImportAssessment::Conflict(format!("import binding: {reason:?}"));
        }
        ImportBindingAssessment::Unknown(reason) => {
            return ImportAssessment::Unknown(format!("import binding: {reason:?}"));
        }
    };
    let mut scan = Impact {
        sema: &sema,
        name: name.as_str(),
        items: &items,
        remaining: 250_000,
        expanded: FxHashSet::default(),
        modules: vec![module],
    };
    match scan.subtree(module) {
        Ok(()) => ImportAssessment::Insert,
        Err(Refusal::Conflict(reason)) => ImportAssessment::Conflict(reason.into()),
        Err(Refusal::Unknown(reason)) => ImportAssessment::Unknown(reason.into()),
    }
}

enum Refusal {
    Conflict(&'static str),
    Unknown(&'static str),
}

struct Impact<'a, 'db> {
    sema: &'a Semantics<'db, RootDatabase>,
    name: &'a str,
    items: &'a [ItemInNs],
    remaining: usize,
    expanded: FxHashSet<hir::MacroCallId>,
    modules: Vec<Module>,
}

impl Impact<'_, '_> {
    fn subtree(&mut self, module: Module) -> Result<(), Refusal> {
        let db = self.sema.db;
        // Inserting a use changes the input of any enclosing attribute macro.
        // Its present expansion is not evidence about that different input.
        let mut ancestor = Some(module);
        while let Some(module) = ancestor {
            let source = module.definition_source(db);
            if source.file_id.is_macro() {
                return Err(Refusal::Unknown("destination has a macro-generated module ancestor"));
            }
            self.inert_attributes(&source.value.node())?;
            ancestor = module.parent(db);
        }

        let mut visited = FxHashSet::default();
        while let Some(module) = self.modules.pop() {
            if !visited.insert(module) {
                continue;
            }
            if visited.len() > 4096 {
                return Err(Refusal::Unknown("import impact exceeds the module work bound"));
            }
            module.import_scope_status(db).map_err(|_| {
                Refusal::Unknown(
                    "the analyzer reports incomplete imports or macros in a dependent module",
                )
            })?;
            let source = module.definition_source(db);
            if source.file_id.is_macro() {
                return Err(Refusal::Unknown("dependent module is macro-generated"));
            }
            let root = self.sema.parse_or_expand(source.file_id);
            let source_node = source.value.node();
            let node = root
                .descendants()
                .find(|node| {
                    node.kind() == source_node.kind()
                        && node.text_range() == source_node.text_range()
                })
                .ok_or(Refusal::Unknown("module source cannot be mapped into its analysis tree"))?;
            self.tree(node, false)?;
            self.modules.extend(module.children(db));
        }
        Ok(())
    }

    fn tree(&mut self, root: SyntaxNode, expansion: bool) -> Result<(), Refusal> {
        let mut walk = root.preorder();
        while let Some(event) = walk.next() {
            let syntax::WalkEvent::Enter(node) = event else { continue };
            self.remaining = self
                .remaining
                .checked_sub(1)
                .ok_or(Refusal::Unknown("import impact exceeds the syntax work bound"))?;
            if node != root
                && let Some(module) = ast::Module::cast(node.clone())
            {
                if expansion {
                    return Err(Refusal::Unknown("macro expansion introduces a module"));
                }
                // Body-local modules live in block DefMaps and are not reported
                // by Module::children. Discover them from their actual syntax.
                let module = self.sema.to_def(&module).ok_or(Refusal::Unknown(
                    "nested module has no unambiguous semantic identity",
                ))?;
                self.modules.push(module);
                walk.skip_subtree();
                continue;
            }
            if node.kind() == SyntaxKind::ERROR {
                return Err(Refusal::Unknown("dependent syntax is incomplete"));
            }
            if ast::MacroRules::can_cast(node.kind()) || ast::MacroDef::can_cast(node.kind()) {
                return Err(Refusal::Unknown(
                    "macro definition can carry lookup outside the module subtree",
                ));
            }
            if let Some(call) = ast::MacroCall::cast(node.clone()) {
                if let Some(path) = call.path() {
                    for node in path
                        .syntax()
                        .descendants()
                        .filter(|node| ast::NameRef::can_cast(node.kind()))
                    {
                        self.named_identifier(&node, expansion)?;
                    }
                }
                let id = self
                    .sema
                    .to_def(&call)
                    .ok_or(Refusal::Unknown("dependent macro call has no complete expansion"))?;
                if self.expanded.insert(id) {
                    if self.expanded.len() > 4096 {
                        return Err(Refusal::Unknown("import impact exceeds the macro work bound"));
                    }
                    let expanded = self.sema.expand(id);
                    if expanded.err.is_some() {
                        return Err(Refusal::Unknown(
                            "dependent macro expansion reported an error",
                        ));
                    }
                    self.tree(expanded.value, true)?;
                }
                // The expansion is authoritative, not the unexpanded token tree.
                walk.skip_subtree();
                continue;
            }
            if let Some(item) = ast::Item::cast(node.clone()) {
                let expanded = self.sema.expand_attr_macro(&item);
                let has_expansion = expanded.is_some();
                if let Some(expanded) = expanded {
                    if expanded.err.is_some() {
                        return Err(Refusal::Unknown(
                            "dependent attribute expansion reported an error",
                        ));
                    }
                    self.tree(expanded.value.value, true)?;
                }
                for attr in node.children().filter_map(ast::Attr::cast) {
                    let Some(meta) = attr.meta() else {
                        return Err(Refusal::Unknown("dependent attribute is incomplete"));
                    };
                    let expansions = self.sema.expand_derive_macro(&meta);
                    let has_derive = expansions.is_some();
                    if let Some(expansions) = expansions {
                        for expanded in expansions {
                            let expanded = expanded.ok_or(Refusal::Unknown(
                                "dependent derive macro has no expansion",
                            ))?;
                            if expanded.err.is_some() {
                                return Err(Refusal::Unknown(
                                    "dependent derive expansion reported an error",
                                ));
                            }
                            self.tree(expanded.value, true)?;
                        }
                    }
                    if !has_expansion && !has_derive {
                        let known_inert = attr.simple_name().as_deref() != Some("cfg_attr")
                            && meta.path().is_some_and(|path| {
                                matches!(
                                    self.sema.resolve_path(&path),
                                    Some(PathResolution::BuiltinAttr(_))
                                )
                            });
                        if !known_inert {
                            return Err(Refusal::Unknown(
                                "dependent attribute has no complete expansion or inert-attribute evidence",
                            ));
                        }
                    }
                }
            }
            if ast::Name::can_cast(node.kind()) || ast::NameRef::can_cast(node.kind()) {
                self.named_identifier(&node, expansion)?;
            }
        }
        Ok(())
    }

    fn named_identifier(&self, node: &SyntaxNode, expansion: bool) -> Result<(), Refusal> {
        let text = node.text().to_string();
        if text.trim_start_matches("r#") == self.name {
            self.identifier(node, expansion)?;
        }
        Ok(())
    }

    fn inert_attributes(&self, node: &SyntaxNode) -> Result<(), Refusal> {
        for attr in node.children().filter_map(ast::Attr::cast) {
            let name = attr.simple_name();
            if !matches!(
                name.as_deref(),
                Some("cfg" | "allow" | "warn" | "deny" | "forbid" | "expect" | "doc")
            ) {
                return Err(Refusal::Unknown(
                    "enclosing module has an attribute with unsupported edit behavior",
                ));
            }
        }
        Ok(())
    }

    fn identifier(&self, node: &SyntaxNode, expansion: bool) -> Result<(), Refusal> {
        match IdentClass::classify_node(self.sema, node) {
            Some(IdentClass::NameClass(NameClass::ConstReference(def))) => self.reference(def),
            Some(IdentClass::NameClass(NameClass::Definition(Definition::Local(_))))
            | Some(IdentClass::NameClass(NameClass::PatFieldShorthand { .. })) => {
                if self.items.iter().any(|item| matches!(item, ItemInNs::Values(_))) {
                    Err(Refusal::Conflict("import could reinterpret an existing pattern binding"))
                } else {
                    Ok(())
                }
            }
            Some(IdentClass::NameClass(NameClass::Definition(_))) => Ok(()),
            Some(IdentClass::NameRefClass(NameRefClass::Definition(def, _))) => self.reference(def),
            Some(IdentClass::NameRefClass(NameRefClass::FieldShorthand { .. })) => Ok(()),
            Some(IdentClass::NameRefClass(NameRefClass::ExternCrateShorthand { .. })) => {
                Err(Refusal::Unknown("import overlaps an extern-crate declaration"))
            }
            Some(IdentClass::Operator(_)) => unreachable!("only names are classified"),
            None if !expansion && unresolved_leading_path(node) => Ok(()),
            None => {
                Err(Refusal::Unknown("same-spelling identifier has no complete binding evidence"))
            }
        }
    }

    fn reference(&self, def: Definition<'_>) -> Result<(), Refusal> {
        // Lexically scoped locals/generics and member names cannot be rebound by
        // a non-trait module import. Pattern declarations are handled separately.
        if matches!(
            def,
            Definition::Local(_)
                | Definition::GenericParam(_)
                | Definition::Field(_)
                | Definition::TupleField(_)
                | Definition::Label(_)
        ) {
            return Ok(());
        }
        if self.items.iter().any(|item| match item {
            ItemInNs::Types(item) | ItemInNs::Values(item) => Definition::from(*item) == def,
            ItemInNs::Macros(_) => false,
        }) {
            Ok(())
        } else {
            Err(Refusal::Conflict("import could change an existing same-spelling reference"))
        }
    }
}

fn unresolved_leading_path(node: &SyntaxNode) -> bool {
    let Some(segment) = node.parent().and_then(ast::PathSegment::cast) else { return false };
    let path = segment.parent_path();
    if path.qualifier().is_some() || segment.coloncolon_token().is_some() {
        return false;
    }
    // A bare unresolved use is the intended insertion use case. Unresolved
    // imports, attribute paths, visibility and generated paths are not evidence.
    for ancestor in path.syntax().ancestors().skip(1) {
        if ast::Attr::can_cast(ancestor.kind())
            || ast::Use::can_cast(ancestor.kind())
            || ast::Visibility::can_cast(ancestor.kind())
        {
            return false;
        }
        if ast::PathExpr::can_cast(ancestor.kind())
            || ast::PathType::can_cast(ancestor.kind())
            || ast::RecordExpr::can_cast(ancestor.kind())
            || ast::RecordPat::can_cast(ancestor.kind())
            || ast::PathPat::can_cast(ancestor.kind())
        {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::ImportAssessment;
    use crate::fixture;
    use syntax::TextRange;

    fn assess(#[rust_analyzer::rust_fixture] fixture: &str, path: &str) -> ImportAssessment {
        let (analysis, file) = fixture::file(fixture);
        let len = analysis.file_text(file).unwrap().len().try_into().unwrap();
        analysis.assess_import(file, TextRange::up_to(len), path, None).unwrap()
    }

    #[test]
    fn availability_and_subtree_impact_are_distinct_obligations() {
        assert_eq!(
            assess("mod api { pub struct Token; } use api::*;", "crate::api::Token"),
            ImportAssessment::AlreadyAvailable,
        );
        assert_eq!(
            assess(
                "mod api { pub struct Token; } mod empty {} use empty::*; fn f() { let _ = Token; }",
                "crate::api::Token"
            ),
            ImportAssessment::Insert,
        );
        // A vacant module binding does not imply the new value binding is safe:
        // Rust may reinterpret a plain pattern as a unit constructor reference.
        assert!(matches!(
            assess(
                "mod api { pub struct Token; } mod empty {} use empty::*; fn f(Token: u8) {}",
                "crate::api::Token"
            ),
            ImportAssessment::Conflict(_),
        ));
        assert!(matches!(
            assess(
                "mod api { pub struct Token; } mod empty {} use empty::*; fn f(Token: u8) {}",
                "crate::api:: /* name */ Token"
            ),
            ImportAssessment::Conflict(_),
        ));
        assert!(matches!(
            assess(
                "mod api { pub const Token: u8 = 1; } fn outer() { mod child { use super::*; pub fn f(Token: u8) {} } }",
                "crate::api::Token"
            ),
            ImportAssessment::Conflict(_) | ImportAssessment::Unknown(_),
        ));
        assert!(matches!(
            assess(
                "mod api { pub struct Token; } mod other { pub struct Token; } use other::*;",
                "crate::api::Token"
            ),
            ImportAssessment::Conflict(_),
        ));
        assert!(matches!(
            assess(
                "mod api { pub struct Token; } mod empty {} use empty::*; macro_rules! escape { () => { Token } }",
                "crate::api::Token"
            ),
            ImportAssessment::Unknown(_),
        ));
    }

    #[test]
    fn expansion_inputs_and_outputs_remain_in_the_impact_boundary() {
        let (analysis, range) = fixture::range(
            r#"
mod api { pub const Token: u8 = 1; }
mod empty {}
macro_rules! bind { () => { let Token = 0u8; }; }
mod client $0{
    use crate::empty::*;
    fn f() { bind!(); }
}$0
"#,
        );
        let result =
            analysis.assess_import(range.file_id, range.range, "crate::api::Token", None).unwrap();
        assert!(matches!(result, ImportAssessment::Conflict(_) | ImportAssessment::Unknown(_)));

        // Unresolved attributes on block items can escape the crate DefMap's
        // diagnostics. Their absent expansion must not be treated as empty.
        let result = assess(
            "mod api { pub struct Token; } mod empty {} use empty::*; fn f() { #[missing] fn nested() {} }",
            "crate::api::Token",
        );
        assert!(matches!(result, ImportAssessment::Unknown(_)));
    }
}
