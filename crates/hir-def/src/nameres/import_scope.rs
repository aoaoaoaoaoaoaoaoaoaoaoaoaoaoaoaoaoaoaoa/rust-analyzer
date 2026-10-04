//! Exact import-mode observations from rust-analyzer's existing resolver.
//!
//! Results are provider facts, not independent compiler-equivalence or uniqueness proofs.

use base_db::SourceDatabase;
use hir_expand::mod_path::ModPath;

use crate::{
    ModuleId,
    nameres::{
        BuiltinShadowMode, ResolveMode, crate_local_def_map, path_resolution::ReachedFixedPoint,
    },
    per_ns::PerNs,
    visibility::Visibility,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportPathResolution {
    Resolved(PerNs),
    Partial,
    Unresolved,
    Indeterminate,
}

/// Uses the ordinary resolver's exact import mode without changing database inputs.
pub fn resolve_import_path(
    db: &dyn SourceDatabase,
    module: ModuleId,
    path: &ModPath,
) -> ImportPathResolution {
    let def_map = module.def_map(db);
    let local = crate_local_def_map(db, module.krate(db)).local(db);
    let result = def_map.resolve_path_fp_with_macro(
        local,
        db,
        ResolveMode::Import,
        module,
        path,
        BuiltinShadowMode::Module,
        None,
    );
    match (result.reached_fixedpoint, result.resolved_def.is_none(), result.segment_index) {
        (ReachedFixedPoint::No, _, _) => ImportPathResolution::Indeterminate,
        (_, true, _) => ImportPathResolution::Unresolved,
        (_, false, Some(_)) => ImportPathResolution::Partial,
        (_, false, None) => {
            // Mirror DefCollector::resolve_import's external-crate filtering.
            let resolved = if result.prefix_info.differing_crate {
                result
                    .resolved_def
                    .filter_visibility(|visibility| matches!(visibility, Visibility::Public))
            } else {
                result.resolved_def
            };
            ImportPathResolution::Resolved(resolved)
        }
    }
}
