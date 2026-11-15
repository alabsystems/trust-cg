// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

//! Actual compiler attribute types and the builtin-macro attribute query.
//! Import selection changes no attribute payload or owner/derive authority.

#[cfg(rustc_attr_ir_attributes)]
pub(crate) use rustc_attr_ir::{InlineAttr, Linkage};
#[cfg(not(rustc_attr_ir_attributes))]
pub(crate) use rustc_hir::attrs::{InlineAttr, Linkage};

#[cfg(rustc_attr_ir_attributes)]
use rustc_attr_ir::find_attr;
#[cfg(not(rustc_attr_ir_attributes))]
use rustc_hir::find_attr;

pub(crate) fn is_builtin_macro(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    did: rustc_hir::def_id::DefId,
) -> bool {
    find_attr!(tcx, did, RustcBuiltinMacro { .. })
}
