// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Transfer every artifact of a freshly compiled module into rustc's carrier.
//!
//! Fresh producers have no incremental-cache links. The legacy carrier records
//! that empty list explicitly; the current carrier has no such field. Cached
//! module restoration is a separate contract and is not represented here.

use std::path::PathBuf;

use rustc_codegen_ssa::{CompiledModule, ModuleKind};

pub(super) struct FreshModule {
    pub(super) name: String,
    pub(super) kind: ModuleKind,
    pub(super) object: Option<PathBuf>,
    pub(super) global_asm_object: Option<PathBuf>,
    pub(super) dwarf_object: Option<PathBuf>,
    pub(super) bytecode: Option<PathBuf>,
    pub(super) assembly: Option<PathBuf>,
    pub(super) llvm_ir: Option<PathBuf>,
}

pub(super) fn fresh(input: FreshModule) -> CompiledModule {
    let FreshModule {
        name,
        kind,
        object,
        global_asm_object,
        dwarf_object,
        bytecode,
        assembly,
        llvm_ir,
    } = input;
    CompiledModule {
        name,
        kind,
        object,
        global_asm_object,
        dwarf_object,
        bytecode,
        assembly,
        llvm_ir,
        #[cfg(rustc_compiled_module_cache_links)]
        links_from_incr_cache: Vec::new(),
    }
}
