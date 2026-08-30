// trust-cg-codegen/wasm/mod.rs - WebAssembly (wasm32) backend
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! WebAssembly (`wasm32`) backend for trust-cg.
//!
//! Trust can compile to WebAssembly through the experimental path
//! `tRust → trust-ir → trust-cg → .wasm`. This backend consumes **trust-ir**
//! directly (no new IR, no intermediate SSA) and emits a binary `.wasm` module.
//! The current lowering and evidence limits are part of the 0.x research
//! boundary; this lane shipped in 0.5.0 (see CHANGELOG.md, [0.5.0]).
//!
//! Unlike the native targets, wasm is a stack machine with structured control
//! flow and its own module format — so it deliberately bypasses register
//! allocation, condition flags, and ELF/Mach-O/COFF emission. The pieces:
//!
//! - [`encode`] — the binary module encoder (Slice 0, + P2 imports).
//! - [`lower`] — trust-ir → wasm lowering (Slice 0: straight-line integer fns).
//! - relooper (Slice 1), linear-memory lowering (Slice 2), calls/imports
//!   (Slice 3), and lowering-refinement proofs (Slice 4) land here next.
//!
//! **P2 — islands.** A module compiled with [`WasmModulePolicy::closed`] (the
//! default, and what [`compile_module`] uses) is a *closed* module: it owns its
//! linear memory, stacks at the top of its own page, and imports nothing, so
//! the boundary really is the module. [`compile_module_with_policy`] compiles
//! an **island** instead: it can share a host module's linear memory
//! ([`WasmMemoryPolicy::Imported`]), take its shadow-stack base from a region
//! the host allocated and published through an imported immutable global
//! ([`WasmStackPolicy::HostBase`]), and bind body-less trust-ir functions to
//! host imports ([`WasmFuncImportPolicy::FromModule`]). Imports occupy the LOW
//! wasm index space, so the encoder shifts every index it hands out and refuses
//! an import declared after a definition
//! ([`encode::WasmEncodeError::ImportAfterDefinition`]).

pub mod encode;
pub mod lower;
pub mod target;

pub use encode::{
    DEFAULT_OWNED_PAGES, GlobalInit, WASM_PAGE_BYTES, WasmEncodeError, WasmMemoryPolicy,
    WasmModule, emit_memory_grow, emit_memory_size,
};
pub use lower::{
    BR_TABLE_MAX_SPAN, BR_TABLE_MAX_SPAN_PER_CASE, BR_TABLE_MIN_CASES, ISLAND_ABI_NAMESPACE,
    ISLAND_HOST_MODULE, ISLAND_MEMORY_IMPORT, ISLAND_STACK_BASE_IMPORT, MEMORY_GROW_EXPORT,
    MEMORY_SIZE_EXPORT, WASM_COMPILE_EVIDENCE_SCHEMA, WASM_STATIC_DATA_BASE, WasmCfgStructural,
    WasmCompileEvidence, WasmFuncImportPolicy, WasmFunctionEnv, WasmLowerError,
    WasmMemoryGrowthPolicy, WasmModulePolicy, WasmStackPolicy, WasmStaticDataPolicy,
    compile_module, compile_module_with_evidence, compile_module_with_evidence_and_policy,
    compile_module_with_policy, island_host_namespace, lower_function,
};
pub use target::{WASM32_TRIPLE, is_wasm32_target, wasm32_target_info};
