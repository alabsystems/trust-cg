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
//! - [`encode`] — the binary module encoder: sections, imports, and the
//!   relocatable-object form (padded LEBs, `linking` v2 symbol table and
//!   segment info, `reloc.CODE`/`reloc.DATA`, `target_features`).
//! - [`lower`] — trust-ir → wasm lowering: the dominator-tree relooper, the
//!   integer/float/bool value domain (narrow integers canonicalized, 128-bit
//!   arithmetic in `lower/wide.rs`, overflow, rotates, `FRem` (a trust-ir
//!   `fmod` helper in a closed module, the library's `fmod` in an object),
//!   IEEE `min`/`max`, atomics, bulk memory),
//!   memory-carried aggregates, tuples, enums and fat pointers (`layout`),
//!   the shadow-stack frame (home slots shared by liveness in
//!   `lower/storage.rs`, per-execution `Alloca`s decided in
//!   `lower/captures.rs` from the capture analysis
//!   `trust_cg_irmid::escape` shares with the mid-end), and the call ABI (`lower/abi.rs`: the
//!   WebAssembly BasicCABI, `sret`, split `i128`; in an object at O1 and
//!   above, unless the producer withholds `multivalue`, the multi-value
//!   internal ABI of strong hidden crate-private functions, gated by
//!   `trust_cg_verify::wasm_internal_abi`). At O1 and above, `opt.rs`
//!   colours, reorders and rematerializes the locals of every emitted body
//!   and keeps a rewrite only when `trust_cg_verify::wasm_local_tv`
//!   validates it (O0 emits the baseline); `locals.rs`
//!   holds the liveness-coalesced baseline and refuses a function over an
//!   engine limit.
//! - `mid.rs` — at O1 and above, before lowering, the trust-ir mid-end
//!   (`trust_cg_irmid`, profile `Wasm32`: copy propagation, pointer chain to
//!   byte-offset GEP, constant-branch folding, pure dead-code elimination,
//!   single-dominating-store forwarding, dead-slot removal and constant-table
//!   promotion to read-only data), each rewrite kept only when its witness checker and the interpreter
//!   differential accept it. Its output is lowered only when it passes the
//!   admission the input passed and trust-ir's validator finds nothing new;
//!   otherwise, or when the lane refuses it, the input is lowered
//!   ([`WasmOptOptions`] switches it off; [`IrmidReport`] is the evidence).
//! - [`frame_bounds`] — the frame-bounds guard every lowered function passes:
//!   no constant-offset access through its frame base leaves the frame.
//! - [`target`] — the `wasm32-unknown-unknown` target pin.
//!
//! Three output forms share that lowering: a closed module
//! ([`compile_module`]), an island inside a host module
//! ([`compile_module_with_policy`], below), and a relocatable object for
//! `wasm-ld` ([`compile_object`]), which imports `env.__linear_memory`,
//! `env.__stack_pointer` and `env.__indirect_function_table` and leaves every
//! address to relocations. Every object passes the CFG structural checker
//! (`trust_cg_verify::wasm_cfg_proofs`) before it is returned.
//!
//! **Admission.** Every module and object entry admits its input as the native
//! entries do, before any contract surface or body is looked at: trust-ir's
//! own codegen admission (`trust_cg_lower::validate_codegen_prerequisites`,
//! no policy widens it), then the codegen LICENSE under a
//! `trust_cg_lower::CodegenLicensePolicy` — the default one, or the caller's
//! through the `*_license` entries ([`compile_module_with_policy_and_license`],
//! [`compile_object_with_license`], ...), which is how the CLI's
//! `--recognize-authority` / `--refuse-unlicensed` and the bridge's session
//! policy reach this lane. A producer
//! that rewrites a module for this lane types it with [`value_types`], the
//! typing its operand gate checks.
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
pub mod frame_bounds;
mod helpers;
mod layout;
mod locals;
pub mod lower;
mod mid;
mod opt;
pub mod target;

pub use encode::{
    DEFAULT_OWNED_PAGES, GlobalInit, WASM_PAGE_BYTES, WasmEncodeError, WasmMemoryPolicy,
    WasmModule, emit_memory_grow, emit_memory_size,
};
pub use helpers::{DIVMOD128_SYMBOL_PREFIX, divmod128_helper_name};
pub use lower::{
    BOX_VALIDITY_NOT_ESTABLISHED, BR_TABLE_MAX_SPAN, BR_TABLE_MAX_SPAN_PER_CASE,
    BR_TABLE_MIN_CASES, ISLAND_ABI_NAMESPACE, ISLAND_HOST_MODULE, ISLAND_MEMORY_IMPORT,
    ISLAND_STACK_BASE_IMPORT, MEMORY_GROW_EXPORT, MEMORY_SIZE_EXPORT, WASM_CLOSED_MIN_STACK_BYTES,
    WASM_COMPILE_EVIDENCE_SCHEMA, WASM_STATIC_DATA_BASE, WasmCfgStructural, WasmCompileEvidence,
    WasmFuncImportPolicy, WasmFunctionEnv, WasmLocalOptSummary, WasmLowerError,
    WasmMemoryGrowthPolicy, WasmModulePolicy, WasmStackPolicy, WasmStaticDataPolicy,
    compile_module, compile_module_with_evidence, compile_module_with_evidence_and_policy,
    compile_module_with_evidence_and_policy_optimized,
    compile_module_with_evidence_policy_and_license,
    compile_module_with_evidence_policy_license_optimized,
    compile_module_with_evidence_policy_license_options, compile_module_with_license,
    compile_module_with_policy, compile_module_with_policy_and_license, compile_object,
    compile_object_optimized, compile_object_with_evidence,
    compile_object_with_evidence_and_license, compile_object_with_evidence_license_optimized,
    compile_object_with_evidence_license_options,
    compile_object_with_evidence_license_options_hints, compile_object_with_evidence_optimized,
    compile_object_with_license, compile_object_with_license_optimized,
    compile_object_with_license_options, compile_object_with_license_options_hints,
    compile_sized_closed_module_with_evidence_license_optimized,
    compile_sized_closed_module_with_evidence_license_options, island_host_namespace,
    lower_function, lower_function_with_license, sized_closed_policy, value_types,
};
pub use mid::{WasmInlineHints, WasmOptOptions};
pub use target::{WASM32_TRIPLE, is_wasm32_target, wasm32_target_info};
pub use trust_cg_irmid::IrmidReport;
