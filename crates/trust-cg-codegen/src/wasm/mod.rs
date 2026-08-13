// trust-cg-codegen/wasm/mod.rs - WebAssembly (wasm32) backend
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! WebAssembly (`wasm32`) backend for trust-cg.
//!
//! Trust can compile to WebAssembly through the experimental path
//! `tRust → trust-ir → trust-cg → .wasm`. This backend consumes **trust-ir**
//! directly (no new IR, no intermediate SSA) and emits a binary `.wasm` module.
//! The current lowering and evidence limits are part of the v0.1.0 research
//! boundary.
//!
//! Unlike the native targets, wasm is a stack machine with structured control
//! flow and its own module format — so it deliberately bypasses register
//! allocation, condition flags, and ELF/Mach-O/COFF emission. The pieces:
//!
//! - [`encode`] — the binary module encoder (Slice 0).
//! - [`lower`] — trust-ir → wasm lowering (Slice 0: straight-line integer fns).
//! - relooper (Slice 1), linear-memory lowering (Slice 2), calls/imports
//!   (Slice 3), and lowering-refinement proofs (Slice 4) land here next.

pub mod encode;
pub mod lower;
pub mod target;

pub use lower::{WasmLowerError, compile_module, lower_function};
pub use target::is_wasm32_target;
