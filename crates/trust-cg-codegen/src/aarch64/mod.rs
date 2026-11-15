// trust-cg-codegen/aarch64/mod.rs - AArch64 target encoding modules
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 (ARM64) instruction encoding.
//!
//! Submodules:
//! - [`encode`] — Unified instruction encoder (dispatches to format-specific modules)
//! - [`encoding`] — Data-processing instruction encoding (ALU, branches, moves)
//! - [`encoding_mem`] — Load/store and address (ADRP) encoding
//! - [`encoding_fp`] — Floating-point instruction encoding
//! - [`decode_check`] — ENC-5 independent emission-time decode-check
//! - [`decode_census`] — Diagnostic census of emitted forms and ENC-5 outcomes
//! - `decode_check_fp_simd` — ENC-5's scalar FP and Advanced SIMD slice
//! - `decode_check_int` — ENC-5's integer, PC-relative, atomic and system slice
//! - [`layout_crosscheck`] — Final-layout branch/ADR/literal/fixup cross-check

pub mod decode_census;
pub mod decode_check;
mod decode_check_fp_simd;
mod decode_check_int;
pub mod encode;
pub mod encoding;
pub mod encoding_fp;
pub mod encoding_mem;
pub mod encoding_neon;
pub(crate) mod jump_table_address;
pub mod layout_crosscheck;

pub use encode::{EncodeError, encode_instruction};
