// trust-cg-dialect - Sample dialects (verif, trust_ir, machir) and conversions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Proof-of-concept dialects used by the end-to-end lowering test:
//!
//! * [`verif`] — a verification-layer dialect exposing the real contract names
//!   (`verif.bfs_step`, `verif.frontier_drain`, `verif.fingerprint_batch`)
//!   with toy scalar lowerings.
//! * [`trust_ir`] — a small subset of trust_ir ops (`trust_ir.add`, `trust_ir.xor`,
//!   `trust_ir.const`, `trust_ir.ret`).
//! * [`machir`] — a small subset of MachIR ops mapping to `AArch64Opcode`.
//! * [`conversions`] — `VerifToTrustIr` and `TrustIrToMachir` [`ConversionPattern`]s.

pub mod ay;
pub mod conversions;
pub mod machir;
pub mod trust_ir;
pub mod verif;
pub use conversions::{TrustIrToMachir, VerifToTrustIr, register_all};
