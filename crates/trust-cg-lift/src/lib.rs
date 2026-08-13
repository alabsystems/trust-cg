// trust-cg-lift - Binary lifting support for Trust Codegen
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Binary lifting support for Trust Codegen.
//!
//! Phase 1 starts with instruction decoding and encode/decode round-trip
//! checks. It intentionally stops at MachIR-shaped decoded instructions; CFG
//! recovery, SSA reconstruction, trust_ir emission, and verification closure are
//! later phases of #378.

pub mod disasm;
