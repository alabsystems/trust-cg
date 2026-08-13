// trust-cg-dialect - Dialect framework + progressive lowering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Dialect framework for Trust Codegen.
//!
//! This crate provides a minimal, MLIR-inspired dialect/op/pass model that sits
//! **above** trust_ir and progressively lowers to MachIR. It does not take an MLIR
//! dependency and does not replicate MLIR's C++ trait hierarchy.
//!
//! Design doc: `designs/2026-04-18-dialect-framework.md`.
//!
//! # Layering
//!
//! ```text
//! verif.*   (frontend / verification-layer ops)
//!   |
//!   v  VerifToTrustIr conversion
//! trust_ir.*   (wraps real trust_ir opcodes)
//!   |
//!   v  TrustIrToMachir conversion
//! machir.* (wraps AArch64/x86/... opcodes)
//!   |
//!   v  emit_mach_function -> trust_cg_ir::MachFunction
//! ```
//!
//! The `dialects` module ships a minimal `verif` contract surface plus sample
//! `trust_ir`/`machir` facades and conversion-pass implementations wired
//! end-to-end. See `tests/end_to_end.rs` for the proof-of-concept pipeline.

pub mod conversion;
pub mod dialect;
pub mod dialects;
pub mod id;
pub mod machir_emit;
pub mod module;
pub mod op;
pub mod pass;
pub mod registry;

pub use conversion::{ConversionDriver, ConversionError, ConversionPattern, Rewriter};
pub use dialect::{Arity, Capabilities, Dialect, OpDef, TypeConstraint};
pub use id::{BlockId, DialectId, DialectOpId, OpCode, OpId, ValueId};
pub use machir_emit::{EmitError, emit_mach_function};
pub use module::{DialectBlock, DialectFunction, DialectModule};
pub use op::{Attribute, Attributes, DialectOp};
pub use pass::{
    Legality, Pass, PassError, validate_legality, validate_type_constraints,
    validate_type_constraints_with_env,
};
pub use registry::DialectRegistry;

// ---------------------------------------------------------------------------
// lower_module — end-to-end progressive-lowering entry point (Trust Codegen#433)
// ---------------------------------------------------------------------------

use trust_cg_ir::MachFunction;

/// Error returned by [`lower_module`].
#[derive(Debug)]
pub enum LowerModuleError {
    /// A required dialect was not registered in the module's registry.
    ///
    /// `lower_module` requires that `verif`, `trust_ir`, and `machir` are all
    /// present. Call [`dialects::conversions::register_all`] before using
    /// this entry point.
    MissingDialect(&'static str),
    /// `verif.* -> trust_ir.*` conversion failed.
    VerifToTrustIr(ConversionError),
    /// `trust_ir.* -> machir.*` conversion failed.
    TrustIrToMachir(ConversionError),
    /// `machir.* -> trust_cg_ir::MachFunction` emission failed.
    Emit(EmitError),
    /// Legality check rejected the intermediate form.
    Legality(pass::PassError),
}

impl std::fmt::Display for LowerModuleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerModuleError::MissingDialect(name) => {
                write!(
                    f,
                    "lower_module: required dialect `{}` not registered",
                    name
                )
            }
            LowerModuleError::VerifToTrustIr(e) => {
                write!(f, "lower_module: verif->trust_ir conversion failed: {}", e)
            }
            LowerModuleError::TrustIrToMachir(e) => {
                write!(f, "lower_module: trust_ir->machir conversion failed: {}", e)
            }
            LowerModuleError::Emit(e) => {
                write!(f, "lower_module: machir emit failed: {}", e)
            }
            LowerModuleError::Legality(e) => {
                write!(f, "lower_module: legality check failed: {}", e)
            }
        }
    }
}

impl std::error::Error for LowerModuleError {}

/// Run the full progressive-lowering pipeline on `module` and emit one
/// `trust_cg_ir::MachFunction` per contained function.
///
/// Pipeline (Trust Codegen#433 / trust_ir#428 integration point):
///
/// 1. Run the `verif.* -> trust_ir.*` conversion driver.
/// 2. Run the `trust_ir.* -> machir.*` conversion driver.
/// 3. Validate that only `machir.*` ops remain (legality gate).
/// 4. Emit a `MachFunction` per function via [`emit_mach_function`].
///
/// The module's [`DialectRegistry`] MUST already have the `verif`, `trust_ir`,
/// and `machir` dialects registered — the standard way is to call
/// [`dialects::conversions::register_all`] at registry construction time.
///
/// Any `DialectOp` that isn't covered by the registered lowering patterns
/// is a hard error at the legality gate, so unhandled ops fail in a single
/// known location rather than silently leaking into the MachFunction.
pub fn lower_module(module: &mut DialectModule) -> Result<Vec<MachFunction>, LowerModuleError> {
    let verif_id = module
        .registry
        .by_name("verif")
        .ok_or(LowerModuleError::MissingDialect("verif"))?;
    let trust_ir_id = module
        .registry
        .by_name("trust_ir")
        .ok_or(LowerModuleError::MissingDialect("trust_ir"))?;
    let machir_id = module
        .registry
        .by_name("machir")
        .ok_or(LowerModuleError::MissingDialect("machir"))?;

    // Stage 1: verif -> trust_ir.
    let stage1 = dialects::conversions::verif_to_trust_ir_driver(verif_id, trust_ir_id);
    stage1
        .run(module)
        .map_err(LowerModuleError::VerifToTrustIr)?;

    // Stage 2: trust_ir -> machir.
    let stage2 = dialects::conversions::trust_ir_to_machir_driver(trust_ir_id, machir_id);
    stage2
        .run(module)
        .map_err(LowerModuleError::TrustIrToMachir)?;

    // Stage 3: legality — only machir.* ops should remain. This is the
    // single known location where an unhandled DialectOp fails hard (per
    // Trust Codegen#433 / trust_ir#428 guidance).
    let legality = Legality::new().produces(machir_id);
    validate_legality(module, &legality).map_err(LowerModuleError::Legality)?;

    // Stage 4: emit one MachFunction per function.
    let mut out = Vec::with_capacity(module.functions.len());
    for i in 0..module.functions.len() {
        let mf = emit_mach_function(module, i).map_err(LowerModuleError::Emit)?;
        out.push(mf);
    }
    Ok(out)
}
