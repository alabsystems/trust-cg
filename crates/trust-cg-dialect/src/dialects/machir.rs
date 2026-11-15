// trust-cg-dialect - Sample `machir` dialect (AArch64 facade)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Minimal `machir` dialect wrapping a small subset of `AArch64Opcode`.
//!
//! Ops are the final lowering target before
//! [`emit_mach_function`](crate::emit_mach_function) translates
//! the dialect function into `trust_cg_ir::MachFunction`. The `machir` layer is a
//! small I64 facade, not a one-to-one instruction wrapper: full-width literals
//! expand into MOVZ/MOVK, and parameter/return ABI transfers are explicit.

use trust_cg_ir::{AArch64Opcode, Type};

use crate::dialect::{Arity, Capabilities, Dialect, OpDef, TypeConstraint};
use crate::id::OpCode;

/// Materialize the complete I64/U64 `value` attribute, using MOVK when needed.
pub const MACHIR_MOVZ_I64: OpCode = OpCode(0);
pub const MACHIR_ADD_RR: OpCode = OpCode(1);
pub const MACHIR_EOR_RR: OpCode = OpCode(2);
pub const MACHIR_RET: OpCode = OpCode(3);

/// Return a `machir` operation's base AArch64 opcode, not its full expansion.
///
/// A mapping alone does not define operand or ABI lowering. The emitter uses
/// dedicated handlers and returns an error for unsupported operations.
pub fn to_aarch64(op: OpCode) -> Option<AArch64Opcode> {
    match op {
        MACHIR_MOVZ_I64 => Some(AArch64Opcode::Movz),
        MACHIR_ADD_RR => Some(AArch64Opcode::AddRR),
        MACHIR_EOR_RR => Some(AArch64Opcode::EorRR),
        MACHIR_RET => Some(AArch64Opcode::Ret),
        _ => None,
    }
}

pub struct MachirDialect;

impl MachirDialect {
    pub fn new() -> Self {
        Self
    }
}

impl Default for MachirDialect {
    fn default() -> Self {
        Self::new()
    }
}

// --- Type-constraint slices ------------------------------------------------
//
// MachIR ops in this PoC all operate on I64 values (AArch64 Xn registers).
// The explicit `Specific(I64)` constraints match the implemented machine
// emitters. Wider opcode coverage requires corresponding type and ABI handling.

static MACHIR_I64_RESULTS: &[TypeConstraint] = &[TypeConstraint::Specific(Type::I64)];
static MACHIR_I64_BINARY_OPERANDS: &[TypeConstraint] = &[
    TypeConstraint::Specific(Type::I64),
    TypeConstraint::Specific(Type::I64),
];
static MACHIR_RET_OPERANDS: &[TypeConstraint] = &[TypeConstraint::Specific(Type::I64)];

static MACHIR_OPS: &[OpDef] = &[
    OpDef {
        op: MACHIR_MOVZ_I64,
        name: "machir.movz.i64",
        capabilities: Capabilities::PURE,
        num_operands: Arity::Fixed(0),
        num_results: Arity::Fixed(1),
        operand_types: &[],
        result_types: MACHIR_I64_RESULTS,
    },
    OpDef {
        op: MACHIR_ADD_RR,
        name: "machir.add.rr",
        capabilities: Capabilities::PURE,
        num_operands: Arity::Fixed(2),
        num_results: Arity::Fixed(1),
        operand_types: MACHIR_I64_BINARY_OPERANDS,
        result_types: MACHIR_I64_RESULTS,
    },
    OpDef {
        op: MACHIR_EOR_RR,
        name: "machir.eor.rr",
        capabilities: Capabilities::PURE,
        num_operands: Arity::Fixed(2),
        num_results: Arity::Fixed(1),
        operand_types: MACHIR_I64_BINARY_OPERANDS,
        result_types: MACHIR_I64_RESULTS,
    },
    OpDef {
        op: MACHIR_RET,
        name: "machir.ret",
        capabilities: Capabilities(
            Capabilities::IS_TERMINATOR.bits() | Capabilities::HAS_SIDE_EFFECT.bits(),
        ),
        num_operands: Arity::Variadic(Some(1)),
        num_results: Arity::Fixed(0),
        operand_types: MACHIR_RET_OPERANDS,
        result_types: &[],
    },
];

impl Dialect for MachirDialect {
    fn namespace(&self) -> &'static str {
        "machir"
    }
    fn ops(&self) -> &[OpDef] {
        MACHIR_OPS
    }
}
