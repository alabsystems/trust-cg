// trust-cg-dialect - Sample `trust_ir` dialect (facade over real trust_ir)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Minimal `trust_ir` dialect used by the PoC lowering pipeline.
//!
//! This is a *facade* — the real trust_ir ops live in the `trust_ir` crate and come in
//! through `trust-cg-lower`'s adapter. The dialect wrapper here defines the op
//! identifiers that conversion patterns use as targets for `VerifToTrustIr` and as
//! sources for `TrustIrToMachir`. Future work will replace these with direct
//! translation against the real trust_ir crate (see design doc §10).

use crate::dialect::{Arity, Capabilities, Dialect, OpDef, TypeConstraint};
use crate::id::OpCode;

pub const TRUST_IR_CONST: OpCode = OpCode(0);
pub const TRUST_IR_ADD: OpCode = OpCode(1);
pub const TRUST_IR_XOR: OpCode = OpCode(2);
pub const TRUST_IR_RET: OpCode = OpCode(3);

pub struct TrustIrDialect;

impl TrustIrDialect {
    pub fn new() -> Self {
        Self
    }
}

impl Default for TrustIrDialect {
    fn default() -> Self {
        Self::new()
    }
}

// --- Type-constraint slices ------------------------------------------------
//
// Shared static slices keep the `OpDef` table readable and avoid duplicated
// constraint data. Polymorphic binaries (`trust_ir.add`, `trust_ir.xor`) accept any
// integer operand pair and produce the same type as `operand[0]` — matching
// the declarative rewrite engine's expectations in #393.

/// `trust_ir.const` results are `AnyInt` — the concrete width comes from the
/// `value` attribute. Future work (once f32/f64 literals land) expands this.
static TRUST_IR_CONST_RESULTS: &[TypeConstraint] = &[TypeConstraint::AnyInt];

/// Binary integer ops: both operands are `AnyInt`; the result width matches
/// `operand[0]`.
static TRUST_IR_BINARY_OPERANDS: &[TypeConstraint] =
    &[TypeConstraint::AnyInt, TypeConstraint::SameAs(0)];
static TRUST_IR_BINARY_RESULTS: &[TypeConstraint] = &[TypeConstraint::SameAs(0)];

/// `trust_ir.ret` is variadic (0 or 1 operands). A single-element slice applies
/// the constraint to every operand present.
static TRUST_IR_RET_OPERANDS: &[TypeConstraint] = &[TypeConstraint::AnyScalar];

static TRUST_IR_OPS: &[OpDef] = &[
    OpDef {
        op: TRUST_IR_CONST,
        name: "trust_ir.const",
        capabilities: Capabilities::PURE,
        num_operands: Arity::Fixed(0),
        num_results: Arity::Fixed(1),
        operand_types: &[],
        result_types: TRUST_IR_CONST_RESULTS,
    },
    OpDef {
        op: TRUST_IR_ADD,
        name: "trust_ir.add",
        capabilities: Capabilities::PURE,
        num_operands: Arity::Fixed(2),
        num_results: Arity::Fixed(1),
        operand_types: TRUST_IR_BINARY_OPERANDS,
        result_types: TRUST_IR_BINARY_RESULTS,
    },
    OpDef {
        op: TRUST_IR_XOR,
        name: "trust_ir.xor",
        capabilities: Capabilities::PURE,
        num_operands: Arity::Fixed(2),
        num_results: Arity::Fixed(1),
        operand_types: TRUST_IR_BINARY_OPERANDS,
        result_types: TRUST_IR_BINARY_RESULTS,
    },
    OpDef {
        op: TRUST_IR_RET,
        name: "trust_ir.ret",
        capabilities: Capabilities(
            Capabilities::IS_TERMINATOR.bits() | Capabilities::HAS_SIDE_EFFECT.bits(),
        ),
        num_operands: Arity::Variadic(Some(1)),
        num_results: Arity::Fixed(0),
        operand_types: TRUST_IR_RET_OPERANDS,
        result_types: &[],
    },
];

impl Dialect for TrustIrDialect {
    fn namespace(&self) -> &'static str {
        "trust_ir"
    }
    fn ops(&self) -> &[OpDef] {
        TRUST_IR_OPS
    }
}
