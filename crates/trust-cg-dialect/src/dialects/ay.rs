// trust-cg-dialect - `ay` high-assurance trust dialect
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The `ay` dialect provides hardware-anchored trust validation for
//! structural authority records.
//!
//! Operations:
//! - `ay.validate_authority(record)`: Hardware-level register check.
//! - `ay.promote_trust(record, evidence)`: Formal escalation.

use trust_cg_ir::Type;

use crate::dialect::{Arity, Capabilities, Dialect, OpDef, TypeConstraint};
use crate::id::OpCode;

/// Opcode for `ay.validate_authority`.
pub const VALIDATE_AUTHORITY: OpCode = OpCode(100);
/// Opcode for `ay.promote_trust`.
pub const PROMOTE_TRUST: OpCode = OpCode(101);

pub struct AYDialect;

impl AYDialect {
    pub fn new() -> Self {
        Self
    }
}

impl Default for AYDialect {
    fn default() -> Self {
        Self::new()
    }
}

static AUTHORITY_RECORD_TYPES: &[TypeConstraint] = &[TypeConstraint::Specific(Type::I64)];
static B1_RESULT_TYPES: &[TypeConstraint] = &[TypeConstraint::Specific(Type::B1)];
static PROMOTE_TYPES: &[TypeConstraint] = &[
    TypeConstraint::Specific(Type::I64),
    TypeConstraint::Specific(Type::I64),
];

static AY_OPS: &[OpDef] = &[
    OpDef {
        op: VALIDATE_AUTHORITY,
        name: "ay.validate_authority",
        capabilities: Capabilities(Capabilities::PURE.bits()),
        num_operands: Arity::Fixed(1),
        num_results: Arity::Fixed(1),
        operand_types: AUTHORITY_RECORD_TYPES,
        result_types: B1_RESULT_TYPES,
    },
    OpDef {
        op: PROMOTE_TRUST,
        name: "ay.promote_trust",
        capabilities: Capabilities(Capabilities::PURE.bits()),
        num_operands: Arity::Fixed(2),
        num_results: Arity::Fixed(1),
        operand_types: PROMOTE_TYPES,
        result_types: AUTHORITY_RECORD_TYPES,
    },
];

impl Dialect for AYDialect {
    fn namespace(&self) -> &'static str {
        "ay"
    }
    fn ops(&self) -> &[OpDef] {
        AY_OPS
    }
}
