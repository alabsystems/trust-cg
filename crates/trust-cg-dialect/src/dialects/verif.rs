// trust-cg-dialect - `verif` contract surface for external consumers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Minimal `verif` dialect surface matching the cross-repo verification op
//! names used by ty and trust_ir:
//!
//! - `verif.bfs_step(frontier, seen_set) -> i64`
//! - `verif.frontier_drain(frontier)`
//! - `verif.fingerprint_batch(states, count) -> i64`
//!
//! The names are the stable contract. The lowering remains intentionally toy
//! scalar semantics inside `trust-cg-dialect` until Trust Codegen grows a real runtime
//! helper ABI for these ops.

use trust_cg_ir::Type;

use crate::dialect::{Arity, Capabilities, Dialect, OpDef, TypeConstraint};
use crate::id::OpCode;

/// Stable opcode for `verif.bfs_step`.
pub const BFS_STEP: OpCode = OpCode(0);
/// Stable opcode for `verif.frontier_drain`.
pub const FRONTIER_DRAIN: OpCode = OpCode(1);
/// Stable opcode for `verif.fingerprint_batch`.
pub const FINGERPRINT_BATCH: OpCode = OpCode(2);
/// Back-compat alias for earlier proof-of-concept code.
pub const FINGERPRINT_BATCH_STUB: OpCode = FINGERPRINT_BATCH;

pub struct VerifDialect;

impl VerifDialect {
    pub fn new() -> Self {
        Self
    }
}

impl Default for VerifDialect {
    fn default() -> Self {
        Self::new()
    }
}

// This PoC crate keeps the value surface scalar until the helper ABI is real.
static BINARY_I64_OPERAND_TYPES: &[TypeConstraint] = &[
    TypeConstraint::Specific(Type::I64),
    TypeConstraint::Specific(Type::I64),
];
static I64_RESULT_TYPES: &[TypeConstraint] = &[TypeConstraint::Specific(Type::I64)];
static FRONTIER_DRAIN_OPERAND_TYPES: &[TypeConstraint] = &[TypeConstraint::Specific(Type::I64)];

static VERIF_OPS: &[OpDef] = &[
    OpDef {
        op: BFS_STEP,
        name: "verif.bfs_step",
        capabilities: Capabilities(
            Capabilities::PURE.bits()
                | Capabilities::BOUNDED_LOOPS.bits()
                | Capabilities::HAS_PARALLELISM.bits(),
        ),
        num_operands: Arity::Fixed(2),
        num_results: Arity::Fixed(1),
        operand_types: BINARY_I64_OPERAND_TYPES,
        result_types: I64_RESULT_TYPES,
    },
    OpDef {
        op: FRONTIER_DRAIN,
        name: "verif.frontier_drain",
        capabilities: Capabilities(Capabilities::HAS_SIDE_EFFECT.bits()),
        num_operands: Arity::Fixed(1),
        num_results: Arity::Fixed(0),
        operand_types: FRONTIER_DRAIN_OPERAND_TYPES,
        result_types: &[],
    },
    OpDef {
        op: FINGERPRINT_BATCH,
        name: "verif.fingerprint_batch",
        capabilities: Capabilities(Capabilities::PURE.bits() | Capabilities::BOUNDED_LOOPS.bits()),
        num_operands: Arity::Fixed(2),
        num_results: Arity::Fixed(1),
        operand_types: BINARY_I64_OPERAND_TYPES,
        result_types: I64_RESULT_TYPES,
    },
];

impl Dialect for VerifDialect {
    fn namespace(&self) -> &'static str {
        "verif"
    }
    fn ops(&self) -> &[OpDef] {
        VERIF_OPS
    }
}
