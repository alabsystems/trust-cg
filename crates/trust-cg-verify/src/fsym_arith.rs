// Symbolic execution: arithmetic UB detector
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Symbolic execution: arithmetic UB detector (Phase 1b).
//!
//! This is an evaluator-only companion to [`crate::fsym_null`]. It checks
//! straight-line source/trapping-semantics integer operations for UB witnesses
//! without wiring the detector into the compiler pipeline. In particular, the
//! signed `INT_MIN / -1`, `INT_MIN % -1`, and signed add/sub/mul/neg overflow
//! checks model source-level trap obligations for future fsym use; they are not
//! the current canonical trust_ir wrapping semantics used by lowering proofs.

use crate::fsym_null::{FsymVerdict, PathContext, guards_hold};
use crate::smt::{EvalResult, SmtExpr, mask};
use std::collections::HashMap;

/// Integer arithmetic operations with language-level UB side conditions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithUbKind {
    /// Unsigned integer division: UB when rhs is zero.
    Udiv,
    /// Signed integer division: UB when rhs is zero or INT_MIN / -1.
    Sdiv,
    /// Unsigned integer remainder: UB when rhs is zero.
    Urem,
    /// Signed integer remainder: UB when rhs is zero or INT_MIN % -1.
    Srem,
    /// Signed integer addition: UB when the mathematical sum is out of range.
    Sadd,
    /// Signed integer subtraction: UB when the mathematical difference is out of range.
    Ssub,
    /// Signed integer multiplication: UB when the mathematical product is out of range.
    Smul,
    /// Signed integer negation: UB when negating INT_MIN.
    Sneg,
}

/// Metadata about an arithmetic operation being checked.
#[derive(Debug, Clone)]
pub struct ArithOp {
    /// Human-friendly label, e.g. "bb3/inst12 sdiv".
    pub label: String,
    /// Operation kind.
    pub kind: ArithUbKind,
    /// Left-hand operand.
    pub lhs: SmtExpr,
    /// Right-hand operand / divisor. Ignored for [`ArithUbKind::Sneg`].
    pub rhs: SmtExpr,
    /// Bit width of both operands.
    pub width: u32,
}

fn no_witness_found() -> FsymVerdict {
    FsymVerdict::Unknown {
        reason: "no witness found in evaluator; escalate to SMT".to_string(),
    }
}

fn eval_bv(expr: &SmtExpr, env: &HashMap<String, u64>) -> Option<u64> {
    match expr.try_eval(env).ok()? {
        EvalResult::Bv(value) => Some(value),
        EvalResult::Bv128(value) => u64::try_from(value).ok(),
        _ => None,
    }
}

fn int_min(width: u32) -> Option<u64> {
    if (1..=64).contains(&width) {
        Some(1_u64 << (width - 1))
    } else {
        None
    }
}

fn minus_one(width: u32) -> Option<u64> {
    if (1..=64).contains(&width) {
        Some(mask(u64::MAX, width))
    } else {
        None
    }
}

fn signed_min_div_minus_one(kind: ArithUbKind, lhs: u64, rhs: u64, width: u32) -> bool {
    matches!(kind, ArithUbKind::Sdiv | ArithUbKind::Srem)
        && Some(lhs) == int_min(width)
        && Some(rhs) == minus_one(width)
}

fn signed_range(width: u32) -> Option<(i128, i128)> {
    if (1..=64).contains(&width) {
        let min = -(1_i128 << (width - 1));
        let max = (1_i128 << (width - 1)) - 1;
        Some((min, max))
    } else {
        None
    }
}

fn to_signed(value: u64, width: u32) -> Option<i128> {
    if !(1..=64).contains(&width) {
        return None;
    }

    let value = mask(value, width);
    let sign_bit = 1_u64 << (width - 1);
    if value & sign_bit == 0 {
        Some(value as i128)
    } else {
        Some(value as i128 - (1_i128 << width))
    }
}

fn outside_signed_range(value: i128, width: u32) -> Option<bool> {
    let (min, max) = signed_range(width)?;
    Some(value < min || value > max)
}

fn signed_overflow(kind: ArithUbKind, lhs: u64, rhs: Option<u64>, width: u32) -> Option<bool> {
    let lhs = to_signed(lhs, width)?;
    match kind {
        ArithUbKind::Sadd => {
            let rhs = to_signed(rhs?, width)?;
            outside_signed_range(lhs + rhs, width)
        }
        ArithUbKind::Ssub => {
            let rhs = to_signed(rhs?, width)?;
            outside_signed_range(lhs - rhs, width)
        }
        ArithUbKind::Smul => {
            let rhs = to_signed(rhs?, width)?;
            outside_signed_range(lhs * rhs, width)
        }
        ArithUbKind::Sneg => outside_signed_range(-lhs, width),
        ArithUbKind::Udiv | ArithUbKind::Sdiv | ArithUbKind::Urem | ArithUbKind::Srem => None,
    }
}

fn has_div_rem_ub_witness(op: &ArithOp, env: &HashMap<String, u64>) -> bool {
    let Some(rhs) = eval_bv(&op.rhs, env) else {
        return false;
    };

    if mask(rhs, op.width) == 0 {
        return true;
    }

    let Some(lhs) = eval_bv(&op.lhs, env) else {
        return false;
    };

    signed_min_div_minus_one(op.kind, mask(lhs, op.width), mask(rhs, op.width), op.width)
}

fn has_signed_overflow_witness(op: &ArithOp, env: &HashMap<String, u64>) -> bool {
    let Some(lhs) = eval_bv(&op.lhs, env) else {
        return false;
    };

    let rhs = if matches!(op.kind, ArithUbKind::Sneg) {
        None
    } else {
        let Some(rhs) = eval_bv(&op.rhs, env) else {
            return false;
        };
        Some(rhs)
    };

    signed_overflow(op.kind, lhs, rhs, op.width).unwrap_or(false)
}

fn has_ub_witness(op: &ArithOp, env: &HashMap<String, u64>) -> bool {
    match op.kind {
        ArithUbKind::Udiv | ArithUbKind::Sdiv | ArithUbKind::Urem | ArithUbKind::Srem => {
            has_div_rem_ub_witness(op, env)
        }
        ArithUbKind::Sadd | ArithUbKind::Ssub | ArithUbKind::Smul | ArithUbKind::Sneg => {
            has_signed_overflow_witness(op, env)
        }
    }
}

fn div_rem_trivially_safe(op: &ArithOp, empty_env: &HashMap<String, u64>) -> bool {
    let Some(rhs) = eval_bv(&op.rhs, empty_env).map(|value| mask(value, op.width)) else {
        return false;
    };

    if rhs == 0 {
        return false;
    }

    match op.kind {
        ArithUbKind::Udiv | ArithUbKind::Urem => true,
        ArithUbKind::Sdiv | ArithUbKind::Srem => {
            let Some(negative_one) = minus_one(op.width) else {
                return false;
            };
            if rhs != negative_one {
                return true;
            }

            let Some(lhs) = eval_bv(&op.lhs, empty_env).map(|value| mask(value, op.width)) else {
                return false;
            };
            !signed_min_div_minus_one(op.kind, lhs, rhs, op.width)
        }
        ArithUbKind::Sadd | ArithUbKind::Ssub | ArithUbKind::Smul | ArithUbKind::Sneg => false,
    }
}

fn signed_overflow_trivially_safe(op: &ArithOp, empty_env: &HashMap<String, u64>) -> bool {
    let Some(lhs) = eval_bv(&op.lhs, empty_env) else {
        return false;
    };

    let rhs = if matches!(op.kind, ArithUbKind::Sneg) {
        None
    } else {
        let Some(rhs) = eval_bv(&op.rhs, empty_env) else {
            return false;
        };
        Some(rhs)
    };

    signed_overflow(op.kind, lhs, rhs, op.width) == Some(false)
}

fn trivially_safe(op: &ArithOp) -> bool {
    let empty_env = HashMap::new();
    match op.kind {
        ArithUbKind::Udiv | ArithUbKind::Sdiv | ArithUbKind::Urem | ArithUbKind::Srem => {
            div_rem_trivially_safe(op, &empty_env)
        }
        ArithUbKind::Sadd | ArithUbKind::Ssub | ArithUbKind::Smul | ArithUbKind::Sneg => {
            signed_overflow_trivially_safe(op, &empty_env)
        }
    }
}

/// Check one arithmetic operation against its path context.
///
/// The fast evaluator reports:
/// - [`FsymVerdict::Safe`] for concrete side conditions that cannot trigger UB.
/// - [`FsymVerdict::Ub`] when a candidate environment satisfies the path guards
///   and makes an arithmetic UB side condition true.
/// - [`FsymVerdict::Unknown`] when no evaluator witness is found and SMT would
///   be needed to prove safety.
pub fn check_arith_ub(op: &ArithOp, ctx: &PathContext) -> FsymVerdict {
    if op.width == 0 || op.width > 64 {
        return no_witness_found();
    }

    if trivially_safe(op) {
        return FsymVerdict::Safe;
    }

    let empty_env = HashMap::new();
    let candidates: &[HashMap<String, u64>] = if ctx.witness_candidates.is_empty() {
        std::slice::from_ref(&empty_env)
    } else {
        ctx.witness_candidates.as_slice()
    };

    for env in candidates {
        if !guards_hold(&ctx.guards, env) {
            continue;
        }

        if has_ub_witness(op, env) {
            return FsymVerdict::Ub {
                witness: env.clone(),
            };
        }
    }

    no_witness_found()
}

/// Check one division/remainder operation against its path context.
pub fn check_div_rem_ub(op: &ArithOp, ctx: &PathContext) -> FsymVerdict {
    match op.kind {
        ArithUbKind::Udiv | ArithUbKind::Sdiv | ArithUbKind::Urem | ArithUbKind::Srem => {
            check_arith_ub(op, ctx)
        }
        ArithUbKind::Sadd | ArithUbKind::Ssub | ArithUbKind::Smul | ArithUbKind::Sneg => {
            no_witness_found()
        }
    }
}

/// Check one source/trapping signed overflow operation against its path context.
pub fn check_signed_overflow_ub(op: &ArithOp, ctx: &PathContext) -> FsymVerdict {
    match op.kind {
        ArithUbKind::Sadd | ArithUbKind::Ssub | ArithUbKind::Smul | ArithUbKind::Sneg => {
            check_arith_ub(op, ctx)
        }
        ArithUbKind::Udiv | ArithUbKind::Sdiv | ArithUbKind::Urem | ArithUbKind::Srem => {
            no_witness_found()
        }
    }
}

/// Scan a collection of arithmetic ops sharing one path context; return
/// each verdict tagged with its op label.
#[cfg(feature = "fsym")]
pub fn run_arith_ub_scan(ops: &[ArithOp], ctx: &PathContext) -> Vec<(String, FsymVerdict)> {
    ops.iter()
        .map(|op| (op.label.clone(), check_arith_ub(op, ctx)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{ArithOp, ArithUbKind, check_div_rem_ub, check_signed_overflow_ub};
    use crate::fsym_null::{FsymVerdict, PathContext};
    use crate::smt::SmtExpr;
    use std::collections::HashMap;

    fn op(kind: ArithUbKind, lhs: SmtExpr, rhs: SmtExpr, width: u32) -> ArithOp {
        ArithOp {
            label: "arith".to_string(),
            kind,
            lhs,
            rhs,
            width,
        }
    }

    fn ctx(guards: Vec<SmtExpr>, witness_candidates: Vec<HashMap<String, u64>>) -> PathContext {
        PathContext {
            guards,
            witness_candidates,
        }
    }

    fn unknown() -> FsymVerdict {
        FsymVerdict::Unknown {
            reason: "no witness found in evaluator; escalate to SMT".to_string(),
        }
    }

    #[test]
    fn concrete_udiv_by_zero_is_ub() {
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Udiv,
                    SmtExpr::bv_const(42, 32),
                    SmtExpr::bv_const(0, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn concrete_udiv_by_zero_under_false_guard_is_not_ub() {
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Udiv,
                    SmtExpr::bv_const(42, 32),
                    SmtExpr::bv_const(0, 32),
                    32,
                ),
                &ctx(vec![SmtExpr::bool_const(false)], vec![]),
            ),
            unknown()
        );
    }

    #[test]
    fn concrete_urem_nonzero_divisor_is_safe() {
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Urem,
                    SmtExpr::bv_const(42, 32),
                    SmtExpr::bv_const(5, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn i1_bitvector_guard_allows_zero_divisor_witness() {
        let guard = SmtExpr::var("g", 1);
        let witness = HashMap::from([(String::from("g"), 1_u64)]);
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Udiv,
                    SmtExpr::bv_const(42, 32),
                    SmtExpr::bv_const(0, 32),
                    32,
                ),
                &ctx(vec![guard], vec![witness.clone()]),
            ),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn i1_bitvector_guard_blocks_zero_divisor_witness() {
        let guard = SmtExpr::var("g", 1);
        let witness = HashMap::from([(String::from("g"), 0_u64)]);
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Udiv,
                    SmtExpr::bv_const(42, 32),
                    SmtExpr::bv_const(0, 32),
                    32,
                ),
                &ctx(vec![guard], vec![witness]),
            ),
            unknown()
        );
    }

    #[test]
    fn wide_bitvector_guard_one_blocks_zero_divisor_witness() {
        let guard = SmtExpr::var("g", 8);
        let witness = HashMap::from([(String::from("g"), 1_u64)]);
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Udiv,
                    SmtExpr::bv_const(42, 32),
                    SmtExpr::bv_const(0, 32),
                    32,
                ),
                &ctx(vec![guard], vec![witness]),
            ),
            unknown()
        );
    }

    #[test]
    fn symbolic_sdiv_zero_divisor_witness_found() {
        let witness = HashMap::from([(String::from("a"), 99_u64), (String::from("b"), 0_u64)]);
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Sdiv,
                    SmtExpr::var("a", 64),
                    SmtExpr::var("b", 64),
                    64,
                ),
                &ctx(vec![], vec![witness.clone()]),
            ),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn symbolic_urem_nonzero_candidate_yields_unknown() {
        let witness = HashMap::from([(String::from("a"), 99_u64), (String::from("b"), 3_u64)]);
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Urem,
                    SmtExpr::var("a", 64),
                    SmtExpr::var("b", 64),
                    64,
                ),
                &ctx(vec![], vec![witness]),
            ),
            unknown()
        );
    }

    #[test]
    fn path_guard_blocks_zero_divisor_witness() {
        let guard = SmtExpr::var("g", 1).eq_expr(SmtExpr::bv_const(1, 1));
        let witness = HashMap::from([
            (String::from("a"), 99_u64),
            (String::from("b"), 0_u64),
            (String::from("g"), 0_u64),
        ]);
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Udiv,
                    SmtExpr::var("a", 64),
                    SmtExpr::var("b", 64),
                    64,
                ),
                &ctx(vec![guard], vec![witness]),
            ),
            unknown()
        );
    }

    #[test]
    fn path_guard_allows_zero_divisor_witness() {
        let guard = SmtExpr::var("g", 1).eq_expr(SmtExpr::bv_const(1, 1));
        let witness = HashMap::from([
            (String::from("a"), 99_u64),
            (String::from("b"), 0_u64),
            (String::from("g"), 1_u64),
        ]);
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Udiv,
                    SmtExpr::var("a", 64),
                    SmtExpr::var("b", 64),
                    64,
                ),
                &ctx(vec![guard], vec![witness.clone()]),
            ),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn source_trapping_signed_int_min_div_minus_one_is_ub() {
        // This pins the fsym source/trapping obligation, not current trust_ir
        // wrapping `Sdiv` semantics or pipeline behavior.
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Sdiv,
                    SmtExpr::bv_const(0x8000_0000, 32),
                    SmtExpr::bv_const(0xffff_ffff, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn source_trapping_signed_int_min_rem_minus_one_is_ub() {
        // This pins the fsym source/trapping obligation, not current trust_ir
        // wrapping `Srem` semantics or pipeline behavior.
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Srem,
                    SmtExpr::bv_const(0x80, 8),
                    SmtExpr::bv_const(0xff, 8),
                    8,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn signed_div_by_minus_one_with_non_min_lhs_is_safe() {
        assert_eq!(
            check_div_rem_ub(
                &op(
                    ArithUbKind::Sdiv,
                    SmtExpr::bv_const(7, 32),
                    SmtExpr::bv_const(0xffff_ffff, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn concrete_signed_add_no_overflow_is_safe() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Sadd,
                    SmtExpr::bv_const(40, 32),
                    SmtExpr::bv_const(2, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn concrete_signed_sub_no_overflow_is_safe() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Ssub,
                    SmtExpr::bv_const(10, 32),
                    SmtExpr::bv_const(3, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn concrete_signed_mul_no_overflow_is_safe() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Smul,
                    SmtExpr::bv_const(5, 32),
                    SmtExpr::bv_const(6, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn source_trapping_signed_add_overflow_is_ub() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Sadd,
                    SmtExpr::bv_const(0x7fff_ffff, 32),
                    SmtExpr::bv_const(1, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn source_trapping_signed_sub_overflow_is_ub() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Ssub,
                    SmtExpr::bv_const(0x80, 8),
                    SmtExpr::bv_const(1, 8),
                    8,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn source_trapping_signed_mul_overflow_is_ub() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Smul,
                    SmtExpr::bv_const(0x40, 8),
                    SmtExpr::bv_const(2, 8),
                    8,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn source_trapping_signed_neg_int_min_is_ub() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Sneg,
                    SmtExpr::bv_const(0x8000_0000, 32),
                    SmtExpr::bv_const(0, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn signed_neg_non_min_is_safe() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Sneg,
                    SmtExpr::bv_const(7, 32),
                    SmtExpr::bv_const(0, 32),
                    32,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn symbolic_signed_add_overflow_witness_found() {
        let witness = HashMap::from([(String::from("a"), 0x7f_u64), (String::from("b"), 1_u64)]);
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Sadd,
                    SmtExpr::var("a", 8),
                    SmtExpr::var("b", 8),
                    8,
                ),
                &ctx(vec![], vec![witness.clone()]),
            ),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn concrete_signed_add_overflow_under_false_guard_is_not_ub() {
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Sadd,
                    SmtExpr::bv_const(0x7fff_ffff, 32),
                    SmtExpr::bv_const(1, 32),
                    32,
                ),
                &ctx(vec![SmtExpr::bool_const(false)], vec![]),
            ),
            unknown()
        );
    }

    #[test]
    fn i1_bitvector_guard_allows_signed_add_overflow_witness() {
        let guard = SmtExpr::var("g", 1);
        let witness = HashMap::from([
            (String::from("a"), 0x7f_u64),
            (String::from("b"), 1_u64),
            (String::from("g"), 1_u64),
        ]);
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Sadd,
                    SmtExpr::var("a", 8),
                    SmtExpr::var("b", 8),
                    8,
                ),
                &ctx(vec![guard], vec![witness.clone()]),
            ),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn wide_bitvector_guard_one_blocks_signed_add_overflow_witness() {
        let guard = SmtExpr::var("g", 8);
        let witness = HashMap::from([
            (String::from("a"), 0x7f_u64),
            (String::from("b"), 1_u64),
            (String::from("g"), 1_u64),
        ]);
        assert_eq!(
            check_signed_overflow_ub(
                &op(
                    ArithUbKind::Sadd,
                    SmtExpr::var("a", 8),
                    SmtExpr::var("b", 8),
                    8,
                ),
                &ctx(vec![guard], vec![witness]),
            ),
            unknown()
        );
    }

    #[test]
    fn fork_branch_i1_else_path_allows_signed_add_overflow_witness() {
        let witness = HashMap::from([
            (String::from("a"), 0x7f_u64),
            (String::from("b"), 1_u64),
            (String::from("g"), 0_u64),
        ]);
        let fork = ctx(vec![], vec![witness.clone()]).fork_branch(SmtExpr::var("g", 1));
        let add = op(
            ArithUbKind::Sadd,
            SmtExpr::var("a", 8),
            SmtExpr::var("b", 8),
            8,
        );

        assert_eq!(check_signed_overflow_ub(&add, &fork.then_ctx), unknown());
        assert_eq!(
            check_signed_overflow_ub(&add, &fork.else_ctx),
            FsymVerdict::Ub { witness }
        );
    }
}
