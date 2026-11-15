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
    /// `shl` / `lshr` / `ashr`: UB when the amount (`rhs`, read unsigned) is
    /// not below the bit width. trust-ir's `ShiftInRange` obligation
    /// (ub-numerics-policy section 1: an out-of-range amount is UB / poison,
    /// NOT masked); the reference interpreter reports "shift amount N is out
    /// of range". `lhs` is carried but plays no part in the condition.
    ShiftAmount,
    /// An access at byte offset `lhs` from a base aligned to (at least)
    /// `align` bytes: UB when `lhs & (align - 1) != 0`. Unary: `rhs` is
    /// ignored.
    Misaligned { align: u64 },
    /// GEP offset arithmetic exactly as trust-ir's reference interpreter
    /// performs it. `lhs` is the index widened to 64 bits (sign-extended when
    /// `signed_index`), `rhs` the 64-bit base it is added to (the byte offset
    /// within a tracked object, or an exact address). UB when a signed index
    /// is negative, or when `index * elem_size + base` exceeds `limit`:
    /// `u64::MAX` for an offset or a 64-bit address ("GEP: negative index",
    /// "byte offset overflow", "pointer offset overflow"), the target's
    /// highest address (`2^32 - 1` on a 32-bit target) for an exact address
    /// there ("address is outside the target's address space"). Width is
    /// always 64. The limit is part of the kind so that every consumer of it
    /// — the evaluator and every solver candidate — decides the TARGET's
    /// condition, never only the 64-bit one.
    GepOffset {
        elem_size: u64,
        signed_index: bool,
        limit: u64,
    },
}

impl ArithUbKind {
    /// True for a kind whose side condition reads only `lhs`.
    pub fn is_unary(self) -> bool {
        matches!(self, ArithUbKind::Sneg | ArithUbKind::Misaligned { .. })
    }
}

/// Decide the UB side condition of one of the pointer / shift kinds
/// (`ShiftAmount`, `Misaligned`, `GepOffset`) on concrete `width`-bit
/// operands. `None` for any other kind, a missing `rhs`, or a width the kind
/// is not defined at.
pub fn memory_arith_ub_on_values(
    kind: ArithUbKind,
    lhs: u64,
    rhs: Option<u64>,
    width: u32,
) -> Option<bool> {
    if !(1..=64).contains(&width) {
        return None;
    }
    match kind {
        ArithUbKind::ShiftAmount => Some(u128::from(mask(rhs?, width)) >= u128::from(width)),
        ArithUbKind::Misaligned { align } => {
            if align == 0 || !align.is_power_of_two() {
                return None;
            }
            Some(mask(lhs, width) & (align - 1) != 0)
        }
        ArithUbKind::GepOffset {
            elem_size,
            signed_index,
            limit,
        } => {
            if width != 64 {
                return None;
            }
            if signed_index && (lhs as i64) < 0 {
                return Some(true);
            }
            let end = u128::from(lhs) * u128::from(elem_size) + u128::from(rhs?);
            Some(end > u128::from(limit))
        }
        ArithUbKind::Udiv
        | ArithUbKind::Sdiv
        | ArithUbKind::Urem
        | ArithUbKind::Srem
        | ArithUbKind::Sadd
        | ArithUbKind::Ssub
        | ArithUbKind::Smul
        | ArithUbKind::Sneg => None,
    }
}

/// The memory/shift kinds, decided in one environment: `Some(true)` UB,
/// `Some(false)` no UB, `None` an operand did not evaluate.
fn memory_arith_ub_in(op: &ArithOp, env: &HashMap<String, u64>) -> Option<bool> {
    // A shift's condition reads only the amount: the shifted value may stay
    // symbolic.
    let lhs = if op.kind == ArithUbKind::ShiftAmount {
        0
    } else {
        eval_bv(&op.lhs, env)?
    };
    let rhs = if op.kind.is_unary() {
        None
    } else {
        Some(eval_bv(&op.rhs, env)?)
    };
    memory_arith_ub_on_values(op.kind, lhs, rhs, op.width)
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
        ArithUbKind::Udiv
        | ArithUbKind::Sdiv
        | ArithUbKind::Urem
        | ArithUbKind::Srem
        | ArithUbKind::ShiftAmount
        | ArithUbKind::Misaligned { .. }
        | ArithUbKind::GepOffset { .. } => None,
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
        ArithUbKind::ShiftAmount
        | ArithUbKind::Misaligned { .. }
        | ArithUbKind::GepOffset { .. } => memory_arith_ub_in(op, env) == Some(true),
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
        ArithUbKind::Sadd
        | ArithUbKind::Ssub
        | ArithUbKind::Smul
        | ArithUbKind::Sneg
        | ArithUbKind::ShiftAmount
        | ArithUbKind::Misaligned { .. }
        | ArithUbKind::GepOffset { .. } => false,
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
        ArithUbKind::Misaligned { align } => {
            memory_arith_ub_in(op, &empty_env) == Some(false)
                || (align.is_power_of_two()
                    && known_trailing_zeros(&op.lhs) >= align.trailing_zeros())
        }
        ArithUbKind::ShiftAmount => {
            memory_arith_ub_in(op, &empty_env) == Some(false)
                || known_unsigned_max(&op.rhs).is_some_and(|max| max < u64::from(op.width))
        }
        ArithUbKind::GepOffset { .. } => memory_arith_ub_in(op, &empty_env) == Some(false),
    }
}

/// An upper bound on `expr`'s unsigned value under every assignment, from its
/// structure, when one is known: `x & 63` is at most 63 (the masked shift
/// amount Rust emits), `x % 8` at most 7, a zero-extended `u8` at most 255.
pub fn known_unsigned_max(expr: &SmtExpr) -> Option<u64> {
    match expr {
        SmtExpr::BvConst { value, .. } => Some(*value),
        SmtExpr::BvAnd { lhs, rhs, .. } => match (known_unsigned_max(lhs), known_unsigned_max(rhs))
        {
            (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
            (bound, None) | (None, bound) => bound,
        },
        SmtExpr::BvURem { lhs, rhs, .. } => {
            let by_divisor = match rhs.as_ref() {
                SmtExpr::BvConst { value, .. } if *value > 0 => Some(*value - 1),
                _ => None,
            };
            match (known_unsigned_max(lhs), by_divisor) {
                (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
                (bound, None) | (None, bound) => bound,
            }
        }
        SmtExpr::BvLshr { lhs, rhs, width } => match rhs.as_ref() {
            SmtExpr::BvConst { value, .. } if *value < u64::from(*width) => {
                let max = known_unsigned_max(lhs).unwrap_or_else(|| mask(u64::MAX, *width));
                Some(max >> value)
            }
            _ => None,
        },
        SmtExpr::ZeroExtend { operand, .. } => known_unsigned_max(operand).or_else(|| {
            let width = operand.try_bv_width().ok()?;
            (width < 64).then(|| mask(u64::MAX, width))
        }),
        _ => None,
    }
}

/// A lower bound on the trailing zero bits of `expr`'s value under every
/// assignment, from its structure: `i * 8 + 16` has at least 3. Wrapping
/// arithmetic keeps the bound (multiplying or adding modulo `2^w` never sets a
/// bit below the operands' common trailing zeros).
pub fn known_trailing_zeros(expr: &SmtExpr) -> u32 {
    let width = expr.try_bv_width().unwrap_or(0);
    let bound = match expr {
        SmtExpr::BvConst { value, width } => value.trailing_zeros().min(*width),
        SmtExpr::BvMul { lhs, rhs, .. } => {
            known_trailing_zeros(lhs).saturating_add(known_trailing_zeros(rhs))
        }
        SmtExpr::BvAdd { lhs, rhs, .. } | SmtExpr::BvSub { lhs, rhs, .. } => {
            known_trailing_zeros(lhs).min(known_trailing_zeros(rhs))
        }
        SmtExpr::BvShl { lhs, rhs, .. } => match rhs.as_ref() {
            SmtExpr::BvConst { value, .. } => {
                known_trailing_zeros(lhs).saturating_add(u32::try_from(*value).unwrap_or(u32::MAX))
            }
            _ => known_trailing_zeros(lhs),
        },
        SmtExpr::ZeroExtend { operand, .. } | SmtExpr::SignExtend { operand, .. } => {
            known_trailing_zeros(operand)
        }
        _ => 0,
    };
    bound.min(width)
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
        ArithUbKind::Sadd
        | ArithUbKind::Ssub
        | ArithUbKind::Smul
        | ArithUbKind::Sneg
        | ArithUbKind::ShiftAmount
        | ArithUbKind::Misaligned { .. }
        | ArithUbKind::GepOffset { .. } => no_witness_found(),
    }
}

/// Check one source/trapping signed overflow operation against its path context.
pub fn check_signed_overflow_ub(op: &ArithOp, ctx: &PathContext) -> FsymVerdict {
    match op.kind {
        ArithUbKind::Sadd | ArithUbKind::Ssub | ArithUbKind::Smul | ArithUbKind::Sneg => {
            check_arith_ub(op, ctx)
        }
        ArithUbKind::Udiv
        | ArithUbKind::Sdiv
        | ArithUbKind::Urem
        | ArithUbKind::Srem
        | ArithUbKind::ShiftAmount
        | ArithUbKind::Misaligned { .. }
        | ArithUbKind::GepOffset { .. } => no_witness_found(),
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
    use super::{
        ArithOp, ArithUbKind, check_arith_ub, check_div_rem_ub, check_signed_overflow_ub,
        known_trailing_zeros,
    };
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

    #[test]
    fn shift_amount_is_ub_at_or_past_the_width() {
        let shift = |amount: u64| {
            check_arith_ub(
                &op(
                    ArithUbKind::ShiftAmount,
                    SmtExpr::var("x", 64),
                    SmtExpr::bv_const(amount, 64),
                    64,
                ),
                &ctx(vec![], vec![]),
            )
        };
        // The shifted value plays no part: a symbolic one is still decided.
        assert_eq!(shift(63), FsymVerdict::Safe);
        assert!(matches!(shift(64), FsymVerdict::Ub { .. }));
        assert!(matches!(shift(u64::MAX), FsymVerdict::Ub { .. }));
    }

    #[test]
    fn masked_shift_amount_is_proven_in_range() {
        use super::known_unsigned_max;
        let masked = SmtExpr::var("n", 64).bvand(SmtExpr::bv_const(63, 64));
        assert_eq!(known_unsigned_max(&masked), Some(63));
        assert_eq!(
            check_arith_ub(
                &op(
                    ArithUbKind::ShiftAmount,
                    SmtExpr::bv_const(1, 64),
                    masked,
                    64,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
        // `n & 64` may be 64: not proven.
        let wide = SmtExpr::var("n", 64).bvand(SmtExpr::bv_const(64, 64));
        assert_eq!(
            check_arith_ub(
                &op(ArithUbKind::ShiftAmount, SmtExpr::bv_const(1, 64), wide, 64),
                &ctx(vec![], vec![]),
            ),
            unknown()
        );
    }

    #[test]
    fn gep_offset_is_ub_on_negative_index_or_64_bit_overflow() {
        let gep_at = |index: u64, base: u64, signed_index: bool, limit: u64| {
            check_arith_ub(
                &op(
                    ArithUbKind::GepOffset {
                        elem_size: 8,
                        signed_index,
                        limit,
                    },
                    SmtExpr::bv_const(index, 64),
                    SmtExpr::bv_const(base, 64),
                    64,
                ),
                &ctx(vec![], vec![]),
            )
        };
        let gep = |index, base, signed_index| gep_at(index, base, signed_index, u64::MAX);
        assert_eq!(gep(3, 16, true), FsymVerdict::Safe);
        assert!(matches!(gep(u64::MAX, 16, true), FsymVerdict::Ub { .. }));
        // The same bits as an unsigned index overflow instead.
        assert!(matches!(gep(u64::MAX, 16, false), FsymVerdict::Ub { .. }));
        assert!(matches!(gep(1, u64::MAX - 7, true), FsymVerdict::Ub { .. }));
        assert_eq!(gep(1, u64::MAX - 8, true), FsymVerdict::Safe);
        // A 32-bit target's limit is its highest address.
        let limit = u64::from(u32::MAX);
        assert_eq!(gep_at(1, limit - 8, true, limit), FsymVerdict::Safe);
        assert!(matches!(
            gep_at(1, limit - 7, true, limit),
            FsymVerdict::Ub { .. }
        ));
    }

    #[test]
    fn alignment_is_proven_from_known_trailing_zeros() {
        let aligned = |offset: SmtExpr| {
            check_arith_ub(
                &op(
                    ArithUbKind::Misaligned { align: 8 },
                    offset,
                    SmtExpr::bv_const(0, 64),
                    64,
                ),
                &ctx(vec![], vec![]),
            )
        };
        assert_eq!(aligned(SmtExpr::bv_const(16, 64)), FsymVerdict::Safe);
        assert!(matches!(
            aligned(SmtExpr::bv_const(12, 64)),
            FsymVerdict::Ub { .. }
        ));
        // `i * 8 + 16`: three trailing zeros whatever `i` is.
        let scaled = SmtExpr::var("i", 64)
            .bvmul(SmtExpr::bv_const(8, 64))
            .bvadd(SmtExpr::bv_const(16, 64));
        assert_eq!(known_trailing_zeros(&scaled), 3);
        assert_eq!(aligned(scaled), FsymVerdict::Safe);
        // `i * 4` proves only 4-byte alignment.
        let quad = SmtExpr::var("i", 64).bvmul(SmtExpr::bv_const(4, 64));
        assert_eq!(aligned(quad), unknown());
    }
}
