// Symbolic execution: out-of-bounds byte-range detector
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Symbolic execution: out-of-bounds byte-range detector (Phase 1c).
//!
//! This evaluator-only checker is the bounds companion to [`crate::fsym_null`]
//! and [`crate::fsym_arith`]. It checks byte-addressed memory accesses against
//! an object size using candidate concrete witnesses before future pipeline
//! wiring escalates unknown cases to SMT.

use crate::fsym_null::{FsymVerdict, PathContext, guards_hold};
use crate::smt::{EvalResult, SmtExpr};
use std::collections::HashMap;

/// Metadata about a byte-range memory access being checked.
#[derive(Debug, Clone)]
pub struct BoundsOp {
    /// Human-friendly label, e.g. "load bb3/inst12".
    pub label: String,
    /// Signed byte offset from the start of the object.
    pub byte_offset: SmtExpr,
    /// Unsigned object size in bytes.
    pub object_size_bytes: SmtExpr,
    /// Access width in bytes.
    pub access_size_bytes: u64,
    /// If true, caller has vouched for bounds safety via an InBounds proof
    /// annotation; the evaluator short-circuits to Safe.
    pub has_in_bounds_annotation: bool,
}

fn no_witness_found() -> FsymVerdict {
    FsymVerdict::Unknown {
        reason: "no witness found in evaluator; escalate to SMT".to_string(),
    }
}

fn eval_bv(expr: &SmtExpr, env: &HashMap<String, u64>) -> Option<(u128, u32)> {
    let width = expr.try_bv_width().ok()?;
    if width == 0 || width > 128 {
        return None;
    }

    match expr.try_eval(env).ok()? {
        EvalResult::Bv(value) => Some((value as u128, width)),
        EvalResult::Bv128(value) => Some((value, width)),
        // Poison (a trapping-op result) has no defined bitvector; fail closed.
        EvalResult::Bool(_)
        | EvalResult::Float(_)
        | EvalResult::Array { .. }
        | EvalResult::Poison => None,
    }
}

fn has_sign_bit(value: u128, width: u32) -> bool {
    debug_assert!((1..=128).contains(&width));
    value & (1_u128 << (width - 1)) != 0
}

fn byte_range_is_oob(op: &BoundsOp, env: &HashMap<String, u64>) -> Option<bool> {
    let (offset, offset_width) = eval_bv(&op.byte_offset, env)?;
    if has_sign_bit(offset, offset_width) {
        return Some(true);
    }

    let (object_size, _) = eval_bv(&op.object_size_bytes, env)?;
    let end = offset.checked_add(op.access_size_bytes as u128)?;
    Some(end > object_size)
}

fn trivially_safe(op: &BoundsOp) -> bool {
    let empty_env = HashMap::new();
    byte_range_is_oob(op, &empty_env) == Some(false)
}

/// Check one byte-range memory operation against its path context.
///
/// The fast evaluator reports:
/// - [`FsymVerdict::Safe`] for InBounds annotations and concrete in-bounds
///   byte ranges.
/// - [`FsymVerdict::Ub`] when a candidate environment satisfies all path guards
///   and makes either `offset < 0` or `offset + access_size > object_size` true.
/// - [`FsymVerdict::Unknown`] when no evaluator witness is found and SMT would
///   be needed to prove safety.
pub fn check_oob_ub(op: &BoundsOp, ctx: &PathContext) -> FsymVerdict {
    if op.has_in_bounds_annotation || trivially_safe(op) {
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

        if byte_range_is_oob(op, env) == Some(true) {
            return FsymVerdict::Ub {
                witness: env.clone(),
            };
        }
    }

    no_witness_found()
}

/// Scan a collection of byte-range memory ops sharing one path context; return
/// each verdict tagged with its op label.
#[cfg(feature = "fsym")]
pub fn run_oob_scan(ops: &[BoundsOp], ctx: &PathContext) -> Vec<(String, FsymVerdict)> {
    ops.iter()
        .map(|op| (op.label.clone(), check_oob_ub(op, ctx)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{BoundsOp, check_oob_ub};
    use crate::fsym_null::{FsymVerdict, PathContext};
    use crate::smt::SmtExpr;
    use std::collections::HashMap;

    fn op(byte_offset: SmtExpr, object_size_bytes: SmtExpr, access_size_bytes: u64) -> BoundsOp {
        BoundsOp {
            label: "bounds".to_string(),
            byte_offset,
            object_size_bytes,
            access_size_bytes,
            has_in_bounds_annotation: false,
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
    fn concrete_in_bounds_is_safe() {
        assert_eq!(
            check_oob_ub(
                &op(SmtExpr::bv_const(4, 64), SmtExpr::bv_const(16, 64), 4),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn concrete_negative_offset_is_ub() {
        assert_eq!(
            check_oob_ub(
                &op(
                    SmtExpr::bv_const(u64::MAX, 64),
                    SmtExpr::bv_const(16, 64),
                    1,
                ),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn concrete_end_past_object_is_ub() {
        assert_eq!(
            check_oob_ub(
                &op(SmtExpr::bv_const(13, 64), SmtExpr::bv_const(16, 64), 4),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Ub {
                witness: HashMap::new(),
            }
        );
    }

    #[test]
    fn exact_end_is_safe() {
        assert_eq!(
            check_oob_ub(
                &op(SmtExpr::bv_const(12, 64), SmtExpr::bv_const(16, 64), 4),
                &ctx(vec![], vec![]),
            ),
            FsymVerdict::Safe
        );
    }

    #[test]
    fn symbolic_offset_oob_witness_found() {
        let witness = HashMap::from([(String::from("i"), 13_u64)]);
        assert_eq!(
            check_oob_ub(
                &op(SmtExpr::var("i", 64), SmtExpr::bv_const(16, 64), 4),
                &ctx(vec![], vec![witness.clone()]),
            ),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn symbolic_object_size_oob_witness_found() {
        let witness = HashMap::from([(String::from("n"), 15_u64)]);
        assert_eq!(
            check_oob_ub(
                &op(SmtExpr::bv_const(12, 64), SmtExpr::var("n", 64), 4),
                &ctx(vec![], vec![witness.clone()]),
            ),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn false_guard_blocks_concrete_oob() {
        assert_eq!(
            check_oob_ub(
                &op(SmtExpr::bv_const(13, 64), SmtExpr::bv_const(16, 64), 4),
                &ctx(vec![SmtExpr::bool_const(false)], vec![]),
            ),
            unknown()
        );
    }

    #[test]
    fn i1_bitvector_guard_allows_oob_witness() {
        let guard = SmtExpr::var("g", 1);
        let witness = HashMap::from([(String::from("g"), 1_u64)]);
        assert_eq!(
            check_oob_ub(
                &op(SmtExpr::bv_const(13, 64), SmtExpr::bv_const(16, 64), 4),
                &ctx(vec![guard], vec![witness.clone()]),
            ),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn wide_bitvector_guard_blocks_oob_witness() {
        let guard = SmtExpr::var("g", 8);
        let witness = HashMap::from([(String::from("g"), 1_u64)]);
        assert_eq!(
            check_oob_ub(
                &op(SmtExpr::bv_const(13, 64), SmtExpr::bv_const(16, 64), 4),
                &ctx(vec![guard], vec![witness]),
            ),
            unknown()
        );
    }

    #[test]
    fn fork_branch_i1_else_path_allows_oob_witness() {
        let witness = HashMap::from([(String::from("i"), 13_u64), (String::from("g"), 0_u64)]);
        let fork = ctx(vec![], vec![witness.clone()]).fork_branch(SmtExpr::var("g", 1));
        let bounds = op(SmtExpr::var("i", 64), SmtExpr::bv_const(16, 64), 4);

        assert_eq!(check_oob_ub(&bounds, &fork.then_ctx), unknown());
        assert_eq!(
            check_oob_ub(&bounds, &fork.else_ctx),
            FsymVerdict::Ub { witness }
        );
    }

    #[test]
    fn in_bounds_annotation_short_circuits() {
        let mut bounds = op(
            SmtExpr::bv_const(u64::MAX, 64),
            SmtExpr::bv_const(16, 64),
            1,
        );
        bounds.has_in_bounds_annotation = true;

        assert_eq!(
            check_oob_ub(&bounds, &ctx(vec![], vec![])),
            FsymVerdict::Safe
        );
    }

    #[cfg(feature = "fsym")]
    #[test]
    fn run_oob_scan_tags_labels() {
        let ops = vec![BoundsOp {
            label: "load0".to_string(),
            byte_offset: SmtExpr::bv_const(0, 64),
            object_size_bytes: SmtExpr::bv_const(4, 64),
            access_size_bytes: 8,
            has_in_bounds_annotation: false,
        }];

        assert_eq!(
            super::run_oob_scan(&ops, &ctx(vec![], vec![])),
            vec![(
                "load0".to_string(),
                FsymVerdict::Ub {
                    witness: HashMap::new(),
                }
            )]
        );
    }
}
