// ROUND 31 / TRUST BATCH 18 — NEGATIVE SLICE (does NOT emit).
// Verbatim transcription of trust-cg-codegen/src/interpreter.rs `eval_fcmp` (:880).
// The emit-closure frontend (mir_lower.rs) CANNOT lower this: `scalar_tir_ty`
// (mir_lower.rs:116) returns None for ty::Float, so the direct float comparisons
// `lhs < rhs` etc. fail with `place leaf is not a memory scalar: float`
// (place_leaf_tir_ty, mir_lower.rs:5178). Kept as the documented non-emitting
// source; the round verifies eval_fcmp via the production interpret() entry and a
// hand-built trust-ir FCmp module instead (see e2e_trust_fns_round18.rs).

#![allow(dead_code)]
#![allow(unused_variables)]

// Verbatim transcription of trust-cg-codegen/src/interpreter.rs eval_fcmp (line 880),
// as a free fn over a local FCmpOp enum matching trust_ir::FCmpOp's 12 variants.
#[derive(Clone, Copy)]
pub enum FCmpOp {
    OEq, ONe, OLt, OLe, OGt, OGe,
    UEq, UNe, ULt, ULe, UGt, UGe,
}

pub fn eval_fcmp(op: FCmpOp, lhs: f64, rhs: f64) -> bool {
    match op {
        FCmpOp::OEq => lhs == rhs,
        FCmpOp::ONe => !lhs.is_nan() && !rhs.is_nan() && lhs != rhs,
        FCmpOp::OLt => lhs < rhs,
        FCmpOp::OLe => lhs <= rhs,
        FCmpOp::OGt => lhs > rhs,
        FCmpOp::OGe => lhs >= rhs,
        FCmpOp::UEq => lhs == rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::UNe => lhs != rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::ULt => lhs < rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::ULe => lhs <= rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::UGt => lhs > rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::UGe => lhs >= rhs || lhs.is_nan() || rhs.is_nan(),
    }
}

fn fcmp_op_from_u32(tag: u32) -> FCmpOp {
    match tag {
        0 => FCmpOp::OEq, 1 => FCmpOp::ONe, 2 => FCmpOp::OLt, 3 => FCmpOp::OLe,
        4 => FCmpOp::OGt, 5 => FCmpOp::OGe, 6 => FCmpOp::UEq, 7 => FCmpOp::UNe,
        8 => FCmpOp::ULt, 9 => FCmpOp::ULe, 10 => FCmpOp::UGt, _ => FCmpOp::UGe,
    }
}

#[no_mangle]
pub extern "C" fn eval_fcmp_root(tag: u32, lhs: f64, rhs: f64) -> u32 {
    eval_fcmp(fcmp_op_from_u32(tag), lhs, rhs) as u32
}
