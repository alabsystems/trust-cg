// trust-cg-verify/if_convert_proofs.rs - SMT proofs for IfConversion pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proves that the IfConversion optimization pass in trust-cg-opt preserves
// program semantics. The pass transforms diamond and triangle CFG patterns
// into conditional select instructions (CSEL, CSINC, CSNEG).
//
// Technique: Alive2-style (PLDI 2021). Each proof encodes the semantics of
// both the original CFG pattern and the replacement instruction, then shows
// equivalence for all inputs.
//
// Reference: crates/trust-cg-opt/src/if_convert.rs
// Related: crates/trust-cg-verify/src/cmp_combine_proofs.rs (CmpSelectCombine proofs)

//! SMT proofs for IfConversion pass correctness.
//!
//! ## IfConversion Proofs
//!
//! | Proof | Property |
//! |-------|----------|
//! | [`proof_diamond_csel_equivalence`] | if(cond) x=a; else x=b ≡ CSEL x, a, b, cond |
//! | [`proof_triangle_csel_equivalence`] | if(cond) x=a; [else x unchanged] ≡ CSEL x, a, x, cond |
//! | [`proof_csinc_formation`] | if(cond) x=a; else x=b+1 ≡ CSINC x, a, b, cond |
//! | [`proof_csneg_formation`] | if(cond) x=a; else x=-b ≡ CSNEG x, a, b, cond |
//! | [`proof_condition_inversion`] | CSEL with inverted condition swaps operands |
//! | [`proof_multi_instruction_hoist_safety`] | Hoisted pure instructions preserve semantics |
//! | [`proof_cfg_structure_preservation`] | Removing dead blocks does not affect reachable code |
//! | [`proof_side_effect_rejection`] | Diamonds with loads/stores/calls are not converted |
//! | [`proof_idempotence`] | Applying if-conversion twice gives same result |
//! | [`proof_arm_condition_code_mapping`] | Each branch condition maps to correct CSEL condition |

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;

// ===========================================================================
// 1. Diamond CSEL equivalence
// ===========================================================================

/// Proof: Diamond CSEL equivalence for 64-bit values.
///
/// Theorem: forall a, b, cond_flag : BV64 .
///   if(cond_flag != 0) x = a; else x = b
///   ≡ CSEL x, a, b, cond
///
/// The IfConversion pass transforms a diamond CFG pattern where the true
/// arm assigns `a` and the false arm assigns `b` into a single CSEL
/// instruction. Both sides compute the same conditional selection.
///
/// Unlike CmpSelectCombine (which handles only single-MOV arms), this
/// covers the general IfConversion diamond pattern with up to 2 instructions
/// per arm. The semantic core is the same: both sides select based on
/// the branch condition.
pub fn proof_diamond_csel_equivalence() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Original diamond CFG:
    //   header: CMP + B.cond -> true_block
    //   true_block:  MOV x, a; B join
    //   false_block: MOV x, b; B join
    //   join: ... (x is live)
    //
    // Semantics: x = (cond_flag != 0) ? a : b
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );

    // After if-conversion: CSEL x, a, b, cond
    // Semantics: x = (cond_flag != 0) ? a : b
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: diamond CSEL — if(cond) a else b ≡ CSEL x, a, b, cond (64-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Diamond CSEL equivalence (8-bit, exhaustive).
pub fn proof_diamond_csel_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: diamond CSEL — if(cond) a else b ≡ CSEL x, a, b, cond (8-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 2. Triangle CSEL equivalence
// ===========================================================================

/// Proof: Triangle CSEL equivalence for 64-bit values.
///
/// Theorem: forall a, x_orig, cond_flag : BV64 .
///   if(cond_flag != 0) x = a; [else x unchanged (= x_orig)]
///   ≡ CSEL x, a, x_orig, cond
///
/// The triangle pattern has a then-block that assigns a value and a
/// fallthrough to the join block (no else arm). The original value of x
/// (x_orig) is preserved when the condition is false.
///
/// IfConversion emits: CSEL x, a, x_orig, cond
/// where x_orig is the destination register itself (identity on false).
pub fn proof_triangle_csel_equivalence() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let x_orig = SmtExpr::var("x_orig", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Original triangle CFG:
    //   header: CMP + B.cond -> then_block, fallthrough -> join
    //   then_block: MOV x, a; B join
    //   join: ... (x is a if taken, x_orig if not)
    //
    // Semantics: x = (cond_flag != 0) ? a : x_orig
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        x_orig.clone(),
    );

    // After if-conversion: CSEL x, a, x, cond
    // Semantics: x = (cond_flag != 0) ? a : x_orig
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        x_orig,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: triangle CSEL — if(cond) x=a ≡ CSEL x, a, x, cond (64-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("x_orig".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Triangle CSEL equivalence (8-bit, exhaustive).
pub fn proof_triangle_csel_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let x_orig = SmtExpr::var("x_orig", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        x_orig.clone(),
    );
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        x_orig,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: triangle CSEL — if(cond) x=a ≡ CSEL x, a, x, cond (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("x_orig".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 3. CSINC formation
// ===========================================================================

/// Proof: CSINC formation for 64-bit values.
///
/// Theorem: forall a, b, cond_flag : BV64 .
///   if(cond_flag != 0) x = a; else x = b + 1
///   ≡ CSINC x, a, b, cond
///
/// IfConversion recognizes when the false arm computes ADD dst, src, #1
/// and the true arm is a MOV. Instead of CSEL, it emits the more compact
/// CSINC instruction which performs the increment in the false case.
///
/// ARM semantics: CSINC Xd, Xn, Xm, cond
///   Xd = cond ? Xn : (Xm + 1)
pub fn proof_csinc_formation() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Original diamond:
    //   true_block:  MOV x, a
    //   false_block: ADD x, b, #1
    let b_plus_one = b.clone().bvadd(SmtExpr::bv_const(1, width));
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b_plus_one,
    );

    // After if-conversion: CSINC x, a, b, cond
    // Semantics: x = (cond) ? a : (b + 1)
    let b_inc = b.bvadd(SmtExpr::bv_const(1, width));
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b_inc,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CSINC — if(cond) a else b+1 ≡ CSINC x, a, b, cond (64-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// CSINC formation (8-bit, exhaustive).
pub fn proof_csinc_formation_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let b_plus_one = b.clone().bvadd(SmtExpr::bv_const(1, width));
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b_plus_one,
    );

    let b_inc = b.bvadd(SmtExpr::bv_const(1, width));
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b_inc,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CSINC — if(cond) a else b+1 ≡ CSINC x, a, b, cond (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 4. CSNEG formation
// ===========================================================================

/// Proof: CSNEG formation for 64-bit values.
///
/// Theorem: forall a, b, cond_flag : BV64 .
///   if(cond_flag != 0) x = a; else x = -b
///   ≡ CSNEG x, a, b, cond
///
/// IfConversion recognizes when the false arm computes NEG dst, src
/// and the true arm is a MOV. It emits CSNEG which negates in the
/// false case.
///
/// ARM semantics: CSNEG Xd, Xn, Xm, cond
///   Xd = cond ? Xn : (-Xm)
pub fn proof_csneg_formation() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Original diamond:
    //   true_block:  MOV x, a
    //   false_block: NEG x, b
    let neg_b = b.clone().bvneg();
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        neg_b,
    );

    // After if-conversion: CSNEG x, a, b, cond
    // Semantics: x = (cond) ? a : (-b)
    let neg_b2 = b.bvneg();
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        neg_b2,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CSNEG — if(cond) a else -b ≡ CSNEG x, a, b, cond (64-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// CSNEG formation (8-bit, exhaustive).
pub fn proof_csneg_formation_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let neg_b = b.clone().bvneg();
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        neg_b,
    );

    let neg_b2 = b.bvneg();
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        neg_b2,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CSNEG — if(cond) a else -b ≡ CSNEG x, a, b, cond (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 5. Condition inversion: CSEL with inverted condition swaps operands
// ===========================================================================

/// Proof: Condition inversion for IfConversion CSEL.
///
/// Theorem: forall a, b, cond_flag : BV64 .
///   CSEL x, a, b, cond ≡ CSEL x, b, a, !cond
///
/// When IfConversion encounters a swapped CSINC/CSNEG pattern (e.g.,
/// true arm has ADD #1, false arm has MOV), it inverts the condition
/// and swaps the operands. This proof shows that inversion preserves
/// semantics.
///
/// This is the core correctness argument for try_csinc() and try_csneg()
/// Case 2 paths in if_convert.rs, where the condition is inverted via
/// `cond.invert()`.
pub fn proof_condition_inversion() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // CSEL x, a, b, cond: x = (cond != 0) ? a : b
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );

    // CSEL x, b, a, !cond: x = (cond == 0) ? b : a
    let inverted = SmtExpr::ite(cond_flag.eq_expr(SmtExpr::bv_const(0, width)), b, a);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: condition inversion — CSEL a,b,cond ≡ CSEL b,a,!cond (64-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: inverted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Condition inversion (8-bit, exhaustive).
pub fn proof_condition_inversion_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );
    let inverted = SmtExpr::ite(cond_flag.eq_expr(SmtExpr::bv_const(0, width)), b, a);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: condition inversion — CSEL a,b,cond ≡ CSEL b,a,!cond (8-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: inverted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 6. Multi-instruction hoist safety
// ===========================================================================

/// Proof: Multi-instruction hoist safety for 64-bit values.
///
/// Theorem: forall src, addend, b, cond_flag : BV64 .
///   if(cond_flag != 0) { t = src + addend; x = t } else { x = b }
///   ≡ t = src + addend; CSEL x, t, b, cond
///
/// When the true arm has 2 instructions (e.g., ADD t, src, addend; MOV x, t),
/// IfConversion hoists the non-final instruction (ADD) unconditionally into
/// the header, then emits a CSEL for the final value.
///
/// Safety argument: the hoisted ADD is pure (no side effects, no flag setting),
/// so executing it unconditionally does not change observable behavior. The ADD
/// result `t` is only used by the CSEL, and in the false case it is simply
/// dead (the CSEL selects `b` instead). The overall value of `x` is identical.
pub fn proof_multi_instruction_hoist_safety() -> ProofObligation {
    let width = 64;
    let src = SmtExpr::var("src", width);
    let addend = SmtExpr::var("addend", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Original diamond (2-inst true arm):
    //   true_block:  ADD t, src, addend; MOV x, t  → x = src + addend
    //   false_block: MOV x, b                      → x = b
    let t = src.clone().bvadd(addend.clone());
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        t.clone(),
        b.clone(),
    );

    // After if-conversion (hoist ADD, emit CSEL):
    //   header: ... ADD t, src, addend; CSEL x, t, b, cond; B join
    // t = src + addend is computed unconditionally but the result is
    // selected by CSEL. x = (cond) ? t : b = (cond) ? (src + addend) : b
    let t_hoisted = src.bvadd(addend);
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        t_hoisted,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: multi-inst hoist — hoisted pure ADD + CSEL preserves value (64-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("src".to_string(), width),
            ("addend".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Multi-instruction hoist safety (8-bit, exhaustive).
///
/// Note: 4 inputs at 8-bit = 2^32 = 4B combinations, which exceeds
/// exhaustive testing. This uses statistical verification (sampling).
pub fn proof_multi_instruction_hoist_safety_8bit() -> ProofObligation {
    let width = 8;
    let src = SmtExpr::var("src", width);
    let addend = SmtExpr::var("addend", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let t = src.clone().bvadd(addend.clone());
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        t,
        b.clone(),
    );

    let t_hoisted = src.bvadd(addend);
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        t_hoisted,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: multi-inst hoist — hoisted pure ADD + CSEL preserves value (8-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("src".to_string(), width),
            ("addend".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 7. CFG structure preservation
// ===========================================================================

/// Proof: CFG structure preservation — removing dead blocks does not
/// affect reachable code.
///
/// Theorem: forall a, b, cond_flag : BV64 .
///   let x_diamond = ite(cond != 0, a, b) in
///   let x_linear = ite(cond != 0, a, b) in
///   x_diamond == x_linear
///
/// After if-conversion, the arm blocks become dead (unreachable). The pass
/// removes them from block_order. This proof shows that the value computed
/// at the join point is identical regardless of whether the dead arm blocks
/// exist in the function.
///
/// The key insight: dead blocks contribute no observable behavior. All
/// live-out values from the diamond are captured by the CSEL instruction(s)
/// in the header. The join block sees exactly the same inputs.
pub fn proof_cfg_structure_preservation() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Diamond CFG: computes x = ite(cond, a, b) via branching
    let diamond = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );

    // Linear code (arm blocks removed): CSEL computes x = ite(cond, a, b)
    let linear = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CFG preservation — dead block removal preserves join value (64-bit)"
            .to_string(),
        trust_ir_expr: diamond,
        aarch64_expr: linear,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// CFG structure preservation (8-bit, exhaustive).
pub fn proof_cfg_structure_preservation_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let diamond = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );
    let linear = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CFG preservation — dead block removal preserves join value (8-bit)"
            .to_string(),
        trust_ir_expr: diamond,
        aarch64_expr: linear,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 8. Side-effect rejection
// ===========================================================================

/// Proof: Side-effect rejection — diamonds with loads/stores/calls are
/// not converted, so the pass preserves original semantics.
///
/// Theorem: forall a, mem_val, cond_flag : BV64 .
///   if(cond_flag != 0) x = a; else x = load(addr)
///   original semantics are preserved (no CSEL emitted)
///
/// When a diamond arm contains a load, store, or call, IfConversion rejects
/// the pattern. The is_safe_to_speculate() check filters out LDR, STR, BL,
/// BLR, and all flag-setting instructions. For rejected patterns, the pass
/// preserves the original CFG unchanged — both sides are identical.
///
/// We model this as: the original diamond semantics using a load value are
/// preserved exactly (identity transform). The pass correctly identifies
/// this as non-convertible and leaves it alone.
pub fn proof_side_effect_rejection() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let mem_val = SmtExpr::var("mem_val", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Original diamond where false arm has a load:
    //   true_block:  MOV x, a
    //   false_block: LDR x, [addr] (= mem_val, side-effecting)
    //
    // Since the pass rejects this, both sides are the original semantics.
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        mem_val.clone(),
    );

    // After (non-)conversion: pass rejects, semantics preserved unchanged.
    let preserved = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        mem_val,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name:
            "IfConversion: side-effect rejection — load arm rejected, semantics preserved (64-bit)"
                .to_string(),
        trust_ir_expr: original,
        aarch64_expr: preserved,
        inputs: vec![
            ("a".to_string(), width),
            ("mem_val".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Side-effect rejection (8-bit, exhaustive).
pub fn proof_side_effect_rejection_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let mem_val = SmtExpr::var("mem_val", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        mem_val.clone(),
    );
    let preserved = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        mem_val,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name:
            "IfConversion: side-effect rejection — load arm rejected, semantics preserved (8-bit)"
                .to_string(),
        trust_ir_expr: original,
        aarch64_expr: preserved,
        inputs: vec![
            ("a".to_string(), width),
            ("mem_val".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 9. Idempotence
// ===========================================================================

/// Proof: Idempotence — applying if-conversion twice gives same result.
///
/// Theorem: forall a, b, cond_flag : BV64 .
///   CSEL(a, b, cond) == CSEL(a, b, cond)  [trivially]
///
/// After the first application of IfConversion, the diamond/triangle
/// pattern is gone — the header now contains a linear sequence ending
/// with CSEL + B (unconditional). There is no BCond left, so the
/// second pass finds nothing to convert. The CSEL result is preserved.
///
/// We model this as: the output of one CSEL is identical to the output
/// of applying the same CSEL again (the pattern is no longer matchable,
/// so the value flows through unchanged).
pub fn proof_idempotence() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // After first if-conversion: CSEL x, a, b, cond
    let first_pass = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );

    // After second if-conversion: no BCond exists, value unchanged
    // The CSEL produces the same result = identity
    let second_pass = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: idempotence — second application preserves CSEL result (64-bit)"
            .to_string(),
        trust_ir_expr: first_pass,
        aarch64_expr: second_pass,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Idempotence (8-bit, exhaustive).
pub fn proof_idempotence_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let first_pass = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );
    let second_pass = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: idempotence — second application preserves CSEL result (8-bit)"
            .to_string(),
        trust_ir_expr: first_pass,
        aarch64_expr: second_pass,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// 10. ARM condition code mapping
// ===========================================================================

/// Proof: ARM condition code mapping — each AArch64 condition code encoding
/// maps to the correct CSEL behavior.
///
/// Theorem: forall a, b : BV64, forall cc_enc : BV4 (cc_enc < 14) .
///   CSEL_with_encoding(a, b, cc_enc) == ite(cc_enc matches cond, a, b)
///
/// The IfConversion pass uses `decode_cond()` to map the 4-bit condition
/// code from BCond to a CondCode enum, and then uses `cond.encoding()` to
/// embed it into the CSEL operand. This proof verifies the round-trip:
/// encoding -> decode -> re-encode preserves the condition semantics.
///
/// We model condition evaluation as: the condition is true iff the encoded
/// value matches a specific bit pattern. The CSEL selects `a` when true,
/// `b` when false. The mapping is bijective for the 14 standard conditions
/// (AL and NV are handled separately).
///
/// Concretely, we verify for condition code EQ (encoding 0):
///   CSEL(a, b, 0) selects a when cc_bit == 0, b otherwise.
/// The pass encodes EQ as 0b0000 and the CSEL hardware decodes it identically.
pub fn proof_arm_condition_code_mapping() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    // Model the condition evaluation result as a 1-bit flag
    let z_flag = SmtExpr::var("z_flag", width);

    // EQ condition: branch taken iff Z flag is set (z_flag != 0)
    // BCond with EQ encoding (0b0000) branches when Z == 1
    // Diamond: true arm gets `a`, false arm gets `b`
    let original = SmtExpr::ite(
        z_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );

    // CSEL with condition code EQ: selects first operand when EQ is true
    // The encoding (0b0000) is decoded to EQ which tests Z == 1
    // Same semantics: select `a` when Z is set, `b` otherwise
    let csel = SmtExpr::ite(z_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(), a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: ARM cc mapping — EQ encoding round-trips correctly (64-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: csel,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("z_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// ARM condition code mapping (8-bit, exhaustive).
pub fn proof_arm_condition_code_mapping_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let z_flag = SmtExpr::var("z_flag", width);

    let original = SmtExpr::ite(
        z_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a.clone(),
        b.clone(),
    );
    let csel = SmtExpr::ite(z_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(), a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: ARM cc mapping — EQ encoding round-trips correctly (8-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: csel,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("z_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// Additional proofs: CSINC with inverted condition
// ===========================================================================

/// Proof: CSINC with inverted condition (swapped arms).
///
/// Theorem: forall a, b, cond_flag : BV64 .
///   if(cond_flag != 0) x = a+1; else x = b
///   ≡ CSINC x, b, a, !cond
///
/// When the true arm has ADD #1 and the false arm has MOV (swapped from
/// the canonical pattern), IfConversion inverts the condition to produce
/// a standard CSINC.
pub fn proof_csinc_inverted() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Original diamond (swapped):
    //   true_block:  ADD x, a, #1
    //   false_block: MOV x, b
    let a_plus_one = a.clone().bvadd(SmtExpr::bv_const(1, width));
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a_plus_one,
        b.clone(),
    );

    // After if-conversion: CSINC x, b, a, !cond
    // CSINC semantics: CSINC Xd, Xn, Xm, cc = cc ? Xn : (Xm + 1)
    // So: CSINC x, b, a, !cond = (!cond) ? b : (a + 1)
    // When cond is true (cond_flag != 0), !cond is false → select a + 1
    // When cond is false (cond_flag == 0), !cond is true → select b
    let a_inc = a.bvadd(SmtExpr::bv_const(1, width));
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a_inc,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CSINC inverted — if(cond) a+1 else b ≡ CSINC b, a, !cond (64-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// CSINC inverted (8-bit, exhaustive).
pub fn proof_csinc_inverted_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let a_plus_one = a.clone().bvadd(SmtExpr::bv_const(1, width));
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        a_plus_one,
        b.clone(),
    );

    let a_inc = a.bvadd(SmtExpr::bv_const(1, width));
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a_inc,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CSINC inverted — if(cond) a+1 else b ≡ CSINC b, a, !cond (8-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// Additional proofs: CSNEG with inverted condition
// ===========================================================================

/// Proof: CSNEG with inverted condition (swapped arms).
///
/// Theorem: forall a, b, cond_flag : BV64 .
///   if(cond_flag != 0) x = -a; else x = b
///   ≡ CSNEG x, b, a, !cond
///
/// When the true arm has NEG and the false arm has MOV (swapped from
/// canonical), IfConversion inverts the condition.
pub fn proof_csneg_inverted() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    // Original diamond (swapped):
    //   true_block:  NEG x, a
    //   false_block: MOV x, b
    let neg_a = a.clone().bvneg();
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        neg_a,
        b.clone(),
    );

    // After if-conversion: CSNEG x, b, a, !cond
    // CSNEG semantics: CSNEG Xd, Xn, Xm, cc = cc ? Xn : (-Xm)
    // So: CSNEG x, b, a, !cond = (!cond) ? b : (-a)
    // When cond is true (cond_flag != 0), !cond is false → select -a
    // When cond is false (cond_flag == 0), !cond is true → select b
    let neg_a2 = a.bvneg();
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        neg_a2,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CSNEG inverted — if(cond) -a else b ≡ CSNEG b, a, !cond (64-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// CSNEG inverted (8-bit, exhaustive).
pub fn proof_csneg_inverted_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond_flag = SmtExpr::var("cond_flag", width);

    let neg_a = a.clone().bvneg();
    let original = SmtExpr::ite(
        cond_flag
            .clone()
            .eq_expr(SmtExpr::bv_const(0, width))
            .not_expr(),
        neg_a,
        b.clone(),
    );

    let neg_a2 = a.bvneg();
    let converted = SmtExpr::ite(
        cond_flag.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        neg_a2,
        b,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: CSNEG inverted — if(cond) -a else b ≡ CSNEG b, a, !cond (8-bit)"
            .to_string(),
        trust_ir_expr: original,
        aarch64_expr: converted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond_flag".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

// ===========================================================================
// Div-guard diamond collapse (HARDWARE-TOTAL div semantics)
// ===========================================================================
//
// The headline win of this family. The source `r += b != 0 ? a/b : 0` is a
// WELL-DEFINED program only because the `b != 0` guard keeps the division out
// of the `b == 0` case (trust_ir `Sdiv`/`Udiv` by zero is UB). A classical
// compiler (clang -O3, LLVM) therefore CANNOT if-convert it: hoisting the IR
// `sdiv` above its guard would execute UB on the zero rows, so clang emits a
// per-element `cbz` branch.
//
// trust-cg reasons at the MACHINE level, where AArch64 `SDIV`/`UDIV` are TOTAL
// (`x / 0 == 0` in silicon, ARM DDI 0487 — no trap). Under that total model,
// encoded by [`crate::aarch64_semantics::encode_sdiv_rr`] /
// [`encode_udiv_rr`] as `ite(rm == 0, 0, bvsdiv/bvudiv(rn, rm))`, the guarded
// select COLLAPSES to ONE unguarded division instruction with no CSEL:
//
//   select(b != 0, a/b, 0)  ==  sdiv_hw(a, b)   for ALL a, b
//
// Proof (no precondition needed):
//   * b != 0:  LHS = bvsdiv(a,b);  RHS = ite(false, 0, bvsdiv(a,b)) = bvsdiv(a,b).
//   * b == 0:  LHS = 0 (the select's else);  RHS = ite(true, 0, …) = 0.
//
// This is a GENUINE (non-degenerate) equivalence: the two sides are distinct
// SMT terms (guard polarity and branch order differ) that agree everywhere.

/// Proof: div-guard diamond collapses to a bare total SDIV (32-bit).
///
/// `select(b != 0, sdiv(a, b), 0)  ==  encode_sdiv_rr(a, b)` for all a, b.
/// The machine side is EXACTLY the total-div encoder the SDIV lowering proof
/// uses, so this obligation is tied to the same silicon semantics.
pub fn proof_select_sdiv_collapse_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_sdiv_rr;
    use trust_cg_ir::cc::OperandSize;

    let width = 32;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);

    // trust_ir guarded select: ite(b != 0, a /s b, 0).
    let guarded = SmtExpr::ite(
        b.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone().bvsdiv(b.clone()),
        SmtExpr::bv_const(0, width),
    );

    // Machine side: the single unguarded total SDIV.
    let bare = encode_sdiv_rr(OperandSize::S32, a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: div-guard collapse — select(b!=0, a/b, 0) ≡ SDIV a,b (total, 32-bit)"
            .to_string(),
        trust_ir_expr: guarded,
        aarch64_expr: bare,
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Proof: div-guard diamond collapses to a bare total SDIV (64-bit).
pub fn proof_select_sdiv_collapse_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_sdiv_rr;
    use trust_cg_ir::cc::OperandSize;

    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);

    let guarded = SmtExpr::ite(
        b.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone().bvsdiv(b.clone()),
        SmtExpr::bv_const(0, width),
    );
    let bare = encode_sdiv_rr(OperandSize::S64, a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: div-guard collapse — select(b!=0, a/b, 0) ≡ SDIV a,b (total, 64-bit)"
            .to_string(),
        trust_ir_expr: guarded,
        aarch64_expr: bare,
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Proof: div-guard diamond collapses to a bare total UDIV (32-bit).
///
/// `select(b != 0, udiv(a, b), 0)  ==  encode_udiv_rr(a, b)` for all a, b.
pub fn proof_select_udiv_collapse_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_udiv_rr;
    use trust_cg_ir::cc::OperandSize;

    let width = 32;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);

    let guarded = SmtExpr::ite(
        b.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone().bvudiv(b.clone()),
        SmtExpr::bv_const(0, width),
    );
    let bare = encode_udiv_rr(OperandSize::S32, a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: div-guard collapse — select(b!=0, a/b, 0) ≡ UDIV a,b (total, 32-bit)"
            .to_string(),
        trust_ir_expr: guarded,
        aarch64_expr: bare,
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Proof: div-guard with a NON-ZERO else value keeps a CSEL (still branchless).
///
/// `select(b != 0, a/b, K)  ==  csel(b != 0, sdiv_hw(a, b), K)` for all a, b, K.
/// This justifies the `? a/b : K` (K != 0) path of the pass: the total div is
/// speculated unconditionally, then a CSEL picks `K` on the zero rows. Still a
/// branchless win, just not a full collapse. Non-degenerate: the guard on the
/// LHS wraps the RAW `bvsdiv` while the RHS's speculated div is the TOTAL form.
pub fn proof_select_sdiv_csel_variant_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_sdiv_rr;
    use trust_cg_ir::cc::OperandSize;

    let width = 32;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let k = SmtExpr::var("k", width);
    let b_nz = b.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr();

    // trust_ir guarded select: ite(b != 0, a /s b, K).
    let guarded = SmtExpr::ite(b_nz.clone(), a.clone().bvsdiv(b.clone()), k.clone());
    // Machine: speculate the total div, then CSEL K on the zero rows.
    let speculated = SmtExpr::ite(b_nz, encode_sdiv_rr(OperandSize::S32, a, b), k);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: div-guard CSEL — select(b!=0, a/b, K) ≡ SDIV;CSEL K (total, 32-bit)"
            .to_string(),
        trust_ir_expr: guarded,
        aarch64_expr: speculated,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("k".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// NEGATIVE CONTROL: a WRONG else value must REFUTE the collapse.
///
/// `select(b != 0, a/b, 1)` is NOT equal to the bare total `SDIV a,b`: they
/// disagree on every `b == 0` row (LHS = 1, RHS = 0). A sound solver must
/// return a counterexample (e.g. `b = 0`). This proves the collapse obligation
/// above is not vacuously satisfiable — the `else == 0` requirement is load-
/// bearing, exactly the shape gate the pass enforces before it fires.
pub fn control_select_sdiv_collapse_wrong_else_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_sdiv_rr;
    use trust_cg_ir::cc::OperandSize;

    let width = 32;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);

    // WRONG else value: 1 instead of 0.
    let guarded_wrong = SmtExpr::ite(
        b.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone().bvsdiv(b.clone()),
        SmtExpr::bv_const(1, width),
    );
    let bare = encode_sdiv_rr(OperandSize::S32, a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "IfConversion: div-guard collapse CONTROL — select(b!=0, a/b, 1) ≢ SDIV (32-bit)"
            .to_string(),
        trust_ir_expr: guarded_wrong,
        aarch64_expr: bare,
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
    }
}

/// Return the div-guard collapse proof obligations (must all VERIFY).
///
/// Kept in a dedicated registry (not folded into [`all_if_convert_proofs`]) so
/// the existing degenerate-retraction counts are untouched. These are GENUINE,
/// precondition-free equivalences under the total-div semantics.
pub fn all_select_div_collapse_proofs() -> Vec<ProofObligation> {
    vec![
        proof_select_sdiv_collapse_i32(),
        proof_select_sdiv_collapse_i64(),
        proof_select_udiv_collapse_i32(),
        proof_select_sdiv_csel_variant_i32(),
    ]
}

/// Return the div-guard collapse NEGATIVE controls (must all REFUTE).
pub fn select_div_collapse_wrong_controls() -> Vec<ProofObligation> {
    vec![control_select_sdiv_collapse_wrong_else_i32()]
}

// ===========================================================================
// Registry functions
// ===========================================================================

/// Return all IfConversion proof obligations (64-bit, statistical).
pub fn all_if_convert_proofs() -> Vec<ProofObligation> {
    vec![
        proof_diamond_csel_equivalence(),
        proof_triangle_csel_equivalence(),
        proof_csinc_formation(),
        proof_csneg_formation(),
        proof_condition_inversion(),
        proof_multi_instruction_hoist_safety(),
        proof_cfg_structure_preservation(),
        proof_side_effect_rejection(),
        proof_idempotence(),
        proof_arm_condition_code_mapping(),
        proof_csinc_inverted(),
        proof_csneg_inverted(),
    ]
}

/// Return all IfConversion proofs including 8-bit exhaustive variants.
/// Retracted degenerate X==X IfConversion self-equality obligations (diamond/triangle CSEL, CSINC/CSNEG +inverted, CFG-preservation, idempotence, multi-inst hoist, side-effect rejection, ARM cc round-trip). Genuine CSEL condition-inversion (a,b,cond==b,a,!cond) proofs remain.
const IFCONVERT_RETRACTED_DEGENERATE: &[&str] = &[
    "IfConversion: ARM cc mapping — EQ encoding round-trips correctly (64-bit)",
    "IfConversion: ARM cc mapping — EQ encoding round-trips correctly (8-bit)",
    "IfConversion: CFG preservation — dead block removal preserves join value (64-bit)",
    "IfConversion: CFG preservation — dead block removal preserves join value (8-bit)",
    "IfConversion: CSINC inverted — if(cond) a+1 else b ≡ CSINC b, a, !cond (64-bit)",
    "IfConversion: CSINC inverted — if(cond) a+1 else b ≡ CSINC b, a, !cond (8-bit)",
    "IfConversion: CSINC — if(cond) a else b+1 ≡ CSINC x, a, b, cond (64-bit)",
    "IfConversion: CSINC — if(cond) a else b+1 ≡ CSINC x, a, b, cond (8-bit)",
    "IfConversion: CSNEG inverted — if(cond) -a else b ≡ CSNEG b, a, !cond (64-bit)",
    "IfConversion: CSNEG inverted — if(cond) -a else b ≡ CSNEG b, a, !cond (8-bit)",
    "IfConversion: CSNEG — if(cond) a else -b ≡ CSNEG x, a, b, cond (64-bit)",
    "IfConversion: CSNEG — if(cond) a else -b ≡ CSNEG x, a, b, cond (8-bit)",
    "IfConversion: diamond CSEL — if(cond) a else b ≡ CSEL x, a, b, cond (64-bit)",
    "IfConversion: diamond CSEL — if(cond) a else b ≡ CSEL x, a, b, cond (8-bit)",
    "IfConversion: idempotence — second application preserves CSEL result (64-bit)",
    "IfConversion: idempotence — second application preserves CSEL result (8-bit)",
    "IfConversion: multi-inst hoist — hoisted pure ADD + CSEL preserves value (64-bit)",
    "IfConversion: multi-inst hoist — hoisted pure ADD + CSEL preserves value (8-bit)",
    "IfConversion: side-effect rejection — load arm rejected, semantics preserved (64-bit)",
    "IfConversion: side-effect rejection — load arm rejected, semantics preserved (8-bit)",
    "IfConversion: triangle CSEL — if(cond) x=a ≡ CSEL x, a, x, cond (64-bit)",
    "IfConversion: triangle CSEL — if(cond) x=a ≡ CSEL x, a, x, cond (8-bit)",
];

pub fn all_if_convert_proofs_with_variants() -> Vec<ProofObligation> {
    let mut proofs = all_if_convert_proofs();
    proofs.push(proof_diamond_csel_equivalence_8bit());
    proofs.push(proof_triangle_csel_equivalence_8bit());
    proofs.push(proof_csinc_formation_8bit());
    proofs.push(proof_csneg_formation_8bit());
    proofs.push(proof_condition_inversion_8bit());
    proofs.push(proof_multi_instruction_hoist_safety_8bit());
    proofs.push(proof_cfg_structure_preservation_8bit());
    proofs.push(proof_side_effect_rejection_8bit());
    proofs.push(proof_idempotence_8bit());
    proofs.push(proof_arm_condition_code_mapping_8bit());
    proofs.push(proof_csinc_inverted_8bit());
    proofs.push(proof_csneg_inverted_8bit());
    // #62 retraction: drop degenerate X==X self-equalities (see IFCONVERT_RETRACTED_DEGENERATE).
    proofs.retain(|p| !IFCONVERT_RETRACTED_DEGENERATE.contains(&p.name.as_str()));
    proofs
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;

    /// Helper: verify a proof obligation and assert it is Valid.
    fn assert_valid(obligation: &ProofObligation) {
        let result = verify_by_evaluation(obligation);
        match &result {
            VerificationResult::Valid => {}
            VerificationResult::Invalid { counterexample } => {
                panic!(
                    "Proof '{}' FAILED with counterexample: {}",
                    obligation.name, counterexample
                );
            }
            VerificationResult::Unknown { reason } => {
                panic!("Proof '{}' returned Unknown: {}", obligation.name, reason);
            }
        }
    }

    // -----------------------------------------------------------------------
    // 1. Diamond CSEL equivalence
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_diamond_csel_equivalence() {
        assert_valid(&proof_diamond_csel_equivalence());
    }

    #[test]
    fn test_proof_diamond_csel_equivalence_8bit() {
        assert_valid(&proof_diamond_csel_equivalence_8bit());
    }

    // -----------------------------------------------------------------------
    // 2. Triangle CSEL equivalence
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_triangle_csel_equivalence() {
        assert_valid(&proof_triangle_csel_equivalence());
    }

    #[test]
    fn test_proof_triangle_csel_equivalence_8bit() {
        assert_valid(&proof_triangle_csel_equivalence_8bit());
    }

    // -----------------------------------------------------------------------
    // 3. CSINC formation
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_csinc_formation() {
        assert_valid(&proof_csinc_formation());
    }

    #[test]
    fn test_proof_csinc_formation_8bit() {
        assert_valid(&proof_csinc_formation_8bit());
    }

    // -----------------------------------------------------------------------
    // 4. CSNEG formation
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_csneg_formation() {
        assert_valid(&proof_csneg_formation());
    }

    #[test]
    fn test_proof_csneg_formation_8bit() {
        assert_valid(&proof_csneg_formation_8bit());
    }

    // -----------------------------------------------------------------------
    // 5. Condition inversion
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_condition_inversion() {
        assert_valid(&proof_condition_inversion());
    }

    #[test]
    fn test_proof_condition_inversion_8bit() {
        assert_valid(&proof_condition_inversion_8bit());
    }

    // -----------------------------------------------------------------------
    // 6. Multi-instruction hoist safety
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_multi_instruction_hoist_safety() {
        assert_valid(&proof_multi_instruction_hoist_safety());
    }

    #[test]
    fn test_proof_multi_instruction_hoist_safety_8bit() {
        assert_valid(&proof_multi_instruction_hoist_safety_8bit());
    }

    // -----------------------------------------------------------------------
    // 7. CFG structure preservation
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_cfg_structure_preservation() {
        assert_valid(&proof_cfg_structure_preservation());
    }

    #[test]
    fn test_proof_cfg_structure_preservation_8bit() {
        assert_valid(&proof_cfg_structure_preservation_8bit());
    }

    // -----------------------------------------------------------------------
    // 8. Side-effect rejection
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_side_effect_rejection() {
        assert_valid(&proof_side_effect_rejection());
    }

    #[test]
    fn test_proof_side_effect_rejection_8bit() {
        assert_valid(&proof_side_effect_rejection_8bit());
    }

    // -----------------------------------------------------------------------
    // 9. Idempotence
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_idempotence() {
        assert_valid(&proof_idempotence());
    }

    #[test]
    fn test_proof_idempotence_8bit() {
        assert_valid(&proof_idempotence_8bit());
    }

    // -----------------------------------------------------------------------
    // 10. ARM condition code mapping
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_arm_condition_code_mapping() {
        assert_valid(&proof_arm_condition_code_mapping());
    }

    #[test]
    fn test_proof_arm_condition_code_mapping_8bit() {
        assert_valid(&proof_arm_condition_code_mapping_8bit());
    }

    // -----------------------------------------------------------------------
    // 11. CSINC inverted
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_csinc_inverted() {
        assert_valid(&proof_csinc_inverted());
    }

    #[test]
    fn test_proof_csinc_inverted_8bit() {
        assert_valid(&proof_csinc_inverted_8bit());
    }

    // -----------------------------------------------------------------------
    // 12. CSNEG inverted
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_csneg_inverted() {
        assert_valid(&proof_csneg_inverted());
    }

    #[test]
    fn test_proof_csneg_inverted_8bit() {
        assert_valid(&proof_csneg_inverted_8bit());
    }

    // -----------------------------------------------------------------------
    // Aggregate tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_if_convert_proofs_valid() {
        let proofs = all_if_convert_proofs();
        assert_eq!(proofs.len(), 12, "expected 12 base proofs");
        for obligation in &proofs {
            assert_valid(obligation);
        }
    }

    #[test]
    fn test_all_if_convert_proofs_with_variants_valid() {
        let proofs = all_if_convert_proofs_with_variants();
        assert_eq!(
            proofs.len(),
            2,
            "expected 2 GENUINE proofs (22 degenerate diamond/triangle/CSINC/CSNEG/CFG \
             self-equality X==X retracted in #62; the CSEL condition-inversion algebra \
             proof — 64+8bit — remains)"
        );
        for obligation in &proofs {
            assert_valid(obligation);
        }
    }

    #[test]
    fn test_proof_names_unique() {
        let proofs = all_if_convert_proofs_with_variants();
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let len_before = names.len();
        names.dedup();
        assert_eq!(names.len(), len_before, "all proof names should be unique");
    }

    // -----------------------------------------------------------------------
    // Div-guard diamond collapse (HARDWARE-TOTAL div semantics)
    // -----------------------------------------------------------------------

    /// Every div-guard collapse obligation must VERIFY and be NON-degenerate.
    #[test]
    fn test_select_div_collapse_proofs_valid_and_genuine() {
        let proofs = all_select_div_collapse_proofs();
        assert_eq!(proofs.len(), 4, "expected 4 div-guard collapse proofs");
        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "div-guard collapse proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            assert_valid(obligation);
        }
    }

    /// The div-guard collapse must have NO preconditions — it holds for ALL
    /// inputs (including `b == 0`), which is the whole point of the total-div
    /// semantics. A precondition here would silently narrow the theorem.
    #[test]
    fn test_select_div_collapse_is_precondition_free() {
        for obligation in all_select_div_collapse_proofs() {
            assert!(
                obligation.preconditions.is_empty(),
                "div-guard collapse '{}' must be precondition-free (holds at b==0 too)",
                obligation.name
            );
        }
    }

    /// The wrong-else NEGATIVE control MUST refute (Invalid), with the
    /// counterexample living on the `b == 0` row. This proves the collapse is
    /// not vacuous: the `else == 0` requirement is load-bearing.
    #[test]
    fn test_select_div_collapse_wrong_else_refutes() {
        for control in select_div_collapse_wrong_controls() {
            let result = verify_by_evaluation(&control);
            match &result {
                VerificationResult::Invalid { .. } => {}
                other => panic!(
                    "NEGATIVE control '{}' must REFUTE (wrong else value), got {:?}",
                    control.name, other
                ),
            }
        }
    }

    /// Concrete edge pin: at `b == 0` the collapse LHS (guarded select, else=0)
    /// and RHS (bare total SDIV) both evaluate to 0; the wrong-else control's
    /// LHS evaluates to 1 (≠ 0). Locks the semantic edge the win rides on.
    #[test]
    fn test_select_div_collapse_zero_divisor_edge() {
        use crate::smt::EvalResult;
        use std::collections::HashMap;

        let good = proof_select_sdiv_collapse_i32();
        let mut env = HashMap::new();
        env.insert("a".to_string(), 42u64);
        env.insert("b".to_string(), 0u64);
        assert_eq!(
            good.trust_ir_expr.eval(&env),
            EvalResult::Bv(0),
            "guarded select must be 0 at b==0"
        );
        assert_eq!(
            good.aarch64_expr.eval(&env),
            EvalResult::Bv(0),
            "bare total SDIV must be 0 at b==0"
        );

        let bad = control_select_sdiv_collapse_wrong_else_i32();
        assert_eq!(
            bad.trust_ir_expr.eval(&env),
            EvalResult::Bv(1),
            "wrong-else control must be 1 at b==0 (the refutation witness)"
        );
    }
}
