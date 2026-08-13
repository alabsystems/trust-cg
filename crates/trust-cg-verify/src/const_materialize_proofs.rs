// trust-cg-verify/const_materialize_proofs.rs - SMT proofs for constant materialization
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proves that AArch64 constant materialization strategies in
// trust-cg-opt/const_materialize.rs produce the correct register values.
// Each strategy (MOVZ, MOVZ+MOVK, ORR logical immediate, MOVN) is modeled
// as SMT bitvector operations and verified against the expected constant.
//
// Technique: Alive2-style (PLDI 2021). For each strategy, encode the
// instruction sequence semantics as SMT bitvector expressions and the
// desired constant value as the target. Check `NOT(strategy == target)`
// for UNSAT. If UNSAT, the materialization is proven correct.
//
// Reference: crates/trust-cg-opt/src/const_materialize.rs
// Reference: ARM Architecture Reference Manual (DDI 0487), C6.2

//! SMT proofs for AArch64 constant materialization strategies.
//!
//! Retained aggregate proofs correspond to strategies in
//! `trust_cg_opt::const_materialize::materialize_constant`. Historical
//! retracted diagnostic constructors are labeled explicitly and never returned
//! by either public aggregate:
//!
//! ## MOVZ (move wide with zero)
//!
//! | Rule | Semantics | Proof |
//! |------|-----------|-------|
//! | MOVZ hw=0 | `Xd = zext(imm16)` | [`proof_movz_hw0`] |
//!
//! The shifted single-MOVZ diagnostic obligations remain available as
//! individual historical constructors, but are degenerate X==X identities and
//! are excluded from every public aggregate used for release proof coverage.
//!
//! ## MOVZ + MOVK (32-bit assembly)
//!
//! | Rule | Semantics | Proof |
//! |------|-----------|-------|
//! | MOVZ+MOVK 32 | `(hi16 << 16) \| lo16` | [`proof_movz_movk_32bit`] |
//!
//! ## MOVZ + 3xMOVK (64-bit assembly)
//!
//! | Rule | Semantics | Proof |
//! |------|-----------|-------|
//! | MOVZ+3xMOVK 64 | `(hw3<<48)\|(hw2<<32)\|(hw1<<16)\|hw0` | [`proof_movz_movk_64bit`] |
//!
//! ## ORR logical immediate
//!
//! | Rule | Semantics | Proof |
//! |------|-----------|-------|
//! | ORR XZR, #imm | `XZR \| bitmask = bitmask` | [`proof_orr_logical_imm`] |
//!
//! ## MOVN (move wide with NOT)
//!
//! | Rule | Semantics | Proof |
//! |------|-----------|-------|
//! | MOVN X hw=0 | `~(zext64(imm16))` | [`proof_movn_hw0`] |
//! | MOVN per form (X) | `~(zext64(imm16) << hw)`, hw ∈ {0,16,32,48} | [`proof_movn_halfword`] |
//! | MOVN per form (W) | `zext32to64(~32(zext32(imm16) << hw))`, hw ∈ {0,16} | [`proof_movn_halfword`] |
//!
//! Shifted MOVN diagnostics are likewise excluded from release aggregates.
//! The retained hw0 proof models only the 64-bit X form. Per-(width, shift)
//! coverage — including the W-form width semantics (32-bit complement followed
//! by zero-extension, upper 32 bits zero) previously named as the known gap —
//! is provided by the [`MOVN_FORMS`] family, whose reference side is an
//! independent concat/XOR inverted-field algebra (see
//! [`movn_inverted_field_spec`]).
//!
//! ## Strategy equivalence
//!
//! | Rule | Semantics | Proof |
//! |------|-----------|-------|
//! | ORR == MOVZ overlap | For single-chunk values | [`proof_orr_movz_equivalence`] |

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;

// ---------------------------------------------------------------------------
// Semantic encoding helpers
// ---------------------------------------------------------------------------

/// Encode MOVZ semantics: `Xd = zero_extend(imm16) << (hw * 16)`.
///
/// MOVZ zeros the entire register, then inserts the 16-bit immediate at
/// the specified halfword position. The result is `imm16 << shift`.
///
/// ARM ARM: "MOVZ moves a 16-bit immediate value to a register, shifting
/// it left by 0, 16, 32 or 48 bits, and clearing the remaining bits."
fn encode_movz(imm16: SmtExpr, hw_shift: u32, width: u32) -> SmtExpr {
    let imm_width = imm16.bv_width();
    let extended = imm16.zero_ext(width - imm_width);
    let shift_amount = SmtExpr::bv_const(hw_shift as u64, width);
    extended.bvshl(shift_amount)
}

/// Encode MOVK semantics: insert 16-bit immediate into existing register value.
///
/// MOVK keeps all other bits of the destination register, and replaces
/// exactly 16 bits at the halfword position `hw_shift`.
///
/// Semantics: `Xd = (Xd & ~(0xFFFF << hw_shift)) | (zext(imm16) << hw_shift)`
///
/// ARM ARM: "MOVK moves a 16-bit immediate value to the specified halfword
/// position of the register, keeping all other bits unchanged."
fn encode_movk(prev: SmtExpr, imm16: SmtExpr, hw_shift: u32, width: u32) -> SmtExpr {
    let imm_width = imm16.bv_width();
    let extended = imm16.zero_ext(width - imm_width);
    let shift_amount = SmtExpr::bv_const(hw_shift as u64, width);
    let shifted = extended.bvshl(shift_amount);

    // Build the mask: ~(0xFFFF << hw_shift)
    let mask_16 = SmtExpr::bv_const(0xFFFF, width);
    let shifted_mask = mask_16.bvshl(SmtExpr::bv_const(hw_shift as u64, width));
    let all_ones = if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let inverted_mask = shifted_mask.bvxor(SmtExpr::bv_const(all_ones, width));

    // Clear the halfword, then insert the new value
    prev.bvand(inverted_mask).bvor(shifted)
}

/// Encode ORR with XZR semantics: `Xd = XZR | bitmask = bitmask`.
///
/// ORR with XZR as the first operand simply loads the logical immediate
/// into the register. This is used for bitmask patterns that are encodable
/// as ARM logical immediates.
fn encode_orr_xzr(bitmask: SmtExpr, width: u32) -> SmtExpr {
    let zero = SmtExpr::bv_const(0, width);
    zero.bvor(bitmask)
}

/// Encode MOVN semantics: `Xd = ~(zero_extend(imm16) << (hw * 16))`.
///
/// MOVN inserts a 16-bit immediate at the specified halfword position,
/// zeros other bits, then inverts the entire result.
///
/// ARM ARM: "MOVN moves the bitwise inverse of a 16-bit immediate value
/// (optionally shifted) to a register."
fn encode_movn(imm16: SmtExpr, hw_shift: u32, width: u32) -> SmtExpr {
    let movz_result = encode_movz(imm16, hw_shift, width);
    let all_ones = if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    movz_result.bvxor(SmtExpr::bv_const(all_ones, width))
}

// ---------------------------------------------------------------------------
// MOVZ proofs: single instruction, each halfword position
// ---------------------------------------------------------------------------

/// Proof: MOVZ #imm16, LSL #0 produces `zext(imm16)`.
///
/// Theorem: forall imm16 : BV16 . zext64(imm16) << 0 == zext64(imm16)
///
/// The simplest materialization: a 16-bit immediate placed in bits [15:0]
/// with bits [63:16] zeroed. Used for constants 0..65535.
pub fn proof_movz_hw0() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);
    let target = imm16.clone().zero_ext(48); // desired value
    let strategy = encode_movz(imm16, 0, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ #imm16, LSL #0 == zext(imm16)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical diagnostic identity for MOVZ LSL #16.
///
/// Retracted from public aggregates under #62: both sides restate the same
/// shifted expression, so this cannot validate lowering or immediate encoding.
pub fn proof_movz_hw1() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);
    let target = imm16
        .clone()
        .zero_ext(48)
        .bvshl(SmtExpr::bv_const(16, width));
    let strategy = encode_movz(imm16, 16, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ #imm16, LSL #16 == zext(imm16) << 16".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical diagnostic identity for MOVZ LSL #32, retracted under #62.
pub fn proof_movz_hw2() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);
    let target = imm16
        .clone()
        .zero_ext(48)
        .bvshl(SmtExpr::bv_const(32, width));
    let strategy = encode_movz(imm16, 32, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ #imm16, LSL #32 == zext(imm16) << 32".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical diagnostic identity for MOVZ LSL #48, retracted under #62.
pub fn proof_movz_hw3() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);
    let target = imm16
        .clone()
        .zero_ext(48)
        .bvshl(SmtExpr::bv_const(48, width));
    let strategy = encode_movz(imm16, 48, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ #imm16, LSL #48 == zext(imm16) << 48".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: MOVZ 32-bit width at hw=0 (8-bit exhaustive variant for imm16).
pub fn proof_movz_hw0_8bit() -> ProofObligation {
    let width = 16; // Use 16-bit total for exhaustive 8-bit imm
    let imm = SmtExpr::var("imm", 8);
    let target = imm.clone().zero_ext(8);
    let extended = imm.zero_ext(8);
    let strategy = extended.bvshl(SmtExpr::bv_const(0, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ #imm8, LSL #0 == zext(imm8) (8-bit)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical exhaustive MOVZ-shift identity, retracted under #62.
pub fn proof_movz_hw1_8bit() -> ProofObligation {
    let width = 16;
    let imm = SmtExpr::var("imm", 8);
    let target = imm.clone().zero_ext(8).bvshl(SmtExpr::bv_const(8, width));
    let strategy = imm.zero_ext(8).bvshl(SmtExpr::bv_const(8, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ #imm8, LSL #8 == zext(imm8) << 8 (8-bit)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// MOVZ + MOVK proofs: two-instruction 32-bit assembly
// ---------------------------------------------------------------------------

/// Proof: MOVZ + MOVK assembles a 32-bit value from two 16-bit halves.
///
/// Theorem: forall lo16, hi16 : BV16 .
///     MOVK(MOVZ(lo16, 0), hi16, 16) == (zext32(hi16) << 16) | zext32(lo16)
///
/// The MOVZ loads the low 16 bits and zeros bits [31:16].
/// The MOVK then inserts the high 16 bits without disturbing bits [15:0].
/// The result is the full 32-bit value.
pub fn proof_movz_movk_32bit() -> ProofObligation {
    let width = 32;
    let lo16 = SmtExpr::var("lo16", 16);
    let hi16 = SmtExpr::var("hi16", 16);

    // Target: the 32-bit value (hi16 << 16) | lo16
    let target = hi16
        .clone()
        .zero_ext(16)
        .bvshl(SmtExpr::bv_const(16, width))
        .bvor(lo16.clone().zero_ext(16));

    // Strategy: MOVZ lo16 at hw=0, then MOVK hi16 at hw=1
    let step1 = encode_movz(lo16, 0, width);
    let step2 = encode_movk(step1, hi16, 16, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ+MOVK assembles 32-bit value".to_string(),
        trust_ir_expr: target,
        aarch64_expr: step2,
        inputs: vec![("lo16".to_string(), 16), ("hi16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: MOVZ + MOVK assembles 16-bit value from two 8-bit halves (exhaustive).
pub fn proof_movz_movk_16bit() -> ProofObligation {
    let width = 16;
    let lo8 = SmtExpr::var("lo8", 8);
    let hi8 = SmtExpr::var("hi8", 8);

    // Target: (hi8 << 8) | lo8
    let target = hi8
        .clone()
        .zero_ext(8)
        .bvshl(SmtExpr::bv_const(8, width))
        .bvor(lo8.clone().zero_ext(8));

    // Strategy: MOVZ lo8 at shift=0 (in 16-bit), then MOVK hi8 at shift=8
    let step1_extended = lo8.zero_ext(8);
    let step1 = step1_extended.bvshl(SmtExpr::bv_const(0, width));
    let step2 = encode_movk(step1, hi8, 8, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ+MOVK assembles 16-bit from 8-bit halves (exhaustive)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: step2,
        inputs: vec![("lo8".to_string(), 8), ("hi8".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// MOVZ + 3xMOVK proof: four-instruction 64-bit assembly
// ---------------------------------------------------------------------------

/// Proof: MOVZ + 3xMOVK assembles a 64-bit value from four 16-bit chunks.
///
/// Theorem: forall hw0, hw1, hw2, hw3 : BV16 .
///     MOVK(MOVK(MOVK(MOVZ(hw0, 0), hw1, 16), hw2, 32), hw3, 48) ==
///     (zext64(hw3) << 48) | (zext64(hw2) << 32) | (zext64(hw1) << 16) | zext64(hw0)
///
/// This is the general case for arbitrary 64-bit constants that don't
/// match simpler patterns (single MOVZ, logical immediate, MOVN).
pub fn proof_movz_movk_64bit() -> ProofObligation {
    let width = 64;
    let hw0 = SmtExpr::var("hw0", 16);
    let hw1 = SmtExpr::var("hw1", 16);
    let hw2 = SmtExpr::var("hw2", 16);
    let hw3 = SmtExpr::var("hw3", 16);

    // Target: the full 64-bit value assembled from four halfwords
    let target = hw3
        .clone()
        .zero_ext(48)
        .bvshl(SmtExpr::bv_const(48, width))
        .bvor(hw2.clone().zero_ext(48).bvshl(SmtExpr::bv_const(32, width)))
        .bvor(hw1.clone().zero_ext(48).bvshl(SmtExpr::bv_const(16, width)))
        .bvor(hw0.clone().zero_ext(48));

    // Strategy: MOVZ hw0 at 0, MOVK hw1 at 16, MOVK hw2 at 32, MOVK hw3 at 48
    let step1 = encode_movz(hw0, 0, width);
    let step2 = encode_movk(step1, hw1, 16, width);
    let step3 = encode_movk(step2, hw2, 32, width);
    let step4 = encode_movk(step3, hw3, 48, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVZ+3xMOVK assembles 64-bit value".to_string(),
        trust_ir_expr: target,
        aarch64_expr: step4,
        inputs: vec![
            ("hw0".to_string(), 16),
            ("hw1".to_string(), 16),
            ("hw2".to_string(), 16),
            ("hw3".to_string(), 16),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// ORR logical immediate proofs
// ---------------------------------------------------------------------------

/// Proof: ORR Xd, XZR, #bitmask produces the bitmask value.
///
/// Theorem: forall bitmask : BV64 . (0 | bitmask) == bitmask
///
/// This is the identity property of bitwise OR with zero. The ORR
/// instruction with XZR (zero register) as the first operand simply
/// loads the logical immediate encoding into the destination register.
pub fn proof_orr_logical_imm() -> ProofObligation {
    let width = 64;
    let bitmask = SmtExpr::var("bitmask", width);

    let target = bitmask.clone();
    let strategy = encode_orr_xzr(bitmask, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: ORR Xd, XZR, #bitmask == bitmask".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("bitmask".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: ORR Wd, WZR, #bitmask produces the bitmask value (32-bit).
pub fn proof_orr_logical_imm_32bit() -> ProofObligation {
    let width = 32;
    let bitmask = SmtExpr::var("bitmask", width);

    let target = bitmask.clone();
    let strategy = encode_orr_xzr(bitmask, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: ORR Wd, WZR, #bitmask == bitmask (32-bit)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("bitmask".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: ORR logical immediate (8-bit exhaustive).
pub fn proof_orr_logical_imm_8bit() -> ProofObligation {
    let width = 8;
    let bitmask = SmtExpr::var("bitmask", width);

    let target = bitmask.clone();
    let strategy = SmtExpr::bv_const(0, width).bvor(bitmask);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: ORR XZR, #bitmask == bitmask (8-bit)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("bitmask".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// MOVN proofs
// ---------------------------------------------------------------------------

/// Proof: MOVN #imm16, LSL #0 produces `~zext(imm16)`.
///
/// Theorem: forall imm16 : BV16 . ~(zext64(imm16) << 0) == ~zext64(imm16)
///
/// MOVN is used for mostly-ones constants where the bitwise inverse has
/// fewer non-zero chunks. For example, 0xFFFF_FFFF_FFFF_1234 is stored
/// as MOVN #0xEDCB (since ~0xFFFF_FFFF_FFFF_1234 = 0x0000_0000_0000_EDCB).
pub fn proof_movn_hw0() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);

    // Target: NOT(zext(imm16)) = all bits inverted
    let all_ones = u64::MAX;
    let target = imm16
        .clone()
        .zero_ext(48)
        .bvxor(SmtExpr::bv_const(all_ones, width));

    let strategy = encode_movn(imm16, 0, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVN #imm16, LSL #0 == ~zext(imm16)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical diagnostic identity for MOVN LSL #16, retracted under #62.
pub fn proof_movn_hw1() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);

    let shifted = imm16
        .clone()
        .zero_ext(48)
        .bvshl(SmtExpr::bv_const(16, width));
    let all_ones = u64::MAX;
    let target = shifted.bvxor(SmtExpr::bv_const(all_ones, width));

    let strategy = encode_movn(imm16, 16, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVN #imm16, LSL #16 == ~(zext(imm16) << 16)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical diagnostic identity for MOVN LSL #32, retracted under #62.
pub fn proof_movn_hw2() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);

    let shifted = imm16
        .clone()
        .zero_ext(48)
        .bvshl(SmtExpr::bv_const(32, width));
    let all_ones = u64::MAX;
    let target = shifted.bvxor(SmtExpr::bv_const(all_ones, width));

    let strategy = encode_movn(imm16, 32, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVN #imm16, LSL #32 == ~(zext(imm16) << 32)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical diagnostic identity for MOVN LSL #48, retracted under #62.
pub fn proof_movn_hw3() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);

    let shifted = imm16
        .clone()
        .zero_ext(48)
        .bvshl(SmtExpr::bv_const(48, width));
    let all_ones = u64::MAX;
    let target = shifted.bvxor(SmtExpr::bv_const(all_ones, width));

    let strategy = encode_movn(imm16, 48, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVN #imm16, LSL #48 == ~(zext(imm16) << 48)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical small-width MOVN identity, retracted under #62.
pub fn proof_movn_hw0_8bit() -> ProofObligation {
    let width = 16;
    let imm = SmtExpr::var("imm", 8);

    let all_ones: u64 = (1u64 << 16) - 1;
    let target = imm
        .clone()
        .zero_ext(8)
        .bvxor(SmtExpr::bv_const(all_ones, width));

    let extended = imm.zero_ext(8);
    let strategy = extended.bvxor(SmtExpr::bv_const(all_ones, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVN #imm8 == ~zext(imm8) (8-bit)".to_string(),
        trust_ir_expr: target,
        aarch64_expr: strategy,
        inputs: vec![("imm".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Strategy equivalence proofs
// ---------------------------------------------------------------------------

/// Proof: ORR XZR, #val is equivalent to MOVZ #val when val fits in 16 bits.
///
/// Theorem: forall val : BV16 . (0 | zext(val)) == (zext(val) << 0)
///
/// For values in [0, 0xFFFF], both single-MOVZ and ORR produce the same
/// result. The optimizer picks MOVZ (shorter encoding), but ORR would also
/// be correct.
pub fn proof_orr_movz_equivalence() -> ProofObligation {
    let width = 64;
    let val = SmtExpr::var("val", 16);

    // ORR XZR, #val (where val fits in 16 bits, treated as logical imm)
    let orr_result = SmtExpr::bv_const(0, width).bvor(val.clone().zero_ext(48));

    // MOVZ #val, LSL #0
    let movz_result = encode_movz(val, 0, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: ORR XZR, #val == MOVZ #val (16-bit overlap)".to_string(),
        trust_ir_expr: orr_result,
        aarch64_expr: movz_result,
        inputs: vec![("val".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: strategy equivalence for 8-bit values (exhaustive).
pub fn proof_orr_movz_equivalence_8bit() -> ProofObligation {
    let width = 16;
    let val = SmtExpr::var("val", 8);

    let orr_result = SmtExpr::bv_const(0, width).bvor(val.clone().zero_ext(8));
    let movz_result = val.zero_ext(8).bvshl(SmtExpr::bv_const(0, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: ORR == MOVZ equivalence (8-bit)".to_string(),
        trust_ir_expr: orr_result,
        aarch64_expr: movz_result,
        inputs: vec![("val".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Historical MOVN/MOVZ complement identity, retracted under #62.
///
/// Theorem: forall imm16 : BV16 .
///     MOVN(imm16, 0) == ~MOVZ(imm16, 0)
///
/// MOVN is defined as the bitwise NOT of the MOVZ result. This proves
/// that the MOVN strategy is exactly the complement of the MOVZ strategy,
/// confirming the relationship used in materialize_constant when choosing
/// between MOVN and multi-instruction MOVZ+MOVK sequences.
pub fn proof_movn_is_complement_of_movz() -> ProofObligation {
    let width = 64;
    let imm16 = SmtExpr::var("imm16", 16);

    // LHS: MOVN result
    let movn_result = encode_movn(imm16.clone(), 0, width);

    // RHS: NOT(MOVZ result)
    let movz_result = encode_movz(imm16, 0, width);
    let all_ones = u64::MAX;
    let not_movz = movz_result.bvxor(SmtExpr::bv_const(all_ones, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVN(imm16, 0) == ~MOVZ(imm16, 0)".to_string(),
        trust_ir_expr: movn_result,
        aarch64_expr: not_movz,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: MOVK is idempotent when writing the same value.
///
/// Theorem: forall imm16 : BV16, base : BV64 .
///     MOVK(MOVK(base, imm16, 0), imm16, 0) == MOVK(base, imm16, 0)
///
/// Writing the same halfword twice produces the same result as writing
/// it once. This validates the MOVK encoding is deterministic.
pub fn proof_movk_idempotent() -> ProofObligation {
    let width = 64;
    let base = SmtExpr::var("base", width);
    let imm16 = SmtExpr::var("imm16", 16);

    let once = encode_movk(base.clone(), imm16.clone(), 0, width);
    let twice = encode_movk(once.clone(), imm16, 0, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVK idempotent (same halfword twice)".to_string(),
        trust_ir_expr: once,
        aarch64_expr: twice,
        inputs: vec![("base".to_string(), width), ("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: MOVK at different halfwords commute.
///
/// Theorem: forall a, b : BV16, base : BV64 .
///     MOVK(MOVK(base, a, 0), b, 16) == MOVK(MOVK(base, b, 16), a, 0)
///
/// Writing non-overlapping halfwords in either order produces the same result.
/// This is important for the optimal_movz_movk_sequence ordering.
pub fn proof_movk_commutative() -> ProofObligation {
    let width = 64;
    let base = SmtExpr::var("base", width);
    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    // Order 1: MOVK a at hw=0, then MOVK b at hw=1
    let order1 = encode_movk(
        encode_movk(base.clone(), a.clone(), 0, width),
        b.clone(),
        16,
        width,
    );

    // Order 2: MOVK b at hw=1, then MOVK a at hw=0
    let order2 = encode_movk(encode_movk(base, b, 16, width), a, 0, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ConstMat: MOVK at hw=0 and hw=1 commute".to_string(),
        trust_ir_expr: order1,
        aarch64_expr: order2,
        inputs: vec![
            ("base".to_string(), width),
            ("a".to_string(), 16),
            ("b".to_string(), 16),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Independent halfword-splice specification of MOVK, built from `concat`/
/// `extract` rather than shift-and-mask.
///
/// This is the REFERENCE side of [`proof_movk_halfword_insert`]. It is written
/// deliberately in a different algebra from [`encode_movk`] (which is
/// shift/mask): the result is assembled by concatenating the destination's
/// surviving halfwords around `imm16` at the halfword slot `hw_shift`.
///
/// Because the two formulations share no sub-expression, a wrong shift, a wrong
/// mask, or an off-by-one halfword index in the encoder REFUTES rather than
/// restating itself. That is precisely the property whose absence caused the
/// shifted MOVZ/MOVN identities to be retracted under #62 (see
/// [`CONSTMAT_RETRACTED_DEGENERATE`]).
fn splice_halfword_spec(base: SmtExpr, imm16: SmtExpr, hw_shift: u32, width: u32) -> SmtExpr {
    debug_assert!(hw_shift + 16 <= width, "halfword slot outside register");
    let below = if hw_shift == 0 {
        None
    } else {
        Some(base.clone().extract(hw_shift - 1, 0))
    };
    let above = if hw_shift + 16 == width {
        None
    } else {
        Some(base.extract(width - 1, hw_shift + 16))
    };
    match (above, below) {
        (None, None) => imm16,
        (None, Some(lo)) => imm16.concat(lo),
        (Some(hi), None) => hi.concat(imm16),
        (Some(hi), Some(lo)) => hi.concat(imm16.concat(lo)),
    }
}

/// Proof: MOVK writes exactly one halfword and preserves every other bit.
///
/// Theorem: forall base : BV{width}, imm16 : BV16 .
///     splice(base, imm16, hw) == (base & ~(0xFFFF << hw)) | (zext(imm16) << hw)
///
/// The left side is an independent concat/extract splice; the right side is the
/// encoder's shift/mask semantics. This is the per-instruction MOVK obligation
/// that `function_verifier` binds to a CONCRETE (width, shift) pair, so a MOVK
/// emitted at the wrong halfword cannot inherit another slot's proof.
///
/// Unlike `proof_movk_idempotent` (which only constrains double application at
/// hw0) this pins the full architectural behaviour: the 16 written bits AND the
/// preservation of the other `width - 16`.
pub fn proof_movk_halfword_insert(hw_shift: u32, width: u32) -> ProofObligation {
    let base = SmtExpr::var("base", width);
    let imm16 = SmtExpr::var("imm16", 16);

    let spec = splice_halfword_spec(base.clone(), imm16.clone(), hw_shift, width);
    let encoded = encode_movk(base, imm16, hw_shift, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "ConstMat: MOVK {} #imm16, LSL #{} splices halfword (preserves other bits)",
            if width == 32 { "Wd" } else { "Xd" },
            hw_shift
        ),
        trust_ir_expr: spec,
        aarch64_expr: encoded,
        inputs: vec![("base".to_string(), width), ("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Every architecturally legal MOVK (width, halfword-shift) pair.
///
/// X form admits LSL #0/#16/#32/#48; W form admits only #0/#16.
pub const MOVK_HALFWORD_FORMS: &[(u32, u32)] =
    &[(64, 0), (64, 16), (64, 32), (64, 48), (32, 0), (32, 16)];

/// The static query string `function_verifier` uses to bind a concrete MOVK to
/// its (width, shift)-specific halfword-splice proof.
///
/// Returns `None` for architecturally illegal pairs, so an out-of-range shift
/// can never fall back to another slot's credit.
pub fn movk_halfword_query(width: u32, hw_shift: u32) -> Option<&'static str> {
    Some(match (width, hw_shift) {
        (64, 0) => "movk xd #imm16, lsl #0 splices halfword",
        (64, 16) => "movk xd #imm16, lsl #16 splices halfword",
        (64, 32) => "movk xd #imm16, lsl #32 splices halfword",
        (64, 48) => "movk xd #imm16, lsl #48 splices halfword",
        (32, 0) => "movk wd #imm16, lsl #0 splices halfword",
        (32, 16) => "movk wd #imm16, lsl #16 splices halfword",
        _ => return None,
    })
}

/// Encode the full-register result of a W-form MOVN, emitter-faithfully.
///
/// The encoder computes the complement in 32 bits — exactly
/// [`encode_movn`]`(imm16, hw, 32)`, the same shift/NOT(-via-XOR)/mask form the
/// emitter uses — and the architectural W-register write then zero-extends the
/// 32-bit result into the 64-bit destination. Modeling the write at 64 bits is
/// what lets the proof PIN "upper 32 bits zero", the W-form width semantics the
/// X-form theorem cannot honestly supply (ARM ARM C6.2.226: writes to a
/// W register zero bits [63:32]).
fn encode_movn_w_result(imm16: SmtExpr, hw_shift: u32) -> SmtExpr {
    encode_movn(imm16, hw_shift, 32).zero_ext(32)
}

/// Independent inverted-field specification of MOVN, built from `concat` of
/// constant all-ones fields around a 16-bit XOR complement.
///
/// This is the REFERENCE side of [`proof_movn_halfword`]. It is written
/// deliberately in a different algebra from [`encode_movn`] (which is
/// zext/shift/full-width-XOR): the bitwise NOT is pushed through the
/// concatenation, so the result is assembled as
/// `ones(above) ++ (imm16 XOR 0xFFFF) ++ ones(below)` — a 16-bit XOR plus
/// constant fields, no register-width shift and no register-width mask.
///
/// Because the two formulations share no sub-expression, a wrong shift, a
/// wrong complement width, or an off-by-one halfword index in the encoder
/// REFUTES rather than restating itself — the property whose absence caused
/// the shifted MOVN identities to be retracted under #62.
fn movn_inverted_field_spec(imm16: SmtExpr, hw_shift: u32, width: u32) -> SmtExpr {
    debug_assert!(hw_shift + 16 <= width, "halfword slot outside register");
    let not16 = imm16.bvxor(SmtExpr::bv_const(0xFFFF, 16));
    let ones = |w: u32| SmtExpr::bv_const((1u64 << w) - 1, w);
    let below = if hw_shift == 0 {
        None
    } else {
        Some(ones(hw_shift))
    };
    let above_width = width - hw_shift - 16;
    let above = if above_width == 0 {
        None
    } else {
        Some(ones(above_width))
    };
    match (above, below) {
        (None, None) => not16,
        (None, Some(lo)) => not16.concat(lo),
        (Some(hi), None) => hi.concat(not16),
        (Some(hi), Some(lo)) => hi.concat(not16.concat(lo)),
    }
}

/// Proof: MOVN inverts one halfword field and forces every other bit.
///
/// X form (`width == 64`), hw ∈ {0, 16, 32, 48}:
///
/// Theorem: forall imm16 : BV16 .
///     ones ++ ~imm16 ++ ones (fields at slot hw) == ~(zext64(imm16) << hw)
///
/// W form (`width == 32`), hw ∈ {0, 16} — the result is modeled over the full
/// 64-bit destination:
///
/// Theorem: forall imm16 : BV16 .
///     zeros32 ++ (ones ++ ~imm16 ++ ones over 32) ==
///     zext32to64(~32(zext32(imm16) << hw))
///
/// The left side is the independent concat/XOR inverted-field algebra of
/// [`movn_inverted_field_spec`]; the right side is the encoder's
/// zext/shift/full-width-XOR semantics ([`encode_movn`], and for W the
/// architectural zero-extending register write via [`encode_movn_w_result`]).
/// `function_verifier` binds each emitted MOVN to a CONCRETE (width, shift)
/// pair, so a MOVN emitted at the wrong halfword — or a W-form MOVN leaning on
/// the 64-bit complement — cannot inherit another form's proof.
pub fn proof_movn_halfword(width: u32, hw_shift: u32) -> ProofObligation {
    let imm16 = SmtExpr::var("imm16", 16);

    let (spec, encoded, name) = if width == 32 {
        let spec =
            SmtExpr::bv_const(0, 32).concat(movn_inverted_field_spec(imm16.clone(), hw_shift, 32));
        let encoded = encode_movn_w_result(imm16, hw_shift);
        (
            spec,
            encoded,
            format!(
                "ConstMat: MOVN Wd #imm16, LSL #{hw_shift} inverts halfword field \
                 (upper 32 bits zero)"
            ),
        )
    } else {
        let spec = movn_inverted_field_spec(imm16.clone(), hw_shift, 64);
        let encoded = encode_movn(imm16, hw_shift, 64);
        (
            spec,
            encoded,
            format!(
                "ConstMat: MOVN Xd #imm16, LSL #{hw_shift} inverts halfword field \
                 (other bits forced to ones)"
            ),
        )
    };

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: spec,
        aarch64_expr: encoded,
        inputs: vec![("imm16".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Every architecturally legal MOVN (width, halfword-shift) pair.
///
/// X form admits LSL #0/#16/#32/#48; W form admits only #0/#16.
pub const MOVN_FORMS: &[(u32, u32)] = &[(64, 0), (64, 16), (64, 32), (64, 48), (32, 0), (32, 16)];

/// The static query string `function_verifier` uses to bind a concrete MOVN to
/// its (width, shift)-specific inverted-field proof.
///
/// Returns `None` for architecturally illegal pairs (W-form LSL #32/#48), so
/// an out-of-range shift can never fall back to another form's credit.
pub fn movn_halfword_query(width: u32, hw_shift: u32) -> Option<&'static str> {
    Some(match (width, hw_shift) {
        (64, 0) => "movn xd #imm16, lsl #0 inverts halfword",
        (64, 16) => "movn xd #imm16, lsl #16 inverts halfword",
        (64, 32) => "movn xd #imm16, lsl #32 inverts halfword",
        (64, 48) => "movn xd #imm16, lsl #48 inverts halfword",
        (32, 0) => "movn wd #imm16, lsl #0 inverts halfword",
        (32, 16) => "movn wd #imm16, lsl #16 inverts halfword",
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Aggregate accessors
// ---------------------------------------------------------------------------

/// Return all retained core constant-materialization proofs.
///
/// Retracted degenerate shifted MOVZ/MOVN identities are omitted here, not
/// merely filtered by the database-specific aggregate.
pub fn all_const_materialize_proofs() -> Vec<ProofObligation> {
    let mut proofs = vec![
        // MOVZ at each halfword position
        proof_movz_hw0(),
        proof_movz_hw1(),
        proof_movz_hw2(),
        proof_movz_hw3(),
        // MOVZ + MOVK assembly
        proof_movz_movk_32bit(),
        proof_movz_movk_64bit(),
        // ORR logical immediate
        proof_orr_logical_imm(),
        proof_orr_logical_imm_32bit(),
        // MOVN at each halfword position
        proof_movn_hw0(),
        proof_movn_hw1(),
        proof_movn_hw2(),
        proof_movn_hw3(),
        // Strategy equivalence
        proof_orr_movz_equivalence(),
        proof_movn_is_complement_of_movz(),
        proof_movk_idempotent(),
        proof_movk_commutative(),
    ];
    // Per-(width, halfword) MOVK splice obligations. These are what make MOVK
    // promotable per-instruction: the idempotent/commute theorems above
    // constrain only hw0 double-application and hw0/hw1 ordering, never the
    // "writes these 16 bits, preserves the other N-16" contract that a
    // materialization chain actually depends on.
    for &(width, hw_shift) in MOVK_HALFWORD_FORMS {
        proofs.push(proof_movk_halfword_insert(hw_shift, width));
    }
    // Per-(width, halfword) MOVN inverted-field obligations. The retained
    // proof_movn_hw0 covers only the X-form hw0 seed; these are what make
    // every emitted MOVN form promotable per-instruction, including the
    // W-form 32-bit-complement + zero-extension semantics.
    for &(width, hw_shift) in MOVN_FORMS {
        proofs.push(proof_movn_halfword(width, hw_shift));
    }
    proofs.retain(|p| !CONSTMAT_RETRACTED_DEGENERATE.contains(&p.name.as_str()));
    proofs
}

/// Return all constant materialization proofs including 8-bit exhaustive variants.
///
/// Total: 9 retained core + 4 retained exhaustive variants = 13 proofs.
/// #62 retraction: degenerate X==X ConstMat MOVZ/MOVN shifted-immediate
/// tautologies (the trust_ir side IS the shifted-zext expression, restated as
/// the machine side; no independent immediate-encoder, a wrong shift could not
/// refute). The GENUINE multi-step assembly proofs (MOVZ+MOVK 32/64-bit, ORR
/// logical-imm, MOVK idempotent/commute, MOVZ LSL#0) remain.
const CONSTMAT_RETRACTED_DEGENERATE: &[&str] = &[
    "ConstMat: MOVN #imm16, LSL #16 == ~(zext(imm16) << 16)",
    "ConstMat: MOVN #imm16, LSL #32 == ~(zext(imm16) << 32)",
    "ConstMat: MOVN #imm16, LSL #48 == ~(zext(imm16) << 48)",
    "ConstMat: MOVN #imm8 == ~zext(imm8) (8-bit)",
    "ConstMat: MOVN(imm16, 0) == ~MOVZ(imm16, 0)",
    "ConstMat: MOVZ #imm16, LSL #16 == zext(imm16) << 16",
    "ConstMat: MOVZ #imm16, LSL #32 == zext(imm16) << 32",
    "ConstMat: MOVZ #imm16, LSL #48 == zext(imm16) << 48",
    "ConstMat: MOVZ #imm8, LSL #8 == zext(imm8) << 8 (8-bit)",
];

pub fn all_const_materialize_proofs_with_variants() -> Vec<ProofObligation> {
    let mut proofs = all_const_materialize_proofs();

    // 8-bit exhaustive variants
    proofs.push(proof_movz_hw0_8bit());
    proofs.push(proof_movz_hw1_8bit());
    proofs.push(proof_movz_movk_16bit());
    proofs.push(proof_orr_logical_imm_8bit());
    proofs.push(proof_movn_hw0_8bit());
    proofs.push(proof_orr_movz_equivalence_8bit());

    proofs.retain(|p| !CONSTMAT_RETRACTED_DEGENERATE.contains(&p.name.as_str()));
    proofs
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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
    // MOVZ proofs (64-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_movz_hw0() {
        assert_valid(&proof_movz_hw0());
    }

    #[test]
    fn test_proof_movz_hw1() {
        assert_valid(&proof_movz_hw1());
    }

    #[test]
    fn test_proof_movz_hw2() {
        assert_valid(&proof_movz_hw2());
    }

    #[test]
    fn test_proof_movz_hw3() {
        assert_valid(&proof_movz_hw3());
    }

    // -----------------------------------------------------------------------
    // MOVZ + MOVK assembly proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_movz_movk_32bit() {
        assert_valid(&proof_movz_movk_32bit());
    }

    #[test]
    fn test_proof_movz_movk_64bit() {
        assert_valid(&proof_movz_movk_64bit());
    }

    // -----------------------------------------------------------------------
    // ORR logical immediate proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_orr_logical_imm() {
        assert_valid(&proof_orr_logical_imm());
    }

    #[test]
    fn test_proof_orr_logical_imm_32bit() {
        assert_valid(&proof_orr_logical_imm_32bit());
    }

    // -----------------------------------------------------------------------
    // MOVN proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_movn_hw0() {
        assert_valid(&proof_movn_hw0());
    }

    #[test]
    fn test_proof_movn_hw1() {
        assert_valid(&proof_movn_hw1());
    }

    #[test]
    fn test_proof_movn_hw2() {
        assert_valid(&proof_movn_hw2());
    }

    #[test]
    fn test_proof_movn_hw3() {
        assert_valid(&proof_movn_hw3());
    }

    // -----------------------------------------------------------------------
    // Strategy equivalence proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_orr_movz_equivalence() {
        assert_valid(&proof_orr_movz_equivalence());
    }

    #[test]
    fn test_proof_movn_is_complement_of_movz() {
        assert_valid(&proof_movn_is_complement_of_movz());
    }

    #[test]
    fn test_proof_movk_idempotent() {
        assert_valid(&proof_movk_idempotent());
    }

    #[test]
    fn test_proof_movk_commutative() {
        assert_valid(&proof_movk_commutative());
    }

    // -----------------------------------------------------------------------
    // 8-bit exhaustive variant proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_movz_hw0_8bit() {
        assert_valid(&proof_movz_hw0_8bit());
    }

    #[test]
    fn test_proof_movz_hw1_8bit() {
        assert_valid(&proof_movz_hw1_8bit());
    }

    #[test]
    fn test_proof_movz_movk_16bit() {
        assert_valid(&proof_movz_movk_16bit());
    }

    #[test]
    fn test_proof_orr_logical_imm_8bit() {
        assert_valid(&proof_orr_logical_imm_8bit());
    }

    #[test]
    fn test_proof_movn_hw0_8bit() {
        assert_valid(&proof_movn_hw0_8bit());
    }

    #[test]
    fn test_proof_orr_movz_equivalence_8bit() {
        assert_valid(&proof_orr_movz_equivalence_8bit());
    }

    // -----------------------------------------------------------------------
    // Aggregate tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_const_materialize_proofs() {
        for obligation in all_const_materialize_proofs() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn test_all_const_materialize_proofs_with_variants() {
        for obligation in all_const_materialize_proofs_with_variants() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn test_proof_count() {
        assert_eq!(
            all_const_materialize_proofs().len(),
            9 + MOVK_HALFWORD_FORMS.len() + MOVN_FORMS.len(),
            "expected 9 retained core proofs + one MOVK halfword-splice proof \
             and one MOVN inverted-field proof per architecturally legal \
             (width, shift) form"
        );
        assert_eq!(
            all_const_materialize_proofs_with_variants().len(),
            13 + MOVK_HALFWORD_FORMS.len() + MOVN_FORMS.len(),
            "expected 13 retained proofs after removing all degenerate shifted \
             MOVZ/MOVN identities retracted in #62, plus the MOVK splice and \
             MOVN inverted-field forms"
        );
    }

    // -----------------------------------------------------------------------
    // MOVK halfword-splice proofs (the per-instruction MOVK promotion basis)
    // -----------------------------------------------------------------------

    #[test]
    fn movk_halfword_insert_holds_for_every_legal_form() {
        for &(width, hw_shift) in MOVK_HALFWORD_FORMS {
            assert_valid(&proof_movk_halfword_insert(hw_shift, width));
        }
    }

    /// NON-VACUITY: the splice spec and the shift/mask encoder are genuinely
    /// independent, so mismatching the halfword slot MUST refute.
    ///
    /// Without this, `proof_movk_halfword_insert` could be an X==X restatement
    /// of the kind retracted under #62 and nobody would notice.
    #[test]
    fn movk_halfword_insert_refutes_when_slot_disagrees() {
        for &(width, hw_shift) in MOVK_HALFWORD_FORMS {
            for &(other_width, other_shift) in MOVK_HALFWORD_FORMS {
                if other_width != width || other_shift == hw_shift {
                    continue;
                }
                let base = SmtExpr::var("base", width);
                let imm16 = SmtExpr::var("imm16", 16);
                // Spec at the CORRECT slot vs encoder at a DIFFERENT slot.
                let mut wrong = proof_movk_halfword_insert(hw_shift, width);
                wrong.aarch64_expr = encode_movk(base, imm16, other_shift, width);
                assert!(
                    !matches!(verify_by_evaluation(&wrong), VerificationResult::Valid),
                    "MOVK splice proof is VACUOUS: spec at hw={hw_shift} accepted an \
                     encoder writing hw={other_shift} at width {width}"
                );
            }
        }
    }

    /// NON-VACUITY: a MOVK that clobbers bits outside its halfword must refute.
    /// This is the half of the contract `proof_movk_idempotent` never covered.
    #[test]
    fn movk_halfword_insert_refutes_when_other_bits_not_preserved() {
        for &(width, hw_shift) in MOVK_HALFWORD_FORMS {
            let imm16 = SmtExpr::var("imm16", 16);
            // A "MOVZ-like" encoder: writes the halfword but ZEROES everything else.
            let clobbering = imm16
                .clone()
                .zero_ext(width - 16)
                .bvshl(SmtExpr::bv_const(hw_shift as u64, width));
            let mut wrong = proof_movk_halfword_insert(hw_shift, width);
            wrong.aarch64_expr = clobbering;
            assert!(
                !matches!(verify_by_evaluation(&wrong), VerificationResult::Valid),
                "MOVK splice proof does not pin bit PRESERVATION at width {width} hw={hw_shift}: \
                 a destructive MOVZ-like encoder was accepted"
            );
        }
    }

    /// The query table must cover exactly the legal forms and reject the rest,
    /// so an out-of-range shift can never inherit another slot's credit.
    #[test]
    fn movk_halfword_query_covers_exactly_the_legal_forms() {
        for &(width, hw_shift) in MOVK_HALFWORD_FORMS {
            let q = movk_halfword_query(width, hw_shift)
                .unwrap_or_else(|| panic!("no query for legal form ({width}, {hw_shift})"));
            let name = proof_movk_halfword_insert(hw_shift, width)
                .name
                .to_lowercase();
            assert!(
                name.contains(q),
                "query {q:?} does not substring-match proof name {name:?}"
            );
        }
        // Architecturally illegal pairs get no credit at all.
        for &(width, hw_shift) in &[(32u32, 32u32), (32, 48), (64, 8), (64, 64), (16, 0)] {
            assert!(
                movk_halfword_query(width, hw_shift).is_none(),
                "illegal MOVK form ({width}, {hw_shift}) must not resolve to a proof"
            );
        }
    }

    /// Every MOVK query string must resolve to exactly ONE proof in the
    /// aggregate — a substring that matched two rows would make credit ambiguous.
    #[test]
    fn each_movk_query_matches_exactly_one_proof() {
        let proofs = all_const_materialize_proofs();
        for &(width, hw_shift) in MOVK_HALFWORD_FORMS {
            let q = movk_halfword_query(width, hw_shift).expect("legal form");
            let hits = proofs
                .iter()
                .filter(|p| p.name.to_lowercase().contains(q))
                .count();
            assert_eq!(
                hits, 1,
                "query {q:?} matched {hits} proofs, expected exactly 1"
            );
        }
    }

    // -----------------------------------------------------------------------
    // MOVN inverted-field proofs (the per-instruction MOVN promotion basis)
    // -----------------------------------------------------------------------

    #[test]
    fn movn_halfword_holds_for_every_legal_form() {
        for &(width, hw_shift) in MOVN_FORMS {
            let proof = proof_movn_halfword(width, hw_shift);
            assert!(
                !proof.is_degenerate(),
                "MOVN proof for ({width}, {hw_shift}) is a degenerate X==X restatement"
            );
            assert_valid(&proof);
        }
    }

    /// NON-VACUITY: the inverted-field spec and the shift/XOR encoder are
    /// genuinely independent, so mismatching the halfword slot MUST refute.
    ///
    /// Without this, `proof_movn_halfword` could be an X==X restatement of the
    /// kind retracted under #62 and nobody would notice.
    #[test]
    fn movn_halfword_refutes_when_slot_disagrees() {
        for &(width, hw_shift) in MOVN_FORMS {
            for &(other_width, other_shift) in MOVN_FORMS {
                if other_width != width || other_shift == hw_shift {
                    continue;
                }
                let imm16 = SmtExpr::var("imm16", 16);
                // Spec at the CORRECT slot vs encoder at a DIFFERENT slot.
                let mut wrong = proof_movn_halfword(width, hw_shift);
                wrong.aarch64_expr = if width == 32 {
                    encode_movn_w_result(imm16, other_shift)
                } else {
                    encode_movn(imm16, other_shift, 64)
                };
                assert!(
                    !matches!(verify_by_evaluation(&wrong), VerificationResult::Valid),
                    "MOVN inverted-field proof is VACUOUS: spec at hw={hw_shift} accepted \
                     an encoder shifting hw={other_shift} at width {width}"
                );
            }
        }
    }

    /// NON-VACUITY: an encoder that flips a single immediate bit must refute
    /// at every legal form.
    #[test]
    fn movn_halfword_refutes_when_an_immediate_bit_flips() {
        for &(width, hw_shift) in MOVN_FORMS {
            for flipped_bit in [0u64, 15] {
                let corrupted =
                    SmtExpr::var("imm16", 16).bvxor(SmtExpr::bv_const(1 << flipped_bit, 16));
                let mut wrong = proof_movn_halfword(width, hw_shift);
                wrong.aarch64_expr = if width == 32 {
                    encode_movn_w_result(corrupted, hw_shift)
                } else {
                    encode_movn(corrupted, hw_shift, 64)
                };
                assert!(
                    !matches!(verify_by_evaluation(&wrong), VerificationResult::Valid),
                    "MOVN proof at width {width} hw={hw_shift} did not refute a \
                     bit-{flipped_bit} immediate corruption"
                );
            }
        }
    }

    /// NON-VACUITY: the W-form proof pins the upper-32-zeroing register write.
    /// A "64-bit complement" encoder (which forces bits [63:32] to ONES) must
    /// refute — this is exactly the width-semantics gap the coverage gate
    /// documents for opcode-wide MOVN credit.
    #[test]
    fn movn_w_form_refutes_when_upper_bits_not_zeroed() {
        for &(width, hw_shift) in MOVN_FORMS {
            if width != 32 {
                continue;
            }
            let imm16 = SmtExpr::var("imm16", 16);
            let mut wrong = proof_movn_halfword(width, hw_shift);
            wrong.aarch64_expr = encode_movn(imm16, hw_shift, 64);
            assert!(
                !matches!(verify_by_evaluation(&wrong), VerificationResult::Valid),
                "W-form MOVN proof at hw={hw_shift} does not pin the zero-extension: \
                 a 64-bit-complement encoder (upper bits ones) was accepted"
            );
        }
    }

    /// The query table must cover exactly the legal forms and reject the rest,
    /// so an illegal W-form shift can never inherit an X-form slot's credit.
    #[test]
    fn movn_halfword_query_covers_exactly_the_legal_forms() {
        for &(width, hw_shift) in MOVN_FORMS {
            let q = movn_halfword_query(width, hw_shift)
                .unwrap_or_else(|| panic!("no query for legal form ({width}, {hw_shift})"));
            let name = proof_movn_halfword(width, hw_shift).name.to_lowercase();
            assert!(
                name.contains(q),
                "query {q:?} does not substring-match proof name {name:?}"
            );
        }
        // Architecturally illegal pairs get no credit at all.
        for &(width, hw_shift) in &[(32u32, 32u32), (32, 48), (64, 8), (64, 64), (16, 0)] {
            assert!(
                movn_halfword_query(width, hw_shift).is_none(),
                "illegal MOVN form ({width}, {hw_shift}) must not resolve to a proof"
            );
        }
    }

    /// Every MOVN query string must resolve to exactly ONE proof in the
    /// aggregate — a substring that matched two rows would make credit ambiguous.
    #[test]
    fn each_movn_query_matches_exactly_one_proof() {
        let proofs = all_const_materialize_proofs();
        for &(width, hw_shift) in MOVN_FORMS {
            let q = movn_halfword_query(width, hw_shift).expect("legal form");
            let hits = proofs
                .iter()
                .filter(|p| p.name.to_lowercase().contains(q))
                .count();
            assert_eq!(
                hits, 1,
                "query {q:?} matched {hits} proofs, expected exactly 1"
            );
        }
    }

    #[test]
    fn public_aggregates_exclude_every_retracted_constmat_row() {
        for proof in all_const_materialize_proofs()
            .into_iter()
            .chain(all_const_materialize_proofs_with_variants())
        {
            assert!(
                !CONSTMAT_RETRACTED_DEGENERATE.contains(&proof.name.as_str()),
                "public aggregate leaked retracted proof {:?}",
                proof.name
            );
        }
    }

    // -----------------------------------------------------------------------
    // Negative tests: verify incorrect strategies are detected
    // -----------------------------------------------------------------------

    /// Negative test: MOVZ at wrong shift is NOT equivalent to correct shift.
    #[test]
    fn test_wrong_movz_shift_detected() {
        let width = 64;
        let imm16 = SmtExpr::var("imm16", 16);

        // Wrong: MOVZ at hw=0 claimed to equal MOVZ at hw=1
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: MOVZ hw=0 == MOVZ hw=1".to_string(),
            trust_ir_expr: encode_movz(imm16.clone(), 0, width),
            aarch64_expr: encode_movz(imm16, 16, width),
            inputs: vec![("imm16".to_string(), 16)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_by_evaluation(&obligation);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!("Expected Invalid for wrong shift, got {:?}", other),
        }
    }

    /// Negative test: MOVN is NOT equivalent to MOVZ (for most values).
    #[test]
    fn test_movn_not_equal_movz() {
        let width = 64;
        let imm16 = SmtExpr::var("imm16", 16);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: MOVN hw=0 == MOVZ hw=0".to_string(),
            trust_ir_expr: encode_movn(imm16.clone(), 0, width),
            aarch64_expr: encode_movz(imm16, 0, width),
            inputs: vec![("imm16".to_string(), 16)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_by_evaluation(&obligation);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!("Expected Invalid for MOVN==MOVZ, got {:?}", other),
        }
    }

    /// Negative test: MOVK at wrong position corrupts value.
    #[test]
    fn test_wrong_movk_position_detected() {
        let width = 32;
        let lo16 = SmtExpr::var("lo16", 16);
        let hi16 = SmtExpr::var("hi16", 16);

        // Wrong: both MOVK at hw=0 (overwrites the first MOVZ)
        let target = hi16
            .clone()
            .zero_ext(16)
            .bvshl(SmtExpr::bv_const(16, width))
            .bvor(lo16.clone().zero_ext(16));
        let step1 = encode_movz(lo16, 0, width);
        let wrong = encode_movk(step1, hi16, 0, width); // wrong: should be hw=16

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: MOVK at hw=0 instead of hw=16".to_string(),
            trust_ir_expr: target,
            aarch64_expr: wrong,
            inputs: vec![("lo16".to_string(), 16), ("hi16".to_string(), 16)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_by_evaluation(&obligation);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!("Expected Invalid for wrong MOVK position, got {:?}", other),
        }
    }

    // -----------------------------------------------------------------------
    // SMT-LIB2 output tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_smt2_output_movz_hw0() {
        let obligation = proof_movz_hw0();
        let smt2 = obligation.to_smt2();
        assert!(smt2.contains("(set-logic QF_BV)"));
        assert!(smt2.contains("(declare-const imm16 (_ BitVec 16))"));
        assert!(smt2.contains("bvshl"));
        assert!(smt2.contains("(check-sat)"));
    }

    #[test]
    fn test_smt2_output_movz_movk_32bit() {
        let obligation = proof_movz_movk_32bit();
        let smt2 = obligation.to_smt2();
        assert!(smt2.contains("(set-logic QF_BV)"));
        assert!(smt2.contains("lo16"));
        assert!(smt2.contains("hi16"));
        assert!(smt2.contains("bvand"));
        assert!(smt2.contains("bvor"));
        assert!(smt2.contains("(check-sat)"));
    }

    #[test]
    fn test_smt2_output_movn_hw0() {
        let obligation = proof_movn_hw0();
        let smt2 = obligation.to_smt2();
        assert!(smt2.contains("(set-logic QF_BV)"));
        assert!(smt2.contains("bvxor"));
        assert!(smt2.contains("(check-sat)"));
    }

    // -----------------------------------------------------------------------
    // Concrete value spot-checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_movz_concrete_0x1234() {
        // MOVZ #0x1234 should produce 0x1234
        use std::collections::HashMap;
        let expr = encode_movz(SmtExpr::bv_const(0x1234, 16), 0, 64);
        let env: HashMap<String, u64> = HashMap::new();
        let result = expr.eval(&env);
        assert_eq!(result, crate::smt::EvalResult::Bv(0x1234));
    }

    #[test]
    fn test_movz_concrete_shifted() {
        // MOVZ #0xABCD, LSL #32 should produce 0x0000_ABCD_0000_0000
        use std::collections::HashMap;
        let expr = encode_movz(SmtExpr::bv_const(0xABCD, 16), 32, 64);
        let env: HashMap<String, u64> = HashMap::new();
        let result = expr.eval(&env);
        assert_eq!(result, crate::smt::EvalResult::Bv(0x0000_ABCD_0000_0000));
    }

    #[test]
    fn test_movk_concrete() {
        // Start with 0x0000_0000_0000_BABE, MOVK #0xCAFE at hw=1
        // Result should be 0x0000_0000_CAFE_BABE
        use std::collections::HashMap;
        let base = SmtExpr::bv_const(0xBABE, 64);
        let expr = encode_movk(base, SmtExpr::bv_const(0xCAFE, 16), 16, 64);
        let env: HashMap<String, u64> = HashMap::new();
        let result = expr.eval(&env);
        assert_eq!(result, crate::smt::EvalResult::Bv(0x0000_0000_CAFE_BABE));
    }

    #[test]
    fn test_movn_concrete() {
        // MOVN #0xEDCB at hw=0 should produce ~0x0000_0000_0000_EDCB
        // = 0xFFFF_FFFF_FFFF_1234
        use std::collections::HashMap;
        let expr = encode_movn(SmtExpr::bv_const(0xEDCB, 16), 0, 64);
        let env: HashMap<String, u64> = HashMap::new();
        let result = expr.eval(&env);
        assert_eq!(result, crate::smt::EvalResult::Bv(0xFFFF_FFFF_FFFF_1234));
    }

    #[test]
    fn test_full_64bit_assembly_concrete() {
        // Assemble 0xDEAD_BEEF_CAFE_BABE via MOVZ+3xMOVK
        use std::collections::HashMap;
        let step1 = encode_movz(SmtExpr::bv_const(0xBABE, 16), 0, 64);
        let step2 = encode_movk(step1, SmtExpr::bv_const(0xCAFE, 16), 16, 64);
        let step3 = encode_movk(step2, SmtExpr::bv_const(0xBEEF, 16), 32, 64);
        let step4 = encode_movk(step3, SmtExpr::bv_const(0xDEAD, 16), 48, 64);
        let env: HashMap<String, u64> = HashMap::new();
        let result = step4.eval(&env);
        assert_eq!(result, crate::smt::EvalResult::Bv(0xDEAD_BEEF_CAFE_BABE));
    }
}
