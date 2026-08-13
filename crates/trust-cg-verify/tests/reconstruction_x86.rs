// trust-cg-verify/tests/reconstruction_x86.rs — Phase-2 operand-reconstruction
// refutation suite (x86-64 integer ALU/bitwise/shift/extend), task #66.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// MIRROR of tests/reconstruction_alu.rs (AArch64) / reconstruction_riscv.rs.
// These tests are the PROOF THAT THE MECHANISM HAS CONTENT for x86-64. The static
// x86-64 lowering proofs build BOTH sides of an obligation from the SAME symbolic
// vars, so they are structurally X==X and the strict gate (#61) credits them ZERO
// — a wrong isel choice could never refute them. The reconstruction path rebuilds
// the MACHINE side from the REAL emitted opcode+operands, so:
//
//   (a) a correct ADD reconstructs to bvadd==bvadd and is credited GENUINELY
//       (provenance Reconstructed), even though the two sides happen to be equal;
//   (b) injecting a wrong opcode (Add-as-Sub, Shl-as-Shr, Movzx-as-Movsx) ⇒ REFUTE;
//   (c) wiring a non-commutative op (Sub, shifts) with swapped source operands ⇒
//       REFUTE; commutative families (Add/Imul/And/Or/Xor) cannot catch an operand
//       swap — documented;
//   (d) the reconstructed path performs NO `name.contains` lookup (anti-f81e45b);
//   (e) the shift `count < width` precondition is LOAD-BEARING (#57): strip it
//       and a shift by exactly width REFUTES.
//
// (b)/(c) construct the BUGGY obligation with the very same public encoders the
// reconstructor uses internally — `encode_trust_ir_*` for the source side and
// `encode_<x86 op>` for the machine side — so they test the exact source-vs-
// machine comparison the mechanism performs.

use trust_cg_ir::X86Opcode;
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_lower::x86_64_isel::{X86ISelInst, X86ISelOperand};

use trust_cg_verify::lowering_proof::MachineSideProvenance;
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::trust_ir_semantics::{
    encode_trust_ir_binop, encode_trust_ir_bitwise_binop, encode_trust_ir_bnot,
    encode_trust_ir_ctpop, encode_trust_ir_cttz, encode_trust_ir_fp_binop, encode_trust_ir_sextend,
    encode_trust_ir_shift, encode_trust_ir_uextend,
};
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::x86_64_semantics::{
    X86FPSize, X86OperandSize, encode_add_rr, encode_and_rr, encode_fp_add_rr, encode_fp_sub_rr,
    encode_imul_rr, encode_lea_base_disp, encode_lea_base_index_scale,
    encode_lea_base_index_scale_disp, encode_movsx, encode_movzx, encode_neg, encode_popcnt,
    encode_shl_rr_masked, encode_shr_rr_masked, encode_sub_rr, encode_tzcnt,
};
use trust_cg_verify::{
    ProofObligation, reconstruct_x86_alu_obligation, representative_x86_reconstructable_inst,
    verify_by_evaluation,
};

use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn r64(id: u32) -> X86ISelOperand {
    X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

const S: X86OperandSize = X86OperandSize::S64;

// FP-64 named leaves used by the wiring-preserving FP reconstruction evaluator.
fn fp_a() -> SmtExpr {
    SmtExpr::var("recon_a", 64)
}
fn fp_b() -> SmtExpr {
    SmtExpr::var("recon_b", 64)
}

/// A reconstructed FP-only obligation (operands as named FP-64 leaves), used by
/// the wrong-opcode / wrong-wiring refutation tests.
fn buggy_fp_binary(name: &str, trust_ir_expr: SmtExpr, machine_expr: SmtExpr) -> ProofObligation {
    ProofObligation {
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![
            ("recon_a".to_string(), 11, 53),
            ("recon_b".to_string(), 11, 53),
        ],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "buggy".to_string(),
            arity: 2,
        },
    }
}

/// The reconstructable opcodes split by arity/shape, used in the round-trip test.
fn all_reconstructable() -> Vec<X86Opcode> {
    vec![
        X86Opcode::AddRR,
        X86Opcode::AddRI,
        X86Opcode::SubRR,
        X86Opcode::SubRI,
        X86Opcode::ImulRR,
        X86Opcode::Neg,
        X86Opcode::AndRR,
        X86Opcode::AndRI,
        X86Opcode::OrRR,
        X86Opcode::OrRI,
        X86Opcode::XorRR,
        X86Opcode::XorRI,
        X86Opcode::Not,
        X86Opcode::ShlRR,
        X86Opcode::ShlRI,
        X86Opcode::ShrRR,
        X86Opcode::ShrRI,
        X86Opcode::SarRR,
        X86Opcode::SarRI,
        X86Opcode::Movzx,
        X86Opcode::MovzxW,
        X86Opcode::MovsxB,
        X86Opcode::MovsxW,
        X86Opcode::Movsx,
        // Effective-address (LEA) reconstruction: base[+index*scale]+disp from the
        // trust_ir Iadd/Imul source vs the INDEPENDENT x86 `encode_lea_*` machine
        // encoder — the genuine EA obligation the degenerate X==X LEA proofs (#62)
        // were retracted pending.
        X86Opcode::Lea,
        X86Opcode::LeaSib,
        // to-100% scalar batch:
        X86Opcode::MovRR,
        X86Opcode::MovRR32,
        X86Opcode::MovssRR,
        X86Opcode::MovsdRR,
        X86Opcode::ImulRRI,
        X86Opcode::Roundsd,
        X86Opcode::Roundss,
        // ---- SSE2/SSE4.1 packed value ops (lane-wise reconstruction) ----
        // packed integer arithmetic (B/W/D/Q element widths):
        X86Opcode::Paddb,
        X86Opcode::Paddw,
        X86Opcode::Paddd,
        X86Opcode::Paddq,
        X86Opcode::Psubb,
        X86Opcode::Psubw,
        X86Opcode::Psubd,
        X86Opcode::Psubq,
        X86Opcode::Pmullw,
        X86Opcode::Pmulld,
        // horizontal byte sum-of-absolute-differences (the byte-sum vectorizer):
        X86Opcode::Psadbw,
        // packed integer compare-mask (incl. q-lane SSE4.1/4.2):
        X86Opcode::Pcmpeqb,
        X86Opcode::Pcmpeqw,
        X86Opcode::Pcmpeqd,
        X86Opcode::Pcmpeqq,
        X86Opcode::Pcmpgtb,
        X86Opcode::Pcmpgtw,
        X86Opcode::Pcmpgtd,
        X86Opcode::Pcmpgtq,
        // full-width packed bitwise:
        X86Opcode::Pand,
        X86Opcode::Por,
        X86Opcode::Pxor,
        X86Opcode::Pandn,
        X86Opcode::Andps,
        X86Opcode::Andpd,
        // packed FP (PS=4xf32, PD=2xf64):
        X86Opcode::Addps,
        X86Opcode::Subps,
        X86Opcode::Mulps,
        X86Opcode::Divps,
        X86Opcode::Addpd,
        X86Opcode::Subpd,
        X86Opcode::Mulpd,
        X86Opcode::Divpd,
        // ---- MEMORY tier (task #76): genuine effective-address reconstruction ----
        // integer loads/stores (width fixed by opcode):
        X86Opcode::MovRM8,
        X86Opcode::MovRM16,
        X86Opcode::MovRM32,
        X86Opcode::MovRM,
        X86Opcode::MovMR8,
        X86Opcode::MovMR16,
        X86Opcode::MovMR32,
        X86Opcode::MovMR,
        // FP loads/stores:
        X86Opcode::MovssRM,
        X86Opcode::MovsdRM,
        X86Opcode::MovssMR,
        X86Opcode::MovsdMR,
        // memory-source ALU (reg OP load(ea)):
        X86Opcode::AddRM,
        X86Opcode::SubRM,
        X86Opcode::CmpRM,
        // register-memory signed multiply (reg * load(ea)):
        X86Opcode::ImulRM,
        // in-place increment / decrement:
        X86Opcode::Inc,
        X86Opcode::Dec,
        // ---- IMPLICIT-OPERAND tier (task #76 final): division + cond-move ----
        // Idiv/Div: the implicit double-width RDX:RAX dividend (sext/zext) with the
        // sdiv/udiv quotient + srem/urem remainder.
        X86Opcode::Idiv,
        X86Opcode::Div,
        // Cmovcc/Cmovcc32: the implicit RFLAGS condition as a genuine CMP+CMOV pair.
        X86Opcode::Cmovcc,
        X86Opcode::Cmovcc32,
    ]
}

// ---------------------------------------------------------------------------
// (a) Correct reconstruction: Valid + Reconstructed provenance + genuine
// ---------------------------------------------------------------------------

#[test]
fn all_reconstructable_opcodes_reconstruct_valid_with_reconstructed_provenance() {
    for op in all_reconstructable() {
        let inst = representative_x86_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must have a representative"));
        let ob = reconstruct_x86_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(ob.is_reconstructed(), "{op:?} must be Reconstructed");
        match &ob.machine_side_provenance {
            MachineSideProvenance::Reconstructed { from_opcode, .. } => {
                assert_eq!(from_opcode, &format!("{op:?}"));
            }
            other => panic!("{op:?} expected Reconstructed, got {other:?}"),
        }
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{op:?} correct lowering must be Valid"
        );
        // NOTE: a CORRECT commutative lowering reconstructs to `bvadd == bvadd`,
        // which is structurally equal — so `is_genuinely_proven()` (structural
        // distinctness) is NOT the right credit predicate here. The credit rule
        // keys on `is_reconstructed()` (asserted above): the non-vacuity comes
        // from the machine side being built from the REAL opcode+operands, so a
        // wrong opcode/wiring would refute (the (b)/(c) tests prove this).
    }
}

#[test]
fn addri_immediate_form_binds_imm_as_constant() {
    // `ADD r, r, #7` — the immediate binds to a bv_const, not a declared input.
    let inst = X86ISelInst::new(
        X86Opcode::AddRI,
        vec![r64(0), r64(1), X86ISelOperand::Imm(7)],
    );
    let ob = reconstruct_x86_alu_obligation(&inst).expect("AddRI must reconstruct");
    assert!(ob.is_reconstructed());
    assert_eq!(
        ob.inputs.len(),
        1,
        "only the src1 register is a declared input"
    );
    assert_eq!(ob.inputs[0].1, 64);
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

#[test]
fn shlri_immediate_count_reconstructs_valid() {
    // SHL r, r, #3 — the count is an immediate; masked machine side + load-bearing
    // precondition (the const count < width is trivially Valid).
    let inst = X86ISelInst::new(
        X86Opcode::ShlRI,
        vec![r64(0), r64(1), X86ISelOperand::Imm(3)],
    );
    let ob = reconstruct_x86_alu_obligation(&inst).expect("ShlRI must reconstruct");
    assert!(ob.is_reconstructed());
    assert_eq!(
        ob.preconditions.len(),
        1,
        "shift must carry the load-bearing count<width precondition"
    );
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

#[test]
fn shlrr_register_count_form_binds_cl_as_input() {
    // SHL r, CL — the RR form is `[dst, src1]` (count implicit in CL). The count
    // binds to a fresh symbolic input + the load-bearing precondition.
    let inst = X86ISelInst::new(X86Opcode::ShlRR, vec![r64(0), r64(1)]);
    let ob = reconstruct_x86_alu_obligation(&inst).expect("ShlRR must reconstruct");
    assert!(ob.is_reconstructed());
    assert_eq!(
        ob.inputs.len(),
        2,
        "ShlRR declares src1 + the implicit CL count as inputs"
    );
    assert_eq!(
        ob.preconditions.len(),
        1,
        "shift carries count<width precondition"
    );
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

// ---------------------------------------------------------------------------
// (b) Wrong-opcode refute, per family
// ---------------------------------------------------------------------------

fn buggy_binary(
    name: &str,
    from_opcode: &str,
    trust_ir_expr: SmtExpr,
    machine_expr: SmtExpr,
) -> ProofObligation {
    ProofObligation {
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![
            ("recon_src1".to_string(), 64),
            ("recon_src2".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: from_opcode.to_string(),
            arity: 2,
        },
    }
}

#[test]
fn injected_sub_for_intended_iadd_refutes() {
    // ARITHMETIC family: isel emitted SUB where Iadd was intended ⇒ bvadd != bvsub.
    let a = SmtExpr::var("recon_src1", 64);
    let b = SmtExpr::var("recon_src2", 64);
    let buggy = buggy_binary(
        "RECONSTRUCTED x86_64 Iadd -> SubRR (INJECTED isel bug)",
        "SubRR",
        encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), b.clone()),
        encode_sub_rr(S, a, b), // WRONG opcode
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "SUB-for-Iadd must REFUTE (bvadd != bvsub)"
    );
    assert!(buggy.is_genuinely_proven());
}

#[test]
fn injected_and_for_intended_bxor_refutes() {
    // BITWISE family: isel emitted AND where Bxor was intended ⇒ bvxor != bvand.
    let a = SmtExpr::var("recon_src1", 64);
    let b = SmtExpr::var("recon_src2", 64);
    let buggy = buggy_binary(
        "RECONSTRUCTED x86_64 Bxor -> AndRR (INJECTED isel bug)",
        "AndRR",
        encode_trust_ir_bitwise_binop(&Opcode::Bxor, Type::I64, a.clone(), b.clone()),
        encode_and_rr(S, a, b), // WRONG opcode
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "AND-for-Bxor must REFUTE (bvxor != bvand)"
    );
}

#[test]
fn injected_shr_for_intended_ishl_refutes() {
    // SHIFT family: isel emitted SHR (logical right) where Ishl (left) was intended
    // ⇒ bvshl != bvlshr. Refutes EVEN WITH the in-range precondition.
    let a = SmtExpr::var("recon_src1", 8);
    let amt = SmtExpr::var("recon_src2", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 Ishl -> ShrRR (INJECTED wrong shift opcode)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_shr_rr_masked(S, a.clone(), amt.clone()), // WRONG: bvlshr
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "ShrRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "SHR-for-Ishl must REFUTE (bvshl != bvlshr) even WITH the in-range precondition"
    );
}

#[test]
fn injected_movsx_for_intended_uextend_refutes() {
    // EXTEND family: isel emitted MOVSX (sign-extend) where Uextend (zero-extend)
    // was intended. For a negative i8 source the sign-extend and zero-extend differ.
    let sym = SmtExpr::var("recon_src", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 Uextend_8_to_64 -> MovsxB (INJECTED isel bug)".to_string(),
        trust_ir_expr: encode_trust_ir_uextend(8, 64, sym.clone()),
        aarch64_expr: encode_movsx(8, 64, sym.clone().zero_ext(56)), // WRONG: sign-extend
        inputs: vec![("recon_src".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "MovsxB".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "MOVSX-for-Uextend must REFUTE (sign vs zero extension differ for negatives)"
    );
}

#[test]
fn injected_movzx_for_intended_sextend_refutes() {
    // The reverse: MOVZX (zero) where Sextend (sign) was intended.
    let sym = SmtExpr::var("recon_src", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 Sextend_8_to_64 -> Movzx (INJECTED isel bug)".to_string(),
        trust_ir_expr: encode_trust_ir_sextend(8, 64, sym.clone()),
        aarch64_expr: encode_movzx(8, 64, sym.clone().zero_ext(56)), // WRONG: zero-extend
        inputs: vec![("recon_src".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Movzx".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "MOVZX-for-Sextend must REFUTE (zero vs sign extension differ for negatives)"
    );
}

// ---------------------------------------------------------------------------
// Effective-address (LEA) reconstruction has CONTENT — the EA obligation is NOT
// the degenerate X==X LEA proof retracted in #62. The trust_ir Iadd/Imul source
// and the INDEPENDENT x86 `encode_lea_*` machine encoder are compared, so a wrong
// EA encoder (wrong-sign disp, wrong scale) REFUTES.
// ---------------------------------------------------------------------------

#[test]
fn faithful_plain_lea_base_disp_validates() {
    // base + disp (trust_ir Iadd) == encode_lea_base_disp(base, disp) ⇒ Valid.
    let base = SmtExpr::var("recon_base", 64);
    let ob = ProofObligation {
        name: "RECONSTRUCTED x86_64 EffectiveAddress -> Lea (faithful base+disp)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(
            &Opcode::Iadd,
            Type::I64,
            base.clone(),
            SmtExpr::bv_const(8, 64),
        ),
        aarch64_expr: encode_lea_base_disp(base.clone(), 8, 64),
        inputs: vec![("recon_base".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Lea".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
        "the faithful base+disp LEA encoder must reconstruct Valid"
    );
}

#[test]
fn injected_wrong_sign_disp_for_lea_refutes() {
    // EFFECTIVE-ADDRESS family: a buggy plain-LEA encoder that SUBTRACTS the
    // displacement (base - disp) instead of adding it ⇒ base+disp != base-disp ⇒
    // REFUTE. Proves the EA reconstruction has content.
    let base = SmtExpr::var("recon_base", 64);
    let disp = SmtExpr::bv_const(8, 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 EffectiveAddress -> Lea (INJECTED wrong-sign disp)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I64, base.clone(), disp.clone()),
        aarch64_expr: encode_sub_rr(S, base.clone(), disp), // WRONG: base - disp
        inputs: vec![("recon_base".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Lea".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "a base-disp LEA encoder must REFUTE against base+disp"
    );
}

#[test]
fn injected_wrong_scale_for_leasib_refutes() {
    // SIB-LEA: a buggy encoder using scale=4 where the intended effective address
    // uses scale=1 ⇒ base+index != base+index*4 ⇒ REFUTE. Proves the EA obligation
    // is scale-sensitive (a wrong addressing-mode scale is caught).
    let base = SmtExpr::var("recon_base", 64);
    let index = SmtExpr::var("recon_index", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 EffectiveAddress -> LeaSib (INJECTED wrong scale)".to_string(),
        // intended source: base + index*1
        trust_ir_expr: encode_trust_ir_binop(
            &Opcode::Iadd,
            Type::I64,
            base.clone(),
            encode_trust_ir_binop(
                &Opcode::Imul,
                Type::I64,
                index.clone(),
                SmtExpr::bv_const(1, 64),
            ),
        ),
        // WRONG machine: base + index*4
        aarch64_expr: encode_lea_base_index_scale(base.clone(), index.clone(), 4),
        inputs: vec![
            ("recon_base".to_string(), 64),
            ("recon_index".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "LeaSib".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "a scale=4 LEA encoder must REFUTE against a scale=1 intended address"
    );
}

// ===========================================================================
// MEMORY tier (task #76): genuine effective-address reconstruction.
//
// The deterministic `SmtExpr::mem_load(ea, load_bits, signed, result_width)`
// memory model treats the load as a deterministic function of the
// (effective-address, width, signedness) triple. So:
//   * a wrong EFFECTIVE ADDRESS (wrong base/index/scale/disp) reads a different
//     value ⇒ REFUTE;
//   * a wrong ACCESS WIDTH (8 vs 32) loads a different value ⇒ REFUTE;
//   * a wrong SIGNEDNESS (zero vs sign extend) differs for a high-bit-set load
//     ⇒ REFUTE.
// Positive cases reconstruct a REAL emitted instruction; refutation cases inject
// a wrong choice into ONE side (mirroring the LEA refutation tests).
// ===========================================================================

mod memory {
    use super::*;

    fn xmm64(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr64))
    }
    fn mem(base: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(r64(base)),
            disp,
        }
    }
    fn sib(base: u32, index: u32, scale: u8, disp: i32) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(r64(base)),
            index: Box::new(r64(index)),
            scale,
            disp,
        }
    }

    // -- (a) POSITIVE: real load/store/mem-ALU/inc-dec reconstruct Valid --------

    #[test]
    fn load_with_disp_reconstructs_valid() {
        // MOV r64, [base + 16] reconstructs Valid: source EA (Iadd) == machine EA
        // (encode_lea_base_disp), so load(ir_ea) == load(machine_ea).
        let inst = X86ISelInst::new(X86Opcode::MovRM, vec![r64(0), mem(1, 16)]);
        let ob = reconstruct_x86_alu_obligation(&inst).expect("MovRM must reconstruct");
        assert!(ob.is_reconstructed());
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "a faithful load (matching EA) must reconstruct Valid"
        );
    }

    #[test]
    fn sib_load_reconstructs_valid() {
        // MOV r64, [base + index*4 + 8] reconstructs Valid.
        let inst = X86ISelInst::new(X86Opcode::MovRM, vec![r64(0), sib(1, 2, 4, 8)]);
        let ob = reconstruct_x86_alu_obligation(&inst).expect("SIB MovRM must reconstruct");
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "a faithful SIB load must reconstruct Valid"
        );
    }

    #[test]
    fn fp_load_and_store_reconstruct_valid() {
        let load = X86ISelInst::new(X86Opcode::MovsdRM, vec![xmm64(0), mem(1, 0)]);
        let store = X86ISelInst::new(X86Opcode::MovsdMR, vec![mem(1, 0), xmm64(0)]);
        for inst in [load, store] {
            let ob = reconstruct_x86_alu_obligation(&inst).expect("FP mem must reconstruct");
            assert!(
                matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
                "{:?} must reconstruct Valid",
                inst.opcode
            );
        }
    }

    #[test]
    fn store_reconstructs_valid_and_binds_value() {
        // MOV [base+0], r64 reconstructs Valid: concat(ir_ea, value) ==
        // concat(machine_ea, value).
        let inst = X86ISelInst::new(X86Opcode::MovMR, vec![mem(0, 0), r64(1)]);
        let ob = reconstruct_x86_alu_obligation(&inst).expect("MovMR must reconstruct");
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "a faithful store must reconstruct Valid"
        );
        // The value leaf is a declared input (so a wrong value half would refute).
        assert!(
            ob.inputs.iter().any(|(n, _)| n == "recon_value"),
            "the store value must be bound as an SMT input"
        );
    }

    #[test]
    fn mem_alu_addrm_reconstructs_valid() {
        // ADD r64, [base + 0] = reg + load(ea) reconstructs Valid.
        let inst = X86ISelInst::new(X86Opcode::AddRM, vec![r64(0), mem(1, 0)]);
        let ob = reconstruct_x86_alu_obligation(&inst).expect("AddRM must reconstruct");
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "a faithful reg+load(ea) must reconstruct Valid"
        );
    }

    #[test]
    fn inc_and_dec_reconstruct_valid() {
        for (op, _) in [(X86Opcode::Inc, true), (X86Opcode::Dec, false)] {
            let inst = X86ISelInst::new(op, vec![r64(0)]);
            let ob = reconstruct_x86_alu_obligation(&inst).expect("inc/dec must reconstruct");
            assert!(
                matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
                "{op:?} must reconstruct Valid"
            );
        }
    }

    // -- (b) REFUTATION: a wrong EA / width / sign / op REFUTES -----------------

    /// A reconstructed memory obligation whose MACHINE side reads from a DIFFERENT
    /// effective address than the SOURCE side. The deterministic memory model
    /// makes the loaded value differ ⇒ Invalid.
    fn buggy_load(name: &str, ir_ea: SmtExpr, machine_ea: SmtExpr, bits: u32) -> ProofObligation {
        ProofObligation {
            name: name.to_string(),
            trust_ir_expr: SmtExpr::mem_load(ir_ea, bits, false, 64),
            aarch64_expr: SmtExpr::mem_load(machine_ea, bits, false, 64),
            inputs: vec![
                ("recon_base".to_string(), 64),
                ("recon_index".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "MovRM".to_string(),
                arity: 1,
            },
        }
    }

    #[test]
    fn wrong_scale_x4_for_x2_load_refutes() {
        // The address-mode lowering used scale=4 where scale=2 was intended:
        // load(base+index*2+0) != load(base+index*4+0) ⇒ REFUTE.
        let base = SmtExpr::var("recon_base", 64);
        let index = SmtExpr::var("recon_index", 64);
        let ir_ea = encode_lea_base_index_scale_disp(base.clone(), index.clone(), 2, 0);
        let machine_ea = encode_lea_base_index_scale_disp(base, index, 4, 0); // WRONG scale
        let buggy = buggy_load("load INJECTED wrong scale x4-for-x2", ir_ea, machine_ea, 64);
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "a scale=4 load EA must REFUTE against the intended scale=2"
        );
    }

    #[test]
    fn wrong_disp_for_load_refutes() {
        // disp +16 emitted where +8 intended: load(base+8) != load(base+16).
        let base = SmtExpr::var("recon_base", 64);
        let ir_ea = encode_lea_base_disp(base.clone(), 8, 64);
        let machine_ea = encode_lea_base_disp(base, 16, 64); // WRONG disp
        let buggy = buggy_load("load INJECTED wrong disp", ir_ea, machine_ea, 64);
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "a +16 load disp must REFUTE against the intended +8"
        );
    }

    #[test]
    fn wrong_base_index_swap_for_load_refutes() {
        // base and index swapped on a non-symmetric scale: load(base+index*4) !=
        // load(index+base*4) in general ⇒ REFUTE.
        let base = SmtExpr::var("recon_base", 64);
        let index = SmtExpr::var("recon_index", 64);
        let ir_ea = encode_lea_base_index_scale_disp(base.clone(), index.clone(), 4, 0);
        let machine_ea = encode_lea_base_index_scale_disp(index, base, 4, 0); // WRONG: swapped
        let buggy = buggy_load("load INJECTED base/index swap", ir_ea, machine_ea, 64);
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "a base/index swap on scale=4 must REFUTE"
        );
    }

    #[test]
    fn wrong_load_width_8_for_32_refutes() {
        // Same EA, but the access width is 8 where 32 was intended: the
        // deterministic memory value at the SAME address differs between an 8-bit
        // and a 32-bit read whenever the value has set bits in [8,32) ⇒ REFUTE.
        let base = SmtExpr::var("recon_base", 64);
        let buggy = ProofObligation {
            name: "load INJECTED wrong width 8-for-32".to_string(),
            trust_ir_expr: SmtExpr::mem_load(base.clone(), 32, false, 64),
            aarch64_expr: SmtExpr::mem_load(base, 8, false, 64), // WRONG width
            inputs: vec![("recon_base".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "MovRM".to_string(),
                arity: 1,
            },
        };
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "an 8-bit load must REFUTE against a 32-bit load at the same address"
        );
    }

    #[test]
    fn wrong_signedness_zero_for_sign_refutes() {
        // Same EA + width, but zero-extend where sign-extend intended: differs
        // whenever the top loaded bit is set ⇒ REFUTE. (This locks in that the
        // memory model is signedness-sensitive, the same property the AArch64
        // LDRSB-vs-LDRB distinction needs.)
        let base = SmtExpr::var("recon_base", 64);
        let buggy = ProofObligation {
            name: "load INJECTED wrong sign zero-for-sign".to_string(),
            trust_ir_expr: SmtExpr::mem_load(base.clone(), 8, true, 64), // sign-extend
            aarch64_expr: SmtExpr::mem_load(base, 8, false, 64),         // WRONG: zero-extend
            inputs: vec![("recon_base".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "MovsxB".to_string(),
                arity: 1,
            },
        };
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "a zero-extend load must REFUTE against a sign-extend load of the same byte"
        );
    }

    #[test]
    fn wrong_ea_for_store_refutes() {
        // Store: concat(ir_ea, value) vs concat(machine_ea, value) with a wrong
        // machine EA ⇒ the address half differs ⇒ REFUTE.
        let base = SmtExpr::var("recon_base", 64);
        let value = SmtExpr::var("recon_value", 64);
        let ir_ea = encode_lea_base_disp(base.clone(), 8, 64);
        let machine_ea = encode_lea_base_disp(base, 24, 64); // WRONG disp
        let buggy = ProofObligation {
            name: "store INJECTED wrong EA".to_string(),
            trust_ir_expr: ir_ea.concat(value.clone()),
            aarch64_expr: machine_ea.concat(value),
            inputs: vec![
                ("recon_base".to_string(), 64),
                ("recon_value".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "MovMR".to_string(),
                arity: 2,
            },
        };
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "a store to a wrong EA must REFUTE (address half differs)"
        );
    }

    #[test]
    fn addrm_as_subrm_refutes() {
        // Memory-ALU: AddRM lowered as SUB (reg - load(ea)) instead of ADD
        // (reg + load(ea)) ⇒ reg+m != reg-m in general ⇒ REFUTE.
        let reg = SmtExpr::var("recon_reg", 64);
        let base = SmtExpr::var("recon_base", 64);
        let m = SmtExpr::mem_load(base.clone(), 64, false, 64);
        let buggy = ProofObligation {
            name: "AddRM INJECTED as SubRM".to_string(),
            trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I64, reg.clone(), m.clone()),
            aarch64_expr: encode_sub_rr(S, reg, m), // WRONG: subtract
            inputs: vec![
                ("recon_reg".to_string(), 64),
                ("recon_base".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "AddRM".to_string(),
                arity: 2,
            },
        };
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "AddRM-as-SubRM must REFUTE (reg+m != reg-m)"
        );
    }

    #[test]
    fn cmprm_wrong_ea_refutes() {
        // CmpRM's observable is reg - load(ea); a wrong EA loads a different
        // operand so the difference differs ⇒ REFUTE.
        let reg = SmtExpr::var("recon_reg", 64);
        let base = SmtExpr::var("recon_base", 64);
        let ir_m = SmtExpr::mem_load(base.clone(), 64, false, 64);
        let machine_m = SmtExpr::mem_load(encode_lea_base_disp(base, 8, 64), 64, false, 64); // WRONG ea
        let buggy = ProofObligation {
            name: "CmpRM INJECTED wrong EA".to_string(),
            trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I64, reg.clone(), ir_m),
            aarch64_expr: encode_sub_rr(S, reg, machine_m),
            inputs: vec![
                ("recon_reg".to_string(), 64),
                ("recon_base".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "CmpRM".to_string(),
                arity: 2,
            },
        };
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "CmpRM with a wrong EA must REFUTE (different loaded operand)"
        );
    }

    #[test]
    fn inc_as_dec_refutes() {
        // In-place: Inc lowered as DEC (pre - 1) instead of INC (pre + 1) ⇒
        // pre+1 != pre-1 for every pre ⇒ REFUTE.
        let pre = SmtExpr::var("recon_pre", 64);
        let one = SmtExpr::bv_const(1, 64);
        let buggy = ProofObligation {
            name: "Inc INJECTED as Dec".to_string(),
            trust_ir_expr: encode_trust_ir_binop(
                &Opcode::Iadd,
                Type::I64,
                pre.clone(),
                one.clone(),
            ),
            aarch64_expr: encode_sub_rr(S, pre, one), // WRONG: pre - 1
            inputs: vec![("recon_pre".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "Inc".to_string(),
                arity: 1,
            },
        };
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "Inc-as-Dec must REFUTE (pre+1 != pre-1)"
        );
    }

    #[test]
    fn load_value_is_deterministic_function_of_address() {
        // Sanity: two loads at the SAME address/width/sign agree (function), and at
        // DIFFERENT addresses differ for some input (refutation soundness). This is
        // the McCarthy read-axiom property the whole tier rests on.
        use std::collections::HashMap;
        use trust_cg_verify::smt::EvalResult;
        let a = SmtExpr::var("a", 64);
        let same1 = SmtExpr::mem_load(a.clone(), 64, false, 64);
        let same2 = SmtExpr::mem_load(a.clone(), 64, false, 64);
        let other = SmtExpr::mem_load(a.clone().bvadd(SmtExpr::bv_const(8, 64)), 64, false, 64);
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0x1000u64);
        assert_eq!(
            same1.eval(&env),
            same2.eval(&env),
            "same address ⇒ same loaded value (deterministic function)"
        );
        assert_ne!(
            same1.eval(&env),
            other.eval(&env),
            "different address ⇒ different loaded value (refutation soundness)"
        );
        // And it really is a bitvector of the result width.
        assert!(matches!(same1.eval(&env), EvalResult::Bv(_)));
    }
}

// ---------------------------------------------------------------------------
// PACKED 128-bit XMM memory MOVES (MOVDQU/MOVDQA RM+MR) — SOUNDNESS PERIMETER
// ---------------------------------------------------------------------------
//
// The whole-XMM 128-bit spill/reload moves are GENUINELY RECONSTRUCTED as TWO
// 64-bit halves at effective addresses `ea` (low 64 bits) and `ea+8` (high 64
// bits), LITTLE-ENDIAN, reusing the PROVEN scalar effective-address machinery
// (SOURCE addresses via trust_ir, MACHINE addresses via the INDEPENDENT x86
// `encode_lea_*`). These tests lock in BOTH directions:
//   (a) a FAITHFUL MOVDQU/MOVDQA RM+MR reconstructs Valid, AND
//   (b) every corruption REFUTES — wrong displacement (ea vs ea+8 offset), wrong
//       half (low/high swapped), wrong width, wrong value (store), and (MOVDQA)
//       a missing/violated `ea % 16 == 0` alignment precondition.
// A false COVERED credit here is as bad as a shipped miscompile, so the
// refutations are MANDATORY: if any fails to fire, the coverage flip is unsound.
mod packed_128bit_moves {
    use super::*;

    fn xmm128(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr128))
    }
    fn mem(base: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(r64(base)),
            disp,
        }
    }
    fn sib(base: u32, index: u32, scale: u8, disp: i32) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(r64(base)),
            index: Box::new(r64(index)),
            scale,
            disp,
        }
    }
    // The `recon_base` leaf and its ea / ea+8 addresses (both encoders agree for
    // the FAITHFUL case; the refutations perturb the machine side).
    fn base() -> SmtExpr {
        SmtExpr::var("recon_base", 64)
    }
    fn eight() -> SmtExpr {
        SmtExpr::bv_const(8, 64)
    }
    fn load64(addr: SmtExpr) -> SmtExpr {
        SmtExpr::mem_load(addr, 64, false, 64)
    }
    fn is_invalid(ob: &ProofObligation) -> bool {
        matches!(verify_by_evaluation(ob), VerificationResult::Invalid { .. })
    }
    fn is_valid(ob: &ProofObligation) -> bool {
        matches!(verify_by_evaluation(ob), VerificationResult::Valid)
    }
    fn recon_prov(from: &str, arity: u8) -> MachineSideProvenance {
        MachineSideProvenance::Reconstructed {
            from_opcode: from.to_string(),
            arity,
        }
    }

    // -- (a) POSITIVE: faithful RM + MR each reconstruct Valid -------------------

    #[test]
    fn movdqu_movdqa_rm_mr_reconstruct_valid() {
        // Load (RM) = [xmm128, MemAddr]; store (MR) = [MemAddr, xmm128]. Aligned
        // (MOVDQA) and unaligned (MOVDQU) each reconstruct Valid; the independent
        // SOURCE (trust_ir) vs MACHINE (encode_lea) EAs agree at both halves.
        for (opcode, kind) in [
            (X86Opcode::MovdquRM, "load"),
            (X86Opcode::MovdqaRM, "load"),
            (X86Opcode::MovdquMR, "store"),
            (X86Opcode::MovdqaMR, "store"),
        ] {
            let inst = if kind == "load" {
                X86ISelInst::new(opcode, vec![xmm128(0), mem(1, 0)])
            } else {
                X86ISelInst::new(opcode, vec![mem(0, 0), xmm128(1)])
            };
            let ob = reconstruct_x86_alu_obligation(&inst)
                .unwrap_or_else(|| panic!("{opcode:?} must reconstruct"));
            assert!(
                ob.is_reconstructed(),
                "{opcode:?} obligation must carry Reconstructed provenance"
            );
            assert!(
                is_valid(&ob),
                "a faithful {opcode:?} (matching two-half EAs) must reconstruct Valid"
            );
        }
    }

    #[test]
    fn movdqu_sib_and_nonzero_disp_reconstruct_valid() {
        // SIB base+index*scale+disp and a non-zero displacement both reconstruct
        // Valid (the two-half EA machinery threads the whole addressing mode).
        for inst in [
            X86ISelInst::new(X86Opcode::MovdquRM, vec![xmm128(0), sib(1, 2, 4, 16)]),
            X86ISelInst::new(X86Opcode::MovdquMR, vec![mem(0, 32), xmm128(1)]),
        ] {
            let ob = reconstruct_x86_alu_obligation(&inst).expect("must reconstruct");
            assert!(is_valid(&ob), "{:?} must reconstruct Valid", inst.opcode);
        }
    }

    #[test]
    fn post_regalloc_xmm_preg_stackslot_spill_shape_reconstructs_valid() {
        // COMPLETENESS: the ACTUAL spill/reload shape the codegen pipeline emits for
        // a whole-Fpr128 value is `MovdquRM xmm_preg, [StackSlot]` (reload) and
        // `MovdquMR [StackSlot], xmm_preg` (spill) — a POST-REGALLOC XMM physical
        // register + a StackSlot-based address. This is exactly what previously
        // fail-closed (x86_opcode_to_source_op returned None). It must now
        // reconstruct Valid so a spilling Fpr128 program is no longer rejected.
        use trust_cg_ir::x86_64_regs::XMM0;
        let xmm_preg = X86ISelOperand::PReg(XMM0);
        let slot = X86ISelOperand::MemAddr {
            base: Box::new(X86ISelOperand::StackSlot(0)),
            disp: 0,
        };
        let reload = X86ISelInst::new(X86Opcode::MovdquRM, vec![xmm_preg.clone(), slot.clone()]);
        let spill = X86ISelInst::new(X86Opcode::MovdquMR, vec![slot, xmm_preg]);
        for inst in [reload, spill] {
            let ob = reconstruct_x86_alu_obligation(&inst)
                .unwrap_or_else(|| panic!("{:?} spill/reload shape must reconstruct", inst.opcode));
            assert!(
                is_valid(&ob),
                "the real Fpr128 spill/reload shape {:?} (XMM PReg + StackSlot) must reconstruct Valid",
                inst.opcode
            );
        }
    }

    #[test]
    fn movdqa_store_binds_both_value_halves_as_inputs() {
        // The store binds BOTH 64-bit value halves as SMT inputs (so a wrong/dropped
        // half refutes) — three inputs total (base + two value halves) routes it to
        // the per-input-width multi-sampler.
        let inst = X86ISelInst::new(X86Opcode::MovdqaMR, vec![mem(0, 0), xmm128(1)]);
        let ob = reconstruct_x86_alu_obligation(&inst).expect("must reconstruct");
        assert!(
            ob.inputs
                .iter()
                .any(|(n, w)| n == "recon_value_lo" && *w == 64)
        );
        assert!(
            ob.inputs
                .iter()
                .any(|(n, w)| n == "recon_value_hi" && *w == 64)
        );
        assert!(
            !ob.preconditions.is_empty(),
            "MOVDQA store must carry the ea%16==0 alignment precondition"
        );
    }

    // The faithful two-half LOAD obligation as production builds it, over the
    // shared `recon_base` leaf: concat(load(ea+8), load(ea)).
    fn faithful_load_sides() -> (SmtExpr, SmtExpr) {
        let src = load64(base().bvadd(eight())).concat(load64(base()));
        let mac = load64(base().bvadd(eight())).concat(load64(base()));
        (src, mac)
    }
    fn load_ob(name: &str, machine: SmtExpr, preconditions: Vec<SmtExpr>) -> ProofObligation {
        let (src, _) = faithful_load_sides();
        ProofObligation {
            name: name.to_string(),
            trust_ir_expr: src,
            aarch64_expr: machine,
            inputs: vec![("recon_base".to_string(), 64)],
            preconditions,
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: recon_prov("MovdquRM", 1),
        }
    }

    // -- (b) REFUTATION: LOAD corruptions ---------------------------------------

    #[test]
    fn load_wrong_high_half_offset_refutes() {
        // High half read at ea+16 where ea+8 is intended: load(ea+16) != load(ea+8)
        // ⇒ REFUTE (a wrong displacement of the second half).
        let machine = load64(base().bvadd(SmtExpr::bv_const(16, 64))).concat(load64(base()));
        let ob = load_ob("V128 load INJECTED high half at ea+16", machine, vec![]);
        assert!(
            is_invalid(&ob),
            "high-half offset ea+16 must REFUTE vs ea+8"
        );
    }

    #[test]
    fn load_swapped_halves_refutes() {
        // Low/high halves swapped: machine = concat(load(ea), load(ea+8)) reads the
        // low bytes from ea+8 and the high bytes from ea ⇒ REFUTE.
        let machine = load64(base()).concat(load64(base().bvadd(eight())));
        let ob = load_ob("V128 load INJECTED swapped halves", machine, vec![]);
        assert!(is_invalid(&ob), "swapped low/high halves must REFUTE");
    }

    #[test]
    fn load_wrong_ea_refutes() {
        // The address-mode lowering added a spurious +8 to the base of BOTH halves
        // (a wrong EA): load(base+8) / load(base+16) != load(base) / load(base+8).
        let wrong_base = encode_lea_base_disp(base(), 8, 64);
        let machine = load64(wrong_base.clone().bvadd(eight())).concat(load64(wrong_base));
        let ob = load_ob("V128 load INJECTED wrong EA (+8 base)", machine, vec![]);
        assert!(is_invalid(&ob), "a wrong base EA must REFUTE");
    }

    #[test]
    fn load_wrong_low_half_width_refutes() {
        // Low half accessed at 32-bit width where 64 is intended: the deterministic
        // memory value differs whenever the loaded value has set bits in [32,64).
        let machine =
            load64(base().bvadd(eight())).concat(SmtExpr::mem_load(base(), 32, false, 64));
        let ob = load_ob("V128 load INJECTED 32-bit low half", machine, vec![]);
        assert!(is_invalid(&ob), "a 32-bit low half must REFUTE vs 64-bit");
    }

    // -- (b) REFUTATION: STORE corruptions --------------------------------------

    // Faithful store SOURCE, over recon_base + two value halves: per-slot observable
    // = value_half + load(slot_ea), concatenated (hi in the upper 64 bits).
    fn vlo() -> SmtExpr {
        SmtExpr::var("recon_value_lo", 64)
    }
    fn vhi() -> SmtExpr {
        SmtExpr::var("recon_value_hi", 64)
    }
    fn store_source() -> SmtExpr {
        let hi = vhi().bvadd(load64(base().bvadd(eight())));
        let lo = vlo().bvadd(load64(base()));
        hi.concat(lo)
    }
    fn store_ob(name: &str, machine: SmtExpr, preconditions: Vec<SmtExpr>) -> ProofObligation {
        ProofObligation {
            name: name.to_string(),
            trust_ir_expr: store_source(),
            aarch64_expr: machine,
            inputs: vec![
                ("recon_base".to_string(), 64),
                ("recon_value_lo".to_string(), 64),
                ("recon_value_hi".to_string(), 64),
            ],
            preconditions,
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: recon_prov("MovdquMR", 2),
        }
    }

    #[test]
    fn store_swapped_value_halves_refutes() {
        // Machine writes hi_val to the LOW slot and lo_val to the HIGH slot ⇒ the
        // (value, address) pairing is wrong ⇒ REFUTE (halves are independent).
        let hi = vlo().bvadd(load64(base().bvadd(eight())));
        let lo = vhi().bvadd(load64(base()));
        let ob = store_ob(
            "V128 store INJECTED swapped value halves",
            hi.concat(lo),
            vec![],
        );
        assert!(is_invalid(&ob), "swapped store value halves must REFUTE");
    }

    #[test]
    fn store_wrong_ea_refutes() {
        // Both slots addressed from a wrong base (+8): the folded address hash
        // differs at each slot ⇒ REFUTE.
        let wrong = encode_lea_base_disp(base(), 8, 64);
        let hi = vhi().bvadd(load64(wrong.clone().bvadd(eight())));
        let lo = vlo().bvadd(load64(wrong));
        let ob = store_ob("V128 store INJECTED wrong EA", hi.concat(lo), vec![]);
        assert!(is_invalid(&ob), "a wrong store EA must REFUTE");
    }

    #[test]
    fn store_dropped_high_half_refutes() {
        // Machine drops the high value half (writes only the address hash, value
        // half = 0) — a truncated 64-bit store where 128 is intended ⇒ REFUTE.
        let hi = load64(base().bvadd(eight())); // WRONG: no hi_val term
        let lo = vlo().bvadd(load64(base()));
        let ob = store_ob(
            "V128 store INJECTED dropped high half",
            hi.concat(lo),
            vec![],
        );
        assert!(is_invalid(&ob), "a dropped high value half must REFUTE");
    }

    // -- (b) REFUTATION: MOVDQA alignment precondition is LOAD-BEARING -----------
    //
    // An aligned-assuming lowering computes the two-half addresses relative to the
    // 16-byte-aligned BLOCK BASE `ea & !15` — correct ONLY when `ea % 16 == 0`. The
    // pair below proves the `ea % 16 == 0` precondition is genuinely load-bearing:
    // WITH it the block-relative machine reconstructs Valid; WITHOUT it (missing /
    // violated) it REFUTES on an unaligned address. So a bad (unaligned) access can
    // NEVER be silently credited — dropping the alignment guard fails closed.
    fn block_base() -> SmtExpr {
        // ea & !15 — the 16-byte-aligned block base.
        base().bvand(SmtExpr::bv_const(!15u64, 64))
    }
    fn aligned_precondition() -> Vec<SmtExpr> {
        vec![
            base()
                .bvand(SmtExpr::bv_const(15, 64))
                .eq_expr(SmtExpr::bv_const(0, 64)),
        ]
    }
    fn block_relative_machine_load() -> SmtExpr {
        // Both halves addressed off the block base: low at (ea&!15), high at
        // (ea&!15)+8. Equals the faithful ea / ea+8 addressing IFF ea is aligned.
        load64(block_base().bvadd(eight())).concat(load64(block_base()))
    }

    #[test]
    fn movdqa_load_with_alignment_precondition_valid() {
        // WITH the ea%16==0 precondition the block-relative (aligned-assuming) load
        // reconstructs Valid — the precondition licenses `ea & !15 == ea`.
        let ob = load_ob(
            "V128 MOVDQA load block-relative WITH ea%16==0",
            block_relative_machine_load(),
            aligned_precondition(),
        );
        assert!(
            is_valid(&ob),
            "the aligned (block-relative) load must be Valid UNDER ea%16==0"
        );
    }

    #[test]
    fn movdqa_load_missing_alignment_precondition_refutes() {
        // WITHOUT the precondition the SAME block-relative load REFUTES: on an
        // unaligned ea, `ea & !15 != ea`, so the halves read different bytes. A
        // missing/violated alignment precondition ⇒ REFUTE (fail closed).
        let ob = load_ob(
            "V128 MOVDQA load block-relative MISSING ea%16==0",
            block_relative_machine_load(),
            vec![],
        );
        assert!(
            is_invalid(&ob),
            "dropping the ea%16==0 precondition must REFUTE (unaligned access not credited)"
        );
    }

    #[test]
    fn movdqa_representative_carries_alignment_precondition_movdqu_does_not() {
        // The production reconstruction attaches ea%16==0 to MOVDQA and NOTHING to
        // MOVDQU — the honest aligned/unaligned distinction.
        let dqa = reconstruct_x86_alu_obligation(&X86ISelInst::new(
            X86Opcode::MovdqaRM,
            vec![xmm128(0), mem(1, 0)],
        ))
        .unwrap();
        let dqu = reconstruct_x86_alu_obligation(&X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![xmm128(0), mem(1, 0)],
        ))
        .unwrap();
        assert!(
            !dqa.preconditions.is_empty(),
            "MOVDQA must carry the ea%16==0 alignment precondition"
        );
        assert!(
            dqu.preconditions.is_empty(),
            "MOVDQU (unaligned) must carry NO alignment precondition"
        );
    }
}

#[test]
fn injected_neg_for_intended_bnot_refutes() {
    // UNARY family: isel emitted NEG (0 - a) where Bnot (~a) was intended.
    // -a != ~a in general (they differ by 1: ~a == -a - 1).
    let sym = SmtExpr::var("recon_src", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 Bnot -> Neg (INJECTED isel bug)".to_string(),
        trust_ir_expr: encode_trust_ir_bnot(Type::I64, sym.clone()),
        aarch64_expr: encode_neg(S, sym.clone()), // WRONG: bvneg
        inputs: vec![("recon_src".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Neg".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "NEG-for-Bnot must REFUTE (-a != ~a)"
    );
}

// ---------------------------------------------------------------------------
// (c) Wrong-wiring refute for NON-commutative ops (Sub, shifts)
// ---------------------------------------------------------------------------

#[test]
fn injected_swapped_operands_on_sub_refutes() {
    // SUB is non-commutative: a - b != b - a in general.
    let a = SmtExpr::var("recon_src1", 64);
    let b = SmtExpr::var("recon_src2", 64);
    let buggy = buggy_binary(
        "RECONSTRUCTED x86_64 Isub -> SubRR (INJECTED swapped wiring)",
        "SubRR",
        encode_trust_ir_binop(&Opcode::Isub, Type::I64, a.clone(), b.clone()), // a - b
        encode_sub_rr(S, b, a),                                                // WRONG: b - a
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped SUB wiring must REFUTE (a - b != b - a)"
    );
}

#[test]
fn injected_swapped_operands_on_shift_refutes() {
    // A shift is non-commutative in its operands: value << count != count << value
    // in general. Wrong wiring ⇒ REFUTE (in range).
    let a = SmtExpr::var("recon_src1", 8);
    let amt = SmtExpr::var("recon_src2", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 Ishl -> ShlRR (INJECTED swapped wiring)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        // WRONG wiring: count as the value, value as the count.
        aarch64_expr: encode_shl_rr_masked(S, amt.clone(), a.clone()),
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: vec![
            amt.clone().bvult(SmtExpr::bv_const(8, 8)),
            a.clone().bvult(SmtExpr::bv_const(8, 8)),
        ],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "ShlRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped shift wiring must REFUTE (value<<count != count<<value)"
    );
}

// ---------------------------------------------------------------------------
// Commutative families cannot catch an operand swap — DOCUMENTED limitation
// ---------------------------------------------------------------------------

#[test]
fn commutative_families_cannot_catch_operand_swap_by_design() {
    // DOCUMENTED LIMITATION: Add/Imul/And/Or/Xor are commutative, so a swapped-
    // operand lowering still proves Valid — exactly like the AArch64/RISC-V
    // commutative ADD. The non-commutative Sub/shifts (above) are the wiring
    // discriminators. Stated explicitly so nobody reads the passing swap as a
    // soundness hole.
    let a = SmtExpr::var("recon_src1", 64);
    let b = SmtExpr::var("recon_src2", 64);

    // Add (swapped): a + b == b + a.
    let add_swapped = buggy_binary(
        "RECONSTRUCTED x86_64 Iadd -> AddRR (swapped, still valid: commutative)",
        "AddRR",
        encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), b.clone()),
        encode_add_rr(S, b.clone(), a.clone()),
    );
    assert!(matches!(
        verify_by_evaluation(&add_swapped),
        VerificationResult::Valid
    ));

    // And (swapped): a & b == b & a.
    let and_swapped = buggy_binary(
        "RECONSTRUCTED x86_64 Band -> AndRR (swapped, still valid: commutative)",
        "AndRR",
        encode_trust_ir_bitwise_binop(&Opcode::Band, Type::I64, a.clone(), b.clone()),
        encode_and_rr(S, b, a),
    );
    assert!(matches!(
        verify_by_evaluation(&and_swapped),
        VerificationResult::Valid
    ));
}

// ---------------------------------------------------------------------------
// (e) The shift count<width precondition is LOAD-BEARING (#57)
// ---------------------------------------------------------------------------

#[test]
fn shift_precondition_is_load_bearing_strip_it_and_it_refutes() {
    // #57: the count<width precondition is GENUINELY load-bearing, not cosmetic.
    // At width 8 (exhaustive), WITH the precondition the in-range equivalence is
    // Valid; WITHOUT it, a shift by exactly width (8 & 7 == 0 on the hardware mask
    // vs clamp-to-0 in the in-house SMT bvshl) is a counterexample ⇒ stripping it
    // REFUTES. The machine side is the FAITHFUL hardware-count-masked encoder.
    let a = SmtExpr::var("recon_src1", 8);
    let amt = SmtExpr::var("recon_src2", 8);
    let mk = |pre: Vec<SmtExpr>| ProofObligation {
        name: "x86 shift8 load-bearing demo".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_shl_rr_masked(S, a.clone(), amt.clone()),
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: pre,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "ShlRR".to_string(),
            arity: 2,
        },
    };
    let with_pre = mk(vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))]);
    let without_pre = mk(vec![]);
    assert!(
        matches!(verify_by_evaluation(&with_pre), VerificationResult::Valid),
        "WITH count<width precondition: in-range equivalence is Valid"
    );
    assert!(
        matches!(
            verify_by_evaluation(&without_pre),
            VerificationResult::Invalid { .. }
        ),
        "WITHOUT the precondition the shift-by-width case REFUTES — load-bearing (#57)"
    );
}

// ---------------------------------------------------------------------------
// (d) Anti-f81e45b: the reconstructed path does NO name.contains lookup
// ---------------------------------------------------------------------------

#[test]
fn reconstructed_path_does_no_name_contains_lookup() {
    // The source span of the x86 reconstruction module must not perform a
    // `name.contains` lookup to bind the source op or the machine encoder — the
    // binding is a TYPED, EXHAUSTIVE opcode match (`x86_opcode_to_source_op`) plus
    // a TYPED positional operand schema. Asserted structurally over the source span.
    let src = include_str!("../src/x86_64_function_verifier.rs");

    let start = src
        .find("// Phase-2 operand reconstruction (x86-64 ALU)")
        .expect("reconstruction section header present");
    let end_marker = "// X86FunctionVerifier";
    let end = src[start..]
        .find(end_marker)
        .map(|o| start + o)
        .expect("X86FunctionVerifier section header follows reconstruction");
    let recon_src = &src[start..end];

    assert!(
        !recon_src.contains(".contains("),
        "the x86 reconstruction path must NOT use any .contains() name lookup \
         (anti-f81e45b): the opcode->source-op binding is a typed exhaustive match"
    );
    assert!(
        recon_src.contains("fn x86_opcode_to_source_op("),
        "reconstruction must resolve the source op via the typed matcher"
    );
}

// ---------------------------------------------------------------------------
// Fail-closed: non-reconstructable opcodes and malformed shapes
// ---------------------------------------------------------------------------

#[test]
fn non_reconstructable_opcode_does_not_reconstruct() {
    // STRUCTURAL FAIL-CLOSED test (NOT a "these are deferred" test).
    //
    // Idiv/Div AND Cmovcc/Cmovcc32 ARE NOW RECONSTRUCTED — they are in
    // `all_reconstructable()` (the #76 implicit-operand tier) and their CORRECTLY-
    // SHAPED instances reconstruct + discharge Valid, as proven by the
    // `division_*` / `cond_move_*` / `x86_fp_and_bitmanip_*` tests below. What
    // this test feeds is a MALFORMED operand shape, so the typed builders fail
    // closed for the correct STRUCTURAL reason (wrong arity / wrong operand kind),
    // returning None rather than silently crediting a misshapen instruction:
    //   * Idiv/Div take exactly ONE explicit operand (the divisor; the dividend is
    //     the implicit RDX:RAX pair). Feeding 3 operands is the WRONG ARITY ⇒ None.
    //   * Cmovcc/Cmovcc32 are the Binary CMP+CMOV select shape; the 3-operand shape
    //     fed here does not match the typed schema ⇒ None.
    //   * MovRI genuinely has no per-instruction model (const==const, no
    //     independent constant model), so it never reconstructs.
    // The point: a misshapen instruction NEVER reconstructs (fail-closed); only a
    // correctly-shaped one does (the dedicated division/cond-move tests prove that).
    for op in [
        X86Opcode::Idiv,
        X86Opcode::Div,
        X86Opcode::MovRI,
        X86Opcode::Cmovcc,
        X86Opcode::Cmovcc32,
    ] {
        let inst = X86ISelInst::new(op, vec![r64(0), r64(1), r64(2)]);
        assert!(
            reconstruct_x86_alu_obligation(&inst).is_none(),
            "{op:?} with a MALFORMED operand shape must fail closed (None) — only its \
             correctly-shaped instance reconstructs (see the division_*/cond_move_* tests)"
        );
    }
}

#[test]
fn malformed_operand_shape_fails_closed() {
    // A reconstructable opcode whose operand shape does not match the typed schema
    // does NOT reconstruct — returns None so the caller can fall through; never
    // silently credited as reconstructed.

    // Structural 2-address AddRI (RSP += imm stack cleanup): the dst is RSP (a GPR)
    // and there are only 2 operands — wrong arity for the 3-operand dataflow form.
    let two = X86ISelInst::new(X86Opcode::AddRR, vec![r64(0), r64(1)]);
    assert!(reconstruct_x86_alu_obligation(&two).is_none());

    // A binary op with a non-register src1 (e.g. an immediate) fails closed.
    let bad_src1 = X86ISelInst::new(
        X86Opcode::AddRR,
        vec![r64(0), X86ISelOperand::Imm(1), r64(2)],
    );
    assert!(reconstruct_x86_alu_obligation(&bad_src1).is_none());

    // A Neg stub with only the dst fails closed (unary needs [dst, src]).
    let neg_stub = X86ISelInst::new(X86Opcode::Neg, vec![r64(0)]);
    assert!(reconstruct_x86_alu_obligation(&neg_stub).is_none());
}

// ===========================================================================
// (h) Scalar FP + bit-manip reconstruction (task: x86 FP-scalar + bit-manip).
// ===========================================================================

/// Every FP-scalar + bit-manip target opcode reconstructs, is Reconstructed, and
/// discharges Valid via its representative instance.
#[test]
fn x86_fp_and_bitmanip_opcodes_reconstruct_valid() {
    let cases = [
        // FP binary (SD + SS).
        X86Opcode::Addsd,
        X86Opcode::Subsd,
        X86Opcode::Mulsd,
        X86Opcode::Divsd,
        X86Opcode::Addss,
        X86Opcode::Subss,
        X86Opcode::Mulss,
        X86Opcode::Divss,
        // FP unary sqrt.
        X86Opcode::Sqrtsd,
        X86Opcode::Sqrtss,
        // FP hardware min/max.
        X86Opcode::Minsd,
        X86Opcode::Maxsd,
        X86Opcode::Minss,
        X86Opcode::Maxss,
        // FP compare-to-mask (UNORD).
        X86Opcode::Cmpsd,
        X86Opcode::Cmpss,
        // FP<->FP casts.
        X86Opcode::Cvtsd2ss,
        X86Opcode::Cvtss2sd,
        // FP->int: BOTH the TRUNCATING (RTZ) CVTT* and the ROUND-TO-NEAREST-EVEN
        // (RNE) CVT*2SI forms (the evaluator now faithfully models the rounding
        // mode of fp.to_sbv; see smt.rs FPToSBv try_eval), and int->FP.
        X86Opcode::Cvttsd2si,
        X86Opcode::Cvttss2si,
        X86Opcode::Cvtsd2si,
        X86Opcode::Cvtss2si,
        X86Opcode::Cvtsi2sd,
        X86Opcode::Cvtsi2ss,
        // Bit-manip.
        X86Opcode::Popcnt,
        X86Opcode::Tzcnt,
        X86Opcode::Lzcnt,
        X86Opcode::Bsf,
        X86Opcode::Bsr,
    ];
    for op in cases {
        let inst = representative_x86_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must have a representative"));
        let ob = reconstruct_x86_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(ob.is_reconstructed(), "{op:?} must be Reconstructed");
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{op:?} correct lowering must be Valid"
        );
    }
}

#[test]
fn injected_subsd_for_intended_addsd_refutes() {
    // FP binary: isel emitted SUBSD where Fadd was intended ⇒ a+b != a-b.
    let buggy = buggy_fp_binary(
        "RECONSTRUCTED x86_64 Fadd -> Subsd (INJECTED isel bug)",
        encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F64, fp_a(), fp_b()),
        encode_fp_sub_rr(X86FPSize::Double, fp_a(), fp_b()), // WRONG opcode
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "SUBSD-for-Fadd must REFUTE"
    );
}

#[test]
fn injected_subsd_swapped_wiring_refutes() {
    // FP NON-COMMUTATIVE wiring: source Fsub(a,b); machine wired SUBSD(b,a).
    let buggy = buggy_fp_binary(
        "RECONSTRUCTED x86_64 Fsub swapped wiring (INJECTED)",
        encode_trust_ir_fp_binop(&Opcode::Fsub, Type::F64, fp_a(), fp_b()),
        encode_fp_sub_rr(X86FPSize::Double, fp_b(), fp_a()), // SWAPPED operands
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "SUBSD with swapped sources must REFUTE (wiring-preserving FP evaluator)"
    );
}

#[test]
fn minsd_swapped_wiring_refutes() {
    // FP hardware MIN is NON-commutative (the SECOND operand wins on unordered/
    // equal, and signed-zero ordering): source = encode_trust_ir_fminsd_hw(a, b);
    // machine wired MINSD(b, a). The wiring-preserving FP evaluator substitutes
    // recon_a/recon_b THROUGH the ITE/fp_lt/fp_ge nodes, so the swap genuinely
    // diverges ⇒ REFUTE. (This also proves the min/max obligation is NOT vacuous:
    // the leaves nested inside the conditional ARE substituted and evaluated.)
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_fminsd_hw;
    use trust_cg_verify::x86_64_semantics::encode_fp_minsd;
    let buggy = buggy_fp_binary(
        "RECONSTRUCTED x86_64 Fmin swapped wiring (INJECTED)",
        encode_trust_ir_fminsd_hw(Type::F64, fp_a(), fp_b()),
        encode_fp_minsd(fp_b(), fp_a()), // SWAPPED operands
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "MINSD with swapped sources must REFUTE (non-commutative on NaN/eq/signed-zero)"
    );
}

#[test]
fn injected_divsd_swapped_wiring_refutes() {
    use trust_cg_verify::x86_64_semantics::encode_fp_div_rr;
    let buggy = buggy_fp_binary(
        "RECONSTRUCTED x86_64 Fdiv swapped wiring (INJECTED)",
        encode_trust_ir_fp_binop(&Opcode::Fdiv, Type::F64, fp_a(), fp_b()),
        encode_fp_div_rr(X86FPSize::Double, fp_b(), fp_a()), // SWAPPED operands
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "DIVSD with swapped sources must REFUTE"
    );
}

#[test]
fn cmpsd_unord_mask_is_non_vacuous() {
    // The UNORD compare-to-mask obligation must be GENUINELY checkable: a WRONG
    // machine side (here a constant all-ZERO mask that ignores NaN) must REFUTE for
    // a NaN input. This proves the recon_a/recon_b leaves inside the isNaN/OR/ITE
    // structure ARE substituted and evaluated (not vacuously skipped).
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_cmp_unord_mask;
    let wrong_zero = SmtExpr::bv_const(0, 64); // never reports unordered — WRONG
    let ob = ProofObligation {
        name: "RECONSTRUCTED x86_64 CmpUnord -> constant-0 mask (INJECTED)".to_string(),
        trust_ir_expr: encode_trust_ir_cmp_unord_mask(64, fp_a(), fp_b()),
        aarch64_expr: wrong_zero,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![
            ("recon_a".to_string(), 11, 53),
            ("recon_b".to_string(), 11, 53),
        ],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "buggy".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Invalid { .. }
        ),
        "a constant-0 mask must REFUTE the UNORD compare (NaN input → all-ones expected)"
    );
}

#[test]
fn addsd_and_mulsd_swap_do_not_refute_commutative() {
    // DOCUMENTED commutative no-refute: a swapped ADDSD/MULSD is still a CORRECT
    // ADDSD/MULSD (a+b == b+a, a*b == b*a) ⇒ Valid, NOT a refutation. The wiring
    // bug-catching power covers only the NON-commutative SUBSD/DIVSD (above).
    let add_swapped = buggy_fp_binary(
        "RECONSTRUCTED x86_64 Fadd swapped (commutative, still valid)",
        encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F64, fp_a(), fp_b()),
        encode_fp_add_rr(X86FPSize::Double, fp_b(), fp_a()),
    );
    assert!(matches!(
        verify_by_evaluation(&add_swapped),
        VerificationResult::Valid
    ));
    let mul_swapped = buggy_fp_binary(
        "RECONSTRUCTED x86_64 Fmul swapped (commutative, still valid)",
        encode_trust_ir_fp_binop(&Opcode::Fmul, Type::F64, fp_a(), fp_b()),
        trust_cg_verify::x86_64_semantics::encode_fp_mul_rr(X86FPSize::Double, fp_b(), fp_a()),
    );
    assert!(matches!(
        verify_by_evaluation(&mul_swapped),
        VerificationResult::Valid
    ));
}

#[test]
fn injected_cvttsd2si_for_intended_fadd_refutes() {
    // FP->int wrong opcode: the TRUNCATING CVTTSD2SI is the genuine reconstructed
    // lowering of trust_ir FcvtToInt. A wrong machine op of a DIFFERENT KIND (here
    // an FP add producing an FP result instead of the int truncation) yields a
    // structurally distinct side ⇒ REFUTE. (The RNE-vs-RTZ rounding-mode and the
    // x86 integer-indefinite OOR mode are both now faithfully modeled — see the
    // x86 ISA references in trust_ir_semantics — so the conversions reconstruct.)
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_fcvt_to_sint_x86;
    let ob = ProofObligation {
        name: "RECONSTRUCTED x86_64 FcvtToInt -> Addsd (INJECTED wrong-kind)".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint_x86(64, fp_a()),
        aarch64_expr: encode_fp_add_rr(X86FPSize::Double, fp_a(), fp_a()), // WRONG kind
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 11, 53)],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Addsd".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Invalid { .. }
        ),
        "an FP-add machine side for an intended int truncation must REFUTE"
    );
}

#[test]
fn injected_tzcnt_for_intended_popcnt_refutes() {
    // BIT-MANIP: source intends Ctpop (population count); machine emitted TZCNT
    // (count-trailing-zeros). popcount(x) != ctz(x) for almost every x ⇒ REFUTE.
    let a = SmtExpr::var("recon_src", 64);
    let ob = ProofObligation {
        name: "RECONSTRUCTED x86_64 Ctpop -> Tzcnt (INJECTED)".to_string(),
        trust_ir_expr: encode_trust_ir_ctpop(a.clone()),
        aarch64_expr: encode_tzcnt(a.clone()), // WRONG bit-count op
        inputs: vec![("recon_src".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Tzcnt".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Invalid { .. }
        ),
        "TZCNT-for-Popcnt must REFUTE (popcount != trailing-zero-count)"
    );
}

#[test]
fn injected_popcnt_for_intended_tzcnt_refutes() {
    // Mirror: source intends Cttz; machine emitted POPCNT ⇒ REFUTE.
    let a = SmtExpr::var("recon_src", 64);
    let ob = ProofObligation {
        name: "RECONSTRUCTED x86_64 Cttz -> Popcnt (INJECTED)".to_string(),
        trust_ir_expr: encode_trust_ir_cttz(a.clone()),
        aarch64_expr: encode_popcnt(a.clone()), // WRONG bit-count op
        inputs: vec![("recon_src".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Popcnt".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Invalid { .. }
        ),
        "POPCNT-for-Tzcnt must REFUTE"
    );
}

#[test]
fn bsf_carries_load_bearing_nonzero_precondition() {
    // BSF reconstructs with a `src != 0` precondition (BSF(0) is architecturally
    // undefined). The reconstructed obligation discharges Valid; this asserts the
    // precondition is present (load-bearing — without it the zero input, where the
    // hardware result is undefined, would have to be reasoned over).
    let inst = representative_x86_reconstructable_inst(X86Opcode::Bsf).expect("Bsf representative");
    let ob = reconstruct_x86_alu_obligation(&inst).expect("Bsf reconstructs");
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
    assert!(
        !ob.preconditions.is_empty(),
        "BSF must carry a load-bearing src != 0 precondition"
    );
}

#[test]
fn cvtsd2ss_wrong_direction_refutes() {
    // FP<->FP cast wrong direction: source intends a DEMOTE to binary32 (Cvtsd2ss),
    // machine emitted the WIDEN Cvtss2sd (keeps binary64). With an f64 leaf that
    // does not round-trip through binary32 they DIVERGE ⇒ REFUTE.
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_fp_format_convert;
    use trust_cg_verify::x86_64_semantics::encode_cvtss2sd;
    let a = SmtExpr::var("recon_a", 64);
    let ob = ProofObligation {
        name: "RECONSTRUCTED x86_64 demote -> Cvtss2sd (INJECTED wrong direction)".to_string(),
        // Source: narrow to binary32 (the intended Cvtsd2ss demote).
        trust_ir_expr: encode_trust_ir_fp_format_convert(8, 24, a.clone()),
        // Machine: the WRONG widen encoder (keeps binary64 precision).
        aarch64_expr: encode_cvtss2sd(a.clone()),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 11, 53)],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Cvtss2sd".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Invalid { .. }
        ),
        "demote-as-Cvtss2sd (wrong direction) must REFUTE"
    );
}

#[test]
fn cvtsd2si_rne_reconstructs_valid_and_rtz_for_rne_refutes() {
    // FAITHFUL FP->signed-int with rounding mode AND x86 integer-indefinite OOR
    // (#99: the x86 CVT*2SI ISA reference is integer-indefinite, not saturating).
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_fcvt_to_sint_x86_rne;
    use trust_cg_verify::x86_64_semantics::encode_cvttsd2si;

    // POSITIVE: CVTSD2SI (RNE) reconstructs and the correct lowering discharges
    // Valid — source x86 fp.to_sbv(RNE, IntegerIndefinite) == machine encoder.
    let inst = representative_x86_reconstructable_inst(X86Opcode::Cvtsd2si)
        .expect("Cvtsd2si representative");
    let ob = reconstruct_x86_alu_obligation(&inst).expect("Cvtsd2si reconstructs");
    assert!(ob.is_reconstructed(), "Cvtsd2si must be Reconstructed");
    assert!(
        matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
        "CVTSD2SI (RNE) correct lowering must be Valid"
    );

    // REFUTATION: an RNE source mis-lowered to a TRUNCATING (RTZ) machine encoder
    // must REFUTE. With the rounding mode faithfully modeled, a non-integral tie
    // input (1.5 -> RNE 2, RTZ 1) makes the two sides DIVERGE. (Both sides share
    // the x86 integer-indefinite OOR mode, so the ROUNDING bug is isolated.)
    let a = SmtExpr::var("recon_a", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 FcvtRneToSint -> RTZ machine (INJECTED wrong rounding)"
            .to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint_x86_rne(64, a.clone()), // RNE intended
        aarch64_expr: encode_cvttsd2si(64, a.clone()),                      // RTZ machine (WRONG)
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 11, 53)],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Cvtsd2si".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "RTZ-for-RNE (truncating CVTT where RNE CVT intended) must REFUTE"
    );
}

#[test]
fn cvtsi2sd_signed_for_unsigned_refutes() {
    // INT->FP source signedness: a SIGNED-int->FP (sign-extend) lowering where an
    // UNSIGNED-int->FP (zero-extend) was intended must REFUTE. For an i32 source
    // with the high bit set (0x80000000) the signed reading is -2147483648 and the
    // unsigned reading is 2147483648 — distinct f64 magnitudes ⇒ DIVERGE.
    use trust_cg_verify::trust_ir_semantics::{
        encode_trust_ir_fcvt_from_sint, encode_trust_ir_fcvt_from_uint,
    };
    let a = SmtExpr::var("recon_src", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 FcvtFromUint -> signed convert (INJECTED wrong signedness)"
            .to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_from_uint(11, 53, a.clone(), 32), // UNSIGNED intended
        aarch64_expr: encode_trust_ir_fcvt_from_sint(11, 53, a.clone()),      // SIGNED (WRONG)
        inputs: vec![("recon_src".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Cvtsi2sd".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "signed-for-unsigned int->FP convert must REFUTE"
    );
}

// ---------------------------------------------------------------------------
// to-100% scalar batch: copy / IMUL-imm / LEA / ROUND refutations + DEFER docs
// ---------------------------------------------------------------------------

#[test]
fn movrr_copy_reconstructs_valid_as_bit_identity() {
    // MOV r64,r64 is a bit-preserving identity: source = src, machine = src.
    // Credited via reconstruction (provenance Reconstructed); a wrong opcode
    // bound here would use a different machine encoder (next test).
    let inst = X86ISelInst::new(X86Opcode::MovRR, vec![r64(0), r64(1)]);
    let ob = reconstruct_x86_alu_obligation(&inst).expect("MovRR reconstructs");
    assert!(ob.is_reconstructed());
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

#[test]
fn injected_not_for_intended_copy_refutes() {
    // COPY family: a buggy "copy" lowering that emits NOT (~src) instead of the
    // bit-identity MOV ⇒ ~src != src ⇒ REFUTE. This proves the copy
    // reconstruction's machine side genuinely depends on the opcode→encoder
    // binding (not a vacuous src==src that any machine op would satisfy).
    use trust_cg_verify::x86_64_semantics::encode_not;
    let sym = SmtExpr::var("recon_src", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 Copy_64 -> NOT (INJECTED non-identity machine)".to_string(),
        trust_ir_expr: sym.clone(), // intended: identity copy
        aarch64_expr: encode_not(S, sym.clone()), // WRONG: ~src
        inputs: vec![("recon_src".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "MovRR".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "NOT-for-Copy must REFUTE (~src != src)"
    );
    assert!(buggy.is_genuinely_proven());
}

#[test]
fn movssrr_scalar_fp_copy_reconstructs_valid() {
    // MOVSS xmm,xmm scalar copy is a bit-preserving FP identity.
    use trust_cg_ir::regs::VReg;
    let xs = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr32));
    let inst = X86ISelInst::new(X86Opcode::MovssRR, vec![xs(0), xs(1)]);
    let ob = reconstruct_x86_alu_obligation(&inst).expect("MovssRR reconstructs");
    assert!(ob.is_reconstructed());
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

#[test]
fn imulrri_reconstructs_valid_and_binds_imm_constant() {
    // IMUL r,r,imm — the imm binds to a width-const; only src is a declared input.
    let inst = X86ISelInst::new(
        X86Opcode::ImulRRI,
        vec![r64(0), r64(1), X86ISelOperand::Imm(42)],
    );
    let ob = reconstruct_x86_alu_obligation(&inst).expect("ImulRRI reconstructs");
    assert!(ob.is_reconstructed());
    assert_eq!(
        ob.inputs.len(),
        1,
        "only src is a declared input (imm is a const)"
    );
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

#[test]
fn imulrri_wrong_imm_refutes() {
    // Inject a machine IMUL by the WRONG immediate (43) against a source that
    // intends *42 ⇒ src*42 != src*43 for src != 0 ⇒ REFUTE. Proves the
    // reconstruction's machine side genuinely depends on the immediate.
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_verify::x86_64_semantics::encode_imul_rri;
    let src = SmtExpr::var("recon_src", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 Imul*42 -> IMUL*43 (INJECTED wrong imm)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(
            &Opcode::Imul,
            Type::I64,
            src.clone(),
            SmtExpr::bv_const(42, 64),
        ),
        aarch64_expr: encode_imul_rri(S, src.clone(), 43), // WRONG imm
        inputs: vec![("recon_src".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "ImulRRI".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "IMUL*43-for-IMUL*42 must REFUTE"
    );
    assert!(buggy.is_genuinely_proven());
}

#[test]
fn lea_base_disp_reconstructs_valid_with_register_and_stackslot_base() {
    // Plain LEA [base+disp] reconstructs for a register base AND a StackSlot base
    // (the StackSlot resolves to a 64-bit frame pointer + slot at frame lowering;
    // both are modeled as the same fresh 64-bit base symbol).
    let reg = X86ISelInst::new(
        X86Opcode::Lea,
        vec![
            r64(0),
            X86ISelOperand::MemAddr {
                base: Box::new(r64(1)),
                disp: 24,
            },
        ],
    );
    let ob = reconstruct_x86_alu_obligation(&reg).expect("LEA reg base reconstructs");
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));

    let slot = X86ISelInst::new(
        X86Opcode::Lea,
        vec![
            r64(0),
            X86ISelOperand::MemAddr {
                base: Box::new(X86ISelOperand::StackSlot(3)),
                disp: 8,
            },
        ],
    );
    let ob = reconstruct_x86_alu_obligation(&slot).expect("LEA stackslot base reconstructs");
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

#[test]
fn lea_base_disp_wrong_disp_refutes() {
    // Inject a machine LEA with the WRONG disp (99) against a source that intends
    // base+16 ⇒ base+16 != base+99 ⇒ REFUTE.
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_verify::x86_64_semantics::encode_lea_base_disp;
    let base = SmtExpr::var("recon_base", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 LEA base+16 -> base+99 (INJECTED wrong disp)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(
            &Opcode::Iadd,
            Type::I64,
            base.clone(),
            SmtExpr::bv_const(16, 64),
        ),
        aarch64_expr: encode_lea_base_disp(base.clone(), 99, 64), // WRONG disp
        inputs: vec![("recon_base".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Lea".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "LEA base+99-for-base+16 must REFUTE"
    );
}

#[test]
fn leasib_reconstructs_valid() {
    let inst =
        representative_x86_reconstructable_inst(X86Opcode::LeaSib).expect("LeaSib representative");
    let ob = reconstruct_x86_alu_obligation(&inst).expect("LeaSib reconstructs");
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

#[test]
fn leasib_wrong_scale_refutes() {
    // Inject a machine SIB-LEA with the WRONG scale (8) against a source that
    // intends scale 4 ⇒ base+index*4 != base+index*8 for index != 0 ⇒ REFUTE.
    // Proves the SIB-LEA machine side genuinely depends on the scale.
    use trust_cg_verify::x86_64_semantics::encode_lea_base_index_scale_disp;
    let base = SmtExpr::var("recon_base", 64);
    let index = SmtExpr::var("recon_index", 64);
    let source_scale4 = base
        .clone()
        .bvadd(index.clone().bvmul(SmtExpr::bv_const(4, 64)))
        .bvadd(SmtExpr::bv_const(16, 64));
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 SIB-LEA scale*4 -> scale*8 (INJECTED wrong scale)".to_string(),
        trust_ir_expr: source_scale4,
        aarch64_expr: encode_lea_base_index_scale_disp(base.clone(), index.clone(), 8, 16), // WRONG scale
        inputs: vec![
            ("recon_base".to_string(), 64),
            ("recon_index".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "LeaSib".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "SIB-LEA scale*8-for-scale*4 must REFUTE"
    );
}

#[test]
fn round_each_mode_reconstructs_valid() {
    // ROUNDSD floor/ceil/trunc (imm8 = 01/10/11) each reconstruct Valid. The
    // native FP evaluator faithfully models all three rounding modes.
    use trust_cg_ir::regs::VReg;
    let xd = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr64));
    for imm8 in [0b01_i64, 0b10, 0b11] {
        let inst = X86ISelInst::new(
            X86Opcode::Roundsd,
            vec![xd(0), xd(1), X86ISelOperand::Imm(imm8)],
        );
        let ob = reconstruct_x86_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("Roundsd imm8={imm8:#b} reconstructs"));
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "Roundsd imm8={imm8:#b} must be Valid"
        );
    }
}

#[test]
fn round_rne_mode_fails_closed() {
    // The round-to-nearest mode (imm8[1:0]=00) is never emitted by the backend;
    // the reconstructor fails closed (returns None) rather than credit it — so a
    // stray RNE-encoded ROUND cannot be silently passed.
    use trust_cg_ir::regs::VReg;
    let xd = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr64));
    let inst = X86ISelInst::new(
        X86Opcode::Roundsd,
        vec![xd(0), xd(1), X86ISelOperand::Imm(0b00)],
    );
    assert!(
        reconstruct_x86_alu_obligation(&inst).is_none(),
        "RNE-mode ROUNDSD (imm8=00) must fail closed (never emitted)"
    );
}

#[test]
fn round_wrong_mode_floor_for_ceil_refutes() {
    // Inject a machine ROUNDSD with FLOOR (imm8=01) against a source that intends
    // CEIL ⇒ floor(0.5)=0 != ceil(0.5)=1 ⇒ REFUTE on a non-integral input. This
    // proves the rounding mode is faithfully modeled (not ignored).
    use trust_cg_lower::types::Type as T;
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_fceil;
    use trust_cg_verify::x86_64_semantics::{X86FPSize, encode_fp_round};
    let a = SmtExpr::var("recon_a", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED x86_64 Round_ceil -> ROUNDSD floor (INJECTED wrong mode)".to_string(),
        trust_ir_expr: encode_trust_ir_fceil(T::F64, a.clone()), // intended: ceil
        aarch64_expr: encode_fp_round(X86FPSize::Double, 0b01, a.clone()), // WRONG: floor
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 11, 53)],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Roundsd".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "floor-for-ceil must REFUTE (floor(0.5) != ceil(0.5)); rounding mode is faithfully modeled"
    );
}

// --- HONEST DEFERRALS: these opcodes are NOT reconstructable (true reasons). ---

#[test]
fn deferred_scalar_opcodes_are_not_reconstructable() {
    // MovRI (materialize a constant: const == const, NO independent constant
    // model in the single instruction) is the ONLY honestly-deferred scalar
    // opcode left — it is `FailClosedAllowlisted` (out of the emittable
    // denominator), NOT a value-reconstruction. Asserting it does not reconstruct
    // guards against a future accidental fake-cover.
    assert!(
        representative_x86_reconstructable_inst(X86Opcode::MovRI).is_none(),
        "MovRI must be honestly deferred (no reconstructable representative — const==const)"
    );

    // Idiv/Div (implicit double-width RDX:RAX dividend) and Cmovcc/Cmovcc32
    // (implicit RFLAGS condition) were FORMERLY deferred but are now GENUINELY
    // reconstructed (task #76 implicit-operand tier): the dividend as a sext/zext
    // leaf with sdiv/udiv quotient+remainder, the condition as a CMP+CMOV pair
    // over the real flag formulas. They MUST now reconstruct (the converse guard:
    // a regression that drops their credit would re-RED them).
    for op in [
        X86Opcode::Idiv,
        X86Opcode::Div,
        X86Opcode::Cmovcc,
        X86Opcode::Cmovcc32,
    ] {
        assert!(
            representative_x86_reconstructable_inst(op).is_some(),
            "{op:?} must now be reconstructable (implicit-operand tier, task #76)"
        );
    }
}

// --- commutative no-refute documentation (IMUL by imm) ---

#[test]
fn imul_is_commutative_operand_swap_not_observable_documented() {
    // The 3-operand IMUL multiply is commutative: swapping src and the imm-as-
    // operand cannot be caught by the reconstruction (a*imm == imm*a). The
    // refutation content for IMUL-imm is the WRONG-IMM test above, not an operand
    // swap. This documents the commutative limitation, mirroring the Add/And/Or/
    // Xor commutative documentation.
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_binop;
    let src = SmtExpr::var("recon_src", 64);
    let a = encode_trust_ir_binop(
        &Opcode::Imul,
        Type::I64,
        src.clone(),
        SmtExpr::bv_const(7, 64),
    );
    let b = encode_trust_ir_binop(
        &Opcode::Imul,
        Type::I64,
        SmtExpr::bv_const(7, 64),
        src.clone(),
    );
    // a and b are the same multiply with operands swapped; structurally distinct
    // expressions but semantically equal (commutative) — no refutation possible.
    let ob = ProofObligation {
        name: "RECONSTRUCTED x86_64 Imul commutative (operand swap, documented no-refute)"
            .to_string(),
        trust_ir_expr: a,
        aarch64_expr: b,
        inputs: vec![("recon_src".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "ImulRRI".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
        "commutative IMUL operand swap is NOT observable (documented)"
    );
}

// ===========================================================================
// SSE2/SSE4.1 PACKED (v128) lane-wise reconstruction — refutation suite
// ===========================================================================
//
// The packed value ops reconstruct LANE-WISE over the 128-bit XMM: the MACHINE
// side is the real packed encoder (`encode_paddd` = lane-wise bvadd at the element
// width fixed by the opcode), the SOURCE side is the trust_ir scalar op
// `map_lanes`-applied at the SAME arrangement. The refutation content is:
//   * a WRONG lane OP (Paddd-as-Psubd: add vs sub) ⇒ REFUTE;
//   * a WRONG lane WIDTH (i16x8 vs i32x4: carry/borrow crosses the wrong boundary)
//     ⇒ REFUTE;
//   * a WRONG predicate (PCMPEQ-as-PCMPGT) ⇒ REFUTE;
//   * the PANDN operand-complement asymmetry ((~a)&b vs a&(~b)) ⇒ REFUTE.
// These build the BUGGY obligation with the same public encoders the reconstructor
// uses, so they test the exact source-vs-machine comparison.

mod packed_v128 {
    use super::*;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_verify::smt::VectorArrangement as VA;
    use trust_cg_verify::trust_ir_semantics::{
        encode_trust_ir_lanewise_binop, encode_trust_ir_lanewise_cmp_mask,
        encode_trust_ir_v128_bitwise,
    };
    use trust_cg_verify::x86_64_semantics::{
        encode_paddd, encode_paddw, encode_pandn, encode_pcmpeqd, encode_pcmpgtd, encode_psubd,
    };

    /// 128-bit symbolic operand as two 64-bit halves (the eval env values are u64).
    fn v128(name: &str) -> SmtExpr {
        SmtExpr::var(format!("{name}_hi"), 64).concat(SmtExpr::var(format!("{name}_lo"), 64))
    }

    fn v128_inputs() -> Vec<(String, u32)> {
        vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("b_hi".to_string(), 64),
        ]
    }

    fn packed_ob(name: &str, trust_ir_expr: SmtExpr, machine_expr: SmtExpr) -> ProofObligation {
        ProofObligation {
            name: name.to_string(),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: v128_inputs(),
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "PACKED".to_string(),
                arity: 2,
            },
        }
    }

    // -- positive: a correct lane-wise reconstruction discharges Valid ----------

    #[test]
    fn paddd_lanewise_reconstructs_valid() {
        let inst = representative_x86_reconstructable_inst(X86Opcode::Paddd)
            .expect("Paddd must have a representative");
        let ob = reconstruct_x86_alu_obligation(&inst).expect("Paddd must reconstruct");
        assert!(ob.is_reconstructed());
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "correct PADDD lane-wise lowering must be Valid"
        );
    }

    // -- (b) WRONG LANE OP: Paddd-as-Psubd refutes ------------------------------

    #[test]
    fn wrong_lane_op_paddd_as_psubd_refutes() {
        let a = v128("a");
        let b = v128("b");
        // SOURCE intends i32x4 ADD; MACHINE is the PSUBD encoder (lane-wise sub).
        let trust_ir_expr =
            encode_trust_ir_lanewise_binop(&Opcode::Iadd, VA::S4, a.clone(), b.clone());
        let machine_expr = encode_psubd(a, b);
        let ob = packed_ob(
            "RECONSTRUCTED x86_64 packed Iadd -> PSUBD (INJECTED wrong lane op)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "Paddd-as-Psubd must REFUTE (lane bvadd != lane bvsub)"
        );
    }

    // -- (b) WRONG LANE WIDTH: i16x8 source vs i32x4 machine refutes ------------

    #[test]
    fn wrong_lane_width_i16x8_for_i32x4_add_refutes() {
        let a = v128("a");
        let b = v128("b");
        // SOURCE treats the vector as i16x8 (8 lanes of 16); MACHINE is PADDD
        // (i32x4, 4 lanes of 32). The carry crosses the 16-bit boundary in the
        // machine where the source has no carry, so they DIVERGE.
        let trust_ir_expr =
            encode_trust_ir_lanewise_binop(&Opcode::Iadd, VA::H8, a.clone(), b.clone());
        let machine_expr = encode_paddd(a, b);
        let ob = packed_ob(
            "RECONSTRUCTED x86_64 packed i16x8-Add -> PADDD i32x4 (INJECTED wrong lane width)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "i16x8-add vs i32x4 PADDD must REFUTE (carry crosses the wrong lane boundary)"
        );
    }

    // Symmetric width check: i32x4 source vs i16x8 (PADDW) machine.
    #[test]
    fn wrong_lane_width_i32x4_for_i16x8_add_refutes() {
        let a = v128("a");
        let b = v128("b");
        let trust_ir_expr =
            encode_trust_ir_lanewise_binop(&Opcode::Iadd, VA::S4, a.clone(), b.clone());
        let machine_expr = encode_paddw(a, b);
        let ob = packed_ob(
            "RECONSTRUCTED x86_64 packed i32x4-Add -> PADDW i16x8 (INJECTED wrong lane width)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "i32x4-add vs i16x8 PADDW must REFUTE (carry crosses the wrong lane boundary)"
        );
    }

    // -- (b) WRONG PREDICATE: PCMPEQ-as-PCMPGT refutes --------------------------

    #[test]
    fn wrong_predicate_pcmpeqd_as_pcmpgtd_refutes() {
        let a = v128("a");
        let b = v128("b");
        // SOURCE intends per-lane EQ mask; MACHINE is the PCMPGTD signed-gt encoder.
        let trust_ir_expr =
            encode_trust_ir_lanewise_cmp_mask(&IntCC::Equal, VA::S4, a.clone(), b.clone());
        let machine_expr = encode_pcmpgtd(a, b);
        let ob = packed_ob(
            "RECONSTRUCTED x86_64 packed Icmp_Eq -> PCMPGTD (INJECTED wrong predicate)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "PCMPEQ-as-PCMPGT must REFUTE (a==b mask != a>b mask)"
        );
    }

    // Symmetric predicate check: PCMPGT source vs PCMPEQ machine.
    #[test]
    fn wrong_predicate_pcmpgtd_as_pcmpeqd_refutes() {
        let a = v128("a");
        let b = v128("b");
        let trust_ir_expr = encode_trust_ir_lanewise_cmp_mask(
            &IntCC::SignedGreaterThan,
            VA::S4,
            a.clone(),
            b.clone(),
        );
        let machine_expr = encode_pcmpeqd(a, b);
        let ob = packed_ob(
            "RECONSTRUCTED x86_64 packed Icmp_Sgt -> PCMPEQD (INJECTED wrong predicate)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "PCMPGT-as-PCMPEQ must REFUTE (a>b mask != a==b mask)"
        );
    }

    // -- (b) PANDN operand-complement asymmetry refutes -------------------------

    #[test]
    fn pandn_operand_complement_asymmetry_refutes() {
        let a = v128("a");
        let b = v128("b");
        // SOURCE intends the WRONG complement order a&(~b) (BorNot-style would be
        // a|(~b); here we use the plain Band as the WRONG model — a&b — which is NOT
        // PANDN's (~a)&b). MACHINE is the real PANDN = (~a)&b.
        let trust_ir_expr = encode_trust_ir_v128_bitwise(&Opcode::Band, a.clone(), b.clone());
        let machine_expr = encode_pandn(a, b);
        let ob = packed_ob(
            "RECONSTRUCTED x86_64 packed Band -> PANDN (INJECTED wrong: a&b != (~a)&b)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "Band-as-PANDN must REFUTE (a&b != (~a)&b)"
        );
    }
}

// ---------------------------------------------------------------------------
// (f) IMPLICIT-OPERAND tier (task #76 final): DIVISION + CONDITIONAL MOVE.
//
// These three families have OPERATIVE inputs that are NOT explicit operands of
// the single instruction:
//   * Idiv/Div — the double-width RDX:RAX dividend (set up by CDQ/CQO + MOV).
//   * Cmovcc/Cmovcc32 — the RFLAGS state of a prior CMP.
// We reconstruct them genuinely (the implicit dividend as a sext/zext leaf, the
// implicit condition as a CMP+CMOV pair over the real flag formulas) and prove
// BOTH that a correct lowering discharges Valid AND that a wrong choice REFUTES.
// ---------------------------------------------------------------------------
mod implicit_operand {
    use super::*;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_verify::x86_64_semantics::{encode_int_cmp_flags, eval_int_condition};

    // -- (a) Positive: each reconstruction discharges Valid -------------------

    #[test]
    fn division_signed_and_unsigned_reconstruct_valid() {
        for op in [X86Opcode::Idiv, X86Opcode::Div] {
            let inst = representative_x86_reconstructable_inst(op).expect("rep inst");
            let ob = reconstruct_x86_alu_obligation(&inst).expect("reconstruct");
            assert!(
                matches!(
                    ob.machine_side_provenance,
                    MachineSideProvenance::Reconstructed { .. }
                ),
                "{op:?} must be Reconstructed-provenance"
            );
            assert!(
                matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
                "{op:?} division reconstruction must discharge Valid"
            );
        }
    }

    #[test]
    fn cond_move_reconstructs_valid_for_every_value_select_cc() {
        for op in [X86Opcode::Cmovcc, X86Opcode::Cmovcc32] {
            let class = if op == X86Opcode::Cmovcc32 {
                RegClass::Gpr32
            } else {
                RegClass::Gpr64
            };
            let reg = |id: u32| X86ISelOperand::VReg(VReg::new(id, class));
            for cc in [
                X86CondCode::E,
                X86CondCode::NE,
                X86CondCode::L,
                X86CondCode::GE,
                X86CondCode::G,
                X86CondCode::LE,
                X86CondCode::B,
                X86CondCode::AE,
                X86CondCode::A,
                X86CondCode::BE,
            ] {
                let inst = X86ISelInst::new(op, vec![reg(0), reg(1), X86ISelOperand::CondCode(cc)]);
                let ob = reconstruct_x86_alu_obligation(&inst).expect("reconstruct cmov");
                assert!(
                    matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
                    "{op:?} with cc {cc:?} must discharge Valid"
                );
            }
        }
    }

    // -- (b) Idiv-as-Div / Div-as-Idiv REFUTE on a negative dividend ----------
    //
    // The ONLY difference between the signed and unsigned models is sext-vs-zext
    // of the dividend (and sdiv-vs-udiv). For a NEGATIVE rax these give different
    // quotients/remainders, so a mislowering REFUTES. divisor==0 is EXCLUDED by
    // the model precondition (so it is never a counterexample), as is INT_MIN/-1.

    /// Build a division obligation with the machine side using the WRONG
    /// signedness (the intended trust_ir op is `signed`, the machine uses the
    /// opposite extension/divide).
    fn buggy_division(name: &str, intended_signed: bool, width: u32) -> ProofObligation {
        let dwidth = width * 2;
        let extra = dwidth - width;
        let rax = SmtExpr::var("recon_rax", width);
        let divisor = SmtExpr::var("recon_divisor", width);

        // SOURCE: the INTENDED single-width op.
        let (q_op, r_op) = if intended_signed {
            (Opcode::Sdiv, Opcode::Srem)
        } else {
            (Opcode::Udiv, Opcode::Urem)
        };
        let ir_q = encode_trust_ir_binop(&q_op, Type::I32, rax.clone(), divisor.clone());
        let ir_r = encode_trust_ir_binop(&r_op, Type::I32, rax.clone(), divisor.clone());
        let trust_ir_expr = ir_q.concat(ir_r);

        // MACHINE: the WRONG signedness (opposite ext + divide).
        let wrong_signed = !intended_signed;
        let (dividend_2w, divisor_2w) = if wrong_signed {
            (rax.clone().sign_ext(extra), divisor.clone().sign_ext(extra))
        } else {
            (rax.clone().zero_ext(extra), divisor.clone().zero_ext(extra))
        };
        let (mq, mr) = if wrong_signed {
            let q = dividend_2w.clone().bvsdiv(divisor_2w.clone());
            let r = dividend_2w
                .clone()
                .bvsub(q.clone().bvmul(divisor_2w.clone()));
            (q, r)
        } else {
            let q = dividend_2w.clone().bvudiv(divisor_2w.clone());
            let r = dividend_2w
                .clone()
                .bvsub(q.clone().bvmul(divisor_2w.clone()));
            (q, r)
        };
        let machine_expr = mq.extract(width - 1, 0).concat(mr.extract(width - 1, 0));

        // Same preconditions as the genuine builder (divisor != 0; signed: no
        // INT_MIN/-1 overflow). The refutation must come from a VALID input
        // (negative dividend), not a precond-excluded one.
        let zero = SmtExpr::bv_const(0, width);
        let mut preconditions = vec![divisor.clone().eq_expr(zero).not_expr()];
        if intended_signed {
            let int_min = SmtExpr::bv_const(1u64 << (width - 1), width);
            let neg_one = SmtExpr::bv_const(((1u128 << width) - 1) as u64, width);
            let overflow = rax
                .clone()
                .eq_expr(int_min)
                .and_expr(divisor.clone().eq_expr(neg_one));
            preconditions.push(overflow.not_expr());
        }

        ProofObligation {
            name: name.to_string(),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: vec![
                ("recon_rax".to_string(), width),
                ("recon_divisor".to_string(), width),
            ],
            preconditions,
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "buggy_div".to_string(),
                arity: 1,
            },
        }
    }

    #[test]
    fn idiv_as_div_refutes_on_negative_dividend() {
        // Intended SIGNED (IDIV); machine emitted UNSIGNED (DIV) = zext/udiv. For a
        // negative dividend the unsigned interpretation reads a huge positive value
        // ⇒ different quotient ⇒ REFUTE.
        let buggy = buggy_division(
            "RECONSTRUCTED x86_64 Sdiv -> DIV (INJECTED sext->zext / sdiv->udiv)",
            true,
            32,
        );
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "IDIV-as-DIV must REFUTE on a negative dividend (signed != unsigned divide)"
        );
    }

    #[test]
    fn div_as_idiv_refutes_on_high_bit_dividend() {
        // Intended UNSIGNED (DIV); machine emitted SIGNED (IDIV) = sext/sdiv. For a
        // dividend with the high bit set the signed interpretation is negative ⇒
        // different quotient ⇒ REFUTE.
        let buggy = buggy_division(
            "RECONSTRUCTED x86_64 Udiv -> IDIV (INJECTED zext->sext / udiv->sdiv)",
            false,
            32,
        );
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "DIV-as-IDIV must REFUTE on a high-bit-set dividend (unsigned != signed divide)"
        );
    }

    #[test]
    fn division_divisor_zero_is_excluded_by_precondition() {
        // DOCUMENTED: divisor==0 (which would #DE on hardware) is never a
        // counterexample because the model carries `divisor != 0` as a
        // precondition. We assert the genuine obligation still discharges Valid
        // (i.e. the precondition does NOT make it vacuous — there are plenty of
        // satisfying nonzero divisors), and that the precondition is present.
        let inst = representative_x86_reconstructable_inst(X86Opcode::Idiv).expect("rep");
        let ob = reconstruct_x86_alu_obligation(&inst).expect("reconstruct");
        assert!(
            !ob.preconditions.is_empty(),
            "division obligation must carry a divisor!=0 (and no-overflow) precondition"
        );
        assert!(matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Valid
        ));
    }

    // -- (c) Cmovcc WRONG-cc REFUTES (E vs NE, L vs GE) -----------------------
    //
    // The machine side uses the genuine `eval_int_condition(cc, flags_of(a,b))`;
    // the source side uses `icmp(intcc, a, b)`. When the cc and intcc DISAGREE
    // (E machine vs NE source, L machine vs GE source) the two selects pick
    // different operands for some (a,b) ⇒ REFUTE. This proves the cc is NOT
    // collapsed to a single abstract boolean (which would make all ccs vacuously
    // equal). Both Cmovcc widths share the model, so width 32 witnesses both.

    /// Build a CMOV obligation where the MACHINE uses `machine_cc` but the SOURCE
    /// predicate is `source_intcc` — a deliberate cc mismatch.
    fn buggy_cond_move(
        name: &str,
        machine_cc: X86CondCode,
        source_intcc: IntCC,
        width: u32,
    ) -> ProofObligation {
        let a = SmtExpr::var("recon_cmp_a", width);
        let b = SmtExpr::var("recon_cmp_b", width);
        let src = SmtExpr::var("recon_src", width);
        let dst = SmtExpr::var("recon_dst", width);

        let flags = encode_int_cmp_flags(width, a.clone(), b.clone());
        let machine_cond = eval_int_condition(machine_cc, &flags);
        let machine_expr = SmtExpr::ite(machine_cond, src.clone(), dst.clone());

        let ir_pred = encode_trust_ir_icmp(&source_intcc, Type::I32, a.clone(), b.clone());
        let ir_cond = ir_pred.eq_expr(SmtExpr::bv_const(1, 1));
        let trust_ir_expr = SmtExpr::ite(ir_cond, src.clone(), dst.clone());

        ProofObligation {
            name: name.to_string(),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: vec![
                ("recon_cmp_a".to_string(), width),
                ("recon_cmp_b".to_string(), width),
                ("recon_src".to_string(), width),
                ("recon_dst".to_string(), width),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "buggy_cmov".to_string(),
                arity: 2,
            },
        }
    }

    #[test]
    fn cmovcc_e_for_ne_refutes() {
        // Machine selects on E (ZF) but source intends NE (!ZF) — complementary.
        let buggy = buggy_cond_move(
            "RECONSTRUCTED x86_64 CMOVcc E-for-NE (INJECTED wrong cc)",
            X86CondCode::E,
            IntCC::NotEqual,
            8,
        );
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "CMOVE-for-NE must REFUTE (ZF select != !ZF select)"
        );
    }

    #[test]
    fn cmovcc_l_for_ge_refutes() {
        // Machine selects on L (SF!=OF) but source intends GE (SF==OF) — the two
        // are exact complements, so the selects diverge whenever a != b.
        let buggy = buggy_cond_move(
            "RECONSTRUCTED x86_64 CMOVcc L-for-GE (INJECTED wrong cc)",
            X86CondCode::L,
            IntCC::SignedGreaterThanOrEqual,
            8,
        );
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "CMOVL-for-GE must REFUTE (signed-< select != signed->= select)"
        );
    }

    #[test]
    fn cmovcc_b_for_ae_refutes() {
        // Unsigned complement: B (CF) vs AE (!CF).
        let buggy = buggy_cond_move(
            "RECONSTRUCTED x86_64 CMOVcc B-for-AE (INJECTED wrong cc)",
            X86CondCode::B,
            IntCC::UnsignedGreaterThanOrEqual,
            8,
        );
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "CMOVB-for-AE must REFUTE (unsigned-< select != unsigned->= select)"
        );
    }

    #[test]
    fn cmovcc_each_correct_cc_is_distinct_not_a_single_abstract_boolean() {
        // SANITY: the cc is NOT collapsed to one abstract boolean. We assert each
        // correct (cc, intcc) pair is Valid AND that a CROSS pairing (signed-L
        // machine vs unsigned-B source) REFUTES — i.e. signed and unsigned
        // condition codes are genuinely different formulas.
        let ok = buggy_cond_move(
            "RECONSTRUCTED x86_64 CMOVcc L+SLT (correct)",
            X86CondCode::L,
            IntCC::SignedLessThan,
            8,
        );
        assert!(
            matches!(verify_by_evaluation(&ok), VerificationResult::Valid),
            "matched L/SignedLessThan must be Valid"
        );
        let cross = buggy_cond_move(
            "RECONSTRUCTED x86_64 CMOVcc L-machine vs unsigned-B source (INJECTED)",
            X86CondCode::L,
            IntCC::UnsignedLessThan,
            8,
        );
        assert!(
            matches!(
                verify_by_evaluation(&cross),
                VerificationResult::Invalid { .. }
            ),
            "signed-L machine vs unsigned-< source must REFUTE (distinct flag formulas)"
        );
    }

    // -- (d) ImulRM (register-memory multiply) reconstructs Valid -------------

    #[test]
    fn imulrm_reconstructs_valid() {
        let inst = representative_x86_reconstructable_inst(X86Opcode::ImulRM).expect("rep");
        let ob = reconstruct_x86_alu_obligation(&inst).expect("reconstruct");
        assert!(
            matches!(
                ob.machine_side_provenance,
                MachineSideProvenance::Reconstructed { .. }
            ),
            "ImulRM must be Reconstructed-provenance"
        );
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "ImulRM (reg * load(ea)) reconstruction must discharge Valid"
        );
    }

    #[test]
    fn imulrm_as_addrm_refutes() {
        // Build the obligation by hand: SOURCE intends Imul(reg, load(ea)) but the
        // MACHINE emitted ADD — different arithmetic ⇒ REFUTE.
        let width = 64u32;
        let reg = SmtExpr::var("recon_reg", width);
        let ir_ea = encode_trust_ir_binop(
            &Opcode::Iadd,
            Type::I64,
            SmtExpr::var("recon_base", 64),
            SmtExpr::bv_const(0, 64),
        );
        let machine_ea = encode_lea_base_disp(SmtExpr::var("recon_base", 64), 0, 64);
        let ir_mem = SmtExpr::mem_load(ir_ea, width, false, width);
        let machine_mem = SmtExpr::mem_load(machine_ea, width, false, width);
        let trust_ir_expr = encode_trust_ir_binop(&Opcode::Imul, Type::I64, reg.clone(), ir_mem);
        let machine_expr = encode_add_rr(S, reg.clone(), machine_mem); // WRONG: ADD not IMUL
        let buggy = ProofObligation {
            name: "RECONSTRUCTED x86_64 ImulRM -> ADD (INJECTED wrong op)".to_string(),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: vec![
                ("recon_reg".to_string(), width),
                ("recon_base".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "buggy".to_string(),
                arity: 2,
            },
        };
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "Imul-as-Add must REFUTE (reg*mem != reg+mem)"
        );
    }

    // -- (e) ImulRMSib (scaled-index register-memory multiply) ----------------

    #[test]
    fn imulrmsib_reconstructs_valid() {
        // The representative carries a SibMemAddr (the pipeline's SIB-opcode
        // integrity guard rejects MemAddr-shaped ImulRMSib), so this
        // exercises the SibMemAddr arm of the EA reconstruction end-to-end.
        let inst = representative_x86_reconstructable_inst(X86Opcode::ImulRMSib).expect("rep");
        assert!(
            matches!(
                inst.operands.get(1),
                Some(X86ISelOperand::SibMemAddr { .. })
            ),
            "ImulRMSib representative must be SIB-shaped"
        );
        let ob = reconstruct_x86_alu_obligation(&inst).expect("reconstruct");
        assert!(
            matches!(
                ob.machine_side_provenance,
                MachineSideProvenance::Reconstructed { .. }
            ),
            "ImulRMSib must be Reconstructed-provenance"
        );
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "ImulRMSib (reg * load(base+index*scale+disp)) reconstruction must discharge Valid"
        );
    }

    #[test]
    fn imulrmsib_wrong_scale_refutes() {
        // Hand-built: SOURCE intends reg * load(base + index*4 + 8) but the
        // MACHINE encodes scale 8 — a different loaded factor ⇒ REFUTE.
        let width = 64u32;
        let reg = SmtExpr::var("recon_reg", width);
        let base = SmtExpr::var("recon_base", 64);
        let index = SmtExpr::var("recon_index", 64);
        let ir_ea = encode_lea_base_index_scale_disp(base.clone(), index.clone(), 4, 8);
        let machine_ea = encode_lea_base_index_scale_disp(base, index, 8, 8); // WRONG scale
        let ir_mem = SmtExpr::mem_load(ir_ea, width, false, width);
        let machine_mem = SmtExpr::mem_load(machine_ea, width, false, width);
        let trust_ir_expr = encode_trust_ir_binop(&Opcode::Imul, Type::I64, reg.clone(), ir_mem);
        let machine_expr = encode_imul_rr(S, reg.clone(), machine_mem);
        let buggy = ProofObligation {
            name: "RECONSTRUCTED x86_64 ImulRMSib scale-4 -> scale-8 (INJECTED wrong EA)"
                .to_string(),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: vec![
                ("recon_reg".to_string(), width),
                ("recon_base".to_string(), 64),
                ("recon_index".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "buggy".to_string(),
                arity: 2,
            },
        };
        assert!(
            matches!(
                verify_by_evaluation(&buggy),
                VerificationResult::Invalid { .. }
            ),
            "wrong SIB scale must REFUTE (different loaded factor)"
        );
    }
}
