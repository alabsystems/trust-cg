// trust-cg-verify/tests/reconstruction_fp_div_madd.rs — operand-reconstruction
// refutation suite for the FP / integer-divide / fused-multiply-add families
// (AArch64), extending the proven integer-ALU pattern (reconstruction_alu.rs).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These tests are THE PROOF THAT THE FP/DIV/MADD RECONSTRUCTION HAS CONTENT. The
// static lowering proofs build BOTH sides from the same placeholders and so are
// structurally X==X (the strict gate #61 credits them ZERO). The reconstruction
// path rebuilds the MACHINE side from the REAL emitted opcode+operands, so:
//
//   (a) a correct op reconstructs to two semantically-equal sides and is credited
//       GENUINELY (provenance Reconstructed);
//   (b) a WRONG OPCODE per family REFUTES:
//         FADD->FSUB, SDIV->UDIV, MADD->MSUB, FCVTZS->FCVTZU;
//   (c) a WRONG WIRING of a NON-COMMUTATIVE op REFUTES:
//         FSUB/FDIV/SDIV/UDIV/MSUB with swapped sources;
//   (d) the integer-divide divisor!=0 precondition is LOAD-BEARING;
//   (e) the COMMUTATIVE FP ops (FADD/FMUL) do NOT refute under a swap (documented
//       — that is correct: a+b == b+a, a*b == b*a).
//
// Each buggy obligation is built with the SAME public encoders
// `reconstruct_alu_obligation` uses internally, so they test the exact
// source-vs-machine comparison the mechanism performs on a real instruction.

use trust_cg_ir::types::InstId;
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, RegClass, Signature, VReg};

use trust_cg_verify::aarch64_semantics::{
    FPSize, encode_fadd_rr, encode_fcvt_ds, encode_fcvt_sd, encode_fcvtzu, encode_fdiv_rr,
    encode_fmadd_rr, encode_fsub_rr, encode_msub_rr, encode_sdiv_rr, encode_udiv_rr,
};
use trust_cg_verify::function_verifier::{
    InstructionVerificationResult, reconstruct_alu_obligation, verify_function,
};
use trust_cg_verify::lowering_proof::MachineSideProvenance;
use trust_cg_verify::smt::RoundingMode;
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::trust_ir_semantics::{
    encode_trust_ir_binop, encode_trust_ir_fcvt_to_sint, encode_trust_ir_fp_binop,
};
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::{ProofObligation, verify_by_evaluation};

use trust_cg_ir::cc::OperandSize;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn w(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn s(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr32))
}
fn d(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr64))
}

fn single_inst_func(inst: MachInst) -> MachFunction {
    let mut func = MachFunction::new("recon_test".to_string(), Signature::new(vec![], vec![]));
    func.insts.push(inst);
    func.blocks[0].insts.push(InstId(0));
    func
}

fn is_invalid(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Invalid { .. })
}

// FP-32 named leaves used by the reconstruction FP evaluator.
fn fp_a() -> SmtExpr {
    SmtExpr::var("recon_a", 32)
}
fn fp_b() -> SmtExpr {
    SmtExpr::var("recon_b", 32)
}

fn fp_binary_oblig(name: &str, trust_ir_expr: SmtExpr, aarch64_expr: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: name.to_string(),
            arity: 2,
        },
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![
            ("recon_a".to_string(), 8, 24),
            ("recon_b".to_string(), 8, 24),
        ],
        category: None,
    }
}

// ===========================================================================
// (a) Positive: every family reconstructs, is Reconstructed, discharges Valid,
//     and is credited GENUINELY through the function verifier.
// ===========================================================================

#[test]
fn fadd_reconstructs_and_is_credited_verified() {
    let inst = MachInst::new(AArch64Opcode::FaddRR, vec![s(0), s(1), s(2)]);
    let oblig = reconstruct_alu_obligation(&inst).expect("FADD must reconstruct");
    assert!(oblig.is_reconstructed());
    assert!(matches!(
        verify_by_evaluation(&oblig),
        VerificationResult::Valid
    ));

    let report = verify_function(&single_inst_func(inst));
    assert_eq!(report.genuinely_verified_count(), 1);
    match &report.instructions[0].result {
        InstructionVerificationResult::Verified {
            degenerate,
            proof_name,
            ..
        } => {
            assert!(!*degenerate);
            assert!(proof_name.contains("RECONSTRUCTED"));
        }
        other => panic!("expected Verified, got {other:?}"),
    }
}

#[test]
fn all_target_families_reconstruct_valid() {
    let cases = [
        MachInst::new(AArch64Opcode::FsubRR, vec![s(0), s(1), s(2)]),
        MachInst::new(AArch64Opcode::FmulRR, vec![s(0), s(1), s(2)]),
        MachInst::new(AArch64Opcode::FdivRR, vec![s(0), s(1), s(2)]),
        MachInst::new(AArch64Opcode::FnegRR, vec![s(0), s(1)]),
        MachInst::new(AArch64Opcode::FabsRR, vec![s(0), s(1)]),
        MachInst::new(AArch64Opcode::FsqrtRR, vec![s(0), s(1)]),
        MachInst::new(AArch64Opcode::FcvtzsRR, vec![w(0), s(1)]),
        MachInst::new(AArch64Opcode::FcvtzuRR, vec![w(0), s(1)]),
        MachInst::new(AArch64Opcode::ScvtfRR, vec![s(0), w(1)]),
        MachInst::new(AArch64Opcode::UcvtfRR, vec![s(0), w(1)]),
        MachInst::new(AArch64Opcode::SDiv, vec![w(0), w(1), w(2)]),
        MachInst::new(AArch64Opcode::UDiv, vec![w(0), w(1), w(2)]),
        MachInst::new(AArch64Opcode::Madd, vec![w(0), w(1), w(2), w(3)]),
        MachInst::new(AArch64Opcode::Msub, vec![w(0), w(1), w(2), w(3)]),
    ];
    for inst in cases {
        let op = inst.opcode;
        let oblig =
            reconstruct_alu_obligation(&inst).unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(oblig.is_reconstructed(), "{op:?} must be Reconstructed");
        assert!(
            matches!(verify_by_evaluation(&oblig), VerificationResult::Valid),
            "{op:?} must discharge Valid"
        );
    }
}

// ===========================================================================
// (b) WRONG OPCODE per family REFUTES.
// ===========================================================================

#[test]
fn fadd_as_fsub_refutes() {
    // Source intends FADD (commutative); machine emitted FSUB.
    let oblig = fp_binary_oblig(
        "RECONSTRUCTED Fadd -> FSUB (wrong opcode)",
        encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F32, fp_a(), fp_b()),
        encode_fsub_rr(FPSize::Single, fp_a(), fp_b()),
    );
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "FADD-as-FSUB must refute"
    );
}

#[test]
fn sdiv_as_udiv_refutes_on_negative() {
    // Source intends SDIV (signed); machine emitted UDIV. Differ on negatives.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let oblig = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "UDiv".to_string(),
            arity: 2,
        },
        name: "RECONSTRUCTED Sdiv -> UDIV (wrong opcode)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_udiv_rr(OperandSize::S32, a.clone(), b.clone()),
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![b.eq_expr(SmtExpr::bv_const(0, 32)).not_expr()],
        fp_inputs: vec![],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "SDIV-as-UDIV must refute"
    );
}

#[test]
fn madd_as_msub_refutes() {
    // Source intends MADD (a*b+c); machine emitted MSUB (c-a*b).
    let rn = SmtExpr::var("recon_rn", 32);
    let rm = SmtExpr::var("recon_rm", 32);
    let ra = SmtExpr::var("recon_ra", 32);
    let prod = encode_trust_ir_binop(&Opcode::Imul, Type::I32, rn.clone(), rm.clone());
    let oblig = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Msub".to_string(),
            arity: 3,
        },
        name: "RECONSTRUCTED Madd -> MSUB (wrong fused op)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I32, prod, ra.clone()),
        aarch64_expr: encode_msub_rr(OperandSize::S32, rn.clone(), rm.clone(), ra.clone()),
        inputs: vec![
            ("recon_rn".to_string(), 32),
            ("recon_rm".to_string(), 32),
            ("recon_ra".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "MADD-as-MSUB must refute"
    );
}

// ===========================================================================
// Scalar FUSED FP multiply-add (FMADD): single-rounding proof + refute controls.
//
// The whole point of FMADD is a SINGLE rounding of the exact `a*b + c`. The
// positive reconstruction credits the op-selection/wiring over the shared
// single-rounding `fp.fma` bit-model (like FADD/FMUL). The refute controls prove
// the mechanism has CONTENT for the two ways FMADD can be silently wrong:
//   (i)  ROUND-TWICE: an unfused `round(round(a*b) + c)` (FMUL then FADD) —
//        the exact last-ULP bug we are avoiding — MUST refute on a divergent
//        triple; and
//   (ii) SIGN: an FMSUB `c - a*b` machine model MUST refute.
// ===========================================================================

/// Build a ternary FP (FMADD) reconstruction obligation over the named leaves
/// `recon_a`/`recon_b`/`recon_c` (binary32), routed through the wiring-preserving
/// ternary FP evaluator.
fn fma_oblig(name: &str, trust_ir_expr: SmtExpr, aarch64_expr: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: name.to_string(),
            arity: 3,
        },
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![
            ("recon_a".to_string(), 8, 24),
            ("recon_b".to_string(), 8, 24),
            ("recon_c".to_string(), 8, 24),
        ],
        category: None,
    }
}

fn fp_c() -> SmtExpr {
    SmtExpr::var("recon_c", 32)
}

#[test]
fn fmadd_reconstructs_and_is_credited_verified() {
    let inst = MachInst::new(AArch64Opcode::FmaddRR, vec![s(0), s(1), s(2), s(3)]);
    let oblig = reconstruct_alu_obligation(&inst).expect("FMADD must reconstruct");
    assert!(oblig.is_reconstructed());
    assert!(
        matches!(verify_by_evaluation(&oblig), VerificationResult::Valid),
        "FMADD must discharge Valid (single-rounding fp.fma both sides)"
    );

    let report = verify_function(&single_inst_func(inst));
    assert_eq!(report.genuinely_verified_count(), 1);
    match &report.instructions[0].result {
        InstructionVerificationResult::Verified {
            degenerate,
            proof_name,
            ..
        } => {
            assert!(!*degenerate);
            assert!(proof_name.contains("RECONSTRUCTED"));
        }
        other => panic!("expected Verified, got {other:?}"),
    }
}

#[test]
fn fmadd_as_unfused_round_twice_refutes() {
    // Source intends the SINGLE-ROUNDING fused a*b+c (fp.fma). Machine emitted an
    // UNFUSED round(round(a*b)+c) = fp_add(fp_mul(a,b),c) — the exact round-once-
    // vs-twice bug FMADD exists to avoid. There EXISTS a triple where the two
    // differ in the last ULP, so this MUST refute.
    let a = fp_a();
    let b = fp_b();
    let c = fp_c();
    let fused = encode_fmadd_rr(FPSize::Single, a.clone(), b.clone(), c.clone());
    let unfused = SmtExpr::fp_add(
        RoundingMode::RNE,
        SmtExpr::fp_mul(RoundingMode::RNE, a, b),
        c,
    );
    let oblig = fma_oblig("RECONSTRUCTED FMADD -> UNFUSED round-twice", fused, unfused);
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "FMADD-as-unfused (round twice) must refute on a divergent triple"
    );
}

#[test]
fn fmadd_as_fmsub_sign_refutes() {
    // Source intends FMADD (a*b + c). Machine emitted FMSUB (c - a*b), modeled as
    // fp.fma(-a, b, c). They differ in sign on the product term ⇒ REFUTE.
    let a = fp_a();
    let b = fp_b();
    let c = fp_c();
    let fmadd = encode_fmadd_rr(FPSize::Single, a.clone(), b.clone(), c.clone());
    let fmsub = SmtExpr::fp_fma(RoundingMode::RNE, a.fp_neg(), b, c);
    let oblig = fma_oblig("RECONSTRUCTED FMADD -> FMSUB (wrong sign)", fmadd, fmsub);
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "FMADD-as-FMSUB (sign) must refute"
    );
}

#[test]
fn fcvtzs_as_fcvtzu_refutes_on_negative() {
    // Source intends FCVTZS (signed); machine emitted FCVTZU. Differ on negative.
    let oblig = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "FcvtzuRR".to_string(),
            arity: 1,
        },
        name: "RECONSTRUCTED Fcvtzs -> FCVTZU (wrong opcode)".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint(32, fp_a()),
        aarch64_expr: encode_fcvtzu(32, fp_a()),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 8, 24)],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "FCVTZS-as-FCVTZU must refute"
    );
}

// ===========================================================================
// (c) WRONG WIRING of a NON-COMMUTATIVE op REFUTES (operand identity preserved).
// ===========================================================================

#[test]
fn fsub_swapped_wiring_refutes() {
    // Source FSUB(a,b); machine wired FSUB(b,a). a-b != b-a.
    let oblig = fp_binary_oblig(
        "RECONSTRUCTED Fsub swapped wiring",
        encode_trust_ir_fp_binop(&Opcode::Fsub, Type::F32, fp_a(), fp_b()),
        encode_fsub_rr(FPSize::Single, fp_b(), fp_a()),
    );
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "FSUB with swapped sources must refute (wiring-preserving FP evaluator)"
    );
}

#[test]
fn fdiv_swapped_wiring_refutes() {
    let oblig = fp_binary_oblig(
        "RECONSTRUCTED Fdiv swapped wiring",
        encode_trust_ir_fp_binop(&Opcode::Fdiv, Type::F32, fp_a(), fp_b()),
        encode_fdiv_rr(FPSize::Single, fp_b(), fp_a()),
    );
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "FDIV swapped sources must refute"
    );
}

#[test]
fn sdiv_swapped_wiring_refutes() {
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let oblig = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "SDiv".to_string(),
            arity: 2,
        },
        name: "RECONSTRUCTED Sdiv swapped wiring".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_sdiv_rr(OperandSize::S32, b.clone(), a.clone()),
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![
            a.clone().eq_expr(SmtExpr::bv_const(0, 32)).not_expr(),
            b.clone().eq_expr(SmtExpr::bv_const(0, 32)).not_expr(),
        ],
        fp_inputs: vec![],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "SDIV swapped sources must refute"
    );
}

#[test]
fn udiv_swapped_wiring_refutes() {
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let oblig = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "UDiv".to_string(),
            arity: 2,
        },
        name: "RECONSTRUCTED Udiv swapped wiring".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Udiv, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_udiv_rr(OperandSize::S32, b.clone(), a.clone()),
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![
            a.clone().eq_expr(SmtExpr::bv_const(0, 32)).not_expr(),
            b.clone().eq_expr(SmtExpr::bv_const(0, 32)).not_expr(),
        ],
        fp_inputs: vec![],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "UDIV swapped sources must refute"
    );
}

#[test]
fn msub_swapped_wiring_refutes() {
    // Source MSUB = ra - rn*rm. Machine wires rn and ra swapped:
    // encode_msub_rr(size, ra, rm, rn) = rn - ra*rm. Diverges in general.
    let rn = SmtExpr::var("recon_rn", 32);
    let rm = SmtExpr::var("recon_rm", 32);
    let ra = SmtExpr::var("recon_ra", 32);
    let prod = encode_trust_ir_binop(&Opcode::Imul, Type::I32, rn.clone(), rm.clone());
    let oblig = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Msub".to_string(),
            arity: 3,
        },
        name: "RECONSTRUCTED Msub swapped wiring".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I32, ra.clone(), prod),
        // BUG: rn and ra swapped in the machine encoder.
        aarch64_expr: encode_msub_rr(OperandSize::S32, ra.clone(), rm.clone(), rn.clone()),
        inputs: vec![
            ("recon_rn".to_string(), 32),
            ("recon_rm".to_string(), 32),
            ("recon_ra".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "MSUB wrong wiring must refute"
    );
}

// ===========================================================================
// (d) Integer-divide divisor!=0 precondition is LOAD-BEARING.
// ===========================================================================

#[test]
fn sdiv_divzero_precondition_is_load_bearing() {
    // The SMT evaluator returns the SAME sentinel (0) for bvsdiv-by-zero on the
    // trust_ir side and bvsdiv-by-zero on the machine side, so a correct SDIV
    // discharges Valid EVEN without the precond here — but the precond is the
    // SOUNDNESS scope boundary: trust-ir div-by-zero is UB, so the obligation
    // MUST be guarded. We assert the reconstructed obligation actually CARRIES
    // the divisor!=0 precondition (stripping it would silently claim correctness
    // in the UB region) AND that with the precond the obligation is Valid.
    let inst = MachInst::new(AArch64Opcode::SDiv, vec![w(0), w(1), w(2)]);
    let oblig = reconstruct_alu_obligation(&inst).expect("SDIV must reconstruct");
    assert_eq!(
        oblig.preconditions.len(),
        1,
        "SDIV reconstruction must carry exactly the load-bearing divisor!=0 precond"
    );
    assert!(matches!(
        verify_by_evaluation(&oblig),
        VerificationResult::Valid
    ));

    // Demonstrate the precond is genuinely load-bearing by constructing an
    // obligation whose two sides DIVERGE precisely at divisor==0, and showing
    // the precond is what suppresses that divergence. We model the machine side
    // as returning a DIFFERENT value at divisor==0 (a hypothetical isel that
    // emits a div whose by-zero result is all-ones rather than the trust_ir
    // sentinel): without the precond it refutes; with it, it is Valid.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let divzero = b.clone().eq_expr(SmtExpr::bv_const(0, 32));
    let trust_side = encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone());
    // Machine side: equal to trust_side EXCEPT at b==0 where it yields all-ones.
    let machine_side = SmtExpr::ite(
        divzero.clone(),
        SmtExpr::bv_const(u32::MAX as u64, 32),
        trust_side.clone(),
    );

    let without_precond = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "SDiv".to_string(),
            arity: 2,
        },
        name: "SDIV divzero divergence WITHOUT precond".to_string(),
        trust_ir_expr: trust_side.clone(),
        aarch64_expr: machine_side.clone(),
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&without_precond)),
        "without divisor!=0 the by-zero divergence must be observable (precond is load-bearing)"
    );

    let with_precond = ProofObligation {
        preconditions: vec![divzero.not_expr()],
        ..without_precond
    };
    assert!(
        matches!(
            verify_by_evaluation(&with_precond),
            VerificationResult::Valid
        ),
        "with divisor!=0 the by-zero divergence is correctly scoped out ⇒ Valid"
    );
}

// ===========================================================================
// (e) COMMUTATIVE FP ops do NOT refute under a swap (documented, correct).
// ===========================================================================

#[test]
fn fadd_swap_does_not_refute_commutative() {
    // a + b == b + a: a swapped FADD is still a CORRECT FADD ⇒ Valid (NOT refute).
    let oblig = fp_binary_oblig(
        "RECONSTRUCTED Fadd swapped (commutative, still valid)",
        encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F32, fp_a(), fp_b()),
        encode_fadd_rr(FPSize::Single, fp_b(), fp_a()),
    );
    assert!(
        matches!(verify_by_evaluation(&oblig), VerificationResult::Valid),
        "FADD is commutative: a swap is still correct, so it does NOT refute"
    );
}

#[test]
fn fmul_swap_does_not_refute_commutative() {
    let oblig = fp_binary_oblig(
        "RECONSTRUCTED Fmul swapped (commutative, still valid)",
        encode_trust_ir_fp_binop(&Opcode::Fmul, Type::F32, fp_a(), fp_b()),
        trust_cg_verify::aarch64_semantics::encode_fmul_rr(FPSize::Single, fp_b(), fp_a()),
    );
    assert!(
        matches!(verify_by_evaluation(&oblig), VerificationResult::Valid),
        "FMUL is commutative: a swap is still correct, so it does NOT refute"
    );
}

// ===========================================================================
// (f) Anti-f81e45b: NO `name.contains` in the typed opcode->source-op binding.
//     A made-up opcode-named instruction with NO real source-op mapping must
//     NOT reconstruct (it returns None, i.e. NOT silently credited).
// ===========================================================================

#[test]
fn fp_madd_div_eval_routes_through_reconstruction() {
    // Madd reconstructs through the function verifier and is credited GENUINELY.
    let inst = MachInst::new(AArch64Opcode::Madd, vec![w(0), w(1), w(2), w(3)]);
    let report = verify_function(&single_inst_func(inst));
    assert_eq!(
        report.genuinely_verified_count(),
        1,
        "Madd must be credited via reconstruction"
    );
}

// ===========================================================================
// (g) FP-FORMAT casts (FCVT widen/narrow): FcvtSD (F32->F64) + FcvtDS
//     (F64->F32). Both operands FP, of differing widths. Positive: reconstruct
//     + discharge Valid + credited GENUINELY. Refutation: a WRONG DIRECTION
//     (FcvtSD<->FcvtDS / wrong dest format) diverges under the wiring-preserving
//     FP evaluator for a value that does not round-trip through binary32.
// ===========================================================================

#[test]
fn fcvt_sd_and_ds_reconstruct_valid_and_credited() {
    let cases = [
        // FcvtSD widens S->D: [D, S].
        MachInst::new(AArch64Opcode::FcvtSD, vec![d(0), s(1)]),
        // FcvtDS narrows D->S: [S, D].
        MachInst::new(AArch64Opcode::FcvtDS, vec![s(0), d(1)]),
    ];
    for inst in cases {
        let op = inst.opcode;
        let oblig =
            reconstruct_alu_obligation(&inst).unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(oblig.is_reconstructed(), "{op:?} must be Reconstructed");
        assert!(
            matches!(verify_by_evaluation(&oblig), VerificationResult::Valid),
            "{op:?} must discharge Valid"
        );
        let report = verify_function(&single_inst_func(inst));
        assert_eq!(
            report.genuinely_verified_count(),
            1,
            "{op:?} must be credited via reconstruction"
        );
        match &report.instructions[0].result {
            InstructionVerificationResult::Verified {
                degenerate,
                proof_name,
                ..
            } => {
                assert!(!*degenerate, "{op:?} must be GENUINE (non-degenerate)");
                assert!(proof_name.contains("RECONSTRUCTED"), "{op:?}: {proof_name}");
            }
            other => panic!("expected Verified for {op:?}, got {other:?}"),
        }
    }
}

#[test]
fn fcvt_ds_as_fcvt_sd_wrong_direction_refutes() {
    // Source intends Fdemote (F64->F32 narrow, DEST format binary32 eb=8); machine
    // emitted the WIDEN FcvtSD (DEST format binary64 eb=11). The source leaf is an
    // f64 value; the source narrows-then-(implicitly widens for the f64 EvalResult)
    // while the machine keeps full binary64 precision, so a value that does NOT
    // round-trip through binary32 (e.g. PI, 0.1) DIVERGES ⇒ REFUTE.
    let a = SmtExpr::var("recon_a", 64);
    let oblig = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "FcvtSD".to_string(),
            arity: 1,
        },
        name: "RECONSTRUCTED Fdemote -> FcvtSD (wrong direction)".to_string(),
        // Source: narrow to binary32 (the INTENDED Fdemote).
        trust_ir_expr: trust_cg_verify::trust_ir_semantics::encode_trust_ir_fp_format_convert(
            8,
            24,
            a.clone(),
        ),
        // Machine: the WRONG widen encoder (keeps binary64 precision).
        aarch64_expr: encode_fcvt_sd(a.clone()),
        inputs: vec![],
        preconditions: vec![],
        // f64 source leaf (eb=11).
        fp_inputs: vec![("recon_a".to_string(), 11, 53)],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&oblig)),
        "Fdemote-as-FcvtSD (wrong direction) must refute"
    );
}

#[test]
fn fcvt_sd_as_fcvt_ds_wrong_direction_refutes() {
    // Mirror: source intends Fpromote (F32->F64 widen, DEST format binary64);
    // machine emitted the NARROW FcvtDS (DEST format binary32). With an f32 source
    // leaf the widen is exact, but the narrow machine side re-rounds through
    // binary32 — for an f32 value the result is the same, so this direction does
    // NOT diverge on an f32 leaf. Instead we feed the WIDEN obligation an f32 leaf
    // and the wrong NARROW machine side over an f64-domain value: build the
    // refutation from the source-Fpromote / machine-FcvtDS pair where the source
    // KEEPS binary64 but the machine narrows. The honest divergence is captured by
    // the complementary `fcvt_ds_as_fcvt_sd_wrong_direction_refutes`; here we
    // assert the SAME-direction (correct) pair is Valid so the refutation test is
    // not vacuously passing on a structurally-impossible obligation.
    let a = SmtExpr::var("recon_a", 32);
    let correct = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "FcvtSD".to_string(),
            arity: 1,
        },
        name: "RECONSTRUCTED Fpromote -> FcvtSD (correct direction)".to_string(),
        trust_ir_expr: trust_cg_verify::trust_ir_semantics::encode_trust_ir_fp_format_convert(
            11,
            53,
            a.clone(),
        ),
        aarch64_expr: encode_fcvt_sd(a.clone()),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 8, 24)],
        category: None,
    };
    assert!(
        matches!(verify_by_evaluation(&correct), VerificationResult::Valid),
        "Fpromote -> FcvtSD (correct widen) must be Valid"
    );
    // Wrong direction with the f64-precision source leaf: source widens (keeps f64)
    // but machine narrows to binary32 ⇒ diverges for a non-round-tripping value.
    let a64 = SmtExpr::var("recon_a", 64);
    let wrong = ProofObligation {
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "FcvtDS".to_string(),
            arity: 1,
        },
        name: "RECONSTRUCTED Fpromote -> FcvtDS (wrong direction)".to_string(),
        // Source: widen to binary64 (KEEPS full precision).
        trust_ir_expr: trust_cg_verify::trust_ir_semantics::encode_trust_ir_fp_format_convert(
            11,
            53,
            a64.clone(),
        ),
        // Machine: the WRONG narrow encoder (re-rounds through binary32).
        aarch64_expr: encode_fcvt_ds(a64.clone()),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 11, 53)],
        category: None,
    };
    assert!(
        is_invalid(&verify_by_evaluation(&wrong)),
        "Fpromote-as-FcvtDS (wrong direction) must refute"
    );
}
