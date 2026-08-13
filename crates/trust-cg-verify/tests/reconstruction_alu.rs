// trust-cg-verify/tests/reconstruction_alu.rs — Phase-2 operand-reconstruction
// PILOT refutation suite (AArch64 integer ALU), task #63.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These tests are the PROOF THAT THE MECHANISM HAS CONTENT. The static lowering
// proofs build BOTH sides of an ALU obligation from the SAME symbolic vars, so
// they are structurally X==X and the strict gate (#61) credits them ZERO — a
// wrong isel choice could never refute them. The reconstruction pilot rebuilds
// the MACHINE side from the REAL emitted opcode+operands, so:
//
//   (a) a correct ADD reconstructs to bvadd==bvadd and is credited GENUINELY
//       (provenance Reconstructed), even though the two sides happen to be equal;
//   (b) injecting SUB where Iadd was intended yields bvadd vs bvsub  ⇒ REFUTE;
//   (c) wiring a non-commutative SUB with swapped source operands  ⇒ REFUTE;
//   (d) the reconstructed path performs NO `name.contains` lookup (anti-f81e45b).
//
// (b) and (c) construct the BUGGY obligation with the very same public encoders
// that `reconstruct_alu_obligation` uses internally — `encode_trust_ir_binop`
// for the source side and `encode_<opcode>` for the machine side — so they test
// the exact source-vs-machine comparison the mechanism performs. If isel emitted
// the wrong opcode/wiring, the machine side built from the REAL instruction
// would diverge from the intended-source side exactly as modeled here.

use trust_cg_ir::types::InstId;
use trust_cg_ir::{
    AArch64Opcode, MachFunction, MachInst, MachOperand, RegClass, Signature, SpecialReg, VReg,
};

use trust_cg_verify::aarch64_semantics::{
    encode_add_rr, encode_and_rr, encode_bic_rr, encode_lsl_rr_masked, encode_lsr_rr_masked,
    encode_orn_rr, encode_orr_rr, encode_sub_rr, encode_uxt,
};
use trust_cg_verify::function_verifier::{
    InstructionVerificationResult, reconstruct_alu_obligation, verify_function,
};
use trust_cg_verify::lowering_proof::MachineSideProvenance;
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::trust_ir_semantics::{
    encode_trust_ir_binop, encode_trust_ir_bitwise_binop, encode_trust_ir_sextend,
    encode_trust_ir_shift,
};
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::{ProofObligation, verify_by_evaluation};

use trust_cg_ir::cc::OperandSize;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn vreg32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}

fn vreg64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn single_inst_func(inst: MachInst) -> MachFunction {
    let mut func = MachFunction::new("recon_test".to_string(), Signature::new(vec![], vec![]));
    func.insts.push(inst);
    func.blocks[0].insts.push(InstId(0));
    func
}

// ---------------------------------------------------------------------------
// (a) AddRR with real operands -> reconstructed, Valid, Reconstructed, Verified
// ---------------------------------------------------------------------------

#[test]
fn add_rr_reconstructs_and_is_credited_verified() {
    // `ADD Wd, Wn, Wm` with real (virtual) register operands.
    let inst = MachInst::new(AArch64Opcode::AddRR, vec![vreg32(0), vreg32(1), vreg32(2)]);

    // The obligation is RECONSTRUCTED from the real instruction.
    let obligation = reconstruct_alu_obligation(&inst).expect("AddRR must reconstruct");
    assert!(
        obligation.is_reconstructed(),
        "machine side must be tagged Reconstructed"
    );
    match &obligation.machine_side_provenance {
        MachineSideProvenance::Reconstructed { from_opcode, arity } => {
            assert_eq!(from_opcode, "AddRR");
            assert_eq!(*arity, 2);
        }
        other => panic!("expected Reconstructed provenance, got {other:?}"),
    }

    // It discharges Valid (a correct ADD: bvadd == bvadd).
    assert!(matches!(
        verify_by_evaluation(&obligation),
        VerificationResult::Valid
    ));

    // End-to-end through the function verifier: credited GENUINELY (not a
    // degenerate binding) because its provenance is Reconstructed.
    let func = single_inst_func(inst);
    let report = verify_function(&func);
    assert_eq!(report.verified_count(), 1);
    assert_eq!(report.genuinely_verified_count(), 1);
    assert_eq!(report.unverified_count(), 0);
    match &report.instructions[0].result {
        InstructionVerificationResult::Verified {
            degenerate,
            proof_name,
            ..
        } => {
            assert!(
                !*degenerate,
                "reconstructed proof must be credited, not degenerate"
            );
            assert!(proof_name.contains("RECONSTRUCTED"));
        }
        other => panic!("expected Verified, got {other:?}"),
    }
}

#[test]
fn add_ri_reconstructs_with_immediate_bound_as_constant() {
    // `ADD Xd, Xn, #7` — the RI form binds the immediate to a bv_const.
    let inst = MachInst::new(
        AArch64Opcode::AddRI,
        vec![vreg64(0), vreg64(1), MachOperand::Imm(7)],
    );
    let obligation = reconstruct_alu_obligation(&inst).expect("AddRI must reconstruct");
    assert!(obligation.is_reconstructed());
    // Only the register source is a declared input; the immediate is a constant.
    assert_eq!(obligation.inputs.len(), 1);
    assert_eq!(obligation.inputs[0].1, 64);
    assert!(matches!(
        verify_by_evaluation(&obligation),
        VerificationResult::Valid
    ));
}

#[test]
fn neg_reconstructs_unary_and_is_valid() {
    let inst = MachInst::new(AArch64Opcode::Neg, vec![vreg32(0), vreg32(1)]);
    let obligation = reconstruct_alu_obligation(&inst).expect("Neg must reconstruct");
    match &obligation.machine_side_provenance {
        MachineSideProvenance::Reconstructed { from_opcode, arity } => {
            assert_eq!(from_opcode, "Neg");
            assert_eq!(*arity, 1);
        }
        other => panic!("expected Reconstructed, got {other:?}"),
    }
    assert!(matches!(
        verify_by_evaluation(&obligation),
        VerificationResult::Valid
    ));
}

// ---------------------------------------------------------------------------
// (b) Inject SUB where Iadd was intended -> REFUTES
// ---------------------------------------------------------------------------

#[test]
fn injected_sub_for_intended_iadd_refutes() {
    // Model the defect: the source IR op is Iadd, but isel emitted SUB. The
    // reconstruction builds the machine side from the REAL (SUB) opcode while the
    // source side is the intended Iadd — over the SAME shared symbols.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);

    let trust_ir_expr = encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a.clone(), b.clone()); // bvadd
    let aarch64_expr = encode_sub_rr(OperandSize::S32, a, b); // bvsub  <-- WRONG opcode

    let buggy = ProofObligation {
        name: "RECONSTRUCTED Iadd -> SubRR (INJECTED isel bug)".to_string(),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "SubRR".to_string(),
            arity: 2,
        },
    };

    // The reconstructed obligation REFUTES: bvadd != bvsub for some inputs.
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "SUB-for-Iadd must REFUTE (this is the content of reconstruction)"
    );
    // It is genuinely distinct — NOT a vacuous X==X.
    assert!(buggy.is_genuinely_proven());
}

// ---------------------------------------------------------------------------
// (c) Wrong operand wiring on a non-commutative SUB -> REFUTES
// ---------------------------------------------------------------------------

#[test]
fn injected_swapped_operands_on_sub_refutes() {
    // SUB is non-commutative: `a - b != b - a` in general. Model an isel that
    // wired the SubRR source operands in the WRONG order. The source side is the
    // intended `Isub(a, b)`; the machine side is the REAL SUB but with the
    // operands swapped (`b - a`).
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);

    let trust_ir_expr = encode_trust_ir_binop(&Opcode::Isub, Type::I32, a.clone(), b.clone()); // a - b
    // WRONG wiring: rn=b, rm=a  ->  b - a
    let aarch64_expr = encode_sub_rr(OperandSize::S32, b, a);

    let buggy = ProofObligation {
        name: "RECONSTRUCTED Isub -> SubRR (INJECTED swapped wiring)".to_string(),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "SubRR".to_string(),
            arity: 2,
        },
    };

    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped SUB wiring must REFUTE (the non-commutative wiring discriminator)"
    );
}

#[test]
fn commutative_add_cannot_catch_operand_swap_by_design() {
    // CONTRAST (documents the known, correct limitation): ADD is commutative, so
    // a swapped-operand ADD still proves Valid. This is why the non-commutative
    // SUB is the operand-wiring discriminator. Stated explicitly so nobody reads
    // the passing ADD-swap as a soundness hole.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let trust_ir_expr = encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a.clone(), b.clone()); // a + b
    let aarch64_expr = encode_add_rr(OperandSize::S32, b, a); // b + a  (swapped)
    let swapped_add = ProofObligation {
        name: "RECONSTRUCTED Iadd -> AddRR (swapped, still valid: commutative)".to_string(),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "AddRR".to_string(),
            arity: 2,
        },
    };
    assert!(matches!(
        verify_by_evaluation(&swapped_add),
        VerificationResult::Valid
    ));
}

// ===========================================================================
// EXTENDED FAMILIES (task #63 Phase-2 extension): bitwise / extends / shifts
// ===========================================================================
//
// Each family proves: (a) a correct lowering reconstructs to Valid with
// Reconstructed provenance; (b) a WRONG opcode refutes; and for NON-COMMUTATIVE
// families (Bic/Orn/Sub/shifts) a WRONG WIRING refutes. Commutative families
// (And/Orr/Eor like Add/Mul) cannot catch an operand swap — documented.

// ---- BITWISE: commutative And / Orr / Eor ----

#[test]
fn and_orr_eor_reconstruct_valid_with_reconstructed_provenance() {
    for (opcode, name) in [
        (AArch64Opcode::AndRR, "AndRR"),
        (AArch64Opcode::OrrRR, "OrrRR"),
        (AArch64Opcode::EorRR, "EorRR"),
    ] {
        let inst = MachInst::new(opcode, vec![vreg32(0), vreg32(1), vreg32(2)]);
        let ob =
            reconstruct_alu_obligation(&inst).unwrap_or_else(|| panic!("{name} must reconstruct"));
        assert!(ob.is_reconstructed(), "{name} must be Reconstructed");
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{name} correct lowering must be Valid"
        );
    }
}

#[test]
fn injected_orr_for_intended_band_refutes() {
    // isel emitted ORR where Band was intended: bvand vs bvor ⇒ REFUTE.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED Band -> OrrRR (INJECTED isel bug)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_orr_rr(OperandSize::S32, a, b), // WRONG: bvor
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "OrrRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "ORR-for-Band must REFUTE (bvand != bvor)"
    );
    assert!(buggy.is_genuinely_proven());
}

#[test]
fn injected_and_for_intended_bxor_refutes() {
    // isel emitted AND where Bxor was intended: bvxor vs bvand ⇒ REFUTE.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED Bxor -> AndRR (INJECTED isel bug)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Bxor,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_and_rr(OperandSize::S32, a, b), // WRONG: bvand
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "AndRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "AND-for-Bxor must REFUTE (bvxor != bvand)"
    );
}

#[test]
fn commutative_bitwise_cannot_catch_operand_swap_by_design() {
    // DOCUMENTED LIMITATION: And/Orr/Eor are commutative, so a swapped-operand
    // lowering still proves Valid — exactly like the commutative ADD. The
    // non-commutative Bic/Orn (below) are the wiring discriminators for bitwise.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let swapped = ProofObligation {
        name: "RECONSTRUCTED Band -> AndRR (swapped, still valid: commutative)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_and_rr(OperandSize::S32, b, a), // swapped
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "AndRR".to_string(),
            arity: 2,
        },
    };
    assert!(matches!(
        verify_by_evaluation(&swapped),
        VerificationResult::Valid
    ));
}

// ---- BITWISE: non-commutative Bic / Orn ----

#[test]
fn bic_and_orn_reconstruct_valid() {
    for (opcode, name) in [
        (AArch64Opcode::BicRR, "BicRR"),
        (AArch64Opcode::OrnRR, "OrnRR"),
    ] {
        let inst = MachInst::new(opcode, vec![vreg32(0), vreg32(1), vreg32(2)]);
        let ob =
            reconstruct_alu_obligation(&inst).unwrap_or_else(|| panic!("{name} must reconstruct"));
        assert!(ob.is_reconstructed());
        assert!(matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Valid
        ));
    }
}

#[test]
fn injected_wrong_opcode_for_bic_refutes() {
    // isel emitted AND (no complement) where BandNot was intended:
    // (a & b) vs (a & ~b) ⇒ REFUTE.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED BandNot -> AndRR (INJECTED isel bug)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BandNot,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_and_rr(OperandSize::S32, a, b), // WRONG: no complement
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "AndRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "AND-for-BandNot must REFUTE (a & b != a & ~b)"
    );
}

#[test]
fn injected_swapped_operands_on_bic_refutes() {
    // BIC is non-commutative (a & ~b != b & ~a). Wrong wiring ⇒ REFUTE.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED BandNot -> BicRR (INJECTED swapped wiring)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BandNot,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_bic_rr(OperandSize::S32, b, a), // WRONG wiring: b & ~a
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "BicRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped BIC wiring must REFUTE (a & ~b != b & ~a)"
    );
}

#[test]
fn injected_swapped_operands_on_orn_refutes() {
    // ORN is non-commutative (a | ~b != b | ~a). Wrong wiring ⇒ REFUTE.
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED BorNot -> OrnRR (INJECTED swapped wiring)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BorNot,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_orn_rr(OperandSize::S32, b, a), // WRONG wiring: b | ~a
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "OrnRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped ORN wiring must REFUTE (a | ~b != b | ~a)"
    );
}

// ---- MVN (Bnot) via ORN with zero register ----

#[test]
fn orn_with_zero_register_reconstructs_as_bnot() {
    // `ORN Rd, WZR, Rm` is the MVN alias = ~Rm. The reconstructor recognizes the
    // zero rn slot and builds the UNARY Bnot semantics (one source input).
    let inst = MachInst::new(
        AArch64Opcode::OrnRR,
        vec![vreg32(0), MachOperand::Special(SpecialReg::WZR), vreg32(2)],
    );
    let ob = reconstruct_alu_obligation(&inst).expect("ORN-as-MVN must reconstruct");
    assert!(ob.is_reconstructed());
    assert!(ob.name.contains("Bnot"), "must model Bnot, got {}", ob.name);
    assert_eq!(ob.inputs.len(), 1, "MVN is unary — one source input");
    match &ob.machine_side_provenance {
        MachineSideProvenance::Reconstructed { arity, .. } => {
            assert_eq!(*arity, 1, "MVN reconstructs with unary arity")
        }
        other => panic!("expected Reconstructed, got {other:?}"),
    }
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

// ---- EXTENDS: Sxt* / Uxt* (unary, width-changing) ----

#[test]
fn sxt_and_uxt_reconstruct_valid() {
    for (opcode, name) in [
        (AArch64Opcode::Sxtb, "Sxtb"),
        (AArch64Opcode::Sxth, "Sxth"),
        (AArch64Opcode::Uxtb, "Uxtb"),
        (AArch64Opcode::Uxth, "Uxth"),
    ] {
        let inst = MachInst::new(opcode, vec![vreg32(0), vreg32(1)]);
        let ob =
            reconstruct_alu_obligation(&inst).unwrap_or_else(|| panic!("{name} must reconstruct"));
        assert!(ob.is_reconstructed());
        assert!(matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Valid
        ));
    }
    // Sxtw/Uxtw widen W -> X.
    for (opcode, name) in [(AArch64Opcode::Sxtw, "Sxtw"), (AArch64Opcode::Uxtw, "Uxtw")] {
        let inst = MachInst::new(opcode, vec![vreg64(0), vreg32(1)]);
        let ob =
            reconstruct_alu_obligation(&inst).unwrap_or_else(|| panic!("{name} must reconstruct"));
        assert!(ob.is_reconstructed());
        assert!(matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Valid
        ));
    }
}

#[test]
fn injected_uxt_for_intended_sextend_refutes() {
    // isel emitted UXTB (zero-extend) where a Sextend (sign-extend) was intended.
    // For a source with bit 7 set, sign vs zero extension differ ⇒ REFUTE.
    let a = SmtExpr::var("recon_src", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED Sextend_8_to_32 -> Uxtb (INJECTED isel bug)".to_string(),
        trust_ir_expr: encode_trust_ir_sextend(8, 32, a.clone()), // sign-extend
        aarch64_expr: encode_uxt(8, 32, a),                       // WRONG: zero-extend
        inputs: vec![("recon_src".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Uxtb".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "UXT-for-Sextend must REFUTE (sign != zero extension for a negative byte)"
    );
    assert!(buggy.is_genuinely_proven());
}

// ---- SHIFTS: Lsl / Lsr / Asr (resolve #57 — load-bearing precondition) ----

#[test]
fn shifts_reconstruct_valid_with_loadbearing_precondition() {
    for (opcode, name) in [
        (AArch64Opcode::LslRR, "LslRR"),
        (AArch64Opcode::LsrRR, "LsrRR"),
        (AArch64Opcode::AsrRR, "AsrRR"),
    ] {
        let inst = MachInst::new(opcode, vec![vreg32(0), vreg32(1), vreg32(2)]);
        let ob =
            reconstruct_alu_obligation(&inst).unwrap_or_else(|| panic!("{name} must reconstruct"));
        assert!(ob.is_reconstructed());
        assert_eq!(
            ob.preconditions.len(),
            1,
            "{name} must carry the load-bearing amount<width precondition (#57)"
        );
        assert!(matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Valid
        ));
    }
}

#[test]
fn shift_precondition_is_load_bearing_strip_it_and_it_refutes() {
    // #57: the amount<width precondition is GENUINELY load-bearing, not cosmetic.
    // At width 8 (exhaustive path), with the precondition the in-range equivalence
    // is Valid; WITHOUT it, a shift by exactly width (8 & 7 == 0 on hardware vs
    // clamp-to-0 in the in-house SMT) is a counterexample ⇒ stripping it REFUTES.
    let a = SmtExpr::var("recon_src1", 8);
    let amt = SmtExpr::var("recon_src2", 8);
    let mk = |pre: Vec<SmtExpr>| ProofObligation {
        name: "shift8 load-bearing demo".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_lsl_rr_masked(OperandSize::S32, a.clone(), amt.clone()),
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: pre,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "LslRR".to_string(),
            arity: 2,
        },
    };
    let with_pre = mk(vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))]);
    let without_pre = mk(vec![]);
    assert!(
        matches!(verify_by_evaluation(&with_pre), VerificationResult::Valid),
        "WITH amount<width precondition: in-range equivalence is Valid"
    );
    assert!(
        matches!(
            verify_by_evaluation(&without_pre),
            VerificationResult::Invalid { .. }
        ),
        "WITHOUT the precondition the shift-by-width case REFUTES — load-bearing (#57)"
    );
}

#[test]
fn injected_lsr_for_intended_ishl_refutes() {
    // isel emitted LSR (logical shift right) where Ishl (shift left) was intended:
    // bvshl vs bvlshr ⇒ REFUTE.
    let a = SmtExpr::var("recon_src1", 8);
    let amt = SmtExpr::var("recon_src2", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED Ishl -> LsrRR (INJECTED wrong shift opcode)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_lsr_rr_masked(OperandSize::S32, a.clone(), amt.clone()), // WRONG
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "LsrRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "LSR-for-Ishl must REFUTE (bvshl != bvlshr) even WITH the in-range precondition"
    );
}

#[test]
fn injected_swapped_operands_on_shift_refutes() {
    // A shift is non-commutative in its operands: `value << amount` !=
    // `amount << value` in general. Wrong wiring ⇒ REFUTE (in range).
    let a = SmtExpr::var("recon_src1", 8);
    let amt = SmtExpr::var("recon_src2", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED Ishl -> LslRR (INJECTED swapped wiring)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        // WRONG wiring: amount as the value, value as the amount.
        aarch64_expr: encode_lsl_rr_masked(OperandSize::S32, amt.clone(), a.clone()),
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: vec![
            amt.clone().bvult(SmtExpr::bv_const(8, 8)),
            a.clone().bvult(SmtExpr::bv_const(8, 8)),
        ],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "LslRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped shift wiring must REFUTE (value<<amt != amt<<value)"
    );
}

// ---------------------------------------------------------------------------
// (d) Anti-f81e45b: the reconstructed path does NO name.contains lookup
// ---------------------------------------------------------------------------

#[test]
fn reconstructed_path_does_no_name_contains_lookup() {
    // The source code of the reconstruction module must not perform a
    // `name.contains` / `name.to_lowercase().contains` lookup to bind the source
    // op or the machine encoder — the binding is a TYPED, EXHAUSTIVE opcode match
    // (`opcode_to_source_op`) plus a TYPED positional operand schema. We assert
    // this structurally over the source span of the reconstruction code.
    let src = include_str!("../src/function_verifier.rs");

    // Extract the reconstruction span: from the pilot section header to the
    // FunctionVerifier section header that follows it.
    let start = src
        .find("// Phase-2 operand reconstruction (PILOT")
        .expect("reconstruction section header present");
    let end_marker = "// FunctionVerifier\n// -----";
    let end = src[start..]
        .find(end_marker)
        .map(|o| start + o)
        .expect("FunctionVerifier section header follows reconstruction");
    let recon_src = &src[start..end];

    assert!(
        !recon_src.contains(".contains("),
        "the reconstruction path must NOT use any .contains() name lookup \
         (anti-f81e45b): the opcode->source-op binding is a typed exhaustive match"
    );
    // And, positively, it DOES use the typed exhaustive matcher.
    assert!(
        recon_src.contains("fn opcode_to_source_op("),
        "reconstruction must resolve the source op via the typed matcher"
    );
}

#[test]
fn non_reconstructable_opcode_does_not_reconstruct() {
    // A NON-reconstructable opcode (e.g. MovR — register copy is not in
    // opcode_to_source_op) returns None: reconstruction is scoped to the
    // reconstructable families, and everything else keeps its existing
    // DB-substring / fail-closed-allowlist path unchanged.
    //
    // (NOTE: SDIV/UDIV/Madd/Msub and the FP families USED to be examples here,
    // but they are now reconstructable via the FP/div/madd extension — this test
    // tracks an opcode that remains genuinely OUTSIDE the reconstructable set.)
    let inst = MachInst::new(AArch64Opcode::MovR, vec![vreg32(0), vreg32(1)]);
    assert!(reconstruct_alu_obligation(&inst).is_none());
    // A branch is likewise not reconstructable (no value-equivalence obligation).
    let br = MachInst::new(AArch64Opcode::B, vec![]);
    assert!(reconstruct_alu_obligation(&br).is_none());
}

#[test]
fn malformed_pilot_operand_shape_fails_closed() {
    // A pilot opcode whose operand shape does not match the typed schema (here:
    // an operand-less AddRR stub) does NOT reconstruct — it returns None so the
    // caller can fall through, and is never silently credited as reconstructed.
    let inst = MachInst::new(AArch64Opcode::AddRR, vec![]);
    assert!(reconstruct_alu_obligation(&inst).is_none());

    // Width mismatch between dst and a source register also fails closed.
    let mixed = MachInst::new(AArch64Opcode::AddRR, vec![vreg32(0), vreg64(1), vreg32(2)]);
    assert!(reconstruct_alu_obligation(&mixed).is_none());
}
