// trust-cg-verify/tests/reconstruction_riscv.rs — Phase-2 operand-reconstruction
// refutation suite (RISC-V RV64 integer ALU/shift/compare), task #63.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// MIRROR of tests/reconstruction_alu.rs (AArch64). These tests are the PROOF
// THAT THE MECHANISM HAS CONTENT for RISC-V. The static RISC-V lowering proofs
// build BOTH sides of an obligation from the SAME symbolic vars, so they are
// structurally X==X and the strict gate (#61) credits them ZERO — a wrong isel
// choice could never refute them. The reconstruction path rebuilds the MACHINE
// side from the REAL emitted opcode+operands, so:
//
//   (a) a correct ADD reconstructs to bvadd==bvadd and is credited GENUINELY
//       (provenance Reconstructed), even though the two sides happen to be equal;
//   (b) injecting a wrong opcode (Add-as-Sub, Sll-as-Srl) ⇒ REFUTE;
//   (c) wiring a non-commutative op (Sub, shifts, Slt/Sltu) with swapped source
//       operands ⇒ REFUTE; commutative families (Add/Mul/And/Or/Xor) cannot catch
//       an operand swap — documented;
//   (d) the reconstructed path performs NO `name.contains` lookup (anti-f81e45b);
//   (e) the shift `amount < width` precondition is LOAD-BEARING (#57): strip it
//       and a shift by exactly width REFUTES.
//
// (b)/(c) construct the BUGGY obligation with the very same public encoders the
// reconstructor uses internally — `encode_trust_ir_*` for the source side and
// `encode_<riscv op>` for the machine side — so they test the exact source-vs-
// machine comparison the mechanism performs.

use trust_cg_ir::{RegClass, RiscVOpcode, VReg};

use trust_cg_verify::lowering_proof::MachineSideProvenance;
use trust_cg_verify::riscv_semantics::{
    RiscVOperandSize, encode_add, encode_and, encode_sll_masked, encode_slt, encode_sltu,
    encode_srl_masked, encode_sub,
};
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::trust_ir_semantics::{
    encode_trust_ir_binop, encode_trust_ir_bitwise_binop, encode_trust_ir_icmp,
    encode_trust_ir_shift,
};
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::{
    ProofObligation, RiscVISelInst, RiscVISelOperand, reconstruct_riscv_alu_obligation,
    representative_riscv_reconstructable_inst, verify_by_evaluation,
};

use trust_cg_lower::instructions::{IntCC, Opcode};
use trust_cg_lower::types::Type;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn x(id: u32) -> RiscVISelOperand {
    RiscVISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn rr(opcode: RiscVOpcode) -> RiscVISelInst {
    RiscVISelInst::with_operands(opcode, vec![x(0), x(1), x(2)])
}

const S: RiscVOperandSize = RiscVOperandSize::S64;

// ---------------------------------------------------------------------------
// (a) Correct reconstruction: Valid + Reconstructed provenance + genuine
// ---------------------------------------------------------------------------

#[test]
fn all_fourteen_alu_opcodes_reconstruct_valid_with_reconstructed_provenance() {
    for op in [
        RiscVOpcode::Add,
        RiscVOpcode::Sub,
        RiscVOpcode::Mul,
        RiscVOpcode::And,
        RiscVOpcode::Or,
        RiscVOpcode::Xor,
        RiscVOpcode::Sll,
        RiscVOpcode::Srl,
        RiscVOpcode::Sra,
        RiscVOpcode::Slli,
        RiscVOpcode::Srli,
        RiscVOpcode::Addi,
        RiscVOpcode::Slt,
        RiscVOpcode::Sltu,
    ] {
        // Slli/Srli/Addi use the immediate form ([rd, rs1, imm]); the generic
        // representative wires [rd, rs1, rs2] which is also valid (rs2 register).
        let inst = representative_riscv_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must have a representative"));
        let ob = reconstruct_riscv_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(ob.is_reconstructed(), "{op:?} must be Reconstructed");
        match &ob.machine_side_provenance {
            MachineSideProvenance::Reconstructed { from_opcode, arity } => {
                assert_eq!(from_opcode, &format!("{op:?}"));
                assert_eq!(*arity, 2);
            }
            other => panic!("{op:?} expected Reconstructed, got {other:?}"),
        }
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{op:?} correct lowering must be Valid"
        );
    }
}

#[test]
fn addi_immediate_form_binds_imm_as_constant() {
    // `ADDI rd, rs1, #7` — the I-type immediate binds to a bv_const, not an input.
    let inst = RiscVISelInst::with_operands(
        RiscVOpcode::Addi,
        vec![x(0), x(1), RiscVISelOperand::Imm(7)],
    );
    let ob = reconstruct_riscv_alu_obligation(&inst).expect("ADDI must reconstruct");
    assert!(ob.is_reconstructed());
    assert_eq!(
        ob.inputs.len(),
        1,
        "only the rs1 register is a declared input"
    );
    assert_eq!(ob.inputs[0].1, 64);
    assert!(matches!(
        verify_by_evaluation(&ob),
        VerificationResult::Valid
    ));
}

#[test]
fn slli_immediate_shift_amount_reconstructs_valid() {
    // SLLI rd, rs1, shamt — the shamt is an immediate amount; masked machine side
    // + load-bearing precondition (the const amount < width is trivially Valid).
    let inst = RiscVISelInst::with_operands(
        RiscVOpcode::Slli,
        vec![x(0), x(1), RiscVISelOperand::Imm(3)],
    );
    let ob = reconstruct_riscv_alu_obligation(&inst).expect("SLLI must reconstruct");
    assert!(ob.is_reconstructed());
    assert_eq!(
        ob.preconditions.len(),
        1,
        "shift must carry the load-bearing amount<width precondition"
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
        inputs: vec![("recon_rs1".to_string(), 64), ("recon_rs2".to_string(), 64)],
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
    let a = SmtExpr::var("recon_rs1", 64);
    let b = SmtExpr::var("recon_rs2", 64);
    let buggy = buggy_binary(
        "RECONSTRUCTED riscv Iadd -> Sub (INJECTED isel bug)",
        "Sub",
        encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), b.clone()),
        encode_sub(S, a, b), // WRONG opcode
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
    let a = SmtExpr::var("recon_rs1", 64);
    let b = SmtExpr::var("recon_rs2", 64);
    let buggy = buggy_binary(
        "RECONSTRUCTED riscv Bxor -> And (INJECTED isel bug)",
        "And",
        encode_trust_ir_bitwise_binop(&Opcode::Bxor, Type::I64, a.clone(), b.clone()),
        encode_and(S, a, b), // WRONG opcode
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
fn injected_srl_for_intended_ishl_refutes() {
    // SHIFT family: isel emitted SRL (logical right) where Ishl (left) was
    // intended ⇒ bvshl != bvlshr. Refutes EVEN WITH the in-range precondition.
    let a = SmtExpr::var("recon_rs1", 8);
    let amt = SmtExpr::var("recon_rs2", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED riscv Ishl -> Srl (INJECTED wrong shift opcode)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_srl_masked(S, a.clone(), amt.clone()), // WRONG: bvlshr
        inputs: vec![("recon_rs1".to_string(), 8), ("recon_rs2".to_string(), 8)],
        preconditions: vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Srl".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "SRL-for-Ishl must REFUTE (bvshl != bvlshr) even WITH the in-range precondition"
    );
}

#[test]
fn injected_sltu_for_intended_signed_slt_refutes() {
    // COMPARE family: isel emitted SLTU (unsigned) where Slt (signed) was intended.
    // For -1 vs 0: signed -1 < 0 is TRUE (1), unsigned 0xFFFF.. < 0 is FALSE (0).
    let a = SmtExpr::var("recon_rs1", 64);
    let b = SmtExpr::var("recon_rs2", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED riscv Icmp_SignedLessThan -> Sltu (INJECTED isel bug)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_sltu(S, a, b), // WRONG: unsigned compare
        inputs: vec![("recon_rs1".to_string(), 64), ("recon_rs2".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Sltu".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "SLTU-for-signed-SLT must REFUTE (signed vs unsigned differ for negatives)"
    );
    assert!(buggy.is_genuinely_proven());
}

// ---------------------------------------------------------------------------
// (c) Wrong-wiring refute for NON-commutative ops (Sub, shifts, Slt/Sltu)
// ---------------------------------------------------------------------------

#[test]
fn injected_swapped_operands_on_sub_refutes() {
    // SUB is non-commutative: a - b != b - a in general.
    let a = SmtExpr::var("recon_rs1", 64);
    let b = SmtExpr::var("recon_rs2", 64);
    let buggy = buggy_binary(
        "RECONSTRUCTED riscv Isub -> Sub (INJECTED swapped wiring)",
        "Sub",
        encode_trust_ir_binop(&Opcode::Isub, Type::I64, a.clone(), b.clone()), // a - b
        encode_sub(S, b, a),                                                   // WRONG: b - a
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
    // A shift is non-commutative in its operands: value << amount != amount <<
    // value in general. Wrong wiring ⇒ REFUTE (in range).
    let a = SmtExpr::var("recon_rs1", 8);
    let amt = SmtExpr::var("recon_rs2", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED riscv Ishl -> Sll (INJECTED swapped wiring)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        // WRONG wiring: amount as the value, value as the amount.
        aarch64_expr: encode_sll_masked(S, amt.clone(), a.clone()),
        inputs: vec![("recon_rs1".to_string(), 8), ("recon_rs2".to_string(), 8)],
        preconditions: vec![
            amt.clone().bvult(SmtExpr::bv_const(8, 8)),
            a.clone().bvult(SmtExpr::bv_const(8, 8)),
        ],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Sll".to_string(),
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

#[test]
fn injected_swapped_operands_on_slt_refutes() {
    // SLT is non-commutative: (a < b) != (b < a) in general.
    let a = SmtExpr::var("recon_rs1", 64);
    let b = SmtExpr::var("recon_rs2", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED riscv Icmp_SLT -> Slt (INJECTED swapped wiring)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_slt(S, b, a), // WRONG wiring: b < a
        inputs: vec![("recon_rs1".to_string(), 64), ("recon_rs2".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Slt".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped SLT wiring must REFUTE ((a<b) != (b<a))"
    );
}

// ---------------------------------------------------------------------------
// Commutative families cannot catch an operand swap — DOCUMENTED limitation
// ---------------------------------------------------------------------------

#[test]
fn commutative_families_cannot_catch_operand_swap_by_design() {
    // DOCUMENTED LIMITATION: Add/Mul/And/Or/Xor are commutative, so a swapped-
    // operand lowering still proves Valid — exactly like the AArch64 commutative
    // ADD. The non-commutative Sub/shifts/Slt (above) are the wiring
    // discriminators. Stated explicitly so nobody reads the passing swap as a
    // soundness hole.
    let a = SmtExpr::var("recon_rs1", 64);
    let b = SmtExpr::var("recon_rs2", 64);

    // Add (swapped): a + b == b + a.
    let add_swapped = buggy_binary(
        "RECONSTRUCTED riscv Iadd -> Add (swapped, still valid: commutative)",
        "Add",
        encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), b.clone()),
        encode_add(S, b.clone(), a.clone()),
    );
    assert!(matches!(
        verify_by_evaluation(&add_swapped),
        VerificationResult::Valid
    ));

    // And (swapped): a & b == b & a.
    let and_swapped = buggy_binary(
        "RECONSTRUCTED riscv Band -> And (swapped, still valid: commutative)",
        "And",
        encode_trust_ir_bitwise_binop(&Opcode::Band, Type::I64, a.clone(), b.clone()),
        encode_and(S, b, a),
    );
    assert!(matches!(
        verify_by_evaluation(&and_swapped),
        VerificationResult::Valid
    ));
}

// ---------------------------------------------------------------------------
// (e) The shift amount<width precondition is LOAD-BEARING (#57)
// ---------------------------------------------------------------------------

#[test]
fn shift_precondition_is_load_bearing_strip_it_and_it_refutes() {
    // #57: the amount<width precondition is GENUINELY load-bearing, not cosmetic.
    // At width 8 (exhaustive), WITH the precondition the in-range equivalence is
    // Valid; WITHOUT it, a shift by exactly width (8 & 7 == 0 on hardware mask vs
    // clamp-to-0 in the in-house SMT bvshl) is a counterexample ⇒ stripping it
    // REFUTES. The machine side is the FAITHFUL hardware-amount-masked encoder.
    let a = SmtExpr::var("recon_rs1", 8);
    let amt = SmtExpr::var("recon_rs2", 8);
    let mk = |pre: Vec<SmtExpr>| ProofObligation {
        name: "riscv shift8 load-bearing demo".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_sll_masked(S, a.clone(), amt.clone()),
        inputs: vec![("recon_rs1".to_string(), 8), ("recon_rs2".to_string(), 8)],
        preconditions: pre,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Sll".to_string(),
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

// ---------------------------------------------------------------------------
// (d) Anti-f81e45b: the reconstructed path does NO name.contains lookup
// ---------------------------------------------------------------------------

#[test]
fn reconstructed_path_does_no_name_contains_lookup() {
    // The source span of the RISC-V reconstruction module must not perform a
    // `name.contains` lookup to bind the source op or the machine encoder — the
    // binding is a TYPED, EXHAUSTIVE opcode match (`opcode_to_source_op`) plus a
    // TYPED positional operand schema. Asserted structurally over the source span.
    let src = include_str!("../src/riscv_function_verifier.rs");

    let start = src
        .find("// Phase-2 operand reconstruction (RISC-V ALU)")
        .expect("reconstruction section header present");
    let end_marker = "// RiscVFunctionVerifier";
    let end = src[start..]
        .find(end_marker)
        .map(|o| start + o)
        .expect("RiscVFunctionVerifier section header follows reconstruction");
    let recon_src = &src[start..end];

    assert!(
        !recon_src.contains(".contains("),
        "the RISC-V reconstruction path must NOT use any .contains() name lookup \
         (anti-f81e45b): the opcode->source-op binding is a typed exhaustive match"
    );
    assert!(
        recon_src.contains("fn opcode_to_source_op("),
        "reconstruction must resolve the source op via the typed matcher"
    );
}

// ---------------------------------------------------------------------------
// Fail-closed: non-reconstructable opcodes and malformed shapes
// ---------------------------------------------------------------------------

#[test]
fn non_reconstructable_opcode_does_not_reconstruct() {
    // A NON-reconstructable opcode (e.g. DIV — not in opcode_to_source_op) returns
    // None: reconstruction is scoped to the 14 ALU/shift/compare ops; everything
    // else keeps its existing DB-substring path.
    let inst = rr(RiscVOpcode::Div);
    assert!(reconstruct_riscv_alu_obligation(&inst).is_none());
    // A branch likewise is not reconstructable.
    let bne = rr(RiscVOpcode::Bne);
    assert!(reconstruct_riscv_alu_obligation(&bne).is_none());
}

#[test]
fn malformed_operand_shape_fails_closed() {
    // A reconstructable opcode whose operand shape does not match the typed schema
    // (here: an operand-less ADD stub) does NOT reconstruct — returns None so the
    // caller can fall through; never silently credited as reconstructed.
    let stub = RiscVISelInst::new(RiscVOpcode::Add);
    assert!(reconstruct_riscv_alu_obligation(&stub).is_none());

    // Wrong arity (only 2 operands) also fails closed.
    let two = RiscVISelInst::with_operands(RiscVOpcode::Add, vec![x(0), x(1)]);
    assert!(reconstruct_riscv_alu_obligation(&two).is_none());
}
