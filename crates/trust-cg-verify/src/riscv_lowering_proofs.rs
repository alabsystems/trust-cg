// trust-cg-verify/riscv_lowering_proofs.rs - RISC-V (RV64) lowering rule proof obligations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Defines proof obligations for trust_ir -> RISC-V (RV64) lowering rules and
// verifies semantic equivalence using the same ProofObligation framework as
// AArch64 and x86-64.
//
// Each proof obligation pairs:
//   - trust_ir instruction semantics (from trust_ir_semantics module) — the SPEC
//   - RISC-V instruction semantics (from riscv_semantics module)     — the MACHINE
//
// and asserts: forall inputs (under preconditions): trust_ir_result == riscv_result
//
// HONESTY POLICY (non-negotiable, see riscv_semantics.rs header):
//
//   * The machine side (the `aarch64_expr` field, reused as the generic machine
//     side here exactly as x86-64 does — DO NOT rename it) is ALWAYS built from
//     `riscv_semantics::encode_*`, authored independently from the trust_ir spec.
//   * 1:1 single-instruction lowerings (Iadd->ADD, ... Ushr->SRL) have no
//     static obligation here: spec and machine side would build the same
//     bitvector op, a degenerate X==X identity (#62 retraction). Those opcodes
//     are credited by riscv_function_verifier's operand reconstruction instead.
//   * For the comparison IDIOMS (Icmp Eq/Ne/Sge/Sgt/Sle/Uge/Ugt/Ule) the machine
//     side models the FULL emitted multi-instruction RISC-V sequence (SUB+SLTIU,
//     SUB+SLTU, SLT+XORI, swapped SLT, ...), which is genuinely DISTINCT from the
//     trust_ir spec's single `bvslt`/`bvult`/`eq` predicate. The gate tests
//     assert_ne the two sides for these idiom families.
//
// Reference: RISC-V Unprivileged ISA Specification (Volume 1, Version 20191213)
// Reference: crates/trust-cg-codegen/src/riscv/ (ISel rules being verified)

//! Proof obligations for RISC-V (RV64) lowering rule verification.
//!
//! Mirrors [`crate::x86_64_lowering_proofs`] but targets RISC-V instruction
//! semantics from [`crate::riscv_semantics`]. Each proof function constructs a
//! [`ProofObligation`] verifiable by evaluation or SMT solving.

use crate::lowering_proof::ProofObligation;
use crate::riscv_semantics::{
    RiscVOperandSize, encode_slt, encode_sltiu, encode_sltu, encode_sub, encode_xori,
};
use crate::smt::SmtExpr;

const I64_W: u32 = 64;
const CAT: crate::lowering_proof::TransvalCheckKind =
    crate::lowering_proof::TransvalCheckKind::InstructionLowering;

fn ab64() -> (SmtExpr, SmtExpr) {
    (SmtExpr::var("a", I64_W), SmtExpr::var("b", I64_W))
}

fn ab_inputs() -> Vec<(String, u32)> {
    vec![("a".to_string(), I64_W), ("b".to_string(), I64_W)]
}

// ===========================================================================
// Comparison IDIOMS (i64): genuinely non-degenerate composed sequences
//
// The machine side models the FULL emitted RISC-V instruction sequence, which
// is structurally distinct from the trust_ir spec predicate. The gate
// asserts_ne the two sides for these families.
// ===========================================================================

/// Proof: `trust_ir::Icmp(Equal, I64, a, b) -> RISC-V [SUB t,a,b; SLTIU rd,t,1]`.
///
/// `SLTIU(a-b, 1)` is the "seqz" idiom: `(a-b) <u 1` iff `a-b == 0` iff `a == b`.
/// Machine side: `encode_sltiu(encode_sub(a,b), 1)` — NOT the spec's `eq(a,b)`.
pub fn proof_riscv_icmp_eq_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    let t = encode_sub(RiscVOperandSize::S64, a.clone(), b.clone());
    let one = SmtExpr::bv_const(1, I64_W);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_EQ_I64 -> SUB+SLTIU(t,1)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::Equal, Type::I64, a, b),
        aarch64_expr: encode_sltiu(RiscVOperandSize::S64, t, one),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Icmp(NotEqual, I64, a, b) -> RISC-V [SUB t,a,b; SLTU rd,x0,t]`.
///
/// `SLTU(0, a-b)` is the "snez" idiom: `0 <u (a-b)` iff `a-b != 0` iff `a != b`.
/// Machine side: `encode_sltu(0, encode_sub(a,b))` — NOT the spec's `!eq(a,b)`.
pub fn proof_riscv_icmp_ne_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    let t = encode_sub(RiscVOperandSize::S64, a.clone(), b.clone());
    let zero = SmtExpr::bv_const(0, I64_W);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_NE_I64 -> SUB+SLTU(x0,t)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::NotEqual, Type::I64, a, b),
        aarch64_expr: encode_sltu(RiscVOperandSize::S64, zero, t),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Icmp(SignedGreaterThanOrEqual, I64, a, b) ->
///         RISC-V [SLT t,a,b; XORI rd,t,1]`.
///
/// `a >=s b` iff NOT `a <s b`; the boolean is inverted with `XORI t, 1`.
/// Machine side: `encode_xori(encode_slt(a,b), 1)` — NOT the spec's `bvsge`.
pub fn proof_riscv_icmp_sge_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    let slt = encode_slt(RiscVOperandSize::S64, a.clone(), b.clone());
    let one = SmtExpr::bv_const(1, 1);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_SGE_I64 -> SLT+XORI(t,1)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::SignedGreaterThanOrEqual, Type::I64, a, b),
        aarch64_expr: encode_xori(RiscVOperandSize::S64, slt, one),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Icmp(SignedGreaterThan, I64, a, b) -> RISC-V SLT rd, b, a`.
///
/// `a >s b` iff `b <s a` — the operands are swapped into a single SLT.
/// Machine side: `encode_slt(b, a)` — operand-swapped, distinct from the spec's
/// `bvsgt(a, b)`.
pub fn proof_riscv_icmp_sgt_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_SGT_I64 -> SLT(b,a)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedGreaterThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_slt(RiscVOperandSize::S64, b, a),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Icmp(SignedLessThanOrEqual, I64, a, b) ->
///         RISC-V [SLT t,b,a; XORI rd,t,1]`.
///
/// `a <=s b` iff NOT `b <s a`. Machine side: `encode_xori(encode_slt(b,a), 1)`.
pub fn proof_riscv_icmp_sle_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    let slt = encode_slt(RiscVOperandSize::S64, b.clone(), a.clone());
    let one = SmtExpr::bv_const(1, 1);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_SLE_I64 -> SLT(b,a)+XORI(t,1)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::SignedLessThanOrEqual, Type::I64, a, b),
        aarch64_expr: encode_xori(RiscVOperandSize::S64, slt, one),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Icmp(UnsignedGreaterThanOrEqual, I64, a, b) ->
///         RISC-V [SLTU t,a,b; XORI rd,t,1]`.
///
/// `a >=u b` iff NOT `a <u b`. Machine side: `encode_xori(encode_sltu(a,b), 1)`.
pub fn proof_riscv_icmp_uge_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    let sltu = encode_sltu(RiscVOperandSize::S64, a.clone(), b.clone());
    let one = SmtExpr::bv_const(1, 1);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_UGE_I64 -> SLTU+XORI(t,1)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::UnsignedGreaterThanOrEqual, Type::I64, a, b),
        aarch64_expr: encode_xori(RiscVOperandSize::S64, sltu, one),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Icmp(UnsignedGreaterThan, I64, a, b) -> RISC-V SLTU rd, b, a`.
///
/// `a >u b` iff `b <u a`. Machine side: `encode_sltu(b, a)` (operand swap).
pub fn proof_riscv_icmp_ugt_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_UGT_I64 -> SLTU(b,a)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedGreaterThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_sltu(RiscVOperandSize::S64, b, a),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Icmp(UnsignedLessThanOrEqual, I64, a, b) ->
///         RISC-V [SLTU t,b,a; XORI rd,t,1]`.
///
/// `a <=u b` iff NOT `b <u a`. Machine side: `encode_xori(encode_sltu(b,a), 1)`.
pub fn proof_riscv_icmp_ule_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    let sltu = encode_sltu(RiscVOperandSize::S64, b.clone(), a.clone());
    let one = SmtExpr::bv_const(1, 1);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_ULE_I64 -> SLTU(b,a)+XORI(t,1)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::UnsignedLessThanOrEqual, Type::I64, a, b),
        aarch64_expr: encode_xori(RiscVOperandSize::S64, sltu, one),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// All RISC-V (RV64) lowering proof obligations: the comparison idioms.
pub fn all_riscv_proofs() -> Vec<ProofObligation> {
    // #62 retraction: static 1:1 "riscv: <op> -> <INSN>" ALU/shift/imm/cmp
    // obligations would be degenerate X==X (the trust_ir spec and the machine
    // side build the SAME bv op; no independent encoder). Those opcodes
    // (Add/Sub/Mul/And/Or/Xor/Sll/Srl/Sra/Slli/Srli/Addi/Slt/Sltu) are now
    // EmittableNeedsProof and CREDITED by the audit_riscv OPERAND RECONSTRUCTION
    // branch (riscv_function_verifier::opcode_to_source_op + reconstruction
    // discharges Valid), which is the genuine coverage that SUPERSEDES the static
    // proof. Only the GENUINE multi-instruction comparison idioms (SUB+SLTIU,
    // SLT+XORI, swapped-SLT, etc.) — whose machine side is a real composed
    // sequence distinct from the spec predicate — remain.
    riscv_idiom_proofs()
}

/// The comparison-idiom proofs whose machine side is a genuinely non-degenerate
/// composed sequence (distinct from the trust_ir spec predicate). The gate
/// asserts `trust_ir_expr != aarch64_expr` for exactly these.
pub fn riscv_idiom_proofs() -> Vec<ProofObligation> {
    vec![
        proof_riscv_icmp_eq_i64(),
        proof_riscv_icmp_ne_i64(),
        proof_riscv_icmp_sge_i64(),
        proof_riscv_icmp_sgt_i64(),
        proof_riscv_icmp_sle_i64(),
        proof_riscv_icmp_uge_i64(),
        proof_riscv_icmp_ugt_i64(),
        proof_riscv_icmp_ule_i64(),
    ]
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;

    /// Every registered RISC-V proof discharges Valid under the evaluator.
    #[test]
    fn all_riscv_proofs_valid_by_evaluation() {
        for p in all_riscv_proofs() {
            let result = verify_by_evaluation(&p);
            assert!(
                matches!(result, VerificationResult::Valid),
                "proof '{}' did not verify Valid: {:?}",
                p.name,
                result
            );
        }
    }

    /// The idiom proofs are genuinely non-degenerate: the machine side is a
    /// composed sequence structurally distinct from the trust_ir spec side
    /// (the f81e45b X==X guard).
    #[test]
    fn idiom_proofs_are_non_degenerate() {
        for p in riscv_idiom_proofs() {
            assert_ne!(
                p.trust_ir_expr, p.aarch64_expr,
                "idiom proof '{}' has identical spec and machine sides (degenerate)",
                p.name
            );
        }
    }

    /// Sanity: the evaluator refutes a mis-lowered obligation (Iadd -> SUB).
    #[test]
    fn wrong_opcode_choice_is_caught() {
        use crate::trust_ir_semantics::encode_trust_ir_binop;
        use trust_cg_lower::instructions::Opcode;
        use trust_cg_lower::types::Type;

        let (a, b) = ab64();
        // Deliberately mis-lower Iadd to SUB; the obligation must be Invalid.
        let bad = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "riscv: BOGUS Iadd_I64 -> SUB".to_string(),
            trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), b.clone()),
            aarch64_expr: encode_sub(RiscVOperandSize::S64, a, b),
            inputs: ab_inputs(),
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(CAT),
        };
        assert!(
            !matches!(verify_by_evaluation(&bad), VerificationResult::Valid),
            "mis-lowering Iadd->SUB should NOT verify Valid"
        );
    }

    #[test]
    fn proof_count_is_stable() {
        // #62: the 14 degenerate static ALU/shift/imm/cmp X==X proofs were RETRACTED
        // (reconstruction-credited); all_riscv_proofs is now exactly the 8 genuine
        // multi-instruction comparison idioms.
        assert_eq!(all_riscv_proofs().len(), 8);
        assert_eq!(riscv_idiom_proofs().len(), 8);
    }
}
