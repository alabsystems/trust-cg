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
//   * For genuine 1:1 single-instruction lowerings (Iadd->ADD, ... Ushr->SRL),
//     both sides independently compute the same bitvector op; the equivalence is
//     an honest identity that PINS the emitted opcode to the source op (a wrong
//     opcode choice, e.g. Iadd->SUB, would make the obligation FALSE and be
//     caught). These are NOT contorted to force a syntactic difference.
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
    RiscVOperandSize, encode_add, encode_and, encode_mul, encode_or, encode_sll, encode_slli,
    encode_slt, encode_sltiu, encode_sltu, encode_sra, encode_srl, encode_srli, encode_sub,
    encode_xor, encode_xori,
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
// Clean 1:1 dataflow ALU lowerings (i64)
//
// trust_ir spec op == RISC-V emitted op, both computing the same bitvector
// operation. Honest identity (pins the opcode); no forced non-degeneracy.
// ===========================================================================

/// Proof: `trust_ir::Iadd(I64, a, b) -> RISC-V ADD rd, rs1, rs2`.
pub fn proof_riscv_add_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Iadd_I64 -> ADD".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_add(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Isub(I64, a, b) -> RISC-V SUB rd, rs1, rs2`.
pub fn proof_riscv_sub_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Isub_I64 -> SUB".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_sub(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Imul(I64, a, b) -> RISC-V MUL rd, rs1, rs2` (low 64 bits).
pub fn proof_riscv_mul_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Imul_I64 -> MUL".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_mul(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Band(I64, a, b) -> RISC-V AND rd, rs1, rs2`.
pub fn proof_riscv_and_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Band_I64 -> AND".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_and(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Bor(I64, a, b) -> RISC-V OR rd, rs1, rs2`.
pub fn proof_riscv_or_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Bor_I64 -> OR".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_or(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Bxor(I64, a, b) -> RISC-V XOR rd, rs1, rs2`.
pub fn proof_riscv_xor_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Bxor_I64 -> XOR".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Bxor,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_xor(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Ishl(I64, a, b) -> RISC-V SLL rd, rs1, rs2`.
///
/// Both sides use SMT `bvshl`; over the in-range shift-amount domain the
/// trust_ir type system guarantees, this is exactly the RV64 SLL `& 0x3F`
/// result (see `riscv_semantics::encode_sll`). Matches the AArch64 i64
/// `Ishl -> LSL` precedent.
pub fn proof_riscv_sll_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Ishl_I64 -> SLL".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_sll(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Ushr(I64, a, b) -> RISC-V SRL rd, rs1, rs2` (logical).
pub fn proof_riscv_srl_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Ushr_I64 -> SRL".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_srl(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Sshr(I64, a, b) -> RISC-V SRA rd, rs1, rs2` (arithmetic).
pub fn proof_riscv_sra_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Sshr_I64 -> SRA".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_sra(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

// ===========================================================================
// Shift-by-immediate lowerings (i64)
//
// The shamt is a compile-time constant in [0, 63], so there is no masking
// subtlety. We pin a representative non-degenerate shamt (5) and also expose
// builders parameterized by shamt for the harness.
// ===========================================================================

/// Proof: `trust_ir::Ishl(I64, a, shamt) -> RISC-V SLLI rd, rs1, shamt`.
///
/// The trust_ir spec is `bvshl(a, bv_const(shamt))`; the machine side is
/// `encode_slli` (also `bvshl` by the constant). Honest 1:1 for a fixed
/// in-range immediate.
pub fn proof_riscv_slli_i64_shamt(shamt: u32) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", I64_W);
    let shamt_const = SmtExpr::bv_const(shamt as u64, I64_W);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("riscv: Ishl_I64_imm{shamt} -> SLLI"),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I64, a.clone(), shamt_const),
        aarch64_expr: encode_slli(RiscVOperandSize::S64, a, shamt),
        inputs: vec![("a".to_string(), I64_W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Ushr(I64, a, shamt) -> RISC-V SRLI rd, rs1, shamt`.
pub fn proof_riscv_srli_i64_shamt(shamt: u32) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", I64_W);
    let shamt_const = SmtExpr::bv_const(shamt as u64, I64_W);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("riscv: Ushr_I64_imm{shamt} -> SRLI"),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I64, a.clone(), shamt_const),
        aarch64_expr: encode_srli(RiscVOperandSize::S64, a, shamt),
        inputs: vec![("a".to_string(), I64_W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Iconst(I64, imm) / Copy / StructGep -> RISC-V ADDI`.
///
/// `ADDI rd, rs1, imm` computes `rs1 + imm`. This single dataflow proof covers
/// the value-bearing roles of the multi-role ADDI (LI when rs1=x0; MV when
/// imm=0; base+offset GEP). We verify the general `rs1 + imm` form against the
/// trust_ir `Iadd` spec; the LI/MV/GEP specializations are instances of it.
pub fn proof_riscv_addi_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", I64_W);
    let imm = SmtExpr::var("imm", I64_W);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Iadd_I64_imm -> ADDI".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), imm.clone()),
        aarch64_expr: encode_addi_value(a, imm),
        inputs: vec![("a".to_string(), I64_W), ("imm".to_string(), I64_W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

fn encode_addi_value(rs1: SmtExpr, imm: SmtExpr) -> SmtExpr {
    crate::riscv_semantics::encode_addi(RiscVOperandSize::S64, rs1, imm)
}

// ===========================================================================
// Direct comparison-value lowerings (i64): SLT / SLTU
//
// trust_ir `Icmp Slt`/`Icmp Ult` lower to the single matching RISC-V
// instruction. Both sides independently produce `ite(<pred>, 1, 0)` as a 1-bit
// result. Honest 1:1 (pins the comparison opcode; SLT vs SLTU confusion would
// be caught). NOT asserted non-degenerate (single-instruction value op).
// ===========================================================================

/// Proof: `trust_ir::Icmp(SignedLessThan, I64, a, b) -> RISC-V SLT`.
pub fn proof_riscv_slt_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_SLT_I64 -> SLT".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_slt(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
}

/// Proof: `trust_ir::Icmp(UnsignedLessThan, I64, a, b) -> RISC-V SLTU`.
pub fn proof_riscv_sltu_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let (a, b) = ab64();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "riscv: Icmp_ULT_I64 -> SLTU".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedLessThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_sltu(RiscVOperandSize::S64, a, b),
        inputs: ab_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(CAT),
    }
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

/// All RISC-V (RV64) lowering proof obligations.
///
/// Ordering groups: clean 1:1 ALU, shift-by-immediate + ADDI value, direct
/// comparison value ops (SLT/SLTU), then the comparison idioms.
pub fn all_riscv_proofs() -> Vec<ProofObligation> {
    // #62 retraction (group b): the 14 static "riscv: <op> -> <INSN>" 1:1 ALU/
    // shift/imm/cmp obligations were degenerate X==X (the trust_ir spec and the
    // machine side built the SAME bv op; no independent encoder). Those opcodes
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

    /// Sanity: the clean 1:1 ALU proofs would FAIL if the wrong opcode were
    /// chosen (e.g. Iadd -> SUB), demonstrating the identity proof is meaningful.
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
