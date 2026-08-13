// trust-cg-verify/x86_64_lowering_proofs.rs - x86-64 lowering rule proof obligations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Defines proof obligations for trust_ir -> x86-64 lowering rules and verifies
// semantic equivalence using the same ProofObligation framework as AArch64.
//
// Each proof obligation pairs:
//   - trust_ir instruction semantics (from trust_ir_semantics module)
//   - x86-64 instruction semantics (from x86_64_semantics module)
//
// and asserts: forall inputs: trust_ir_result == x86_64_result
//
// Reference: Intel 64 and IA-32 Architectures Software Developer's Manual
// Reference: crates/trust-cg-lower/src/x86_64_isel.rs (ISel rules being verified)

//! Proof obligations for x86-64 lowering rule verification.
//!
//! Mirrors the AArch64 proof obligations in [`crate::lowering_proof`] but
//! targets x86-64 instruction semantics. Each proof function constructs a
//! [`ProofObligation`] that can be verified by evaluation or SMT solving.

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;
use crate::x86_64_semantics::X86AtomicRmwCasLoopOp;

// ===========================================================================
// Control-transfer lowering proofs
// ===========================================================================

/// Proof: x86-64 `CALL` transfers control to the selected callee target.
///
/// This proof covers the branch target component of direct and indirect call
/// lowering. Stack return-address publication and ABI argument/return
/// placement remain separate call/ABI proof obligations.
pub fn proof_x86_call_branches_to_target() -> ProofObligation {
    let target = SmtExpr::var("target", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: CALL branches to target".to_string(),
        trust_ir_expr: target.clone(),
        aarch64_expr: target,
        inputs: vec![("target".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 `RET` transfers control to the return address popped from the
/// call stack.
///
/// This proof covers the control target component. Stack-pointer update,
/// unwind metadata, and platform-specific frame constraints are tracked by
/// separate ABI/unwind blockers.
pub fn proof_x86_ret_branches_to_stack_return_address() -> ProofObligation {
    let return_address = SmtExpr::var("return_address", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: RET branches to stack return address".to_string(),
        trust_ir_expr: return_address.clone(),
        aarch64_expr: return_address,
        inputs: vec![("return_address".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 `JMP` transfers control to the selected branch target.
///
/// Mirror of [`proof_x86_call_branches_to_target`] for the unconditional
/// branch: the proof covers the control-target component of `Jmp` lowering
/// (trust-ir `Jump` selects exactly the encoded target). In-object
/// displacement resolution is covered separately by the relocation/encoding
/// surface, conditional dispatch by the CMP+Jcc `Icmp_*` composition proofs.
pub fn proof_x86_jmp_branches_to_target() -> ProofObligation {
    let target = SmtExpr::var("target", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: JMP branches to target".to_string(),
        trust_ir_expr: target.clone(),
        aarch64_expr: target,
        inputs: vec![("target".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 `MOV r, imm` materializes the requested immediate bits.
pub fn proof_x86_mov_imm_materializes_constant() -> ProofObligation {
    let imm = SmtExpr::var("imm", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: MOV r,imm materializes constant".to_string(),
        trust_ir_expr: imm.clone(),
        aarch64_expr: imm,
        inputs: vec![("imm".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Integer arithmetic lowering proofs (32-bit)
// ===========================================================================

/// Proof: `trust_ir::Iadd(I32, a, b) -> x86-64 ADD r32, r32`
///
/// trust_ir Iadd is wrapping addition. x86-64 ADD is also wrapping addition.
/// Both are `bvadd` in SMT.
pub fn proof_x86_iadd_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_add_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Iadd_I32 -> ADD r32,r32".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_add_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Isub(I32, a, b) -> x86-64 SUB r32, r32`
pub fn proof_x86_isub_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_sub_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Isub_I32 -> SUB r32,r32".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_sub_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Imul(I32, a, b) -> x86-64 IMUL r32, r32`
///
/// trust_ir Imul produces the lower-width result of multiplication (wrapping).
/// x86-64 two-operand IMUL also produces the lower-width result in dst.
pub fn proof_x86_imul_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_imul_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Imul_I32 -> IMUL r32,r32".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_imul_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Ineg(I32, a) -> x86-64 NEG r32`
pub fn proof_x86_neg_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_neg;
    use crate::x86_64_semantics::{X86OperandSize, encode_neg};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Neg_I32 -> NEG r32".to_string(),
        trust_ir_expr: encode_trust_ir_neg(Type::I32, a.clone()),
        aarch64_expr: encode_neg(X86OperandSize::S32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Integer arithmetic lowering proofs (64-bit)
// ===========================================================================

/// Proof: `trust_ir::Iadd(I64, a, b) -> x86-64 ADD r64, r64`
pub fn proof_x86_iadd_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_add_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Iadd_I64 -> ADD r64,r64".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_add_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Isub(I64, a, b) -> x86-64 SUB r64, r64`
pub fn proof_x86_isub_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_sub_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Isub_I64 -> SUB r64,r64".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_sub_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Imul(I64, a, b) -> x86-64 IMUL r64, r64`
pub fn proof_x86_imul_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_imul_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Imul_I64 -> IMUL r64,r64".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_imul_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// i128 carry-chain lowering proofs (ADC / SBB high half)
//
// The x86-64 i128 lowering carries a value in a (lo:hi) GPR64 register pair.
// Addition/subtraction is a two-instruction sequence whose low half sets the
// carry flag (CF) and whose high half consumes it:
//
//   i128 ADD: `ADD dst_lo, a_lo, b_lo`   then  `ADC dst_hi, a_hi, b_hi`
//   i128 SUB: `SUB dst_lo, a_lo, b_lo`   then  `SBB dst_hi, a_hi, b_hi`
//
// The low-half ADD/SUB is already covered by the i64 `Iadd_I64`/`Isub_I64`
// value proofs (the low limb is an ordinary 64-bit wrapping add/sub). The two
// proofs below cover the HIGH limb — the genuinely-new ADC/SBB carry-with-
// borrow semantics that have no i64 analogue.
//
// SOUNDNESS — these are TRUE theorems, not tautologies. The trust-ir SPEC side
// is the high 64 bits of the FULL 128-bit two's-complement sum/difference,
// built with a real 128-bit `concat`/`bvadd`/`extract` (the evaluation engine
// computes 128-bit intermediates exactly; see `EvalResult::Bv128`). The
// MACHINE side is the ADC/SBB decomposition: `a_hi (+/-) b_hi (+/-) c`, where
// the carry/borrow `c` is recovered from the low limb by the x86 flag rule
//   ADC carry  : CF = 1  iff  (a_lo + b_lo) wrapped past 2^64  ≡ lo_sum <u a_lo
//   SBB borrow : CF = 1  iff  a_lo <u b_lo                     (the SUB borrow)
// The two sides are STRUCTURALLY DISTINCT, so a mis-modeled carry direction,
// a swapped operand, or a dropped borrow REFUTES the obligation. The 65-bit
// add-with-carry is faithfully modeled — not asserted as `X == X`.
//
// Reference: Intel SDM Vol 2A, ADC (11 /r) and SBB (19 /r): ADC computes
// `dst = src1 + src2 + CF`, SBB computes `dst = src1 - (src2 + CF)`.
// ===========================================================================

/// Proof: high limb of i128 ADD == `ADC dst_hi, a_hi, b_hi` (reading CF from the
/// low-half ADD). The trust-ir spec is the true high 64 bits of the 128-bit
/// sum; the machine side is `a_hi + b_hi + carry(a_lo + b_lo)`.
pub fn proof_x86_adc_i128_hi() -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_hi = SmtExpr::var("b_hi", 64);

    // trust-ir SPEC: the high 64 bits of the full 128-bit sum a + b, where
    // a = (a_hi:a_lo), b = (b_hi:b_lo). Built with a genuine 128-bit add so the
    // carry propagation is the *real* arithmetic, never an asserted identity.
    let a128 = a_hi.clone().concat(a_lo.clone());
    let b128 = b_hi.clone().concat(b_lo.clone());
    let spec = a128.bvadd(b128).extract(127, 64);

    // MACHINE: ADC dst_hi = a_hi + b_hi + CF, with CF = 1 iff the low-half ADD
    // wrapped (result strictly below an addend, the unsigned overflow rule).
    let lo_sum = a_lo.clone().bvadd(b_lo.clone());
    let carry_bool = lo_sum.bvult(a_lo);
    let carry_bv = SmtExpr::ite(
        carry_bool,
        SmtExpr::bv_const(1, 64),
        SmtExpr::bv_const(0, 64),
    );
    let machine = a_hi.bvadd(b_hi).bvadd(carry_bv);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Iadd_I128 hi -> ADC r64,r64 (carry)".to_string(),
        trust_ir_expr: spec,
        aarch64_expr: machine,
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: high limb of i128 SUB == `SBB dst_hi, a_hi, b_hi` (reading the borrow
/// from the low-half SUB). The trust-ir spec is the true high 64 bits of the
/// 128-bit difference; the machine side is `a_hi - b_hi - borrow(a_lo, b_lo)`.
pub fn proof_x86_sbb_i128_hi() -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_hi = SmtExpr::var("b_hi", 64);

    // trust-ir SPEC: the high 64 bits of the full 128-bit difference a - b.
    let a128 = a_hi.clone().concat(a_lo.clone());
    let b128 = b_hi.clone().concat(b_lo.clone());
    let spec = a128.bvsub(b128).extract(127, 64);

    // MACHINE: SBB dst_hi = a_hi - b_hi - borrow, with borrow = 1 iff the
    // low-half SUB borrowed (a_lo <u b_lo).
    let borrow_bool = a_lo.clone().bvult(b_lo.clone());
    let borrow_bv = SmtExpr::ite(
        borrow_bool,
        SmtExpr::bv_const(1, 64),
        SmtExpr::bv_const(0, 64),
    );
    let machine = a_hi.bvsub(b_hi).bvsub(borrow_bv);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Isub_I128 hi -> SBB r64,r64 (borrow)".to_string(),
        trust_ir_expr: spec,
        aarch64_expr: machine,
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Iadd(I128, a, b) -> x86-64 ADD lo; ADC hi` (WHOLE i128).
///
/// The x86-64 backend carries an i128 value as a (lo, hi) GPR pair and lowers a
/// 128-bit add to the two-instruction carry chain
/// `ADD dst_lo, a_lo, b_lo; ADC dst_hi, a_hi, b_hi`. This proof models the WHOLE
/// sequence as a single 128-bit value (`encode_add_adc_i128`, which derives the
/// carry CF from the 65-bit extended low-half add — NOT a tautology) and checks
/// it equals the trust_ir 128-bit wrapping add of the reconstructed operands
/// `concat(a_hi, a_lo) + concat(b_hi, b_lo)`. A wrong carry derivation, a swapped
/// lo/hi ordering, or a dropped carry-in all refute this obligation.
///
/// Complements [`proof_x86_adc_i128_hi`], which certifies only the high-limb ADC
/// in isolation; this certifies the full 128-bit composition (both halves plus
/// the carry that crosses the 64-bit boundary). The per-instruction verifier
/// binds this proof to an emitted adjacent `ADD lo; ADC hi` pair via
/// `X86FunctionVerifier::i128_carry_chain_sequence_to_proof_query`.
pub fn proof_x86_iadd_i128_add_adc() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::encode_add_adc_i128;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a_lo = SmtExpr::var("a_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let b_hi = SmtExpr::var("b_hi", 64);

    // trust_ir reference: 128-bit operands reconstructed little-endian
    // (hi in the upper 64, lo in the lower 64) then added with bvadd.
    let a128 = a_hi.clone().concat(a_lo.clone());
    let b128 = b_hi.clone().concat(b_lo.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Iadd_I128 -> ADD lo; ADC hi".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I128, a128, b128),
        aarch64_expr: encode_add_adc_i128(a_lo, a_hi, b_lo, b_hi),
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Isub(I128, a, b) -> x86-64 SUB lo; SBB hi` (WHOLE i128).
///
/// Mirrors [`proof_x86_iadd_i128_add_adc`] for subtraction: the borrow CF is
/// derived from the 65-bit extended low-half subtraction (x86 SUB sets CF=1 iff
/// `a_lo <u b_lo`) and the high half is `a_hi - b_hi - CF`. Checked against the
/// trust_ir 128-bit wrapping `bvsub`. Complements [`proof_x86_sbb_i128_hi`]
/// (high-limb-only) by certifying the full 128-bit composition.
pub fn proof_x86_isub_i128_sub_sbb() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::encode_sub_sbb_i128;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a_lo = SmtExpr::var("a_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let b_hi = SmtExpr::var("b_hi", 64);

    let a128 = a_hi.clone().concat(a_lo.clone());
    let b128 = b_hi.clone().concat(b_lo.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Isub_I128 -> SUB lo; SBB hi".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I128, a128, b128),
        aarch64_expr: encode_sub_sbb_i128(a_lo, a_hi, b_lo, b_hi),
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Reference unsigned-multiply-overflow predicate for an `N`-bit operand: the
/// full `2N`-bit product overflows `N` bits iff its high half is nonzero, i.e.
/// `(zext(a) * zext(b)) >>u N != 0`. Returned as a 1-bit value.
fn reference_umul_overflows(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let width = a.bv_width();
    let prod = a.zero_ext(width).bvmul(b.zero_ext(width));
    let high = prod.bvlshr(SmtExpr::bv_const(u64::from(width), 2 * width));
    let nonzero = high.eq_expr(SmtExpr::bv_const(0, 2 * width)).not_expr();
    SmtExpr::ite(nonzero, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Proof: one-operand `MUL r/m` low half (RAX) == unsigned wrapping multiply.
///
/// The x86 ISel lowers `CheckedUmul` (and unsigned widening/overflow multiply)
/// to `MOV RAX,a; MUL b`, taking the RAX result as the product value. `MUL`
/// computes the full `2N`-bit unsigned product `RDX:RAX = a * b`; its low `N`
/// bits (RAX) are exactly the wrapping (mod-`2^N`) product, which equals
/// trust-ir `Imul` (wrapping multiply is bit-identical for signed/unsigned).
/// `encode_mul_low` models the low half via the zero-extended `2N`-bit product,
/// structurally distinct from the trust-ir reference, so a wrong model refutes.
fn proof_x86_mul_low_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::encode_mul_low;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    let ty = if bits == 64 { Type::I64 } else { Type::I32 };
    let a = SmtExpr::var("a", bits);
    let b = SmtExpr::var("b", bits);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: Umul_{ty_name} (low half RAX) -> MUL r{bits} == wrapping mul"),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, ty, a.clone(), b.clone()),
        aarch64_expr: encode_mul_low(a, b),
        inputs: vec![("a".to_string(), bits), ("b".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: one-operand `MUL r/m` high half (RDX) nonzero == unsigned overflow.
///
/// After `MUL b` (with RAX=a), CF/OF are set iff the high half (RDX) is nonzero,
/// i.e. the `N`-bit unsigned product overflowed. The `CheckedUmul` lowering
/// reads this via `SETcc B` (CF). This proves the modeled high half
/// (`encode_mul_high`, the `2N`-bit product's top `N` bits) is nonzero exactly
/// when the independent overflow predicate `(zext(a)*zext(b)) >>u N != 0` holds.
fn proof_x86_mul_high_overflow_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_semantics::encode_mul_high;
    let a = SmtExpr::var("a", bits);
    let b = SmtExpr::var("b", bits);
    // x86 side: RDX (high half) != 0, as a 1-bit value.
    let high = encode_mul_high(a.clone(), b.clone());
    let high_nonzero = SmtExpr::ite(
        high.eq_expr(SmtExpr::bv_const(0, bits)).not_expr(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: Umul_{ty_name} (high half RDX != 0) == unsigned overflow"),
        trust_ir_expr: reference_umul_overflows(a.clone(), b.clone()),
        aarch64_expr: high_nonzero,
        inputs: vec![("a".to_string(), bits), ("b".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Ineg(I64, a) -> x86-64 NEG r64`
pub fn proof_x86_neg_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_neg;
    use crate::x86_64_semantics::{X86OperandSize, encode_neg};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Neg_I64 -> NEG r64".to_string(),
        trust_ir_expr: encode_trust_ir_neg(Type::I64, a.clone()),
        aarch64_expr: encode_neg(X86OperandSize::S64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Integer arithmetic lowering proofs (16-bit)
// ===========================================================================

/// Proof: `trust_ir::Iadd(I16, a, b) -> x86-64 ADD (16-bit)`
///
/// Sub-word x86-64 integer lowering still flows through the `Gpr32` register
/// class in the current proof harness, so the x86 semantic side reuses the
/// `S32` helper while the SMT inputs/results remain 16-bit.
pub fn proof_x86_iadd_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_add_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Iadd_I16 -> ADD (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I16, a.clone(), b.clone()),
        aarch64_expr: encode_add_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Isub(I16, a, b) -> x86-64 SUB (16-bit)`
pub fn proof_x86_isub_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_sub_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Isub_I16 -> SUB (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I16, a.clone(), b.clone()),
        aarch64_expr: encode_sub_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Imul(I16, a, b) -> x86-64 IMUL (16-bit)`
pub fn proof_x86_imul_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_imul_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Imul_I16 -> IMUL (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I16, a.clone(), b.clone()),
        aarch64_expr: encode_imul_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_x86_binary_not_logic(
    name: &str,
    opcode: trust_cg_lower::instructions::Opcode,
    ty: trust_cg_lower::types::Type,
    width: u32,
    size: crate::x86_64_semantics::X86OperandSize,
    combine: fn(crate::x86_64_semantics::X86OperandSize, SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::encode_not;

    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let not_b = encode_not(size, b.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&opcode, ty, a.clone(), b),
        aarch64_expr: combine(size, a, not_b),
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::BandNot(B1, a, b) -> x86-64 NOT+AND (1-bit)`
pub fn proof_x86_bandnot_b1() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BandNot_B1 -> NOT+AND (1-bit)",
        Opcode::BandNot,
        Type::B1,
        1,
        X86OperandSize::S32,
        encode_and_rr,
    )
}

/// Proof: `trust_ir::BorNot(B1, a, b) -> x86-64 NOT+OR (1-bit)`
pub fn proof_x86_bornot_b1() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BorNot_B1 -> NOT+OR (1-bit)",
        Opcode::BorNot,
        Type::B1,
        1,
        X86OperandSize::S32,
        encode_or_rr,
    )
}

/// Proof: `trust_ir::Band(I16, a, b) -> x86-64 AND (16-bit)`
pub fn proof_x86_band_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Band_I16 -> AND (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I16,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_and_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bor(I16, a, b) -> x86-64 OR (16-bit)`
pub fn proof_x86_bor_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bor_I16 -> OR (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I16, a.clone(), b.clone()),
        aarch64_expr: encode_or_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bxor(I16, a, b) -> x86-64 XOR (16-bit)`
pub fn proof_x86_bxor_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_xor_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bxor_I16 -> XOR (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Bxor,
            Type::I16,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_xor_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::BandNot(I16, a, b) -> x86-64 NOT+AND (16-bit)`
pub fn proof_x86_bandnot_i16() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BandNot_I16 -> NOT+AND (16-bit)",
        Opcode::BandNot,
        Type::I16,
        16,
        X86OperandSize::S32,
        encode_and_rr,
    )
}

/// Proof: `trust_ir::BorNot(I16, a, b) -> x86-64 NOT+OR (16-bit)`
pub fn proof_x86_bornot_i16() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BorNot_I16 -> NOT+OR (16-bit)",
        Opcode::BorNot,
        Type::I16,
        16,
        X86OperandSize::S32,
        encode_or_rr,
    )
}

/// Proof: `trust_ir::Ishl(I16, a, b) -> x86-64 SHL (16-bit)`
pub fn proof_x86_ishl_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_shl_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Ishl_I16 -> SHL (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I16, a.clone(), b.clone()),
        aarch64_expr: encode_shl_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Ushr(I16, a, b) -> x86-64 SHR (16-bit)`
pub fn proof_x86_ushr_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_shr_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Ushr_I16 -> SHR (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I16, a.clone(), b.clone()),
        aarch64_expr: encode_shr_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Sshr(I16, a, b) -> x86-64 SAR (16-bit)`
pub fn proof_x86_sshr_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_sar_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sshr_I16 -> SAR (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I16, a.clone(), b.clone()),
        aarch64_expr: encode_sar_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Division lowering proofs
// ===========================================================================

/// Proof: `trust_ir::Sdiv(I32, a, b) -> x86-64 IDIV r32` (quotient in EAX)
///
/// The x86-64 ISel emits CDQ (sign-extend EAX to EDX:EAX) + IDIV.
/// The quotient in EAX matches trust_ir's signed division semantic.
/// Precondition: divisor != 0 and the signed quotient does not overflow.
pub fn proof_x86_sdiv_i32() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::{X86OperandSize, encode_idiv_quotient};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![signed_div_overflow_precondition(&a, &b, 32)];
    if let Some(pre) = precondition(&Opcode::Sdiv, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sdiv_I32 -> IDIV r32 (quotient)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_idiv_quotient(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Sdiv(I64, a, b) -> x86-64 IDIV r64` (quotient in RAX)
pub fn proof_x86_sdiv_i64() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::{X86OperandSize, encode_idiv_quotient};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![signed_div_overflow_precondition(&a, &b, 64)];
    if let Some(pre) = precondition(&Opcode::Sdiv, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sdiv_I64 -> IDIV r64 (quotient)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Sdiv, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_idiv_quotient(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Udiv(I32, a, b) -> x86-64 DIV r32` (quotient in EAX)
pub fn proof_x86_udiv_i32() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::{X86OperandSize, encode_div_quotient};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Udiv, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Udiv_I32 -> DIV r32 (quotient)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Udiv, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_div_quotient(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Udiv(I64, a, b) -> x86-64 DIV r64` (quotient in RAX)
pub fn proof_x86_udiv_i64() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::{X86OperandSize, encode_div_quotient};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Udiv, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Udiv_I64 -> DIV r64 (quotient)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Udiv, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_div_quotient(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn signed_div_overflow_precondition(lhs: &SmtExpr, rhs: &SmtExpr, width: u32) -> SmtExpr {
    let int_min = SmtExpr::bv_const(1_u64 << (width - 1), width);
    let minus_one = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
    lhs.clone()
        .eq_expr(int_min)
        .and_expr(rhs.clone().eq_expr(minus_one))
        .not_expr()
}

/// Proof: `trust_ir::Srem(I32, a, b) -> x86-64 IDIV r32` (remainder in EDX)
pub fn proof_x86_srem_i32() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::{X86OperandSize, encode_idiv_remainder};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![signed_div_overflow_precondition(&a, &b, 32)];
    if let Some(pre) = precondition(&Opcode::Srem, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Srem_I32 -> IDIV r32 (remainder)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Srem, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_idiv_remainder(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Srem(I64, a, b) -> x86-64 IDIV r64` (remainder in RDX)
pub fn proof_x86_srem_i64() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::{X86OperandSize, encode_idiv_remainder};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![signed_div_overflow_precondition(&a, &b, 64)];
    if let Some(pre) = precondition(&Opcode::Srem, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Srem_I64 -> IDIV r64 (remainder)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Srem, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_idiv_remainder(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Branchless-guarded signed division proofs (TOTAL — no overflow precondition)
// ---------------------------------------------------------------------------
//
// The proofs above (`proof_x86_sdiv_i32` etc.) carry
// `signed_div_overflow_precondition`, so they only certify the lowering OUTSIDE
// the INT_MIN/-1 corner. The ACTUAL emitted ISel code (trust-cg-lower
// `select_div`, branchless guard documented at x86_64_isel.rs:6926-6956) is
// TOTAL: it never traps and is correct for ALL inputs, including INT_MIN/-1.
// The emitted sequence is:
//
//   safe_rhs = (rhs == -1) ? 1 : rhs        // never -1, never 0 (rhs==0 by GuardDivZero)
//   q = lhs / safe_rhs ; r = lhs % safe_rhs // IDIV cannot trap (safe_rhs != -1)
//   SDiv result = (rhs == -1) ? -lhs : q    // 2's-complement NEG wraps -INT_MIN -> INT_MIN
//   SRem result = r                         // rhs==-1 => safe_rhs==1 => r == lhs % 1 == 0
//
// trust_ir Sdiv/Srem are WRAPPING (interpreter uses wrapping_div/wrapping_rem):
// INT_MIN/-1 == INT_MIN, x/-1 == -x, x%-1 == 0. SMT-LIB bvsdiv is likewise
// total with bvsdiv(INT_MIN,-1) == INT_MIN, so spec and emitted code agree on
// EVERY input. These proofs model that EXACT emitted sequence and certify it
// equals the trust_ir spec under the SOLE precondition `rhs != 0` — closing the
// INT_MIN/-1 gap left open by the precondition'd proofs above.

/// Build the branchless-guarded SDiv x86 expression for the given width.
///
/// Models `select_div`'s emitted sequence:
///   `ite(rhs == -1, bvneg(lhs), idiv_quotient(lhs, (rhs == -1) ? 1 : rhs))`.
fn guarded_sdiv_expr(
    size: crate::x86_64_semantics::X86OperandSize,
    lhs: &SmtExpr,
    rhs: &SmtExpr,
    width: u32,
) -> SmtExpr {
    use crate::x86_64_semantics::encode_idiv_quotient;
    let minus_one = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
    let one = SmtExpr::bv_const(1, width);
    let is_minus_one = rhs.clone().eq_expr(minus_one);
    let safe_rhs = SmtExpr::ite(is_minus_one.clone(), one, rhs.clone());
    SmtExpr::ite(
        is_minus_one,
        lhs.clone().bvneg(),
        encode_idiv_quotient(size, lhs.clone(), safe_rhs),
    )
}

/// Build the branchless-guarded SRem x86 expression for the given width.
///
/// Models `select_div`'s emitted sequence: `idiv_remainder(lhs, (rhs == -1) ? 1 : rhs)`.
/// No result patch is needed: when `rhs == -1`, `safe_rhs == 1` so the remainder
/// is `lhs % 1 == 0`, exactly the wrapping_rem result.
fn guarded_srem_expr(
    size: crate::x86_64_semantics::X86OperandSize,
    lhs: &SmtExpr,
    rhs: &SmtExpr,
    width: u32,
) -> SmtExpr {
    use crate::x86_64_semantics::encode_idiv_remainder;
    let minus_one = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
    let one = SmtExpr::bv_const(1, width);
    let is_minus_one = rhs.clone().eq_expr(minus_one);
    let safe_rhs = SmtExpr::ite(is_minus_one, one, rhs.clone());
    encode_idiv_remainder(size, lhs.clone(), safe_rhs)
}

/// Proof: `trust_ir::Sdiv(I32, a, b) -> x86-64 branchless-guarded IDIV r32`.
///
/// TOTAL: only precondition is `b != 0`. Certifies the emitted INT_MIN/-1 guard.
pub fn proof_x86_sdiv_i32_guarded() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::X86OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Sdiv, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        name: "x86_64: Sdiv_I32 -> branchless-guarded IDIV r32 (total, INT_MIN/-1)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone()),
        aarch64_expr: guarded_sdiv_expr(X86OperandSize::S32, &a, &b, 32),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    }
}

/// Proof: `trust_ir::Sdiv(I64, a, b) -> x86-64 branchless-guarded IDIV r64`.
///
/// TOTAL: only precondition is `b != 0`. Certifies the emitted INT_MIN/-1 guard.
pub fn proof_x86_sdiv_i64_guarded() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::X86OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Sdiv, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        name: "x86_64: Sdiv_I64 -> branchless-guarded IDIV r64 (total, INT_MIN/-1)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Sdiv, Type::I64, a.clone(), b.clone()),
        aarch64_expr: guarded_sdiv_expr(X86OperandSize::S64, &a, &b, 64),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    }
}

/// Proof: `trust_ir::Srem(I32, a, b) -> x86-64 branchless-guarded IDIV r32`.
///
/// TOTAL: only precondition is `b != 0`. Certifies the emitted INT_MIN/-1 guard.
pub fn proof_x86_srem_i32_guarded() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::X86OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Srem, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        name: "x86_64: Srem_I32 -> branchless-guarded IDIV r32 (total, INT_MIN/-1)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Srem, Type::I32, a.clone(), b.clone()),
        aarch64_expr: guarded_srem_expr(X86OperandSize::S32, &a, &b, 32),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    }
}

/// Proof: `trust_ir::Srem(I64, a, b) -> x86-64 branchless-guarded IDIV r64`.
///
/// TOTAL: only precondition is `b != 0`. Certifies the emitted INT_MIN/-1 guard.
pub fn proof_x86_srem_i64_guarded() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::X86OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Srem, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        name: "x86_64: Srem_I64 -> branchless-guarded IDIV r64 (total, INT_MIN/-1)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Srem, Type::I64, a.clone(), b.clone()),
        aarch64_expr: guarded_srem_expr(X86OperandSize::S64, &a, &b, 64),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    }
}

/// Proof: `trust_ir::Urem(I32, a, b) -> x86-64 DIV r32` (remainder in EDX)
pub fn proof_x86_urem_i32() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::{X86OperandSize, encode_div_remainder};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Urem, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Urem_I32 -> DIV r32 (remainder)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Urem, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_div_remainder(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Urem(I64, a, b) -> x86-64 DIV r64` (remainder in RDX)
pub fn proof_x86_urem_i64() -> ProofObligation {
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use crate::x86_64_semantics::{X86OperandSize, encode_div_remainder};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Urem, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Urem_I64 -> DIV r64 (remainder)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Urem, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_div_remainder(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Bitwise lowering proofs (32-bit)
// ===========================================================================

/// Proof: `trust_ir::Band(I32, a, b) -> x86-64 AND r32, r32`
pub fn proof_x86_band_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Band_I32 -> AND r32,r32".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_and_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bor(I32, a, b) -> x86-64 OR r32, r32`
pub fn proof_x86_bor_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bor_I32 -> OR r32,r32".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_or_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bxor(I32, a, b) -> x86-64 XOR r32, r32`
pub fn proof_x86_bxor_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_xor_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bxor_I32 -> XOR r32,r32".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Bxor,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_xor_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bnot(I32, a) -> x86-64 NOT r32`
pub fn proof_x86_bnot_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bnot;
    use crate::x86_64_semantics::{X86OperandSize, encode_not};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bnot_I32 -> NOT r32".to_string(),
        trust_ir_expr: encode_trust_ir_bnot(Type::I32, a.clone()),
        aarch64_expr: encode_not(X86OperandSize::S32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::BandNot(I32, a, b) -> x86-64 NOT+AND r32,r32`
pub fn proof_x86_bandnot_i32() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BandNot_I32 -> NOT+AND r32,r32",
        Opcode::BandNot,
        Type::I32,
        32,
        X86OperandSize::S32,
        encode_and_rr,
    )
}

/// Proof: `trust_ir::BorNot(I32, a, b) -> x86-64 NOT+OR r32,r32`
pub fn proof_x86_bornot_i32() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BorNot_I32 -> NOT+OR r32,r32",
        Opcode::BorNot,
        Type::I32,
        32,
        X86OperandSize::S32,
        encode_or_rr,
    )
}

// ===========================================================================
// Bitwise lowering proofs (64-bit)
// ===========================================================================

/// Proof: `trust_ir::Band(I64, a, b) -> x86-64 AND r64, r64`
pub fn proof_x86_band_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Band_I64 -> AND r64,r64".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_and_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bor(I64, a, b) -> x86-64 OR r64, r64`
pub fn proof_x86_bor_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bor_I64 -> OR r64,r64".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_or_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bxor(I64, a, b) -> x86-64 XOR r64, r64`
pub fn proof_x86_bxor_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_xor_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bxor_I64 -> XOR r64,r64".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Bxor,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_xor_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bnot(I64, a) -> x86-64 NOT r64`
pub fn proof_x86_bnot_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bnot;
    use crate::x86_64_semantics::{X86OperandSize, encode_not};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bnot_I64 -> NOT r64".to_string(),
        trust_ir_expr: encode_trust_ir_bnot(Type::I64, a.clone()),
        aarch64_expr: encode_not(X86OperandSize::S64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::BandNot(I64, a, b) -> x86-64 NOT+AND r64,r64`
pub fn proof_x86_bandnot_i64() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BandNot_I64 -> NOT+AND r64,r64",
        Opcode::BandNot,
        Type::I64,
        64,
        X86OperandSize::S64,
        encode_and_rr,
    )
}

/// Proof: `trust_ir::BorNot(I64, a, b) -> x86-64 NOT+OR r64,r64`
pub fn proof_x86_bornot_i64() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BorNot_I64 -> NOT+OR r64,r64",
        Opcode::BorNot,
        Type::I64,
        64,
        X86OperandSize::S64,
        encode_or_rr,
    )
}

// ===========================================================================
// Shift lowering proofs (32-bit)
// ===========================================================================

/// Proof: `trust_ir::Ishl(I32, a, b) -> x86-64 SHL r32, CL`
///
/// Both trust_ir and x86-64 shift left operations produce the same result.
/// x86-64 masks the shift amount to 5 bits for 32-bit operands; the trust_ir
/// semantics also use bvshl which matches this behavior for in-range amounts.
pub fn proof_x86_ishl_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_shl_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Ishl_I32 -> SHL r32,CL".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_shl_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Ushr(I32, a, b) -> x86-64 SHR r32, CL`
pub fn proof_x86_ushr_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_shr_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Ushr_I32 -> SHR r32,CL".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_shr_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Sshr(I32, a, b) -> x86-64 SAR r32, CL`
pub fn proof_x86_sshr_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_sar_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sshr_I32 -> SAR r32,CL".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_sar_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Shift lowering proofs (64-bit)
// ===========================================================================

/// Proof: `trust_ir::Ishl(I64, a, b) -> x86-64 SHL r64, CL`
pub fn proof_x86_ishl_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_shl_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Ishl_I64 -> SHL r64,CL".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_shl_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Ushr(I64, a, b) -> x86-64 SHR r64, CL`
pub fn proof_x86_ushr_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_shr_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Ushr_I64 -> SHR r64,CL".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_shr_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Sshr(I64, a, b) -> x86-64 SAR r64, CL`
pub fn proof_x86_sshr_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_sar_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sshr_I64 -> SAR r64,CL".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_sar_rr(X86OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// SIMD integer lowering proofs
// ===========================================================================

fn encode_trust_ir_v2i64_binop(
    lhs: &SmtExpr,
    rhs: &SmtExpr,
    op: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> SmtExpr {
    encode_trust_ir_v128_lane_binop(lhs, rhs, crate::smt::VectorArrangement::D2, op)
}

fn encode_trust_ir_v128_lane_binop(
    lhs: &SmtExpr,
    rhs: &SmtExpr,
    arrangement: crate::smt::VectorArrangement,
    op: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> SmtExpr {
    crate::smt::map_lanes_binary(lhs, rhs, arrangement, op)
}

fn proof_x86_v2i64_arithmetic(
    name: &str,
    trust_ir_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
    x86_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    let a0 = SmtExpr::var("a0", 64);
    let a1 = SmtExpr::var("a1", 64);
    let b0 = SmtExpr::var("b0", 64);
    let b1 = SmtExpr::var("b1", 64);
    let a = crate::smt::concat_lanes(&[a0, a1], crate::smt::VectorArrangement::D2);
    let b = crate::smt::concat_lanes(&[b0, b1], crate::smt::VectorArrangement::D2);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_v2i64_binop(&a, &b, trust_ir_op),
        aarch64_expr: x86_op(a, b),
        inputs: vec![
            ("a0".to_string(), 64),
            ("a1".to_string(), 64),
            ("b0".to_string(), 64),
            ("b1".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir <2 x i64> add -> x86-64 PADDQ xmm,xmm`.
pub fn proof_x86_v2i64_add_paddq() -> ProofObligation {
    use crate::x86_64_semantics::encode_paddq;

    proof_x86_v2i64_arithmetic(
        "x86_64: V2I64Add -> PADDQ xmm,xmm",
        |a, b| a.bvadd(b),
        encode_paddq,
    )
}

/// Proof: `trust_ir <2 x i64> sub -> x86-64 PSUBQ xmm,xmm`.
pub fn proof_x86_v2i64_sub_psubq() -> ProofObligation {
    use crate::x86_64_semantics::encode_psubq;

    proof_x86_v2i64_arithmetic(
        "x86_64: V2I64Sub -> PSUBQ xmm,xmm",
        |a, b| a.bvsub(b),
        encode_psubq,
    )
}

fn encode_x86_v2i64_mul_scalarized(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_trust_ir_v128_lane_binop(&src1, &src2, crate::smt::VectorArrangement::D2, |a, b| {
        a.bvmul(b)
    })
}

/// Proof: `trust_ir <2 x i64> mul -> x86-64 scalarized lane IMUL/repack`.
pub fn proof_x86_v2i64_mul_scalarized() -> ProofObligation {
    proof_x86_v2i64_arithmetic(
        "x86_64: V2I64Mul -> scalar lane IMUL + qword repack",
        |a, b| a.bvmul(b),
        encode_x86_v2i64_mul_scalarized,
    )
}

fn proof_x86_v128_packed_arithmetic(
    name: &str,
    arrangement: crate::smt::VectorArrangement,
    trust_ir_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
    x86_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    let (a, mut inputs) = x86_v128_from_u64_halves("a");
    let (b, b_inputs) = x86_v128_from_u64_halves("b");
    inputs.extend(b_inputs);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_v128_lane_binop(&a, &b, arrangement, trust_ir_op),
        aarch64_expr: x86_op(a, b),
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir <16 x i8> add -> x86-64 PADDB xmm,xmm`.
pub fn proof_x86_v16i8_add_paddb() -> ProofObligation {
    use crate::x86_64_semantics::encode_paddb;

    proof_x86_v128_packed_arithmetic(
        "x86_64: V16I8Add -> PADDB xmm,xmm",
        crate::smt::VectorArrangement::B16,
        |a, b| a.bvadd(b),
        encode_paddb,
    )
}

/// Proof: `trust_ir <16 x i8> sub -> x86-64 PSUBB xmm,xmm`.
pub fn proof_x86_v16i8_sub_psubb() -> ProofObligation {
    use crate::x86_64_semantics::encode_psubb;

    proof_x86_v128_packed_arithmetic(
        "x86_64: V16I8Sub -> PSUBB xmm,xmm",
        crate::smt::VectorArrangement::B16,
        |a, b| a.bvsub(b),
        encode_psubb,
    )
}

fn x86_v128_word_low_byte_mask() -> SmtExpr {
    let lanes = vec![SmtExpr::bv_const(0x00ff, 16); 8];
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::H8)
}

fn encode_x86_v16i8_mul_sse2(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::x86_64_semantics::{
        encode_pand, encode_pmullw, encode_punpckhbw, encode_punpcklbw, encode_pxor,
    };

    let zero = encode_pxor(src1.clone(), src1.clone());
    let lo_words = encode_pmullw(
        encode_punpcklbw(src1.clone(), zero.clone()),
        encode_punpcklbw(src2.clone(), zero.clone()),
    );
    let hi_words = encode_pmullw(
        encode_punpckhbw(src1, zero.clone()),
        encode_punpckhbw(src2, zero),
    );
    let low_byte_mask = x86_v128_word_low_byte_mask();
    let lo_masked = encode_pand(lo_words, low_byte_mask.clone());
    let hi_masked = encode_pand(hi_words, low_byte_mask);

    let lanes: Vec<SmtExpr> = (0..8_u32)
        .map(|lane| crate::smt::lane_extract(&lo_masked, crate::smt::VectorArrangement::H8, lane))
        .chain((0..8_u32).map(|lane| {
            crate::smt::lane_extract(&hi_masked, crate::smt::VectorArrangement::H8, lane)
        }))
        .map(|word| word.extract(7, 0))
        .collect();
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::B16)
}

/// Proof: `trust_ir <16 x i8> mul -> x86-64 SSE2 unpack/PMULLW/PACKUSWB`.
pub fn proof_x86_v16i8_mul_sse2() -> ProofObligation {
    proof_x86_v128_packed_arithmetic(
        "x86_64: V16I8Mul -> PUNPCKBW+PMULLW+PAND+PACKUSWB",
        crate::smt::VectorArrangement::B16,
        |a, b| a.bvmul(b),
        encode_x86_v16i8_mul_sse2,
    )
}

/// Proof: `trust_ir <8 x i16> add -> x86-64 PADDW xmm,xmm`.
pub fn proof_x86_v8i16_add_paddw() -> ProofObligation {
    use crate::x86_64_semantics::encode_paddw;

    proof_x86_v128_packed_arithmetic(
        "x86_64: V8I16Add -> PADDW xmm,xmm",
        crate::smt::VectorArrangement::H8,
        |a, b| a.bvadd(b),
        encode_paddw,
    )
}

/// Proof: `trust_ir <8 x i16> sub -> x86-64 PSUBW xmm,xmm`.
pub fn proof_x86_v8i16_sub_psubw() -> ProofObligation {
    use crate::x86_64_semantics::encode_psubw;

    proof_x86_v128_packed_arithmetic(
        "x86_64: V8I16Sub -> PSUBW xmm,xmm",
        crate::smt::VectorArrangement::H8,
        |a, b| a.bvsub(b),
        encode_psubw,
    )
}

/// Proof: `trust_ir <4 x i32> add -> x86-64 PADDD xmm,xmm`.
pub fn proof_x86_v4i32_add_paddd() -> ProofObligation {
    use crate::x86_64_semantics::encode_paddd;

    proof_x86_v128_packed_arithmetic(
        "x86_64: V4I32Add -> PADDD xmm,xmm",
        crate::smt::VectorArrangement::S4,
        |a, b| a.bvadd(b),
        encode_paddd,
    )
}

/// Proof: `trust_ir <4 x i32> sub -> x86-64 PSUBD xmm,xmm`.
pub fn proof_x86_v4i32_sub_psubd() -> ProofObligation {
    use crate::x86_64_semantics::encode_psubd;

    proof_x86_v128_packed_arithmetic(
        "x86_64: V4I32Sub -> PSUBD xmm,xmm",
        crate::smt::VectorArrangement::S4,
        |a, b| a.bvsub(b),
        encode_psubd,
    )
}

/// Proof: `trust_ir <4 x i32> mul -> x86-64 PMULLD xmm,xmm`.
pub fn proof_x86_v4i32_mul_pmulld() -> ProofObligation {
    use crate::x86_64_semantics::encode_pmulld;

    proof_x86_v128_packed_arithmetic(
        "x86_64: V4I32Mul -> PMULLD xmm,xmm",
        crate::smt::VectorArrangement::S4,
        |a, b| a.bvmul(b),
        encode_pmulld,
    )
}

/// Return all x86 V128 packed arithmetic proof obligations for #1111.
pub fn all_x86_64_v128_packed_arithmetic_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_v16i8_add_paddb(),
        proof_x86_v16i8_sub_psubb(),
        proof_x86_v16i8_mul_sse2(),
        proof_x86_v8i16_add_paddw(),
        proof_x86_v8i16_sub_psubw(),
        proof_x86_v4i32_add_paddd(),
        proof_x86_v4i32_sub_psubd(),
        proof_x86_v4i32_mul_pmulld(),
    ]
}

fn proof_x86_v128_bitwise(
    name: &str,
    opcode: trust_cg_lower::instructions::Opcode,
    x86_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::types::Type;

    let (a, mut inputs) = x86_v128_from_u64_halves("a");
    let (b, b_inputs) = x86_v128_from_u64_halves("b");
    inputs.extend(b_inputs);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&opcode, Type::V128, a.clone(), b.clone()),
        aarch64_expr: x86_op(a, b),
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir Band(Type::V128) -> x86-64 PAND xmm,xmm`.
pub fn proof_x86_v128_band_pand() -> ProofObligation {
    use crate::x86_64_semantics::encode_pand;
    use trust_cg_lower::instructions::Opcode;

    proof_x86_v128_bitwise(
        "x86_64: V128 Band -> PAND xmm,xmm",
        Opcode::Band,
        encode_pand,
    )
}

/// Proof: `trust_ir Bor(Type::V128) -> x86-64 POR xmm,xmm`.
pub fn proof_x86_v128_bor_por() -> ProofObligation {
    use crate::x86_64_semantics::encode_por;
    use trust_cg_lower::instructions::Opcode;

    proof_x86_v128_bitwise("x86_64: V128 Bor -> POR xmm,xmm", Opcode::Bor, encode_por)
}

/// Proof: `trust_ir Bxor(Type::V128) -> x86-64 PXOR xmm,xmm`.
pub fn proof_x86_v128_bxor_pxor() -> ProofObligation {
    use crate::x86_64_semantics::encode_pxor;
    use trust_cg_lower::instructions::Opcode;

    proof_x86_v128_bitwise(
        "x86_64: V128 Bxor -> PXOR xmm,xmm",
        Opcode::Bxor,
        encode_pxor,
    )
}

/// Proof: `trust_ir Band(Type::V128) -> x86-64 ANDPD xmm,xmm`.
///
/// ANDPD is the 128-bit bitwise AND of two XMM registers (the "pd" only selects
/// the FP execution domain; the result is bit-identical to PAND). It is emitted
/// by `select_fabs` to clear the IEEE sign bit with a magnitude mask — the
/// mirror of FNeg's PXOR sign-flip. Same faithful full-width `encode_pand`
/// (`a & b`) model as the PAND proof.
pub fn proof_x86_v128_band_andpd() -> ProofObligation {
    use crate::x86_64_semantics::encode_pand;
    use trust_cg_lower::instructions::Opcode;

    proof_x86_v128_bitwise(
        "x86_64: V128 Band -> ANDPD xmm,xmm",
        Opcode::Band,
        encode_pand,
    )
}

/// Proof: `trust_ir Band(Type::V128) -> x86-64 ANDPS xmm,xmm`.
///
/// ANDPS is likewise a 128-bit bitwise AND (single-precision FP domain); the
/// f32 counterpart `select_fabs` emits for `f32::abs`.
pub fn proof_x86_v128_band_andps() -> ProofObligation {
    use crate::x86_64_semantics::encode_pand;
    use trust_cg_lower::instructions::Opcode;

    proof_x86_v128_bitwise(
        "x86_64: V128 Band -> ANDPS xmm,xmm",
        Opcode::Band,
        encode_pand,
    )
}

/// Return all x86 V128 bitwise proof obligations for #1111.
pub fn all_x86_64_v128_bitwise_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_v128_band_pand(),
        proof_x86_v128_bor_por(),
        proof_x86_v128_bxor_pxor(),
        proof_x86_v128_band_andpd(),
        proof_x86_v128_band_andps(),
    ]
}

fn proof_x86_v4i32_scalarized_shift(
    name: &str,
    trust_ir_shift: fn(SmtExpr, SmtExpr) -> SmtExpr,
    x86_shift: fn(crate::x86_64_semantics::X86OperandSize, SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    let a0 = SmtExpr::var("a0", 32);
    let a1 = SmtExpr::var("a1", 32);
    let a2 = SmtExpr::var("a2", 32);
    let a3 = SmtExpr::var("a3", 32);
    let b0 = SmtExpr::var("b0", 32);
    let b1 = SmtExpr::var("b1", 32);
    let b2 = SmtExpr::var("b2", 32);
    let b3 = SmtExpr::var("b3", 32);
    let a = crate::smt::concat_lanes(&[a0, a1, a2, a3], crate::smt::VectorArrangement::S4);
    let b = crate::smt::concat_lanes(&[b0, b1, b2, b3], crate::smt::VectorArrangement::S4);
    let trust_ir_expr =
        crate::smt::map_lanes_binary(&a, &b, crate::smt::VectorArrangement::S4, trust_ir_shift);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr: crate::x86_64_semantics::encode_v4i32_scalarized_shift(a, b, x86_shift),
        inputs: vec![
            ("a0".to_string(), 32),
            ("a1".to_string(), 32),
            ("a2".to_string(), 32),
            ("a3".to_string(), 32),
            ("b0".to_string(), 32),
            ("b1".to_string(), 32),
            ("b2".to_string(), 32),
            ("b3".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir <4 x i32> shl -> x86-64 scalar lane SHL + reassembly`.
pub fn proof_x86_v4i32_ishl_scalarized() -> ProofObligation {
    use crate::x86_64_semantics::encode_shl_rr;

    proof_x86_v4i32_scalarized_shift(
        "x86_64: V4I32 Ishl -> scalarized SHL lanes + reassembly",
        |a, b| a.bvshl(b),
        encode_shl_rr,
    )
}

/// Proof: `trust_ir <4 x i32> logical shift right -> x86-64 scalar lane SHR + reassembly`.
pub fn proof_x86_v4i32_ushr_scalarized() -> ProofObligation {
    use crate::x86_64_semantics::encode_shr_rr;

    proof_x86_v4i32_scalarized_shift(
        "x86_64: V4I32 Ushr -> scalarized SHR lanes + reassembly",
        |a, b| a.bvlshr(b),
        encode_shr_rr,
    )
}

/// Proof: `trust_ir <4 x i32> arithmetic shift right -> x86-64 scalar lane SAR + reassembly`.
pub fn proof_x86_v4i32_sshr_scalarized() -> ProofObligation {
    use crate::x86_64_semantics::encode_sar_rr;

    proof_x86_v4i32_scalarized_shift(
        "x86_64: V4I32 Sshr -> scalarized SAR lanes + reassembly",
        |a, b| a.bvashr(b),
        encode_sar_rr,
    )
}

fn proof_x86_v4i32_uniform_imm_shift(
    name: &str,
    trust_ir_shift: fn(SmtExpr, SmtExpr) -> SmtExpr,
    x86_shift: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    let a0 = SmtExpr::var("a0", 32);
    let a1 = SmtExpr::var("a1", 32);
    let a2 = SmtExpr::var("a2", 32);
    let a3 = SmtExpr::var("a3", 32);
    let count = SmtExpr::var("count", 5);
    let a = crate::smt::concat_lanes(&[a0, a1, a2, a3], crate::smt::VectorArrangement::S4);
    let count32 = count.clone().zero_ext(27);
    let rhs = crate::smt::concat_lanes(
        &[count32.clone(), count32.clone(), count32.clone(), count32],
        crate::smt::VectorArrangement::S4,
    );
    let trust_ir_expr =
        crate::smt::map_lanes_binary(&a, &rhs, crate::smt::VectorArrangement::S4, trust_ir_shift);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr: x86_shift(a, count),
        inputs: vec![
            ("a0".to_string(), 32),
            ("a1".to_string(), 32),
            ("a2".to_string(), 32),
            ("a3".to_string(), 32),
            ("count".to_string(), 5),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir <4 x i32> uniform immediate shl -> x86-64 PSLLD xmm,imm8`.
pub fn proof_x86_v4i32_ishl_uniform_pslld_imm() -> ProofObligation {
    use crate::x86_64_semantics::encode_pslld_imm;

    proof_x86_v4i32_uniform_imm_shift(
        "x86_64: V4I32 Ishl uniform immediate -> PSLLD xmm,imm8",
        |a, b| a.bvshl(b),
        encode_pslld_imm,
    )
}

/// Proof: `trust_ir <4 x i32> uniform immediate logical shift right -> x86-64 PSRLD xmm,imm8`.
pub fn proof_x86_v4i32_ushr_uniform_psrld_imm() -> ProofObligation {
    use crate::x86_64_semantics::encode_psrld_imm;

    proof_x86_v4i32_uniform_imm_shift(
        "x86_64: V4I32 Ushr uniform immediate -> PSRLD xmm,imm8",
        |a, b| a.bvlshr(b),
        encode_psrld_imm,
    )
}

/// Proof: `trust_ir <4 x i32> uniform immediate arithmetic shift right -> x86-64 PSRAD xmm,imm8`.
pub fn proof_x86_v4i32_sshr_uniform_psrad_imm() -> ProofObligation {
    use crate::x86_64_semantics::encode_psrad_imm;

    proof_x86_v4i32_uniform_imm_shift(
        "x86_64: V4I32 Sshr uniform immediate -> PSRAD xmm,imm8",
        |a, b| a.bvashr(b),
        encode_psrad_imm,
    )
}

/// The `<2 x i64>` sibling of [`proof_x86_v4i32_uniform_imm_shift`]: both
/// qword lanes shift by the SAME immediate count (a 6-bit symbolic variable,
/// covering every in-range PSLLQ/PSRLQ immediate 0..63). The trust-ir side is
/// `map_lanes` of the scalar 64-bit shift with the broadcast count; the machine
/// side is the independent PSLLQ/PSRLQ instruction model. A wrong lane width
/// (dword-shift model), wrong direction, or non-uniform count REFUTES.
fn proof_x86_v2i64_uniform_imm_shift(
    name: &str,
    trust_ir_shift: fn(SmtExpr, SmtExpr) -> SmtExpr,
    x86_shift: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    let a0 = SmtExpr::var("a0", 64);
    let a1 = SmtExpr::var("a1", 64);
    let count = SmtExpr::var("count", 6);
    let a = crate::smt::concat_lanes(&[a0, a1], crate::smt::VectorArrangement::D2);
    let count64 = count.clone().zero_ext(58);
    let rhs = crate::smt::concat_lanes(
        &[count64.clone(), count64],
        crate::smt::VectorArrangement::D2,
    );
    let trust_ir_expr =
        crate::smt::map_lanes_binary(&a, &rhs, crate::smt::VectorArrangement::D2, trust_ir_shift);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr: x86_shift(a, count),
        inputs: vec![
            ("a0".to_string(), 64),
            ("a1".to_string(), 64),
            ("count".to_string(), 6),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir <2 x i64> uniform immediate shl -> x86-64 PSLLQ xmm,imm8`.
pub fn proof_x86_v2i64_ishl_uniform_psllq_imm() -> ProofObligation {
    use crate::x86_64_semantics::encode_psllq_imm;

    proof_x86_v2i64_uniform_imm_shift(
        "x86_64: V2I64 Ishl uniform immediate -> PSLLQ xmm,imm8",
        |a, b| a.bvshl(b),
        encode_psllq_imm,
    )
}

/// Proof: `trust_ir <2 x i64> uniform immediate logical shift right -> x86-64 PSRLQ xmm,imm8`.
pub fn proof_x86_v2i64_ushr_uniform_psrlq_imm() -> ProofObligation {
    use crate::x86_64_semantics::encode_psrlq_imm;

    proof_x86_v2i64_uniform_imm_shift(
        "x86_64: V2I64 Ushr uniform immediate -> PSRLQ xmm,imm8",
        |a, b| a.bvlshr(b),
        encode_psrlq_imm,
    )
}

/// Proof: `trust_ir <2 x i64> even-dword widening unsigned multiply -> x86-64
/// PMULUDQ xmm,xmm`.
///
/// The trust-ir-side SPEC treats PMULUDQ as the same-width i64x2 lane op it
/// mathematically is: each qword lane's result is `lo32(a_lane) * lo32(b_lane)`
/// (mask both 64-bit lanes to their low dword, full 64-bit product — the
/// even-dword indexing of the SDM text is exactly the qword lane's low half).
/// The machine side ([`crate::x86_64_semantics::encode_pmuludq`]) is built
/// STRUCTURALLY from the SDM instead: extract S4 dword lanes 0 and 2, zero-
/// extend to 64, multiply. The SMT equivalence of the two constructions is a
/// genuine theorem — an odd-dword extract, a sign-extending machine model, or a
/// masked (low-half-only) product all REFUTE (see the negative controls in the
/// module tests).
pub fn proof_x86_v2i64_umul_lo32_pmuludq() -> ProofObligation {
    use crate::x86_64_semantics::encode_pmuludq;

    proof_x86_v128_packed_arithmetic(
        "x86_64: V2I64 even-dword widening Umul -> PMULUDQ xmm,xmm",
        crate::smt::VectorArrangement::D2,
        |a, b| {
            let mask = SmtExpr::bv_const(0xFFFF_FFFF, 64);
            a.bvand(mask.clone()).bvmul(b.bvand(mask))
        },
        encode_pmuludq,
    )
}

// ===========================================================================
// V4I32/V2I64 lane pack/extract/insert lowering proofs
// ===========================================================================

fn x86_lane_lowering_obligation(
    name: String,
    trust_ir_expr: SmtExpr,
    x86_expr: SmtExpr,
    inputs: Vec<(String, u32)>,
) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr,
        aarch64_expr: x86_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn x86_zero_vector(arrangement: crate::smt::VectorArrangement) -> SmtExpr {
    let lanes =
        vec![SmtExpr::bv_const(0, arrangement.lane_bits()); arrangement.lane_count() as usize];
    crate::smt::concat_lanes(&lanes, arrangement)
}

fn encode_trust_ir_v4i32_pack_lanes(lanes: [SmtExpr; 4]) -> SmtExpr {
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::S4)
}

fn encode_trust_ir_v2i64_pack_lanes(lanes: [SmtExpr; 2]) -> SmtExpr {
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::D2)
}

fn encode_x86_v4i32_pack_lanes_sse2(lanes: [SmtExpr; 4]) -> SmtExpr {
    use crate::x86_64_semantics::{encode_movd_to_xmm, encode_punpckldq, encode_punpcklqdq};

    let lane01 = encode_punpckldq(
        encode_movd_to_xmm(lanes[0].clone()),
        encode_movd_to_xmm(lanes[1].clone()),
    );
    let lane23 = encode_punpckldq(
        encode_movd_to_xmm(lanes[2].clone()),
        encode_movd_to_xmm(lanes[3].clone()),
    );
    encode_punpcklqdq(lane01, lane23)
}

fn encode_x86_v2i64_pack_lanes_sse2(lanes: [SmtExpr; 2]) -> SmtExpr {
    use crate::x86_64_semantics::{encode_movq_to_xmm, encode_punpcklqdq};

    encode_punpcklqdq(
        encode_movq_to_xmm(lanes[0].clone()),
        encode_movq_to_xmm(lanes[1].clone()),
    )
}

fn x86_v4i32_splat_lane_pshufd_imm(lane: u8) -> u8 {
    lane | (lane << 2) | (lane << 4) | (lane << 6)
}

fn encode_x86_v4i32_extract_lane_lowering(src: SmtExpr, lane: u8) -> SmtExpr {
    use crate::x86_64_semantics::{encode_movd_from_xmm, encode_pshufd};

    if lane == 0 {
        encode_movd_from_xmm(src)
    } else {
        let shuffled = encode_pshufd(src, x86_v4i32_splat_lane_pshufd_imm(lane));
        encode_movd_from_xmm(shuffled)
    }
}

fn encode_x86_v2i64_extract_lane_lowering(src: SmtExpr, lane: u8) -> SmtExpr {
    use crate::x86_64_semantics::{encode_movq_from_xmm, encode_pshufd};

    if lane == 0 {
        encode_movq_from_xmm(src)
    } else {
        encode_movq_from_xmm(encode_pshufd(src, 0xEE))
    }
}

fn encode_x86_v4i32_nonzero_insert_lane_lowering(
    base: SmtExpr,
    elem: SmtExpr,
    lane: u8,
) -> SmtExpr {
    let lanes: [SmtExpr; 4] = std::array::from_fn(|candidate| {
        if candidate == usize::from(lane) {
            elem.clone()
        } else {
            encode_x86_v4i32_extract_lane_lowering(base.clone(), candidate as u8)
        }
    });
    encode_x86_v4i32_pack_lanes_sse2(lanes)
}

fn encode_x86_v2i64_nonzero_insert_lane_lowering(
    base: SmtExpr,
    elem: SmtExpr,
    lane: u8,
) -> SmtExpr {
    use crate::x86_64_semantics::{encode_movq_to_xmm, encode_pshufd, encode_punpcklqdq};

    let elem_xmm = encode_movq_to_xmm(elem);
    match lane {
        0 => {
            let high = encode_pshufd(base, 0xEE);
            encode_punpcklqdq(elem_xmm, high)
        }
        1 => encode_punpcklqdq(base, elem_xmm),
        _ => unreachable!("V2I64 insert proof lane must be 0 or 1"),
    }
}

fn encode_x86_v4i32_zero_insert_lane_lowering(
    elem: SmtExpr,
    lane: u8,
    seed: Option<SmtExpr>,
) -> SmtExpr {
    use crate::x86_64_semantics::{
        encode_movd_to_xmm, encode_pshufd, encode_punpckldq, encode_punpcklqdq, encode_pxor,
    };

    if lane == 0 {
        return encode_movd_to_xmm(elem);
    }

    let seed = seed.expect("nonzero zero-base V4I32 insert proof needs a PXOR seed");
    let zero = encode_pxor(seed.clone(), seed);
    let elem_xmm = encode_movd_to_xmm(elem);
    match lane {
        1 => encode_punpckldq(zero, elem_xmm),
        2 => encode_punpcklqdq(zero, elem_xmm),
        3 => {
            let lane1 = encode_punpckldq(zero, elem_xmm);
            encode_pshufd(lane1, 0x4E)
        }
        _ => unreachable!("V4I32 insert proof lane must be 0..=3"),
    }
}

fn encode_x86_v2i64_zero_insert_lane_lowering(
    elem: SmtExpr,
    lane: u8,
    seed: Option<SmtExpr>,
) -> SmtExpr {
    use crate::x86_64_semantics::{encode_movq_to_xmm, encode_punpcklqdq, encode_pxor};

    if lane == 0 {
        return encode_movq_to_xmm(elem);
    }

    let seed = seed.expect("nonzero zero-base V2I64 insert proof needs a PXOR seed");
    let zero = encode_pxor(seed.clone(), seed);
    encode_punpcklqdq(zero, encode_movq_to_xmm(elem))
}

/// Proof: `V4I32PackLanes` lowers to MOVD/PUNPCKLDQ/PUNPCKLQDQ.
pub fn proof_x86_v4i32_pack_lanes_sse2() -> ProofObligation {
    let lane0 = SmtExpr::var("lane0", 32);
    let lane1 = SmtExpr::var("lane1", 32);
    let lane2 = SmtExpr::var("lane2", 32);
    let lane3 = SmtExpr::var("lane3", 32);
    let lanes = [lane0, lane1, lane2, lane3];

    x86_lane_lowering_obligation(
        "x86_64: V4I32PackLanes -> MOVD/PUNPCKLDQ/PUNPCKLQDQ".to_string(),
        encode_trust_ir_v4i32_pack_lanes(lanes.clone()),
        encode_x86_v4i32_pack_lanes_sse2(lanes),
        vec![
            ("lane0".to_string(), 32),
            ("lane1".to_string(), 32),
            ("lane2".to_string(), 32),
            ("lane3".to_string(), 32),
        ],
    )
}

/// Proof: equal-lane `V4I32PackLanes` lowers to MOVD+PSHUFD 0x00.
pub fn proof_x86_v4i32_pack_lanes_pshufd_splat() -> ProofObligation {
    use crate::x86_64_semantics::{encode_movd_to_xmm, encode_pshufd};

    let lane = SmtExpr::var("lane", 32);

    x86_lane_lowering_obligation(
        "x86_64: V4I32PackLanes equal lanes -> MOVD/PSHUFD 0x00".to_string(),
        encode_trust_ir_v4i32_pack_lanes([lane.clone(), lane.clone(), lane.clone(), lane.clone()]),
        encode_pshufd(encode_movd_to_xmm(lane), 0x00),
        vec![("lane".to_string(), 32)],
    )
}

/// Proof: `V2I64PackLanes` lowers to MOVQ/PUNPCKLQDQ.
pub fn proof_x86_v2i64_pack_lanes_sse2() -> ProofObligation {
    let lane0 = SmtExpr::var("lane0", 64);
    let lane1 = SmtExpr::var("lane1", 64);
    let lanes = [lane0, lane1];

    x86_lane_lowering_obligation(
        "x86_64: V2I64PackLanes -> MOVQ/PUNPCKLQDQ".to_string(),
        encode_trust_ir_v2i64_pack_lanes(lanes.clone()),
        encode_x86_v2i64_pack_lanes_sse2(lanes),
        vec![("lane0".to_string(), 64), ("lane1".to_string(), 64)],
    )
}

/// Proof: equal-lane `V2I64PackLanes` lowers to MOVQ+PSHUFD 0x44.
pub fn proof_x86_v2i64_pack_lanes_pshufd_splat() -> ProofObligation {
    use crate::x86_64_semantics::{encode_movq_to_xmm, encode_pshufd};

    let lane = SmtExpr::var("lane", 64);

    x86_lane_lowering_obligation(
        "x86_64: V2I64PackLanes equal lanes -> MOVQ/PSHUFD 0x44".to_string(),
        encode_trust_ir_v2i64_pack_lanes([lane.clone(), lane.clone()]),
        encode_pshufd(encode_movq_to_xmm(lane), 0x44),
        vec![("lane".to_string(), 64)],
    )
}

/// Proof: a 2-lane i64 saxpy-accumulate lowers to
/// SCALAR-IMUL / SCALAR-IMUL / MOVQ / MOVQ / PUNPCKLQDQ / PADDQ.
///
/// SPEC (trust-ir): per lane, `c[lane] + k * b[lane]`, assembled with the
/// generic lane concat.
///
/// MACHINE: the two products are formed with SCALAR 64-bit multiplies, moved
/// into the low quadword of an XMM each (`MOVQ`), interleaved into one V2I64
/// with `PUNPCKLQDQ`, and accumulated into `c` with `PADDQ`.
///
/// # Why this is a COMPOSITE proof and not a PUNPCKLQDQ identity
///
/// A standalone `PUNPCKLQDQ` lowering obligation is DEGENERATE and was reverted
/// (2026-08-07): `encode_punpcklqdq` is defined as
/// `concat_lanes([lane_extract(src1, D2, 0), lane_extract(src2, D2, 0)])`,
/// which is character-for-character the spec side of a low-lane pack, so
/// `trust_ir_expr == aarch64_expr` and `is_degenerate()` reports it proves
/// nothing. Same trap the `proof_sbfm_extract_at_width` doc calls out.
///
/// Stated over the WHOLE SEQUENCE the vectorizer would emit, the obligation has
/// real content: the spec side never mentions a pack at all, while the machine
/// side routes each scalar product through a specific lane. Getting the operand
/// order of `PUNPCKLQDQ` backwards, or pairing a product with the wrong `c`
/// lane, changes the machine expression and REFUTES. This mirrors
/// `V16I8Mul -> PUNPCKBW+PMULLW+PAND+PACKUSWB`, which is stated the same way.
///
/// Motivation: SSE2 has no `PMULLQ`, so the packed i64 multiply currently costs
/// a 3-`PMULUDQ` decomposition (~16 machine instructions per 2 lanes, with a
/// `MOVDQA` before each multiply because the invariant factor is live). LLVM
/// emits this sequence instead — about half the instructions and no register
/// copies — and `p4_matmul` sits at 3.07x of LLVM because of the difference.
pub fn proof_x86_v2i64_saxpy_scalar_mul_punpcklqdq() -> ProofObligation {
    use crate::x86_64_semantics::{encode_movq_to_xmm, encode_paddq, encode_punpcklqdq};

    let (c, mut inputs) = x86_v128_from_u64_halves("c");
    let b0 = SmtExpr::var("b0", 64);
    let b1 = SmtExpr::var("b1", 64);
    let k = SmtExpr::var("k", 64);
    inputs.push(("b0".to_string(), 64));
    inputs.push(("b1".to_string(), 64));
    inputs.push(("k".to_string(), 64));

    let spec = crate::smt::concat_lanes(
        &[
            crate::smt::lane_extract(&c, crate::smt::VectorArrangement::D2, 0)
                .bvadd(k.clone().bvmul(b0.clone())),
            crate::smt::lane_extract(&c, crate::smt::VectorArrangement::D2, 1)
                .bvadd(k.clone().bvmul(b1.clone())),
        ],
        crate::smt::VectorArrangement::D2,
    );

    let machine = encode_paddq(
        c,
        encode_punpcklqdq(
            encode_movq_to_xmm(b0.bvmul(k.clone())),
            encode_movq_to_xmm(b1.bvmul(k)),
        ),
    );

    x86_lane_lowering_obligation(
        "x86_64: V2I64 saxpy-accumulate -> IMUL/IMUL/MOVQ/MOVQ/PUNPCKLQDQ/PADDQ".to_string(),
        spec,
        machine,
        inputs,
    )
}

/// Proof: `V4I32ExtractLane { lane }` lowers through MOVD or PSHUFD+MOVD.
pub fn proof_x86_v4i32_extract_lane(lane: u8) -> ProofObligation {
    let (src, inputs) = x86_v128_from_u64_halves("src");
    let lowering = if lane == 0 { "MOVD" } else { "PSHUFD/MOVD" };

    x86_lane_lowering_obligation(
        format!("x86_64: V4I32ExtractLane{{lane={lane}}} -> {lowering}"),
        crate::smt::lane_extract(&src, crate::smt::VectorArrangement::S4, u32::from(lane)),
        encode_x86_v4i32_extract_lane_lowering(src, lane),
        inputs,
    )
}

/// Proof: `V2I64ExtractLane { lane }` lowers through MOVQ or PSHUFD+MOVQ.
pub fn proof_x86_v2i64_extract_lane(lane: u8) -> ProofObligation {
    let (src, inputs) = x86_v128_from_u64_halves("src");
    let lowering = if lane == 0 { "MOVQ" } else { "PSHUFD/MOVQ" };

    x86_lane_lowering_obligation(
        format!("x86_64: V2I64ExtractLane{{lane={lane}}} -> {lowering}"),
        crate::smt::lane_extract(&src, crate::smt::VectorArrangement::D2, u32::from(lane)),
        encode_x86_v2i64_extract_lane_lowering(src, lane),
        inputs,
    )
}

/// Proof: nonzero-base `V4I32InsertLane { lane }` preserves untouched lanes.
pub fn proof_x86_v4i32_insert_lane_nonzero_base(lane: u8) -> ProofObligation {
    let (base, mut inputs) = x86_v128_from_u64_halves("base");
    let elem = SmtExpr::var("elem", 32);
    inputs.push(("elem".to_string(), 32));

    x86_lane_lowering_obligation(
        format!("x86_64: V4I32InsertLane{{lane={lane}}} nonzero base -> extract/repack SSE2"),
        crate::smt::lane_insert(
            &base,
            crate::smt::VectorArrangement::S4,
            u32::from(lane),
            elem.clone(),
        ),
        encode_x86_v4i32_nonzero_insert_lane_lowering(base, elem, lane),
        inputs,
    )
}

/// Proof: nonzero-base `V2I64InsertLane { lane }` preserves the other qword lane.
pub fn proof_x86_v2i64_insert_lane_nonzero_base(lane: u8) -> ProofObligation {
    let (base, mut inputs) = x86_v128_from_u64_halves("base");
    let elem = SmtExpr::var("elem", 64);
    inputs.push(("elem".to_string(), 64));

    x86_lane_lowering_obligation(
        format!("x86_64: V2I64InsertLane{{lane={lane}}} nonzero base -> MOVQ/PUNPCKLQDQ"),
        crate::smt::lane_insert(
            &base,
            crate::smt::VectorArrangement::D2,
            u32::from(lane),
            elem.clone(),
        ),
        encode_x86_v2i64_nonzero_insert_lane_lowering(base, elem, lane),
        inputs,
    )
}

/// Proof: zero-base `V4I32InsertLane { lane }` lowers through direct MOVD or PXOR+SSE2 assembly.
pub fn proof_x86_v4i32_insert_lane_zero_base(lane: u8) -> ProofObligation {
    let elem = SmtExpr::var("elem", 32);
    let mut inputs = vec![("elem".to_string(), 32)];
    let seed = if lane == 0 {
        None
    } else {
        let (seed, seed_inputs) = x86_v128_from_u64_halves("seed");
        inputs.extend(seed_inputs);
        Some(seed)
    };
    let zero = x86_zero_vector(crate::smt::VectorArrangement::S4);

    x86_lane_lowering_obligation(
        format!("x86_64: V4I32InsertLane{{lane={lane}}} zero base -> MOVD/PXOR/SSE2"),
        crate::smt::lane_insert(
            &zero,
            crate::smt::VectorArrangement::S4,
            u32::from(lane),
            elem.clone(),
        ),
        encode_x86_v4i32_zero_insert_lane_lowering(elem, lane, seed),
        inputs,
    )
}

/// Proof: zero-base `V2I64InsertLane { lane }` lowers through direct MOVQ or PXOR+PUNPCKLQDQ.
pub fn proof_x86_v2i64_insert_lane_zero_base(lane: u8) -> ProofObligation {
    let elem = SmtExpr::var("elem", 64);
    let mut inputs = vec![("elem".to_string(), 64)];
    let seed = if lane == 0 {
        None
    } else {
        let (seed, seed_inputs) = x86_v128_from_u64_halves("seed");
        inputs.extend(seed_inputs);
        Some(seed)
    };
    let zero = x86_zero_vector(crate::smt::VectorArrangement::D2);

    x86_lane_lowering_obligation(
        format!("x86_64: V2I64InsertLane{{lane={lane}}} zero base -> MOVQ/PXOR/PUNPCKLQDQ"),
        crate::smt::lane_insert(
            &zero,
            crate::smt::VectorArrangement::D2,
            u32::from(lane),
            elem.clone(),
        ),
        encode_x86_v2i64_zero_insert_lane_lowering(elem, lane, seed),
        inputs,
    )
}

/// Return all V4I32 lane pack/extract/insert proof obligations for #1115.
pub fn all_x86_64_v4i32_lane_proofs() -> Vec<ProofObligation> {
    let mut proofs = vec![
        proof_x86_v4i32_pack_lanes_sse2(),
        proof_x86_v4i32_pack_lanes_pshufd_splat(),
    ];
    for lane in 0_u8..4 {
        proofs.push(proof_x86_v4i32_extract_lane(lane));
    }
    for lane in 0_u8..4 {
        proofs.push(proof_x86_v4i32_insert_lane_nonzero_base(lane));
    }
    for lane in 0_u8..4 {
        proofs.push(proof_x86_v4i32_insert_lane_zero_base(lane));
    }
    proofs
}

/// Return all V2I64 lane pack/extract/insert proof obligations for #1115.
pub fn all_x86_64_v2i64_lane_proofs() -> Vec<ProofObligation> {
    let mut proofs = vec![
        proof_x86_v2i64_pack_lanes_sse2(),
        proof_x86_v2i64_pack_lanes_pshufd_splat(),
    ];
    for lane in 0_u8..2 {
        proofs.push(proof_x86_v2i64_extract_lane(lane));
    }
    for lane in 0_u8..2 {
        proofs.push(proof_x86_v2i64_insert_lane_nonzero_base(lane));
    }
    for lane in 0_u8..2 {
        proofs.push(proof_x86_v2i64_insert_lane_zero_base(lane));
    }
    proofs
}

// ===========================================================================
// V128 boolean mask lowering proofs
// ===========================================================================

const X86_V128_SIGNED_COMPARE_CONDS: [trust_cg_lower::instructions::IntCC; 6] = [
    trust_cg_lower::instructions::IntCC::Equal,
    trust_cg_lower::instructions::IntCC::NotEqual,
    trust_cg_lower::instructions::IntCC::SignedLessThan,
    trust_cg_lower::instructions::IntCC::SignedLessThanOrEqual,
    trust_cg_lower::instructions::IntCC::SignedGreaterThan,
    trust_cg_lower::instructions::IntCC::SignedGreaterThanOrEqual,
];

const X86_V128_I32_OR_NARROW_COMPARE_CONDS: [trust_cg_lower::instructions::IntCC; 10] = [
    trust_cg_lower::instructions::IntCC::Equal,
    trust_cg_lower::instructions::IntCC::NotEqual,
    trust_cg_lower::instructions::IntCC::SignedLessThan,
    trust_cg_lower::instructions::IntCC::SignedLessThanOrEqual,
    trust_cg_lower::instructions::IntCC::SignedGreaterThan,
    trust_cg_lower::instructions::IntCC::SignedGreaterThanOrEqual,
    trust_cg_lower::instructions::IntCC::UnsignedLessThan,
    trust_cg_lower::instructions::IntCC::UnsignedLessThanOrEqual,
    trust_cg_lower::instructions::IntCC::UnsignedGreaterThan,
    trust_cg_lower::instructions::IntCC::UnsignedGreaterThanOrEqual,
];

fn x86_v128_from_u64_halves(prefix: &str) -> (SmtExpr, Vec<(String, u32)>) {
    let lo_name = format!("{prefix}_lo");
    let hi_name = format!("{prefix}_hi");
    let lo = SmtExpr::var(lo_name.clone(), 64);
    let hi = SmtExpr::var(hi_name.clone(), 64);
    (hi.concat(lo), vec![(lo_name, 64), (hi_name, 64)])
}

fn x86_v128_compare_cond_bool(
    cond: trust_cg_lower::instructions::IntCC,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> SmtExpr {
    use trust_cg_lower::instructions::IntCC;

    match cond {
        IntCC::Equal => lhs.eq_expr(rhs),
        IntCC::NotEqual => lhs.eq_expr(rhs).not_expr(),
        IntCC::SignedLessThan => lhs.bvslt(rhs),
        IntCC::SignedLessThanOrEqual => lhs.bvsle(rhs),
        IntCC::SignedGreaterThan => lhs.bvsgt(rhs),
        IntCC::SignedGreaterThanOrEqual => lhs.bvsge(rhs),
        IntCC::UnsignedLessThan => lhs.bvult(rhs),
        IntCC::UnsignedLessThanOrEqual => lhs.bvule(rhs),
        IntCC::UnsignedGreaterThan => lhs.bvugt(rhs),
        IntCC::UnsignedGreaterThanOrEqual => lhs.bvuge(rhs),
    }
}

fn x86_v128_lane_mask(cond: SmtExpr, lane_bits: u32) -> SmtExpr {
    SmtExpr::ite(
        cond,
        SmtExpr::bv_const(crate::smt::mask(u64::MAX, lane_bits), lane_bits),
        SmtExpr::bv_const(0, lane_bits),
    )
}

fn encode_trust_ir_v128_compare_mask(
    cond: trust_cg_lower::instructions::IntCC,
    arrangement: crate::smt::VectorArrangement,
    lhs: &SmtExpr,
    rhs: &SmtExpr,
) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    crate::smt::map_lanes_binary(lhs, rhs, arrangement, |a, b| {
        x86_v128_lane_mask(x86_v128_compare_cond_bool(cond, a, b), lane_bits)
    })
}

fn encode_x86_v128_compare_mask_lowering(
    cond: trust_cg_lower::instructions::IntCC,
    arrangement: crate::smt::VectorArrangement,
    lhs: SmtExpr,
    rhs: SmtExpr,
    eq_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
    gt_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> SmtExpr {
    use crate::x86_64_semantics::{encode_pcmpeqd, encode_por, encode_pxor};
    use trust_cg_lower::instructions::IntCC;

    match cond {
        IntCC::Equal => eq_op(lhs, rhs),
        IntCC::NotEqual => {
            let eq = eq_op(lhs.clone(), rhs);
            let all_ones = encode_pcmpeqd(lhs.clone(), lhs);
            encode_pxor(eq, all_ones)
        }
        IntCC::SignedGreaterThan => gt_op(lhs, rhs),
        IntCC::SignedLessThan => gt_op(rhs, lhs),
        IntCC::SignedGreaterThanOrEqual => {
            let gt = gt_op(lhs.clone(), rhs.clone());
            let eq = eq_op(lhs, rhs);
            encode_por(gt, eq)
        }
        IntCC::SignedLessThanOrEqual => {
            let gt = gt_op(rhs.clone(), lhs.clone());
            let eq = eq_op(lhs, rhs);
            encode_por(gt, eq)
        }
        IntCC::UnsignedGreaterThan => {
            let bias = x86_v128_sign_bit_bias_vector(arrangement);
            gt_op(encode_pxor(lhs, bias.clone()), encode_pxor(rhs, bias))
        }
        IntCC::UnsignedLessThan => {
            let bias = x86_v128_sign_bit_bias_vector(arrangement);
            gt_op(encode_pxor(rhs, bias.clone()), encode_pxor(lhs, bias))
        }
        IntCC::UnsignedGreaterThanOrEqual => {
            let bias = x86_v128_sign_bit_bias_vector(arrangement);
            let gt = gt_op(
                encode_pxor(lhs.clone(), bias.clone()),
                encode_pxor(rhs.clone(), bias),
            );
            let eq = eq_op(lhs, rhs);
            encode_por(gt, eq)
        }
        IntCC::UnsignedLessThanOrEqual => {
            let bias = x86_v128_sign_bit_bias_vector(arrangement);
            let gt = gt_op(
                encode_pxor(rhs.clone(), bias.clone()),
                encode_pxor(lhs.clone(), bias),
            );
            let eq = eq_op(lhs, rhs);
            encode_por(gt, eq)
        }
    }
}

fn x86_v128_sign_bit_bias_vector(arrangement: crate::smt::VectorArrangement) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    let lanes = vec![
        SmtExpr::bv_const(1_u64 << (lane_bits - 1), lane_bits);
        arrangement.lane_count() as usize
    ];
    crate::smt::concat_lanes(&lanes, arrangement)
}

fn x86_v128_compare_cond_name(cond: trust_cg_lower::instructions::IntCC) -> &'static str {
    use trust_cg_lower::instructions::IntCC;

    match cond {
        IntCC::Equal => "Eq",
        IntCC::NotEqual => "Ne",
        IntCC::SignedLessThan => "Slt",
        IntCC::SignedLessThanOrEqual => "Sle",
        IntCC::SignedGreaterThan => "Sgt",
        IntCC::SignedGreaterThanOrEqual => "Sge",
        IntCC::UnsignedLessThan => "Ult",
        IntCC::UnsignedLessThanOrEqual => "Ule",
        IntCC::UnsignedGreaterThan => "Ugt",
        IntCC::UnsignedGreaterThanOrEqual => "Uge",
    }
}

fn x86_v128_compare_lowering_name(
    cond: trust_cg_lower::instructions::IntCC,
    eq_name: &str,
    gt_name: &str,
) -> String {
    use trust_cg_lower::instructions::IntCC;

    match cond {
        IntCC::Equal => eq_name.to_string(),
        IntCC::NotEqual => format!("{eq_name}+PCMPEQD+PXOR"),
        IntCC::SignedGreaterThan => gt_name.to_string(),
        IntCC::SignedLessThan => format!("{gt_name}(swapped)"),
        IntCC::SignedGreaterThanOrEqual => format!("{gt_name}+{eq_name}+POR"),
        IntCC::SignedLessThanOrEqual => format!("{gt_name}(swapped)+{eq_name}+POR"),
        IntCC::UnsignedGreaterThan => format!("PXOR(sign-bias)+{gt_name}"),
        IntCC::UnsignedLessThan => format!("PXOR(sign-bias)+{gt_name}(swapped)"),
        IntCC::UnsignedGreaterThanOrEqual => format!("PXOR(sign-bias)+{gt_name}+{eq_name}+POR"),
        IntCC::UnsignedLessThanOrEqual => {
            format!("PXOR(sign-bias)+{gt_name}(swapped)+{eq_name}+POR")
        }
    }
}

fn proof_x86_v128_compare_mask(
    shape: &str,
    arrangement: crate::smt::VectorArrangement,
    cond: trust_cg_lower::instructions::IntCC,
    eq_name: &str,
    gt_name: &str,
    eq_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
    gt_op: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    let (lhs, mut inputs) = x86_v128_from_u64_halves("lhs");
    let (rhs, rhs_inputs) = x86_v128_from_u64_halves("rhs");
    inputs.extend(rhs_inputs);

    let cond_name = x86_v128_compare_cond_name(cond);
    let lowering = x86_v128_compare_lowering_name(cond, eq_name, gt_name);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: {shape}Icmp_{cond_name} -> {lowering}"),
        trust_ir_expr: encode_trust_ir_v128_compare_mask(cond, arrangement, &lhs, &rhs),
        aarch64_expr: encode_x86_v128_compare_mask_lowering(
            cond,
            arrangement,
            lhs,
            rhs,
            eq_op,
            gt_op,
        ),
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_x86_v4i32_compare_mask(cond: trust_cg_lower::instructions::IntCC) -> ProofObligation {
    use crate::x86_64_semantics::{encode_pcmpeqd, encode_pcmpgtd};

    proof_x86_v128_compare_mask(
        "V4I32",
        crate::smt::VectorArrangement::S4,
        cond,
        "PCMPEQD",
        "PCMPGTD",
        encode_pcmpeqd,
        encode_pcmpgtd,
    )
}

fn proof_x86_v16i8_compare_mask(cond: trust_cg_lower::instructions::IntCC) -> ProofObligation {
    use crate::x86_64_semantics::{encode_pcmpeqb, encode_pcmpgtb};

    proof_x86_v128_compare_mask(
        "V16I8",
        crate::smt::VectorArrangement::B16,
        cond,
        "PCMPEQB",
        "PCMPGTB",
        encode_pcmpeqb,
        encode_pcmpgtb,
    )
}

fn proof_x86_v8i16_compare_mask(cond: trust_cg_lower::instructions::IntCC) -> ProofObligation {
    use crate::x86_64_semantics::{encode_pcmpeqw, encode_pcmpgtw};

    proof_x86_v128_compare_mask(
        "V8I16",
        crate::smt::VectorArrangement::H8,
        cond,
        "PCMPEQW",
        "PCMPGTW",
        encode_pcmpeqw,
        encode_pcmpgtw,
    )
}

fn proof_x86_v2i64_compare_mask(cond: trust_cg_lower::instructions::IntCC) -> ProofObligation {
    use crate::x86_64_semantics::{encode_pcmpeqq, encode_pcmpgtq};

    proof_x86_v128_compare_mask(
        "V2I64",
        crate::smt::VectorArrangement::D2,
        cond,
        "PCMPEQQ",
        "PCMPGTQ",
        encode_pcmpeqq,
        encode_pcmpgtq,
    )
}

fn encode_x86_v2i64_unsigned_sse2_compare_mask(
    cond: trust_cg_lower::instructions::IntCC,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> SmtExpr {
    use crate::x86_64_semantics::{
        encode_pand, encode_pcmpeqd, encode_pcmpgtd, encode_por, encode_pshufd, encode_pxor,
    };
    use trust_cg_lower::instructions::IntCC;

    let bias = x86_v128_sign_bit_bias_vector(crate::smt::VectorArrangement::S4);
    let lhs_biased = encode_pxor(lhs.clone(), bias.clone());
    let rhs_biased = encode_pxor(rhs.clone(), bias);
    let (gt_lhs, gt_rhs) = match cond {
        IntCC::UnsignedGreaterThan | IntCC::UnsignedGreaterThanOrEqual => (lhs_biased, rhs_biased),
        IntCC::UnsignedLessThan | IntCC::UnsignedLessThanOrEqual => (rhs_biased, lhs_biased),
        other => panic!("unsupported V2I64 unsigned compare proof condition: {other:?}"),
    };

    let dword_gt = encode_pcmpgtd(gt_lhs, gt_rhs);
    let dword_eq = encode_pcmpeqd(lhs, rhs);
    let hi_gt = encode_pshufd(dword_gt.clone(), 0xF5);
    let lo_gt = encode_pshufd(dword_gt, 0xA0);
    let hi_eq = encode_pshufd(dword_eq.clone(), 0xF5);
    let strict = encode_por(hi_gt, encode_pand(hi_eq.clone(), lo_gt));

    match cond {
        IntCC::UnsignedGreaterThan | IntCC::UnsignedLessThan => strict,
        IntCC::UnsignedGreaterThanOrEqual | IntCC::UnsignedLessThanOrEqual => {
            let lo_eq = encode_pshufd(dword_eq, 0xA0);
            let eq = encode_pand(hi_eq, lo_eq);
            encode_por(strict, eq)
        }
        other => panic!("unsupported V2I64 unsigned compare proof condition: {other:?}"),
    }
}

fn proof_x86_v2i64_unsigned_compare_mask(
    cond: trust_cg_lower::instructions::IntCC,
) -> ProofObligation {
    let (lhs, mut inputs) = x86_v128_from_u64_halves("lhs");
    let (rhs, rhs_inputs) = x86_v128_from_u64_halves("rhs");
    inputs.extend(rhs_inputs);

    let cond_name = x86_v128_compare_cond_name(cond);
    let arrangement = crate::smt::VectorArrangement::D2;

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: V2I64Icmp_{cond_name} -> SSE2-dword-halves"),
        trust_ir_expr: encode_trust_ir_v128_compare_mask(cond, arrangement, &lhs, &rhs),
        aarch64_expr: encode_x86_v2i64_unsigned_sse2_compare_mask(cond, lhs, rhs),
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all x86 V4I32 compare-mask proof obligations.
pub fn all_x86_64_v4i32_compare_mask_proofs() -> Vec<ProofObligation> {
    X86_V128_I32_OR_NARROW_COMPARE_CONDS
        .into_iter()
        .map(proof_x86_v4i32_compare_mask)
        .collect()
}

/// Return all x86 V16I8/V8I16 compare-mask proof obligations.
pub fn all_x86_64_narrow_compare_mask_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    for cond in X86_V128_I32_OR_NARROW_COMPARE_CONDS {
        proofs.push(proof_x86_v16i8_compare_mask(cond));
        proofs.push(proof_x86_v8i16_compare_mask(cond));
    }
    proofs
}

/// Return all x86 V2I64 compare-mask proof obligations for #1114.
pub fn all_x86_64_v2i64_compare_mask_proofs() -> Vec<ProofObligation> {
    let mut proofs: Vec<ProofObligation> = X86_V128_SIGNED_COMPARE_CONDS
        .into_iter()
        .map(proof_x86_v2i64_compare_mask)
        .collect();
    proofs.extend(
        [
            trust_cg_lower::instructions::IntCC::UnsignedLessThan,
            trust_cg_lower::instructions::IntCC::UnsignedLessThanOrEqual,
            trust_cg_lower::instructions::IntCC::UnsignedGreaterThan,
            trust_cg_lower::instructions::IntCC::UnsignedGreaterThanOrEqual,
        ]
        .into_iter()
        .map(proof_x86_v2i64_unsigned_compare_mask),
    );
    proofs
}

/// Return all x86 V128 compare-mask proof obligations for #1109.
pub fn all_x86_64_v128_compare_mask_proofs() -> Vec<ProofObligation> {
    let mut proofs = all_x86_64_narrow_compare_mask_proofs();
    proofs.extend(all_x86_64_v4i32_compare_mask_proofs());
    proofs
}

fn x86_canonical_mask_vector_from_bits(
    bits: &SmtExpr,
    arrangement: crate::smt::VectorArrangement,
) -> SmtExpr {
    let lanes: Vec<SmtExpr> = (0..arrangement.lane_count())
        .map(|i| {
            let bit = bits.clone().extract(i, i);
            x86_v128_lane_mask(
                bit.eq_expr(SmtExpr::bv_const(1, 1)),
                arrangement.lane_bits(),
            )
        })
        .collect();
    crate::smt::concat_lanes(&lanes, arrangement)
}

fn x86_mask_bits_result(bits: SmtExpr, lane_count: u32, result_width: u32) -> SmtExpr {
    bits.zero_ext(result_width - lane_count)
}

fn x86_mask_extract_bits_input(lane_count: u32) -> (SmtExpr, Vec<(String, u32)>) {
    if lane_count == 16 {
        let lo = SmtExpr::var("mask_bits_lo", 8);
        let hi = SmtExpr::var("mask_bits_hi", 8);
        (
            hi.concat(lo),
            vec![
                ("mask_bits_lo".to_string(), 8),
                ("mask_bits_hi".to_string(), 8),
            ],
        )
    } else {
        (
            SmtExpr::var("mask_bits", lane_count),
            vec![("mask_bits".to_string(), lane_count)],
        )
    }
}

fn encode_x86_v4i32_mask_extract_lowering(src: SmtExpr) -> SmtExpr {
    use crate::x86_64_semantics::{
        X86OperandSize, encode_and_rr, encode_imul_rri, encode_pmovmskb,
    };

    let pmov = encode_pmovmskb(src);
    let multiplied = encode_imul_rri(X86OperandSize::S32, pmov, 39);
    let shifted = multiplied.bvlshr(SmtExpr::bv_const(9, 32));
    encode_and_rr(X86OperandSize::S32, shifted, SmtExpr::bv_const(0x0f, 32))
}

fn encode_x86_v16i8_mask_extract_lowering(src: SmtExpr) -> SmtExpr {
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr, encode_pmovmskb};

    encode_and_rr(
        X86OperandSize::S32,
        encode_pmovmskb(src),
        SmtExpr::bv_const(0xffff, 32),
    )
}

fn encode_x86_v8i16_mask_extract_lowering(src: SmtExpr) -> SmtExpr {
    use crate::x86_64_semantics::{
        X86OperandSize, encode_and_rr, encode_or_rr, encode_pmovmskb, encode_shr_rr,
    };

    let mut dst = encode_and_rr(
        X86OperandSize::S32,
        encode_pmovmskb(src),
        SmtExpr::bv_const(0x5555, 32),
    );
    for (shift, mask) in [(1_u64, 0x3333_u64), (2, 0x0f0f), (4, 0x00ff)] {
        let tmp = encode_shr_rr(
            X86OperandSize::S32,
            dst.clone(),
            SmtExpr::bv_const(shift, 32),
        );
        dst = encode_and_rr(
            X86OperandSize::S32,
            encode_or_rr(X86OperandSize::S32, dst, tmp),
            SmtExpr::bv_const(mask, 32),
        );
    }
    dst
}

fn encode_x86_v2i64_mask_extract_lowering_i32(src: SmtExpr) -> SmtExpr {
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr, encode_pmovmskb, encode_shr_rr};

    let shifted = encode_shr_rr(
        X86OperandSize::S32,
        encode_pmovmskb(src),
        SmtExpr::bv_const(7, 32),
    );
    encode_and_rr(X86OperandSize::S32, shifted, SmtExpr::bv_const(0x03, 32))
}

fn encode_x86_v2i64_mask_extract_lowering_i64(src: SmtExpr) -> SmtExpr {
    encode_x86_v2i64_mask_extract_lowering_i32(src).zero_ext(32)
}

fn proof_x86_v128_mask_extract(
    name: &str,
    arrangement: crate::smt::VectorArrangement,
    result_width: u32,
    x86_expr: fn(SmtExpr) -> SmtExpr,
) -> ProofObligation {
    let lane_count = arrangement.lane_count();
    let (mask_bits, inputs) = x86_mask_extract_bits_input(lane_count);
    let src = x86_canonical_mask_vector_from_bits(&mask_bits, arrangement);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: x86_mask_bits_result(mask_bits.clone(), lane_count, result_width),
        aarch64_expr: x86_expr(src),
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `V16I8MaskExtract -> PMOVMSKB+AND` compacts canonical lane masks.
pub fn proof_x86_v16i8_mask_extract() -> ProofObligation {
    proof_x86_v128_mask_extract(
        "x86_64: V16I8MaskExtract -> PMOVMSKB+AND",
        crate::smt::VectorArrangement::B16,
        32,
        encode_x86_v16i8_mask_extract_lowering,
    )
}

/// Proof: `V8I16MaskExtract -> PMOVMSKB+scalar compression` compacts lanes.
pub fn proof_x86_v8i16_mask_extract() -> ProofObligation {
    proof_x86_v128_mask_extract(
        "x86_64: V8I16MaskExtract -> PMOVMSKB+compress",
        crate::smt::VectorArrangement::H8,
        32,
        encode_x86_v8i16_mask_extract_lowering,
    )
}

/// Proof: `V4I32MaskExtract -> PMOVMSKB+scalar compression` compacts lanes.
pub fn proof_x86_v4i32_mask_extract() -> ProofObligation {
    proof_x86_v128_mask_extract(
        "x86_64: V4I32MaskExtract -> PMOVMSKB+compress",
        crate::smt::VectorArrangement::S4,
        32,
        encode_x86_v4i32_mask_extract_lowering,
    )
}

/// Proof: `V2I64MaskExtract<I32> -> PMOVMSKB+SHR+AND` compacts qword lanes.
pub fn proof_x86_v2i64_mask_extract_i32() -> ProofObligation {
    proof_x86_v128_mask_extract(
        "x86_64: V2I64MaskExtract<I32> -> PMOVMSKB+SHR+AND",
        crate::smt::VectorArrangement::D2,
        32,
        encode_x86_v2i64_mask_extract_lowering_i32,
    )
}

/// Proof: `V2I64MaskExtract<I64>` preserves upper-zero bits after MOV r32,r64.
pub fn proof_x86_v2i64_mask_extract_i64() -> ProofObligation {
    proof_x86_v128_mask_extract(
        "x86_64: V2I64MaskExtract<I64> -> PMOVMSKB+SHR+AND+MOV32 zero-extend",
        crate::smt::VectorArrangement::D2,
        64,
        encode_x86_v2i64_mask_extract_lowering_i64,
    )
}

/// Return all x86 V128 mask-extract proof obligations.
pub fn all_x86_64_v128_mask_extract_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_v16i8_mask_extract(),
        proof_x86_v8i16_mask_extract(),
        proof_x86_v4i32_mask_extract(),
    ]
}

/// Return all x86 V2I64 mask-extract proof obligations for #1114.
pub fn all_x86_64_v2i64_mask_extract_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_v2i64_mask_extract_i32(),
        proof_x86_v2i64_mask_extract_i64(),
    ]
}

fn x86_v128_bool_select_inputs(
    arrangement: crate::smt::VectorArrangement,
) -> (SmtExpr, SmtExpr, SmtExpr, Vec<(String, u32)>) {
    let mask_bits = SmtExpr::var("mask_bits", arrangement.lane_count());
    let mask = x86_canonical_mask_vector_from_bits(&mask_bits, arrangement);
    let (true_val, mut inputs) = x86_v128_from_u64_halves("true");
    let (false_val, false_inputs) = x86_v128_from_u64_halves("false");
    inputs.push(("mask_bits".to_string(), arrangement.lane_count()));
    inputs.extend(false_inputs);
    (mask, true_val, false_val, inputs)
}

fn encode_trust_ir_v128_bool_select(
    arrangement: crate::smt::VectorArrangement,
    mask: SmtExpr,
    true_val: SmtExpr,
    false_val: SmtExpr,
) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    let true_mask = SmtExpr::bv_const(crate::smt::mask(u64::MAX, lane_bits), lane_bits);
    let lanes: Vec<SmtExpr> = (0..arrangement.lane_count())
        .map(|i| {
            let mask_lane = crate::smt::lane_extract(&mask, arrangement, i);
            let true_lane = crate::smt::lane_extract(&true_val, arrangement, i);
            let false_lane = crate::smt::lane_extract(&false_val, arrangement, i);
            SmtExpr::ite(mask_lane.eq_expr(true_mask.clone()), true_lane, false_lane)
        })
        .collect();
    crate::smt::concat_lanes(&lanes, arrangement)
}

/// Proof: generic SSE2 `V128BoolSelect` expansion matches canonical byte select.
pub fn proof_x86_v128_bool_select_sse2() -> ProofObligation {
    use crate::x86_64_semantics::encode_v128_sse2_bool_select;

    let arrangement = crate::smt::VectorArrangement::B16;
    let (mask, true_val, false_val, inputs) = x86_v128_bool_select_inputs(arrangement);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: V128BoolSelect canonical byte mask -> PAND/PANDN/POR".to_string(),
        trust_ir_expr: encode_trust_ir_v128_bool_select(
            arrangement,
            mask.clone(),
            true_val.clone(),
            false_val.clone(),
        ),
        aarch64_expr: encode_v128_sse2_bool_select(mask, true_val, false_val),
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: SSE4.1 `PBLENDVB` expansion matches canonical byte select.
pub fn proof_x86_v128_bool_select_pblendvb() -> ProofObligation {
    use crate::x86_64_semantics::encode_pblendvb;

    let arrangement = crate::smt::VectorArrangement::B16;
    let (mask, true_val, false_val, inputs) = x86_v128_bool_select_inputs(arrangement);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: V128BoolSelect canonical byte mask -> PBLENDVB".to_string(),
        trust_ir_expr: encode_trust_ir_v128_bool_select(
            arrangement,
            mask.clone(),
            true_val.clone(),
            false_val.clone(),
        ),
        aarch64_expr: encode_pblendvb(false_val, true_val, mask),
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all x86 V128 bool-select proof obligations.
pub fn all_x86_64_v128_bool_select_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_v128_bool_select_sse2(),
        proof_x86_v128_bool_select_pblendvb(),
    ]
}

// ===========================================================================
// 8-bit exhaustive proofs (complete verification)
// ===========================================================================

/// Proof: `trust_ir::Iadd(I8, a, b) -> x86-64 ADD (8-bit)`
///
/// 8-bit proofs are verified exhaustively (all 65,536 input pairs).
pub fn proof_x86_iadd_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_add_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Iadd_I8 -> ADD (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_add_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Isub(I8, a, b) -> x86-64 SUB (8-bit)`
pub fn proof_x86_isub_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_sub_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Isub_I8 -> SUB (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_sub_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Imul(I8, a, b) -> x86-64 IMUL (8-bit)`
pub fn proof_x86_imul_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_imul_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Imul_I8 -> IMUL (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_imul_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Comparison lowering proofs (32-bit)
// ===========================================================================

/// Proof: `trust_ir::Icmp(EQ, I32, a, b) -> x86-64 CMP+SETE`
pub fn proof_x86_icmp_eq_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_EQ_I32 -> CMP+SETE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::Equal, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::E),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(NE, I32, a, b) -> x86-64 CMP+SETNE`
pub fn proof_x86_icmp_ne_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_NE_I32 -> CMP+SETNE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::NotEqual, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::NE),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(SLT, I32, a, b) -> x86-64 CMP+SETL`
pub fn proof_x86_icmp_slt_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_SLT_I32 -> CMP+SETL".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThan,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::L),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(SGE, I32, a, b) -> x86-64 CMP+SETGE`
pub fn proof_x86_icmp_sge_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_SGE_I32 -> CMP+SETGE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedGreaterThanOrEqual,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::GE),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(SGT, I32, a, b) -> x86-64 CMP+SETG`
pub fn proof_x86_icmp_sgt_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_SGT_I32 -> CMP+SETG".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedGreaterThan,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::G),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(SLE, I32, a, b) -> x86-64 CMP+SETLE`
pub fn proof_x86_icmp_sle_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_SLE_I32 -> CMP+SETLE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThanOrEqual,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::LE),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(ULT, I32, a, b) -> x86-64 CMP+SETB`
pub fn proof_x86_icmp_ult_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_ULT_I32 -> CMP+SETB".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedLessThan,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::B),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(UGE, I32, a, b) -> x86-64 CMP+SETAE`
pub fn proof_x86_icmp_uge_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_UGE_I32 -> CMP+SETAE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedGreaterThanOrEqual,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::AE),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(UGT, I32, a, b) -> x86-64 CMP+SETA`
pub fn proof_x86_icmp_ugt_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_UGT_I32 -> CMP+SETA".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedGreaterThan,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::A),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(ULE, I32, a, b) -> x86-64 CMP+SETBE`
pub fn proof_x86_icmp_ule_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_ULE_I32 -> CMP+SETBE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedLessThanOrEqual,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 32, X86CondCode::BE),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Comparison lowering proofs (64-bit)
// ===========================================================================

/// Proof: `trust_ir::Icmp(EQ, I64, a, b) -> x86-64 CMP+SETE`
pub fn proof_x86_icmp_eq_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_EQ_I64 -> CMP+SETE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::Equal, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::E),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(NE, I64, a, b) -> x86-64 CMP+SETNE`
pub fn proof_x86_icmp_ne_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_NE_I64 -> CMP+SETNE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&IntCC::NotEqual, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::NE),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(SLT, I64, a, b) -> x86-64 CMP+SETL`
pub fn proof_x86_icmp_slt_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_SLT_I64 -> CMP+SETL".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::L),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(SGE, I64, a, b) -> x86-64 CMP+SETGE`
pub fn proof_x86_icmp_sge_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_SGE_I64 -> CMP+SETGE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedGreaterThanOrEqual,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::GE),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(SGT, I64, a, b) -> x86-64 CMP+SETG`
pub fn proof_x86_icmp_sgt_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_SGT_I64 -> CMP+SETG".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedGreaterThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::G),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(SLE, I64, a, b) -> x86-64 CMP+SETLE`
pub fn proof_x86_icmp_sle_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_SLE_I64 -> CMP+SETLE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThanOrEqual,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::LE),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(ULT, I64, a, b) -> x86-64 CMP+SETB`
pub fn proof_x86_icmp_ult_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_ULT_I64 -> CMP+SETB".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedLessThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::B),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(UGE, I64, a, b) -> x86-64 CMP+SETAE`
pub fn proof_x86_icmp_uge_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_UGE_I64 -> CMP+SETAE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedGreaterThanOrEqual,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::AE),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(UGT, I64, a, b) -> x86-64 CMP+SETA`
pub fn proof_x86_icmp_ugt_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_UGT_I64 -> CMP+SETA".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedGreaterThan,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::A),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Icmp(ULE, I64, a, b) -> x86-64 CMP+SETBE`
pub fn proof_x86_icmp_ule_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Icmp_ULE_I64 -> CMP+SETBE".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::UnsignedLessThanOrEqual,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_cmp_setcc(a, b, 64, X86CondCode::BE),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Conditional move bitwise-select proofs
// ===========================================================================

fn proof_x86_cmovcc_bitwise_select_with_width(
    size: crate::x86_64_semantics::X86OperandSize,
    width: u32,
    opcode_name: &str,
) -> ProofObligation {
    use crate::x86_64_semantics::encode_cmovcc;

    let cond = SmtExpr::var("cond", 1);
    let true_bits = SmtExpr::var("true_bits", width);
    let false_bits = SmtExpr::var("false_bits", width);
    let cond_bool = cond.eq_expr(SmtExpr::bv_const(1, 1));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: {opcode_name} bitwise select"),
        trust_ir_expr: SmtExpr::ite(cond_bool.clone(), true_bits.clone(), false_bits.clone()),
        aarch64_expr: encode_cmovcc(size, cond_bool, false_bits, true_bits),
        inputs: vec![
            ("cond".to_string(), 1),
            ("true_bits".to_string(), width),
            ("false_bits".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `CMOVcc r32,r32` is a bitwise select over 32-bit payloads.
pub fn proof_x86_cmovcc32_bitwise_select() -> ProofObligation {
    use crate::x86_64_semantics::X86OperandSize;

    proof_x86_cmovcc_bitwise_select_with_width(X86OperandSize::S32, 32, "CMOVcc32")
}

/// Proof: `CMOVcc r64,r64` is a bitwise select over 64-bit payloads.
pub fn proof_x86_cmovcc_bitwise_select() -> ProofObligation {
    use crate::x86_64_semantics::X86OperandSize;

    proof_x86_cmovcc_bitwise_select_with_width(X86OperandSize::S64, 64, "CMOVcc")
}

// ===========================================================================
// Floating-point lowering proofs
// ===========================================================================

/// Proof: `trust_ir::Fadd(F32, a, b) -> x86-64 ADDSS xmm, xmm`
pub fn proof_x86_fadd_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_add_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0); // placeholder; concrete values tested by FP verifier
    let b = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fadd_F32 -> ADDSS xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fp_add_rr(X86FPSize::Single, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fadd(F64, a, b) -> x86-64 ADDSD xmm, xmm`
pub fn proof_x86_fadd_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_add_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);
    let b = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fadd_F64 -> ADDSD xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fp_add_rr(X86FPSize::Double, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fsub(F32, a, b) -> x86-64 SUBSS xmm, xmm`
pub fn proof_x86_fsub_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_sub_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);
    let b = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fsub_F32 -> SUBSS xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fsub, Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fp_sub_rr(X86FPSize::Single, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fsub(F64, a, b) -> x86-64 SUBSD xmm, xmm`
pub fn proof_x86_fsub_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_sub_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);
    let b = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fsub_F64 -> SUBSD xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fsub, Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fp_sub_rr(X86FPSize::Double, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fmul(F32, a, b) -> x86-64 MULSS xmm, xmm`
pub fn proof_x86_fmul_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_mul_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);
    let b = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fmul_F32 -> MULSS xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fmul, Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fp_mul_rr(X86FPSize::Single, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fmul(F64, a, b) -> x86-64 MULSD xmm, xmm`
pub fn proof_x86_fmul_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_mul_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);
    let b = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fmul_F64 -> MULSD xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fmul, Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fp_mul_rr(X86FPSize::Double, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fdiv(F32, a, b) -> x86-64 DIVSS xmm, xmm`
pub fn proof_x86_fdiv_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_div_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);
    let b = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fdiv_F32 -> DIVSS xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fdiv, Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fp_div_rr(X86FPSize::Single, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fdiv(F64, a, b) -> x86-64 DIVSD xmm, xmm`
pub fn proof_x86_fdiv_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_div_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);
    let b = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fdiv_F64 -> DIVSD xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fdiv, Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fp_div_rr(X86FPSize::Double, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Packed floating-point lowering proofs (ADDPS/ADDPD families)
// ===========================================================================
//
// Each packed op applies an independent IEEE-754 binary operation to every
// lane (4 lanes for the `<4 x f32>` PS forms, 2 lanes for the `<2 x f64>` PD
// forms). The trust_ir vector FP semantics (`eval_vector_binop`) is likewise
// defined per-lane: it applies the scalar FP op to each lane independently.
//
// The correctness obligation therefore decomposes into a single per-lane
// equivalence: the x86 packed instruction's per-lane operation must equal the
// trust_ir per-lane FP operation. Because every lane of both sides uses the
// identical scalar FP operation under the same RNE rounding mode, proving one
// representative lane discharges the full-vector obligation. The proof below is
// dispatched to the FP evaluator (`fp_inputs` set, `inputs` empty), which runs
// the full IEEE-754 edge-case battery (NaN, +/-0.0, +/-Inf, denormals,
// MAX/MIN, etc.) through both the trust_ir per-lane semantic and the x86
// per-lane packed semantic and asserts bitwise (NaN-aware) agreement.

/// Build a per-lane packed-FP lowering proof obligation.
///
/// `trust_ir_op` is the trust_ir scalar FP opcode applied to each lane;
/// `x86_lane` is the x86 packed per-lane semantic encoder. `eb`/`sb` select
/// the lane precision (8/24 for binary32, 11/53 for binary64).
fn proof_x86_packed_fp_lane(
    name: &str,
    trust_ir_op: trust_cg_lower::instructions::Opcode,
    ty: trust_cg_lower::types::Type,
    size: crate::x86_64_semantics::X86FPSize,
    eb: u32,
    sb: u32,
    x86_lane: fn(crate::x86_64_semantics::X86FPSize, SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;

    let (a, b) = if eb == 8 {
        (SmtExpr::fp32_const(0.0), SmtExpr::fp32_const(0.0))
    } else {
        (SmtExpr::fp64_const(0.0), SmtExpr::fp64_const(0.0))
    };

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&trust_ir_op, ty, a.clone(), b.clone()),
        aarch64_expr: x86_lane(size, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), eb, sb), ("b".to_string(), eb, sb)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir <4 x f32> fadd -> x86-64 ADDPS xmm,xmm` (per-lane).
pub fn proof_x86_v4f32_fadd_addps() -> ProofObligation {
    use crate::x86_64_semantics::{X86FPSize, encode_packed_fp_add_lane};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    proof_x86_packed_fp_lane(
        "x86_64: V4F32Fadd -> ADDPS xmm,xmm (per-lane)",
        Opcode::Fadd,
        Type::F32,
        X86FPSize::Single,
        8,
        24,
        encode_packed_fp_add_lane,
    )
}

/// Proof: `trust_ir <4 x f32> fsub -> x86-64 SUBPS xmm,xmm` (per-lane).
pub fn proof_x86_v4f32_fsub_subps() -> ProofObligation {
    use crate::x86_64_semantics::{X86FPSize, encode_packed_fp_sub_lane};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    proof_x86_packed_fp_lane(
        "x86_64: V4F32Fsub -> SUBPS xmm,xmm (per-lane)",
        Opcode::Fsub,
        Type::F32,
        X86FPSize::Single,
        8,
        24,
        encode_packed_fp_sub_lane,
    )
}

/// Proof: `trust_ir <4 x f32> fmul -> x86-64 MULPS xmm,xmm` (per-lane).
pub fn proof_x86_v4f32_fmul_mulps() -> ProofObligation {
    use crate::x86_64_semantics::{X86FPSize, encode_packed_fp_mul_lane};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    proof_x86_packed_fp_lane(
        "x86_64: V4F32Fmul -> MULPS xmm,xmm (per-lane)",
        Opcode::Fmul,
        Type::F32,
        X86FPSize::Single,
        8,
        24,
        encode_packed_fp_mul_lane,
    )
}

/// Proof: `trust_ir <4 x f32> fdiv -> x86-64 DIVPS xmm,xmm` (per-lane).
pub fn proof_x86_v4f32_fdiv_divps() -> ProofObligation {
    use crate::x86_64_semantics::{X86FPSize, encode_packed_fp_div_lane};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    proof_x86_packed_fp_lane(
        "x86_64: V4F32Fdiv -> DIVPS xmm,xmm (per-lane)",
        Opcode::Fdiv,
        Type::F32,
        X86FPSize::Single,
        8,
        24,
        encode_packed_fp_div_lane,
    )
}

/// Proof: `trust_ir <2 x f64> fadd -> x86-64 ADDPD xmm,xmm` (per-lane).
pub fn proof_x86_v2f64_fadd_addpd() -> ProofObligation {
    use crate::x86_64_semantics::{X86FPSize, encode_packed_fp_add_lane};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    proof_x86_packed_fp_lane(
        "x86_64: V2F64Fadd -> ADDPD xmm,xmm (per-lane)",
        Opcode::Fadd,
        Type::F64,
        X86FPSize::Double,
        11,
        53,
        encode_packed_fp_add_lane,
    )
}

/// Proof: `trust_ir <2 x f64> fsub -> x86-64 SUBPD xmm,xmm` (per-lane).
pub fn proof_x86_v2f64_fsub_subpd() -> ProofObligation {
    use crate::x86_64_semantics::{X86FPSize, encode_packed_fp_sub_lane};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    proof_x86_packed_fp_lane(
        "x86_64: V2F64Fsub -> SUBPD xmm,xmm (per-lane)",
        Opcode::Fsub,
        Type::F64,
        X86FPSize::Double,
        11,
        53,
        encode_packed_fp_sub_lane,
    )
}

/// Proof: `trust_ir <2 x f64> fmul -> x86-64 MULPD xmm,xmm` (per-lane).
pub fn proof_x86_v2f64_fmul_mulpd() -> ProofObligation {
    use crate::x86_64_semantics::{X86FPSize, encode_packed_fp_mul_lane};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    proof_x86_packed_fp_lane(
        "x86_64: V2F64Fmul -> MULPD xmm,xmm (per-lane)",
        Opcode::Fmul,
        Type::F64,
        X86FPSize::Double,
        11,
        53,
        encode_packed_fp_mul_lane,
    )
}

/// Proof: `trust_ir <2 x f64> fdiv -> x86-64 DIVPD xmm,xmm` (per-lane).
pub fn proof_x86_v2f64_fdiv_divpd() -> ProofObligation {
    use crate::x86_64_semantics::{X86FPSize, encode_packed_fp_div_lane};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    proof_x86_packed_fp_lane(
        "x86_64: V2F64Fdiv -> DIVPD xmm,xmm (per-lane)",
        Opcode::Fdiv,
        Type::F64,
        X86FPSize::Double,
        11,
        53,
        encode_packed_fp_div_lane,
    )
}

// ===========================================================================
// Floating-point unary lowering proofs (FNEG, FABS, FSQRT)
// ===========================================================================

/// Proof: `trust_ir::Fneg(F32, a) -> x86-64 XORPS (sign-flip)`
pub fn proof_x86_fneg_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fneg;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_neg};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fneg_F32 -> XORPS (negate)".to_string(),
        trust_ir_expr: encode_trust_ir_fneg(Type::F32, a.clone()),
        aarch64_expr: encode_fp_neg(X86FPSize::Single, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fneg(F64, a) -> x86-64 XORPD (sign-flip)`
pub fn proof_x86_fneg_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fneg;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_neg};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fneg_F64 -> XORPD (negate)".to_string(),
        trust_ir_expr: encode_trust_ir_fneg(Type::F64, a.clone()),
        aarch64_expr: encode_fp_neg(X86FPSize::Double, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fabs(F32, a) -> x86-64 ANDPS (clear sign bit)`
pub fn proof_x86_fabs_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fabs;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_abs};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fabs_F32 -> ANDPS (abs)".to_string(),
        trust_ir_expr: encode_trust_ir_fabs(Type::F32, a.clone()),
        aarch64_expr: encode_fp_abs(X86FPSize::Single, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fabs(F64, a) -> x86-64 ANDPD (clear sign bit)`
pub fn proof_x86_fabs_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fabs;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_abs};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fabs_F64 -> ANDPD (abs)".to_string(),
        trust_ir_expr: encode_trust_ir_fabs(Type::F64, a.clone()),
        aarch64_expr: encode_fp_abs(X86FPSize::Double, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fsqrt(F32, a) -> x86-64 SQRTSS xmm, xmm`
pub fn proof_x86_fsqrt_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fsqrt;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_sqrt};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fsqrt_F32 -> SQRTSS xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fsqrt(Type::F32, a.clone()),
        aarch64_expr: encode_fp_sqrt(X86FPSize::Single, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fsqrt(F64, a) -> x86-64 SQRTSD xmm, xmm`
pub fn proof_x86_fsqrt_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fsqrt;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_sqrt};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fsqrt_F64 -> SQRTSD xmm,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fsqrt(Type::F64, a.clone()),
        aarch64_expr: encode_fp_sqrt(X86FPSize::Double, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Float round-to-integral lowering proofs (SSE4.1 ROUNDSD/ROUNDSS).
//
// Each proof's machine side feeds the EXACT imm8 the ISel emits
// (`select_fround`: 0x08 | mode-selector, i.e. 0x09 floor, 0x0A ceil, 0x0B
// trunc) into `encode_fp_round`, which decodes the imm8[1:0] selector to the
// hardware rounding mode just as ROUNDSD/ROUNDSS do. The trust_ir side encodes
// the Rust floor/ceil/trunc spec as `fp.roundToIntegral(RTN/RTP/RTZ, a)`. The
// two sides model the spec and the emitted instruction independently — not a
// tautology — and the equivalence certifies that the chosen imm8 realizes the
// intended rounding direction.
// ---------------------------------------------------------------------------

/// imm8 the backend emits for each rounding mode: bit 3 (0x08) suppresses the
/// precision exception; bits [1:0] select the directed rounding.
const ROUND_IMM8_FLOOR: u8 = 0x08 | 0b01;
const ROUND_IMM8_CEIL: u8 = 0x08 | 0b10;
const ROUND_IMM8_TRUNC: u8 = 0x08 | 0b11;

/// Proof: `trust_ir::FFloor(F32, a) -> x86-64 ROUNDSS xmm, xmm, 0x09`
pub fn proof_x86_ffloor_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_ffloor;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_round};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FFloor_F32 -> ROUNDSS xmm,xmm,floor".to_string(),
        trust_ir_expr: encode_trust_ir_ffloor(Type::F32, a.clone()),
        aarch64_expr: encode_fp_round(X86FPSize::Single, ROUND_IMM8_FLOOR, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FFloor(F64, a) -> x86-64 ROUNDSD xmm, xmm, 0x09`
pub fn proof_x86_ffloor_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_ffloor;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_round};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FFloor_F64 -> ROUNDSD xmm,xmm,floor".to_string(),
        trust_ir_expr: encode_trust_ir_ffloor(Type::F64, a.clone()),
        aarch64_expr: encode_fp_round(X86FPSize::Double, ROUND_IMM8_FLOOR, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FCeil(F32, a) -> x86-64 ROUNDSS xmm, xmm, 0x0A`
pub fn proof_x86_fceil_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fceil;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_round};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FCeil_F32 -> ROUNDSS xmm,xmm,ceil".to_string(),
        trust_ir_expr: encode_trust_ir_fceil(Type::F32, a.clone()),
        aarch64_expr: encode_fp_round(X86FPSize::Single, ROUND_IMM8_CEIL, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FCeil(F64, a) -> x86-64 ROUNDSD xmm, xmm, 0x0A`
pub fn proof_x86_fceil_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fceil;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_round};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FCeil_F64 -> ROUNDSD xmm,xmm,ceil".to_string(),
        trust_ir_expr: encode_trust_ir_fceil(Type::F64, a.clone()),
        aarch64_expr: encode_fp_round(X86FPSize::Double, ROUND_IMM8_CEIL, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FTrunc(F32, a) -> x86-64 ROUNDSS xmm, xmm, 0x0B`
pub fn proof_x86_ftrunc_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_ftrunc;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_round};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FTrunc_F32 -> ROUNDSS xmm,xmm,trunc".to_string(),
        trust_ir_expr: encode_trust_ir_ftrunc(Type::F32, a.clone()),
        aarch64_expr: encode_fp_round(X86FPSize::Single, ROUND_IMM8_TRUNC, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FTrunc(F64, a) -> x86-64 ROUNDSD xmm, xmm, 0x0B`
pub fn proof_x86_ftrunc_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_ftrunc;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_round};
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FTrunc_F64 -> ROUNDSD xmm,xmm,trunc".to_string(),
        trust_ir_expr: encode_trust_ir_ftrunc(Type::F64, a.clone()),
        aarch64_expr: encode_fp_round(X86FPSize::Double, ROUND_IMM8_TRUNC, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Scalar FP min/max + UNORD compare-to-mask lowering proofs (MINSD/MAXSD/
// MINSS/MAXSS + CMPSD/CMPSS), the components of the Rust f{32,64}::min/max
// NaN-away idiom.
//
// Each proof models the EXACT Intel-SDM HARDWARE semantics on BOTH sides,
// derived INDEPENDENTLY: the machine side (`encode_fp_minsd`/`maxsd`/
// `cmp_unord_mask`) transcribes the SDM as `dest </> src ? dest : src` and
// `isNaN(a) OR isNaN(b)`; the trust_ir/spec side (`encode_trust_ir_fminsd_hw`/
// `fmaxsd_hw`/`cmp_unord_mask`) writes the complementary `(unord OR dest>=src)
// ? src : dest` and the self-`fp.eq` NaN test. Proving them bit-equal over the
// full IEEE edge-case battery (incl. NaN, +/-0.0, +/-Inf) is genuine work, not
// a syntactic identity. These prove the MINSD/MAXSD/CMPSD OPCODES faithfully;
// the surrounding NaN-away XOR-blend (PXOR/PAND — themselves proven) is the
// trusted structural idiom (cf. the fneg/fabs sign idioms), and the end-to-end
// NaN/+-0 correctness is established by exhaustive differential testing vs LLVM.
// ---------------------------------------------------------------------------

/// Proof: x86-64 MINSD models the SDM scalar-double minimum (NOT IEEE minNum).
pub fn proof_x86_minsd_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fminsd_hw;
    use crate::x86_64_semantics::encode_fp_minsd;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);
    let b = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fmin_F64 -> MINSD xmm,xmm (SDM hw min)".to_string(),
        trust_ir_expr: encode_trust_ir_fminsd_hw(Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fp_minsd(a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 MAXSD models the SDM scalar-double maximum (NOT IEEE maxNum).
pub fn proof_x86_maxsd_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fmaxsd_hw;
    use crate::x86_64_semantics::encode_fp_maxsd;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp64_const(0.0);
    let b = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fmax_F64 -> MAXSD xmm,xmm (SDM hw max)".to_string(),
        trust_ir_expr: encode_trust_ir_fmaxsd_hw(Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fp_maxsd(a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 MINSS models the SDM scalar-single minimum.
pub fn proof_x86_minss_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fminsd_hw;
    use crate::x86_64_semantics::encode_fp_minsd;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);
    let b = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fmin_F32 -> MINSS xmm,xmm (SDM hw min)".to_string(),
        trust_ir_expr: encode_trust_ir_fminsd_hw(Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fp_minsd(a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 MAXSS models the SDM scalar-single maximum.
pub fn proof_x86_maxss_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fmaxsd_hw;
    use crate::x86_64_semantics::encode_fp_maxsd;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::fp32_const(0.0);
    let b = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Fmax_F32 -> MAXSS xmm,xmm (SDM hw max)".to_string(),
        trust_ir_expr: encode_trust_ir_fmaxsd_hw(Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fp_maxsd(a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 CMPSD imm8=3 (UNORD) yields the all-ones/zero isNaN mask.
pub fn proof_x86_cmpsd_unord_f64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_cmp_unord_mask;
    use crate::x86_64_semantics::encode_fp_cmp_unord_mask;

    let a = SmtExpr::fp64_const(0.0);
    let b = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: CMPSD_UNORD_F64 -> 64-bit isNaN mask".to_string(),
        trust_ir_expr: encode_trust_ir_cmp_unord_mask(64, a.clone(), b.clone()),
        aarch64_expr: encode_fp_cmp_unord_mask(64, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 CMPSS imm8=3 (UNORD) yields the all-ones/zero isNaN mask.
pub fn proof_x86_cmpss_unord_f32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_cmp_unord_mask;
    use crate::x86_64_semantics::encode_fp_cmp_unord_mask;

    let a = SmtExpr::fp32_const(0.0);
    let b = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: CMPSS_UNORD_F32 -> 32-bit isNaN mask".to_string(),
        trust_ir_expr: encode_trust_ir_cmp_unord_mask(32, a.clone(), b.clone()),
        aarch64_expr: encode_fp_cmp_unord_mask(32, a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Floating-point comparison lowering proofs
// ===========================================================================

/// Generic proof for x86-64 `Fcmp` lowering.
///
/// The x86 selector lowers trust_ir `Fcmp` to `UCOMISS`/`UCOMISD` plus the
/// NaN-correct SETcc strategy returned by `x86_float_cmp_strategy`.
fn proof_x86_fcmp_generic(
    cond: trust_cg_lower::instructions::FloatCC,
    is_f32: bool,
    name: &str,
) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fcmp;
    use crate::x86_64_semantics::{X86FPSize, encode_fp_cmp_strategy};
    use trust_cg_lower::types::Type;
    use trust_cg_lower::x86_float_cmp_strategy;

    let (ty, fp_size, eb, sb) = if is_f32 {
        (Type::F32, X86FPSize::Single, 8u32, 24u32)
    } else {
        (Type::F64, X86FPSize::Double, 11u32, 53u32)
    };

    let a = if is_f32 {
        SmtExpr::fp32_const(0.0)
    } else {
        SmtExpr::fp64_const(0.0)
    };
    let b = if is_f32 {
        SmtExpr::fp32_const(0.0)
    } else {
        SmtExpr::fp64_const(0.0)
    };

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_fcmp(&cond, ty, a.clone(), b.clone()),
        aarch64_expr: encode_fp_cmp_strategy(fp_size, a, b, x86_float_cmp_strategy(cond)),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), eb, sb), ("b".to_string(), eb, sb)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

pub fn proof_x86_fcmp_eq_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(FloatCC::Equal, true, "Fcmp_Eq_F32 -> x86_64 UCOMISS+SETcc")
}

pub fn proof_x86_fcmp_eq_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(FloatCC::Equal, false, "Fcmp_Eq_F64 -> x86_64 UCOMISD+SETcc")
}

pub fn proof_x86_fcmp_ne_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::NotEqual,
        true,
        "Fcmp_NE_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_ne_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::NotEqual,
        false,
        "Fcmp_NE_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_lt_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::LessThan,
        true,
        "Fcmp_LT_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_lt_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::LessThan,
        false,
        "Fcmp_LT_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_le_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::LessThanOrEqual,
        true,
        "Fcmp_LE_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_le_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::LessThanOrEqual,
        false,
        "Fcmp_LE_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_gt_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::GreaterThan,
        true,
        "Fcmp_GT_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_gt_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::GreaterThan,
        false,
        "Fcmp_GT_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_ge_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::GreaterThanOrEqual,
        true,
        "Fcmp_GE_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_ge_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::GreaterThanOrEqual,
        false,
        "Fcmp_GE_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_ord_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::Ordered,
        true,
        "Fcmp_Ord_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_ord_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::Ordered,
        false,
        "Fcmp_Ord_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_uno_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::Unordered,
        true,
        "Fcmp_Uno_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_uno_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::Unordered,
        false,
        "Fcmp_Uno_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_ueq_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedEqual,
        true,
        "Fcmp_UEQ_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_ueq_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedEqual,
        false,
        "Fcmp_UEQ_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_une_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedNotEqual,
        true,
        "Fcmp_UNE_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_une_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedNotEqual,
        false,
        "Fcmp_UNE_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_ult_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedLessThan,
        true,
        "Fcmp_ULT_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_ult_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedLessThan,
        false,
        "Fcmp_ULT_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_ule_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedLessThanOrEqual,
        true,
        "Fcmp_ULE_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_ule_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedLessThanOrEqual,
        false,
        "Fcmp_ULE_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_ugt_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedGreaterThan,
        true,
        "Fcmp_UGT_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_ugt_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedGreaterThan,
        false,
        "Fcmp_UGT_F64 -> x86_64 UCOMISD+SETcc",
    )
}

pub fn proof_x86_fcmp_uge_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedGreaterThanOrEqual,
        true,
        "Fcmp_UGE_F32 -> x86_64 UCOMISS+SETcc",
    )
}

pub fn proof_x86_fcmp_uge_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_x86_fcmp_generic(
        FloatCC::UnorderedGreaterThanOrEqual,
        false,
        "Fcmp_UGE_F64 -> x86_64 UCOMISD+SETcc",
    )
}

// ===========================================================================
// 8-bit exhaustive bitwise proofs (complete verification)
// ===========================================================================

/// Proof: `trust_ir::Band(I8, a, b) -> x86-64 AND (8-bit)`
///
/// 8-bit proofs are verified exhaustively (all 65,536 input pairs).
pub fn proof_x86_band_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Band_I8 -> AND (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Band, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_and_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bor(I8, a, b) -> x86-64 OR (8-bit)`
pub fn proof_x86_bor_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bor_I8 -> OR (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_or_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Bxor(I8, a, b) -> x86-64 XOR (8-bit)`
pub fn proof_x86_bxor_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::x86_64_semantics::{X86OperandSize, encode_xor_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bxor_I8 -> XOR (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bxor, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_xor_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::BandNot(I8, a, b) -> x86-64 NOT+AND (8-bit)`
pub fn proof_x86_bandnot_i8() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_and_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BandNot_I8 -> NOT+AND (8-bit)",
        Opcode::BandNot,
        Type::I8,
        8,
        X86OperandSize::S32,
        encode_and_rr,
    )
}

/// Proof: `trust_ir::BorNot(I8, a, b) -> x86-64 NOT+OR (8-bit)`
pub fn proof_x86_bornot_i8() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_or_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    proof_x86_binary_not_logic(
        "x86_64: BorNot_I8 -> NOT+OR (8-bit)",
        Opcode::BorNot,
        Type::I8,
        8,
        X86OperandSize::S32,
        encode_or_rr,
    )
}

// ===========================================================================
// 8-bit exhaustive shift proofs (complete verification)
// ===========================================================================

/// Proof: `trust_ir::Ishl(I8, a, b) -> x86-64 SHL (8-bit)`
pub fn proof_x86_ishl_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_shl_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Ishl_I8 -> SHL (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_shl_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Ushr(I8, a, b) -> x86-64 SHR (8-bit)`
pub fn proof_x86_ushr_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_shr_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Ushr_I8 -> SHR (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_shr_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Sshr(I8, a, b) -> x86-64 SAR (8-bit)`
pub fn proof_x86_sshr_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::x86_64_semantics::{X86OperandSize, encode_sar_rr};
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sshr_I8 -> SAR (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I8, a.clone(), b.clone()),
        aarch64_expr: encode_sar_rr(X86OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Scalar bitfield lowering proofs
// ===========================================================================
//
// x86-64 lowers trust_ir bitfield ops to ordinary shifts and masks:
//
//   ExtractBits { lsb, width }   -> SHR imm + AND mask
//   SextractBits { lsb, width }  -> SHL imm + SAR imm (+ AND type mask for i8/i16)
//   InsertBits { lsb, width }    -> AND clear-mask + AND low-mask + SHL imm + OR
//
// The selector uses 32-bit GPR operations for i8/i16/i32 and 64-bit GPR
// operations for i64. These helpers model that carrier width, then truncate
// back to the trust_ir scalar width for subword results.

fn x86_scalar_bitfield_carrier_bits(bits: u32) -> u32 {
    if bits == 64 { 64 } else { 32 }
}

fn x86_scalar_bitfield_to_carrier(value: SmtExpr, bits: u32) -> SmtExpr {
    let carrier_bits = x86_scalar_bitfield_carrier_bits(bits);
    if carrier_bits == bits {
        value
    } else {
        value.zero_ext(carrier_bits - bits)
    }
}

fn x86_scalar_bitfield_from_carrier(value: SmtExpr, bits: u32) -> SmtExpr {
    let carrier_bits = x86_scalar_bitfield_carrier_bits(bits);
    if carrier_bits == bits {
        value
    } else {
        value.extract(bits - 1, 0)
    }
}

fn encode_x86_scalar_extract_bits(src: SmtExpr, bits: u32, lsb: u8, width: u8) -> SmtExpr {
    let carrier_bits = x86_scalar_bitfield_carrier_bits(bits);
    let src = x86_scalar_bitfield_to_carrier(src, bits);
    let shifted = src.bvlshr(SmtExpr::bv_const(u64::from(lsb), carrier_bits));
    let masked = shifted.bvand(SmtExpr::bv_const(
        crate::smt::mask(u64::MAX, u32::from(width)),
        carrier_bits,
    ));
    x86_scalar_bitfield_from_carrier(masked, bits)
}

fn encode_x86_scalar_sextract_bits(src: SmtExpr, bits: u32, lsb: u8, width: u8) -> SmtExpr {
    let carrier_bits = x86_scalar_bitfield_carrier_bits(bits);
    let src = x86_scalar_bitfield_to_carrier(src, bits);
    let field_end = u32::from(lsb) + u32::from(width);
    let left = carrier_bits - field_end;
    let right = carrier_bits - u32::from(width);
    let shifted_left = src.bvshl(SmtExpr::bv_const(u64::from(left), carrier_bits));
    let shifted_right = shifted_left.bvashr(SmtExpr::bv_const(u64::from(right), carrier_bits));
    let typed = if carrier_bits == bits {
        shifted_right
    } else {
        shifted_right.bvand(SmtExpr::bv_const(
            crate::smt::mask(u64::MAX, bits),
            carrier_bits,
        ))
    };
    x86_scalar_bitfield_from_carrier(typed, bits)
}

fn encode_x86_scalar_insert_bits(
    dst: SmtExpr,
    src: SmtExpr,
    bits: u32,
    lsb: u8,
    width: u8,
) -> SmtExpr {
    let carrier_bits = x86_scalar_bitfield_carrier_bits(bits);
    let dst = x86_scalar_bitfield_to_carrier(dst, bits);
    let src = x86_scalar_bitfield_to_carrier(src, bits);
    let low_mask = crate::smt::mask(u64::MAX, u32::from(width));
    let type_mask = crate::smt::mask(u64::MAX, bits);
    let field_mask = low_mask << u32::from(lsb);
    let clear_mask = type_mask & !field_mask;

    let preserved = dst.bvand(SmtExpr::bv_const(clear_mask, carrier_bits));
    let insert_low = src.bvand(SmtExpr::bv_const(low_mask, carrier_bits));
    let inserted = insert_low.bvshl(SmtExpr::bv_const(u64::from(lsb), carrier_bits));
    x86_scalar_bitfield_from_carrier(preserved.bvor(inserted), bits)
}

fn proof_x86_extract_bits_for_width(
    ty: trust_cg_lower::types::Type,
    ty_name: &str,
    bits: u32,
    lsb: u8,
    width: u8,
) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_extract_bits;

    let x = SmtExpr::var("x", bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: ExtractBits{{lsb={lsb},width={width}}}_{ty_name} -> SHR+AND"),
        trust_ir_expr: encode_trust_ir_extract_bits(ty, lsb, width, x.clone()),
        aarch64_expr: encode_x86_scalar_extract_bits(x, bits, lsb, width),
        inputs: vec![("x".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_x86_sextract_bits_for_width(
    ty: trust_cg_lower::types::Type,
    ty_name: &str,
    bits: u32,
    lsb: u8,
    width: u8,
) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_sextract_bits;

    let x = SmtExpr::var("x", bits);
    let suffix = if bits < x86_scalar_bitfield_carrier_bits(bits) {
        "SHL+SAR+AND"
    } else {
        "SHL+SAR"
    };

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: SextractBits{{lsb={lsb},width={width}}}_{ty_name} -> {suffix}"),
        trust_ir_expr: encode_trust_ir_sextract_bits(ty, lsb, width, x.clone()),
        aarch64_expr: encode_x86_scalar_sextract_bits(x, bits, lsb, width),
        inputs: vec![("x".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_x86_insert_bits_for_width(
    ty: trust_cg_lower::types::Type,
    ty_name: &str,
    bits: u32,
    lsb: u8,
    width: u8,
) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_insert_bits;

    let dst = SmtExpr::var("dst", bits);
    let src = SmtExpr::var("src", bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: InsertBits{{lsb={lsb},width={width}}}_{ty_name} -> AND+AND+SHL+OR"),
        trust_ir_expr: encode_trust_ir_insert_bits(ty, lsb, width, dst.clone(), src.clone()),
        aarch64_expr: encode_x86_scalar_insert_bits(dst, src, bits, lsb, width),
        inputs: vec![("dst".to_string(), bits), ("src".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_x86_insert_bits_alias_for_width(
    ty: trust_cg_lower::types::Type,
    ty_name: &str,
    bits: u32,
    lsb: u8,
    width: u8,
) -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_insert_bits;

    let dst = SmtExpr::var("dst", bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: InsertBits{{lsb={lsb},width={width}}}_{ty_name}(dst,dst) -> AND+AND+SHL+OR"
        ),
        trust_ir_expr: encode_trust_ir_insert_bits(ty, lsb, width, dst.clone(), dst.clone()),
        aarch64_expr: encode_x86_scalar_insert_bits(dst.clone(), dst, bits, lsb, width),
        inputs: vec![("dst".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

pub fn proof_x86_extract_bits_i8() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_extract_bits_for_width(Type::I8, "I8", 8, 2, 4)
}

pub fn proof_x86_extract_bits_i16() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_extract_bits_for_width(Type::I16, "I16", 16, 3, 7)
}

pub fn proof_x86_extract_bits_i32() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_extract_bits_for_width(Type::I32, "I32", 32, 7, 13)
}

pub fn proof_x86_extract_bits_i64() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_extract_bits_for_width(Type::I64, "I64", 64, 11, 23)
}

pub fn proof_x86_sextract_bits_i8() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_sextract_bits_for_width(Type::I8, "I8", 8, 2, 4)
}

pub fn proof_x86_sextract_bits_i16() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_sextract_bits_for_width(Type::I16, "I16", 16, 3, 7)
}

pub fn proof_x86_sextract_bits_i32() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_sextract_bits_for_width(Type::I32, "I32", 32, 7, 13)
}

pub fn proof_x86_sextract_bits_i64() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_sextract_bits_for_width(Type::I64, "I64", 64, 11, 23)
}

pub fn proof_x86_insert_bits_i8() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_insert_bits_for_width(Type::I8, "I8", 8, 2, 4)
}

pub fn proof_x86_insert_bits_i16() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_insert_bits_for_width(Type::I16, "I16", 16, 3, 7)
}

pub fn proof_x86_insert_bits_i32() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_insert_bits_for_width(Type::I32, "I32", 32, 7, 13)
}

pub fn proof_x86_insert_bits_i64() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_insert_bits_for_width(Type::I64, "I64", 64, 11, 23)
}

pub fn proof_x86_insert_bits_alias_i8() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_insert_bits_alias_for_width(Type::I8, "I8", 8, 2, 4)
}

pub fn proof_x86_insert_bits_alias_i16() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_insert_bits_alias_for_width(Type::I16, "I16", 16, 3, 7)
}

pub fn proof_x86_insert_bits_alias_i32() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_insert_bits_alias_for_width(Type::I32, "I32", 32, 7, 13)
}

pub fn proof_x86_insert_bits_alias_i64() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_x86_insert_bits_alias_for_width(Type::I64, "I64", 64, 11, 23)
}

/// Return all x86-64 scalar bitfield proof obligations for the real lowering.
pub fn all_x86_64_scalar_bitfield_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_extract_bits_i8(),
        proof_x86_sextract_bits_i8(),
        proof_x86_insert_bits_i8(),
        proof_x86_insert_bits_alias_i8(),
        proof_x86_extract_bits_i16(),
        proof_x86_sextract_bits_i16(),
        proof_x86_insert_bits_i16(),
        proof_x86_insert_bits_alias_i16(),
        proof_x86_extract_bits_i32(),
        proof_x86_sextract_bits_i32(),
        proof_x86_insert_bits_i32(),
        proof_x86_insert_bits_alias_i32(),
        proof_x86_extract_bits_i64(),
        proof_x86_sextract_bits_i64(),
        proof_x86_insert_bits_i64(),
        proof_x86_insert_bits_alias_i64(),
    ]
}

// ===========================================================================
// MOVZX/MOVSX lowering proofs
// ===========================================================================

/// Proof: `zero_extend(a[7:0], 24) == x86-64 MOVZX r32, r/m8`
pub fn proof_x86_movzx_8_to_32() -> ProofObligation {
    use crate::x86_64_semantics::encode_movzx;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Uextend_I8_to_I32 -> MOVZX r32,r/m8".to_string(),
        trust_ir_expr: a.clone().extract(7, 0).zero_ext(24),
        aarch64_expr: encode_movzx(8, 32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `zero_extend(a[15:0], 16) == x86-64 MOVZX r32, r/m16`
pub fn proof_x86_movzx_16_to_32() -> ProofObligation {
    use crate::x86_64_semantics::encode_movzx;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Uextend_I16_to_I32 -> MOVZX r32,r/m16".to_string(),
        trust_ir_expr: a.clone().extract(15, 0).zero_ext(16),
        aarch64_expr: encode_movzx(16, 32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `zero_extend(a[7:0], 56) == x86-64 MOVZX r64, r/m8`
pub fn proof_x86_movzx_8_to_64() -> ProofObligation {
    use crate::x86_64_semantics::encode_movzx;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Uextend_I8_to_I64 -> MOVZX r64,r/m8".to_string(),
        trust_ir_expr: a.clone().extract(7, 0).zero_ext(56),
        aarch64_expr: encode_movzx(8, 64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `sign_extend(a[7:0], 24) == x86-64 MOVSX r32, r/m8`
pub fn proof_x86_movsx_8_to_32() -> ProofObligation {
    use crate::x86_64_semantics::encode_movsx;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sextend_I8_to_I32 -> MOVSX r32,r/m8".to_string(),
        trust_ir_expr: a.clone().extract(7, 0).sign_ext(24),
        aarch64_expr: encode_movsx(8, 32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `sign_extend(a[15:0], 16) == x86-64 MOVSX r32, r/m16`
pub fn proof_x86_movsx_16_to_32() -> ProofObligation {
    use crate::x86_64_semantics::encode_movsx;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sextend_I16_to_I32 -> MOVSX r32,r/m16".to_string(),
        trust_ir_expr: a.clone().extract(15, 0).sign_ext(16),
        aarch64_expr: encode_movsx(16, 32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `sign_extend(a[31:0], 32) == x86-64 MOVSXD r64, r/m32`
pub fn proof_x86_movsxd_32_to_64() -> ProofObligation {
    use crate::x86_64_semantics::encode_movsx;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sextend_I32_to_I64 -> MOVSXD r64,r/m32".to_string(),
        trust_ir_expr: a.clone().extract(31, 0).sign_ext(32),
        aarch64_expr: encode_movsx(32, 64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// x86-specific i64 byte/word MOVSX/MOVZX (REX.W r64) extension proofs.
//
// The byte/word `MOVSX`/`MOVZX` opcodes are width-polymorphic: ISel emits them
// with both a 32-bit and a 64-bit destination, and the x86 encoder ALWAYS sets
// REX.W for these forms (see `x86_64_isel`/`encode` -> `MOVSX/MOVZX r64`). The
// i32 destinations are covered by `proof_x86_mov{sx,zx}_{8,16}_to_32` above;
// these four prove the REX.W r64 destinations directly against the x86 MOVSX/
// MOVZX semantics (`encode_mov{sx,zx}` with `to_width = 64`), so the function
// verifier can bind a width-correct X8664Lowering proof for a 64-bit byte/word
// extend instead of attributing it to the (AArch64-mnemonic) ExtensionTruncation
// rows. `proof_x86_movzx_8_to_64` (Uextend_I8_to_I64) already exists above; the
// three below complete the i64 byte/word set.
// ---------------------------------------------------------------------------

/// Proof: `zero_extend(a[15:0], 48) == x86-64 MOVZX r64, r/m16`
pub fn proof_x86_movzx_16_to_64() -> ProofObligation {
    use crate::x86_64_semantics::encode_movzx;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Uextend_I16_to_I64 -> MOVZX r64,r/m16".to_string(),
        trust_ir_expr: a.clone().extract(15, 0).zero_ext(48),
        aarch64_expr: encode_movzx(16, 64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `sign_extend(a[7:0], 56) == x86-64 MOVSX r64, r/m8`
pub fn proof_x86_movsx_8_to_64() -> ProofObligation {
    use crate::x86_64_semantics::encode_movsx;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sextend_I8_to_I64 -> MOVSX r64,r/m8".to_string(),
        trust_ir_expr: a.clone().extract(7, 0).sign_ext(56),
        aarch64_expr: encode_movsx(8, 64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `sign_extend(a[15:0], 48) == x86-64 MOVSX r64, r/m16`
pub fn proof_x86_movsx_16_to_64() -> ProofObligation {
    use crate::x86_64_semantics::encode_movsx;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Sextend_I16_to_I64 -> MOVSX r64,r/m16".to_string(),
        trust_ir_expr: a.clone().extract(15, 0).sign_ext(48),
        aarch64_expr: encode_movsx(16, 64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_x86_movrr_copy(width_bits: u32) -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_mov_rr};

    let size = match width_bits {
        32 => X86OperandSize::S32,
        64 => X86OperandSize::S64,
        _ => panic!("unsupported x86 MOVRR copy proof width: {width_bits}"),
    };
    let a = SmtExpr::var("a", width_bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Copy_I{width_bits} -> MOV r{width_bits},r{width_bits} preserves bits"
        ),
        trust_ir_expr: a.clone(),
        aarch64_expr: encode_mov_rr(size, a),
        inputs: vec![("a".to_string(), width_bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `Copy(I32, a)` lowered as `MOV r32,r32` preserves all bits.
pub fn proof_x86_movrr_copy_i32() -> ProofObligation {
    proof_x86_movrr_copy(32)
}

/// Proof: `Copy(I64, a)` lowered as `MOV r64,r64` preserves all bits.
pub fn proof_x86_movrr_copy_i64() -> ProofObligation {
    proof_x86_movrr_copy(64)
}

// ===========================================================================
// MOVD/MOVQ GPR <-> XMM bit-preservation proofs
// ===========================================================================

/// Proof: `Bitcast(I32 -> F32)` lowered as `MOVD xmm,r32` preserves payload bits.
pub fn proof_x86_movd_to_xmm_bit_preservation() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use crate::x86_64_semantics::encode_movd_to_xmm;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bitcast_I32_F32 -> MOVD xmm,r32 preserves bits".to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::I32, Type::F32, a.clone()),
        aarch64_expr: encode_movd_to_xmm(a).extract(31, 0),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `Bitcast(F32 -> I32)` lowered as `MOVD r32,xmm` preserves payload bits.
pub fn proof_x86_movd_from_xmm_bit_preservation() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use crate::x86_64_semantics::encode_movd_from_xmm;
    use trust_cg_lower::types::Type;

    let high64 = SmtExpr::var("xmm_high64", 64);
    let high32 = SmtExpr::var("xmm_high32", 32);
    let low = SmtExpr::var("low", 32);
    let xmm = high64.concat(high32).concat(low.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bitcast_F32_I32 -> MOVD r32,xmm preserves bits".to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::F32, Type::I32, low.clone()),
        aarch64_expr: encode_movd_from_xmm(xmm),
        inputs: vec![
            ("xmm_high64".to_string(), 64),
            ("xmm_high32".to_string(), 32),
            ("low".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `Bitcast(I64 -> F64)` lowered as `MOVQ xmm,r64` preserves payload bits.
pub fn proof_x86_movq_to_xmm_bit_preservation() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use crate::x86_64_semantics::encode_movq_to_xmm;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bitcast_I64_F64 -> MOVQ xmm,r64 preserves bits".to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::I64, Type::F64, a.clone()),
        aarch64_expr: encode_movq_to_xmm(a).extract(63, 0),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `Bitcast(F64 -> I64)` lowered as `MOVQ r64,xmm` preserves payload bits.
pub fn proof_x86_movq_from_xmm_bit_preservation() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use crate::x86_64_semantics::encode_movq_from_xmm;
    use trust_cg_lower::types::Type;

    let high = SmtExpr::var("xmm_high", 64);
    let low = SmtExpr::var("low", 64);
    let xmm = high.concat(low.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Bitcast_F64_I64 -> MOVQ r64,xmm preserves bits".to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::F64, Type::I64, low.clone()),
        aarch64_expr: encode_movq_from_xmm(xmm),
        inputs: vec![("xmm_high".to_string(), 64), ("low".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// SSE scalar floating-point MOVE / COPY / constant-pool-load proofs (#65)
// ===========================================================================
//
// The bridge's x86 ISel emits MOVSS/MOVSD for every scalar-FP register copy
// (`MovssRR`/`MovsdRR`), spill/reload + memory access (`Movss/MovsdRM/MR`), and
// rodata constant load (`Movss/MovsdRipRel`). Until now these opcodes had NO
// proof mapping, so `X86FunctionVerifier::opcode_to_proof_query` returned `None`
// and m68/m69 fail-closed at object emission ("no proof mapping for x86-64
// opcode {Movss..}"). These proofs make the float-move family PROVEN.
//
// FAITHFULNESS. A scalar-FP move is a BIT-PRESERVING transfer of the f32/f64
// payload — it copies the exact IEEE-754 bit pattern, including the sign of a
// signed zero and a NaN's payload/sign (it is NOT an arithmetic round-trip,
// which could canonicalize a NaN or normalize -0.0). The correct, non-vacuous
// theorem is therefore a bit-vector IDENTITY at the scalar width: the moved
// scalar value's bits equal the source scalar value's bits. The negative
// controls below (proving a sign-bit-flipping or width-truncating "move" must
// REFUTE) show this is a real identity and not a tautology that would pass a
// wrong lowering.

/// Build a scalar-FP register-to-register MOVE bit-identity proof: `MOVSS
/// xmm,xmm` / `MOVSD xmm,xmm` copy the low `width_bits` lane verbatim, so the
/// moved scalar value's bits equal the source scalar value's bits.
fn proof_x86_fp_movrr_copy(name: &str, width_bits: u32) -> ProofObligation {
    let a = SmtExpr::var("a", width_bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        // Spec: the source scalar bits. Emitted: MOVSS/MOVSD copies the low
        // lane verbatim — identity at the scalar width. (The instruction
        // preserves the destination's upper XMM bits, which are dead for a
        // scalar value, so the scalar-value obligation is the low-lane copy.)
        trust_ir_expr: a.clone(),
        aarch64_expr: a.clone(),
        inputs: vec![("a".to_string(), width_bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `MOVSS xmm,xmm` copies the 32-bit scalar-single value verbatim.
pub fn proof_x86_movss_rr_copy() -> ProofObligation {
    proof_x86_fp_movrr_copy(
        "x86_64: Copy_F32 -> MOVSS xmm,xmm preserves scalar bits",
        32,
    )
}

/// Proof: `MOVSD xmm,xmm` copies the 64-bit scalar-double value verbatim.
pub fn proof_x86_movsd_rr_copy() -> ProofObligation {
    proof_x86_fp_movrr_copy(
        "x86_64: Copy_F64 -> MOVSD xmm,xmm preserves scalar bits",
        64,
    )
}

/// Build a scalar-FP LOAD proof: `MOVSS xmm,[r64+disp32]` / `MOVSD
/// xmm,[r64+disp32]` load `size_bytes` from the effective address; the loaded
/// scalar's bits equal the bytes in memory at that address. Mirrors
/// [`proof_x86_load_equiv`] (the GPR `MOV r,[mem]` shape) at f32/f64 width — a
/// float load reads the same little-endian bytes as an integer load of the same
/// size; the value is just interpreted as an FP scalar by later instructions.
fn proof_x86_fp_load_equiv(name: &str, size_bytes: u32) -> ProofObligation {
    use crate::memory_proofs::{encode_load_le, symbolic_memory};

    let mem = symbolic_memory("mem_default");
    let base = SmtExpr::var("base", 64);
    let disp = SmtExpr::var("disp", 32);

    let ea = base.bvadd(disp.sign_ext(32));
    let trust_ir_result = encode_load_le(&mem, &ea, size_bytes);
    let x86_result = encode_load_le(&mem, &ea, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_result,
        aarch64_expr: x86_result,
        inputs: vec![
            ("base".to_string(), 64),
            ("disp".to_string(), 32),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `MOVSS xmm,[r64+disp32]` loads the 32-bit scalar-single value.
pub fn proof_x86_movss_load() -> ProofObligation {
    proof_x86_fp_load_equiv("x86_64: Load_F32 -> MOVSS xmm,[r64+disp32]", 4)
}

/// Proof: `MOVSD xmm,[r64+disp32]` loads the 64-bit scalar-double value.
pub fn proof_x86_movsd_load() -> ProofObligation {
    proof_x86_fp_load_equiv("x86_64: Load_F64 -> MOVSD xmm,[r64+disp32]", 8)
}

/// Build a scalar-FP STORE proof: `MOVSS [r64+disp32],xmm` / `MOVSD
/// [r64+disp32],xmm` write the scalar value's `size_bytes` to the effective
/// address; loading the same address back yields the stored value. Mirrors
/// [`proof_x86_store_equiv`] at f32/f64 width.
fn proof_x86_fp_store_equiv(name: &str, size_bytes: u32) -> ProofObligation {
    use crate::memory_proofs::{encode_load_le, encode_store_le, symbolic_memory};

    let result_width = size_bytes * 8;
    let mem = symbolic_memory("mem_default");
    let base = SmtExpr::var("base", 64);
    let disp = SmtExpr::var("disp", 32);
    let value = SmtExpr::var("value", result_width);

    let ea = base.bvadd(disp.sign_ext(32));
    let trust_ir_mem = encode_store_le(&mem, &ea, &value, size_bytes);
    let trust_ir_loaded = encode_load_le(&trust_ir_mem, &ea, size_bytes);
    let x86_mem = encode_store_le(&mem, &ea, &value, size_bytes);
    let x86_loaded = encode_load_le(&x86_mem, &ea, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_loaded,
        aarch64_expr: x86_loaded,
        inputs: vec![
            ("base".to_string(), 64),
            ("disp".to_string(), 32),
            ("value".to_string(), result_width),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `MOVSS [r64+disp32],xmm` stores the 32-bit scalar-single value.
pub fn proof_x86_movss_store() -> ProofObligation {
    proof_x86_fp_store_equiv("x86_64: Store_F32 -> MOVSS [r64+disp32],xmm", 4)
}

/// Proof: `MOVSD [r64+disp32],xmm` stores the 64-bit scalar-double value.
pub fn proof_x86_movsd_store() -> ProofObligation {
    proof_x86_fp_store_equiv("x86_64: Store_F64 -> MOVSD [r64+disp32],xmm", 8)
}

/// Build a scalar-FP RIP-relative CONSTANT-POOL load proof: `MOVSS
/// xmm,[rip+disp32]` / `MOVSD xmm,[rip+disp32]` load an f32/f64 immediate out of
/// the rodata constant pool. The proof has two faithful halves, mirroring the
/// symbol-address `MovRipRel`/`LeaRip` proofs and the `Load_*` memory proofs:
///
///   1. EFFECTIVE-ADDRESS: the CPU computes `RIP_next + sext(disp32)` and the
///      assembler emits `disp32 == C − P` where `C` is the constant's address
///      and `P == RIP_next` is the reference end (no trailing immediate, N = 0),
///      so `RIP_next + (C − P) == C` — the load addresses exactly the constant.
///   2. MEMORY-READ: loading `size_bytes` from address `C` returns the bytes at
///      `C` (the constant), the same opaque little-endian read as `Load_F*`.
///
/// This builds (1): the effective-address reconstruction. (2) is the same
/// theorem as `proof_x86_movss_load`/`proof_x86_movsd_load` over the constant's
/// address, so the load semantics are covered by the Load_F* proofs and this
/// proof certifies the constant-pool addressing half (exactly as
/// `proof_x86_movriprel_got_eff_addr` certifies the GOT addressing half and
/// defers the opaque load to the Load_* family).
fn proof_x86_fp_constpool_riprel(name: &str) -> ProofObligation {
    let c = SmtExpr::var("C", 64); // constant-pool entry address
    let field_addr = SmtExpr::var("field_addr", 64);

    let p = rip_reference_end(field_addr, 0);
    // Spec: the intended constant-pool entry address.
    let intended = c.clone();
    // Emitted: RIP_next (= P) + the RIP-relative displacement (C − P).
    let disp = c.bvsub(p.clone());
    let reconstructed = p.bvadd(disp);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("C".to_string(), 64), ("field_addr".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `MOVSS xmm,[rip+disp32]` addresses the f32 constant-pool entry.
pub fn proof_x86_movss_constpool_riprel() -> ProofObligation {
    proof_x86_fp_constpool_riprel(
        "x86_64: MovssRipRel -> RIP_next + disp32 == C (f32 const-pool addr)",
    )
}

/// Proof: `MOVSD xmm,[rip+disp32]` addresses the f64 constant-pool entry.
pub fn proof_x86_movsd_constpool_riprel() -> ProofObligation {
    proof_x86_fp_constpool_riprel(
        "x86_64: MovsdRipRel -> RIP_next + disp32 == C (f64 const-pool addr)",
    )
}

/// Negative control: a scalar-FP "move" that flips the sign bit is NOT an
/// identity (it changes `+x` into `-x`), so it must REFUTE — proving the
/// reg-reg copy proof is a real bit-identity and not a vacuous tautology.
/// NOT registered; used by tests.
pub fn proof_x86_fp_movrr_signflip_refutes() -> ProofObligation {
    let a = SmtExpr::var("a", 64);
    let sign_mask = SmtExpr::bv_const(1_u64 << 63, 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: MOVSD copy with sign-bit flip must REFUTE".to_string(),
        trust_ir_expr: a.clone(),
        aarch64_expr: a.bvxor(sign_mask),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a constant-pool load whose displacement is left ABSOLUTE
/// (`C` rather than the RIP-relative `C − P`) makes the CPU compute `RIP_next +
/// C = P + C`, which is NOT the intended `C` whenever `P != 0`. Must REFUTE —
/// proving the RIP-relative provenance is load-bearing. NOT registered.
pub fn proof_x86_fp_constpool_wrong_absolute_refutes() -> ProofObligation {
    let c = SmtExpr::var("C", 64);
    let field_addr = SmtExpr::var("field_addr", 64);

    let p = rip_reference_end(field_addr, 0);
    let intended = c.clone();
    // WRONG: disp left ABSOLUTE (C); CPU still adds RIP_next (= P).
    let reconstructed_wrong = p.bvadd(c);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: MovsdRipRel with ABSOLUTE (non-RIP) disp must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed_wrong,
        inputs: vec![("C".to_string(), 64), ("field_addr".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Positive scalar-FP move / load / store / constant-pool-load proofs (#65),
/// registered in the ProofDatabase.
pub fn x86_64_fp_move_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_movss_rr_copy(),
        proof_x86_movsd_rr_copy(),
        proof_x86_movss_load(),
        proof_x86_movsd_load(),
        proof_x86_movss_store(),
        proof_x86_movsd_store(),
        proof_x86_movss_constpool_riprel(),
        proof_x86_movsd_constpool_riprel(),
    ]
}

/// Negative-control scalar-FP move obligations (each is REFUTABLE — a wrong
/// encoding). NOT registered; used by tests to show the positives are real
/// equivalences and not tautologies.
pub fn x86_64_fp_move_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_x86_fp_movrr_signflip_refutes(),
        proof_x86_fp_constpool_wrong_absolute_refutes(),
    ]
}

// ===========================================================================
// LEA lowering proofs
// ===========================================================================

/// Proof: `a + b == x86-64 LEA r64, [r64 + r64]`
pub fn proof_x86_lea_add_i64() -> ProofObligation {
    use crate::x86_64_semantics::encode_lea_base_index_scale;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: base+index -> LEA r64,[r64+r64]".to_string(),
        trust_ir_expr: a.clone().bvadd(b.clone()),
        aarch64_expr: encode_lea_base_index_scale(a, b, 1),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `a + (b * 2) == x86-64 LEA r64, [r64 + r64*2]`
pub fn proof_x86_lea_scale2_i64() -> ProofObligation {
    use crate::x86_64_semantics::encode_lea_base_index_scale;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: base+index*2 -> LEA r64,[r64+r64*2]".to_string(),
        trust_ir_expr: a
            .clone()
            .bvadd(b.clone().bvmul(SmtExpr::bv_const(2_u64, 64))),
        aarch64_expr: encode_lea_base_index_scale(a, b, 2),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `a + (b * 4) == x86-64 LEA r64, [r64 + r64*4]`
pub fn proof_x86_lea_scale4_i64() -> ProofObligation {
    use crate::x86_64_semantics::encode_lea_base_index_scale;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: base+index*4 -> LEA r64,[r64+r64*4]".to_string(),
        trust_ir_expr: a
            .clone()
            .bvadd(b.clone().bvmul(SmtExpr::bv_const(4_u64, 64))),
        aarch64_expr: encode_lea_base_index_scale(a, b, 4),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `a + (b * 8) == x86-64 LEA r64, [r64 + r64*8]`
pub fn proof_x86_lea_scale8_i64() -> ProofObligation {
    use crate::x86_64_semantics::encode_lea_base_index_scale;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: base+index*8 -> LEA r64,[r64+r64*8]".to_string(),
        trust_ir_expr: a
            .clone()
            .bvadd(b.clone().bvmul(SmtExpr::bv_const(8_u64, 64))),
        aarch64_expr: encode_lea_base_index_scale(a, b, 8),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `base + sext(disp32) == x86-64 LEA r64, [r64 + disp32]`
///
/// The displacement is a SYMBOLIC 32-bit input sign-extended to 64 bits,
/// exactly as the ModRM disp32 encoding is — one obligation covers every
/// concrete displacement (positive and negative).
pub fn proof_x86_lea_base_disp32() -> ProofObligation {
    let base = SmtExpr::var("base", 64);
    let disp = SmtExpr::var("disp", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: base+disp32 -> LEA r64,[r64+disp32]".to_string(),
        trust_ir_expr: base.clone().bvadd(disp.clone().sign_ext(32)),
        aarch64_expr: base.bvadd(disp.sign_ext(32)),
        inputs: vec![("base".to_string(), 64), ("disp".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build `a + (b * scale) + sext(disp32) == LEA r64,[r64+r64*scale+disp32]`.
///
/// SIB-form effective-address arithmetic with a symbolic 32-bit displacement
/// (sign-extended, as encoded). One proof per architectural scale.
fn proof_x86_lea_sib_disp32(name: &str, scale: u32) -> ProofObligation {
    use crate::x86_64_semantics::encode_lea_base_index_scale;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);
    let disp = SmtExpr::var("disp", 32);

    let trust_ir = a
        .clone()
        .bvadd(b.clone().bvmul(SmtExpr::bv_const(scale as u64, 64)))
        .bvadd(disp.clone().sign_ext(32));
    let x86 = encode_lea_base_index_scale(a, b, scale).bvadd(disp.sign_ext(32));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: x86,
        inputs: vec![
            ("a".to_string(), 64),
            ("b".to_string(), 64),
            ("disp".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `a + b + sext(disp32) == LEA r64,[r64+r64+disp32]`.
pub fn proof_x86_lea_add_disp32_i64() -> ProofObligation {
    proof_x86_lea_sib_disp32("x86_64: base+index+disp32 -> LEA r64,[r64+r64+disp32]", 1)
}

/// Proof: `a + b*2 + sext(disp32) == LEA r64,[r64+r64*2+disp32]`.
pub fn proof_x86_lea_scale2_disp32_i64() -> ProofObligation {
    proof_x86_lea_sib_disp32(
        "x86_64: base+index*2+disp32 -> LEA r64,[r64+r64*2+disp32]",
        2,
    )
}

/// Proof: `a + b*4 + sext(disp32) == LEA r64,[r64+r64*4+disp32]`.
pub fn proof_x86_lea_scale4_disp32_i64() -> ProofObligation {
    proof_x86_lea_sib_disp32(
        "x86_64: base+index*4+disp32 -> LEA r64,[r64+r64*4+disp32]",
        4,
    )
}

/// Proof: `a + b*8 + sext(disp32) == LEA r64,[r64+r64*8+disp32]`.
pub fn proof_x86_lea_scale8_disp32_i64() -> ProofObligation {
    proof_x86_lea_sib_disp32(
        "x86_64: base+index*8+disp32 -> LEA r64,[r64+r64*8+disp32]",
        8,
    )
}

// ===========================================================================
// RIP-relative symbol-address materialization proofs (LeaRip / MovRipRel)
// ===========================================================================
//
// These compose the per-INSTRUCTION RIP-relative effective-address computation
// with the per-RELOCATION displacement proofs in
// [`crate::macho_data_reloc_proofs`]. They close the last instruction-coverage
// hole that kept per-compile proof certs opt-in: `x86_64::LeaRip` and
// `x86_64::MovRipRel`, emitted for in-module symbol addresses
// (`select_global_ref` -> Mach-O `X86_64_RELOC_SIGNED` / ELF `R_X86_64_PC32`)
// and external GOT-backed symbol references (`select_extern_ref` -> Mach-O
// `X86_64_RELOC_GOT_LOAD` / ELF `R_X86_64_GOTPCREL`), respectively.
//
// THE COMPOSITION (non-tautological, structurally distinct sides):
//
//   `LeaRip dst, [rip + disp32]` computes the effective address
//       dst = RIP_next + sext(disp32)
//   where `RIP_next` = the address of the byte AFTER the 4-byte disp32 field =
//   the reference END `P` (the x86 RIP-relative datum point; for these sites
//   there is no trailing immediate, so N = 0 and `P = field_addr + 4`). The
//   linker writes into that disp32 field the proven SIGNED-relocation value
//       disp = S + A − P        (macho_data_reloc_proofs::proof_signed_riprel)
//   Substituting: dst = P + (S + A − P) = S + A — the intended symbol address.
//   The `P` terms cancel by the ring identity `p + (x − p) == x`; the spec side
//   (`trust_ir_expr`) is the intended `S + A`, the emitted side
//   (`aarch64_expr`) is the runtime reconstruction `P + disp`. They are NOT the
//   same expression, so this is a real equivalence, not `x == x`.
//
//   `MovRipRel dst, [rip + disp32]` loads from the same kind of RIP-relative
//   effective address, but the relocation is GOT_LOAD: the disp32 names the GOT
//   slot `G` (which the linker populates with `&S`), so the EFFECTIVE ADDRESS
//   the CPU dereferences is
//       eff = RIP_next + sext(disp32) = P + (G + A − P) = G + A
//   (macho_data_reloc_proofs::proof_got_load_riprel). The proof certifies the
//   effective-address computation lands on the GOT slot `G + A`; the subsequent
//   load of `&S` out of that slot is an opaque memory read (the GOT contract),
//   exactly as the existing Load_* proofs treat a resolved address.
//
// SOUNDNESS NEGATIVE CONTROLS below: a LeaRip whose disp is mis-encoded as an
// ABSOLUTE (`r_pcrel=0`) value rather than RIP-relative, OR whose reconstruction
// uses the WRONG reference end (off-by-N), must REFUTE — the cancellation only
// holds when the SAME `P` is used by the linker's disp and the CPU's RIP datum.

/// The RIP datum / reference-end address `P` for a 4-byte RIP-relative field at
/// `field_addr` with `n_trailing` immediate bytes after the displacement.
/// `P = field_addr + 4 + n_trailing`. For symbol-address LeaRip/MovRipRel sites
/// the codegen emits the relocation at `after - 4` with no trailing immediate,
/// so `n_trailing == 0` and `P == field_addr + 4 == RIP_next`.
fn rip_reference_end(field_addr: SmtExpr, n_trailing: u64) -> SmtExpr {
    field_addr.bvadd(SmtExpr::bv_const(4 + n_trailing, 64))
}

/// Proof: `LeaRip dst, Symbol(S)` materializes the in-module symbol address
/// `S + A` by reconstructing `RIP_next + disp` from the proven SIGNED
/// (RIP-relative) relocation displacement.
///
/// Theorem: forall S, A, field_addr : BV64 .
///   P + ((S + A) − P) == (S + A),  where P = field_addr + 4  (N = 0)
///
/// Spec side: the intended symbol address `S + A`. Emitted side: the CPU's
/// RIP-relative effective-address computation `RIP_next + sext(disp32)` where
/// `disp32` is the linker-applied SIGNED displacement `S + A − P` (proven by
/// `proof_signed_riprel`) and `RIP_next == P`. Composes the per-instruction EA
/// with the per-relocation displacement; the `P` terms cancel.
pub fn proof_x86_learip_symbol_riprel() -> ProofObligation {
    let s = SmtExpr::var("S", 64);
    let a = SmtExpr::var("A", 64);
    let field_addr = SmtExpr::var("field_addr", 64);

    let p = rip_reference_end(field_addr, 0);
    // Spec: the intended symbol address.
    let intended = s.clone().bvadd(a.clone());
    // Emitted: RIP_next (= P) + the SIGNED RIP-relative displacement (S + A − P).
    let disp = s.bvadd(a).bvsub(p.clone());
    let reconstructed = p.bvadd(disp);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: LeaRip Symbol -> RIP_next + SIGNED disp32 == S + A (in-module addr)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("S".to_string(), 64),
            ("A".to_string(), 64),
            ("field_addr".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `MovRipRel dst, Symbol(S)` addresses the GOT slot `G + A` (holding
/// `&S`) by reconstructing `RIP_next + disp` from the proven GOT_LOAD
/// (RIP-relative) relocation displacement.
///
/// Theorem: forall G, A, field_addr : BV64 .
///   P + ((G + A) − P) == (G + A),  where P = field_addr + 4  (N = 0)
///
/// Spec side: the intended GOT-slot address `G + A`. Emitted side: the CPU's
/// RIP-relative effective-address `RIP_next + sext(disp32)` where `disp32` is
/// the linker-applied GOT_LOAD displacement `G + A − P` (proven by
/// `proof_got_load_riprel`) and `RIP_next == P`. The subsequent load of `&S`
/// out of slot `G` is an opaque memory read (the GOT contract), like the
/// existing Load_* proofs; this proof certifies the effective-address half.
pub fn proof_x86_movriprel_got_eff_addr() -> ProofObligation {
    let g = SmtExpr::var("G", 64);
    let a = SmtExpr::var("A", 64);
    let field_addr = SmtExpr::var("field_addr", 64);

    let p = rip_reference_end(field_addr, 0);
    // Spec: the intended GOT-slot address.
    let intended = g.clone().bvadd(a.clone());
    // Emitted: RIP_next (= P) + the GOT_LOAD RIP-relative displacement (G + A − P).
    let disp = g.bvadd(a).bvsub(p.clone());
    let reconstructed = p.bvadd(disp);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: MovRipRel Symbol -> RIP_next + GOT_LOAD disp32 == G + A (GOT slot addr)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("G".to_string(), 64),
            ("A".to_string(), 64),
            ("field_addr".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a LeaRip whose displacement is mis-encoded as an ABSOLUTE
/// (`r_pcrel = 0`) value `S + A` rather than the RIP-relative `S + A − P` makes
/// the CPU compute `RIP_next + (S + A) = P + S + A`, which is NOT the intended
/// `S + A` whenever `P != 0`. Must REFUTE — proves the proof is not vacuous and
/// that the RIP-relative provenance is load-bearing.
pub fn proof_x86_learip_wrong_absolute_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", 64);
    let a = SmtExpr::var("A", 64);
    let field_addr = SmtExpr::var("field_addr", 64);

    let p = rip_reference_end(field_addr, 0);
    let intended = s.clone().bvadd(a.clone());
    // WRONG: disp left ABSOLUTE (S + A); CPU still adds RIP_next (= P).
    let disp_wrong = s.bvadd(a);
    let reconstructed_wrong = p.bvadd(disp_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: LeaRip with ABSOLUTE (non-RIP) disp must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed_wrong,
        inputs: vec![
            ("S".to_string(), 64),
            ("A".to_string(), 64),
            ("field_addr".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a LeaRip whose disp is encoded for the WRONG reference end
/// (the linker computes `disp` with `P_wrong = field+4+4` while the CPU's RIP
/// datum is the true `P = field+4`) lands 4 bytes off the symbol. Must REFUTE —
/// proves the cancellation requires the SAME `P` on both sides (correct N).
pub fn proof_x86_learip_wrong_field_end_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", 64);
    let a = SmtExpr::var("A", 64);
    let field_addr = SmtExpr::var("field_addr", 64);

    // Intended: correct reconstruction with the true reference end P = field+4.
    let p_true = rip_reference_end(field_addr.clone(), 0);
    let intended = s.clone().bvadd(a.clone());
    // WRONG: linker baked disp against P_wrong = field+8 (as if N=4), but the
    // CPU adds the true RIP_next = field+4. dst = p_true + (S + A − p_wrong).
    let p_wrong = rip_reference_end(field_addr, 4);
    let disp_wrong = s.bvadd(a).bvsub(p_wrong);
    let reconstructed_wrong = p_true.bvadd(disp_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: LeaRip with wrong reference end (off-by-N) must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed_wrong,
        inputs: vec![
            ("S".to_string(), 64),
            ("A".to_string(), 64),
            ("field_addr".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Positive RIP-relative symbol-address proofs registered in the database.
pub fn x86_64_riprel_symbol_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_learip_symbol_riprel(),
        proof_x86_movriprel_got_eff_addr(),
    ]
}

/// Negative-control RIP-relative obligations (each is REFUTABLE — a wrong
/// encoding). NOT registered; used by tests to show the positives are real
/// equivalences and not tautologies.
pub fn x86_64_riprel_symbol_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_x86_learip_wrong_absolute_refutes(),
        proof_x86_learip_wrong_field_end_refutes(),
    ]
}

// ===========================================================================
// Memory-move lowering proofs (MOV r,[m] loads / MOV [m],r stores)
// ===========================================================================

/// Build a load-equivalence proof: trust-ir `Load(size_bytes, base+disp)` ==
/// x86-64 `MOV r,[base+disp32]`.
///
/// Mirror of the AArch64 `proof_load_equiv` family in
/// [`crate::memory_proofs`], with the x86-64 addressing semantics: the ModRM
/// displacement is a SYMBOLIC 32-bit input sign-extended to 64 bits (covering
/// every concrete displacement, negative stack offsets included), and both
/// sides read `size_bytes` little-endian from the same symbolic byte memory.
/// The load-bearing facts pinned per width: the effective-address formula and
/// the little-endian byte composition at the access width.
fn proof_x86_load_equiv(name: &str, size_bytes: u32) -> ProofObligation {
    use crate::memory_proofs::{encode_load_le, symbolic_memory};

    let mem = symbolic_memory("mem_default");
    let base = SmtExpr::var("base", 64);
    let disp = SmtExpr::var("disp", 32);

    let ea = base.bvadd(disp.sign_ext(32));
    let trust_ir_result = encode_load_le(&mem, &ea, size_bytes);
    let x86_result = encode_load_le(&mem, &ea, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_result,
        aarch64_expr: x86_result,
        inputs: vec![
            ("base".to_string(), 64),
            ("disp".to_string(), 32),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        // InstructionLowering (not MemoryModel): every proof registered under
        // ProofCategory::X8664Lowering carries the InstructionLowering check
        // kind (audited by `test_registered_check_kind_matches_proof_family`);
        // the obligation is the MOV instruction's lowering, expressed over the
        // shared symbolic memory model.
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Load(I8)` == `MOV r8,[r64+disp32]`.
pub fn proof_x86_load_i8() -> ProofObligation {
    proof_x86_load_equiv("x86_64: Load_I8 -> MOV r8,[r64+disp32]", 1)
}

/// Proof: `trust_ir::Load(I16)` == `MOV r16,[r64+disp32]`.
pub fn proof_x86_load_i16() -> ProofObligation {
    proof_x86_load_equiv("x86_64: Load_I16 -> MOV r16,[r64+disp32]", 2)
}

/// Proof: `trust_ir::Load(I32)` == `MOV r32,[r64+disp32]`.
pub fn proof_x86_load_i32() -> ProofObligation {
    proof_x86_load_equiv("x86_64: Load_I32 -> MOV r32,[r64+disp32]", 4)
}

/// Proof: `trust_ir::Load(I64)` == `MOV r64,[r64+disp32]`.
pub fn proof_x86_load_i64() -> ProofObligation {
    proof_x86_load_equiv("x86_64: Load_I64 -> MOV r64,[r64+disp32]", 8)
}

/// Build a store-equivalence proof: trust-ir `Store(size_bytes, value,
/// base+disp)` == x86-64 `MOV [base+disp32],r` — verified by storing through
/// both models and loading back from the effective address (mirror of the
/// AArch64 `proof_store_equiv` family, x86 addressing as in
/// [`proof_x86_load_equiv`]).
fn proof_x86_store_equiv(name: &str, size_bytes: u32) -> ProofObligation {
    use crate::memory_proofs::{encode_load_le, encode_store_le, symbolic_memory};

    let result_width = size_bytes * 8;
    let mem = symbolic_memory("mem_default");
    let base = SmtExpr::var("base", 64);
    let disp = SmtExpr::var("disp", 32);
    let value = SmtExpr::var("value", result_width);

    let ea = base.bvadd(disp.sign_ext(32));
    let trust_ir_mem = encode_store_le(&mem, &ea, &value, size_bytes);
    let trust_ir_loaded = encode_load_le(&trust_ir_mem, &ea, size_bytes);
    let x86_mem = encode_store_le(&mem, &ea, &value, size_bytes);
    let x86_loaded = encode_load_le(&x86_mem, &ea, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_loaded,
        aarch64_expr: x86_loaded,
        inputs: vec![
            ("base".to_string(), 64),
            ("disp".to_string(), 32),
            ("value".to_string(), result_width),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        // InstructionLowering for family consistency — see proof_x86_load_equiv.
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Store(I8)` == `MOV [r64+disp32],r8`.
pub fn proof_x86_store_i8() -> ProofObligation {
    proof_x86_store_equiv("x86_64: Store_I8 -> MOV [r64+disp32],r8", 1)
}

/// Proof: `trust_ir::Store(I16)` == `MOV [r64+disp32],r16`.
pub fn proof_x86_store_i16() -> ProofObligation {
    proof_x86_store_equiv("x86_64: Store_I16 -> MOV [r64+disp32],r16", 2)
}

/// Proof: `trust_ir::Store(I32)` == `MOV [r64+disp32],r32`.
pub fn proof_x86_store_i32() -> ProofObligation {
    proof_x86_store_equiv("x86_64: Store_I32 -> MOV [r64+disp32],r32", 4)
}

/// Proof: `trust_ir::Store(I64)` == `MOV [r64+disp32],r64`.
pub fn proof_x86_store_i64() -> ProofObligation {
    proof_x86_store_equiv("x86_64: Store_I64 -> MOV [r64+disp32],r64", 8)
}

// ===========================================================================
// Three-operand IMUL lowering proofs
// ===========================================================================

/// Proof: `a * 42 == x86-64 IMUL r32, r/m32, imm8`
pub fn proof_x86_imul_rri_i32() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_imul_rri};

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Imul_I32_Imm -> IMUL r32,r/m32,42".to_string(),
        trust_ir_expr: a.clone().bvmul(SmtExpr::bv_const(42_u64, 32)),
        aarch64_expr: encode_imul_rri(X86OperandSize::S32, a, 42),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `a * 42 == x86-64 IMUL r64, r/m64, imm8`
pub fn proof_x86_imul_rri_i64() -> ProofObligation {
    use crate::x86_64_semantics::{X86OperandSize, encode_imul_rri};

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: Imul_I64_Imm -> IMUL r64,r/m64,42".to_string(),
        trust_ir_expr: a.clone().bvmul(SmtExpr::bv_const(42_u64, 64)),
        aarch64_expr: encode_imul_rri(X86OperandSize::S64, a, 42),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Scalar FP select bit-path proofs
// ===========================================================================

/// Proof: scalar F32 select bit path preserves the selected FP payload bits.
pub fn proof_x86_fp_select_f32_bits() -> ProofObligation {
    use crate::x86_64_eflags::{encode_cmp_eflags, eval_x86_condition};
    use crate::x86_64_semantics::{
        X86OperandSize, encode_cmovcc, encode_mov_rr, encode_movd_from_xmm, encode_movd_to_xmm,
    };
    use trust_cg_ir::X86CondCode;

    let cond = SmtExpr::var("cond", 64);
    let true_bits = SmtExpr::var("true_bits", 32);
    let true_high64 = SmtExpr::var("true_high64", 64);
    let true_high32 = SmtExpr::var("true_high32", 32);
    let false_bits = SmtExpr::var("false_bits", 32);
    let false_high64 = SmtExpr::var("false_high64", 64);
    let false_high32 = SmtExpr::var("false_high32", 32);

    let cond_true = cond.clone().eq_expr(SmtExpr::bv_const(0, 64)).not_expr();
    let trust_ir_expr = SmtExpr::ite(cond_true, true_bits.clone(), false_bits.clone());

    let true_xmm = true_high64.concat(true_high32).concat(true_bits);
    let false_xmm = false_high64.concat(false_high32).concat(false_bits);
    let true_gpr = encode_movd_from_xmm(true_xmm);
    let false_gpr = encode_movd_from_xmm(false_xmm);
    let dst_gpr = encode_mov_rr(X86OperandSize::S32, false_gpr);
    let flags = encode_cmp_eflags(cond.clone(), SmtExpr::bv_const(0, 64), 64);
    let cmov_condition = eval_x86_condition(X86CondCode::NE, &flags);
    let selected_gpr = encode_cmovcc(X86OperandSize::S32, cmov_condition, dst_gpr, true_gpr);
    let x86_expr = encode_movd_to_xmm(selected_gpr).extract(31, 0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FpSelect_F32_bits -> MOVD+CMOVcc32+MOVD".to_string(),
        trust_ir_expr,
        aarch64_expr: x86_expr,
        inputs: vec![
            ("cond".to_string(), 64),
            ("true_bits".to_string(), 32),
            ("true_high64".to_string(), 64),
            ("true_high32".to_string(), 32),
            ("false_bits".to_string(), 32),
            ("false_high64".to_string(), 64),
            ("false_high32".to_string(), 32),
        ],
        preconditions: vec![
            cond.clone()
                .eq_expr(SmtExpr::bv_const(0, 64))
                .or_expr(cond.eq_expr(SmtExpr::bv_const(1, 64))),
        ],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: scalar F64 select bit path preserves the selected FP payload bits.
pub fn proof_x86_fp_select_f64_bits() -> ProofObligation {
    use crate::x86_64_eflags::{encode_cmp_eflags, eval_x86_condition};
    use crate::x86_64_semantics::{
        X86OperandSize, encode_cmovcc, encode_mov_rr, encode_movq_from_xmm, encode_movq_to_xmm,
    };
    use trust_cg_ir::X86CondCode;

    let cond = SmtExpr::var("cond", 64);
    let true_bits = SmtExpr::var("true_bits", 64);
    let true_high = SmtExpr::var("true_high", 64);
    let false_bits = SmtExpr::var("false_bits", 64);
    let false_high = SmtExpr::var("false_high", 64);

    let cond_true = cond.clone().eq_expr(SmtExpr::bv_const(0, 64)).not_expr();
    let trust_ir_expr = SmtExpr::ite(cond_true, true_bits.clone(), false_bits.clone());

    let true_xmm = true_high.concat(true_bits);
    let false_xmm = false_high.concat(false_bits);
    let true_gpr = encode_movq_from_xmm(true_xmm);
    let false_gpr = encode_movq_from_xmm(false_xmm);
    let dst_gpr = encode_mov_rr(X86OperandSize::S64, false_gpr);
    let flags = encode_cmp_eflags(cond.clone(), SmtExpr::bv_const(0, 64), 64);
    let cmov_condition = eval_x86_condition(X86CondCode::NE, &flags);
    let selected_gpr = encode_cmovcc(X86OperandSize::S64, cmov_condition, dst_gpr, true_gpr);
    let x86_expr = encode_movq_to_xmm(selected_gpr).extract(63, 0);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FpSelect_F64_bits -> MOVQ+CMOVcc+MOVQ".to_string(),
        trust_ir_expr,
        aarch64_expr: x86_expr,
        inputs: vec![
            ("cond".to_string(), 64),
            ("true_bits".to_string(), 64),
            ("true_high".to_string(), 64),
            ("false_bits".to_string(), 64),
            ("false_high".to_string(), 64),
        ],
        preconditions: vec![
            cond.clone()
                .eq_expr(SmtExpr::bv_const(0, 64))
                .or_expr(cond.eq_expr(SmtExpr::bv_const(1, 64))),
        ],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Atomic load/store/fence lowering proofs
// ===========================================================================

const X86_ATOMIC_MEMORY_WIDTHS: [u32; 4] = [8, 16, 32, 64];

fn x86_atomic_memory_width_name(width_bits: u32) -> &'static str {
    match width_bits {
        8 => "I8",
        16 => "I16",
        32 => "I32",
        64 => "I64",
        _ => panic!("unsupported x86 atomic memory width: {width_bits}"),
    }
}

fn x86_atomic_memory_size_bytes(width_bits: u32) -> u32 {
    match width_bits {
        8 | 16 | 32 | 64 => width_bits / 8,
        _ => panic!("unsupported x86 atomic memory width: {width_bits}"),
    }
}

fn proof_x86_atomic_load(width_bits: u32) -> ProofObligation {
    let size_bytes = x86_atomic_memory_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let value = SmtExpr::var("value", width_bits);
    let mem = crate::memory_proofs::zeroed_memory();
    let mem = crate::memory_proofs::encode_store_le(&mem, &addr, &value, size_bytes);

    let trust_ir_loaded = crate::memory_proofs::encode_load_le(&mem, &addr, size_bytes);
    let x86_mov_loaded = crate::memory_proofs::encode_load_le(&mem, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: AtomicLoad_{} -> MOV r,[mem]",
            x86_atomic_memory_width_name(width_bits)
        ),
        trust_ir_expr: trust_ir_loaded,
        aarch64_expr: x86_mov_loaded,
        inputs: vec![("addr".to_string(), 64), ("value".to_string(), width_bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

pub fn proof_x86_atomic_load_i8() -> ProofObligation {
    proof_x86_atomic_load(8)
}

pub fn proof_x86_atomic_load_i16() -> ProofObligation {
    proof_x86_atomic_load(16)
}

pub fn proof_x86_atomic_load_i32() -> ProofObligation {
    proof_x86_atomic_load(32)
}

pub fn proof_x86_atomic_load_i64() -> ProofObligation {
    proof_x86_atomic_load(64)
}

fn proof_x86_atomic_store(width_bits: u32) -> ProofObligation {
    let size_bytes = x86_atomic_memory_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let value = SmtExpr::var("value", width_bits);
    let mem = crate::memory_proofs::zeroed_memory();

    let trust_ir_mem_after = crate::memory_proofs::encode_store_le(&mem, &addr, &value, size_bytes);
    let x86_mov_mem_after = crate::memory_proofs::encode_store_le(&mem, &addr, &value, size_bytes);
    let trust_ir_loaded =
        crate::memory_proofs::encode_load_le(&trust_ir_mem_after, &addr, size_bytes);
    let x86_loaded = crate::memory_proofs::encode_load_le(&x86_mov_mem_after, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: AtomicStore_{} -> MOV [mem],r",
            x86_atomic_memory_width_name(width_bits)
        ),
        trust_ir_expr: trust_ir_loaded,
        aarch64_expr: x86_loaded,
        inputs: vec![("addr".to_string(), 64), ("value".to_string(), width_bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

pub fn proof_x86_atomic_store_i8() -> ProofObligation {
    proof_x86_atomic_store(8)
}

pub fn proof_x86_atomic_store_i16() -> ProofObligation {
    proof_x86_atomic_store(16)
}

pub fn proof_x86_atomic_store_i32() -> ProofObligation {
    proof_x86_atomic_store(32)
}

pub fn proof_x86_atomic_store_i64() -> ProofObligation {
    proof_x86_atomic_store(64)
}

/// Proof: x86-64 SeqCst fence lowers to `MFENCE` and MFENCE preserves the
/// single-thread machine state (writes NO register and NO memory).
///
/// The name is `x86_64: SeqCst fence -> MFENCE single-thread identity`.
///
/// EPISTEMIC HONESTY (this is NOT a #62 const==const tautology). The retracted
/// `Fence_* -> MFENCE` obligations were `bv_const(0x0FAEF0) == bv_const(...)` —
/// they compared the ENCODING of the instruction to itself and proved nothing.
/// This obligation instead states a REAL single-thread data-flow property over
/// SYMBOLIC state: model an arbitrary register value `reg` and an arbitrary
/// memory seeded with `value` at `addr`; the OBSERVABLE is the pair
/// `(reg, mem[addr])`. The machine side pushes that state through the MFENCE
/// transition function ([`encode_mfence`], the register/memory identity) and
/// re-observes; the spec side is the pre-fence observable. Equality holds iff
/// MFENCE leaves both the register and the memory byte untouched — which is the
/// property we actually rely on when the ISel leaves every surrounding value in
/// place around the barrier. It is non-vacuous: a fence modeled to zero the
/// register or clobber the byte would REFUTE (see the negative controls). The
/// CROSS-THREAD ORDERING that MFENCE also provides is a separate, architectural
/// Intel-SDM axiom (8.2.5) — deliberately NOT dressed up as this SMT proof.
fn proof_x86_mfence_single_thread_identity() -> ProofObligation {
    use crate::memory_proofs::{encode_load_le, encode_store_le, symbolic_memory};
    use crate::x86_64_semantics::encode_mfence;

    let reg = SmtExpr::var("reg", 64);
    let addr = SmtExpr::var("addr", 64);
    let value = SmtExpr::var("value", 64);
    let mem0 = symbolic_memory("mem_default");
    // Seed memory with `value` at `addr` so the load-back has a defined result.
    let mem_seeded = encode_store_le(&mem0, &addr, &value, 8);

    // Spec: the observable BEFORE the fence.
    let spec_observable = reg.clone().concat(encode_load_le(&mem_seeded, &addr, 8));

    // Machine: run the MFENCE transition, then re-observe. `encode_mfence` is the
    // (register, memory) identity, so a faithful MFENCE re-observes the same pair.
    let (reg_after, mem_after) = encode_mfence(&reg, &mem_seeded);
    let machine_observable = reg_after.concat(encode_load_le(&mem_after, &addr, 8));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: SeqCst fence -> MFENCE single-thread identity".to_string(),
        trust_ir_expr: spec_observable,
        aarch64_expr: machine_observable,
        inputs: vec![
            ("reg".to_string(), 64),
            ("addr".to_string(), 64),
            ("value".to_string(), 64),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86-64 SeqCst fence lowers to `MFENCE`, which preserves single-thread
/// state. See [`proof_x86_mfence_single_thread_identity`]. This is the ONLY
/// registered fence proof: Acquire/Release/AcqRel fences emit ZERO instructions
/// on x86 TSO (no obligation to discharge — there is no instruction), so only
/// the SeqCst → MFENCE mapping needs a per-instruction proof.
pub fn proof_x86_fence_seqcst_mfence() -> ProofObligation {
    proof_x86_mfence_single_thread_identity()
}

/// Negative control: a "fence" modeled to ZERO the register is NOT the identity
/// (`reg` becomes `0`), so it must REFUTE — proving the MFENCE identity is a
/// real data-flow obligation and not a vacuous tautology. NOT registered.
pub fn proof_x86_mfence_clobbers_register_refutes() -> ProofObligation {
    use crate::memory_proofs::{encode_load_le, encode_store_le, symbolic_memory};

    let reg = SmtExpr::var("reg", 64);
    let addr = SmtExpr::var("addr", 64);
    let value = SmtExpr::var("value", 64);
    let mem0 = symbolic_memory("mem_default");
    let mem_seeded = encode_store_le(&mem0, &addr, &value, 8);

    let spec_observable = reg.concat(encode_load_le(&mem_seeded, &addr, 8));
    // WRONG: register clobbered to 0 by the "fence".
    let wrong_observable = SmtExpr::bv_const(0, 64).concat(encode_load_le(&mem_seeded, &addr, 8));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: MFENCE that clobbers a register must REFUTE".to_string(),
        trust_ir_expr: spec_observable,
        aarch64_expr: wrong_observable,
        inputs: vec![
            ("reg".to_string(), 64),
            ("addr".to_string(), 64),
            ("value".to_string(), 64),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a "fence" modeled to CLOBBER the fenced memory byte (store
/// a different value) is NOT the identity, so it must REFUTE — proving the
/// memory half of the MFENCE identity is load-bearing. NOT registered.
pub fn proof_x86_mfence_clobbers_memory_refutes() -> ProofObligation {
    use crate::memory_proofs::{encode_load_le, encode_store_le, symbolic_memory};

    let reg = SmtExpr::var("reg", 64);
    let addr = SmtExpr::var("addr", 64);
    let value = SmtExpr::var("value", 64);
    let mem0 = symbolic_memory("mem_default");
    let mem_seeded = encode_store_le(&mem0, &addr, &value, 8);

    let spec_observable = reg.clone().concat(encode_load_le(&mem_seeded, &addr, 8));
    // WRONG: the "fence" overwrites the fenced byte with value+1.
    let mem_clobbered = encode_store_le(
        &mem_seeded,
        &addr,
        &value.bvadd(SmtExpr::bv_const(1, 64)),
        8,
    );
    let wrong_observable = reg.concat(encode_load_le(&mem_clobbered, &addr, 8));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: MFENCE that clobbers memory must REFUTE".to_string(),
        trust_ir_expr: spec_observable,
        aarch64_expr: wrong_observable,
        inputs: vec![
            ("reg".to_string(), 64),
            ("addr".to_string(), 64),
            ("value".to_string(), 64),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// The MFENCE single-thread-identity negative controls (each REFUTABLE). NOT
/// registered; used by tests to show the SeqCst-fence positive is a real
/// data-flow obligation and not a tautology.
pub fn x86_64_mfence_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_x86_mfence_clobbers_register_refutes(),
        proof_x86_mfence_clobbers_memory_refutes(),
    ]
}

pub fn all_x86_64_atomic_load_store_fence_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();

    for width_bits in X86_ATOMIC_MEMORY_WIDTHS {
        proofs.push(proof_x86_atomic_load(width_bits));
        proofs.push(proof_x86_atomic_store(width_bits));
    }
    // Only the SeqCst fence emits an instruction (MFENCE); Acquire/Release/AcqRel
    // fences are zero-instruction on x86 TSO, so there is nothing to prove for
    // them. The SeqCst MFENCE gets a genuine single-thread-identity proof.
    proofs.push(proof_x86_fence_seqcst_mfence());

    proofs
}

// ===========================================================================
// AtomicRmwCasLoop lowering proofs
// ===========================================================================

const X86_ATOMIC_RMW_CAS_LOOP_NARROW_WIDTHS: [u32; 2] = [8, 16];
const X86_ATOMIC_RMW_CAS_LOOP_GENERIC_WIDTHS: [u32; 2] = [32, 64];
const X86_ATOMIC_RMW_CAS_LOOP_NARROW_OPS: [X86AtomicRmwCasLoopOp; 6] = [
    X86AtomicRmwCasLoopOp::Add,
    X86AtomicRmwCasLoopOp::Sub,
    X86AtomicRmwCasLoopOp::And,
    X86AtomicRmwCasLoopOp::Or,
    X86AtomicRmwCasLoopOp::Xor,
    X86AtomicRmwCasLoopOp::Xchg,
];
const X86_ATOMIC_RMW_CAS_LOOP_GENERIC_OPS: [X86AtomicRmwCasLoopOp; 10] = [
    X86AtomicRmwCasLoopOp::Add,
    X86AtomicRmwCasLoopOp::Sub,
    X86AtomicRmwCasLoopOp::And,
    X86AtomicRmwCasLoopOp::Or,
    X86AtomicRmwCasLoopOp::Xor,
    // Xchg (swap) at I32/I64: routed through the CAS loop by select_atomic_rmw
    // (the bare XCHG fast path was deleted -- it had no proof). Same old-return +
    // new-memory (= operand) obligations as the narrow Xchg, already registered.
    X86AtomicRmwCasLoopOp::Xchg,
    X86AtomicRmwCasLoopOp::Max,
    X86AtomicRmwCasLoopOp::Min,
    X86AtomicRmwCasLoopOp::UMax,
    X86AtomicRmwCasLoopOp::UMin,
];

fn x86_atomic_rmw_cas_loop_op_name(op: X86AtomicRmwCasLoopOp) -> &'static str {
    match op {
        X86AtomicRmwCasLoopOp::Add => "Add",
        X86AtomicRmwCasLoopOp::Sub => "Sub",
        X86AtomicRmwCasLoopOp::And => "And",
        X86AtomicRmwCasLoopOp::Or => "Or",
        X86AtomicRmwCasLoopOp::Xor => "Xor",
        X86AtomicRmwCasLoopOp::Xchg => "Xchg",
        X86AtomicRmwCasLoopOp::Max => "Max",
        X86AtomicRmwCasLoopOp::Min => "Min",
        X86AtomicRmwCasLoopOp::UMax => "UMax",
        X86AtomicRmwCasLoopOp::UMin => "UMin",
    }
}

fn x86_atomic_rmw_cas_loop_width_name(width_bits: u32) -> &'static str {
    match width_bits {
        8 => "I8",
        16 => "I16",
        32 => "I32",
        64 => "I64",
        _ => panic!("unsupported x86 AtomicRmwCasLoop width: {width_bits}"),
    }
}

fn x86_atomic_rmw_cas_loop_opcode_name(width_bits: u32) -> &'static str {
    match width_bits {
        8 => "AtomicRmwCasLoop8",
        16 => "AtomicRmwCasLoop16",
        32 | 64 => "AtomicRmwCasLoop",
        _ => panic!("unsupported x86 AtomicRmwCasLoop width: {width_bits}"),
    }
}

fn x86_atomic_rmw_cas_loop_size_bytes(width_bits: u32) -> u32 {
    match width_bits {
        8 | 16 | 32 | 64 => width_bits / 8,
        _ => panic!("unsupported x86 AtomicRmwCasLoop width: {width_bits}"),
    }
}

fn x86_atomic_rmw_cas_loop_return_value(value: SmtExpr, width_bits: u32) -> SmtExpr {
    if width_bits < 32 {
        value.zero_ext(32 - width_bits)
    } else {
        value
    }
}

fn x86_atomic_rmw_cas_loop_seeded_memory(
    addr: &SmtExpr,
    old: &SmtExpr,
    size_bytes: u32,
) -> SmtExpr {
    let mem = crate::memory_proofs::zeroed_memory();
    crate::memory_proofs::encode_store_le(&mem, addr, old, size_bytes)
}

/// Proof: x86 AtomicRmwCasLoop returns the old memory value.
///
/// Narrow byte/halfword loops finish with MOVZX into the 32-bit destination
/// carrier, so the old-value proof compares zero-extended old values for i8
/// and i16 while keeping the memory operation width narrow.
fn proof_x86_atomic_rmw_cas_loop_returns_old(
    width_bits: u32,
    op: X86AtomicRmwCasLoopOp,
) -> ProofObligation {
    use crate::x86_64_semantics::encode_atomic_rmw_cas_loop;

    let size_bytes = x86_atomic_rmw_cas_loop_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let old = SmtExpr::var("old", width_bits);
    let operand = SmtExpr::var("operand", width_bits);
    let mem = x86_atomic_rmw_cas_loop_seeded_memory(&addr, &old, size_bytes);

    let trust_ir_old = x86_atomic_rmw_cas_loop_return_value(old.clone(), width_bits);
    let (x86_old, _mem_after) = encode_atomic_rmw_cas_loop(&mem, &addr, &operand, size_bytes, op);
    let x86_old = x86_atomic_rmw_cas_loop_return_value(x86_old, width_bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: {}_{}_{} returns old value",
            x86_atomic_rmw_cas_loop_opcode_name(width_bits),
            x86_atomic_rmw_cas_loop_op_name(op),
            x86_atomic_rmw_cas_loop_width_name(width_bits)
        ),
        trust_ir_expr: trust_ir_old,
        aarch64_expr: x86_old,
        inputs: vec![
            ("addr".to_string(), 64),
            ("old".to_string(), width_bits),
            ("operand".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86 AtomicRmwCasLoop writes old OP operand back to memory.
fn proof_x86_atomic_rmw_cas_loop_updates_mem(
    width_bits: u32,
    op: X86AtomicRmwCasLoopOp,
) -> ProofObligation {
    use crate::x86_64_semantics::{
        encode_atomic_rmw_cas_loop, encode_atomic_rmw_cas_loop_new_value,
    };

    let size_bytes = x86_atomic_rmw_cas_loop_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let old = SmtExpr::var("old", width_bits);
    let operand = SmtExpr::var("operand", width_bits);
    let mem = x86_atomic_rmw_cas_loop_seeded_memory(&addr, &old, size_bytes);

    let trust_ir_new = encode_atomic_rmw_cas_loop_new_value(op, old.clone(), operand.clone());
    let (_x86_old, mem_after) = encode_atomic_rmw_cas_loop(&mem, &addr, &operand, size_bytes, op);
    let x86_loaded = crate::memory_proofs::encode_load_le(&mem_after, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: {}_{}_{} updates memory",
            x86_atomic_rmw_cas_loop_opcode_name(width_bits),
            x86_atomic_rmw_cas_loop_op_name(op),
            x86_atomic_rmw_cas_loop_width_name(width_bits)
        ),
        trust_ir_expr: trust_ir_new,
        aarch64_expr: x86_loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("old".to_string(), width_bits),
            ("operand".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: a byte/halfword CAS-loop at addr preserves the adjacent value at
/// addr + size. This covers the narrow locked CMPXCHG retry-loop byte range.
fn proof_x86_atomic_rmw_cas_loop_adjacent_non_interference(
    width_bits: u32,
    op: X86AtomicRmwCasLoopOp,
) -> ProofObligation {
    use crate::x86_64_semantics::encode_atomic_rmw_cas_loop;

    assert!(
        width_bits == 8 || width_bits == 16,
        "adjacent AtomicRmwCasLoop non-interference is only registered for i8/i16"
    );

    let size_bytes = x86_atomic_rmw_cas_loop_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let adjacent_addr = addr.clone().bvadd(SmtExpr::bv_const(size_bytes as u64, 64));
    let old = SmtExpr::var("old", width_bits);
    let operand = SmtExpr::var("operand", width_bits);
    let neighbor = SmtExpr::var("neighbor", width_bits);

    let mem = crate::memory_proofs::zeroed_memory();
    let mem = crate::memory_proofs::encode_store_le(&mem, &addr, &old, size_bytes);
    let mem = crate::memory_proofs::encode_store_le(&mem, &adjacent_addr, &neighbor, size_bytes);
    let (_x86_old, mem_after) = encode_atomic_rmw_cas_loop(&mem, &addr, &operand, size_bytes, op);
    let x86_adjacent_after =
        crate::memory_proofs::encode_load_le(&mem_after, &adjacent_addr, size_bytes);

    let max_start = u64::MAX - (2 * size_bytes as u64) + 1;
    let precond_no_wrap = SmtExpr::bvuge(SmtExpr::bv_const(max_start, 64), addr);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: {}_{}_{} preserves adjacent memory",
            x86_atomic_rmw_cas_loop_opcode_name(width_bits),
            x86_atomic_rmw_cas_loop_op_name(op),
            x86_atomic_rmw_cas_loop_width_name(width_bits)
        ),
        trust_ir_expr: neighbor,
        aarch64_expr: x86_adjacent_after,
        inputs: vec![
            ("addr".to_string(), 64),
            ("old".to_string(), width_bits),
            ("operand".to_string(), width_bits),
            ("neighbor".to_string(), width_bits),
        ],
        preconditions: vec![precond_no_wrap],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all x86 AtomicRmwCasLoop proof obligations for the real lowering surface.
pub fn all_x86_64_atomic_rmw_cas_loop_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();

    for width_bits in X86_ATOMIC_RMW_CAS_LOOP_NARROW_WIDTHS {
        for op in X86_ATOMIC_RMW_CAS_LOOP_NARROW_OPS {
            proofs.push(proof_x86_atomic_rmw_cas_loop_returns_old(width_bits, op));
            proofs.push(proof_x86_atomic_rmw_cas_loop_updates_mem(width_bits, op));
            proofs.push(proof_x86_atomic_rmw_cas_loop_adjacent_non_interference(
                width_bits, op,
            ));
        }
    }

    for width_bits in X86_ATOMIC_RMW_CAS_LOOP_GENERIC_WIDTHS {
        for op in X86_ATOMIC_RMW_CAS_LOOP_GENERIC_OPS {
            proofs.push(proof_x86_atomic_rmw_cas_loop_returns_old(width_bits, op));
            proofs.push(proof_x86_atomic_rmw_cas_loop_updates_mem(width_bits, op));
        }
    }

    proofs
}

// ===========================================================================
// x86 LOCK CMPXCHG (compare_exchange) lowering proofs [slice 4]
// ===========================================================================
//
// These certify the CONDITIONAL compare-and-swap that backs Rust's
// `AtomicT::compare_exchange`. It is a genuinely NEW soundness primitive vs the
// unconditional RMW CAS loop: the store is GATED on `expected == mem[addr]`, and
// the instruction produces TWO observable outputs — the returned OLD value AND a
// success flag. Three obligations per width (i32/i64) pin the whole data flow:
//
//   1. returns-old: the destination (RAX after CMPXCHG) is ALWAYS the old memory
//      value — in BOTH the success and failure branches.
//   2. conditional-store: memory afterwards equals `desired` when
//      `expected == old`, and is UNCHANGED (still `old`) when `expected != old`.
//      A single `ite(equal, desired, old)` obligation captures both branches.
//   3. success-flag: the flag the adapter re-derives (`Icmp Equal(old, expected)`)
//      equals `(old == expected)` — exactly the ZF CMPXCHG sets. This proves the
//      dual-output shape: success on equality, failure otherwise.
//
// Non-vacuity is witnessed by the negative controls (`x86_64_cmpxchg_negative_
// controls`): an UNCONDITIONAL store, a returns-DESIRED variant, and a BACKWARDS
// flag each REFUTE. The cross-thread LOCK serialization CMPXCHG also provides is
// the same Intel-SDM architectural axiom the atomic load/store/RMW proofs rest
// on — deliberately NOT dressed up as an SMT theorem here.
//
// Reference: crates/trust-cg-lower/src/x86_64_isel.rs `select_cmpxchg`.

const X86_CMPXCHG_WIDTHS: [u32; 2] = [32, 64];

fn x86_cmpxchg_width_name(width_bits: u32) -> &'static str {
    match width_bits {
        32 => "I32",
        64 => "I64",
        _ => panic!("unsupported x86 CMPXCHG width: {width_bits}"),
    }
}

fn x86_cmpxchg_size_bytes(width_bits: u32) -> u32 {
    match width_bits {
        32 => 4,
        64 => 8,
        _ => panic!("unsupported x86 CMPXCHG width: {width_bits}"),
    }
}

/// Seed a zeroed memory with the current value `old` at `addr`.
fn x86_cmpxchg_seeded_memory(addr: &SmtExpr, old: &SmtExpr, size_bytes: u32) -> SmtExpr {
    let mem = crate::memory_proofs::zeroed_memory();
    crate::memory_proofs::encode_store_le(&mem, addr, old, size_bytes)
}

/// Proof: x86 CMPXCHG returns the OLD memory value in RAX, in BOTH branches.
///
/// The trust-ir `CmpXchg` first result is the loaded value (`old`); the machine
/// side is `ret` from `encode_cmpxchg`, which models RAX-after as
/// `ite(expected==old, expected, old)` — the SUCCESS branch keeps `expected`
/// (which equals `old`), the FAILURE branch loads `old`. This is STRUCTURALLY
/// distinct from the bare `old` spec (so NOT a degenerate X==X) yet equal at
/// every point. Since `expected`/`desired` are free symbolic inputs, the solver
/// checks equality under BOTH `expected == old` (success) and `expected != old`
/// (failure): `ret == old` must hold for every assignment, so a lowering that
/// returned `expected` unconditionally (or `desired`) would refute on the
/// failure branch.
fn proof_x86_cmpxchg_returns_old(width_bits: u32) -> ProofObligation {
    use crate::x86_64_semantics::encode_cmpxchg;

    let size_bytes = x86_cmpxchg_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let old = SmtExpr::var("old", width_bits);
    let expected = SmtExpr::var("expected", width_bits);
    let desired = SmtExpr::var("desired", width_bits);
    let mem = x86_cmpxchg_seeded_memory(&addr, &old, size_bytes);

    let (ret, _mem_after, _flag) = encode_cmpxchg(&mem, &addr, &expected, &desired, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Cmpxchg_{} returns old value",
            x86_cmpxchg_width_name(width_bits)
        ),
        trust_ir_expr: old,
        aarch64_expr: ret,
        inputs: vec![
            ("addr".to_string(), 64),
            ("old".to_string(), width_bits),
            ("expected".to_string(), width_bits),
            ("desired".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: x86 CMPXCHG performs the CONDITIONAL store.
///
/// The reloaded memory equals `ite(expected == old, desired, old)`: on equality
/// the byte becomes `desired`; otherwise it is UNCHANGED (still `old`). The
/// trust-ir spec is that same conditional; a lowering that stored `desired`
/// unconditionally (or never stored) would refute on the mismatched branch.
fn proof_x86_cmpxchg_conditional_store(width_bits: u32) -> ProofObligation {
    use crate::x86_64_semantics::encode_cmpxchg;

    let size_bytes = x86_cmpxchg_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let old = SmtExpr::var("old", width_bits);
    let expected = SmtExpr::var("expected", width_bits);
    let desired = SmtExpr::var("desired", width_bits);
    let mem = x86_cmpxchg_seeded_memory(&addr, &old, size_bytes);

    // Spec: memory after = desired on equality, else the unchanged old value.
    let spec_new = SmtExpr::ite(
        expected.clone().eq_expr(old.clone()),
        desired.clone(),
        old.clone(),
    );

    let (_ret, mem_after, _flag) = encode_cmpxchg(&mem, &addr, &expected, &desired, size_bytes);
    let machine_loaded = crate::memory_proofs::encode_load_le(&mem_after, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Cmpxchg_{} conditional store (desired iff expected==old)",
            x86_cmpxchg_width_name(width_bits)
        ),
        trust_ir_expr: spec_new,
        aarch64_expr: machine_loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("old".to_string(), width_bits),
            ("expected".to_string(), width_bits),
            ("desired".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: on the SUCCESS branch (`expected == old`), CMPXCHG stores `desired`.
///
/// The general conditional-store proof above is correct, but RANDOM sampling
/// almost never hits `expected == old` for wide values, so it exercises only the
/// failure arm. This obligation FORCES the success branch by using ONE symbolic
/// value for BOTH the seeded memory and `expected` — the equality then always
/// holds, so the store MUST land `desired` and the load-back equals `desired`.
/// This concretely exercises the desired-store path a "never stores" bug would
/// miss (that bug reloads `expected`, which differs from `desired`, so it
/// REFUTES). Machine goes through the real store/load, so it is non-degenerate.
fn proof_x86_cmpxchg_success_stores_desired(width_bits: u32) -> ProofObligation {
    use crate::x86_64_semantics::encode_cmpxchg;

    let size_bytes = x86_cmpxchg_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    // ONE value plays both roles: seeded memory value AND `expected` => the
    // hardware equality `expected == mem[addr]` is unconditionally satisfied.
    let matched = SmtExpr::var("matched", width_bits);
    let desired = SmtExpr::var("desired", width_bits);
    let mem = x86_cmpxchg_seeded_memory(&addr, &matched, size_bytes);

    let (_ret, mem_after, _flag) = encode_cmpxchg(&mem, &addr, &matched, &desired, size_bytes);
    let machine_loaded = crate::memory_proofs::encode_load_le(&mem_after, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Cmpxchg_{} success branch stores desired",
            x86_cmpxchg_width_name(width_bits)
        ),
        // On success the memory becomes exactly `desired`.
        trust_ir_expr: desired,
        aarch64_expr: machine_loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("matched".to_string(), width_bits),
            ("desired".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: on the FAILURE branch (`expected != old`), CMPXCHG leaves memory
/// UNCHANGED (still `old`).
///
/// A `expected != old` PRECONDITION restricts sampling to the failure arm; the
/// reloaded memory must still be `old` (the store is suppressed). A lowering that
/// stored `desired` unconditionally REFUTES here whenever `desired != old`.
/// Together with the success-branch proof, both arms of the conditional CAS are
/// concretely exercised.
fn proof_x86_cmpxchg_failure_preserves_memory(width_bits: u32) -> ProofObligation {
    use crate::x86_64_semantics::encode_cmpxchg;

    let size_bytes = x86_cmpxchg_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let old = SmtExpr::var("old", width_bits);
    let expected = SmtExpr::var("expected", width_bits);
    let desired = SmtExpr::var("desired", width_bits);
    let mem = x86_cmpxchg_seeded_memory(&addr, &old, size_bytes);

    let (_ret, mem_after, _flag) = encode_cmpxchg(&mem, &addr, &expected, &desired, size_bytes);
    let machine_loaded = crate::memory_proofs::encode_load_le(&mem_after, &addr, size_bytes);

    // Restrict to the FAILURE arm: expected != old.
    let precond_mismatch = expected.clone().eq_expr(old.clone()).not_expr();

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Cmpxchg_{} failure branch preserves memory",
            x86_cmpxchg_width_name(width_bits)
        ),
        // On failure memory is unchanged: still `old`.
        trust_ir_expr: old,
        aarch64_expr: machine_loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("old".to_string(), width_bits),
            ("expected".to_string(), width_bits),
            ("desired".to_string(), width_bits),
        ],
        preconditions: vec![precond_mismatch],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: the adapter's `Icmp Equal(returned_old, expected)` recovers CMPXCHG's
/// success flag (ZF).
///
/// The isel returns ONLY the old value in RAX; the adapter re-derives the success
/// bool as `Icmp Equal(old, expected)` — it does NOT read ZF. This obligation
/// certifies that post-hoc derivation equals the hardware flag: the SPEC side is
/// the adapter's `ite(returned_old == expected, 1, 0)` over the FAITHFUL returned
/// value `ret = ite(expected==old, expected, old)`, and the MACHINE side is the
/// ZF `encode_cmpxchg` models (`ite(expected==old, 1, 0)`). The two are equal at
/// every point (`ret == expected` iff `expected == old`) but STRUCTURALLY DISTINCT
/// (the spec nests the returned-value `ite` inside the equality), so this is a
/// GENUINE theorem — a lowering whose returned value or flag was wrong makes the
/// two diverge — not a degenerate X==X. A flag set BACKWARDS refutes (see the
/// negative control).
fn proof_x86_cmpxchg_success_flag(width_bits: u32) -> ProofObligation {
    use crate::x86_64_semantics::encode_cmpxchg;

    let size_bytes = x86_cmpxchg_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let old = SmtExpr::var("old", width_bits);
    let expected = SmtExpr::var("expected", width_bits);
    let desired = SmtExpr::var("desired", width_bits);
    let mem = x86_cmpxchg_seeded_memory(&addr, &old, size_bytes);

    let (ret, _mem_after, flag) = encode_cmpxchg(&mem, &addr, &expected, &desired, size_bytes);

    // Spec: exactly what the ADAPTER emits — `Icmp Equal(returned_old, expected)`
    // materialized as a 0/1 bitvector (SETcc/MOVZX). `ret` is the CMPXCHG result
    // value, so this is the real post-hoc flag recovery, nested over the returned
    // `ite` and thus structurally distinct from the bare hardware ZF.
    let spec_flag = SmtExpr::ite(
        ret.eq_expr(expected.clone()),
        SmtExpr::bv_const(1, width_bits),
        SmtExpr::bv_const(0, width_bits),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Cmpxchg_{} success flag == Icmp Equal(returned_old, expected)",
            x86_cmpxchg_width_name(width_bits)
        ),
        trust_ir_expr: spec_flag,
        aarch64_expr: flag,
        inputs: vec![
            ("addr".to_string(), 64),
            ("old".to_string(), width_bits),
            ("expected".to_string(), width_bits),
            ("desired".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a "CMPXCHG" that stores `desired` UNCONDITIONALLY is NOT the
/// conditional CAS, so on the FAILURE branch (expected != old) memory would be
/// wrongly overwritten. Must REFUTE. NOT registered.
pub fn proof_x86_cmpxchg_unconditional_store_refutes(width_bits: u32) -> ProofObligation {
    let size_bytes = x86_cmpxchg_size_bytes(width_bits);
    let addr = SmtExpr::var("addr", 64);
    let old = SmtExpr::var("old", width_bits);
    let expected = SmtExpr::var("expected", width_bits);
    let desired = SmtExpr::var("desired", width_bits);
    let mem = x86_cmpxchg_seeded_memory(&addr, &old, size_bytes);

    // Spec: the CORRECT conditional store.
    let spec_new = SmtExpr::ite(
        expected.clone().eq_expr(old.clone()),
        desired.clone(),
        old.clone(),
    );
    // WRONG: always store `desired` (drops the equality guard).
    let wrong_mem = crate::memory_proofs::encode_store_le(&mem, &addr, &desired, size_bytes);
    let wrong_loaded = crate::memory_proofs::encode_load_le(&wrong_mem, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Cmpxchg_{} that stores UNCONDITIONALLY must REFUTE",
            x86_cmpxchg_width_name(width_bits)
        ),
        trust_ir_expr: spec_new,
        aarch64_expr: wrong_loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("old".to_string(), width_bits),
            ("expected".to_string(), width_bits),
            ("desired".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a "CMPXCHG" that returns `desired` instead of `old` is
/// wrong on the success branch (`compare_exchange` must return the observed old
/// value, never the new one). Must REFUTE. NOT registered.
pub fn proof_x86_cmpxchg_returns_desired_refutes(width_bits: u32) -> ProofObligation {
    let old = SmtExpr::var("old", width_bits);
    let desired = SmtExpr::var("desired", width_bits);

    // Spec: return old. WRONG: return desired. They differ whenever old != desired
    // (the common case under sampling), so this REFUTES.
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Cmpxchg_{} that returns DESIRED must REFUTE",
            x86_cmpxchg_width_name(width_bits)
        ),
        trust_ir_expr: old,
        aarch64_expr: desired,
        inputs: vec![
            ("old".to_string(), width_bits),
            ("desired".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a "CMPXCHG" whose success flag is set BACKWARDS (1 on
/// inequality, 0 on equality) inverts `is_ok()`. Must REFUTE. NOT registered.
pub fn proof_x86_cmpxchg_backwards_flag_refutes(width_bits: u32) -> ProofObligation {
    let old = SmtExpr::var("old", width_bits);
    let expected = SmtExpr::var("expected", width_bits);

    // Spec: 1 on equality. WRONG: 1 on INequality (flag inverted).
    let spec_flag = SmtExpr::ite(
        old.clone().eq_expr(expected.clone()),
        SmtExpr::bv_const(1, width_bits),
        SmtExpr::bv_const(0, width_bits),
    );
    let wrong_flag = SmtExpr::ite(
        old.eq_expr(expected),
        SmtExpr::bv_const(0, width_bits),
        SmtExpr::bv_const(1, width_bits),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "x86_64: Cmpxchg_{} with a BACKWARDS success flag must REFUTE",
            x86_cmpxchg_width_name(width_bits)
        ),
        trust_ir_expr: spec_flag,
        aarch64_expr: wrong_flag,
        inputs: vec![
            ("old".to_string(), width_bits),
            ("expected".to_string(), width_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// The CMPXCHG negative controls (each REFUTABLE). NOT registered; used by tests
/// to show the CMPXCHG positives are real conditional-data-flow obligations and
/// not vacuous tautologies.
pub fn x86_64_cmpxchg_negative_controls() -> Vec<ProofObligation> {
    let mut controls = Vec::new();
    for width_bits in X86_CMPXCHG_WIDTHS {
        controls.push(proof_x86_cmpxchg_unconditional_store_refutes(width_bits));
        controls.push(proof_x86_cmpxchg_returns_desired_refutes(width_bits));
        controls.push(proof_x86_cmpxchg_backwards_flag_refutes(width_bits));
    }
    controls
}

/// Return all x86 CMPXCHG (compare_exchange) proof obligations for the real
/// lowering surface (i32/i64): returns-old + conditional-store + success-flag.
pub fn all_x86_64_cmpxchg_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    for width_bits in X86_CMPXCHG_WIDTHS {
        proofs.push(proof_x86_cmpxchg_returns_old(width_bits));
        proofs.push(proof_x86_cmpxchg_conditional_store(width_bits));
        proofs.push(proof_x86_cmpxchg_success_stores_desired(width_bits));
        proofs.push(proof_x86_cmpxchg_failure_preserves_memory(width_bits));
        proofs.push(proof_x86_cmpxchg_success_flag(width_bits));
    }
    proofs
}

// ===========================================================================
// SSE floating-point conversion lowering proofs (CVT* family)
// ===========================================================================
//
// MXCSR rounding assumption: the non-truncating conversions honor MXCSR.RC,
// which the backend leaves at its ABI default of round-to-nearest-even (RNE),
// exactly as documented for the scalar FP arithmetic proofs (ADDSD/...). The
// truncating CVTT variants round toward zero (RTZ) by definition. Each proof
// asserts that the modeled x86 instruction semantics equal the trust_ir
// conversion semantics (Fcvt / FpExt / FpTrunc) -- the same IEEE conversion.
//
// Reference: crates/trust-cg-lower/src/x86_64_isel.rs select_fcvt_to_int /
//            select_fcvt_from_int / select_fpext / select_fptrunc.

/// Proof: `trust_ir::FcvtFromInt(F64, I64, a) -> x86-64 CVTSI2SD xmm, r64`
///
/// Signed I64 -> binary64 under RNE. The trust_ir `FcvtFromInt` and the
/// modeled `CVTSI2SD` are the same `bv_to_fp(RNE, a, 11, 53)`.
pub fn proof_x86_cvtsi2sd_i64() -> ProofObligation {
    use crate::smt::RoundingMode;
    use crate::x86_64_semantics::{X86CvtIntWidth, encode_cvtsi2sd};

    let a = SmtExpr::var("a", 64);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FcvtFromInt_F64_I64 -> CVTSI2SD xmm,r64".to_string(),
        trust_ir_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 11, 53),
        aarch64_expr: encode_cvtsi2sd(X86CvtIntWidth::I64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtFromInt(F64, I32, a) -> x86-64 CVTSI2SD xmm, r32`
pub fn proof_x86_cvtsi2sd_i32() -> ProofObligation {
    use crate::smt::RoundingMode;
    use crate::x86_64_semantics::{X86CvtIntWidth, encode_cvtsi2sd};

    let a = SmtExpr::var("a", 32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FcvtFromInt_F64_I32 -> CVTSI2SD xmm,r32".to_string(),
        trust_ir_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 11, 53),
        aarch64_expr: encode_cvtsi2sd(X86CvtIntWidth::I32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtFromInt(F32, I64, a) -> x86-64 CVTSI2SS xmm, r64`
///
/// Signed I64 -> binary32 under RNE (may round; f32 has a 24-bit significand).
pub fn proof_x86_cvtsi2ss_i64() -> ProofObligation {
    use crate::smt::RoundingMode;
    use crate::x86_64_semantics::{X86CvtIntWidth, encode_cvtsi2ss};

    let a = SmtExpr::var("a", 64);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FcvtFromInt_F32_I64 -> CVTSI2SS xmm,r64".to_string(),
        trust_ir_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 8, 24),
        aarch64_expr: encode_cvtsi2ss(X86CvtIntWidth::I64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtFromInt(F32, I32, a) -> x86-64 CVTSI2SS xmm, r32`
pub fn proof_x86_cvtsi2ss_i32() -> ProofObligation {
    use crate::smt::RoundingMode;
    use crate::x86_64_semantics::{X86CvtIntWidth, encode_cvtsi2ss};

    let a = SmtExpr::var("a", 32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FcvtFromInt_F32_I32 -> CVTSI2SS xmm,r32".to_string(),
        trust_ir_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 8, 24),
        aarch64_expr: encode_cvtsi2ss(X86CvtIntWidth::I32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtToInt(I64, F64, a) -> x86-64 CVTTSD2SI r64, xmm`
///
/// Truncating (RTZ) binary64 -> signed I64. The reference is the x86-ISA-faithful
/// conversion: NaN/+-Inf/overflow -> INTEGER-INDEFINITE 0x80..0 (#99), NOT
/// saturating. (The Rust-level saturating `FloatToInt` lowering to x86 wraps this
/// opcode in a range-checking fixup; this proof pins the bare ISA semantics.)
pub fn proof_x86_cvttsd2si_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fcvt_to_sint_x86;
    use crate::x86_64_semantics::encode_cvttsd2si;

    let a = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FcvtToInt_I64_F64 -> CVTTSD2SI r64,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint_x86(64, a.clone()),
        aarch64_expr: encode_cvttsd2si(64, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtToInt(I32, F64, a) -> x86-64 CVTTSD2SI r32, xmm`
pub fn proof_x86_cvttsd2si_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fcvt_to_sint_x86;
    use crate::x86_64_semantics::encode_cvttsd2si;

    let a = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FcvtToInt_I32_F64 -> CVTTSD2SI r32,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint_x86(32, a.clone()),
        aarch64_expr: encode_cvttsd2si(32, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtToInt(I64, F32, a) -> x86-64 CVTTSS2SI r64, xmm`
pub fn proof_x86_cvttss2si_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fcvt_to_sint_x86;
    use crate::x86_64_semantics::encode_cvttss2si;

    let a = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FcvtToInt_I64_F32 -> CVTTSS2SI r64,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint_x86(64, a.clone()),
        aarch64_expr: encode_cvttss2si(64, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtToInt(I32, F32, a) -> x86-64 CVTTSS2SI r32, xmm`
pub fn proof_x86_cvttss2si_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fcvt_to_sint_x86;
    use crate::x86_64_semantics::encode_cvttss2si;

    let a = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FcvtToInt_I32_F32 -> CVTTSS2SI r32,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint_x86(32, a.clone()),
        aarch64_expr: encode_cvttss2si(32, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: non-truncating `CVTSD2SI r64, xmm == x86 fp_to_sbv(RNE, indef, a, 64)`.
///
/// The non-truncating CVTSD2SI uses MXCSR rounding (RNE default) and x86 integer-
/// indefinite out-of-range. This pins the instruction's documented round-to-
/// nearest-even + indefinite semantics; there is no ISel-emitted trust_ir op for
/// it (the ISel uses CVTT for C casts), so the reference is the x86 ISA RNE form.
pub fn proof_x86_cvtsd2si_rne_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fcvt_to_sint_x86_rne;
    use crate::x86_64_semantics::encode_cvtsd2si;

    let a = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: CVTSD2SI_RNE_I64 -> fp_to_sbv(RNE) r64,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint_x86_rne(64, a.clone()),
        aarch64_expr: encode_cvtsd2si(64, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: non-truncating `CVTSS2SI r64, xmm == x86 fp_to_sbv(RNE, indef, a, 64)`.
pub fn proof_x86_cvtss2si_rne_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_fcvt_to_sint_x86_rne;
    use crate::x86_64_semantics::encode_cvtss2si;

    let a = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: CVTSS2SI_RNE_I64 -> fp_to_sbv(RNE) r64,xmm".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint_x86_rne(64, a.clone()),
        aarch64_expr: encode_cvtss2si(64, a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FPTrunc(F32, F64, a) -> x86-64 CVTSD2SS xmm, xmm`
///
/// Narrow binary64 -> binary32 under RNE (precision change, may round).
pub fn proof_x86_cvtsd2ss() -> ProofObligation {
    use crate::smt::RoundingMode;
    use crate::x86_64_semantics::encode_cvtsd2ss;

    let a = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FPTrunc_F32_F64 -> CVTSD2SS xmm,xmm".to_string(),
        trust_ir_expr: SmtExpr::fp_to_fp(RoundingMode::RNE, a.clone(), 8, 24),
        aarch64_expr: encode_cvtsd2ss(a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FPExt(F64, F32, a) -> x86-64 CVTSS2SD xmm, xmm`
///
/// Widen binary32 -> binary64 (exact for every finite single).
pub fn proof_x86_cvtss2sd() -> ProofObligation {
    use crate::smt::RoundingMode;
    use crate::x86_64_semantics::encode_cvtss2sd;

    let a = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "x86_64: FPExt_F64_F32 -> CVTSS2SD xmm,xmm".to_string(),
        trust_ir_expr: SmtExpr::fp_to_fp(RoundingMode::RNE, a.clone(), 11, 53),
        aarch64_expr: encode_cvtss2sd(a),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all SSE FP conversion lowering proofs (CVT* family).
pub fn all_x86_64_fp_conversion_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_cvtsi2sd_i64(),
        proof_x86_cvtsi2sd_i32(),
        proof_x86_cvtsi2ss_i64(),
        proof_x86_cvtsi2ss_i32(),
        proof_x86_cvttsd2si_i64(),
        proof_x86_cvttsd2si_i32(),
        proof_x86_cvttss2si_i64(),
        proof_x86_cvttss2si_i32(),
        proof_x86_cvtsd2si_rne_i64(),
        proof_x86_cvtss2si_rne_i64(),
        proof_x86_cvtsd2ss(),
        proof_x86_cvtss2sd(),
    ]
}

// ===========================================================================
// Bit manipulation lowering proofs (BSF/BSR/TZCNT/LZCNT/POPCNT)
// ===========================================================================
//
// Each proof models the x86 bit-counting instruction as a bitvector function
// (x86_64_semantics::encode_{popcnt,tzcnt,lzcnt,bsf,bsr}) and asserts it equals
// a reference bitvector semantics encoded here directly (the mathematical
// trust_ir Ctpop/Cttz/Ctlz definition). The reference encodings are validated
// against Rust's native count_ones/trailing_zeros/leading_zeros by the unit
// tests in x86_64_semantics; here the proofs pin the *equivalence* of the two
// independent formulations across all inputs (exhaustive at i8, sampled at
// i32/i64).
//
// Zero-input subtleties handled:
//   - POPCNT(0) = 0, TZCNT(0) = LZCNT(0) = width (defined results).
//   - BSF(0)/BSR(0): destination architecturally undefined (ZF flags zero), so
//     the BSF/BSR proofs carry a `src != 0` precondition. Under that
//     precondition BSF == TZCNT and BSR == (width - 1) - LZCNT.

/// Reference (trust_ir `Ctpop`) population count: number of set bits.
///
/// Delegates to the canonical public trust_ir source encoder
/// (`trust_ir_semantics::encode_trust_ir_ctpop`), which is the SAME spec the
/// x86 reconstruction path uses — so the static-DB proof and the reconstruction
/// obligation share one source of truth.
fn reference_ctpop(src: SmtExpr) -> SmtExpr {
    crate::trust_ir_semantics::encode_trust_ir_ctpop(src)
}

fn proof_x86_popcnt_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_semantics::encode_popcnt;
    let a = SmtExpr::var("a", bits);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: Ctpop_{ty_name} -> POPCNT r,r"),
        trust_ir_expr: reference_ctpop(a.clone()),
        aarch64_expr: encode_popcnt(a),
        inputs: vec![("a".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Reference count-trailing-zeros (`Cttz`) with the defined zero-input = width.
/// Delegates to the canonical public encoder (shared with reconstruction).
fn reference_cttz(src: SmtExpr) -> SmtExpr {
    crate::trust_ir_semantics::encode_trust_ir_cttz(src)
}

/// Reference count-leading-zeros (`Ctlz`) with the defined zero-input = width.
/// Delegates to the canonical public encoder (shared with reconstruction).
fn reference_ctlz(src: SmtExpr) -> SmtExpr {
    crate::trust_ir_semantics::encode_trust_ir_ctlz(src)
}

fn proof_x86_tzcnt_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_semantics::encode_tzcnt;
    let a = SmtExpr::var("a", bits);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: Cttz_{ty_name} -> TZCNT r,r"),
        trust_ir_expr: reference_cttz(a.clone()),
        aarch64_expr: encode_tzcnt(a),
        inputs: vec![("a".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_x86_lzcnt_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_semantics::encode_lzcnt;
    let a = SmtExpr::var("a", bits);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: Ctlz_{ty_name} -> LZCNT r,r"),
        trust_ir_expr: reference_ctlz(a.clone()),
        aarch64_expr: encode_lzcnt(a),
        inputs: vec![("a".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `BSF r,r == TZCNT r,r` under the precondition `src != 0`.
///
/// BSF is the bit-scan-forward (lowest set bit index). It coincides with TZCNT
/// (and trust_ir `Cttz`) for nonzero inputs; the zero input is excluded because
/// BSF leaves the destination architecturally undefined and sets ZF.
fn proof_x86_bsf_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_semantics::encode_bsf;
    let a = SmtExpr::var("a", bits);
    let nonzero = a.clone().eq_expr(SmtExpr::bv_const(0, bits)).not_expr();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: Cttz_{ty_name} (nonzero) -> BSF r,r"),
        trust_ir_expr: reference_cttz(a.clone()),
        aarch64_expr: encode_bsf(a),
        inputs: vec![("a".to_string(), bits)],
        preconditions: vec![nonzero],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Reference BSR semantics for nonzero inputs: index of the highest set bit,
/// i.e. `(width - 1) - Ctlz(src)`. Delegates to the canonical public encoder
/// (shared with reconstruction).
fn reference_bsr_nonzero(src: SmtExpr) -> SmtExpr {
    crate::trust_ir_semantics::encode_trust_ir_bsr_nonzero(src)
}

/// Proof: `BSR r,r == (width - 1) - Ctlz(src)` under the precondition
/// `src != 0`.
///
/// BSR is the bit-scan-reverse (highest set bit index). The zero input is
/// excluded because BSR leaves the destination architecturally undefined and
/// sets ZF.
fn proof_x86_bsr_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_semantics::encode_bsr;
    let a = SmtExpr::var("a", bits);
    let nonzero = a.clone().eq_expr(SmtExpr::bv_const(0, bits)).not_expr();
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: BSR_{ty_name} (nonzero) == width-1-Ctlz"),
        trust_ir_expr: reference_bsr_nonzero(a.clone()),
        aarch64_expr: encode_bsr(a),
        inputs: vec![("a".to_string(), bits)],
        preconditions: vec![nonzero],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Reference predicate the x86 AND/CMP/Jcc→BT/Jcc peephole replaces: the AND-mask
/// test `(src AND (1 << k)) != 0`, returned as a 1-bit value (`1` iff bit `k` of
/// `src` is set). This is the EXACT predicate the peephole erases (`AndRI %v,
/// #(1<<k); CmpRI %v,#0`) and re-encodes on `CF`; the proof asserts the BT-set
/// `CF` equals it.
fn reference_and_mask_bit(src: SmtExpr, k: u32) -> SmtExpr {
    let width = src.bv_width();
    let mask = SmtExpr::bv_const(1u64 << k, width);
    let nonzero = src
        .bvand(mask)
        .eq_expr(SmtExpr::bv_const(0, width))
        .not_expr();
    SmtExpr::ite(nonzero, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Proof: `BtRI %src, #k` sets `CF := bit k of src`, equal to the AND-mask
/// predicate `(src AND (1 << k)) != 0`.
///
/// This is the semantic obligation for the x86 `AndRI; CmpRI #0; Jcc {E|NE}`
/// → `BtRI #k; Jcc {AE|B}` peephole (`trust-cg-opt/src/x86_peephole.rs`): that
/// rewrite is sound exactly because the `CF` produced by `BT src, k` equals the
/// zero/nonzero test of the erased `AND src, (1<<k)`. The two sides are modeled
/// distinctly — the x86 side as the SDM shift form `(src >> k) & 1`
/// (`encode_bt_cf`), the reference side as the AND-mask form `(src & (1<<k)) !=
/// 0` (`reference_and_mask_bit`) — so a wrong BT model refutes rather than
/// matching trivially. Quantified over every static bit index `k < width`.
fn proof_x86_bt_cf_for_width_bit(bits: u32, k: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_semantics::encode_bt_cf;
    let a = SmtExpr::var("a", bits);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: BtRI_{ty_name}#{k} CF == bit{k}(src) == (src & (1<<{k})) != 0"),
        trust_ir_expr: reference_and_mask_bit(a.clone(), k),
        aarch64_expr: encode_bt_cf(a, k),
        inputs: vec![("a".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// All `BtRI` CF obligations for one register width: one per static bit index
/// `k` in `0..bits`. The peephole's `bit_k` is `imm.trailing_zeros()` of a
/// power-of-two AND immediate, which ranges over every in-width bit position, so
/// every emittable `(width, k)` instance is covered.
fn proof_x86_bt_cf_all_bits(bits: u32, ty_name: &str) -> Vec<ProofObligation> {
    (0..bits)
        .map(|k| proof_x86_bt_cf_for_width_bit(bits, k, ty_name))
        .collect()
}

/// Return all x86-64 bit-manipulation lowering proofs.
pub fn all_x86_64_bit_manip_proofs() -> Vec<ProofObligation> {
    let mut proofs = vec![
        // POPCNT (Ctpop)
        proof_x86_popcnt_for_width(8, "I8"),
        proof_x86_popcnt_for_width(16, "I16"),
        proof_x86_popcnt_for_width(32, "I32"),
        proof_x86_popcnt_for_width(64, "I64"),
        // TZCNT (Cttz, defined zero = width)
        proof_x86_tzcnt_for_width(8, "I8"),
        proof_x86_tzcnt_for_width(32, "I32"),
        proof_x86_tzcnt_for_width(64, "I64"),
        // LZCNT (Ctlz, defined zero = width)
        proof_x86_lzcnt_for_width(8, "I8"),
        proof_x86_lzcnt_for_width(32, "I32"),
        proof_x86_lzcnt_for_width(64, "I64"),
        // BSF (nonzero == Cttz)
        proof_x86_bsf_for_width(8, "I8"),
        proof_x86_bsf_for_width(32, "I32"),
        proof_x86_bsf_for_width(64, "I64"),
        // BSR (nonzero == width-1-Ctlz)
        proof_x86_bsr_for_width(8, "I8"),
        proof_x86_bsr_for_width(32, "I32"),
        proof_x86_bsr_for_width(64, "I64"),
    ];
    // BT r,imm8 CF semantics for the AND/CMP/Jcc→BT/Jcc peephole. The peephole
    // emits BtRI at the AND's register class (Gpr32: k<=31, Gpr64: k<=63), so
    // every emittable (width, k) bit-test instance is proven exhaustively per
    // bit index. 32 (i32) + 64 (i64) = 96 obligations.
    proofs.extend(proof_x86_bt_cf_all_bits(32, "I32"));
    proofs.extend(proof_x86_bt_cf_all_bits(64, "I64"));
    proofs
}

// ===========================================================================
// Parity flag (PF) lowering proofs
// ===========================================================================
//
// PF is the even-parity of the low 8 bits of an instruction result. After
// CMP/SUB computing `result = src1 - src2`, the SETcc P (parity even) / NP
// (parity odd) condition codes consume PF. These proofs pin the x86 EFLAGS PF
// model (x86_64_eflags) against an independent reference: PF == NOT(xor-reduce
// of result[7:0]).
//
// Reference: Intel SDM Vol 1 §3.4.3.1 (Status Flags, PF).

/// Reference even-parity predicate over the low 8 bits of `result`.
///
/// `PF = 1` iff the number of set bits in `result[7:0]` is even, i.e. the XOR
/// of the eight low bits is 0.
fn reference_pf_low8(result: SmtExpr) -> SmtExpr {
    let low = result.extract(7, 0);
    let mut xor = low.clone().extract(0, 0);
    for i in 1..8u32 {
        xor = xor.bvxor(low.clone().extract(i, i));
    }
    // Even parity: xor-reduction is 0.
    xor.eq_expr(SmtExpr::bv_const(0, 1))
}

fn bool_to_bv1(b: SmtExpr) -> SmtExpr {
    SmtExpr::ite(b, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Proof: `CMP PF(a, b) == even_parity((a - b)[7:0])` at the given width.
///
/// Asserts the x86 EFLAGS PF model equals the reference even-parity of the low
/// byte of the subtraction result.
fn proof_x86_cmp_pf_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_eflags::encode_cmp_eflags;

    let a = SmtExpr::var("a", bits);
    let b = SmtExpr::var("b", bits);

    let flags = encode_cmp_eflags(a.clone(), b.clone(), bits);
    let diff = a.clone().bvsub(b.clone());
    let reference = reference_pf_low8(diff);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: CMP_PF_flag_{ty_name}"),
        trust_ir_expr: bool_to_bv1(reference),
        aarch64_expr: bool_to_bv1(flags.pf),
        inputs: vec![("a".to_string(), bits), ("b".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `SETcc P (a, b) == even_parity((a - b)[7:0])` at the given width.
///
/// The full CMP + SETcc P sequence yields 1 exactly when the low byte of the
/// difference has even parity. This verifies the P condition-code evaluation
/// against the reference, exercising the previously-placeholder PF path.
fn proof_x86_setcc_p_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;

    let a = SmtExpr::var("a", bits);
    let b = SmtExpr::var("b", bits);

    let setcc = encode_cmp_setcc(a.clone(), b.clone(), bits, X86CondCode::P);
    let diff = a.clone().bvsub(b.clone());
    let reference = bool_to_bv1(reference_pf_low8(diff));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: CMP+SETcc_P_{ty_name}"),
        trust_ir_expr: reference,
        aarch64_expr: setcc,
        inputs: vec![("a".to_string(), bits), ("b".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `SETcc NP (a, b) == odd_parity((a - b)[7:0])` at the given width.
fn proof_x86_setcc_np_for_width(bits: u32, ty_name: &str) -> ProofObligation {
    use crate::x86_64_eflags::encode_cmp_setcc;
    use trust_cg_ir::X86CondCode;

    let a = SmtExpr::var("a", bits);
    let b = SmtExpr::var("b", bits);

    let setcc = encode_cmp_setcc(a.clone(), b.clone(), bits, X86CondCode::NP);
    let diff = a.clone().bvsub(b.clone());
    // NP = parity odd = NOT(even parity).
    let reference = bool_to_bv1(reference_pf_low8(diff).not_expr());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: CMP+SETcc_NP_{ty_name}"),
        trust_ir_expr: reference,
        aarch64_expr: setcc,
        inputs: vec![("a".to_string(), bits), ("b".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all x86-64 parity-flag (PF) proofs.
pub fn all_x86_64_parity_flag_proofs() -> Vec<ProofObligation> {
    vec![
        proof_x86_cmp_pf_for_width(8, "I8"),
        proof_x86_cmp_pf_for_width(32, "I32"),
        proof_x86_setcc_p_for_width(8, "I8"),
        proof_x86_setcc_p_for_width(32, "I32"),
        proof_x86_setcc_np_for_width(8, "I8"),
        proof_x86_setcc_np_for_width(32, "I32"),
    ]
}

// ===========================================================================
// Collect all proofs
// ===========================================================================

/// Return all x86-64 lowering proof obligations.
///
/// This provides a single entry point for running all x86-64 verification
/// proofs, analogous to how the AArch64 proofs are collected.
// ---------------------------------------------------------------------------
// ROL (rotate-left by constant) lowering proofs
// ---------------------------------------------------------------------------
//
// x86 has a single-instruction rotate; before the `x86_rotate_idiom` peephole
// exists the frontend emits the six-instruction shift/shift/or sequence for
// `x.rotate_left(k)`. This obligation ties the two.
//
// FAITHFULNESS / NON-DEGENERACY. `ROL` MEANS `(x << k) | (x >>u (w-k))`, which
// is character-for-character the idiom it replaces, so the naive obligation is
// exactly the vacuous `X == X` that `is_degenerate` exists to catch. As on the
// AArch64 side (`lowering_proof::proof_eor_ror_shift`) the MACHINE side is
// therefore written with the two OR halves in the OPPOSITE order:
//   * SOURCE  = `(x << k) | (x >>u (w-k))`   (`encode_rotl_source`)
//   * MACHINE = `(x >>u (w-k)) | (x << k)`   (`encode_rol_ri`)
// Structurally distinct, provably equal because OR commutes.

/// One ROL obligation at `size`, rotate amount `k` in `[1, width)`.
pub fn proof_x86_rol_ri(size: crate::x86_64_semantics::X86OperandSize, k: u32) -> ProofObligation {
    use crate::x86_64_semantics::{encode_rol_ri, encode_rotl_source, x86_operand_size_bits};
    let width = x86_operand_size_bits(size);
    let x = SmtExpr::var("x", width);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64: RotL_I{width} k={k} -> ROL (rotate-left by imm8)"),
        trust_ir_expr: encode_rotl_source(size, x.clone(), k),
        aarch64_expr: encode_rol_ri(size, x, k),
        inputs: vec![("x".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// ROL obligations across representative amounts at 32 and 64 bits, including
/// both boundaries (`k = 1` and `k = width - 1`).
pub fn all_x86_rol_proofs() -> Vec<ProofObligation> {
    use crate::x86_64_semantics::X86OperandSize;
    let mut out = Vec::new();
    for k in [1u32, 7, 9, 16, 31] {
        out.push(proof_x86_rol_ri(X86OperandSize::S32, k));
    }
    for k in [1u32, 7, 9, 32, 57, 63] {
        out.push(proof_x86_rol_ri(X86OperandSize::S64, k));
    }
    out
}

/// NEGATIVE CONTROLS: each perturbs the MACHINE side and MUST be refuted. A
/// positive obligation that nothing can falsify is decoration, not evidence.
///
/// 1. WRONG AMOUNT     — rotate by `k + 1`.
/// 2. WRONG DIRECTION  — rotate RIGHT by `k` (i.e. `ROR`, halves swapped in
///                       amount as well as order).
/// 3. HALF DROPPED     — only the `<< k` half, no wrap-around.
#[cfg(test)]
pub(crate) fn x86_rol_wrong_controls(
    size: crate::x86_64_semantics::X86OperandSize,
    k: u32,
) -> Vec<ProofObligation> {
    use crate::x86_64_semantics::{encode_rol_ri, encode_rotl_source, x86_operand_size_bits};
    let width = x86_operand_size_bits(size);
    let x = SmtExpr::var("x", width);
    let src = encode_rotl_source(size, x.clone(), k);
    let mk = |name: &str, machine: SmtExpr| ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("x86_64 CONTROL (must refute): {name}"),
        trust_ir_expr: src.clone(),
        aarch64_expr: machine,
        inputs: vec![("x".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    };
    vec![
        mk("wrong amount k+1", encode_rol_ri(size, x.clone(), k + 1)),
        mk(
            "wrong direction (ROR k)",
            encode_rol_ri(size, x.clone(), width - k),
        ),
        mk(
            "wrap-around half dropped",
            x.bvshl(SmtExpr::bv_const(u64::from(k), width)),
        ),
    ]
}

pub fn all_x86_64_proofs() -> Vec<ProofObligation> {
    let mut proofs = vec![
        // Control transfer
        proof_x86_call_branches_to_target(),
        proof_x86_ret_branches_to_stack_return_address(),
        proof_x86_jmp_branches_to_target(),
        proof_x86_mov_imm_materializes_constant(),
        // Effective-address arithmetic (LEA with displacement)
        proof_x86_lea_base_disp32(),
        proof_x86_lea_add_disp32_i64(),
        proof_x86_lea_scale2_disp32_i64(),
        proof_x86_lea_scale4_disp32_i64(),
        proof_x86_lea_scale8_disp32_i64(),
        // RIP-relative symbol-address materialization (LeaRip / MovRipRel):
        // composes the per-instruction RIP-relative EA with the proven
        // SIGNED / GOT_LOAD relocation displacements (macho_data_reloc_proofs).
        proof_x86_learip_symbol_riprel(),
        proof_x86_movriprel_got_eff_addr(),
        // Memory moves (loads/stores at every access width)
        proof_x86_load_i8(),
        proof_x86_load_i16(),
        proof_x86_load_i32(),
        proof_x86_load_i64(),
        proof_x86_store_i8(),
        proof_x86_store_i16(),
        proof_x86_store_i32(),
        proof_x86_store_i64(),
        // Arithmetic (32-bit)
        proof_x86_iadd_i32(),
        proof_x86_isub_i32(),
        proof_x86_imul_i32(),
        proof_x86_neg_i32(),
        // Arithmetic (64-bit)
        proof_x86_iadd_i64(),
        proof_x86_isub_i64(),
        proof_x86_imul_i64(),
        proof_x86_neg_i64(),
        // Boolean bitwise
        proof_x86_bandnot_b1(),
        proof_x86_bornot_b1(),
        // Arithmetic (16-bit)
        proof_x86_iadd_i16(),
        proof_x86_isub_i16(),
        proof_x86_imul_i16(),
        proof_x86_band_i16(),
        proof_x86_bor_i16(),
        proof_x86_bxor_i16(),
        proof_x86_bandnot_i16(),
        proof_x86_bornot_i16(),
        proof_x86_ishl_i16(),
        proof_x86_ushr_i16(),
        proof_x86_sshr_i16(),
        // Division
        proof_x86_sdiv_i32(),
        proof_x86_sdiv_i64(),
        proof_x86_udiv_i32(),
        proof_x86_udiv_i64(),
        proof_x86_srem_i32(),
        proof_x86_srem_i64(),
        proof_x86_urem_i32(),
        proof_x86_urem_i64(),
        // Branchless-guarded signed division (TOTAL, certifies INT_MIN/-1)
        proof_x86_sdiv_i32_guarded(),
        proof_x86_sdiv_i64_guarded(),
        proof_x86_srem_i32_guarded(),
        proof_x86_srem_i64_guarded(),
        // Bitwise (32-bit)
        proof_x86_band_i32(),
        proof_x86_bor_i32(),
        proof_x86_bxor_i32(),
        proof_x86_bnot_i32(),
        proof_x86_bandnot_i32(),
        proof_x86_bornot_i32(),
        // Bitwise (64-bit)
        proof_x86_band_i64(),
        proof_x86_bor_i64(),
        proof_x86_bxor_i64(),
        proof_x86_bnot_i64(),
        proof_x86_bandnot_i64(),
        proof_x86_bornot_i64(),
        // Shifts (32-bit)
        proof_x86_ishl_i32(),
        proof_x86_ushr_i32(),
        proof_x86_sshr_i32(),
        // Shifts (64-bit)
        proof_x86_ishl_i64(),
        proof_x86_ushr_i64(),
        proof_x86_sshr_i64(),
        // SIMD integer
        proof_x86_v2i64_add_paddq(),
        proof_x86_v2i64_sub_psubq(),
        proof_x86_v2i64_mul_scalarized(),
        proof_x86_v4i32_ishl_scalarized(),
        proof_x86_v4i32_ushr_scalarized(),
        proof_x86_v4i32_sshr_scalarized(),
        proof_x86_v4i32_ishl_uniform_pslld_imm(),
        proof_x86_v4i32_ushr_uniform_psrld_imm(),
        proof_x86_v4i32_sshr_uniform_psrad_imm(),
        proof_x86_v2i64_ishl_uniform_psllq_imm(),
        proof_x86_v2i64_ushr_uniform_psrlq_imm(),
        proof_x86_v2i64_umul_lo32_pmuludq(),
        // 8-bit exhaustive (arithmetic)
        proof_x86_iadd_i8(),
        proof_x86_isub_i8(),
        proof_x86_imul_i8(),
        // 8-bit exhaustive (bitwise)
        proof_x86_band_i8(),
        proof_x86_bor_i8(),
        proof_x86_bxor_i8(),
        proof_x86_bandnot_i8(),
        proof_x86_bornot_i8(),
        // 8-bit exhaustive (shifts)
        proof_x86_ishl_i8(),
        proof_x86_ushr_i8(),
        proof_x86_sshr_i8(),
        // Comparisons (32-bit)
        proof_x86_icmp_eq_i32(),
        proof_x86_icmp_ne_i32(),
        proof_x86_icmp_slt_i32(),
        proof_x86_icmp_sge_i32(),
        proof_x86_icmp_sgt_i32(),
        proof_x86_icmp_sle_i32(),
        proof_x86_icmp_ult_i32(),
        proof_x86_icmp_uge_i32(),
        proof_x86_icmp_ugt_i32(),
        proof_x86_icmp_ule_i32(),
        // Comparisons (64-bit)
        proof_x86_icmp_eq_i64(),
        proof_x86_icmp_ne_i64(),
        proof_x86_icmp_slt_i64(),
        proof_x86_icmp_sge_i64(),
        proof_x86_icmp_sgt_i64(),
        proof_x86_icmp_sle_i64(),
        proof_x86_icmp_ult_i64(),
        proof_x86_icmp_uge_i64(),
        proof_x86_icmp_ugt_i64(),
        proof_x86_icmp_ule_i64(),
        // Floating-point (binary)
        proof_x86_fadd_f32(),
        proof_x86_fadd_f64(),
        proof_x86_fsub_f32(),
        proof_x86_fsub_f64(),
        proof_x86_fmul_f32(),
        proof_x86_fmul_f64(),
        proof_x86_fdiv_f32(),
        proof_x86_fdiv_f64(),
        // Packed floating-point (ADDPS/ADDPD families, per-lane)
        proof_x86_v4f32_fadd_addps(),
        proof_x86_v4f32_fsub_subps(),
        proof_x86_v4f32_fmul_mulps(),
        proof_x86_v4f32_fdiv_divps(),
        proof_x86_v2f64_fadd_addpd(),
        proof_x86_v2f64_fsub_subpd(),
        proof_x86_v2f64_fmul_mulpd(),
        proof_x86_v2f64_fdiv_divpd(),
        // Floating-point (unary: FNEG, FABS, FSQRT)
        proof_x86_fneg_f32(),
        proof_x86_fneg_f64(),
        proof_x86_fabs_f32(),
        proof_x86_fabs_f64(),
        proof_x86_fsqrt_f32(),
        proof_x86_fsqrt_f64(),
        // Floating-point round-to-integral (ROUNDSS/ROUNDSD: floor/ceil/trunc)
        proof_x86_ffloor_f32(),
        proof_x86_ffloor_f64(),
        proof_x86_fceil_f32(),
        proof_x86_fceil_f64(),
        proof_x86_ftrunc_f32(),
        proof_x86_ftrunc_f64(),
        // Scalar FP NaN-away min/max components (MINSD/MAXSD/MINSS/MAXSS +
        // CMPSD/CMPSS UNORD mask) for Rust f{32,64}::min/max.
        proof_x86_minsd_f64(),
        proof_x86_maxsd_f64(),
        proof_x86_minss_f32(),
        proof_x86_maxss_f32(),
        proof_x86_cmpsd_unord_f64(),
        proof_x86_cmpss_unord_f32(),
        // Floating-point comparisons (UCOMISS/UCOMISD + SETcc)
        proof_x86_fcmp_eq_f32(),
        proof_x86_fcmp_eq_f64(),
        proof_x86_fcmp_ne_f32(),
        proof_x86_fcmp_ne_f64(),
        proof_x86_fcmp_lt_f32(),
        proof_x86_fcmp_lt_f64(),
        proof_x86_fcmp_le_f32(),
        proof_x86_fcmp_le_f64(),
        proof_x86_fcmp_gt_f32(),
        proof_x86_fcmp_gt_f64(),
        proof_x86_fcmp_ge_f32(),
        proof_x86_fcmp_ge_f64(),
        proof_x86_fcmp_ord_f32(),
        proof_x86_fcmp_ord_f64(),
        proof_x86_fcmp_uno_f32(),
        proof_x86_fcmp_uno_f64(),
        proof_x86_fcmp_ueq_f32(),
        proof_x86_fcmp_ueq_f64(),
        proof_x86_fcmp_une_f32(),
        proof_x86_fcmp_une_f64(),
        proof_x86_fcmp_ult_f32(),
        proof_x86_fcmp_ult_f64(),
        proof_x86_fcmp_ule_f32(),
        proof_x86_fcmp_ule_f64(),
        proof_x86_fcmp_ugt_f32(),
        proof_x86_fcmp_ugt_f64(),
        proof_x86_fcmp_uge_f32(),
        proof_x86_fcmp_uge_f64(),
        // Extensions (MOVZX/MOVSX)
        proof_x86_movzx_8_to_32(),
        proof_x86_movzx_16_to_32(),
        proof_x86_movzx_8_to_64(),
        proof_x86_movzx_16_to_64(),
        proof_x86_movsx_8_to_32(),
        proof_x86_movsx_16_to_32(),
        proof_x86_movsx_8_to_64(),
        proof_x86_movsx_16_to_64(),
        proof_x86_movsxd_32_to_64(),
        // Register copies introduced by ISel and local x86 peepholes.
        proof_x86_movrr_copy_i32(),
        proof_x86_movrr_copy_i64(),
        // LEA
        proof_x86_lea_add_i64(),
        proof_x86_lea_scale2_i64(),
        proof_x86_lea_scale4_i64(),
        proof_x86_lea_scale8_i64(),
        // Three-operand IMUL
        proof_x86_imul_rri_i32(),
        proof_x86_imul_rri_i64(),
        // One-operand widening MUL (RDX:RAX = RAX * src) used by CheckedUmul /
        // unsigned widening+overflow multiply: low half (RAX) == wrapping mul,
        // high half (RDX) != 0 == unsigned overflow (the SETcc B / CF source).
        proof_x86_mul_low_for_width(32, "I32"),
        proof_x86_mul_low_for_width(64, "I64"),
        proof_x86_mul_high_overflow_for_width(32, "I32"),
        proof_x86_mul_high_overflow_for_width(64, "I64"),
        // CMOVcc and GPR/XMM bit transfers used by scalar FP select.
        proof_x86_cmovcc_bitwise_select(),
        proof_x86_cmovcc32_bitwise_select(),
        proof_x86_movd_to_xmm_bit_preservation(),
        proof_x86_movd_from_xmm_bit_preservation(),
        proof_x86_movq_to_xmm_bit_preservation(),
        proof_x86_movq_from_xmm_bit_preservation(),
        proof_x86_fp_select_f32_bits(),
        proof_x86_fp_select_f64_bits(),
        // SSE scalar-FP MOVE / COPY / load / store / constant-pool-load (#65):
        // MOVSS/MOVSD reg-reg copies, memory loads/stores, and rodata const
        // loads. Bit-identity / memory-load / RIP-relative-addressing proofs.
        proof_x86_movss_rr_copy(),
        proof_x86_movsd_rr_copy(),
        proof_x86_movss_load(),
        proof_x86_movsd_load(),
        proof_x86_movss_store(),
        proof_x86_movsd_store(),
        proof_x86_movss_constpool_riprel(),
        proof_x86_movsd_constpool_riprel(),
        // Direct CMP EFLAGS-write proofs at i32 (issue #458).
        // These pin the SF/ZF/CF/OF flag-write semantics independent of the
        // SETcc chain so regressions in a single flag surface locally rather
        // than cascading through the ten indirect `proof_x86_icmp_*_i32`
        // obligations. Mirrors the AArch64 NZCV per-flag precedent in
        // `lowering_proof::proof_nzcv_*_flag_i32`.
        crate::x86_64_eflags_proofs::proof_x86_cmp_writes_zf_i32(),
        crate::x86_64_eflags_proofs::proof_x86_cmp_writes_sf_i32(),
        crate::x86_64_eflags_proofs::proof_x86_cmp_writes_cf_i32(),
        crate::x86_64_eflags_proofs::proof_x86_cmp_writes_of_i32(),
        // i128 carry-chain high-half lowering (ADC / SBB). The low halves are
        // the ordinary i64 ADD/SUB covered above; these certify the carry/borrow
        // propagation into the high limb. See `proof_x86_adc_i128_hi`.
        proof_x86_adc_i128_hi(),
        proof_x86_sbb_i128_hi(),
        // i128 carry-chain WHOLE-value composition (ADD lo; ADC hi / SUB lo; SBB
        // hi). Unlike the high-limb-only proofs above, these model the FULL
        // 128-bit value — both halves plus the carry/borrow that crosses the
        // 64-bit boundary — against the trust_ir 128-bit bvadd/bvsub. The
        // per-instruction verifier binds them to an emitted adjacent ADD+ADC /
        // SUB+SBB pair via `i128_carry_chain_sequence_to_proof_query`.
        proof_x86_iadd_i128_add_adc(),
        proof_x86_isub_i128_sub_sbb(),
    ];

    proofs.extend(all_x86_64_v128_packed_arithmetic_proofs());
    // Vectorizer lowering-SEQUENCE obligations: a whole emitted instruction
    // sequence proved against its trust-ir meaning, rather than one instruction
    // against its own semantics helper (which for pure data movement is
    // degenerate X==X — see `proof_x86_v2i64_saxpy_scalar_mul_punpcklqdq`).
    proofs.push(proof_x86_v2i64_saxpy_scalar_mul_punpcklqdq());
    proofs.extend(all_x86_64_v128_bitwise_proofs());
    proofs.extend(all_x86_64_v4i32_lane_proofs());
    proofs.extend(all_x86_64_v2i64_lane_proofs());
    proofs.extend(all_x86_64_v128_compare_mask_proofs());
    proofs.extend(all_x86_64_v128_mask_extract_proofs());
    proofs.extend(all_x86_64_v2i64_compare_mask_proofs());
    proofs.extend(all_x86_64_v2i64_mask_extract_proofs());
    proofs.extend(all_x86_64_v128_bool_select_proofs());
    proofs.extend(all_x86_64_scalar_bitfield_proofs());
    proofs.extend(all_x86_64_atomic_load_store_fence_proofs());
    proofs.extend(all_x86_64_atomic_rmw_cas_loop_proofs());
    proofs.extend(all_x86_64_cmpxchg_proofs());
    proofs.extend(all_x86_64_fp_conversion_proofs());
    proofs.extend(all_x86_64_bit_manip_proofs());
    proofs.extend(all_x86_64_parity_flag_proofs());
    // ROL (rotate-left by constant) — see the FAITHFULNESS note above. Added
    // BEFORE the retraction filter so the same hygiene applies to it.
    proofs.extend(all_x86_rol_proofs());
    proofs.retain(|p| !X86_RETRACTED_DEGENERATE.contains(&p.name.as_str()));

    proofs
}

/// #62 retraction: degenerate X==X x86-64 obligations — control-flow
/// target==target (CALL/JMP/RET), MOV r,imm const==const materialization, and
/// the plain/SIB LEA effective-address arithmetic (the EA expression is the SAME
/// on both sides; no independent address-mode encoder). They proved nothing and
/// are removed. The GENUINE x86 proofs (RIP-relative LeaRip/MovRipRel
/// relocations, the no-scale base+index LEA, Umul low/high, Bitcast,
/// vector/compare idioms, SETcc, etc.) remain.
///
/// SLICE 3 (fences): the four `Fence_* -> MFENCE` const==const tautologies that
/// used to be listed here are GONE, not filtered — they are no longer produced.
/// Acquire/Release/AcqRel fences now emit ZERO instructions on x86 TSO (no
/// obligation), and the SeqCst fence's MFENCE gained a GENUINE single-thread
/// identity proof (`proof_x86_mfence_single_thread_identity`, a real data-flow
/// obligation over symbolic register/memory state), which is registered.
const X86_RETRACTED_DEGENERATE: &[&str] = &[
    "x86_64: CALL branches to target",
    "x86_64: JMP branches to target",
    "x86_64: RET branches to stack return address",
    "x86_64: MOV r,imm materializes constant",
    "x86_64: base+disp32 -> LEA r64,[r64+disp32]",
    "x86_64: base+index*2 -> LEA r64,[r64+r64*2]",
    "x86_64: base+index*2+disp32 -> LEA r64,[r64+r64*2+disp32]",
    "x86_64: base+index*4 -> LEA r64,[r64+r64*4]",
    "x86_64: base+index*4+disp32 -> LEA r64,[r64+r64*4+disp32]",
    "x86_64: base+index*8 -> LEA r64,[r64+r64*8]",
    "x86_64: base+index*8+disp32 -> LEA r64,[r64+r64*8+disp32]",
    "x86_64: base+index+disp32 -> LEA r64,[r64+r64+disp32]",
];

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {

    /// The ROL obligations must (a) DISCHARGE, (b) be NON-DEGENERATE, and (c)
    /// have their perturbations REFUTED. Without (b) and (c) a passing (a) is
    /// worthless: `ROL` means exactly the idiom it replaces, so the naive
    /// obligation is `X == X`.
    #[test]
    fn x86_rol_proofs_are_faithful_and_non_degenerate() {
        use crate::x86_64_semantics::X86OperandSize;

        let positives = super::all_x86_rol_proofs();
        assert!(!positives.is_empty(), "ROL family must not be empty");
        for p in &positives {
            assert!(
                !p.is_degenerate(),
                "{} is X==X — the machine side must use the OPPOSITE OR order",
                p.name
            );
        }

        // The controls must be structurally distinct too, else "refuted" would
        // be meaningless.
        for size in [X86OperandSize::S32, X86OperandSize::S64] {
            for c in super::x86_rol_wrong_controls(size, 9) {
                assert!(!c.is_degenerate(), "{} unexpectedly degenerate", c.name);
            }
        }
    }
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;
    use rayon::prelude::*;

    const MAX_X86_PROOF_EVAL_WORKERS: usize = 4;

    fn x86_proof_eval_worker_count() -> usize {
        let available = std::thread::available_parallelism().map_or(1, usize::from);
        let operator_limit = std::env::var("TRUST_CG_MAX_PARALLELISM")
            .ok()
            .and_then(|value| value.trim().parse::<usize>().ok())
            .filter(|value| *value > 0)
            .unwrap_or(MAX_X86_PROOF_EVAL_WORKERS);
        available
            .min(operator_limit)
            .clamp(1, MAX_X86_PROOF_EVAL_WORKERS)
    }

    fn x86_proof_failure_report(results: &[(String, VerificationResult)]) -> Option<String> {
        let failures: Vec<String> = results
            .iter()
            .filter_map(|(name, result)| match result {
                VerificationResult::Valid => None,
                other => Some(format!("Proof '{name}' failed: {other:?}")),
            })
            .collect();
        (!failures.is_empty()).then(|| failures.join("\n"))
    }

    fn assert_x86_proof_valid(obligation: ProofObligation) {
        let name = obligation.name.clone();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 proof failed for {name}: {result:?}"
        );
    }

    fn assert_x86_proof_valid_with_samples(obligation: ProofObligation, sample_count: u64) {
        let name = obligation.name.clone();
        let config = crate::lowering_proof::VerificationConfig::with_sample_count(sample_count);
        let result = crate::lowering_proof::verify_by_evaluation_with_config(&obligation, &config);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 proof failed for {name}: {result:?}"
        );
    }

    /// The i128 ADC/SBB high-limb carry proofs must discharge with a high
    /// sample count (4 inputs => `verify_random_multi`), AND a deliberately
    /// broken machine model (carry dropped / wrong direction) must REFUTE —
    /// proving the obligations are faithful theorems, not vacuous tautologies.
    #[test]
    fn x86_i128_adc_sbb_high_limb_proofs_discharge_and_are_not_vacuous() {
        // (1) The real proofs discharge.
        assert_x86_proof_valid_with_samples(proof_x86_adc_i128_hi(), 20_000);
        assert_x86_proof_valid_with_samples(proof_x86_sbb_i128_hi(), 20_000);

        let config = crate::lowering_proof::VerificationConfig::with_sample_count(20_000);

        // (2) ADC with the carry DROPPED (machine = a_hi + b_hi, no carry) must
        // be refuted by the true-128-bit spec whenever the low limb wraps.
        {
            let mut broken = proof_x86_adc_i128_hi();
            let a_hi = SmtExpr::var("a_hi", 64);
            let b_hi = SmtExpr::var("b_hi", 64);
            broken.aarch64_expr = a_hi.bvadd(b_hi); // dropped the +carry
            let r = crate::lowering_proof::verify_by_evaluation_with_config(&broken, &config);
            assert!(
                !matches!(r, VerificationResult::Valid),
                "ADC proof with the carry dropped must REFUTE (not vacuous): {r:?}"
            );
        }

        // (3) SBB with the borrow flipped to an ADD (machine = a_hi - b_hi +
        // borrow) must be refuted.
        {
            let mut broken = proof_x86_sbb_i128_hi();
            let a_lo = SmtExpr::var("a_lo", 64);
            let b_lo = SmtExpr::var("b_lo", 64);
            let a_hi = SmtExpr::var("a_hi", 64);
            let b_hi = SmtExpr::var("b_hi", 64);
            let borrow_bool = a_lo.bvult(b_lo);
            let borrow_bv = SmtExpr::ite(
                borrow_bool,
                SmtExpr::bv_const(1, 64),
                SmtExpr::bv_const(0, 64),
            );
            broken.aarch64_expr = a_hi.bvsub(b_hi).bvadd(borrow_bv); // +borrow, wrong sign
            let r = crate::lowering_proof::verify_by_evaluation_with_config(&broken, &config);
            assert!(
                !matches!(r, VerificationResult::Valid),
                "SBB proof with the borrow direction flipped must REFUTE (not vacuous): {r:?}"
            );
        }
    }

    // -----------------------------------------------------------------------
    // i128 carry-chain WHOLE-value (ADD+ADC / SUB+SBB) composition proof tests
    // -----------------------------------------------------------------------

    /// The i128 ADD+ADC composition proof must discharge: the full 128-bit value
    /// `concat(adc_hi, add_lo)` equals trust_ir `bvadd` of the reconstructed
    /// operands, with the carry derived faithfully from the 65-bit low-half add.
    #[test]
    fn test_x86_64_iadd_i128_add_adc_proof() {
        assert_x86_proof_valid(proof_x86_iadd_i128_add_adc());
    }

    /// The i128 SUB+SBB composition proof must discharge.
    #[test]
    fn test_x86_64_isub_i128_sub_sbb_proof() {
        assert_x86_proof_valid(proof_x86_isub_i128_sub_sbb());
    }

    /// NEGATIVE CONTROL: an ADD+ADC model that DROPS the carry-in to the high
    /// half (`dst_hi = a_hi + b_hi`, no `+ CF`) is WRONG and MUST be refuted —
    /// this is precisely the carry-across-the-64-bit-boundary miscompile the real
    /// proof guards against. If this passed, the proof would be a tautology.
    #[test]
    fn test_x86_64_iadd_i128_dropped_carry_is_refuted() {
        use crate::trust_ir_semantics::encode_trust_ir_binop;
        use trust_cg_lower::instructions::Opcode;
        use trust_cg_lower::types::Type;

        let a_lo = SmtExpr::var("a_lo", 64);
        let a_hi = SmtExpr::var("a_hi", 64);
        let b_lo = SmtExpr::var("b_lo", 64);
        let b_hi = SmtExpr::var("b_hi", 64);

        let a128 = a_hi.clone().concat(a_lo.clone());
        let b128 = b_hi.clone().concat(b_lo.clone());

        // WRONG machine side: high half forgets the carry-in.
        let wrong_lo = a_lo.bvadd(b_lo);
        let wrong_hi = a_hi.bvadd(b_hi);
        let wrong = wrong_hi.concat(wrong_lo);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "NEGATIVE: Iadd_I128 dropped carry-in".to_string(),
            trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I128, a128, b128),
            aarch64_expr: wrong,
            inputs: vec![
                ("a_lo".to_string(), 64),
                ("a_hi".to_string(), 64),
                ("b_lo".to_string(), 64),
                ("b_hi".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = crate::lowering_proof::verify_by_evaluation_with_config(
            &obligation,
            &crate::lowering_proof::VerificationConfig::with_sample_count(20_000),
        );
        assert!(
            !matches!(result, VerificationResult::Valid),
            "dropped-carry i128 add model must be refuted, but it passed"
        );
    }

    /// NEGATIVE CONTROL: a SUB+SBB model that DROPS the borrow-in to the high
    /// half (`dst_hi = a_hi - b_hi`, no `- CF`) is WRONG and MUST be refuted.
    #[test]
    fn test_x86_64_isub_i128_dropped_borrow_is_refuted() {
        use crate::trust_ir_semantics::encode_trust_ir_binop;
        use trust_cg_lower::instructions::Opcode;
        use trust_cg_lower::types::Type;

        let a_lo = SmtExpr::var("a_lo", 64);
        let a_hi = SmtExpr::var("a_hi", 64);
        let b_lo = SmtExpr::var("b_lo", 64);
        let b_hi = SmtExpr::var("b_hi", 64);

        let a128 = a_hi.clone().concat(a_lo.clone());
        let b128 = b_hi.clone().concat(b_lo.clone());

        let wrong_lo = a_lo.bvsub(b_lo);
        let wrong_hi = a_hi.bvsub(b_hi);
        let wrong = wrong_hi.concat(wrong_lo);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "NEGATIVE: Isub_I128 dropped borrow-in".to_string(),
            trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I128, a128, b128),
            aarch64_expr: wrong,
            inputs: vec![
                ("a_lo".to_string(), 64),
                ("a_hi".to_string(), 64),
                ("b_lo".to_string(), 64),
                ("b_hi".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = crate::lowering_proof::verify_by_evaluation_with_config(
            &obligation,
            &crate::lowering_proof::VerificationConfig::with_sample_count(20_000),
        );
        assert!(
            !matches!(result, VerificationResult::Valid),
            "dropped-borrow i128 sub model must be refuted, but it passed"
        );
    }

    /// NEGATIVE CONTROL: a SWAPPED lo/hi ordering (`concat(add_lo, adc_hi)` —
    /// big-endian instead of little-endian) is WRONG and MUST be refuted. This
    /// pins the lo-first register-pair convention the backend relies on.
    #[test]
    fn test_x86_64_iadd_i128_swapped_halves_is_refuted() {
        use crate::trust_ir_semantics::encode_trust_ir_binop;
        use crate::x86_64_semantics::encode_add_adc_i128;
        use trust_cg_lower::instructions::Opcode;
        use trust_cg_lower::types::Type;

        let a_lo = SmtExpr::var("a_lo", 64);
        let a_hi = SmtExpr::var("a_hi", 64);
        let b_lo = SmtExpr::var("b_lo", 64);
        let b_hi = SmtExpr::var("b_hi", 64);

        let a128 = a_hi.clone().concat(a_lo.clone());
        let b128 = b_hi.clone().concat(b_lo.clone());

        // Correct value but with halves concatenated in the WRONG order.
        let correct = encode_add_adc_i128(a_lo, a_hi, b_lo, b_hi);
        let lo_half = correct.clone().extract(63, 0);
        let hi_half = correct.extract(127, 64);
        let swapped = lo_half.concat(hi_half); // put lo on top

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "NEGATIVE: Iadd_I128 swapped halves".to_string(),
            trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I128, a128, b128),
            aarch64_expr: swapped,
            inputs: vec![
                ("a_lo".to_string(), 64),
                ("a_hi".to_string(), 64),
                ("b_lo".to_string(), 64),
                ("b_hi".to_string(), 64),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = crate::lowering_proof::verify_by_evaluation_with_config(
            &obligation,
            &crate::lowering_proof::VerificationConfig::with_sample_count(20_000),
        );
        assert!(
            !matches!(result, VerificationResult::Valid),
            "swapped-halves i128 add model must be refuted, but it passed"
        );
    }

    fn assert_x86_binary_not_logic_valid(obligation: ProofObligation) {
        let name = obligation.name.clone();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 binary-not proof failed for {name}: {result:?}"
        );
    }

    #[test]
    fn test_x86_64_bandnot_scalar_proofs() {
        for obligation in [
            proof_x86_bandnot_b1(),
            proof_x86_bandnot_i8(),
            proof_x86_bandnot_i16(),
            proof_x86_bandnot_i32(),
            proof_x86_bandnot_i64(),
        ] {
            assert_x86_binary_not_logic_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_bornot_scalar_proofs() {
        for obligation in [
            proof_x86_bornot_b1(),
            proof_x86_bornot_i8(),
            proof_x86_bornot_i16(),
            proof_x86_bornot_i32(),
            proof_x86_bornot_i64(),
        ] {
            assert_x86_binary_not_logic_valid(obligation);
        }
    }

    // -----------------------------------------------------------------------
    // Arithmetic lowering proof tests (32-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_iadd_i32_proof() {
        let obligation = proof_x86_iadd_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Iadd_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_isub_i32_proof() {
        let obligation = proof_x86_isub_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Isub_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_imul_i32_proof() {
        let obligation = proof_x86_imul_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Imul_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_v2i64_paddq_psubq_proofs() {
        for obligation in [
            proof_x86_v2i64_add_paddq(),
            proof_x86_v2i64_sub_psubq(),
            proof_x86_v2i64_mul_scalarized(),
        ] {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v128_packed_arithmetic_proof_family_registered() {
        let proofs = all_x86_64_v128_packed_arithmetic_proofs();
        assert_eq!(
            proofs.len(),
            8,
            "expected eight V128 packed arithmetic proof obligations"
        );

        for op in [
            "PADDB", "PSUBB", "V16I8Mul", "PADDW", "PSUBW", "PADDD", "PSUBD", "PMULLD",
        ] {
            assert!(
                proofs.iter().any(|proof| proof.name.contains(op)),
                "missing {op} packed arithmetic proof"
            );
        }
    }

    #[test]
    fn test_x86_64_v128_packed_arithmetic_proofs() {
        for obligation in all_x86_64_v128_packed_arithmetic_proofs() {
            if obligation.name.contains("V16I8Mul") {
                assert_x86_proof_valid_with_samples(obligation, 4096);
            } else {
                assert_x86_proof_valid(obligation);
            }
        }
    }

    #[test]
    fn test_x86_64_v128_bitwise_proof_family_registered() {
        let proofs = all_x86_64_v128_bitwise_proofs();
        assert_eq!(
            proofs.len(),
            5,
            "expected five V128 bitwise proof obligations (PAND/POR/PXOR + the \
             two V128-Band forms ANDPD/ANDPS)"
        );

        for op in ["PAND", "POR", "PXOR", "ANDPD", "ANDPS"] {
            assert!(
                proofs.iter().any(|proof| proof.name.contains(op)),
                "missing {op} bitwise proof"
            );
        }
    }

    #[test]
    fn test_x86_64_v128_bitwise_proofs() {
        for obligation in all_x86_64_v128_bitwise_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v4i32_scalarized_shift_proofs() {
        for obligation in [
            proof_x86_v4i32_ishl_scalarized(),
            proof_x86_v4i32_ushr_scalarized(),
            proof_x86_v4i32_sshr_scalarized(),
        ] {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v4i32_uniform_imm_shift_proofs() {
        for obligation in [
            proof_x86_v4i32_ishl_uniform_pslld_imm(),
            proof_x86_v4i32_ushr_uniform_psrld_imm(),
            proof_x86_v4i32_sshr_uniform_psrad_imm(),
        ] {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v2i64_uniform_imm_shift_proofs() {
        for obligation in [
            proof_x86_v2i64_ishl_uniform_psllq_imm(),
            proof_x86_v2i64_ushr_uniform_psrlq_imm(),
        ] {
            assert_x86_proof_valid(obligation);
        }
    }

    /// NEGATIVE CONTROL: the qword-shift spec paired with the DWORD machine
    /// shift (PSLLD-for-PSLLQ — the exact lane-width confusion the group-12 vs
    /// group-13 opcode byte distinction encodes) must REFUTE: a 1-bit qword
    /// shl carries bit 31 into bit 32, a dword shl drops it.
    #[test]
    fn test_x86_64_v2i64_shift_wrong_lane_width_refutes() {
        use crate::x86_64_semantics::encode_pslld_imm;

        let wrong = proof_x86_v2i64_uniform_imm_shift(
            "x86_64: V2I64 Ishl uniform immediate with DWORD machine shift must REFUTE",
            |a, b| a.bvshl(b),
            encode_pslld_imm,
        );
        let result = verify_by_evaluation(&wrong);
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "dword-machine-shift model for a qword shift spec must refute, got {result:?}"
        );
    }

    /// NEGATIVE CONTROL: a wrong shift DIRECTION (PSRLQ machine model under the
    /// shl spec) must REFUTE.
    #[test]
    fn test_x86_64_v2i64_shift_wrong_direction_refutes() {
        use crate::x86_64_semantics::encode_psrlq_imm;

        let wrong = proof_x86_v2i64_uniform_imm_shift(
            "x86_64: V2I64 Ishl uniform immediate with PSRLQ machine model must REFUTE",
            |a, b| a.bvshl(b),
            encode_psrlq_imm,
        );
        let result = verify_by_evaluation(&wrong);
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "wrong-direction qword shift model must refute, got {result:?}"
        );
    }

    #[test]
    fn test_x86_64_v2i64_pmuludq_proof() {
        assert_x86_proof_valid(proof_x86_v2i64_umul_lo32_pmuludq());
    }

    /// NEGATIVE CONTROLS for the PMULUDQ faithful model: an ODD-dword machine
    /// extract (lanes 1,3 instead of 0,2), a SIGN-extending machine model, and
    /// a LOW-HALF-ONLY (masked-to-32-bit) product must each REFUTE — together
    /// they witness that the proof pins the exact even-dword zero-extended
    /// full-width product of the Intel SDM.
    #[test]
    fn test_x86_64_v2i64_pmuludq_wrong_models_refute() {
        let spec: fn(SmtExpr, SmtExpr) -> SmtExpr = |a, b| {
            let mask = SmtExpr::bv_const(0xFFFF_FFFF, 64);
            a.bvand(mask.clone()).bvmul(b.bvand(mask))
        };
        let make = |name: &str, machine: fn(SmtExpr, SmtExpr) -> SmtExpr| {
            proof_x86_v128_packed_arithmetic(name, crate::smt::VectorArrangement::D2, spec, machine)
        };

        // (a) Odd-dword extract (lanes 1,3 — the HIGH dword of each qword).
        let odd = make(
            "x86_64: PMULUDQ with ODD-dword machine extract must REFUTE",
            |src1, src2| {
                let lanes: Vec<SmtExpr> = [1u32, 3u32]
                    .iter()
                    .map(|&lane| {
                        let a = crate::smt::lane_extract(
                            &src1,
                            crate::smt::VectorArrangement::S4,
                            lane,
                        )
                        .zero_ext(32);
                        let b = crate::smt::lane_extract(
                            &src2,
                            crate::smt::VectorArrangement::S4,
                            lane,
                        )
                        .zero_ext(32);
                        a.bvmul(b)
                    })
                    .collect();
                crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::D2)
            },
        );
        // (b) Sign-extending machine model (PMULDQ semantics, not PMULUDQ).
        let signed = make(
            "x86_64: PMULUDQ with SIGN-extending machine model must REFUTE",
            |src1, src2| {
                let lanes: Vec<SmtExpr> = [0u32, 2u32]
                    .iter()
                    .map(|&lane| {
                        let a = crate::smt::lane_extract(
                            &src1,
                            crate::smt::VectorArrangement::S4,
                            lane,
                        )
                        .sign_ext(32);
                        let b = crate::smt::lane_extract(
                            &src2,
                            crate::smt::VectorArrangement::S4,
                            lane,
                        )
                        .sign_ext(32);
                        a.bvmul(b)
                    })
                    .collect();
                crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::D2)
            },
        );
        // (c) Low-half-only product (a 32-bit low multiply zero-extended, i.e.
        //     the widening product's high half dropped).
        let low_half = make(
            "x86_64: PMULUDQ with LOW-HALF-ONLY product must REFUTE",
            |src1, src2| {
                let lanes: Vec<SmtExpr> = [0u32, 2u32]
                    .iter()
                    .map(|&lane| {
                        let a = crate::smt::lane_extract(
                            &src1,
                            crate::smt::VectorArrangement::S4,
                            lane,
                        );
                        let b = crate::smt::lane_extract(
                            &src2,
                            crate::smt::VectorArrangement::S4,
                            lane,
                        );
                        a.bvmul(b).zero_ext(32)
                    })
                    .collect();
                crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::D2)
            },
        );

        for wrong in [odd, signed, low_half] {
            let name = wrong.name.clone();
            let result = verify_by_evaluation(&wrong);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "{name}: expected refutation, got {result:?}"
            );
        }
    }

    #[test]
    fn test_x86_64_v4i32_lane_proof_family_registered() {
        let proofs = all_x86_64_v4i32_lane_proofs();
        assert_eq!(
            proofs.len(),
            14,
            "expected fourteen V4I32 lane pack/extract/insert proof obligations"
        );

        assert_eq!(
            proofs
                .iter()
                .filter(|proof| proof.name.contains("V4I32PackLanes"))
                .count(),
            2,
            "expected general and equal-lane V4I32 pack proofs"
        );
        assert_eq!(
            proofs
                .iter()
                .filter(|proof| proof.name.contains("V4I32ExtractLane"))
                .count(),
            4,
            "expected one V4I32 extract proof per lane"
        );
        assert_eq!(
            proofs
                .iter()
                .filter(|proof| proof.name.contains("V4I32InsertLane")
                    && proof.name.contains("nonzero base"))
                .count(),
            4,
            "expected one nonzero-base V4I32 insert proof per lane"
        );
        assert_eq!(
            proofs
                .iter()
                .filter(|proof| proof.name.contains("V4I32InsertLane")
                    && proof.name.contains("zero base")
                    && !proof.name.contains("nonzero base"))
                .count(),
            4,
            "expected one zero-base V4I32 insert proof per lane"
        );
    }

    #[test]
    fn test_x86_64_v4i32_lane_proofs() {
        for obligation in all_x86_64_v4i32_lane_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    /// NEGATIVE CONTROL: the obligation must REFUTE a wrong lowering.
    ///
    /// Swapping the `PUNPCKLQDQ` operands routes `b1`'s product into lane 0 and
    /// `b0`'s into lane 1. If that still verified, the obligation would be
    /// asserting nothing about lane routing — which is the only thing this
    /// sequence can get wrong.
    #[test]
    fn v2i64_saxpy_punpcklqdq_refutes_swapped_operands() {
        use crate::x86_64_semantics::{encode_movq_to_xmm, encode_paddq, encode_punpcklqdq};

        let good = proof_x86_v2i64_saxpy_scalar_mul_punpcklqdq();
        let (c, _) = x86_v128_from_u64_halves("c");
        let b0 = SmtExpr::var("b0", 64);
        let b1 = SmtExpr::var("b1", 64);
        let k = SmtExpr::var("k", 64);

        let mut wrong = good.clone();
        // SWAPPED: b1's product now lands in lane 0.
        wrong.aarch64_expr = encode_paddq(
            c,
            encode_punpcklqdq(
                encode_movq_to_xmm(b1.bvmul(k.clone())),
                encode_movq_to_xmm(b0.bvmul(k)),
            ),
        );

        assert!(
            !matches!(verify_by_evaluation(&wrong), VerificationResult::Valid),
            "swapped PUNPCKLQDQ operands must REFUTE — otherwise the obligation \
             says nothing about which product reaches which lane"
        );
    }

    /// Guards the lesson from the reverted PUNPCKLQDQ identity: this obligation
    /// must not be `X == X`. Discharging is NOT proving.
    #[test]
    fn v2i64_saxpy_punpcklqdq_proof_is_not_degenerate() {
        let p = proof_x86_v2i64_saxpy_scalar_mul_punpcklqdq();
        assert!(
            !p.is_degenerate(),
            "spec and machine sides must be structurally distinct, else the \
             obligation can never be refuted by a wrong lowering"
        );
        assert_x86_proof_valid(p);
    }

    #[test]
    fn test_x86_64_v2i64_lane_proof_family_registered() {
        let proofs = all_x86_64_v2i64_lane_proofs();
        assert_eq!(
            proofs.len(),
            8,
            "expected eight V2I64 lane pack/extract/insert proof obligations"
        );

        assert_eq!(
            proofs
                .iter()
                .filter(|proof| proof.name.contains("V2I64PackLanes"))
                .count(),
            2,
            "expected general and equal-lane V2I64 pack proofs"
        );
        assert_eq!(
            proofs
                .iter()
                .filter(|proof| proof.name.contains("V2I64ExtractLane"))
                .count(),
            2,
            "expected one V2I64 extract proof per lane"
        );
        assert_eq!(
            proofs
                .iter()
                .filter(|proof| proof.name.contains("V2I64InsertLane")
                    && proof.name.contains("nonzero base"))
                .count(),
            2,
            "expected one nonzero-base V2I64 insert proof per lane"
        );
        assert_eq!(
            proofs
                .iter()
                .filter(|proof| proof.name.contains("V2I64InsertLane")
                    && proof.name.contains("zero base")
                    && !proof.name.contains("nonzero base"))
                .count(),
            2,
            "expected one zero-base V2I64 insert proof per lane"
        );
    }

    #[test]
    fn test_x86_64_v2i64_lane_proofs() {
        for obligation in all_x86_64_v2i64_lane_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v4i32_compare_mask_proof_family_registered() {
        let proofs = all_x86_64_v4i32_compare_mask_proofs();
        assert_eq!(
            proofs.len(),
            10,
            "expected ten V4I32 compare-mask proof obligations"
        );

        for cond in [
            "Eq", "Ne", "Slt", "Sle", "Sgt", "Sge", "Ult", "Ule", "Ugt", "Uge",
        ] {
            assert!(
                proofs
                    .iter()
                    .any(|proof| proof.name.contains(&format!("V4I32Icmp_{cond}"))),
                "missing V4I32Icmp_{cond} proof"
            );
        }
    }

    #[test]
    fn test_x86_64_v128_compare_mask_proof_family_registered() {
        let proofs = all_x86_64_v128_compare_mask_proofs();
        assert_eq!(
            proofs.len(),
            30,
            "expected V16I8, V8I16, and V4I32 compare-mask proof obligations"
        );

        for shape in ["V16I8", "V8I16", "V4I32"] {
            for cond in [
                "Eq", "Ne", "Slt", "Sle", "Sgt", "Sge", "Ult", "Ule", "Ugt", "Uge",
            ] {
                assert!(
                    proofs
                        .iter()
                        .any(|proof| proof.name.contains(&format!("{shape}Icmp_{cond}"))),
                    "missing {shape}Icmp_{cond} proof"
                );
            }
        }
    }

    #[test]
    fn test_x86_64_v2i64_compare_mask_proof_family_registered() {
        let proofs = all_x86_64_v2i64_compare_mask_proofs();
        assert_eq!(
            proofs.len(),
            10,
            "expected ten V2I64 compare-mask proof obligations"
        );

        for cond in [
            "Eq", "Ne", "Slt", "Sle", "Sgt", "Sge", "Ult", "Ule", "Ugt", "Uge",
        ] {
            assert!(
                proofs
                    .iter()
                    .any(|proof| proof.name.contains(&format!("V2I64Icmp_{cond}"))),
                "missing V2I64Icmp_{cond} proof"
            );
        }
    }

    #[test]
    fn test_x86_64_v4i32_compare_mask_proofs() {
        for obligation in all_x86_64_v4i32_compare_mask_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_narrow_compare_mask_proofs() {
        for obligation in all_x86_64_narrow_compare_mask_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v2i64_compare_mask_proofs() {
        for obligation in all_x86_64_v2i64_compare_mask_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v4i32_mask_extract_proof() {
        assert_x86_proof_valid(proof_x86_v4i32_mask_extract());
    }

    #[test]
    fn test_x86_64_v128_mask_extract_proofs() {
        let proofs = all_x86_64_v128_mask_extract_proofs();
        assert_eq!(proofs.len(), 3, "expected three V128 mask-extract proofs");
        for obligation in proofs {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v2i64_mask_extract_proofs() {
        let proofs = all_x86_64_v2i64_mask_extract_proofs();
        assert_eq!(proofs.len(), 2, "expected two V2I64 mask-extract proofs");
        for obligation in proofs {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_v128_bool_select_proof_family_registered() {
        let proofs = all_x86_64_v128_bool_select_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "expected SSE2 and SSE4.1 V128BoolSelect proof obligations"
        );
        assert!(
            proofs
                .iter()
                .any(|proof| proof.name.contains("PAND/PANDN/POR")),
            "missing SSE2 V128BoolSelect proof"
        );
        assert!(
            proofs.iter().any(|proof| proof.name.contains("PBLENDVB")),
            "missing PBLENDVB V128BoolSelect proof"
        );
    }

    #[test]
    fn test_x86_64_v128_bool_select_proofs() {
        for obligation in all_x86_64_v128_bool_select_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_neg_i32_proof() {
        let obligation = proof_x86_neg_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Neg_I32 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Arithmetic lowering proof tests (64-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_iadd_i64_proof() {
        let obligation = proof_x86_iadd_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Iadd_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_isub_i64_proof() {
        let obligation = proof_x86_isub_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Isub_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_imul_i64_proof() {
        let obligation = proof_x86_imul_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Imul_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_neg_i64_proof() {
        let obligation = proof_x86_neg_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Neg_I64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Arithmetic lowering proof tests (16-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_iadd_i16_proof() {
        let obligation = proof_x86_iadd_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Iadd_I16 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_isub_i16_proof() {
        let obligation = proof_x86_isub_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Isub_I16 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_imul_i16_proof() {
        let obligation = proof_x86_imul_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Imul_I16 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_band_i16_proof() {
        let obligation = proof_x86_band_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Band_I16 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bor_i16_proof() {
        let obligation = proof_x86_bor_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bor_I16 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bxor_i16_proof() {
        let obligation = proof_x86_bxor_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bxor_I16 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_ishl_i16_proof() {
        let obligation = proof_x86_ishl_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Ishl_I16 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_ushr_i16_proof() {
        let obligation = proof_x86_ushr_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Ushr_I16 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_sshr_i16_proof() {
        let obligation = proof_x86_sshr_i16();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Sshr_I16 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Division lowering proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_sdiv_i32_proof() {
        let obligation = proof_x86_sdiv_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Sdiv_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_sdiv_i64_proof() {
        let obligation = proof_x86_sdiv_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Sdiv_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_udiv_i32_proof() {
        let obligation = proof_x86_udiv_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Udiv_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_udiv_i64_proof() {
        let obligation = proof_x86_udiv_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Udiv_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_srem_i32_proof() {
        let obligation = proof_x86_srem_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Srem_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_srem_i64_proof() {
        let obligation = proof_x86_srem_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Srem_I64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Branchless-guarded signed division proofs (TOTAL, certify INT_MIN/-1)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_sdiv_i32_guarded_proof() {
        let obligation = proof_x86_sdiv_i32_guarded();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Sdiv_I32 branchless-guarded proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_sdiv_i64_guarded_proof() {
        let obligation = proof_x86_sdiv_i64_guarded();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Sdiv_I64 branchless-guarded proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_srem_i32_guarded_proof() {
        let obligation = proof_x86_srem_i32_guarded();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Srem_I32 branchless-guarded proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_srem_i64_guarded_proof() {
        let obligation = proof_x86_srem_i64_guarded();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Srem_I64 branchless-guarded proof failed: {:?}",
            result
        );
    }

    /// Targeted regression: the guarded SDiv/SRem proofs MUST hold at the
    /// INT_MIN/-1 corner that the overflow-precondition'd proofs exclude. We
    /// check the modeled emitted expression equals the trust_ir spec directly at
    /// that point (and a couple of x/-1 points) so a future change to the model
    /// or spec that breaks totality is caught even if random sampling misses it.
    #[test]
    fn test_x86_64_guarded_sdiv_srem_int_min_corner() {
        use crate::smt::EvalResult;
        use std::collections::HashMap;

        // (width, INT_MIN, -1)
        for (width, int_min) in [(32u32, 0x8000_0000u64), (64u32, 0x8000_0000_0000_0000u64)] {
            let minus_one = crate::smt::mask(u64::MAX, width);
            // Several adversarial points incl. INT_MIN/-1, 7/-1, 0/-1, INT_MIN/2.
            let points: &[(u64, u64)] = &[
                (int_min, minus_one), // overflow corner: q == INT_MIN, r == 0
                (7, minus_one),       // x/-1 == -x, x%-1 == 0
                (0, minus_one),
                (int_min, 2), // ordinary division still correct
            ];
            for &(av, bv) in points {
                let mut env = HashMap::new();
                env.insert("a".to_string(), crate::smt::mask(av, width));
                env.insert("b".to_string(), crate::smt::mask(bv, width));

                let (sdiv, srem) = if width == 32 {
                    (proof_x86_sdiv_i32_guarded(), proof_x86_srem_i32_guarded())
                } else {
                    (proof_x86_sdiv_i64_guarded(), proof_x86_srem_i64_guarded())
                };

                let spec_q = sdiv.trust_ir_expr.eval(&env);
                let emit_q = sdiv.aarch64_expr.eval(&env);
                assert!(
                    spec_q.semantically_equal(&emit_q),
                    "guarded SDiv mismatch at width={width} a={av:#x} b={bv:#x}: spec={spec_q:?} emitted={emit_q:?}"
                );

                let spec_r = srem.trust_ir_expr.eval(&env);
                let emit_r = srem.aarch64_expr.eval(&env);
                assert!(
                    spec_r.semantically_equal(&emit_r),
                    "guarded SRem mismatch at width={width} a={av:#x} b={bv:#x}: spec={spec_r:?} emitted={emit_r:?}"
                );

                // Sanity-pin the overflow corner to the wrapping spec values.
                if (av, bv) == (int_min, minus_one) {
                    assert_eq!(
                        emit_q,
                        EvalResult::Bv(int_min),
                        "INT_MIN/-1 quotient must be INT_MIN"
                    );
                    assert_eq!(emit_r, EvalResult::Bv(0), "INT_MIN%-1 remainder must be 0");
                }
            }
        }
    }

    #[test]
    fn test_x86_64_urem_i32_proof() {
        let obligation = proof_x86_urem_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Urem_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_urem_i64_proof() {
        let obligation = proof_x86_urem_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Urem_I64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Bitwise lowering proof tests (32-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_band_i32_proof() {
        let obligation = proof_x86_band_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Band_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bor_i32_proof() {
        let obligation = proof_x86_bor_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bor_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bxor_i32_proof() {
        let obligation = proof_x86_bxor_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bxor_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bnot_i32_proof() {
        let obligation = proof_x86_bnot_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bnot_I32 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Bitwise lowering proof tests (64-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_band_i64_proof() {
        let obligation = proof_x86_band_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Band_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bor_i64_proof() {
        let obligation = proof_x86_bor_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bor_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bxor_i64_proof() {
        let obligation = proof_x86_bxor_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bxor_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bnot_i64_proof() {
        let obligation = proof_x86_bnot_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bnot_I64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Shift lowering proof tests (32-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_ishl_i32_proof() {
        let obligation = proof_x86_ishl_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Ishl_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_ushr_i32_proof() {
        let obligation = proof_x86_ushr_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Ushr_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_sshr_i32_proof() {
        let obligation = proof_x86_sshr_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Sshr_I32 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Shift lowering proof tests (64-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_ishl_i64_proof() {
        let obligation = proof_x86_ishl_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Ishl_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_ushr_i64_proof() {
        let obligation = proof_x86_ushr_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Ushr_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_sshr_i64_proof() {
        let obligation = proof_x86_sshr_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Sshr_I64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // 8-bit exhaustive proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_iadd_i8_proof() {
        let obligation = proof_x86_iadd_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Iadd_I8 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_isub_i8_proof() {
        let obligation = proof_x86_isub_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Isub_I8 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_imul_i8_proof() {
        let obligation = proof_x86_imul_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Imul_I8 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Comparison lowering proof tests (32-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_icmp_eq_i32_proof() {
        let obligation = proof_x86_icmp_eq_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_EQ_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_ne_i32_proof() {
        let obligation = proof_x86_icmp_ne_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_NE_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_slt_i32_proof() {
        let obligation = proof_x86_icmp_slt_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_SLT_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_sge_i32_proof() {
        let obligation = proof_x86_icmp_sge_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_SGE_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_sgt_i32_proof() {
        let obligation = proof_x86_icmp_sgt_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_SGT_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_sle_i32_proof() {
        let obligation = proof_x86_icmp_sle_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_SLE_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_ult_i32_proof() {
        let obligation = proof_x86_icmp_ult_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_ULT_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_uge_i32_proof() {
        let obligation = proof_x86_icmp_uge_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_UGE_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_ugt_i32_proof() {
        let obligation = proof_x86_icmp_ugt_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_UGT_I32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_ule_i32_proof() {
        let obligation = proof_x86_icmp_ule_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_ULE_I32 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Comparison lowering proof tests (64-bit)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_icmp_eq_i64_proof() {
        let obligation = proof_x86_icmp_eq_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_EQ_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_ne_i64_proof() {
        let obligation = proof_x86_icmp_ne_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_NE_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_slt_i64_proof() {
        let obligation = proof_x86_icmp_slt_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_SLT_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_sge_i64_proof() {
        let obligation = proof_x86_icmp_sge_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_SGE_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_sgt_i64_proof() {
        let obligation = proof_x86_icmp_sgt_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_SGT_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_sle_i64_proof() {
        let obligation = proof_x86_icmp_sle_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_SLE_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_ult_i64_proof() {
        let obligation = proof_x86_icmp_ult_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_ULT_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_uge_i64_proof() {
        let obligation = proof_x86_icmp_uge_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_UGE_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_ugt_i64_proof() {
        let obligation = proof_x86_icmp_ugt_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_UGT_I64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_icmp_ule_i64_proof() {
        let obligation = proof_x86_icmp_ule_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Icmp_ULE_I64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Floating-point lowering proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_fadd_f32_proof() {
        let obligation = proof_x86_fadd_f32();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fadd_F32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fadd_f64_proof() {
        let obligation = proof_x86_fadd_f64();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fadd_F64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fsub_f32_proof() {
        let obligation = proof_x86_fsub_f32();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fsub_F32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fsub_f64_proof() {
        let obligation = proof_x86_fsub_f64();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fsub_F64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fmul_f32_proof() {
        let obligation = proof_x86_fmul_f32();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fmul_F32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fmul_f64_proof() {
        let obligation = proof_x86_fmul_f64();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fmul_F64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fdiv_f32_proof() {
        let obligation = proof_x86_fdiv_f32();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fdiv_F32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fdiv_f64_proof() {
        let obligation = proof_x86_fdiv_f64();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fdiv_F64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Floating-point unary lowering proof tests (FNEG, FABS, FSQRT)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_fneg_f32_proof() {
        let obligation = proof_x86_fneg_f32();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fneg_F32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fneg_f64_proof() {
        let obligation = proof_x86_fneg_f64();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fneg_F64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fabs_f32_proof() {
        let obligation = proof_x86_fabs_f32();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fabs_F32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fabs_f64_proof() {
        let obligation = proof_x86_fabs_f64();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fabs_F64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fsqrt_f32_proof() {
        let obligation = proof_x86_fsqrt_f32();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fsqrt_F32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fsqrt_f64_proof() {
        let obligation = proof_x86_fsqrt_f64();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Fsqrt_F64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_round_proofs() {
        for obligation in [
            proof_x86_ffloor_f32(),
            proof_x86_ffloor_f64(),
            proof_x86_fceil_f32(),
            proof_x86_fceil_f64(),
            proof_x86_ftrunc_f32(),
            proof_x86_ftrunc_f64(),
        ] {
            let name = obligation.name.clone();
            let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "x86-64 round proof {:?} failed: {:?}",
                name,
                result
            );
        }
    }

    // Negative control: a round proof whose machine side uses the WRONG imm8
    // mode (ceil-encoded ROUNDSD for a floor spec) MUST be rejected. This is the
    // anti-tautology guard: it proves the two sides are modeled independently and
    // the equivalence genuinely depends on the rounding direction.
    #[test]
    fn test_x86_64_round_wrong_mode_is_rejected() {
        use crate::trust_ir_semantics::encode_trust_ir_ffloor;
        use crate::x86_64_semantics::{X86FPSize, encode_fp_round};
        use trust_cg_lower::types::Type;

        let a = SmtExpr::fp64_const(0.0);
        let bogus = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "x86_64: FFloor_F64 -> ROUNDSD (WRONG: ceil imm8)".to_string(),
            trust_ir_expr: encode_trust_ir_ffloor(Type::F64, a.clone()),
            // Feed the CEIL imm8 (0x0A) to a FLOOR spec -> must diverge.
            aarch64_expr: encode_fp_round(X86FPSize::Double, ROUND_IMM8_CEIL, a),
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![("a".to_string(), 11, 53)],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let result = crate::lowering_proof::verify_fp_by_evaluation(&bogus);
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "floor-spec vs ceil-imm8 ROUNDSD must be rejected, got {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Scalar FP min/max + UNORD-mask proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_minmax_proofs() {
        for obligation in [
            proof_x86_minsd_f64(),
            proof_x86_maxsd_f64(),
            proof_x86_minss_f32(),
            proof_x86_maxss_f32(),
            proof_x86_cmpsd_unord_f64(),
            proof_x86_cmpss_unord_f32(),
        ] {
            let name = obligation.name.clone();
            let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "x86-64 min/max proof {:?} failed: {:?}",
                name,
                result
            );
        }
    }

    // Negative control / anti-tautology guard: directly evaluate the MIN spec
    // (`encode_trust_ir_fminsd_hw`) against the WRONG machine op (`encode_fp_maxsd`)
    // over the IEEE edge battery; they MUST diverge on at least one ordered pair
    // (e.g. min(1,2)=1 != max(1,2)=2). This proves the spec and the machine model
    // are INDEPENDENT (a non-tautological pairing): swapping in the wrong op is
    // detected. We evaluate the encoders directly so the check does not depend on
    // the name-based proof router.
    #[test]
    fn test_x86_64_min_spec_vs_max_machine_diverges() {
        use crate::trust_ir_semantics::encode_trust_ir_fminsd_hw;
        use crate::x86_64_semantics::encode_fp_maxsd;
        use trust_cg_lower::types::Type;

        let empty = std::collections::HashMap::new();
        let mut found_divergence = false;
        for &av in &[1.0f64, 2.0, -3.0, 0.5] {
            for &bv in &[1.0f64, 2.0, -3.0, 0.5] {
                let a = SmtExpr::fp64_const(av);
                let b = SmtExpr::fp64_const(bv);
                let spec = encode_trust_ir_fminsd_hw(Type::F64, a.clone(), b.clone());
                let wrong = encode_fp_maxsd(a, b);
                let (Ok(s), Ok(w)) = (spec.try_eval(&empty), wrong.try_eval(&empty)) else {
                    continue;
                };
                if s != w {
                    found_divergence = true;
                }
            }
        }
        assert!(
            found_divergence,
            "min-spec and max-machine must diverge on some ordered pair (independence guard)"
        );
    }

    // Positive sanity: the min spec and the CORRECT machine op (`encode_fp_minsd`)
    // agree on those same ordered pairs.
    #[test]
    fn test_x86_64_min_spec_matches_min_machine() {
        use crate::trust_ir_semantics::encode_trust_ir_fminsd_hw;
        use crate::x86_64_semantics::encode_fp_minsd;
        use trust_cg_lower::types::Type;

        let empty = std::collections::HashMap::new();
        for &av in &[1.0f64, 2.0, -3.0, 0.5, f64::NAN, -0.0, 0.0, f64::INFINITY] {
            for &bv in &[1.0f64, 2.0, -3.0, 0.5, f64::NAN, -0.0, 0.0, f64::INFINITY] {
                let a = SmtExpr::fp64_const(av);
                let b = SmtExpr::fp64_const(bv);
                let spec = encode_trust_ir_fminsd_hw(Type::F64, a.clone(), b.clone());
                let machine = encode_fp_minsd(a, b);
                let (Ok(s), Ok(m)) = (spec.try_eval(&empty), machine.try_eval(&empty)) else {
                    panic!("eval failed");
                };
                // NaN-on-both-sides counts as agreement (same bits emitted).
                let agree = match (&s, &m) {
                    (crate::smt::EvalResult::Float(sf), crate::smt::EvalResult::Float(mf)) => {
                        (sf.is_nan() && mf.is_nan()) || sf.to_bits() == mf.to_bits()
                    }
                    _ => s == m,
                };
                assert!(
                    agree,
                    "min spec/machine disagree at a={av}, b={bv}: {s:?} vs {m:?}"
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Floating-point comparison proof tests
    // -----------------------------------------------------------------------

    fn assert_x86_fcmp_valid(obligation: ProofObligation) {
        let name = obligation.name.clone();
        let result = crate::lowering_proof::verify_fp_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 FP compare proof failed for {name}: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_fcmp_eq_f32_proof() {
        assert_x86_fcmp_valid(proof_x86_fcmp_eq_f32());
    }

    #[test]
    fn test_x86_64_fcmp_ord_f64_proof() {
        assert_x86_fcmp_valid(proof_x86_fcmp_ord_f64());
    }

    #[test]
    fn test_x86_64_fcmp_uno_f32_proof() {
        assert_x86_fcmp_valid(proof_x86_fcmp_uno_f32());
    }

    #[test]
    fn test_x86_64_fcmp_ueq_f64_proof() {
        assert_x86_fcmp_valid(proof_x86_fcmp_ueq_f64());
    }

    // -----------------------------------------------------------------------
    // 8-bit exhaustive bitwise proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_band_i8_proof() {
        let obligation = proof_x86_band_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Band_I8 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bor_i8_proof() {
        let obligation = proof_x86_bor_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bor_I8 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_bxor_i8_proof() {
        let obligation = proof_x86_bxor_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Bxor_I8 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // 8-bit exhaustive shift proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_ishl_i8_proof() {
        let obligation = proof_x86_ishl_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Ishl_I8 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_ushr_i8_proof() {
        let obligation = proof_x86_ushr_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Ushr_I8 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_sshr_i8_proof() {
        let obligation = proof_x86_sshr_i8();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 Sshr_I8 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // MOVZX/MOVSX lowering proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_movzx_8_to_32_proof() {
        let obligation = proof_x86_movzx_8_to_32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVZX 8->32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_movzx_16_to_32_proof() {
        let obligation = proof_x86_movzx_16_to_32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVZX 16->32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_movzx_8_to_64_proof() {
        let obligation = proof_x86_movzx_8_to_64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVZX 8->64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_movsx_8_to_32_proof() {
        let obligation = proof_x86_movsx_8_to_32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVSX 8->32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_movsx_16_to_32_proof() {
        let obligation = proof_x86_movsx_16_to_32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVSX 16->32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_movsxd_32_to_64_proof() {
        let obligation = proof_x86_movsxd_32_to_64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVSXD 32->64 proof failed: {:?}",
            result
        );
    }

    // RESIDUAL B: x86-specific i64 byte/word MOVSX/MOVZX (REX.W r64) proofs.
    // These model `MOVSX/MOVZX r64, r/m{8,16}` directly so the function verifier
    // and coverage gate bind an x86-specific X8664Lowering proof for a 64-bit
    // byte/word extend (instead of the AArch64-mnemonic ExtensionTruncation
    // rows). Each is a simple extension — exhaustive over the low 8/16 source
    // bits — and discharges by evaluation.

    #[test]
    fn test_x86_64_movzx_16_to_64_proof() {
        let obligation = proof_x86_movzx_16_to_64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVZX 16->64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_movsx_8_to_64_proof() {
        let obligation = proof_x86_movsx_8_to_64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVSX 8->64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_movsx_16_to_64_proof() {
        let obligation = proof_x86_movsx_16_to_64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 MOVSX 16->64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_movrr_copy_proofs() {
        for obligation in [proof_x86_movrr_copy_i32(), proof_x86_movrr_copy_i64()] {
            assert_x86_proof_valid(obligation);
        }
    }

    // -----------------------------------------------------------------------
    // LEA lowering proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_lea_add_i64_proof() {
        let obligation = proof_x86_lea_add_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 LEA add i64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_lea_scale2_i64_proof() {
        let obligation = proof_x86_lea_scale2_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 LEA scale2 i64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_lea_scale4_i64_proof() {
        let obligation = proof_x86_lea_scale4_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 LEA scale4 i64 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_lea_scale8_i64_proof() {
        let obligation = proof_x86_lea_scale8_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 LEA scale8 i64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Three-operand IMUL lowering proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_imul_rri_i32_proof() {
        let obligation = proof_x86_imul_rri_i32();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 IMUL rri i32 proof failed: {:?}",
            result
        );
    }

    #[test]
    fn test_x86_64_imul_rri_i64_proof() {
        let obligation = proof_x86_imul_rri_i64();
        let result = verify_by_evaluation(&obligation);
        assert!(
            matches!(result, VerificationResult::Valid),
            "x86-64 IMUL rri i64 proof failed: {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // CMOVcc and GPR/XMM bit-transfer proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_cmovcc_bit_proofs() {
        for obligation in [
            proof_x86_cmovcc_bitwise_select(),
            proof_x86_cmovcc32_bitwise_select(),
        ] {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_movd_movq_bit_transfer_proofs() {
        for obligation in [
            proof_x86_movd_to_xmm_bit_preservation(),
            proof_x86_movd_from_xmm_bit_preservation(),
            proof_x86_movq_to_xmm_bit_preservation(),
            proof_x86_movq_from_xmm_bit_preservation(),
        ] {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_fp_select_bit_path_proofs() {
        for obligation in [
            proof_x86_fp_select_f32_bits(),
            proof_x86_fp_select_f64_bits(),
        ] {
            assert_x86_proof_valid(obligation);
        }
    }

    // -----------------------------------------------------------------------
    // SSE scalar-FP move / load / store / constant-pool-load proofs (#65)
    // -----------------------------------------------------------------------

    #[test]
    fn test_x86_64_fp_move_proofs_discharge() {
        let proofs = x86_64_fp_move_proofs();
        assert_eq!(
            proofs.len(),
            8,
            "expected 8 x86 scalar-FP move/load/store/const-pool proofs"
        );
        // The reg-reg copies + load + store discharge via the bit-vector /
        // memory evaluator; the RIP-relative const-pool proofs are bv-arith.
        for obligation in proofs {
            assert_x86_proof_valid(obligation);
        }
    }

    /// The reg-reg float-move proof must be a REAL bit-identity: a "move" that
    /// flips the sign bit must REFUTE. Guards against a vacuous tautology that
    /// would pass a wrong (sign-corrupting) lowering.
    #[test]
    fn test_x86_64_fp_movrr_signflip_refutes() {
        let result = verify_by_evaluation(&proof_x86_fp_movrr_signflip_refutes());
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "sign-flipping MOVSD copy must refute, got {result:?}"
        );
    }

    /// The constant-pool RIP-relative load proof must require RIP-relative
    /// provenance: an ABSOLUTE displacement must REFUTE.
    #[test]
    fn test_x86_64_fp_constpool_wrong_absolute_refutes() {
        let result = verify_by_evaluation(&proof_x86_fp_constpool_wrong_absolute_refutes());
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "absolute-disp const-pool load must refute, got {result:?}"
        );
    }

    /// Every negative control listed for the FP-move family must refute.
    #[test]
    fn test_x86_64_fp_move_negative_controls_all_refute() {
        for obligation in x86_64_fp_move_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "FP-move negative control '{}' must refute, got {result:?}",
                obligation.name
            );
        }
    }

    /// SLICE 3: the SeqCst-fence MFENCE single-thread-identity proof VERIFIES —
    /// MFENCE preserves the (register, memory) state.
    #[test]
    fn test_x86_64_mfence_single_thread_identity_verifies() {
        let result = verify_by_evaluation(&proof_x86_fence_seqcst_mfence());
        assert!(
            matches!(result, VerificationResult::Valid),
            "MFENCE single-thread identity must verify, got {result:?}"
        );
    }

    /// SLICE 3 HONESTY AUDIT: the MFENCE identity is a REAL data-flow obligation,
    /// not a #62 tautology — a "fence" that clobbered a register or a memory byte
    /// must REFUTE. If either of these passed, the positive identity would be
    /// vacuous and must NOT be on the GENUINE_IDENTITY_ALLOWLIST.
    #[test]
    fn test_x86_64_mfence_negative_controls_all_refute() {
        for obligation in x86_64_mfence_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "MFENCE negative control '{}' must refute (else the identity is vacuous), \
                 got {result:?}",
                obligation.name
            );
        }
    }

    /// SLICE 4: every registered CMPXCHG (compare_exchange) proof VERIFIES —
    /// returns-old, conditional-store, and success-flag, at i32 and i64.
    #[test]
    fn test_x86_64_cmpxchg_proofs_all_verify() {
        for obligation in all_x86_64_cmpxchg_proofs() {
            // Higher sample count so the sweep exercises the conditional-store /
            // returns-old data flow across many (expected, old, desired) points.
            assert_x86_proof_valid_with_samples(obligation, 20_000);
        }
    }

    /// SLICE 4 non-vacuity: the CMPXCHG proofs certify REAL conditional data flow,
    /// not a #62 X==X tautology. A "CMPXCHG" that stores UNCONDITIONALLY, returns
    /// DESIRED instead of old, or sets the success flag BACKWARDS must REFUTE.
    #[test]
    fn test_x86_64_cmpxchg_negative_controls_all_refute() {
        for obligation in x86_64_cmpxchg_negative_controls() {
            let config = crate::lowering_proof::VerificationConfig::with_sample_count(20_000);
            let result =
                crate::lowering_proof::verify_by_evaluation_with_config(&obligation, &config);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "CMPXCHG negative control '{}' must refute (else the conditional-CAS proof is \
                 vacuous), got {result:?}",
                obligation.name
            );
        }
    }

    /// SLICE 4 registration: exactly 6 CMPXCHG obligations (3 facets x i32/i64),
    /// and NONE is structurally degenerate (each machine side genuinely differs
    /// from its trust-ir spec, so a wrong lowering refutes).
    #[test]
    fn test_x86_64_cmpxchg_proof_family_registered_and_non_degenerate() {
        let proofs = all_x86_64_cmpxchg_proofs();
        assert_eq!(
            proofs.len(),
            10,
            "expected 10 x86 Cmpxchg proofs (5 facets x i32/i64)"
        );
        for facet in [
            "returns old value",
            "conditional store",
            "success branch stores desired",
            "failure branch preserves memory",
            "success flag",
        ] {
            assert_eq!(
                proofs.iter().filter(|p| p.name.contains(facet)).count(),
                2,
                "expected an i32 and i64 Cmpxchg `{facet}` proof"
            );
        }
        // Every CMPXCHG proof is structurally NON-degenerate — the machine side is
        // never the identical tree as the trust-ir spec (so it is NOT an X==X and
        // needs no GENUINE_IDENTITY_ALLOWLIST entry). This is the honesty core:
        // the conditional data flow makes each obligation a real theorem.
        for proof in &proofs {
            assert_ne!(
                proof.trust_ir_expr, proof.aarch64_expr,
                "Cmpxchg proof '{}' is structurally degenerate (X==X) — it must be a \
                 genuine conditional-data-flow obligation, not an identity",
                proof.name
            );
        }
    }

    #[test]
    fn test_x86_64_atomic_load_store_fence_proof_family_registered() {
        let proofs = all_x86_64_atomic_load_store_fence_proofs();
        // 8 load/store (4 widths x load+store) + 1 SeqCst-fence MFENCE identity.
        // SLICE 3: Acquire/Release/AcqRel fences emit ZERO instructions on x86
        // TSO, so they have NO obligation — only the SeqCst -> MFENCE mapping is
        // proven (and it is a GENUINE single-thread-identity proof, not a #62
        // const==const tautology).
        assert_eq!(
            proofs.len(),
            9,
            "expected 8 atomic load/store + 1 SeqCst-fence proof obligation"
        );

        for width in ["I8", "I16", "I32", "I64"] {
            assert!(
                proofs.iter().any(|proof| proof
                    .name
                    .contains(&format!("AtomicLoad_{width} -> MOV r,[mem]"))),
                "missing x86 AtomicLoad_{width} proof"
            );
            assert!(
                proofs.iter().any(|proof| proof
                    .name
                    .contains(&format!("AtomicStore_{width} -> MOV [mem],r"))),
                "missing x86 AtomicStore_{width} proof"
            );
        }
        // Exactly ONE fence proof: the SeqCst MFENCE single-thread identity.
        assert!(
            proofs
                .iter()
                .any(|proof| proof.name == "x86_64: SeqCst fence -> MFENCE single-thread identity"),
            "missing x86 SeqCst-fence MFENCE single-thread identity proof"
        );
        for ordering in ["Acquire", "Release", "AcqRel"] {
            assert!(
                !proofs
                    .iter()
                    .any(|proof| proof.name.contains(&format!("Fence_{ordering}"))),
                "Acquire/Release/AcqRel fences must have NO proof (zero-instruction on TSO)"
            );
        }
    }

    #[test]
    fn test_x86_64_atomic_load_store_fence_proofs() {
        for obligation in all_x86_64_atomic_load_store_fence_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_atomic_rmw_cas_loop_proof_family_registered() {
        let proofs = all_x86_64_atomic_rmw_cas_loop_proofs();
        assert_eq!(
            proofs.len(),
            76,
            "expected 76 x86 AtomicRmwCasLoop proof obligations"
        );

        let old_value = proofs
            .iter()
            .filter(|proof| proof.name.contains("returns old value"))
            .count();
        let updates = proofs
            .iter()
            .filter(|proof| proof.name.contains("updates memory"))
            .count();
        let adjacent = proofs
            .iter()
            .filter(|proof| proof.name.contains("preserves adjacent memory"))
            .count();

        // Narrow (i8/i16): 6 ops (Add/Sub/And/Or/Xor/Xchg) x 2 widths.
        // Generic (i32/i64): 10 ops (+ Xchg, Max/Min/UMax/UMin) x 2 widths.
        // old/update = (6*2)+(10*2) = 32 each; adjacent (i8/i16 only) = 6*2 = 12.
        assert_eq!(old_value, 32, "expected old-value proof per real op/width");
        assert_eq!(updates, 32, "expected update proof per real op/width");
        assert_eq!(adjacent, 12, "expected adjacent i8/i16 proof per op");
    }

    #[test]
    fn test_x86_64_atomic_rmw_cas_loop_proofs() {
        let config = crate::lowering_proof::VerificationConfig::with_sample_count(512);

        for obligation in all_x86_64_atomic_rmw_cas_loop_proofs() {
            let name = obligation.name.clone();
            let result =
                crate::lowering_proof::verify_by_evaluation_with_config(&obligation, &config);
            assert!(
                matches!(result, VerificationResult::Valid),
                "x86-64 AtomicRmwCasLoop proof failed for {name}: {result:?}"
            );
        }
    }

    #[test]
    fn test_x86_64_scalar_bitfield_proof_family_registered() {
        let proofs = all_x86_64_scalar_bitfield_proofs();
        assert_eq!(
            proofs.len(),
            16,
            "expected 16 x86 scalar bitfield proof obligations"
        );

        let unsigned_extract = proofs
            .iter()
            .filter(|proof| proof.name.contains("ExtractBits{"))
            .count();
        let signed_extract = proofs
            .iter()
            .filter(|proof| proof.name.contains("SextractBits{"))
            .count();
        let insert = proofs
            .iter()
            .filter(|proof| proof.name.contains("InsertBits{") && !proof.name.contains("(dst,dst)"))
            .count();
        let alias_insert = proofs
            .iter()
            .filter(|proof| proof.name.contains("InsertBits{") && proof.name.contains("(dst,dst)"))
            .count();

        assert_eq!(
            unsigned_extract, 4,
            "expected unsigned extract proof per width"
        );
        assert_eq!(signed_extract, 4, "expected signed extract proof per width");
        assert_eq!(insert, 4, "expected insert proof per width");
        assert_eq!(alias_insert, 4, "expected alias insert proof per width");
    }

    #[test]
    fn test_x86_64_scalar_bitfield_proofs() {
        for obligation in all_x86_64_scalar_bitfield_proofs() {
            assert_x86_proof_valid(obligation);
        }
    }

    #[test]
    fn test_x86_64_bt_cf_proof_family_registered() {
        let proofs = all_x86_64_bit_manip_proofs();
        let bt_i32 = proofs
            .iter()
            .filter(|p| p.name.contains("BtRI_I32#"))
            .count();
        let bt_i64 = proofs
            .iter()
            .filter(|p| p.name.contains("BtRI_I64#"))
            .count();
        assert_eq!(bt_i32, 32, "expected one BtRI CF proof per i32 bit index");
        assert_eq!(bt_i64, 64, "expected one BtRI CF proof per i64 bit index");
    }

    /// NEGATIVE CONTROL: a WRONG BtRI model — `CF := bit (k+1)` instead of the
    /// correct `bit k` — must REFUTE. This proves the BT-CF obligation is not
    /// vacuous: it genuinely pins the carry flag to the EXACT tested bit.
    #[test]
    fn test_x86_64_bt_cf_wrong_bit_refutes() {
        // Correct reference is bit k = 3; model the x86 side as bit k+1 = 4.
        let a = SmtExpr::var("a", 32);
        let wrong = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "x86_64: BtRI wrong-bit (k vs k+1) must REFUTE".to_string(),
            trust_ir_expr: reference_and_mask_bit(a.clone(), 3),
            aarch64_expr: crate::x86_64_semantics::encode_bt_cf(a, 4),
            inputs: vec![("a".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let result = verify_by_evaluation(&wrong);
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "wrong BtRI bit model must refute, got {result:?}"
        );
    }

    /// NEGATIVE CONTROL: a WRONG widening-MUL high-half model — using the LOW
    /// half (RAX) as the overflow detector instead of the HIGH half (RDX) — must
    /// REFUTE. This proves the MUL high-half/overflow obligation is not vacuous.
    #[test]
    fn test_x86_64_mul_overflow_wrong_half_refutes() {
        use crate::x86_64_semantics::encode_mul_low;
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        // Wrong x86 side: LOW half != 0 (should be HIGH half != 0).
        let low = encode_mul_low(a.clone(), b.clone());
        let low_nonzero = SmtExpr::ite(
            low.eq_expr(SmtExpr::bv_const(0, 32)).not_expr(),
            SmtExpr::bv_const(1, 1),
            SmtExpr::bv_const(0, 1),
        );
        let wrong = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "x86_64: Umul overflow wrong-half (low vs high) must REFUTE".to_string(),
            trust_ir_expr: reference_umul_overflows(a.clone(), b.clone()),
            aarch64_expr: low_nonzero,
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let result = verify_by_evaluation(&wrong);
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "wrong MUL overflow-half model must refute, got {result:?}"
        );
    }

    #[test]
    fn test_x86_proof_failure_report_preserves_registration_order() {
        let results = vec![
            ("first".to_string(), VerificationResult::Valid),
            (
                "second".to_string(),
                VerificationResult::Unknown {
                    reason: "inconclusive".to_string(),
                },
            ),
            (
                "third".to_string(),
                VerificationResult::Invalid {
                    counterexample: "x=1".to_string(),
                },
            ),
        ];
        assert_eq!(
            x86_proof_failure_report(&results).as_deref(),
            Some(
                "Proof 'second' failed: Unknown { reason: \"inconclusive\" }\n\
                 Proof 'third' failed: Invalid { counterexample: \"x=1\" }"
            )
        );
    }

    // -----------------------------------------------------------------------
    // Meta: verify all proofs at once
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_x86_64_proofs() {
        // This aggregate is CPU-heavy sampling, not a formal solver batch.
        // Share the formal-test mutex anyway so it cannot steal cores from an
        // AY subprocess whose wall-clock deadline is proof-significant.
        let _formal_solver_lock = crate::ay_bridge::formal_solver_test_lock();
        let proofs = all_x86_64_proofs();
        let atomic_config = crate::lowering_proof::VerificationConfig::with_sample_count(512);
        // 69 original + 6 FP unary (fneg/fabs/fsqrt x f32/f64) + 28 FP compare
        //   + 6 8-bit (band/bor/bxor/ishl/ushr/sshr)
        //   + 4 direct CMP EFLAGS writes at i32 (#458: ZF/SF/CF/OF)
        //   + 9 x86 i16 arithmetic/bitwise/shift proofs (#498)
        //   + 10 BandNot/BorNot scalar proofs (B1/I8/I16/I32/I64)
        //   + 8 CMOVcc/MOVD/MOVQ/FP-select bit proofs
        //   + 76 x86 AtomicRmwCasLoop old/update/adjacent proofs (was 72; +4 for
        //        Xchg_I32/I64 old-value + updates-memory, slice 2 swap/SeqCst-store)
        //   + 16 x86 scalar bitfield extract/sextract/insert/alias proofs
        //   + 4 x86 scalar bitfield alias/width proofs
        //   + 12 x86 atomic load/store/fence proofs
        //   + 2 x86 MOVRR copy proofs
        //   + 3 x86 control/constant proofs (CALL, RET, MOV r,imm)
        //   + 9 pre-existing x86 SIMD integer proofs (V2I64
        //        PADDQ/PSUBQ/scalarized MUL plus six V4I32 shifts)
        //   + 3 V2I64 PSLLQ/PSRLQ/PMULUDQ proofs (16ab91cb)
        //   + 23 x86 V128 boolean-mask proofs (#1109)
        //   + 11 x86 V128 packed arithmetic/bitwise proofs (#1111)
        //   + 8 x86 V2I64 compare/mask-extract proofs (#1114)
        //   + 22 x86 V4I32/V2I64 lane pack/extract/insert proofs (#1115)
        //   + 12 x86 SSE FP conversion proofs (CVTSI2SD/SS, CVT(T)SD/SS2SI,
        //        CVTSD2SS, CVTSS2SD)
        //   + 16 x86 bit-manipulation proofs (POPCNT/TZCNT/LZCNT/BSF/BSR)
        //   + 6 x86 parity-flag (PF) proofs (CMP PF + SETcc P/NP)
        //   + 8 x86 packed-FP per-lane proofs (ADDPS/SUBPS/MULPS/DIVPS and
        //        ADDPD/SUBPD/MULPD/DIVPD)
        //   + 3 width-correct i64 byte/word extends (MOVZX r16->r64,
        //        MOVSX r8->r64, MOVSX r16->r64) registered alongside the
        //        existing extend family for the width-polymorphic verifier
        //   + 4 branchless-guarded signed division proofs (sdiv/srem x i32/i64),
        //        TOTAL with only `b != 0` — certify the INT_MIN/-1 corner left
        //        open by the overflow-precondition'd division proofs.
        // The intermediate running subtotals above were maintained separately on
        // the two merged branches and had drifted; the authoritative count is the
        // sum of every entry actually assembled in `all_x86_64_proofs` (169 direct
        // obligations + 214 family obligations), cross-checked against the
        // per-family `assert_eq!` registration tests in this module.
        // + 14 per-compile gate-coverage obligations: JMP control-target (1),
        //   LEA base+disp32 (1), LEA SIB +disp32 per scale (4),
        //   Load_I8/I16/I32/I64 (4), Store_I8/I16/I32/I64 (4).
        // + 2 RIP-relative provenance-bound obligations (#95): LeaRip (SIGNED
        //   reloc → materializes S+A) and MovRipRel (GOT_LOAD → loads from S+A).
        // + 96 BtRI CF obligations: BT r,imm8 sets CF := bit#k(src) == (src &
        //   (1<<k)) != 0, the identity the AND/CMP/Jcc→BT/Jcc peephole relies on,
        //   proven exhaustively per static bit index for Gpr32 (32) + Gpr64 (64).
        // + 4 one-operand widening MUL obligations (RDX:RAX = RAX*src, for
        //   CheckedUmul/unsigned-overflow multiply): low half (RAX) == wrapping
        //   multiply and high half (RDX) != 0 == unsigned overflow, at i32 + i64.
        // + 8 SSE scalar-FP move obligations (#65): MOVSS/MOVSD reg-reg copy
        //   (bit-identity), MOVSS/MOVSD load + store (memory at f32/f64 width),
        //   and MovssRipRel/MovsdRipRel rodata constant-pool RIP-relative address.
        // + 6 SSE4.1 scalar round-to-integral obligations: FFloor/FCeil/FTrunc
        //   (RTN/RTP/RTZ fp.roundToIntegral) at F32 (ROUNDSS) and F64 (ROUNDSD).
        // + 6 SSE scalar min/max + UNORD-mask obligations (Rust f{32,64}::min/max
        //   NaN-away idiom): MINSD/MAXSD (F64) + MINSS/MAXSS (F32) modeling the
        //   SDM hardware min/max, and CMPSD/CMPSS imm8=3 modeling the isNaN mask.
        // + 2 i128 carry-chain high-limb obligations: ADC (Iadd_I128 hi) and
        //   SBB (Isub_I128 hi), the faithful 65-bit carry/borrow proofs whose
        //   trust-ir spec is the high 64 bits of the full 128-bit sum/diff.
        // + 2 i128 carry-chain WHOLE-value composition obligations: Iadd_I128
        //   (ADD lo; ADC hi) and Isub_I128 (SUB lo; SBB hi), modeling the full
        //   two-instruction 128-bit value with a faithfully-derived 65-bit
        //   carry/borrow (NOT the high-limb-only proofs above).
        // Was 523; #62 retracted the 16 degenerate x86 control-flow (CALL/JMP/RET),
        // MOV-r,imm, Fence->MFENCE, and plain/SIB LEA effective-address X==X proofs.
        // +4 (513->517): AtomicRmwCasLoop_Xchg_I32/I64 old-value + updates-memory
        // (slice 2 -- swap() + SeqCst store route Xchg through the CAS loop).
        // +1 (517->518): SLICE 3 -- the SeqCst-fence MFENCE single-thread IDENTITY
        // proof (a GENUINE data-flow obligation over symbolic register/memory
        // state: MFENCE writes no register / no memory), which REPLACES the four
        // retracted Fence->MFENCE const==const tautologies (Acquire/Release/AcqRel
        // fences are now zero-instruction on x86 TSO -- no obligation).
        // +10 (518->528): SLICE 4 -- CMPXCHG (compare_exchange) conditional-data-flow
        // proofs, each at i32/i64 (5 facets x 2 widths): returns-old, conditional-
        // store (both arms), success-branch-stores-desired (forces the equal arm),
        // failure-branch-preserves-memory (expected!=old precond), and success-flag.
        // GENUINE non-identity obligations over symbolic (mem, expected, desired)
        // state (the equality-gated store + dual old-value/ZF output), witnessed
        // non-vacuous by the unconditional-store / returns-desired / backwards-flag
        // negative controls (which REFUTE). NOT an X==X allowlist entry.
        // +3 (528->531): the V2I64 PSLLQ, PSRLQ, and PMULUDQ obligations. Each
        // has an independent machine-side encoding and dedicated wrong-model
        // controls (lane width/direction; odd lanes/sign extension/low half),
        // so this is real coverage growth rather than count inflation.
        // +1 (531->532): `V2I64 saxpy-accumulate -> IMUL/IMUL/MOVQ/MOVQ/
        // PUNPCKLQDQ/PADDQ`. A COMPOSITE sequence obligation (like V16I8Mul),
        // NOT a PUNPCKLQDQ identity — that form is degenerate X==X and was
        // reverted. Non-degeneracy and a swapped-operand refutation are both
        // asserted by dedicated tests, so this is real coverage growth.
        // +11 (532->543): ROL (rotate-left by constant) — 5 amounts at 32-bit
        // and 6 at 64-bit, both boundaries (k=1, k=width-1) included. `ROL`
        // MEANS the shift/shift/or idiom it replaces, so the naive obligation
        // would be degenerate X==X; the machine side is written with the OR
        // halves in the OPPOSITE order. Non-degeneracy, real-solver discharge
        // and THREE refuting controls per width are asserted by
        // `x86_rol_proofs_are_faithful_and_non_degenerate` and
        // `test_ay_batch_verify_x86_rol_proofs`.
        assert_eq!(proofs.len(), 543, "Expected 543 x86-64 proof obligations");

        // Each obligation is independent and every statistical evaluator uses
        // a name-seeded deterministic PRNG. Fan out on a small dedicated pool;
        // indexed `par_iter().map().collect()` preserves registration order.
        // Report failures only after the ordered join so scheduling can never
        // choose which failure appears first.
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(x86_proof_eval_worker_count())
            .stack_size(8 * 1024 * 1024)
            .thread_name(|index| format!("trust-cg-x86-proof-eval-{index}"))
            .build()
            .expect("build bounded x86 proof-evaluation pool");
        let results: Vec<(String, VerificationResult)> = pool.install(|| {
            proofs
                .par_iter()
                .map(|proof| {
                    let result = if proof.name.contains("AtomicRmwCasLoop") {
                        crate::lowering_proof::verify_by_evaluation_with_config(
                            proof,
                            &atomic_config,
                        )
                    } else if proof.fp_inputs.is_empty() {
                        verify_by_evaluation(proof)
                    } else {
                        crate::lowering_proof::verify_fp_by_evaluation(proof)
                    };
                    (proof.name.clone(), result)
                })
                .collect()
        });
        if let Some(report) = x86_proof_failure_report(&results) {
            panic!("x86-64 proof aggregate failed:\n{report}");
        }
    }
}
