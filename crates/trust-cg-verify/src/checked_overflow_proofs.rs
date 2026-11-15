// trust-cg-verify/checked_overflow_proofs.rs - Checked overflow lowering proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proves the #474 AArch64 checked-arithmetic idioms:
//   sadd: ADDS + CSET VS
//   ssub: SUBS + CSET VS
//   smul: MUL + SMULH + ASR + CMP + CSET NE
//   uadd: ADDS + CSET HS
//   usub: SUBS + CSET LO
//   umul: MUL + UMULH + CMP #0 + CSET NE

//! Proof obligations for checked integer overflow lowering.
//!
//! Each proof packs the two LIR results as a single bitvector:
//! `overflow_b1 :: value_iN`. This lets the existing single-expression
//! [`ProofObligation`](crate::lowering_proof::ProofObligation) machinery prove
//! both the wrapping arithmetic result and the overflow flag together.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

#[derive(Debug, Clone, Copy)]
enum CheckedOverflowKind {
    Sadd,
    Ssub,
    Smul,
    Uadd,
    Usub,
    Umul,
}

fn bv1(cond: SmtExpr) -> SmtExpr {
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

fn msb(value: &SmtExpr, width: u32) -> SmtExpr {
    value.clone().extract(width - 1, width - 1)
}

fn pack(value: SmtExpr, overflow: SmtExpr) -> SmtExpr {
    bv1(overflow).concat(value)
}

fn signed_product(lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    lhs.sign_ext(width).bvmul(rhs.sign_ext(width))
}

fn unsigned_product(lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    lhs.zero_ext(width).bvmul(rhs.zero_ext(width))
}

fn trust_ir_checked(kind: CheckedOverflowKind, lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    match kind {
        CheckedOverflowKind::Sadd => {
            let value = lhs.clone().bvadd(rhs.clone());
            let exact = lhs.sign_ext(1).bvadd(rhs.sign_ext(1));
            let wrapped = value.clone().sign_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Ssub => {
            let value = lhs.clone().bvsub(rhs.clone());
            let exact = lhs.sign_ext(1).bvsub(rhs.sign_ext(1));
            let wrapped = value.clone().sign_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Smul => {
            // SPEC form (deliberately DISTINCT from the AArch64 SMULH-high form so
            // the obligation is a genuine equivalence theorem, not an X==X
            // tautology): signed overflow iff the FULL 2w-bit signed product does
            // not equal the sign-extension of the wrapped w-bit result. This is
            // provably equal to the instruction-side `SMULH != ASR(value, w-1)`
            // (the low w bits agree by construction, so the high halves must), but
            // is encoded differently — ay discharges a real theorem.
            let value = lhs.clone().bvmul(rhs.clone());
            let product = signed_product(lhs, rhs, width);
            let wrapped = value.clone().sign_ext(width);
            pack(value, product.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Uadd => {
            let value = lhs.clone().bvadd(rhs.clone());
            let exact = lhs.zero_ext(1).bvadd(rhs.zero_ext(1));
            let wrapped = value.clone().zero_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Usub => {
            let value = lhs.clone().bvsub(rhs.clone());
            let exact = lhs.zero_ext(1).bvsub(rhs.zero_ext(1));
            let wrapped = value.clone().zero_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Umul => {
            // SPEC form (distinct from the AArch64 UMULH-high form): unsigned
            // overflow iff the FULL 2w-bit unsigned product does not equal the
            // zero-extension of the wrapped w-bit result. Provably equal to the
            // instruction-side `UMULH != 0`, encoded differently — a real theorem.
            let value = lhs.clone().bvmul(rhs.clone());
            let product = unsigned_product(lhs, rhs, width);
            let wrapped = value.clone().zero_ext(width);
            pack(value, product.eq_expr(wrapped).not_expr())
        }
    }
}

fn aarch64_checked(kind: CheckedOverflowKind, lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    match kind {
        CheckedOverflowKind::Sadd => {
            let value = lhs.clone().bvadd(rhs.clone());
            let lhs_sign = msb(&lhs, width);
            let rhs_sign = msb(&rhs, width);
            let value_sign = msb(&value, width);
            let overflow = lhs_sign
                .clone()
                .eq_expr(rhs_sign)
                .and_expr(lhs_sign.eq_expr(value_sign).not_expr());
            pack(value, overflow)
        }
        CheckedOverflowKind::Ssub => {
            let value = lhs.clone().bvsub(rhs.clone());
            let lhs_sign = msb(&lhs, width);
            let rhs_sign = msb(&rhs, width);
            let value_sign = msb(&value, width);
            let overflow = lhs_sign
                .clone()
                .eq_expr(rhs_sign)
                .not_expr()
                .and_expr(lhs_sign.eq_expr(value_sign).not_expr());
            pack(value, overflow)
        }
        CheckedOverflowKind::Smul => {
            let value = lhs.clone().bvmul(rhs.clone());
            let product = signed_product(lhs, rhs, width);
            let high = product.extract((2 * width) - 1, width);
            let sign = value
                .clone()
                .bvashr(SmtExpr::bv_const((width - 1) as u64, width));
            pack(value, high.eq_expr(sign).not_expr())
        }
        CheckedOverflowKind::Uadd => {
            let value = lhs.clone().bvadd(rhs);
            pack(value.clone(), value.bvult(lhs))
        }
        CheckedOverflowKind::Usub => {
            let value = lhs.clone().bvsub(rhs.clone());
            pack(value, lhs.bvult(rhs))
        }
        CheckedOverflowKind::Umul => {
            let value = lhs.clone().bvmul(rhs.clone());
            let product = unsigned_product(lhs, rhs, width);
            let high = product.extract((2 * width) - 1, width);
            pack(value, high.eq_expr(SmtExpr::bv_const(0, width)).not_expr())
        }
    }
}

fn proof_checked_overflow_width(
    kind: CheckedOverflowKind,
    width: u32,
    name: &str,
) -> ProofObligation {
    let lhs = SmtExpr::var("a", width);
    let rhs = SmtExpr::var("b", width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_checked(kind, lhs.clone(), rhs.clone(), width),
        aarch64_expr: aarch64_checked(kind, lhs, rhs, width),
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Prove `CheckedSadd(I64)` lowers to `ADDS; CSET VS`.
pub fn proof_checked_sadd_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Sadd,
        64,
        "CheckedSadd_I64 -> ADDS+CSET_VS",
    )
}

/// Prove `CheckedSsub(I64)` lowers to `SUBS; CSET VS`.
pub fn proof_checked_ssub_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Ssub,
        64,
        "CheckedSsub_I64 -> SUBS+CSET_VS",
    )
}

/// Prove `CheckedSmul(I64)` lowers to `MUL; SMULH; ASR; CMP; CSET NE`.
pub fn proof_checked_smul_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Smul,
        64,
        "CheckedSmul_I64 -> MUL+SMULH+ASR+CMP+CSET_NE",
    )
}

/// Prove `CheckedUadd(U64)` lowers to `ADDS; CSET HS`.
pub fn proof_checked_uadd_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Uadd,
        64,
        "CheckedUadd_I64 -> ADDS+CSET_HS",
    )
}

/// Prove `CheckedUsub(U64)` lowers to `SUBS; CSET LO`.
pub fn proof_checked_usub_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Usub,
        64,
        "CheckedUsub_I64 -> SUBS+CSET_LO",
    )
}

/// Prove `CheckedUmul(U64)` lowers to `MUL; UMULH; CMP #0; CSET NE`.
pub fn proof_checked_umul_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Umul,
        64,
        "CheckedUmul_I64 -> MUL+UMULH+CMP0+CSET_NE",
    )
}

// --- i128 / u128 checked ADD/SUB overflow (the 128-bit add/sub lowering) ------
//
// Unlike i64, the 128-bit add/sub overflow lowering decomposes into the
// width-generic bit-pattern fallback (wrapping Iadd/Isub + sign/carry compare).
// The overflow PREDICATE these compute is exactly the width-parametric
// `aarch64_checked` formula at width 128, so these obligations are just the i64
// proofs re-instantiated at 128 bits. They are a clean linear-bitvector
// equivalence (NO `bvmul`), so — unlike i128 MUL, whose 256-bit `bvmul` times
// out — they discharge formally. The i128 checked MUL obligations live in
// `checked_mul_i128_proofs`: the backend lowers 128-bit checked multiply as the
// low product plus a guarded `__udivti3`/`__divti3` division identity
// (AArch64) or a division-free limb check (x86-64, OD-224), and that family
// states each flag against the exact 256-bit product reconstructed from 64-bit
// limbs (evaluator-discharged, not formal).

/// Prove the `CheckedSadd` overflow predicate at width 128 (i128 add).
pub fn proof_checked_sadd_i128() -> ProofObligation {
    proof_checked_overflow_width(CheckedOverflowKind::Sadd, 128, "CheckedSadd_I128 predicate")
}

/// Prove the `CheckedSsub` overflow predicate at width 128 (i128 sub).
pub fn proof_checked_ssub_i128() -> ProofObligation {
    proof_checked_overflow_width(CheckedOverflowKind::Ssub, 128, "CheckedSsub_I128 predicate")
}

/// Prove the `CheckedUadd` overflow predicate at width 128 (u128 add).
pub fn proof_checked_uadd_i128() -> ProofObligation {
    proof_checked_overflow_width(CheckedOverflowKind::Uadd, 128, "CheckedUadd_I128 predicate")
}

/// Prove the `CheckedUsub` overflow predicate at width 128 (u128 sub).
pub fn proof_checked_usub_i128() -> ProofObligation {
    proof_checked_overflow_width(CheckedOverflowKind::Usub, 128, "CheckedUsub_I128 predicate")
}

/// The four i128/u128 checked add/sub overflow-predicate obligations.
pub fn all_checked_overflow_add_sub_i128_proofs() -> Vec<ProofObligation> {
    vec![
        proof_checked_sadd_i128(),
        proof_checked_ssub_i128(),
        proof_checked_uadd_i128(),
        proof_checked_usub_i128(),
    ]
}

// --- i128 checked ADD/SUB via the FLAG-SETTING carry chain -------------------
//
// The AArch64 ISel lowers `Checked{S,U}{add,sub}` at I128 over the register
// pair:
//
//     ADDS dst_lo, a_lo, b_lo ; ADCS dst_hi, a_hi, b_hi ; CSET ov, VS|HS
//     SUBS dst_lo, a_lo, b_lo ; SBCS dst_hi, a_hi, b_hi ; CSET ov, VS|LO
//
// The chain's VALUE is covered by the existing faithful whole-chain
// composition proofs (`proof_iadd/isub_i128_whole_chain` — the flag-setting
// variants compute the identical value chain, S bit aside). These obligations
// are the missing HALF: the OVERFLOW BIT. The spec side is the exact native
// 128-bit overflow definition (carry compare / borrow compare / msb-form
// signed overflow — all 128-bit operations, no width extension); the machine
// side rebuilds the FINAL NZCV bit of the flag-setting high-half op from
// 64-bit limb arithmetic, exactly as the hardware computes it (65/66-bit
// extended limb sums). Both sides are 1-bit results built from ≤128-bit
// intermediates, so the obligations are evaluator-dischargeable AND
// ay-formal; the two sides are structurally distinct, so a dropped carry or
// a C/V condition confusion REFUTES (see the negative controls).

/// 1-bit carry-out of the 64-bit add `a + b + carry_in` (carry_in is 1-bit):
/// bit 64 of the 65-bit extended sum — the C flag ADDS/ADCS computes.
fn adc_carry_out_64(a: SmtExpr, b: SmtExpr, carry_in: SmtExpr) -> SmtExpr {
    a.zero_ext(1)
        .bvadd(b.zero_ext(1))
        .bvadd(carry_in.zero_ext(64))
        .extract(64, 64)
}

/// 1-bit borrow-out of the 64-bit sub `a - b - borrow_in` (borrow_in is
/// 1-bit): bit 64 of the 65-bit extended difference. SUBS/SBCS set
/// `C = NOT borrow`; `CSET LO` reads `C == 0`, i.e. exactly this bit.
fn sbc_borrow_out_64(a: SmtExpr, b: SmtExpr, borrow_in: SmtExpr) -> SmtExpr {
    a.zero_ext(1)
        .bvsub(b.zero_ext(1))
        .bvsub(borrow_in.zero_ext(64))
        .extract(64, 64)
}

/// SPEC side of the checked-i128 overflow bit: the exact native 128-bit
/// overflow definition, as a 1-bit vector. All operations stay at width 128
/// (carry/borrow via `bvult`, signed overflow via the msb form), keeping the
/// expression inside the evaluator's 128-bit ceiling.
fn native_i128_overflow_bit(kind: CheckedOverflowKind, a: SmtExpr, b: SmtExpr) -> SmtExpr {
    match kind {
        CheckedOverflowKind::Uadd => {
            // Carry out of `a + b`: the wrapped sum is less than an addend.
            bv1(a.clone().bvadd(b).bvult(a))
        }
        CheckedOverflowKind::Usub => {
            // Borrow of `a - b`.
            bv1(a.bvult(b))
        }
        CheckedOverflowKind::Sadd => {
            // Same-sign addends, result sign differs.
            let sum = a.clone().bvadd(b.clone());
            bv1(msb(&a, 128)
                .eq_expr(msb(&b, 128))
                .and_expr(msb(&a, 128).eq_expr(msb(&sum, 128)).not_expr()))
        }
        CheckedOverflowKind::Ssub => {
            // Differing-sign operands, result sign differs from the minuend.
            let diff = a.clone().bvsub(b.clone());
            bv1(msb(&a, 128)
                .eq_expr(msb(&b, 128))
                .not_expr()
                .and_expr(msb(&a, 128).eq_expr(msb(&diff, 128)).not_expr()))
        }
        CheckedOverflowKind::Smul | CheckedOverflowKind::Umul => {
            unreachable!(
                "no checked-i128 mul carry chain exists (mul is the division identity or the \
                 limb check of checked_mul_i128_proofs)"
            )
        }
    }
}

/// MACHINE side of the checked-i128 overflow bit: the final NZCV bit of the
/// flag-setting high-half op (`ADCS`/`SBCS`), rebuilt from 64-bit limb
/// arithmetic, then read by the chain's CSET (HS = C, LO = !C i.e. the
/// borrow, VS = V).
fn carry_chain_i128_overflow_bit(
    kind: CheckedOverflowKind,
    a_lo: SmtExpr,
    a_hi: SmtExpr,
    b_lo: SmtExpr,
    b_hi: SmtExpr,
) -> SmtExpr {
    let one1 = SmtExpr::bv_const(1, 1);
    let zero1 = SmtExpr::bv_const(0, 1);
    match kind {
        CheckedOverflowKind::Uadd => {
            // CSET HS: C of the high-half add-with-carry.
            let c_lo = adc_carry_out_64(a_lo, b_lo, zero1);
            bv1(adc_carry_out_64(a_hi, b_hi, c_lo).eq_expr(one1))
        }
        CheckedOverflowKind::Sadd => {
            // CSET VS: V — the exact 66-bit signed sum of
            // `a_hi + b_hi + c_lo` disagrees with the wrapped 64-bit result.
            // (65 bits cannot hold max_i64 + max_i64 + 1; extend by 2.)
            let c_lo = adc_carry_out_64(a_lo, b_lo, zero1);
            let dst_hi = a_hi
                .clone()
                .bvadd(b_hi.clone())
                .bvadd(c_lo.clone().zero_ext(63));
            let exact = a_hi
                .sign_ext(2)
                .bvadd(b_hi.sign_ext(2))
                .bvadd(c_lo.zero_ext(65));
            bv1(exact.eq_expr(dst_hi.sign_ext(2)).not_expr())
        }
        CheckedOverflowKind::Usub => {
            // CSET LO: C clear, i.e. the high-half borrow-out.
            let br_lo = sbc_borrow_out_64(a_lo, b_lo, zero1);
            bv1(sbc_borrow_out_64(a_hi, b_hi, br_lo).eq_expr(one1))
        }
        CheckedOverflowKind::Ssub => {
            // CSET VS: V — the exact 66-bit signed difference of
            // `a_hi - b_hi - br_lo` disagrees with the wrapped 64-bit result.
            let br_lo = sbc_borrow_out_64(a_lo, b_lo, zero1);
            let dst_hi = a_hi
                .clone()
                .bvsub(b_hi.clone())
                .bvsub(br_lo.clone().zero_ext(63));
            let exact = a_hi
                .sign_ext(2)
                .bvsub(b_hi.sign_ext(2))
                .bvsub(br_lo.zero_ext(65));
            bv1(exact.eq_expr(dst_hi.sign_ext(2)).not_expr())
        }
        CheckedOverflowKind::Smul | CheckedOverflowKind::Umul => {
            unreachable!(
                "no checked-i128 mul carry chain exists (mul is the division identity or the \
                 limb check of checked_mul_i128_proofs)"
            )
        }
    }
}

fn proof_checked_i128_overflow_bit(kind: CheckedOverflowKind, name: &str) -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let b_hi = SmtExpr::var("b_hi", 64);
    let a128 = a_hi.clone().concat(a_lo.clone());
    let b128 = b_hi.clone().concat(b_lo.clone());
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: native_i128_overflow_bit(kind, a128, b128),
        aarch64_expr: carry_chain_i128_overflow_bit(kind, a_lo, a_hi, b_lo, b_hi),
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Prove the `CheckedSadd(I128)` overflow bit: `ADDS lo; ADCS hi; CSET VS`.
pub fn proof_checked_sadd_i128_overflow_bit() -> ProofObligation {
    proof_checked_i128_overflow_bit(
        CheckedOverflowKind::Sadd,
        "CheckedSadd_I128 overflow bit -> ADDS lo; ADCS hi; CSET VS",
    )
}

/// Prove the `CheckedUadd(U128)` overflow bit: `ADDS lo; ADCS hi; CSET HS`.
pub fn proof_checked_uadd_i128_overflow_bit() -> ProofObligation {
    proof_checked_i128_overflow_bit(
        CheckedOverflowKind::Uadd,
        "CheckedUadd_I128 overflow bit -> ADDS lo; ADCS hi; CSET HS",
    )
}

/// Prove the `CheckedSsub(I128)` overflow bit: `SUBS lo; SBCS hi; CSET VS`.
pub fn proof_checked_ssub_i128_overflow_bit() -> ProofObligation {
    proof_checked_i128_overflow_bit(
        CheckedOverflowKind::Ssub,
        "CheckedSsub_I128 overflow bit -> SUBS lo; SBCS hi; CSET VS",
    )
}

/// Prove the `CheckedUsub(U128)` overflow bit: `SUBS lo; SBCS hi; CSET LO`.
pub fn proof_checked_usub_i128_overflow_bit() -> ProofObligation {
    proof_checked_i128_overflow_bit(
        CheckedOverflowKind::Usub,
        "CheckedUsub_I128 overflow bit -> SUBS lo; SBCS hi; CSET LO",
    )
}

/// The four checked-i128 carry-chain OVERFLOW-BIT obligations, one per
/// `Checked{S,U}{add,sub}` at I128. The chain's value half is
/// `proof_iadd/isub_i128_whole_chain`.
pub fn all_checked_i128_carry_chain_proofs() -> Vec<ProofObligation> {
    vec![
        proof_checked_sadd_i128_overflow_bit(),
        proof_checked_uadd_i128_overflow_bit(),
        proof_checked_ssub_i128_overflow_bit(),
        proof_checked_usub_i128_overflow_bit(),
    ]
}

/// Return all #474 checked-overflow lowering proofs.
pub fn all_checked_overflow_proofs() -> Vec<ProofObligation> {
    vec![
        proof_checked_sadd_i64(),
        proof_checked_ssub_i64(),
        proof_checked_smul_i64(),
        proof_checked_uadd_i64(),
        proof_checked_usub_i64(),
        proof_checked_umul_i64(),
    ]
}

/// Width-8 EXHAUSTIVE proof that the genuine SPEC overflow predicate
/// (full 2w-bit signed product != sign-extension of the wrapped w-bit value)
/// is EQUIVALENT to the AArch64 SMULH-high predicate
/// (`SMULH != ASR(value, w-1)`).
///
/// This is the honest mul evidence: it discharges COMPLETELY over all 2^16
/// width-8 inputs (exhaustive) AND formally via ay in ~100-250ms. The overflow
/// predicate is width-uniform — "full 2w-bit product != ext(wrapped w-bit
/// value)" is the SAME theorem at every width w — so an exhaustive width-8
/// discharge witnesses the predicate's shape, while the full 64-bit FORMAL
/// discharge is pending solver capacity (128-bit `bvmul` times out). This is
/// deliberately NOT a 64-bit formal claim.
pub fn exact_smul_flag_equivalence_i8() -> ProofObligation {
    let lhs = SmtExpr::var("a", 8);
    let rhs = SmtExpr::var("b", 8);
    let value = lhs.clone().bvmul(rhs.clone());
    let product = signed_product(lhs, rhs, 8);
    let exact_overflow = product
        .clone()
        .eq_expr(value.clone().sign_ext(8))
        .not_expr();
    let high = product.extract(15, 8);
    let sign = value.bvashr(SmtExpr::bv_const(7, 8));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CheckedSmul_I8 exact product overflow == SMULH high-half predicate (exhaustive w=8)"
            .to_string(),
        trust_ir_expr: bv1(exact_overflow),
        aarch64_expr: bv1(high.eq_expr(sign).not_expr()),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Width-8 EXHAUSTIVE proof that the genuine SPEC unsigned overflow predicate
/// (full 2w-bit unsigned product != zero-extension of the wrapped w-bit value)
/// is EQUIVALENT to the AArch64 UMULH-high predicate (`UMULH != 0`).
///
/// Same honesty contract as [`exact_smul_flag_equivalence_i8`]: exhaustive at
/// width-8 (all 2^16 inputs) and ay-formal at width-8; the 64-bit FORMAL
/// discharge is pending solver capacity. NOT a 64-bit formal claim.
pub fn exact_umul_flag_equivalence_i8() -> ProofObligation {
    let lhs = SmtExpr::var("a", 8);
    let rhs = SmtExpr::var("b", 8);
    let value = lhs.clone().bvmul(rhs.clone());
    let product = unsigned_product(lhs, rhs, 8);
    let exact_overflow = product
        .clone()
        .eq_expr(value.clone().zero_ext(8))
        .not_expr();
    let high = product.extract(15, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CheckedUmul_I8 exact product overflow == UMULH high-half predicate (exhaustive w=8)"
            .to_string(),
        trust_ir_expr: bv1(exact_overflow),
        aarch64_expr: bv1(high.eq_expr(SmtExpr::bv_const(0, 8)).not_expr()),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Return the width-8 EXHAUSTIVE mul-overflow equivalence proofs.
///
/// These are the honest mul evidence cited by the Smulh/Umulh coverage-gate
/// allowlist reason: a genuine overflow-equivalence theorem, exhaustively
/// verified at width-8 (all 2^16 cases) and ay-formal at width-8. The full
/// 64-bit FORMAL discharge of [`proof_checked_smul_i64`] /
/// [`proof_checked_umul_i64`] is pending solver capacity (128-bit `bvmul`),
/// so the 64-bit Smulh/Umulh opcodes stay fail-closed-allowlisted rather than
/// claim a 64-bit formal proof.
pub fn all_checked_overflow_mul_exhaustive_i8_proofs() -> Vec<ProofObligation> {
    vec![
        exact_smul_flag_equivalence_i8(),
        exact_umul_flag_equivalence_i8(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay_cli, z3_available};
    use crate::lowering_proof::verify_by_evaluation;
    use crate::smt::EvalResult;
    use crate::verify::VerificationResult;
    use std::collections::HashMap;

    fn packed(overflow: bool, value: u64) -> EvalResult {
        EvalResult::Bv128(((overflow as u128) << 64) | value as u128)
    }

    fn eval_pair(obligation: &ProofObligation, a: u64, b: u64) -> (EvalResult, EvalResult) {
        let env = HashMap::from([("a".to_string(), a), ("b".to_string(), b)]);
        (
            obligation.trust_ir_expr.eval(&env),
            obligation.aarch64_expr.eval(&env),
        )
    }

    #[test]
    fn test_all_checked_overflow_proofs_count() {
        let proofs = all_checked_overflow_proofs();
        assert_eq!(proofs.len(), 6);
        for proof in proofs {
            assert_eq!(
                proof.inputs,
                vec![("a".to_string(), 64), ("b".to_string(), 64)]
            );
        }
    }

    #[test]
    fn test_checked_overflow_i8_exhaustive_eval() {
        let proofs = [
            proof_checked_overflow_width(
                CheckedOverflowKind::Sadd,
                8,
                "CheckedSadd_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Ssub,
                8,
                "CheckedSsub_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Smul,
                8,
                "CheckedSmul_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Uadd,
                8,
                "CheckedUadd_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Usub,
                8,
                "CheckedUsub_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Umul,
                8,
                "CheckedUmul_I8 exhaustive shape",
            ),
        ];

        for proof in proofs {
            assert!(
                matches!(verify_by_evaluation(&proof), VerificationResult::Valid),
                "{} did not pass exhaustive i8 evaluation",
                proof.name
            );
        }
    }

    /// Formally discharge the i128/u128 checked ADD/SUB overflow predicate via
    /// the AY solver. These are the 128-bit instantiations of the i8/i64-proven
    /// add/sub obligations; unlike i128 MUL (256-bit `bvmul`, which times out)
    /// they are linear-bitvector and discharge, so they are held to the i64
    /// add/sub rows' discipline in `test_checked_overflow_i64_z3_cli`: each
    /// obligation MUST formally Verify. A `CounterExample` means the 128-bit
    /// add/sub overflow lowering is WRONG; a checker or self-check rejection, a
    /// timeout, any other `Unknown` and an `Error` are a failure to produce the
    /// proof. Each fails the test. The only skips are the named, tracked absent
    /// capabilities: no proof authority installed, and AY's disclosed proof
    /// hole (`crate::formal_gap`).
    #[test]
    fn test_checked_overflow_add_sub_i128_formally_discharges() {
        // Every solver-coupled test in this binary serializes on
        // `formal_solver_test_lock`: `verify_with_ay_cli` drives the ONE
        // process-global resident `ay` slot, and the resident-I/O tests in
        // `ay_bridge::subprocess_tests` assert exclusive ownership of that
        // slot under the lock (a fake resident spawned exactly once across
        // two queries, an empty slot after an anomaly). Measured 2026-09-20:
        // with these four tests unlocked, `resident_io_reuses_a_framed_process_
        // with_unlimited_and_huge_budgets` saw `started\nstarted\n` — this
        // test's real `ay` had displaced its fake between its two queries.
        let _solver_lock = crate::ay_bridge::formal_solver_test_lock();
        let proofs = all_checked_overflow_add_sub_i128_proofs();
        assert_eq!(proofs.len(), 4);
        // Non-degeneracy: a spec that is structurally `X == X` proves nothing.
        for proof in &proofs {
            assert_ne!(
                proof.trust_ir_expr, proof.aarch64_expr,
                "DEGENERATE (X==X) i128 overflow proof {:?}",
                proof.name
            );
        }

        if !z3_available() {
            crate::formal_gap::skip_test(
                "test_checked_overflow_add_sub_i128_formally_discharges",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }
        let config = AYConfig::default().with_timeout(120_000);
        for proof in &proofs {
            let result = verify_with_ay_cli(proof, &config);
            if let Some(reason) = crate::formal_gap::disclosed_proof_hole(&result) {
                crate::formal_gap::print_gap_skip(&format!("obligation '{}'", proof.name), &reason);
                continue;
            }
            match result {
                AYResult::Verified => {}
                AYResult::CounterExample(cx) => panic!(
                    "SOUNDNESS: i128 add/sub overflow predicate {:?} REFUTED by {cx:?}",
                    proof.name
                ),
                other => panic!(
                    "{} returned {other}; the i128/u128 add/sub overflow obligations MUST \
                     formally Verify",
                    proof.name
                ),
            }
        }
    }

    /// The four checked-i128 carry-chain OVERFLOW-BIT obligations must be
    /// non-degenerate, EVALUATOR-dischargeable (that is exactly what the
    /// coverage gate runs), and formally dischargeable where the solver
    /// cooperates. The formal attempt follows the 64-bit checked-mul rows'
    /// discipline (`test_checked_overflow_i64_z3_cli`): a `Timeout`, or an
    /// `Unknown` the strict gate files as capacity, is tolerated and printed;
    /// a `CounterExample` is a refutation, and an `Error` or an `Unknown` the
    /// strict gate files as a SOUNDNESS failure
    /// (`proof_gate::unknown_is_hard_failure`: a working checker's rejection
    /// of AY's proof, AY's own self-check rejection, a trusted proof step, an
    /// internal error) is a verdict on a proof, not capacity. Each fails the
    /// test. With no proof authority installed the formal half skips by name.
    #[test]
    fn test_checked_i128_carry_chain_formally_discharges() {
        // Solver-coupled: serialize on the shared resident slot (see
        // `test_checked_overflow_add_sub_i128_formally_discharges`).
        let _solver_lock = crate::ay_bridge::formal_solver_test_lock();
        let proofs = all_checked_i128_carry_chain_proofs();
        assert_eq!(proofs.len(), 4);
        for proof in &proofs {
            assert_ne!(
                proof.trust_ir_expr, proof.aarch64_expr,
                "DEGENERATE (X==X) checked-i128 overflow-bit proof {:?}",
                proof.name
            );
            // The gate's own discharge path: the sampling evaluator must
            // accept every obligation.
            assert!(
                matches!(verify_by_evaluation(proof), VerificationResult::Valid),
                "{} did not pass the default evaluator",
                proof.name
            );
        }

        if !z3_available() {
            crate::formal_gap::skip_test(
                "test_checked_i128_carry_chain_formally_discharges (formal half)",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }
        let config = AYConfig::default().with_timeout(120_000);
        let mut discharged = 0;
        for proof in &proofs {
            let result = verify_with_ay_cli(proof, &config);
            match result {
                AYResult::Verified => discharged += 1,
                AYResult::CounterExample(cx) => panic!(
                    "SOUNDNESS: checked-i128 overflow bit {:?} REFUTED by {cx:?}",
                    proof.name
                ),
                AYResult::Unknown(ref reason)
                    if crate::proof_gate::unknown_is_hard_failure(reason) =>
                {
                    panic!(
                        "{} returned {result}; the strict proof gate files this as a soundness \
                         failure, not capacity",
                        proof.name
                    )
                }
                AYResult::Error(e) => panic!("{} solver error: {e}", proof.name),
                AYResult::SolverUnsat | AYResult::Timeout | AYResult::Unknown(_) => {
                    eprintln!("capacity (not discharged) {:?}: {result}", proof.name)
                }
            }
        }
        eprintln!("checked-i128 overflow bit: {discharged}/4 formally discharged");
    }

    /// Concrete boundary cases for the overflow-bit obligations, evaluated on
    /// BOTH sides: the carry that exists only via the low limb (the exact
    /// miscompile a dropped carry-in would produce) and its negative twin.
    #[test]
    fn test_checked_i128_overflow_bit_boundary_cases() {
        // a = 2^128 - 2^63 (a_hi all-ones, a_lo = 2^63), b = 2^63:
        // a + b = 2^128 -> unsigned carry OUT, and the high-limb C is set
        // ONLY because the low half carries in.
        let carry_env = HashMap::from([
            ("a_lo".to_string(), 1u64 << 63),
            ("a_hi".to_string(), u64::MAX),
            ("b_lo".to_string(), 1u64 << 63),
            ("b_hi".to_string(), 0),
        ]);
        // Same shape minus the low-half carry: no overflow.
        let no_carry_env = HashMap::from([
            ("a_lo".to_string(), 1u64 << 62),
            ("a_hi".to_string(), u64::MAX),
            ("b_lo".to_string(), 1u64 << 62),
            ("b_hi".to_string(), 0),
        ]);
        let uadd = proof_checked_uadd_i128_overflow_bit();
        for (env, expect) in [(&carry_env, 1u64), (&no_carry_env, 0u64)] {
            for (side, expr) in [
                ("spec", &uadd.trust_ir_expr),
                ("machine", &uadd.aarch64_expr),
            ] {
                assert_eq!(
                    expr.eval(env),
                    EvalResult::Bv(expect),
                    "uadd {side} side disagrees on the carry-through-low-limb case"
                );
            }
        }

        // Signed: i128::MAX + 1 overflows; the V is visible only at the
        // high limb WITH the carry-in from the low half.
        let smax_env = HashMap::from([
            ("a_lo".to_string(), u64::MAX),
            ("a_hi".to_string(), i64::MAX as u64),
            ("b_lo".to_string(), 1u64),
            ("b_hi".to_string(), 0),
        ]);
        let sadd = proof_checked_sadd_i128_overflow_bit();
        for (side, expr) in [
            ("spec", &sadd.trust_ir_expr),
            ("machine", &sadd.aarch64_expr),
        ] {
            assert_eq!(
                expr.eval(&smax_env),
                EvalResult::Bv(1),
                "sadd {side} side must see i128::MAX + 1 overflow"
            );
        }

        // Unsigned sub: 0 - 1 borrows; the borrow propagates through the
        // high limb only via the low half.
        let borrow_env = HashMap::from([
            ("a_lo".to_string(), 0u64),
            ("a_hi".to_string(), 0u64),
            ("b_lo".to_string(), 1u64),
            ("b_hi".to_string(), 0u64),
        ]);
        let usub = proof_checked_usub_i128_overflow_bit();
        for (side, expr) in [
            ("spec", &usub.trust_ir_expr),
            ("machine", &usub.aarch64_expr),
        ] {
            assert_eq!(
                expr.eval(&borrow_env),
                EvalResult::Bv(1),
                "usub {side} side must see 0 - 1 borrow"
            );
        }
    }

    /// NEGATIVE CONTROLS: the overflow-bit obligations must REFUTE the two
    /// characteristic miscompiles they exist to catch — a dropped carry-in to
    /// the high limb, and a C/V condition confusion in the CSET. If either
    /// passed, the obligation would be a tautology. Refutation is checked by
    /// the default EVALUATOR (the gate's discharge path) and, where the
    /// solver cooperates, formally.
    #[test]
    fn test_checked_i128_carry_chain_negative_controls_refute() {
        // Solver-coupled: serialize on the shared resident slot (see
        // `test_checked_overflow_add_sub_i128_formally_discharges`).
        let _solver_lock = crate::ay_bridge::formal_solver_test_lock();
        let a_lo = SmtExpr::var("a_lo", 64);
        let a_hi = SmtExpr::var("a_hi", 64);
        let b_lo = SmtExpr::var("b_lo", 64);
        let b_hi = SmtExpr::var("b_hi", 64);
        let one1 = SmtExpr::bv_const(1, 1);
        let zero1 = SmtExpr::bv_const(0, 1);

        // (1) DROPPED CARRY: the high-limb C forgets the low half's carry.
        let dropped_carry =
            bv1(adc_carry_out_64(a_hi.clone(), b_hi.clone(), zero1.clone()).eq_expr(one1.clone()));

        // (2) C/V CONFUSION: the "signed overflow" bit reads the CARRY
        //     (CSET HS where CSET VS belongs).
        let c_lo = adc_carry_out_64(a_lo.clone(), b_lo.clone(), zero1);
        let cv_confused = bv1(adc_carry_out_64(a_hi, b_hi, c_lo).eq_expr(one1));

        // Each control is asserted at the strongest lane that can SEE it.
        // The dropped-carry miscompile diverges only where
        // `a_hi + b_hi == 2^64 - 1` exactly AND the low half carries — a
        // ~2^-64 sliver that neither the 36 edge combos (paired-index edges
        // can never make a_hi + b_hi odd-all-ones) nor random sampling lands
        // on. Evaluation is asserted non-Valid-by-construction only via the
        // DIRECTED point below; refutation is the solver's job — which is
        // exactly why the formal obligation exists. The C/V confusion
        // diverges on huge regions (any carry-only or V-only input), so the
        // evaluator must refute it outright.
        let config = AYConfig::default().with_timeout(120_000);

        for (label, wrong_machine, evaluator_must_refute, kind) in [
            (
                "dropped carry-in",
                dropped_carry,
                false,
                CheckedOverflowKind::Uadd,
            ),
            (
                "CSET HS where VS belongs",
                cv_confused,
                true,
                CheckedOverflowKind::Sadd,
            ),
        ] {
            let correct = match kind {
                CheckedOverflowKind::Uadd => proof_checked_uadd_i128_overflow_bit(),
                CheckedOverflowKind::Sadd => proof_checked_sadd_i128_overflow_bit(),
                _ => unreachable!(),
            };
            let obligation = ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: format!("NEGATIVE: checked-i128 overflow bit, {label}"),
                trust_ir_expr: correct.trust_ir_expr.clone(),
                aarch64_expr: wrong_machine,
                inputs: correct.inputs,
                preconditions: vec![],
                fp_inputs: vec![],
                category: Some(TransvalCheckKind::InstructionLowering),
            };
            if evaluator_must_refute {
                assert!(
                    matches!(
                        verify_by_evaluation(&obligation),
                        VerificationResult::Invalid { .. }
                    ),
                    "TAUTOLOGY: the {label} miscompile was NOT refuted by evaluation — the \
                     checked-i128 overflow-bit obligation proves nothing"
                );
            } else {
                // DIRECTED witness for the sampling-invisible control: the
                // exact boundary where only the low-limb carry sets C.
                let witness = HashMap::from([
                    ("a_lo".to_string(), 1u64 << 63),
                    ("a_hi".to_string(), u64::MAX),
                    ("b_lo".to_string(), 1u64 << 63),
                    ("b_hi".to_string(), 0u64),
                ]);
                assert_ne!(
                    obligation.trust_ir_expr.eval(&witness),
                    obligation.aarch64_expr.eval(&witness),
                    "the {label} miscompile must diverge at the carry-through boundary"
                );
            }
            if !z3_available() {
                crate::formal_gap::skip_test(
                    &format!(
                        "test_checked_i128_carry_chain_negative_controls_refute (formal half, \
                         {label})"
                    ),
                    crate::formal_gap::NO_PROOF_AUTHORITY,
                );
                continue;
            }
            match verify_with_ay_cli(&obligation, &config) {
                AYResult::Verified => panic!(
                    "TAUTOLOGY: the {label} miscompile was formally VERIFIED — the \
                     checked-i128 overflow-bit obligation proves nothing"
                ),
                AYResult::CounterExample(_) => {}
                AYResult::SolverUnsat => panic!(
                    "TAUTOLOGY: AY answered unsat on the {label} miscompile — the \
                     checked-i128 overflow-bit obligation proves nothing"
                ),
                AYResult::Unknown(ref reason)
                    if crate::proof_gate::unknown_is_hard_failure(reason) =>
                {
                    panic!(
                        "the {label} miscompile returned {:?}: AY answered that the \
                         known-wrong lowering is correct and its proof was rejected, which the \
                         strict proof gate files as a soundness failure",
                        reason
                    )
                }
                AYResult::Error(e) => panic!("the {label} miscompile: solver error: {e}"),
                AYResult::Timeout | AYResult::Unknown(_) => eprintln!(
                    "capacity (no formal refutation; the evaluator/witness refutation above \
                     stands) {label}"
                ),
            }
        }
    }

    #[test]
    fn test_checked_mul_exact_overflow_predicates_i8_exhaustive() {
        for proof in all_checked_overflow_mul_exhaustive_i8_proofs() {
            assert!(
                matches!(verify_by_evaluation(&proof), VerificationResult::Valid),
                "{} did not pass exhaustive i8 evaluation",
                proof.name
            );
        }
    }

    /// NON-DEGENERACY (f81e45b / X==X guard): NO checked-overflow proof — the 6
    /// i64 lowering obligations OR the 2 width-8 mul-equivalence proofs — may
    /// have a `trust_ir_expr` that is structurally identical to its
    /// `aarch64_expr`. A degenerate `X == X` obligation discharges trivially and
    /// proves NOTHING; binding such a thing to a coverage row would be a silent
    /// false claim. `SmtExpr: Eq`, so this is a direct structural check.
    #[test]
    fn test_checked_overflow_proofs_are_non_degenerate() {
        let mut proofs = all_checked_overflow_proofs();
        proofs.extend(all_checked_overflow_mul_exhaustive_i8_proofs());
        for proof in proofs {
            assert_ne!(
                proof.trust_ir_expr, proof.aarch64_expr,
                "DEGENERATE (X==X) checked-overflow proof {:?}: trust_ir_expr is \
                 structurally identical to aarch64_expr — it proves nothing",
                proof.name
            );
        }
    }

    #[test]
    fn test_checked_overflow_i64_corner_values() {
        let cases = [
            (
                proof_checked_sadd_i64(),
                i64::MAX as u64,
                1,
                packed(true, i64::MIN as u64),
            ),
            (
                proof_checked_ssub_i64(),
                i64::MIN as u64,
                1,
                packed(true, i64::MAX as u64),
            ),
            (
                proof_checked_smul_i64(),
                i64::MIN as u64,
                u64::MAX,
                packed(true, i64::MIN as u64),
            ),
            (proof_checked_uadd_i64(), u64::MAX, 1, packed(true, 0)),
            (proof_checked_usub_i64(), 0, 1, packed(true, u64::MAX)),
            (
                proof_checked_umul_i64(),
                u64::MAX,
                2,
                packed(true, u64::MAX.wrapping_sub(1)),
            ),
        ];

        for (proof, a, b, expected) in cases {
            let (trust_ir, aarch64) = eval_pair(&proof, a, b);
            assert_eq!(
                trust_ir, expected,
                "{} trust_ir corner mismatch",
                proof.name
            );
            assert_eq!(aarch64, expected, "{} AArch64 corner mismatch", proof.name);
        }
    }

    /// Per-strength discharge of the checked-overflow proofs via AY + Clean:
    ///   - the 4 add/sub i64 obligations FORMALLY verify (and fast);
    ///   - the 2 mul i64 obligations carry a GENUINE (non-degenerate) 64-bit
    ///     equivalence theorem that is SMT-hard (128-bit `bvmul`) and TIMES OUT
    ///     under a bounded budget — a Timeout/Unknown is tolerated (capacity,
    ///     NOT a miscompile), but a CounterExample/Error is a hard fail;
    ///   - the 2 width-8 mul-equivalence proofs FORMALLY verify at width-8,
    ///     anchoring the honest "exhaustively/formally verified at width-8,
    ///     64-bit discharge pending solver capacity" claim.
    ///
    /// This is deliberately NOT a "all 6 i64 -> Verified" assertion: the i64 mul
    /// FORMAL discharge is out of reach and we never claim it.
    #[test]
    fn test_checked_overflow_i64_z3_cli() {
        if !z3_available() {
            eprintln!("skipping checked-overflow SMT proof: z3 not available");
            return;
        }

        // Solver-coupled: serialize on the shared resident slot (see
        // `test_checked_overflow_add_sub_i128_formally_discharges`). The
        // 10 s budget below is this query's SOLVER budget; the resident lane
        // no longer charges it for waiting behind a sibling's window, and
        // holding the lock keeps that wait short as well.
        let _solver_lock = crate::ay_bridge::formal_solver_test_lock();
        let config = AYConfig::default().with_timeout(10_000);

        // add/sub i64: MUST formally verify.
        for proof in [
            proof_checked_sadd_i64(),
            proof_checked_ssub_i64(),
            proof_checked_uadd_i64(),
            proof_checked_usub_i64(),
        ] {
            let result = verify_with_ay_cli(&proof, &config);
            // Certification-gap guard (crate::formal_gap): skip LOUDLY only on
            // AY's disclosed proof hole; anything else still fails the original
            // assertion.
            if let Some(reason) = crate::formal_gap::disclosed_proof_hole(&result) {
                crate::formal_gap::print_gap_skip(&format!("obligation '{}'", proof.name), &reason);
                continue;
            }
            assert!(
                matches!(result, AYResult::Verified),
                "{} returned {}; the add/sub i64 obligations MUST formally Verify",
                proof.name,
                result
            );
        }

        // mul i64: genuine theorem, SMT-hard at 64-bit. Tolerate capacity
        // (Timeout/Unknown); a CounterExample/Error would be a real miscompile.
        // An Unknown the strict proof gate files as a SOUNDNESS failure (a
        // working checker's rejection of AY's proof, AY's own self-check
        // rejection, a trusted proof step, an internal error) is not capacity
        // and fails here too.
        for proof in [proof_checked_smul_i64(), proof_checked_umul_i64()] {
            let result = verify_with_ay_cli(&proof, &config);
            match result {
                AYResult::Unknown(ref reason)
                    if crate::proof_gate::unknown_is_hard_failure(reason) =>
                {
                    panic!(
                        "{} returned {}; the strict proof gate files this as a soundness \
                         failure, not capacity",
                        proof.name, result
                    )
                }
                AYResult::Verified
                | AYResult::SolverUnsat
                | AYResult::Timeout
                | AYResult::Unknown(_) => {}
                AYResult::CounterExample(_) | AYResult::Error(_) => panic!(
                    "{} returned {}; the i64 mul overflow predicate is DISPROVED \
                     (soundness failure), not merely capacity-pending",
                    proof.name, result
                ),
            }
        }

        // width-8 mul-equivalence: MUST formally verify (the honest mul anchor).
        for proof in all_checked_overflow_mul_exhaustive_i8_proofs() {
            let result = verify_with_ay_cli(&proof, &config);
            // Certification-gap guard (crate::formal_gap): same discipline as
            // the add/sub block above.
            if let Some(reason) = crate::formal_gap::disclosed_proof_hole(&result) {
                crate::formal_gap::print_gap_skip(&format!("obligation '{}'", proof.name), &reason);
                continue;
            }
            assert!(
                matches!(result, AYResult::Verified),
                "{} returned {}; the width-8 mul-equivalence anchor MUST formally Verify",
                proof.name,
                result
            );
        }
    }
}
