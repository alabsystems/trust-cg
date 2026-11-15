// trust-cg-verify/checked_mul_i128_proofs.rs - i128/u128 checked-multiply idiom obligations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Proof obligations for the 128-bit checked-multiply idioms the adapter emits
//! for `Inst::Overflow { MulOverflow, I128 | U128 }` (ledger row L04-P10).
//!
//! The adapter (`translate_overflow` in trust-cg-lower) does NOT compute a
//! 256-bit product. On every target the value is the low 128-bit product
//! (`Imul I128`); the flag's expansion is chosen per target (ruling OD-224):
//!
//! ```text
//! value = a * b                                    (Imul I128)
//! AArch64 (and every target but x86-64): a guarded division identity,
//!   u128:  flag = a != 0 && value /u (a == 0 ? 1 : a) != b
//!   i128:  flag = (b != 0 && value /s g != a) || (a == MIN && b == -1)
//!          where g = (b == 0 || (a == MIN && b == -1)) ? 1 : b
//! x86-64: the division-free limb check (LLVM's UMULO limb form),
//!   u128:  core(a, b, value), where with x = x1:x0, y = y1:y0, p1 = hi(p):
//!          core(x, y, p) = hi(x1*y0) != 0 | hi(x0*y1) != 0
//!                        | p1 <u lo(x1*y0) + lo(x0*y1) | (x1 != 0 & y1 != 0)
//!   u128 by a constant C:  other >u floor((2^128 - 1) / C)
//!   i128:  core(|a|, |b|, neg ? -value : value)
//!          | (((value <s 0) ^ neg) & value != 0),   neg = (a <s 0) ^ (b <s 0)
//!          (the magnitudes as I64 mask arithmetic under the masks x1 >>a 63)
//! ```
//!
//! The AArch64 divisions are `__udivti3` / `__divti3` libcalls; the guards
//! keep the divisor non-zero and away from `MIN / -1`. The x86-64 form calls
//! nothing: its products are two `I64` `CheckedUmul`s.
//!
//! Six obligations state the idioms, each with structurally distinct sides
//! so a wrong machine side can refute:
//!
//! * [`proof_imul_i128_low_product_chain`]: SOURCE is the 128-bit `bvmul` of
//!   the two operands; MACHINE is the limb chain the AArch64 ISel selects
//!   (`select_i128_mul`): `lo = a_lo * b_lo`, `hi = UMULH(a_lo, b_lo) +
//!   a_lo * b_hi + a_hi * b_lo` (mod 2^64), with UMULH stated as the high half
//!   of the exact 128-bit limb product. This supersedes the free-variable
//!   UMULH stand-in of `lowering_proof::proof_imul_i128_hi` (which stays
//!   registered for its existing bindings) now that the evaluator computes
//!   128-bit products.
//! * [`proof_checked_umul_i128_overflow_flag`] (AArch64's expansion): SOURCE
//!   is trust-ir's checked multiply semantics — the exact 256-bit product does
//!   not fit in 128 bits, stated as "its high 128 bits are non-zero" and
//!   computed from 64-bit limb products with every intermediate at most 128
//!   bits wide; MACHINE is the guarded `__udivti3` division identity above.
//! * [`proof_checked_smul_i128_overflow_flag`] (AArch64's expansion): SOURCE
//!   is the exact signed product outside `[-2^127, 2^127 - 1]`, computed from
//!   operand magnitudes and the result sign; MACHINE is the guarded `__divti3`
//!   identity above.
//! * [`proof_checked_umul_i128_limb_check_flag`] (x86-64's expansion, OD-224):
//!   the unsigned SOURCE above; MACHINE is the division-free limb check over
//!   the adapter's exact LIR ops (`Imul`, `Ushr` by 64 + `Trunc`, `I64`
//!   `CheckedUmul`, `Iadd`, `Icmp`, `Band`/`Bor`).
//! * [`proof_checked_smul_i128_limb_check_flag`] (x86-64's expansion, OD-224):
//!   the signed SOURCE above; MACHINE is the magnitudes route (`I64` mask
//!   arithmetic under the sign masks, the unsigned core, the sign check).
//! * [`proof_checked_umul_i128_const_limit_flag`] (x86-64's expansion of a
//!   multiply by a constant `C`, OD-224): the unsigned SOURCE above; MACHINE is
//!   `a >u (C == 0 ? 2^128 - 1 : (2^128 - 1) / C)` over a symbolic `C` (the
//!   adapter computes the limit at translation time).
//!
//! Evidence strength: every obligation carries four 64-bit limb inputs and is
//! discharged by the default evaluator — sampled `Statistical(N)` acceptance
//! plus the directed boundary battery of [`checked_mul_i128_credit`], which
//! also checks both sides against Rust's native `checked_mul`/`wrapping_mul`
//! at every battery point. That is regression evidence, not a formal proof;
//! the 128-bit `bvmul`/`bvudiv`/`bvsdiv` terms are outside the strict gate's
//! solver budget (the opt-in external-solver campaign has not been run over
//! them, like the 64-bit `CheckedSmul_I64`/`CheckedUmul_I64` rows). The
//! limb-check rows drop the division but keep the 128-bit `bvmul` of the value
//! (`Imul I128`) and the source's exact limb products (OD-224 records the AY
//! attempt on them). The x86-64
//! expansion's own scaled analogs are swept exhaustively (8 bits with 4-bit
//! limbs, 16 bits with 8-bit limbs) over the adapter's actual output by
//! `trust-cg-lower`'s `adapter_i128_mulo_tests`: evidence for those widths
//! only, never for the 128-bit circuit.
//!
//! The coverage gate credits the `Umulh` row only when
//! [`checked_mul_i128_credit`] holds: every obligation is non-degenerate and
//! discharges, both sides agree with the native oracle on the battery, and
//! EVERY negative control ([`checked_mul_i128_controls`]) refutes — at its
//! directed witness, and under the sampling evaluator when it is
//! sampling-visible. A control that survives makes the hook refuse. The
//! limb-check controls are the OD-224 design's mutants (a dropped carry, a
//! signed carry compare, a dropped both-high test, the signed/unsigned swaps,
//! a dropped zero guard, ...), each at its replayed 128-bit counterexample.
//!
//! What this does NOT establish — the named deferrals in
//! [`CHECKED_MUL_I128_DEFERRALS`]: the machine side is the LIR expansion the
//! adapter emits, stated over the ISel limb chain, not the Arm ARM semantics
//! of independently decoded captured encoder words (the `aarch64_value_decode_proofs`
//! form); the `__udivti3`/`__divti3` libcalls of the AArch64 expansion are
//! assumed to implement unsigned/signed 128-bit truncating division (no
//! obligation covers the runtime); and the per-compile function verifier
//! still binds an emitted UMULH to the 64-bit `CheckedUmul_I64` obligation,
//! not to this chain. The x86-64 expansion's selection is the x86-64 body
//! theorem's business (`x86_source_bound_body`), not this family's.

use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, TransvalCheckKind, VerificationConfig,
    verify_by_evaluation_with_config,
};
use crate::smt::{EvalResult, SmtExpr};
use crate::verify::VerificationResult;
use std::collections::HashMap;

/// Which obligation of the family a control mutates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckedMulI128Form {
    /// The low 128-bit product chain (`Imul I128`).
    LowProductChain,
    /// The unsigned overflow flag (`CheckedUmul` at U128): AArch64's guarded
    /// `__udivti3` division identity.
    UnsignedFlag,
    /// The signed overflow flag (`CheckedSmul` at I128): AArch64's guarded
    /// `__divti3` division identity.
    SignedFlag,
    /// The unsigned overflow flag: x86-64's division-free limb check (OD-224).
    UnsignedFlagLimbCheck,
    /// The signed overflow flag: x86-64's division-free magnitudes route
    /// (OD-224).
    SignedFlagLimbCheck,
    /// The unsigned overflow flag of a multiply by a constant: x86-64's
    /// compare of the other operand with the constant's limit (OD-224).
    UnsignedFlagConstLimit,
}

impl CheckedMulI128Form {
    /// Every form, in registration order.
    pub const ALL: [Self; 6] = [
        Self::LowProductChain,
        Self::UnsignedFlag,
        Self::SignedFlag,
        Self::UnsignedFlagLimbCheck,
        Self::SignedFlagLimbCheck,
        Self::UnsignedFlagConstLimit,
    ];

    /// The registered obligation of this form.
    pub fn obligation(self) -> ProofObligation {
        match self {
            Self::LowProductChain => proof_imul_i128_low_product_chain(),
            Self::UnsignedFlag => proof_checked_umul_i128_overflow_flag(),
            Self::SignedFlag => proof_checked_smul_i128_overflow_flag(),
            Self::UnsignedFlagLimbCheck => proof_checked_umul_i128_limb_check_flag(),
            Self::SignedFlagLimbCheck => proof_checked_smul_i128_limb_check_flag(),
            Self::UnsignedFlagConstLimit => proof_checked_umul_i128_const_limit_flag(),
        }
    }

    /// The lower-case name query the coverage gate resolves this form with;
    /// a unique substring of the registered name.
    pub const fn query(self) -> &'static str {
        match self {
            Self::LowProductChain => "imul_i128 low-product chain",
            Self::UnsignedFlag => "checkedumul_i128 overflow flag -> guarded __udivti3",
            Self::SignedFlag => "checkedsmul_i128 overflow flag -> guarded __divti3",
            Self::UnsignedFlagLimbCheck => "checkedumul_i128 overflow flag -> division-free",
            Self::SignedFlagLimbCheck => "checkedsmul_i128 overflow flag -> division-free",
            Self::UnsignedFlagConstLimit => "checkedumul_i128 overflow flag -> constant-operand",
        }
    }

    /// Whether this form states an unsigned flag, a signed flag, or neither
    /// (the low-product chain).
    pub const fn flag_sign(self) -> Option<bool> {
        match self {
            Self::LowProductChain => None,
            Self::UnsignedFlag | Self::UnsignedFlagLimbCheck | Self::UnsignedFlagConstLimit => {
                Some(false)
            }
            Self::SignedFlag | Self::SignedFlagLimbCheck => Some(true),
        }
    }
}

/// What the family deliberately does not claim.
pub const CHECKED_MUL_I128_DEFERRALS: &[&str] = &[
    "decoded-word machine side: the MUL/UMULH/MADD chain and the CMP/CSEL/AND/ORR flag logic are \
     stated over the ISel limb chain, not decoded from captured encoder words \
     (aarch64_value_decode_proofs form); a wrong register choice encodes and decodes perfectly",
    "runtime division: __udivti3 / __divti3 (the AArch64 expansion's) are assumed to implement \
     truncating unsigned / signed 128-bit division on the guarded operands; no obligation covers \
     the runtime library (the x86-64 limb check calls no routine, OD-224)",
    "per-compile binding: FunctionVerifier::opcode_to_proof_query still binds an emitted UMULH \
     to CheckedUmul_I64; the i128 chain is credited at the coverage-gate row, not per instance",
];

const LIMB: u32 = 64;

fn bv1(cond: SmtExpr) -> SmtExpr {
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

fn one1() -> SmtExpr {
    SmtExpr::bv_const(1, 1)
}

fn zero128() -> SmtExpr {
    SmtExpr::bv_const(0, LIMB).concat(SmtExpr::bv_const(0, LIMB))
}

fn one128() -> SmtExpr {
    SmtExpr::bv_const(0, LIMB).concat(SmtExpr::bv_const(1, LIMB))
}

/// `2^127` as a 128-bit constant (the `i128::MIN` pattern).
fn min128() -> SmtExpr {
    SmtExpr::bv_const(1 << 63, LIMB).concat(SmtExpr::bv_const(0, LIMB))
}

/// `2^127 - 1` as a 128-bit constant (`i128::MAX`).
fn max128() -> SmtExpr {
    SmtExpr::bv_const(i64::MAX as u64, LIMB).concat(SmtExpr::bv_const(u64::MAX, LIMB))
}

fn all_ones128() -> SmtExpr {
    SmtExpr::bv_const(u64::MAX, LIMB).concat(SmtExpr::bv_const(u64::MAX, LIMB))
}

/// The four limb inputs and their 128-bit compositions.
struct Limbs {
    a_lo: SmtExpr,
    a_hi: SmtExpr,
    b_lo: SmtExpr,
    b_hi: SmtExpr,
    a: SmtExpr,
    b: SmtExpr,
}

fn limbs() -> Limbs {
    let a_lo = SmtExpr::var("a_lo", LIMB);
    let a_hi = SmtExpr::var("a_hi", LIMB);
    let b_lo = SmtExpr::var("b_lo", LIMB);
    let b_hi = SmtExpr::var("b_hi", LIMB);
    let a = a_hi.clone().concat(a_lo.clone());
    let b = b_hi.clone().concat(b_lo.clone());
    Limbs {
        a_lo,
        a_hi,
        b_lo,
        b_hi,
        a,
        b,
    }
}

fn limb_inputs() -> Vec<(String, u32)> {
    vec![
        ("a_lo".to_string(), LIMB),
        ("a_hi".to_string(), LIMB),
        ("b_lo".to_string(), LIMB),
        ("b_hi".to_string(), LIMB),
    ]
}

/// Exact 128-bit unsigned product of two 64-bit limbs.
fn limb_product(x: SmtExpr, y: SmtExpr) -> SmtExpr {
    x.zero_ext(LIMB).bvmul(y.zero_ext(LIMB))
}

fn high64(x: SmtExpr) -> SmtExpr {
    x.extract(127, 64)
}

fn low64(x: SmtExpr) -> SmtExpr {
    x.extract(63, 0)
}

/// The high 128 bits of the exact 256-bit product `(a_hi:a_lo) * (b_hi:b_lo)`,
/// computed from the four 64x64 limb products with every intermediate at
/// most 128 bits wide (the evaluator's ceiling).
///
/// With `p00 = a_lo*b_lo`, `p01 = a_lo*b_hi`, `p10 = a_hi*b_lo`,
/// `p11 = a_hi*b_hi` (each exact in 128 bits):
///
/// ```text
/// mid1  = high64(p00) + p01          <= 2^128 - 2^64: never wraps
/// mid2  = mid1 + p10                 wraps at most once; carry = mid2 <u mid1
/// high  = high64(mid2) + p11 + (carry << 64)
/// ```
///
/// which is exact because the full product is
/// `low64(p00) + 2^64 * low64(mid2) + 2^128 * (high64(mid2) + carry*2^64 + p11)`
/// and the last factor is below `2^128`.
fn exact_high128_unsigned(a_lo: SmtExpr, a_hi: SmtExpr, b_lo: SmtExpr, b_hi: SmtExpr) -> SmtExpr {
    let p00 = limb_product(a_lo.clone(), b_lo.clone());
    let p01 = limb_product(a_lo, b_hi.clone());
    let p10 = limb_product(a_hi.clone(), b_lo);
    let p11 = limb_product(a_hi, b_hi);
    let mid1 = high64(p00).zero_ext(LIMB).bvadd(p01);
    let mid2 = mid1.clone().bvadd(p10);
    let carry = bv1(mid2.clone().bvult(mid1));
    let carry_term = carry
        .zero_ext(127)
        .bvshl(SmtExpr::bv_const(64, LIMB).zero_ext(LIMB));
    high64(mid2).zero_ext(LIMB).bvadd(p11).bvadd(carry_term)
}

/// SOURCE of the unsigned flag: trust-ir's `u128` checked multiply overflows
/// iff the exact product's high 128 bits are non-zero.
fn source_umul_i128_flag(l: &Limbs) -> SmtExpr {
    let high = exact_high128_unsigned(
        l.a_lo.clone(),
        l.a_hi.clone(),
        l.b_lo.clone(),
        l.b_hi.clone(),
    );
    bv1(high.eq_expr(zero128()).not_expr())
}

/// MACHINE of the unsigned flag: the guarded `__udivti3` division identity
/// `build_u128_mul_overflow` emits.
fn machine_umul_i128_flag(l: &Limbs) -> SmtExpr {
    let product = l.a.clone().bvmul(l.b.clone());
    let a_is_zero = l.a.clone().eq_expr(zero128());
    let safe_a = SmtExpr::ite(a_is_zero.clone(), one128(), l.a.clone());
    let q = product.bvudiv(safe_a);
    bv1(a_is_zero
        .not_expr()
        .and_expr(q.eq_expr(l.b.clone()).not_expr()))
}

/// SOURCE of the signed flag: trust-ir's `i128` checked multiply overflows iff
/// the exact signed product lies outside `[-2^127, 2^127 - 1]`. Stated over
/// operand magnitudes: with `m = |a| * |b|` exact (`high:low`, each 128 bits)
/// and the result negative iff exactly one operand is negative, overflow iff
/// `high != 0`, or `low > 2^127 - 1` for a non-negative result, or
/// `low > 2^127` for a negative one. `|i128::MIN| = 2^127` fits a `u128`.
fn source_smul_i128_flag(l: &Limbs) -> SmtExpr {
    let a_neg = l.a.clone().extract(127, 127).eq_expr(one1());
    let b_neg = l.b.clone().extract(127, 127).eq_expr(one1());
    let mag_a = SmtExpr::ite(a_neg.clone(), l.a.clone().bvneg(), l.a.clone());
    let mag_b = SmtExpr::ite(b_neg.clone(), l.b.clone().bvneg(), l.b.clone());
    let high = exact_high128_unsigned(
        low64(mag_a.clone()),
        high64(mag_a.clone()),
        low64(mag_b.clone()),
        high64(mag_b.clone()),
    );
    let low = mag_a.bvmul(mag_b);
    // Exactly one operand negative: a XOR b on the sign.
    let negative = a_neg.clone().eq_expr(b_neg).not_expr();
    let limit = SmtExpr::ite(negative, min128(), max128());
    bv1(high.eq_expr(zero128()).not_expr().or_expr(low.bvugt(limit)))
}

/// MACHINE of the signed flag: the guarded `__divti3` division identity
/// `build_i128_signed_mul_overflow` emits.
fn machine_smul_i128_flag(l: &Limbs) -> SmtExpr {
    let product = l.a.clone().bvmul(l.b.clone());
    let b_is_zero = l.b.clone().eq_expr(zero128());
    let a_is_min = l.a.clone().eq_expr(min128());
    let b_is_neg1 = l.b.clone().eq_expr(all_ones128());
    let min_neg1 = a_is_min.and_expr(b_is_neg1);
    let avoid_div = b_is_zero.clone().or_expr(min_neg1.clone());
    let safe_b = SmtExpr::ite(avoid_div, one128(), l.b.clone());
    let q = product.bvsdiv(safe_b);
    let div_ovf = b_is_zero
        .not_expr()
        .and_expr(q.eq_expr(l.a.clone()).not_expr());
    bv1(div_ovf.or_expr(min_neg1))
}

/// MACHINE of the low product: the `MUL; UMULH; MADD; MADD` limb chain
/// `select_i128_mul` emits, as the 128-bit pair `hi:lo`.
fn machine_imul_i128_chain(l: &Limbs) -> SmtExpr {
    let lo = l.a_lo.clone().bvmul(l.b_lo.clone());
    let umulh = high64(limb_product(l.a_lo.clone(), l.b_lo.clone()));
    // t1 = MADD a_lo, b_hi, t0  =>  t0 + a_lo * b_hi
    let t1 = umulh.bvadd(l.a_lo.clone().bvmul(l.b_hi.clone()));
    // hi = MADD a_hi, b_lo, t1  =>  t1 + a_hi * b_lo
    let hi = t1.bvadd(l.a_hi.clone().bvmul(l.b_lo.clone()));
    hi.concat(lo)
}

/// `Iconst{I128, 64}`: the shift amount of a limb split.
fn sixty_four128() -> SmtExpr {
    SmtExpr::bv_const(0, LIMB).concat(SmtExpr::bv_const(64, LIMB))
}

/// `Trunc{I64}(Ushr(x, Iconst{I128, 64}))`: the high limb as the adapter
/// spells it (`push_i128_high_limb`).
fn high_limb(x: SmtExpr) -> SmtExpr {
    x.bvlshr(sixty_four128()).extract(63, 0)
}

/// `I64` `CheckedUmul x, y`: `[low, overflow]`, the overflow "the exact
/// 128-bit product's high half is non-zero" (the LIR's definition).
fn checked_umul64(x: SmtExpr, y: SmtExpr) -> (SmtExpr, SmtExpr) {
    let p = limb_product(x, y);
    (
        low64(p.clone()),
        high64(p).eq_expr(SmtExpr::bv_const(0, LIMB)).not_expr(),
    )
}

/// `I64` `CheckedSmul x, y` (the `smul_cross` control only): the low half of
/// the signed product and "it does not fit 64 signed bits".
fn checked_smul64(x: SmtExpr, y: SmtExpr) -> (SmtExpr, SmtExpr) {
    let p = x.sign_ext(LIMB).bvmul(y.sign_ext(LIMB));
    let low = low64(p.clone());
    (low.clone(), p.eq_expr(low.sign_ext(LIMB)).not_expr())
}

/// The x86-64 expansion's unsigned core (`push_u128_mulo_core`, OD-224) as a
/// Bool, over the limbs: `x * y >= 2^128` given `x = x1:x0`, `y = y1:y0` and
/// `p1 = hi(x * y mod 2^128)`. `mutant` names one of the design's mutants
/// (`None` is the real expansion).
fn limb_check_core(
    [x0, x1]: [SmtExpr; 2],
    [y0, y1]: [SmtExpr; 2],
    p1: SmtExpr,
    mutant: Option<&str>,
) -> SmtExpr {
    let mul = if mutant == Some("smul_cross") {
        checked_smul64
    } else {
        checked_umul64
    };
    let (m1, o1) = mul(x1.clone(), y0);
    let (m2, o2) = mul(x0, y1.clone());
    let t = m1.bvadd(m2);
    let carry = match mutant {
        Some("carry_signed") => p1.bvslt(t),
        Some("carry_ule") => p1.bvule(t),
        _ => p1.bvult(t),
    };
    let zero = SmtExpr::bv_const(0, LIMB);
    let both = x1
        .eq_expr(zero.clone())
        .not_expr()
        .and_expr(y1.eq_expr(zero).not_expr());
    let terms = [("o1", o1), ("o2", o2), ("c", carry), ("both", both)];
    let dropped = match mutant {
        Some("drop_o1") => Some("o1"),
        Some("drop_o2") => Some("o2"),
        Some("drop_carry") => Some("c"),
        Some("drop_both") => Some("both"),
        _ => None,
    };
    terms
        .into_iter()
        .filter(|(name, _)| Some(*name) != dropped)
        .map(|(_, term)| term)
        .reduce(SmtExpr::or_expr)
        .expect("at least three terms remain")
}

/// The two limbs `[lo, hi]` of a 128-bit value as the adapter splits it
/// (`Trunc`, `Trunc(Ushr(x, 64))`).
fn limbs_of_expr(x: SmtExpr) -> [SmtExpr; 2] {
    [low64(x.clone()), high_limb(x)]
}

/// MACHINE of the x86-64 unsigned flag (`build_u128_mul_overflow_divfree`):
/// the core of `(a, b)` and the high limb of `a * b`.
fn machine_umul_i128_limb_check(l: &Limbs, mutant: Option<&str>) -> SmtExpr {
    let product = l.a.clone().bvmul(l.b.clone());
    bv1(limb_check_core(
        limbs_of_expr(l.a.clone()),
        limbs_of_expr(l.b.clone()),
        high_limb(product),
        mutant,
    ))
}

/// `(x1 ^ m) - m - (((x0 | (0 - x0)) >> 63) & m)`: the high limb of `m ? -x :
/// x` (`push_masked_negation_high`).
fn masked_negation_high([x0, x1]: [SmtExpr; 2], m: SmtExpr) -> SmtExpr {
    let k63 = SmtExpr::bv_const(63, LIMB);
    let negated = SmtExpr::bv_const(0, LIMB).bvsub(x0.clone());
    let nonzero = x0.bvor(negated).bvlshr(k63);
    let borrow = nonzero.bvand(m.clone());
    x1.bvxor(m.clone()).bvsub(m).bvsub(borrow)
}

/// The limbs of `m ? -x : x` (`push_magnitude_limbs`).
fn magnitude_limbs(x: [SmtExpr; 2], m: SmtExpr) -> [SmtExpr; 2] {
    let low = x[0].clone().bvxor(m.clone()).bvsub(m.clone());
    [low, masked_negation_high(x, m)]
}

/// MACHINE of the x86-64 signed flag (`build_i128_signed_mul_overflow_divfree`):
/// the core on the magnitudes (`I64` mask arithmetic under the sign masks
/// `x1 >>a 63`) plus the sign check, as the adapter emits them.
fn machine_smul_i128_limb_check(l: &Limbs, mutant: Option<&str>) -> SmtExpr {
    let zero = SmtExpr::bv_const(0, LIMB);
    let k63 = SmtExpr::bv_const(63, LIMB);
    let product = l.a.clone().bvmul(l.b.clone());
    let a = limbs_of_expr(l.a.clone());
    let b = limbs_of_expr(l.b.clone());
    let r = limbs_of_expr(product);
    let ma = a[1].clone().bvashr(k63.clone());
    let mb = b[1].clone().bvashr(k63.clone());
    let raw = mutant == Some("unsigned_core_raw");
    let (ua, ub) = if raw {
        (a.clone(), b.clone())
    } else {
        (
            magnitude_limbs(a, ma.clone()),
            magnitude_limbs(b, mb.clone()),
        )
    };
    let mn = if mutant == Some("neg_or") {
        ma.bvor(mb)
    } else {
        ma.bvxor(mb)
    };
    let pu1 = if raw || mutant == Some("pu_eq_r") {
        r[1].clone()
    } else {
        masked_negation_high(r.clone(), mn.clone())
    };
    let ou = limb_check_core(ua, ub, pu1, None);
    let sign = r[1]
        .clone()
        .bvashr(k63)
        .bvxor(mn)
        .eq_expr(zero.clone())
        .not_expr();
    let r_nz = r[0].clone().bvor(r[1].clone()).eq_expr(zero).not_expr();
    let bad = if mutant == Some("no_zero_guard") {
        sign
    } else {
        sign.and_expr(r_nz)
    };
    bv1(match mutant {
        Some("no_sign_check") => ou,
        Some("no_ou") => bad,
        _ => ou.or_expr(bad),
    })
}

/// MACHINE of the x86-64 unsigned flag of a multiply by a constant (OD-224):
/// the other operand compared with the constant's limit, `a >u (b == 0 ?
/// 2^128 - 1 : (2^128 - 1) / b)`, stated over a symbolic `b` (the adapter
/// computes the limit at translation time). `mutant` names a control.
fn machine_umul_i128_const_limit(l: &Limbs, mutant: Option<&str>) -> SmtExpr {
    let divisor = if mutant == Some("divisor_low_limb") {
        SmtExpr::bv_const(0, LIMB).concat(l.b_lo.clone())
    } else {
        l.b.clone()
    };
    let limit = SmtExpr::ite(
        divisor.clone().eq_expr(zero128()),
        all_ones128(),
        all_ones128().bvudiv(divisor),
    );
    let limit = if mutant == Some("limit_plus_one") {
        limit.bvadd(one128())
    } else {
        limit
    };
    bv1(match mutant {
        Some("uge_for_ugt") => l.a.clone().bvuge(limit),
        Some("sgt_for_ugt") => l.a.clone().bvsgt(limit),
        _ => l.a.clone().bvugt(limit),
    })
}

fn obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: limb_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// `Imul I128`: the 128-bit product equals the `MUL; UMULH; MADD; MADD` limb
/// chain, with UMULH as the exact high half of the low-limb product.
pub fn proof_imul_i128_low_product_chain() -> ProofObligation {
    let l = limbs();
    obligation(
        "Imul_I128 low-product chain -> MUL+UMULH+MADD+MADD (128-bit product vs limb chain)",
        l.a.clone().bvmul(l.b.clone()),
        machine_imul_i128_chain(&l),
    )
}

/// `CheckedUmul` at U128: the overflow flag of the guarded `__udivti3`
/// division identity equals "the exact 256-bit product has a non-zero high
/// 128 bits".
pub fn proof_checked_umul_i128_overflow_flag() -> ProofObligation {
    let l = limbs();
    obligation(
        "CheckedUmul_I128 overflow flag -> guarded __udivti3 division identity (exact 256-bit \
         product high half)",
        source_umul_i128_flag(&l),
        machine_umul_i128_flag(&l),
    )
}

/// `CheckedSmul` at I128: the overflow flag of the guarded `__divti3`
/// division identity equals "the exact signed product is outside
/// `[-2^127, 2^127 - 1]`".
pub fn proof_checked_smul_i128_overflow_flag() -> ProofObligation {
    let l = limbs();
    obligation(
        "CheckedSmul_I128 overflow flag -> guarded __divti3 division identity (exact 256-bit \
         signed product)",
        source_smul_i128_flag(&l),
        machine_smul_i128_flag(&l),
    )
}

/// `CheckedUmul` at U128 on x86-64 (OD-224): the overflow flag of the
/// division-free limb check equals "the exact 256-bit product has a non-zero
/// high 128 bits".
pub fn proof_checked_umul_i128_limb_check_flag() -> ProofObligation {
    let l = limbs();
    obligation(
        "CheckedUmul_I128 overflow flag -> division-free limb check (x86-64: two I64 \
         CheckedUmul + carry + both-high test; exact 256-bit product high half)",
        source_umul_i128_flag(&l),
        machine_umul_i128_limb_check(&l, None),
    )
}

/// `CheckedSmul` at I128 on x86-64 (OD-224): the overflow flag of the
/// division-free magnitudes route equals "the exact signed product is outside
/// `[-2^127, 2^127 - 1]`".
pub fn proof_checked_smul_i128_limb_check_flag() -> ProofObligation {
    let l = limbs();
    obligation(
        "CheckedSmul_I128 overflow flag -> division-free limb check on the magnitudes (x86-64: \
         unsigned core + sign check; exact 256-bit signed product)",
        source_smul_i128_flag(&l),
        machine_smul_i128_limb_check(&l, None),
    )
}

/// `CheckedUmul` at U128 with a constant operand on x86-64 (OD-224): the
/// compare of the other operand with the constant's limit equals "the exact
/// 256-bit product has a non-zero high 128 bits", over a symbolic constant.
pub fn proof_checked_umul_i128_const_limit_flag() -> ProofObligation {
    let l = limbs();
    obligation(
        "CheckedUmul_I128 overflow flag -> constant-operand limit compare (x86-64: the other \
         operand >u (2^128 - 1) / C; exact 256-bit product high half)",
        source_umul_i128_flag(&l),
        machine_umul_i128_const_limit(&l, None),
    )
}

/// The six obligations of the family, in registration order.
pub fn all_checked_mul_i128_proofs() -> Vec<ProofObligation> {
    CheckedMulI128Form::ALL
        .iter()
        .map(|form| form.obligation())
        .collect()
}

/// A wrong machine side the family must refute.
#[derive(Clone)]
pub struct CheckedMulI128Control {
    /// The obligation whose machine side is replaced.
    pub form: CheckedMulI128Form,
    /// The miscompile this control stands for.
    pub label: &'static str,
    /// The wrong machine side.
    pub machine: fn() -> SmtExpr,
    /// `(a_lo, a_hi, b_lo, b_hi)` at which the wrong side diverges from the
    /// source side.
    pub witness: [u64; 4],
    /// Whether the default sampling evaluator (edge battery plus random
    /// limbs) must ALSO refute it. A control that diverges only on a sliver
    /// the sampler cannot reach is refuted by its directed witness alone.
    pub sampling_visible: bool,
}

impl std::fmt::Debug for CheckedMulI128Control {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CheckedMulI128Control")
            .field("form", &self.form)
            .field("label", &self.label)
            .field("witness", &self.witness)
            .field("sampling_visible", &self.sampling_visible)
            .finish()
    }
}

fn control_chain_wrong_cross_limb() -> SmtExpr {
    // hi = UMULH + a_lo*b_hi + a_hi*b_HI: the second MADD reads the wrong limb.
    let l = limbs();
    let lo = l.a_lo.clone().bvmul(l.b_lo.clone());
    let umulh = high64(limb_product(l.a_lo.clone(), l.b_lo.clone()));
    let t1 = umulh.bvadd(l.a_lo.bvmul(l.b_hi.clone()));
    let hi = t1.bvadd(l.a_hi.bvmul(l.b_hi));
    hi.concat(lo)
}

fn control_chain_dropped_umulh() -> SmtExpr {
    // hi = a_lo*b_hi + a_hi*b_lo: the low-limb carry (UMULH) is dropped.
    let l = limbs();
    let lo = l.a_lo.clone().bvmul(l.b_lo.clone());
    let hi = l.a_lo.bvmul(l.b_hi).bvadd(l.a_hi.bvmul(l.b_lo));
    hi.concat(lo)
}

fn control_umul_guard_dropped() -> SmtExpr {
    // flag = value /u safe_a != b without the `a != 0` conjunct.
    let l = limbs();
    let product = l.a.clone().bvmul(l.b.clone());
    let safe_a = SmtExpr::ite(l.a.clone().eq_expr(zero128()), one128(), l.a);
    bv1(product.bvudiv(safe_a).eq_expr(l.b).not_expr())
}

fn control_umul_wrong_operand() -> SmtExpr {
    // flag = a != 0 && value /u safe_a != A: the quotient is compared with the
    // divisor's operand instead of the other factor.
    let l = limbs();
    let product = l.a.clone().bvmul(l.b);
    let a_is_zero = l.a.clone().eq_expr(zero128());
    let safe_a = SmtExpr::ite(a_is_zero.clone(), one128(), l.a.clone());
    bv1(a_is_zero
        .not_expr()
        .and_expr(product.bvudiv(safe_a).eq_expr(l.a).not_expr()))
}

fn control_umul_low_limb_idiom() -> SmtExpr {
    // flag = UMULH(a_lo, b_lo) != 0: the 64-bit idiom misapplied to the low
    // limbs, blind to the high limbs.
    let l = limbs();
    bv1(high64(limb_product(l.a_lo, l.b_lo))
        .eq_expr(SmtExpr::bv_const(0, LIMB))
        .not_expr())
}

fn control_smul_min_neg1_dropped() -> SmtExpr {
    // flag = b != 0 && value /s g != a with g guarding only b == 0.
    let l = limbs();
    let product = l.a.clone().bvmul(l.b.clone());
    let b_is_zero = l.b.clone().eq_expr(zero128());
    let safe_b = SmtExpr::ite(b_is_zero.clone(), one128(), l.b);
    bv1(b_is_zero
        .not_expr()
        .and_expr(product.bvsdiv(safe_b).eq_expr(l.a).not_expr()))
}

fn control_smul_unsigned_division() -> SmtExpr {
    // The signed identity with `__udivti3` where `__divti3` belongs.
    let l = limbs();
    let product = l.a.clone().bvmul(l.b.clone());
    let b_is_zero = l.b.clone().eq_expr(zero128());
    let a_is_min = l.a.clone().eq_expr(min128());
    let b_is_neg1 = l.b.clone().eq_expr(all_ones128());
    let min_neg1 = a_is_min.and_expr(b_is_neg1);
    let avoid_div = b_is_zero.clone().or_expr(min_neg1.clone());
    let safe_b = SmtExpr::ite(avoid_div, one128(), l.b);
    let div_ovf = b_is_zero
        .not_expr()
        .and_expr(product.bvudiv(safe_b).eq_expr(l.a).not_expr());
    bv1(div_ovf.or_expr(min_neg1))
}

fn control_smul_wrong_operand() -> SmtExpr {
    // The quotient is compared with b (the divisor's operand) instead of a.
    let l = limbs();
    let product = l.a.clone().bvmul(l.b.clone());
    let b_is_zero = l.b.clone().eq_expr(zero128());
    let a_is_min = l.a.eq_expr(min128());
    let b_is_neg1 = l.b.clone().eq_expr(all_ones128());
    let min_neg1 = a_is_min.and_expr(b_is_neg1);
    let avoid_div = b_is_zero.clone().or_expr(min_neg1.clone());
    let safe_b = SmtExpr::ite(avoid_div, one128(), l.b.clone());
    let div_ovf = b_is_zero
        .not_expr()
        .and_expr(product.bvsdiv(safe_b).eq_expr(l.b).not_expr());
    bv1(div_ovf.or_expr(min_neg1))
}

/// The OD-224 design's mutants of the x86-64 limb check (its `lir_model.py`
/// spellings), one machine side each.
macro_rules! limb_check_control {
    ($name:ident, $machine:ident, $mutant:literal) => {
        fn $name() -> SmtExpr {
            $machine(&limbs(), Some($mutant))
        }
    };
}
limb_check_control!(
    control_lc_drop_carry,
    machine_umul_i128_limb_check,
    "drop_carry"
);
limb_check_control!(
    control_lc_drop_both,
    machine_umul_i128_limb_check,
    "drop_both"
);
limb_check_control!(control_lc_drop_o1, machine_umul_i128_limb_check, "drop_o1");
limb_check_control!(control_lc_drop_o2, machine_umul_i128_limb_check, "drop_o2");
limb_check_control!(
    control_lc_carry_signed,
    machine_umul_i128_limb_check,
    "carry_signed"
);
limb_check_control!(
    control_lc_carry_ule,
    machine_umul_i128_limb_check,
    "carry_ule"
);
limb_check_control!(
    control_lc_smul_cross,
    machine_umul_i128_limb_check,
    "smul_cross"
);
limb_check_control!(
    control_lc_no_zero_guard,
    machine_smul_i128_limb_check,
    "no_zero_guard"
);
limb_check_control!(
    control_lc_no_sign_check,
    machine_smul_i128_limb_check,
    "no_sign_check"
);
limb_check_control!(control_lc_no_ou, machine_smul_i128_limb_check, "no_ou");
limb_check_control!(control_lc_neg_or, machine_smul_i128_limb_check, "neg_or");
limb_check_control!(control_lc_pu_eq_r, machine_smul_i128_limb_check, "pu_eq_r");
limb_check_control!(
    control_lc_unsigned_core_raw,
    machine_smul_i128_limb_check,
    "unsigned_core_raw"
);

limb_check_control!(
    control_cl_uge_for_ugt,
    machine_umul_i128_const_limit,
    "uge_for_ugt"
);
limb_check_control!(
    control_cl_limit_plus_one,
    machine_umul_i128_const_limit,
    "limit_plus_one"
);
limb_check_control!(
    control_cl_sgt_for_ugt,
    machine_umul_i128_const_limit,
    "sgt_for_ugt"
);
limb_check_control!(
    control_cl_divisor_low_limb,
    machine_umul_i128_const_limit,
    "divisor_low_limb"
);

/// The signed/unsigned dispatch swap: the unsigned limb check where the signed
/// one belongs.
fn control_lc_unsigned_for_signed() -> SmtExpr {
    machine_umul_i128_limb_check(&limbs(), None)
}

/// The signed/unsigned dispatch swap: the signed limb check where the
/// unsigned one belongs.
fn control_lc_signed_for_unsigned() -> SmtExpr {
    machine_smul_i128_limb_check(&limbs(), None)
}

/// Limbs `(a_lo, a_hi, b_lo, b_hi)` of the pair `(a, b)`.
const fn limbs_of(a: u128, b: u128) -> [u64; 4] {
    [a as u64, (a >> 64) as u64, b as u64, (b >> 64) as u64]
}

/// The negative controls: characteristic miscompiles of the idiom, each with
/// the directed point at which it diverges from the source side.
pub fn checked_mul_i128_controls() -> Vec<CheckedMulI128Control> {
    use CheckedMulI128Form as F;
    vec![
        CheckedMulI128Control {
            form: F::LowProductChain,
            label: "second MADD multiplies a_hi by b_hi instead of b_lo",
            machine: control_chain_wrong_cross_limb,
            witness: limbs_of(1u128 << 64, 3),
            sampling_visible: true,
        },
        CheckedMulI128Control {
            form: F::LowProductChain,
            label: "UMULH carry of the low-limb product dropped",
            machine: control_chain_dropped_umulh,
            witness: limbs_of(1u128 << 63, 4),
            sampling_visible: true,
        },
        CheckedMulI128Control {
            form: F::UnsignedFlag,
            label: "a != 0 guard dropped (0 * b flagged for every b != 1)",
            machine: control_umul_guard_dropped,
            witness: limbs_of(0, 2),
            sampling_visible: false,
        },
        CheckedMulI128Control {
            form: F::UnsignedFlag,
            label: "quotient compared with the divisor's operand a instead of b",
            machine: control_umul_wrong_operand,
            witness: limbs_of(2, 3),
            sampling_visible: false,
        },
        CheckedMulI128Control {
            form: F::UnsignedFlag,
            label: "64-bit UMULH idiom misapplied to the low limbs (high limbs ignored)",
            machine: control_umul_low_limb_idiom,
            witness: limbs_of(1u128 << 64, 1u128 << 64),
            sampling_visible: true,
        },
        CheckedMulI128Control {
            form: F::SignedFlag,
            label: "MIN * -1 term dropped",
            machine: control_smul_min_neg1_dropped,
            witness: limbs_of(i128::MIN as u128, -1i128 as u128),
            sampling_visible: false,
        },
        CheckedMulI128Control {
            form: F::SignedFlag,
            label: "__udivti3 where __divti3 belongs",
            machine: control_smul_unsigned_division,
            witness: limbs_of(-2i128 as u128, 3),
            sampling_visible: false,
        },
        CheckedMulI128Control {
            form: F::SignedFlag,
            label: "quotient compared with b instead of a",
            machine: control_smul_wrong_operand,
            witness: limbs_of(2, 3),
            sampling_visible: false,
        },
        // The x86-64 limb check (OD-224): the design's mutants, each at its
        // replayed 128-bit counterexample (`z3_mutants_w128.jsonl`,
        // `w128_witnesses.json`).
        CheckedMulI128Control {
            form: F::UnsignedFlagLimbCheck,
            label: "carry term dropped (hi(a0*b0) + cross low halves overflowing is missed)",
            machine: control_lc_drop_carry,
            witness: limbs_of(0x2_0000_0000_0000_0005, 0x7fff_ffff_ffff_ffff),
            sampling_visible: SAMPLING_VISIBLE_LC[0],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagLimbCheck,
            label: "both-high-limbs test dropped",
            machine: control_lc_drop_both,
            witness: limbs_of(1 << 65, 1 << 64),
            sampling_visible: SAMPLING_VISIBLE_LC[1],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagLimbCheck,
            label: "hi(a1*b0) != 0 dropped",
            machine: control_lc_drop_o1,
            witness: limbs_of(0x2_5555_5555_5555_5558, 0xaaaa_aaaa_aaaa_aaab),
            sampling_visible: SAMPLING_VISIBLE_LC[2],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagLimbCheck,
            label: "hi(a0*b1) != 0 dropped",
            machine: control_lc_drop_o2,
            witness: limbs_of(0x8000_0000_0000_0000, 1 << 66),
            sampling_visible: SAMPLING_VISIBLE_LC[3],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagLimbCheck,
            label: "carry compared signed (slt for ult)",
            machine: control_lc_carry_signed,
            witness: limbs_of(0x8000_0000_0000_0002, 0x1_ffff_ffff_ffff_fff9),
            sampling_visible: SAMPLING_VISIBLE_LC[4],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagLimbCheck,
            label: "carry compared ule for ult",
            machine: control_lc_carry_ule,
            witness: limbs_of(0, 0xffff_ffff_ffff_ffff),
            sampling_visible: SAMPLING_VISIBLE_LC[5],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagLimbCheck,
            label: "CheckedSmul for the cross products' CheckedUmul (signed/unsigned swap)",
            machine: control_lc_smul_cross,
            witness: limbs_of((1 << 127) - 1, 2),
            sampling_visible: SAMPLING_VISIBLE_LC[6],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagLimbCheck,
            label: "signed limb check where the unsigned one belongs (dispatch swap)",
            machine: control_lc_signed_for_unsigned,
            witness: limbs_of(u128::MAX, 2),
            sampling_visible: SAMPLING_VISIBLE_LC[7],
        },
        CheckedMulI128Control {
            form: F::SignedFlagLimbCheck,
            label: "zero guard (result != 0) dropped: 0 * negative flagged",
            machine: control_lc_no_zero_guard,
            witness: limbs_of(1 << 127, 0),
            sampling_visible: SAMPLING_VISIBLE_LC[8],
        },
        CheckedMulI128Control {
            form: F::SignedFlagLimbCheck,
            label: "sign check dropped",
            machine: control_lc_no_sign_check,
            witness: limbs_of(u128::MAX, 1 << 127),
            sampling_visible: SAMPLING_VISIBLE_LC[9],
        },
        CheckedMulI128Control {
            form: F::SignedFlagLimbCheck,
            label: "magnitude core dropped",
            machine: control_lc_no_ou,
            witness: limbs_of(3, 0x5555_5555_5555_5555_5555_5555_5555_5556),
            sampling_visible: SAMPLING_VISIBLE_LC[10],
        },
        CheckedMulI128Control {
            form: F::SignedFlagLimbCheck,
            label: "result sign neg built as sa | sb",
            machine: control_lc_neg_or,
            witness: limbs_of(1 << 127, u128::MAX),
            sampling_visible: SAMPLING_VISIBLE_LC[11],
        },
        CheckedMulI128Control {
            form: F::SignedFlagLimbCheck,
            label: "core reads the wrapped product's high limb instead of |a*b|'s",
            machine: control_lc_pu_eq_r,
            witness: limbs_of(
                0xffff_ffff_ffff_ffff_c682_f89a_f6c0_2260,
                0x4_d2ed_c029_572a_6118,
            ),
            sampling_visible: SAMPLING_VISIBLE_LC[12],
        },
        CheckedMulI128Control {
            form: F::SignedFlagLimbCheck,
            label: "core on the raw bit patterns (signed/unsigned swap)",
            machine: control_lc_unsigned_core_raw,
            witness: limbs_of(2, 0xc0 << 120),
            sampling_visible: SAMPLING_VISIBLE_LC[13],
        },
        CheckedMulI128Control {
            form: F::SignedFlagLimbCheck,
            label: "unsigned limb check where the signed one belongs (dispatch swap)",
            machine: control_lc_unsigned_for_signed,
            witness: limbs_of(u128::MAX, 2),
            sampling_visible: SAMPLING_VISIBLE_LC[14],
        },
        // The constant-operand limit compare (OD-224).
        CheckedMulI128Control {
            form: F::UnsignedFlagConstLimit,
            label: "uge for ugt (the limit itself flagged)",
            machine: control_cl_uge_for_ugt,
            witness: limbs_of(u128::MAX / 3, 3),
            sampling_visible: SAMPLING_VISIBLE_LC[15],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagConstLimit,
            label: "limit off by one",
            machine: control_cl_limit_plus_one,
            witness: limbs_of(u128::MAX / 3 + 1, 3),
            sampling_visible: SAMPLING_VISIBLE_LC[16],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagConstLimit,
            label: "signed compare for the unsigned one",
            machine: control_cl_sgt_for_ugt,
            witness: limbs_of(1 << 127, 2),
            sampling_visible: SAMPLING_VISIBLE_LC[17],
        },
        CheckedMulI128Control {
            form: F::UnsignedFlagConstLimit,
            label: "limit of the constant's low limb only",
            machine: control_cl_divisor_low_limb,
            witness: limbs_of(1 << 64, (1 << 64) + 1),
            sampling_visible: SAMPLING_VISIBLE_LC[18],
        },
    ]
}

/// Whether the default sampling evaluator also refutes each limb-check
/// control, in [`checked_mul_i128_controls`] order: measured (and pinned) by
/// `the_limb_check_controls_sampling_visibility_is_as_recorded`. Those the
/// sampler misses (a dropped carry or cross-product test, `ule` for `ult`,
/// the signed cross products, the dropped zero guard, the core reading the
/// wrapped product, the limit compare's off-by-one controls) diverge on
/// slivers its edge battery and random limbs do not reach; each is refuted at
/// its directed witness.
const SAMPLING_VISIBLE_LC: [bool; 19] = [
    false, true, false, false, true, false, false, true, // unsigned
    false, true, true, true, false, true, true, // signed
    false, false, true, true, // constant operand
];

/// Directed unsigned boundary pairs: the product and flag edges a division
/// identity either recovers or does not.
pub const UMUL_I128_BATTERY: &[(u128, u128)] = &[
    (0, u128::MAX),
    (u128::MAX, 0),
    (1, u128::MAX),
    (u128::MAX, 1),
    (u128::MAX, 2),
    (2, u128::MAX),
    (1 << 127, 2),
    (1 << 127, 1),
    ((1 << 127) - 1, 2),
    (1 << 64, 1 << 64),
    ((1 << 64) - 1, (1 << 64) - 1),
    (1 << 64, (1 << 64) - 1),
    ((1 << 64) + 1, (1 << 64) - 1),
    ((1 << 64) + 1, (1 << 64) + 1),
    (1 << 65, 1 << 64),
    (1 << 63, 1 << 63),
    (1 << 63, 1 << 65),
    (1 << 63, 1 << 64),
    (7, 0),
    (5, 3),
    (u128::MAX, u128::MAX),
    (u128::MAX / 3, 3),
    (u128::MAX / 3 + 1, 3),
];

/// Directed signed boundary pairs.
pub const SMUL_I128_BATTERY: &[(i128, i128)] = &[
    (i128::MIN, -1),
    (-1, i128::MIN),
    (i128::MIN, 1),
    (i128::MIN, 0),
    (i128::MAX, 1),
    (i128::MAX, 2),
    (i128::MAX, -1),
    (i128::MAX, -2),
    (i128::MIN, 2),
    (i128::MIN / 2, 2),
    (i128::MIN / 2, -2),
    (1 << 64, 1 << 64),
    ((1 << 64) - 1, (1 << 64) - 1),
    (1 << 63, 1 << 63),
    (1 << 63, 1 << 64),
    (-(1 << 63), 1 << 64),
    (1 << 126, 2),
    (1 << 126, -2),
    (-(1 << 126), -2),
    (-(1 << 126), 2),
    (0, i128::MAX),
    (0, i128::MIN),
    (5, 3),
    (-5, 3),
    (5, -3),
    (-5, -3),
    (i128::MAX, i128::MAX),
    (i128::MIN, i128::MIN),
];

fn env_of(limbs: [u64; 4]) -> HashMap<String, u64> {
    HashMap::from([
        ("a_lo".to_string(), limbs[0]),
        ("a_hi".to_string(), limbs[1]),
        ("b_lo".to_string(), limbs[2]),
        ("b_hi".to_string(), limbs[3]),
    ])
}

/// What the coverage gate learns from a successful credit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedMulI128Credit {
    /// Obligations that discharged under the evaluator.
    pub obligations: usize,
    /// Directed boundary points at which both sides matched the native oracle.
    pub battery_points: usize,
    /// Negative controls refuted.
    pub controls_refuted: usize,
}

/// The production credit: the registered obligations, the registered control
/// battery and the default evaluator configuration. Cached per process — the
/// audit of the AArch64 inventory would otherwise re-run the sampling sweep
/// for every row.
pub fn checked_mul_i128_credit() -> Result<CheckedMulI128Credit, String> {
    static CREDIT: std::sync::OnceLock<Result<CheckedMulI128Credit, String>> =
        std::sync::OnceLock::new();
    CREDIT
        .get_or_init(|| {
            checked_mul_i128_credit_with(
                &all_checked_mul_i128_proofs(),
                &checked_mul_i128_controls(),
                &VerificationConfig::default(),
            )
        })
        .clone()
}

/// [`checked_mul_i128_credit`] over injected obligations and controls, so a
/// test can hand the hook a degenerate obligation or a surviving control and
/// watch it refuse.
///
/// Refuses unless: every form has exactly one obligation, which is
/// non-degenerate and evaluates `Valid`; at every battery point both sides of
/// the flag obligations equal Rust's native `checked_mul` verdict and both
/// sides of the chain obligation equal `wrapping_mul`; and every control is
/// non-degenerate, diverges from its form's source side at its witness (a
/// point where the real obligation agrees), and — when sampling-visible — is
/// refuted by the evaluator as well.
pub fn checked_mul_i128_credit_with(
    obligations: &[ProofObligation],
    controls: &[CheckedMulI128Control],
    config: &VerificationConfig,
) -> Result<CheckedMulI128Credit, String> {
    let mut by_form: Vec<(CheckedMulI128Form, &ProofObligation)> = Vec::new();
    for form in CheckedMulI128Form::ALL {
        let query = form.query();
        let matching: Vec<&ProofObligation> = obligations
            .iter()
            .filter(|o| o.name.to_lowercase().contains(query))
            .collect();
        let [only] = matching[..] else {
            return Err(format!(
                "{form:?}: expected exactly one obligation matching {query:?}, found {}",
                matching.len()
            ));
        };
        if !only.is_genuinely_proven() {
            return Err(format!(
                "{form:?}: obligation {:?} is degenerate (source == machine)",
                only.name
            ));
        }
        match verify_by_evaluation_with_config(only, config) {
            VerificationResult::Valid => {}
            other => {
                return Err(format!(
                    "{form:?}: obligation {:?} did not discharge: {other:?}",
                    only.name
                ));
            }
        }
        by_form.push((form, only));
    }
    let obligation_of = |form: CheckedMulI128Form| -> Result<&ProofObligation, String> {
        by_form
            .iter()
            .find(|(f, _)| *f == form)
            .map(|(_, o)| *o)
            .ok_or_else(|| format!("{form:?}: no resolved obligation"))
    };

    // Directed battery against the native oracle.
    let mut battery_points = 0;
    let chain = obligation_of(CheckedMulI128Form::LowProductChain)?;
    let flag_forms = |signed: bool| -> Result<Vec<&ProofObligation>, String> {
        CheckedMulI128Form::ALL
            .into_iter()
            .filter(|form| form.flag_sign() == Some(signed))
            .map(obligation_of)
            .collect()
    };
    let umuls = flag_forms(false)?;
    for &(a, b) in UMUL_I128_BATTERY {
        let env = env_of(limbs_of(a, b));
        let want_flag = EvalResult::Bv(u64::from(a.checked_mul(b).is_none()));
        for umul in &umuls {
            for (side, expr) in [
                ("source", &umul.trust_ir_expr),
                ("machine", &umul.aarch64_expr),
            ] {
                let got = expr.eval(&env);
                if got != want_flag {
                    return Err(format!(
                        "unsigned flag {side} side of {:?} disagrees with native \
                         u128::checked_mul at ({a:#x}, {b:#x}): got {got:?}, want {want_flag:?}",
                        umul.name
                    ));
                }
            }
        }
        let want_product = EvalResult::Bv128(a.wrapping_mul(b));
        for (side, expr) in [
            ("source", &chain.trust_ir_expr),
            ("machine", &chain.aarch64_expr),
        ] {
            let got = expr.eval(&env);
            if got != want_product {
                return Err(format!(
                    "low-product chain {side} side disagrees with native wrapping_mul at \
                     ({a:#x}, {b:#x}): got {got:?}, want {want_product:?}"
                ));
            }
        }
        battery_points += 1;
    }
    let smuls = flag_forms(true)?;
    for &(a, b) in SMUL_I128_BATTERY {
        let env = env_of(limbs_of(a as u128, b as u128));
        let want_flag = EvalResult::Bv(u64::from(a.checked_mul(b).is_none()));
        for smul in &smuls {
            for (side, expr) in [
                ("source", &smul.trust_ir_expr),
                ("machine", &smul.aarch64_expr),
            ] {
                let got = expr.eval(&env);
                if got != want_flag {
                    return Err(format!(
                        "signed flag {side} side of {:?} disagrees with native \
                         i128::checked_mul at ({a}, {b}): got {got:?}, want {want_flag:?}",
                        smul.name
                    ));
                }
            }
        }
        let want_product = EvalResult::Bv128(a.wrapping_mul(b) as u128);
        for (side, expr) in [
            ("source", &chain.trust_ir_expr),
            ("machine", &chain.aarch64_expr),
        ] {
            let got = expr.eval(&env);
            if got != want_product {
                return Err(format!(
                    "low-product chain {side} side disagrees with native wrapping_mul at \
                     ({a}, {b}): got {got:?}, want {want_product:?}"
                ));
            }
        }
        battery_points += 1;
    }

    // Every control must refute.
    let mut controls_refuted = 0;
    for form in CheckedMulI128Form::ALL {
        if !controls.iter().any(|c| c.form == form) {
            return Err(format!("{form:?} has no negative control"));
        }
    }
    for control in controls {
        let real = obligation_of(control.form)?;
        let wrong = (control.machine)();
        if wrong == real.trust_ir_expr {
            return Err(format!(
                "control {:?} ({:?}) is the source side itself and cannot refute",
                control.label, control.form
            ));
        }
        let env = env_of(control.witness);
        let source_at = real.trust_ir_expr.eval(&env);
        let real_at = real.aarch64_expr.eval(&env);
        if source_at != real_at {
            return Err(format!(
                "control {:?} ({:?}): the real obligation itself disagrees at the witness \
                 {:?} ({source_at:?} vs {real_at:?})",
                control.label, control.form, control.witness
            ));
        }
        let wrong_at = wrong.eval(&env);
        if wrong_at == source_at {
            return Err(format!(
                "control {:?} ({:?}) SURVIVES at its witness {:?}: both sides give {source_at:?}",
                control.label, control.form, control.witness
            ));
        }
        if control.sampling_visible {
            let mutated = ProofObligation {
                name: format!("NEGATIVE: {} ({:?})", control.label, control.form),
                aarch64_expr: wrong,
                ..real.clone()
            };
            match verify_by_evaluation_with_config(&mutated, config) {
                VerificationResult::Invalid { .. } => {}
                other => {
                    return Err(format!(
                        "control {:?} ({:?}) SURVIVES the sampling evaluator: {other:?}",
                        control.label, control.form
                    ));
                }
            }
        }
        controls_refuted += 1;
    }

    Ok(CheckedMulI128Credit {
        obligations: by_form.len(),
        battery_points,
        controls_refuted,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay_cli};
    use crate::lowering_proof::verify_by_evaluation;

    #[test]
    fn family_has_six_non_degenerate_obligations_that_discharge() {
        let proofs = all_checked_mul_i128_proofs();
        assert_eq!(proofs.len(), 6);
        for proof in &proofs {
            assert!(
                proof.is_genuinely_proven(),
                "DEGENERATE (X==X) obligation {:?}",
                proof.name
            );
            assert_eq!(proof.inputs, limb_inputs());
            assert!(
                matches!(verify_by_evaluation(proof), VerificationResult::Valid),
                "{} did not pass the default evaluator",
                proof.name
            );
        }
        let names: std::collections::HashSet<&str> =
            proofs.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names.len(), 6, "names must be unique");
        for form in CheckedMulI128Form::ALL {
            let hits = proofs
                .iter()
                .filter(|p| p.name.to_lowercase().contains(form.query()))
                .count();
            assert_eq!(hits, 1, "{form:?}: query {:?} must be unique", form.query());
        }
    }

    #[test]
    fn credit_holds_with_the_registered_battery_and_controls() {
        let credit = checked_mul_i128_credit().unwrap_or_else(|e| panic!("credit refused: {e}"));
        assert_eq!(
            credit,
            CheckedMulI128Credit {
                obligations: 6,
                battery_points: UMUL_I128_BATTERY.len() + SMUL_I128_BATTERY.len(),
                controls_refuted: checked_mul_i128_controls().len(),
            }
        );
        assert_eq!(checked_mul_i128_controls().len(), 8 + 15 + 4);
    }

    /// The x86-64 limb check (OD-224) has its own controls: the design's
    /// thirteen non-equivalent mutants and the two dispatch swaps, each wrong
    /// at its witness while the real limb check and the source agree there.
    #[test]
    fn the_limb_check_forms_carry_the_design_mutants() {
        let controls = checked_mul_i128_controls();
        for (form, want) in [
            (CheckedMulI128Form::UnsignedFlagLimbCheck, 8),
            (CheckedMulI128Form::SignedFlagLimbCheck, 7),
            (CheckedMulI128Form::UnsignedFlagConstLimit, 4),
        ] {
            let mine: Vec<_> = controls.iter().filter(|c| c.form == form).collect();
            assert_eq!(mine.len(), want, "{form:?}");
            let real = form.obligation();
            for control in mine {
                let env = env_of(control.witness);
                let truth = real.trust_ir_expr.eval(&env);
                assert_eq!(real.aarch64_expr.eval(&env), truth, "{}", control.label);
                assert_ne!((control.machine)().eval(&env), truth, "{}", control.label);
            }
        }
    }

    /// Which limb-check controls the default sampling evaluator refutes on its
    /// own (beyond their directed witness) is measured here and pinned in
    /// [`SAMPLING_VISIBLE_LC`], so a control the sampler stops seeing fails
    /// the credit, and one it starts seeing is noticed.
    #[test]
    fn the_limb_check_controls_sampling_visibility_is_as_recorded() {
        let config = VerificationConfig::default();
        let measured: Vec<bool> = checked_mul_i128_controls()
            .into_iter()
            .filter(|c| {
                matches!(
                    c.form,
                    CheckedMulI128Form::UnsignedFlagLimbCheck
                        | CheckedMulI128Form::SignedFlagLimbCheck
                        | CheckedMulI128Form::UnsignedFlagConstLimit
                )
            })
            .map(|c| {
                let real = c.form.obligation();
                let mutated = ProofObligation {
                    name: format!("NEGATIVE: {}", c.label),
                    aarch64_expr: (c.machine)(),
                    ..real
                };
                matches!(
                    verify_by_evaluation_with_config(&mutated, &config),
                    VerificationResult::Invalid { .. }
                )
            })
            .collect();
        eprintln!("L04_P10_SAMPLING_VISIBLE_LC {measured:?}");
        assert_eq!(measured, SAMPLING_VISIBLE_LC.to_vec());
    }

    /// The limb-check machine sides against native arithmetic on a random
    /// stream of operands of every bit length and sign: statistical,
    /// regression-only evidence (the adapter's own output is swept
    /// exhaustively at 8 and 16 bits by `trust-cg-lower`'s
    /// `adapter_i128_mulo_tests`).
    #[test]
    fn the_limb_check_machine_sides_match_native_checked_mul_on_random_pairs() {
        let umul = machine_umul_i128_limb_check(&limbs(), None);
        let smul = machine_smul_i128_limb_check(&limbs(), None);
        let limit = machine_umul_i128_const_limit(&limbs(), None);
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            state.wrapping_mul(0x2545_f491_4f6c_dd1d)
        };
        for _ in 0..20_000 {
            let mut operand = || {
                let x = (u128::from(next()) << 64) | u128::from(next());
                let bits = (next() % 129) as u32;
                let x = if bits == 128 {
                    x
                } else {
                    x & ((1u128 << bits) - 1)
                };
                if next() % 2 == 0 { x } else { x.wrapping_neg() }
            };
            let (a, b) = (operand(), operand());
            let env = env_of(limbs_of(a, b));
            assert_eq!(
                umul.eval(&env),
                EvalResult::Bv(u64::from(a.checked_mul(b).is_none())),
                "u ({a:#x}, {b:#x})"
            );
            assert_eq!(
                limit.eval(&env),
                EvalResult::Bv(u64::from(a.checked_mul(b).is_none())),
                "limit ({a:#x}, {b:#x})"
            );
            assert_eq!(
                smul.eval(&env),
                EvalResult::Bv(u64::from((a as i128).checked_mul(b as i128).is_none())),
                "s ({a:#x}, {b:#x})"
            );
        }
    }

    #[test]
    fn credit_refuses_a_surviving_control() {
        let mut controls = checked_mul_i128_controls();
        controls.push(CheckedMulI128Control {
            form: CheckedMulI128Form::UnsignedFlag,
            label: "identity mutation must survive",
            machine: || machine_umul_i128_flag(&limbs()),
            witness: limbs_of(5, 3),
            sampling_visible: false,
        });
        let err = checked_mul_i128_credit_with(
            &all_checked_mul_i128_proofs(),
            &controls,
            &VerificationConfig::default(),
        )
        .expect_err("a surviving control must refuse the credit");
        assert!(err.contains("SURVIVES"), "{err}");
    }

    #[test]
    fn credit_refuses_a_degenerate_or_missing_obligation() {
        let mut proofs = all_checked_mul_i128_proofs();
        let l = limbs();
        proofs[1].aarch64_expr = source_umul_i128_flag(&l);
        let err = checked_mul_i128_credit_with(
            &proofs,
            &checked_mul_i128_controls(),
            &VerificationConfig::default(),
        )
        .expect_err("a degenerate obligation must refuse the credit");
        assert!(err.contains("degenerate"), "{err}");

        let missing: Vec<ProofObligation> =
            all_checked_mul_i128_proofs().into_iter().take(2).collect();
        let err = checked_mul_i128_credit_with(
            &missing,
            &checked_mul_i128_controls(),
            &VerificationConfig::default(),
        )
        .expect_err("a missing form must refuse the credit");
        assert!(err.contains("expected exactly one obligation"), "{err}");
    }

    #[test]
    fn credit_refuses_a_wrong_flag_that_the_battery_sees() {
        // A machine side that flags every product overflows at (5, 3), where
        // the native oracle says no overflow.
        let mut proofs = all_checked_mul_i128_proofs();
        proofs[1].aarch64_expr = bv1(SmtExpr::bool_const(true));
        let err = checked_mul_i128_credit_with(
            &proofs,
            &checked_mul_i128_controls(),
            &VerificationConfig::default(),
        )
        .expect_err("a wrong flag must refuse the credit");
        assert!(
            err.contains("did not discharge") || err.contains("native u128::checked_mul"),
            "{err}"
        );
    }

    /// The exact-high-half reconstruction is what the source sides rest on:
    /// check it against native 256-bit arithmetic simulated with `u128`
    /// halves at points that exercise every carry path.
    #[test]
    fn exact_high128_matches_native_wide_products() {
        let l = limbs();
        let high = exact_high128_unsigned(l.a_lo, l.a_hi, l.b_lo, l.b_hi);
        let points: &[(u128, u128)] = &[
            (u128::MAX, u128::MAX),
            (u128::MAX, 2),
            (1 << 64, 1 << 64),
            ((1 << 64) - 1, (1 << 64) - 1),
            ((1 << 64) + 1, u128::MAX),
            (u128::MAX - 1, u128::MAX - 1),
            (1 << 127, 2),
            (1 << 127, 1 << 127),
            (
                0xdead_beef_cafe_f00d_0123_4567_89ab_cdef,
                0xfedc_ba98_7654_3210_0fed_cba9_8765_4321,
            ),
            (0, u128::MAX),
        ];
        for &(a, b) in points {
            // Native: split into 64-bit limbs and accumulate in u128 with
            // explicit carries (a different arrangement from the SMT side).
            let (a0, a1) = (a as u64 as u128, a >> 64);
            let (b0, b1) = (b as u64 as u128, b >> 64);
            let p00 = a0 * b0;
            let p01 = a0 * b1;
            let p10 = a1 * b0;
            let p11 = a1 * b1;
            let (m1, c1) = (p00 >> 64).overflowing_add(p01);
            let (m2, c2) = m1.overflowing_add(p10);
            let carries = u128::from(c1) + u128::from(c2);
            let want = (m2 >> 64) + p11 + (carries << 64);
            let got = high.eval(&env_of(limbs_of(a, b)));
            assert_eq!(got, EvalResult::Bv128(want), "high128 at ({a:#x}, {b:#x})");
        }
    }

    /// Every deferral is named, and the family's documentation of what it
    /// does not claim is non-empty.
    #[test]
    fn deferrals_are_named() {
        assert_eq!(CHECKED_MUL_I128_DEFERRALS.len(), 3);
        assert!(
            CHECKED_MUL_I128_DEFERRALS
                .iter()
                .any(|d| d.contains("decoded-word"))
        );
    }

    // -----------------------------------------------------------------------
    // OD-224's structured formal attempt on the limb check. The flag
    // obligations' only nonlinear terms are 64x64 -> 128 limb products and the
    // value's 128-bit `bvmul`. With every product a free input (two 64-bit
    // halves each) and the facts the limb check needs stated as
    // preconditions, the equivalence is linear; the facts themselves are
    // multiplier lemmas, attempted on their own below. NONE of this is
    // registered or credited: L04-P10's class stays what the module doc says.
    // -----------------------------------------------------------------------

    /// A free 128-bit product `name` as two 64-bit inputs.
    fn free128(name: &str) -> SmtExpr {
        SmtExpr::var(format!("{name}_hi"), LIMB).concat(SmtExpr::var(format!("{name}_lo"), LIMB))
    }

    fn free128_inputs(name: &str) -> [(String, u32); 2] {
        [(format!("{name}_lo"), LIMB), (format!("{name}_hi"), LIMB)]
    }

    /// `(2^64 - 1)^2`, the largest exact 64x64 product.
    fn max_limb_product() -> SmtExpr {
        SmtExpr::bv_const(0xffff_ffff_ffff_fffe, LIMB).concat(SmtExpr::bv_const(1, LIMB))
    }

    /// The facts about an exact limb product `p = x * y` the limb check
    /// needs: it is zero iff a factor is, and at most `(2^64 - 1)^2`.
    fn product_facts(p: &SmtExpr, x: &SmtExpr, y: &SmtExpr) -> [SmtExpr; 2] {
        let zero = SmtExpr::bv_const(0, LIMB);
        [
            p.clone().eq_expr(zero128()).eq_expr(
                x.clone()
                    .eq_expr(zero.clone())
                    .or_expr(y.clone().eq_expr(zero)),
            ),
            p.clone().bvule(max_limb_product()),
        ]
    }

    /// The unsigned core lemma: with the four limb products free (`p00 =
    /// a_lo*b_lo`, `p01 = a_lo*b_hi`, `p10 = a_hi*b_lo`, `p11 = a_hi*b_hi`)
    /// under [`product_facts`], and the value's high limb spelled by the
    /// `Imul` chain (`hi(p00) + lo(p01) + lo(p10)`, the low-product-chain
    /// form), the limb check equals "the exact product's high half is
    /// non-zero" (the source of [`source_umul_i128_flag`] over the same
    /// products).
    fn core_lemma_unsigned() -> ProofObligation {
        let l = limbs();
        let [p00, p01, p10, p11] = ["p00", "p01", "p10", "p11"].map(free128);
        let mid1 = high64(p00.clone()).zero_ext(LIMB).bvadd(p01.clone());
        let mid2 = mid1.clone().bvadd(p10.clone());
        let carry = bv1(mid2.clone().bvult(mid1));
        let carry_term = carry
            .zero_ext(127)
            .bvshl(SmtExpr::bv_const(64, LIMB).zero_ext(LIMB));
        let high = high64(mid2)
            .zero_ext(LIMB)
            .bvadd(p11.clone())
            .bvadd(carry_term);
        let source = bv1(high.eq_expr(zero128()).not_expr());
        let p1 = high64(p00.clone())
            .bvadd(low64(p01.clone()))
            .bvadd(low64(p10.clone()));
        let zero = SmtExpr::bv_const(0, LIMB);
        let (m1, o1) = (
            low64(p10.clone()),
            high64(p10.clone()).eq_expr(zero.clone()).not_expr(),
        );
        let (m2, o2) = (
            low64(p01.clone()),
            high64(p01.clone()).eq_expr(zero.clone()).not_expr(),
        );
        let carry = p1.bvult(m1.bvadd(m2));
        let both = l
            .a_hi
            .clone()
            .eq_expr(zero.clone())
            .not_expr()
            .and_expr(l.b_hi.clone().eq_expr(zero).not_expr());
        let machine = bv1(o1.or_expr(o2).or_expr(carry).or_expr(both));
        let mut preconditions = Vec::new();
        for (p, x, y) in [
            (&p00, &l.a_lo, &l.b_lo),
            (&p01, &l.a_lo, &l.b_hi),
            (&p10, &l.a_hi, &l.b_lo),
            (&p11, &l.a_hi, &l.b_hi),
        ] {
            preconditions.extend(product_facts(p, x, y));
        }
        let mut inputs = limb_inputs();
        for name in ["p00", "p01", "p10", "p11"] {
            inputs.extend(free128_inputs(name));
        }
        ProofObligation {
            machine_side_provenance: MachineSideProvenance::StaticDb,
            name: "OD-224 attempt: limb-check core lemma (limb products free)".to_string(),
            trust_ir_expr: source,
            aarch64_expr: machine,
            inputs,
            preconditions,
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        }
    }

    /// The signed reduction lemma (the design's L3): with `m = |a| * |b| mod
    /// 2^128` and `h` the exact product's high half free, the value `r = neg
    /// ? -m : m` (lemma L2) and the unsigned core's verdict `h != 0` (the core
    /// lemma on the magnitudes), the magnitudes route's flag equals the
    /// signed source's "`h != 0` or `m` above the signed limit".
    fn reduction_lemma_signed() -> ProofObligation {
        let l = limbs();
        let (m, h) = (free128("m"), free128("h"));
        let zero = SmtExpr::bv_const(0, LIMB);
        let sa = l.a_hi.clone().bvslt(zero.clone());
        let sb = l.b_hi.clone().bvslt(zero.clone());
        let neg = sa.eq_expr(sb).not_expr();
        let high_nz = h.eq_expr(zero128()).not_expr();
        let limit = SmtExpr::ite(neg.clone(), min128(), max128());
        let source = bv1(high_nz.clone().or_expr(m.clone().bvugt(limit)));
        let r = SmtExpr::ite(neg.clone(), m.clone().bvneg(), m);
        let r_neg = high_limb(r.clone()).bvslt(zero);
        let r_nz = r.eq_expr(zero128()).not_expr();
        let bad = r_neg.eq_expr(neg).not_expr().and_expr(r_nz);
        let machine = bv1(high_nz.or_expr(bad));
        let mut inputs = limb_inputs();
        inputs.extend(free128_inputs("m"));
        inputs.extend(free128_inputs("h"));
        ProofObligation {
            machine_side_provenance: MachineSideProvenance::StaticDb,
            name: "OD-224 attempt: magnitudes-route sign reduction (product free)".to_string(),
            trust_ir_expr: source,
            aarch64_expr: machine,
            inputs,
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        }
    }

    /// The multiplier lemmas the two lemmas above assume, each stated alone:
    /// the zero-product fact and the bound of one exact 64x64 product, and
    /// the `Imul I128` value's high limb as the limb chain (the
    /// low-product-chain row, restricted to its high half).
    fn multiplier_lemmas() -> Vec<ProofObligation> {
        let l = limbs();
        let p = limb_product(l.a_lo.clone(), l.b_lo.clone());
        let zero = SmtExpr::bv_const(0, LIMB);
        let fact = |name: &str, source: SmtExpr, machine: SmtExpr| ProofObligation {
            machine_side_provenance: MachineSideProvenance::StaticDb,
            name: format!("OD-224 attempt: {name}"),
            trust_ir_expr: source,
            aarch64_expr: machine,
            inputs: limb_inputs(),
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        };
        vec![
            fact(
                "zero product (a_lo*b_lo == 0 iff a factor is 0)",
                bv1(p.clone().eq_expr(zero128())),
                bv1(l
                    .a_lo
                    .clone()
                    .eq_expr(zero.clone())
                    .or_expr(l.b_lo.clone().eq_expr(zero))),
            ),
            fact(
                "product bound (a_lo*b_lo <= (2^64-1)^2)",
                bv1(p.bvule(max_limb_product())),
                one1(),
            ),
            fact(
                "Imul_I128 high limb as the limb chain",
                high_limb(l.a.clone().bvmul(l.b.clone())),
                high64(limb_product(l.a_lo.clone(), l.b_lo.clone()))
                    .bvadd(l.a_lo.clone().bvmul(l.b_hi.clone()))
                    .bvadd(l.a_hi.clone().bvmul(l.b_lo.clone())),
            ),
        ]
    }

    /// The two linear lemmas hold where their free products are the REAL
    /// products (so their preconditions hold), at the battery and on random
    /// operands; a lemma whose machine side drops the carry is refuted at
    /// such a point. Regression evidence for the lemma statements only.
    #[test]
    fn the_structured_lemmas_hold_at_real_products() {
        fn env_with(a: u128, b: u128) -> HashMap<String, u64> {
            let mut env = env_of(limbs_of(a, b));
            let (a0, a1, b0, b1) = (a as u64 as u128, a >> 64, b as u64 as u128, b >> 64);
            for (name, p) in [
                ("p00", a0 * b0),
                ("p01", a0 * b1),
                ("p10", a1 * b0),
                ("p11", a1 * b1),
            ] {
                env.insert(format!("{name}_lo"), p as u64);
                env.insert(format!("{name}_hi"), (p >> 64) as u64);
            }
            let (sa, sb) = ((a as i128) < 0, (b as i128) < 0);
            let (ma, mb) = (
                if sa { a.wrapping_neg() } else { a },
                if sb { b.wrapping_neg() } else { b },
            );
            let m = ma.wrapping_mul(mb);
            let h = ma.widening_mul_high(mb);
            env.insert("m_lo".into(), m as u64);
            env.insert("m_hi".into(), (m >> 64) as u64);
            env.insert("h_lo".into(), h as u64);
            env.insert("h_hi".into(), (h >> 64) as u64);
            env
        }
        trait WideningHigh {
            fn widening_mul_high(self, other: Self) -> Self;
        }
        impl WideningHigh for u128 {
            fn widening_mul_high(self, other: u128) -> u128 {
                let (a0, a1) = (self as u64 as u128, self >> 64);
                let (b0, b1) = (other as u64 as u128, other >> 64);
                let (p00, p01, p10, p11) = (a0 * b0, a0 * b1, a1 * b0, a1 * b1);
                let (m1, c1) = (p00 >> 64).overflowing_add(p01);
                let (m2, c2) = m1.overflowing_add(p10);
                (m2 >> 64) + p11 + ((u128::from(c1) + u128::from(c2)) << 64)
            }
        }
        let core = core_lemma_unsigned();
        let reduction = reduction_lemma_signed();
        let mut points: Vec<(u128, u128)> = UMUL_I128_BATTERY.to_vec();
        points.extend(
            SMUL_I128_BATTERY
                .iter()
                .map(|&(a, b)| (a as u128, b as u128)),
        );
        for &(a, b) in &points {
            let env = env_with(a, b);
            for pre in &core.preconditions {
                assert_eq!(pre.eval(&env), EvalResult::Bool(true), "({a:#x}, {b:#x})");
            }
            assert_eq!(
                core.trust_ir_expr.eval(&env),
                EvalResult::Bv(u64::from(a.checked_mul(b).is_none()))
            );
            assert_eq!(core.aarch64_expr.eval(&env), core.trust_ir_expr.eval(&env));
            assert_eq!(
                reduction.trust_ir_expr.eval(&env),
                EvalResult::Bv(u64::from((a as i128).checked_mul(b as i128).is_none())),
                "({a:#x}, {b:#x})"
            );
            assert_eq!(
                reduction.aarch64_expr.eval(&env),
                reduction.trust_ir_expr.eval(&env)
            );
        }
        for lemma in multiplier_lemmas() {
            for &(a, b) in &points {
                let env = env_of(limbs_of(a, b));
                assert_eq!(
                    lemma.trust_ir_expr.eval(&env),
                    lemma.aarch64_expr.eval(&env),
                    "{} at ({a:#x}, {b:#x})",
                    lemma.name
                );
            }
        }
    }

    /// OD-224's structured formal attempt on AY (tool-gated; recorded, never
    /// credited): the two linear lemmas must be Verified or capacity, the
    /// multiplier lemmas they rest on are attempted alone; a counterexample
    /// or a soundness-class answer fails the test. Each outcome and its time
    /// is printed (`L04_P10_STRUCTURED`) for the OD-224 record.
    #[test]
    fn the_structured_formal_attempt_never_refutes() {
        if !crate::ay_bridge::z3_available() {
            crate::formal_gap::skip_test(
                "the_structured_formal_attempt_never_refutes",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }
        let config = AYConfig::default().with_timeout(60_000);
        let mut lemmas = vec![core_lemma_unsigned(), reduction_lemma_signed()];
        lemmas.extend(multiplier_lemmas());
        for proof in lemmas {
            let start = std::time::Instant::now();
            let result = verify_with_ay_cli(&proof, &config);
            eprintln!(
                "L04_P10_STRUCTURED {} -> {result} ({:.1} s)",
                proof.name,
                start.elapsed().as_secs_f64()
            );
            match result {
                AYResult::Unknown(ref reason)
                    if crate::proof_gate::unknown_is_hard_failure(reason) =>
                {
                    panic!("{} returned {result}: a soundness-class answer", proof.name)
                }
                AYResult::CounterExample(cx) => {
                    panic!("SOUNDNESS: {} REFUTED by {cx:?}", proof.name)
                }
                AYResult::Error(e) => panic!("{} solver error: {e}", proof.name),
                _ => {}
            }
        }
    }

    /// Formal attempt: the family's 128-bit `bvmul`/division terms are beyond
    /// the strict gate's solver budget like the 64-bit mul rows, so a Timeout,
    /// or an Unknown the strict gate files as capacity, is tolerated. A
    /// CounterExample is a refutation, and an Error, or an Unknown the strict
    /// gate files as a SOUNDNESS failure (a working checker's rejection of AY's
    /// proof, AY's own self-check rejection, a trusted proof step, an internal
    /// error), is a verdict on a proof, not capacity: each fails the test, the
    /// same discipline as the 64-bit rows in `checked_overflow_proofs`.
    #[test]
    fn formal_attempt_never_refutes() {
        if !crate::ay_bridge::z3_available() {
            crate::formal_gap::skip_test(
                "formal_attempt_never_refutes",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }
        let config = AYConfig::default().with_timeout(10_000);
        for proof in all_checked_mul_i128_proofs() {
            let start = std::time::Instant::now();
            let result = verify_with_ay_cli(&proof, &config);
            eprintln!(
                "L04_P10_FORMAL {} -> {result} ({:.1} s)",
                proof.name,
                start.elapsed().as_secs_f64()
            );
            match result {
                AYResult::Unknown(ref reason)
                    if crate::proof_gate::unknown_is_hard_failure(reason) =>
                {
                    panic!(
                        "{} returned {result}; the strict proof gate files this as a soundness \
                         failure, not capacity",
                        proof.name
                    )
                }
                AYResult::Verified
                | AYResult::SolverUnsat
                | AYResult::Timeout
                | AYResult::Unknown(_) => {}
                AYResult::CounterExample(cx) => {
                    panic!("SOUNDNESS: {} REFUTED by {cx:?}", proof.name)
                }
                AYResult::Error(e) => panic!("{} solver error: {e}", proof.name),
            }
        }
    }
}
