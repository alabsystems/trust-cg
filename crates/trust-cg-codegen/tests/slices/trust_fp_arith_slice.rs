// Trust-toolchain slice — the FP-VERIFICATION BIT-MODEL *ARITHMETIC PIPELINE*
// (fadd / fsub / fmul / fdiv / fsqrt / fcvt + int<->float), transcribed VERBATIM
// from  trust-cg/crates/trust-cg-verify/src/fp_bitmodel.rs.
//
// ROUND 26 / TRUST BATCH 13 — the SOUNDNESS-CRITICAL CORE of trust-cg's FP TCB.
// R25 (batch 12) verified the classify / fcmp / min-max predicates of this same
// module; it DEFERRED the heavier RNE arithmetic. This slice does the arithmetic:
// the integer-only IEEE-754 fadd/fmul/fdiv/fsqrt/fcvt against which trust-cg proves
// its FP-op lowerings. A ROUNDING bug here means the FP proofs compare against a
// WRONG oracle -> a soundness hole. Hence the quad-oracle (native == JIT ==
// linked-production == host-FPU) in the harness.
//
// FpFmt FLATTENED to its geometry scalars (total, mant, exp_w, bias): the
// production `FpFmt { total, mant, exp_w, bias }` is passed by value; here we pass
// the fields as scalars (exactly the R25 batch-12 discipline, extended with `bias`,
// which the arithmetic pipeline DOES consult — it only entered fmul/fcvt/fti/itf,
// none of which R25 transcribed). Widths driven by the harness: F16 (16,10,5,15),
// F32 (32,23,8,127), F64 (64,52,11,1023). FpFmt methods inlined as scalar exprs:
//   f.sign_bit()  -> total - 1
//   f.exp_max()   -> exp_max(exp_w) = (1<<exp_w) - 1
//   f.mant_mask() -> (1u64 << mant) - 1
//   f.word_mask() -> word_mask(total)
//
// THREE verbatim-preserving substitutions (each a frontend [F4] empty-leaf gap;
// each semantically identical, documented at its site):
//   (S1) `x.leading_zeros()`  -> `u128_leading_zeros(x)` explicit bit-scan
//        (core::num::leading_zeros lowers to an empty extern leaf; the scan counts
//         the same high zero bits).
//   (S2) `a.saturating_sub(b)` -> `if a >= b { a - b } else { 0 }`
//        `x.min(k)`            -> `if x < k { x } else { k }`
//        (core::num::saturating_sub / core::cmp::Ord::min are empty leaves).
//   (S3) `0u128.wrapping_sub(v)` -> `0u128 - v`
//        (core::num::wrapping_sub is an empty leaf; under `-C overflow-checks=off`
//         the plain `-` is two's-complement wrapping — identical).
//   (S4) `u128::MAX` -> `!0u128` (bit-identical; current frontend lowering
//        canonicalizes the all-ones value as `Constant::U128`).
//   (S5) 32-bit shift `x >> 1` (x:u32) -> `x >> 1u32`  ([F3]: the frontend does not
//        normalize a 32-bit shift-amount const to the LHS type, so bare `>> 1`
//        yields an i32 rhs and validate fails; `1u32` is identical Rust semantics).
//   (S6) The tail `*_finish` of the THREE highest-u128-pressure cores — fa_finish
//        (fadd_core), fm_finish (fmul_core), finish_nat_sub (fdiv_finite) — is
//        INLINED at its unique call site. The trust-cg aarch64 ISel limit (owner #3,
//        "value not defined before use") mishandles a u128 passed as a CALL ARGUMENT
//        under the core's register pressure; inlining removes the u128 call-arg. Body
//        verbatim; semantically identical. fsqrt/fcvt/fti/itf JIT with their finish as
//        separate fns (lower pressure), so those are left unchanged. This is a NEW
//        surfaced manifestation of owner #3 (a u128 call-argument, not the R13 256-bit
//        multiply); documented in the round report.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure <root>` per the README recipe;
// `-C overflow-checks=off -C debug-assertions=off` (the runtime `1u64 << mant`
// shifts + the wrapping subtract S3, exactly as batch-8/9/12). Roots:
//   fp_addsub_root / fp_mul_root / fp_div_root / fp_sqrt_root /
//   fp_cvt_root / fp_fti_root / fp_itf_root.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(clippy::needless_return)]

// ===========================================================================
// (S1) leading_zeros(u128) as an explicit bit-scan — see header.
// ===========================================================================
fn u128_leading_zeros(x: u128) -> u32 {
    let mut n: u32 = 0;
    let mut i: u32 = 128;
    while i > 0 {
        i -= 1;
        if (x >> i) & 1 == 1 {
            return n;
        }
        n += 1;
    }
    n
}

// ===========================================================================
// FIELD EXTRACT + CLASSIFY (integer-only; mirrors fp_bitmodel.rs classify).
// ===========================================================================
fn sign(total: u32, x: u64) -> bool {
    (x >> (total - 1)) & 1 == 1
}
fn exp_field(mant: u32, exp_w: u32, x: u64) -> u32 {
    ((x >> mant) & ((1u64 << exp_w) - 1)) as u32
}
fn exp_max(exp_w: u32) -> u32 {
    (1u32 << exp_w) - 1
}
fn mant_field(mant: u32, x: u64) -> u64 {
    x & ((1u64 << mant) - 1)
}
fn exp_all_ones(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_field(mant, exp_w, x) == exp_max(exp_w)
}
fn exp_all_zero(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_field(mant, exp_w, x) == 0
}
fn mant_zero(mant: u32, x: u64) -> bool {
    mant_field(mant, x) == 0
}
fn is_nan(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_all_ones(mant, exp_w, x) && !mant_zero(mant, x)
}
fn is_inf(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_all_ones(mant, exp_w, x) && mant_zero(mant, x)
}
fn is_zero(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_all_zero(mant, exp_w, x) && mant_zero(mant, x)
}
fn is_subnormal(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_all_zero(mant, exp_w, x) && !mant_zero(mant, x)
}
fn is_normal(mant: u32, exp_w: u32, x: u64) -> bool {
    !exp_all_ones(mant, exp_w, x) && !exp_all_zero(mant, exp_w, x)
}
fn mant_msb(mant: u32, x: u64) -> bool {
    (x >> (mant - 1)) & 1 == 1
}
fn is_qnan(mant: u32, exp_w: u32, x: u64) -> bool {
    is_nan(mant, exp_w, x) && mant_msb(mant, x)
}
fn is_snan(mant: u32, exp_w: u32, x: u64) -> bool {
    is_nan(mant, exp_w, x) && !mant_msb(mant, x)
}

fn word_mask(total: u32) -> u64 {
    if total >= 64 {
        u64::MAX
    } else {
        (1u64 << total) - 1
    }
}
fn fabs(total: u32, x: u64) -> u64 {
    x & !(1u64 << (total - 1)) & word_mask(total)
}
fn fneg(total: u32, x: u64) -> u64 {
    (x ^ (1u64 << (total - 1))) & word_mask(total)
}

// ===========================================================================
// NaN PROCESSING (ARM FPProcessNaNs).
// ===========================================================================
fn quiet(total: u32, mant: u32, x: u64) -> u64 {
    (x | (1u64 << (mant - 1))) & word_mask(total)
}
fn select_nan(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    if is_snan(mant, exp_w, a) {
        quiet(total, mant, a)
    } else if is_snan(mant, exp_w, b) {
        quiet(total, mant, b)
    } else if is_qnan(mant, exp_w, a) {
        a & word_mask(total)
    } else {
        b & word_mask(total)
    }
}

// ===========================================================================
// RNE ROUNDING + result-shape constructors (shared by FADD/FMUL/FCVT).
// ===========================================================================
const GUARD_ROOM: u32 = 3;

fn round_up(lsb: bool, guard: bool, round_or_sticky: bool) -> bool {
    guard && (round_or_sticky || lsb)
}

fn pack(total: u32, mant: u32, exp_w: u32, exp_n: u32, sgn: bool, mant_bits: u64) -> u64 {
    let m = mant_bits & ((1u64 << mant) - 1);
    let e = (exp_n as u64 & ((1u64 << exp_w) - 1)) << mant;
    let s = (sgn as u64) << (total - 1);
    (m | e | s) & word_mask(total)
}

fn default_qnan(total: u32, mant: u32, exp_w: u32) -> u64 {
    pack(total, mant, exp_w, exp_max(exp_w), false, 1u64 << (mant - 1))
}
fn inf_of(total: u32, mant: u32, exp_w: u32, sgn: bool) -> u64 {
    pack(total, mant, exp_w, exp_max(exp_w), sgn, 0)
}
fn zero_of(total: u32, mant: u32, exp_w: u32, sgn: bool) -> u64 {
    pack(total, mant, exp_w, 0, sgn, 0)
}

fn hi_set_u128(x: u128) -> u32 {
    if x == 0 {
        0
    } else {
        127 - u128_leading_zeros(x) // (S1)
    }
}

fn shr_sticky_u128(x: u128, shr: u32) -> u128 {
    if shr == 0 {
        return x;
    }
    if shr >= 128 {
        return (x != 0) as u128;
    }
    let dropped = x & ((1u128 << shr) - 1);
    (x >> shr) | (dropped != 0) as u128
}

// ===========================================================================
// FADD / FSUB / FMUL — RNE.  Work register: u128.
// ===========================================================================
fn sig_build(mant: u32, implicit: bool, x: u64) -> u128 {
    let m = mant_field(mant, x) as u128;
    if implicit {
        m | (1u128 << mant)
    } else {
        m
    }
}

fn round_word(s: u128) -> u128 {
    let lsb = (s >> GUARD_ROOM) & 1 == 1;
    let guard = (s >> (GUARD_ROOM - 1)) & 1 == 1;
    let round_b = (s >> (GUARD_ROOM - 2)) & 1 == 1;
    let sticky_b = s & 1 == 1;
    let r_up = round_up(lsb, guard, round_b || sticky_b);
    let mant_place = s >> GUARD_ROOM;
    if r_up {
        mant_place + 1
    } else {
        mant_place
    }
}

fn fadd_finite(total: u32, mant: u32, exp_w: u32, sa: bool, sb: bool, a: u64, b: u64) -> u64 {
    let same_sign = sa == sb;
    let eza = exp_all_zero(mant, exp_w, a);
    let ezb = exp_all_zero(mant, exp_w, b);
    let ea = if eza { 1 } else { exp_field(mant, exp_w, a) };
    let eb = if ezb { 1 } else { exp_field(mant, exp_w, b) };
    let sig_a = sig_build(mant, !eza, a) << GUARD_ROOM;
    let sig_b = sig_build(mant, !ezb, b) << GUARD_ROOM;
    let a_ge = if ea == eb { sig_a >= sig_b } else { ea > eb };
    let (e_big, e_small, s_big, s_small, sign_big) = if a_ge {
        (ea, eb, sig_a, sig_b, sa)
    } else {
        (eb, ea, sig_b, sig_a, sb)
    };
    let equal_mag = ea == eb && sig_a == sig_b;
    if !same_sign && equal_mag {
        return zero_of(total, mant, exp_w, false);
    }
    // (S6) fadd_core INLINED here. `fadd_core` had u128 PARAMETERS (s_big, s_small);
    // the trust-cg aarch64 ISel limit (owner #3) mishandles a u128 PARAMETER combined
    // with a u128 call-arg inside the body ("value not defined before use"). Inlining
    // makes s_big/s_small LOCALS (computed above), which lowers cleanly. Body verbatim
    // from fadd_core (with the S6-inlined fa_finish tail); sign_r := sign_big.
    let sign_r = sign_big;
    let imp_idx = mant + GUARD_ROOM;
    let d = e_big - e_small;
    let s_small_a = if d >= 128 {
        (s_small != 0) as u128
    } else {
        s_small >> d
    };
    let sticky_a = if d == 0 {
        false
    } else if d >= 128 {
        s_small != 0
    } else {
        (s_small & ((1u128 << d) - 1)) != 0
    };
    let s_comb = if same_sign {
        (s_big + s_small_a) | (sticky_a as u128)
    } else if sticky_a {
        (s_big - s_small_a - 1) | 1
    } else {
        s_big - s_small_a
    };
    let carry = (s_comb >> (imp_idx + 1)) & 1 == 1;
    let s_after_carry = if carry {
        shr_sticky_u128(s_comb, 1)
    } else {
        s_comb
    };
    let e_after_carry = if carry { e_big + 1 } else { e_big };
    let high_set = hi_set_u128(s_after_carry);
    let need_left = !carry && high_set < imp_idx;
    let sh_amt_raw = imp_idx - high_set;
    let exp_headroom = e_after_carry - 1;
    let sh_amt = if need_left && exp_headroom < sh_amt_raw {
        exp_headroom
    } else if need_left {
        sh_amt_raw
    } else {
        0
    };
    let s_norm = if need_left {
        s_after_carry << sh_amt
    } else {
        s_after_carry
    };
    let e_norm = if need_left {
        e_after_carry - sh_amt
    } else {
        e_after_carry
    };
    let s_rounded = round_word(s_norm);
    let post_carry = (s_rounded >> (mant + 1)) & 1 == 1;
    let s_final = if post_carry { s_rounded >> 1 } else { s_rounded };
    let e_final = if post_carry { e_norm + 1 } else { e_norm };
    let implicit_clear = (s_final >> mant) & 1 == 0;
    let subnormal = implicit_clear && e_final == 1;
    let e_after_sub = if subnormal { 0 } else { e_final };
    let overflow = e_after_sub >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_after_sub };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(total, mant, exp_w, out_exp, sign_r, out_mant)
}

#[allow(dead_code)] // inlined into fadd_finite (S6): u128 params trip owner-#3 ISel.
fn fadd_core(
    total: u32,
    mant: u32,
    exp_w: u32,
    sign_r: bool,
    same_sign: bool,
    e_big: u32,
    e_small: u32,
    s_big: u128,
    s_small: u128,
) -> u64 {
    let work_w: u32 = total;
    let _ = work_w;
    let imp_idx = mant + GUARD_ROOM;
    let d = e_big - e_small;
    let s_small_a = if d >= 128 {
        (s_small != 0) as u128
    } else {
        s_small >> d
    };
    let sticky_a = if d == 0 {
        false
    } else if d >= 128 {
        s_small != 0
    } else {
        (s_small & ((1u128 << d) - 1)) != 0
    };
    let s_comb = if same_sign {
        (s_big + s_small_a) | (sticky_a as u128)
    } else if sticky_a {
        (s_big - s_small_a - 1) | 1
    } else {
        s_big - s_small_a
    };
    let carry = (s_comb >> (imp_idx + 1)) & 1 == 1;
    let s_after_carry = if carry {
        shr_sticky_u128(s_comb, 1)
    } else {
        s_comb
    };
    let e_after_carry = if carry { e_big + 1 } else { e_big };
    let high_set = hi_set_u128(s_after_carry);
    let need_left = !carry && high_set < imp_idx;
    let sh_amt_raw = imp_idx - high_set;
    let exp_headroom = e_after_carry - 1;
    let sh_amt = if need_left && exp_headroom < sh_amt_raw {
        exp_headroom
    } else if need_left {
        sh_amt_raw
    } else {
        0
    };
    let s_norm = if need_left {
        s_after_carry << sh_amt
    } else {
        s_after_carry
    };
    let e_norm = if need_left {
        e_after_carry - sh_amt
    } else {
        e_after_carry
    };
    let s_rounded = round_word(s_norm);
    // (S6) fa_finish(total, mant, exp_w, sign_r, e_norm, s_rounded) INLINED. The ISel
    // limit (owner #3, "value not defined before use") mishandles a u128 passed as a
    // CALL ARGUMENT under the core's u128 register pressure; inlining the single-
    // call-site tail removes the u128 call-arg. Body verbatim from fa_finish;
    // semantically identical. (sqrt/cvt keep their finish as separate fns — they JIT.)
    let post_carry = (s_rounded >> (mant + 1)) & 1 == 1;
    let s_final = if post_carry { s_rounded >> 1 } else { s_rounded };
    let e_final = if post_carry { e_norm + 1 } else { e_norm };
    let implicit_clear = (s_final >> mant) & 1 == 0;
    let subnormal = implicit_clear && e_final == 1;
    let e_after_sub = if subnormal { 0 } else { e_final };
    let overflow = e_after_sub >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_after_sub };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(total, mant, exp_w, out_exp, sign_r, out_mant)
}

#[allow(dead_code)] // inlined into fadd_core (S6); kept for reference / the original shape.
fn fa_finish(total: u32, mant: u32, exp_w: u32, sign_r: bool, e_norm: u32, s_rounded: u128) -> u64 {
    let post_carry = (s_rounded >> (mant + 1)) & 1 == 1;
    let s_final = if post_carry {
        s_rounded >> 1
    } else {
        s_rounded
    };
    let e_final = if post_carry { e_norm + 1 } else { e_norm };
    let implicit_clear = (s_final >> mant) & 1 == 0;
    let subnormal = implicit_clear && e_final == 1;
    let e_after_sub = if subnormal { 0 } else { e_final };
    let overflow = e_after_sub >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_after_sub };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(total, mant, exp_w, out_exp, sign_r, out_mant)
}

fn fadd(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    let a = a & word_mask(total);
    let b = b & word_mask(total);
    let sa = sign(total, a);
    let sb = sign(total, b);
    if is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b) {
        return select_nan(total, mant, exp_w, a, b);
    }
    if is_inf(mant, exp_w, a) {
        if is_inf(mant, exp_w, b) {
            return if sa == sb {
                inf_of(total, mant, exp_w, sa)
            } else {
                default_qnan(total, mant, exp_w)
            };
        }
        return inf_of(total, mant, exp_w, sa);
    }
    if is_inf(mant, exp_w, b) {
        return inf_of(total, mant, exp_w, sb);
    }
    if is_zero(mant, exp_w, a) {
        if is_zero(mant, exp_w, b) {
            return if sa && sb {
                zero_of(total, mant, exp_w, true)
            } else {
                zero_of(total, mant, exp_w, false)
            };
        }
        return b;
    }
    if is_zero(mant, exp_w, b) {
        return a;
    }
    fadd_finite(total, mant, exp_w, sa, sb, a, b)
}

fn fsub(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    let a = a & word_mask(total);
    let b = b & word_mask(total);
    // owner #8 fix: FSUB propagates a NaN operand with its ORIGINAL sign; dispatch NaN
    // over (a, b) here rather than fadd(a, fneg(b)) which would flip a b-NaN's sign.
    if is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b) {
        return select_nan(total, mant, exp_w, a, b);
    }
    fadd(total, mant, exp_w, a, fneg(total, b))
}

fn fmul(total: u32, mant: u32, exp_w: u32, bias: u32, a: u64, b: u64) -> u64 {
    let a = a & word_mask(total);
    let b = b & word_mask(total);
    let sa = sign(total, a);
    let sb = sign(total, b);
    let sgn = sa ^ sb;
    if is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b) {
        return select_nan(total, mant, exp_w, a, b);
    }
    if is_inf(mant, exp_w, a) {
        return if is_zero(mant, exp_w, b) {
            default_qnan(total, mant, exp_w)
        } else {
            inf_of(total, mant, exp_w, sgn)
        };
    }
    if is_inf(mant, exp_w, b) {
        return if is_zero(mant, exp_w, a) {
            default_qnan(total, mant, exp_w)
        } else {
            inf_of(total, mant, exp_w, sgn)
        };
    }
    if is_zero(mant, exp_w, a) || is_zero(mant, exp_w, b) {
        return zero_of(total, mant, exp_w, sgn);
    }
    fmul_finite(total, mant, exp_w, bias, sgn, a, b)
}

fn fmul_finite(total: u32, mant: u32, exp_w: u32, bias: u32, sgn: bool, a: u64, b: u64) -> u64 {
    let eza = exp_all_zero(mant, exp_w, a);
    let ezb = exp_all_zero(mant, exp_w, b);
    let sa_w = sig_build(mant, !eza, a);
    let sb_w = sig_build(mant, !ezb, b);
    let ea = if eza { 1u32 } else { exp_field(mant, exp_w, a) };
    let eb = if ezb { 1u32 } else { exp_field(mant, exp_w, b) };
    // (S6) fmul_core INLINED here (sa_w/sb_w were u128 PARAMETERS -> now LOCALS).
    // See fadd_finite for the owner-#3 ISel rationale. Body verbatim from fmul_core
    // (with the S6-inlined fm_finish tail).
    let prod = sa_w * sb_w;
    let top = hi_set_u128(prod);
    let target = mant + GUARD_ROOM;
    let big_s = top + ea + eb;
    let big_d = bias + 2 * mant;
    let underflow = big_s <= big_d;
    let extra = if underflow { 1 + (big_d - big_s) } else { 0 };
    let shift_src = top + extra;
    let need_left = shift_src < target;
    let shr = if shift_src >= target {
        shift_src - target
    } else {
        0
    };
    let shl = if target >= shift_src {
        target - shift_src
    } else {
        0
    };
    let out_e = if underflow { 0 } else { big_s - big_d };
    let p_placed = if need_left {
        prod << shl
    } else {
        shr_sticky_u128(prod, shr)
    };
    let s_rounded = round_word(p_placed);
    let post_carry = (s_rounded >> (mant + 1)) & 1 == 1;
    let s_final = if post_carry { s_rounded >> 1 } else { s_rounded };
    let e_fin0 = if post_carry { out_e + 1 } else { out_e };
    let implicit_set = (s_final >> mant) & 1 == 1;
    let promote = out_e == 0 && implicit_set;
    let e_fin = if promote { 1 } else { e_fin0 };
    let overflow = e_fin >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_fin };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(total, mant, exp_w, out_exp, sgn, out_mant)
}

#[allow(dead_code)] // inlined into fmul_finite (S6): u128 params trip owner-#3 ISel.
fn fmul_core(
    total: u32,
    mant: u32,
    exp_w: u32,
    bias: u32,
    sgn: bool,
    ea: u32,
    eb: u32,
    sa_w: u128,
    sb_w: u128,
) -> u64 {
    let prod = sa_w * sb_w;
    let top = hi_set_u128(prod);
    let target = mant + GUARD_ROOM;
    let big_s = top + ea + eb;
    let big_d = bias + 2 * mant;
    let underflow = big_s <= big_d;
    let extra = if underflow { 1 + (big_d - big_s) } else { 0 };
    let shift_src = top + extra;
    let need_left = shift_src < target;
    // (S2) shift_src.saturating_sub(target)
    let shr = if shift_src >= target {
        shift_src - target
    } else {
        0
    };
    // (S2) target.saturating_sub(shift_src)
    let shl = if target >= shift_src {
        target - shift_src
    } else {
        0
    };
    let out_e = if underflow { 0 } else { big_s - big_d };
    let p_placed = if need_left {
        prod << shl
    } else {
        shr_sticky_u128(prod, shr)
    };
    let s_rounded = round_word(p_placed);
    // (S6) fm_finish(total, mant, exp_w, sgn, out_e, s_rounded) INLINED — see fadd_core.
    let post_carry = (s_rounded >> (mant + 1)) & 1 == 1;
    let s_final = if post_carry { s_rounded >> 1 } else { s_rounded };
    let e_fin0 = if post_carry { out_e + 1 } else { out_e };
    let implicit_set = (s_final >> mant) & 1 == 1;
    let promote = out_e == 0 && implicit_set;
    let e_fin = if promote { 1 } else { e_fin0 };
    let overflow = e_fin >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_fin };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(total, mant, exp_w, out_exp, sgn, out_mant)
}

#[allow(dead_code)] // inlined into fmul_core (S6).
fn fm_finish(total: u32, mant: u32, exp_w: u32, sign_r: bool, out_e: u32, s_rounded: u128) -> u64 {
    let post_carry = (s_rounded >> (mant + 1)) & 1 == 1;
    let s_final = if post_carry {
        s_rounded >> 1
    } else {
        s_rounded
    };
    let e_fin0 = if post_carry { out_e + 1 } else { out_e };
    let implicit_set = (s_final >> mant) & 1 == 1;
    let promote = out_e == 0 && implicit_set;
    let e_fin = if promote { 1 } else { e_fin0 };
    let overflow = e_fin >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_fin };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(total, mant, exp_w, out_exp, sign_r, out_mant)
}

// ===========================================================================
// FCVT  f32 <-> f64  (widen exact / narrow RNE).  F32=(32,23,8,127) F64=(64,52,11,1023)
// ===========================================================================
fn fcvt_widen(x: u64) -> u64 {
    let x = x & word_mask(32);
    let s = sign(32, x);
    if is_nan(23, 8, x) {
        let m32 = mant_field(23, x);
        let mut m64 = m32 << 29;
        if is_snan(23, 8, x) {
            m64 |= 1u64 << 51;
        }
        return pack(64, 52, 11, 2047, s, m64);
    }
    if is_inf(23, 8, x) {
        return inf_of(64, 52, 11, s);
    }
    if is_zero(23, 8, x) {
        return zero_of(64, 52, 11, s);
    }
    if exp_all_zero(23, 8, x) {
        let m32 = mant_field(23, x);
        let hi = hi_set_u128(m32 as u128);
        let e64 = hi + 874;
        let m64 = ((m32 << (52 - hi)) as u128 & ((1u128 << 52) - 1)) as u64;
        pack(64, 52, 11, e64, s, m64)
    } else {
        let e32 = exp_field(23, 8, x);
        let m32 = mant_field(23, x);
        pack(64, 52, 11, e32 + 896, s, m32 << 29)
    }
}

fn fcvt_narrow(x: u64) -> u64 {
    let s = sign(64, x);
    if is_nan(52, 11, x) {
        let m64 = mant_field(52, x);
        let m32 = (m64 >> 29) | (1u64 << 22);
        return pack(32, 23, 8, 255, s, m32);
    }
    if is_inf(52, 11, x) {
        return inf_of(32, 23, 8, s);
    }
    if is_zero(52, 11, x) {
        return zero_of(32, 23, 8, s);
    }
    let e64 = exp_field(52, 11, x);
    let sig = sig_build(52, !exp_all_zero(52, 11, x), x);
    let normal_target = e64 > 896;
    let extra = if normal_target { 0 } else { 897 - e64 };
    let shr = 26 + extra;
    let e_cand = if normal_target { e64 - 896 } else { 1 };
    let s_shift = shr_sticky_u128(sig, shr);
    let s_rounded = round_word(s_shift);
    nar_finish(s, e_cand, s_rounded)
}

fn nar_finish(sign_r: bool, e_cand: u32, s_rounded: u128) -> u64 {
    let post_carry = (s_rounded >> 24) & 1 == 1;
    let s_final = if post_carry {
        s_rounded >> 1
    } else {
        s_rounded
    };
    let e_final = if post_carry { e_cand + 1 } else { e_cand };
    let implicit_clear = (s_final >> 23) & 1 == 0;
    let subnormal = implicit_clear && e_final == 1;
    let e_after_sub = if subnormal { 0 } else { e_final };
    let overflow = e_after_sub >= 255;
    let out_exp = if overflow { 255 } else { e_after_sub };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(32, 23, 8, out_exp, sign_r, out_mant)
}

// ===========================================================================
// FCVT  f16 <-> f32 / f64.  F16=(16,10,5,15).
// ===========================================================================
fn fp16_widen(dst_total: u32, dst_mant: u32, dst_exp_w: u32, dst_bias: u32, x: u64) -> u64 {
    let x = x & word_mask(16);
    let s = sign(16, x);
    if is_nan(10, 5, x) {
        let m16 = mant_field(10, x);
        let mut m_dst = m16 << (dst_mant - 10);
        if is_snan(10, 5, x) {
            m_dst |= 1u64 << (dst_mant - 1);
        }
        return pack(dst_total, dst_mant, dst_exp_w, exp_max(dst_exp_w), s, m_dst);
    }
    if is_inf(10, 5, x) {
        return inf_of(dst_total, dst_mant, dst_exp_w, s);
    }
    if is_zero(10, 5, x) {
        return zero_of(dst_total, dst_mant, dst_exp_w, s);
    }
    if exp_all_zero(10, 5, x) {
        let m16 = mant_field(10, x);
        let hi = hi_set_u128(m16 as u128);
        let e_dst = hi + dst_bias - 24;
        let m_dst = ((m16 << (dst_mant - hi)) as u128 & ((1u128 << dst_mant) - 1)) as u64;
        pack(dst_total, dst_mant, dst_exp_w, e_dst, s, m_dst)
    } else {
        let e16 = exp_field(10, 5, x);
        let m16 = mant_field(10, x);
        pack(dst_total, dst_mant, dst_exp_w, e16 + dst_bias - 15, s, m16 << (dst_mant - 10))
    }
}

fn fcvt_h_to_s(x: u64) -> u64 {
    fp16_widen(32, 23, 8, 127, x)
}
fn fcvt_h_to_d(x: u64) -> u64 {
    fp16_widen(64, 52, 11, 1023, x)
}

fn nar_finish16(sign_r: bool, e_cand: u32, s_rounded: u128) -> u64 {
    let post_carry = (s_rounded >> 11) & 1 == 1;
    let s_final = if post_carry {
        s_rounded >> 1
    } else {
        s_rounded
    };
    let e_final = if post_carry { e_cand + 1 } else { e_cand };
    let implicit_clear = (s_final >> 10) & 1 == 0;
    let subnormal = implicit_clear && e_final == 1;
    let e_after_sub = if subnormal { 0 } else { e_final };
    let overflow = e_after_sub >= 31;
    let out_exp = if overflow { 31 } else { e_after_sub };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(16, 10, 5, out_exp, sign_r, out_mant)
}

fn fp16_narrow_finite(src_total: u32, src_mant: u32, src_exp_w: u32, src_bias: u32, x: u64) -> u64 {
    let s = sign(src_total, x);
    let eb = exp_field(src_mant, src_exp_w, x);
    let sig = sig_build(src_mant, !exp_all_zero(src_mant, src_exp_w, x), x);
    let imp_pos = src_mant;
    let thresh = src_bias - 15;
    let normal_target = eb > thresh;
    let ef0 = if normal_target {
        eb + 15 - src_bias
    } else {
        0
    };
    let extra = if normal_target {
        0
    } else {
        (src_bias + 1) - (eb + 15)
    };
    let shr = (imp_pos - 13) + extra;
    let e_cand = if normal_target { ef0 } else { 1 };
    let s_shift = shr_sticky_u128(sig, shr);
    let s_rounded = round_word(s_shift);
    nar_finish16(s, e_cand, s_rounded)
}

fn fp16_narrow(src_total: u32, src_mant: u32, src_exp_w: u32, src_bias: u32, x: u64) -> u64 {
    let x = x & word_mask(src_total);
    let s = sign(src_total, x);
    if is_nan(src_mant, src_exp_w, x) {
        let m = mant_field(src_mant, x);
        let m16 = (m >> (src_mant - 10)) | (1u64 << 9);
        return pack(16, 10, 5, 31, s, m16);
    }
    if is_inf(src_mant, src_exp_w, x) {
        return inf_of(16, 10, 5, s);
    }
    if is_zero(src_mant, src_exp_w, x) {
        return zero_of(16, 10, 5, s);
    }
    fp16_narrow_finite(src_total, src_mant, src_exp_w, src_bias, x)
}

fn fcvt_s_to_h(x: u64) -> u64 {
    fp16_narrow(32, 23, 8, 127, x)
}
fn fcvt_d_to_h(x: u64) -> u64 {
    fp16_narrow(64, 52, 11, 1023, x)
}

// ===========================================================================
// FCVT  f -> int  (FCVTZS/ZU round-to-zero, FCVTNS/NU round-to-nearest).
// ===========================================================================

fn mask_low(n: u32, x: u128) -> u128 {
    if n >= 128 {
        x
    } else {
        x & ((1u128 << n) - 1)
    }
}

fn fti_finish_u(int_w: u32, neg: bool, mag: u128) -> u128 {
    let u_max: u128 = if int_w >= 128 {
        !0u128 // (S4) u128::MAX, canonically emitted as Constant::U128.
    } else {
        (1u128 << int_w) - 1
    };
    let sat = if mag > u_max { u_max } else { mag };
    let v = if neg { 0 } else { sat };
    mask_low(int_w, v)
}

fn fti_finish_s(int_w: u32, neg: bool, mag: u128) -> u128 {
    let s_max: u128 = (1u128 << (int_w - 1)) - 1;
    let s_min_mag: u128 = 1u128 << (int_w - 1);
    let result: u128 = if neg {
        if mag <= s_min_mag {
            0u128 - mag // (S3) 0u128.wrapping_sub(mag)
        } else {
            0u128 - s_min_mag // (S3)
        }
    } else if mag > s_max {
        s_max
    } else {
        mag
    };
    mask_low(int_w, result)
}

fn fti_core(
    total: u32,
    mant: u32,
    exp_w: u32,
    bias: u32,
    int_w: u32,
    signed: bool,
    nearest: bool,
    sgn: bool,
    x: u64,
) -> u128 {
    let subn = exp_all_zero(mant, exp_w, x);
    let eb = exp_field(mant, exp_w, x);
    let sig = sig_build(mant, !subn, x);
    let pos_part: u32 = if subn { 2 } else { eb + 1 };
    let sub_part: u32 = bias + mant;
    // (S2) pos_part.saturating_sub(sub_part)
    let shl2 = if pos_part >= sub_part {
        pos_part - sub_part
    } else {
        0
    };
    // (S2) sub_part.saturating_sub(pos_part)
    let shr2 = if sub_part >= pos_part {
        sub_part - pos_part
    } else {
        0
    };
    let aligned: u128 = if shl2 > 0 {
        // (S2) shl2.min(127)
        sig << (if shl2 < 127 { shl2 } else { 127 })
    } else if shr2 > 0 {
        if shr2 >= 128 {
            0
        } else {
            sig >> shr2
        }
    } else {
        sig
    };
    let sticky: bool = if shr2 > 0 {
        if shr2 >= 128 {
            sig != 0
        } else {
            (sig & ((1u128 << shr2) - 1)) != 0
        }
    } else {
        false
    };
    let int_trunc = aligned >> 1;
    let rounded_raw: u128 = if nearest {
        let int_part = aligned >> 1;
        let guard = aligned & 1 == 1;
        let lsb = int_part & 1 == 1;
        let r_up = guard && (sticky || lsb);
        if r_up {
            int_part + 1
        } else {
            int_part
        }
    } else {
        int_trunc
    };
    // owner #9 fix: saturate on u128 overflow of sig<<shl2, not just shl2>=128
    // (missed exact powers of two like f32 2^127 -> aligned wrapped to 0).
    let too_big = shl2 > 0 && shl2 > u128_leading_zeros(sig);
    let over_mag: u128 = 1u128 << int_w;
    let rounded = if too_big { over_mag } else { rounded_raw };
    if signed {
        fti_finish_s(int_w, sgn, rounded)
    } else {
        fti_finish_u(int_w, sgn, rounded)
    }
}

fn fti(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, signed: bool, nearest: bool, x: u64) -> u64 {
    let x = x & word_mask(total);
    let sgn = sign(total, x);
    let over_mag: u128 = 1u128 << int_w;
    let r = if is_nan(mant, exp_w, x) {
        0
    } else if is_inf(mant, exp_w, x) {
        if signed {
            fti_finish_s(int_w, sgn, over_mag)
        } else {
            fti_finish_u(int_w, sgn, over_mag)
        }
    } else if is_zero(mant, exp_w, x) {
        0
    } else {
        fti_core(total, mant, exp_w, bias, int_w, signed, nearest, sgn, x)
    };
    mask_low(int_w, r) as u64
}

fn fcvtzs(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, x: u64) -> u64 {
    fti(total, mant, exp_w, bias, int_w, true, false, x)
}
fn fcvtzu(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, x: u64) -> u64 {
    fti(total, mant, exp_w, bias, int_w, false, false, x)
}
fn fcvtns(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, x: u64) -> u64 {
    fti(total, mant, exp_w, bias, int_w, true, true, x)
}
fn fcvtnu(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, x: u64) -> u64 {
    fti(total, mant, exp_w, bias, int_w, false, true, x)
}

// x86 f -> SIGNED int (integer-indefinite OOR).
fn integer_indefinite(int_w: u32) -> u128 {
    mask_low(int_w, 1u128 << (int_w - 1))
}

fn fti_mag(total: u32, mant: u32, exp_w: u32, bias: u32, nearest: bool, x: u64) -> (u128, bool) {
    let subn = exp_all_zero(mant, exp_w, x);
    let eb = exp_field(mant, exp_w, x);
    let sig = sig_build(mant, !subn, x);
    let pos_part: u32 = if subn { 2 } else { eb + 1 };
    let sub_part: u32 = bias + mant;
    // (S2)
    let shl2 = if pos_part >= sub_part {
        pos_part - sub_part
    } else {
        0
    };
    // (S2)
    let shr2 = if sub_part >= pos_part {
        sub_part - pos_part
    } else {
        0
    };
    let aligned: u128 = if shl2 > 0 {
        // (S2)
        sig << (if shl2 < 127 { shl2 } else { 127 })
    } else if shr2 > 0 {
        if shr2 >= 128 {
            0
        } else {
            sig >> shr2
        }
    } else {
        sig
    };
    let sticky: bool = if shr2 > 0 {
        if shr2 >= 128 {
            sig != 0
        } else {
            (sig & ((1u128 << shr2) - 1)) != 0
        }
    } else {
        false
    };
    let rounded_raw: u128 = if nearest {
        let int_part = aligned >> 1;
        let guard = aligned & 1 == 1;
        let lsb = int_part & 1 == 1;
        if guard && (sticky || lsb) {
            int_part + 1
        } else {
            int_part
        }
    } else {
        aligned >> 1
    };
    // owner #9 fix: saturate on u128 overflow of sig<<shl2, not just shl2>=128.
    let too_big = shl2 > 0 && shl2 > u128_leading_zeros(sig);
    (rounded_raw, too_big)
}

fn fti_indef_s(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, nearest: bool, x: u64) -> u64 {
    let x = x & word_mask(total);
    if is_nan(mant, exp_w, x) || is_inf(mant, exp_w, x) {
        return mask_low(int_w, integer_indefinite(int_w)) as u64;
    }
    if is_zero(mant, exp_w, x) {
        return 0;
    }
    let sgn = sign(total, x);
    let (mag, too_big) = fti_mag(total, mant, exp_w, bias, nearest, x);
    let s_max: u128 = (1u128 << (int_w - 1)) - 1;
    let s_min_mag: u128 = 1u128 << (int_w - 1);
    let out_of_range = too_big || if sgn { mag > s_min_mag } else { mag > s_max };
    if out_of_range {
        return mask_low(int_w, integer_indefinite(int_w)) as u64;
    }
    let result: u128 = if sgn { 0u128 - mag } else { mag }; // (S3)
    mask_low(int_w, result) as u64
}

fn cvtt_to_si(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, x: u64) -> u64 {
    fti_indef_s(total, mant, exp_w, bias, int_w, false, x)
}
fn cvt_to_si(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, x: u64) -> u64 {
    fti_indef_s(total, mant, exp_w, bias, int_w, true, x)
}

// ===========================================================================
// int -> f  (SCVTF / UCVTF), RNE.
// ===========================================================================
fn itf(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, signed: bool, x: u64) -> u64 {
    let src = mask_low(int_w, x as u128);
    if src == 0 {
        return zero_of(total, mant, exp_w, false);
    }
    let neg = signed && ((x >> (int_w - 1)) & 1 == 1);
    let mag: u128 = if neg {
        mask_low(int_w, 0u128 - src) // (S3)
    } else {
        src
    };
    let sgn = neg;
    itf_core(total, mant, exp_w, bias, sgn, mag)
}

fn itf_core(total: u32, mant: u32, exp_w: u32, bias: u32, sgn: bool, mag: u128) -> u64 {
    let hi = hi_set_u128(mag);
    let target = mant + GUARD_ROOM;
    let placed: u128 = if target < hi {
        let shr = hi - target;
        shr_sticky_u128(mag, shr)
    } else {
        mag << (target - hi)
    };
    let e_cand = hi + bias;
    let s_rounded = round_word(placed);
    let post_carry = (s_rounded >> (mant + 1)) & 1 == 1;
    let s_final = if post_carry {
        s_rounded >> 1
    } else {
        s_rounded
    };
    let e_final = if post_carry { e_cand + 1 } else { e_cand };
    let overflow = e_final >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_final };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(total, mant, exp_w, out_exp, sgn, out_mant)
}

fn scvtf(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, x: u64) -> u64 {
    itf(total, mant, exp_w, bias, int_w, true, x)
}
fn ucvtf(total: u32, mant: u32, exp_w: u32, bias: u32, int_w: u32, x: u64) -> u64 {
    itf(total, mant, exp_w, bias, int_w, false, x)
}

// ===========================================================================
// FDIV / FSQRT — RNE.
// ===========================================================================
fn sig_nat(mant: u32, subn: bool, x: u64) -> u128 {
    let m = mant_field(mant, x) as u128;
    if subn {
        m
    } else {
        m | (1u128 << mant)
    }
}

fn eff_exp(mant: u32, exp_w: u32, x: u64) -> u32 {
    if exp_all_zero(mant, exp_w, x) {
        1
    } else {
        exp_field(mant, exp_w, x)
    }
}

fn sticky_shr_u128(v: u128, k: u32) -> bool {
    if k == 0 {
        false
    } else if k >= 128 {
        v != 0
    } else {
        (v & ((1u128 << k) - 1)) != 0
    }
}

fn shr_u128(v: u128, k: u32) -> u128 {
    if k >= 128 {
        0
    } else {
        v >> k
    }
}

fn round_nat(placed: u128, extra_sticky: bool) -> u128 {
    let lsb = (placed >> GUARD_ROOM) & 1 == 1;
    let guard = (placed >> 2) & 1 == 1;
    let round_b = (placed >> 1) & 1 == 1;
    let sticky_b = extra_sticky || (placed & 1 == 1);
    let r_up = round_up(lsb, guard, round_b || sticky_b);
    let mant_place = placed >> GUARD_ROOM;
    if r_up {
        mant_place + 1
    } else {
        mant_place
    }
}

fn finish_nat(total: u32, mant: u32, exp_w: u32, sign_r: bool, e_cand: u32, sig: u128) -> u64 {
    let post_carry = (sig >> (mant + 1)) & 1 == 1;
    let s_fin = if post_carry { sig >> 1 } else { sig };
    let e_fin = if post_carry { e_cand + 1 } else { e_cand };
    let overflow = e_fin >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_fin };
    let out_mant = if overflow {
        0
    } else {
        (s_fin as u64) & ((1u64 << mant) - 1)
    };
    pack(total, mant, exp_w, out_exp, sign_r, out_mant)
}

#[allow(dead_code)] // inlined into fdiv_finite (S6).
fn finish_nat_sub(total: u32, mant: u32, exp_w: u32, sign_r: bool, out_e: u32, sig: u128) -> u64 {
    let post_carry = (sig >> (mant + 1)) & 1 == 1;
    let s_fin = if post_carry { sig >> 1 } else { sig };
    let e_fin0 = if post_carry { out_e + 1 } else { out_e };
    let promote = out_e == 0 && ((s_fin >> mant) & 1 == 1);
    let e_fin = if promote { 1 } else { e_fin0 };
    let overflow = e_fin >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_fin };
    let out_mant = if overflow {
        0
    } else {
        (s_fin as u64) & ((1u64 << mant) - 1)
    };
    pack(total, mant, exp_w, out_exp, sign_r, out_mant)
}

fn div_long(bits_n: u32, num: u128, den: u128) -> (u128, u128) {
    let mut rem: u128 = 0;
    let mut q: u128 = 0;
    let mut i = bits_n;
    while i > 0 {
        i -= 1;
        let bit = (num >> i) & 1;
        let rem2 = rem * 2 + bit;
        let ge = rem2 >= den;
        rem = if ge { rem2 - den } else { rem2 };
        q = q * 2 + if ge { 1 } else { 0 };
    }
    (q, rem)
}

#[allow(dead_code)] // inlined into fdiv (S6): u128 params trip owner-#3 ISel.
fn fdiv_finite(
    total: u32,
    mant: u32,
    exp_w: u32,
    bias: u32,
    sign_r: bool,
    ea_e: u32,
    eb_e: u32,
    sig_a: u128,
    sig_b: u128,
) -> u64 {
    let s_a = mant - hi_set_u128(sig_a);
    let s_b = mant - hi_set_u128(sig_b);
    let sig_a = sig_a << s_a;
    let sig_b = sig_b << s_b;
    let big_s = mant + GUARD_ROOM + 2;
    let num = sig_a << big_s;
    let bits_n = hi_set_u128(num) + 1;
    let (q, rem) = div_long(bits_n, num, sig_b);
    let div_sticky = rem != 0;
    let qhi = hi_set_u128(q);
    let target = mant + GUARD_ROOM;
    let pos_part = qhi + ea_e + bias + s_b;
    let sub_part = eb_e + big_s + s_a;
    let underflow = pos_part <= sub_part;
    let extra = if underflow {
        (sub_part - pos_part) + 1
    } else {
        0
    };
    let shift_src = qhi + extra;
    let need_right = shift_src > target;
    // (S2)
    let shr = if shift_src >= target {
        shift_src - target
    } else {
        0
    };
    // (S2)
    let shl = if target >= shift_src {
        target - shift_src
    } else {
        0
    };
    let place_sticky = need_right && sticky_shr_u128(q, shr);
    let placed = if need_right {
        shr_u128(q, shr)
    } else {
        q << shl
    };
    let out_e = if underflow { 0 } else { pos_part - sub_part };
    let rounded = round_nat(placed, div_sticky || place_sticky);
    // (S6) finish_nat_sub(total, mant, exp_w, sign_r, out_e, rounded) INLINED — see fadd_core.
    let post_carry = (rounded >> (mant + 1)) & 1 == 1;
    let s_fin = if post_carry { rounded >> 1 } else { rounded };
    let e_fin0 = if post_carry { out_e + 1 } else { out_e };
    let promote = out_e == 0 && ((s_fin >> mant) & 1 == 1);
    let e_fin = if promote { 1 } else { e_fin0 };
    let overflow = e_fin >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_fin };
    let out_mant = if overflow { 0 } else { (s_fin as u64) & ((1u64 << mant) - 1) };
    pack(total, mant, exp_w, out_exp, sign_r, out_mant)
}

fn fdiv(total: u32, mant: u32, exp_w: u32, bias: u32, a: u64, b: u64) -> u64 {
    let a = a & word_mask(total);
    let b = b & word_mask(total);
    let sgn = sign(total, a) ^ sign(total, b);
    if is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b) {
        return select_nan(total, mant, exp_w, a, b);
    }
    if is_inf(mant, exp_w, a) {
        return if is_inf(mant, exp_w, b) {
            default_qnan(total, mant, exp_w)
        } else {
            inf_of(total, mant, exp_w, sgn)
        };
    }
    if is_inf(mant, exp_w, b) {
        return zero_of(total, mant, exp_w, sgn);
    }
    if is_zero(mant, exp_w, a) {
        return if is_zero(mant, exp_w, b) {
            default_qnan(total, mant, exp_w)
        } else {
            zero_of(total, mant, exp_w, sgn)
        };
    }
    if is_zero(mant, exp_w, b) {
        return inf_of(total, mant, exp_w, sgn);
    }
    // (S6) fdiv_finite INLINED here (sig_a/sig_b were u128 PARAMETERS -> now LOCALS,
    // computed by sig_nat). See fadd_finite for the owner-#3 ISel rationale. Body
    // verbatim from fdiv_finite (with the S6-inlined finish_nat_sub tail).
    let sign_r = sgn;
    let ea_e = eff_exp(mant, exp_w, a);
    let eb_e = eff_exp(mant, exp_w, b);
    let sig_a = sig_nat(mant, exp_all_zero(mant, exp_w, a), a);
    let sig_b = sig_nat(mant, exp_all_zero(mant, exp_w, b), b);
    let s_a = mant - hi_set_u128(sig_a);
    let s_b = mant - hi_set_u128(sig_b);
    let sig_a = sig_a << s_a;
    let sig_b = sig_b << s_b;
    let big_s = mant + GUARD_ROOM + 2;
    let num = sig_a << big_s;
    let bits_n = hi_set_u128(num) + 1;
    let (q, rem) = div_long(bits_n, num, sig_b);
    let div_sticky = rem != 0;
    let qhi = hi_set_u128(q);
    let target = mant + GUARD_ROOM;
    let pos_part = qhi + ea_e + bias + s_b;
    let sub_part = eb_e + big_s + s_a;
    let underflow = pos_part <= sub_part;
    let extra = if underflow {
        (sub_part - pos_part) + 1
    } else {
        0
    };
    let shift_src = qhi + extra;
    let need_right = shift_src > target;
    let shr = if shift_src >= target {
        shift_src - target
    } else {
        0
    };
    let shl = if target >= shift_src {
        target - shift_src
    } else {
        0
    };
    let place_sticky = need_right && sticky_shr_u128(q, shr);
    let placed = if need_right {
        shr_u128(q, shr)
    } else {
        q << shl
    };
    let out_e = if underflow { 0 } else { pos_part - sub_part };
    let rounded = round_nat(placed, div_sticky || place_sticky);
    let post_carry = (rounded >> (mant + 1)) & 1 == 1;
    let s_fin = if post_carry { rounded >> 1 } else { rounded };
    let e_fin0 = if post_carry { out_e + 1 } else { out_e };
    let promote = out_e == 0 && ((s_fin >> mant) & 1 == 1);
    let e_fin = if promote { 1 } else { e_fin0 };
    let overflow = e_fin >= exp_max(exp_w);
    let out_exp = if overflow { exp_max(exp_w) } else { e_fin };
    let out_mant = if overflow { 0 } else { (s_fin as u64) & ((1u64 << mant) - 1) };
    pack(total, mant, exp_w, out_exp, sign_r, out_mant)
}

fn sqrt_digits(iters: u32, sig_e: u128, two_fbits: u32) -> (u128, u128) {
    let mut rem: u128 = 0;
    let mut root: u128 = 0;
    let mut i = iters;
    while i > 0 {
        i -= 1;
        let pos = i * 2;
        let two_bits = if pos >= two_fbits {
            (sig_e >> (pos - two_fbits)) & 3
        } else if pos + 1 == two_fbits {
            (sig_e & 1) << 1
        } else {
            0
        };
        let rem4 = rem * 4 + two_bits;
        let cand = root * 4 + 1;
        let ge = rem4 >= cand;
        rem = if ge { rem4 - cand } else { rem4 };
        root = root * 2 + if ge { 1 } else { 0 };
    }
    (root, rem)
}

fn fsqrt_finite(total: u32, mant: u32, exp_w: u32, bias: u32, e_e: u32, sig: u128) -> u64 {
    const SQ_OFF: u32 = 4096;
    let fbits = mant + GUARD_ROOM + 3;
    let p_off = (e_e + SQ_OFF) - (bias + mant);
    let odd = p_off & 1 == 1;
    let sig_e = if odd { sig << 1 } else { sig };
    let p_prime_off = if odd { p_off - 1 } else { p_off };
    let two_fbits = fbits * 2;
    let m_hi = hi_set_u128(sig_e) + two_fbits;
    let iters = (m_hi >> 1u32) + 1; // (S5) 1u32 suffix: F3 — the frontend does not
    let (root, rem) = sqrt_digits(iters, sig_e, two_fbits); // normalize a 32-bit
    let sticky = rem != 0; // shift-amount const to the LHS type (unlike 64-bit),
    let rhi = hi_set_u128(root); // so bare `>> 1` on a u32 gives an i32 rhs -> validate
    let half_off = SQ_OFF >> 1u32; // fails. `1u32` is identical Rust semantics.
    let half_prime_off = p_prime_off >> 1u32; // (S5)
    let pos_part = rhi + half_prime_off + bias;
    let sub_part = half_off + fbits;
    let e_cand = pos_part - sub_part;
    let target = mant + GUARD_ROOM;
    let need_right = rhi > target;
    // (S2)
    let shr = if rhi >= target { rhi - target } else { 0 };
    // (S2)
    let shl = if target >= rhi { target - rhi } else { 0 };
    let place_sticky = need_right && sticky_shr_u128(root, shr);
    let placed = if need_right {
        shr_u128(root, shr)
    } else {
        root << shl
    };
    let rounded = round_nat(placed, sticky || place_sticky);
    finish_nat(total, mant, exp_w, false, e_cand, rounded)
}

fn fsqrt(total: u32, mant: u32, exp_w: u32, bias: u32, a: u64) -> u64 {
    let a = a & word_mask(total);
    if is_nan(mant, exp_w, a) {
        return select_nan(total, mant, exp_w, a, a);
    }
    if sign(total, a) {
        return if is_zero(mant, exp_w, a) {
            a
        } else {
            default_qnan(total, mant, exp_w)
        };
    }
    if is_inf(mant, exp_w, a) {
        return a;
    }
    if is_zero(mant, exp_w, a) {
        return a;
    }
    fsqrt_finite(total, mant, exp_w, bias, eff_exp(mant, exp_w, a), sig_nat(mant, exp_all_zero(mant, exp_w, a), a))
}

// ===========================================================================
// MONO ROOTS — write results to a 0xDEAD-poisonable out-POD (round-11/12 style).
// ===========================================================================

#[repr(C)]
pub struct AddSubOut {
    pub fadd: u64,
    pub fsub: u64,
}
#[no_mangle]
pub extern "C" fn fp_addsub_root(total: u32, mant: u32, exp_w: u32, a: u64, b: u64, out: *mut AddSubOut) {
    let r = AddSubOut {
        fadd: fadd(total, mant, exp_w, a, b),
        fsub: fsub(total, mant, exp_w, a, b),
    };
    unsafe {
        *out = r;
    }
}

#[repr(C)]
pub struct MulOut {
    pub fmul: u64,
}
#[no_mangle]
pub extern "C" fn fp_mul_root(total: u32, mant: u32, exp_w: u32, bias: u32, a: u64, b: u64, out: *mut MulOut) {
    let r = MulOut {
        fmul: fmul(total, mant, exp_w, bias, a, b),
    };
    unsafe {
        *out = r;
    }
}

#[repr(C)]
pub struct DivOut {
    pub fdiv: u64,
}
#[no_mangle]
pub extern "C" fn fp_div_root(total: u32, mant: u32, exp_w: u32, bias: u32, a: u64, b: u64, out: *mut DivOut) {
    let r = DivOut {
        fdiv: fdiv(total, mant, exp_w, bias, a, b),
    };
    unsafe {
        *out = r;
    }
}

#[repr(C)]
pub struct SqrtOut {
    pub fsqrt: u64,
}
#[no_mangle]
pub extern "C" fn fp_sqrt_root(total: u32, mant: u32, exp_w: u32, bias: u32, a: u64, out: *mut SqrtOut) {
    let r = SqrtOut {
        fsqrt: fsqrt(total, mant, exp_w, bias, a),
    };
    unsafe {
        *out = r;
    }
}

// FCVT float<->float: op ∈ {0:widen f32->f64, 1:narrow f64->f32,
//   2:h_to_s, 3:h_to_d, 4:s_to_h, 5:d_to_h}.
#[repr(C)]
pub struct CvtOut {
    pub out: u64,
}
#[no_mangle]
pub extern "C" fn fp_cvt_root(op: u32, x: u64, out: *mut CvtOut) {
    let v = if op == 0 {
        fcvt_widen(x)
    } else if op == 1 {
        fcvt_narrow(x)
    } else if op == 2 {
        fcvt_h_to_s(x)
    } else if op == 3 {
        fcvt_h_to_d(x)
    } else if op == 4 {
        fcvt_s_to_h(x)
    } else {
        fcvt_d_to_h(x)
    };
    let r = CvtOut { out: v };
    unsafe {
        *out = r;
    }
}

// FCVT float->int: mode ∈ {0:fcvtzs,1:fcvtzu,2:fcvtns,3:fcvtnu,4:cvtt(x86),5:cvt(x86)}.
#[repr(C)]
pub struct FtiOut {
    pub out: u64,
}
#[no_mangle]
pub extern "C" fn fp_fti_root(
    total: u32,
    mant: u32,
    exp_w: u32,
    bias: u32,
    int_w: u32,
    mode: u32,
    x: u64,
    out: *mut FtiOut,
) {
    let v = if mode == 0 {
        fcvtzs(total, mant, exp_w, bias, int_w, x)
    } else if mode == 1 {
        fcvtzu(total, mant, exp_w, bias, int_w, x)
    } else if mode == 2 {
        fcvtns(total, mant, exp_w, bias, int_w, x)
    } else if mode == 3 {
        fcvtnu(total, mant, exp_w, bias, int_w, x)
    } else if mode == 4 {
        cvtt_to_si(total, mant, exp_w, bias, int_w, x)
    } else {
        cvt_to_si(total, mant, exp_w, bias, int_w, x)
    };
    let r = FtiOut { out: v };
    unsafe {
        *out = r;
    }
}

// int->float: signed_tag ∈ {0:ucvtf, 1:scvtf}.
#[repr(C)]
pub struct ItfOut {
    pub out: u64,
}
#[no_mangle]
pub extern "C" fn fp_itf_root(
    total: u32,
    mant: u32,
    exp_w: u32,
    bias: u32,
    int_w: u32,
    signed_tag: u32,
    x: u64,
    out: *mut ItfOut,
) {
    let v = if signed_tag == 0 {
        ucvtf(total, mant, exp_w, bias, int_w, x)
    } else {
        scvtf(total, mant, exp_w, bias, int_w, x)
    };
    let r = ItfOut { out: v };
    unsafe {
        *out = r;
    }
}
