// trust-cg-verify/src/fp_bitmodel.rs — INTEGER-ONLY IEEE-754 FP bit-model.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// EVICTING THE HOST FPU FROM THE FP-VERIFICATION TCB.
// ===========================================================================
//
// THE FINDING this module repairs: trust-cg's FP verification path (smt.rs,
// the SmtExpr `try_eval` FP cases) computed every F32/F64 op via NATIVE Rust
// `f64` arithmetic (FPAdd=a+b, FPMul=a*b, FPNeg=-a, FPToSBv=`rounded as i64`,
// BvToFP=`as f64`, FPToFP=`(f as f32) as f64`, the classify predicates via
// `a.is_nan()`/`a.is_normal()`, round_fp_by_mode via `round_ties_even`/…).
// That put the HOST CPU's FPU inside the FP-verification trust base: a host FPU
// that rounded differently from the AArch64 target, or any `as`-cast corner the
// host got wrong, would be INVISIBLE to verification.
//
// THIS MODULE replaces native float arithmetic with a DETERMINISTIC,
// INTEGER-ONLY, BIT-LEVEL IEEE-754 model. Every function here operates on raw
// bit patterns held in `u32` / `u64` / `u128` and uses ONLY integer & bitwise
// operations (`+ - * << >> & | ^ == <` on integers). There is ZERO `f32`/`f64`
// arithmetic anywhere in this file (enforced by a grep gate in the bridge test
// and the soundness manifest). The only things trusted are the host INTEGER ALU
// and THIS algorithm — and the algorithm is itself validated, bit-for-bit,
// against REAL Apple M4 silicon by tests/fp_bitmodel_bridge.rs (the chip
// `:= rfl` theorems of the sibling Clean tree's proofs/aarch64_fp*_chip.lean).
//
// PORTED FROM (read-only reference — the M4-silicon-validated, integer-only,
// ZERO-axiom Clean FP B-defs):
//   * proofs/aarch64_fp.lean       — layout / classify / FABS / FNEG / FCMP→NZCV
//                                     / FMIN / FMAX / FMINNM / FMAXNM / NaN sel.
//   * proofs/aarch64_fp_arith.lean — FADD / FSUB / FMUL, RNE (guard/round/sticky
//                                     align-add-normalize-round-renorm pipeline).
//   * proofs/aarch64_fp_cvt.lean   — FCVT widen/narrow + f↔int (FCVTZS/ZU/NS/NU,
//                                     SCVTF/UCVTF), RNE.
// Clean represents a value as `List Bool` (LSB-first); HERE that bit list is the
// native integer's bit positions (bit i of the list == bit i of the word), so
// each Clean word op maps to one native integer op:
//   bitAt i x        -> (x >> i) & 1
//   wordAdd x y      -> x.wrapping_add(y)   (in a register wide enough; we use
//                                            exact-width or u128 so no overflow)
//   lshrByK k x      -> x >> k
//   shlByK k x       -> x << k
//   hiSet x          -> if x==0 {0} else {bits-1 - x.leading_zeros()}
//   orLowK k x       -> (x & ((1<<k)-1)) != 0
// All exponents/shift amounts are plain integers, exactly as the Clean Nats.
//
// PORTED (#94): FDIV / FSQRT are now here too, INTEGER-ONLY, from the
// on-chip-validated Clean model (proofs/aarch64_fp_divsqrt.lean):
//   * FDIV  — restoring bit-by-bit long division of the implicit-bit-extended
//             significands + remainder-sticky + RNE + specials.
//   * FSQRT — digit-by-digit (non-restoring, two-bits-per-iteration) integer
//             square root + remainder-sticky + RNE + specials.
// Both are width-generic (binary32 + binary64), validated bit-for-bit against the
// 194 aarch64_fp_divsqrt_chip.lean M4 facts by the bridge, and SWAPPED into smt.rs
// (host FPU EVICTED for div/sqrt at binary64 + binary16). The fdiv path adds a
// subnormal-significand normalization the Clean reference omitted (the silicon grid
// had no subnormal divides, so the reference's quotient-precision loss there went
// uncaught); see fdiv_finite. RESIDUAL (Pending B-aarch64-fp-pending): binary32
// ops stay native only because the smt.rs EvalResult::Float(f64) carrier is lossy
// for raw f32 bits — the bit-model ITSELF already supports F32 (FpFmt binary32).
//
// CONVENTIONS (matching the Clean defs and AArch64 FPCR default RNE):
//   * binary32: sign bit 31, exp [30:23] (bias 127), mantissa [22:0].
//   * binary64: sign bit 63, exp [62:52] (bias 1023), mantissa [51:0].
//   * Default NaN: 0x7FC0_0000 (f32) / 0x7FF8_0000_0000_0000 (f64).
//   * selectNaN / quiet follow ARM FPProcessNaNs (sNaN→quiet(op1) first, …).
//   * f→int: NaN→0, out-of-range SATURATES (signed min/max, unsigned 0/max),
//     negative→unsigned saturates to 0.

#![allow(clippy::needless_range_loop)]

// ===========================================================================
// PER-WIDTH FP GEOMETRY (a tiny descriptor so the core is width-generic).
// ===========================================================================

/// Field geometry of an IEEE binary-k format held in a `u64` bit pattern.
#[derive(Clone, Copy)]
pub struct FpFmt {
    /// Total width in bits (32 or 64).
    pub total: u32,
    /// Mantissa field width (23 or 52).
    pub mant: u32,
    /// Exponent field width (8 or 11).
    pub exp_w: u32,
    /// Exponent bias (127 or 1023).
    pub bias: u32,
}

/// binary16 (FP16 / ARMv8.2-FP16): sign bit 15, exp [14:10] (5 bits, bias 15),
/// mantissa [9:0]. expMax (all-ones) = 31; implicit-1 at bit index 10.
pub const F16: FpFmt = FpFmt {
    total: 16,
    mant: 10,
    exp_w: 5,
    bias: 15,
};
pub const F32: FpFmt = FpFmt {
    total: 32,
    mant: 23,
    exp_w: 8,
    bias: 127,
};
pub const F64: FpFmt = FpFmt {
    total: 64,
    mant: 52,
    exp_w: 11,
    bias: 1023,
};

impl FpFmt {
    #[inline]
    fn sign_bit(&self) -> u32 {
        self.total - 1
    }
    /// Max biased exponent value (all-ones) = 2^exp_w - 1.
    #[inline]
    fn exp_max(&self) -> u32 {
        (1u32 << self.exp_w) - 1
    }
    /// Mask of the mantissa field (low `mant` bits).
    #[inline]
    fn mant_mask(&self) -> u64 {
        (1u64 << self.mant) - 1
    }
    /// Mask of the whole `total`-bit pattern.
    #[inline]
    fn word_mask(&self) -> u64 {
        if self.total >= 64 {
            u64::MAX
        } else {
            (1u64 << self.total) - 1
        }
    }
}

// ===========================================================================
// FIELD EXTRACT + CLASSIFY (integer-only; mirrors aarch64_fp.lean classify).
// ===========================================================================

#[inline]
fn sign(f: FpFmt, x: u64) -> bool {
    (x >> f.sign_bit()) & 1 == 1
}
/// Biased exponent field as an integer.
#[inline]
fn exp_field(f: FpFmt, x: u64) -> u32 {
    ((x >> f.mant) & ((1u64 << f.exp_w) - 1)) as u32
}
/// Mantissa field as an integer.
#[inline]
fn mant_field(f: FpFmt, x: u64) -> u64 {
    x & f.mant_mask()
}
#[inline]
fn exp_all_ones(f: FpFmt, x: u64) -> bool {
    exp_field(f, x) == f.exp_max()
}
#[inline]
fn exp_all_zero(f: FpFmt, x: u64) -> bool {
    exp_field(f, x) == 0
}
#[inline]
fn mant_zero(f: FpFmt, x: u64) -> bool {
    mant_field(f, x) == 0
}

pub fn is_nan(f: FpFmt, x: u64) -> bool {
    exp_all_ones(f, x) && !mant_zero(f, x)
}
pub fn is_inf(f: FpFmt, x: u64) -> bool {
    exp_all_ones(f, x) && mant_zero(f, x)
}
pub fn is_zero(f: FpFmt, x: u64) -> bool {
    exp_all_zero(f, x) && mant_zero(f, x)
}
pub fn is_subnormal(f: FpFmt, x: u64) -> bool {
    exp_all_zero(f, x) && !mant_zero(f, x)
}
pub fn is_normal(f: FpFmt, x: u64) -> bool {
    !exp_all_ones(f, x) && !exp_all_zero(f, x)
}
/// Mantissa MSB (bit mant-1): set ⇒ quiet NaN.
#[inline]
fn mant_msb(f: FpFmt, x: u64) -> bool {
    (x >> (f.mant - 1)) & 1 == 1
}
pub fn is_qnan(f: FpFmt, x: u64) -> bool {
    is_nan(f, x) && mant_msb(f, x)
}
pub fn is_snan(f: FpFmt, x: u64) -> bool {
    is_nan(f, x) && !mant_msb(f, x)
}

// ===========================================================================
// FABS / FNEG — pure sign-bit ops.
// ===========================================================================

pub fn fabs(f: FpFmt, x: u64) -> u64 {
    x & !(1u64 << f.sign_bit()) & f.word_mask()
}
pub fn fneg(f: FpFmt, x: u64) -> u64 {
    (x ^ (1u64 << f.sign_bit())) & f.word_mask()
}

// ===========================================================================
// ORDERED COMPARE on bit patterns (NaN guarded by the caller).
//   magnitude = low (total-1) bits (exp:mantissa); sign-magnitude ordering.
// ===========================================================================

#[inline]
fn magnitude(f: FpFmt, x: u64) -> u64 {
    x & !(1u64 << f.sign_bit()) & f.word_mask()
}

/// Strict ordered less-than (assumes neither is NaN). Mirrors fpLt32/64.
fn fp_lt(f: FpFmt, a: u64, b: u64) -> bool {
    let sa = sign(f, a);
    let sb = sign(f, b);
    let ma = magnitude(f, a);
    let mb = magnitude(f, b);
    if sa {
        if sb {
            // both negative: a<b iff |a|>|b|
            mb < ma
        } else {
            // a neg, b pos: a<b unless both zero
            !(ma == 0 && mb == 0)
        }
    } else if sb {
        // a pos, b neg: false
        false
    } else {
        // both positive: a<b iff |a|<|b|
        ma < mb
    }
}

/// Equality as reals (no NaN): bit-equal OR both zero (+0 == -0).
fn fp_eq(f: FpFmt, a: u64, b: u64) -> bool {
    let am = a & f.word_mask();
    let bm = b & f.word_mask();
    am == bm || (is_zero(f, a) && is_zero(f, b))
}

// ===========================================================================
// FCMP → NZCV  (ARM DDI 0487 FCMP; flags as probed on M4 via MRS NZCV).
//   ordered EQ -> NZCV 0110 ; ordered LT -> 1000 ; ordered GT -> 0010 ;
//   UNORDERED  -> 0011.  Returned per-flag (mirrors fcmpN/Z/C/V).
// ===========================================================================

#[inline]
fn fcmp_unord(f: FpFmt, a: u64, b: u64) -> bool {
    is_nan(f, a) || is_nan(f, b)
}
/// N: set only on ordered LT.
pub fn fcmp_n(f: FpFmt, a: u64, b: u64) -> bool {
    !fcmp_unord(f, a, b) && fp_lt(f, a, b)
}
/// Z: set only on ordered EQ.
pub fn fcmp_z(f: FpFmt, a: u64, b: u64) -> bool {
    !fcmp_unord(f, a, b) && fp_eq(f, a, b)
}
/// C: set unless ordered LT (i.e. GT, EQ, or unordered).
pub fn fcmp_c(f: FpFmt, a: u64, b: u64) -> bool {
    !fcmp_n(f, a, b)
}
/// V: set only when unordered.
pub fn fcmp_v(f: FpFmt, a: u64, b: u64) -> bool {
    fcmp_unord(f, a, b)
}

// ===========================================================================
// NaN PROCESSING (ARM FPProcessNaNs) + numeric MIN/MAX + the {F}MIN/MAX family.
// ===========================================================================

#[inline]
fn quiet(f: FpFmt, x: u64) -> u64 {
    (x | (1u64 << (f.mant - 1))) & f.word_mask()
}
/// selectNaN: sNaN(a)→quiet a ; sNaN(b)→quiet b ; qNaN(a)→a ; else b.
fn select_nan(f: FpFmt, a: u64, b: u64) -> u64 {
    if is_snan(f, a) {
        quiet(f, a)
    } else if is_snan(f, b) {
        quiet(f, b)
    } else if is_qnan(f, a) {
        a & f.word_mask()
    } else {
        b & f.word_mask()
    }
}

fn num_min(f: FpFmt, a: u64, b: u64) -> u64 {
    if is_zero(f, a) && is_zero(f, b) {
        // signed-zero rule: min returns the -0 one.
        if sign(f, a) {
            a & f.word_mask()
        } else {
            b & f.word_mask()
        }
    } else if fp_lt(f, a, b) {
        a & f.word_mask()
    } else {
        b & f.word_mask()
    }
}
fn num_max(f: FpFmt, a: u64, b: u64) -> u64 {
    if is_zero(f, a) && is_zero(f, b) {
        // signed-zero rule: max returns the +0 one.
        if sign(f, a) {
            b & f.word_mask()
        } else {
            a & f.word_mask()
        }
    } else if fp_lt(f, b, a) {
        a & f.word_mask()
    } else {
        b & f.word_mask()
    }
}

/// FMIN — NaN-propagating (NaN whenever either input is NaN).
pub fn fmin(f: FpFmt, a: u64, b: u64) -> u64 {
    if is_nan(f, a) || is_nan(f, b) {
        select_nan(f, a, b)
    } else {
        num_min(f, a, b)
    }
}
/// FMAX — NaN-propagating.
pub fn fmax(f: FpFmt, a: u64, b: u64) -> u64 {
    if is_nan(f, a) || is_nan(f, b) {
        select_nan(f, a, b)
    } else {
        num_max(f, a, b)
    }
}
#[inline]
fn nm_force_nan(f: FpFmt, a: u64, b: u64) -> bool {
    is_snan(f, a) || is_snan(f, b) || (is_nan(f, a) && is_nan(f, b))
}
/// FMINNM — IEEE minNum: a lone qNaN yields the NUMBER.
pub fn fminnm(f: FpFmt, a: u64, b: u64) -> u64 {
    if nm_force_nan(f, a, b) {
        select_nan(f, a, b)
    } else if is_nan(f, a) {
        b & f.word_mask()
    } else if is_nan(f, b) {
        a & f.word_mask()
    } else {
        num_min(f, a, b)
    }
}
/// FMAXNM — IEEE maxNum.
pub fn fmaxnm(f: FpFmt, a: u64, b: u64) -> u64 {
    if nm_force_nan(f, a, b) {
        select_nan(f, a, b)
    } else if is_nan(f, a) {
        b & f.word_mask()
    } else if is_nan(f, b) {
        a & f.word_mask()
    } else {
        num_max(f, a, b)
    }
}

// ===========================================================================
// RNE ROUNDING + result-shape constructors (shared by FADD/FMUL/FCVT).
// ===========================================================================

/// guard room below the kept LSB: 3 extra low bits (guard, round, sticky slot).
const GUARD_ROOM: u32 = 3;

/// round up iff guard && (round || sticky || lsb).  (Clean roundUp.)
#[inline]
fn round_up(lsb: bool, guard: bool, round_or_sticky: bool) -> bool {
    guard && (round_or_sticky || lsb)
}

/// Pack [mantissa | biased-exp | sign] into a `total`-bit pattern. `mant_bits`
/// supplies the mantissa field (its low `mant` bits are used).
fn pack(f: FpFmt, exp_n: u32, sgn: bool, mant_bits: u64) -> u64 {
    let m = mant_bits & f.mant_mask();
    let e = (exp_n as u64 & ((1u64 << f.exp_w) - 1)) << f.mant;
    let s = (sgn as u64) << f.sign_bit();
    (m | e | s) & f.word_mask()
}

fn default_qnan(f: FpFmt) -> u64 {
    // exp all-ones, sign 0, mantissa = only MSB (bit mant-1) set.
    pack(f, f.exp_max(), false, 1u64 << (f.mant - 1))
}
fn inf_of(f: FpFmt, sgn: bool) -> u64 {
    pack(f, f.exp_max(), sgn, 0)
}
fn zero_of(f: FpFmt, sgn: bool) -> u64 {
    pack(f, 0, sgn, 0)
}

/// Index of the highest set bit (0 if x==0). Mirrors Clean hiSet.
#[inline]
fn hi_set_u128(x: u128) -> u32 {
    if x == 0 { 0 } else { 127 - x.leading_zeros() }
}

/// Right-shift `x` by `shr`, folding ALL shifted-out bits into bit 0 (sticky).
#[inline]
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
// FADD / FSUB / FMUL — RNE.  Work register: u128 (room for f64 53-bit
// significand + guard, and the f64 product 106 bits, exactly as Clean's
// workW=64/prodW=128).
// ===========================================================================

/// Build a significand in a u128 work register: mantissa field in [0..mant),
/// implicit bit at index `mant` (1 for normals, 0 for subnormals/zero).
#[inline]
fn sig_build(f: FpFmt, implicit: bool, x: u64) -> u128 {
    let m = mant_field(f, x) as u128;
    if implicit { m | (1u128 << f.mant) } else { m }
}

/// THE RNE round of a guard-roomed significand: bits [2]=guard,[1]=round,
/// [0]=sticky, bit GUARD_ROOM = kept LSB. Returns the mantissa-placed (>>3)
/// significand, +1 if it rounds up. Mirrors faRoundWord / fmRoundWord.
fn round_word(s: u128) -> u128 {
    let lsb = (s >> GUARD_ROOM) & 1 == 1;
    let guard = (s >> (GUARD_ROOM - 1)) & 1 == 1;
    let round_b = (s >> (GUARD_ROOM - 2)) & 1 == 1;
    let sticky_b = s & 1 == 1;
    let r_up = round_up(lsb, guard, round_b || sticky_b);
    let mant_place = s >> GUARD_ROOM;
    if r_up { mant_place + 1 } else { mant_place }
}

/// Add or subtract (sign-magnitude) two finite operands, RNE. `a_or_sub`
/// selects FADD (false) / the subtract that FSUB feeds (b's sign flipped).
fn fadd_finite(f: FpFmt, sa: bool, sb: bool, a: u64, b: u64) -> u64 {
    let same_sign = sa == sb;
    let eza = exp_all_zero(f, a);
    let ezb = exp_all_zero(f, b);
    // effective exponent (subnormals act at 1).
    let ea = if eza { 1 } else { exp_field(f, a) };
    let eb = if ezb { 1 } else { exp_field(f, b) };
    // significand shifted up by GUARD_ROOM (mirrors faSig).
    let sig_a = sig_build(f, !eza, a) << GUARD_ROOM;
    let sig_b = sig_build(f, !ezb, b) << GUARD_ROOM;
    // order so (eBig, sBig) >= (eSmall, sSmall) (faGE).
    let a_ge = if ea == eb { sig_a >= sig_b } else { ea > eb };
    let (e_big, e_small, s_big, s_small, sign_big) = if a_ge {
        (ea, eb, sig_a, sig_b, sa)
    } else {
        (eb, ea, sig_b, sig_a, sb)
    };
    // exact cancellation (x + (-x)) -> +0.
    let equal_mag = ea == eb && sig_a == sig_b;
    if !same_sign && equal_mag {
        return zero_of(f, false);
    }
    fadd_core(f, sign_big, same_sign, e_big, e_small, s_big, s_small)
}

/// The staged FADD core (align-add-normalize-round-renorm). Mirrors fAddCore.
fn fadd_core(
    f: FpFmt,
    sign_r: bool,
    same_sign: bool,
    e_big: u32,
    e_small: u32,
    s_big: u128,
    s_small: u128,
) -> u64 {
    let work_w: u32 = f.total; // 32 or 64 — but we hold in u128; only used for masking semantics.
    let _ = work_w;
    let imp_idx = f.mant + GUARD_ROOM;
    // STAGE A: align smaller significand, add/sub, fold alignment sticky -> bit0.
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
    // For ADD, the dropped alignment bits are an ADDED fraction in (0,1): the
    // integer sum is unaffected and the residual is captured by OR-ing sticky into
    // bit 0. For SUBTRACT, the dropped bits are a SUBTRACTED fraction `frac` in
    // (0,1), so the exact result is `s_big - s_small_a - frac`. OR-ing sticky after
    // the integer subtraction would ADD instead of subtract — a 1-ULP error in the
    // cancellation path (it produced a result 1 ULP too high; caught by an 81M-input
    // differential fuzz vs the host FPU at BOTH binary32 and binary64, and confirmed
    // 1 ULP off the correctly-rounded RNE value by exact-rational arithmetic). The
    // BORROW-correct form rewrites `s_big - s_small_a - frac` as
    // `(s_big - s_small_a - 1) + (1 - frac)`: since `0 < frac < 1`, the term
    // `(1 - frac)` is a nonzero fraction in (0,1), so the integer part is
    // `s_big - s_small_a - 1` and the residual sticky is 1. (When no bits were
    // dropped, `frac == 0` and the plain integer subtraction is already exact.)
    let s_comb = if same_sign {
        (s_big + s_small_a) | (sticky_a as u128)
    } else if sticky_a {
        (s_big - s_small_a - 1) | 1
    } else {
        // s_big >= s_small_a by construction (big ordering); exact subtract.
        s_big - s_small_a
    };
    // STAGE B: carry-out (bit imp_idx+1 set) -> right shift 1 (sticky), exp+1.
    let carry = (s_comb >> (imp_idx + 1)) & 1 == 1;
    let s_after_carry = if carry {
        shr_sticky_u128(s_comb, 1)
    } else {
        s_comb
    };
    let e_after_carry = if carry { e_big + 1 } else { e_big };
    // STAGE C: cancellation left-normalise (bring top set bit up to imp_idx).
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
    // STAGE D: round ties-to-even.
    let s_rounded = round_word(s_norm);
    // STAGE E: post-round renormalise + subnormal/overflow + pack.
    fa_finish(f, sign_r, e_norm, s_rounded)
}

/// Post-round renormalise + subnormal/overflow handling + pack. Mirrors faFinish.
fn fa_finish(f: FpFmt, sign_r: bool, e_norm: u32, s_rounded: u128) -> u64 {
    let post_carry = (s_rounded >> (f.mant + 1)) & 1 == 1;
    let s_final = if post_carry {
        s_rounded >> 1
    } else {
        s_rounded
    };
    let e_final = if post_carry { e_norm + 1 } else { e_norm };
    // subnormal: implicit bit (index mant) clear AND exp == 1 -> exp 0.
    let implicit_clear = (s_final >> f.mant) & 1 == 0;
    let subnormal = implicit_clear && e_final == 1;
    let e_after_sub = if subnormal { 0 } else { e_final };
    let overflow = e_after_sub >= f.exp_max();
    let out_exp = if overflow { f.exp_max() } else { e_after_sub };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(f, out_exp, sign_r, out_mant)
}

/// FADD with full special-case dispatch. Mirrors fadd32/fadd64.
pub fn fadd(f: FpFmt, a: u64, b: u64) -> u64 {
    let a = a & f.word_mask();
    let b = b & f.word_mask();
    let sa = sign(f, a);
    let sb = sign(f, b);
    if is_nan(f, a) || is_nan(f, b) {
        return select_nan(f, a, b);
    }
    if is_inf(f, a) {
        if is_inf(f, b) {
            return if sa == sb {
                inf_of(f, sa)
            } else {
                default_qnan(f)
            };
        }
        return inf_of(f, sa);
    }
    if is_inf(f, b) {
        return inf_of(f, sb);
    }
    if is_zero(f, a) {
        if is_zero(f, b) {
            // (-0)+(-0) = -0 ; otherwise +0.
            return if sa && sb {
                zero_of(f, true)
            } else {
                zero_of(f, false)
            };
        }
        return b;
    }
    if is_zero(f, b) {
        return a;
    }
    fadd_finite(f, sa, sb, a, b)
}

/// FSUB a - b = FADD a (-b) (sign of b flipped), with the SAME special handling
/// AArch64 FSUB applies. The simplest faithful model: negate b's sign bit and
/// reuse FADD (the IEEE definition of subtraction; matches the chip differential
/// for the no-NaN cases, and selectNaN over the ORIGINAL operands for NaN — which
/// FADD over the negated b preserves since negation does not change NaN-ness or
/// the payload selection between a and b).
pub fn fsub(f: FpFmt, a: u64, b: u64) -> u64 {
    let a = a & f.word_mask();
    let b = b & f.word_mask();
    // Trust: owner #8 fix — AArch64 FSUB processes NaN propagation over the ORIGINAL
    // operands: a NaN in `b` is propagated (quieted) with its ORIGINAL sign; FSUB does
    // NOT negate `b` before NaN handling. Modeling fsub as `fadd(a, fneg(b))` fed the
    // sign-flipped `fneg(b)` into select_nan, so a propagated b-NaN came back with the
    // WRONG sign (e.g. fsub(+0, +qNaN) gave -qNaN; host keeps +qNaN). Dispatch the NaN
    // case here over (a, b) — matching fadd/fmul — and use the negated b only for the
    // finite/inf/zero arithmetic (where fneg is exact and select_nan never fires).
    // See tests/e2e_trust_fns_round13.rs trust_fp_fsub_nan_sign_bug_pinned (was a
    // fail-loud pin; now a clean bill: model == host FPU).
    if is_nan(f, a) || is_nan(f, b) {
        return select_nan(f, a, b);
    }
    fadd(f, a, fneg(f, b))
}

/// FMUL with full special-case dispatch. Mirrors fmul32/fmul64.
pub fn fmul(f: FpFmt, a: u64, b: u64) -> u64 {
    let a = a & f.word_mask();
    let b = b & f.word_mask();
    let sa = sign(f, a);
    let sb = sign(f, b);
    let sgn = sa ^ sb;
    if is_nan(f, a) || is_nan(f, b) {
        return select_nan(f, a, b);
    }
    if is_inf(f, a) {
        return if is_zero(f, b) {
            default_qnan(f)
        } else {
            inf_of(f, sgn)
        };
    }
    if is_inf(f, b) {
        return if is_zero(f, a) {
            default_qnan(f)
        } else {
            inf_of(f, sgn)
        };
    }
    if is_zero(f, a) || is_zero(f, b) {
        return zero_of(f, sgn);
    }
    fmul_finite(f, sgn, a, b)
}

fn fmul_finite(f: FpFmt, sgn: bool, a: u64, b: u64) -> u64 {
    let eza = exp_all_zero(f, a);
    let ezb = exp_all_zero(f, b);
    // significands with implicit bit at index mant (0 for subnormals).
    let sa_w = sig_build(f, !eza, a);
    let sb_w = sig_build(f, !ezb, b);
    let ea = if eza { 1u32 } else { exp_field(f, a) };
    let eb = if ezb { 1u32 } else { exp_field(f, b) };
    fmul_core(f, sgn, ea, eb, sa_w, sb_w)
}

/// The staged FMUL core (exact product, derive exponent from field weights,
/// gradual underflow, round, renorm). Mirrors fMulCore.
fn fmul_core(f: FpFmt, sgn: bool, ea: u32, eb: u32, sa_w: u128, sb_w: u128) -> u64 {
    let prod = sa_w * sb_w; // exact: ≤ (53 bits)^2 = 106 bits ≪ 128.
    let top = hi_set_u128(prod);
    let target = f.mant + GUARD_ROOM;
    // S = top + ea + eb ; D = bias + 2*mant.
    let big_s = top + ea + eb;
    let big_d = f.bias + 2 * f.mant;
    let underflow = big_s <= big_d;
    // extra downshift for gradual underflow = 1 + D - S (only when underflow).
    let extra = if underflow { 1 + (big_d - big_s) } else { 0 };
    let shift_src = top + extra;
    // The f16-relevant LEFT-shift branch (mirrors the Clean fMulCore `needLeft`):
    // when the product's top set bit (after the gradual-underflow `extra` downshift)
    // lands BELOW the rounding target, the product must be shifted UP by
    // (target - shift_src) — a LEFT shift, lossless (no sticky) — to seat the
    // implicit/top bit at `target`. This arises for binary16 when a SUBNORMAL
    // operand (significand << 2^mant) multiplies a power-of-two-ish operand so the
    // integer product is small (e.g. minsub * 2^10 = min normal). For f32/f64 the
    // product top bit is always >= target, so `need_left` is false and the
    // right-only path below is taken (this branch is backward-compatible).
    let need_left = shift_src < target;
    let shr = shift_src.saturating_sub(target); // right amount (0 when need_left)
    let shl = target.saturating_sub(shift_src); // left amount  (0 when !need_left)
    let out_e = if underflow { 0 } else { big_s - big_d };
    let p_placed = if need_left {
        prod << shl
    } else {
        shr_sticky_u128(prod, shr)
    };
    let s_rounded = round_word(p_placed);
    fm_finish(f, sgn, out_e, s_rounded)
}

/// FMUL post-round renormalise + subnormal→normal promotion + overflow + pack.
fn fm_finish(f: FpFmt, sign_r: bool, out_e: u32, s_rounded: u128) -> u64 {
    let post_carry = (s_rounded >> (f.mant + 1)) & 1 == 1;
    let s_final = if post_carry {
        s_rounded >> 1
    } else {
        s_rounded
    };
    let e_fin0 = if post_carry { out_e + 1 } else { out_e };
    // a subnormal that rounded up to set the implicit bit -> min normal (exp 1).
    let implicit_set = (s_final >> f.mant) & 1 == 1;
    let promote = out_e == 0 && implicit_set;
    let e_fin = if promote { 1 } else { e_fin0 };
    let overflow = e_fin >= f.exp_max();
    let out_exp = if overflow { f.exp_max() } else { e_fin };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(f, out_exp, sign_r, out_mant)
}

// ===========================================================================
// FMA — scalar fused multiply-add: round_RNE(a*b + c) with a SINGLE rounding.
//
// This is the whole point of a fused multiply-add: the exact (unrounded)
// product `a*b` is added to `c` and the sum is rounded ONCE — NOT
// `round(round(a*b) + c)` (two roundings), which differs in the last ULP on a
// dense set of inputs. Integer-only, host-FPU-free, width-generic (binary16/
// 32/64), matching AArch64 FMADD (Rd = Ra + Rn*Rm; here a=Rn, b=Rm, c=Ra).
//
// NaN / special handling matches the AArch64 FMADD *instruction* (probed on
// Apple silicon, NOT libm `fma`): FPProcessNaNs3 selects the FIRST NaN in the
// positional order (addend c, then a, then b), signaling NaNs before quiet
// NaNs, quieting a selected sNaN; a `0*Inf` (or `Inf-Inf`) invalid product
// yields the default qNaN, and a `0*Inf` product with a *quiet*-NaN addend
// also yields the default qNaN (ARM: `typeA==QNaN && zero*inf`).
//
// The finite core computes the EXACT product significand (an integer, up to
// 2*(mant+1) bits), aligns the addend into a bounded window (anything below the
// window folds to a sticky bit), combines sign-magnitude, then rounds once via
// the shared `round_word` (RNE) + `fm_finish` (renormalise/subnormal-promote/
// overflow) used by FMUL — so the single-rounding claim rests on the same
// validated rounding kernel. Validated bit-for-bit against the hardware FMADD
// by the fma bridge test and scripts/fuzz/fmafuzz.py (clang-fused differential).
// ===========================================================================

/// Unpack a FINITE operand into (significand, lsb-exponent): value ==
/// `sig * 2^e_lsb`, with the implicit bit at index `mant` (subnormals act at
/// effective exponent 1, implicit bit clear).
#[inline]
fn fma_unpack(f: FpFmt, x: u64) -> (u128, i64) {
    let ez = exp_all_zero(f, x);
    let sig = sig_build(f, !ez, x);
    let e_eff = if ez { 1i64 } else { exp_field(f, x) as i64 };
    let e_lsb = e_eff - f.bias as i64 - f.mant as i64;
    (sig, e_lsb)
}

/// FMADD NaN selection (see module note): positional order c, a, b; sNaN first
/// (quieted) then qNaN; the `prod_invalid` (0*Inf) + qNaN-addend corner yields
/// the default qNaN. Caller guarantees at least one of a/b/c is a NaN.
fn fma_select_nan(f: FpFmt, a: u64, b: u64, c: u64, prod_invalid: bool) -> u64 {
    if is_snan(f, c) {
        return quiet(f, c);
    }
    if is_snan(f, a) {
        return quiet(f, a);
    }
    if is_snan(f, b) {
        return quiet(f, b);
    }
    // 0*Inf invalid with a QUIET-NaN addend -> default NaN (ARM FPMulAdd).
    if prod_invalid && is_qnan(f, c) {
        return default_qnan(f);
    }
    if is_qnan(f, c) {
        return c & f.word_mask();
    }
    if is_qnan(f, a) {
        return a & f.word_mask();
    }
    // must be qNaN in b
    b & f.word_mask()
}

/// Place a significand (value `sig * 2^e_lsb`) into the accumulator scale `2^e0`,
/// returning (placed integer, sticky) where sticky records nonzero bits dropped
/// below the accumulator LSB. Left shifts are exact; right shifts fold dropped
/// bits into the sticky flag.
#[inline]
fn fma_place(sig: u128, e_lsb: i64, e0: i64) -> (u128, bool) {
    if sig == 0 {
        return (0, false);
    }
    let shift = e_lsb - e0;
    if shift >= 0 {
        (sig << (shift as u32), false)
    } else {
        let s = (-shift) as u32;
        if s >= 128 {
            (0, true)
        } else {
            let dropped = sig & ((1u128 << s) - 1);
            (sig >> s, dropped != 0)
        }
    }
}

/// The staged FMA finite core: exact product + aligned addend, single RNE round.
/// `sp`/`sc` are the product and addend signs; all inputs finite (product
/// nonzero, addend nonzero — the zero cases are handled by `fma`).
fn fma_finite(f: FpFmt, sp: bool, sc: bool, a: u64, b: u64, c: u64) -> u64 {
    let (pa, ea_lsb) = fma_unpack(f, a);
    let (pb, eb_lsb) = fma_unpack(f, b);
    let pm = pa * pb; // exact product significand (<= 2*(mant+1) bits).
    let ep_lsb = ea_lsb + eb_lsb;
    let (cm, ec_lsb) = fma_unpack(f, c);

    let p_hi = hi_set_u128(pm) as i64;
    let ptop = ep_lsb + p_hi;
    let c_hi = hi_set_u128(cm) as i64;
    let ctop = ec_lsb + c_hi;
    let anchor = ptop.max(ctop);

    // Window wide enough to hold the full product below the anchor (cancellation
    // keeps the operands within one exponent, so no meaningful bit is lost), plus
    // carry/guard headroom; comfortably inside u128 for binary16/32/64.
    let window: i64 = 2 * f.mant as i64 + 6;
    let e0 = anchor - (window - 1);

    let (p_pl, p_stky) = fma_place(pm, ep_lsb, e0);
    let (c_pl, c_stky) = fma_place(cm, ec_lsb, e0);

    // Order by top exponent (the higher-top operand is placed exactly, never
    // sticky); ties (equal tops) are both exact — order by placed integer.
    let (hi, hi_sign, lo, lo_stky) = if ptop > ctop {
        (p_pl, sp, c_pl, c_stky)
    } else if ctop > ptop {
        (c_pl, sc, p_pl, p_stky)
    } else if p_pl >= c_pl {
        (p_pl, sp, c_pl, false)
    } else {
        (c_pl, sc, p_pl, false)
    };

    let same_sign = sp == sc;
    let comb = if same_sign {
        let s = hi + lo;
        if lo_stky { s | 1 } else { s }
    } else if lo_stky {
        // borrow-correct subtract with dropped fraction (mirrors fadd_core):
        // hi > lo strictly whenever sticky is present, so no underflow.
        (hi - lo - 1) | 1
    } else {
        hi - lo
    };
    if comb == 0 {
        // exact cancellation -> +0 under RNE.
        return zero_of(f, false);
    }

    fma_round(f, hi_sign, comb, e0)
}

/// Round `comb * 2^e0` (comb != 0) to the format, RNE, via the shared FMUL
/// rounding kernel (`round_word` + `fm_finish`): seat the significand at
/// `mant + GUARD_ROOM` with sticky, apply gradual-underflow downshift when the
/// biased exponent is <= 0, round once, renormalise/promote/overflow.
fn fma_round(f: FpFmt, sign_r: bool, comb: u128, e0: i64) -> u64 {
    let top = hi_set_u128(comb) as i64;
    let e_biased = e0 + top + f.bias as i64;
    let underflow = e_biased <= 0;
    let extra = if underflow { 1 - e_biased } else { 0 };
    let target = (f.mant + GUARD_ROOM) as i64;
    let shr = top - target + extra;
    let placed = if shr >= 0 {
        shr_sticky_u128(comb, shr as u32)
    } else {
        comb << ((-shr) as u32)
    };
    let out_e = if underflow { 0 } else { e_biased as u32 };
    let s_rounded = round_word(placed);
    fm_finish(f, sign_r, out_e, s_rounded)
}

/// FMA with full special-case dispatch: `round_RNE(a*b + c)`, single rounding.
pub fn fma(f: FpFmt, a: u64, b: u64, c: u64) -> u64 {
    let a = a & f.word_mask();
    let b = b & f.word_mask();
    let c = c & f.word_mask();
    let sa = sign(f, a);
    let sb = sign(f, b);
    let sc = sign(f, c);
    let sp = sa ^ sb;

    let prod_invalid = (is_inf(f, a) && is_zero(f, b)) || (is_zero(f, a) && is_inf(f, b));

    if is_nan(f, a) || is_nan(f, b) || is_nan(f, c) {
        return fma_select_nan(f, a, b, c, prod_invalid);
    }
    if prod_invalid {
        return default_qnan(f);
    }
    // Product is +-Inf (one operand Inf, the other nonzero/finite).
    if is_inf(f, a) || is_inf(f, b) {
        if is_inf(f, c) && sc != sp {
            return default_qnan(f); // Inf + (-Inf)
        }
        return inf_of(f, sp);
    }
    // Product finite; addend infinite.
    if is_inf(f, c) {
        return inf_of(f, sc);
    }
    // Product is +-0.
    if is_zero(f, a) || is_zero(f, b) {
        if is_zero(f, c) {
            // (+-0) + (+-0): -0 only when BOTH are -0, else +0 (RNE).
            return zero_of(f, sp && sc);
        }
        return c; // 0 + c = c
    }
    // Addend is +-0 and product nonzero: result == round(product) == FMUL (the
    // +-0 cannot change a nonzero product's value, and the product is nonzero so
    // no exact-zero sign question arises).
    if is_zero(f, c) {
        return fmul(f, a, b);
    }
    fma_finite(f, sp, sc, a, b, c)
}

// ===========================================================================
// FCVT  f32 <-> f64  (widen exact / narrow RNE).  Mirrors aarch64_fp_cvt.lean.
// ===========================================================================

/// FCVT f32 -> f64 (widening, EXACT). Input low 32 bits; output 64 bits.
pub fn fcvt_widen(x: u64) -> u64 {
    let x = x & F32.word_mask();
    let s = sign(F32, x);
    if is_nan(F32, x) {
        // widen NaN: mant64 = mant32 << 29 ; quiet (set bit 51) if sNaN.
        let m32 = mant_field(F32, x);
        let mut m64 = m32 << 29;
        if is_snan(F32, x) {
            m64 |= 1u64 << 51;
        }
        return pack(F64, 2047, s, m64);
    }
    if is_inf(F32, x) {
        return inf_of(F64, s);
    }
    if is_zero(F32, x) {
        return zero_of(F64, s);
    }
    if exp_all_zero(F32, x) {
        // subnormal f32 -> normal f64.
        let m32 = mant_field(F32, x);
        let hi = hi_set_u128(m32 as u128); // top set bit (0..22)
        let e64 = hi + 874;
        let m64 = ((m32 << (52 - hi)) as u128 & ((1u128 << 52) - 1)) as u64;
        pack(F64, e64, s, m64)
    } else {
        // normal f32 -> f64: e64 = e32 + 896 ; mant64 = mant32 << 29.
        let e32 = exp_field(F32, x);
        let m32 = mant_field(F32, x);
        pack(F64, e32 + 896, s, m32 << 29)
    }
}

/// FCVT f64 -> f32 (narrowing, RNE). Input 64 bits; output low 32 bits.
pub fn fcvt_narrow(x: u64) -> u64 {
    let s = sign(F64, x);
    if is_nan(F64, x) {
        // narrow NaN: mant32 = (mant64 >> 29) | quiet-bit(22).
        let m64 = mant_field(F64, x);
        let m32 = (m64 >> 29) | (1u64 << 22);
        return pack(F32, 255, s, m32);
    }
    if is_inf(F64, x) {
        return inf_of(F32, s);
    }
    if is_zero(F64, x) {
        return zero_of(F32, s);
    }
    // FINITE: build 53-bit significand, downshift to f32 position, RNE round.
    let e64 = exp_field(F64, x);
    let sig = sig_build(F64, !exp_all_zero(F64, x), x); // top bit at index 52
    // implicit-bit-position biased f32 exponent (true): ef0 = e64 - 896.
    let normal_target = e64 > 896;
    let extra = if normal_target { 0 } else { 897 - e64 };
    let shr = 26 + extra;
    let e_cand = if normal_target { e64 - 896 } else { 1 };
    let s_shift = shr_sticky_u128(sig, shr);
    let s_rounded = round_word(s_shift);
    nar_finish(s, e_cand, s_rounded)
}

/// f64->f32 finish (FADD-shape, fixed at f32 geometry). Mirrors narFinish.
fn nar_finish(sign_r: bool, e_cand: u32, s_rounded: u128) -> u64 {
    let post_carry = (s_rounded >> 24) & 1 == 1; // bit (mant32+1)=24
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
    pack(F32, out_exp, sign_r, out_mant)
}

// ===========================================================================
// FCVT  f16 <-> f32 / f64  (widen EXACT / narrow RNE).
//   PORTED FROM (read-only, M4-silicon-validated, integer-only, zero-axiom):
//     proofs/aarch64_fp16.lean   — fcvt_widen / fcvt_h_to_s / fcvt_h_to_d /
//                                   narrowFiniteCore / fcvt_s_to_h / fcvt_d_to_h.
//   binary16: total 16, mant 10, exp_w 5, bias 15, sign bit 15, mant MSB bit 9,
//   exp_max (all-ones) 31, implicit-1 at bit index 10.
//   THIS REPLACES trust-cg's bespoke fp16_bits_to_f64 / f64_to_fp16_bits /
//   round_to_fp16_value (smt.rs), which were NOT silicon-validated. The bridge
//   (tests/fp_bitmodel_bridge.rs) asserts these == the 200+ aarch64_fp16_chip.lean
//   `:= rfl` facts recorded on a real Apple M4 (ARMv8.2-FP16 in hardware).
// ===========================================================================

/// FCVT f16 -> dst (F32 or F64), WIDENING, EXACT. Input low 16 bits; output the
/// dst format's bit pattern. Mirrors aarch64_fp16.lean fcvt_widen.
fn fp16_widen(dst: FpFmt, x: u64) -> u64 {
    let x = x & F16.word_mask();
    let s = sign(F16, x);
    if is_nan(F16, x) {
        // widen NaN: dst mant = (m16 << (mantDst-10)); quiet if sNaN (set dst MSB).
        let m16 = mant_field(F16, x);
        let mut m_dst = m16 << (dst.mant - 10);
        if is_snan(F16, x) {
            m_dst |= 1u64 << (dst.mant - 1);
        }
        return pack(dst, dst.exp_max(), s, m_dst);
    }
    if is_inf(F16, x) {
        return inf_of(dst, s);
    }
    if is_zero(F16, x) {
        return zero_of(dst, s);
    }
    if exp_all_zero(F16, x) {
        // subnormal f16 -> NORMAL dst. hi = top set bit of m16 (0..9).
        //   biased dst exp = hi + bias - 24 ; mant = (m16 << (mantDst-hi)) & mask.
        let m16 = mant_field(F16, x);
        let hi = hi_set_u128(m16 as u128);
        let e_dst = hi + dst.bias - 24;
        let m_dst = ((m16 << (dst.mant - hi)) as u128 & ((1u128 << dst.mant) - 1)) as u64;
        pack(dst, e_dst, s, m_dst)
    } else {
        // normal f16 -> dst: e_dst = e16 + bias - 15 ; mant = m16 << (mantDst-10).
        let e16 = exp_field(F16, x);
        let m16 = mant_field(F16, x);
        pack(dst, e16 + dst.bias - 15, s, m16 << (dst.mant - 10))
    }
}

/// FCVT f16 -> f32 (widen EXACT). Mirrors fcvt_h_to_s.
pub fn fcvt_h_to_s(x: u64) -> u64 {
    fp16_widen(F32, x)
}
/// FCVT f16 -> f64 (widen EXACT). Mirrors fcvt_h_to_d.
pub fn fcvt_h_to_d(x: u64) -> u64 {
    fp16_widen(F64, x)
}

/// f16 narrow finish (FADD-shape, fixed at f16 geometry). Mirrors narFinish16.
/// post-carry at bit (mant16+1)=11; subnormal test bit mant16=10 & exp==1;
/// overflow when e >= 31 (expMax16).
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
    pack(F16, out_exp, sign_r, out_mant)
}

/// Narrow a FINITE source to f16, RNE. `src` is the source format (F32/F64).
/// Mirrors narrowFiniteCore: build the source significand, right-shift (sticky)
/// so the implicit-1 lands at (10 + GUARD_ROOM) = 13, RNE round, finish.
///   ef0_true (biased f16 exp) = eb - srcBias + 15 ; normal target when eb >
///   srcBias - 15 ; shr base = impPos - 13 ; subnormal extra = 1 - ef0_true.
fn fp16_narrow_finite(src: FpFmt, x: u64) -> u64 {
    let s = sign(src, x);
    let eb = exp_field(src, x);
    let sig = sig_build(src, !exp_all_zero(src, x), x); // top bit at index src.mant
    let imp_pos = src.mant; // implicit-1 bit position = src mantissa width (23 or 52)
    let thresh = src.bias - 15; // eb > thresh  <=>  ef0_true >= 1
    let normal_target = eb > thresh;
    // Guarded: ef0 is only used when normal_target (e_cand below); computing it
    // unconditionally underflowed u64 for sources that narrow to a subnormal/zero
    // f16 (eb + 15 < src.bias). The Python mirror used arbitrary-precision ints so
    // it never hit this; the cargo bridge (silicon facts) caught the panic.
    let ef0 = if normal_target { eb + 15 - src.bias } else { 0 }; // ef0_true (>= 1 when normal_target)
    let extra = if normal_target {
        0
    } else {
        (src.bias + 1) - (eb + 15)
    }; // 1 - ef0
    let shr = (imp_pos - 13) + extra;
    let e_cand = if normal_target { ef0 } else { 1 };
    let s_shift = shr_sticky_u128(sig, shr);
    let s_rounded = round_word(s_shift);
    nar_finish16(s, e_cand, s_rounded)
}

/// Narrow a src -> f16, full special-case dispatch. NaN -> high 10 bits of the
/// src mantissa, quieted (set bit 9), exp all-ones. Inf/Zero passthrough.
fn fp16_narrow(src: FpFmt, x: u64) -> u64 {
    let x = x & src.word_mask();
    let s = sign(src, x);
    if is_nan(src, x) {
        // f16 mant = (src mant >> (srcMantW-10)) | (1<<9) (quiet).
        let m = mant_field(src, x);
        let m16 = (m >> (src.mant - 10)) | (1u64 << 9);
        return pack(F16, 31, s, m16);
    }
    if is_inf(src, x) {
        return inf_of(F16, s);
    }
    if is_zero(src, x) {
        return zero_of(F16, s);
    }
    fp16_narrow_finite(src, x)
}

/// FCVT f32 -> f16 (narrow RNE). Mirrors fcvt_s_to_h.
pub fn fcvt_s_to_h(x: u64) -> u64 {
    fp16_narrow(F32, x)
}
/// FCVT f64 -> f16 (narrow RNE). Mirrors fcvt_d_to_h.
pub fn fcvt_d_to_h(x: u64) -> u64 {
    fp16_narrow(F64, x)
}

// ===========================================================================
// FCVT  f -> int  (FCVTZS/ZU round-to-zero, FCVTNS/NU round-to-nearest).
//   NaN -> 0 ; out-of-range SATURATES ; negative->unsigned -> 0.
//   Work register: u128 (Clean ftiRegW = 128).  Mirrors aarch64_fp_cvt.lean.
// ===========================================================================

/// Saturate+sign for the UNSIGNED case. `mag` is the magnitude (>=0); `neg` the
/// source sign. Returns the low `int_w` bits.
fn fti_finish_u(int_w: u32, neg: bool, mag: u128) -> u128 {
    let u_max: u128 = if int_w >= 128 {
        u128::MAX
    } else {
        (1u128 << int_w) - 1
    };
    let sat = if mag > u_max { u_max } else { mag };
    let v = if neg { 0 } else { sat };
    mask_low(int_w, v)
}

/// Saturate+sign for the SIGNED case. `mag` is the magnitude (>=0).
fn fti_finish_s(int_w: u32, neg: bool, mag: u128) -> u128 {
    let s_max: u128 = (1u128 << (int_w - 1)) - 1;
    let s_min_mag: u128 = 1u128 << (int_w - 1);
    let result: u128 = if neg {
        // value = -mag ; valid iff mag <= 2^(int_w-1). overflow -> INT_MIN.
        if mag <= s_min_mag {
            0u128.wrapping_sub(mag) // two's complement
        } else {
            0u128.wrapping_sub(s_min_mag)
        }
    } else if mag > s_max {
        s_max
    } else {
        mag
    };
    mask_low(int_w, result)
}

#[inline]
fn mask_low(n: u32, x: u128) -> u128 {
    if n >= 128 { x } else { x & ((1u128 << n) - 1) }
}

/// f -> int core for a FINITE non-zero value. `f` is the source FP format,
/// `int_w` the target int width, `signed`/`nearest` the mode flags.
fn fti_core(f: FpFmt, int_w: u32, signed: bool, nearest: bool, sgn: bool, x: u64) -> u128 {
    let subn = exp_all_zero(f, x);
    let eb = exp_field(f, x);
    let sig = sig_build(f, !subn, x); // implicit at index mant
    // value*2 exponent offset = ebiased - bias - mant + 1 (subnormal: 2 - bias - mant).
    let pos_part: u32 = if subn { 2 } else { eb + 1 };
    let sub_part: u32 = f.bias + f.mant;
    let shl2 = pos_part.saturating_sub(sub_part); // left amount (0 if neg)
    let shr2 = sub_part.saturating_sub(pos_part); // right amount (0 if pos)
    // align value*2: guard kept at bit0.
    let aligned: u128 = if shl2 > 0 {
        sig << shl2.min(127)
    } else if shr2 > 0 {
        if shr2 >= 128 { 0 } else { sig >> shr2 }
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
        // round-to-nearest-even on value*2: int = aligned>>1, guard = aligned bit0.
        let int_part = aligned >> 1;
        let guard = aligned & 1 == 1;
        let lsb = int_part & 1 == 1;
        let r_up = guard && (sticky || lsb);
        if r_up { int_part + 1 } else { int_part }
    } else {
        int_trunc
    };
    // HUGE-VALUE GUARD (owner #9 fix): saturate whenever aligning value*2
    // (`sig << shl2`) overflows the u128 work register — i.e. `shl2` exceeds sig's
    // leading zeros, so the top bit is shifted out and `aligned` wraps. The old guard
    // `shl2 >= FTI_REG_W` only caught a huge shift amount and MISSED exact powers of
    // two whose sig MSB (at bit `mant`) pushes the product past 2^128: e.g. f32 2^127
    // has sig=2^23, shl2=105 > lz(sig)=104, so `aligned` wrapped to 0 and the result
    // UNDER-saturated to 0 instead of INT_MAX. When it overflows the u128, the true
    // magnitude far exceeds any int_w, so force saturation. (Values that fit in u128
    // but exceed int_w are still saturated correctly by fti_finish_s/u.)
    let too_big = shl2 > 0 && shl2 > sig.leading_zeros();
    let over_mag: u128 = 1u128 << int_w; // 2^int_w forces saturation
    let rounded = if too_big { over_mag } else { rounded_raw };
    if signed {
        fti_finish_s(int_w, sgn, rounded)
    } else {
        fti_finish_u(int_w, sgn, rounded)
    }
}

/// f -> int, generic. Returns exactly `int_w` low bits.
fn fti(f: FpFmt, int_w: u32, signed: bool, nearest: bool, x: u64) -> u64 {
    let x = x & f.word_mask();
    let sgn = sign(f, x);
    let over_mag: u128 = 1u128 << int_w;
    let r = if is_nan(f, x) {
        0
    } else if is_inf(f, x) {
        if signed {
            fti_finish_s(int_w, sgn, over_mag)
        } else {
            fti_finish_u(int_w, sgn, over_mag)
        }
    } else if is_zero(f, x) {
        0
    } else {
        fti_core(f, int_w, signed, nearest, sgn, x)
    };
    mask_low(int_w, r) as u64
}

// Named f->int entries (FP fmt, int width, signed, nearest).
pub fn fcvtzs(f: FpFmt, int_w: u32, x: u64) -> u64 {
    fti(f, int_w, true, false, x)
}
pub fn fcvtzu(f: FpFmt, int_w: u32, x: u64) -> u64 {
    fti(f, int_w, false, false, x)
}
pub fn fcvtns(f: FpFmt, int_w: u32, x: u64) -> u64 {
    fti(f, int_w, true, true, x)
}
pub fn fcvtnu(f: FpFmt, int_w: u32, x: u64) -> u64 {
    fti(f, int_w, false, true, x)
}

// ===========================================================================
// x86 f -> SIGNED int  (CVT[T]SS2SI / CVT[T]SD2SI), INTEGER-INDEFINITE on
// out-of-range / NaN / +-Inf.  Intel SDM Vol 2A: when the source cannot be
// represented in the destination integer (NaN, +-Inf, or the rounded magnitude
// is outside the signed `int_w`-bit range), the result is the "integer
// indefinite" value: sign bit set, all other bits 0 (i.e. INT_MIN for the
// destination width). Otherwise the normally-rounded value is returned.
//
// This is the SAME rounding machinery as `fcvtzs`/`fcvtns` (`fti_core`,
// silicon-validated); only the OUT-OF-RANGE policy differs (x86 indefinite vs
// AArch64/wasm/RISC-V saturate). `nearest` selects CVT* (RNE) vs CVTT* (RTZ).
// ===========================================================================

/// The x86 integer-indefinite value for a `int_w`-bit signed destination:
/// the most-negative integer (sign bit set, rest 0), masked to `int_w` bits.
#[inline]
fn integer_indefinite(int_w: u32) -> u128 {
    mask_low(int_w, 1u128 << (int_w - 1))
}

/// Compute (rounded magnitude, too_big) for a FINITE non-zero value, sharing
/// the exact alignment/rounding of `fti_core` but WITHOUT applying the
/// saturate-or-indefinite finish — so the caller decides the out-of-range
/// policy.
fn fti_mag(f: FpFmt, nearest: bool, x: u64) -> (u128, bool) {
    let subn = exp_all_zero(f, x);
    let eb = exp_field(f, x);
    let sig = sig_build(f, !subn, x);
    let pos_part: u32 = if subn { 2 } else { eb + 1 };
    let sub_part: u32 = f.bias + f.mant;
    let shl2 = pos_part.saturating_sub(sub_part);
    let shr2 = sub_part.saturating_sub(pos_part);
    let aligned: u128 = if shl2 > 0 {
        sig << shl2.min(127)
    } else if shr2 > 0 {
        if shr2 >= 128 { 0 } else { sig >> shr2 }
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
    // owner #9 fix: saturate when `sig << shl2` overflows the u128 work register
    // (shl2 > sig's leading zeros), not just when shl2 >= 128 — see fti_core.
    let too_big = shl2 > 0 && shl2 > sig.leading_zeros();
    (rounded_raw, too_big)
}

/// f -> signed int with x86 integer-indefinite out-of-range behaviour.
/// `nearest` = false -> CVTT* (truncate toward zero); true -> CVT* (RNE).
fn fti_indef_s(f: FpFmt, int_w: u32, nearest: bool, x: u64) -> u64 {
    let x = x & f.word_mask();
    // NaN and +-Inf are never representable -> integer indefinite.
    if is_nan(f, x) || is_inf(f, x) {
        return mask_low(int_w, integer_indefinite(int_w)) as u64;
    }
    if is_zero(f, x) {
        return 0;
    }
    let sgn = sign(f, x);
    let (mag, too_big) = fti_mag(f, nearest, x);
    // Signed range: [-2^(int_w-1), 2^(int_w-1) - 1]. The valid magnitudes are
    // mag <= 2^(int_w-1)-1 for non-negative, mag <= 2^(int_w-1) for negative.
    let s_max: u128 = (1u128 << (int_w - 1)) - 1;
    let s_min_mag: u128 = 1u128 << (int_w - 1);
    let out_of_range = too_big || if sgn { mag > s_min_mag } else { mag > s_max };
    if out_of_range {
        return mask_low(int_w, integer_indefinite(int_w)) as u64;
    }
    let result: u128 = if sgn { 0u128.wrapping_sub(mag) } else { mag };
    mask_low(int_w, result) as u64
}

/// x86 CVTT*2SI: f -> signed int, truncate toward zero, integer-indefinite OOR.
pub fn cvtt_to_si(f: FpFmt, int_w: u32, x: u64) -> u64 {
    fti_indef_s(f, int_w, false, x)
}

/// x86 CVT*2SI: f -> signed int, round-to-nearest-even, integer-indefinite OOR.
pub fn cvt_to_si(f: FpFmt, int_w: u32, x: u64) -> u64 {
    fti_indef_s(f, int_w, true, x)
}

// ===========================================================================
// int -> f  (SCVTF / UCVTF), RNE.  Mirrors aarch64_fp_cvt.lean itf.
// ===========================================================================

/// int -> f. `int_w` source int width, `signed` selects SCVTF/UCVTF.
fn itf(f: FpFmt, int_w: u32, signed: bool, x: u64) -> u64 {
    let src = mask_low(int_w, x as u128);
    if src == 0 {
        return zero_of(f, false);
    }
    let neg = signed && ((x >> (int_w - 1)) & 1 == 1);
    let mag: u128 = if neg {
        mask_low(int_w, 0u128.wrapping_sub(src))
    } else {
        src
    };
    let sgn = neg;
    itf_core(f, sgn, mag)
}

fn itf_core(f: FpFmt, sgn: bool, mag: u128) -> u64 {
    let hi = hi_set_u128(mag);
    let target = f.mant + GUARD_ROOM;
    let placed: u128 = if target < hi {
        // need right shift, fold sticky into bit0.
        let shr = hi - target;
        shr_sticky_u128(mag, shr)
    } else {
        mag << (target - hi)
    };
    let e_cand = hi + f.bias;
    let s_rounded = round_word(placed);
    let post_carry = (s_rounded >> (f.mant + 1)) & 1 == 1;
    let s_final = if post_carry {
        s_rounded >> 1
    } else {
        s_rounded
    };
    let e_final = if post_carry { e_cand + 1 } else { e_cand };
    let overflow = e_final >= f.exp_max();
    let out_exp = if overflow { f.exp_max() } else { e_final };
    let out_mant = if overflow { 0 } else { s_final as u64 };
    pack(f, out_exp, sgn, out_mant)
}

pub fn scvtf(f: FpFmt, int_w: u32, x: u64) -> u64 {
    itf(f, int_w, true, x)
}
pub fn ucvtf(f: FpFmt, int_w: u32, x: u64) -> u64 {
    itf(f, int_w, false, x)
}

// ===========================================================================
// FDIV / FSQRT — RNE.  PORTED FROM (read-only, M4-silicon-validated, integer-
// only, zero-axiom):
//   proofs/aarch64_fp_divsqrt.lean
//     FDIV : restoring bit-by-bit LONG DIVISION of the implicit-bit-extended
//            significands + REMAINDER-STICKY + RNE + specials.
//     FSQRT: digit-by-digit (non-restoring style, two-bits-per-iteration)
//            integer SQUARE-ROOT + REMAINDER-STICKY + RNE + specials.
// Both are width-generic (binary32 / binary64) via `FpFmt` and use ONLY
// integer/bitwise ops on u128 (no f32/f64 anywhere — enforced by the grep gate).
//
// FAITHFULNESS NOTE re. register width. The Clean reference MATERIALIZES the
// shifted dividend `num = sigA << bigS` and the radicand `M = sigE << (2*fbits)`
// as single CLOSED Nats (arbitrary precision) and derives the sticky by a
// multiply-back (`q*sigB != num` / `root*root != M`). For f64 those materialized
// integers exceed 128 bits (M ≈ 170 bits). We DO NOT need them: the long-
// division / digit recursion threads only the running REMAINDER (which stays
// < divisor / < 2*root+1 — well under 128 bits), and `num = q*den + rem` /
// `M = root*root + rem` give `q*den != num ⟺ rem != 0` and
// `root*root != M ⟺ rem != 0`. So we compute the sticky from the (small)
// final remainder — MATHEMATICALLY IDENTICAL to the Clean multiply-back, and
// keeping every intermediate within u128. The radicand bits are read on demand
// from `sigE` (bit j of M is bit (j - 2*fbits) of sigE) rather than materialized.
// ===========================================================================

/// A finite operand's significand as an integer (implicit bit included):
/// normal -> 2^mant + mantissa ; subnormal -> mantissa (no implicit). Mirrors
/// Clean `sigNat`.
#[inline]
fn sig_nat(f: FpFmt, subn: bool, x: u64) -> u128 {
    let m = mant_field(f, x) as u128;
    if subn { m } else { m | (1u128 << f.mant) }
}

/// Effective biased exponent (subnormals act at 1). Mirrors the Clean
/// `selNat (expAllZero..) 1 (expNat ..)`.
#[inline]
fn eff_exp(f: FpFmt, x: u64) -> u32 {
    if exp_all_zero(f, x) {
        1
    } else {
        exp_field(f, x)
    }
}

/// `true` iff the low `k` bits of `v` are not all zero (the dropped-bits sticky).
/// Mirrors Clean `stickyShrNat`.
#[inline]
fn sticky_shr_u128(v: u128, k: u32) -> bool {
    if k == 0 {
        false
    } else if k >= 128 {
        v != 0
    } else {
        (v & ((1u128 << k) - 1)) != 0
    }
}

/// Right-shift `v` by `k`, clamping to 0 for `k >= 128` (Rust `>>` by >= bit-width
/// panics; the Clean `Nat.shiftRight` saturates to 0). The shifted-out bits are
/// the caller's sticky via `sticky_shr_u128`. Used for placing a deeply-underflowed
/// quotient / root (e.g. min-subnormal / max-normal divide).
#[inline]
fn shr_u128(v: u128, k: u32) -> u128 {
    if k >= 128 { 0 } else { v >> k }
}

/// RNE-round a significand whose kept-LSB sits at bit `GUARD_ROOM` (= 3), with
/// guard at bit 2, round at bit 1, sticky at bit 0 (plus the folded-in division/
/// sqrt remainder sticky `extra_sticky`). Returns the mantissa-placed (>>3)
/// significand, +1 if it rounds up. Mirrors Clean `roundNat`.
fn round_nat(placed: u128, extra_sticky: bool) -> u128 {
    let lsb = (placed >> GUARD_ROOM) & 1 == 1;
    let guard = (placed >> 2) & 1 == 1;
    let round_b = (placed >> 1) & 1 == 1;
    let sticky_b = extra_sticky || (placed & 1 == 1);
    let r_up = round_up(lsb, guard, round_b || sticky_b);
    let mant_place = placed >> GUARD_ROOM;
    if r_up { mant_place + 1 } else { mant_place }
}

/// finishNat: post-round renormalise (single implicit carry) + overflow + pack.
/// `e_cand` is the candidate biased exponent (>= 1 regime). Mirrors `finishNat`.
fn finish_nat(f: FpFmt, sign_r: bool, e_cand: u32, sig: u128) -> u64 {
    let post_carry = (sig >> (f.mant + 1)) & 1 == 1;
    let s_fin = if post_carry { sig >> 1 } else { sig };
    let e_fin = if post_carry { e_cand + 1 } else { e_cand };
    let overflow = e_fin >= f.exp_max();
    let out_exp = if overflow { f.exp_max() } else { e_fin };
    let out_mant = if overflow {
        0
    } else {
        (s_fin as u64) & f.mant_mask()
    };
    pack(f, out_exp, sign_r, out_mant)
}

/// finishNatSub: finishNat + subnormal (out_e == 0) round-up-to-min-normal
/// promotion. Mirrors `finishNatSub` (used by FDIV's gradual-underflow path).
fn finish_nat_sub(f: FpFmt, sign_r: bool, out_e: u32, sig: u128) -> u64 {
    let post_carry = (sig >> (f.mant + 1)) & 1 == 1;
    let s_fin = if post_carry { sig >> 1 } else { sig };
    let e_fin0 = if post_carry { out_e + 1 } else { out_e };
    // a subnormal (out_e 0) that rounded up to set the implicit bit -> min normal.
    let promote = out_e == 0 && ((s_fin >> f.mant) & 1 == 1);
    let e_fin = if promote { 1 } else { e_fin0 };
    let overflow = e_fin >= f.exp_max();
    let out_exp = if overflow { f.exp_max() } else { e_fin };
    let out_mant = if overflow {
        0
    } else {
        (s_fin as u64) & f.mant_mask()
    };
    pack(f, out_exp, sign_r, out_mant)
}

/// Restoring bit-by-bit long division of a u128 `num` (with `bits_n` significant
/// bits) by `den`, returning (quotient, final remainder). The remainder stays
/// < `den` throughout (so it — and `rem2 = rem*2 + bit` < 2*den — fit in u128).
/// Mirrors Clean `divQ` / `divRem` fused into one pass.
fn div_long(bits_n: u32, num: u128, den: u128) -> (u128, u128) {
    let mut rem: u128 = 0;
    let mut q: u128 = 0;
    // i runs from bits_n-1 down to 0 (consume the dividend MSB-first).
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

/// FDIV finite path. `ea_e`/`eb_e` effective biased exponents; `sig_a`/`sig_b`
/// implicit-bit-extended significands. Mirrors `fDivFinite` + `fdFinish`.
///
/// FAITHFULNESS FIX (beyond the Clean reference, which assumed NORMALIZED
/// significands and silently lost quotient precision for SUBNORMAL operands —
/// untested by the silicon grid, which has no subnormal divides). We FIRST
/// normalize each subnormal significand so its top set bit lands at index `mant`
/// (the implicit-bit position), recording the normalization left-shifts `s_a` /
/// `s_b`. Normalization preserves the operand VALUE (value = sig*2^(e-bias-mant),
/// so sig<<s with e tracked by -s leaves it unchanged), and is folded into the
/// field-weight exponent bookkeeping (pos_part += s_b ; sub_part += s_a). With
/// both significands normalized to `mant` bits the quotient ALWAYS has >= target+1
/// significant bits, so no rounding bits are dropped. For normal operands
/// s_a == s_b == 0 and this reduces EXACTLY to the validated Clean formula.
fn fdiv_finite(f: FpFmt, sign_r: bool, ea_e: u32, eb_e: u32, sig_a: u128, sig_b: u128) -> u64 {
    // Normalize subnormal significands so the top set bit lands at index `mant`.
    let s_a = f.mant - hi_set_u128(sig_a);
    let s_b = f.mant - hi_set_u128(sig_b);
    let sig_a = sig_a << s_a;
    let sig_b = sig_b << s_b;
    let big_s = f.mant + GUARD_ROOM + 2;
    let num = sig_a << big_s;
    let bits_n = hi_set_u128(num) + 1;
    let (q, rem) = div_long(bits_n, num, sig_b);
    let div_sticky = rem != 0;
    let qhi = hi_set_u128(q);
    let target = f.mant + GUARD_ROOM;
    // biased exponent: Ebiased = qhi + ea_e + bias + s_b - eb_e - big_s - s_a.
    let pos_part = qhi + ea_e + f.bias + s_b;
    let sub_part = eb_e + big_s + s_a;
    let underflow = pos_part <= sub_part;
    let extra = if underflow {
        (sub_part - pos_part) + 1
    } else {
        0
    };
    let shift_src = qhi + extra;
    let need_right = shift_src > target;
    let shr = shift_src.saturating_sub(target);
    let shl = target.saturating_sub(shift_src);
    let place_sticky = need_right && sticky_shr_u128(q, shr);
    let placed = if need_right {
        shr_u128(q, shr)
    } else {
        q << shl
    };
    let out_e = if underflow { 0 } else { pos_part - sub_part };
    let rounded = round_nat(placed, div_sticky || place_sticky);
    finish_nat_sub(f, sign_r, out_e, rounded)
}

/// FDIV with full special-case dispatch. Mirrors `fdiv32` / `fdiv64`.
///   NaN -> selectNaN ; Inf/Inf -> qNaN ; Inf/fin -> Inf ; fin/Inf -> 0 ;
///   0/0 -> qNaN ; 0/fin -> 0 ; x/0 -> +-Inf (DZ) ; sign = signA XOR signB.
pub fn fdiv(f: FpFmt, a: u64, b: u64) -> u64 {
    let a = a & f.word_mask();
    let b = b & f.word_mask();
    let sgn = sign(f, a) ^ sign(f, b);
    if is_nan(f, a) || is_nan(f, b) {
        return select_nan(f, a, b);
    }
    if is_inf(f, a) {
        return if is_inf(f, b) {
            default_qnan(f)
        } else {
            inf_of(f, sgn)
        };
    }
    if is_inf(f, b) {
        return zero_of(f, sgn);
    }
    if is_zero(f, a) {
        return if is_zero(f, b) {
            default_qnan(f)
        } else {
            zero_of(f, sgn)
        };
    }
    if is_zero(f, b) {
        return inf_of(f, sgn);
    }
    fdiv_finite(
        f,
        sgn,
        eff_exp(f, a),
        eff_exp(f, b),
        sig_nat(f, exp_all_zero(f, a), a),
        sig_nat(f, exp_all_zero(f, b), b),
    )
}

/// Digit-by-digit integer square root over `iters` result bits of the radicand
/// `M = sig_e << (2*fbits)`, reading two radicand bits per iteration WITHOUT
/// materializing `M` (bit `2i+1..2i` of M = the corresponding bits of `sig_e`
/// offset down by `2*fbits`). Returns (root, final remainder). The remainder
/// stays < 2*root+1 (fits u128). Mirrors Clean `sqrtRoot` / `sqrtRem`.
fn sqrt_digits(iters: u32, sig_e: u128, two_fbits: u32) -> (u128, u128) {
    let mut rem: u128 = 0;
    let mut root: u128 = 0;
    let mut i = iters;
    while i > 0 {
        i -= 1;
        // the two radicand bits at positions 2i+1, 2i of M = sig_e << two_fbits.
        let pos = i * 2;
        let two_bits = if pos >= two_fbits {
            (sig_e >> (pos - two_fbits)) & 3
        } else if pos + 1 == two_fbits {
            // straddle: only the high of the pair (bit two_fbits) maps to sig_e bit 0.
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

/// FSQRT finite positive path. `e_e` effective biased exponent, `sig` implicit-
/// bit-extended significand. Mirrors `fSqrtFinite` + the staged sqOff/sqFinish.
fn fsqrt_finite(f: FpFmt, e_e: u32, sig: u128) -> u64 {
    // p = e_e - bias - mant, tracked with an even offset to stay non-negative.
    const SQ_OFF: u32 = 4096; // even, > any |p| for our widths
    let fbits = f.mant + GUARD_ROOM + 3;
    let p_off = (e_e + SQ_OFF) - (f.bias + f.mant); // = p + SQ_OFF (always >= 0)
    let odd = p_off & 1 == 1;
    // make the radicand exponent EVEN: if p is odd, shift sig left 1 (p' = p - 1).
    let sig_e = if odd { sig << 1 } else { sig };
    let p_prime_off = if odd { p_off - 1 } else { p_off }; // p' + SQ_OFF (even)
    // M = sig_e << (2*fbits) ; iters = top-bit(M)/2 + 1, computed from sig_e.
    let two_fbits = fbits * 2;
    let m_hi = hi_set_u128(sig_e) + two_fbits; // top set bit index of M
    let iters = (m_hi >> 1) + 1;
    let (root, rem) = sqrt_digits(iters, sig_e, two_fbits);
    let sticky = rem != 0;
    // place + round + finish (sqFinish).
    let rhi = hi_set_u128(root);
    let half_off = SQ_OFF >> 1;
    let half_prime_off = p_prime_off >> 1; // = p'/2 + SQ_OFF/2
    let pos_part = rhi + half_prime_off + f.bias;
    let sub_part = half_off + fbits;
    let e_cand = pos_part - sub_part;
    let target = f.mant + GUARD_ROOM;
    let need_right = rhi > target;
    let shr = rhi.saturating_sub(target);
    let shl = target.saturating_sub(rhi);
    let place_sticky = need_right && sticky_shr_u128(root, shr);
    let placed = if need_right {
        shr_u128(root, shr)
    } else {
        root << shl
    };
    let rounded = round_nat(placed, sticky || place_sticky);
    finish_nat(f, false, e_cand, rounded)
}

/// FSQRT with full special-case dispatch. Mirrors `fsqrt32` / `fsqrt64`.
///   NaN -> selectNaN ; -0 -> -0 ; neg (nonzero) -> default qNaN ;
///   +Inf -> +Inf ; +0 -> +0.
pub fn fsqrt(f: FpFmt, a: u64) -> u64 {
    let a = a & f.word_mask();
    if is_nan(f, a) {
        return select_nan(f, a, a);
    }
    if sign(f, a) {
        return if is_zero(f, a) { a } else { default_qnan(f) };
    }
    if is_inf(f, a) {
        return a;
    }
    if is_zero(f, a) {
        return a;
    }
    fsqrt_finite(f, eff_exp(f, a), sig_nat(f, exp_all_zero(f, a), a))
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- a few of the Clean in-file sanity witnesses, ported as unit checks.

    #[test]
    fn classify_basic() {
        // 0x7FF0_..0 = +Inf f64 ; 0x7FF8_..0 = qNaN f64.
        assert!(is_inf(F64, 0x7FF0_0000_0000_0000));
        assert!(is_nan(F64, 0x7FF8_0000_0000_0000));
        assert!(is_qnan(F64, 0x7FF8_0000_0000_0000));
        assert!(is_snan(F64, 0x7FF0_0000_0000_0001));
        assert!(is_zero(F32, 0));
        assert!(is_zero(F32, 0x8000_0000)); // -0
    }

    #[test]
    fn fabs_fneg() {
        assert_eq!(fabs(F32, 0xBF80_0000), 0x3F80_0000); // |-1.0| = 1.0
        assert_eq!(fneg(F32, 0x3F80_0000), 0xBF80_0000); // -(1.0) = -1.0
    }

    #[test]
    fn fadd_witnesses() {
        // 1.0 + 1.0 = 2.0 (0x3F800000 + 0x3F800000 = 0x40000000)
        assert_eq!(fadd(F32, 0x3F80_0000, 0x3F80_0000), 0x4000_0000);
        // 1.0 + (-1.0) = +0
        assert_eq!(fadd(F32, 0x3F80_0000, 0xBF80_0000), 0x0000_0000);
        // (-0)+(-0) = -0
        assert_eq!(fadd(F32, 0x8000_0000, 0x8000_0000), 0x8000_0000);
    }

    // REGRESSION (#94 f32 stage): the FADD/FSUB alignment-sticky-on-SUBTRACT borrow
    // fix. When the smaller operand is shifted right during alignment and drops
    // nonzero bits, an effective SUBTRACTION must SUBTRACT that dropped fraction
    // (borrow), not OR it in (which adds). The old code did
    // `(s_big - s_small_a) | sticky`, producing a 1-ULP-too-high result in the
    // cancellation path. The silicon grid has no such case, so the bridge could not
    // catch it; found by an 81M/280M-input differential fuzz vs the host FPU and
    // confirmed 1 ULP off the correctly-rounded RNE value by exact-rational
    // arithmetic. These pin the CORRECTLY-ROUNDED results as INTEGER bit patterns
    // (== a faithful FPU, cross-checked offline). A regression to the
    // OR-after-subtract form mismatches these (it would yield the +1-ULP value
    // shown in each comment). The differential-vs-host-FPU fuzz lives in
    // tests/fp_bitmodel_bridge.rs (it legitimately uses the host FPU as an oracle,
    // which the integer-only grep gate forbids inside this model file).
    #[test]
    fn fadd_fsub_subtract_sticky_borrow() {
        // 1.0 + (tiny negative 0xBA9CC52D) — the original witness. Correctly-rounded
        // RNE = 0x3F7FB19D; the OR-after-subtract bug gave 0x3F7FB19E (+1 ULP).
        assert_eq!(fadd(F32, 0x3F80_0000, 0xBA9C_C52D), 0x3F7F_B19D);
        // The FSUB form of the same: 1.0 - 0x3A9CC52D == 0x3F7FB19D.
        assert_eq!(fsub(F32, 0x3F80_0000, 0x3A9C_C52D), 0x3F7F_B19D);
        // 2.0 + (tiny negative 0xB5CA365A): subtractive alignment drops sticky bits,
        // RNE = 0x3FFFFFF3 (the OR-bug gave 0x3FFFFFF4, +1 ULP).
        assert_eq!(fadd(F32, 0x4000_0000, 0xB5CA_365A), 0x3FFF_FFF3);
        // F64 analogue (same bug class, in production since #89): 1.0 + a small
        // negative (0xBC90000000000001) whose low set bit falls below the result
        // LSB, forcing alignment to drop nonzero sticky bits on the subtraction.
        // Correctly-rounded RNE = 0x3FEFFFFFFFFFFFFF (cross-checked vs the host FPU
        // offline); the OR-after-subtract bug rounded up by 1 ULP to 0x3FF0..0.
        assert_eq!(
            fadd(F64, 0x3FF0_0000_0000_0000, 0xBC90_0000_0000_0001),
            0x3FEF_FFFF_FFFF_FFFF
        );
    }

    #[test]
    fn fmul_witnesses() {
        // 2.0 * 3.0 = 6.0 (0x40000000 * 0x40400000 = 0x40C00000)
        assert_eq!(fmul(F32, 0x4000_0000, 0x4040_0000), 0x40C0_0000);
        // (-1.0) * 2.0 = -2.0 (sign = xor)
        assert_eq!(fmul(F32, 0xBF80_0000, 0x4000_0000), 0xC000_0000);
    }

    #[test]
    fn cvt_widen_narrow() {
        // widen 2.0_f32 (0x40000000) -> 2.0_f64 (0x4000000000000000)
        assert_eq!(fcvt_widen(0x4000_0000), 0x4000_0000_0000_0000);
        // narrow 1.0_f64 (0x3FF0000000000000) -> 1.0_f32 (0x3F800000)
        assert_eq!(fcvt_narrow(0x3FF0_0000_0000_0000), 0x3F80_0000);
    }

    #[test]
    fn cvt_f_to_int() {
        // FCVTZS 2.5_f32 -> 2 (round to zero)
        assert_eq!(fcvtzs(F32, 32, 0x4020_0000), 2);
        // FCVTNS 2.5_f32 -> 2 (ties to even)
        assert_eq!(fcvtns(F32, 32, 0x4020_0000), 2);
        // FCVTNS 3.5_f32 -> 4 (ties to even)
        assert_eq!(fcvtns(F32, 32, 0x4060_0000), 4);
    }

    #[test]
    fn cvt_int_to_f() {
        // SCVTF 1_W -> 1.0_f32
        assert_eq!(scvtf(F32, 32, 1), 0x3F80_0000);
        // SCVTF -1_W (0xFFFFFFFF) -> -1.0_f32
        assert_eq!(scvtf(F32, 32, 0xFFFF_FFFF), 0xBF80_0000);
        // UCVTF 1_X -> 1.0_f64
        assert_eq!(ucvtf(F64, 64, 1), 0x3FF0_0000_0000_0000);
    }

    // ---- FP16 witnesses (mirror the chip-validated `:= rfl` of aarch64_fp16.lean).
    // 1.0 f16 = 0x3C00 ; 2.0 = 0x4000 ; 3.0 = 0x4200 ; 6.0 = 0x4600 ;
    // +Inf = 0x7C00 ; qNaN = 0x7E00 ; sNaN = 0x7C01 ; max subnormal = 0x03FF ;
    // min subnormal = 0x0001 (= 2^-24) ; min normal = 0x0400.

    #[test]
    fn fp16_classify() {
        assert!(is_inf(F16, 0x7C00));
        assert!(is_qnan(F16, 0x7E00));
        assert!(is_snan(F16, 0x7C01));
        assert!(is_zero(F16, 0x0000));
        assert!(is_subnormal(F16, 0x03FF));
        assert!(is_normal(F16, 0x3C00));
    }

    #[test]
    fn fp16_widen_witnesses() {
        // widen 1.0_f16 (0x3C00) -> 1.0_f32 (0x3F800000).
        assert_eq!(fcvt_h_to_s(0x3C00), 0x3F80_0000);
        // widen min subnormal f16 (0x0001 = 2^-24) -> 2^-24 f64 (NORMAL: exp 999).
        // exp 999 = 0x3E7 ; 0x3E7 << 52 = 0x3E70_0000_0000_0000.
        assert_eq!(fcvt_h_to_d(0x0001), 0x3E70_0000_0000_0000);
        // widen +Inf f16 -> +Inf f64.
        assert_eq!(fcvt_h_to_d(0x7C00), 0x7FF0_0000_0000_0000);
        // widen sNaN f16 (0x7C01) -> f32: quieted (set bit 22), payload shifted.
        assert_eq!(fcvt_h_to_s(0x7C01), 0x7FC0_2000);
    }

    #[test]
    fn fp16_narrow_witnesses() {
        // narrow 3.0_f32 (0x40400000) -> 3.0_f16 (0x4200).
        assert_eq!(fcvt_s_to_h(0x4040_0000), 0x4200);
        // narrow 1.0_f64 -> 1.0_f16 (0x3C00).
        assert_eq!(fcvt_d_to_h(0x3FF0_0000_0000_0000), 0x3C00);
        // OVERFLOW: a huge f64 (> f16 max ~65504) narrows to +Inf (0x7C00).
        // 1e6 = 0x412E848000000000.
        assert_eq!(fcvt_d_to_h(0x412E_8480_0000_0000), 0x7C00);
        // narrow qNaN f64 -> f16 qNaN (0x7E00).
        assert_eq!(fcvt_d_to_h(0x7FF8_0000_0000_0000), 0x7E00);
    }

    #[test]
    fn fp16_widen_narrow_roundtrip_is_identity() {
        // Every f16 widens to f64 EXACTLY, so narrowing back is the identity for
        // all finite, inf, and qNaN classes (sNaN narrows to a quieted qNaN).
        for bits in 0u64..=0xFFFF {
            // skip sNaN (quieting changes the payload deliberately).
            if is_snan(F16, bits) {
                continue;
            }
            let wide = fcvt_h_to_d(bits);
            let back = fcvt_d_to_h(wide);
            // NaN payloads: a qNaN widened then narrowed stays a qNaN; compare class.
            if is_nan(F16, bits) {
                assert!(is_nan(F16, back), "qNaN roundtrip failed for {bits:#06x}");
            } else {
                assert_eq!(
                    back, bits,
                    "f16 widen-narrow roundtrip mismatch for {bits:#06x}"
                );
            }
        }
    }

    #[test]
    fn fp16_arith_witnesses() {
        // FADD.h 1.0 + 1.0 = 2.0 (0x4000).
        assert_eq!(fadd(F16, 0x3C00, 0x3C00), 0x4000);
        // FMUL.h 2.0 * 3.0 = 6.0 (0x4600).
        assert_eq!(fmul(F16, 0x4000, 0x4200), 0x4600);
        // FMUL.h SUBNORMAL UNDERFLOW: maxsub * maxsub (0x03FF^2) -> +0 (0x0000).
        // (the gradual-underflow path that needs the LEFT-shift `need_left` branch.)
        assert_eq!(fmul(F16, 0x03FF, 0x03FF), 0x0000);
        // FMUL.h min-subnormal * 2^10: minsub(0x0001) * 1024.0(0x6400) -> min normal
        // (0x0400). Exercises the need_left LEFT-shift branch producing a normal.
        assert_eq!(fmul(F16, 0x0001, 0x6400), 0x0400);
    }

    // ---- FDIV / FSQRT witnesses (decoded from the M4-chip-validated `:= rfl`
    // ds_sanity_* of proofs/aarch64_fp_divsqrt.lean — see the LSB-first List Bool
    // literals there). These pin the integer-only port to silicon-recorded bits.
    #[test]
    fn fdiv_witnesses() {
        // ds_sanity_div_simple: 2.0 / 1.0 = 2.0.
        assert_eq!(fdiv(F32, 0x4000_0000, 0x3F80_0000), 0x4000_0000);
        // ds_sanity_div_third: 1.0 / 3.0 = 0x3eaaaaab (RNE of the repeating quotient).
        assert_eq!(fdiv(F32, 0x3F80_0000, 0x4040_0000), 0x3EAA_AAAB);
        // ds_sanity_div_byzero: x/0 -> +Inf (DZ). 0x3FFFFFFE (a finite) / +0.
        assert_eq!(fdiv(F32, 0x3FFF_FFFE, 0x0000_0000), 0x7F80_0000);
        // ds_sanity_div_zerozero: 0/0 -> default qNaN.
        assert_eq!(fdiv(F32, 0x0000_0000, 0x0000_0000), 0x7FC0_0000);
        // binary64: 6.0 / 2.0 = 3.0.
        assert_eq!(
            fdiv(F64, 0x4018_0000_0000_0000, 0x4000_0000_0000_0000),
            0x4008_0000_0000_0000
        );
        // -1.0 / 2.0 = -0.5 (sign = xor; exact).
        assert_eq!(fdiv(F32, 0xBF80_0000, 0x4000_0000), 0xBF00_0000);
    }

    #[test]
    fn fsqrt_witnesses() {
        // ds_sanity_sqrt_four: sqrt(4.0) = 2.0 (perfect square, exact).
        assert_eq!(fsqrt(F32, 0x4080_0000), 0x4000_0000);
        // ds_sanity_sqrt_two: sqrt(2.0) = 0x3fb504f3 (irrational, RNE).
        assert_eq!(fsqrt(F32, 0x4000_0000), 0x3FB5_04F3);
        // ds_sanity_sqrt_neg: sqrt(negative finite) -> default qNaN.
        assert_eq!(fsqrt(F32, 0xBFFF_FFFE), 0x7FC0_0000);
        // ds_sanity_sqrt64: sqrt(2.0_f64) = 0x3ff6a09e667f3bcd.
        assert_eq!(fsqrt(F64, 0x4000_0000_0000_0000), 0x3FF6_A09E_667F_3BCD);
        // sqrt(1.0) = 1.0 ; sqrt(+0) = +0 ; sqrt(-0) = -0 ; sqrt(+Inf) = +Inf.
        assert_eq!(fsqrt(F32, 0x3F80_0000), 0x3F80_0000);
        assert_eq!(fsqrt(F32, 0x0000_0000), 0x0000_0000);
        assert_eq!(fsqrt(F32, 0x8000_0000), 0x8000_0000);
        assert_eq!(fsqrt(F32, 0x7F80_0000), 0x7F80_0000);
        // sqrt(9.0_f64) = 3.0_f64 (perfect square).
        assert_eq!(fsqrt(F64, 0x4022_0000_0000_0000), 0x4008_0000_0000_0000);
    }

    // SUBNORMAL-operand div/sqrt: the silicon grid has NO subnormal divides, so
    // the Clean reference's normalized-significand assumption silently dropped
    // quotient precision there. fdiv_finite now normalizes subnormal significands
    // first; these pin the fix (expected values are the correctly-rounded RNE
    // results, identical to a faithful FPU and to the bit-model's full-precision
    // long division). A regression to the un-normalized path mismatches these.
    #[test]
    fn fdiv_subnormal_operands() {
        // min subnormal f32 (0x1) / max subnormal f32 (0x007fffff) = 2^-23 / (1-2^-23)
        // correctly-rounded to 0x34000001 (the LSB the un-normalized path dropped).
        assert_eq!(fdiv(F32, 0x0000_0001, 0x007F_FFFF), 0x3400_0001);
        // min subnormal f32 / 1.0 = the same min subnormal (exact).
        assert_eq!(fdiv(F32, 0x0000_0001, 0x3F80_0000), 0x0000_0001);
        // 1.0 / min subnormal f32 -> +Inf (overflow).
        assert_eq!(fdiv(F32, 0x3F80_0000, 0x0000_0001), 0x7F80_0000);
        // min subnormal f64 / max subnormal f64 -> correctly-rounded LSB present.
        assert_eq!(
            fdiv(F64, 0x0000_0000_0000_0001, 0x000F_FFFF_FFFF_FFFF),
            0x3CB0_0000_0000_0001
        );
        // subnormal result: 4.0 / a huge normal underflows toward subnormal/0
        // (panic-free placement of a deeply-underflowed quotient).
        let _ = fdiv(F32, 0x0080_0000, 0x7F7F_FFFF); // min-normal / max-normal
    }

    // FMA — scalar single-rounding fused multiply-add. These pins were captured
    // from the AArch64 FMADD *instruction* (clang inline-asm on Apple silicon);
    // the exhaustive bit-identity vs the hardware FMADD lives in
    // scripts/fuzz/fmafuzz.py. The SINGLE-ROUNDING property (fused != unfused) is
    // the whole point and is asserted directly below.
    #[test]
    fn fma_witnesses() {
        // Exact: 2*3 + 4 = 10.0 (f64).
        assert_eq!(
            fma(
                F64,
                0x4000_0000_0000_0000,
                0x4008_0000_0000_0000,
                0x4010_0000_0000_0000
            ),
            0x4024_0000_0000_0000
        );
        // 1.5 * 2.0 + (-1.0) = 2.0 (f32).
        assert_eq!(fma(F32, 0x3FC0_0000, 0x4000_0000, 0xBF80_0000), 0x4000_0000);

        // SINGLE ROUNDING is the point: a = 1.0000000001, a*a - 1 rounded ONCE
        // keeps the exact-product tail (hardware FMADD = 0x3deb7ce00005e728),
        // whereas the unfused round(round(a*a) - 1) drops it to 0x3deb7ce000000000.
        let a2 = 0x3FF0_0000_0006_DF38u64; // 1.0000000001_f64
        let neg_one = 0xBFF0_0000_0000_0000u64;
        let fused = fma(F64, a2, a2, neg_one);
        assert_eq!(
            fused, 0x3DEB_7CE0_0005_E728,
            "fused (single rounding) tail kept"
        );
        let unfused = fadd(F64, fmul(F64, a2, a2), neg_one);
        assert_eq!(
            unfused, 0x3DEB_7CE0_0000_0000,
            "unfused drops the product tail"
        );
        assert_ne!(
            fused, unfused,
            "single-rounding FMA must DIFFER from round-twice fmul+fadd"
        );

        // Specials matching the hardware FMADD instruction (probed via clang asm):
        // 0*Inf + finite -> default qNaN.
        assert_eq!(
            fma(F64, 0x0, 0x7FF0_0000_0000_0000, 0x4000_0000_0000_0000),
            0x7FF8_0000_0000_0000
        );
        // Inf*1 + (-Inf) -> default qNaN (Inf - Inf).
        assert_eq!(
            fma(
                F64,
                0x7FF0_0000_0000_0000,
                0x3FF0_0000_0000_0000,
                0xFFF0_0000_0000_0000
            ),
            0x7FF8_0000_0000_0000
        );
        // NaN positional priority (addend c first): sNaN(a) beats qNaN(c); result
        // = quieted a. sNaN(c) beats everything.
        assert_eq!(
            fma(
                F64,
                0x7FF0_0000_0000_0009,
                0x4008_0000_0000_0000,
                0x7FF8_0000_0000_0005
            ),
            0x7FF8_0000_0000_0009
        );
        assert_eq!(
            fma(
                F64,
                0x7FF8_0000_0000_0041,
                0x4000_0000_0000_0000,
                0x7FF0_0000_0000_0033
            ),
            0x7FF8_0000_0000_0033
        );
        // f64::MAX * 2 + f64::MIN stays finite MAX (overflow avoided by the exact
        // product then the huge negative addend) — a fused-only outcome.
        assert_eq!(
            fma(
                F64,
                0x7FEF_FFFF_FFFF_FFFF,
                0x4000_0000_0000_0000,
                0xFFEF_FFFF_FFFF_FFFF
            ),
            0x7FEF_FFFF_FFFF_FFFF
        );
    }
}
