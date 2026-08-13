// trust-cg-verify/aarch64_semantics.rs - AArch64 instruction semantics as SMT formulas
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Encodes AArch64 instruction semantics as bitvector SMT expressions.
// Each instruction maps to a pure function from input bitvectors to output
// bitvectors, modeling the instruction's effect on destination registers.
//
// Reference: ARM Architecture Reference Manual (DDI 0487), Section C6.
// Reference: designs/2026-04-13-verification-architecture.md

//! AArch64 instruction semantics encoded as [`SmtExpr`] bitvector formulas.
//!
//! Key principle: 32-bit operations (W registers) produce 32-bit results.
//! The zero-extension to 64-bit X registers is verified separately as a lemma.
//! When verifying a 32-bit lowering rule, we compare 32-bit trust_ir result with
//! 32-bit AArch64 result.

use crate::smt::SmtExpr;
use trust_cg_ir::cc::OperandSize;
use trust_cg_lower::isel::AArch64CC;

/// Encode `ADD Wd, Wn, Wm` or `ADD Xd, Xn, Xm` — register-register add.
///
/// Semantics: `Rd = Rn + Rm` (wrapping).
pub fn encode_add_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size; // Width is carried by the expressions themselves.
    rn.bvadd(rm)
}

/// Encode `SUB Wd, Wn, Wm` or `SUB Xd, Xn, Xm` — register-register subtract.
///
/// Semantics: `Rd = Rn - Rm` (wrapping).
pub fn encode_sub_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvsub(rm)
}

/// Encode `MUL Wd, Wn, Wm` or `MUL Xd, Xn, Xm` — register-register multiply.
///
/// On AArch64 this is actually `MADD Rd, Rn, Rm, XZR` (multiply-add with zero).
/// Semantics: `Rd = Rn * Rm` (wrapping, lower bits).
pub fn encode_mul_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvmul(rm)
}

/// Encode `MADD Wd, Wn, Wm, Wa` or `MADD Xd, Xn, Xm, Xa` -- multiply-add.
///
/// Semantics: `Rd = Ra + (Rn * Rm)` (wrapping, lower bits).
/// Reference: ARM DDI 0487, C6.2.163 MADD.
pub fn encode_madd_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr, ra: SmtExpr) -> SmtExpr {
    let _ = size;
    ra.bvadd(rn.bvmul(rm))
}

/// Encode `UMULL Xd, Wn, Wm` — unsigned 32x32->64 multiply-long.
///
/// UMULL is the alias of `UMADDL Xd, Wn, Wm, XZR` (Data-processing, 3 source;
/// U=1, o0=0, Ra=XZR — exactly the word the encoder emits, see
/// `trust-cg-codegen/src/aarch64/encode.rs`). Per ARM DDI 0487, C6.2.296
/// UMADDL: `Xd = Xa + UInt(Wn) * UInt(Wm)`, with `Xa = XZR = 0` here. The
/// operands are the FULL W registers (no truncation), zero-extended to 64
/// bits, so the 64-bit product is exact — UMULL has EXACTLY this one form
/// (sf=1 is hardwired; there is no W-destination or X-source variant).
///
/// Modeled faithfully as `0 + zero_extend(Wn, 32) * zero_extend(Wm, 32)`,
/// keeping the architectural XZR addend of the UMADDL alias. `rn`/`rm` must be
/// 32-bit expressions; the result is 64-bit. The `ZeroExtend`-node formulation
/// is STRUCTURALLY DISTINCT from the `Concat(0, x)` zext formulation the
/// lowering obligation uses on its trust_ir side (`is_genuinely_proven`, not
/// X==X), and a sign-extending machine side (the SMULL confusion) REFUTES.
pub fn encode_umull_rr(rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    debug_assert_eq!(rn.bv_width(), 32);
    debug_assert_eq!(rm.bv_width(), 32);
    let xzr = SmtExpr::bv_const(0, 64);
    xzr.bvadd(rn.zero_ext(32).bvmul(rm.zero_ext(32)))
}

/// Encode `SDIV Wd, Wn, Wm` or `SDIV Xd, Xn, Xm` — signed divide.
///
/// Semantics (the HARDWARE TRUTH, not the SMT-LIB default): AArch64 `SDIV` is
/// a **total** function. Per ARM DDI 0487, C6.2.223 SDIV:
///   * `Rm != 0`: `Rd = Rn /s Rm`, truncated toward zero.
///   * `Rm == 0`: `Rd = 0` (division by zero produces zero in silicon — there
///     is NO trap, unlike x86 `IDIV`).
///   * `Rn == INT_MIN && Rm == -1`: `Rd = INT_MIN` (signed overflow wraps; the
///     mathematically-unrepresentable `|INT_MIN|` is delivered as `INT_MIN`).
///
/// We model this as `ite(Rm == 0, 0, bvsdiv(Rn, Rm))`. The bare SMT `bvsdiv`
/// already matches the hardware on the `INT_MIN / -1` overflow edge (SMT-LIB
/// `bvsdiv` of `INT_MIN`/`-1` = `INT_MIN`), so the only correction the `ite`
/// applies is the divide-by-zero case: SMT-LIB `bvsdiv(x, 0)` is `#b111…1`
/// (all-ones), whereas the silicon delivers `0`. Wrapping in the `ite` makes
/// this encoder the FAITHFUL, TOTAL model that x86 `IDIV` (a `#DE` trap) is not.
///
/// This total form REFINES the previous `Rm != 0`-preconditioned encoding:
/// under any obligation that already assumes `Rm != 0`, the `ite` collapses to
/// `bvsdiv(Rn, Rm)`, so every existing div lowering proof still discharges. The
/// total form additionally lets the if-conversion pass prove that
/// `select(Rm != 0, Rn/Rm, 0)` collapses to this single unguarded instruction.
///
/// For proofs whose observable domain is already `Rm != 0` and where the total
/// `ite` would only tax the solver (the `Srem`/`Urem` `MSUB` reconstructions),
/// use [`encode_sdiv_rr_nonzero`] / [`encode_udiv_rr_nonzero`] — the bare form
/// this `ite` collapses to under that precondition.
pub fn encode_sdiv_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size; // Width is carried by the expressions themselves.
    let width = rm.bv_width();
    let zero = SmtExpr::bv_const(0, width);
    let rm_is_zero = rm.clone().eq_expr(zero.clone());
    SmtExpr::ite(rm_is_zero, zero, rn.bvsdiv(rm))
}

/// Encode `UDIV Wd, Wn, Wm` or `UDIV Xd, Xn, Xm` — unsigned divide.
///
/// Semantics (the HARDWARE TRUTH): AArch64 `UDIV` is a **total** function. Per
/// ARM DDI 0487, C6.2.289 UDIV:
///   * `Rm != 0`: `Rd = Rn /u Rm`, truncated toward zero.
///   * `Rm == 0`: `Rd = 0` (division by zero produces zero in silicon — no trap).
///
/// We model this as `ite(Rm == 0, 0, bvudiv(Rn, Rm))`. The `ite` corrects the
/// SMT-LIB default, where `bvudiv(x, 0)` is `#b111…1` (all-ones); the silicon
/// delivers `0`. This total form REFINES the previous `Rm != 0`-preconditioned
/// encoding (the `ite` collapses to `bvudiv` whenever `Rm != 0`), so every
/// existing proof still discharges.
pub fn encode_udiv_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size; // Width is carried by the expressions themselves.
    let width = rm.bv_width();
    let zero = SmtExpr::bv_const(0, width);
    let rm_is_zero = rm.clone().eq_expr(zero.clone());
    SmtExpr::ite(rm_is_zero, zero, rn.bvudiv(rm))
}

/// Divisor-nonzero specialization of [`encode_sdiv_rr`]: the bare `bvsdiv(rn, rm)`.
///
/// On the domain `rm != 0`, the total [`encode_sdiv_rr`] `ite(rm == 0, 0,
/// bvsdiv(rn, rm))` collapses to EXACTLY this bare form. Use this ONLY inside
/// obligations that ALREADY assert `rm != 0` — e.g. the `Srem` = `SDIV; MSUB`
/// reconstruction, whose correctness is itself a divisor-nonzero claim.
///
/// Verifying against this bare representative is LOGICALLY IDENTICAL to
/// verifying against the total encoder under that precondition (the div's
/// zero-divisor value is not observable there — a solver could derive either
/// obligation from the other), so it does NOT weaken the obligation. It exists
/// purely to keep the SMT formula on the solver's fast path: the total `ite`
/// roughly 10×'s ay's wall time on the (already hard) 16-bit `MSUB`
/// reconstruction — pushing `Srem_I16` past 150 s — whereas the bare form
/// discharges in well under a second.
pub fn encode_sdiv_rr_nonzero(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvsdiv(rm)
}

/// Divisor-nonzero specialization of [`encode_udiv_rr`]: the bare `bvudiv(rn, rm)`.
///
/// See [`encode_sdiv_rr_nonzero`] for the full rationale. Use ONLY where an
/// `rm != 0` precondition is asserted (the `Urem` = `UDIV; MSUB` reconstruction).
pub fn encode_udiv_rr_nonzero(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvudiv(rm)
}

/// Encode `NEG Wd, Wn` or `NEG Xd, Xn` — negate.
///
/// On AArch64, `NEG Rd, Rn` is an alias for `SUB Rd, XZR/WZR, Rn`.
/// Semantics: `Rd = 0 - Rn` (two's complement negation).
pub fn encode_neg(size: OperandSize, rn: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvneg()
}

/// Encode `MSUB Wd, Wn, Wm, Wa` or `MSUB Xd, Xn, Xm, Xa` -- multiply-subtract.
///
/// Semantics: `Rd = Ra - (Rn * Rm)` (wrapping, lower bits).
/// Reference: ARM DDI 0487, C6.2.183 MSUB.
///
/// Used by `Urem`/`Srem` lowering: `rem = a - (a / b) * b`.
pub fn encode_msub_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr, ra: SmtExpr) -> SmtExpr {
    let _ = size;
    ra.bvsub(rn.bvmul(rm))
}

/// Encode `MOV Wd, Wn` or `MOV Xd, Xn` -- register-register move.
///
/// On AArch64, `MOV` is an alias for `ORR Rd, XZR/WZR, Rn` for GPRs.
/// Semantics: `Rd = Rn` (identity).
///
/// Used by `Bitcast` lowering between same-width GPR types.
pub fn encode_mov_rr(size: OperandSize, rn: SmtExpr) -> SmtExpr {
    let _ = size;
    rn
}

/// Encode `FMOV Sd, Sn` / `FMOV Dd, Dn` / `FMOV Dd, Xn` / `FMOV Xd, Dn` --
/// floating-point (or GPR<->FPR) register move.
///
/// Semantics: `Fd = Fn` / `Xd = Dn` -- pure bit-level copy with no rounding,
/// no NaN sanitization, and no width change. Used by `Bitcast` lowering
/// between integer and FP registers of the same width (e.g. `i32<->f32`,
/// `i64<->f64`).
/// Reference: ARM DDI 0487, C7.2.140 FMOV (register), C7.2.141 FMOV (general).
pub fn encode_fmov(rn: SmtExpr) -> SmtExpr {
    rn
}

/// Encode `UBFM Wd, Wn, #immr, #imms` -- unsigned bitfield move.
///
/// This helper covers the extract sub-case (`imms >= immr`), which is how
/// trust_ir `ExtractBits { lsb, width }` lowers. With `immr = lsb` and
/// `imms = lsb + width - 1`:
///
///   Wd = zero_extend((Wn >> lsb) & mask(width))
///
/// The helper takes the bitvector width `bv_width` (8 for i8 proofs) and
/// assumes the input is masked to that width. At 8 bits, the result is
/// simply `(rn lsr lsb) & mask(width)` -- zero-extension is a no-op within
/// the 8-bit domain. Requires `lsb + width <= bv_width` and `width >= 1`.
///
/// Reference: ARM DDI 0487, C6.2.335 UBFM (and alias C6.2.334 UBFX).
pub fn encode_ubfm_extract(rn: SmtExpr, lsb: u32, width: u32, bv_width: u32) -> SmtExpr {
    debug_assert!(width >= 1, "encode_ubfm_extract: width must be >= 1");
    debug_assert!(
        lsb + width <= bv_width,
        "encode_ubfm_extract: lsb + width must fit in bv_width"
    );
    debug_assert_eq!(
        rn.bv_width(),
        bv_width,
        "encode_ubfm_extract: operand width must match bv_width"
    );

    let shifted = rn.bvlshr(SmtExpr::bv_const(lsb as u64, bv_width));
    let mask = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), bv_width);
    shifted.bvand(mask)
}

/// Encode `SBFM Wd, Wn, #immr, #imms` -- signed bitfield move.
///
/// This helper covers the extract sub-case (`imms >= immr`), which is how
/// trust_ir `SextractBits { lsb, width }` lowers. With `immr = lsb` and
/// `imms = lsb + width - 1`:
///
///   Wd = sign_extend((Wn >> lsb) & mask(width), from bit (width-1))
///
/// In an 8-bit bitvector domain, we realize this as:
///
///   1. Extract the `width`-bit slice `Wn[lsb+width-1 : lsb]`.
///   2. Sign-extend that slice back up to `bv_width` bits (replicating
///      bit `width-1` of the slice to fill the upper bits).
///
/// SMT `(extract)` + `(sign_extend)` expresses this directly.
/// Requires `lsb + width <= bv_width` and `width >= 1`.
///
/// Reference: ARM DDI 0487, C6.2.266 SBFM (and alias C6.2.264 SBFX).
pub fn encode_sbfm_extract(rn: SmtExpr, lsb: u32, width: u32, bv_width: u32) -> SmtExpr {
    debug_assert!(width >= 1, "encode_sbfm_extract: width must be >= 1");
    debug_assert!(
        lsb + width <= bv_width,
        "encode_sbfm_extract: lsb + width must fit in bv_width"
    );
    debug_assert_eq!(
        rn.bv_width(),
        bv_width,
        "encode_sbfm_extract: operand width must match bv_width"
    );

    let high = lsb + width - 1;
    let slice = rn.extract(high, lsb);
    if width == bv_width {
        // No extension needed -- slice already has the full width.
        slice
    } else {
        slice.sign_ext(bv_width - width)
    }
}

/// Encode `SXTB`/`SXTH`/`SXTW` -- signed integer extension (SBFM extract alias).
///
/// `SXTB Wd, Wn` / `SXTH Wd, Wn` / `SXTW Xd, Wn` sign-extend the low `from_bits`
/// bits of the source to the destination width `to_bits`, replicating bit
/// `from_bits - 1`. This is the machine (AArch64) side of the trust_ir `Sextend`
/// lowering; the source side is
/// [`crate::trust_ir_semantics::encode_trust_ir_sextend`]. The encoder takes a
/// `from_bits`-wide `rn` (the source value occupies the low bits of its
/// register) and produces a `to_bits`-wide result.
///
/// Built from the REAL opcode so a wrong sign/zero choice (UXT-for-SXT) or a
/// wrong source width yields a structurally distinct result for some input
/// ⇒ REFUTE (task #63 Phase-2 reconstruction).
pub fn encode_sxt(from_bits: u32, to_bits: u32, rn: SmtExpr) -> SmtExpr {
    debug_assert!(
        to_bits > from_bits,
        "encode_sxt: to_bits must exceed from_bits"
    );
    debug_assert_eq!(
        rn.bv_width(),
        from_bits,
        "encode_sxt: rn width must equal from_bits"
    );
    rn.sign_ext(to_bits - from_bits)
}

/// Encode `UXTB`/`UXTH`/`UXTW` -- unsigned integer extension (UBFM extract /
/// AND-mask alias; UXTW is the W-write zero-extension).
///
/// `UXTB Wd, Wn` / `UXTH Wd, Wn` / `UXTW Xd, Wn` zero-extend the low `from_bits`
/// bits of the source to the destination width `to_bits`. This is the machine
/// (AArch64) side of the trust_ir `Uextend` lowering; the source side is
/// [`crate::trust_ir_semantics::encode_trust_ir_uextend`]. A wrong sign/zero
/// choice (SXT-for-UXT) yields a distinct result for a negative source
/// ⇒ REFUTE.
pub fn encode_uxt(from_bits: u32, to_bits: u32, rn: SmtExpr) -> SmtExpr {
    debug_assert!(
        to_bits > from_bits,
        "encode_uxt: to_bits must exceed from_bits"
    );
    debug_assert_eq!(
        rn.bv_width(),
        from_bits,
        "encode_uxt: rn width must equal from_bits"
    );
    rn.zero_ext(to_bits - from_bits)
}

/// Encode `BFM Wd, Wn, #immr, #imms` in its bitfield-insert form (BFI alias).
///
/// `BFI Wd, Wn, #lsb, #width` (`BFM Wd, Wn, #(reg_size - lsb) mod reg_size,
/// #(width - 1)`) copies the low `width` bits of `Wn` into `Wd[lsb+width-1:lsb]`,
/// leaving the other bits of `Wd` unchanged. This is how trust_ir
/// `InsertBits { lsb, width }` lowers -- `rd` holds the old value of the
/// destination (propagated from `args[0]` via a `COPY` emitted by ISel;
/// see `isel.rs::select_bitfield_insert`), and `rn` is the source of the
/// bits to insert (`args[1]`).
///
/// Semantics:
///
///   Wd = (Wd_old & ~(mask(width) << lsb)) | ((Wn & mask(width)) << lsb)
///
/// Requires `lsb + width <= bv_width` and `width >= 1`.
///
/// Reference: ARM DDI 0487, C6.2.46 BFM (and alias C6.2.45 BFI).
pub fn encode_bfm_insert(rd: SmtExpr, rn: SmtExpr, lsb: u32, width: u32, bv_width: u32) -> SmtExpr {
    debug_assert!(width >= 1, "encode_bfm_insert: width must be >= 1");
    debug_assert!(
        lsb + width <= bv_width,
        "encode_bfm_insert: lsb + width must fit in bv_width"
    );
    debug_assert_eq!(
        rd.bv_width(),
        bv_width,
        "encode_bfm_insert: Wd width must match bv_width"
    );
    debug_assert_eq!(
        rn.bv_width(),
        bv_width,
        "encode_bfm_insert: Wn width must match bv_width"
    );

    let width_mask = crate::smt::mask(u64::MAX, width);
    let shifted_mask = crate::smt::mask(width_mask << lsb, bv_width);
    let inv_mask = crate::smt::mask(!shifted_mask, bv_width);

    let preserved = rd.bvand(SmtExpr::bv_const(inv_mask, bv_width));
    let insert_slice = rn
        .bvand(SmtExpr::bv_const(width_mask, bv_width))
        .bvshl(SmtExpr::bv_const(lsb as u64, bv_width));

    preserved.bvor(insert_slice)
}

// ---------------------------------------------------------------------------
// Floating-point instruction semantics
// ---------------------------------------------------------------------------

/// Floating-point precision selector.
///
/// Maps to AArch64 S (single) and D (double) register sizes for FP operations.
/// Reference: ARM DDI 0487, Section C7 (SIMD and Floating-Point Instructions).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FPSize {
    /// Single-precision (32-bit, S registers). IEEE 754 binary32.
    Single,
    /// Double-precision (64-bit, D registers). IEEE 754 binary64.
    Double,
}

impl FPSize {
    /// Exponent bits for this FP size.
    pub fn eb(self) -> u32 {
        match self {
            FPSize::Single => 8,
            FPSize::Double => 11,
        }
    }

    /// Significand bits (including implicit bit) for this FP size.
    pub fn sb(self) -> u32 {
        match self {
            FPSize::Single => 24,
            FPSize::Double => 53,
        }
    }
}

/// Encode `FADD Sd, Sn, Sm` or `FADD Dd, Dn, Dm` -- floating-point add.
///
/// Semantics: `Fd = Fn + Fm` using RNE rounding mode (default FPCR.RMode).
/// Reference: ARM DDI 0487, C7.2.74 FADD (scalar).
pub fn encode_fadd_rr(_size: FPSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_add(RoundingMode::RNE, rn, rm)
}

/// Encode `FSUB Sd, Sn, Sm` or `FSUB Dd, Dn, Dm` -- floating-point subtract.
///
/// Semantics: `Fd = Fn - Fm` using RNE rounding mode.
/// Reference: ARM DDI 0487, C7.2.161 FSUB (scalar).
pub fn encode_fsub_rr(_size: FPSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_sub(RoundingMode::RNE, rn, rm)
}

/// Encode `FMUL Sd, Sn, Sm` or `FMUL Dd, Dn, Dm` -- floating-point multiply.
///
/// Semantics: `Fd = Fn * Fm` using RNE rounding mode.
/// Reference: ARM DDI 0487, C7.2.128 FMUL (scalar).
pub fn encode_fmul_rr(_size: FPSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_mul(RoundingMode::RNE, rn, rm)
}

/// Encode `FMADD Sd, Sn, Sm, Sa` / `FMADD Dd, Dn, Dm, Da` -- scalar FUSED
/// multiply-add: `Fd = Fa + Fn*Fm` with a SINGLE rounding of the exact
/// product-plus-addend (`fp.fma`), NOT `round(round(Fn*Fm) + Fa)` (two
/// roundings). This is the whole point of FMADD; a round-twice model differs
/// in the last ULP on a dense set of inputs and REFUTES.
///
/// `fp.fma(rm, a, b, c) = a*b + c`, so FMADD is `fp_fma(rn, rm, ra)`.
/// Reference: ARM DDI 0487, C7.2.116 FMADD (scalar).
pub fn encode_fmadd_rr(_size: FPSize, rn: SmtExpr, rm: SmtExpr, ra: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_fma(RoundingMode::RNE, rn, rm, ra)
}

/// Encode `FNEG Sd, Sn` or `FNEG Dd, Dn` -- floating-point negate.
///
/// Semantics: `Fd = -Fn` (bitwise sign flip, no rounding needed).
/// Reference: ARM DDI 0487, C7.2.132 FNEG (scalar).
pub fn encode_fneg(_size: FPSize, rn: SmtExpr) -> SmtExpr {
    rn.fp_neg()
}

/// Encode `FABS Sd, Sn` or `FABS Dd, Dn` -- floating-point absolute value.
///
/// Semantics: `Fd = |Fn|` (clear sign bit, no rounding needed).
/// Reference: ARM DDI 0487, C7.2.73 FABS (scalar).
pub fn encode_fabs(_size: FPSize, rn: SmtExpr) -> SmtExpr {
    rn.fp_abs()
}

/// Encode `FSQRT Sd, Sn` or `FSQRT Dd, Dn` -- floating-point square root.
///
/// Semantics: `Fd = sqrt(Fn)` with default RNE rounding mode.
/// Reference: ARM DDI 0487, C7.2.160 FSQRT (scalar).
pub fn encode_fsqrt(_size: FPSize, rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_sqrt(RoundingMode::RNE, rn)
}

/// Encode `FRINTM Sd, Sn` / `FRINTM Dd, Dn` -- round to integral toward -inf.
///
/// Semantics: `Fd = roundToIntegral(RTN, Fn)` (floor). Reference: ARM DDI 0487,
/// C7.2.156 FRINTM (scalar).
pub fn encode_frintm(_size: FPSize, rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_round_to_integral(RoundingMode::RTN, rn)
}

/// Encode `FRINTP Sd, Sn` / `FRINTP Dd, Dn` -- round to integral toward +inf.
///
/// Semantics: `Fd = roundToIntegral(RTP, Fn)` (ceil). Reference: ARM DDI 0487,
/// C7.2.159 FRINTP (scalar).
pub fn encode_frintp(_size: FPSize, rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_round_to_integral(RoundingMode::RTP, rn)
}

/// Encode `FRINTZ Sd, Sn` / `FRINTZ Dd, Dn` -- round to integral toward zero.
///
/// Semantics: `Fd = roundToIntegral(RTZ, Fn)` (trunc). Reference: ARM DDI 0487,
/// C7.2.162 FRINTZ (scalar).
pub fn encode_frintz(_size: FPSize, rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_round_to_integral(RoundingMode::RTZ, rn)
}

/// Encode `FDIV Sd, Sn, Sm` or `FDIV Dd, Dn, Dm` -- floating-point divide.
///
/// Semantics: `Fd = Fn / Fm` using RNE rounding mode.
/// Reference: ARM DDI 0487, C7.2.77 FDIV (scalar).
pub fn encode_fdiv_rr(_size: FPSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_div(RoundingMode::RNE, rn, rm)
}

/// Encode `FMINNM Sd, Sn, Sm` / `FMINNM Dd, Dn, Dm` — IEEE minNum scalar FP min
/// (Rust `f{32,64}::min`): lone NaN -> the number, else the smaller. Reference:
/// ARM DDI 0487, C7.2.137 FMINNM (scalar).
pub fn encode_fminnm_rr(_size: FPSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    SmtExpr::fp_min_ieee(rn, rm)
}

/// Encode `FMAXNM Sd, Sn, Sm` / `FMAXNM Dd, Dn, Dm` — IEEE maxNum scalar FP max
/// (Rust `f{32,64}::max`). Reference: ARM DDI 0487, C7.2.131 FMAXNM (scalar).
pub fn encode_fmaxnm_rr(_size: FPSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    SmtExpr::fp_max_ieee(rn, rm)
}

/// Encode `FCVTZS Wd, Sn` / `FCVTZS Xd, Dn` — FP→signed-int (round toward zero).
///
/// Semantics: `Rd = (signed int_width) Fn`, truncating toward zero.
/// Reference: ARM DDI 0487, C7.2.69 FCVTZS (scalar, integer).
pub fn encode_fcvtzs(int_width: u32, rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_to_sbv(RoundingMode::RTZ, rn, int_width)
}

/// Encode `FCVTZU Wd, Sn` / `FCVTZU Xd, Dn` — FP→unsigned-int (round toward zero).
///
/// Semantics: `Rd = (unsigned int_width) Fn`, truncating toward zero.
/// Reference: ARM DDI 0487, C7.2.72 FCVTZU (scalar, integer).
pub fn encode_fcvtzu(int_width: u32, rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_to_ubv(RoundingMode::RTZ, rn, int_width)
}

/// Encode `SCVTF Sd, Wn` / `SCVTF Dd, Xn` — signed-int→FP (round-to-nearest-even).
///
/// Semantics: `Fd = (fp) (signed)Rn`. The `BvToFP` evaluator interprets the
/// bitvector as SIGNED (sign-extends), matching SCVTF.
/// Reference: ARM DDI 0487, C7.2.194 SCVTF (scalar, integer).
pub fn encode_scvtf(eb: u32, sb: u32, rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::bv_to_fp(RoundingMode::RNE, rn, eb, sb)
}

/// Encode `UCVTF Sd, Wn` / `UCVTF Dd, Xn` — unsigned-int→FP (round-to-nearest-even).
///
/// Semantics: `Fd = (fp) (unsigned)Rn`. Because `BvToFP` sign-extends, the
/// operand must already be a sign-bit-clear (zero-extended) value for the
/// UNSIGNED interpretation to be correct; the reconstruction path zero-extends
/// the source before calling this so both sides share the identical operand.
/// Reference: ARM DDI 0487, C7.2.326 UCVTF (scalar, integer).
pub fn encode_ucvtf(eb: u32, sb: u32, rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::bv_to_fp(RoundingMode::RNE, rn, eb, sb)
}

/// Encode `FCVT Dd, Sn` — single→double precision CONVERT (widen / promote).
///
/// Semantics: `Dd = (binary64) Sn`. Every finite binary32 is exactly
/// representable in binary64, so the conversion is exact and the rounding mode is
/// immaterial (RNE used for uniformity). The destination format `(eb=11, sb=53)`
/// is what makes this the WIDEN direction.
/// Reference: ARM DDI 0487, C7.2.67 FCVT (scalar, floating-point precision).
pub fn encode_fcvt_sd(rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_to_fp(RoundingMode::RNE, rn, 11, 53)
}

/// Encode `FCVT Sd, Dn` — double→single precision CONVERT (narrow / demote).
///
/// Semantics: `Sd = (binary32) Dn`, ROUNDING-aware (round-to-nearest-even, the
/// default FPCR.RMode). Many binary64 values are not exactly representable in
/// binary32, so this genuinely rounds. The destination format `(eb=8, sb=24)` is
/// what makes this the NARROW direction.
/// Reference: ARM DDI 0487, C7.2.67 FCVT (scalar, floating-point precision).
pub fn encode_fcvt_ds(rn: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_to_fp(RoundingMode::RNE, rn, 8, 24)
}

/// AArch64 NZCV flags produced by `FCMP Sn, Sm` / `FCMP Dn, Dm` (ARM DDI 0487,
/// C7.2.76; the FPCompare result table in J1.3). The four flags are returned as
/// the [`crate::nzcv::NzcvFlags`] Bool quadruple, modeling the hardware exactly:
///
/// | relation (ordered) | N | Z | C | V |
/// |--------------------|---|---|---|---|
/// | `a < b`            | 1 | 0 | 0 | 0 |
/// | `a == b`           | 0 | 1 | 1 | 0 |
/// | `a > b`            | 0 | 0 | 1 | 0 |
/// | unordered (NaN)    | 0 | 0 | 1 | 1 |
///
/// Encoded as `N = a<b`, `Z = a==b`, `C = ¬(a<b)`, `V = isNaN(a)∨isNaN(b)`. The
/// IEEE `fp.lt`/`fp.eq` predicates are FALSE for an unordered pair, so this
/// reproduces every row of the table (e.g. unordered ⇒ `lt`/`eq` false ⇒
/// `N=0,Z=0,C=¬false=1`, and `V=1`).
fn encode_fcmp_flags(rn: SmtExpr, rm: SmtExpr) -> crate::nzcv::NzcvFlags {
    let lt = rn.clone().fp_lt(rm.clone());
    let eq = rn.clone().fp_eq(rm.clone());
    let unordered = rn.fp_is_nan().or_expr(rm.fp_is_nan());
    crate::nzcv::NzcvFlags {
        n: lt.clone(),
        z: eq,
        c: lt.not_expr(),
        v: unordered,
    }
}

/// Encode the AArch64 `FCMP` + `CSET cc` sequence that materializes a float
/// comparison: `FCMP` sets NZCV (see [`encode_fcmp_flags`]) and `CSET Wd, cc`
/// reads them via the architectural condition-code table
/// ([`crate::nzcv::eval_condition`]). Returns a 1-bit bitvector (`bv1(1)`/
/// `bv1(0)`), the trust_ir `B1` shape.
///
/// FAITHFUL / NON-DEGENERATE: the machine result is `eval_condition(cc, NZCV)` —
/// the condition code `cc` is the ONLY operand-of-interest, and a WRONG cc
/// reads a different flag combination, so this DIVERGES from the intended
/// comparison (the adversarial cond-code check refutes). Contrast the retracted
/// model that re-stated the source `fp.lt`/`fp.eq` directly per FloatCC (an
/// X==X that no wrong cond-code could refute).
pub fn encode_fcmp_cset(_size: FPSize, rn: SmtExpr, rm: SmtExpr, cc: AArch64CC) -> SmtExpr {
    let flags = encode_fcmp_flags(rn, rm);
    crate::nzcv::encode_cset(cc, &flags)
}

/// Encode `FCMP Sn, Sm` / `FCMP Dn, Dm` + condition-code extraction for a
/// trust_ir `FloatCC`, modeling the EXACT instruction sequence the AArch64 ISel
/// emits (`select_fcmp`): `FCMP` followed by `CSET` with the cond code chosen by
/// [`AArch64CC::from_floatcc`]. Returns a 1-bit bitvector.
///
/// The cond code is taken from `from_floatcc`, so this obligation VALIDATES that
/// mapping against the hardware NZCV semantics: a wrong `from_floatcc` entry
/// reads the wrong flags and refutes. `UnorderedEqual` is the one ISel form that
/// is NOT a single cond code — `select_fcmp` materializes it as `(CSET EQ) OR
/// (CSET VS)` (ordered-equal OR unordered) — so it is modeled exactly that way.
///
/// Reference: ARM DDI 0487, C7.2.76 FCMP (scalar); C1.2.4 condition codes.
pub fn encode_fcmp(
    size: FPSize,
    rn: SmtExpr,
    rm: SmtExpr,
    cond: &trust_cg_lower::instructions::FloatCC,
) -> SmtExpr {
    use trust_cg_lower::instructions::FloatCC;

    match cond {
        // `select_fcmp` lowers UnorderedEqual as two CSETs (EQ, VS) OR-ed, since
        // "ordered-equal OR unordered" is not a single AArch64 condition code.
        FloatCC::UnorderedEqual => {
            let flags = encode_fcmp_flags(rn, rm);
            let eq_bit = crate::nzcv::encode_cset(AArch64CC::EQ, &flags);
            let vs_bit = crate::nzcv::encode_cset(AArch64CC::VS, &flags);
            eq_bit.bvor(vs_bit)
        }
        other => encode_fcmp_cset(size, rn, rm, AArch64CC::from_floatcc(*other)),
    }
}

/// Encode `FCSEL Rd, Rn, Rm, cond` — scalar FP conditional select — as a
/// BIT-PRESERVING mux over the RAW register bit-vectors: given the architectural
/// NZCV `flags`, the result is `Rn` (bit-for-bit) when `cond` holds and `Rm`
/// otherwise (`ite(eval_condition(cc, flags), rn, rm)`).
///
/// `rn`/`rm` are the raw `width`-bit FPR contents — there is NO FP arithmetic and
/// NO canonicalization, so NaN payloads (including signaling NaNs), signed zeros
/// and denormals pass through EXACTLY (safe by construction). The condition is
/// modeled through the SAME [`crate::nzcv::eval_condition`] the hardware uses, so
/// a WRONG condition code reads a different flag combination and selects the
/// wrong operand — the non-vacuity the inverted-cond control exploits. Reference:
/// ARM DDI 0487, C7.2.75 FCSEL.
pub fn encode_fcsel(
    cc: AArch64CC,
    flags: &crate::nzcv::NzcvFlags,
    rn: SmtExpr,
    rm: SmtExpr,
) -> SmtExpr {
    SmtExpr::ite(crate::nzcv::eval_condition(cc, flags), rn, rm)
}

/// Compute the 8-bit AArch64 scalar `FMOV`-immediate field for an ENCODABLE
/// floating-point value, or `None` when the value is not representable.
///
/// This MIRRORS the codegen encoder
/// (`trust-cg-codegen/src/aarch64/encode.rs::encode_fmov_imm8`): the value must
/// have a zero low-48 mantissa and a biased-f64 exponent in `[1020, 1027]`
/// (unbiased `[-3, +4]`). The field packs `sign:NOT(e2):e1:e0:top4mantissa`.
/// (The ISel only emits `FmovImm` when this returns `Some`; otherwise it
/// materializes the IEEE bits in a GPR and `FMOV`s them across — see
/// `select_fconst`.)
pub fn fmov_imm8_field(value: f64) -> Option<u8> {
    let bits = value.to_bits();
    let sign = ((bits >> 63) & 1) as u8;
    let exp = ((bits >> 52) & 0x7FF) as i32;
    let frac = bits & 0x000F_FFFF_FFFF_FFFF;
    if frac & 0x0000_FFFF_FFFF_FFFF != 0 {
        return None;
    }
    if !(1020..=1027).contains(&exp) {
        return None;
    }
    let top4 = ((frac >> 48) & 0xF) as u8;
    let biased_3 = (exp - 1020) as u8; // 0..=7
    let not_b = ((biased_3 >> 2) ^ 1) & 1;
    Some((sign << 7) | (not_b << 6) | ((biased_3 & 0b11) << 4) | top4)
}

/// Encode the hardware DECODE of an AArch64 scalar `FMOV`-immediate field — the
/// ARM `VFPExpandImm(imm8, N)` algorithm (ARM DDI 0487, J1.3 / shared pseudocode
/// `VFPExpandImm`) — as a SYMBOLIC bitvector that ASSEMBLES the IEEE-754 bit
/// pattern from the 8 immediate bits. `width` is the destination format width
/// (32 for `FMOV Sd, #imm`, 64 for `FMOV Dd, #imm`).
///
/// With `imm8 = a:b:c:d:e:f:g:h`:
///   sign = a; exp = NOT(b) : Replicate(b, E-3) : c:d ; frac = e:f:g:h : Zeros.
///
/// This is the INDEPENDENT decode side of the [`fmov_imm8_field`] encode side:
/// the obligation `assemble(encode(v)) == bits(v)` (built in the function
/// verifier's `reconstruct_fmov_imm`) is a genuine ENCODING round-trip — the
/// assembly is a structural extract/shift/or tree, NOT a copy of the constant,
/// so a wrong field formula or wrong bit placement REFUTES (it is not the
/// degenerate `const == const`).
pub fn encode_fmov_imm_bits(field: u8, width: u32) -> SmtExpr {
    debug_assert!(
        width == 32 || width == 64,
        "FMOV-imm width must be 32 or 64"
    );
    // Format parameters: f32 = (E=8, F=23); f64 = (E=11, F=52).
    let (exp_w, frac_w) = if width == 64 {
        (11u32, 52u32)
    } else {
        (8u32, 23u32)
    };
    // Replicate(b, E-3): a run of (E-3) copies of bit b, value `b * (2^(E-3)-1)`.
    let brep_mask: u64 = (1u64 << (exp_w - 3)) - 1;

    let bv = |v: u64| SmtExpr::bv_const(v, width);
    let imm = bv(field as u64);
    let shr = |x: SmtExpr, n: u64| x.bvlshr(bv(n));
    let shl = |x: SmtExpr, n: u64| x.bvshl(bv(n));

    // Field bit extracts (each a width-bit value holding the small field).
    let sign = shr(imm.clone(), 7).bvand(bv(1)); // a
    let b = shr(imm.clone(), 6).bvand(bv(1)); // b
    let cd = shr(imm.clone(), 4).bvand(bv(0b11)); // c:d
    let efgh = imm.bvand(bv(0xF)); // e:f:g:h
    let not_b = b.clone().bvxor(bv(1)); // NOT(b)
    let brep = b.bvmul(bv(brep_mask)); // Replicate(b, E-3)

    // Place each field at its IEEE position. The exponent occupies bits
    // [frac_w .. frac_w+exp_w-1]: its MSB (NOT b) sits at the sign-1 bit, the
    // replicated run just below, then c:d at the bottom two exponent bits.
    shl(sign, (width - 1) as u64)
        .bvor(shl(not_b, (width - 2) as u64))
        .bvor(shl(brep, (frac_w + 2) as u64))
        .bvor(shl(cd, frac_w as u64))
        .bvor(shl(efgh, (frac_w - 4) as u64))
}

// ---------------------------------------------------------------------------
// Bitwise instruction semantics
// ---------------------------------------------------------------------------

/// Encode `AND Wd, Wn, Wm` or `AND Xd, Xn, Xm` — bitwise AND.
///
/// Semantics: `Rd = Rn & Rm`.
/// Reference: ARM DDI 0487, C6.2.12 AND (shifted register).
pub fn encode_and_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvand(rm)
}

/// Encode `ORR Wd, Wn, Wm` or `ORR Xd, Xn, Xm` — bitwise inclusive OR.
///
/// Semantics: `Rd = Rn | Rm`.
/// Reference: ARM DDI 0487, C6.2.230 ORR (shifted register).
pub fn encode_orr_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvor(rm)
}

/// Encode `EOR Wd, Wn, Wm` or `EOR Xd, Xn, Xm` — bitwise exclusive OR.
///
/// Semantics: `Rd = Rn ^ Rm`.
/// Reference: ARM DDI 0487, C6.2.87 EOR (shifted register).
pub fn encode_eor_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvxor(rm)
}

/// Encode `MVN Wd, Wm` or `MVN Xd, Xm` — bitwise NOT (move NOT).
///
/// On AArch64, `MVN Rd, Rm` is an alias for `ORN Rd, XZR/WZR, Rm`.
/// Semantics: `Rd = ~Rm` (bitwise complement).
/// Reference: ARM DDI 0487, C6.2.192 MVN.
pub fn encode_mvn(size: OperandSize, rn: SmtExpr) -> SmtExpr {
    let width = operand_size_bits(size);
    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
    rn.bvxor(all_ones)
}

/// Encode `BIC Wd, Wn, Wm` or `BIC Xd, Xn, Xm` — bitwise bit clear (AND-NOT).
///
/// Semantics: `Rd = Rn & ~Rm`.
/// Reference: ARM DDI 0487, C6.2.21 BIC (shifted register).
///
/// Used by `trust_ir::BandNot` lowering (`select_logic(..., AArch64LogicOp::Bic, ...)`
/// in `trust_cg_lower::isel`). The complement is taken at `rm`'s actual
/// bitvector width so the encoder composes correctly at sub-register widths
/// — I8/I16 proofs encode operands as 8/16-bit bitvectors even though the
/// machine instruction uses a 32-bit W register. The `size` parameter is
/// accepted for consistency with the rest of this file but ignored for SMT
/// encoding (width comes from the operand sort, matching `encode_and_rr` /
/// `encode_orr_rr`).
pub fn encode_bic_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    let width = rm.bv_width();
    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
    rn.bvand(rm.bvxor(all_ones))
}

/// Encode `ORN Wd, Wn, Wm` or `ORN Xd, Xn, Xm` — bitwise inclusive OR NOT.
///
/// Semantics: `Rd = Rn | ~Rm`.
/// Reference: ARM DDI 0487, C6.2.229 ORN (shifted register).
///
/// Used by `trust_ir::BorNot` lowering (`select_logic(..., AArch64LogicOp::Orn, ...)`
/// in `trust_cg_lower::isel`). Complements at `rm`'s actual bitvector width for
/// the same sub-register reason noted on [`encode_bic_rr`].
pub fn encode_orn_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    let width = rm.bv_width();
    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
    rn.bvor(rm.bvxor(all_ones))
}

/// AArch64 register-shift kind — the 2-bit `shift` field of the logical
/// shifted-register instruction form (`AArch64InstrFormats.td` `BaseLogicalSReg`):
/// `LSL=0b00, LSR=0b01, ASR=0b10, ROR=0b11`. LSL/LSR/ROR are emitted by the
/// shifted-EOR fusion lanes; ASR remains available for wrong-kind controls.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegShiftKind {
    /// Logical shift left (`shift=0b00`): `rm << amount`.
    Lsl,
    /// Logical shift right (`shift=0b01`): `rm >>u amount` (zero-fill).
    Lsr,
    /// Arithmetic shift right (`shift=0b10`): `rm >>s amount` (sign-fill).
    Asr,
    /// Rotate right (`shift=0b11`): `(rm >>u amount) | (rm << (width-amount))`.
    Ror,
}

/// Apply the register-shift `kind` by the constant `amount` to `rm`, modeling
/// the shifted-operand the AArch64 logical shifted-register form feeds into the
/// logical op. `amount` must be in `[0, width)`; for [`RegShiftKind::Ror`] the
/// rotate is expressed as `(rm >>u amount) | (rm << (width-amount))` (the
/// standard shift-composition — `amount == 0` is the identity).
///
/// `width` is the register width in bits (32 for W, 64 for X). The shift amounts
/// are `width`-bit constants so the in-house SMT shift evaluator composes them
/// exactly in the in-range region (no clamp ambiguity — `amount` and
/// `width-amount` are both `< width` for `amount` in `[1, width)`).
pub fn shifted_reg_operand(kind: RegShiftKind, rm: SmtExpr, amount: u32, width: u32) -> SmtExpr {
    let amt = SmtExpr::bv_const(u64::from(amount), width);
    match kind {
        RegShiftKind::Lsl => rm.bvshl(amt),
        RegShiftKind::Lsr => rm.bvlshr(amt),
        RegShiftKind::Asr => rm.bvashr(amt),
        RegShiftKind::Ror => {
            if amount == 0 {
                return rm;
            }
            let lo = rm.clone().bvlshr(amt);
            let hi = rm.bvshl(SmtExpr::bv_const(u64::from(width - amount), width));
            lo.bvor(hi)
        }
    }
}

/// Encode `EOR Rd, Rn, Rm, <kind> #amount` — bitwise exclusive-OR with a
/// register-shifted second source. Semantics: `Rd = Rn ^ shift(Rm, kind, amount)`.
/// Reference: ARM DDI 0487, C6.2.87 EOR (shifted register).
///
/// The un-shifted operand is `rn` (ARM `Rn`); the shifted operand is `rm` (ARM
/// `Rm, <kind> #amount`). Used both as the MACHINE side of the EOR-ROR fusion
/// obligation ([`RegShiftKind::Ror`]) and, with the OTHER shift kinds / a
/// perturbed amount / swapped operands, as the WRONG-encoding negative controls.
pub fn encode_eor_shifted_reg(
    size: OperandSize,
    rn: SmtExpr,
    rm: SmtExpr,
    kind: RegShiftKind,
    amount: u32,
) -> SmtExpr {
    let width = operand_size_bits(size);
    rn.bvxor(shifted_reg_operand(kind, rm, amount, width))
}

/// Encode the FRONTEND `x ^ ROTL(v, r)` idiom the rotate-fusion peephole
/// COLLAPSES: `Rn ^ ((Rm << r) | (Rm >>u (width - r)))`. This is the SOURCE side
/// of the EOR-ROR obligation — the ROTL(v, r) the C-level ARX round writes,
/// which equals `rotr(v, width - r)`, i.e. the ROR by `k = width - r` the fused
/// `EOR ..., ROR #k` performs. Written with the two shifted halves in the
/// OPPOSITE OR order from [`encode_eor_shifted_reg`]'s ROR so the two sides are
/// STRUCTURALLY DISTINCT (non-degenerate: `is_genuinely_proven`) yet provably
/// equal. `r` in `[1, width)`.
pub fn encode_eor_rotl_source(size: OperandSize, rn: SmtExpr, rm: SmtExpr, r: u32) -> SmtExpr {
    let width = operand_size_bits(size);
    let hi = rm.clone().bvshl(SmtExpr::bv_const(u64::from(r), width));
    let lo = rm.bvlshr(SmtExpr::bv_const(u64::from(width - r), width));
    rn.bvxor(hi.bvor(lo))
}

/// Encode `ADD Rd, Rn, Rm, <kind> #amount` — add with a register-shifted second
/// source. Semantics: `Rd = Rn + shift(Rm, kind, amount)` (wrapping).
/// Reference: ARM DDI 0487, C6.2.4 ADD (shifted register).
///
/// The un-shifted base is `rn` (ARM `Rn`); the shifted operand is `rm` (ARM
/// `Rm, <kind> #amount`). Used as the MACHINE side of the shift-add fusion
/// obligation ([`RegShiftKind::Lsl`]); with a perturbed amount / swapped
/// operands / the wrong op it is the negative controls. ADD commutes in value,
/// but the shift binds to `rm` only.
pub fn encode_add_shifted_reg(
    size: OperandSize,
    rn: SmtExpr,
    rm: SmtExpr,
    kind: RegShiftKind,
    amount: u32,
) -> SmtExpr {
    let width = operand_size_bits(size);
    rn.bvadd(shifted_reg_operand(kind, rm, amount, width))
}

/// Encode `SUB Rd, Rn, Rm, <kind> #amount` — subtract a register-shifted second
/// source. Semantics: `Rd = Rn - shift(Rm, kind, amount)` (wrapping).
/// Reference: ARM DDI 0487, C6.2.313 SUB (shifted register).
///
/// The un-shifted minuend is `rn` (ARM `Rn`); the shifted subtrahend is `rm`
/// (ARM `Rm, <kind> #amount`). SUB is NON-COMMUTATIVE — the shift can ONLY sit
/// on the subtrahend `rm`, which is exactly the load-bearing asymmetry the
/// operand-swap negative control exercises.
pub fn encode_sub_shifted_reg(
    size: OperandSize,
    rn: SmtExpr,
    rm: SmtExpr,
    kind: RegShiftKind,
    amount: u32,
) -> SmtExpr {
    let width = operand_size_bits(size);
    rn.bvsub(shifted_reg_operand(kind, rm, amount, width))
}

// ---------------------------------------------------------------------------
// Shift instruction semantics
// ---------------------------------------------------------------------------

/// Encode `LSL Wd, Wn, Wm` or `LSL Xd, Xn, Xm` — logical shift left.
///
/// On AArch64, `LSL Rd, Rn, Rm` is an alias for `LSLV Rd, Rn, Rm`.
/// Semantics: `Rd = Rn << (Rm mod width)`.
/// Reference: ARM DDI 0487, C6.2.171 LSL (register).
pub fn encode_lsl_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvshl(rm)
}

/// Encode `LSR Wd, Wn, Wm` or `LSR Xd, Xn, Xm` — logical shift right.
///
/// On AArch64, `LSR Rd, Rn, Rm` is an alias for `LSRV Rd, Rn, Rm`.
/// Semantics: `Rd = Rn >> (Rm mod width)` (unsigned / zero-fill).
/// Reference: ARM DDI 0487, C6.2.173 LSR (register).
pub fn encode_lsr_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvlshr(rm)
}

/// Encode `ASR Wd, Wn, Wm` or `ASR Xd, Xn, Xm` — arithmetic shift right.
///
/// On AArch64, `ASR Rd, Rn, Rm` is an alias for `ASRV Rd, Rn, Rm`.
/// Semantics: `Rd = Rn >>_s (Rm mod width)` (sign-extending).
/// Reference: ARM DDI 0487, C6.2.16 ASR (register).
pub fn encode_asr_rr(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    rn.bvashr(rm)
}

// ---------------------------------------------------------------------------
// Hardware-faithful (amount-masked) shift semantics — task #57
// ---------------------------------------------------------------------------
//
// The plain `encode_lsl_rr` / `encode_lsr_rr` / `encode_asr_rr` above use the
// in-house SMT `bvshl`/`bvlshr`/`bvashr`, whose evaluator CLAMPS the result to 0
// (or to the sign fill, for ASR) when the shift amount is >= the bitvector
// width. The AArch64 LSLV/LSRV/ASRV instructions instead MASK the amount to the
// register width (`amount & (width - 1)`), so a shift by exactly `width` is a
// shift by 0 (identity), NOT a clamp to 0. THAT is the #57 divergence.
//
// These encoders model the AArch64 instruction FAITHFULLY: they mask the amount
// before shifting, so they match the real hardware everywhere — including the
// out-of-range region where the plain SMT encoder diverges. The reconstruction
// path (`function_verifier::reconstruct_shift_obligation`) pairs the FAITHFUL
// machine side here with the PLAIN-`bvshl` trust_ir source side under a
// LOAD-BEARING `amount < width` precondition: in range the mask is the identity
// and the two sides agree; OUT of range the faithful (masked) machine side and
// the clamp-to-0 source side DIVERGE, so the precondition is genuinely required
// for the obligation to discharge `Valid` (strip it and the obligation REFUTES
// at amount == width). That resolves #57's "cosmetic precondition" reopening.

/// The hardware shift-amount mask `(width - 1)` as a `width`-bit constant.
///
/// AArch64 shift-by-register masks the amount with this value (mod 32 for W, mod
/// 64 for X); `width` is a power of two so `width - 1` is the low-bits mask. The
/// width is taken from the OPERAND sort (`rm.bv_width()`), not the `OperandSize`
/// parameter, so the encoder composes correctly at any bitvector width (mirrors
/// `encode_bic_rr`/`encode_orn_rr`).
fn shift_amount_mask(width: u32) -> SmtExpr {
    SmtExpr::bv_const((width as u64).wrapping_sub(1), width)
}

/// Encode `LSLV Wd, Wn, Wm` / `LSLV Xd, Xn, Xm` with the FAITHFUL hardware
/// amount mask (`Rd = Rn << (Rm & (width - 1))`). See the module note above.
pub fn encode_lsl_rr_masked(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    let width = rm.bv_width();
    rn.bvshl(rm.bvand(shift_amount_mask(width)))
}

/// Encode `LSRV Wd, Wn, Wm` / `LSRV Xd, Xn, Xm` with the FAITHFUL hardware
/// amount mask (`Rd = Rn >>u (Rm & (width - 1))`). See the module note above.
pub fn encode_lsr_rr_masked(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    let width = rm.bv_width();
    rn.bvlshr(rm.bvand(shift_amount_mask(width)))
}

/// Encode `ASRV Wd, Wn, Wm` / `ASRV Xd, Xn, Xm` with the FAITHFUL hardware
/// amount mask (`Rd = Rn >>s (Rm & (width - 1))`). See the module note above.
pub fn encode_asr_rr_masked(size: OperandSize, rn: SmtExpr, rm: SmtExpr) -> SmtExpr {
    let _ = size;
    let width = rm.bv_width();
    rn.bvashr(rm.bvand(shift_amount_mask(width)))
}

/// Width in bits for an OperandSize.
pub fn operand_size_bits(size: OperandSize) -> u32 {
    match size {
        OperandSize::S32 => 32,
        OperandSize::S64 => 64,
    }
}

/// Map an OperandSize to the corresponding trust-cg-lower Type.
pub fn operand_size_to_type(size: OperandSize) -> trust_cg_lower::types::Type {
    match size {
        OperandSize::S32 => trust_cg_lower::types::Type::I32,
        OperandSize::S64 => trust_cg_lower::types::Type::I64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::EvalResult;
    use std::collections::HashMap;

    fn env(pairs: &[(&str, u64)]) -> HashMap<String, u64> {
        pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    fn sym32() -> (SmtExpr, SmtExpr) {
        (SmtExpr::var("a", 32), SmtExpr::var("b", 32))
    }

    #[test]
    fn test_add_rr_32() {
        let (a, b) = sym32();
        let expr = encode_add_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 100), ("b", 200)]));
        assert_eq!(result, EvalResult::Bv(300));
    }

    #[test]
    fn test_sub_rr_32() {
        let (a, b) = sym32();
        let expr = encode_sub_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 10), ("b", 3)]));
        assert_eq!(result, EvalResult::Bv(7));
    }

    #[test]
    fn test_mul_rr_32() {
        let (a, b) = sym32();
        let expr = encode_mul_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 6), ("b", 7)]));
        assert_eq!(result, EvalResult::Bv(42));
    }

    #[test]
    fn test_neg_32() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_neg(OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 1)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_neg_zero() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_neg(OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 0)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    // -----------------------------------------------------------------------
    // Floating-point instruction semantics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fadd_single() {
        let a = SmtExpr::fp32_const(1.5f32);
        let b = SmtExpr::fp32_const(2.5f32);
        let expr = encode_fadd_rr(FPSize::Single, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(4.0));
    }

    #[test]
    fn test_fadd_double() {
        let a = SmtExpr::fp64_const(100.0);
        let b = SmtExpr::fp64_const(200.0);
        let expr = encode_fadd_rr(FPSize::Double, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(300.0));
    }

    #[test]
    fn test_fsub_single() {
        let a = SmtExpr::fp32_const(10.0f32);
        let b = SmtExpr::fp32_const(3.5f32);
        let expr = encode_fsub_rr(FPSize::Single, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(6.5));
    }

    #[test]
    fn test_fsub_double() {
        let a = SmtExpr::fp64_const(100.0);
        let b = SmtExpr::fp64_const(42.0);
        let expr = encode_fsub_rr(FPSize::Double, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(58.0));
    }

    #[test]
    fn test_fmul_single() {
        let a = SmtExpr::fp32_const(3.0f32);
        let b = SmtExpr::fp32_const(7.0f32);
        let expr = encode_fmul_rr(FPSize::Single, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(21.0));
    }

    #[test]
    fn test_fmul_double() {
        let a = SmtExpr::fp64_const(6.0);
        let b = SmtExpr::fp64_const(7.0);
        let expr = encode_fmul_rr(FPSize::Double, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(42.0));
    }

    #[test]
    fn test_fneg_single() {
        let a = SmtExpr::fp32_const(42.0f32);
        let expr = encode_fneg(FPSize::Single, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(-42.0));
    }

    #[test]
    fn test_fneg_double() {
        let a = SmtExpr::fp64_const(std::f64::consts::PI);
        let expr = encode_fneg(FPSize::Double, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(-std::f64::consts::PI));
    }

    #[test]
    fn test_fneg_double_negative() {
        let a = SmtExpr::fp64_const(-100.0);
        let expr = encode_fneg(FPSize::Double, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(100.0));
    }

    #[test]
    fn test_fdiv_single() {
        let a = SmtExpr::fp32_const(10.0f32);
        let b = SmtExpr::fp32_const(4.0f32);
        let expr = encode_fdiv_rr(FPSize::Single, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(2.5));
    }

    #[test]
    fn test_fdiv_double() {
        let a = SmtExpr::fp64_const(10.0);
        let b = SmtExpr::fp64_const(4.0);
        let expr = encode_fdiv_rr(FPSize::Double, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(2.5));
    }

    #[test]
    fn test_fcmp_eq_true() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(1.0);
        let expr = encode_fcmp(FPSize::Double, a, b, &FloatCC::Equal);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_fcmp_eq_false() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_fcmp(FPSize::Double, a, b, &FloatCC::Equal);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_fcmp_lt_true() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_fcmp(FPSize::Double, a, b, &FloatCC::LessThan);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_fcmp_gt_true() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(3.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_fcmp(FPSize::Double, a, b, &FloatCC::GreaterThan);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_fcmp_ordered_no_nan() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_fcmp(FPSize::Double, a, b, &FloatCC::Ordered);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_fcmp_unordered_no_nan() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_fcmp(FPSize::Double, a, b, &FloatCC::Unordered);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_fp_size_parameters() {
        assert_eq!(FPSize::Single.eb(), 8);
        assert_eq!(FPSize::Single.sb(), 24);
        assert_eq!(FPSize::Double.eb(), 11);
        assert_eq!(FPSize::Double.sb(), 53);
    }

    // -----------------------------------------------------------------------
    // Bitwise instruction semantics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_and_rr_32() {
        let (a, b) = sym32();
        let expr = encode_and_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0xFF00_FF00), ("b", 0x0F0F_0F0F)]));
        assert_eq!(result, EvalResult::Bv(0x0F00_0F00));
    }

    #[test]
    fn test_orr_rr_32() {
        let (a, b) = sym32();
        let expr = encode_orr_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0xFF00_0000), ("b", 0x00FF_0000)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_0000));
    }

    #[test]
    fn test_eor_rr_32() {
        let (a, b) = sym32();
        let expr = encode_eor_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0xAAAA_AAAA), ("b", 0x5555_5555)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_mvn_32() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_mvn(OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 0)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_mvn_32_all_ones() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_mvn(OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 0xFFFF_FFFF)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_bic_rr_32() {
        let (a, b) = sym32();
        let expr = encode_bic_rr(OperandSize::S32, a, b);
        // a & ~b — clear bits of a where b is set
        let result = expr.eval(&env(&[("a", 0xFFFF_FFFF), ("b", 0x0F0F_0F0F)]));
        assert_eq!(result, EvalResult::Bv(0xF0F0_F0F0));
    }

    #[test]
    fn test_bic_rr_8() {
        // Sub-register width: I8 BandNot lowering proof uses 8-bit operands
        // even though the machine instruction runs in W registers.
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let expr = encode_bic_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0xFF), ("b", 0x0F)]));
        assert_eq!(result, EvalResult::Bv(0xF0));
    }

    #[test]
    fn test_orn_rr_32() {
        let (a, b) = sym32();
        let expr = encode_orn_rr(OperandSize::S32, a, b);
        // a | ~b
        let result = expr.eval(&env(&[("a", 0x0000_FFFF), ("b", 0xFFFF_0000)]));
        assert_eq!(result, EvalResult::Bv(0x0000_FFFF));
    }

    #[test]
    fn test_orn_rr_8() {
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let expr = encode_orn_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0x00), ("b", 0x0F)]));
        // ~0x0F (8-bit) = 0xF0
        assert_eq!(result, EvalResult::Bv(0xF0));
    }

    // -----------------------------------------------------------------------
    // Shift instruction semantics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lsl_rr_32() {
        let (a, b) = sym32();
        let expr = encode_lsl_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 1), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(16));
    }

    #[test]
    fn test_lsr_rr_32() {
        let (a, b) = sym32();
        let expr = encode_lsr_rr(OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0x8000_0000), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(0x0800_0000));
    }

    #[test]
    fn test_asr_rr_32() {
        let (a, b) = sym32();
        let expr = encode_asr_rr(OperandSize::S32, a, b);
        // Arithmetic shift right of 0x80000000 by 4 = 0xF8000000 (sign-extends)
        let result = expr.eval(&env(&[("a", 0x8000_0000), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(0xF800_0000));
    }

    #[test]
    fn test_asr_rr_32_positive() {
        let (a, b) = sym32();
        let expr = encode_asr_rr(OperandSize::S32, a, b);
        // Positive value: 0x7FFFFFFF >> 4 = 0x07FFFFFF (zero-fills)
        let result = expr.eval(&env(&[("a", 0x7FFF_FFFF), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(0x07FF_FFFF));
    }

    // -----------------------------------------------------------------------
    // MADD / MSUB / MOV / FMOV semantics tests (issue #435)
    // -----------------------------------------------------------------------

    #[test]
    fn test_madd_rr_32() {
        let (a, b) = sym32();
        let c = SmtExpr::var("c", 32);
        // MADD: c + (a * b) = 100 + (3 * 4) = 112
        let expr = encode_madd_rr(OperandSize::S32, a, b, c);
        let result = expr.eval(&env(&[("a", 3), ("b", 4), ("c", 100)]));
        assert_eq!(result, EvalResult::Bv(112));
    }

    #[test]
    fn test_msub_rr_32() {
        let (a, b) = sym32();
        let c = SmtExpr::var("c", 32);
        // MSUB: c - (a * b) = 100 - (3 * 4) = 88
        let expr = encode_msub_rr(OperandSize::S32, a, b, c);
        let result = expr.eval(&env(&[("a", 3), ("b", 4), ("c", 100)]));
        assert_eq!(result, EvalResult::Bv(88));
    }

    #[test]
    fn test_msub_rr_models_urem() {
        // Urem lowering: rem = a - (a /u b) * b
        // Concretely: 17 urem 5 = 2 = 17 - (17/5)*5 = 17 - 15
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let q = a.clone().bvudiv(b.clone());
        let expr = encode_msub_rr(OperandSize::S32, q, b, a);
        let result = expr.eval(&env(&[("a", 17), ("b", 5)]));
        assert_eq!(result, EvalResult::Bv(2));
    }

    #[test]
    fn test_mov_rr_identity() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_mov_rr(OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 0xDEAD_BEEF)]));
        assert_eq!(result, EvalResult::Bv(0xDEAD_BEEF));
    }

    #[test]
    fn test_fmov_identity() {
        // FMOV between GPR/FPR is a pure bit-level copy.
        let a = SmtExpr::var("a", 64);
        let expr = encode_fmov(a);
        let result = expr.eval(&env(&[("a", 0x3FF0_0000_0000_0000)]));
        assert_eq!(result, EvalResult::Bv(0x3FF0_0000_0000_0000));
    }

    // -----------------------------------------------------------------------
    // UBFM / SBFM / BFM semantics tests (issue #452)
    // -----------------------------------------------------------------------

    #[test]
    fn test_ubfm_extract_mid_nibble_i8() {
        // x = 0b10110100; lsb=2, width=4 -> slice = 0b1101 = 13.
        let a = SmtExpr::var("a", 8);
        let expr = encode_ubfm_extract(a, 2, 4, 8);
        let result = expr.eval(&env(&[("a", 0b1011_0100)]));
        assert_eq!(result, EvalResult::Bv(0b0000_1101));
    }

    #[test]
    fn test_ubfm_extract_low_nibble_i8() {
        // lsb=0, width=4 -> low nibble.
        let a = SmtExpr::var("a", 8);
        let expr = encode_ubfm_extract(a, 0, 4, 8);
        let result = expr.eval(&env(&[("a", 0xAB)]));
        assert_eq!(result, EvalResult::Bv(0x0B));
    }

    #[test]
    fn test_ubfm_extract_full_width_i8() {
        // lsb=0, width=8 -> whole byte, identity.
        let a = SmtExpr::var("a", 8);
        let expr = encode_ubfm_extract(a, 0, 8, 8);
        let result = expr.eval(&env(&[("a", 0xDE)]));
        assert_eq!(result, EvalResult::Bv(0xDE));
    }

    #[test]
    fn test_sbfm_extract_negative_slice_i8() {
        // x = 0b0010_1100; lsb=2, width=4 -> slice = 0b1011 (top bit set).
        // Sign-extends to 0xFB (-5 in i8).
        let a = SmtExpr::var("a", 8);
        let expr = encode_sbfm_extract(a, 2, 4, 8);
        let result = expr.eval(&env(&[("a", 0b0010_1100)]));
        assert_eq!(result, EvalResult::Bv(0xFB));
    }

    #[test]
    fn test_sbfm_extract_nonnegative_slice_i8() {
        // x = 0b0001_0100; lsb=2, width=4 -> slice = 0b0101 (top bit clear).
        // Sign-extend yields 0b0000_0101 = 5.
        let a = SmtExpr::var("a", 8);
        let expr = encode_sbfm_extract(a, 2, 4, 8);
        let result = expr.eval(&env(&[("a", 0b0001_0100)]));
        assert_eq!(result, EvalResult::Bv(0x05));
    }

    #[test]
    fn test_sbfm_extract_full_width_i8() {
        // lsb=0, width=8 -> whole byte, identity (sign-extend by 0).
        let a = SmtExpr::var("a", 8);
        let expr = encode_sbfm_extract(a, 0, 8, 8);
        let result = expr.eval(&env(&[("a", 0x80)]));
        assert_eq!(result, EvalResult::Bv(0x80));
    }

    #[test]
    fn test_bfm_insert_mid_nibble_i8() {
        // Wd = 0b1010_1010; Wn = 0b0000_1101; lsb=2, width=4.
        // Mask of width 4 shifted by 2: 0b0011_1100.
        // Preserved: Wd & ~mask = 0b1010_1010 & 0b1100_0011 = 0b1000_0010.
        // Insert: (Wn & 0b1111) << 2 = 0b0011_0100.
        // Result: 0b1000_0010 | 0b0011_0100 = 0b1011_0110.
        let d = SmtExpr::var("d", 8);
        let n = SmtExpr::var("n", 8);
        let expr = encode_bfm_insert(d, n, 2, 4, 8);
        let result = expr.eval(&env(&[("d", 0b1010_1010), ("n", 0b0000_1101)]));
        assert_eq!(result, EvalResult::Bv(0b1011_0110));
    }

    #[test]
    fn test_bfm_insert_low_nibble_clear_i8() {
        // Wd = 0xFF; Wn = 0x00; lsb=0, width=4 -> clear low nibble.
        let d = SmtExpr::var("d", 8);
        let n = SmtExpr::var("n", 8);
        let expr = encode_bfm_insert(d, n, 0, 4, 8);
        let result = expr.eval(&env(&[("d", 0xFF), ("n", 0x00)]));
        assert_eq!(result, EvalResult::Bv(0xF0));
    }

    #[test]
    fn test_bfm_insert_full_width_i8() {
        // lsb=0, width=8 -> replace entire byte with Wn (Wd ignored).
        let d = SmtExpr::var("d", 8);
        let n = SmtExpr::var("n", 8);
        let expr = encode_bfm_insert(d, n, 0, 8, 8);
        let result = expr.eval(&env(&[("d", 0x12), ("n", 0x34)]));
        assert_eq!(result, EvalResult::Bv(0x34));
    }
}
