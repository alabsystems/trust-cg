// trust-cg-verify/trust_ir_semantics.rs - trust_ir instruction semantics as SMT formulas
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Encodes trust_ir instruction semantics as bitvector SMT expressions.
// Each trust_ir instruction maps to a pure function from input bitvectors
// to an output bitvector.
//
// This is the ACTIVE trust_ir semantic encoder used by all verification proofs.
// It encodes trust_ir opcodes (from trust-cg-lower's `Opcode` enum) directly as
// `SmtExpr` bitvector formulas for SMT-based equivalence checking.
//
// SOURCE POLICY:
//
//   This module is the active local SMT encoder for trust_ir instruction
//   semantics. It encodes trust_ir opcodes (via trust-cg-lower's `Opcode` enum, which
//   maps from `trust_ir::Inst`) as `SmtExpr` bitvector formulas for SMT-based
//   equivalence proofs.
//
//   Issue #255 tracks replacing covered families with trust_ir's canonical
//   ay/formal semantics API when that API is available to this crate. Until
//   then, this module and its tests are the public source of truth for the
//   local-vs-upstream boundary.

//! trust_ir instruction semantics encoded as [`SmtExpr`] bitvector formulas.
//!
//! Each function takes symbolic input expressions and returns the symbolic
//! output expression representing the instruction's semantics.
//!
//! The local encoder remains authoritative for the families implemented here;
//! issue #255 tracks migration to trust-ir's canonical semantics API.

use crate::smt::{OutOfRangeMode, RoundingMode, SmtError, SmtExpr};
use std::sync::Arc;
use trust_cg_lower::instructions::{IntCC, Opcode};
use trust_cg_lower::types::Type;

/// Encode a trust_ir binary arithmetic operation as an SMT bitvector expression (fallible).
///
/// Returns `Err(SmtError::UnsupportedType)` if the opcode is not a supported
/// binary arithmetic opcode.
///
/// # Supported opcodes
///
/// - `Opcode::Iadd` -> `bvadd`
/// - `Opcode::Isub` -> `bvsub`
/// - `Opcode::Imul` -> `bvmul`
/// - `Opcode::Sdiv` -> `bvsdiv`
/// - `Opcode::Udiv` -> `bvudiv`
/// - `Opcode::Srem` -> `a - bvsdiv(a, b) * b`
/// - `Opcode::Urem` -> `a - bvudiv(a, b) * b`
pub fn try_encode_trust_ir_binop(
    opcode: &Opcode,
    _ty: Type,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> Result<SmtExpr, SmtError> {
    match opcode {
        Opcode::Iadd => Ok(lhs.bvadd(rhs)),
        Opcode::Isub => Ok(lhs.bvsub(rhs)),
        Opcode::Imul => Ok(lhs.bvmul(rhs)),
        Opcode::Sdiv => Ok(lhs.bvsdiv(rhs)),
        Opcode::Udiv => Ok(lhs.bvudiv(rhs)),
        // Remainder: a % b = a - (a / b) * b
        // Composed from existing SMT operations until native bvsrem/bvurem are added.
        Opcode::Srem => {
            let quotient = lhs.clone().bvsdiv(rhs.clone());
            Ok(lhs.bvsub(quotient.bvmul(rhs)))
        }
        Opcode::Urem => {
            let quotient = lhs.clone().bvudiv(rhs.clone());
            Ok(lhs.bvsub(quotient.bvmul(rhs)))
        }
        other => Err(SmtError::UnsupportedType(format!(
            "encode_trust_ir_binop: unsupported opcode {:?}",
            other
        ))),
    }
}

/// Encode a trust_ir binary arithmetic operation as an SMT bitvector expression.
///
/// Convenience wrapper around [`try_encode_trust_ir_binop`].
///
/// # Panics
///
/// Panics if `opcode` is not a binary arithmetic opcode.
pub fn encode_trust_ir_binop(opcode: &Opcode, ty: Type, lhs: SmtExpr, rhs: SmtExpr) -> SmtExpr {
    try_encode_trust_ir_binop(opcode, ty, lhs, rhs).expect(
        "encode_trust_ir_binop: unsupported opcode; use try_encode_trust_ir_binop() for fallible encoding",
    )
}

/// Encode a trust_ir unary negation as an SMT bitvector expression.
///
/// `Neg(a)` is encoded as `bvneg(a)` which is `bvsub(0, a)` in SMT-LIB2.
/// This matches the AArch64 NEG instruction semantics.
pub fn encode_trust_ir_neg(_ty: Type, operand: SmtExpr) -> SmtExpr {
    operand.bvneg()
}

/// Encode a trust_ir floating-point binary operation as an SMT FP expression (fallible).
///
/// Returns `Err(SmtError::UnsupportedType)` if the opcode is not a supported
/// floating-point binary opcode.
///
/// # Supported opcodes
///
/// - `Opcode::Fadd` -> `fp.add(RNE, a, b)`
/// - `Opcode::Fsub` -> `fp.sub(RNE, a, b)`
/// - `Opcode::Fmul` -> `fp.mul(RNE, a, b)`
/// - `Opcode::Fdiv` -> `fp.div(RNE, a, b)`
///
/// All FP operations use RNE (round to nearest, ties to even) as the default
/// rounding mode, matching AArch64's default FPCR.RMode setting.
pub fn try_encode_trust_ir_fp_binop(
    opcode: &Opcode,
    _ty: Type,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> Result<SmtExpr, SmtError> {
    use crate::smt::RoundingMode;
    match opcode {
        Opcode::Fadd => Ok(SmtExpr::fp_add(RoundingMode::RNE, lhs, rhs)),
        Opcode::Fsub => Ok(SmtExpr::fp_sub(RoundingMode::RNE, lhs, rhs)),
        Opcode::Fmul => Ok(SmtExpr::fp_mul(RoundingMode::RNE, lhs, rhs)),
        Opcode::Fdiv => Ok(SmtExpr::fp_div(RoundingMode::RNE, lhs, rhs)),
        // Rust f{32,64}::min/max == IEEE minimumNumber/maximumNumber. Same model
        // the AArch64 FMINNM/FMAXNM machine encoder uses (a 1:1 identity); the
        // exact NaN/-0 behavior is pinned by the on-host execution test.
        Opcode::Fmin => Ok(SmtExpr::fp_min_ieee(lhs, rhs)),
        Opcode::Fmax => Ok(SmtExpr::fp_max_ieee(lhs, rhs)),
        other => Err(SmtError::UnsupportedType(format!(
            "encode_trust_ir_fp_binop: unsupported opcode {:?}",
            other
        ))),
    }
}

/// Encode a trust_ir floating-point binary operation as an SMT FP expression.
///
/// Convenience wrapper around [`try_encode_trust_ir_fp_binop`].
///
/// # Panics
///
/// Panics if `opcode` is not a floating-point binary opcode.
pub fn encode_trust_ir_fp_binop(opcode: &Opcode, ty: Type, lhs: SmtExpr, rhs: SmtExpr) -> SmtExpr {
    try_encode_trust_ir_fp_binop(opcode, ty, lhs, rhs)
        .expect("encode_trust_ir_fp_binop: unsupported opcode; use try_encode_trust_ir_fp_binop() for fallible encoding")
}

/// Encode a trust_ir floating-point negation as an SMT FP expression.
///
/// `Fneg(a)` is encoded as `fp.neg(a)`. This matches the AArch64 FNEG instruction.
pub fn encode_trust_ir_fneg(_ty: Type, operand: SmtExpr) -> SmtExpr {
    operand.fp_neg()
}

/// Encode a trust_ir floating-point absolute value as an SMT FP expression.
///
/// `Fabs(a)` is encoded as `fp.abs(a)`. This matches the AArch64 FABS instruction.
///
/// Reference: ARM DDI 0487, C7.2.73 FABS (scalar).
pub fn encode_trust_ir_fabs(_ty: Type, operand: SmtExpr) -> SmtExpr {
    operand.fp_abs()
}

/// Encode a trust_ir floating-point square root as an SMT FP expression.
///
/// `Fsqrt(a)` is encoded as `fp.sqrt(RNE, a)`. The rounding mode is RNE
/// (round-to-nearest-even), matching the default FPCR.RMode on AArch64.
///
/// Reference: ARM DDI 0487, C7.2.160 FSQRT (scalar).
pub fn encode_trust_ir_fsqrt(_ty: Type, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_sqrt(RoundingMode::RNE, operand)
}

/// Encode a trust_ir floating-point UNARY value op as an SMT FP expression,
/// dispatched by opcode (`Fneg`/`Fabs`/`Fsqrt`).
///
/// Used by the AArch64 operand-reconstruction path: it pairs the intended
/// trust_ir source op with the real machine encoder (`encode_fneg`/`encode_fabs`/
/// `encode_fsqrt`). A wrong unary op (FNEG-as-FABS) yields a structurally
/// distinct expression that diverges for a negative input ⇒ REFUTE.
pub fn try_encode_trust_ir_fp_unaryop(
    opcode: &Opcode,
    ty: Type,
    operand: SmtExpr,
) -> Result<SmtExpr, SmtError> {
    match opcode {
        Opcode::Fneg => Ok(encode_trust_ir_fneg(ty, operand)),
        Opcode::Fabs => Ok(encode_trust_ir_fabs(ty, operand)),
        Opcode::Fsqrt => Ok(encode_trust_ir_fsqrt(ty, operand)),
        // Round-to-integral family (Rust `f{32,64}::floor`/`ceil`/`trunc`).
        // Paired with the AArch64 FRINTM/FRINTP/FRINTZ machine encoders; a wrong
        // rounding direction (floor-as-ceil) diverges on a non-integral input
        // ⇒ REFUTE.
        Opcode::Ffloor => Ok(encode_trust_ir_ffloor(ty, operand)),
        Opcode::Fceil => Ok(encode_trust_ir_fceil(ty, operand)),
        Opcode::Ftrunc => Ok(encode_trust_ir_ftrunc(ty, operand)),
        other => Err(SmtError::UnsupportedType(format!(
            "encode_trust_ir_fp_unaryop: unsupported opcode {:?}",
            other
        ))),
    }
}

/// Encode `trust_ir::FcvtToInt(int_width, fp, a)` — FP→signed-int conversion
/// (round toward zero), as `fp.to_sbv(RTZ, a, int_width)`.
///
/// Matches AArch64 FCVTZS (and C cast-to-signed-int) truncation semantics.
/// Reference: ARM DDI 0487, C7.2.69 FCVTZS (scalar, integer).
pub fn encode_trust_ir_fcvt_to_sint(int_width: u32, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_to_sbv(RoundingMode::RTZ, operand, int_width)
}

/// Encode `trust_ir::FcvtToUint(int_width, fp, a)` — FP→unsigned-int conversion
/// (round toward zero), as `fp.to_ubv(RTZ, a, int_width)`.
///
/// Matches AArch64 FCVTZU truncation semantics.
/// Reference: ARM DDI 0487, C7.2.72 FCVTZU (scalar, integer).
pub fn encode_trust_ir_fcvt_to_uint(int_width: u32, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_to_ubv(RoundingMode::RTZ, operand, int_width)
}

/// Encode an FP→signed-int conversion with ROUND-TO-NEAREST-EVEN (the
/// non-truncating form), as `fp.to_sbv(RNE, a, int_width)`. SATURATING
/// out-of-range (the shared AArch64/wasm/RISC-V/Rust contract); contrast the RTZ
/// `encode_trust_ir_fcvt_to_sint`. A truncating-for-rounding (or vice versa)
/// machine mismatch diverges for a non-integral input ⇒ REFUTE.
pub fn encode_trust_ir_fcvt_to_sint_rne(int_width: u32, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_to_sbv(RoundingMode::RNE, operand, int_width)
}

/// x86 `CVTT*2SI` ISA reference: FP→signed-int, truncate toward zero (RTZ),
/// INTEGER-INDEFINITE on NaN / +-Inf / out-of-range (Intel SDM Vol 2A). This is
/// the x86 ISA-faithful spec for the TRUNCATING `CVTTSD2SI`/`CVTTSS2SI` machine
/// opcodes — DISTINCT from the saturating `encode_trust_ir_fcvt_to_sint`
/// (AArch64 FCVTZS / wasm trunc_sat / RISC-V FCVT), which they must NOT be
/// modelled as (#99: a saturating spec for the x86 opcode was a latent
/// miscompile-class divergence, caught by the Rosetta bridge). The Rust-level
/// `FloatToInt` (saturating) lowering to x86 must therefore WRAP this opcode in
/// a range-checking fixup — that is the lowering's job, not this ISA proof's.
/// Reference: Intel SDM Vol 2A, CVTTSD2SI/CVTTSS2SI.
pub fn encode_trust_ir_fcvt_to_sint_x86(int_width: u32, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_to_sbv_mode(
        RoundingMode::RTZ,
        operand,
        int_width,
        OutOfRangeMode::IntegerIndefinite,
    )
}

/// x86 `CVT*2SI` ISA reference: FP→signed-int, round-to-nearest-even (RNE, the
/// MXCSR default), INTEGER-INDEFINITE on NaN / +-Inf / out-of-range. The
/// non-truncating x86 ISA-faithful spec for `CVTSD2SI`/`CVTSS2SI`; see
/// `encode_trust_ir_fcvt_to_sint_x86` for the truncating form and the
/// saturating-vs-indefinite rationale.
/// Reference: Intel SDM Vol 2A, CVTSD2SI/CVTSS2SI.
pub fn encode_trust_ir_fcvt_to_sint_x86_rne(int_width: u32, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_to_sbv_mode(
        RoundingMode::RNE,
        operand,
        int_width,
        OutOfRangeMode::IntegerIndefinite,
    )
}

/// Encode `trust_ir::FcvtFromInt(fp, int, a)` — signed-int→FP conversion
/// (round-to-nearest-even, the default FPCR.RMode), as
/// `(to_fp eb sb) RNE a` with `a` interpreted as a SIGNED bitvector.
///
/// Matches AArch64 SCVTF. Reference: ARM DDI 0487, C7.2.194 SCVTF.
pub fn encode_trust_ir_fcvt_from_sint(eb: u32, sb: u32, operand: SmtExpr) -> SmtExpr {
    SmtExpr::bv_to_fp(RoundingMode::RNE, operand, eb, sb)
}

/// Encode `trust_ir::FcvtFromUint(fp, int, a)` — unsigned-int→FP conversion
/// (round-to-nearest-even), as `(to_fp eb sb) RNE zext(a)`.
///
/// The `BvToFP` evaluator interprets its operand as SIGNED, so the operand is
/// zero-extended by one bit-width first to guarantee a non-negative
/// (sign-bit-clear) value, giving the correct UNSIGNED conversion.
/// Matches AArch64 UCVTF. Reference: ARM DDI 0487, C7.2.326 UCVTF.
pub fn encode_trust_ir_fcvt_from_uint(
    eb: u32,
    sb: u32,
    operand: SmtExpr,
    src_width: u32,
) -> SmtExpr {
    let zext = SmtExpr::ZeroExtend {
        operand: Arc::new(operand),
        extra_bits: src_width,
        width: src_width * 2,
    };
    SmtExpr::bv_to_fp(RoundingMode::RNE, zext, eb, sb)
}

/// Encode a trust_ir FP-FORMAT conversion (`Fpromote`/`Fdemote`) — a cast
/// BETWEEN two IEEE-754 floating-point formats, as `(to_fp eb sb) RNE a` where
/// `(eb, sb)` is the DESTINATION format.
///
/// `Fpromote` (F32→F64, widen) is exact for every finite single, so rounding is
/// immaterial; `Fdemote` (F64→F32, narrow) genuinely rounds, modeled here with
/// round-to-nearest-even (the default FPCR.RMode / MXCSR.RC), matching AArch64
/// FCVT and the C float/double cast. The DIRECTION is encoded entirely by the
/// destination `(eb, sb)`: the SAME encoder builds both the widen (target binary64
/// 11/53) and the narrow (target binary32 8/24), so a wrong direction (a demote
/// where a promote was intended, or vice versa) produces a structurally different
/// destination format and DIVERGES under the wiring-preserving FP evaluator for a
/// value that does not round-trip through binary32 ⇒ REFUTE.
///
/// Reference: ARM DDI 0487, C7.2.67 FCVT (scalar, floating-point precision).
pub fn encode_trust_ir_fp_format_convert(eb: u32, sb: u32, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_to_fp(RoundingMode::RNE, operand, eb, sb)
}

/// Encode a trust_ir floating-point floor as an SMT FP expression.
///
/// `FFloor(a)` is `fp.roundToIntegral(RTN, a)` — round toward negative
/// infinity. This is the exact spec of the Rust `f{32,64}::floor` /
/// `floorf{32,64}` intrinsic: the largest integral value not greater than `a`.
pub fn encode_trust_ir_ffloor(_ty: Type, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_round_to_integral(RoundingMode::RTN, operand)
}

/// Encode a trust_ir floating-point ceiling as an SMT FP expression.
///
/// `FCeil(a)` is `fp.roundToIntegral(RTP, a)` — round toward positive infinity.
/// This is the exact spec of the Rust `f{32,64}::ceil` / `ceilf{32,64}`
/// intrinsic: the smallest integral value not less than `a`.
pub fn encode_trust_ir_fceil(_ty: Type, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_round_to_integral(RoundingMode::RTP, operand)
}

/// Encode a trust_ir floating-point truncation as an SMT FP expression.
///
/// `FTrunc(a)` is `fp.roundToIntegral(RTZ, a)` — round toward zero. This is the
/// exact spec of the Rust `f{32,64}::trunc` / `truncf{32,64}` intrinsic: the
/// integral part of `a`, dropping the fractional digits.
pub fn encode_trust_ir_ftrunc(_ty: Type, operand: SmtExpr) -> SmtExpr {
    SmtExpr::fp_round_to_integral(RoundingMode::RTZ, operand)
}

/// Encode trust_ir `Ctpop` (population count) — the number of set bits in
/// `operand`, as a sum of the `width` individual source bits zero-extended to the
/// result width. The result lies in `[0, width]`.
///
/// This is the INDEPENDENT trust_ir reference spec for the x86 POPCNT lowering;
/// the machine side is `x86_64_semantics::encode_popcnt`. A POPCNT-for-TZCNT (or
/// any other bit-count op) mismatch diverges (popcount != trailing-zero-count for
/// almost every input) ⇒ REFUTE.
/// Spec for the byte sum-of-absolute-differences reduction that `PSADBW`
/// implements (the SOURCE side of the reconstruction against
/// [`crate::x86_64_semantics::encode_psadbw`]). For each 64-bit output lane
/// `j` in {0,1}, `dst.qword[j] = Σ_{i=0..8} |a.byte[8j+i] - b.byte[8j+i]|`
/// (each byte zero-extended to 64 bits, so `|x-y| = ite(x >=u y, x-y, y-x)` is
/// exact and the group sum never wraps). Written independently of the machine
/// encoder; a wrong emitted opcode reconstructs to a different machine
/// expression and REFUTES this equality (the reconstruction's non-degeneracy).
pub fn encode_trust_ir_byte_sad(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let mut lanes: Vec<SmtExpr> = Vec::with_capacity(2);
    for j in 0..2u32 {
        let mut sum = SmtExpr::bv_const(0, 64);
        for i in 0..8u32 {
            let byte = j * 8 + i;
            let a_byte = a.clone().extract(byte * 8 + 7, byte * 8).zero_ext(56);
            let b_byte = b.clone().extract(byte * 8 + 7, byte * 8).zero_ext(56);
            let absdiff = SmtExpr::ite(
                a_byte.clone().bvuge(b_byte.clone()),
                a_byte.clone().bvsub(b_byte.clone()),
                b_byte.bvsub(a_byte),
            );
            sum = sum.bvadd(absdiff);
        }
        lanes.push(sum);
    }
    lanes[1].clone().concat(lanes[0].clone())
}

pub fn encode_trust_ir_ctpop(operand: SmtExpr) -> SmtExpr {
    let width = operand.bv_width();
    let mut acc = SmtExpr::bv_const(0, width);
    for i in 0..width {
        let bit = operand.clone().extract(i, i);
        let bit_w = if width == 1 {
            bit
        } else {
            bit.zero_ext(width - 1)
        };
        acc = acc.bvadd(bit_w);
    }
    acc
}

/// Encode trust_ir `Cttz` (count trailing zeros) with the DEFINED zero-input
/// convention `Cttz(0) = width` (matching x86 TZCNT). Scans from MSB to LSB so the
/// lowest set bit wins.
///
/// The machine side is `x86_64_semantics::encode_tzcnt`. For x86 BSF (which
/// coincides with TZCNT for nonzero inputs) the caller carries a `src != 0`
/// precondition (BSF(0) is architecturally undefined).
pub fn encode_trust_ir_cttz(operand: SmtExpr) -> SmtExpr {
    let width = operand.bv_width();
    let mut result = SmtExpr::bv_const(u64::from(width), width);
    for i in (0..width).rev() {
        let set = operand
            .clone()
            .extract(i, i)
            .eq_expr(SmtExpr::bv_const(1, 1));
        result = SmtExpr::ite(set, SmtExpr::bv_const(u64::from(i), width), result);
    }
    result
}

/// Encode trust_ir `Ctlz` (count leading zeros) with the DEFINED zero-input
/// convention `Ctlz(0) = width` (matching x86 LZCNT). Scans from LSB to MSB so the
/// highest set bit wins and contributes `width - 1 - i` leading zeros.
///
/// The machine side is `x86_64_semantics::encode_lzcnt`.
pub fn encode_trust_ir_ctlz(operand: SmtExpr) -> SmtExpr {
    let width = operand.bv_width();
    let mut result = SmtExpr::bv_const(u64::from(width), width);
    for i in 0..width {
        let leading = width - 1 - i;
        let set = operand
            .clone()
            .extract(i, i)
            .eq_expr(SmtExpr::bv_const(1, 1));
        result = SmtExpr::ite(set, SmtExpr::bv_const(u64::from(leading), width), result);
    }
    result
}

/// Encode the x86 BSR (bit-scan-reverse) reference for NONZERO inputs: the index
/// of the highest set bit, `(width - 1) - Ctlz(src)`. The caller carries a
/// `src != 0` precondition (BSR(0) is architecturally undefined). The machine side
/// is `x86_64_semantics::encode_bsr`.
pub fn encode_trust_ir_bsr_nonzero(operand: SmtExpr) -> SmtExpr {
    let width = operand.bv_width();
    let ctlz = encode_trust_ir_ctlz(operand);
    SmtExpr::bv_const(u64::from(width - 1), width).bvsub(ctlz)
}

/// Spec of the `MINSD`/`MINSS` HARDWARE minimum, formulated INDEPENDENTLY of
/// the machine-side encoder (`x86_64_semantics::encode_fp_minsd`).
///
/// The machine side transcribes the SDM as the single `dest < src ? dest : src`
/// conditional. Here we write the equivalent spec from the COMPLEMENTARY angle:
/// the result is the second operand `src` exactly when the inputs are unordered
/// (either is NaN) OR `dest >= src` (ordered); the result is `dest` only in the
/// remaining case — `dest < src` ordered. The two formulations select on
/// different primitives (`fp.lt` vs `fp.ge` + explicit `fp.isNaN`), so proving
/// them bit-equal over every NaN / signed-zero / ordered pair is genuine SMT
/// work (the solver must reason about IEEE comparison + NaN), not a syntactic
/// identity. This is the FAITHFUL MINSD hardware spec — NOT IEEE minNum (the
/// NaN-away correction lives in the bridge's XOR-blend fixup).
pub fn encode_trust_ir_fminsd_hw(_ty: Type, dest: SmtExpr, src: SmtExpr) -> SmtExpr {
    let unord = dest.clone().fp_is_nan().or_expr(src.clone().fp_is_nan());
    let ge = dest.clone().fp_ge(src.clone());
    // (unordered OR dest >= src) ? src : dest
    SmtExpr::ite(unord.or_expr(ge), src, dest)
}

/// Spec of the `MAXSD`/`MAXSS` HARDWARE maximum — mirror of
/// `encode_trust_ir_fminsd_hw`. The result is the second operand `src` when the
/// inputs are unordered OR `dest <= src`; the result is `dest` only when
/// `dest > src` ordered. Independent (uses `fp.le`) of the machine side's
/// `dest > src ? dest : src`.
pub fn encode_trust_ir_fmaxsd_hw(_ty: Type, dest: SmtExpr, src: SmtExpr) -> SmtExpr {
    let unord = dest.clone().fp_is_nan().or_expr(src.clone().fp_is_nan());
    let le = dest.clone().fp_le(src.clone());
    // (unordered OR dest <= src) ? src : dest
    SmtExpr::ite(unord.or_expr(le), src, dest)
}

/// Spec of the `CMPSD`/`CMPSS` UNORD (predicate 3) compare-to-mask, formulated
/// independently of the machine-side `encode_fp_cmp_unord_mask`.
///
/// The mask is all-ones (of the lane width) iff the inputs are unordered. The
/// machine side writes that as `isNaN(a) OR isNaN(b)`; here we write the
/// equivalent `NOT(a == a) OR NOT(b == b)` — a self-`fp.eq` NaN test (a number
/// equals itself; only NaN does not). Proving them equal exercises the solver's
/// `fp.eq`/`fp.isNaN`/NaN reasoning. `width` is the lane width (64 SD / 32 SS).
pub fn encode_trust_ir_cmp_unord_mask(width: u32, a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let a_not_self = a.clone().fp_eq(a).not_expr();
    let b_not_self = b.clone().fp_eq(b).not_expr();
    let unord = a_not_self.or_expr(b_not_self);
    let all_ones = SmtExpr::bv_const(u64::MAX, width);
    let zero = SmtExpr::bv_const(0, width);
    SmtExpr::ite(unord, all_ones, zero)
}

/// Create symbolic FP input variables for a binary FP operation.
///
/// Returns `(lhs, rhs)` as FP constant nodes. For FP proofs, we use
/// `FPConst` nodes that the evaluator interprets via native f32/f64.
/// The `eb` and `sb` parameters specify the FP format (e.g., 8/24 for f32, 11/53 for f64).
pub fn symbolic_fp_binary_inputs(eb: u32, sb: u32) -> (SmtExpr, SmtExpr) {
    let _total = eb + sb;
    // Use Var nodes with the bit-width matching the FP format.
    // The proof obligation's fp_inputs field declares these as FP-sorted.
    // For evaluation, we populate them via the fp_env pathway.
    (
        SmtExpr::FPConst { bits: 0, eb, sb }, // placeholder; actual values set per test
        SmtExpr::FPConst { bits: 0, eb, sb },
    )
}

/// Encode a trust_ir floating-point comparison as an SMT expression.
///
/// `Fcmp(cond, a, b)` returns a 1-bit bitvector: `bv1(1)` if the condition
/// holds, `bv1(0)` otherwise. This matches the AArch64 FCMP + CSET output
/// format.
///
/// # Supported conditions
///
/// All 14 `FloatCC` variants: 6 ordered, 2 ordering predicates, 6 unordered.
///
/// Ordered comparisons return false when either operand is NaN.
/// Unordered comparisons return true when either operand is NaN.
pub fn encode_trust_ir_fcmp(
    cond: &trust_cg_lower::instructions::FloatCC,
    _ty: Type,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> SmtExpr {
    use trust_cg_lower::instructions::FloatCC;

    let a_nan = lhs.clone().fp_is_nan();
    let b_nan = rhs.clone().fp_is_nan();
    let either_nan = a_nan.clone().or_expr(b_nan.clone());

    let bool_result = match cond {
        FloatCC::Equal => lhs.fp_eq(rhs),
        FloatCC::NotEqual => lhs.fp_eq(rhs).not_expr(),
        FloatCC::LessThan => lhs.fp_lt(rhs),
        FloatCC::LessThanOrEqual => lhs.fp_le(rhs),
        FloatCC::GreaterThan => lhs.fp_gt(rhs),
        FloatCC::GreaterThanOrEqual => lhs.fp_ge(rhs),
        FloatCC::Ordered => a_nan.not_expr().and_expr(b_nan.not_expr()),
        FloatCC::Unordered => either_nan,
        FloatCC::UnorderedEqual => lhs.fp_eq(rhs).or_expr(either_nan),
        FloatCC::UnorderedNotEqual => lhs.fp_eq(rhs).not_expr().or_expr(either_nan),
        FloatCC::UnorderedLessThan => lhs.fp_lt(rhs).or_expr(either_nan),
        FloatCC::UnorderedLessThanOrEqual => lhs.fp_le(rhs).or_expr(either_nan),
        FloatCC::UnorderedGreaterThan => lhs.fp_gt(rhs).or_expr(either_nan),
        FloatCC::UnorderedGreaterThanOrEqual => lhs.fp_ge(rhs).or_expr(either_nan),
    };

    SmtExpr::ite(
        bool_result,
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    )
}

/// Encode a trust_ir integer constant.
pub fn encode_trust_ir_iconst(ty: Type, imm: i64) -> SmtExpr {
    let width = ty.bits();
    SmtExpr::bv_const(imm as u64, width)
}

/// Create symbolic input variables for a binary operation at the given type.
///
/// Returns `(lhs, rhs)` as symbolic `SmtExpr::Var` nodes.
pub fn symbolic_binary_inputs(ty: Type) -> (SmtExpr, SmtExpr) {
    let width = ty.bits();
    (SmtExpr::var("a", width), SmtExpr::var("b", width))
}

/// Create a symbolic input variable for a unary operation.
pub fn symbolic_unary_input(ty: Type) -> SmtExpr {
    SmtExpr::var("a", ty.bits())
}

/// Encode a trust_ir integer comparison as an SMT expression.
///
/// `Icmp(cond, a, b)` returns a 1-bit bitvector: `bv1(1)` if the condition
/// holds, `bv1(0)` otherwise. This matches the AArch64 CSET output format.
///
/// # Supported conditions
///
/// All 10 `IntCC` variants (see `trust_cg_lower::instructions::IntCC`).
pub fn encode_trust_ir_icmp(cond: &IntCC, _ty: Type, lhs: SmtExpr, rhs: SmtExpr) -> SmtExpr {
    let cmp_bool = match cond {
        IntCC::Equal => lhs.eq_expr(rhs),
        IntCC::NotEqual => lhs.eq_expr(rhs).not_expr(),
        IntCC::SignedLessThan => lhs.bvslt(rhs),
        IntCC::SignedGreaterThanOrEqual => lhs.bvsge(rhs),
        IntCC::SignedGreaterThan => lhs.bvsgt(rhs),
        IntCC::SignedLessThanOrEqual => lhs.bvsle(rhs),
        IntCC::UnsignedLessThan => lhs.bvult(rhs),
        IntCC::UnsignedGreaterThanOrEqual => lhs.bvuge(rhs),
        IntCC::UnsignedGreaterThan => lhs.bvugt(rhs),
        IntCC::UnsignedLessThanOrEqual => lhs.bvule(rhs),
    };
    SmtExpr::ite(cmp_bool, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

// ---------------------------------------------------------------------------
// LANE-WISE (packed/SIMD) trust_ir source semantics
// ---------------------------------------------------------------------------
//
// A packed/SIMD value op is N independent copies of a SCALAR trust_ir op over the
// lanes of a fixed-width vector. The SOURCE side of a lane-wise reconstruction is
// therefore the scalar trust_ir op `map_lanes`-applied over the chosen
// [`VectorArrangement`]. The MACHINE side is the real packed encoder (a DIFFERENT
// module). They agree IFF the typed opcode->source mapping picked the RIGHT scalar
// op AND the RIGHT lane shape: a wrong lane op (Iadd-for-Isub) diverges in every
// lane, and a wrong lane WIDTH (i16x8 vs i32x4) produces a structurally different
// 128-bit value (carry/borrow crosses the lane boundary at the wrong place) ⇒
// REFUTE. This is the lane-wise dual of the scalar reconstruction credit content.

/// Encode a trust_ir lane-wise ARITHMETIC binary op (`Iadd`/`Isub`/`Imul`) over a
/// vector at the given [`VectorArrangement`]: extract each lane, apply the scalar
/// op, concat. The SOURCE side of a packed integer add/sub/mul reconstruction.
///
/// Panics if `opcode` is not one of Iadd/Isub/Imul (the lane-wise arithmetic set
/// the packed reconstruction uses).
pub fn encode_trust_ir_lanewise_binop(
    opcode: &Opcode,
    arrangement: crate::smt::VectorArrangement,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> SmtExpr {
    crate::smt::map_lanes_binary(&lhs, &rhs, arrangement, |a, b| match opcode {
        Opcode::Iadd => a.bvadd(b),
        Opcode::Isub => a.bvsub(b),
        Opcode::Imul => a.bvmul(b),
        other => panic!("encode_trust_ir_lanewise_binop: unsupported lane op {other:?}"),
    })
}

/// Encode a trust_ir lane-wise INTEGER COMPARE (`Equal`/`SignedGreaterThan`) over
/// a vector at the given [`VectorArrangement`], producing a per-lane ALL-ONES /
/// ALL-ZERO mask (the SSE PCMP* compare-mask convention, matching the machine
/// `encode_packed_eq`/`encode_packed_signed_gt`). The SOURCE side of a packed
/// compare-mask reconstruction.
///
/// Panics if `cond` is not Equal or SignedGreaterThan (the only conditions whose
/// whole packed lowering is the single PCMPEQ*/PCMPGT* instruction).
pub fn encode_trust_ir_lanewise_cmp_mask(
    cond: &IntCC,
    arrangement: crate::smt::VectorArrangement,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, lane_bits), lane_bits);
    let zero = SmtExpr::bv_const(0, lane_bits);
    crate::smt::map_lanes_binary(&lhs, &rhs, arrangement, |a, b| {
        let cmp_bool = match cond {
            IntCC::Equal => a.eq_expr(b),
            IntCC::SignedGreaterThan => a.bvsgt(b),
            other => panic!("encode_trust_ir_lanewise_cmp_mask: unsupported lane cond {other:?}"),
        };
        SmtExpr::ite(cmp_bool, all_ones.clone(), zero.clone())
    })
}

/// Encode a trust_ir lane-wise FULL-WIDTH BITWISE op (`Band`/`Bor`/`Bxor`/
/// `BandNot`) over a 128-bit vector. Bitwise ops are lane-independent (every bit
/// is computed identically regardless of lane boundaries), so the full-width
/// SmtExpr op IS the lane-wise reconstruction — there is no lane-width content,
/// only the OP content. The SOURCE side of a packed PAND/POR/PXOR/PANDN.
///
/// PANDN computes `(~a) & b` (note the operand order: the FIRST operand is
/// complemented), matching the x86 `encode_pandn`.
pub fn encode_trust_ir_v128_bitwise(opcode: &Opcode, lhs: SmtExpr, rhs: SmtExpr) -> SmtExpr {
    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, 64), 64);
    let all_ones_128 = all_ones.clone().concat(all_ones);
    match opcode {
        Opcode::Band => lhs.bvand(rhs),
        Opcode::Bor => lhs.bvor(rhs),
        Opcode::Bxor => lhs.bvxor(rhs),
        // PANDN: (~lhs) & rhs.
        Opcode::BandNot => lhs.bvxor(all_ones_128).bvand(rhs),
        other => panic!("encode_trust_ir_v128_bitwise: unsupported op {other:?}"),
    }
}

/// Encode a trust_ir bitwise binary operation as an SMT bitvector expression (fallible).
///
/// Returns `Err(SmtError::UnsupportedType)` if the opcode is not a supported
/// bitwise binary opcode.
///
/// # Supported opcodes
///
/// - `Opcode::Band`    -> `bvand`
/// - `Opcode::Bor`     -> `bvor`
/// - `Opcode::Bxor`    -> `bvxor`
/// - `Opcode::BandNot` -> `lhs & ~rhs`  (AArch64 BIC semantics)
/// - `Opcode::BorNot`  -> `lhs | ~rhs`  (AArch64 ORN semantics)
pub fn try_encode_trust_ir_bitwise_binop(
    opcode: &Opcode,
    ty: Type,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> Result<SmtExpr, SmtError> {
    match opcode {
        Opcode::Band => Ok(lhs.bvand(rhs)),
        Opcode::Bor => Ok(lhs.bvor(rhs)),
        Opcode::Bxor => Ok(lhs.bvxor(rhs)),
        Opcode::BandNot => {
            let width = ty.bits();
            let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
            Ok(lhs.bvand(rhs.bvxor(all_ones)))
        }
        Opcode::BorNot => {
            let width = ty.bits();
            let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
            Ok(lhs.bvor(rhs.bvxor(all_ones)))
        }
        other => Err(SmtError::UnsupportedType(format!(
            "encode_trust_ir_bitwise_binop: unsupported opcode {:?}",
            other
        ))),
    }
}

/// Encode a trust_ir bitwise binary operation as an SMT bitvector expression.
///
/// Convenience wrapper around [`try_encode_trust_ir_bitwise_binop`].
///
/// # Panics
///
/// Panics if `opcode` is not a bitwise binary opcode.
pub fn encode_trust_ir_bitwise_binop(
    opcode: &Opcode,
    ty: Type,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> SmtExpr {
    try_encode_trust_ir_bitwise_binop(opcode, ty, lhs, rhs)
        .expect("encode_trust_ir_bitwise_binop: unsupported opcode; use try_encode_trust_ir_bitwise_binop() for fallible encoding")
}

/// Encode a trust_ir bitwise NOT as an SMT bitvector expression.
///
/// `Bnot(a)` is encoded as `bvxor(a, all_ones)` which flips all bits.
/// This matches the AArch64 MVN instruction semantics.
pub fn encode_trust_ir_bnot(ty: Type, operand: SmtExpr) -> SmtExpr {
    let width = ty.bits();
    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
    operand.bvxor(all_ones)
}

/// Encode a trust_ir `Sextend { from_ty, to_ty }` -- signed integer extension.
///
/// Semantics: the `from_ty`-bit `operand` is SIGN-extended to `to_ty` bits,
/// replicating bit `from_bits - 1` across the new high bits. This is the source
/// (trust_ir) side of the AArch64 `SXTB`/`SXTH`/`SXTW` lowering. The machine
/// side built from the REAL opcode is [`crate::aarch64_semantics::encode_sxt`];
/// the two agree IFF isel emitted a SIGN extend of the right source width — a
/// UXT-for-Sextend (zero instead of sign extension) yields a different result
/// for a negative source ⇒ REFUTE (task #63 Phase-2 reconstruction).
///
/// `operand` must be a `from_bits`-wide bitvector and `to_bits > from_bits`.
pub fn encode_trust_ir_sextend(from_bits: u32, to_bits: u32, operand: SmtExpr) -> SmtExpr {
    debug_assert!(
        to_bits > from_bits,
        "encode_trust_ir_sextend: to_bits must exceed from_bits"
    );
    debug_assert_eq!(
        operand.bv_width(),
        from_bits,
        "encode_trust_ir_sextend: operand width must equal from_bits"
    );
    operand.sign_ext(to_bits - from_bits)
}

/// Encode a trust_ir `Uextend { from_ty, to_ty }` -- unsigned integer extension.
///
/// Semantics: the `from_ty`-bit `operand` is ZERO-extended to `to_ty` bits. This
/// is the source (trust_ir) side of the AArch64 `UXTB`/`UXTH`/`UXTW` lowering.
/// The machine side built from the REAL opcode is
/// [`crate::aarch64_semantics::encode_uxt`]; the two agree IFF isel emitted a
/// ZERO extend of the right source width — a SXT-for-Uextend (sign instead of
/// zero extension) yields a different result for a negative source ⇒ REFUTE.
///
/// `operand` must be a `from_bits`-wide bitvector and `to_bits > from_bits`.
pub fn encode_trust_ir_uextend(from_bits: u32, to_bits: u32, operand: SmtExpr) -> SmtExpr {
    debug_assert!(
        to_bits > from_bits,
        "encode_trust_ir_uextend: to_bits must exceed from_bits"
    );
    debug_assert_eq!(
        operand.bv_width(),
        from_bits,
        "encode_trust_ir_uextend: operand width must equal from_bits"
    );
    operand.zero_ext(to_bits - from_bits)
}

/// Encode a trust_ir `Bitcast { to_ty }` as an SMT bitvector expression.
///
/// `Bitcast` reinterprets the bits of `operand` as a different type of the
/// same width. At the SMT bitvector level this is the identity function --
/// the bit pattern is unchanged. The trust_ir type system enforces that the
/// source and target types have the same bit width.
///
/// # Lowering
///
/// On AArch64, `Bitcast` lowers to one of:
/// - `MOV Wd, Wn` / `MOV Xd, Xn` for GPR<->GPR (e.g. `i32<->i32` with type
///   reinterpretation, or pointer bitcasts)
/// - `FMOV Sd, Sn` / `FMOV Dd, Dn` for FPR<->FPR (e.g. `f32<->f32`)
/// - `FMOV Sd, Wn` / `FMOV Wd, Sn` / `FMOV Dd, Xn` / `FMOV Xd, Dn` for
///   GPR<->FPR (e.g. `i32<->f32`, `i64<->f64`)
///
/// All of these are pure bit-level copies with no rounding, no NaN
/// sanitization, and no width change, so the SMT equivalence reduces to
/// `out == in`.
pub fn encode_trust_ir_bitcast(_from_ty: Type, _to_ty: Type, operand: SmtExpr) -> SmtExpr {
    operand
}

/// Encode a trust_ir `ExtractBits { lsb, width }` -- unsigned bitfield extract.
///
/// Semantics: the `width`-bit slice of `operand` starting at bit `lsb` is
/// returned, zero-extended to the full operand width:
///
///   result = (operand lsr lsb) & mask(width)
///
/// On AArch64 this lowers to `UBFM Wd, Wn, #lsb, #(lsb + width - 1)` (see
/// `trust-cg-lower/src/isel.rs::select_bitfield_extract`).
///
/// # Preconditions
///
/// - `width >= 1`
/// - `lsb + width <= ty.bits()` (enforced by the trust_ir type system; the
///   encoder only asserts the operand width matches `ty`).
///
/// Reference: ARM DDI 0487, C6.2.335 UBFM / C6.2.334 UBFX.
pub fn encode_trust_ir_extract_bits(ty: Type, lsb: u8, width: u8, operand: SmtExpr) -> SmtExpr {
    let bv_width = ty.bits();
    debug_assert!(
        width >= 1,
        "encode_trust_ir_extract_bits: width must be >= 1"
    );
    debug_assert!(
        (lsb as u32) + (width as u32) <= bv_width,
        "encode_trust_ir_extract_bits: lsb + width must fit in ty.bits()"
    );
    debug_assert_eq!(
        operand.bv_width(),
        bv_width,
        "encode_trust_ir_extract_bits: operand width must match ty.bits()"
    );

    let shifted = operand.bvlshr(SmtExpr::bv_const(lsb as u64, bv_width));
    let mask = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width as u32), bv_width);
    shifted.bvand(mask)
}

/// Encode a trust_ir `SextractBits { lsb, width }` -- signed bitfield extract.
///
/// Semantics: the `width`-bit slice of `operand` starting at bit `lsb` is
/// extracted and sign-extended back to the full operand width:
///
///   result = sign_extend(operand[lsb + width - 1 : lsb])
///
/// On AArch64 this lowers to `SBFM Wd, Wn, #lsb, #(lsb + width - 1)` (see
/// `trust-cg-lower/src/isel.rs::select_bitfield_extract`).
///
/// # Preconditions
///
/// - `width >= 1`
/// - `lsb + width <= ty.bits()`
///
/// Reference: ARM DDI 0487, C6.2.266 SBFM / C6.2.264 SBFX.
pub fn encode_trust_ir_sextract_bits(ty: Type, lsb: u8, width: u8, operand: SmtExpr) -> SmtExpr {
    let bv_width = ty.bits();
    debug_assert!(
        width >= 1,
        "encode_trust_ir_sextract_bits: width must be >= 1"
    );
    debug_assert!(
        (lsb as u32) + (width as u32) <= bv_width,
        "encode_trust_ir_sextract_bits: lsb + width must fit in ty.bits()"
    );
    debug_assert_eq!(
        operand.bv_width(),
        bv_width,
        "encode_trust_ir_sextract_bits: operand width must match ty.bits()"
    );

    let high = lsb as u32 + width as u32 - 1;
    let slice = operand.extract(high, lsb as u32);
    if width as u32 == bv_width {
        slice
    } else {
        slice.sign_ext(bv_width - width as u32)
    }
}

/// Encode a trust_ir `InsertBits { lsb, width }` -- bitfield insert.
///
/// Semantics: replaces bits `[lsb + width - 1 : lsb]` of `dst` with the low
/// `width` bits of `src`, leaving the other bits of `dst` unchanged:
///
///   result = (dst & ~(mask(width) << lsb)) | ((src & mask(width)) << lsb)
///
/// On AArch64 this lowers to a `COPY` of `dst` into the result register
/// followed by `BFM Wd, Ws, #immr, #imms` with `immr = (reg_size - lsb) mod
/// reg_size`, `imms = width - 1` (see
/// `trust-cg-lower/src/isel.rs::select_bitfield_insert`).
///
/// # Preconditions
///
/// - `width >= 1`
/// - `lsb + width <= ty.bits()`
///
/// Reference: ARM DDI 0487, C6.2.46 BFM / C6.2.45 BFI.
pub fn encode_trust_ir_insert_bits(
    ty: Type,
    lsb: u8,
    width: u8,
    dst: SmtExpr,
    src: SmtExpr,
) -> SmtExpr {
    let bv_width = ty.bits();
    debug_assert!(
        width >= 1,
        "encode_trust_ir_insert_bits: width must be >= 1"
    );
    debug_assert!(
        (lsb as u32) + (width as u32) <= bv_width,
        "encode_trust_ir_insert_bits: lsb + width must fit in ty.bits()"
    );
    debug_assert_eq!(
        dst.bv_width(),
        bv_width,
        "encode_trust_ir_insert_bits: dst width must match ty.bits()"
    );
    debug_assert_eq!(
        src.bv_width(),
        bv_width,
        "encode_trust_ir_insert_bits: src width must match ty.bits()"
    );

    let width_mask = crate::smt::mask(u64::MAX, width as u32);
    let shifted_mask = crate::smt::mask(width_mask << lsb, bv_width);
    let inv_mask = crate::smt::mask(!shifted_mask, bv_width);

    let preserved = dst.bvand(SmtExpr::bv_const(inv_mask, bv_width));
    let insert_slice = src
        .bvand(SmtExpr::bv_const(width_mask, bv_width))
        .bvshl(SmtExpr::bv_const(lsb as u64, bv_width));

    preserved.bvor(insert_slice)
}

/// Encode a trust_ir shift operation as an SMT bitvector expression (fallible).
///
/// Returns `Err(SmtError::UnsupportedType)` if the opcode is not a supported
/// shift opcode.
///
/// # Supported opcodes
///
/// - `Opcode::Ishl` -> `bvshl`  (logical shift left)
/// - `Opcode::Ushr` -> `bvlshr` (logical shift right)
/// - `Opcode::Sshr` -> `bvashr` (arithmetic shift right)
///
/// # Shift amount semantics
///
/// On AArch64, shift amounts are masked to the register width (mod 32 for W,
/// mod 64 for X). The SMT `bvshl`/`bvlshr`/`bvashr` operations define the
/// result as zero when the shift amount >= width, which differs slightly.
/// For proofs, we verify equivalence under the assumption that the shift
/// amount is in range [0, width). The trust_ir type system enforces this.
pub fn try_encode_trust_ir_shift(
    opcode: &Opcode,
    _ty: Type,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> Result<SmtExpr, SmtError> {
    match opcode {
        Opcode::Ishl => Ok(lhs.bvshl(rhs)),
        Opcode::Ushr => Ok(lhs.bvlshr(rhs)),
        Opcode::Sshr => Ok(lhs.bvashr(rhs)),
        other => Err(SmtError::UnsupportedType(format!(
            "encode_trust_ir_shift: unsupported opcode {:?}",
            other
        ))),
    }
}

/// Encode a trust_ir shift operation as an SMT bitvector expression.
///
/// Convenience wrapper around [`try_encode_trust_ir_shift`].
///
/// # Panics
///
/// Panics if `opcode` is not a shift opcode.
pub fn encode_trust_ir_shift(opcode: &Opcode, ty: Type, lhs: SmtExpr, rhs: SmtExpr) -> SmtExpr {
    try_encode_trust_ir_shift(opcode, ty, lhs, rhs).expect(
        "encode_trust_ir_shift: unsupported opcode; use try_encode_trust_ir_shift() for fallible encoding",
    )
}

/// Return the precondition for a trust_ir opcode, if any.
///
/// Division and remainder opcodes require `rhs != 0`. Other opcodes have no preconditions.
pub fn precondition(opcode: &Opcode, _ty: Type, _lhs: &SmtExpr, rhs: &SmtExpr) -> Option<SmtExpr> {
    match opcode {
        Opcode::Sdiv | Opcode::Udiv | Opcode::Srem | Opcode::Urem => {
            // Precondition: divisor != 0
            let zero = SmtExpr::bv_const(0, rhs.bv_width());
            Some(rhs.clone().eq_expr(zero).not_expr())
        }
        _ => None,
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

    #[test]
    fn test_encode_iadd() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 3), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(7));
    }

    #[test]
    fn test_encode_isub() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_binop(&Opcode::Isub, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 10), ("b", 3)]));
        assert_eq!(result, EvalResult::Bv(7));
    }

    #[test]
    fn test_encode_imul() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_binop(&Opcode::Imul, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 6), ("b", 7)]));
        assert_eq!(result, EvalResult::Bv(42));
    }

    #[test]
    fn test_encode_neg() {
        let a = symbolic_unary_input(Type::I32);
        let expr = encode_trust_ir_neg(Type::I32, a);
        // neg(5) in 32-bit = 0xFFFFFFFF - 5 + 1 = 0xFFFFFFFB
        let result = expr.eval(&env(&[("a", 5)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFBu64));
    }

    #[test]
    fn test_precondition_div() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let pre = precondition(&Opcode::Sdiv, Type::I32, &a, &b);
        assert!(pre.is_some());
        // b=0 should fail precondition
        let result = pre.unwrap().eval(&env(&[("a", 1), ("b", 0)]));
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_encode_icmp_eq_true() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_icmp(&IntCC::Equal, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 42), ("b", 42)]));
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_icmp_eq_false() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_icmp(&IntCC::Equal, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 42), ("b", 43)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_encode_icmp_slt() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_icmp(&IntCC::SignedLessThan, Type::I32, a, b);
        // -1 < 0 (signed)
        let neg1 = 0xFFFF_FFFFu64;
        let result = expr.eval(&env(&[("a", neg1), ("b", 0)]));
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_icmp_ult() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_icmp(&IntCC::UnsignedLessThan, Type::I32, a, b);
        // 3 <_u 10
        let result = expr.eval(&env(&[("a", 3), ("b", 10)]));
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_icmp_ult_not_less() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_icmp(&IntCC::UnsignedLessThan, Type::I32, a, b);
        // 0xFFFFFFFF is NOT <_u 0 (it's the biggest unsigned value)
        let result = expr.eval(&env(&[("a", 0xFFFF_FFFF), ("b", 0)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_no_precondition_add() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let pre = precondition(&Opcode::Iadd, Type::I32, &a, &b);
        assert!(pre.is_none());
    }

    // -----------------------------------------------------------------------
    // Floating-point semantic encoder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_fadd_f32() {
        let a = SmtExpr::fp32_const(1.5f32);
        let b = SmtExpr::fp32_const(2.5f32);
        let expr = encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F32, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(4.0));
    }

    #[test]
    fn test_encode_fsub_f64() {
        let a = SmtExpr::fp64_const(10.0);
        let b = SmtExpr::fp64_const(3.5);
        let expr = encode_trust_ir_fp_binop(&Opcode::Fsub, Type::F64, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(6.5));
    }

    #[test]
    fn test_encode_fmul_f64() {
        let a = SmtExpr::fp64_const(3.0);
        let b = SmtExpr::fp64_const(7.0);
        let expr = encode_trust_ir_fp_binop(&Opcode::Fmul, Type::F64, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(21.0));
    }

    #[test]
    fn test_encode_fdiv_f64() {
        let a = SmtExpr::fp64_const(10.0);
        let b = SmtExpr::fp64_const(4.0);
        let expr = encode_trust_ir_fp_binop(&Opcode::Fdiv, Type::F64, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(2.5));
    }

    #[test]
    fn test_encode_fneg_f64() {
        let a = SmtExpr::fp64_const(42.0);
        let expr = encode_trust_ir_fneg(Type::F64, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(-42.0));
    }

    #[test]
    fn test_encode_fneg_f32() {
        let a = SmtExpr::fp32_const(-std::f32::consts::PI);
        let expr = encode_trust_ir_fneg(Type::F32, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        // Negation of -PI should be +PI (as f64, with f32 precision)
        assert_eq!(result, EvalResult::Float(std::f32::consts::PI as f64)); // f32 -> f64 precision
    }

    #[test]
    fn test_try_encode_fp_binop_unsupported() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let result = try_encode_trust_ir_fp_binop(&Opcode::Iadd, Type::F64, a, b);
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------------
    // Bitwise semantic encoder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_band() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_bitwise_binop(&Opcode::Band, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 0xFF00_FF00), ("b", 0x0F0F_0F0F)]));
        assert_eq!(result, EvalResult::Bv(0x0F00_0F00));
    }

    #[test]
    fn test_encode_bor() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 0xFF00_0000), ("b", 0x00FF_0000)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_0000));
    }

    #[test]
    fn test_encode_bxor() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_bitwise_binop(&Opcode::Bxor, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 0xAAAA_AAAA), ("b", 0x5555_5555)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_encode_bnot() {
        let a = symbolic_unary_input(Type::I32);
        let expr = encode_trust_ir_bnot(Type::I32, a);
        let result = expr.eval(&env(&[("a", 0)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_encode_bnot_ones() {
        let a = symbolic_unary_input(Type::I32);
        let expr = encode_trust_ir_bnot(Type::I32, a);
        let result = expr.eval(&env(&[("a", 0xFFFF_FFFF)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    // -----------------------------------------------------------------------
    // Shift semantic encoder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_ishl() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_shift(&Opcode::Ishl, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 1), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(16));
    }

    #[test]
    fn test_encode_ushr() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_shift(&Opcode::Ushr, Type::I32, a, b);
        let result = expr.eval(&env(&[("a", 0x8000_0000), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(0x0800_0000));
    }

    #[test]
    fn test_encode_sshr() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let expr = encode_trust_ir_shift(&Opcode::Sshr, Type::I32, a, b);
        // Arithmetic shift right of 0x80000000 by 4 = 0xF8000000 (sign-extends)
        let result = expr.eval(&env(&[("a", 0x8000_0000), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(0xF800_0000));
    }

    #[test]
    fn test_try_encode_bitwise_unsupported() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let result = try_encode_trust_ir_bitwise_binop(&Opcode::Iadd, Type::I32, a, b);
        assert!(result.is_err());
    }

    #[test]
    fn test_try_encode_shift_unsupported() {
        let (a, b) = symbolic_binary_inputs(Type::I32);
        let result = try_encode_trust_ir_shift(&Opcode::Iadd, Type::I32, a, b);
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------------
    // FP comparison (FCMP) semantic encoder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_trust_ir_fcmp_eq_true() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(1.0);
        let expr = encode_trust_ir_fcmp(&FloatCC::Equal, Type::F64, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_trust_ir_fcmp_eq_false() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_trust_ir_fcmp(&FloatCC::Equal, Type::F64, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_encode_trust_ir_fcmp_lt_true() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_trust_ir_fcmp(&FloatCC::LessThan, Type::F64, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_trust_ir_fcmp_gt_true() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(3.0);
        let b = SmtExpr::fp64_const(1.0);
        let expr = encode_trust_ir_fcmp(&FloatCC::GreaterThan, Type::F64, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_trust_ir_fcmp_ordered_no_nan() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_trust_ir_fcmp(&FloatCC::Ordered, Type::F64, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_trust_ir_fcmp_ordered_with_nan() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(f64::NAN);
        let b = SmtExpr::fp64_const(1.0);
        let expr = encode_trust_ir_fcmp(&FloatCC::Ordered, Type::F64, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_encode_trust_ir_fcmp_unordered_with_nan() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(f64::NAN);
        let b = SmtExpr::fp64_const(1.0);
        let expr = encode_trust_ir_fcmp(&FloatCC::Unordered, Type::F64, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_trust_ir_fcmp_unordered_eq_nan() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp64_const(f64::NAN);
        let b = SmtExpr::fp64_const(f64::NAN);
        let expr = encode_trust_ir_fcmp(&FloatCC::UnorderedEqual, Type::F64, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        // NaN should make UnorderedEqual true
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_encode_trust_ir_fcmp_f32() {
        use trust_cg_lower::instructions::FloatCC;
        let a = SmtExpr::fp32_const(1.5f32);
        let b = SmtExpr::fp32_const(2.5f32);
        let expr = encode_trust_ir_fcmp(&FloatCC::LessThan, Type::F32, a, b);
        let result = expr.eval(&std::collections::HashMap::new());
        assert_eq!(result, EvalResult::Bv(1));
    }

    // -----------------------------------------------------------------------
    // Bitfield trust_ir semantics tests (issue #452)
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_trust_ir_extract_bits_i8() {
        // x = 0b1011_0100; lsb=2, width=4 -> 0b0000_1101.
        let a = SmtExpr::var("a", 8);
        let expr = encode_trust_ir_extract_bits(Type::I8, 2, 4, a);
        let result = expr.eval(&env(&[("a", 0b1011_0100)]));
        assert_eq!(result, EvalResult::Bv(0b0000_1101));
    }

    #[test]
    fn test_encode_trust_ir_sextract_bits_i8_negative() {
        // x = 0b0010_1100; lsb=2, width=4 -> slice 0b1011 -> sign-extend to 0xFB.
        let a = SmtExpr::var("a", 8);
        let expr = encode_trust_ir_sextract_bits(Type::I8, 2, 4, a);
        let result = expr.eval(&env(&[("a", 0b0010_1100)]));
        assert_eq!(result, EvalResult::Bv(0xFB));
    }

    #[test]
    fn test_encode_trust_ir_sextract_bits_i8_nonnegative() {
        // x = 0b0001_0100; lsb=2, width=4 -> slice 0b0101 -> extend to 0x05.
        let a = SmtExpr::var("a", 8);
        let expr = encode_trust_ir_sextract_bits(Type::I8, 2, 4, a);
        let result = expr.eval(&env(&[("a", 0b0001_0100)]));
        assert_eq!(result, EvalResult::Bv(0x05));
    }

    #[test]
    fn test_encode_trust_ir_insert_bits_i8() {
        // Wd = 0b1010_1010; Wn = 0b0000_1101; lsb=2, width=4.
        // Expected result: 0b1011_0110 (see `aarch64_semantics::test_bfm_insert_mid_nibble_i8`).
        let d = SmtExpr::var("d", 8);
        let n = SmtExpr::var("n", 8);
        let expr = encode_trust_ir_insert_bits(Type::I8, 2, 4, d, n);
        let result = expr.eval(&env(&[("d", 0b1010_1010), ("n", 0b0000_1101)]));
        assert_eq!(result, EvalResult::Bv(0b1011_0110));
    }
}
