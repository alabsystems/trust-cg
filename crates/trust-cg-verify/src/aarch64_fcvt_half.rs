// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Bit-level value semantics of the four half-precision FCVT forms the
//! AArch64 selector emits (X-OPCODES-P7): `FCVT Sd, Hn`, `FCVT Dd, Hn`,
//! `FCVT Hd, Sn` and `FCVT Hd, Dn`.
//!
//! Two statements of each conversion, written independently of one another
//! and of `fp_bitmodel`:
//!
//! * [`arm_fpconvert`] transcribes the Arm ARM `FPConvert` pseudo-code
//!   (DDI 0487, `shared/functions/float`: `FPUnpackCV`, `FPConvertNaN`,
//!   `FPRoundCV`/`FPRoundBase`). It unpacks the operand to a significand and
//!   the exponent of its leading one, chooses the destination quantum, and
//!   rounds by comparing the discarded fraction with one half, incrementing
//!   with the two carry rules of `FPRoundBase`.
//! * [`ieee_convert_format`] states IEEE 754-2019 `convertFormat` (§5.4.2)
//!   with roundTiesToEven as integer arithmetic on the raw magnitude: an
//!   exact rebias for widening, and add-half-then-truncate over the source
//!   exponent's range cases for narrowing. NaN results follow §6.2.3: the
//!   result is quiet and keeps the high-order payload bits.
//!
//! Both are total functions from the raw source bits to the raw destination
//! bits, as bit-vector `SmtExpr`s, so an obligation comparing them compares
//! exact bit patterns: signed zeros and NaN payloads included.
//!
//! Both assume the FPCR the generated code runs under, which is the Linux and
//! Darwin process default: round to nearest with ties to even, `FZ = 0` (the
//! conversions ignore `FZ16`), `DN = 0` (NaN payloads propagate), `AHP = 0`
//! (IEEE half precision, not the alternative format) and `AH = 0`. Nothing
//! here reads or proves the FPCR value at run time, and FPSR exception flags
//! and floating-point traps are outside the model.

use crate::smt::SmtExpr;

/// An IEEE 754 binary interchange format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IeeeFormat {
    /// binary16.
    Half,
    /// binary32.
    Single,
    /// binary64.
    Double,
}

impl IeeeFormat {
    /// Total width in bits.
    pub const fn bits(self) -> u32 {
        match self {
            Self::Half => 16,
            Self::Single => 32,
            Self::Double => 64,
        }
    }

    /// Exponent field width.
    pub const fn exp_bits(self) -> u32 {
        match self {
            Self::Half => 5,
            Self::Single => 8,
            Self::Double => 11,
        }
    }

    /// Trailing significand (fraction) field width.
    pub const fn frac_bits(self) -> u32 {
        match self {
            Self::Half => 10,
            Self::Single => 23,
            Self::Double => 52,
        }
    }

    /// Exponent bias.
    pub const fn bias(self) -> u32 {
        match self {
            Self::Half => 15,
            Self::Single => 127,
            Self::Double => 1023,
        }
    }

    /// The format an AArch64 scalar FP `ftype`/`opc` field selects: `00`
    /// single, `01` double, `11` half; `10` selects none of them.
    pub const fn from_ftype(ftype: u32) -> Option<Self> {
        match ftype {
            0b00 => Some(Self::Single),
            0b01 => Some(Self::Double),
            0b11 => Some(Self::Half),
            _ => None,
        }
    }
}

/// One of the four conversions between binary16 and binary32/binary64.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum HalfConversion {
    /// binary16 -> binary32 (`FCVT Sd, Hn`), exact.
    HalfToSingle,
    /// binary16 -> binary64 (`FCVT Dd, Hn`), exact.
    HalfToDouble,
    /// binary32 -> binary16 (`FCVT Hd, Sn`), rounded.
    SingleToHalf,
    /// binary64 -> binary16 (`FCVT Hd, Dn`), rounded.
    DoubleToHalf,
}

impl HalfConversion {
    /// Every conversion.
    pub const ALL: [Self; 4] = [
        Self::HalfToSingle,
        Self::HalfToDouble,
        Self::SingleToHalf,
        Self::DoubleToHalf,
    ];

    /// Source format.
    pub const fn source(self) -> IeeeFormat {
        match self {
            Self::HalfToSingle | Self::HalfToDouble => IeeeFormat::Half,
            Self::SingleToHalf => IeeeFormat::Single,
            Self::DoubleToHalf => IeeeFormat::Double,
        }
    }

    /// Destination format.
    pub const fn destination(self) -> IeeeFormat {
        match self {
            Self::HalfToSingle => IeeeFormat::Single,
            Self::HalfToDouble => IeeeFormat::Double,
            Self::SingleToHalf | Self::DoubleToHalf => IeeeFormat::Half,
        }
    }

    /// Whether the conversion widens (and is therefore exact).
    pub const fn widens(self) -> bool {
        matches!(self, Self::HalfToSingle | Self::HalfToDouble)
    }

    /// The conversion between two formats, if it is one of the four.
    pub fn from_formats(source: IeeeFormat, destination: IeeeFormat) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|conv| conv.source() == source && conv.destination() == destination)
    }
}

fn bv(value: u64, width: u32) -> SmtExpr {
    SmtExpr::bv_const(value, width)
}

fn ones(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn is_one(bit: SmtExpr) -> SmtExpr {
    bit.eq_expr(bv(1, 1))
}

fn zext_to(expr: SmtExpr, width: u32) -> SmtExpr {
    let from = expr.bv_width();
    if from == width {
        expr
    } else {
        expr.zero_ext(width - from)
    }
}

/// `sign : exp : frac` with each part already at its field width.
fn pack(sign: SmtExpr, exp: SmtExpr, frac: SmtExpr) -> SmtExpr {
    sign.concat(exp).concat(frac)
}

/// The raw fields of an operand in `format`.
struct Fields {
    sign: SmtExpr,
    exp: SmtExpr,
    frac: SmtExpr,
    is_nan: SmtExpr,
    is_inf: SmtExpr,
    is_zero: SmtExpr,
    exp_zero: SmtExpr,
}

fn fields(format: IeeeFormat, op: &SmtExpr) -> Fields {
    let (n, e, f) = (format.bits(), format.exp_bits(), format.frac_bits());
    let sign = op.clone().extract(n - 1, n - 1);
    let exp = op.clone().extract(n - 2, f);
    let frac = op.clone().extract(f - 1, 0);
    let exp_ones = exp.clone().eq_expr(bv(ones(e), e));
    let exp_zero = exp.clone().eq_expr(bv(0, e));
    let frac_zero = frac.clone().eq_expr(bv(0, f));
    Fields {
        is_nan: exp_ones.clone().and_expr(frac_zero.clone().not_expr()),
        is_inf: exp_ones.and_expr(frac_zero.clone()),
        is_zero: exp_zero.clone().and_expr(frac_zero),
        sign,
        exp,
        frac,
        exp_zero,
    }
}

// ===========================================================================
// Arm ARM FPConvert
// ===========================================================================

/// Width of the signed exponent arithmetic. Every intermediate exponent and
/// shift of the four conversions lies in `-1100..1100`.
const EW: u32 = 16;
/// Width of the significand arithmetic: a binary64 significand is 53 bits and
/// a widened binary16 significand is shifted left by at most 52.
const MW: u32 = 64;

fn exp_const(value: i64) -> SmtExpr {
    bv(value as u64, EW)
}

/// The bit position of the most significant one of a nonzero `frac`, as a
/// signed `EW`-bit value (`FPUnpackCV` normalizes a denormal operand to it).
fn leading_one_position(frac: &SmtExpr, width: u32) -> SmtExpr {
    (0..width).fold(exp_const(0), |lower, bit| {
        SmtExpr::ite(
            is_one(frac.clone().extract(bit, bit)),
            exp_const(i64::from(bit)),
            lower,
        )
    })
}

/// `FPConvert(op, FPCR, FPRounding_TIEEVEN)` for `conv`, over the raw source
/// bits `op`, returning the raw destination bits.
///
/// Transcribed for the default FPCR (see the module documentation):
///
/// * NaN: `FPConvertNaN` — the payload below the quiet bit is left-justified
///   in 51 bits and its top `F - 1` bits become the destination payload under
///   a set quiet bit; the sign is kept.
/// * infinity and zero keep their sign.
/// * otherwise `FPRoundCV` of the exact value: the leading one's exponent
///   selects a normal (biased exponent > 0) or denormal destination quantum,
///   `int_mant` is the value in units of that quantum rounded down, and the
///   discarded `error` is compared with one half, ties going to the even
///   `int_mant`. A round-up to `2^F` promotes a denormal to the smallest
///   normal; a round-up to `2^(F+1)` increments the exponent. A biased
///   exponent of `2^E - 1` or more overflows to infinity.
pub fn arm_fpconvert(conv: HalfConversion, op: &SmtExpr) -> SmtExpr {
    let (src, dst) = (conv.source(), conv.destination());
    let (fs, ed, fd) = (src.frac_bits(), dst.exp_bits(), dst.frac_bits());
    let x = fields(src, op);

    // FPConvertNaN.
    let payload = x.frac.clone().extract(fs - 2, 0);
    let frac51 = if fs - 1 == 51 {
        payload
    } else {
        payload.concat(bv(0, 51 - (fs - 1)))
    };
    let nan_result = pack(
        x.sign.clone(),
        bv(ones(ed), ed),
        bv(1, 1).concat(frac51.extract(50, 51 - (fd - 1))),
    );
    let inf_result = pack(x.sign.clone(), bv(ones(ed), ed), bv(0, fd));
    let zero_result = x.sign.clone().concat(bv(0, ed + fd));

    // Exact value = sig * 2^e_lsb; `exponent` is its leading one's exponent.
    let sig = SmtExpr::ite(
        x.exp_zero.clone(),
        zext_to(x.frac.clone(), MW),
        zext_to(bv(1, 1).concat(x.frac.clone()), MW),
    );
    let biased_src = SmtExpr::ite(x.exp_zero.clone(), exp_const(1), zext_to(x.exp.clone(), EW));
    let e_lsb = biased_src.bvsub(exp_const(i64::from(src.bias() + fs)));
    let lead = SmtExpr::ite(
        x.exp_zero.clone(),
        leading_one_position(&x.frac, fs),
        exp_const(i64::from(fs)),
    );
    let exponent = e_lsb.clone().bvadd(lead);

    // FPRoundBase: minimum_exp = 1 - bias; biased_exp = exponent - minimum_exp + 1.
    let minimum_exp = 1 - i64::from(dst.bias());
    let biased_pre = exponent.clone().bvsub(exp_const(minimum_exp - 1));
    let normal_target = biased_pre.clone().bvsgt(exp_const(0));
    let quantum = SmtExpr::ite(normal_target.clone(), exponent, exp_const(minimum_exp))
        .bvsub(exp_const(i64::from(fd)));
    let shift = quantum.bvsub(e_lsb);
    let exact = shift.clone().bvsle(exp_const(0));
    // shift <= 0: the value is a multiple of the quantum (widening).
    let int_exact = sig
        .clone()
        .bvshl(zext_to(exp_const(0).bvsub(shift.clone()), MW));
    // shift > 0: discard `shift` bits. `sig < 2^53`, so clamping at 64 keeps
    // int_mant = 0 and the half bit = 0 for every larger shift.
    let right = zext_to(
        SmtExpr::ite(shift.clone().bvsgt(exp_const(64)), exp_const(64), shift),
        MW,
    );
    let int_rounded_down = sig.clone().bvlshr(right.clone());
    let below = right.bvsub(bv(1, MW));
    let half = is_one(sig.clone().bvlshr(below.clone()).extract(0, 0));
    let rest_mask = bv(1, MW).bvshl(below).bvsub(bv(1, MW));
    let rest_nonzero = sig.bvand(rest_mask).eq_expr(bv(0, MW)).not_expr();
    let int_mant = SmtExpr::ite(exact.clone(), int_exact, int_rounded_down);
    let round_up = exact
        .not_expr()
        .and_expr(half.and_expr(rest_nonzero.or_expr(is_one(int_mant.clone().extract(0, 0)))));
    let biased = SmtExpr::ite(normal_target, biased_pre, exp_const(0));
    let mant1 = SmtExpr::ite(
        round_up.clone(),
        int_mant.clone().bvadd(bv(1, MW)),
        int_mant,
    );
    let to_normal = round_up
        .clone()
        .and_expr(mant1.clone().eq_expr(bv(1u64 << fd, MW)));
    let to_next = round_up.and_expr(mant1.clone().eq_expr(bv(1u64 << (fd + 1), MW)));
    let biased2 = SmtExpr::ite(
        to_next.clone(),
        biased.clone().bvadd(exp_const(1)),
        SmtExpr::ite(to_normal, exp_const(1), biased),
    );
    let mant2 = SmtExpr::ite(to_next, mant1.clone().bvlshr(bv(1, MW)), mant1);
    let overflow = biased2.clone().bvsge(exp_const(ones(ed) as i64));
    let finite_result = pack(x.sign, biased2.extract(ed - 1, 0), mant2.extract(fd - 1, 0));

    SmtExpr::ite(
        x.is_nan,
        nan_result,
        SmtExpr::ite(
            x.is_inf,
            inf_result.clone(),
            SmtExpr::ite(
                x.is_zero,
                zero_result,
                SmtExpr::ite(overflow, inf_result, finite_result),
            ),
        ),
    )
}

// ===========================================================================
// IEEE 754 convertFormat, and deliberately wrong variants for controls
// ===========================================================================

/// What [`ieee_convert_format_with`] states. [`IeeeClaim::CORRECT`] is the
/// machine-IR intent; every other value is a negative control that a
/// correct `FCVT` word must refute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IeeeClaim {
    pub rounding: ClaimRounding,
    pub nan: ClaimNan,
    /// Flush binary16 denormal operands (widening) or results (narrowing)
    /// to zero, as if `FZ16` governed the conversion.
    pub flush_half_denormals: bool,
    /// Read or write binary16 as the Arm alternative half-precision format
    /// (`FPCR.AHP = 1`): exponent 31 is an ordinary binade, NaN converts to
    /// zero and infinity saturates.
    pub alternative_half: bool,
}

/// Rounding direction of a narrowing claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClaimRounding {
    /// roundTiesToEven (the intent).
    TiesToEven,
    /// roundTiesToAway.
    TiesToAway,
    /// roundTowardZero.
    TowardZero,
}

/// NaN result of a claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClaimNan {
    /// Quiet, sign and high-order payload kept (the intent).
    PropagatePayload,
    /// The default NaN (`FPCR.DN = 1`): positive, quiet, payload zero.
    Default,
}

impl IeeeClaim {
    /// The machine-IR intent of a half-precision `FCVT`.
    pub const CORRECT: Self = Self {
        rounding: ClaimRounding::TiesToEven,
        nan: ClaimNan::PropagatePayload,
        flush_half_denormals: false,
        alternative_half: false,
    };
}

/// IEEE 754 `convertFormat` for `conv` with roundTiesToEven and §6.2.3 NaN
/// propagation, over the raw source bits `op`.
pub fn ieee_convert_format(conv: HalfConversion, op: &SmtExpr) -> SmtExpr {
    ieee_convert_format_with(conv, op, IeeeClaim::CORRECT)
}

/// [`ieee_convert_format`] under `claim`.
pub fn ieee_convert_format_with(conv: HalfConversion, op: &SmtExpr, claim: IeeeClaim) -> SmtExpr {
    if conv.widens() {
        widen_half(conv.destination(), op, claim)
    } else {
        narrow_to_half(conv.source(), op, claim)
    }
}

fn default_nan(format: IeeeFormat) -> SmtExpr {
    let (e, f) = (format.exp_bits(), format.frac_bits());
    bv((ones(e) << f) | (1u64 << (f - 1)), format.bits())
}

/// binary16 -> `dst`, exact.
fn widen_half(dst: IeeeFormat, op: &SmtExpr, claim: IeeeClaim) -> SmtExpr {
    let (n, e, f) = (dst.bits(), dst.exp_bits(), dst.frac_bits());
    let x = fields(IeeeFormat::Half, op);
    let rebias = u64::from(dst.bias() - 15);
    // Magnitude rebias: (h & 0x7fff) << (F - 10), plus (bias_d - 15) << F.
    let magnitude = zext_to(op.clone().extract(14, 0), n - 1);
    let normal_mag = magnitude
        .bvshl(bv(u64::from(f - 10), n - 1))
        .bvadd(bv(rebias << f, n - 1));
    let normal = x.sign.clone().concat(normal_mag);
    // A denormal binary16 `frac * 2^-24` with its leading one at bit p is the
    // normal `2^(p - 24) * (frac / 2^p)`: subtract the leading one and scale
    // the remaining bits up to the destination fraction's top.
    let denormal = (0..10u32).fold(x.sign.clone().concat(bv(0, n - 1)), |smaller, p| {
        let leading = bv(1u64 << p, 10);
        let exp = u64::from(dst.bias()) + u64::from(p) - 24;
        let tail = zext_to(x.frac.clone().bvsub(leading.clone()), f).bvshl(bv(u64::from(f - p), f));
        SmtExpr::ite(
            x.frac.clone().bvuge(leading),
            pack(x.sign.clone(), bv(exp, e), tail),
            smaller,
        )
    });
    let signed_zero = x.sign.clone().concat(bv(0, n - 1));
    let nan = match claim.nan {
        ClaimNan::PropagatePayload => pack(
            x.sign.clone(),
            bv(ones(e), e),
            bv(1, 1)
                .concat(x.frac.clone().extract(8, 0))
                .concat(bv(0, f - 10)),
        ),
        ClaimNan::Default => default_nan(dst),
    };
    let inf = pack(x.sign.clone(), bv(ones(e), e), bv(0, f));
    let exp_31 = x.exp.clone().eq_expr(bv(31, 5));
    let special = if claim.alternative_half {
        // Exponent 31 is the binade [2^16, 2^17): the magnitude rebias covers it.
        normal.clone()
    } else {
        SmtExpr::ite(x.is_nan, nan, inf)
    };
    let denormal = if claim.flush_half_denormals {
        signed_zero.clone()
    } else {
        denormal
    };
    SmtExpr::ite(
        exp_31,
        special,
        SmtExpr::ite(
            x.is_zero,
            signed_zero,
            SmtExpr::ite(x.exp_zero, denormal, normal),
        ),
    )
}

/// Add-half-then-truncate: round `value` right by `shift` bits.
fn round_right(value: SmtExpr, shift: SmtExpr, rounding: ClaimRounding) -> SmtExpr {
    let width = value.bv_width();
    let one = bv(1, width);
    let half = one.clone().bvshl(shift.clone().bvsub(one.clone()));
    let biased = match rounding {
        ClaimRounding::TowardZero => value,
        ClaimRounding::TiesToAway => value.bvadd(half),
        ClaimRounding::TiesToEven => {
            let kept_lsb = value.clone().bvlshr(shift.clone()).bvand(one.clone());
            value.bvadd(half.bvsub(one)).bvadd(kept_lsb)
        }
    };
    biased.bvlshr(shift)
}

/// `src` -> binary16, rounded as `claim` states.
fn narrow_to_half(src: IeeeFormat, op: &SmtExpr, claim: IeeeClaim) -> SmtExpr {
    let f = src.frac_bits();
    let bias = u64::from(src.bias());
    let x = fields(src, op);
    let exp = zext_to(x.exp.clone(), MW);
    let magnitude = zext_to(op.clone().extract(src.bits() - 2, 0), MW);
    let sh = u64::from(f - 10);
    let max_normal = 0x7BFFu64;
    let (top_exp, overflow_mag) = if claim.alternative_half {
        // AHP: exponent 31 is a binade; saturate at the largest AHP value.
        (bias + 16, 0x7FFFu64)
    } else {
        (
            bias + 15,
            match claim.rounding {
                ClaimRounding::TowardZero => max_normal,
                _ => 0x7C00,
            },
        )
    };
    // Normal binary16 range: value in [2^-14, 2^(top_exp - bias + 1)).
    let rebased = magnitude.bvsub(bv((bias - 15) << f, MW));
    let normal_rounded = round_right(rebased, bv(sh, MW), claim.rounding);
    let normal_limit = if claim.alternative_half {
        0x7FFFu64
    } else {
        0x7BFFu64
    };
    let normal_mag = SmtExpr::ite(
        normal_rounded.clone().bvugt(bv(normal_limit, MW)),
        bv(overflow_mag, MW),
        normal_rounded,
    );
    // Denormal binary16 range: value in [2^-25, 2^-14), in units of 2^-24.
    let significand = bv(1u64 << f, MW).bvadd(zext_to(x.frac.clone(), MW));
    let sh2 = bv(bias - 14 + sh, MW).bvsub(exp.clone());
    let denormal_rounded = round_right(significand, sh2, claim.rounding);
    let denormal_mag = if claim.flush_half_denormals {
        // Only a result that rounded to the smallest normal survives a flush.
        SmtExpr::ite(
            denormal_rounded.clone().bvuge(bv(0x400, MW)),
            denormal_rounded,
            bv(0, MW),
        )
    } else {
        denormal_rounded
    };
    let finite_mag = SmtExpr::ite(
        exp.clone().bvugt(bv(top_exp, MW)),
        bv(overflow_mag, MW),
        SmtExpr::ite(
            exp.clone().bvuge(bv(bias - 14, MW)),
            normal_mag,
            SmtExpr::ite(exp.bvuge(bv(bias - 25, MW)), denormal_mag, bv(0, MW)),
        ),
    );
    let finite = x.sign.clone().concat(finite_mag.extract(14, 0));
    let nan = if claim.alternative_half {
        x.sign.clone().concat(bv(0, 15))
    } else {
        match claim.nan {
            ClaimNan::PropagatePayload => x
                .sign
                .clone()
                .concat(bv(0b111111, 6))
                .concat(x.frac.clone().extract(f - 2, f - 10)),
            ClaimNan::Default => default_nan(IeeeFormat::Half),
        }
    };
    let inf = if claim.alternative_half {
        x.sign.clone().concat(bv(0x7FFF, 15))
    } else {
        x.sign.clone().concat(bv(0x7C00, 15))
    };
    SmtExpr::ite(x.is_nan, nan, SmtExpr::ite(x.is_inf, inf, finite))
}

// ===========================================================================
// Structured boundary battery
// ===========================================================================

/// Source bit patterns at which a narrowing conversion's rounding decisions
/// change: for binary16 results across every binade (normal and denormal),
/// the exact values, the halfway points between neighbours and one source ulp
/// either side of them, with both signs; the overflow and underflow
/// thresholds; the largest and smallest source values; signed zeros,
/// infinities and quiet and signaling NaNs with payload bits above and below
/// the ten the result keeps. For a widening source it is every binary16.
///
/// Random sampling almost never reaches an exact tie of a binary32 or
/// binary64 source (the discarded bits would all have to be `100...0`), so a
/// rounding-direction error survives sampling; this battery reaches every
/// kind of tie deterministically. It is a finite test set, not a proof.
pub fn half_conversion_battery(conv: HalfConversion) -> Vec<u64> {
    if conv.widens() {
        return (0..=u16::MAX).map(u64::from).collect();
    }
    let src = conv.source();
    let f = src.frac_bits();
    let sh = f - 10;
    let bias = u64::from(src.bias());
    let sign_bit = 1u64 << (src.bits() - 1);
    let exp_mask = ones(src.exp_bits()) << f;
    let mut magnitudes: Vec<u64> = Vec::new();
    // Every binary16 finite magnitude k in a spread of fractions, re-expressed
    // in the source format, and its halfway point to k + 1.
    let fractions: [u64; 9] = [0, 1, 2, 3, 0x155, 0x200, 0x2AA, 0x3FE, 0x3FF];
    for half_exp in 0..=30u64 {
        for &frac in &fractions {
            let k = (half_exp << 10) | frac;
            let exact = widen_half_magnitude(src, k);
            let next = widen_half_magnitude(src, k + 1);
            let mid = (exact + next) / 2; // exact: both lie on one binade's grid or adjacent ones
            for value in [exact, mid] {
                magnitudes.extend([value, value.wrapping_sub(1), value + 1]);
            }
        }
    }
    // Deep underflow and the zero/denormal-result boundary: 2^-25 and 2^-26.
    for unbiased in [-25i64, -26, -27, -30, -60] {
        let e = (bias as i64 + unbiased) as u64;
        let base = e << f;
        magnitudes.extend([base, base - 1, base + 1, base | (1 << (f - 1))]);
    }
    // Overflow: 65504 (max), 65520 (the tie to infinity), 2^16, the largest
    // finite source value, source denormals and zero.
    let tie_to_inf = ((bias + 15) << f) | (0x3FF << sh) | (1 << (sh - 1));
    magnitudes.extend([
        tie_to_inf,
        tie_to_inf - 1,
        tie_to_inf + 1,
        (bias + 16) << f,
        exp_mask - 1,
        1,
        (1 << f) - 1,
        0,
    ]);
    // Infinity and NaNs: quiet and signaling, payload bits kept and dropped.
    let quiet = 1u64 << (f - 1);
    magnitudes.extend([
        exp_mask,
        exp_mask | quiet,
        exp_mask | 1,
        exp_mask | quiet | 1,
        exp_mask | (1 << sh),
        exp_mask | (ones(f) & !quiet),
        exp_mask | ones(f),
        exp_mask | (0x155 << sh),
    ]);
    let mut battery = Vec::with_capacity(magnitudes.len() * 2);
    for magnitude in magnitudes {
        let magnitude = magnitude & (sign_bit - 1);
        battery.push(magnitude);
        battery.push(magnitude | sign_bit);
    }
    battery.sort_unstable();
    battery.dedup();
    battery
}

/// The source-format bits of the binary16 magnitude `k` (`k <= 0x7C00`),
/// computed with the integer rebias; a denormal `k` becomes a normal source.
fn widen_half_magnitude(src: IeeeFormat, k: u64) -> u64 {
    let f = src.frac_bits();
    let bias = u64::from(src.bias());
    let (exp, frac) = (k >> 10, k & 0x3FF);
    if exp == 0 {
        if frac == 0 {
            return 0;
        }
        let p = 63 - u64::from(frac.leading_zeros());
        let e = bias + p - 24;
        return (e << f) | (((frac - (1 << p)) << (u64::from(f) - p)) & ones(f));
    }
    ((exp + bias - 15) << f) | (frac << (f - 10))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fp_bitmodel;
    use crate::smt::{EvalEnv, EvalResult};

    fn eval(expr: &SmtExpr, name: &str, value: u64) -> u64 {
        let mut env = EvalEnv::default();
        env.insert(name.to_string(), value);
        match expr.try_eval(&env).expect("evaluates") {
            EvalResult::Bv(bits) => bits,
            other => panic!("unexpected {other:?}"),
        }
    }

    fn bitmodel(conv: HalfConversion, x: u64) -> u64 {
        match conv {
            HalfConversion::HalfToSingle => fp_bitmodel::fcvt_h_to_s(x),
            HalfConversion::HalfToDouble => fp_bitmodel::fcvt_h_to_d(x),
            HalfConversion::SingleToHalf => fp_bitmodel::fcvt_s_to_h(x),
            HalfConversion::DoubleToHalf => fp_bitmodel::fcvt_d_to_h(x),
        }
    }

    /// Both statements agree with each other and with the silicon-validated
    /// integer bit model: every binary16 for the widening forms, the whole
    /// boundary battery for the narrowing forms.
    #[test]
    fn arm_and_ieee_statements_agree_with_the_bit_model() {
        for conv in HalfConversion::ALL {
            let var = SmtExpr::var("x", conv.source().bits());
            let arm = arm_fpconvert(conv, &var);
            let ieee = ieee_convert_format(conv, &var);
            assert_eq!(arm.bv_width(), conv.destination().bits());
            assert_eq!(ieee.bv_width(), conv.destination().bits());
            let battery = half_conversion_battery(conv);
            assert!(battery.len() > 500, "{conv:?}: {}", battery.len());
            for x in battery {
                let want = bitmodel(conv, x);
                assert_eq!(eval(&arm, "x", x), want, "{conv:?} arm x={x:#x}");
                assert_eq!(eval(&ieee, "x", x), want, "{conv:?} ieee x={x:#x}");
            }
        }
    }

    /// The narrowing battery reaches exact ties that round each way, the
    /// overflow tie and a payload-truncating NaN.
    #[test]
    fn narrowing_battery_reaches_every_rounding_situation() {
        for conv in [HalfConversion::SingleToHalf, HalfConversion::DoubleToHalf] {
            let src = conv.source();
            let f = src.frac_bits();
            let battery = half_conversion_battery(conv);
            let tie_bits = 1u64 << (f - 11);
            let is_tie = |x: u64| {
                let exp = (x >> f) & ones(src.exp_bits());
                let normal_half =
                    exp >= u64::from(src.bias()) - 14 && exp <= u64::from(src.bias()) + 15;
                normal_half && x & ones(f - 10) == tie_bits
            };
            let ties_up = battery
                .iter()
                .filter(|&&x| is_tie(x) && (x >> (f - 10)) & 1 == 1)
                .count();
            let ties_down = battery
                .iter()
                .filter(|&&x| is_tie(x) && (x >> (f - 10)) & 1 == 0)
                .count();
            assert!(
                ties_up > 20 && ties_down > 20,
                "{conv:?}: {ties_up}/{ties_down}"
            );
            assert!(battery.iter().any(|&x| bitmodel(conv, x) == 0x7C00
                && x & (1 << (src.bits() - 1)) == 0
                && (x >> f) & ones(src.exp_bits()) == u64::from(src.bias()) + 15));
            assert!(battery.iter().any(|&x| {
                let r = bitmodel(conv, x);
                r & 0x7C00 == 0 && r & 0x3FF != 0
            }));
        }
    }

    /// Every deliberately wrong claim differs from the correct one at some
    /// battery point, so none of the controls is vacuous by construction.
    #[test]
    fn every_wrong_claim_is_distinguished_on_the_battery() {
        let wrong = [
            IeeeClaim {
                rounding: ClaimRounding::TowardZero,
                ..IeeeClaim::CORRECT
            },
            IeeeClaim {
                rounding: ClaimRounding::TiesToAway,
                ..IeeeClaim::CORRECT
            },
            IeeeClaim {
                nan: ClaimNan::Default,
                ..IeeeClaim::CORRECT
            },
            IeeeClaim {
                flush_half_denormals: true,
                ..IeeeClaim::CORRECT
            },
            IeeeClaim {
                alternative_half: true,
                ..IeeeClaim::CORRECT
            },
        ];
        for conv in HalfConversion::ALL {
            let var = SmtExpr::var("x", conv.source().bits());
            let correct = ieee_convert_format(conv, &var);
            let battery = half_conversion_battery(conv);
            for claim in wrong {
                if conv.widens() && claim.rounding != ClaimRounding::TiesToEven {
                    continue; // widening is exact: rounding claims coincide
                }
                let mutated = ieee_convert_format_with(conv, &var, claim);
                assert!(
                    battery
                        .iter()
                        .any(|&x| eval(&correct, "x", x) != eval(&mutated, "x", x)),
                    "{conv:?}: {claim:?} is indistinguishable on the battery"
                );
            }
        }
    }

    /// Widening is exact, so every rounding claim states the same function.
    #[test]
    fn widening_ignores_the_rounding_claim() {
        for conv in [HalfConversion::HalfToSingle, HalfConversion::HalfToDouble] {
            let var = SmtExpr::var("x", 16);
            let correct = ieee_convert_format(conv, &var);
            for rounding in [ClaimRounding::TowardZero, ClaimRounding::TiesToAway] {
                let claim = IeeeClaim {
                    rounding,
                    ..IeeeClaim::CORRECT
                };
                let other = ieee_convert_format_with(conv, &var, claim);
                for x in (0..=u16::MAX).step_by(97) {
                    assert_eq!(
                        eval(&correct, "x", u64::from(x)),
                        eval(&other, "x", u64::from(x))
                    );
                }
            }
        }
    }

    /// Random binary32/binary64 sources agree with the bit model too.
    #[test]
    fn narrowing_agrees_with_the_bit_model_on_random_sources() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        for conv in [HalfConversion::SingleToHalf, HalfConversion::DoubleToHalf] {
            let bits = conv.source().bits();
            let var = SmtExpr::var("x", bits);
            let arm = arm_fpconvert(conv, &var);
            let ieee = ieee_convert_format(conv, &var);
            for _ in 0..20_000 {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                // Bias half of the samples into the binary16 exponent window.
                let x = if state & 1 == 0 {
                    state & ones(bits)
                } else {
                    let f = conv.source().frac_bits();
                    let bias = u64::from(conv.source().bias());
                    let exp = bias - 26 + (state >> 58) % 44;
                    (state & (1 << (bits - 1))) | (exp << f) | ((state >> 3) & ones(f))
                };
                let want = bitmodel(conv, x);
                assert_eq!(eval(&arm, "x", x), want, "{conv:?} arm x={x:#x}");
                assert_eq!(eval(&ieee, "x", x), want, "{conv:?} ieee x={x:#x}");
            }
        }
    }
}
