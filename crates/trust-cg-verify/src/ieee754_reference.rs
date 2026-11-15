// trust-cg-verify/ieee754_reference.rs - independent IEEE 754 reference
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! An independent reference for IEEE 754-2019 binary16, binary32 and
//! binary64 arithmetic, rounding and conversions, written for ledger
//! `L04-P3` as the third party of a three-way differential: the verifier's
//! semantic models ([`crate::aarch64_semantics`] evaluated by
//! [`crate::smt::SmtExpr::try_eval`]), the instruction executed on the host
//! CPU, and this module.
//!
//! # Independence
//!
//! Every function here works on raw bit patterns with integer arithmetic only.
//! Nothing here performs a host floating-point operation, converts through
//! `f32`/`f64`, or calls [`crate::fp_bitmodel`], [`crate::aarch64_fcvt_half`] or
//! the SMT evaluator. The construction is deliberately the simplest one that is
//! obviously exact:
//!
//! * an operand is unpacked to `(-1)^neg * mag * 2^exp` with an integer `mag`;
//! * every operation computes its exact result in that form, except that a sum
//!   whose terms are so far apart that the smaller one cannot fit beside the
//!   larger in 128 bits keeps only a STICKY bit for the smaller one (it lies
//!   strictly below every rounding boundary of the result, see [`sum_terms`]),
//!   and a quotient or square root keeps its integer part plus a sticky bit for
//!   a nonzero remainder;
//! * one routine, [`round_pack`], rounds such a value to a format in a rounding
//!   direction and computes the exception flags.
//!
//! # Semantics
//!
//! The IEEE 754 choices the standard leaves open follow the Arm Architecture
//! Reference Manual (DDI 0487) pseudo-code under the default FPCR of an Apple
//! or Linux AArch64 process: round to nearest even, `FZ = FZ16 = 0` (subnormal
//! operands and results are honored), `DN = 0` (NaN payloads propagate),
//! `AH = 0` and `AHP = 0` (IEEE half precision). Concretely:
//!
//! * NaN propagation is `FPProcessNaNs`: the first signaling NaN in operand
//!   order, quieted, else the first quiet NaN; operations that create a NaN
//!   return the default NaN (positive, quiet, zero payload). For the fused
//!   multiply-add the order is addend, multiplicand, multiplier (`FPMulAdd`),
//!   and `qNaN + inf * 0` is the default NaN with Invalid Operation.
//! * Tininess is detected BEFORE rounding (`FPRoundBase` with `AH = 0`), so
//!   Underflow is raised for a tiny inexact result even when it rounds to the
//!   smallest normal number.
//! * `FPConvertNaN` keeps the high-order payload bits on narrowing and pads with
//!   zeros on widening.
//! * Float-to-integer conversion saturates and maps NaN to zero, raising Invalid
//!   Operation for NaN and for every saturated result and Inexact only for an
//!   in-range result that was rounded (`FPToFixed`); that is also Rust's
//!   saturating `as` cast at any destination width, which TrustIR's
//!   `FPToSISat`/`FPToUISat` name.
//!
//! Flags use the Arm FPSR cumulative-bit positions ([`Flags`]), so a flag set
//! compares directly with `FPSR[4:0]`.
//!
//! # Evidence boundary
//!
//! This is a reference written by hand. Its agreement with the CPU and with the
//! verifier models is testing evidence over the inputs that were run; nothing
//! here is a proof, and nothing in the proof database cites it.

use std::cmp::Ordering;

/// An IEEE 754 binary interchange format.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Format {
    /// binary16 (`H` registers).
    Half,
    /// binary32 (`S` registers).
    Single,
    /// binary64 (`D` registers).
    Double,
}

impl Format {
    /// Every format, narrowest first.
    pub const ALL: [Format; 3] = [Format::Half, Format::Single, Format::Double];

    /// Total width in bits.
    pub const fn width(self) -> u32 {
        match self {
            Format::Half => 16,
            Format::Single => 32,
            Format::Double => 64,
        }
    }

    /// Exponent field width.
    pub const fn exp_bits(self) -> u32 {
        match self {
            Format::Half => 5,
            Format::Single => 8,
            Format::Double => 11,
        }
    }

    /// Trailing significand field width.
    pub const fn frac_bits(self) -> u32 {
        self.width() - 1 - self.exp_bits()
    }

    /// Precision `p` (significand bits including the implicit bit).
    pub const fn precision(self) -> u32 {
        self.frac_bits() + 1
    }

    /// Exponent bias.
    pub const fn bias(self) -> i32 {
        (1 << (self.exp_bits() - 1)) - 1
    }

    /// Exponent of the smallest normal number.
    pub const fn emin(self) -> i32 {
        1 - self.bias()
    }

    /// Exponent of the largest finite number.
    pub const fn emax(self) -> i32 {
        self.bias()
    }

    /// Mask of the format's bits.
    pub const fn mask(self) -> u64 {
        if self.width() == 64 {
            u64::MAX
        } else {
            (1u64 << self.width()) - 1
        }
    }

    /// The sign bit.
    pub const fn sign_bit(self) -> u64 {
        1u64 << (self.width() - 1)
    }

    /// The exponent field, all ones, in position.
    pub const fn exp_mask(self) -> u64 {
        ((1u64 << self.exp_bits()) - 1) << self.frac_bits()
    }

    /// The trailing significand field.
    pub const fn frac_mask(self) -> u64 {
        (1u64 << self.frac_bits()) - 1
    }

    /// The quiet bit of a NaN (the top trailing-significand bit).
    pub const fn quiet_bit(self) -> u64 {
        1u64 << (self.frac_bits() - 1)
    }

    /// The Arm default NaN: positive, quiet, zero payload.
    pub const fn default_nan(self) -> u64 {
        self.exp_mask() | self.quiet_bit()
    }

    /// Signed infinity.
    pub const fn infinity(self, neg: bool) -> u64 {
        self.exp_mask() | if neg { self.sign_bit() } else { 0 }
    }

    /// Signed largest finite number.
    pub const fn max_finite(self, neg: bool) -> u64 {
        (self.exp_mask() - (1u64 << self.frac_bits()))
            | self.frac_mask()
            | if neg { self.sign_bit() } else { 0 }
    }

    /// Signed zero.
    pub const fn zero(self, neg: bool) -> u64 {
        if neg { self.sign_bit() } else { 0 }
    }

    /// Short name (`f16`, `f32`, `f64`).
    pub const fn name(self) -> &'static str {
        match self {
            Format::Half => "f16",
            Format::Single => "f32",
            Format::Double => "f64",
        }
    }
}

/// A rounding direction attribute (IEEE 754-2019 §4.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Rounding {
    /// roundTiesToEven (FPCR.RMode = RN, FRINTN, the default).
    TiesToEven,
    /// roundTiesToAway (FRINTA, FCVTAS).
    TiesToAway,
    /// roundTowardZero (FRINTZ, FCVTZS).
    TowardZero,
    /// roundTowardPositive (FRINTP).
    TowardPositive,
    /// roundTowardNegative (FRINTM).
    TowardNegative,
}

impl Rounding {
    /// Every rounding direction.
    pub const ALL: [Rounding; 5] = [
        Rounding::TiesToEven,
        Rounding::TiesToAway,
        Rounding::TowardZero,
        Rounding::TowardPositive,
        Rounding::TowardNegative,
    ];
}

/// IEEE 754 exception flags, at the Arm FPSR cumulative-bit positions.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Flags(pub u8);

impl Flags {
    /// No exception.
    pub const NONE: Flags = Flags(0);
    /// Invalid Operation (FPSR.IOC, bit 0).
    pub const INVALID: Flags = Flags(1 << 0);
    /// Division by Zero (FPSR.DZC, bit 1).
    pub const DIV_BY_ZERO: Flags = Flags(1 << 1);
    /// Overflow (FPSR.OFC, bit 2).
    pub const OVERFLOW: Flags = Flags(1 << 2);
    /// Underflow (FPSR.UFC, bit 3).
    pub const UNDERFLOW: Flags = Flags(1 << 3);
    /// Inexact (FPSR.IXC, bit 4).
    pub const INEXACT: Flags = Flags(1 << 4);

    /// The raw FPSR-position bits.
    pub const fn bits(self) -> u8 {
        self.0
    }

    /// The union of two flag sets.
    pub const fn union(self, other: Flags) -> Flags {
        Flags(self.0 | other.0)
    }

    /// Whether every flag of `other` is set.
    pub const fn contains(self, other: Flags) -> bool {
        self.0 & other.0 == other.0
    }
}

impl std::fmt::Display for Flags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const NAMES: [(Flags, &str); 5] = [
            (Flags::INVALID, "IOC"),
            (Flags::DIV_BY_ZERO, "DZC"),
            (Flags::OVERFLOW, "OFC"),
            (Flags::UNDERFLOW, "UFC"),
            (Flags::INEXACT, "IXC"),
        ];
        let set: Vec<&str> = NAMES
            .iter()
            .filter(|(flag, _)| self.contains(*flag))
            .map(|(_, name)| *name)
            .collect();
        if set.is_empty() {
            f.write_str("-")
        } else {
            f.write_str(&set.join("|"))
        }
    }
}

/// A result value with the exception flags its computation raised.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Outcome<T> {
    /// The result (raw bits of the destination format, or an integer).
    pub value: T,
    /// The exception flags raised.
    pub flags: Flags,
}

impl<T> Outcome<T> {
    const fn exact(value: T) -> Self {
        Outcome {
            value,
            flags: Flags::NONE,
        }
    }

    const fn with(value: T, flags: Flags) -> Self {
        Outcome { value, flags }
    }
}

/// The IEEE 754 class of an encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Class {
    /// A zero of either sign.
    Zero,
    /// A subnormal number.
    Subnormal,
    /// A normal number.
    Normal,
    /// An infinity.
    Infinity,
    /// A quiet NaN.
    QuietNan,
    /// A signaling NaN.
    SignalingNan,
}

/// The class of `bits` in `fmt`.
pub fn classify(fmt: Format, bits: u64) -> Class {
    let bits = bits & fmt.mask();
    let exp = bits & fmt.exp_mask();
    let frac = bits & fmt.frac_mask();
    if exp == fmt.exp_mask() {
        if frac == 0 {
            Class::Infinity
        } else if frac & fmt.quiet_bit() != 0 {
            Class::QuietNan
        } else {
            Class::SignalingNan
        }
    } else if exp == 0 {
        if frac == 0 {
            Class::Zero
        } else {
            Class::Subnormal
        }
    } else {
        Class::Normal
    }
}

/// Whether `bits` is a NaN of either kind.
pub fn is_nan(fmt: Format, bits: u64) -> bool {
    matches!(classify(fmt, bits), Class::QuietNan | Class::SignalingNan)
}

/// An unpacked operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operand {
    Nan,
    Inf {
        neg: bool,
    },
    /// `(-1)^neg * mag * 2^exp`; `mag == 0` is a signed zero.
    Finite {
        neg: bool,
        mag: u128,
        exp: i32,
    },
}

fn unpack(fmt: Format, bits: u64) -> Operand {
    let bits = bits & fmt.mask();
    let neg = bits & fmt.sign_bit() != 0;
    let biased = ((bits & fmt.exp_mask()) >> fmt.frac_bits()) as i32;
    let frac = u128::from(bits & fmt.frac_mask());
    let all_ones = (1i32 << fmt.exp_bits()) - 1;
    let frac_bits = fmt.frac_bits() as i32;
    if biased == all_ones {
        if frac == 0 {
            Operand::Inf { neg }
        } else {
            Operand::Nan
        }
    } else if biased == 0 {
        Operand::Finite {
            neg,
            mag: frac,
            exp: fmt.emin() - frac_bits,
        }
    } else {
        Operand::Finite {
            neg,
            mag: frac | (1u128 << frac_bits),
            exp: biased - fmt.bias() - frac_bits,
        }
    }
}

fn negate(op: Operand) -> Operand {
    match op {
        Operand::Nan => Operand::Nan,
        Operand::Inf { neg } => Operand::Inf { neg: !neg },
        Operand::Finite { neg, mag, exp } => Operand::Finite {
            neg: !neg,
            mag,
            exp,
        },
    }
}

fn is_zero(op: Operand) -> bool {
    matches!(op, Operand::Finite { mag: 0, .. })
}

fn is_inf(op: Operand) -> bool {
    matches!(op, Operand::Inf { .. })
}

fn sign_of(op: Operand) -> bool {
    match op {
        Operand::Nan => false,
        Operand::Inf { neg } | Operand::Finite { neg, .. } => neg,
    }
}

fn bit_len(x: u128) -> u32 {
    128 - x.leading_zeros()
}

/// The quieted form of a NaN (`FPProcessNaN` with `DN = 0`).
pub fn quiet(fmt: Format, bits: u64) -> u64 {
    (bits & fmt.mask()) | fmt.quiet_bit()
}

/// `FPProcessNaNs` over `ops` in order: the first signaling NaN quieted (with
/// Invalid Operation), else the first quiet NaN, else `None`.
fn process_nans(fmt: Format, ops: &[u64]) -> Option<Outcome<u64>> {
    if let Some(&snan) = ops
        .iter()
        .find(|&&op| classify(fmt, op) == Class::SignalingNan)
    {
        return Some(Outcome::with(quiet(fmt, snan), Flags::INVALID));
    }
    ops.iter()
        .find(|&&op| classify(fmt, op) == Class::QuietNan)
        .map(|&qnan| Outcome::exact(qnan & fmt.mask()))
}

fn invalid(fmt: Format) -> Outcome<u64> {
    Outcome::with(fmt.default_nan(), Flags::INVALID)
}

/// Round `(-1)^neg * value * 2^exp` to `fmt` in direction `rm`, where `value`
/// is `mag` exactly when `sticky` is false and lies strictly between `mag` and
/// `mag + 1` when it is true. `mag` must be nonzero.
///
/// With `sticky` set the caller must leave at least one bit below the rounding
/// position (the result quantum must exceed `2^exp`); every caller keeps at
/// least `precision + 1` significant bits in `mag` for that reason, and the
/// routine asserts it.
fn round_pack(
    fmt: Format,
    neg: bool,
    mag: u128,
    exp: i32,
    sticky: bool,
    rm: Rounding,
) -> Outcome<u64> {
    assert!(mag != 0, "round_pack of an exact zero");
    let p = fmt.precision() as i32;
    // floor(log2 |value|): exact even with the sticky bit, which never reaches
    // the next power of two.
    let top = bit_len(mag) as i32 - 1 + exp;
    let tiny = top < fmt.emin();
    let quantum_min = fmt.emin() - (p - 1);
    let quantum = (top - (p - 1)).max(quantum_min);
    let (kept, half_cmp, inexact) = if quantum <= exp {
        assert!(!sticky, "sticky bit at or above the rounding position");
        (mag << (exp - quantum), Ordering::Less, false)
    } else {
        let shift = (quantum - exp) as u32;
        let (kept, rem, half) = if shift >= 129 {
            // Everything is far below half a quantum (mag < 2^128 <= half).
            (0, mag, None)
        } else if shift == 128 {
            (0, mag, Some(1u128 << 127))
        } else {
            (
                mag >> shift,
                mag & ((1u128 << shift) - 1),
                Some(1u128 << (shift - 1)),
            )
        };
        let half_cmp = match half {
            None => Ordering::Less,
            Some(half) => match rem.cmp(&half) {
                Ordering::Equal if sticky => Ordering::Greater,
                other => other,
            },
        };
        (kept, half_cmp, rem != 0 || sticky)
    };
    let round_up = match rm {
        Rounding::TiesToEven => {
            half_cmp == Ordering::Greater || (half_cmp == Ordering::Equal && kept & 1 == 1)
        }
        Rounding::TiesToAway => half_cmp != Ordering::Less,
        Rounding::TowardZero => false,
        Rounding::TowardPositive => inexact && !neg,
        Rounding::TowardNegative => inexact && neg,
    };
    let mut sig = kept + u128::from(round_up);
    let mut quantum = quantum;
    if sig == 1u128 << p {
        // Rounding carried into the next binade.
        sig >>= 1;
        quantum += 1;
    }
    let mut flags = Flags::NONE;
    if inexact {
        flags = flags.union(Flags::INEXACT);
        if tiny {
            flags = flags.union(Flags::UNDERFLOW);
        }
    }
    let sign = fmt.zero(neg);
    if sig == 0 {
        return Outcome::with(sign, flags);
    }
    if sig < 1u128 << (p - 1) {
        assert_eq!(quantum, quantum_min, "subnormal significand above emin");
        return Outcome::with(sign | sig as u64, flags);
    }
    let e = quantum + p - 1;
    if e > fmt.emax() {
        let to_infinity = match rm {
            Rounding::TiesToEven | Rounding::TiesToAway => true,
            Rounding::TowardZero => false,
            Rounding::TowardPositive => !neg,
            Rounding::TowardNegative => neg,
        };
        let value = if to_infinity {
            fmt.infinity(neg)
        } else {
            fmt.max_finite(neg)
        };
        return Outcome::with(value, flags.union(Flags::OVERFLOW).union(Flags::INEXACT));
    }
    let biased = (e + fmt.bias()) as u64;
    let frac = (sig as u64) & fmt.frac_mask();
    Outcome::with(sign | (biased << fmt.frac_bits()) | frac, flags)
}

/// A signed value `(-1)^neg * mag * 2^exp`, exact unless `sticky`, in which
/// case the true magnitude lies strictly between `mag` and `mag + 1` units.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Wide {
    neg: bool,
    mag: u128,
    exp: i32,
    sticky: bool,
}

/// The sum of two signed terms of at most 106 significant bits each.
///
/// The term whose leading bit is higher is shifted so its leading bit sits at
/// bit 125 (two bits of headroom for the carry); the other is aligned to the
/// same exponent. When that alignment would drop nonzero bits of the smaller
/// term, those bits are below bit 0 while the result keeps at least 124
/// significant bits, so only "nonzero" matters for rounding to at most 53 bits:
/// the true sum lies strictly between two adjacent integers there, neither of
/// which is a rounding boundary, and the pair is returned as `mag` plus the
/// sticky bit. Otherwise the sum is exact.
fn sum_terms(neg1: bool, m1: u128, e1: i32, neg2: bool, m2: u128, e2: i32) -> Wide {
    debug_assert!(bit_len(m1) <= 106 && bit_len(m2) <= 106);
    if m1 == 0 {
        return Wide {
            neg: neg2,
            mag: m2,
            exp: e2,
            sticky: false,
        };
    }
    if m2 == 0 {
        return Wide {
            neg: neg1,
            mag: m1,
            exp: e1,
            sticky: false,
        };
    }
    let top1 = bit_len(m1) as i32 - 1 + e1;
    let top2 = bit_len(m2) as i32 - 1 + e2;
    let ((nd, md, ed), (no, mo, eo)) = if top1 >= top2 {
        ((neg1, m1, e1), (neg2, m2, e2))
    } else {
        ((neg2, m2, e2), (neg1, m1, e1))
    };
    let shift = 125 - (bit_len(md) as i32 - 1);
    let exp = ed - shift;
    let big_d = md << shift;
    let (big_o, sticky) = if eo >= exp {
        (mo << (eo - exp), false)
    } else {
        let drop = (exp - eo) as u32;
        if drop >= 128 {
            (0, true)
        } else {
            (mo >> drop, mo & ((1u128 << drop) - 1) != 0)
        }
    };
    if nd == no {
        Wide {
            neg: nd,
            mag: big_d + big_o,
            exp,
            sticky,
        }
    } else if !sticky {
        match big_d.cmp(&big_o) {
            Ordering::Less => Wide {
                neg: no,
                mag: big_o - big_d,
                exp,
                sticky: false,
            },
            _ => Wide {
                neg: nd,
                mag: big_d - big_o,
                exp,
                sticky: false,
            },
        }
    } else {
        // big_d >= 2^125 > big_o + 1: the true difference is in
        // (big_d - big_o - 1, big_d - big_o).
        Wide {
            neg: nd,
            mag: big_d - big_o - 1,
            exp,
            sticky: true,
        }
    }
}

fn round_wide(fmt: Format, wide: Wide, rm: Rounding) -> Outcome<u64> {
    if wide.mag == 0 && !wide.sticky {
        // An exact zero sum of nonzero terms: +0, or -0 rounding downward.
        return Outcome::exact(fmt.zero(rm == Rounding::TowardNegative));
    }
    round_pack(fmt, wide.neg, wide.mag, wide.exp, wide.sticky, rm)
}

fn add_impl(fmt: Format, a: u64, b: u64, negate_b: bool, rm: Rounding) -> Outcome<u64> {
    if let Some(nan) = process_nans(fmt, &[a, b]) {
        return nan;
    }
    let x = unpack(fmt, a);
    let y = if negate_b {
        negate(unpack(fmt, b))
    } else {
        unpack(fmt, b)
    };
    match (x, y) {
        (Operand::Inf { neg: n1 }, Operand::Inf { neg: n2 }) => {
            if n1 != n2 {
                invalid(fmt)
            } else {
                Outcome::exact(fmt.infinity(n1))
            }
        }
        (Operand::Inf { neg }, _) | (_, Operand::Inf { neg }) => Outcome::exact(fmt.infinity(neg)),
        (
            Operand::Finite {
                neg: n1,
                mag: m1,
                exp: e1,
            },
            Operand::Finite {
                neg: n2,
                mag: m2,
                exp: e2,
            },
        ) => {
            if m1 == 0 && m2 == 0 {
                let neg = if n1 == n2 {
                    n1
                } else {
                    rm == Rounding::TowardNegative
                };
                return Outcome::exact(fmt.zero(neg));
            }
            round_wide(fmt, sum_terms(n1, m1, e1, n2, m2, e2), rm)
        }
        _ => unreachable!("NaN operands were processed"),
    }
}

/// `a + b` (FADD).
pub fn add(fmt: Format, a: u64, b: u64, rm: Rounding) -> Outcome<u64> {
    add_impl(fmt, a, b, false, rm)
}

/// `a - b` (FSUB).
pub fn sub(fmt: Format, a: u64, b: u64, rm: Rounding) -> Outcome<u64> {
    add_impl(fmt, a, b, true, rm)
}

/// `a * b` (FMUL).
pub fn mul(fmt: Format, a: u64, b: u64, rm: Rounding) -> Outcome<u64> {
    if let Some(nan) = process_nans(fmt, &[a, b]) {
        return nan;
    }
    let (x, y) = (unpack(fmt, a), unpack(fmt, b));
    let neg = sign_of(x) != sign_of(y);
    if (is_inf(x) && is_zero(y)) || (is_zero(x) && is_inf(y)) {
        return invalid(fmt);
    }
    if is_inf(x) || is_inf(y) {
        return Outcome::exact(fmt.infinity(neg));
    }
    if is_zero(x) || is_zero(y) {
        return Outcome::exact(fmt.zero(neg));
    }
    let (
        Operand::Finite {
            mag: m1, exp: e1, ..
        },
        Operand::Finite {
            mag: m2, exp: e2, ..
        },
    ) = (x, y)
    else {
        unreachable!("special operands were handled")
    };
    round_pack(fmt, neg, m1 * m2, e1 + e2, false, rm)
}

/// `a / b` (FDIV).
pub fn div(fmt: Format, a: u64, b: u64, rm: Rounding) -> Outcome<u64> {
    if let Some(nan) = process_nans(fmt, &[a, b]) {
        return nan;
    }
    let (x, y) = (unpack(fmt, a), unpack(fmt, b));
    let neg = sign_of(x) != sign_of(y);
    if (is_inf(x) && is_inf(y)) || (is_zero(x) && is_zero(y)) {
        return invalid(fmt);
    }
    if is_inf(x) || is_zero(y) {
        let flags = if is_inf(x) {
            Flags::NONE
        } else {
            Flags::DIV_BY_ZERO
        };
        return Outcome::with(fmt.infinity(neg), flags);
    }
    if is_zero(x) || is_inf(y) {
        return Outcome::exact(fmt.zero(neg));
    }
    let (
        Operand::Finite {
            mag: m1, exp: e1, ..
        },
        Operand::Finite {
            mag: m2, exp: e2, ..
        },
    ) = (x, y)
    else {
        unreachable!("special operands were handled")
    };
    // Scale the dividend so the quotient keeps at least precision + 2 bits.
    let p = fmt.precision() as i32;
    let scale = (p + 3 + bit_len(m2) as i32 - bit_len(m1) as i32).max(0);
    let numerator = m1 << scale;
    let quotient = numerator / m2;
    let remainder = numerator % m2;
    round_pack(fmt, neg, quotient, e1 - e2 - scale, remainder != 0, rm)
}

/// The integer square root (floor) of `n`, by the digit-by-digit method.
fn isqrt(n: u128) -> u128 {
    let mut rem = n;
    let mut root = 0u128;
    let mut bit = 1u128 << 126;
    while bit > n {
        bit >>= 2;
    }
    while bit != 0 {
        if rem >= root + bit {
            rem -= root + bit;
            root = (root >> 1) + bit;
        } else {
            root >>= 1;
        }
        bit >>= 2;
    }
    root
}

/// `sqrt(a)` (FSQRT).
pub fn sqrt(fmt: Format, a: u64, rm: Rounding) -> Outcome<u64> {
    if let Some(nan) = process_nans(fmt, &[a]) {
        return nan;
    }
    match unpack(fmt, a) {
        Operand::Finite { mag: 0, .. } => Outcome::exact(a & fmt.mask()),
        Operand::Inf { neg: false } => Outcome::exact(fmt.infinity(false)),
        Operand::Inf { neg: true } | Operand::Finite { neg: true, .. } => invalid(fmt),
        Operand::Finite {
            neg: false,
            mag,
            exp,
        } => {
            // Radicand with at least 2 * (precision + 2) bits and an even
            // exponent, so the root keeps at least precision + 2 bits.
            let p = fmt.precision() as i32;
            let mut shift = (2 * (p + 2) + 1 - bit_len(mag) as i32).max(0);
            if (exp - shift) % 2 != 0 {
                shift += 1;
            }
            let radicand = mag << shift;
            let root = isqrt(radicand);
            round_pack(
                fmt,
                false,
                root,
                (exp - shift) / 2,
                root * root != radicand,
                rm,
            )
        }
        Operand::Nan => unreachable!("NaN operands were processed"),
    }
}

/// `addend + n * m` with a single rounding (FMADD `Rd = Ra + Rn * Rm`, Arm
/// `FPMulAdd(addend, op1 = n, op2 = m)`).
pub fn fma(fmt: Format, n: u64, m: u64, addend: u64, rm: Rounding) -> Outcome<u64> {
    let (x, y, a) = (unpack(fmt, n), unpack(fmt, m), unpack(fmt, addend));
    let inf_times_zero = (is_inf(x) && is_zero(y)) || (is_zero(x) && is_inf(y));
    if classify(fmt, addend) == Class::QuietNan && inf_times_zero {
        return invalid(fmt);
    }
    if let Some(nan) = process_nans(fmt, &[addend, n, m]) {
        return nan;
    }
    let sign_p = sign_of(x) != sign_of(y);
    let inf_p = is_inf(x) || is_inf(y);
    let zero_p = is_zero(x) || is_zero(y);
    let neg_a = sign_of(a);
    if inf_times_zero || (is_inf(a) && inf_p && neg_a != sign_p) {
        return invalid(fmt);
    }
    if (is_inf(a) && !neg_a) || (inf_p && !sign_p) {
        return Outcome::exact(fmt.infinity(false));
    }
    if (is_inf(a) && neg_a) || (inf_p && sign_p) {
        return Outcome::exact(fmt.infinity(true));
    }
    if is_zero(a) && zero_p && neg_a == sign_p {
        return Outcome::exact(fmt.zero(neg_a));
    }
    let (
        Operand::Finite {
            mag: ma, exp: ea, ..
        },
        Operand::Finite {
            mag: m1, exp: e1, ..
        },
        Operand::Finite {
            mag: m2, exp: e2, ..
        },
    ) = (a, x, y)
    else {
        unreachable!("special operands were handled")
    };
    round_wide(fmt, sum_terms(neg_a, ma, ea, sign_p, m1 * m2, e1 + e2), rm)
}

/// `-a` (FNEG): flips the sign bit of every encoding, NaNs included.
pub fn neg(fmt: Format, a: u64) -> Outcome<u64> {
    Outcome::exact((a ^ fmt.sign_bit()) & fmt.mask())
}

/// `|a|` (FABS): clears the sign bit of every encoding, NaNs included.
pub fn abs(fmt: Format, a: u64) -> Outcome<u64> {
    Outcome::exact(a & !fmt.sign_bit() & fmt.mask())
}

/// Compare two non-NaN operands by value (`-0 == +0`).
fn compare_values(x: Operand, y: Operand) -> Ordering {
    fn key(op: Operand) -> (i8, bool, u128, i32) {
        match op {
            Operand::Inf { neg } => (if neg { -2 } else { 2 }, neg, 0, 0),
            Operand::Finite { mag: 0, .. } => (0, false, 0, 0),
            Operand::Finite { neg, mag, exp } => (if neg { -1 } else { 1 }, neg, mag, exp),
            Operand::Nan => unreachable!("NaNs are not ordered"),
        }
    }
    let (kx, ky) = (key(x), key(y));
    if kx.0 != ky.0 || kx.0.abs() != 1 {
        return kx.0.cmp(&ky.0);
    }
    // Same sign, both nonzero finite: compare magnitudes exactly.
    let magnitude = compare_magnitudes(kx.2, kx.3, ky.2, ky.3);
    if kx.1 { magnitude.reverse() } else { magnitude }
}

fn compare_magnitudes(m1: u128, e1: i32, m2: u128, e2: i32) -> Ordering {
    let top1 = bit_len(m1) as i32 - 1 + e1;
    let top2 = bit_len(m2) as i32 - 1 + e2;
    if top1 != top2 {
        return top1.cmp(&top2);
    }
    // Same leading-bit position: align at the smaller exponent (the
    // difference is below 64 for operands of at most 64 bits).
    let low = e1.min(e2);
    (m1 << (e1 - low)).cmp(&(m2 << (e2 - low)))
}

fn min_max_impl(fmt: Format, a: u64, b: u64, is_min: bool) -> Outcome<u64> {
    if let Some(nan) = process_nans(fmt, &[a, b]) {
        return nan;
    }
    let (x, y) = (unpack(fmt, a), unpack(fmt, b));
    let order = compare_values(x, y);
    let pick_first = if is_min {
        order == Ordering::Less
    } else {
        order == Ordering::Greater
    };
    let chosen = if pick_first { a } else { b };
    let chosen_op = if pick_first { x } else { y };
    if is_zero(chosen_op) {
        let neg = if is_min {
            sign_of(x) || sign_of(y)
        } else {
            sign_of(x) && sign_of(y)
        };
        return Outcome::exact(fmt.zero(neg));
    }
    Outcome::exact(chosen & fmt.mask())
}

/// FMIN: NaN-propagating minimum (`FPMin`), `-0 < +0`.
pub fn min(fmt: Format, a: u64, b: u64) -> Outcome<u64> {
    min_max_impl(fmt, a, b, true)
}

/// FMAX: NaN-propagating maximum (`FPMax`), `-0 < +0`.
pub fn max(fmt: Format, a: u64, b: u64) -> Outcome<u64> {
    min_max_impl(fmt, a, b, false)
}

fn min_max_num_impl(fmt: Format, a: u64, b: u64, is_min: bool) -> Outcome<u64> {
    // FPMinNum/FPMaxNum: a lone QUIET NaN is replaced by the infinity that
    // loses the comparison; signaling NaNs still propagate (quieted).
    let replacement = fmt.infinity(!is_min);
    let (qa, qb) = (
        classify(fmt, a) == Class::QuietNan,
        classify(fmt, b) == Class::QuietNan,
    );
    let (a, b) = match (qa, qb) {
        (true, false) => (replacement, b),
        (false, true) => (a, replacement),
        _ => (a, b),
    };
    min_max_impl(fmt, a, b, is_min)
}

/// FMINNM: IEEE 754-2008 `minNum` (`FPMinNum`): a lone quiet NaN yields the
/// number, a signaling NaN propagates quieted with Invalid Operation.
pub fn min_num(fmt: Format, a: u64, b: u64) -> Outcome<u64> {
    min_max_num_impl(fmt, a, b, true)
}

/// FMAXNM: IEEE 754-2008 `maxNum` (`FPMaxNum`).
pub fn max_num(fmt: Format, a: u64, b: u64) -> Outcome<u64> {
    min_max_num_impl(fmt, a, b, false)
}

/// Round the magnitude `mag * 2^exp` (`exp < 0`) to an integer in direction
/// `rm` for a value of sign `neg`. Returns the integer magnitude (`None` when
/// it exceeds `u128`) and whether the value was not already an integer.
fn round_magnitude_to_integer(
    neg: bool,
    mag: u128,
    exp: i32,
    rm: Rounding,
) -> (Option<u128>, bool) {
    if exp >= 0 {
        if bit_len(mag) as i32 + exp > 128 {
            return (None, false);
        }
        return (Some(mag << exp), false);
    }
    let shift = (-exp) as u32;
    let (kept, half_cmp, inexact) = if shift >= 129 {
        (0, Ordering::Less, mag != 0)
    } else if shift == 128 {
        (0, mag.cmp(&(1u128 << 127)), mag != 0)
    } else {
        let rem = mag & ((1u128 << shift) - 1);
        (mag >> shift, rem.cmp(&(1u128 << (shift - 1))), rem != 0)
    };
    let round_up = match rm {
        Rounding::TiesToEven => {
            half_cmp == Ordering::Greater || (half_cmp == Ordering::Equal && kept & 1 == 1)
        }
        Rounding::TiesToAway => half_cmp != Ordering::Less,
        Rounding::TowardZero => false,
        Rounding::TowardPositive => inexact && !neg,
        Rounding::TowardNegative => inexact && neg,
    };
    (Some(kept + u128::from(round_up)), inexact)
}

/// Round to an integral value in the same format (FRINT*). `exact` raises
/// Inexact when the result differs from the operand (FRINTX); the other
/// FRINT forms never raise it. A zero result keeps the operand's sign.
pub fn round_to_integral(fmt: Format, a: u64, rm: Rounding, exact: bool) -> Outcome<u64> {
    if let Some(nan) = process_nans(fmt, &[a]) {
        return nan;
    }
    match unpack(fmt, a) {
        Operand::Inf { .. } | Operand::Finite { mag: 0, .. } => Outcome::exact(a & fmt.mask()),
        Operand::Finite { exp, .. } if exp >= 0 => Outcome::exact(a & fmt.mask()),
        Operand::Finite { neg, mag, exp } => {
            let (integer, inexact) = round_magnitude_to_integer(neg, mag, exp, rm);
            let integer = integer.expect("a sub-integer exponent keeps the magnitude small");
            let flags = if exact && inexact {
                Flags::INEXACT
            } else {
                Flags::NONE
            };
            if integer == 0 {
                return Outcome::with(fmt.zero(neg), flags);
            }
            let packed = round_pack(fmt, neg, integer, 0, false, rm);
            assert_eq!(
                packed.flags,
                Flags::NONE,
                "an integral result is representable"
            );
            Outcome::with(packed.value, flags)
        }
        Operand::Nan => unreachable!("NaN operands were processed"),
    }
}

/// Convert to an integer of `width` bits (1..=128), `signed` or not, rounding
/// in direction `rm` (FCVT{Z,N,M,P,A}{S,U} at W/X, and Rust's saturating `as`
/// cast at any width with `TowardZero`). Out-of-range values saturate and NaN
/// converts to zero; both raise Invalid Operation. The value is the
/// destination's two's-complement bit pattern, zero-extended to 128 bits.
pub fn to_int(fmt: Format, a: u64, rm: Rounding, width: u32, signed: bool) -> Outcome<u128> {
    assert!((1..=128).contains(&width), "integer width {width}");
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let (max_pos, max_neg_mag) = if signed {
        ((1u128 << (width - 1)) - 1, 1u128 << (width - 1))
    } else {
        (mask, 0)
    };
    let saturate = |neg: bool| {
        let value = if neg {
            max_neg_mag.wrapping_neg() & mask
        } else {
            max_pos
        };
        Outcome::with(value, Flags::INVALID)
    };
    match unpack(fmt, a) {
        Operand::Nan => Outcome::with(0, Flags::INVALID),
        Operand::Inf { neg } => saturate(neg),
        Operand::Finite { mag: 0, .. } => Outcome::exact(0),
        Operand::Finite { neg, mag, exp } => {
            let (integer, inexact) = round_magnitude_to_integer(neg, mag, exp, rm);
            let Some(integer) = integer else {
                return saturate(neg);
            };
            let flags = if inexact { Flags::INEXACT } else { Flags::NONE };
            if integer == 0 {
                return Outcome::with(0, flags);
            }
            if neg {
                if integer > max_neg_mag {
                    return saturate(true);
                }
                Outcome::with(integer.wrapping_neg() & mask, flags)
            } else {
                if integer > max_pos {
                    return saturate(false);
                }
                Outcome::with(integer, flags)
            }
        }
    }
}

/// Convert the integer `(-1)^neg * magnitude` to `fmt` (SCVTF/UCVTF). Zero
/// converts to `+0`.
pub fn from_int(fmt: Format, neg: bool, magnitude: u128, rm: Rounding) -> Outcome<u64> {
    if magnitude == 0 {
        return Outcome::exact(fmt.zero(false));
    }
    round_pack(fmt, neg, magnitude, 0, false, rm)
}

/// Convert the low `width` bits of `bits`, read as a signed (`signed`) or
/// unsigned integer, to `fmt`.
pub fn from_int_bits(
    fmt: Format,
    bits: u128,
    width: u32,
    signed: bool,
    rm: Rounding,
) -> Outcome<u64> {
    assert!((1..=128).contains(&width), "integer width {width}");
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let bits = bits & mask;
    let negative = signed && (bits >> (width - 1)) & 1 == 1;
    let magnitude = if negative {
        bits.wrapping_neg() & mask
    } else {
        bits
    };
    // The most negative value's magnitude is 2^(width-1), which the masked
    // negation yields exactly (it equals the bit pattern itself).
    from_int(fmt, negative, magnitude, rm)
}

/// `FPConvertNaN`: the NaN `bits` of `src`, quieted, with its payload's
/// high-order bits kept (narrowing) or zero-padded (widening).
pub fn convert_nan(src: Format, dst: Format, bits: u64) -> u64 {
    let neg = bits & src.sign_bit() != 0;
    let payload = bits & (src.quiet_bit() - 1);
    let payload = if dst.frac_bits() >= src.frac_bits() {
        payload << (dst.frac_bits() - src.frac_bits())
    } else {
        payload >> (src.frac_bits() - dst.frac_bits())
    };
    dst.zero(neg) | dst.exp_mask() | dst.quiet_bit() | payload
}

/// Convert between formats (FCVT), rounding in direction `rm`.
pub fn convert(src: Format, dst: Format, bits: u64, rm: Rounding) -> Outcome<u64> {
    match unpack(src, bits) {
        Operand::Nan => {
            let flags = if classify(src, bits) == Class::SignalingNan {
                Flags::INVALID
            } else {
                Flags::NONE
            };
            Outcome::with(convert_nan(src, dst, bits), flags)
        }
        Operand::Inf { neg } => Outcome::exact(dst.infinity(neg)),
        Operand::Finite { neg, mag: 0, .. } => Outcome::exact(dst.zero(neg)),
        Operand::Finite { neg, mag, exp } => round_pack(dst, neg, mag, exp, false, rm),
    }
}

/// The exact value of a finite `bits` as `(neg, mag, exp)` with `value =
/// (-1)^neg * mag * 2^exp`, or `None` for an infinity or a NaN. Exposed so a
/// test can state an exact property of a result without host arithmetic.
pub fn exact_value(fmt: Format, bits: u64) -> Option<(bool, u128, i32)> {
    match unpack(fmt, bits) {
        Operand::Finite { neg, mag, exp } => Some((neg, mag, exp)),
        _ => None,
    }
}

#[cfg(test)]
#[path = "ieee754_reference_tests.rs"]
mod tests;
