// Rust's float -> integer conversions, computed from the IEEE 754 encoding
// alone: the model (`spec_trunc`, `spec_saturating`, `spec_unchecked_defined`)
// uses no float arithmetic and no float -> int `as`, so it owes nothing to any
// compiler under test; only the input generator below computes with floats.
// One copy serves both users: the bridge test harness includes it, and the
// LLVM-built driver program gets it appended to its source.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

/// The float rounded toward zero: `None` for a NaN, otherwise `(negative,
/// magnitude)`, where the magnitude is `None` for an infinity or for a finite
/// value of 2^128 or more. `exp_bits`/`man_bits` give the format (8/23 for
/// binary32, 11/52 for binary64); `bits` holds its encoding in the low bits.
#[allow(dead_code)]
pub fn spec_trunc(bits: u64, exp_bits: u32, man_bits: u32) -> Option<(bool, Option<u128>)> {
    let negative = (bits >> (exp_bits + man_bits)) & 1 == 1;
    let exp_mask = (1u64 << exp_bits) - 1;
    let exp = (bits >> man_bits) & exp_mask;
    let man = bits & ((1u64 << man_bits) - 1);
    if exp == exp_mask {
        return if man == 0 {
            Some((negative, None))
        } else {
            None
        };
    }
    let bias = (1i64 << (exp_bits - 1)) - 1;
    // value = significand * 2^(unbiased - man_bits); subnormals use exponent 1.
    let (significand, unbiased) = if exp == 0 {
        (man, 1 - bias)
    } else {
        (man | (1u64 << man_bits), exp as i64 - bias)
    };
    let significand = u128::from(significand);
    let shift = unbiased - i64::from(man_bits);
    // A left shift by at most the leading-zero count keeps every bit (2^127
    // itself fits); one more bit is 2^128 or beyond.
    let magnitude = if shift >= 0 {
        if shift > i64::from(significand.leading_zeros()) {
            None
        } else {
            Some(significand << shift)
        }
    } else if -shift >= 128 {
        Some(0)
    } else {
        Some(significand >> (-shift))
    };
    Some((negative, magnitude))
}

/// `iN::MAX` / `uN::MAX` and the magnitude of `iN::MIN` (0 when unsigned).
#[allow(dead_code)]
fn spec_bounds(bits: u32, signed: bool) -> (u128, u128) {
    let all = if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    };
    if signed {
        (all >> 1, 1u128 << (bits - 1))
    } else {
        (all, 0)
    }
}

/// Rust's `x as {iN,uN}` (saturating since 1.45: NaN -> 0, out-of-range ->
/// MIN/MAX, otherwise toward zero), as the destination's `bits`-bit pattern.
#[allow(dead_code)]
pub fn spec_saturating(truncated: Option<(bool, Option<u128>)>, bits: u32, signed: bool) -> u128 {
    let (max, min_magnitude) = spec_bounds(bits, signed);
    let mask = if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    };
    match truncated {
        None => 0,
        Some((false, Some(m))) if m <= max => m,
        Some((false, _)) => max,
        Some((true, _)) if !signed => 0,
        Some((true, Some(m))) if m <= min_magnitude => m.wrapping_neg() & mask,
        Some((true, _)) => min_magnitude,
    }
}

/// Whether `x.to_int_unchecked::<{iN,uN}>()` is defined: `x` is finite and its
/// value rounded toward zero is representable (core's `f32::to_int_unchecked`
/// "Safety" section). `-128.9f32 as i8` and `-0.5f32 as u8` are inside.
#[allow(dead_code)]
pub fn spec_unchecked_defined(
    truncated: Option<(bool, Option<u128>)>,
    bits: u32,
    signed: bool,
) -> bool {
    let (max, min_magnitude) = spec_bounds(bits, signed);
    match truncated {
        Some((false, Some(m))) => m <= max,
        Some((true, Some(m))) => m <= min_magnitude,
        _ => false,
    }
}

/// Magnitudes around every integer boundary: 2^(N-1) and 2^N for N in
/// 8..=128, one below them, the fractional band just past them, and ordinary
/// in-range values. Negated below, so -2^(N-1) - 0.9 (inside `to_int_unchecked`'s
/// domain, truncating to iN::MIN) and -0.9 (truncating to 0) are present too.
#[allow(dead_code)]
fn spec_magnitudes() -> Vec<f64> {
    let mut magnitudes = vec![
        0.0,
        0.5,
        0.9,
        0.999_999_999,
        1.0,
        1.5,
        1.9,
        2.5,
        100.7,
        1e10,
        1e18,
        1e19,
        1e20,
        1e30,
        1e38,
        1e300,
    ];
    for n in [8i32, 16, 32, 64, 128] {
        let p = 2f64.powi(n - 1);
        let q = 2f64.powi(n);
        magnitudes.extend([
            p,
            q,
            p - 1.0,
            q - 1.0,
            p - 0.5,
            q - 0.5,
            p + 0.5,
            p + 0.9,
            p + 1.0,
            q + 0.5,
            q + 1.0,
        ]);
    }
    magnitudes
}

/// The binary64 inputs (encodings): NaNs of both signs and kinds, the
/// infinities, the extremes, subnormals and signed zeros, and every
/// boundary magnitude with both signs and both neighbouring floats.
#[allow(dead_code)]
pub fn spec_inputs_f64() -> Vec<u64> {
    let mut values: Vec<u64> = vec![
        0x7ff8_0000_0000_0000,
        0xfff8_0000_0000_0000,
        0x7ff0_0000_0000_0001,
        0xfff4_0000_0000_0000,
        f64::INFINITY.to_bits(),
        f64::NEG_INFINITY.to_bits(),
        f64::MAX.to_bits(),
        f64::MIN.to_bits(),
        f64::MIN_POSITIVE.to_bits(),
        (-f64::MIN_POSITIVE).to_bits(),
        1,
        0x8000_0000_0000_0001,
    ];
    for magnitude in spec_magnitudes() {
        for x in [magnitude, -magnitude] {
            values.extend([x.to_bits(), x.next_up().to_bits(), x.next_down().to_bits()]);
        }
    }
    values.sort_unstable();
    values.dedup();
    values
}

/// The binary32 inputs (encodings, zero-extended), built like the binary64
/// ones at binary32 precision.
#[allow(dead_code)]
pub fn spec_inputs_f32() -> Vec<u64> {
    let mut values: Vec<u32> = vec![
        0x7fc0_0000,
        0xffc0_0000,
        0x7f80_0001,
        0xffa0_0000,
        f32::INFINITY.to_bits(),
        f32::NEG_INFINITY.to_bits(),
        f32::MAX.to_bits(),
        f32::MIN.to_bits(),
        f32::MIN_POSITIVE.to_bits(),
        (-f32::MIN_POSITIVE).to_bits(),
        1,
        0x8000_0001,
    ];
    for magnitude in spec_magnitudes() {
        // Round to the nearest binary32 (an f64 -> f32 conversion, not a
        // float -> int one).
        let magnitude = magnitude as f32;
        for x in [magnitude, -magnitude] {
            values.extend([x.to_bits(), x.next_up().to_bits(), x.next_down().to_bits()]);
        }
    }
    values.sort_unstable();
    values.dedup();
    values.into_iter().map(u64::from).collect()
}
