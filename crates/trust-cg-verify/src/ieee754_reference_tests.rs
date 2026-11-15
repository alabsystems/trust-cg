// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Known-answer vectors for the independent IEEE 754 reference.
//!
//! Every expected value below is stated as raw bits and was derived by hand
//! from the exact rational result (the derivation is in the comment beside the
//! less obvious ones); none is computed by the host FPU. The live hardware
//! differential (`tests/aarch64_fp_ieee_differential.rs`) is the much larger
//! check; these vectors pin the reference's own reading of the standard.

use super::*;

const RNE: Rounding = Rounding::TiesToEven;
const RNA: Rounding = Rounding::TiesToAway;
const RTZ: Rounding = Rounding::TowardZero;
const RTP: Rounding = Rounding::TowardPositive;
const RTN: Rounding = Rounding::TowardNegative;

const H: Format = Format::Half;
const S: Format = Format::Single;
const D: Format = Format::Double;

const NONE: Flags = Flags::NONE;
const IOC: Flags = Flags::INVALID;
const DZC: Flags = Flags::DIV_BY_ZERO;
const IXC: Flags = Flags::INEXACT;
const OFC_IXC: Flags = Flags(Flags::OVERFLOW.0 | Flags::INEXACT.0);
const UFC_IXC: Flags = Flags(Flags::UNDERFLOW.0 | Flags::INEXACT.0);

#[track_caller]
fn check(got: Outcome<u64>, value: u64, flags: Flags) {
    assert_eq!(
        (got.value, got.flags),
        (value, flags),
        "got {:#x} [{}], expected {value:#x} [{flags}]",
        got.value,
        got.flags
    );
}

#[track_caller]
fn check_int(got: Outcome<u128>, value: u128, flags: Flags) {
    assert_eq!(
        (got.value, got.flags),
        (value, flags),
        "got {:#x} [{}], expected {value:#x} [{flags}]",
        got.value,
        got.flags
    );
}

#[test]
fn format_constants() {
    assert_eq!(
        (H.bias(), H.emin(), H.emax(), H.precision()),
        (15, -14, 15, 11)
    );
    assert_eq!(
        (S.bias(), S.emin(), S.emax(), S.precision()),
        (127, -126, 127, 24)
    );
    assert_eq!(
        (D.bias(), D.emin(), D.emax(), D.precision()),
        (1023, -1022, 1023, 53)
    );
    assert_eq!(H.default_nan(), 0x7e00);
    assert_eq!(S.default_nan(), 0x7fc0_0000);
    assert_eq!(D.default_nan(), 0x7ff8_0000_0000_0000);
    assert_eq!(H.max_finite(false), 0x7bff);
    assert_eq!(S.max_finite(true), 0xff7f_ffff);
    assert_eq!(D.max_finite(false), 0x7fef_ffff_ffff_ffff);
    assert_eq!(H.infinity(true), 0xfc00);
    assert_eq!(classify(S, 0x7f80_0001), Class::SignalingNan);
    assert_eq!(classify(S, 0x7fc0_0000), Class::QuietNan);
    assert_eq!(classify(H, 0x0001), Class::Subnormal);
    assert_eq!(classify(D, 0x8000_0000_0000_0000), Class::Zero);
}

#[test]
fn binary64_arithmetic_vectors() {
    // 0.1 + 0.2 = 0.30000000000000004.
    check(
        add(D, 0x3fb9_9999_9999_999a, 0x3fc9_9999_9999_999a, RNE),
        0x3fd3_3333_3333_3334,
        IXC,
    );
    // 1 / 3.
    check(
        div(D, 0x3ff0_0000_0000_0000, 0x4008_0000_0000_0000, RNE),
        0x3fd5_5555_5555_5555,
        IXC,
    );
    // sqrt(2).
    check(
        sqrt(D, 0x4000_0000_0000_0000, RNE),
        0x3ff6_a09e_667f_3bcd,
        IXC,
    );
    // sqrt(4) = 2 exactly; sqrt(2^-1074) = 2^-537 exactly.
    check(
        sqrt(D, 0x4010_0000_0000_0000, RNE),
        0x4000_0000_0000_0000,
        NONE,
    );
    check(
        sqrt(D, 0x0000_0000_0000_0001, RNE),
        0x1e60_0000_0000_0000,
        NONE,
    );
    // 0.1 * 10 = 1 + 2^-54 rounds to 1; fused 0.1 * 10 - 1 = 2^-54 exactly.
    check(
        mul(D, 0x3fb9_9999_9999_999a, 0x4024_0000_0000_0000, RNE),
        0x3ff0_0000_0000_0000,
        IXC,
    );
    check(
        fma(
            D,
            0x3fb9_9999_9999_999a,
            0x4024_0000_0000_0000,
            0xbff0_0000_0000_0000,
            RNE,
        ),
        0x3c90_0000_0000_0000,
        NONE,
    );
    // Ties at 1: 1 + 2^-53 -> 1 (even); (1 + 2^-52) + 2^-53 -> 1 + 2^-51.
    check(
        add(D, 0x3ff0_0000_0000_0000, 0x3ca0_0000_0000_0000, RNE),
        0x3ff0_0000_0000_0000,
        IXC,
    );
    check(
        add(D, 0x3ff0_0000_0000_0001, 0x3ca0_0000_0000_0000, RNE),
        0x3ff0_0000_0000_0002,
        IXC,
    );
    check(
        add(D, 0x3ff0_0000_0000_0000, 0x3ca0_0000_0000_0000, RNA),
        0x3ff0_0000_0000_0001,
        IXC,
    );
    // A term 2^-1074 beside 1: only the sticky bit survives.
    check(
        add(D, 0x3ff0_0000_0000_0000, 0x0000_0000_0000_0001, RTP),
        0x3ff0_0000_0000_0001,
        IXC,
    );
    check(
        sub(D, 0x3ff0_0000_0000_0000, 0x0000_0000_0000_0001, RNE),
        0x3ff0_0000_0000_0000,
        IXC,
    );
    check(
        sub(D, 0x3ff0_0000_0000_0000, 0x0000_0000_0000_0001, RTZ),
        0x3fef_ffff_ffff_ffff,
        IXC,
    );
    // Overflow: MAX * 2 by direction.
    let max = 0x7fef_ffff_ffff_ffff;
    let two = 0x4000_0000_0000_0000;
    check(mul(D, max, two, RNE), 0x7ff0_0000_0000_0000, OFC_IXC);
    check(mul(D, max, two, RTZ), max, OFC_IXC);
    check(mul(D, max, two, RTN), max, OFC_IXC);
    check(
        mul(D, max | D.sign_bit(), two, RTP),
        max | D.sign_bit(),
        OFC_IXC,
    );
    // Underflow: 2^-1074 * 0.5 is a tie between 0 and 2^-1074.
    check(
        mul(D, 0x0000_0000_0000_0001, 0x3fe0_0000_0000_0000, RNE),
        0,
        UFC_IXC,
    );
    check(
        mul(D, 0x0000_0000_0000_0001, 0x3fe0_0000_0000_0000, RNA),
        1,
        UFC_IXC,
    );
    // An exact subnormal result raises nothing.
    check(
        sub(D, 0x0010_0000_0000_0000, 0x0000_0000_0000_0001, RNE),
        0x000f_ffff_ffff_ffff,
        NONE,
    );
    // Tininess before rounding: the largest subnormal times (1 + 2^-52) is
    // 2^-1022 - 2^-1126, which rounds to the smallest normal and still
    // raises Underflow.
    check(
        mul(D, 0x000f_ffff_ffff_ffff, 0x3ff0_0000_0000_0001, RNE),
        0x0010_0000_0000_0000,
        UFC_IXC,
    );
}

#[test]
fn special_operand_vectors() {
    let one = 0x3ff0_0000_0000_0000;
    let inf = D.infinity(false);
    let ninf = D.infinity(true);
    let zero = D.zero(false);
    let nzero = D.zero(true);
    let dnan = D.default_nan();
    check(div(D, one, zero, RNE), inf, DZC);
    check(div(D, one | D.sign_bit(), zero, RNE), ninf, DZC);
    check(div(D, one, nzero, RNE), ninf, DZC);
    check(div(D, inf, zero, RNE), inf, NONE);
    check(div(D, zero, zero, RNE), dnan, IOC);
    check(div(D, inf, ninf, RNE), dnan, IOC);
    check(div(D, zero, inf, RNE), zero, NONE);
    check(mul(D, zero, inf, RNE), dnan, IOC);
    check(add(D, inf, ninf, RNE), dnan, IOC);
    check(sub(D, inf, inf, RNE), dnan, IOC);
    check(add(D, inf, inf, RNE), inf, NONE);
    check(sqrt(D, one | D.sign_bit(), RNE), dnan, IOC);
    check(sqrt(D, nzero, RNE), nzero, NONE);
    check(sqrt(D, ninf, RNE), dnan, IOC);
    check(sqrt(D, inf, RNE), inf, NONE);
    // Signed zeros of sums.
    check(sub(D, one, one, RNE), zero, NONE);
    check(sub(D, one, one, RTN), nzero, NONE);
    check(add(D, nzero, nzero, RNE), nzero, NONE);
    check(add(D, zero, nzero, RNE), zero, NONE);
    check(add(D, zero, nzero, RTN), nzero, NONE);
    // NaN propagation: first signaling NaN quieted, else first quiet NaN.
    check(
        add(D, 0x7ff0_0000_0000_0001, one, RNE),
        0x7ff8_0000_0000_0001,
        IOC,
    );
    check(
        add(D, one, 0xfff8_0000_0000_0123, RNE),
        0xfff8_0000_0000_0123,
        NONE,
    );
    check(
        add(D, 0x7ff8_0000_0000_0002, 0x7ff0_0000_0000_0003, RNE),
        0x7ff8_0000_0000_0003,
        IOC,
    );
    check(
        mul(D, 0x7ff8_0000_0000_0002, 0x7ff8_0000_0000_0005, RNE),
        0x7ff8_0000_0000_0002,
        NONE,
    );
    // Fused multiply-add: the addend is processed first, and a quiet-NaN
    // addend beside inf * 0 is the default NaN with Invalid Operation.
    check(
        fma(D, 0x7ff0_0000_0000_0001, one, 0x7ff0_0000_0000_0002, RNE),
        0x7ff8_0000_0000_0002,
        IOC,
    );
    check(fma(D, inf, zero, 0x7ff8_0000_0000_0009, RNE), dnan, IOC);
    check(fma(D, inf, zero, one, RNE), dnan, IOC);
    check(
        fma(D, 0x7ff8_0000_0000_0004, one, 0x7ff8_0000_0000_0007, RNE),
        0x7ff8_0000_0000_0007,
        NONE,
    );
    check(fma(D, inf, one, ninf, RNE), dnan, IOC);
    check(fma(D, nzero, one, zero, RNE), zero, NONE);
    check(fma(D, nzero, one, nzero, RNE), nzero, NONE);
    check(fma(D, nzero, one, zero, RTN), nzero, NONE);
    // FNEG/FABS are sign-bit operations, NaNs included.
    check(neg(D, 0x7ff0_0000_0000_0001), 0xfff0_0000_0000_0001, NONE);
    check(abs(D, 0xfff8_0000_0000_0001), 0x7ff8_0000_0000_0001, NONE);
}

#[test]
fn min_max_vectors() {
    let one = 0x3f80_0000;
    let two = 0x4000_0000;
    let qnan = 0x7fc0_1234;
    let snan = 0x7f80_0001;
    let zero = 0;
    let nzero = 0x8000_0000;
    check(min_num(S, one, two), one, NONE);
    check(max_num(S, one, two), two, NONE);
    check(min_num(S, qnan, two), two, NONE);
    check(max_num(S, two, qnan), two, NONE);
    check(min_num(S, snan, two), 0x7fc0_0001, IOC);
    check(min_num(S, qnan, snan), 0x7fc0_0001, IOC);
    check(min_num(S, qnan, 0x7fc0_9999), qnan, NONE);
    check(min_num(S, zero, nzero), nzero, NONE);
    check(min_num(S, nzero, zero), nzero, NONE);
    check(max_num(S, zero, nzero), zero, NONE);
    check(max_num(S, nzero, zero), zero, NONE);
    check(min(S, qnan, two), qnan, NONE);
    check(max(S, two, snan), 0x7fc0_0001, IOC);
    check(min_num(S, 0xff80_0000, qnan), 0xff80_0000, NONE);
}

#[test]
fn binary32_and_binary16_arithmetic_vectors() {
    // 0.1f + 0.2f: 40265319 * 2^-27 = 10066329.75 * 2^-25 -> 0x3e99999a.
    check(add(S, 0x3dcc_cccd, 0x3e4c_cccd, RNE), 0x3e99_999a, IXC);
    // 1/3: 2^25 / 3 = 11184810.67 -> 0xaaaaab.
    check(div(S, 0x3f80_0000, 0x4040_0000, RNE), 0x3eaa_aaab, IXC);
    // sqrt(2) * 2^23 = 11863283.2 -> 0xb504f3.
    check(sqrt(S, 0x4000_0000, RNE), 0x3fb5_04f3, IXC);
    check(mul(S, 0x7f7f_ffff, 0x4000_0000, RNE), 0x7f80_0000, OFC_IXC);
    // binary16: 1/3 = 1365.33 * 2^-12 -> 0x3555; sqrt(2) = 1448.15 * 2^-10.
    check(div(H, 0x3c00, 0x4200, RNE), 0x3555, IXC);
    check(sqrt(H, 0x4000, RNE), 0x3da8, IXC);
    // 65504 + 16 = 65520 is a tie between 65504 (odd) and 2^16: overflow.
    check(add(H, 0x7bff, 0x4c00, RNE), 0x7c00, OFC_IXC);
    // Toward zero, 65520 rounds to 65504 even with an unbounded exponent:
    // inexact, not an overflow.
    check(add(H, 0x7bff, 0x4c00, RTZ), 0x7bff, IXC);
    // 2^-24 * 0.5 ties to 0; 3 * 2^-24 * 0.5 ties to 2 * 2^-24.
    check(mul(H, 0x0001, 0x3800, RNE), 0x0000, UFC_IXC);
    check(mul(H, 0x0003, 0x3800, RNE), 0x0002, UFC_IXC);
    check(mul(H, 0x8003, 0x3800, RNE), 0x8002, UFC_IXC);
    check(add(H, 0x7c01, 0x3c00, RNE), 0x7e01, IOC);
}

#[test]
fn conversion_vectors() {
    // binary16 -> binary32 is exact.
    check(convert(H, S, 0x0001, RNE), 0x3380_0000, NONE);
    check(convert(H, S, 0x7bff, RNE), 0x477f_e000, NONE);
    check(convert(H, D, 0x8400, RNE), 0xbf10_0000_0000_0000, NONE);
    // binary32 -> binary16: overflow and underflow.
    check(convert(S, H, 0x477f_f000, RNE), 0x7c00, OFC_IXC);
    check(convert(S, H, 0x477f_efff, RNE), 0x7bff, IXC);
    check(convert(S, H, 0x3300_0000, RNE), 0x0000, UFC_IXC);
    check(convert(S, H, 0x3300_0001, RNE), 0x0001, UFC_IXC);
    // binary64 -> binary32: 1 + 2^-24 ties to 1.
    check(convert(D, S, 0x3ff0_0000_1000_0000, RNE), 0x3f80_0000, IXC);
    check(convert(D, S, 0x3ff0_0000_1000_0001, RNE), 0x3f80_0001, IXC);
    check(convert(D, S, 0x3ff0_0000_1000_0000, RTP), 0x3f80_0001, IXC);
    // NaN payloads: high-order bits kept, quieted; a signaling NaN raises IOC.
    check(convert(S, H, 0x7f80_0001, RNE), 0x7e00, IOC);
    check(convert(S, H, 0x7fc0_2000, RNE), 0x7e01, NONE);
    check(convert(H, S, 0x7d23, RNE), 0x7fe4_6000, IOC);
    check(convert(S, D, 0xffc0_0001, RNE), 0xfff8_0000_2000_0000, NONE);
}

#[test]
fn float_to_integer_vectors() {
    // binary32 -> i32 around the range ends.
    check_int(to_int(S, 0x4eff_ffff, RTZ, 32, true), 2_147_483_520, NONE);
    check_int(to_int(S, 0x4f00_0000, RTZ, 32, true), 0x7fff_ffff, IOC);
    check_int(to_int(S, 0xcf00_0000, RTZ, 32, true), 0x8000_0000, NONE);
    check_int(to_int(S, 0xcf00_0001, RTZ, 32, true), 0x8000_0000, IOC);
    check_int(to_int(S, 0x7fc0_0000, RTZ, 32, true), 0, IOC);
    check_int(to_int(S, 0xff80_0000, RTZ, 64, true), 1 << 63, IOC);
    // 1.5 and -1.5 truncate with Inexact.
    check_int(to_int(S, 0x3fc0_0000, RTZ, 32, true), 1, IXC);
    check_int(to_int(S, 0xbfc0_0000, RTZ, 32, true), 0xffff_ffff, IXC);
    check_int(to_int(S, 0xbfc0_0000, RNE, 32, true), 0xffff_fffe, IXC);
    check_int(to_int(S, 0xbfc0_0000, RTN, 32, true), 0xffff_fffe, IXC);
    check_int(to_int(S, 0xbfc0_0000, RTP, 32, true), 0xffff_ffff, IXC);
    check_int(to_int(S, 0x4020_0000, RNA, 32, true), 3, IXC);
    check_int(to_int(S, 0x4020_0000, RNE, 32, true), 2, IXC);
    // Unsigned: -0.5 truncates to 0 (Inexact), -1.0 saturates (Invalid).
    check_int(to_int(S, 0xbf00_0000, RTZ, 32, false), 0, IXC);
    check_int(to_int(S, 0xbf80_0000, RTZ, 32, false), 0, IOC);
    check_int(to_int(S, 0x8000_0000, RTZ, 32, false), 0, NONE);
    // 1e19 fits u64 but not i64.
    check_int(
        to_int(D, 0x43e1_58e4_6091_3d00, RTZ, 64, true),
        0x7fff_ffff_ffff_ffff,
        IOC,
    );
    check_int(
        to_int(D, 0x43e1_58e4_6091_3d00, RTZ, 64, false),
        10_000_000_000_000_000_000,
        NONE,
    );
    // Narrow saturating widths (Rust `as` at i8/u8, TrustIR FPToSISat).
    check_int(to_int(S, 0x42ff_cccd, RTZ, 8, true), 127, IXC); // 127.9
    check_int(to_int(S, 0x4300_0000, RTZ, 8, true), 127, IOC); // 128
    check_int(to_int(S, 0xc300_e666, RTZ, 8, true), 0x80, IXC); // -128.9
    check_int(to_int(S, 0xc301_0000, RTZ, 8, true), 0x80, IOC); // -129
    check_int(to_int(S, 0x437f_8000, RTZ, 8, false), 255, IXC); // 255.5
    check_int(to_int(S, 0x4380_0000, RTZ, 8, false), 255, IOC); // 256
    // i128 and a value beyond u128.
    check_int(
        to_int(D, 0x47e0_0000_0000_0000, RTZ, 128, true),
        (1u128 << 127) - 1,
        IOC,
    );
    check_int(
        to_int(D, 0xc7e0_0000_0000_0000, RTZ, 128, true),
        1u128 << 127,
        NONE,
    );
    check_int(
        to_int(D, 0x7fef_ffff_ffff_ffff, RTZ, 128, false),
        u128::MAX,
        IOC,
    );
}

#[test]
fn integer_to_float_vectors() {
    // 2^24 + 1 ties to 2^24; 2^24 + 3 ties to 2^24 + 4.
    check(
        from_int_bits(S, 16_777_217, 32, true, RNE),
        0x4b80_0000,
        IXC,
    );
    check(
        from_int_bits(S, 16_777_219, 32, true, RNE),
        0x4b80_0002,
        IXC,
    );
    check(
        from_int_bits(S, 0x8000_0000, 32, true, RNE),
        0xcf00_0000,
        NONE,
    );
    check(
        from_int_bits(S, 0x7fff_ffff, 32, true, RNE),
        0x4f00_0000,
        IXC,
    );
    check(
        from_int_bits(S, 0xffff_ffff, 32, false, RNE),
        0x4f80_0000,
        IXC,
    );
    check(
        from_int_bits(S, 0xffff_ffff, 32, true, RNE),
        0xbf80_0000,
        NONE,
    );
    check(
        from_int_bits(S, u128::from(u64::MAX), 64, false, RNE),
        0x5f80_0000,
        IXC,
    );
    check(
        from_int_bits(D, u128::from(u64::MAX), 64, false, RNE),
        0x43f0_0000_0000_0000,
        IXC,
    );
    check(
        from_int_bits(D, 1u128 << 63, 64, true, RNE),
        0xc3e0_0000_0000_0000,
        NONE,
    );
    check(from_int_bits(D, 0, 64, true, RNE), 0, NONE);
    // binary16: 65520 overflows, 65519 rounds to 65504.
    check(from_int_bits(H, 65_520, 32, false, RNE), 0x7c00, OFC_IXC);
    check(from_int_bits(H, 65_519, 32, false, RNE), 0x7bff, IXC);
    check(from_int_bits(S, 0x80, 8, true, RNE), 0xc300_0000, NONE);
}

#[test]
fn round_to_integral_vectors() {
    let cases: [(u64, [u64; 5]); 5] = [
        // value: [N, A, M, P, Z]
        (
            0x4004_0000_0000_0000,
            [
                0x4000 << 48,
                0x4008 << 48,
                0x4000 << 48,
                0x4008 << 48,
                0x4000 << 48,
            ],
        ), // 2.5
        (
            0xc004_0000_0000_0000,
            [
                0xc000 << 48,
                0xc008 << 48,
                0xc008 << 48,
                0xc000 << 48,
                0xc000 << 48,
            ],
        ), // -2.5
        (
            0xbfd9_9999_9999_999a,
            [
                0x8000 << 48,
                0x8000 << 48,
                0xbff0 << 48,
                0x8000 << 48,
                0x8000 << 48,
            ],
        ), // -0.4
        (0x3fe0_0000_0000_0000, [0, 0x3ff0 << 48, 0, 0x3ff0 << 48, 0]), // 0.5
        (
            0x3fe8_0000_0000_0000,
            [0x3ff0 << 48, 0x3ff0 << 48, 0, 0x3ff0 << 48, 0],
        ), // 0.75
    ];
    for (value, expected) in cases {
        for (rm, want) in [RNE, RNA, RTN, RTP, RTZ].into_iter().zip(expected) {
            check(round_to_integral(D, value, rm, false), want, NONE);
        }
    }
    // FRINTX raises Inexact when it changes the value; the others never do.
    check(
        round_to_integral(D, 0x4004_0000_0000_0000, RNE, true),
        0x4000 << 48,
        IXC,
    );
    check(
        round_to_integral(D, 0x4000_0000_0000_0000, RNE, true),
        0x4000 << 48,
        NONE,
    );
    // 8388607.5f ties to the even 8388608.
    check(
        round_to_integral(S, 0x4aff_ffff, RNE, false),
        0x4b00_0000,
        NONE,
    );
    check(
        round_to_integral(S, 0x4aff_ffff, RTZ, false),
        0x4aff_fffe,
        NONE,
    );
    check(
        round_to_integral(S, 0x7f80_0001, RTZ, false),
        0x7fc0_0001,
        IOC,
    );
    check(round_to_integral(H, 0xbc01, RTP, false), 0xbc00, NONE);
    check(round_to_integral(H, 0x3801, RTN, false), 0x0000, NONE);
}

/// Exhaustive binary16 self-consistency: widening is exact and narrowing
/// recovers the operand; `x + 0`, `x * 1`, `|x|` and `-x` behave as the
/// identities they are; addition and multiplication commute on a dense grid.
#[test]
fn binary16_exhaustive_identities() {
    for x in 0..=u16::MAX {
        let x = u64::from(x);
        let wide = convert(H, D, x, RNE);
        let back = convert(D, H, wide.value, RNE);
        if is_nan(H, x) {
            assert!(is_nan(D, wide.value) && is_nan(H, back.value));
            assert_eq!(back.value, quiet(H, x), "{x:#06x}");
            continue;
        }
        assert_eq!(wide.flags, NONE, "{x:#06x}");
        assert_eq!((back.value, back.flags), (x, NONE), "{x:#06x}");
        if classify(H, x) != Class::Zero {
            check(add(H, x, 0, RNE), x, NONE);
        }
        check(mul(H, x, 0x3c00, RNE), x, NONE);
        check(abs(H, x), x & 0x7fff, NONE);
        check(neg(H, x), x ^ 0x8000, NONE);
    }
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..200_000 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let (a, b) = (seed & 0xffff, (seed >> 16) & 0xffff);
        if is_nan(H, a) || is_nan(H, b) {
            continue;
        }
        assert_eq!(add(H, a, b, RNE), add(H, b, a, RNE), "{a:#x} {b:#x}");
        assert_eq!(mul(H, a, b, RNE), mul(H, b, a, RNE), "{a:#x} {b:#x}");
    }
}
