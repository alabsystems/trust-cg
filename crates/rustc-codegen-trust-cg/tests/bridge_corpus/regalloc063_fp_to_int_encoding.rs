// CORPUS FIXTURE — [TCG-REGALLOC-063] sub-family B: the FP->int conversion the
// ENCODER refused on arity.
//
// On 2026-09-14 `select_fcvt_to_int`/`select_fcvt_to_uint` emitted
// `FcvtzsRR/FcvtzuRR` with a THIRD operand — an `Imm` source-width hint — while
// `encode_scalar_fp_int_conversion` demanded exactly two operands. So EVERY
// `f64 as i64` / `f32 as u32` failed the compile closed: on `library/core` the
// single encoding root was `core::num::imp::traits::pow2_to_pow10`, refused with
// `invalid operand at index 2 for FcvtzsRR ... operands [PReg(x0), PReg(d2), Imm(64)]`.
// The selector now emits the two-operand form, and the encoder still refuses a
// third operand; this program keeps the conversions exercised end to end.
//
// The values below are all EXACTLY representable, so `as` is a pure truncation
// toward zero and the expected integers are unambiguous. Saturating edges
// (NaN -> 0, out-of-range -> the type's bound) are included because `as` is
// saturating in Rust and a wrong ftype/sf in the encoding shows up there first.
//
// All correct -> exit 0. Any mismatch -> that check's index.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[inline(never)]
fn d_to_i64(x: f64) -> i64 {
    x as i64
}
#[inline(never)]
fn d_to_u64(x: f64) -> u64 {
    x as u64
}
#[inline(never)]
fn d_to_i32(x: f64) -> i32 {
    x as i32
}
#[inline(never)]
fn s_to_i64(x: f32) -> i64 {
    x as i64
}
#[inline(never)]
fn s_to_u32(x: f32) -> u32 {
    x as u32
}

/// The `pow2_to_pow10` shape itself: an f64 multiply feeding one FCVTZS.
#[inline(never)]
fn pow2_to_pow10(v: i64) -> i64 {
    (v as f64 * 0.301_029_995_663_981_2_f64) as i64
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    if d_to_i64(black_box(1234567.0f64)) != 1234567 {
        return 1;
    }
    if d_to_i64(black_box(-98765.5f64)) != -98765 {
        return 2;
    }
    if d_to_u64(black_box(4294967296.75f64)) != 4294967296 {
        return 3;
    }
    if d_to_i32(black_box(-2147483.9f64)) != -2147483 {
        return 4;
    }
    if s_to_i64(black_box(65536.5f32)) != 65536 {
        return 5;
    }
    if s_to_u32(black_box(3000000.25f32)) != 3000000 {
        return 6;
    }
    // Rust `as` saturates: NaN -> 0, out of range -> the bound.
    if d_to_i64(black_box(f64::NAN)) != 0 {
        return 7;
    }
    if d_to_i64(black_box(f64::INFINITY)) != i64::MAX {
        return 8;
    }
    if d_to_u64(black_box(-1.5f64)) != 0 {
        return 9;
    }
    if pow2_to_pow10(black_box(1024i64)) != 308 {
        return 10;
    }
    0
}
