// CORPUS FIXTURE — `u128` `overflowing_mul` / `checked_mul` / `saturating_mul`. The
// adapter rejects `Inst::Overflow` on 128-bit (the multiply would need a 256-bit
// product), so the bridge composes the overflow flag from the DIVISION IDENTITY using
// PROVEN u128 primitives: wrapping mul, then `overflow = a != 0 && wrapped /u a != b`,
// with a `select(a==0, 1, a)` divisor so the unsigned `UDIV` (which only traps on
// divide-by-zero) is safe. Each emitted op carries its own per-instruction cert, so no
// new proof obligation is introduced. (Signed i128 mul-overflow additionally has the
// x86 MIN/-1 IDIV trap and still fails closed.)
//
// Exercises the boundaries where a wrong overflow flag would surface: 2^64*2^64
// (exactly overflows), (2^64-1)^2 (exactly fits), MAX*MAX, MAX*1, *0, and a divisor
// straddling MAX/3. All correct -> exit 7. (O0 fails closed on the range-iter helper.)
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut c = 0i32;

    // no overflow, value 42.
    let (v0, o0) = black_box(6u128).overflowing_mul(black_box(7u128));
    if !o0 && v0 > 41 && v0 < 43 {
        c += 1;
    }
    // 2^64 * 2^64 == 2^128 -> overflow (exactly one over).
    let (_, o1) = black_box(1u128 << 64).overflowing_mul(black_box(1u128 << 64));
    if o1 {
        c += 1;
    }
    // (2^64-1)^2 < 2^128 -> no overflow.
    let (_, o2) = black_box((1u128 << 64) - 1).overflowing_mul(black_box((1u128 << 64) - 1));
    if !o2 {
        c += 1;
    }
    // MAX * 1 (no overflow) and MAX * MAX (overflow).
    let (_, o3) = black_box(u128::MAX).overflowing_mul(black_box(1u128));
    let (_, o4) = black_box(u128::MAX).overflowing_mul(black_box(u128::MAX));
    if !o3 && o4 {
        c += 1;
    }
    // * 0 (no overflow) and 0 * MAX (no overflow).
    let (vz, oz) = black_box(123u128).overflowing_mul(black_box(0u128));
    let (_, oz2) = black_box(0u128).overflowing_mul(black_box(u128::MAX));
    if !oz && vz < 1 && !oz2 {
        c += 1;
    }
    // 3 * (MAX/3) fits; 3 * (MAX/3 + 1) overflows.
    let (_, o5) = black_box(3u128).overflowing_mul(black_box(u128::MAX / 3));
    let (_, o6) = black_box(3u128).overflowing_mul(black_box(u128::MAX / 3 + 1));
    if !o5 && o6 {
        c += 1;
    }
    // checked_mul + saturating_mul (built on the same overflow path).
    let ok_chk =
        black_box(6u128).checked_mul(black_box(7u128)).is_some()
            && black_box(u128::MAX).checked_mul(black_box(2u128)).is_none();
    let sat = black_box(u128::MAX).saturating_mul(black_box(2u128)); // clamps to MAX
    if ok_chk && (sat >> 120) > 0 {
        c += 1;
    }

    c // 7
}
