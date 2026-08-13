// CORPUS FIXTURE — 128-bit `overflowing_add`/`overflowing_sub` (and `saturating_*`
// built on them) on `i128` and `u128`. The trust-cg adapter rejects `Inst::Overflow`
// on 128-bit types (its overflow formula is width-specialized to <=64-bit, and the
// multiply needs a 256-bit product). The bridge now composes the (wrapped, overflow)
// pair for ADD/SUB from PROVEN i128 primitives — wrapping add/sub plus the bit-exact
// overflow condition:
//   unsigned add: wrapped <u lhs       unsigned sub: lhs <u rhs
//   signed   add: (~(lhs^rhs) & (lhs^wrapped)) <s 0
//   signed   sub: ( (lhs^rhs) & (lhs^wrapped)) <s 0
// Each emitted op carries its own per-instruction cert, so no new proof obligation
// is introduced. (overflowing_mul is still left to the rejected Inst::Overflow.)
//
// Exercises the boundary cases where a wrong overflow formula would surface:
// i128::MAX+1, i128::MIN+(-1)/-1, u128::MAX wrap, unsigned borrow, and a saturating
// clamp. The result is driven by the overflow BOOLs plus i128 `<`/`>` comparisons
// (which lower to a bool icmp, not the separate i128 switchInt gap); no i128 `==` /
// `match` is used. All correct -> exit 7. (O0 fails closed on the range-iter helper.)
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

    // Each overflow bit is the composed formula's output; one point per correct case.
    let (v1, o1) = black_box(5u128).overflowing_add(black_box(37u128));
    if !o1 && v1 > 41 && v1 < 43 {
        c += 1; // 1  (no overflow, wrapped value 42)
    }
    let (_, o2) = black_box(u128::MAX).overflowing_add(black_box(1u128));
    if o2 {
        c += 1; // 2  (unsigned add wrap)
    }
    let (_, o3) = black_box(3u128).overflowing_sub(black_box(5u128));
    if o3 {
        c += 1; // 3  (unsigned sub borrow)
    }
    let (v4, o4) = black_box(50u128).overflowing_sub(black_box(8u128));
    if !o4 && v4 > 41 && v4 < 43 {
        c += 1; // 4  (clean unsigned sub, value 42)
    }
    let (_, o5) = black_box(i128::MAX).overflowing_add(black_box(1i128));
    if o5 {
        c += 1; // 5  (signed add positive overflow)
    }
    let (_, o6) = black_box(i128::MIN).overflowing_add(black_box(-1i128));
    let (_, o7) = black_box(i128::MAX).overflowing_add(black_box(-1i128));
    if o6 && !o7 {
        c += 1; // 6  (signed add negative overflow; diff-sign no overflow)
    }
    let (_, o8) = black_box(i128::MIN).overflowing_sub(black_box(1i128));
    let (_, o9) = black_box(10i128).overflowing_sub(black_box(3i128));
    let sat_lo = black_box(5u128).saturating_sub(black_box(20u128)); // clamps to 0
    if o8 && !o9 && sat_lo < 1 {
        c += 1; // 7  (signed sub overflow; clean signed sub; saturating clamp to 0)
    }

    c
}
