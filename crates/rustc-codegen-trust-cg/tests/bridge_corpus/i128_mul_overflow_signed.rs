// CORPUS FIXTURE — SIGNED `i128` `overflowing_mul` / `checked_mul`. The adapter
// rejects `Inst::Overflow` on 128-bit (the multiply needs a 256-bit product), and the
// signed division identity is hazardous on x86 because IDIV traps on BOTH `/0` AND
// `i128::MIN / -1`. The bridge composes the overflow flag from PROVEN i128 primitives
// while guarding both traps:
//   a == 0  -> no overflow
//   a == -1 -> overflow iff b == i128::MIN
//   else    -> overflow iff wrapped /s a != b   (a outside {0,-1} never traps)
// realized branch-free with selects that map the trapping divisors {0,-1} to a safe
// `2` before the divide. Each emitted op carries its own per-instruction cert.
//
// The dangerous cases are the trap-prone ones — MIN*-1, -1*MIN, MIN*MIN — which must
// detect overflow WITHOUT executing a trapping IDIV. All correct -> exit 7.
// (O0 fails closed on the range-iterator library helper.)
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // A boundary matrix: (a, b, expected-overflow). One point if all predictions hold.
    let cases: [(i128, i128, bool); 12] = [
        (black_box(6), black_box(7), false),            // 42, fits
        (black_box(i128::MIN), black_box(-1), true),    // MIN * -1 overflows (trap-prone)
        (black_box(-1), black_box(i128::MIN), true),    // symmetric
        (black_box(i128::MIN), black_box(1), false),    // MIN * 1 fits
        (black_box(i128::MIN), black_box(2), true),      // MIN * 2 overflows
        (black_box(i128::MAX), black_box(-1), false),   // MAX * -1 = -MAX fits
        (black_box(i128::MAX), black_box(2), true),      // MAX * 2 overflows
        (black_box(0), black_box(i128::MIN), false),    // 0 * anything fits
        (black_box(-7), black_box(6), false),           // -42 fits
        (black_box(1i128 << 70), black_box(1i128 << 70), true), // 2^140 overflows (positive)
        (black_box(-(1i128 << 70)), black_box(1i128 << 70), true), // -2^140 overflows (negative)
        (black_box(2), black_box(i128::MAX / 2 + 1), true), // just over
    ];
    let mut ok = 0i32;
    let mut i = 0usize;
    while i < 12 {
        let (a, b, exp) = cases[i];
        let (_, o) = a.overflowing_mul(b);
        if o == exp {
            ok += 1;
        }
        i += 1;
    }
    let m1 = ok == 12;

    // checked_mul: the MIN*-1 trap case must yield None (overflow) without trapping.
    let m2 = black_box(6i128).checked_mul(black_box(7i128)).is_some()
        && black_box(i128::MIN).checked_mul(black_box(-1i128)).is_none()
        && black_box(i128::MAX).checked_mul(black_box(2i128)).is_none();

    if m1 && m2 {
        7
    } else {
        13
    }
}
