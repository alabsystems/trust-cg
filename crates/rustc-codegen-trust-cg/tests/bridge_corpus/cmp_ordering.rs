// CORPUS FIXTURE — the three-way comparison `Cmp` / `core::cmp::Ordering`
// (`i32::signum`, `Ord::cmp`, `cmp::max`/`min`). Before this lowering the
// `Ordering` type itself didn't convert ("Ty::core::cmp::Ordering") and the `Cmp`
// binop / `discriminant(Ordering)` were unmodeled, so every comparison-producing-
// Ordering form failed closed.
//
// Now correct at O0/O2/O3: `Ordering` (the `#[lang = "Ordering"]` enum, `#[repr(i8)]`
// with Less/Equal/Greater = -1/0/1) is modeled as an `I8` scalar whose value IS its
// discriminant; `Cmp(a, b)` is `gt ? 1 : (lt ? -1 : 0)` built from two proven
// Selects over signed/unsigned `ICmp`s; `discriminant(ordering)` is the identity;
// `ordering as iN` is a plain integer cast. No new proof obligation.
//
// Checks: (a) signum's three outcomes; (b) signed vs UNSIGNED comparison
// correctness (`0x8000_0000u32 > 1` is Greater unsigned, not Less); (c) max/min.
// All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::cmp::Ordering;
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) signum: -1 / 0 / 1.
    let ok_a = black_box(-9i32).signum() == -1
        && black_box(0i32).signum() == 0
        && black_box(9i32).signum() == 1;

    // (b) signed vs unsigned: as u32, 0x8000_0000 > 1 (Greater); as i32, -5 < 3 (Less).
    let ok_b = matches!(black_box(0x8000_0000u32).cmp(&black_box(1u32)), Ordering::Greater)
        && matches!(black_box(-5i32).cmp(&black_box(3i32)), Ordering::Less)
        && matches!(black_box(7u32).cmp(&black_box(7u32)), Ordering::Equal);

    // (c) Ord::max / min (built on Ord::cmp).
    let ok_c = core::cmp::max(black_box(13i32), black_box(27i32)) == 27
        && core::cmp::min(black_box(13i32), black_box(27i32)) == 13;

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
