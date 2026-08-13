// CORPUS FIXTURE — `Ordering`-VALUE-producing methods (`reverse`, `then`/
// `then_with`, `is_ge`/`is_le`). Matching an `Ordering` already worked once `Cmp`
// landed; these methods additionally RECONSTRUCT an `Ordering` value
// (`discriminant(o); switchInt; _0 = const Ordering::Greater`), which routed an
// Ordering through the scalarized-enum aggregate path and failed closed
// ("Ordering Use from non-place operand" / "Use source discriminant before
// aggregate binding").
//
// The fix keeps `Ordering` off the per-field aggregate path entirely
// (`scalarized_aggregate_kind_name` returns None for the `Ordering` lang item): it
// is a scalar `I8`, so a const/constructed Ordering value is a scalar i8 and
// `switchInt` runs on that i8. Correct at O2/O3 (at -O0 the `cmp`/`reverse`/`then`
// calls are non-inlined library calls -> fail-closed, sound).
//
// (a) reverse maps Less<->Greater; (b) then_with chains a second key; (c) is_ge/
// is_le. All correct -> exit 7.
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
    // (a) reverse: (3 < 8) = Less, reversed = Greater; (9 > 2) = Greater, reversed = Less.
    let ok_a = matches!(black_box(3i32).cmp(&black_box(8i32)).reverse(), Ordering::Greater)
        && matches!(black_box(9i32).cmp(&black_box(2i32)).reverse(), Ordering::Less)
        && matches!(black_box(5i32).cmp(&black_box(5i32)).reverse(), Ordering::Equal);

    // (b) then_with: first key equal, so the second key decides (5 > 3 = Greater).
    let ok_b = matches!(
        black_box(1i32)
            .cmp(&black_box(1i32))
            .then_with(|| black_box(5i32).cmp(&black_box(3i32))),
        Ordering::Greater
    );

    // (c) is_ge / is_le.
    let ok_c =
        black_box(8i32).cmp(&black_box(3i32)).is_ge() && black_box(3i32).cmp(&black_box(8i32)).is_le();

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
