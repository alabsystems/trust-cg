#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;

// A by-VALUE niche-encoded NESTED enum (`Option<Option<Result<..>>>`): the outer
// niches over the inner, which niches over the `Result`. Every arm is exercised
// via a runtime selector and yields a DISTINCT value, so a wrong discriminant
// (wrong match arm) at any nesting level would diverge from the LLVM oracle. This
// pins the niche-encoded nested-enum-field descent in
// `validate_memory_aggregate_field_leaves` + the projected niche discriminant
// decode in `lower_memory_projected_discriminant`.
#[inline(never)]
fn mk(s: i64) -> Option<Option<Result<i64, i64>>> {
    match s {
        0 => Some(Some(Ok(bb(11)))),
        1 => Some(Some(Err(bb(22)))),
        2 => Some(None),
        _ => None,
    }
}

#[inline(never)]
fn ev(a: Option<Option<Result<i64, i64>>>) -> i64 {
    match a {
        Some(Some(Ok(v))) => v + 1,
        Some(Some(Err(v))) => v + 2,
        Some(None) => 3,
        None => 4,
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc = 0i64;
    let mut s = 0i64;
    while s < bb(4) {
        acc = acc.wrapping_mul(103).wrapping_add(ev(mk(s)));
        s += 1;
    }
    (acc & 0x7f) as i32
}
