#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;

// A niche-encoded NESTED enum matched THROUGH A REFERENCE: `ev` takes `&Outer`,
// so the inner discriminant is `discriminant(((*r) as M).0)` — a deref + downcast
// + field chain. Every arm is exercised via a runtime selector and yields a
// DISTINCT value, so a wrong discriminant (wrong arm) at any nesting level would
// diverge from the LLVM oracle. Pins the deref-plus-projection discriminant path
// in `lower_reference_deref_discriminant`.
enum Inner {
    P(i64),
    Q(i64),
}
enum Outer {
    M(Option<Inner>),
    N(i64),
}

#[inline(never)]
fn mk(s: i64) -> Outer {
    match s {
        0 => Outer::M(Some(Inner::P(bb(5)))),
        1 => Outer::M(Some(Inner::Q(bb(6)))),
        2 => Outer::M(None),
        _ => Outer::N(bb(9)),
    }
}

#[inline(never)]
fn ev(o: &Outer) -> i64 {
    match o {
        Outer::M(Some(Inner::P(v))) => *v + 1,
        Outer::M(Some(Inner::Q(v))) => *v + 2,
        Outer::M(None) => 7,
        Outer::N(v) => *v + 8,
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc = 0i64;
    let mut s = 0i64;
    while s < bb(4) {
        acc = acc.wrapping_mul(107).wrapping_add(ev(&mk(s)));
        s += 1;
    }
    (acc & 0x7f) as i32
}
