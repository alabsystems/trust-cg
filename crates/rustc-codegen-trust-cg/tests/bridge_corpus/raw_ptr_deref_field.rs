// CORPUS FIXTURE — a raw pointer to a PROJECTED sub-place reached THROUGH a
// reference: `&raw const (*r).field` / `&raw mut (*r).field` / `&raw (*r)[i]`.
// This is the `&raw const (*self).v` shape an atomic's inner-value pointer takes,
// and a `&raw mut (*r).field` write-through. It failed closed ([TCG-MIR-UNSUPPORTED]
// Rvalue::RawPtr): the projected-RawPtr lowering handled `addr_of!(s.field)` of a
// memory-backed local but EXCLUDED a leading Deref (it has no slot on `r`).
//
// The address is `r's pointer value + field_offset / i*stride`: bind `r`'s bound
// pointer as the base and resolve the Field/Downcast/Index chain after the leading
// Deref through the pointee's layout. Correct at O2/O3.
//
// (a) read through `(*r).field`; (b) write-through `(*r).field` (siblings untouched);
// (c) nested `(*r).inner.field`. All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

struct S {
    a: u32,
    b: u32,
    c: u32,
}
struct Inner {
    x: u32,
    y: u32,
}
struct Outer {
    a: u32,
    inner: Inner,
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) read through a shared reference.
    let s0 = S {
        a: black_box(11),
        b: black_box(7),
        c: black_box(13),
    };
    let r0 = &s0;
    let pr = core::ptr::addr_of!((*r0).b);
    let ok_a = unsafe { *pr } == 7;

    // (b) write-through a mutable reference; siblings untouched.
    let mut s1 = S {
        a: black_box(1),
        b: black_box(2),
        c: black_box(3),
    };
    let r1 = &mut s1;
    let pw = core::ptr::addr_of_mut!((*r1).b);
    unsafe {
        *pw = black_box(99);
    }
    let ok_b = s1.a == 1 && s1.b == 99 && s1.c == 3;

    // (c) nested field through a reference.
    let mut o = Outer {
        a: black_box(1),
        inner: Inner {
            x: black_box(2),
            y: black_box(5),
        },
    };
    let r2 = &mut o;
    let py = core::ptr::addr_of_mut!((*r2).inner.y);
    unsafe {
        *py = black_box(7);
    }
    let ok_c = o.inner.x == 2 && o.inner.y == 7;

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
