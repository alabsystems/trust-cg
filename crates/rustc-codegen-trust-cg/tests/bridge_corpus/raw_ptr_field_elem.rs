// CORPUS FIXTURE — a raw pointer to a PROJECTED sub-place of an aggregate
// (`addr_of!(s.field)`, `addr_of!(a[i])`, nested `o.inner.field`). Before the
// projected-`Rvalue::RawPtr` lowering these failed closed ([TCG-MIR-UNSUPPORTED]
// Rvalue::RawPtr): unlike a *reference* to a field (which the scalarized path
// represents with a borrowed-scalar snapshot), a raw pointer needs the field to
// have a REAL address. The fix forces the base aggregate memory-backed
// (compute_memory_backed_locals case 4d) and binds the pointer to `slot +
// field_offset` / `slot + i*stride` via `memory_place_address` — so a write
// through the pointer hits the field's storage and a later direct read sees it.
//
// Three checks (struct field, array element, nested field), each a write-through
// observed by a direct read -> exit 7.
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
    // (a) struct field: write `s.b` through `addr_of_mut!`, read it + the untouched `s.a`.
    let mut s = S {
        a: black_box(11),
        b: black_box(22),
    };
    let pb = core::ptr::addr_of_mut!(s.b);
    unsafe {
        *pb = black_box(99);
    }
    let ok_a = s.a == 11 && s.b == 99;

    // (b) array element: write `a[i]` (runtime index) through `addr_of_mut!`.
    let mut a: [u32; 4] = [black_box(1), black_box(2), black_box(3), black_box(4)];
    let i = black_box(2usize);
    let pe = core::ptr::addr_of_mut!(a[i]);
    unsafe {
        *pe = black_box(50);
    }
    let ok_b = a[0] == 1 && a[2] == 50 && a[3] == 4;

    // (c) nested struct field: write `o.inner.y` through a nested projection.
    let mut o = Outer {
        a: black_box(1),
        inner: Inner {
            x: black_box(10),
            y: black_box(20),
        },
    };
    let py = core::ptr::addr_of_mut!(o.inner.y);
    unsafe {
        *py = black_box(7);
    }
    let ok_c = o.inner.x == 10 && o.inner.y == 7;

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
