// CORPUS FIXTURE — `Cell<T>` interior mutability (`Cell::new` / `get` / `set` /
// `replace`). `Cell<u32>` is TRANSPARENT over `UnsafeCell<u32>` over `u32` (two
// transparent levels), so it types as the inner scalar — but it failed closed
// where `UnsafeCell` alone did not: `Cell::get/set` is `&raw const (cell.0)` (a
// Field-projected RawPtr of the transparent scalar) and `Cell::new` is the NESTED
// construct `Cell { UnsafeCell { v } }`, whose inner level was bound field-wise
// (projected) then read whole as a scalar.
//
// Two pieces close it, both reusing the `UnsafeCell` foundation: (1) a single
// `Field` projection of a celled transparent scalar addresses offset 0 (the cell
// pointer); (2) a single-scalar newtype CONSTRUCT (`adt_maps_to_single_scalar`)
// binds the dest's scalar value to its one non-ZST field — so nested transparent
// wrappers collapse to the inner scalar, and `finish_assign_target` stores it into
// the cell for an address-taken `Cell`.
//
// (a) set overwrites the constructed value; (b) replace returns the old + sets new;
// (c) a `Cell` accumulator mutated across a loop. All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::cell::Cell;
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) set overwrites the construction value.
    let a = Cell::new(black_box(99u32));
    a.set(black_box(7));
    let ok_a = a.get() == 7;

    // (b) replace returns the OLD value and stores the new one.
    let b = Cell::new(black_box(3u32));
    let old = b.replace(black_box(10));
    let ok_b = old == 3 && b.get() == 10;

    // (c) a Cell accumulator mutated across a loop (interior mutability).
    let c = Cell::new(0u32);
    let mut i = 0u32;
    while i < black_box(7u32) {
        c.set(c.get() + 1);
        i += 1;
    }
    let ok_c = c.get() == 7;

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
