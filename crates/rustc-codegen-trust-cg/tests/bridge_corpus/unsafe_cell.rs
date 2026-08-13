// CORPUS FIXTURE — `UnsafeCell<T>` interior mutability (`UnsafeCell::new` /
// `.get()` / read+write through the raw pointer). `UnsafeCell<u32>` is a
// transparent newtype the bridge types as the inner scalar (`U32`), so
// `UnsafeCell::get` = `&raw const cell` is a raw pointer to that scalar — which
// failed closed: the scalar cell-pass only celled primitive `ty::Int/Uint/...`
// referents (not a transparent scalar-newtype ADT), and a celled local's
// `cell = UnsafeCell { value: v }` construct (an Aggregate into a scalar place) had
// no handler.
//
// The fix cells a referent whose trust-ir type is a NON-pointer scalar (covering a
// transparent scalar newtype, excluding `Vec`-as-`Ptr`), and stores a transparent
// single-scalar-field aggregate construct as its inner scalar. So `&raw const cell`
// is the cell's stable address, and reads/writes through `*c.get()` route through
// it.
//
// (a) read a value written at construction; (b) write through `*c.get()` then read
// it back. Both correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::cell::UnsafeCell;
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) read through `get()` the value the cell was constructed with.
    let a = UnsafeCell::new(black_box(7u32));
    let ok_a = unsafe { *a.get() } == 7;

    // (b) write through `*c.get()`, then read it back.
    let b = UnsafeCell::new(black_box(3u32));
    unsafe {
        *b.get() = black_box(7);
    }
    let ok_b = unsafe { *b.get() } == 7;

    if ok_a && ok_b {
        7
    } else {
        13
    }
}
