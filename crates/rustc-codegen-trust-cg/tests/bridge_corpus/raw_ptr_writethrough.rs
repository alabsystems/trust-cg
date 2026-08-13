// CORPUS FIXTURE — a raw pointer to a scalar local observes (and is observed by)
// real memory at every access. Before the `Rvalue::RawPtr`-of-a-scalar lowering,
// taking `&x as *mut/*const T` / `addr_of!(x)` of a primitive scalar failed
// closed ([TCG-MIR-UNSUPPORTED] Rvalue::RawPtr). The fix cells the referent
// (gives it a stable stack slot) and binds the raw pointer to that address, so a
// `*p = v` write hits `x`'s storage, a later direct `x` read sees it, a direct
// `x` mutation is seen by a `*p` read, and two raw pointers to the same scalar
// alias the one slot.
//
// Three independent checks, all must hold -> exit 7:
//   (a) `*p = 99` through a `*mut` makes `x == 99`;
//   (b) mutating `y` directly is observed by a `*const` deref (cell, not snapshot);
//   (c) write via `pz`, read via its copy `qz` — aliasing through one slot.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) write-through a `*mut` is observed by a direct read of `x`.
    let mut x: u32 = black_box(10);
    let p = &mut x as *mut u32;
    unsafe {
        *p = black_box(99);
    }
    let ok_a = x == 99;

    // (b) a direct mutation of `y` is observed through a `*const` deref.
    let mut y: u32 = black_box(5);
    let py = &y as *const u32;
    y = black_box(123);
    let ok_b = unsafe { *py } == 123;

    // (c) write via `pz`, read via its alias copy `qz`.
    let mut z: u32 = black_box(1);
    let pz = &mut z as *mut u32;
    let qz = pz;
    unsafe {
        *pz = black_box(200);
    }
    let ok_c = unsafe { *qz } == 200;

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
