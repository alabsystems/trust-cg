// Reaudit gap E: a `static mut` mutated by #[inline(never)] helper FUNCTIONS in
// SEPARATE objects, called from main — exercises the cross-object data import (each
// object IMPORTs the one canonical External definition). Reads back the accumulated
// value (42), pinning the cross-object resolution + the load-not-CSE'd-past-a-call.
#![no_std]
#![no_main]
use core::hint::black_box;
#[panic_handler] fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
static mut ACC: u64 = 0;
#[inline(never)] fn bump(x: u64) { unsafe { ACC = ACC.wrapping_add(x); } }
#[no_mangle] pub extern "C" fn main() -> i32 {
    bump(black_box(30));
    bump(black_box(12));
    unsafe { (ACC % 126) as i32 }
}
