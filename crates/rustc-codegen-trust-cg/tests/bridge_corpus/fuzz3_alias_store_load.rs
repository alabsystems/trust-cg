// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// Two `*mut u64` raw pointers to the SAME local, store through one + load through
// the other (must not assume no-alias / must not drop the forwarded store).
// Agree O0/O2/O3 -> 15.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    let mut x = black_box(3u64);
    let p = &mut x as *mut u64;
    let q = &mut x as *mut u64;
    unsafe {
        *p = 10;
        let a = *q;
        *q = a + 5;
    }
    (x & 0xff) as i32
}
