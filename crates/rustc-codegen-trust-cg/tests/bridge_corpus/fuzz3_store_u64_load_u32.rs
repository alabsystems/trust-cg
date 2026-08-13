// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// Store a u64 through *mut u64, immediately load the low and high halves through
// `*const u32` / `.add(1)` (sub-slot partial-overlap load forwarding).
// Agree O0/O2/O3 -> 204.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    let mut x = black_box(0u64);
    let p = &mut x as *mut u64;
    unsafe {
        *p = 0x1122334455667788;
        let lo = *(p as *const u32);
        let hi = *((p as *const u32).add(1));
        ((lo.wrapping_add(hi)) & 0xff) as i32
    }
}
