// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// `static mut BUF: [u32;8]` written then summed in a loop (cross-object mutable
// global array store/load through the data symbol). Agree O0/O2/O3 -> 92.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    static mut BUF: [u32; 8] = [0; 8];
    unsafe {
        for i in 0..black_box(8usize) { BUF[i] = (i as u32) * 3 + 1; }
        let mut s = 0u32;
        for i in 0..8 { s += BUF[i]; }
        (s & 0xff) as i32
    }
}
