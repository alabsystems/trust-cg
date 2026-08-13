// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// `union U { v: u64, halves: [u32;2] }` — write both [u32;2] lanes then read the
// combined u64 field (union field write + differently-typed whole read).
// Agree O0/O2/O3 -> 173.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    union U { v: u64, halves: [u32; 2] }
    let mut u = U { v: black_box(0u64) };
    unsafe { u.halves[0] = 0xDEAD; u.halves[1] = 0xBEEF; }
    let combined = unsafe { u.v };
    let r = (combined >> 16) ^ (combined & 0xffff);
    (r & 0xff) as i32
}
