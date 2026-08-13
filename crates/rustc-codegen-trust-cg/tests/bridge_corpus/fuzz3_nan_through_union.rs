// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// qNaN bit pattern 0x7FF8.. reinterpreted u64->f64 through a union, `is_nan()`
// branch + `to_bits()` round-trip (bit-exact float pun, no NaN-canonicalization).
// Agree O0/O2/O3 -> 49.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    union U { f: f64, b: u64 }
    let n = black_box(0x7FF8000000000000u64);
    let u = U { b: n };
    let f = unsafe { u.f };
    let mut r = 0u64;
    if f.is_nan() { r += 50; }
    let back = f.to_bits();
    r += back >> 52;
    (r & 0xff) as i32
}
