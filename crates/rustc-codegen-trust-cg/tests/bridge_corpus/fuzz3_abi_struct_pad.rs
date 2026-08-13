// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// #[inline(never)] fn returning a by-value #[repr(C)] struct { u8, u64 } with
// internal padding (two-eightbyte INTEGER ABI return). Agree O0/O2/O3 -> 95.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    #[repr(C)] #[derive(Clone, Copy)]
    struct S { a: u8, b: u64 }
    #[inline(never)]
    fn make(x: u64) -> S { S { a: (x & 0xff) as u8, b: x * 1000 } }
    let s = make(black_box(7));
    let r = s.a as u64 + s.b;
    (r & 0xff) as i32
}
