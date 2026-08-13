// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// #[inline(never)] fn returning a by-value #[repr(C)] struct { u8, u16, u32 }
// (mixed-width single-eightbyte INTEGER-class ABI return), fields recombined in
// the caller. Agree O0/O2/O3 -> 181.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    #[repr(C)] #[derive(Clone, Copy)]
    struct M { a: u8, b: u16, c: u32 }
    #[inline(never)]
    fn make(x: u32) -> M { M { a: (x & 0xff) as u8, b: (x + 1) as u16, c: x * 7 } }
    let m = make(black_box(20));
    let r = m.a as u32 + m.b as u32 + m.c;
    (r & 0xff) as i32
}
