// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// #[repr(C)] struct { i8, i16, i32, i64 } with NEGATIVE values — each narrow
// field load must sign-extend (movsx not movzx) before widening to i64; a movzx
// would diverge. Agree O0/O2/O3 -> 99.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    #[repr(C)] #[derive(Clone, Copy)]
    struct S { a: i8, b: i16, c: i32, d: i64 }
    let s = S { a: black_box(-1), b: black_box(-300), c: black_box(-70000), d: black_box(-5000000000) };
    let r: i64 = s.a as i64 + s.b as i64 + s.c as i64 + s.d;
    ((r & 0xff) as u8) as i32
}
