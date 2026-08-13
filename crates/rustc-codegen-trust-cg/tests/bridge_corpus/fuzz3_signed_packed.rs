// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// #[repr(packed)] struct { i8, i32, i16 } with negative values — MISALIGNED
// signed narrow loads sign-extend correctly. Agree O0/O2/O3 -> 107.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    #[repr(packed)] #[derive(Clone, Copy)]
    struct P { a: i8, b: i32, c: i16 }
    let p = P { a: black_box(-1), b: black_box(-100000), c: black_box(-500) };
    let a = p.a; let b = p.b; let c = p.c;
    let r: i64 = a as i64 + b as i64 + c as i64;
    ((r & 0xff) as u8) as i32
}
