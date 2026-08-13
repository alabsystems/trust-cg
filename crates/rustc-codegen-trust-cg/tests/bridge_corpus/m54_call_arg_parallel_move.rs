// CORPUS FIXTURE — bug #54: multi-arg call parallel-move (cyclic register
// permutation). Passing args in reverse forces register swaps among
// rdi/rsi/rdx/rcx; a naive sequential move clobbers one.
// Correct exit: (4*27 + 3*9 + 2*3 + 1) & 0xff = 142 & 0xff = 142.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[inline(never)]
fn sub4(a: i64, b: i64, c: i64, d: i64) -> i64 { a * 27 + b * 9 + c * 3 + d }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = black_box(1i64);
    let b = black_box(2i64);
    let c = black_box(3i64);
    let d = black_box(4i64);
    (sub4(d, c, b, a) & 0xff) as i32
}
