// CORPUS FIXTURE — bug #67: overflowing_mul by zero (TrapMismatch shape).
// `5i32.overflowing_mul(0)` SIGFPE'd on x86 (IDIV-based overflow check by zero)
// while LLVM returns (0, false). trust-cg trap vs LLVM value = TrapMismatch.
// Correct exit: (0 + 0) & 0xff = 0.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = black_box(5i32);
    let b = black_box(0i32);
    let (v, o) = a.overflowing_mul(b);
    ((v + o as i32) & 0xff) as i32
}
