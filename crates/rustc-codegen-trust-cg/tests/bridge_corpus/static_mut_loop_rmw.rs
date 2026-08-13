// Reaudit gap E boundary pin: a `static mut` read-modify-write whose next iteration
// depends on the stored value (true loop-carried THROUGH the static, across the back
// edge). The back-edge faithfulness gate must keep this either CORRECT or
// FAIL-CLOSED — NEVER a dropped-store miscompile (the union-loop store-drop class).
// At O0 it compiles (x_{k+1}=2x_k+1 from 1, 10 iters -> 2047 % 120 = 7); at O2/O3 the
// gate may refuse a loop-carried *mut scalarization (sound fail-closed). The corpus
// test accepts MATCH or fail-closed; a Divergence (wrong value) fails the test.
#![no_std]
#![no_main]
use core::hint::black_box;
#[panic_handler] fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
static mut X: u32 = 1;
#[no_mangle] pub extern "C" fn main() -> i32 {
    unsafe {
        let n = black_box(10u32);
        let mut i = 0u32;
        while i < n { X = X.wrapping_mul(2).wrapping_add(1); i += 1; }
        (X % 120) as i32
    }
}
