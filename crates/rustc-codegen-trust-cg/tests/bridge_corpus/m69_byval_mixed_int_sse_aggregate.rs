// CORPUS FIXTURE — bug #69: by-value aggregate with a MIXED INT+SSE eightbyte.
// `struct{a:i64, x:f64}` is one INTEGER eightbyte and one SSE eightbyte under
// SysV; passed by value it must go in {rdi (or stack), xmm0}. Mis-placing the
// SSE half into a GPR corrupts the float on the callee side.
// Correct exit: (7 + 35) & 0xff = 42.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
struct Mixed { a: i64, x: f64 }
#[inline(never)]
fn use_mixed(m: Mixed) -> i64 {
    m.a + (m.x as i64)
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let m = Mixed { a: black_box(7), x: black_box(35.0_f64) };
    (use_mixed(m) & 0xff) as i32
}
