// CORPUS FIXTURE — bug #55: by-ref closure capture. A closure capturing a local
// by mutable reference and mutating it; both adds must persist to the enclosing
// frame after the closure runs.
// Correct exit: (11 + 31) & 0xff = 42.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: i64 = black_box(0);
    let mut add = |v: i64| { acc += v; };
    add(black_box(11));
    add(black_box(31));
    (acc & 0xff) as i32
}
