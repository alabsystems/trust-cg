// GOAL-3 perf baseline benchmark.
// Iterative Fibonacci (wrapping), repeated many times.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 1300000 {
        let mut a: u64 = 0;
        let mut b: u64 = 1;
        let mut i: u32 = 0;
        while i < 90 {
            let t = a.wrapping_add(b);
            a = b;
            b = t;
            i += 1;
        }
        acc = acc.wrapping_add(a);
        rep += 1;
    }
    (acc & 0xff) as i32
}
