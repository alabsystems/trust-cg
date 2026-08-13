// GOAL-3 perf baseline benchmark.
// Collatz step-count over a range of starting values, repeated.
// Branch + mixed mul/div/mod heavy.
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
    while rep < 30 {
        let mut start: u64 = 2 + rep as u64;
        let mut total: u64 = 0;
        while start < 20000 {
            let mut n = start;
            let mut steps: u64 = 0;
            while n != 1 {
                if n & 1 == 0 {
                    n /= 2;
                } else {
                    n = n.wrapping_mul(3).wrapping_add(1);
                }
                steps += 1;
            }
            total = total.wrapping_add(steps);
            start += 1;
        }
        acc = acc.wrapping_add(total);
        rep += 1;
    }
    (acc & 0xff) as i32
}
