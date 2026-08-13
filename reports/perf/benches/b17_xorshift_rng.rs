// GOAL-3 perf baseline benchmark.
// xorshift128+ style PRNG churn — shift/xor/add heavy, tight loop.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut s0: u64 = 0x8a5cd789635d2dff;
    let mut s1: u64 = 0x121fd2155c472f96;
    let mut acc: u64 = 0;
    let mut i: u64 = 0;
    while i < 36000000 {
        let mut x = s0;
        let y = s1;
        s0 = y;
        x ^= x << 23;
        x ^= x >> 17;
        x ^= y ^ (y >> 26);
        s1 = x;
        acc = acc.wrapping_add(x.wrapping_add(y));
        i += 1;
    }
    (acc & 0xff) as i32
}
