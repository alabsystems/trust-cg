// GOAL-3 perf baseline benchmark.
// Bit manipulation: manual popcount (Kernighan) + bit reverse loop.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[inline(never)]
fn popcount(mut x: u64) -> u32 {
    let mut c = 0u32;
    while x != 0 {
        x &= x - 1;
        c += 1;
    }
    c
}

#[inline(never)]
fn bitrev(mut x: u64) -> u64 {
    let mut r: u64 = 0;
    let mut i = 0;
    while i < 64 {
        r = (r << 1) | (x & 1);
        x >>= 1;
        i += 1;
    }
    r
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut v: u64 = 0x9e3779b97f4a7c15;
    let mut i: u64 = 0;
    while i < 700000 {
        v = v.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        acc = acc.wrapping_add(popcount(v) as u64);
        acc ^= bitrev(v) >> 32;
        i += 1;
    }
    (acc & 0xff) as i32
}
