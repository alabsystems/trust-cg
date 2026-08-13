// PC06 POSITIVE: a 1-arg pure fn (tests n_args=1 cluster recognition).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
fn collatz_len(mut n: u64) -> u64 {
    let mut c = 0u64;
    while n != 1 { n = if n & 1 == 0 { n / 2 } else { 3 * n + 1 }; c += 1; }
    c
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0; let mut r: u32 = 0;
    while r < 500 { acc = acc.wrapping_add(collatz_len(27)); r += 1; }
    ((acc ^ 0x11) & 0xff) as i32
}
