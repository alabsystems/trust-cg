// PC09 POSITIVE: two DIFFERENT pure fns in one loop (distinct clusters).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
fn ack(m: u64, n: u64) -> u64 {
    if m == 0 { n + 1 } else if n == 0 { ack(m - 1, 1) } else { ack(m - 1, ack(m, n - 1)) }
}
fn fib(n: u64) -> u64 { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0; let mut r: u32 = 0;
    while r < 400 { acc = acc.wrapping_add(ack(2, 4)); acc = acc.wrapping_add(fib(10)); r += 1; }
    ((acc ^ 0x77) & 0xff) as i32
}
