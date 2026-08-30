// PC07 POSITIVE: a DOWN-counting `while i > 0` loop (different guard cc than <).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
fn ack(m: u64, n: u64) -> u64 {
    if m == 0 { n + 1 } else if n == 0 { ack(m - 1, 1) } else { ack(m - 1, ack(m, n - 1)) }
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0; let mut i: u32 = 300;
    while i > 0 { acc = acc.wrapping_add(ack(2, 6)); i -= 1; }
    ((acc ^ 0x22) & 0xff) as i32
}
