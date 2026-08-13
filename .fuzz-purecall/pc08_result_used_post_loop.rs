// PC08 POSITIVE: the hoisted call's result is ALSO used AFTER the loop
// (tests result-vreg dominance/liveness past the loop exit).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
fn ack(m: u64, n: u64) -> u64 {
    if m == 0 { n + 1 } else if n == 0 { ack(m - 1, 1) } else { ack(m - 1, ack(m, n - 1)) }
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0; let mut r: u32 = 0;
    let v = ack(2, 5);
    while r < 400 { acc = acc.wrapping_add(v); r += 1; }
    acc = acc.wrapping_add(v); // v used after the loop too
    ((acc ^ 0x44) & 0xff) as i32
}
