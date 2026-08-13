// PC10 ADVERSARIAL: 2-arg pure call, ONE arg invariant, ONE loop-variant.
// The cluster's invariance check must reject it (a partial hoist would freeze
// the variant arg).
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
    while r < 40 { acc = acc.wrapping_add(ack(2, (r % 7) as u64)); r += 1; }
    ((acc ^ 0x99) & 0xff) as i32
}
