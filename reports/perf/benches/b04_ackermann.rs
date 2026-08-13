// GOAL-3 perf baseline benchmark.
// Recursive Ackermann (small m,n) repeated; exercises call/return + recursion.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

fn ack(m: u64, n: u64) -> u64 {
    if m == 0 {
        n + 1
    } else if n == 0 {
        ack(m - 1, 1)
    } else {
        ack(m - 1, ack(m, n - 1))
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 1800 {
        // ack(2, n) and ack(3, n) for small n.
        acc = acc.wrapping_add(ack(2, 9));
        acc = acc.wrapping_add(ack(3, 5));
        rep += 1;
    }
    ((acc ^ 0xa5) & 0xff) as i32
}
