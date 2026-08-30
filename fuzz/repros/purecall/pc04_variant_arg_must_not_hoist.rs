// PC04 ADVERSARIAL (must NOT hoist): the callee IS pure, but its argument is
// loop-VARIANT (depends on the induction variable). The invariance test on the
// arg-setup sources MUST fail → no hoist. Hoisting would freeze the arg at one
// value → wrong checksum.
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
    while rep < 60 {
        // n = (rep % 5) is loop-VARIANT → not hoistable.
        acc = acc.wrapping_add(ack(2, (rep % 5) as u64));
        rep += 1;
    }
    ((acc ^ 0x0f) & 0xff) as i32
}
