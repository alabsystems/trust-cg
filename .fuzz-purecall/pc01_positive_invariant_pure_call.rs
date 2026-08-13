// PC01 POSITIVE: a pure function called with loop-invariant args inside a hot,
// guaranteed->=1-iteration loop. The pure-call hoist SHOULD fire here; the
// checksum must be identical with the hoist ON vs OFF. (Mirrors b04_ackermann's
// shape but smaller so it runs fast in the differential.)
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

// Pure: result depends only on args, no memory writes, self-recursive.
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
    while rep < 400 {
        // Invariant args (2,7) — same every iteration → hoistable.
        acc = acc.wrapping_add(ack(2, 7));
        rep += 1;
    }
    ((acc ^ 0x5a) & 0xff) as i32
}
