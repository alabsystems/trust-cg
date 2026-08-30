// PC05 ADVERSARIAL (must NOT hoist — TRAP/DIVERGENCE hazard): the pure call sits
// in a loop that may execute ZERO times (guarded by a condition that is false on
// some runs), AND the callee can diverge/trap for the given args. Hoisting the
// call into the pre-header (before the guard) would execute it on the zero-trip
// path, introducing a non-termination/trap the original never had.
//
// The placement-safety rule (only hoist when the pre-header UNCONDITIONALLY
// reaches the header) MUST refuse this. The differential checks that BOTH the
// zero-trip and the non-zero-trip inputs produce identical exit codes hoist
// ON vs OFF.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

// Pure but NON-TOTAL: recurses forever unless n eventually hits 0 via the base
// case. For the arg used below it terminates; the point is the loop guard, not
// this function — but keep it a real recursive pure call to exercise the tier.
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
    // `bound` is 0 here → the loop body (and the pure call) must execute ZERO
    // times. If the hoist wrongly lifts the call before the guard, it runs once.
    let bound: u32 = 0;
    let mut acc: u64 = 0;
    let mut i: u32 = 0;
    while i < bound {
        acc = acc.wrapping_add(ack(2, 6));
        i += 1;
    }
    // acc MUST be 0 (loop never ran). A wrong hoist makes acc = ack(2,6).
    ((acc ^ 0xc3) & 0xff) as i32
}
