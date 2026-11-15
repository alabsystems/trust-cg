// PC11 ADVERSARIAL (must NOT hoist — TRAP/DIVERGENCE hazard, OD-230): the loop
// certainly runs (0..10), but the pure call sits in a CONDITIONAL ARM that no
// iteration takes (`i == LIMIT`, LIMIT = 1000, read opaquely). The callee
// overflows the stack for its argument. The source never calls it, so it
// returns normally; hoisting the call into the preheader would crash the run.
//
// Before OD-230 the tier required only that the loop runs at least once and
// took the call from any loop block, so it hoisted this one. It now hoists only
// from the first iteration's straight path, which the arm is not on.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

// Pure (no memory, self-recursive), and not a tail call: each level keeps a
// frame, so `deep(1 << 40)` overflows the stack long before it returns.
fn deep(n: u64) -> u64 {
    if n == 0 { 0 } else { 1 + deep(n - 1) }
}

// Mutable statics, so no pass may assume their values and fold the arm away.
// (Not `read_volatile`: the bridge refuses the `volatile_load` intrinsic.)
static mut LIMIT: u32 = 1000;
static mut DEPTH: u64 = 1 << 40;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let limit = unsafe { LIMIT };
    let depth = unsafe { DEPTH };
    let mut acc: u64 = 0;
    let mut i: u32 = 0;
    while i < 10 {
        if i == limit {
            acc = acc.wrapping_add(deep(depth));
        }
        acc = acc.wrapping_add(i as u64);
        i += 1;
    }
    // acc = 0 + 1 + ... + 9 = 45; exit code 45 ^ 0x3c.
    ((acc ^ 0x3c) & 0xff) as i32
}
