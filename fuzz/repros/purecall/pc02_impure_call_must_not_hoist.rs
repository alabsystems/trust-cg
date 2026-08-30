// PC02 ADVERSARIAL (must NOT hoist): the callee writes to a static (observable
// side effect). Even with loop-invariant args, hoisting it out of the loop would
// change how many times the store runs → the accumulated static must differ.
// The purity fixpoint MUST demote `bump` (it contains a Store), so the hoist
// never fires. Checksum must be identical hoist ON vs OFF (i.e. the hoist stays
// disabled for this call).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

static mut COUNTER: u64 = 0;

// IMPURE: writes global state; its "return" is invariant but its effect is not.
#[inline(never)]
fn bump(k: u64) -> u64 {
    unsafe {
        COUNTER = COUNTER.wrapping_add(k);
        COUNTER & 0xff
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 500 {
        acc = acc.wrapping_add(bump(3)); // invariant arg, but IMPURE → must run 500x
        rep += 1;
    }
    // Depends on COUNTER having been bumped exactly 500 times.
    let total = unsafe { COUNTER };
    ((acc ^ total) & 0xff) as i32
}
