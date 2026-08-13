// PC03 ADVERSARIAL (must NOT hoist): the callee is side-effect-free at the
// WRITE level but READS mutable global state that the loop body mutates between
// calls. Its result is therefore NOT loop-invariant even though its explicit
// args are. Hoisting it would freeze a stale read → wrong checksum.
// The purity fixpoint MUST demote `probe` (it contains a Load of a mutable
// static), so it is never eligible for the invariant-call hoist.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

static mut STATE: u64 = 1;

// Reads mutable global → result changes across iterations despite invariant arg.
#[inline(never)]
fn probe(salt: u64) -> u64 {
    unsafe { STATE.wrapping_mul(salt).wrapping_add(7) & 0xff }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 300 {
        acc = acc.wrapping_add(probe(5)); // invariant arg, but reads-mutating STATE
        unsafe {
            STATE = STATE.wrapping_add(rep as u64 + 1);
        }
        rep += 1;
    }
    ((acc ^ 0x33) & 0xff) as i32
}
