// CORPUS FIXTURE — `.scan(state, f).sum()` (an UNMODELED adapter reduction).
//
// FOUND BY FUZZ-2 differential sweep. `Scan` is not a modeled adapter, so the
// `.sum()` terminal cannot drive the chain; the general path compiled the real
// `<i64 as Sum>::sum::<Scan<..>>` whose reachable `<Scan as Iterator>::try_fold`
// was TRAPPED as a (wrongly-assumed-dead) ud2 stub and HIT at runtime -> SIGILL
// (a TrapMismatch, not a clean fail-closed). Now the sum/fold/count terminal fails
// CLOSED at compile time when its chain is unmodeled (and `scan` bodies are excluded
// from the dead-iterator trap), so this rejects at compile time rather than SIGILL.
//
// LLVM: 1,3,6,10,15 -> 35.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let n = bb(6i64);
    let s: i64 = (1..n).scan(0i64, |acc, x| { *acc += x; Some(*acc) }).sum();
    (s & 0xff) as i32
}
