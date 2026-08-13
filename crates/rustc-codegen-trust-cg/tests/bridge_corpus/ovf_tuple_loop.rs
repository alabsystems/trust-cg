// CORPUS FIXTURE — loop-carried `(iN, bool)` overflow tuple (piece-3 loop VC).
// `p = p.0.overflowing_add(K)` in a loop: at O2/O3 the loop-carried tuple is
// scalarized into the wrapped i32 (p.0) and the overflow FLAG (p.1), both threaded
// through header slots. The back-edge threading VC PROVES the flag slot by binding
// it (on both the MIR spec and the trust-ir impl) to a shared uninterpreted overflow
// symbol, so the loop is admitted by proof instead of the structural false-reject
// [TCG-SSA-071]. (Before: the SPEC walk bailed on the non-scalar `(i32, bool)` temp.)
// O0 uses the non-inlined `overflowing_add` library CALL on the loop path — an
// orthogonal fail-closed (safe, not a miscompile). Correct exit = LLVM oracle.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut p: (i32, bool) = (bb(1i32), false);
    let mut i: i32 = 0;
    while i < bb(40i32) {
        p = p.0.overflowing_add(bb(100000000i32));
        i += 1;
    }
    ((p.0 & 0x7f) + if p.1 { 1 } else { 0 }) as i32
}
