// CORPUS FIXTURE / REGRESSION GUARD — a `union` LOCAL mutated across a loop
// back-edge. A union maps to a single scalar via the union-ABI path, but a projected
// `u.field = v` / whole `u = U { .. }` reassignment inside a loop is NOT registered
// as a loop-carried scalar def and is NOT memory-backed (only address-taken unions
// are), so its in-loop store-back was silently DROPPED — every iteration read the
// pre-loop value (a `union { i: u32 }` accumulator returned its INITIAL value;
// found by reaudit, was llvm=31 / tcg=1). The loop-carried-union case now FAILS
// CLOSED rather than miscompiling (loop_carried_aggregate_error).
//
// This fixture exists to PIN that: the differential harness treats trust-cg
// fail-closed as a non-failing note, but a *** Divergence *** (compile-and-
// miscompile) FAILS the test. So if a future change makes a loop-carried union
// emit code again, this fixture catches a wrong value; if it is properly threaded
// (correct code), it MATCHes. Either way it can never silently regress to a
// miscompile. Expected value when correct: 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

union U {
    i: u32,
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // u.i: 1 -> 11 -> 21 -> 31 over 3 iterations; (31 - 24) = 7.
    let mut u = U { i: black_box(1u32) };
    let mut i = 0u32;
    while i < black_box(3u32) {
        u.i = unsafe { u.i }.wrapping_add(10);
        i += 1;
    }
    (unsafe { u.i } as i32) - 24
}
