// CORPUS FIXTURE (OPT-6b) — verified elimination of a RUNTIME-index array
// bounds check made redundant by a DOMINATING compare (the sieve marking-loop
// shape).
//
// Every loop below indexes with a runtime `usize` variable that a dominating
// loop-guard compare (`q < 64`, `i < 64`, `j <= 63`) already proves in bounds
// for the constant-length array. That is exactly the shape the bridge routes
// through `try_lower_bounds_check_as_dominated_verified_guard`: the analysis
// finds the dominating fact, the ay lane discharges the per-instance
// implication `(idx <op> K) => (idx <u len)`, and the Certified-Elimination
// Kernel deletes the check against the discharged obligation (fail-closed).
//
// This fixture is a DIFFERENTIAL correctness pin, NOT a trap pin: every access
// is in bounds at runtime, so the probe fires (or, with `TCG_REFINE_SOLVER=0`
// / no solver, silently stays the legacy compare+branch) and the observable
// result is identical to LLVM either way. The at-boundary write (`j <= 63`
// touching index 63, the LAST valid element of a `[u8; 64]`) pins that the
// elimination does not disturb at-bounds behavior. Out-of-bounds trap
// preservation for the REFUTED shapes (off-by-one `<=u len`, weaker guard,
// index mutated between guard and check) is pinned by the bridge-only trap
// tests in `dom_bounds_refutation_x86.rs` (an OOB fixture cannot live in this
// no_std corpus: an LLVM bounds-panic HANGS in the `loop {}` panic handler
// while the kept trust-cg check TRAPS, a structural divergence unrelated to
// OPT-6b).
//
// Expected exit: marking loop (q = 4, 7, .., 61 -> 20 marks), zeros counted
// 64-20 = 44; boundary loop writes 2 to indices 60..=63 (4 entries);
// 44 + 4 = 48.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut comp = [0u8; 64];

    // (a) The sieve marking loop: runtime start + runtime stride, guard
    //     `q < 64` dominating the `comp[q]` write check (Ult, K == len).
    let p = black_box(3usize);
    let mut q = black_box(4usize);
    while q < 64 {
        comp[q] = 1;
        q += p;
    }

    // (b) The counting loop: guard `i < 64` dominating the `comp[i]` read
    //     check.
    let mut count = 0i32;
    let mut i = black_box(0usize);
    while i < 64 {
        if comp[i] == 0 {
            count += 1;
        }
        i += 1;
    }

    // (c) An at-boundary `<=` guard: `j <= 63` dominates `comp[j]` (Ule,
    //     K == len - 1, discharges) and the loop's last write touches index
    //     63 — the LAST valid element.
    let mut j = black_box(60usize);
    while j <= 63 {
        comp[j] = 2;
        j += 1;
    }

    // (d) Recount so the boundary writes are observable.
    let mut c2 = 0i32;
    let mut k = black_box(0usize);
    while k < 64 {
        if comp[k] == 2 {
            c2 += 1;
        }
        k += 1;
    }

    count + c2
}
