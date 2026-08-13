// CORPUS FIXTURE (OPT-6a) — verified elimination of a CONSTANT-index,
// CONSTANT-length array bounds check.
//
// The array ELEMENTS are `black_box`d (runtime values, so the array is a real
// memory-backed slot and the reads are genuine loads), but every index is a
// COMPILE-TIME CONSTANT and the array length is fixed. That is the exact shape
// the bridge routes into the verified Certified-Elimination Kernel: rustc emits
// `Assert(BoundsCheck { len: const N, index: const k })`, the bridge discharges
// `k <u N` through the ay solver lane and emits a `GuardBoundsCheck` probe the
// kernel deletes (fail-closed) — see `try_lower_bounds_check_as_verified_guard`.
//
// This fixture is a DIFFERENTIAL correctness pin, NOT a trap pin: every access
// is strictly in bounds, so the probe fires (or, with `TCG_REFINE_SOLVER=0` /
// no solver, silently stays the legacy compare+branch), and the observable
// result is identical to LLVM either way. Out-of-bounds / at-bounds traps are
// covered structurally: the probe path is taken ONLY for a strictly-in-bounds
// constant index, so it can never touch a trapping or dynamic-index check
// (which stays the byte-identical legacy lowering); the surviving-carrier trap
// is pinned by `trust-cg-codegen/tests/guard_bounds_probe_x86.rs`.
//
// A trapping OOB fixture is deliberately absent: these `#![no_std]` corpus
// programs use a `loop {}` panic handler, so an LLVM bounds-panic HANGS while
// the trust-cg carrier TRAPS (UD2), which the differential would (correctly)
// flag as a hang/trap divergence unrelated to OPT-6a.
//
// All accesses in bounds -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) constant-index in-bounds reads of a fixed `[i64; 5]` (probe candidates:
    //     len=5 const, index in {0,2,4} const, each strictly < 5).
    let a: [i64; 5] = [
        black_box(10i64),
        black_box(20i64),
        black_box(30i64),
        black_box(40i64),
        black_box(50i64),
    ];
    let ok_a = a[0] == 10 && a[2] == 30 && a[4] == 50;

    // (b) constant-index writes then read-back (the write place-projection also
    //     carries a constant-bound bounds check).
    let mut b: [i64; 4] = [black_box(1i64), black_box(2i64), black_box(3i64), black_box(4i64)];
    b[1] = black_box(9i64);
    b[3] = black_box(8i64);
    let ok_b = b[0] == 1 && b[1] == 9 && b[3] == 8;

    // (c) a DYNAMIC in-bounds index — the legacy compare+branch path, which
    //     OPT-6a must leave completely unchanged (index not constant -> no
    //     probe). Correctness here proves no regression on the non-probe path.
    let j = black_box(3usize);
    let ok_c = a[j] == 40;

    // (d) constant index 0 (the boundary `0 <u N`, still strictly in bounds).
    let ok_d = b[0] == 1 && a[1] == 20;

    if ok_a && ok_b && ok_c && ok_d {
        7
    } else {
        13
    }
}
