// CORPUS FIXTURE — OPT-4: shared trust-ir-level inlining of a small PURE scalar
// leaf callee called in a HOT LOOP.
//
// `mix` is a single-block, call-free (leaf), scalar-u64 helper built entirely
// from wrapping arithmetic + bitwise ops (no overflow/shift/div guards, no
// memory, no control flow) — exactly the v1-eligible shape. The trust-ir-level
// inliner (compiler.rs `translate_module_for_arch` seam) splices `mix`'s body
// into `main`'s loop body before ISel; LLVM keeps the call (`#[inline(never)]`).
// BOTH lanes must fold the same accumulator, so the exit codes are identical at
// O0/O2/O3. This pins that inlining stays semantics-preserving.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;

#[inline(never)]
fn mix(x: u64, k: u64) -> u64 {
    let a = x ^ x.wrapping_shl(13);
    let b = a.wrapping_mul(k | 1);
    b ^ b.wrapping_shr(7)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let k = bb(0x9E3779B97F4A7C15u64);
    let n = bb(4096u64);
    let mut acc: u64 = bb(1u64);
    let mut i = 0u64;
    while i < n {
        acc = mix(acc ^ i, k);
        i = i.wrapping_add(1);
    }
    (acc % 126) as i32
}
