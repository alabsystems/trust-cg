// sret pointer clobber: `f` returns [i16;12] (24 bytes -> indirect via X8) and
// calls `g`, which ALSO returns indirectly and stages its own buffer address
// into X8. X8 is call-clobbered (AAPCS64 clobbers X0-X18), so the incoming
// return-buffer pointer is dead by the epilogue: it MUST be saved before that
// call. isel stored the return value through the physical X8 instead of a copy
// saved at entry, so `f` wrote its result into its own frame and the caller
// read uninitialised stack.
// Was: LLVM 177, trust-cg NONDET at O0/O1/O2/O3 *and* with proofs ON.
// LLVM emits `mov x20, x8` at entry; we now do the same.
use std::hint::black_box as bb;

#[inline(never)]
fn g(p: u32) -> (i32, u64, u64) { (p as i32, p as u64, 7u64) }

#[inline(never)]
fn f(p1: i16) -> [i16; 12] {
    let (a, b, c) = g(p1 as u32);
    [a as i16, b as i16, c as i16, p1, p1, p1, p1, p1, p1, p1, p1, p1]
}

fn main() {
    let r = f(bb(10334i16));
    let mut acc: u64 = 0;
    let mut q = 0usize;
    while q < 12 { acc = acc.wrapping_mul(31).wrapping_add(r[q % 12] as i64 as u64); q += 1; }
    std::process::exit((acc % 251) as i32);   // 177
}
