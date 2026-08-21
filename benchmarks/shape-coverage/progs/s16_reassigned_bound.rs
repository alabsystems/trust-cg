// strided_store_unroll: the loop BOUND is itself loop-carried and reassigned in
// the body, and `recognize_native_const_bound` const-resolved it through the
// def map (last-wins over the emitted layout) to the LATCH value. Entering with
// q=8 and lim=4, `8 < 4` is false so the loop never runs and the program writes
// NOTHING; the pass believed N=64 and wrote 56 bytes at indices 8..=63 — past a
// 16-byte buffer into a SEPARATE allocation. Was: LLVM 0, trust-cg 32 at O2/O3.
use std::hint::black_box as bb;
#[inline(never)]
fn go(buf: &mut [u8], s: usize, q0: usize) {
    let mut lim = 4usize;
    let mut q = q0;
    while q < lim { buf[q] = 1u8; q += s; lim = 64; }
}
fn main() {
    let s = bb(1usize); let q0 = bb(8usize);
    let mut b = vec![0u8; 16];
    let guard = vec![0xAAu8; 64];
    go(&mut b, s, q0);
    let mut bad = 0usize; let mut i = 0usize;
    while i < 64 { if guard[i] != 0xAA { bad += 1; } i += 1; }
    std::process::exit(bad as i32);   // 0 = the guard allocation is intact
}
