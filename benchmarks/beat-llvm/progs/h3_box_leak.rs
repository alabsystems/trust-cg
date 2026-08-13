// heap: Box-heavy — 1.5M individual Box allocations kept alive in a Vec (allocator
// throughput), then deref-sum passes. Deliberately leak-on-exit (std::process::exit
// runs no drops) — stays inside the proven drop-free heap envelope; the dropping
// variant is h4_vec_dropper (expected-INCOMPLETE until COMPLETE-4).
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let n = bb(1_500_000usize);
    let mut x: u64 = bb(0x243F6A8885A308D3u64);
    let mut v: Vec<Box<u64>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        v.push(Box::new(x));
        i += 1;
    }
    let passes = bb(20u32);
    let mut acc: u64 = 0;
    let mut p = 0u32;
    while p < passes {
        let mut k = 0usize;
        while k < v.len() {
            acc = acc.wrapping_add(*v[k]);
            k += 1;
        }
        p += 1;
    }
    done(acc);
}
