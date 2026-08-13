// heap: Vec push (with organic growth/realloc) then repeated index-sum passes.
// One Vec for the whole program; exits via std::process::exit (no drop before
// exit — the r_vec/heap-canary envelope, 0456e2a reachability-GC fix).
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let n = bb(300_000usize);
    let mut x: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        v.push(x);
        i += 1;
    }
    let passes = bb(300u32);
    let mut acc: u64 = 0;
    let mut p = 0u32;
    while p < passes {
        let mut k = 0usize;
        while k < v.len() {
            acc = acc.wrapping_add(v[k]);
            k += 1;
        }
        p += 1;
    }
    done(acc);
}
