// DIAGNOSTIC copy of h1_vec_push_sum with the reduction split across FOUR
// accumulators. Same total work, same checksum; the ONLY difference is that the
// loop-carried add chain is 4 independent chains instead of 1.
use std::hint::black_box as bb;
fn done(code: u64) -> ! { std::process::exit((code % 126) as i32) }
fn main() {
    let n = bb(300_000usize);
    let mut x: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < n { x ^= x << 13; x ^= x >> 7; x ^= x << 17; v.push(x); i += 1; }
    let passes = bb(3000u32);
    let (mut a0, mut a1, mut a2, mut a3) = (0u64, 0u64, 0u64, 0u64);
    let mut p = 0u32;
    while p < passes {
        let mut k = 0usize;
        while k + 3 < v.len() {
            a0 = a0.wrapping_add(v[k]);
            a1 = a1.wrapping_add(v[k + 1]);
            a2 = a2.wrapping_add(v[k + 2]);
            a3 = a3.wrapping_add(v[k + 3]);
            k += 4;
        }
        while k < v.len() { a0 = a0.wrapping_add(v[k]); k += 1; }
        p += 1;
    }
    done(a0.wrapping_add(a1).wrapping_add(a2).wrapping_add(a3));
}
