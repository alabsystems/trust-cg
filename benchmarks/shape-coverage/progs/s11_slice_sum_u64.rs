// neon_array slice-sum lane: bounds-checked Vec index.
use std::hint::black_box as bb;
fn main() { let n = bb(1000usize); let mut v: Vec<u64> = Vec::new();
    let mut x: u64 = bb(0x9E3779B97F4A7C15); let mut i = 0usize;
    while i < n { x ^= x << 13; x ^= x >> 7; x ^= x << 17; v.push(x); i += 1; }
    let mut acc: u64 = bb(41); let mut k = 0usize;
    while k < v.len() { acc = acc.wrapping_add(v[k]); k += 1; }
    std::process::exit((acc % 126) as i32); }
