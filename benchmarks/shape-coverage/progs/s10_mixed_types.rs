// vectorize: element-type homogeneity.
use std::hint::black_box as bb;
fn main() { let n = bb(64usize); let a = bb([7u32; 64]); let b = bb([3u64; 64]);
    let mut c = [0u64; 64]; let mut i = 0usize;
    while i < n { c[i] = (a[i] as u64).wrapping_mul(b[i]).wrapping_add(i as u64); i += 1; }
    let s: u64 = c.iter().fold(0u64,|x,&y| x.wrapping_add(y));
    std::process::exit((s % 126) as i32); }
