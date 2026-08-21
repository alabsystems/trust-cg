// FP reduction must NOT be reassociated (non-associative).
use std::hint::black_box as bb;
fn main() { let n = bb(64usize); let mut a=[0.0f32;64];
    for i in 0..64 { a[i] = 1.0 / ((i as f32) + 1.0); }
    let a = bb(a); let mut s = bb(0.0f32); let mut i=0usize;
    while i < n { s += a[i]; i += 1; }
    std::process::exit(((s * 1000.0) as i64 % 126) as i32); }
