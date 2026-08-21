// Narrow element widths through a reduction.
use std::hint::black_box as bb;
fn main() { let n = bb(64usize); let mut a=[0i8;64]; let mut b=[0i16;64];
    for i in 0..64 { a[i]=((i as i32 % 100) - 50) as i8; b[i]=((i as i32 * 7) % 1000 - 500) as i16; }
    let (a,b)=(bb(a),bb(b));
    let mut s1: i64 = 0; let mut s2: i64 = 0; let mut i=0usize;
    while i < n { s1 += a[i] as i64; s2 += b[i] as i64; i += 1; }
    std::process::exit(((s1+s2).rem_euclid(126)) as i32); }
