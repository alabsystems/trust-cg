// f64 sum/product reductions must NOT be reassociated (LLVM no-fast-math keeps
// them sequential); one huge + many tiny values so any lane-parallel reordering
// changes the rounded bits. Guards the vectorizer's FP-order preservation.
// vectorizer sums lanes in parallel it reassociates -> different rounding.
// Values: one huge + many tiny, where sequential vs tree order differ in bits.
use std::hint::black_box as bb;
fn main() {
    let n = bb(1024usize);
    let mut a = vec![0.0f64; n];
    a[0] = bb(1e16);
    for i in 1..n { a[i] = bb(1.0 + (i as f64) * 1e-3); }
    let mut s = 0.0f64;
    for i in 0..n { s = s + a[i]; }          // sequential — must match LLVM exactly
    let mut s2 = 0.0f64;
    for i in 0..n { s2 += a[n-1-i]; }        // reverse order (different value, both backends)
    let mut prod = 1.0f64;
    for i in 0..n { prod = prod * (1.0 + a[i] * 1e-9); }
    let mut acc: u64 = 0;
    acc = acc.wrapping_add(s.to_bits()).wrapping_add(s2.to_bits().rotate_left(1)).wrapping_add(prod.to_bits().rotate_left(2));
    std::process::exit((acc % 251) as i32);
}
