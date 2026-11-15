use std::hint::black_box;
#[inline(never)] fn fsum(v: &[i64]) -> i64 { v.iter().map(|&x| x).sum() }
fn main() {
    // front-to-back: MAX + 1 overflows (panics with checks on, wraps to MIN-1.. with checks off)
    let b = black_box(vec![i64::MAX, 1, -1]);
    println!("{}", fsum(&b));
}
