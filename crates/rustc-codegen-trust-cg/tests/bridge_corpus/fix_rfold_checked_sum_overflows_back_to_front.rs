use std::hint::black_box;
#[inline(never)] fn rsum(v: &[i64]) -> i64 { v.iter().rev().map(|&x| x).sum() }
fn main() {
    // rustc's reverse order: MAX + 1 overflows -> panics with checks on; forward: -1+1+MAX = MAX
    let c = black_box(vec![-1i64, 1, i64::MAX]);
    println!("{}", rsum(&c));
}
