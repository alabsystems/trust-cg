use std::hint::black_box;
#[inline(never)] fn rsum(v: &[i64]) -> i64 { v.iter().rev().map(|&x| x).sum() }
fn main() {
    let a = black_box(vec![1i64, i64::MAX - 1, -1]);
    println!("{}", rsum(&a));
    let b = black_box(vec![i64::MAX, 1, -1]);
    println!("{}", rsum(&b));
}
