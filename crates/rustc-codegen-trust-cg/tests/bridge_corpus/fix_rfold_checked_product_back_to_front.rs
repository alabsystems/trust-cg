use std::hint::black_box;
#[inline(never)] fn rprod(v: &[i64]) -> i64 { v.iter().rev().map(|&x| x).product() }
fn main() {
    let a = black_box(vec![2i64, i64::MAX / 2 + 1, 0]);
    println!("{}", rprod(&a));
}
