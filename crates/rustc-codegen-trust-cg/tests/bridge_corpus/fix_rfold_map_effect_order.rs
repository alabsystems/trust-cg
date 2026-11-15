use std::hint::black_box;
#[inline(never)] fn rsum(v: &[u64]) -> u64 { v.iter().rev().map(|&x| { print!("{x} "); x }).sum() }
#[inline(never)] fn rsumw(v: &[u64]) -> u64 { v.iter().rev().map(|&x| { print!("{x} "); x.wrapping_mul(3) }).fold(0u64, |a, b| a.wrapping_add(b)) }
fn main() {
    let a = black_box(vec![1u64, 2, 3, 4]);
    let s = rsum(&a);
    println!("= {s}");
    let t = rsumw(&a);
    println!("= {t}");
}
