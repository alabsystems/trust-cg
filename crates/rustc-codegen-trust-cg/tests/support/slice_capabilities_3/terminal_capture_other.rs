// Shapes beside this admission: an integer `contains` of a register scalar
// (stored-reference class at -O0/-O1), and a Range `any` / Map `all` whose
// optimized form is `try_fold` with a by-value capturing check closure (its
// own soundness gate). Match or named refusal.
use std::hint::black_box;
#[inline(never)]
fn contains_u32(v: &[u32], x: u32) -> bool {
    v.contains(&x)
}
#[inline(never)]
fn range_any(n: u64, k: u64) -> bool {
    (0..n).any(|i| i * i == k)
}
#[inline(never)]
fn mapped_all(v: &[u32], lim: u32) -> bool {
    v.iter().map(|x| x * 2).all(|y| y < lim)
}
fn main() {
    println!(
        "{} {}",
        contains_u32(black_box(&[7, 8]), 8),
        contains_u32(black_box(&[7]), 9)
    );
    println!(
        "{} {}",
        range_any(black_box(100), 49),
        range_any(black_box(100), 50)
    );
    println!(
        "{} {}",
        mapped_all(black_box(&[1, 2, 3]), 20),
        mapped_all(black_box(&[1, 2, 30]), 18)
    );
}
