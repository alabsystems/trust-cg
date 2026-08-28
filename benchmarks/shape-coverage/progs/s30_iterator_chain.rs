// iterator adapters: map/filter/map/fold + collect (the filter_next/filter_map bool-const paths).
use std::hint::black_box as bb;
fn main() {
    let n = bb(2000u64);
    let s: u64 = (0..n)
        .map(|i| i.wrapping_mul(3).wrapping_add(1))
        .filter(|&x| x % 2 == 0)
        .map(|x| x >> 1)
        .fold(0u64, |a, x| a.wrapping_add(x));
    let v: Vec<u64> = (0..bb(50u64)).filter(|x| x % 3 != 0).collect();
    let t = v.iter().fold(s, |a, &x| a.wrapping_add(x));
    std::process::exit((t % 229) as i32);
}
