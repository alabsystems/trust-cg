// const sub-slicing (Range/RangeTo/RangeFrom) + split_at with a const index on
// array AND vec receivers — all now work at every opt (const-range class
// 376111af/ee0d3c50 + split_at). Guards these against regression.
use std::hint::black_box as bb;
fn sum(s: &[u64]) -> u64 { s.iter().fold(0u64, |a, &x| a.wrapping_add(x)) }
fn ops(s: &[u64]) -> u64 {
    let mut acc = s.len() as u64;
    acc = acc.wrapping_add(sum(s));
    if s.len() >= 4 {
        acc = acc.wrapping_add(sum(&s[1..3]));
        acc = acc.wrapping_add(sum(&s[..2]));
        acc = acc.wrapping_add(sum(&s[2..]));
        let (a, b) = s.split_at(2);
        acc = acc.wrapping_add(sum(a).wrapping_mul(3)).wrapping_add(sum(b));
    }
    acc
}
fn main() {
    let arr = [bb(10u64), bb(20), bb(30), bb(40), bb(50), bb(60)];
    let mut v: Vec<u64> = Vec::new();
    for i in 0..bb(6u64) { v.push(i.wrapping_mul(7).wrapping_add(3)); }
    let total = ops(&arr).wrapping_add(ops(&v)).wrapping_add(ops(&arr[1..5]));
    std::process::exit((total % 233) as i32);
}
