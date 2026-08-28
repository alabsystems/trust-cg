// match with range patterns, or-patterns, guards, @ bindings, and early return
// from a loop (Option) — the match-lowering + branch-fold paths.
use std::hint::black_box as bb;
fn classify(x: i64) -> u64 {
    match x {
        i64::MIN..=-1 => 1,
        0 => 2,
        1 | 2 | 3 => 3,
        n if n % 2 == 0 => n as u64 & 0xff,
        n @ 4..=100 => (n as u64).wrapping_mul(2) & 0xff,
        _ => 99,
    }
}
fn find(a: &[i64], target: i64) -> Option<usize> {
    for (i, &v) in a.iter().enumerate() { if v == target { return Some(i); } }
    None
}
fn main() {
    let mut acc: u64 = 0;
    for x in [bb(-5i64), bb(0), bb(2), bb(6), bb(50), bb(1000), bb(3), bb(-1)].iter() {
        acc = acc.wrapping_add(classify(*x));
    }
    let data = [bb(10i64), bb(20), bb(30), bb(40), bb(50)];
    for t in [bb(30i64), bb(99), bb(10), bb(50)].iter() {
        acc = acc.wrapping_add(find(&data, *t).map_or(777, |i| i as u64));
    }
    std::process::exit((acc % 241) as i32);
}
