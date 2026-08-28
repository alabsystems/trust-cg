// Option method chains (ubiquitous): unwrap_or/map_or/unwrap_or_default/and_then/
// filter + iter max/min/position.unwrap_or — const defaults promoted at O1.
use std::hint::black_box as bb;
fn f(o: Option<u64>, s: &[u64]) -> u64 {
    let a = o.unwrap_or(7);
    let b = o.map_or(11, |v| v.wrapping_mul(2));
    let c = o.unwrap_or_default();
    let d = o.and_then(|v| if v > 5 { Some(v) } else { None }).unwrap_or(0);
    let e = o.filter(|&v| v % 2 == 0).map_or(3, |v| v);
    let g = s.iter().copied().max().unwrap_or(0);
    let h = s.iter().copied().min().unwrap_or(99);
    let i = s.iter().position(|&x| x == 30).unwrap_or(999) as u64;
    a.wrapping_add(b).wrapping_add(c).wrapping_add(d).wrapping_add(e).wrapping_add(g).wrapping_add(h).wrapping_add(i)
}
fn main() {
    let v = [bb(10u64), bb(20), bb(30), bb(40)];
    let mut acc = 0u64;
    for &o in [Some(bb(6u64)), None, Some(bb(3)), Some(bb(8))].iter() { acc = acc.wrapping_add(f(o, &v)); }
    std::process::exit((acc % 233) as i32);
}
