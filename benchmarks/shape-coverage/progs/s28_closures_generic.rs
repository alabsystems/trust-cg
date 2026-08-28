// closures: FnOnce/FnMut passed to generic fns, captured mutable state.
use std::hint::black_box as bb;
fn apply_once<F: FnOnce(u64) -> u64>(f: F, x: u64) -> u64 { f(x) }
fn apply_mut<F: FnMut(u64)>(mut f: F, n: u64) { for i in 0..n { f(i); } }
fn main() {
    let cap = bb(11u64);
    let mut sum: u64 = 0;
    apply_mut(|i| { sum = sum.wrapping_add(i.wrapping_mul(cap)); }, bb(300));
    let once = apply_once(move |x| x.wrapping_add(cap).wrapping_mul(3), bb(7));
    let s = sum.wrapping_add(once);
    std::process::exit((s % 241) as i32);
}
