// closures: impl Fn return (adder), FnMut accumulation through a generic fn,
// capture by value/ref, closure created in a loop.
// returning closures via impl Fn
use std::hint::black_box as bb;
fn adder(n: u64) -> impl Fn(u64) -> u64 { move |x| x.wrapping_add(n) }
fn apply_n<F: FnMut() -> u64>(mut f: F, n: u64) -> u64 { let mut s = 0u64; for _ in 0..n { s = s.wrapping_add(f()); } s }
fn main() {
    let base = bb(100u64);
    let add = adder(bb(7));
    let mut counter = bb(0u64);
    let s1 = apply_n(|| { counter = counter.wrapping_add(3); counter.wrapping_mul(base) }, bb(50));
    let mut total = 0u64;
    for i in 0..bb(30u64) { let cl = |x: u64| x.wrapping_mul(base).wrapping_add(i); total = total.wrapping_add(cl(add(i))); }
    std::process::exit(((s1 ^ total) % 233) as i32);
}
