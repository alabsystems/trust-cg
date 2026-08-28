// generic fns with trait bounds (T: Ord+Copy, F: Fn) monomorphized over u64/i64.
use std::hint::black_box as bb;
fn max_of<T: Ord + Copy>(s: &[T], d: T) -> T { s.iter().copied().fold(d, |a, x| if x > a { x } else { a }) }
fn apply<T: Copy, F: Fn(T) -> T>(s: &[T], f: F, init: T, g: impl Fn(T, T) -> T) -> T { s.iter().copied().map(f).fold(init, g) }
fn main() {
    let a = [bb(10u64), bb(30), bb(20)];
    let b = [bb(-5i64), bb(3), bb(-1)];
    let acc = max_of(&a, 0).wrapping_add(max_of(&b, i64::MIN).wrapping_abs() as u64)
        .wrapping_add(apply(&a, |x| x.wrapping_mul(2), 1, |p, x| p.wrapping_add(x)));
    std::process::exit((acc % 239) as i32);
}
