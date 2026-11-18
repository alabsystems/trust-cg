// A `Copy` FnMut closure handed to two terminals: each call owns its own copy
// of the environment (std moves a COPY of `f` in), so the second call starts
// from the caller's state, not from the first call's mutated copy; the
// caller's closure local is never written.
use std::hint::black_box;

#[inline(never)]
fn twice(v: &[i64], limit: i64) -> (bool, bool, Option<usize>) {
    let mut acc = 0i64;
    let mut over = move |x: &i64| {
        acc += *x;
        acc > limit
    };
    let a = v.iter().any(over);
    let b = v.iter().any(over);
    let c = v.iter().position(|x| over(x));
    (a, b, c)
}

fn main() {
    let mut v: Vec<i64> = Vec::new();
    for i in 0..20 {
        v.push(i * 5 - 3);
    }
    println!("{:?}", twice(black_box(&v), black_box(40)));
    println!("{:?}", twice(black_box(&v[..2]), black_box(40)));
    println!("{:?}", twice(black_box(&v[..0]), black_box(-1)));
}
