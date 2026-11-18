// A closure environment owning, by value, a struct that holds a Vec field.
// Outside the inline-header admission: the closure-environment route keeps
// [TCG-COLLECTION-IMAGE] (record SLICE-CAP3-GATE-SCOPE).
use std::hint::black_box;

struct S {
    k: u8,
    v: Vec<u32>,
}

#[inline(never)]
fn mk(n: u32) -> S {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i);
    }
    S { k: 1, v }
}

#[inline(never)]
fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> u64 {
    f(x)
}

#[inline(never)]
fn go(n: u32) -> u64 {
    let s = mk(n);
    let f = move |k: u64| k + s.v.len() as u64 + s.k as u64;
    apply(&f, 1) + apply(&f, 2)
}

fn main() {
    println!("{} {}", go(black_box(0)), go(black_box(4)));
}
