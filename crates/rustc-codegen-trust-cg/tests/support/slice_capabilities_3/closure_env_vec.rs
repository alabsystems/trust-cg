// A closure environment owning a Vec by value (FnOnce through a generic
// caller). Outside the inline-header admission: the closure-environment route
// keeps [TCG-COLLECTION-IMAGE] (record SLICE-CAP3-GATE-SCOPE).
use std::hint::black_box;

#[inline(never)]
fn call<F: FnOnce() -> Vec<u32>>(f: F) -> usize {
    f().len()
}

#[inline(never)]
fn go(n: u32) -> usize {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i);
    }
    call(move || {
        let mut w = v;
        w.push(1);
        w
    })
}

fn main() {
    println!("{} {}", go(black_box(0)), go(black_box(9)));
}
