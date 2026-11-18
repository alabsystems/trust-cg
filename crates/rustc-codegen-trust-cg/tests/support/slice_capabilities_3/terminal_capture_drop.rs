// A terminal closure that OWNS a `String` capture keeps its refusal: its
// environment owns a collection header, which the closure-environment route
// refuses ([TCG-COLLECTION-IMAGE], record SLICE-CAP3-GATE-SCOPE).
use std::hint::black_box;
#[inline(never)]
fn owned(v: &[usize], s: String) -> bool {
    v.iter().any(move |x| *x == s.len())
}
fn main() {
    let mut s = String::new();
    s.push_str("hello");
    println!("{}", owned(black_box(&[1, 5]), s));
}
