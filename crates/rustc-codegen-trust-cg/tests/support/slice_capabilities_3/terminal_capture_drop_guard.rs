// A terminal closure that OWNS a capture with drop glue (a user `Drop` type
// holding no collection) keeps its refusal: the synthesized drive runs no
// cleanup for the environment.
use std::hint::black_box;
struct Guard(usize);
impl Drop for Guard {
    fn drop(&mut self) {
        println!("drop {}", self.0);
    }
}
#[inline(never)]
fn owned(v: &[usize], g: Guard) -> bool {
    v.iter().any(move |x| *x == g.0)
}
fn main() {
    println!("{}", owned(black_box(&[1, 5]), Guard(black_box(5))));
}
