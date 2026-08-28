// &mut dyn Trait driven through a generic fn (mutable trait-object dispatch).
use std::hint::black_box as bb;
trait Gen { fn next(&mut self) -> u64; }
struct Counter { c: u64, step: u64 }
impl Gen for Counter { fn next(&mut self) -> u64 { self.c = self.c.wrapping_add(self.step); self.c } }
fn drive(g: &mut dyn Gen, n: u64) -> u64 { let mut a = 0u64; for _ in 0..n { a = a.wrapping_add(g.next()); } a }
fn main() {
    let mut c = Counter { c: bb(0), step: bb(3) };
    let a = drive(&mut c, bb(600));
    let mut d = Counter { c: bb(100), step: bb(7) };
    let b = drive(&mut d, bb(400));
    std::process::exit(((a ^ b) % 223) as i32);
}
