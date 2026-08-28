// operator overloading: impl Add/Sub/Mul for a struct, used in expressions
use std::hint::black_box as bb;
use std::ops::{Add, Mul};
#[derive(Clone, Copy)] struct V2 { x: u64, y: u64 }
impl Add for V2 { type Output = V2; fn add(self, o: V2) -> V2 { V2 { x: self.x.wrapping_add(o.x), y: self.y.wrapping_add(o.y) } } }
impl Mul<u64> for V2 { type Output = V2; fn mul(self, s: u64) -> V2 { V2 { x: self.x.wrapping_mul(s), y: self.y.wrapping_mul(s) } } }
fn main() {
    let mut acc = V2 { x: bb(0), y: bb(0) };
    for i in 0..bb(50u64) {
        let v = V2 { x: bb(i), y: bb(i.wrapping_mul(2)) };
        acc = acc + v * bb(3);
    }
    std::process::exit(((acc.x ^ acc.y) % 233) as i32);
}
