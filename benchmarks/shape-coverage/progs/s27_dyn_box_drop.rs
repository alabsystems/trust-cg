// Box<dyn Shape> with a Drop impl + Vec field: exercises the drop-in-place vtable entry. Declines: 'Place projection field 1 before aggregate binding'.
use std::hint::black_box as bb;
trait Shape { fn area(&self) -> u64; }
struct Sq { s: u64, buf: Vec<u64> }
impl Shape for Sq { fn area(&self) -> u64 { self.s.wrapping_mul(self.s).wrapping_add(self.buf.len() as u64) } }
impl Drop for Sq { fn drop(&mut self) { bb(&self.buf); } }
fn main() {
    let mut acc: u64 = 0;
    for i in 0..bb(500u64) {
        let b: Box<dyn Shape> = Box::new(Sq { s: bb(i + 1), buf: vec![i; (i % 4 + 1) as usize] });
        acc = acc.wrapping_add(b.area());
    }
    std::process::exit((acc % 239) as i32);
}
