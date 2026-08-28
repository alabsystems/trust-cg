// trait objects: [Box<dyn Op>; N] dispatched in a loop (exercises the vtable pointer + Tuple-typed vtable global). O0 compiles; O1+ hits 'memory aggregate whole assignment from non-local operand'.
use std::hint::black_box as bb;
trait Op { fn apply(&self, x: u64) -> u64; }
struct Add(u64); struct Mul(u64); struct Xor(u64);
impl Op for Add { fn apply(&self, x: u64) -> u64 { x.wrapping_add(self.0) } }
impl Op for Mul { fn apply(&self, x: u64) -> u64 { x.wrapping_mul(self.0) } }
impl Op for Xor { fn apply(&self, x: u64) -> u64 { x ^ self.0 } }
fn main() {
    let ops: [Box<dyn Op>; 3] = [Box::new(Add(bb(7))), Box::new(Mul(bb(3))), Box::new(Xor(bb(0x5a)))];
    let mut acc: u64 = bb(1);
    for i in 0..bb(1000u64) {
        let op = &ops[(i % 3) as usize];
        acc = op.apply(acc).wrapping_add(i);
    }
    std::process::exit((acc % 251) as i32);
}
