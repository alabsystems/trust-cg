// leaf user `impl Drop` (RAII guard): drop runs at scope end, on explicit drop(),
// and across a function boundary; the guard mutates through a &mut field. No
// drop-needing fields (so no recursive glue) — the ubiquitous RAII pattern.
use std::hint::black_box as bb;
struct Counter<'a> { slot: &'a mut u64 }
impl<'a> Drop for Counter<'a> {
    fn drop(&mut self) { *self.slot = self.slot.wrapping_mul(31).wrapping_add(7); }
}
fn run(out: &mut u64, n: u64) {
    let _c = Counter { slot: out };
    let mut s = 0u64;
    for i in 0..n { s = s.wrapping_add(i); }
    bb(s);
}
fn main() {
    let mut a = bb(1u64);
    for _ in 0..bb(20u64) { run(&mut a, bb(10)); }   // drop at fn scope end, x20
    let mut b = bb(100u64);
    { let g = Counter { slot: &mut b }; drop(g); }    // explicit drop
    let mut c = bb(5u64);
    { let _g = Counter { slot: &mut c }; }            // drop at block scope end
    std::process::exit(((a ^ b ^ c) % 233) as i32);
}
