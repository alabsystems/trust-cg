// &mut-returning fns: custom IndexMut (array-backed) + select-of-two-&mut.
// Formerly HARD-DECLINED at O0/O1 by direct_scalar_ref_select_return's early
// mutable-ref guard; now falls through to general call lowering (write-back
// owned there). See tests/unsupported_program.rs::mutable_scalar_reference_return_*.
use std::hint::black_box as bb;
use std::ops::{Index, IndexMut};
struct Grid { data: [u64; 16], w: usize }
impl Index<(usize, usize)> for Grid { type Output = u64; fn index(&self, (r, c): (usize, usize)) -> &u64 { &self.data[r * self.w + c] } }
impl IndexMut<(usize, usize)> for Grid { fn index_mut(&mut self, (r, c): (usize, usize)) -> &mut u64 { &mut self.data[r * self.w + c] } }
#[inline(never)]
fn pick<'a>(f: bool, a: &'a mut u64, b: &'a mut u64) -> &'a mut u64 { if f { a } else { b } }
fn main() {
    let mut g = Grid { data: [0u64; 16], w: 4 };
    let mut acc = 0u64;
    for r in 0..4 { for c in 0..4 {
        g[(r, c)] = bb((r * 10 + c) as u64);
        g[(r, c)] = g[(r, c)].wrapping_mul(3).wrapping_add(bb(7));
        acc = acc.wrapping_add(g[(r, c)]);
    } }
    let mut x = bb(5u64); let mut y = bb(9u64);
    for i in 0..bb(40u64) {
        let s = pick(i % 3 == 0, &mut x, &mut y);
        *s = s.wrapping_mul(2).wrapping_add(i);
        acc = acc.wrapping_add(x).wrapping_add(y.rotate_left(5));
    }
    std::process::exit((acc % 241) as i32);
}
