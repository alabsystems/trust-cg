// custom Index impl (a matrix-like type)
use std::hint::black_box as bb;
use std::ops::Index;
struct Grid { data: [u64; 16], w: usize }
impl Index<(usize, usize)> for Grid { type Output = u64; fn index(&self, (r, c): (usize, usize)) -> &u64 { &self.data[r * self.w + c] } }
fn main() {
    let mut g = Grid { data: [0u64; 16], w: 4 };
    for i in 0..16 { g.data[i] = bb(i as u64 * 3); }
    let mut acc = 0u64;
    for r in 0..4 { for c in 0..4 { acc = acc.wrapping_add(g[(r, c)].wrapping_mul((r + c) as u64 + 1)); } }
    std::process::exit((acc % 241) as i32);
}
