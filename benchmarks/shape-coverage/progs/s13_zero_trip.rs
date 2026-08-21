// Zero-trip and tiny-trip loops around vectorizable shapes.
use std::hint::black_box as bb;
fn main() { let mut total: u64 = 0;
    for n in [0usize, 1, 2, 3, 7, 8, 9, 15, 16, 17] {
        let n = bb(n); let mut acc: u64 = bb(3); let mut i = 0usize;
        while i < n { acc = acc.wrapping_add((i as u64).wrapping_mul(5)); i += 1; }
        total = total.wrapping_add(acc); }
    std::process::exit((total % 126) as i32); }
