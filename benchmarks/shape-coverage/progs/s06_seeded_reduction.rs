// neon_reduce: NON-ZERO initial accumulator must survive vectorization.
use std::hint::black_box as bb;
fn main() { let n = bb(200u32); let seed = bb(12345u32);
    let mut acc: u32 = seed; let mut i = 0u32;
    while i < n { acc = acc.wrapping_add(i.wrapping_mul(7) | i.wrapping_mul(3)); i += 1; }
    std::process::exit((acc % 126) as i32); }
