// struct/array whole-value copies, indexed-place swaps (gap-1, daa4a5d0), and
// std::mem::swap of aggregates ([u64;3] + a struct — typed_swap aggregate arm).
use std::hint::black_box as bb;
#[derive(Clone, Copy)] struct Big { a: [u64; 5], b: u32, c: [u8; 7], d: f64 }
fn main() {
    let mut acc: u64 = 0;
    let mut arr: [Big; 8] = [Big { a: [0;5], b: 0, c: [0;7], d: 0.0 }; 8];
    for i in 0..8 {
        arr[i].a[i % 5] = bb(i as u64 * 100);
        arr[i].b = bb(i as u32 * 7);
        arr[i].c[i % 7] = bb(i as u8);
        arr[i].d = bb(i as f64 * 1.5);
    }
    // whole-struct copies + swaps
    for i in 0..7 { let t = arr[i]; arr[i] = arr[i+1]; arr[i+1] = t; }
    let copy = arr;              // whole-array copy
    for b in copy.iter() {
        acc = acc.wrapping_add(b.a.iter().fold(0u64, |x, &y| x.wrapping_add(y)));
        acc = acc.wrapping_add(b.b as u64).wrapping_add(b.c.iter().fold(0u64, |x, &y| x.wrapping_add(y as u64)));
        acc = acc.wrapping_add(b.d.to_bits());
    }
    // std::mem::swap on scalars and arrays
    let mut x = bb(0x1111u64); let mut y = bb(0x2222u64); std::mem::swap(&mut x, &mut y);
    acc = acc.wrapping_add(x).wrapping_add(y << 1);
    let mut p = [bb(1u64), bb(2), bb(3)]; let mut q = [bb(4u64), bb(5), bb(6)]; std::mem::swap(&mut p, &mut q);
    acc = acc.wrapping_add(p.iter().chain(q.iter()).fold(0, |a, &v| a.wrapping_mul(31).wrapping_add(v)));
    std::process::exit((acc % 241) as i32);
}
