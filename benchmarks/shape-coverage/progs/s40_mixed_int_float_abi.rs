// mixed int/float calling convention: interleaved X-reg/V-reg args, >8 of each
// (stack spill), mixed widths. A misassigned arg register misplaces a value —
// the ABI blindspot whole-program gates cannot see (cross-backend-abi-blindspot).
use std::hint::black_box as bb;
#[inline(never)]
fn f(a: u64, x: f64, b: i32, y: f32, c: u8, z: f64, d: i64, w: f32, e: u16, v: f64,
     g: i8, u: f32, h: u32, t: f64, i: u64, s: f32) -> u64 {
    let fp = (x + z as f64 + v + t) + (y + w + u + s) as f64;
    (a ^ (b as u64) ^ (c as u64) ^ (d as u64) ^ (e as u64) ^ (g as u8 as u64)
        ^ (h as u64) ^ i).wrapping_add(fp.to_bits())
}
fn main() {
    let mut acc: u64 = 0;
    for k in 0..bb(50u64) {
        acc = acc.wrapping_add(f(
            bb(k), bb(1.5 + k as f64), bb(-3), bb(2.5f32), bb(7), bb(0.25),
            bb(-100), bb(1.25f32), bb(9), bb(4.5), bb(-2), bb(0.5f32),
            bb(123456), bb(8.0), bb(k.wrapping_mul(3)), bb(0.125f32),
        ));
    }
    std::process::exit((acc % 251) as i32);
}
