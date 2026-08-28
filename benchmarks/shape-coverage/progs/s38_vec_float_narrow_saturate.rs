// float->narrow-int saturation under VECTORIZATION + memory stores (complements
// the scalar s37; guards the NEON/vectorized fcvt path for f243d837).
use std::hint::black_box as bb;
fn main() {
    let n = bb(256usize);
    let mut acc: u64 = 0;
    let mut out = vec![0u8; n];
    for i in 0..n { let f = (i as f64) * bb(3.0) - bb(100.0); out[i] = f as u8; }  // saturating to u8
    for i in 0..n { acc = acc.wrapping_add(out[i] as u64); }
    let mut o2 = vec![0i16; n];
    for i in 0..n { let f = (i as f32) * bb(1000.0f32) - bb(50000.0f32); o2[i] = f as i16; }
    for i in 0..n { acc = acc.wrapping_add(o2[i] as u16 as u64); }
    let mut o3 = vec![0i32; n];
    for i in 0..n { let f = (i as f64) * bb(1e8); o3[i] = f as i32; }  // large -> i32::MAX
    for i in 0..n { acc = acc.wrapping_add(o3[i] as u32 as u64); }
    std::process::exit((acc % 251) as i32);
}
