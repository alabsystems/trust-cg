// a*b+c (two roundings) must NOT be silently fused into fmadd (one rounding);
// mul_add IS fused. Values chosen so fused != unfused. Guards the no-fast-math
// contract (matches LLVM); the 'unfuse-serial-fma' path must keep them distinct.
// on values where the product's low bits matter. LLVM without fast-math never
// fuses; trust-cg must match. mul_add IS fused. Values chosen so fused != unfused.
use std::hint::black_box as bb;
fn main() {
    let mut acc: u64 = 0;
    // f64: x = 1 + 2^-52 region; product loses bits that fma would keep
    let a = [bb(1.0000000000001f64), bb(1e8 + 1.0), bb(0.1), bb(3.0), bb(1.0 - 1e-15)];
    let b = [bb(1.0000000000001f64), bb(1e8 - 1.0), bb(0.1), bb(7.0000000000001), bb(1.0 + 1e-15)];
    let c = [bb(-1.0000000000002f64), bb(-1e16), bb(-0.010000000000001), bb(-21.0), bb(-1.0)];
    for i in 0..5 { for j in 0..5 { for k in 0..5 {
        let unfused = a[i] * b[j] + c[k];        // two roundings — must stay unfused
        let fused = a[i].mul_add(b[j], c[k]);    // one rounding — fma
        acc = acc.wrapping_add(unfused.to_bits());
        acc = acc.wrapping_add(fused.to_bits().rotate_left(1));
        acc = acc.wrapping_add(((unfused != fused) as u64) * 5);   // often TRUE
    }}}
    std::process::exit((acc % 251) as i32);
}
