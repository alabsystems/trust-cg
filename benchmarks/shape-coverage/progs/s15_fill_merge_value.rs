// neon_fill: the fill VALUE is a MERGE vreg (one live def per predecessor, as
// the frontend lowers every block parameter). Resolving it to a constant picks
// whichever arm comes last in the emitted layout and broadcasts that constant
// on EVERY path. Three arms so if-conversion cannot collapse it to one Csel.
// Was: LLVM 192, trust-cg 197 (= 64*7 mod 251, the `_ => 7` arm) at O2 and O3.
use std::hint::black_box as bb;
#[inline(never)]
fn fill(dst: *mut u8, n: usize, k: u32) {
    let v = match k { 0 => 3u8, 1 => 5u8, _ => 7u8 };
    let mut i = 0usize;
    while i < n { unsafe { *dst.add(i) = v; } i += 1; }
}
fn main() {
    let n = bb(64usize);
    let mut b = vec![0u8; 128];
    fill(b.as_mut_ptr(), n, bb(0u32));
    let mut acc = 0u32;
    for i in 0..n { acc += b[i] as u32; }
    std::process::exit((acc % 251) as i32);
}
