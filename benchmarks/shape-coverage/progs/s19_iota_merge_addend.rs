// neon_iota_fill: the invariant ADDEND of the affine stored value is a MERGE
// vreg (3 arms, one live def each). value_shape() resolves it with const_value
// through the last-wins def map and materializes THAT constant into the vector
// preheader, so the vector prefix stores the wrong values.
use std::hint::black_box as bb;

#[inline(never)]
fn fill(dst: *mut u32, n: usize, k: u32) {
    let r = match k { 0 => 3u32, 1 => 5u32, _ => 7u32 };
    let mut i = 0usize;
    while i < n {
        unsafe { *dst.add(i) = (i as u32).wrapping_add(r); }
        i += 1;
    }
}

fn main() {
    let n = bb(200usize);
    let mut b = vec![0u32; 256];
    fill(b.as_mut_ptr(), n, bb(0u32));
    let mut acc: u32 = 0;
    for i in 0..n { acc = acc.wrapping_add(b[i]); }
    std::process::exit((acc % 251) as i32);
}
