// neon_iota_fill lead 2b: the loop BOUND is a MERGE vreg (3 arms, all defs
// OUTSIDE the loop, so the pass's in-loop def discipline never sees them).
// recognize_native_test -> const_value resolves it to the LAST arm (200) and
// the pass builds a 192-element vector prefix for a loop that runs 8 times.
use std::hint::black_box as bb;

#[inline(never)]
fn go(dst: *mut u32, k: u32) {
    let lim = match k { 0 => 8usize, 1 => 12usize, _ => 200usize };
    let mut i = 0usize;
    while i < lim {
        unsafe { *dst.add(i) = i as u32; }
        i += 1;
    }
}

fn main() {
    let mut b = vec![0u32; 256];
    go(b.as_mut_ptr(), bb(0u32));
    let mut acc: u32 = 0;
    for i in 0..256 { acc = acc.wrapping_add(b[i]); }
    std::process::exit((acc % 251) as i32);   // 28 = only 0..=7 written
}
