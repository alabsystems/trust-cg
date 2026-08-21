// TARGET A: address indexed by the INCREMENTED value (q+s), while the loop test
// and the iv are q.  strip_copies(iv) walks the latch copy `q = qq` to qq, so
// same_as_iv(qq, iv) is TRUE and resolve_addr_base hands back `base` for an
// address that is really base + iv + s.
use std::hint::black_box as bb;
#[inline(never)]
fn go(buf: &mut [u8], s: usize, q0: usize) {
    let mut q = q0;
    while q < 64 { let qq = q + s; buf[qq] = 1u8; q = qq; }
}
fn main() {
    let s = bb(3usize); let q0 = bb(0usize);
    let mut b = vec![0u8; 160];
    go(&mut b, s, q0);
    let mut acc: u64 = 0; let mut i = 0usize;
    while i < 160 { acc = acc.wrapping_add((b[i] as u64) * (i as u64 + 1)); i += 1; }
    std::process::exit((acc % 251) as i32);
}
