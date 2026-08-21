// sret pointer clobber: `f` returns [i16;12] (24 bytes -> indirect via X8) and
// calls `g`, which also returns indirectly and stages its own buffer address in
// X8. The incoming return-buffer pointer must be saved before that call.
use std::hint::black_box as bb;

#[inline(never)]
fn g(p: u32) -> (i32, u64, u64) {
    (p as i32, p as u64, 7)
}

#[inline(never)]
fn f(p1: i16) -> [i16; 12] {
    let (a, b, c) = g(p1 as u32);
    [
        a as i16, b as i16, c as i16, p1, p1, p1, p1, p1, p1, p1, p1, p1,
    ]
}

fn main() {
    let r = f(bb(10334_i16));
    let mut acc = 0_u64;
    let mut q = 0_usize;
    while q < 12 {
        acc = acc
            .wrapping_mul(31)
            .wrapping_add(r[q % 12] as i64 as u64);
        q += 1;
    }
    std::process::exit((acc % 251) as i32); // 177
}
