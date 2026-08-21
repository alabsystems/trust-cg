// neon_bytesum: raw-pointer popcount byte-sum whose load index is `i + 1`
// (the iv's LATCH source). same_as_iv strips the iv through its latch copy.
use std::hint::black_box as bb;
const N: usize = 4096;
#[inline(never)]
fn go(a: *const u8) -> u64 {
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N {
        let ii = i + 1;
        acc = acc.wrapping_add((unsafe { *a.add(ii) } as u32).count_ones() as u64);
        i = ii;
    }
    acc
}
fn main() {
    let mut v = vec![0u8; N + 1];
    let mut x: u64 = bb(0x243F6A8885A308D3u64);
    let mut i = 0usize;
    while i < N + 1 { x ^= x << 13; x ^= x >> 7; x ^= x << 17; v[i] = (x & 0xFF) as u8; i += 1; }
    let acc = go(v.as_ptr());
    std::process::exit((acc % 251) as i32);
}
