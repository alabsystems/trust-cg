// neon_bytesum: MERGE-value loop bound (3 arms, last arm 4096); true bound 8.
use std::hint::black_box as bb;
const N: usize = 4096;
#[inline(never)]
fn go(a: *const u8, k: u32) -> u64 {
    let n = match k { 0 => 8usize, 1 => 12usize, _ => N };
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < n { acc = acc.wrapping_add((unsafe { *a.add(i) } as u32).count_ones() as u64); i += 1; }
    acc
}
fn main() {
    let mut v = vec![0u8; N + 1];
    let mut x: u64 = bb(0x243F6A8885A308D3u64);
    let mut i = 0usize;
    while i < N + 1 { x ^= x << 13; x ^= x >> 7; x ^= x << 17; v[i] = (x & 0xFF) as u8; i += 1; }
    let acc = go(v.as_ptr(), bb(0u32));
    std::process::exit((acc % 251) as i32);
}
