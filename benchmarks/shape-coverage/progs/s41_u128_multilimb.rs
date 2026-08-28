// u128 multi-limb arithmetic across the 64-bit boundary: add/sub/mul/div/rem,
// unsigned compare, wrapping shifts 0..128. Complex carry/borrow lowering.
use std::hint::black_box as bb;
fn main() {
    let mut acc: u64 = 0;
    let a: [u128; 5] = [bb(0), bb(1), bb(0xffff_ffff_ffff_ffff), bb(1u128 << 64), bb(0xdeadbeef_cafebabe_12345678_9abcdef0)];
    let b: [u128; 4] = [bb(3), bb(0x1_0000_0000), bb((1u128 << 64) | 7), bb(1000000007)];
    for &x in a.iter() { for &y in b.iter() {
        let s = x.wrapping_add(y); let d = x.wrapping_sub(y); let m = x.wrapping_mul(y);
        let q = x / y; let r = x % y;
        acc = acc.wrapping_add((s ^ (s >> 64)) as u64);
        acc = acc.wrapping_add((d ^ (d >> 64)) as u64);
        acc = acc.wrapping_add((m ^ (m >> 64)) as u64);
        acc = acc.wrapping_add((q ^ (q >> 64)) as u64).wrapping_add((r ^ (r >> 64)) as u64);
        acc = acc.wrapping_add((x < y) as u64).wrapping_add((x >= y) as u64 * 2);
    }}
    for s in 0u32..128 { acc = acc.wrapping_add((a[4].wrapping_shl(s) ^ a[4].wrapping_shr(s)) as u64); }
    std::process::exit((acc % 251) as i32);
}
