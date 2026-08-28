// i64<->u64<->i32<->u32 casts: sign/zero extension + truncation round-trips
// i64<->u64<->i32<->u32 casts (sign/zero extension + truncation)
use std::hint::black_box as bb;
fn main() {
    let mut acc: u64 = 0;
    let seeds: [i64; 5] = [bb(-1), bb(i64::MIN), bb(0x1_0000_0001), bb(-0x8000_0000), bb(0x7fff_ffff_ffff_ffff)];
    for &s in seeds.iter() {
        let u = s as u64;
        let i32v = s as i32;
        let u32v = s as u32;
        let back = (i32v as i64).wrapping_add(u32v as i64).wrapping_add((u >> 32) as i64);
        acc = acc.wrapping_add(back as u64).wrapping_add(u.wrapping_shr(17));
        acc = acc.wrapping_add((i32v as u64) ^ (u32v as u64));
    }
    std::process::exit((acc % 239) as i32);
}
