// bit intrinsics on all widths (u8/u16/u32/u64): reverse_bits, swap_bytes,
// rotate_left/right, leading_zeros — each maps to specific instructions (RBIT,
// REV, REV16, extract-rotate) whose width form must be correct.
use std::hint::black_box as bb;
fn main() {
    let mut acc: u64 = 0;
    let u64s: [u64; 3] = [bb(0x0123456789abcdef), bb(0xffff_0000_ffff_0000), bb(1)];
    for &x in u64s.iter() {
        acc = acc.wrapping_add(x.reverse_bits()).wrapping_add(x.swap_bytes());
        acc = acc.wrapping_add(x.rotate_left(17)).wrapping_add(x.rotate_right(29));
    }
    let u32s: [u32; 3] = [bb(0x12345678), bb(0xff00ff00), bb(0x80000001)];
    for &x in u32s.iter() { acc = acc.wrapping_add(x.reverse_bits() as u64).wrapping_add(x.swap_bytes() as u64).wrapping_add(x.rotate_left(13) as u64); }
    let u16s: [u16; 3] = [bb(0x1234), bb(0xabcd), bb(0x8001)];
    for &x in u16s.iter() { acc = acc.wrapping_add(x.reverse_bits() as u64).wrapping_add(x.swap_bytes() as u64).wrapping_add(x.rotate_left(5) as u64); }
    let u8s: [u8; 3] = [bb(0x81), bb(0xff), bb(0x12)];
    for &x in u8s.iter() { acc = acc.wrapping_add(x.reverse_bits() as u64).wrapping_add(x.rotate_left(3) as u64).wrapping_add(x.leading_zeros() as u64); }
    std::process::exit((acc % 239) as i32);
}
