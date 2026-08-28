// leading/trailing zeros, popcount, rotate_left/right, wrapping_neg on boundary values
// leading/trailing zeros, popcount, rotate on boundary values (bit-precise)
use std::hint::black_box as bb;
fn main() {
    let v = [bb(0u64), bb(1), bb(0x8000_0000_0000_0000), bb(0xffff_ffff_ffff_ffff), bb(0xf0f0_f0f0_0f0f_0f0f)];
    let mut acc: u64 = 0;
    for &x in v.iter() {
        acc = acc.wrapping_add(x.leading_zeros() as u64).wrapping_add(x.trailing_zeros() as u64);
        acc = acc.wrapping_add(x.count_ones() as u64).wrapping_add(x.rotate_left(13)).wrapping_add(x.rotate_right(7));
        acc = acc.wrapping_add(x.wrapping_neg());
    }
    std::process::exit((acc % 233) as i32);
}
