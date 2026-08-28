// unsigned div/rem with operands above i64::MAX (u64 UDiv/URem, not signed) — guards the census i64/u64-signedness risk area by execution
// unsigned division/remainder with operands above i64::MAX
use std::hint::black_box as bb;
fn main() {
    let a = [bb(0xffff_ffff_ffff_ffffu64), bb(0x8000_0000_0000_0000), bb(0xdead_beef_cafe_babe), bb(12345678901234567890)];
    let b = [bb(3u64), bb(0x8000_0000_0000_0001), bb(7), bb(1000000007)];
    let mut acc: u64 = 0;
    for &x in a.iter() { for &y in b.iter() {
        acc = acc.wrapping_add(x / y).wrapping_add(x % y).wrapping_mul(31).wrapping_add(1);
    }}
    std::process::exit((acc % 249) as i32);
}
