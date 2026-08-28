// signed div/rem edge cases incl. i64::MIN, wrapping_div/rem, arithmetic shift-right
// signed division/remainder edge cases incl. i64::MIN, arithmetic shift right
use std::hint::black_box as bb;
fn main() {
    let a = [bb(i64::MIN), bb(-1i64), bb(i64::MAX), bb(-7), bb(1)];
    let b = [bb(-1i64), bb(3), bb(-4), bb(1000000007)];
    let mut acc: i64 = 0;
    for &x in a.iter() { for &y in b.iter() {
        acc = acc.wrapping_add(x.wrapping_div(y)).wrapping_add(x.wrapping_rem(y));
        acc = acc.wrapping_add(x >> (3 & 63));
    }}
    std::process::exit((acc.rem_euclid(247)) as i32);
}
