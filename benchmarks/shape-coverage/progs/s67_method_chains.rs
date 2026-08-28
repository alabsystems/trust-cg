// method chains on primitives: count_ones/leading_zeros/rotate/abs/min/max/clamp/
// pow/isqrt + slice filter/map/sum. No allocation.
use std::hint::black_box as bb;
fn main() {
    let mut acc = 0u64;
    for i in 0..bb(64u64) {
        let x = i.wrapping_mul(3).wrapping_add(1);
        acc = acc.wrapping_add(x.count_ones() as u64)
            .wrapping_add(x.leading_zeros() as u64)
            .wrapping_add(x.rotate_left(5).wrapping_sub(x))
            .wrapping_add((x as i64).abs() as u64)
            .wrapping_add(x.min(1000).max(10))
            .wrapping_add(x.clamp(5, 500))
            .wrapping_add(x.pow(2 % 3))
            .wrapping_add(x.isqrt());
    }
    let v = [bb(5u64), bb(3), bb(8), bb(1), bb(9)];
    acc = acc.wrapping_add(v.iter().copied().filter(|&x| x > 3).map(|x| x * x).sum::<u64>());
    std::process::exit((acc % 241) as i32);
}
