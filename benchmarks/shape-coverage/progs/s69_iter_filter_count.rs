// iterator-adapter chains on slices: filter().count(), filter().map().sum() —
// work at all opts (the str.bytes() variant hits a separate ordering gap).
use std::hint::black_box as bb;
fn main() {
    let v = [bb(1u64), bb(2), bb(3), bb(4), bb(5), bb(6)];
    let c = v.iter().filter(|&&x| x % 2 == 0).count();
    let s: u64 = v.iter().filter(|&&x| x > 2).map(|&x| x * x).sum();
    std::process::exit(((c as u64).wrapping_add(s) % 233) as i32);
}
