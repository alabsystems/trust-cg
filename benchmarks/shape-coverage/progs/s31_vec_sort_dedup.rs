// Vec push/sort/dedup/enumerate/fold. Declines: PartialOrd::lt FnDef (sort comparator).
use std::hint::black_box as bb;
fn main() {
    let mut v: Vec<u64> = Vec::new();
    let mut s = bb(0x1234u64);
    for _ in 0..bb(400u64) { s = s.wrapping_mul(6364136223846793005).wrapping_add(1); v.push(s >> 33); }
    v.sort();
    v.dedup();
    let acc = v.iter().enumerate().fold(0u64, |a, (i, &x)| a.wrapping_add(x.wrapping_mul(i as u64 + 1)));
    std::process::exit((acc % 227) as i32);
}
