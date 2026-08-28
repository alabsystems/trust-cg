// niche-optimized Option<NonZero*> must round-trip: 0 encodes None, nonzero the
// value. Iterated by reference (array-by-value IntoIterator is a separate gap).
use std::hint::black_box as bb;
use std::num::{NonZeroU32, NonZeroU64, NonZeroU8};
fn main() {
    let mut acc: u64 = 0;
    let xs = [bb(0u32), bb(1), bb(42), bb(0xffffffff), bb(0)];
    for &x in xs.iter() {
        let o = NonZeroU32::new(x);
        acc = acc.wrapping_add(o.map_or(0xDEAD, |n| n.get() as u64)).wrapping_add(o.is_some() as u64 * 3);
    }
    let ys = [bb(0u64), bb(0x1_0000_0001), bb(u64::MAX)];
    for &y in ys.iter() {
        let o = NonZeroU64::new(y);
        acc = acc.wrapping_add(o.map_or(0, |n| n.get())).wrapping_add(o.is_none() as u64 * 7);
    }
    let bsz = [bb(0u8), bb(255), bb(128)];
    for &b in bsz.iter() {
        let o = NonZeroU8::new(b);
        acc = acc.wrapping_add(o.map_or(11, |n| n.get() as u64));
    }
    std::process::exit((acc % 251) as i32);
}
