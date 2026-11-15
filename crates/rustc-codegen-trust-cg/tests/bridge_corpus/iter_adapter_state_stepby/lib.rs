// Fixture library for `tests/iterator_adapter_state_differential.rs`: `StepBy`
// values built by the backend under test and read by LLVM-compiled std code (a
// returned value, an argument, a shared generic instance), and the bridge's own
// StepBy drivers over values std's `StepBy::new` built. The bridge admits
// `StepBy` only at -Copt-level=0. Every output is fully determined by std.

use std::iter::{Chain, StepBy};
use std::ops::{Range, RangeInclusive};

#[inline(never)]
pub fn ret_u32(n: u32) -> StepBy<Range<u32>> {
    (0..n).step_by(2)
}
#[inline(never)]
pub fn ret_u8(a: u8, b: u8) -> StepBy<Range<u8>> {
    (a..b).step_by(100)
}
#[inline(never)]
pub fn ret_u64_near_max() -> StepBy<Range<u64>> {
    (u64::MAX - 10..u64::MAX).step_by(4)
}
#[inline(never)]
pub fn ret_empty(n: u32) -> StepBy<Range<u32>> {
    (n..n).step_by(3)
}
#[inline(never)]
pub fn ret_i32(n: i32) -> StepBy<Range<i32>> {
    (0..n).step_by(2)
}
#[inline(never)]
pub fn ret_incl_i32(a: i32, b: i32) -> StepBy<RangeInclusive<i32>> {
    (a..=b).step_by(3)
}
#[inline(never)]
pub fn ret_incl_u8(a: u8, b: u8) -> StepBy<RangeInclusive<u8>> {
    (a..=b).step_by(2)
}
#[inline(never)]
pub fn ret_chain(n: i32) -> StepBy<Chain<Range<i32>, Range<i32>>> {
    (0..n).chain(10..10 + n).step_by(2)
}
/// A step above `u8::MAX`: core's countdown `spec_next` steps by `u8::MAX`.
#[inline(never)]
pub fn ret_u8_step_over_max(a: u8, b: u8) -> StepBy<Range<u8>> {
    (a..b).step_by(300)
}
/// A `Range` wider than `usize`: no `SpecRangeSetup`, core's default
/// `first_take` / `nth` stepping.
#[inline(never)]
pub fn ret_u128(n: u128) -> StepBy<Range<u128>> {
    (0..n).step_by(5)
}
#[inline(never)]
pub fn terminal_incl_u64_sum(it: StepBy<RangeInclusive<u64>>) -> u64 {
    it.sum()
}
#[inline(never)]
pub fn terminal_usize_count(it: StepBy<Range<usize>>) -> usize {
    it.count()
}
#[inline(never)]
pub fn for_sum(it: StepBy<Range<u32>>) -> u32 {
    let mut s = 0;
    for x in it {
        s += x;
    }
    s
}
#[inline(never)]
pub fn next_pair(mut it: StepBy<Range<u64>>) -> (Option<u64>, Option<u64>) {
    (it.next(), it.next())
}
#[inline(never)]
pub fn terminal_sum(it: StepBy<Range<u32>>) -> u32 {
    it.sum()
}
#[inline(never)]
pub fn terminal_collect(it: StepBy<Range<usize>>) -> Vec<usize> {
    it.collect()
}
#[inline(never)]
pub fn terminal_incl_count(it: StepBy<RangeInclusive<u32>>) -> usize {
    it.count()
}
#[inline(never)]
pub fn local_u16_sum(n: u16, k: usize) -> u32 {
    let mut it = (3..n).step_by(5);
    for _ in 0..k {
        it.next();
    }
    it.map(|x| u32::from(x)).sum()
}
#[inline(never)]
pub fn local_u16_count(n: u16, k: usize) -> usize {
    let mut it = (3..n).step_by(5);
    for _ in 0..k {
        it.next();
    }
    it.count()
}
#[inline(never)]
pub fn local_u16_collect(n: u16, k: usize) -> Vec<u16> {
    let mut it = (3..n).step_by(5);
    for _ in 0..k {
        it.next();
    }
    it.collect()
}
#[inline(never)]
pub fn local_incl_sum(n: u64) -> u64 {
    (1..=n).step_by(4).sum()
}
/// A `&mut` short-circuit terminal hands the StepBy back to std code. The drive
/// keeps its running countdown in `step_minus_one`; a drive the source ran out
/// of mid-skip must still leave std's constant `k-1` there (std's `nth` never
/// changes it), which a later std `next` and `Debug` read.
#[inline(never)]
pub fn ref_any_i32(it: &mut StepBy<Range<i32>>) -> bool {
    it.any(|x| x > 1000)
}
#[inline(never)]
pub fn ref_position_incl(it: &mut StepBy<RangeInclusive<u64>>) -> Option<usize> {
    it.position(|x| x > 1000)
}
/// Instantiates `<Range<u64> as Iterator>::step_by`, `StepBy::<Range<u64>>::new`
/// and `<StepBy<Range<u64>> as Iterator>::next` in this crate; at -O0 a
/// downstream crate shares those instances (`-Zshare-generics`).
#[inline(never)]
pub fn shared_u64(n: u64) -> u64 {
    let mut s = 0;
    for x in (0..n).step_by(4) {
        s += x;
    }
    s
}
