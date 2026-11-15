#![no_std]
#![feature(core_intrinsics, const_eval_select)]
#![allow(internal_features)]
use projected_aggregate_types::Union24;
const fn ct(_: u64, _: Union24) -> u64 {
    0
}
#[inline(never)]
fn rt(s: u64, v: Union24) -> u64 {
    unsafe { v.words[0].rotate_left(7) ^ v.words[1].wrapping_add(s) ^ v.words[2].rotate_right(11) }
}
#[unsafe(no_mangle)]
pub const fn selected(v: Union24, s: u64) -> u64 {
    core::intrinsics::const_eval_select((s, v), ct, rt)
}
