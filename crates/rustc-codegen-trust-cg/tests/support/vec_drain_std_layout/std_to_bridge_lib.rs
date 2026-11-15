// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Compiled by the bridge (and by LLVM for the oracle). Every function receives
// a `vec::Drain` that LLVM-compiled code built with std's `Vec::drain` (the Vec
// already shortened to the range start, a kept tail recorded in `tail_start` /
// `tail_len`) and drops, drives or hands it back here.
use std::vec::Drain;

#[derive(Clone, Copy)]
pub struct Pt(pub u32, pub u32);

pub struct W<'a>(pub Drain<'a, u32>, pub u8);

#[inline(never)]
pub fn sink(_d: Drain<'_, u32>) {}

#[inline(never)]
pub fn sink_u8(_d: Drain<'_, u8>) {}

#[inline(never)]
pub fn sink_u64(_d: Drain<'_, u64>) {}

#[inline(never)]
pub fn sink_char(_d: Drain<'_, char>) {}

#[inline(never)]
pub fn sink_pair(_d: Drain<'_, (u32, u16)>) {}

#[inline(never)]
pub fn sink_pt(_d: Drain<'_, Pt>) {}

#[inline(never)]
pub fn consume(d: Drain<'_, u32>) -> u32 {
    let mut s = 0;
    for x in d {
        s = s * 10 + x;
    }
    s
}

#[inline(never)]
pub fn pass(d: Drain<'_, u32>) -> Drain<'_, u32> {
    d.into_iter()
}

#[inline(never)]
pub fn pass_move(d: Drain<'_, u32>) -> Drain<'_, u32> {
    d
}

#[inline(never)]
pub fn opt_param(o: Option<Drain<'_, u32>>) -> u32 {
    if let Some(_d) = o { 1 } else { 0 }
}

#[inline(never)]
pub fn struct_param(w: W<'_>) -> u8 {
    let W(_d, b) = w;
    b
}
