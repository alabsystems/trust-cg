// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Compiled by the bridge (and by LLVM for the oracle). Every function builds a
// `vec::Drain` here with `Vec::drain` and lets it reach std's own code: returned
// (bare, in an `Option`, in a tuple) to LLVM-compiled code that iterates, drops
// or leaks it, or leaked here through `mem::forget` of an aggregate. std's
// `Vec::drain` shortens the Vec to the range start before the Drain exists.
use std::vec::Drain;

#[derive(Clone, Copy)]
pub struct Pt(pub u32, pub u32);

/// Move-only: no `Copy`, `Clone` or `Drop`.
pub struct Tok(pub u32);

#[inline(never)]
pub fn make(v: &mut Vec<u32>, k: usize) -> Drain<'_, u32> {
    v.drain(k..)
}

#[inline(never)]
pub fn make_all(v: &mut Vec<u32>) -> Drain<'_, u32> {
    v.drain(..)
}

#[inline(never)]
pub fn make_u8(v: &mut Vec<u8>, k: usize) -> Drain<'_, u8> {
    v.drain(k..)
}

#[inline(never)]
pub fn make_u64(v: &mut Vec<u64>, k: usize) -> Drain<'_, u64> {
    v.drain(k..)
}

#[inline(never)]
pub fn make_char(v: &mut Vec<char>, k: usize) -> Drain<'_, char> {
    v.drain(k..)
}

#[inline(never)]
pub fn make_pair(v: &mut Vec<(u32, u16)>, k: usize) -> Drain<'_, (u32, u16)> {
    v.drain(k..)
}

#[inline(never)]
pub fn make_pt(v: &mut Vec<Pt>, k: usize) -> Drain<'_, Pt> {
    v.drain(k..)
}

#[inline(never)]
pub fn ret_option(v: &mut Vec<u32>, k: usize) -> Option<Drain<'_, u32>> {
    Some(v.drain(k..))
}

#[inline(never)]
pub fn ret_tuple(v: &mut Vec<u32>, k: usize) -> (Drain<'_, u32>, u8) {
    (v.drain(k..), 3)
}

#[inline(never)]
pub fn leak_len(v: &mut Vec<u32>, k: usize) {
    std::mem::forget(Some(v.drain(k..)));
}

#[inline(never)]
pub fn leak_tuple(v: &mut Vec<u32>) {
    std::mem::forget((v.drain(..), 0u8));
}

#[inline(never)]
pub fn dup_tok(v: &mut Vec<Tok>) -> Option<Tok> {
    let mut d = v.drain(..);
    let t = d.next();
    std::mem::forget(Some(d));
    t
}

/// Control: a Drain this function builds, drives and drops itself.
#[inline(never)]
pub fn sum_from(v: &mut Vec<u32>, k: usize) -> u32 {
    let mut s = 0;
    for x in v.drain(k..) {
        s = s * 10 + x;
    }
    s
}
