// Fixture of tests/stride_iter_family_differential_aarch64.rs (`for`/`next`/`len`/`size_hint`/`last`/`nth`/`rev`/`next_back`/`nth_back`/`enumerate`/`skip`/`remainder`/`into_remainder` over the nine slice chunk and window iterators).
// Generated once from the sweep's shape tables; edit by hand, keeping each
// `s_<shape>` function's row id (its position in `main`) stable.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Every row prints `<row> <type> <len> <n> <value> <buffer hash>` for each
// slice length 0..=9 and chunk/window size 1..=4, so a wrong chunk, a wrong
// count, a skipped or extra element, or a write through a `_mut` chunk to the
// wrong element changes a printed line.
#![allow(unused)]
use std::hint::black_box as bb;
trait K: Copy {
    fn k(self) -> u64;
    fn mk(i: u64) -> Self;
    fn bump(&mut self);
}
impl K for u8 {
    fn k(self) -> u64 {
        self as u64
    }
    fn mk(i: u64) -> Self {
        (i * 7 + 3) as u8
    }
    fn bump(&mut self) {
        *self = self.wrapping_mul(3).wrapping_add(1)
    }
}
impl K for u32 {
    fn k(self) -> u64 {
        self as u64
    }
    fn mk(i: u64) -> Self {
        (i * 40503 + 5) as u32
    }
    fn bump(&mut self) {
        *self = self.wrapping_mul(5).wrapping_add(2)
    }
}
impl K for u64 {
    fn k(self) -> u64 {
        self
    }
    fn mk(i: u64) -> Self {
        i.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1)
    }
    fn bump(&mut self) {
        *self = self.wrapping_mul(7).wrapping_add(3)
    }
}
#[derive(Clone, Copy)]
struct P {
    a: u32,
    b: u16,
}
impl K for P {
    fn k(self) -> u64 {
        self.a as u64 * 3 + self.b as u64
    }
    fn mk(i: u64) -> Self {
        P {
            a: (i * 5 + 1) as u32,
            b: (i * 11 + 2) as u16,
        }
    }
    fn bump(&mut self) {
        self.a = self.a.wrapping_add(7);
        self.b ^= 5
    }
}
#[derive(Clone, Copy)]
struct Q {
    a: u8,
    b: u8,
    c: u8,
}
impl K for Q {
    fn k(self) -> u64 {
        self.a as u64 * 65536 + self.b as u64 * 256 + self.c as u64
    }
    fn mk(i: u64) -> Self {
        Q {
            a: (i * 3) as u8,
            b: (i + 9) as u8,
            c: (i * 13 + 1) as u8,
        }
    }
    fn bump(&mut self) {
        self.c = self.c.wrapping_add(1)
    }
}
fn hs<T: K>(c: &[T]) -> u64 {
    let mut h = c.len() as u64 + 1;
    let mut i = 0;
    while i < c.len() {
        let x = &c[i];
        h = h
            .wrapping_mul(1000003)
            .wrapping_add(x.k().wrapping_add(i as u64));
        i += 1;
    }
    h
}
fn mix(a: u64, b: u64) -> u64 {
    a.wrapping_mul(31).wrapping_add(b)
}
#[inline(never)]
fn s_chunks_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for (i, c) in v.chunks(n).enumerate() {
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for (i, c) in v.chunks_exact(n).enumerate() {
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.chunks_exact(n) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_last<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.chunks_exact(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_chunks_exact_len<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.chunks_exact(n).len() as u64
}
#[inline(never)]
fn s_chunks_exact_mut_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for (i, c) in v.chunks_exact_mut(n).enumerate() {
        c[0].bump();
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_mut_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for c in v.chunks_exact_mut(n) {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_mut_intorem<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.chunks_exact_mut(n);
    let a = it.next().map_or(5, |c| {
        c[0].bump();
        hs(c)
    });
    let r = it.into_remainder();
    for x in r.iter_mut() {
        x.bump();
    }
    mix(a, hs(r))
}
#[inline(never)]
fn s_chunks_exact_mut_last<T: K>(v: &mut [T], n: usize) -> u64 {
    v.chunks_exact_mut(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_chunks_exact_mut_len<T: K>(v: &mut [T], n: usize) -> u64 {
    v.chunks_exact_mut(n).len() as u64
}
#[inline(never)]
fn s_chunks_exact_mut_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.chunks_exact_mut(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_chunks_exact_mut_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for c in v.chunks_exact_mut(n).rev() {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_mut_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.chunks_exact_mut(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_chunks_exact_mut_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.chunks_exact_mut(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks_exact(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_chunks_exact_nth<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks_exact(n);
    let a = it.nth(1).map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_chunks_exact_nthback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks_exact(n);
    let a = it.nth_back(1).map_or(7, |c| hs(c));
    let b = it.next_back().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_chunks_exact_rem<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks_exact(n);
    let a = hs(it.remainder());
    it.next();
    mix(a, hs(it.remainder()))
}
#[inline(never)]
fn s_chunks_exact_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.chunks_exact(n).rev() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks_exact(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_chunks_exact_skip<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.chunks_exact(n).skip(1) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_exact_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks_exact(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.chunks(n) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_last<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.chunks(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_chunks_len<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.chunks(n).len() as u64
}
#[inline(never)]
fn s_chunks_mut_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for (i, c) in v.chunks_mut(n).enumerate() {
        c[0].bump();
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_chunks_mut_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for c in v.chunks_mut(n) {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_mut_last<T: K>(v: &mut [T], n: usize) -> u64 {
    v.chunks_mut(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_chunks_mut_len<T: K>(v: &mut [T], n: usize) -> u64 {
    v.chunks_mut(n).len() as u64
}
#[inline(never)]
fn s_chunks_mut_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.chunks_mut(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_chunks_mut_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for c in v.chunks_mut(n).rev() {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_mut_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.chunks_mut(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_chunks_mut_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.chunks_mut(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_chunks_nth<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks(n);
    let a = it.nth(1).map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_chunks_nthback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks(n);
    let a = it.nth_back(1).map_or(7, |c| hs(c));
    let b = it.next_back().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_chunks_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.chunks(n).rev() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_chunks_skip<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.chunks(n).skip(1) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_chunks_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.chunks(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for (i, c) in v.rchunks(n).enumerate() {
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for (i, c) in v.rchunks_exact(n).enumerate() {
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.rchunks_exact(n) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_last<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.rchunks_exact(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_rchunks_exact_len<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.rchunks_exact(n).len() as u64
}
#[inline(never)]
fn s_rchunks_exact_mut_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for (i, c) in v.rchunks_exact_mut(n).enumerate() {
        c[0].bump();
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_mut_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for c in v.rchunks_exact_mut(n) {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_mut_intorem<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.rchunks_exact_mut(n);
    let a = it.next().map_or(5, |c| {
        c[0].bump();
        hs(c)
    });
    let r = it.into_remainder();
    for x in r.iter_mut() {
        x.bump();
    }
    mix(a, hs(r))
}
#[inline(never)]
fn s_rchunks_exact_mut_last<T: K>(v: &mut [T], n: usize) -> u64 {
    v.rchunks_exact_mut(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_rchunks_exact_mut_len<T: K>(v: &mut [T], n: usize) -> u64 {
    v.rchunks_exact_mut(n).len() as u64
}
#[inline(never)]
fn s_rchunks_exact_mut_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.rchunks_exact_mut(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_rchunks_exact_mut_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for c in v.rchunks_exact_mut(n).rev() {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_mut_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.rchunks_exact_mut(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_rchunks_exact_mut_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.rchunks_exact_mut(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks_exact(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_rchunks_exact_nth<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks_exact(n);
    let a = it.nth(1).map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_rchunks_exact_nthback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks_exact(n);
    let a = it.nth_back(1).map_or(7, |c| hs(c));
    let b = it.next_back().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_rchunks_exact_rem<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks_exact(n);
    let a = hs(it.remainder());
    it.next();
    mix(a, hs(it.remainder()))
}
#[inline(never)]
fn s_rchunks_exact_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.rchunks_exact(n).rev() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks_exact(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_rchunks_exact_skip<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.rchunks_exact(n).skip(1) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_exact_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks_exact(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.rchunks(n) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_last<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.rchunks(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_rchunks_len<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.rchunks(n).len() as u64
}
#[inline(never)]
fn s_rchunks_mut_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for (i, c) in v.rchunks_mut(n).enumerate() {
        c[0].bump();
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_rchunks_mut_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for c in v.rchunks_mut(n) {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_mut_last<T: K>(v: &mut [T], n: usize) -> u64 {
    v.rchunks_mut(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_rchunks_mut_len<T: K>(v: &mut [T], n: usize) -> u64 {
    v.rchunks_mut(n).len() as u64
}
#[inline(never)]
fn s_rchunks_mut_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.rchunks_mut(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_rchunks_mut_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for c in v.rchunks_mut(n).rev() {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_mut_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.rchunks_mut(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_rchunks_mut_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut it = v.rchunks_mut(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        c[0].bump();
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_rchunks_nth<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks(n);
    let a = it.nth(1).map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_rchunks_nthback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks(n);
    let a = it.nth_back(1).map_or(7, |c| hs(c));
    let b = it.next_back().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_rchunks_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.rchunks(n).rev() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_rchunks_skip<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.rchunks(n).skip(1) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_rchunks_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.rchunks(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_windows_enumerate<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for (i, c) in v.windows(n).enumerate() {
        h = mix(h, hs(c).wrapping_add(i as u64));
    }
    h
}
#[inline(never)]
fn s_windows_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.windows(n) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_windows_last<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.windows(n).last().map_or(7, |c| hs(c))
}
#[inline(never)]
fn s_windows_len<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.windows(n).len() as u64
}
#[inline(never)]
fn s_windows_nextback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.windows(n);
    let a = it.next_back().map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    let d = it.next_back().map_or(11, |c| hs(c));
    mix(mix(a, b), d)
}
#[inline(never)]
fn s_windows_nth<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.windows(n);
    let a = it.nth(1).map_or(7, |c| hs(c));
    let b = it.next().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_windows_nthback<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.windows(n);
    let a = it.nth_back(1).map_or(7, |c| hs(c));
    let b = it.next_back().map_or(9, |c| hs(c));
    mix(a, b)
}
#[inline(never)]
fn s_windows_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.windows(n).rev() {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_windows_sizehint<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.windows(n);
    let a = it.next().is_some() as u64;
    let (lo, hi) = it.size_hint();
    a * 10000 + lo as u64 * 100 + hi.map_or(99, |x| x as u64)
}
#[inline(never)]
fn s_windows_skip<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for c in v.windows(n).skip(1) {
        h = mix(h, hs(c));
    }
    h
}
#[inline(never)]
fn s_windows_whilenext<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut it = v.windows(n);
    let mut h = 0u64;
    while let Some(c) = it.next() {
        h = mix(h, hs(c));
    }
    h
}

/// Row `id`'s shape over `v` with size `n`.
fn case<T: K>(id: u32, v: &mut [T], n: usize) -> u64 {
    match id {
        0 => s_chunks_enumerate::<T>(v, n),
        1 => s_chunks_exact_enumerate::<T>(v, n),
        2 => s_chunks_exact_for::<T>(v, n),
        3 => s_chunks_exact_last::<T>(v, n),
        4 => s_chunks_exact_len::<T>(v, n),
        5 => s_chunks_exact_mut_enumerate::<T>(v, n),
        6 => s_chunks_exact_mut_for::<T>(v, n),
        7 => s_chunks_exact_mut_intorem::<T>(v, n),
        8 => s_chunks_exact_mut_last::<T>(v, n),
        9 => s_chunks_exact_mut_len::<T>(v, n),
        10 => s_chunks_exact_mut_nextback::<T>(v, n),
        11 => s_chunks_exact_mut_rev::<T>(v, n),
        12 => s_chunks_exact_mut_sizehint::<T>(v, n),
        13 => s_chunks_exact_mut_whilenext::<T>(v, n),
        14 => s_chunks_exact_nextback::<T>(v, n),
        15 => s_chunks_exact_nth::<T>(v, n),
        16 => s_chunks_exact_nthback::<T>(v, n),
        17 => s_chunks_exact_rem::<T>(v, n),
        18 => s_chunks_exact_rev::<T>(v, n),
        19 => s_chunks_exact_sizehint::<T>(v, n),
        20 => s_chunks_exact_skip::<T>(v, n),
        21 => s_chunks_exact_whilenext::<T>(v, n),
        22 => s_chunks_for::<T>(v, n),
        23 => s_chunks_last::<T>(v, n),
        24 => s_chunks_len::<T>(v, n),
        25 => s_chunks_mut_enumerate::<T>(v, n),
        26 => s_chunks_mut_for::<T>(v, n),
        27 => s_chunks_mut_last::<T>(v, n),
        28 => s_chunks_mut_len::<T>(v, n),
        29 => s_chunks_mut_nextback::<T>(v, n),
        30 => s_chunks_mut_rev::<T>(v, n),
        31 => s_chunks_mut_sizehint::<T>(v, n),
        32 => s_chunks_mut_whilenext::<T>(v, n),
        33 => s_chunks_nextback::<T>(v, n),
        34 => s_chunks_nth::<T>(v, n),
        35 => s_chunks_nthback::<T>(v, n),
        36 => s_chunks_rev::<T>(v, n),
        37 => s_chunks_sizehint::<T>(v, n),
        38 => s_chunks_skip::<T>(v, n),
        39 => s_chunks_whilenext::<T>(v, n),
        40 => s_rchunks_enumerate::<T>(v, n),
        41 => s_rchunks_exact_enumerate::<T>(v, n),
        42 => s_rchunks_exact_for::<T>(v, n),
        43 => s_rchunks_exact_last::<T>(v, n),
        44 => s_rchunks_exact_len::<T>(v, n),
        45 => s_rchunks_exact_mut_enumerate::<T>(v, n),
        46 => s_rchunks_exact_mut_for::<T>(v, n),
        47 => s_rchunks_exact_mut_intorem::<T>(v, n),
        48 => s_rchunks_exact_mut_last::<T>(v, n),
        49 => s_rchunks_exact_mut_len::<T>(v, n),
        50 => s_rchunks_exact_mut_nextback::<T>(v, n),
        51 => s_rchunks_exact_mut_rev::<T>(v, n),
        52 => s_rchunks_exact_mut_sizehint::<T>(v, n),
        53 => s_rchunks_exact_mut_whilenext::<T>(v, n),
        54 => s_rchunks_exact_nextback::<T>(v, n),
        55 => s_rchunks_exact_nth::<T>(v, n),
        56 => s_rchunks_exact_nthback::<T>(v, n),
        57 => s_rchunks_exact_rem::<T>(v, n),
        58 => s_rchunks_exact_rev::<T>(v, n),
        59 => s_rchunks_exact_sizehint::<T>(v, n),
        60 => s_rchunks_exact_skip::<T>(v, n),
        61 => s_rchunks_exact_whilenext::<T>(v, n),
        62 => s_rchunks_for::<T>(v, n),
        63 => s_rchunks_last::<T>(v, n),
        64 => s_rchunks_len::<T>(v, n),
        65 => s_rchunks_mut_enumerate::<T>(v, n),
        66 => s_rchunks_mut_for::<T>(v, n),
        67 => s_rchunks_mut_last::<T>(v, n),
        68 => s_rchunks_mut_len::<T>(v, n),
        69 => s_rchunks_mut_nextback::<T>(v, n),
        70 => s_rchunks_mut_rev::<T>(v, n),
        71 => s_rchunks_mut_sizehint::<T>(v, n),
        72 => s_rchunks_mut_whilenext::<T>(v, n),
        73 => s_rchunks_nextback::<T>(v, n),
        74 => s_rchunks_nth::<T>(v, n),
        75 => s_rchunks_nthback::<T>(v, n),
        76 => s_rchunks_rev::<T>(v, n),
        77 => s_rchunks_sizehint::<T>(v, n),
        78 => s_rchunks_skip::<T>(v, n),
        79 => s_rchunks_whilenext::<T>(v, n),
        80 => s_windows_enumerate::<T>(v, n),
        81 => s_windows_for::<T>(v, n),
        82 => s_windows_last::<T>(v, n),
        83 => s_windows_len::<T>(v, n),
        84 => s_windows_nextback::<T>(v, n),
        85 => s_windows_nth::<T>(v, n),
        86 => s_windows_nthback::<T>(v, n),
        87 => s_windows_rev::<T>(v, n),
        88 => s_windows_sizehint::<T>(v, n),
        89 => s_windows_skip::<T>(v, n),
        90 => s_windows_whilenext::<T>(v, n),
        _ => u64::MAX,
    }
}

const SHAPES: u32 = 91;

/// Every shape over every slice length 0..=9 and size 1..=4, on a fresh buffer.
fn rows<T: K>(tag: u64) {
    let mut id = 0u32;
    while id < SHAPES {
        let mut len = 0usize;
        while len <= 9 {
            let mut n = 1usize;
            while n <= 4 {
                let mut buf = [T::mk(0); 9];
                let mut i = 0;
                while i < 9 {
                    buf[i] = T::mk(i as u64 * 7 + tag);
                    i += 1;
                }
                let h = case::<T>(bb(id), &mut buf[..bb(len)], bb(n));
                println!("{} {} {} {} {} {}", id, tag, len, n, h, hs(&buf[..]));
                n += 1;
            }
            len += 1;
        }
        id += 1;
    }
}

fn main() {
    rows::<u8>(1);
    rows::<u32>(2);
    rows::<u64>(3);
    rows::<P>(4);
    rows::<Q>(5);
}
