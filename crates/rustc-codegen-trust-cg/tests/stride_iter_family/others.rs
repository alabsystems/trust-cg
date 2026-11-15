// Fixture of tests/stride_iter_family_differential_aarch64.rs (`as_chunks`/`as_rchunks`/`as_chunks_mut` and `chunk_by`/`chunk_by_mut`, whose `next` builds a `windows(2)` iterator inside core).
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
fn s_as_chunks_all<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    {
        let (a, r) = v.as_chunks::<1>();
        for x in a {
            h = mix(h, hs(&x[..]));
        }
        h = mix(h, hs(r));
    }
    {
        let (a, r) = v.as_chunks::<2>();
        for x in a {
            h = mix(h, hs(&x[..]));
        }
        h = mix(h, hs(r));
    }
    {
        let (a, r) = v.as_chunks::<3>();
        for x in a {
            h = mix(h, hs(&x[..]));
        }
        h = mix(h, hs(r));
    }
    {
        let (a, r) = v.as_chunks::<4>();
        for x in a {
            h = mix(h, hs(&x[..]));
        }
        h = mix(h, hs(r));
    }
    h.wrapping_add(n as u64)
}
#[inline(never)]
fn s_as_chunks_mut<T: K>(v: &mut [T], n: usize) -> u64 {
    let (a, r) = v.as_chunks_mut::<2>();
    for x in a.iter_mut() {
        x[1].bump();
    }
    for x in r.iter_mut() {
        x.bump();
    }
    a.len() as u64 * 10 + r.len() as u64 + n as u64
}
#[inline(never)]
fn s_as_chunks_rchunks<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    {
        let (r, a) = v.as_rchunks::<2>();
        for x in a {
            h = mix(h, hs(&x[..]));
        }
        h = mix(h, hs(r));
    }
    {
        let (r, a) = v.as_rchunks::<3>();
        for x in a.iter().rev() {
            h = mix(h, hs(&x[..]));
        }
        h = mix(h, hs(r));
    }
    h.wrapping_add(n as u64)
}
#[inline(never)]
fn s_chunk_by_for<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for g in v.chunk_by(|a: &T, b: &T| a.k() % 4 <= b.k() % 4) {
        h = mix(h, hs(g));
    }
    h
}
#[inline(never)]
fn s_chunk_by_last<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.chunk_by(|a: &T, b: &T| a.k() % 4 <= b.k() % 4)
        .last()
        .map_or(7, |g| hs(g))
}
#[inline(never)]
fn s_chunk_by_mut<T: K>(v: &mut [T], n: usize) -> u64 {
    let mut h = 0u64;
    for g in v.chunk_by_mut(|a: &T, b: &T| a.k() % 4 <= b.k() % 4) {
        g[0].bump();
        h = mix(h, hs(g));
    }
    h
}
#[inline(never)]
fn s_chunk_by_rev<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    let mut h = 0u64;
    for g in v.chunk_by(|a: &T, b: &T| a.k() % 4 <= b.k() % 4).rev() {
        h = mix(h, hs(g));
    }
    h
}

/// Row `id`'s shape over `v` with size `n`.
fn case<T: K>(id: u32, v: &mut [T], n: usize) -> u64 {
    match id {
        0 => s_as_chunks_all::<T>(v, n),
        1 => s_as_chunks_mut::<T>(v, n),
        2 => s_as_chunks_rchunks::<T>(v, n),
        3 => s_chunk_by_for::<T>(v, n),
        4 => s_chunk_by_last::<T>(v, n),
        5 => s_chunk_by_mut::<T>(v, n),
        6 => s_chunk_by_rev::<T>(v, n),
        _ => u64::MAX,
    }
}

const SHAPES: u32 = 7;

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
