// Fixture of tests/stride_iter_family_differential_aarch64.rs (`count()` of the nine slice chunk and window iterators).
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
fn s_chunks_count<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.chunks(n).count() as u64
}
#[inline(never)]
fn s_chunks_exact_count<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.chunks_exact(n).count() as u64
}
#[inline(never)]
fn s_chunks_exact_mut_count<T: K>(v: &mut [T], n: usize) -> u64 {
    v.chunks_exact_mut(n).count() as u64
}
#[inline(never)]
fn s_chunks_mut_count<T: K>(v: &mut [T], n: usize) -> u64 {
    v.chunks_mut(n).count() as u64
}
#[inline(never)]
fn s_rchunks_count<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.rchunks(n).count() as u64
}
#[inline(never)]
fn s_rchunks_exact_count<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.rchunks_exact(n).count() as u64
}
#[inline(never)]
fn s_rchunks_exact_mut_count<T: K>(v: &mut [T], n: usize) -> u64 {
    v.rchunks_exact_mut(n).count() as u64
}
#[inline(never)]
fn s_rchunks_mut_count<T: K>(v: &mut [T], n: usize) -> u64 {
    v.rchunks_mut(n).count() as u64
}
#[inline(never)]
fn s_windows_count<T: K>(v: &mut [T], n: usize) -> u64 {
    let v: &[T] = v;
    v.windows(n).count() as u64
}

/// Row `id`'s shape over `v` with size `n`.
fn case<T: K>(id: u32, v: &mut [T], n: usize) -> u64 {
    match id {
        0 => s_chunks_count::<T>(v, n),
        1 => s_chunks_exact_count::<T>(v, n),
        2 => s_chunks_exact_mut_count::<T>(v, n),
        3 => s_chunks_mut_count::<T>(v, n),
        4 => s_rchunks_count::<T>(v, n),
        5 => s_rchunks_exact_count::<T>(v, n),
        6 => s_rchunks_exact_mut_count::<T>(v, n),
        7 => s_rchunks_mut_count::<T>(v, n),
        8 => s_windows_count::<T>(v, n),
        _ => u64::MAX,
    }
}

const SHAPES: u32 = 9;

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
