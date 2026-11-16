// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
#[derive(Clone, Copy, PartialEq, Debug)]
struct Name(u32);
#[derive(Clone, Copy, PartialEq, Debug)]
struct W64(u64);
#[derive(Clone, Copy, PartialEq, Debug)]
struct Fl(f32);
#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(transparent)]
struct Tr(i16);
#[derive(Clone, Copy, PartialEq, Debug)]
struct Nest(Name);
struct Rec {
    a: u8,
    n: Name,
    w: W64,
    f: Fl,
    t: Tr,
    nn: Nest,
    o: Option<u32>,
    c: std::cell::Cell<u32>,
}
#[inline(never)]
fn by_name(all: &[Rec], n: &Name) -> usize {
    for (i, r) in all.iter().enumerate() {
        if &r.n == n {
            return i;
        }
    }
    9
}
#[inline(never)]
fn idx(all: &[Rec], n: &Name) -> usize {
    let mut i = 0;
    while i < all.len() {
        if &all[i].n == n {
            return i;
        }
        i += 1;
    }
    9
}
#[inline(never)]
fn w(all: &[Rec], i: usize) -> u64 {
    let r = &all[i].w;
    r.0
}
#[inline(never)]
fn f(all: &[Rec], i: usize) -> f32 {
    let r = &all[i].f;
    r.0
}
#[inline(never)]
fn t(all: &mut [Rec], i: usize) {
    let r = &mut all[i].t;
    r.0 -= 5;
}
#[inline(never)]
fn nn(all: &[Rec], i: usize) -> u32 {
    let r = &all[i].nn.0;
    r.0
}
#[inline(never)]
fn o(all: &[Rec], i: usize) -> u32 {
    let r = &all[i].o;
    r.unwrap_or(77)
}
#[inline(never)]
fn c(all: &[Rec], i: usize) {
    let r = &all[i].c;
    r.set(r.get() + 1);
}
#[inline(never)]
fn last(all: &[Rec]) -> u32 {
    match all {
        [.., l] => {
            let r = &l.n;
            r.0
        }
        [] => 0,
    }
}
fn mk(i: u32) -> Rec {
    Rec {
        a: i as u8,
        n: Name(i * 7),
        w: W64(i as u64 * 1000),
        f: Fl(i as f32 * 0.5),
        t: Tr(i as i16),
        nn: Nest(Name(i + 1)),
        o: if i % 2 == 0 { Some(i) } else { None },
        c: std::cell::Cell::new(i),
    }
}
fn main() {
    let k = bb(0u32);
    let mut v = [mk(k), mk(k + 1), mk(k + 2), mk(k + 3), mk(k + 4)];
    t(&mut v, bb(2));
    c(&v, bb(3));
    c(&v, bb(3));
    println!(
        "{} {} {} {} {} {} {} {} {} {}",
        by_name(&v, &Name(14)),
        idx(&v, &Name(21)),
        idx(&v, &Name(5)),
        w(&v, bb(4)),
        f(&v, bb(3)),
        v[2].t.0,
        nn(&v, bb(1)),
        o(&v, bb(1)) + o(&v, bb(2)),
        v[3].c.get(),
        last(&v)
    );
    println!("{}", last(&v[..0]) + v[0].a as u32);
}
