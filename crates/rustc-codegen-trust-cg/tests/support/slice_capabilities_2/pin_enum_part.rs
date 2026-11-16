// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
#[derive(Clone, Copy, PartialEq)]
enum Kind {
    A,
    B,
    C,
}
#[derive(Clone, Copy, PartialEq)]
enum K16 {
    X = 300,
    Y = 7,
}
#[derive(Clone, Copy)]
struct Rec {
    a: u8,
    k: Kind,
    w: K16,
}
#[inline(never)]
fn find(all: &[Rec], k: &Kind) -> usize {
    let mut i = 0;
    while i < all.len() {
        if &all[i].k == k {
            return i;
        }
        i += 1;
    }
    9
}
#[inline(never)]
fn findw(all: &[Rec], k: &K16) -> usize {
    let mut i = 0;
    while i < all.len() {
        if &all[i].w == k {
            return i;
        }
        i += 1;
    }
    9
}
fn main() {
    let v = [
        Rec {
            a: 1,
            k: Kind::A,
            w: K16::X,
        },
        Rec {
            a: 2,
            k: Kind::C,
            w: K16::Y,
        },
        Rec {
            a: 3,
            k: Kind::B,
            w: K16::X,
        },
    ];
    let v = bb(v);
    std::process::exit(
        (find(&v, &Kind::B) * 10 + find(&v, bb(&Kind::C)) + findw(&v, bb(&K16::Y)) * 100) as i32,
    );
}
