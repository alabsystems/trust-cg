// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
#[derive(Clone, Copy)]
struct LR {
    start: u32,
    end: u32,
}
#[derive(Clone, Copy)]
struct Mixed {
    a: u8,
    b: u64,
    c: i16,
}
struct Holder {
    pad: u8,
    ranges: [LR; 3],
}
fn unflatten(flat: &[u32; 8], out: &mut [LR; 4]) {
    let mut i = 0;
    while i < 4 {
        out[i] = LR {
            start: flat[2 * i],
            end: flat[2 * i + 1],
        };
        i += 1;
    }
}
fn mixed(out: &mut [Mixed; 3], k: u64) {
    for i in 0..3 {
        out[i] = Mixed {
            a: i as u8,
            b: k << i,
            c: -(i as i16),
        };
    }
    out[2] = out[0];
}
fn field(h: &mut Holder, s: u32) {
    for i in 0..3 {
        h.ranges[i] = LR {
            start: s + i as u32,
            end: s,
        };
    }
    h.ranges[bb(1)] = LR { start: 99, end: 98 };
}
fn main() {
    let flat = bb([1, 2, 3, 4, 5, 6, 7, 8]);
    let mut o = [LR { start: 0, end: 0 }; 4];
    unflatten(&flat, &mut o);
    let mut m = [Mixed { a: 9, b: 9, c: 9 }; 3];
    mixed(&mut m, bb(3));
    let mut h = Holder {
        pad: 1,
        ranges: [LR { start: 0, end: 0 }; 3],
    };
    field(&mut h, bb(20));
    let mut s = h.pad as u64;
    for i in 0..4 {
        s = s * 100 + o[i].start as u64 * 10 + o[i].end as u64;
    }
    for i in 0..3 {
        s = s.wrapping_mul(1000) + m[i].a as u64 * 100 + m[i].b * 10 + (m[i].c + 5) as u64;
        s = s.wrapping_mul(10000) + h.ranges[i].start as u64 * 100 + h.ranges[i].end as u64;
    }
    println!("{}", s);
}
