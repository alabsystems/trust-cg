// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Name(pub u32);
#[derive(Clone, Copy)]
pub struct Ind {
    pub tag: u8,
    pub name: Name,
    pub w: u64,
}
#[derive(Clone, Copy)]
pub struct Pad {
    pub a: u8,
    pub inner: (u16, Name),
    pub z: u8,
}
#[inline(never)]
fn find(all: &[Ind], n: &Name) -> usize {
    let mut idx = 0usize;
    while idx < all.len() {
        if &all[idx].name == n {
            return idx;
        }
        idx += 1;
    }
    77
}
#[inline(never)]
fn find_pad(all: &[Pad], n: &Name) -> usize {
    let mut idx = 0usize;
    while idx < all.len() {
        if &all[idx].inner.1 == n {
            return idx;
        }
        idx += 1;
    }
    77
}
#[inline(never)]
fn last_w(all: &[Ind]) -> u64 {
    match all {
        [.., last] => {
            let r = &last.w;
            *r
        }
        [] => 5,
    }
}
#[inline(never)]
fn bump(all: &mut [Ind], i: usize) {
    let r = &mut all[i].name;
    r.0 += 3;
}
fn main() {
    let k = std::hint::black_box(2u32);
    let mut v = [
        Ind {
            tag: 1,
            name: Name(5),
            w: 10,
        },
        Ind {
            tag: 2,
            name: Name(k),
            w: 20,
        },
        Ind {
            tag: 3,
            name: Name(9),
            w: 30,
        },
    ];
    let p = [
        Pad {
            a: 1,
            inner: (3, Name(4)),
            z: 2,
        },
        Pad {
            a: 1,
            inner: (3, Name(k)),
            z: 2,
        },
    ];
    let a = find(&v, &Name(k));
    let b = find(&v, &Name(100));
    let c = find_pad(&p, &Name(k));
    bump(&mut v, 1);
    let d = find(&v, &Name(k + 3));
    let e = last_w(&v);
    let f = last_w(&v[..0]);
    let s = a + b * 3 + c * 5 + d * 7 + e as usize + f as usize + v[0].tag as usize;
    std::process::exit((s % 251) as i32);
}
