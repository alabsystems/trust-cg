// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The deref-STORE twin of the slice-element-part borrow
// (`lower_scalar_memory_store_value`): a reference local `r = &s[k].part`
// that is itself stored into an aggregate (`[&r]`, `(&r, 5)`) is celled by
// the stored-reference cell pass, so the borrow is stored INTO the cell
// rather than bound as a scalar. Parts: a `Name(u32)` newtype field, an
// array-field element `&s[k].arr[j]`, a `[.., x]` tail (`ConstantIndex`
// from the end, including the empty slice), and a `u64` field; plus a
// closure capturing `r` (its own upvar route).
use std::hint::black_box as bb;
#[derive(Clone, Copy, PartialEq, Debug)]
struct Name(u32);
#[derive(Clone, Copy, Debug)]
struct Rec {
    pad: u8,
    n: Name,
    arr: [Name; 3],
    w: u64,
}
#[inline(never)]
fn mk(i: u32) -> Rec {
    let mut a = [Name(0); 3];
    a[0] = Name(i + 7);
    a[1] = Name(i * 3);
    a[2] = Name(i ^ 9);
    Rec {
        pad: i as u8,
        n: Name(i * 11 + 1),
        arr: a,
        w: i as u64 * 1000,
    }
}
#[inline(never)]
fn via_arr(s: &[Rec], k: usize) -> u32 {
    let r = &s[k].n;
    let arr = [&r, &r];
    (**arr[0]).0 * 2 + (**arr[1]).0
}
#[inline(never)]
fn via_arr_idx(s: &[Rec], k: usize, j: usize) -> u32 {
    let r = &s[k].arr[j];
    let t = (&r, 5u8);
    (**t.0).0 + t.1 as u32
}
#[inline(never)]
fn via_tail(s: &[Rec]) -> u32 {
    if let [.., x] = s {
        let r = &x.n;
        let t = [&r];
        (**t[0]).0
    } else {
        0
    }
}
#[inline(never)]
fn via_closure(s: &[Rec], k: usize) -> u32 {
    let r = &s[k].n;
    let f = || {
        let rr = &r;
        rr.0 + 1
    };
    f() + bb(0)
}
#[inline(never)]
fn w64(s: &[Rec], k: usize) -> u64 {
    let r = &s[k].w;
    let arr = [&r];
    **arr[0] + s[k].pad as u64
}
fn main() {
    let v = [mk(bb(0)), mk(bb(1)), mk(bb(2)), mk(bb(3)), mk(bb(4))];
    let mut s = 0u64;
    for k in 0..5 {
        s = s.wrapping_mul(31).wrapping_add(via_arr(&v, bb(k)) as u64);
        s = s
            .wrapping_mul(31)
            .wrapping_add(via_arr_idx(&v, bb(k), bb(k % 3)) as u64);
        s = s
            .wrapping_mul(31)
            .wrapping_add(via_closure(&v, bb(k)) as u64);
        s = s.wrapping_mul(31).wrapping_add(w64(&v, bb(k)));
    }
    s = s
        .wrapping_mul(31)
        .wrapping_add(via_tail(&v[..bb(3)]) as u64 + via_tail(&v[..bb(0)]) as u64);
    println!("{s}");
    std::process::exit((s % 251) as i32);
}
