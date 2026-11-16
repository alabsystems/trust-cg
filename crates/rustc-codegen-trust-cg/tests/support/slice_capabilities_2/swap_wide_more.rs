// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Wide-pointer swaps that are NOT the thin pointer admission's: `*const [u16]`,
// `&mut str`, `&std::path::Path`, a `[u8]` newtype (plain and
// `repr(transparent)`) and a slice-tail DST `&Hdr<[u32]>`. Each keeps a
// two-lane route (the fat slice/str arm or the lane-wise aggregate arm).
// Removing the layout thinness check of `typed_swap_thin_pointer_value`
// changed none of them (2026-11-15), so they are a net, not a test of it.
use std::hint::black_box as bb;
#[allow(dead_code)]
struct W([u8]);
#[repr(transparent)]
#[allow(dead_code)]
struct B([u8]);
#[allow(dead_code)]
struct Hdr<T: ?Sized> {
    n: u8,
    t: T,
}
#[inline(never)]
fn s_raw<'a>(x: &mut *const [u16], y: &mut *const [u16]) {
    std::mem::swap(x, y)
}
fn run_raw() -> u64 {
    let v1 = [1u16, 2, 3, 4];
    let v2 = [5u16; 2];
    let (mut p, mut q): (*const [u16], *const [u16]) = (bb(&v1[..]), bb(&v2[..]));
    s_raw(&mut p, &mut q);
    (p.len() * 10 + q.len()) as u64
}
#[inline(never)]
fn s_mstr<'a>(x: &mut &'a mut str, y: &mut &'a mut str) {
    std::mem::swap(x, y)
}
fn run_mstr() -> u64 {
    let mut s1 = String::from("abc");
    let mut s2 = String::from("hello");
    let (mut p, mut q): (&mut str, &mut str) = (bb(s1.as_mut_str()), bb(s2.as_mut_str()));
    s_mstr(&mut p, &mut q);
    (p.len() * 10 + q.len()) as u64
}
#[inline(never)]
fn s_path<'a>(x: &mut &'a std::path::Path, y: &mut &'a std::path::Path) {
    std::mem::swap(x, y)
}
fn run_path() -> u64 {
    let (mut p, mut q) = (
        std::path::Path::new(bb("/abc")),
        std::path::Path::new(bb("/x")),
    );
    s_path(&mut p, &mut q);
    (p.as_os_str().len() * 10 + q.as_os_str().len()) as u64
}
#[inline(never)]
fn s_w<'a>(x: &mut &'a W, y: &mut &'a W) {
    std::mem::swap(x, y)
}
fn run_w() -> u64 {
    let (s1, s2) = (bb(&[1u8, 2, 3][..]), bb(&[9u8; 5][..]));
    let (mut p, mut q): (&W, &W) = unsafe {
        (
            &*(s1 as *const [u8] as *const W),
            &*(s2 as *const [u8] as *const W),
        )
    };
    s_w(&mut p, &mut q);
    (p.0.len() * 10 + q.0.len() + p.0[0] as usize) as u64
}
#[inline(never)]
fn s_b<'a>(x: &mut &'a B, y: &mut &'a B) {
    std::mem::swap(x, y)
}
fn run_b() -> u64 {
    let (s1, s2) = (bb(&[1u8, 2, 3][..]), bb(&[9u8; 5][..]));
    let (mut p, mut q): (&B, &B) = unsafe {
        (
            &*(s1 as *const [u8] as *const B),
            &*(s2 as *const [u8] as *const B),
        )
    };
    s_b(&mut p, &mut q);
    (p.0.len() * 10 + q.0.len() + p.0[0] as usize) as u64
}
#[inline(never)]
fn s_hsl<'a>(x: &mut &'a Hdr<[u32]>, y: &mut &'a Hdr<[u32]>) {
    std::mem::swap(x, y)
}
fn run_hsl() -> u64 {
    let a = Hdr {
        n: bb(1u8),
        t: [1u32, 2, 3],
    };
    let b = Hdr {
        n: bb(2u8),
        t: [9u32; 5],
    };
    let (mut p, mut q): (&Hdr<[u32]>, &Hdr<[u32]>) = (&a, &b);
    s_hsl(&mut p, &mut q);
    (p.n as usize * 100 + p.t.len() * 10 + q.t.len()) as u64
}
fn main() {
    let mut r = 0u64;
    r = r.wrapping_mul(31).wrapping_add(run_raw());
    r = r.wrapping_mul(31).wrapping_add(run_mstr());
    r = r.wrapping_mul(31).wrapping_add(run_path());
    r = r.wrapping_mul(31).wrapping_add(run_w());
    r = r.wrapping_mul(31).wrapping_add(run_b());
    r = r.wrapping_mul(31).wrapping_add(run_hsl());
    println!("{r}");
    std::process::exit((r % 251) as i32);
}
