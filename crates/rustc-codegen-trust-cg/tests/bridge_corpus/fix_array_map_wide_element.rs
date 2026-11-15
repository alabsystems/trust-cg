// Corpus: `<[T; N]>::map` whose SOURCE element is a length-metadata WIDE
// pointer (`&str`, `&[T]`, `&mut [T]`, `*const [T]`, `&CStr`). The wide RESULT
// side, and the `NonNull<[T]>` carrier source, are
// `fix_array_map_wide_result.rs`.
//
// The bridge intercepts the call and builds the element loop itself. A wide
// element is rustc's `ScalarPair` `{ data, len }`; the bridge's one-value type
// for it is the data half alone, so the loop must pass BOTH lanes: the
// `{ data, len }` slot the closure body's by-value parameter declares.
//
// WHAT EACH ROW WOULD CATCH. Every printed value depends on the LENGTH lane or
// on an element read through the data lane:
//  * `str_lens` / `slice_lens` / `raw_lens` / `cstr_lens`: a
//    dropped length lane prints a garbage length (or reads out of bounds);
//  * `str_last_bytes`: indexes the last byte, so a wrong data or length lane is
//    a wrong byte or an out-of-bounds read;
//  * `mut_slice_write`: writes through each `&mut [u8]` element, so a forged
//    data lane writes into another object (`y` must stay untouched);
//  * `mut_str_upper`: rewrites each `&mut str` element in place, so a forged
//    pair rewrites the wrong bytes (or none) and prints the wrong length;
//  * `captured_total`: a capturing `FnMut` over `&str`, in call order;
//  * `captured_wide`: a `move` closure whose environment holds a `&str`, so the
//    environment's own two lanes and each element's two lanes are both read;
//  * `u128_ctl` / `char_ctl`: one-lane controls (a 16-byte scalar element is
//    one lane, not a pair).
#![allow(dead_code)]

use std::ffi::CStr;
use std::hint::black_box as bb;

#[inline(never)]
fn str_lens(a: [&str; 3]) -> [usize; 3] {
    a.map(|s| s.len())
}

#[inline(never)]
fn slice_lens(a: [&[u64]; 2]) -> [u64; 2] {
    a.map(|s| s.iter().sum::<u64>() * 10 + s.len() as u64)
}

#[inline(never)]
fn raw_lens(a: [*const [u8]; 2]) -> [usize; 2] {
    a.map(|p| p.len())
}

#[inline(never)]
fn cstr_lens(a: [&CStr; 2]) -> [usize; 2] {
    a.map(|c| c.to_bytes().len())
}

#[inline(never)]
fn str_last_bytes(a: [&str; 2]) -> [u8; 2] {
    a.map(|s| s.as_bytes()[s.len() - 1])
}

#[inline(never)]
fn mut_slice_write(a: [&mut [u8]; 2]) -> [usize; 2] {
    a.map(|s| {
        if !s.is_empty() {
            s[0] = 9;
        }
        s.len()
    })
}

#[inline(never)]
fn mut_str_upper(a: [&mut str; 2]) -> [usize; 2] {
    a.map(|s| {
        s.make_ascii_uppercase();
        s.len()
    })
}

#[inline(never)]
fn captured_wide(a: [&str; 2], pre: &str) -> [usize; 2] {
    a.map(move |s| s.len() * 10 + pre.len())
}

#[inline(never)]
fn captured_total(a: [&str; 3]) -> ([usize; 3], usize) {
    let mut total = 0;
    let r = a.map(|s| {
        total += s.len();
        total
    });
    (r, total)
}

/// One-lane control: a 16-byte scalar element is one lane, not a pair.
#[inline(never)]
fn u128_ctl(a: [u128; 2]) -> [u128; 2] {
    a.map(|x| (x >> 1) + 1)
}

#[inline(never)]
fn char_ctl(a: [char; 2]) -> [u32; 2] {
    a.map(|c| c as u32 + 1)
}

fn main() {
    // Every printed value is bound to a local first: the whole-program bridge
    // formats only call-stable places.
    let [a0, a1, a2] = str_lens(bb(["hello", "", "wor"]));
    println!("str_lens {} {} {}", a0, a1, a2);
    let xs = bb([1u64, 2, 3]);
    let [s0, s1] = slice_lens(bb([&xs[..], &xs[2..]]));
    println!("slice_lens {} {}", s0, s1);
    let v = bb([1u8, 2, 3]);
    let [r0, r1] = raw_lens(bb([&v[..] as *const [u8], &v[2..] as *const [u8]]));
    println!("raw_lens {} {}", r0, r1);
    let [c0, c1] = cstr_lens(bb([c"hello", c"ab"]));
    println!("cstr_lens {} {}", c0, c1);
    let [b0, b1] = str_last_bytes(bb(["hello", "wor"]));
    println!("str_last_bytes {} {}", b0, b1);
    // `x` holds `y`'s address then `1usize`: a closure handed `x`'s first 16
    // bytes as its `{ data, len }` would write into `y` instead of `x`.
    let mut y = [0u8; 4];
    let mut x = [0u8; 16];
    x[..8].copy_from_slice(&(y.as_mut_ptr() as usize).to_le_bytes());
    x[8..].copy_from_slice(&1usize.to_le_bytes());
    let mut z = [7u8; 2];
    let [m0, m1] = mut_slice_write(bb([&mut x[..], &mut z[..]]));
    let y = bb(y);
    let (x0, z0, z1, y0) = (x[0], z[0], z[1], y[0]);
    println!(
        "mut_slice_write {} {} x0={} z={} {} y0={}",
        m0, m1, x0, z0, z1, y0
    );
    let mut lo = bb(*b"abc");
    let mut hi = bb(*b"de");
    // ASCII bytes, so both are valid UTF-8 (the checked conversion would pull
    // `Utf8Error`'s `Debug` impl into the program).
    let lo_s = unsafe { std::str::from_utf8_unchecked_mut(&mut lo) };
    let hi_s = unsafe { std::str::from_utf8_unchecked_mut(&mut hi) };
    let [u0, u1] = mut_str_upper(bb([lo_s, hi_s]));
    let (lo0, lo2, hi1) = (lo[0], lo[2], hi[1]);
    println!("mut_str_upper {} {} {} {} {}", u0, u1, lo0, lo2, hi1);
    let [w0, w1] = captured_wide(bb(["hello", ""]), bb("xyz"));
    println!("captured_wide {} {}", w0, w1);
    let ([t0, t1, t2], total) = captured_total(bb(["hello", "", "ab"]));
    println!("captured_total {} {} {} {}", t0, t1, t2, total);
    let [q0, q1] = u128_ctl(bb([u128::MAX, 6]));
    let (q0_hi, q1_lo) = ((q0 >> 64) as u64, q1 as u64);
    println!("u128_ctl {} {}", q0_hi, q1_lo);
    let [h0, h1] = char_ctl(bb(['a', 'z']));
    println!("char_ctl {} {}", h0, h1);
}
