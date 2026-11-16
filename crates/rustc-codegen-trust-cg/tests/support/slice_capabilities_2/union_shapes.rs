// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
use std::mem::MaybeUninit;
#[derive(Debug, Clone, Copy)]
struct P {
    a: u8,
    b: u64,
    c: u16,
}
#[derive(Debug)]
struct G<T> {
    x: T,
    y: T,
    z: [u16; 3],
}
#[derive(Debug)]
enum E {
    A(u64, u8),
    B,
}
#[inline(never)]
fn wr<T>(p: *mut T, v: T) {
    unsafe { p.write(v) }
}
#[inline(never)]
fn mk(k: u64) -> (P, G<i32>, [u64; 3], (u8, u64), E) {
    let mut a = MaybeUninit::<P>::uninit();
    wr(
        a.as_mut_ptr(),
        P {
            a: k as u8,
            b: k << 33,
            c: 7,
        },
    );
    let mut b = MaybeUninit::<G<i32>>::uninit();
    wr(
        b.as_mut_ptr(),
        G {
            x: -(k as i32),
            y: 3,
            z: [1, 2, k as u16],
        },
    );
    let mut c = MaybeUninit::<[u64; 3]>::uninit();
    wr(c.as_mut_ptr(), [k, k + 1, k * k]);
    let mut d = MaybeUninit::<(u8, u64)>::uninit();
    wr(d.as_mut_ptr(), (9, k));
    let mut e = MaybeUninit::<E>::uninit();
    wr(e.as_mut_ptr(), if k % 2 == 0 { E::A(k, 1) } else { E::B });
    unsafe {
        (
            a.assume_init(),
            b.assume_init(),
            c.assume_init(),
            d.assume_init(),
            e.assume_init(),
        )
    }
}
fn main() {
    for k in 0..bb(4u64) {
        let (a, b, c, d, e) = mk(k);
        println!("{:?} {:?} {:?} {:?} {:?}", a, b, c, d, e);
    }
    let arr: [MaybeUninit<P>; 2] = [
        MaybeUninit::new(P { a: 1, b: 2, c: 3 }),
        MaybeUninit::new(P { a: 4, b: 5, c: 6 }),
    ];
    let back: [P; 2] = unsafe { std::mem::transmute(arr) };
    println!("{:?}", back);
}
