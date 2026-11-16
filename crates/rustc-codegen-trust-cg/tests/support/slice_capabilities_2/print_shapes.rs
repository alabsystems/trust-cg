// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
#[derive(Debug, Clone, Copy)]
struct TyId(u32);
#[derive(Debug, Clone, Copy)]
enum Shape {
    SliceLen { elem: TyId },
    StrLen,
}
fn main() {
    let v = bb(0xABu32);
    let n = bb(-42i32);
    let w = bb(7usize);
    println!("[{:#010X}] [{:#x}] [{:x}] [{:08x}]", v, v, n, v);
    println!(
        "{:#x} {:x} {} {}",
        bb(u128::MAX),
        bb(-1i128),
        bb(i128::MIN),
        bb(u64::MAX)
    );
    println!(
        "[{:5}] [{:<5}] [{:^5}] [{:*^7}] [{:+}] [{:+05}]",
        n, n, n, n, v, n
    );
    println!("[{:w$}] [{:>1$}] [{:.3}] [{:.*}]", v, w, n, 2, bb(1.5f64));
    println!(
        "{:?} {:?} {:#?}",
        bb(Shape::SliceLen { elem: TyId(7) }),
        bb(Shape::StrLen),
        bb(TyId(3))
    );
    println!("{0} {1} {0} {name}", v, n, name = bb("nm"));
    eprintln!("err {:?} {:>3}", bb(Some(1u8)), bb(2u8));
}
