// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Distinct component weights expose swapped lanes, bad field offsets,
// truncation, environment displacement and lost trailing arguments. At x7,
// rustc independently places the Pair's second lane on the stack. Keep the
// closures' types exposed through these real source-owned return signatures.
pub(super) const CALLEE: &str = r#"
#[inline(never)]
pub fn pair(s: u64) -> impl Fn((u32, u32)) -> u64 {
    move |p| s + p.0 as u64 * 3 + p.1 as u64 * 17
}
#[inline(never)]
pub fn word(s: u64) -> impl Fn((u32, usize)) -> u64 {
    move |p| s + p.0 as u64 * 3 + p.1 as u64 * 17
}
#[inline(never)]
pub fn pair_spill(s: u64) -> impl Fn(u64,u64,u64,u64,u64,u64,(u32,u32),u64) -> u64 {
    move |a,b,c,d,e,f,p,z| s+a+b*2+c*3+d*4+e*5+f*6+p.0 as u64*11+p.1 as u64*17+z*19
}
#[inline(never)]
pub fn word_spill(s: u64) -> impl Fn(u64,u64,u64,u64,u64,u64,(u32,usize),u64) -> u64 {
    move |a,b,c,d,e,f,p,z| s+a+b*2+c*3+d*4+e*5+f*6+p.0 as u64*11+p.1 as u64*17+z*19
}
#[inline(never)]
pub fn mutable(s: u64) -> impl FnMut((u32,u32)) -> u64 {
    let mut state=s;
    move |p| { state += p.0 as u64*3+p.1 as u64*17; state }
}
#[inline(never)]
pub fn ignored() -> impl Fn((),(u32,u32),()) -> u64 {
    |_,p,_| p.0 as u64*3+p.1 as u64*17
}
#[inline(never)]
pub fn local(pair: (u32,u32), word: (u32,usize)) -> u64 {
    let f=|p:(u32,u32),w:(u32,usize)| p.0 as u64*3+p.1 as u64*17+w.0 as u64*23+w.1 as u64*29;
    f(pair,word)
}
"#;

pub(super) const CALLER: &str = r#"
use std::hint::black_box as bb;
unsafe extern "C" { fn write(fd: i32, bytes: *const u8, count: usize) -> isize; }
fn main() {
    let mut f=pair_lib::mutable(bb(37));
    let first=f(bb((17,31))); let second=f(bb((19,37)));
    let values = [
        pair_lib::pair(bb(37))(bb((0x12345678,0xfedcba98))),
        pair_lib::word(bb(37))(bb((0xfedcba98,0x123456789usize))),
        pair_lib::pair_spill(bb(37))(bb(1),bb(2),bb(3),bb(4),bb(5),bb(6),bb((0x12345678,0xfedcba98)),bb(31)),
        pair_lib::word_spill(bb(37))(bb(1),bb(2),bb(3),bb(4),bb(5),bb(6),bb((0xfedcba98,0x123456789usize)),bb(31)),
        first, second,
        pair_lib::ignored()((),bb((17,31)),()),
        pair_lib::local(bb((17,31)),bb((19,0x123456789usize))),
    ];
    // This independent C byte observer avoids adding Rust formatting machinery
    // to the ABI fixture. The source owns the live array for the whole write.
    let count=unsafe { write(1, values.as_ptr() as *const u8, 64) };
    if count != 64 { std::process::exit(1); }
}
"#;

pub(super) const EXPECTED: [u64; 8] = [
    73_606_195_109,
    95_901_847_558,
    76_049_554_957,
    130_108_876_654,
    615,
    1301,
    578,
    141_714_833_020,
];
