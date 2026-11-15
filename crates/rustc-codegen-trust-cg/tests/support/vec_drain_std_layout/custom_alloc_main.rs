// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Always LLVM-compiled. `--list` names the one case (the shape the hunt probe
// harness drives); any other argument runs it.
#![feature(allocator_api)]
use std::hint::black_box as bb;

fn five() -> Vec<u32, klib::Fwd> {
    let mut v = Vec::new_in(klib::Fwd);
    v.extend_from_slice(&[1, 2, 3, 4, 5]);
    v
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("--list") {
        println!("all");
        return;
    }
    let mut v = five();
    drop(klib::make(bb(&mut v), bb(2)));
    println!("make drop {v:?}");
    let mut v = five();
    let got: Vec<u32> = klib::make(bb(&mut v), bb(1)).collect();
    println!("make collect {got:?} {v:?}");
    let mut v = five();
    klib::sink(bb(v.drain(1..3)));
    println!("sink 1..3 {v:?}");
    let mut v = five();
    let s = klib::sum_from(bb(&mut v), bb(2));
    println!("sum_from s={s} {v:?}");
}
