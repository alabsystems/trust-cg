// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Always LLVM-compiled. `--list` names the one case (the shape the hunt probe
// harness drives); any other argument runs it. A Vec is printed only while its
// length is within its original length, so a corrupted header cannot make the
// LLVM-side print read past the allocation.
use std::hint::black_box as bb;

fn show(tag: &str, v: &[u32], max: usize) {
    if v.len() <= max {
        println!("{tag} {v:?}");
    } else {
        println!("{tag} len={}", v.len());
    }
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("--list") {
        println!("all");
        return;
    }
    for (lo, hi) in [(1, 3), (0, 5), (0, 2), (2, 2), (3, 5)] {
        let mut v = vec![1u32, 2, 3, 4, 5];
        klib::sink(bb(v.drain(lo..hi)));
        show(&format!("sink {lo}..{hi}"), &v, 5);
    }
    let mut v = vec![10u8, 20, 30, 40, 50];
    klib::sink_u8(bb(v.drain(1..3)));
    println!("sink_u8 {v:?}");
    let mut v = vec![10u64, 20, 30, 40, 50];
    klib::sink_u64(bb(v.drain(1..3)));
    println!("sink_u64 {v:?}");
    let mut v = vec!['a', 'b', 'c', 'd', 'e'];
    klib::sink_char(bb(v.drain(1..3)));
    println!("sink_char {v:?}");
    let mut v = vec![(1u32, 1u16), (2, 2), (3, 3), (4, 4), (5, 5)];
    klib::sink_pair(bb(v.drain(1..3)));
    println!("sink_pair {v:?}");
    let mut v: Vec<klib::Pt> = (1..=5).map(|i| klib::Pt(i, i * 10)).collect();
    klib::sink_pt(bb(v.drain(1..3)));
    let pts: Vec<(u32, u32)> = v.iter().map(|p| (p.0, p.1)).collect();
    println!("sink_pt {pts:?}");

    let mut v = vec![1u32, 2, 3, 4, 5];
    let s = klib::consume(bb(v.drain(1..3)));
    show(&format!("consume s={s}"), &v, 5);

    let mut v = vec![1u32, 2, 3, 4, 5];
    drop(klib::pass(bb(v.drain(1..3))));
    show("pass drop", &v, 5);
    let mut v = vec![1u32, 2, 3, 4, 5];
    let got: Vec<u32> = klib::pass(bb(v.drain(1..4))).collect();
    show(&format!("pass collect {got:?}"), &v, 5);
    let mut v = vec![1u32, 2, 3, 4, 5];
    drop(klib::pass_move(bb(v.drain(1..3))));
    show("pass_move drop", &v, 5);

    let mut v = vec![1u32, 2, 3, 4, 5];
    let r = klib::opt_param(bb(Some(v.drain(1..3))));
    show(&format!("opt_param r={r}"), &v, 5);
    let mut v = vec![1u32, 2, 3, 4, 5];
    let b = klib::struct_param(bb(klib::W(v.drain(1..3), 7)));
    show(&format!("struct_param b={b}"), &v, 5);
}
