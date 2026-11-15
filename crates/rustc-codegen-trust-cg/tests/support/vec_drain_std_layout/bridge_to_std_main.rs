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
    let mut v = vec![1u32, 2, 3, 4, 5];
    drop(klib::make(bb(&mut v), bb(1)));
    show("make drop", &v, 5);
    let mut v = vec![1u32, 2, 3, 4, 5];
    let got: Vec<u32> = klib::make(bb(&mut v), bb(2)).collect();
    show(&format!("make collect {got:?}"), &v, 5);
    let mut v = vec![1u32, 2, 3, 4, 5];
    let mut d = klib::make(bb(&mut v), bb(1));
    let first = d.next();
    let rest = d.len();
    drop(d);
    show(&format!("make partial {first:?} rest={rest}"), &v, 5);
    let mut v = vec![1u32, 2, 3, 4, 5];
    std::mem::forget(klib::make(bb(&mut v), bb(3)));
    v.push(9);
    show("make forget", &v, 6);
    let mut v = vec![1u32, 2, 3, 4, 5];
    drop(klib::make(bb(&mut v), bb(5)));
    show("make empty", &v, 5);
    let mut v = vec![1u32, 2, 3, 4, 5];
    drop(klib::make_all(bb(&mut v)));
    show("make_all drop", &v, 5);

    let mut v = vec![10u8, 20, 30, 40, 50];
    let got: Vec<u8> = klib::make_u8(bb(&mut v), bb(2)).collect();
    println!("make_u8 {got:?} {v:?}");
    let mut v = vec![10u64, 20, 30, 40, 50];
    drop(klib::make_u64(bb(&mut v), bb(1)));
    println!("make_u64 {v:?}");
    let mut v = vec!['a', 'b', 'c', 'd', 'e'];
    let got: String = klib::make_char(bb(&mut v), bb(3)).collect();
    println!("make_char {got} {v:?}");
    let mut v = vec![(1u32, 1u16), (2, 2), (3, 3), (4, 4), (5, 5)];
    drop(klib::make_pair(bb(&mut v), bb(2)));
    println!("make_pair {v:?}");
    let mut v: Vec<klib::Pt> = (1..=5).map(|i| klib::Pt(i, i * 10)).collect();
    let got: Vec<(u32, u32)> = klib::make_pt(bb(&mut v), bb(3))
        .map(|p| (p.0, p.1))
        .collect();
    let pts: Vec<(u32, u32)> = v.iter().map(|p| (p.0, p.1)).collect();
    println!("make_pt {got:?} {pts:?}");

    let mut v = vec![1u32, 2, 3, 4, 5];
    let s: u32 = klib::ret_option(bb(&mut v), bb(2))
        .map(|d| d.sum())
        .unwrap_or(0);
    show(&format!("ret_option s={s}"), &v, 5);
    let mut v = vec![1u32, 2, 3, 4, 5];
    let (d, b) = klib::ret_tuple(bb(&mut v), bb(1));
    drop(d);
    show(&format!("ret_tuple b={b}"), &v, 5);

    let mut v = vec![7u32, 8, 9];
    klib::leak_len(bb(&mut v), bb(1));
    v.push(100);
    show("leak_len", &v, 4);
    let mut v = vec![7u32, 8, 9];
    klib::leak_tuple(bb(&mut v));
    show("leak_tuple", &v, 3);
    let mut v = vec![klib::Tok(1), klib::Tok(2), klib::Tok(3)];
    let t = klib::dup_tok(bb(&mut v));
    let held: Vec<u32> = v.iter().map(|x| x.0).collect();
    show(&format!("dup_tok taken={:?}", t.map(|x| x.0)), &held, 3);

    let mut v = vec![1u32, 2, 3, 4, 5];
    let s = klib::sum_from(bb(&mut v), bb(2));
    show(&format!("sum_from s={s}"), &v, 5);
}
