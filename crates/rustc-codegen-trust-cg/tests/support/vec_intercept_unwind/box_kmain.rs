//! Driver of `box_klib.rs` (always LLVM-built): runs one case under
//! `catch_unwind`, prints the Vec, then drops it (a box owned by two slots is
//! freed twice there) and reports that the drop finished.

use std::hint::black_box;
use std::panic::{AssertUnwindSafe, catch_unwind};

const CASES: &[&str] = &["retain_box", "dedup_by_box"];

fn run(values: &[u32], f: fn(&mut Vec<Box<u32>>)) {
    let mut v: Vec<Box<u32>> = black_box(values.iter().map(|&x| Box::new(x)).collect());
    let panicked = catch_unwind(AssertUnwindSafe(|| f(&mut v))).is_err();
    let distinct = v
        .iter()
        .enumerate()
        .all(|(i, a)| v[..i].iter().all(|b| !std::ptr::eq(&**a, &**b)));
    println!(
        "panicked={panicked} len={} v={v:?} distinct_boxes={distinct}",
        v.len()
    );
    drop(v);
    println!("dropped");
}

fn main() {
    let case = std::env::args().nth(1).unwrap_or_default();
    if case == "--list" {
        for case in CASES {
            println!("{case}");
        }
        return;
    }
    std::panic::set_hook(Box::new(|_| {}));
    match case.as_str() {
        "retain_box" => run(&[3, 1, 4, 1, 5, 9], klib::retain_box),
        "dedup_by_box" => run(&[3, 1, 4, 1, 5, 9], klib::dedup_by_box),
        other => panic!("unknown case {other:?}"),
    }
}
