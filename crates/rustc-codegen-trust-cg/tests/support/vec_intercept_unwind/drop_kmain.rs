//! Driver of `drop_klib.rs` (always LLVM-built): arms one element's drop to
//! panic, runs one case under `catch_unwind`, prints the Vec and every drop
//! so far, then drops the Vec and prints the drops again. An element dropped
//! twice, or left in the Vec after its drop, shows in the logs.

use std::fmt::Debug;
use std::hint::black_box;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::Ordering::SeqCst;

const CASES: &[&str] = &[
    "retain_first_removed_drop_panics",
    "retain_second_removed_drop_panics",
    "retain_last_removed_drop_panics",
    "retain_after_kept_drop_panics",
    "retain_pred_panics",
    "retain_mut_drop_panics",
    "retain_local_drop_panics",
    "retain_control",
    "dedup_by_first_dup_drop_panics",
    "dedup_by_later_dup_drop_panics",
    "dedup_by_cmp_panics",
    "dedup_by_control",
    "dedup_by_key_later_dup_drop_panics",
    "dedup_by_key_panics",
    "dedup_derived_dup_drop_panics",
    "dedup_user_eq_dup_drop_panics",
    "dedup_user_eq_panics",
];

fn log() -> Vec<u32> {
    let n = klib::N.load(SeqCst).min(64);
    (0..n).map(|i| klib::LOG[i].load(SeqCst)).collect()
}

fn run<T: Debug>(xs: &[u32], arm: u32, mk: fn(u32) -> T, f: impl FnOnce(&mut Vec<T>)) {
    let mut v: Vec<T> = black_box(xs.iter().map(|&x| mk(x)).collect());
    klib::N.store(0, SeqCst);
    klib::ARM.store(arm, SeqCst);
    let panicked = catch_unwind(AssertUnwindSafe(|| f(&mut v))).is_err();
    println!("panicked={panicked} len={} v={v:?}", v.len());
    println!("during={:?}", log());
    klib::ARM.store(0, SeqCst);
    drop(v);
    println!("after_drop={:?}", log());
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
    let w = klib::W;
    let odd = [11u32, 21, 32, 41, 52, 63];
    let runs = [11u32, 12, 21, 22, 23, 31];
    match case.as_str() {
        "retain_first_removed_drop_panics" => run(&odd, 11, w, klib::retain_even),
        "retain_second_removed_drop_panics" => run(&odd, 21, w, klib::retain_even),
        "retain_last_removed_drop_panics" => run(&odd, 63, w, klib::retain_even),
        "retain_after_kept_drop_panics" => run(&[12, 31, 42, 51, 62], 31, w, klib::retain_even),
        "retain_pred_panics" => run(&[11, 22, 7, 5, 33], 0, w, klib::retain_pred_panics),
        // `retain_mut` adds 100 first: 111, 121, 141 and 163 are removed.
        "retain_mut_drop_panics" => run(&odd, 141, w, klib::retain_mut_even),
        "retain_local_drop_panics" => run(&odd, 41, w, klib::retain_with_local),
        "retain_control" => run(&odd, 0, w, klib::retain_even),
        "dedup_by_first_dup_drop_panics" => run(&runs, 12, w, klib::dedup_by_tens),
        "dedup_by_later_dup_drop_panics" => run(&runs, 22, w, klib::dedup_by_tens),
        "dedup_by_cmp_panics" => run(&[51, 52, 59, 61], 0, w, klib::dedup_by_cmp_panics),
        "dedup_by_control" => run(&runs, 0, w, klib::dedup_by_tens),
        "dedup_by_key_later_dup_drop_panics" => run(&runs, 22, w, klib::dedup_by_key_tens),
        "dedup_by_key_panics" => run(&[51, 52, 59, 61], 0, w, klib::dedup_by_key_panics),
        "dedup_derived_dup_drop_panics" => {
            run(&[1, 1, 2, 2, 2, 3], 2, klib::D, klib::dedup_derived)
        }
        "dedup_user_eq_dup_drop_panics" => run(&runs, 22, klib::E, klib::dedup_user_eq),
        "dedup_user_eq_panics" => run(&[51, 52, 59, 61], 0, klib::E, klib::dedup_user_eq),
        other => panic!("unknown case {other:?}"),
    }
}
