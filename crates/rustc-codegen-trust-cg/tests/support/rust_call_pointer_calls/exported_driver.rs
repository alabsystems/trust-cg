// LLVM caller of `exported.rs`, built by either backend.
#![feature(unboxed_closures)]
extern crate exported;
use std::hint::black_box as bb;

fn main() {
    let k = bb(41u64);
    let direct = exported::flag((bb(k) > 100, k)) + exported::flag((bb(k) < 100, k));
    let f = bb(exported::get_flag());
    let pointer = f((bb(k) > 100, k)) + f((bb(k) < 100, k));
    println!("v {direct} {pointer}");
}
