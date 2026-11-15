// Binary halves: each call expression becomes the body of `main` in its own
// driver (`rust_call_pointer_calls.rs`), so each shape is pinned on its own:
// the bridge must compile every one and print the value LLVM's program does.
#![feature(unboxed_closures)]
#![allow(improper_ctypes)]
extern crate callees;
use callees::*;
use std::hint::black_box as bb;

mod foreign {
    unsafe extern "rust-call" {
        #[link_name = "tcg_rust_call_foreign"]
        pub fn rcf(a: (u64, [f32; 4], u8)) -> u64;
    }
}

fn main() {
    let k = bb(41u64);
    let v = CALL;
    println!("v {v}");
}
