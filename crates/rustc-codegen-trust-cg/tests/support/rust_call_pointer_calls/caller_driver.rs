// LLVM control for `caller.rs`: the pointers are LLVM's `callees` items.
extern crate callees;
extern crate caller;
use std::hint::black_box as bb;

fn main() {
    let k = bb(41u64);
    println!(
        "v {} {}",
        caller::call_repro(bb(callees::get_repro()), k),
        caller::call_flag(bb(callees::get_flag()), k)
    );
}
