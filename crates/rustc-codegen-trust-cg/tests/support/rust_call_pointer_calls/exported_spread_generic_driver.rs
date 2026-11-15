// LLVM caller of `exported_spread_generic.rs`: the library's own call, then a
// direct call, a call from this crate's own generic and a call through the
// vtable this crate builds, of `<Spread<u64> as Fn<_>>::call`.
extern crate exported_spread_generic;
use exported_spread_generic::{Spread, use_here};
use std::hint::black_box as bb;

type Dyn = dyn Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64;

#[inline(never)]
fn call_it<F: Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64>(f: &F, k: u64) -> u64 {
    f(k, 2, 3, 4, 5, 6, bb("hello"))
}

#[inline(never)]
fn call_dyn(f: &Dyn, k: u64) -> u64 {
    f(k, 2, 3, 4, 5, 6, bb("hello"))
}

fn main() {
    let k = bb(41u64);
    let s = Spread(bb(7u64));
    let direct = s(k, 2, 3, 4, 5, 6, bb("hello"));
    let (here, generic) = (use_here(k), call_it(&s, k));
    println!("v {here} {direct} {generic} {}", call_dyn(&s, k));
}
