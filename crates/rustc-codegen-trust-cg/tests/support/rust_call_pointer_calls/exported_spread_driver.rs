// Caller of `exported_spread.rs`: a direct call, a call from this crate's own
// generic and a call through the vtable this crate builds, each reaching the
// library's `<Spread as Fn<_>>::call` by symbol.
extern crate exported_spread;
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
    let s = exported_spread::Spread(bb(7));
    let direct = s(k, 2, 3, 4, 5, 6, bb("hello"));
    println!("v {direct} {} {}", call_it(&s, k), call_dyn(&s, k));
}
