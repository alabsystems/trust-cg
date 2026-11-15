// Binary half: instantiates its own copies of the library's local-copy items
// (the fn-pointer `u64::from`, `<i128>::wrapping_mul`, and `<TA as Tr>::t`
// through a vtable it builds) and calls the library's.
extern crate fixture;
use fixture::*;
use std::hint::black_box as bb;

fn main() {
    let k = bb(41u64);
    let f: fn(u16) -> u64 = u64::from;
    let ta = TA(k + 1);
    let d: &dyn Tr = &ta;
    let h = bb(-0x1234_5678_9abc_def0_1122_3344_5566_7788i128);
    let x = h.wrapping_mul(5).wrapping_sub(0x22);
    println!("{} {}", widen(bb(41)), bb(f)(bb(43)));
    println!("{} {}", mk(k), use_dyn(d));
    println!("{} {}", wide(h), (x as u64) ^ ((x >> 64) as u64));
}
