// (j) A shared borrow of a scalarized `Cell`-bearing struct passed to a callee
// that mutates through interior mutability: the borrow was materialized into a
// temp with no reload, so the write was lost (`a=1 b=1 c=1` for `100 100 7`).
// Fixed: `compute_memory_backed_locals` (4i) memory-backs an address-taken
// `!Freeze` local; a scalarized `!Freeze` referent that cannot be memory-backed
// is refused at the call-arg sites (`[TCG-INTERIOR-MUT-SNAPSHOT]`).
#![allow(dead_code)]
use std::cell::Cell;
struct S { c: Cell<u32>, k: u32 }
#[inline(never)] fn set(s: &S, v: u32) { s.c.set(v); }
#[inline(never)] fn get(s: &S) -> u32 { s.c.get() }
#[inline(never)] fn bump_scalar(c: &Cell<u8>) { c.set(c.get() + 1); }
fn main() {
    let s = S { c: Cell::new(1), k: 10 };
    set(&s, 100);
    let a = s.c.get();
    let b = get(&s);
    s.c.set(7);
    let c = get(&s);
    let sc = Cell::new(40u8);
    bump_scalar(&sc);
    bump_scalar(&sc);
    let scv = sc.get();
    let k = s.k;
    println!("a={} b={} c={} k={} sc={}", a, b, c, k, scv);
}
