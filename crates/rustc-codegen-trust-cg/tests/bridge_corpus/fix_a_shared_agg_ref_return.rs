// (a) A shared `&S` RETURNED from a callee that received `&s` of a scalarized
// struct: an interior-mutability store through the returned reference must
// reach `s`. The places lane declined every `&Aggregate` return, so the callee
// returned the address of the materialized call TEMP (lane: a=1 b=1, LLVM: 50 60).
// Fixed: `compute_memory_backed_locals` (4i)/(4j) memory-back a `!Freeze` referent
// and any referent whose `&` reaches a reference-returning callee; the residual
// shape is refused in `direct_scalar_ref_select_return`.
#![allow(dead_code)]
use std::cell::Cell;
struct S { c: Cell<u32>, k: u32 }
#[inline(never)] fn view(s: &S) -> &S { s }
#[inline(never)] fn read_k(s: &S) -> u32 { s.k }
#[inline(never)] fn pick<'a>(c: bool, a: &'a S, b: &'a S) -> &'a S { if c { a } else { b } }
fn main() {
    let s = S { c: Cell::new(1), k: 10 };
    s.c.set(50);
    let a = s.c.get();
    view(&s).c.set(60);
    let b = s.c.get();
    let k = read_k(view(&s));
    let t = S { c: Cell::new(7), k: 20 };
    pick(false, &s, &t).c.set(300);
    let v3 = t.c.get();
    println!("a={} b={} k={} v3={}", a, b, k, v3);
}
