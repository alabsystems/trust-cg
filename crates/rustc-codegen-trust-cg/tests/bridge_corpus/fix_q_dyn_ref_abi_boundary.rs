// Corpus: a BORROWED TRAIT OBJECT (`&dyn Tr`) crossing a by-value ABI boundary.
//
// `&dyn Trait` is a fat pointer `{ data, vtable }` — the same two-eightbyte image
// as a `&[T]`'s `{ data, len }`, differing only in what lane 1 MEANS. rustc gives
// both `PassMode::Pair`. Before this lane, `fat_ptr_or_memory_aggregate_layout`
// recognised the slice and slice-tail-DST spellings but not the trait-object one,
// so a `&dyn` in return or by-value-parameter position fell through to
// `rust_ty_to_trust_ir_ty`, which has no mapping for a trait-object reference,
// and the function failed closed with `Ty::dyn …` (15 `library/core` roots).
//
// WHY A WRONG MODEL IS A WRONG NUMBER HERE, NOT A REFUSAL. Every row dispatches
// through TWO DIFFERENT impls whose methods return DIFFERENT values, so a vtable
// that is dropped, shared between the two objects, or swapped with the data lane
// prints the wrong number rather than merely crashing:
//   * `p` / `q` return the SAME reference back across the boundary and then call
//     two different methods on it — if lane 1 were lost, neither call could
//     resolve; if lane 1 were the data pointer, `f` would read the vtable as an
//     integer field.
//   * `k` SELECTS between two trait objects across a branch, so the two fat
//     pointers must stay paired lane-for-lane through a phi.
//   * `t` takes TWO `&dyn` parameters at once and calls a different method on
//     each — the case where confusing the two receivers' vtables is invisible to
//     a single-object test.
//
// Every value is returned from an `#[inline(never)]` function, so each crosses a
// real ABI boundary before it is read.
#![allow(dead_code)]

trait Tr {
    fn f(&self) -> i64;
    fn g(&self) -> i64;
}

struct A(i64);
struct B(i64);

impl Tr for A {
    fn f(&self) -> i64 {
        self.0 + 1000
    }
    fn g(&self) -> i64 {
        11
    }
}

impl Tr for B {
    fn f(&self) -> i64 {
        self.0 + 2000
    }
    fn g(&self) -> i64 {
        22
    }
}

#[inline(never)]
fn passthru<'a>(d: &'a dyn Tr) -> &'a dyn Tr {
    d
}

#[inline(never)]
fn pick<'a>(d: &'a dyn Tr, e: &'a dyn Tr, first: bool) -> &'a dyn Tr {
    if first { d } else { e }
}

#[inline(never)]
fn two(d: &dyn Tr, e: &dyn Tr) -> i64 {
    d.f() + e.g()
}

fn main() {
    let a = A(7);
    let b = B(9);
    let ra: &dyn Tr = &a;
    let rb: &dyn Tr = &b;

    let p1 = passthru(ra).f();
    let p2 = passthru(rb).f();
    println!("p {} {}", p1, p2); // 1007 2009

    let q1 = passthru(ra).g();
    let q2 = passthru(rb).g();
    println!("q {} {}", q1, q2); // 11 22

    let k1 = pick(ra, rb, true).f();
    let k2 = pick(ra, rb, false).f();
    println!("k {} {}", k1, k2); // 1007 2009

    let t1 = two(ra, rb);
    let t2 = two(rb, ra);
    println!("t {} {}", t1, t2); // 1029 2020
}
