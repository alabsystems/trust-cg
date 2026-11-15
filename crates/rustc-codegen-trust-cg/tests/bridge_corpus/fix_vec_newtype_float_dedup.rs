// CORPUS FIXTURE — `Vec::dedup` of a float newtype with a derived `PartialEq`
// compares with IEEE `==`.
//
// WHAT IT PINS. `F(f64)` maps to the scalar `F64`, so `Vec<F>::dedup` reaches
// the scalar dedup helper, which chose its comparison from `element_ty`
// (an ADT, so not a float) and compared bits: `[+0.0, -0.0]` kept both and
// `[NaN, NaN]` (same bits) kept one, where the derived `==` (IEEE) keeps one and
// two. At -O0/-O1 (at -O2/-O3 `dedup` is inlined into `dedup_by`).
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM at
// -O0/-O1 (`2 1` for `1 2`).

use std::hint::black_box as bb;

#[derive(PartialEq, Clone, Copy)]
struct F(f64);

#[derive(PartialEq, Clone, Copy)]
struct G(F);

#[inline(never)]
fn dedup_f(v: &mut Vec<F>) -> u32 {
    v.dedup();
    v.len() as u32
}

#[inline(never)]
fn dedup_g(v: &mut Vec<G>) -> u32 {
    v.dedup();
    v.len() as u32
}

#[inline(never)]
fn line(a: u32, b: u32) {
    println!("{a} {b}");
}

fn main() {
    let mut zeros = Vec::new();
    zeros.push(F(bb(0.0)));
    zeros.push(F(bb(-0.0)));
    let mut nans = Vec::new();
    nans.push(F(bb(f64::NAN)));
    nans.push(F(bb(f64::NAN)));
    let a = dedup_f(&mut zeros);
    let b = dedup_f(&mut nans);
    line(a, b);
    let mut zeros = Vec::new();
    zeros.push(G(F(bb(0.0))));
    zeros.push(G(F(bb(-0.0))));
    let mut nans = Vec::new();
    nans.push(G(F(bb(f64::NAN))));
    nans.push(G(F(bb(f64::NAN))));
    let a = dedup_g(&mut zeros);
    let b = dedup_g(&mut nans);
    line(a, b);
}
