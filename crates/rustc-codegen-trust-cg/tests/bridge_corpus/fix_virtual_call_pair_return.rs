// A VIRTUAL call returning a TWO-REGISTER by-value aggregate into a
// memory-backed destination: `(i64, i64)` and `&'static str`.
//
// Both are `BackendRepr::ScalarPair`, so rustc's `FnAbi` places them
// `PassMode::Pair` — two registers of the scalars' OWN classes, NOT one lane
// tuple. The bridge must read that placement off rustc's `FnAbi` for the trait
// method (a vtable slot has no symbol to key the direct lane's
// `scalar_pair_returns` map on) and store each returned register at rustc's own
// lane offset. A dropped lane, a swapped lane, or a whole-slot relocation of a
// register pair all show up as a wrong number or a truncated string here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

pub trait Split {
    fn pair(&self, k: i64) -> (i64, i64);
    fn name(&self, k: i64) -> &'static str;
}

pub struct Lo(i64);
pub struct Hi(i64);

impl Split for Lo {
    fn pair(&self, k: i64) -> (i64, i64) {
        (self.0 + k, self.0 - k)
    }
    fn name(&self, k: i64) -> &'static str {
        if k > 0 { "lo-positive" } else { "lo" }
    }
}

impl Split for Hi {
    fn pair(&self, k: i64) -> (i64, i64) {
        (self.0 * k, self.0 ^ k)
    }
    fn name(&self, k: i64) -> &'static str {
        if k > 0 { "hi-positive-and-then-some" } else { "hi" }
    }
}

// The destination of each virtual call is a whole local that is read back
// FIELD-WISE afterwards, which forces a real memory slot.
#[inline(never)]
fn probe(s: &dyn Split, k: i64) -> (i64, i64, usize, u8) {
    let p = s.pair(k);
    let n = s.name(k);
    // Every field / byte of both returns is observed.
    let mut sum = 0u8;
    for b in n.as_bytes() {
        sum = sum.wrapping_add(*b);
    }
    (p.0, p.1, n.len(), sum)
}

// A slice of `&dyn Split` would be the natural driver, but `slice::Iter<&dyn T>`
// stops at an unrelated pre-existing gate (`Ty::dyn ...`) that would mask the one
// this fixture exercises. Two explicit receivers exercise the same call sites.
#[inline(never)]
fn accumulate(p: &dyn Split, q: &dyn Split) -> (i64, i64, usize, u8) {
    let mut a = 0i64;
    let mut b = 0i64;
    let mut l = 0usize;
    let mut s = 0u8;
    let mut i = 0i64;
    while i < 4 {
        let it: &dyn Split = if i % 2 == 0 { p } else { q };
        let (x, y, n, cs) = probe(it, i - 1);
        a = a.wrapping_add(x);
        b = b.wrapping_add(y);
        l += n;
        s = s.wrapping_add(cs);
        i += 1;
    }
    (a, b, l, s)
}

// A `&'static str` return observed WITHOUT printing it: its length and a byte
// checksum. Printing a runtime-length `&str` stops at an unrelated pre-existing
// gate (`[TCG-FMT-RTSTR]`), which would mask the one this fixture exercises —
// and a checksum observes every byte the two lanes must have carried, which
// printing the string would not do any better.
#[inline(never)]
fn digest(s: &'static str) -> (usize, u32) {
    let mut cs = 0u32;
    for b in s.as_bytes() {
        cs = cs.wrapping_mul(31).wrapping_add(*b as u32);
    }
    (s.len(), cs)
}

fn main() {
    let lo = Lo(7);
    let hi = Hi(-3);
    let (a, b, l, s) = accumulate(&lo, &hi);
    println!("{a}");
    println!("{b}");
    println!("{l}");
    println!("{s}");

    // The same calls with their results read back through a pattern binding and
    // through the tuple's own fields, so BOTH lanes are observed separately.
    // (Each value goes through a plain local before `println!`: a field read in
    // the argument position stops at an unrelated pre-existing gate — "format!
    // arg reference does not trace to a value local".)
    let d: &dyn Split = &hi;
    let (x, y) = d.pair(11);
    println!("{x}");
    println!("{y}");
    let t = d.pair(-11);
    let t0 = t.0;
    let t1 = t.1;
    println!("{t0}");
    println!("{t1}");

    // Both fat-pointer lanes of a virtual `-> &'static str` return: a dropped
    // length lane gives the wrong count, a dropped data lane the wrong checksum.
    let (n0, c0) = digest(d.name(1));
    let (n1, c1) = digest(d.name(-1));
    println!("{n0}");
    println!("{c0}");
    println!("{n1}");
    println!("{c1}");
}
