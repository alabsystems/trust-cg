// CORPUS FIXTURE — a user `impl PartialEq<P>` / `PartialOrd<P>` /
// `FromIterator<Q>` for `Vec<u32>`, reached through core's provided `ne` / `lt`
// / `Iterator::collect`, runs the user's code.
//
// WHAT IT PINS. A provided trait method keeps core's DefId even when rustc
// selected a USER impl, so the crate test admitted `<Vec<u32> as
// PartialEq<P>>::ne`, `<Vec<u32> as PartialOrd<P>>::lt` and
// `collect::<Vec<u32>>` over `Q` items as alloc's Vec methods: `ne`/`lt` read
// the `&P` operand as a Vec header (an out-of-bounds read), and `collect`
// pushed the iterator's items instead of running the user's `from_iter`.
// Measured on 6b108b81d: every check below answered differently from LLVM at
// -O0/-O1 (exit 18), and the non-inlined generic `ne` at -O2/-O3 too (exit 7).
// A provided method is admitted only when the impl rustc selects is alloc's
// own, and `collect` only when the iterator's `Item` is the element type.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It compiles and DIVERGES from LLVM: the
// exit code carries one bit per wrong answer.

use std::cmp::Ordering;
use std::hint::black_box as bb;

pub struct P(pub u64, pub u64, pub u64);

impl PartialEq<P> for Vec<u32> {
    fn eq(&self, p: &P) -> bool {
        self.len() as u64 == p.0
    }
}

impl PartialOrd<P> for Vec<u32> {
    fn partial_cmp(&self, p: &P) -> Option<Ordering> {
        (self.len() as u64).partial_cmp(&p.0)
    }
}

pub struct Q(pub u32);

impl FromIterator<Q> for Vec<u32> {
    fn from_iter<I: IntoIterator<Item = Q>>(it: I) -> Self {
        let mut v = Vec::new();
        for q in it {
            v.push(q.0 + 100);
        }
        v
    }
}

#[inline(never)]
fn ne(v: &Vec<u32>, p: &P) -> bool {
    *v != *p
}

#[inline(never)]
fn lt(v: &Vec<u32>, p: &P) -> bool {
    *v < *p
}

#[inline(never)]
fn generic_ne<T: PartialEq<P>>(t: &T, p: &P) -> bool {
    *t != *p
}

#[inline(never)]
fn collect_q(n: u32) -> Vec<u32> {
    (0..n).map(|i| Q(i)).collect()
}

fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(bb(9));
    v.push(bb(8));
    let mut code = 0;
    if ne(&v, &P(bb(2), 0, 0)) {
        code |= 1;
    }
    if !lt(&v, &P(bb(5), 0, 0)) {
        code |= 2;
    }
    if generic_ne(&v, &P(bb(2), 0, 0)) {
        code |= 4;
    }
    let c = collect_q(bb(3));
    if c.len() != 3 || c[0] != 100 || c[2] != 102 {
        code |= 8;
    }
    std::process::exit(code + 3);
}
