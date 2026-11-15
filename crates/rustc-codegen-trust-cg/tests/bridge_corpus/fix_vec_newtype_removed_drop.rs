// CORPUS FIXTURE — a `Vec` compaction drops every element it removes when the
// element is a class-1 newtype that needs drop.
//
// WHAT IT PINS. Class-1 `Vec` admission keys on the scalar an element maps to,
// which sees through a single-field newtype, so `W(u32)` with a `Drop` impl is
// class 1. `retain`, `retain_mut`, `dedup_by` and the shrink of `resize_with`
// compacted the buffer without dropping the elements they removed, `dedup` used
// the bit-comparing helper, and `dedup_by_key` was synthesized: every removed
// `W` was leaked (a drop delta of 0 where std's is 2 to 4), at -O0..-O3.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM (every
// line's drop delta reads 0).

use std::hint::black_box as bb;
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};

static DROPS: AtomicU32 = AtomicU32::new(0);

#[derive(PartialEq)]
struct W(u32);

impl Drop for W {
    fn drop(&mut self) {
        DROPS.fetch_add(1, SeqCst);
    }
}

// [1, 1, 2, 4, 4, 7]
#[inline(never)]
fn six() -> Vec<W> {
    let mut v = Vec::new();
    v.push(W(bb(1)));
    v.push(W(bb(1)));
    v.push(W(bb(2)));
    v.push(W(bb(4)));
    v.push(W(bb(4)));
    v.push(W(bb(7)));
    v
}

#[inline(never)]
fn digest(v: &Vec<W>) -> u32 {
    let mut s = v.len() as u32;
    let mut i = 0;
    while i < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[i].0);
        i += 1;
    }
    s
}

#[inline(never)]
fn retain(v: &mut Vec<W>) {
    v.retain(|w| w.0 % 2 == 0);
}

#[inline(never)]
fn retain_mut(v: &mut Vec<W>) {
    v.retain_mut(|w| {
        w.0 += 1;
        w.0 % 2 == 0
    });
}

#[inline(never)]
fn dedup(v: &mut Vec<W>) {
    v.dedup();
}

#[inline(never)]
fn dedup_by(v: &mut Vec<W>) {
    v.dedup_by(|a, b| a.0 / 2 == b.0 / 2);
}

#[inline(never)]
fn dedup_by_key(v: &mut Vec<W>) {
    v.dedup_by_key(|w| w.0 / 3);
}

#[inline(never)]
fn shrink(v: &mut Vec<W>) {
    v.resize_with(2, || W(99));
}

#[inline(never)]
fn line(name: u32, during: u32, digest: u32) {
    println!("{name} {during} {digest}");
}

fn main() {
    {
        let mut v = six();
        let d0 = DROPS.load(SeqCst);
        retain(&mut v);
        line(1, DROPS.load(SeqCst) - d0, digest(&v));
    }
    {
        let mut v = six();
        let d0 = DROPS.load(SeqCst);
        retain_mut(&mut v);
        line(2, DROPS.load(SeqCst) - d0, digest(&v));
    }
    {
        let mut v = six();
        let d0 = DROPS.load(SeqCst);
        dedup(&mut v);
        line(3, DROPS.load(SeqCst) - d0, digest(&v));
    }
    {
        let mut v = six();
        let d0 = DROPS.load(SeqCst);
        dedup_by(&mut v);
        line(4, DROPS.load(SeqCst) - d0, digest(&v));
    }
    {
        let mut v = six();
        let d0 = DROPS.load(SeqCst);
        dedup_by_key(&mut v);
        line(5, DROPS.load(SeqCst) - d0, digest(&v));
    }
    {
        let mut v = six();
        let d0 = DROPS.load(SeqCst);
        shrink(&mut v);
        line(6, DROPS.load(SeqCst) - d0, digest(&v));
    }
    line(7, DROPS.load(SeqCst), 0);
}
