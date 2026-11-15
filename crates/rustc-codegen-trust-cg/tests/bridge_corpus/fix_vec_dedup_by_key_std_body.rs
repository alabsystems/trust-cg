// CORPUS FIXTURE — `Vec::dedup_by_key` is std's `dedup_by(|a, b| key(a) ==
// key(b))`: two key calls per comparison, the key type's own `PartialEq`, and
// every key dropped.
//
// WHAT IT PINS. The bridge synthesized `dedup_by_key` as a loop that called the
// key once per element, cached the last kept key, compared keys as zero-extended
// bits, and never dropped a key. Each line below diverged at -O0..-O3: the call
// count (3 for 4), an element-mutating key (`[1]` for `[2]`), a key newtype with a
// hand-written `eq` (3 elements kept for 2), and a key with `Drop` (0 drops for 4).
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM.

use std::hint::black_box as bb;
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};

static KEY_DROPS: AtomicU32 = AtomicU32::new(0);

// Equal when equal mod 10 (a lawful equivalence).
struct Mod10(u64);

impl PartialEq for Mod10 {
    fn eq(&self, other: &Mod10) -> bool {
        self.0 % 10 == other.0 % 10
    }
}

#[derive(PartialEq)]
struct D(u64);

impl Drop for D {
    fn drop(&mut self) {
        KEY_DROPS.fetch_add(1, SeqCst);
    }
}

#[inline(never)]
fn digest(v: &Vec<u64>) -> u64 {
    let mut s = v.len() as u64;
    let mut i = 0;
    while i < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[i]);
        i += 1;
    }
    s
}

#[inline(never)]
fn count_calls(v: &mut Vec<u64>) -> u64 {
    let mut n = 0;
    v.dedup_by_key(|x| {
        n += 1;
        *x
    });
    n
}

#[inline(never)]
fn bump(v: &mut Vec<u64>) {
    v.dedup_by_key(|x| {
        *x += 1;
        *x / 4
    });
}

#[inline(never)]
fn mod10(v: &mut Vec<u64>) {
    v.dedup_by_key(|x| Mod10(*x));
}

#[inline(never)]
fn drop_key(v: &mut Vec<u64>) {
    v.dedup_by_key(|x| D(*x / 2));
}

#[inline(never)]
fn line(a: u64, b: u64) {
    println!("{a} {b}");
}

#[inline(never)]
fn three(a: u64, b: u64, c: u64) -> Vec<u64> {
    let mut v = Vec::new();
    v.push(bb(a));
    v.push(bb(b));
    v.push(bb(c));
    v
}

fn main() {
    let mut v = three(1, 2, 3);
    let n = count_calls(&mut v);
    line(n, digest(&v));
    let mut v = three(0, 1, 2);
    bump(&mut v);
    line(0, digest(&v));
    let mut v = three(1, 11, 2);
    mod10(&mut v);
    line(0, digest(&v));
    let mut v = three(4, 5, 8);
    drop_key(&mut v);
    line(u64::from(KEY_DROPS.load(SeqCst)), digest(&v));
}
