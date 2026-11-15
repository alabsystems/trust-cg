// CORPUS FIXTURE — an array whose element is a `Vec<T>` / `String` holds each
// element as rustc's whole 24-byte `{cap, ptr, len}` image.
//
// WHAT IT PINS. A default-`Global` `Vec`/`String` LOCAL is bound to the address
// of its own 24-byte slot, so its trust-ir type is a one-word `Ptr` carrier, and
// `memory_scalar_leaf_ty` answers that carrier for the header type. A
// memory-backed `[Vec<i64>; N]` was therefore lowered by the SCALAR-element
// array arms: `[x, y]` stored ONE word per 24-byte element -- the source local's
// slot ADDRESS -- leaving `{&slot, <stale>, <stale>}`, and `[const { Vec::new() };
// N]` refused. Every later `a[i].len()` / `a[i][j]` / `a.iter()` read garbage:
// SIGSEGV at -O0..-O3 for a `[Vec<i64>; 2]` literal, a wrong digest then SIGSEGV
// for a `[String; 3]` literal. The ragged-rows section is the `Vec<Vec<u32>>`
// whose `g[0].len()` read 0 on the v52 base (before the whole-header deref
// store), so `if j < g[0].len() { g[i][j] } else { 7 }` answered 7.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM (a
// signal or wrong digest) -- a hard failure of
// `collection_header_element_image_differential`.

use std::hint::black_box as bb;

#[inline(never)]
fn digest_v(v: &Vec<i64>) -> u64 {
    let mut s = v.len() as u64 * 1000 + v.capacity().min(999) as u64;
    let mut j = 0;
    while j < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[j] as u64);
        j += 1;
    }
    s
}

#[inline(never)]
fn digest_s(v: &String) -> u64 {
    let b = v.as_bytes();
    let mut s = b.len() as u64;
    let mut j = 0;
    while j < b.len() {
        s = s.wrapping_mul(31).wrapping_add(b[j] as u64);
        j += 1;
    }
    s
}

#[inline(never)]
fn out(x: u64) {
    println!("{x}");
}

// `[x, y]` of two pushed `Vec<i64>` locals, read back by index. LLVM: 33050909.
#[inline(never)]
fn array_literal_of_vec_locals() -> u64 {
    let mut x = Vec::new();
    x.push(bb(1i64));
    let mut y = Vec::new();
    y.push(bb(2i64));
    y.push(bb(3));
    let a = [x, y];
    digest_v(&a[0]) * 1000 + digest_v(&a[1])
}

// The same array walked through `a.iter()` (a slice of 24-byte elements).
// LLVM: 2890784.
#[inline(never)]
fn array_iter() -> u64 {
    let mut x = Vec::new();
    x.push(bb(1i64));
    let mut y = Vec::new();
    y.push(bb(2i64));
    y.push(bb(3));
    let a = [x, y];
    let mut s = 0u64;
    for v in a.iter() {
        s = s * 31 + digest_v(v);
    }
    s
}

// A `[String; 3]` literal of a `String::from`, a `format!` and a `String::new`.
// LLVM: 5032043000 (digests 5027, 5043, 0).
#[inline(never)]
fn string_array() -> u64 {
    let a: [String; 3] = [String::from("ab"), format!("c{}", bb(4)), String::new()];
    digest_s(&a[0]) * 1_000_000 + digest_s(&a[1]) * 1000 + digest_s(&a[2])
}

#[inline(never)]
fn make(n: i64) -> Vec<i64> {
    let mut v = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(i * n);
        i += 1;
    }
    v
}

// Elements that are CALL RESULTS (returned through the hidden return buffer).
#[inline(never)]
fn array_of_call_results() -> u64 {
    let a = [make(bb(3)), make(bb(5)), make(bb(0))];
    digest_v(&a[0]) * 7 + digest_v(&a[1]) * 3 + digest_v(&a[2])
}

#[inline(never)]
fn rq_row0_len(g: &[Vec<u32>]) -> usize {
    g[0].len()
}

#[inline(never)]
fn rq_2d_guard_row0(g: &[Vec<u32>], i: usize, j: usize) -> u32 {
    if j < g[0].len() { g[i][j] } else { 7 }
}

// Ragged `Vec<Vec<u32>>` rows of length 8 and 4. LLVM: 8, 13, 7.
#[inline(never)]
fn ragged_rows() -> u64 {
    let mut g: Vec<Vec<u32>> = Vec::new();
    g.push(vec![1, 2, 3, 4, 5, 6, 7, 8]);
    g.push(vec![11, 12, 13, 14]);
    let g = bb(g);
    let len0 = rq_row0_len(bb(&g)) as u64;
    let inb = rq_2d_guard_row0(bb(&g), bb(1), bb(2)) as u64;
    let inb0 = rq_2d_guard_row0(bb(&g), bb(0), bb(6)) as u64;
    len0 * 1_000_000 + inb * 1000 + inb0
}

fn main() {
    out(array_literal_of_vec_locals());
    out(array_iter());
    out(string_array());
    out(array_of_call_results());
    out(ragged_rows());
}
