// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The callee crate of `intercept_panic_replay_differential`, compiled by each
//! backend. Every function fails through a std entry the bridge intercepts, or
//! panics in a frame that cannot unwind. The driver (always LLVM) installs a
//! hook that prints the payload and the full location.
#![allow(improper_ctypes_definitions)]

#[derive(Clone, Copy, Debug)]
pub struct Pair {
    pub a: u32,
    pub b: u64,
}

// `Vec` methods whose std body tests the index and fails through its own nested
// `assert_failed`: not `#[track_caller]` for `swap_remove`, which reports a
// location inside `alloc`; the others report this crate's call.
#[inline(never)]
pub fn swap_remove_u32(v: &mut Vec<u32>, i: usize) -> u32 {
    v.swap_remove(i)
}
#[inline(never)]
pub fn swap_remove_pair(v: &mut Vec<Pair>, i: usize) -> Pair {
    v.swap_remove(i)
}
#[inline(never)]
pub fn remove_u32(v: &mut Vec<u32>, i: usize) -> u32 {
    v.remove(i)
}
#[inline(never)]
pub fn insert_u32(v: &mut Vec<u32>, i: usize) {
    v.insert(i, 9)
}
#[inline(never)]
pub fn split_off_len(v: &mut Vec<u32>, at: usize) -> usize {
    v.split_off(at).len()
}
#[inline(never)]
pub fn insert_mut_u32(v: &mut Vec<u32>, i: usize) -> u32 {
    *v.insert_mut(i, 5)
}

// `assert!(mid <= self.len())` inside `core`.
#[inline(never)]
pub fn rotate_left_u32(v: &mut Vec<u32>, k: usize) {
    v.rotate_left(k)
}
#[inline(never)]
pub fn rotate_right_u8(v: &mut [u8], k: usize) {
    v.rotate_right(k)
}

// `slice::range` -> `into_slice_range` -> `slice_index_fail`, located inside
// `core::slice::index`.
#[inline(never)]
pub fn drain_from(v: &mut Vec<u32>, a: usize) {
    v.drain(a..);
}
#[inline(never)]
pub fn extend_within(v: &mut Vec<u32>, a: usize, b: usize) {
    v.extend_from_within(a..b)
}

// The `#[rustc_inherit_overflow_checks]` closures of core's integer `Sum` /
// `Product` (this crate is built with overflow checks on).
#[inline(never)]
pub fn sum_u8(v: &[u8]) -> u8 {
    v.iter().sum()
}
#[inline(never)]
pub fn product_u16(v: &[u16]) -> u16 {
    v.iter().product()
}

// `#[track_caller]` entries: this crate's call is the location, std formats the
// message.
#[inline(never)]
pub fn slice_swap(v: &mut [u32], i: usize, j: usize) {
    v.swap(i, j)
}
#[inline(never)]
pub fn vec_range_to(v: &Vec<u32>, i: usize) -> usize {
    v[..i].len()
}
#[inline(never)]
pub fn vec_range_full(v: &Vec<u32>) -> usize {
    v[..].len()
}
#[inline(never)]
pub fn vec_range_mut(v: &mut Vec<u32>, i: usize, j: usize) -> usize {
    let s = &mut v[i..j];
    s.len()
}
#[inline(never)]
pub fn array_range(i: usize, j: usize) -> usize {
    let a = [1u32, 2, 3, 4];
    a[i..j].len()
}
#[inline(never)]
pub fn array_range_mut(i: usize, j: usize) -> usize {
    let mut a = [1u32, 2, 3, 4];
    let s = &mut a[i..j];
    s.len()
}
#[inline(never)]
pub fn str_range(s: &str, i: usize, j: usize) -> usize {
    s[i..j].len()
}
#[inline(never)]
pub fn str_range_to(s: &str, i: usize) -> usize {
    s[..i].len()
}
#[inline(never)]
pub fn split_at_len(v: &[u32], i: usize) -> usize {
    v.split_at(i).0.len()
}
// `str::split_at` / `split_at_mut` are not `#[track_caller]`: both failures
// (`mid > len`, a `mid` inside a char) report the `slice_error_fail` call
// inside `core`.
#[inline(never)]
pub fn str_split_at(s: &str, i: usize) -> usize {
    s.split_at(i).0.len()
}
#[inline(never)]
pub fn str_split_at_mut(s: &mut str, i: usize) -> usize {
    s.split_at_mut(i).1.len()
}
// The bridge lowers a stride iterator's `next` from its own cursor, and its
// `len` only where rustc's MIR inliner folded the constructor away (-O2/-O3);
// it refuses each form at the other levels, so the test selects `next` with
// `--cfg stride_next` at -O0/-O1. Either form constructs the iterator first.
#[cfg(stride_next)]
#[inline(never)]
pub fn windows_len(v: &[u32], n: usize) -> usize {
    match v.windows(n).next() {
        Some(window) => window.len(),
        None => 0,
    }
}
#[cfg(not(stride_next))]
#[inline(never)]
pub fn windows_len(v: &[u32], n: usize) -> usize {
    v.windows(n).len()
}
#[cfg(stride_next)]
#[inline(never)]
pub fn chunks_len(v: &[u32], n: usize) -> usize {
    match v.chunks(n).next() {
        Some(chunk) => chunk.len(),
        None => 0,
    }
}
#[cfg(not(stride_next))]
#[inline(never)]
pub fn chunks_len(v: &[u32], n: usize) -> usize {
    v.chunks(n).len()
}
// The other zero-size stride constructors. Their failure edge raises std's
// own panic for the zero size (`std_panic_route`, `StdFailure::Constant`):
// `windows` calls `expect_failed` (a formatted `String` payload), the chunk
// family `assert!`s a literal (a `&str` payload). The payload's TYPE is what a
// hook's downcast observes; the merge of `c5919a122` raised `windows(0)` with
// a `&str` at -O0/-O1 (this test's `windows_len` rows) until `7c60cee46`.
#[cfg(stride_next)]
#[inline(never)]
pub fn chunks_exact_len(v: &[u32], n: usize) -> usize {
    match v.chunks_exact(n).next() {
        Some(chunk) => chunk.len(),
        None => 0,
    }
}
#[cfg(not(stride_next))]
#[inline(never)]
pub fn chunks_exact_len(v: &[u32], n: usize) -> usize {
    v.chunks_exact(n).len()
}
#[cfg(stride_next)]
#[inline(never)]
pub fn rchunks_len(v: &[u32], n: usize) -> usize {
    match v.rchunks(n).next() {
        Some(chunk) => chunk.len(),
        None => 0,
    }
}
#[cfg(not(stride_next))]
#[inline(never)]
pub fn rchunks_len(v: &[u32], n: usize) -> usize {
    v.rchunks(n).len()
}
#[cfg(stride_next)]
#[inline(never)]
pub fn rchunks_exact_len(v: &[u32], n: usize) -> usize {
    match v.rchunks_exact(n).next() {
        Some(chunk) => chunk.len(),
        None => 0,
    }
}
#[cfg(not(stride_next))]
#[inline(never)]
pub fn rchunks_exact_len(v: &[u32], n: usize) -> usize {
    v.rchunks_exact(n).len()
}

// Panics in `extern "C"` frames: under `panic=unwind` the hook runs, the unwind
// reaches the frame's terminate pad, and `panic_cannot_unwind` aborts.
#[inline(never)]
pub extern "C" fn c_panic_literal(n: u32) -> u32 {
    if n != 0 {
        panic!("literal in extern C")
    }
    0
}
#[inline(never)]
pub extern "C" fn c_assert(n: u32) -> u32 {
    assert!(n < 2);
    n
}
#[inline(never)]
pub extern "C" fn c_unreachable(n: u32) -> u32 {
    if n != 0 {
        unreachable!()
    }
    0
}
#[inline(never)]
pub extern "C" fn c_swap_remove(v: &mut Vec<u32>, i: usize) -> u32 {
    v.swap_remove(i)
}
#[inline(never)]
pub extern "C" fn c_split_at(v: &[u32], i: usize) -> usize {
    v.split_at(i).0.len()
}
#[inline(never)]
pub extern "C" fn c_str_range(s: &str, i: usize) -> usize {
    s[..i].len()
}
#[inline(never)]
pub extern "C" fn c_str_split_at(s: &str, i: usize) -> usize {
    s.split_at(i).1.len()
}
