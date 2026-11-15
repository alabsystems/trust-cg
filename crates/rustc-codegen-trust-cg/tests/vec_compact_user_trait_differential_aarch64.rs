// Other hosts compile no native test; a Darwin host must meet every prerequisite.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// The bridge's in-place `Vec` models (`retain`, `retain_mut`, `dedup`,
// `dedup_by`, `dedup_by_key`, `resize_with`, `insert`) against LLVM, for
// elements and keys whose `Drop` or `PartialEq` is user code, and its by-value
// iterator terminals over an owning `vec::IntoIter` when their payload unwinds.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `vec_element_ty` admits an element by its LAYOUT: a single-field newtype
// with a user `Drop` (`struct D(u32)`) maps to its scalar leaf, and `Box<U>` is
// a pointer element. A model is sound for such an element only when it makes
// every user-observable call std makes. MEASURED at origin/main 33eefbf58
// (Trust pack 9192, `no-proof-certs`, this file's test binary run against that
// backend): every destruction and unwind cell failed at -O0..-O3, each by
// diverging from LLVM, except that `dedup_by_key_f64_key` failed object
// emission ([TCG-IR-LOWER]), `dedup_derived_float_newtypes` diverged at
// -O0/-O1 only (at -O2/-O3 std's `dedup` reaches `dedup_by`),
// `unwind_closure_result_in_cell_unobservable_cleanup` was refused
// [TCG-EH-CALL-EDGE], and `dedup_by_key_ordering_key` and
// `dedup_by_key_repr_u8_enum_key` matched (the removed bitwise key model was
// exact for those keys; the cells guard the std body that replaced it). The
// refusal cells compiled (and diverged) or were refused under other codes; the
// control cells already matched.
//
//   * retain / retain_mut / dedup / dedup_by / dedup_by_key never dropped the
//     elements they removed, and resize_with's shrink never dropped the
//     truncated tail (skipped `Drop::drop`, leaked `Box` payloads);
//   * under panic=unwind, a closure that unwound out of retain / retain_mut /
//     dedup_by / dedup_by_key left `len` unchanged and the tail unshifted, so
//     a kept element was dropped twice (a `Box` element: a double free,
//     SIGTRAP in libmalloc), also from a frame with no cleanup of its own; a
//     destructor that unwound out of retain or resize_with's shrink did the
//     same or skipped the rest of the tail; a generator that unwound out of
//     resize_with leaked the elements already generated; an out-of-bounds
//     `insert` never dropped the moved-in element;
//   * dedup_by_key compared keys bit by bit (a user `PartialEq` on the key
//     never ran) and called the key once per element, where std calls
//     `key(current)` and `key(last kept)` per comparison through `&mut`;
//   * a closure that owned a value with a destructor was never dropped;
//   * dedup of a derived newtype over a float (`struct F(f64)`) compared the
//     leaf's bits at -O0/-O1, where its `PartialEq` is the field's IEEE `==`
//     (`NaN != NaN`, `0.0 == -0.0`).
//
// Each `Match` cell must now compile and match LLVM on stdout, exit code and
// killing signal. Each refusal cell must fail closed with the named
// `[TCG-...]` code at every level listed. The control cells show the models
// still compile and match for primitive elements and keys (u8..u64, i*, f32,
// f64, bool, char) and for derived-`PartialEq` no-drop elements.
//
// The `INTO_ITER_*` guests (the fifth test): a by-value terminal over
// `v.into_iter()` (`for_each`, `fold`, `sum`, `count`, `max`, `last`,
// `collect`, `extend`) owns the iterator, so when its closure or `Sum`'s
// checked add unwinds, std frees the iterator's buffer inside the terminal and
// then a `collect`'s partly built `Vec`. `extend` reserves as std's
// `SpecExtend` does, and a `Sum` / `Product` overflow reports the location of
// core's own check. MEASURED at origin/main b53f9641f (Trust pack 9192,
// `no-proof-certs`, this test run against that backend): 72 of the 148 cells
// it had then failed, each compiled and diverged from LLVM:
//
//   * 40 by-value unwind cells: one deallocation short (two for
//     `collect_fresh_buffer`), and `in_nounwind_frame` aborted without writing
//     `freed`. They are every such cell at -O0/-O1 and the filter/count,
//     map/max, skip/fold and take/sum cells at -O2/-O3;
//   * 12 `extend` cells whose destination grows: the bridge pushed with
//     doubling, where std reserves a `TrustedLen` source's exact count before
//     the drive and any other source's `size_hint().0 + 1` when the
//     destination is full (capacities and allocation counts differ);
//   * 20 overflow cells: the panic reported the reduction's call (in a
//     `#[track_caller]` frame, that frame's caller), where LLVM reports core's
//     `accum.rs` check.
//
// At 45c86dffe, with the buffer release in place, the 32 `extend` and
// overflow cells still failed the same way. The reservation the `extend`
// cells pin is the one 72a46f7ed made (`chain_is_trusted_len`,
// `emit_chain_exact_remaining`), which `tests/vec_extend_capacity_aarch64.rs`
// pins by capacity alone, without an unwind or an allocation count. The
// `&mut self` terminals, the `for` loop and the other controls matched, and
// the 48 refusal cells refused with the codes and reasons pinned here.
//
// The two `*_final_length_past_usize_max` guests came with the rebase onto
// main 988fd541d: with 72a46f7ed's reservation, whose `len + n` wrapped,
// their 4 -O0/-O1 cells diverged (the drive pushed 50 elements, capacity 64,
// before the payload panicked, where std raises capacity overflow with the
// destination untouched: `len*1000+cap=1002` and `2002`). The final length
// now saturates; their -O2/-O3 cells refuse as the other `extend` cells do.
//
// The `extend_range_*` guests extend from a bare `Range`, which the bridge
// lowers apart from the chain drive (`lower_vec_extend_range`). For the two
// `i64` guests, MEASURED at 14e9bc711 (debug bridge, Trust 9192,
// `no-proof-certs`, the guests compiled against that backend and LLVM): all
// 8 of their -O0/-O1 cells diverged. The count was a signed `end - start`,
// so a span of `2^63` or more read as empty: the extend appended nothing and
// returned (exit 0, `len*1000+cap=1002`), where std raises capacity overflow
// (exit 101 under `panic=unwind`, SIGABRT under `panic=abort`). The count is
// now the range's span in its own type and the final length saturates.
// The `u64` and `usize` guests came with the fill's same-width move: MEASURED
// at fb96d7a17 (same setup), their 8 -O0/-O1 cells were refused at object
// emission (`[TCG-IR-LOWER]`, a `CastOp::Trunc` from `I64` to `U64`, which
// is no narrowing); with the `Bitcast` they raise std's capacity overflow
// as LLVM does. Every guest's -O2/-O3 cells refuse as the other `extend`
// cells do.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const TARGET: &str = "aarch64-apple-darwin";
const LEVELS: [u32; 4] = [0, 1, 2, 3];
const RUN_TIMEOUT: Duration = Duration::from_secs(60);

/// Shared by every guest: a counting allocator (`live=` is the number of live
/// allocations), a fixed log the guests append to, a `D(u32)` whose user
/// `Drop` logs its value, and `Rep`, whose `Drop` prints the report while the
/// frame unwinds.
const PRELUDE: &str = r#"#![allow(static_mut_refs, dead_code, unused_mut, unused_variables, unused_assignments)]
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicIsize, Ordering::Relaxed};
struct Counting;
static LIVE: AtomicIsize = AtomicIsize::new(0);
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { LIVE.fetch_add(1, Relaxed); unsafe { System.alloc(l) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { LIVE.fetch_sub(1, Relaxed); unsafe { System.dealloc(p, l) } }
}
#[global_allocator]
static GA: Counting = Counting;
static mut LOG: [u32; 128] = [0; 128];
static mut N: usize = 0;
#[inline(never)]
fn log(x: u32) { unsafe { let n = N; if n < 128 { LOG[n] = x; N = n + 1; } } }
struct D(u32);
impl Drop for D { fn drop(&mut self) { log(self.0); } }
#[inline(never)]
fn report_log() {
    let n = unsafe { N };
    print!("log:");
    let mut i = 0;
    while i < n { print!(" {}", unsafe { LOG[i] }); i += 1; }
    println!();
}
#[inline(never)]
fn report() {
    print!("live={} ", LIVE.load(Relaxed));
    report_log();
}
struct Rep;
impl Drop for Rep { fn drop(&mut self) { report(); } }
"#;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Want {
    /// The bridge compiles the guest and its run matches LLVM's.
    Match,
    /// The bridge fails closed naming this `[TCG-...]` code, its stderr holds
    /// every one of these reasons, and every function it refuses (a `- symbol:
    /// reason` line) names the code or one of the reasons, so a refusal for
    /// any other reason fails the cell.
    Refuse(&'static str, &'static [&'static str]),
}

const MATCH4: [Want; 4] = [Want::Match; 4];

struct Case {
    name: &'static str,
    body: &'static str,
    /// Expected outcome per level -O0..-O3 under `-Cpanic=abort`, if run there.
    abort: Option<[Want; 4]>,
    /// Expected outcome per level -O0..-O3 under `-Cpanic=unwind`, if run there.
    unwind: Option<[Want; 4]>,
}

/// Both strategies, every level must match.
const fn both(name: &'static str, body: &'static str) -> Case {
    Case {
        name,
        body,
        abort: Some(MATCH4),
        unwind: Some(MATCH4),
    }
}

/// A guest that panics: only `-Cpanic=unwind` exercises its repair.
const fn unwinding(name: &'static str, body: &'static str) -> Case {
    Case {
        name,
        body,
        abort: None,
        unwind: Some(MATCH4),
    }
}

/// Removed, deduplicated and truncated elements: their destructors run in
/// std's order, the key closure / key `PartialEq` of `dedup_by_key` run
/// exactly as std calls them, and `dedup` decides by the element's own
/// `PartialEq`. No guest panics.
const DESTRUCTION_CASES: &[Case] = &[
    both(
        "retain_drop_newtype",
        r#"fn main() {
    {
        let mut v = Vec::new();
        for i in 1..=5 { v.push(D(i)); }
        v.retain(|d| { log(200 + d.0); d.0 != 2 && d.0 != 4 });
        log(100 + v.len() as u32);
    }
    report();
}
"#,
    ),
    both(
        "retain_mut_drop_newtype",
        r#"fn main() {
    {
        let mut v = Vec::new();
        for i in 1..=6 { v.push(D(i)); }
        v.retain_mut(|d| { d.0 += 10; d.0 % 3 != 0 });
        log(100 + v.len() as u32);
    }
    report();
}
"#,
    ),
    both(
        "retain_box",
        r#"fn main() {
    let before = LIVE.load(Relaxed);
    {
        let mut v: Vec<Box<u32>> = Vec::new();
        for i in 1..=6 { v.push(Box::new(i)); }
        v.retain(|b| **b % 2 == 0);
        log(100 + v.len() as u32);
        log(300 + (LIVE.load(Relaxed) - before) as u32);
        let mut s = 0; for b in v.iter() { s += **b; } log(s);
    }
    log(500 + (LIVE.load(Relaxed) - before) as u32);
    report();
}
"#,
    ),
    both(
        "dedup_by_drop_newtype",
        r#"fn main() {
    {
        let mut v = Vec::new();
        for &i in [1u32, 11, 2, 3, 13, 23, 4].iter() { v.push(D(i)); }
        v.dedup_by(|a, b| { log(200 + a.0); a.0 % 10 == b.0 % 10 });
        log(100 + v.len() as u32);
    }
    report();
}
"#,
    ),
    both(
        "dedup_by_key_drop_newtype",
        r#"fn main() {
    {
        let mut v = Vec::new();
        for &i in [1u32, 1, 2, 3, 3, 3, 4].iter() { v.push(D(i)); }
        v.dedup_by_key(|d| { log(300 + d.0); d.0 });
        log(100 + v.len() as u32);
    }
    report();
}
"#,
    ),
    both(
        "dedup_by_key_box",
        r#"fn main() {
    let before = LIVE.load(Relaxed);
    {
        let mut v: Vec<Box<u32>> = Vec::new();
        for i in 0..6u32 { v.push(Box::new(i / 2)); }
        v.dedup_by_key(|b| **b);
        log(100 + v.len() as u32);
        log(300 + (LIVE.load(Relaxed) - before) as u32);
    }
    log(500 + (LIVE.load(Relaxed) - before) as u32);
    report();
}
"#,
    ),
    both(
        "dedup_derived_eq_drop_newtype",
        r#"#[derive(PartialEq)]
struct E(u32);
impl Drop for E { fn drop(&mut self) { log(self.0); } }
fn main() {
    {
        let mut v = Vec::new();
        for &i in [1u32, 1, 2, 3, 3, 3, 4].iter() { v.push(E(i)); }
        v.dedup();
        log(100 + v.len() as u32);
    }
    report();
}
"#,
    ),
    both(
        "dedup_by_key_user_eq_key",
        r#"#[derive(Clone, Copy)]
struct K(i64);
impl PartialEq for K {
    fn eq(&self, o: &K) -> bool { log(400); self.0 % 2 == o.0 % 2 }
}
fn main() {
    let mut v: Vec<i64> = Vec::new();
    for &x in [1i64, 3, 5, 2, 4, 7].iter() { v.push(x); }
    v.dedup_by_key(|x| K(*x));
    log(100 + v.len() as u32);
    for x in v.iter() { log(*x as u32); }
    report_log();
}
"#,
    ),
    both(
        "dedup_by_key_user_enum_key",
        r#"#[derive(Clone, Copy)]
enum E { A, B, C }
impl PartialEq for E {
    fn eq(&self, o: &E) -> bool { matches!((self, o), (E::C, E::C)) || (!matches!(self, E::C) && !matches!(o, E::C)) }
}
fn main() {
    let mut v: Vec<u8> = Vec::new();
    for &x in [0u8, 1, 0, 2, 2, 1].iter() { v.push(x); }
    v.dedup_by_key(|x| match *x { 0 => E::A, 1 => E::B, _ => E::C });
    log(100 + v.len() as u32);
    for x in v.iter() { log(*x as u32); }
    report_log();
}
"#,
    ),
    // Keys whose `PartialEq` is the builtin derive: a fieldless enum, std's
    // `Ordering`, a `#[repr(u8)]` enum. Std's own `key(a) == key(b)` closure
    // stores each key in a memory cell (its address goes to `eq`), and its
    // second `key` call carries a cleanup edge whose pad only drops the first
    // key, which needs no drop.
    both(
        "dedup_by_key_derived_enum_key_drop_newtype",
        r#"#[derive(PartialEq, Clone, Copy)]
enum K { A, B, C }
fn main() {
    {
        let mut v = Vec::new();
        for &i in [10u32, 11, 20, 21, 22, 30, 12].iter() { v.push(D(i)); }
        v.dedup_by_key(|d| { log(300 + d.0); match d.0 / 10 { 1 => K::A, 2 => K::B, _ => K::C } });
        log(100 + v.len() as u32);
    }
    report();
}
"#,
    ),
    both(
        "dedup_by_key_ordering_key",
        r#"fn main() {
    let mut v: Vec<u32> = Vec::new();
    for &x in [1u32, 2, 5, 7, 9, 5, 3, 4].iter() { v.push(x); }
    v.dedup_by_key(|x| (*x).cmp(&5));
    log(100 + v.len() as u32);
    for x in v.iter() { log(*x); }
    report_log();
}
"#,
    ),
    both(
        "dedup_by_key_repr_u8_enum_key",
        r#"#[derive(PartialEq, Clone, Copy)]
#[repr(u8)]
enum K { A = 3, B = 9 }
fn main() {
    let mut v: Vec<i16> = Vec::new();
    for &x in [-1i16, -2, 3, 4, -5].iter() { v.push(x); }
    v.dedup_by_key(|x| if *x < 0 { K::A } else { K::B });
    log(100 + v.len() as u32);
    for x in v.iter() { log(*x as u32); }
    report_log();
}
"#,
    ),
    // A derived newtype over a float maps to its float leaf; its `PartialEq` is
    // the field's IEEE `==` (`NaN != NaN`, `0.0 == -0.0`). The logged exponent
    // bits show which element of each run was kept.
    both(
        "dedup_derived_float_newtypes",
        r#"#[derive(PartialEq, Clone, Copy)]
struct F(f64);
#[derive(PartialEq, Clone, Copy)]
struct H(f32);
#[derive(PartialEq, Clone, Copy)]
struct G(H);
#[inline(never)]
fn f64s() {
    let mut v: Vec<F> = Vec::new();
    for &x in [f64::NAN, f64::NAN, 0.0, -0.0, 1.0, 1.0, -0.0, 0.0].iter() { v.push(F(x)); }
    v.dedup();
    log(100 + v.len() as u32);
    for x in v.iter() { log((x.0.to_bits() >> 52) as u32); }
}
#[inline(never)]
fn f32_zeros() {
    let mut v: Vec<H> = Vec::new();
    for &x in [0.0f32, -0.0, 1.0].iter() { v.push(H(x)); }
    v.dedup();
    log(200 + v.len() as u32);
    for x in v.iter() { log(x.0.to_bits() >> 23); }
}
#[inline(never)]
fn f32_nans() {
    let mut v: Vec<H> = Vec::new();
    for _ in 0..2 { v.push(H(f32::NAN)); }
    v.dedup();
    log(300 + v.len() as u32);
}
#[inline(never)]
fn nested() {
    let mut v: Vec<G> = Vec::new();
    for &x in [-0.0f32, 0.0, 2.0].iter() { v.push(G(H(x))); }
    v.dedup();
    log(400 + v.len() as u32);
    for x in v.iter() { log(x.0 .0.to_bits() >> 23); }
}
fn main() {
    f64s(); f32_zeros(); f32_nans(); nested();
    report_log();
}
"#,
    ),
    both(
        "dedup_by_key_mut_key",
        r#"fn main() {
    let mut v: Vec<u32> = Vec::new();
    for &x in [10u32, 20, 30, 40].iter() { v.push(x); }
    v.dedup_by_key(|x| { log(*x); *x += 1; *x / 1000 + (*x % 2) });
    log(100 + v.len() as u32);
    for x in v.iter() { log(*x); }
    report_log();
}
"#,
    ),
    both(
        "dedup_by_key_call_count",
        r#"fn main() {
    let mut v: Vec<u32> = Vec::new();
    for x in 1..=6u32 { v.push(x); }
    let mut calls = 0u32;
    v.dedup_by_key(|x| { calls += 1; *x / 2 });
    log(calls);
    log(100 + v.len() as u32);
    for x in v.iter() { log(200 + *x); }
    report_log();
}
"#,
    ),
    both(
        "dedup_by_key_f64_key",
        r#"fn key(x: &mut u64) -> f64 {
    if *x < 2 { f64::NAN } else if *x == 2 { 0.0 } else { -0.0 }
}
fn main() {
    let mut v: Vec<u64> = Vec::new();
    for x in 0..5u64 { v.push(x); }
    v.dedup_by_key(|x| key(x));
    log(100 + v.len() as u32);
    for x in v.iter() { log(*x as u32); }
    report_log();
}
"#,
    ),
    both(
        "resize_with_shrink_drop_newtype",
        r#"fn main() {
    {
        let mut v = Vec::new();
        for i in 1..=6 { v.push(D(i)); }
        let mut k = 50;
        v.resize_with(3, || { k += 1; D(k) });
        log(100 + v.len() as u32);
        v.resize_with(5, || { k += 1; D(k) });
        log(110 + v.len() as u32);
    }
    report();
}
"#,
    ),
    both(
        "resize_with_shrink_box",
        r#"fn main() {
    let before = LIVE.load(Relaxed);
    {
        let mut v: Vec<Box<u32>> = Vec::new();
        for i in 1..=6 { v.push(Box::new(i)); }
        v.resize_with(2, || Box::new(9));
        log(100 + v.len() as u32);
        log(300 + (LIVE.load(Relaxed) - before) as u32);
    }
    log(500 + (LIVE.load(Relaxed) - before) as u32);
    report();
}
"#,
    ),
];

/// A closure or destructor unwinds out of the model: the Vec must be left
/// exactly as std's guards leave it, and every element dropped exactly once.
const UNWIND_CASES: &[Case] = &[
    unwinding(
        "unwind_retain_drop_newtype",
        r#"fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for i in 1..=4 { v.push(D(i)); }
    v.retain(|d| { if d.0 == 3 { panic!("p"); } d.0 != 1 });
    log(100 + v.len() as u32);
}
"#,
    ),
    unwinding(
        "unwind_retain_mut_drop_newtype",
        r#"fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for i in 1..=5 { v.push(D(i)); }
    v.retain_mut(|d| { if d.0 == 4 { panic!("p"); } d.0 += 10; d.0 != 12 });
    log(100 + v.len() as u32);
}
"#,
    ),
    unwinding(
        "unwind_retain_box",
        r#"fn main() {
    let _r = Rep;
    let mut v: Vec<Box<u32>> = Vec::new();
    for i in 1..=4 { v.push(Box::new(i)); }
    v.retain(|b| { if **b == 3 { panic!("p"); } **b != 1 });
    log(100 + v.len() as u32);
}
"#,
    ),
    unwinding(
        "unwind_retain_drop_panics",
        r#"struct P(u32);
impl Drop for P { fn drop(&mut self) { log(self.0); if self.0 == 2 { panic!("drop"); } } }
fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for i in 1..=5 { v.push(P(i)); }
    v.retain(|d| { log(200 + d.0); d.0 != 2 && d.0 != 4 });
    log(100 + v.len() as u32);
}
"#,
    ),
    unwinding(
        "unwind_retain_u64_observed",
        r#"struct G(*mut Vec<u64>);
impl Drop for G {
    fn drop(&mut self) {
        let v = unsafe { &*self.0 };
        log(100 + v.len() as u32);
        for x in v.iter() { log(*x as u32); }
        report_log();
    }
}
fn main() {
    let mut v: Vec<u64> = Vec::new();
    for x in 1..=5u64 { v.push(x); }
    let p: *mut Vec<u64> = &mut v;
    let _g = G(p);
    unsafe { (*p).retain(|x| { if *x == std::hint::black_box(4) { panic!("p"); } *x % 2 == 1 }); }
    log(999);
}
"#,
    ),
    unwinding(
        "unwind_dedup_by_drop_newtype",
        r#"fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for &i in [1u32, 1, 2, 3, 4].iter() { v.push(D(i)); }
    v.dedup_by(|a, b| { if a.0 == 3 { panic!("p"); } a.0 == b.0 });
    log(100 + v.len() as u32);
}
"#,
    ),
    unwinding(
        "unwind_dedup_by_key_drop_newtype",
        r#"fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for &i in [1u32, 1, 2, 3, 4].iter() { v.push(D(i)); }
    v.dedup_by_key(|a| { if a.0 == 3 { panic!("p"); } a.0 });
    log(100 + v.len() as u32);
}
"#,
    ),
    // The key call that unwinds is std's second (`key(last kept)`), whose
    // cleanup edge drops the first key: an enum with no destructor.
    unwinding(
        "unwind_dedup_by_key_enum_key_on_last_kept",
        r#"#[derive(PartialEq, Clone, Copy)]
enum K { Odd, Even }
fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for &i in [1u32, 3, 2, 5, 4].iter() { v.push(D(i)); }
    let mut calls = 0u32;
    v.dedup_by_key(|d| {
        calls += 1;
        log(300 + d.0);
        if calls == 6 { panic!("p"); }
        if d.0 % 2 == 0 { K::Even } else { K::Odd }
    });
    log(100 + v.len() as u32);
}
"#,
    ),
    // The same closure shape in user code: a generic `f(a) == f(b)` whose
    // second call unwinds through a frame whose pad drops nothing.
    unwinding(
        "unwind_closure_result_in_cell_unobservable_cleanup",
        r#"#[derive(PartialEq, Clone, Copy)]
enum K { Lo, Hi }
#[inline(never)]
fn same<T: PartialEq, F: FnMut(u32) -> T>(f: &mut F, a: u32, b: u32) -> bool { f(a) == f(b) }
fn main() {
    let _r = Rep;
    let _d = D(7);
    let mut key = |x: u32| { log(200 + x); if x == 9 { panic!("p"); } if x < 5 { K::Lo } else { K::Hi } };
    log(same(&mut key, 1, 2) as u32);
    log(same(&mut key, 1, 6) as u32);
    log(same(&mut key, 3, 9) as u32);
    log(999);
}
"#,
    ),
    unwinding(
        "unwind_resize_with_grow",
        r#"fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for i in 1..=2 { v.push(D(i)); }
    let mut k = 50;
    v.resize_with(5, || { k += 1; if k == 53 { panic!("p"); } D(k) });
    log(100 + v.len() as u32);
}
"#,
    ),
    // A model called from a frame with no cleanup of its own (the call's unwind
    // action is `Continue`) still owns its landing pad.
    unwinding(
        "unwind_retain_from_cleanup_free_frame",
        r#"#[inline(never)]
fn compact(v: &mut Vec<D>) {
    v.retain(|d| { if d.0 == 4 { panic!("p"); } d.0 != 2 });
}
fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for i in 1..=5 { v.push(D(i)); }
    compact(&mut v);
    log(100 + v.len() as u32);
}
"#,
    ),
    unwinding(
        "unwind_dedup_by_from_cleanup_free_frame",
        r#"#[inline(never)]
fn squash(v: &mut Vec<D>) {
    v.dedup_by(|a, b| { if a.0 == 4 { panic!("p"); } a.0 == b.0 });
}
fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for &i in [1u32, 1, 2, 2, 4, 5].iter() { v.push(D(i)); }
    squash(&mut v);
    log(100 + v.len() as u32);
}
"#,
    ),
    unwinding(
        "unwind_insert_oob_from_cleanup_free_frame",
        r#"struct R2;
impl Drop for R2 { fn drop(&mut self) { report_log(); } }
#[inline(never)]
fn put(v: &mut Vec<D>, at: usize, x: D) {
    v.insert(at, x);
}
fn main() {
    let _r = R2;
    let mut v = Vec::new();
    for i in 1..=3 { v.push(D(i)); }
    put(&mut v, std::hint::black_box(9), D(70));
    log(100 + v.len() as u32);
}
"#,
    ),
    // A truncated element's destructor unwinds: the rest of the tail is still
    // dropped (`drop_in_place::<[T]>`), and the Vec keeps the new length.
    unwinding(
        "unwind_resize_with_shrink_drop_panics",
        r#"struct P(u32);
impl Drop for P { fn drop(&mut self) { log(self.0); if self.0 == 3 { panic!("drop"); } } }
#[inline(never)]
fn shrink(v: &mut Vec<P>) {
    v.resize_with(1, || P(9));
}
fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    for i in 1..=5 { v.push(P(i)); }
    shrink(&mut v);
    log(100 + v.len() as u32);
}
"#,
    ),
    // std formats the out-of-bounds message (`insertion index (is 7) should be
    // <= len (is 3)`) where the bridge raises a fixed one, so the payload's
    // allocation count is not compared here; only the drops are.
    unwinding(
        "unwind_insert_oob",
        r#"struct R2;
impl Drop for R2 { fn drop(&mut self) { report_log(); } }
fn main() {
    let _r = R2;
    let mut v = Vec::new();
    for i in 1..=3 { v.push(D(i)); }
    let x = D(50);
    v.insert(std::hint::black_box(7), D(9));
    log(100 + v.len() as u32);
}
"#,
    ),
];

/// The models still compile, and match LLVM, for primitive elements and keys
/// and for derived-`PartialEq` no-drop elements.
const CONTROL_CASES: &[Case] = &[
    // One `Vec` per function: a `main` holding several primitive `Vec`s hits an
    // unrelated, pre-existing [TCG-SSA-071] refusal under panic=unwind at -O2/-O3.
    both(
        "control_retain_primitives",
        r#"#[inline(never)]
fn u8s() {
    let mut v: Vec<u8> = Vec::new(); for x in 0..10u8 { v.push(x); }
    v.retain(|x| *x % 3 != 0);
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
#[inline(never)]
fn i64s() {
    let mut v: Vec<i64> = Vec::new(); for x in -5..5i64 { v.push(x * 7); }
    v.retain_mut(|x| { *x += 1; *x > 0 });
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
#[inline(never)]
fn bools() {
    let mut v: Vec<bool> = Vec::new(); for x in 0..7u32 { v.push(x % 2 == 0); }
    v.retain(|x| *x);
    log(v.len() as u32);
}
#[inline(never)]
fn chars() {
    let mut v: Vec<char> = Vec::new(); for x in 0..6u32 { v.push(char::from_u32(0x61 + x).unwrap_or('?')); }
    v.retain(|c| *c != 'b' && *c != 'e');
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
#[inline(never)]
fn u16s() {
    let mut v: Vec<u16> = Vec::new(); for x in 0..9u16 { v.push(x * 1000); }
    v.retain(|x| *x >= 3000);
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
#[inline(never)]
fn i32s() {
    let mut v: Vec<i32> = Vec::new(); for x in -4..4i32 { v.push(x); }
    v.retain(|x| *x != 0);
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
fn main() {
    u8s(); i64s(); bools(); chars(); u16s(); i32s();
    report_log();
}
"#,
    ),
    both(
        "control_dedup_primitives_and_derived",
        r#"#[derive(PartialEq, Clone, Copy)]
struct W(u32);
#[inline(never)]
fn u8s() {
    let mut v: Vec<u8> = Vec::new(); for x in 0..9u8 { v.push(x / 3 % 2); }
    v.dedup();
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
#[inline(never)]
fn i64s() {
    let mut v: Vec<i64> = Vec::new(); for x in -3..6i64 { v.push(x); }
    v.dedup_by_key(|x| *x / 2);
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
#[inline(never)]
fn u32s() {
    let mut v: Vec<u32> = Vec::new(); for x in 0..6u32 { v.push(10 * (x / 2) + x % 2); }
    v.dedup_by(|a, b| *a / 10 == *b / 10);
    log(v.len() as u32); for x in v.iter() { log(*x); }
}
#[inline(never)]
fn chars() {
    let mut v: Vec<char> = Vec::new(); for x in 0..6u32 { v.push(char::from_u32(0x61 + x / 2).unwrap_or('?')); }
    v.dedup();
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
#[inline(never)]
fn bools() {
    let mut v: Vec<bool> = Vec::new(); for x in 0..6u32 { v.push(x / 2 == 1); }
    v.dedup();
    log(v.len() as u32);
}
#[inline(never)]
fn derived() {
    let mut v: Vec<W> = Vec::new(); for x in 0..6u32 { v.push(W(x / 2)); }
    v.dedup();
    log(v.len() as u32); for x in v.iter() { log(x.0); }
}
#[inline(never)]
fn u16_keys() {
    let mut v: Vec<u16> = Vec::new(); for x in 5..12u16 { v.push(x * 3); }
    v.dedup_by_key(|x| (*x / 10) as u8);
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
fn main() {
    u8s(); i64s(); u32s(); chars(); bools(); derived(); u16_keys();
    report_log();
}
"#,
    ),
    // Primitive floats and a derived integer newtype keep the dedup helpers.
    both(
        "control_dedup_floats_and_derived_int_newtype",
        r#"#[derive(PartialEq, Clone, Copy)]
struct I(i64);
#[inline(never)]
fn f64s() {
    let mut v: Vec<f64> = Vec::new();
    for &x in [f64::NAN, f64::NAN, 0.0, -0.0, 1.0, 1.0].iter() { v.push(x); }
    v.dedup();
    log(100 + v.len() as u32);
    for x in v.iter() { log((x.to_bits() >> 52) as u32); }
}
#[inline(never)]
fn f32s() {
    let mut v: Vec<f32> = Vec::new();
    for &x in [-0.0f32, 0.0, f32::NAN, f32::NAN].iter() { v.push(x); }
    v.dedup();
    log(200 + v.len() as u32);
    for x in v.iter() { log(x.to_bits() >> 23); }
}
#[inline(never)]
fn ints() {
    let mut v: Vec<I> = Vec::new();
    for &x in [-1i64, -1, 0, i64::MIN, i64::MIN, 5].iter() { v.push(I(x)); }
    v.dedup();
    log(300 + v.len() as u32);
    for x in v.iter() { log((x.0 >> 32) as u32); }
}
fn main() {
    f64s(); f32s(); ints();
    report_log();
}
"#,
    ),
    both(
        "control_resize_with_insert_primitives",
        r#"#[inline(never)]
fn u32s() {
    let mut v: Vec<u32> = Vec::new(); for x in 0..6u32 { v.push(x); }
    v.resize_with(2, || 9);
    let mut k = 40u32;
    v.resize_with(5, || { k += 1; k });
    log(v.len() as u32); for x in v.iter() { log(*x); }
}
#[inline(never)]
fn i8s() {
    let mut v: Vec<i8> = Vec::new(); for x in 0..3i8 { v.push(-x); }
    v.insert(1, 100);
    v.insert(4, -100);
    log(v.len() as u32); for x in v.iter() { log(*x as u32); }
}
#[inline(never)]
fn u64s() {
    let mut v: Vec<u64> = Vec::new(); for x in 0..3u64 { v.push(x << 40); }
    v.insert(0, 7);
    log(v.len() as u32); for x in v.iter() { log((*x >> 40) as u32 + *x as u32); }
}
fn main() {
    u32s(); i8s(); u64s();
    report_log();
}
"#,
    ),
    both(
        "control_insert_resize_with_drop_newtype",
        r#"fn main() {
    {
        let mut d: Vec<D> = Vec::new(); for x in 1..=3u32 { d.push(D(x)); }
        d.insert(1, D(9));
        let mut m = 60u32;
        d.resize_with(6, || { m += 1; D(m) });
        log(d.len() as u32); for x in d.iter() { log(x.0); }
    }
    report();
}
"#,
    ),
    both(
        "control_retain_dedup_derived_struct",
        r#"#[derive(PartialEq, Clone, Copy)]
struct P { a: u32, b: u16 }
fn main() {
    let mut v: Vec<P> = Vec::new();
    for x in 0..8u32 { v.push(P { a: x / 2, b: (x * 3) as u16 }); }
    v.retain(|p| p.b % 2 == 0);
    v.dedup_by(|x, y| x.a == y.a);
    log(v.len() as u32); for p in v.iter() { log(p.a * 100 + p.b as u32); }
    report_log();
}
"#,
    ),
];

/// Shapes whose user-observable calls the models do not make fail closed by
/// name instead.
const REFUSAL_CASES: &[Case] = &[
    // std drops the `move` closure (and the `D` it owns) when `retain`
    // returns; the model never drops its closure, so the consumed-closure
    // admission refuses it.
    Case {
        name: "refuse_retain_closure_owns_drop",
        body: r#"fn main() {
    {
        let g = D(77);
        let mut v: Vec<u32> = Vec::new();
        for x in 1..=4u32 { v.push(x); }
        v.retain(move |x| { let _ = &g; *x != 2 });
        log(100 + v.len() as u32);
    }
    report();
}
"#,
        abort: Some([Want::Refuse("TCG-CLOSURE-DROP", &[]); 4]),
        unwind: Some([Want::Refuse("TCG-CLOSURE-DROP", &[]); 4]),
    },
    // A closure owning only a `Box` frees nothing but memory, but this
    // prelude links a counting `#[global_allocator]` whose `dealloc` the
    // skipped drop glue would have run (`live=` reads it back), so the same
    // admission refuses it.
    Case {
        name: "refuse_retain_closure_owns_box_under_global_allocator",
        body: r#"fn main() {
    {
        let b = Box::new(2u32);
        let mut v: Vec<u32> = Vec::new();
        for x in 1..=4u32 { v.push(x); }
        v.retain(move |x| *x % *b == 0);
        log(100 + v.len() as u32);
    }
    report();
}
"#,
        abort: Some([Want::Refuse("TCG-CLOSURE-DROP", &[]); 4]),
        unwind: Some([Want::Refuse("TCG-CLOSURE-DROP", &[]); 4]),
    },
    // `Outer` needs drop through its field, so its destruction is not the
    // single user `Drop::drop` call the model lowers.
    Case {
        name: "refuse_retain_nested_drop_newtype",
        body: r#"struct Outer(D);
fn main() {
    {
        let mut v: Vec<Outer> = Vec::new();
        for x in 1..=4u32 { v.push(Outer(D(x))); }
        v.retain(|o| o.0 .0 != 2);
        log(100 + v.len() as u32);
    }
    report();
}
"#,
        abort: Some([Want::Refuse("TCG-VEC-ELEM-DROP", &[]); 4]),
        unwind: Some([Want::Refuse("TCG-VEC-ELEM-DROP", &[]); 4]),
    },
];

/// The owning `vec::IntoIter` guests: a counting allocator whose report gives
/// the allocations and deallocations since the last `make` / `mark`, the value a
/// terminal produced (`out`), and `Rep`, whose `Drop` prints the report while
/// the frame unwinds (the bridge refuses `catch_unwind`'s intrinsic). A nonzero
/// `TRACE_SIZE` makes the deallocation of exactly that many bytes write `freed`
/// to stdout at once, which a later abort cannot lose. `note` records a `Vec`'s
/// length and capacity without allocating; `Notes`, declared before `Rep`,
/// prints them after the report, so its own printing is never counted.
macro_rules! into_iter_prelude {
    () => {
        r#"#![allow(static_mut_refs, dead_code, unused_mut, unused_variables, improper_ctypes_definitions)]
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}
struct Counting;
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);
static TRACE_SIZE: AtomicUsize = AtomicUsize::new(0);
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc(l) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        DEALLOCS.fetch_add(1, Relaxed);
        if l.size() == TRACE_SIZE.load(Relaxed) { unsafe { write(1, b"freed\n".as_ptr(), 6); } }
        unsafe { System.dealloc(p, l) }
    }
}
#[global_allocator]
static GA: Counting = Counting;
static mut A0: usize = 0;
static mut D0: usize = 0;
static mut OUT: u64 = 0;
#[inline(never)]
fn mark() { unsafe { A0 = ALLOCS.load(Relaxed); D0 = DEALLOCS.load(Relaxed); } }
#[inline(never)]
fn fresh(n: u64) -> Vec<u64> {
    let mut v = Vec::with_capacity(n as usize);
    for i in 1..=n { v.push(i * 10); }
    v
}
#[inline(never)]
fn make(n: u64) -> Vec<u64> {
    let v = fresh(n);
    mark();
    v
}
#[inline(never)]
fn trip(x: u64) -> bool { x == std::hint::black_box(50) }
#[inline(never)]
fn out(x: u64) { unsafe { OUT = x; } }
#[inline(never)]
fn report() {
    let a = ALLOCS.load(Relaxed) - unsafe { A0 };
    let d = DEALLOCS.load(Relaxed) - unsafe { D0 };
    println!("allocs={} deallocs={} out={}", a, d, unsafe { OUT });
}
struct Rep;
impl Drop for Rep { fn drop(&mut self) { report(); } }
static mut NOTES: [u64; 8] = [0; 8];
static mut NOTED: usize = 0;
#[inline(never)]
fn note(len: usize, cap: usize) {
    unsafe { if NOTED < 8 { NOTES[NOTED] = (len * 1000 + cap) as u64; NOTED += 1; } }
}
struct Notes;
impl Drop for Notes {
    fn drop(&mut self) {
        let n = unsafe { NOTED };
        let mut i = 0;
        while i < n { println!("len*1000+cap={}", unsafe { NOTES[i] }); i += 1; }
    }
}
"#
    };
}
const INTO_ITER_PRELUDE: &str = into_iter_prelude!();

/// `INTO_ITER_PRELUDE` plus `show_panic_location`, which installs a panic hook
/// that writes the panic's `Location` at once (an abort cannot lose it).
const INTO_ITER_HOOK_PRELUDE: &str = concat!(
    into_iter_prelude!(),
    r#"fn put(bytes: &[u8]) { unsafe { write(1, bytes.as_ptr(), bytes.len()); } }
fn put_num(mut n: u32) {
    let mut digits = [0u8; 10];
    let mut i = 10;
    loop { i -= 1; digits[i] = b'0' + (n % 10) as u8; n /= 10; if n == 0 { break; } }
    let mut out = [0u8; 10];
    let mut k = 0;
    while i < 10 { out[k] = digits[i]; k += 1; i += 1; }
    unsafe { write(1, out.as_ptr(), k); }
}
#[inline(never)]
fn show_panic_location() {
    std::panic::set_hook(Box::new(|info| {
        let l = info.location().unwrap();
        put(b"panic at ");
        put(l.file().as_bytes());
        put(b":");
        put_num(l.line());
        put(b":");
        put_num(l.column());
        put(b"\n");
    }));
}
"#
);

const INTO_ITER_GUESTS: Guests = Guests {
    prelude: INTO_ITER_PRELUDE,
    overflow_checks: false,
};

/// The same guests, with the location hook, under `-Coverflow-checks=on`,
/// where `Sum`'s and `Product`'s checked arithmetic panics.
const INTO_ITER_CHECKED_GUESTS: Guests = Guests {
    prelude: INTO_ITER_HOOK_PRELUDE,
    overflow_checks: true,
};

/// The -O2/-O3 refusals of the `INTO_ITER_*` guests. MIR inlining hands the
/// bridge a different call there, and each is refused before the bridge
/// reaches the by-value terminal lowering that opens its landing pad
/// (`begin_consumed_owner_drive`): `Iterator::fold` / `sum` over an iterator
/// rustc keeps out of memory, `Vec`'s unintercepted `extend_trusted` /
/// `extend_desugared` / `spec_extend`, a collect's `Vec` returned through an
/// indirect call, `rfold` on the owning iterator. Each pin names its reasons,
/// so a refusal raised by the drive itself, or by the pad
/// (`[TCG-INTOITER-UNWIND-RELEASE]`), fails the cell.
const FOLD_SELF_NOT_IN_MEMORY: &str = "iterator fold self argument is not memory-backed";
const SUM_SELF_NOT_IN_MEMORY: &str = "iterator sum self argument is not memory-backed";
const EXTEND_TRUSTED: &str = "::extend_trusted is not an intercepted Vec method";
const EXTEND_DESUGARED: &str = "::extend_desugared is not an intercepted Vec method";
const SPEC_EXTEND: &str = "::spec_extend is not an intercepted Vec method";
const FOLD_REFUSED: Want = Want::Refuse("TCG-MIR-UNSUPPORTED", &[FOLD_SELF_NOT_IN_MEMORY]);
const SUM_REFUSED: Want = Want::Refuse("TCG-MIR-UNSUPPORTED", &[SUM_SELF_NOT_IN_MEMORY]);
const EXTEND_TRUSTED_REFUSED: Want = Want::Refuse("TCG-MIR-UNSUPPORTED", &[EXTEND_TRUSTED]);
const EXTEND_DESUGARED_REFUSED: Want = Want::Refuse("TCG-MIR-UNSUPPORTED", &[EXTEND_DESUGARED]);
const COLLECT_SRET_REFUSED: Want = Want::Refuse("TCG-SRET-ABI", &[]);
const RFOLD_REFUSED: Want = Want::Refuse("TCG-OWNING-ITER-METHOD", &["`rfold` on a vec::IntoIter"]);
/// `control_into_iter_terminals_low_levels` at -O2/-O3: its five functions,
/// each refused for its own reason.
const CONTROL_LOW_LEVELS_REFUSED: Want = Want::Refuse(
    "TCG-MIR-UNSUPPORTED",
    &[
        FOLD_SELF_NOT_IN_MEMORY,
        SUM_SELF_NOT_IN_MEMORY,
        "[TCG-SRET-ABI]",
        EXTEND_TRUSTED,
    ],
);

/// Match at -O0/-O1, `refusal` at -O2/-O3.
const fn low_levels(refusal: Want) -> [Want; 4] {
    [Want::Match, Want::Match, refusal, refusal]
}

/// A panicking guest whose -O2/-O3 cells are `refusal` (`low_levels`).
const fn unwinding_low(name: &'static str, body: &'static str, refusal: Want) -> Case {
    Case {
        name,
        body,
        abort: None,
        unwind: Some(low_levels(refusal)),
    }
}

/// A guest run under both strategies whose -O2/-O3 cells are `refusal`.
const fn both_low(name: &'static str, body: &'static str, refusal: Want) -> Case {
    Case {
        name,
        body,
        abort: Some(low_levels(refusal)),
        unwind: Some(low_levels(refusal)),
    }
}

/// A by-value terminal (`for_each`, `fold`, `sum`, `count`, `max`, `last`,
/// `collect`, `extend`) owns the `vec::IntoIter` it consumes: when its payload
/// closure, or `Sum`'s checked add, panics, std drops that iterator inside the
/// terminal (the buffer is freed) and, for `collect`, then the `Vec` being
/// built, before the unwind reaches the caller's frame. Each guest panics at the
/// fifth element; `Rep` reports the counts while `main` unwinds, so a buffer the
/// unwind skipped shows as one deallocation short of LLVM's. In a frame that
/// cannot unwind (`extern "C"`) the buffer is freed before the abort. An
/// `extend` whose destination must grow reserves as std's `SpecExtend` does,
/// and the unwind finds that capacity (`note`). The `&mut self` terminals
/// (`any`, `find`) and the `for` loop leave the iterator to the caller's own
/// drop and are the controls.
const INTO_ITER_UNWIND_CASES: &[Case] = &[
    unwinding_low(
        "unwind_into_iter_for_each",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    let mut s = 0u64;
    v.into_iter().for_each(|x| { if trip(x) { panic!("p"); } s += x; });
    out(s);
}
"#,
        FOLD_REFUSED,
    ),
    unwinding_low(
        "unwind_into_iter_fold",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().fold(0u64, |a, x| { if trip(x) { panic!("p"); } a + x }));
}
"#,
        FOLD_REFUSED,
    ),
    unwinding_low(
        "unwind_into_iter_map_sum",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().map(|x| { if trip(x) { panic!("p"); } x * 2 }).sum::<u64>());
}
"#,
        SUM_REFUSED,
    ),
    unwinding_low(
        "unwind_into_iter_map_last",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().map(|x| { if trip(x) { panic!("p"); } x ^ 7 }).last().unwrap_or(0));
}
"#,
        FOLD_REFUSED,
    ),
    unwinding(
        "unwind_into_iter_filter_count",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().filter(|x| { if trip(*x) { panic!("p"); } *x % 20 == 0 }).count() as u64);
}
"#,
    ),
    unwinding(
        "unwind_into_iter_map_max",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().map(|x| { if trip(x) { panic!("p"); } x ^ 7 }).max().unwrap_or(0));
}
"#,
    ),
    unwinding(
        "unwind_into_iter_skip_fold",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().skip(2).fold(0u64, |a, x| { if trip(x) { panic!("p"); } a + x }));
}
"#,
    ),
    unwinding(
        "unwind_into_iter_take_map_sum",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().take(6).map(|x| { if trip(x) { panic!("p"); } x }).sum::<u64>());
}
"#,
    ),
    unwinding_low(
        "unwind_into_iter_rev_for_each",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    let mut s = 0u64;
    v.into_iter().rev().for_each(|x| { if trip(x) { panic!("p"); } s += x; });
    out(s);
}
"#,
        RFOLD_REFUSED,
    ),
    // std collects in place: the source buffer becomes the result, freed once.
    unwinding_low(
        "unwind_into_iter_collect_in_place",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    let w: Vec<u64> = v.into_iter().map(|x| { if trip(x) { panic!("p"); } x + 1 }).collect();
    out(w.len() as u64);
}
"#,
        COLLECT_SRET_REFUSED,
    ),
    // The result has a buffer of its own: both are freed.
    unwinding_low(
        "unwind_into_iter_collect_fresh_buffer",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    let w: Vec<u32> = v.into_iter().map(|x| { if trip(x) { panic!("p"); } x as u32 }).collect();
    out(w.len() as u64);
}
"#,
        COLLECT_SRET_REFUSED,
    ),
    // The extended `Vec` stays the caller's to drop; the iterator is extend's.
    unwinding_low(
        "unwind_into_iter_extend",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    let mut w: Vec<u64> = Vec::with_capacity(16);
    w.extend(v.into_iter().map(|x| { if trip(x) { panic!("p"); } x + 1 }));
    out(w.len() as u64);
}
"#,
        EXTEND_TRUSTED_REFUSED,
    ),
    // A destination that must grow: `extend_trusted` reserves the iterator's
    // exact length before pulling anything (`max(2 * cap, len + n,
    // MIN_NON_ZERO_CAP)`), and the unwind finds that capacity and the
    // elements written so far.
    unwinding_low(
        "unwind_into_iter_extend_reserves_before_the_drive",
        r#"struct Cap(*const Vec<u64>);
impl Drop for Cap { fn drop(&mut self) { unsafe { note((*self.0).len(), (*self.0).capacity()); } } }
fn main() {
    let _n = Notes;
    let _r = Rep;
    let v = make(8);
    let mut w: Vec<u64> = Vec::with_capacity(2);
    w.push(9);
    let _c = Cap(&w);
    w.extend(v.into_iter().map(|x| { if trip(x) { panic!("p"); } x + 1 }));
    out(w.len() as u64);
}
"#,
        EXTEND_TRUSTED_REFUSED,
    ),
    // `skip` over the owning iterator is not `TrustedLen`: `extend_desugared`
    // reserves `size_hint().0 + 1` when the destination is full.
    unwinding_low(
        "unwind_into_iter_extend_reserves_when_full",
        r#"struct Cap(*const Vec<u64>);
impl Drop for Cap { fn drop(&mut self) { unsafe { note((*self.0).len(), (*self.0).capacity()); } } }
fn main() {
    let _n = Notes;
    let _r = Rep;
    let v = make(8);
    let mut w: Vec<u64> = Vec::with_capacity(2);
    w.push(9);
    let _c = Cap(&w);
    w.extend(v.into_iter().skip(1).map(|x| { if trip(x) { panic!("p"); } x + 1 }));
    out(w.len() as u64);
}
"#,
        EXTEND_DESUGARED_REFUSED,
    ),
    // A final length `len + n` past `usize::MAX`: `extend_trusted`'s
    // `reserve(n)` raises capacity overflow before anything is pulled, so the
    // unwind finds the destination as it was (`len*1000+cap=1002`). A
    // reservation that wrapped to a length the Vec already holds would let the
    // drive push until the payload panics at 50.
    unwinding_low(
        "unwind_extend_trusted_final_length_past_usize_max",
        r#"struct Cap(*const Vec<u64>);
impl Drop for Cap { fn drop(&mut self) { unsafe { note((*self.0).len(), (*self.0).capacity()); } } }
fn main() {
    let _n = Notes;
    let _r = Rep;
    mark();
    let mut w: Vec<u64> = Vec::with_capacity(2);
    w.push(9);
    let _c = Cap(&w);
    let end = std::hint::black_box(usize::MAX);
    w.extend((0..end).map(|x| { if trip(x as u64) { panic!("p"); } x as u64 }));
    out(w.len() as u64);
}
"#,
        EXTEND_TRUSTED_REFUSED,
    ),
    // The same past a full destination for a chain that is not `TrustedLen`:
    // `extend_desugared` pulls the first element, then reserves
    // `size_hint().0 + 1`, which overflows `len + additional`.
    unwinding_low(
        "unwind_extend_desugared_final_length_past_usize_max",
        r#"struct Cap(*const Vec<u64>);
impl Drop for Cap { fn drop(&mut self) { unsafe { note((*self.0).len(), (*self.0).capacity()); } } }
fn main() {
    let _n = Notes;
    let _r = Rep;
    mark();
    let mut w: Vec<u64> = Vec::with_capacity(2);
    w.push(9);
    w.push(8);
    let _c = Cap(&w);
    let end = std::hint::black_box(usize::MAX);
    w.extend((1..end).inspect(|_| {}).map(|x| { if trip(x as u64) { panic!("p"); } x as u64 }));
    out(w.len() as u64);
}
"#,
        EXTEND_DESUGARED_REFUSED,
    ),
    // A bare `Range` source, which the bridge extends by a count-up fill
    // rather than the chain drive: `extend_trusted` reserves the range's
    // length, and `i64::MIN..i64::MAX` holds `2^64 - 1` elements, so
    // `len + additional` passes `usize::MAX` and std raises capacity overflow
    // with the destination untouched (`len*1000+cap=1002`; under
    // `panic=abort` the raise aborts).
    both_low(
        "extend_range_final_length_past_usize_max",
        r#"struct Cap(*const Vec<i64>);
impl Drop for Cap { fn drop(&mut self) { unsafe { note((*self.0).len(), (*self.0).capacity()); } } }
fn main() {
    let _n = Notes;
    let _r = Rep;
    mark();
    let mut w: Vec<i64> = Vec::with_capacity(2);
    w.push(9);
    let _c = Cap(&w);
    let lo = std::hint::black_box(i64::MIN);
    let hi = std::hint::black_box(i64::MAX);
    w.extend(lo..hi);
    out(w.len() as u64);
}
"#,
        EXTEND_TRUSTED_REFUSED,
    ),
    // `-1..i64::MAX` holds `2^63` elements: `len + additional` fits in
    // `usize`, but `2^63` eight-byte elements pass `isize::MAX` bytes, which
    // std's layout check reports as the same capacity overflow.
    both_low(
        "extend_range_byte_size_past_isize_max",
        r#"struct Cap(*const Vec<i64>);
impl Drop for Cap { fn drop(&mut self) { unsafe { note((*self.0).len(), (*self.0).capacity()); } } }
fn main() {
    let _n = Notes;
    let _r = Rep;
    mark();
    let mut w: Vec<i64> = Vec::with_capacity(2);
    w.push(9);
    let _c = Cap(&w);
    let lo = std::hint::black_box(-1i64);
    let hi = std::hint::black_box(i64::MAX);
    w.extend(lo..hi);
    out(w.len() as u64);
}
"#,
        EXTEND_TRUSTED_REFUSED,
    ),
    // The same raise from an unsigned 64-bit range, whose span is compared
    // and counted unsigned: `0..u64::MAX` holds `2^64 - 1` elements, so
    // `len + additional` passes `usize::MAX`.
    both_low(
        "extend_range_u64_final_length_past_usize_max",
        r#"struct Cap(*const Vec<u64>);
impl Drop for Cap { fn drop(&mut self) { unsafe { note((*self.0).len(), (*self.0).capacity()); } } }
fn main() {
    let _n = Notes;
    let _r = Rep;
    mark();
    let mut w: Vec<u64> = Vec::with_capacity(2);
    w.push(9);
    let _c = Cap(&w);
    let lo = std::hint::black_box(0u64);
    let hi = std::hint::black_box(u64::MAX);
    w.extend(lo..hi);
    out(w.len() as u64);
}
"#,
        EXTEND_TRUSTED_REFUSED,
    ),
    // `0..2^62` over `usize`: `len + additional` fits in `usize`, but
    // `2^62 + 1` eight-byte elements pass `isize::MAX` bytes.
    both_low(
        "extend_range_usize_byte_size_past_isize_max",
        r#"struct Cap(*const Vec<usize>);
impl Drop for Cap { fn drop(&mut self) { unsafe { note((*self.0).len(), (*self.0).capacity()); } } }
fn main() {
    let _n = Notes;
    let _r = Rep;
    mark();
    let mut w: Vec<usize> = Vec::with_capacity(2);
    w.push(9);
    let _c = Cap(&w);
    let lo = std::hint::black_box(0usize);
    let hi = std::hint::black_box(1usize << 62);
    w.extend(lo..hi);
    out(w.len() as u64);
}
"#,
        EXTEND_TRUSTED_REFUSED,
    ),
    // The terminal call's own unwind action is `Continue`: the frame has no
    // cleanup of its own.
    unwinding_low(
        "unwind_into_iter_from_cleanup_free_frame",
        r#"#[inline(never)]
fn drive(v: Vec<u64>) -> u64 { v.into_iter().map(|x| { if trip(x) { panic!("p"); } x * 3 }).sum() }
fn main() {
    let _r = Rep;
    let v = make(8);
    out(drive(v));
}
"#,
        SUM_REFUSED,
    ),
    // A first drive in the same frame finished normally and freed its buffer.
    unwinding_low(
        "unwind_into_iter_second_drive_in_frame",
        r#"#[inline(never)]
fn drives(v: Vec<u64>, w: Vec<u64>) -> u64 {
    let a: u64 = v.into_iter().map(|x| x + 1).sum();
    let b: u64 = w.into_iter().map(|x| { if trip(x) { panic!("p"); } x * 3 }).sum();
    a + b
}
fn main() {
    let _r = Rep;
    let v = make(4);
    let w = make(8);
    out(drives(v, w));
}
"#,
        SUM_REFUSED,
    ),
    // A frame that cannot unwind aborts; the buffer (104 bytes) is freed first.
    unwinding_low(
        "unwind_into_iter_in_nounwind_frame",
        r#"#[inline(never)]
extern "C" fn drive(v: Vec<u64>) {
    v.into_iter().for_each(|x| { if trip(x) { panic!("p"); } });
}
fn main() {
    let v = make(13);
    TRACE_SIZE.store(13 * 8, Relaxed);
    drive(v);
    out(1);
}
"#,
        FOLD_REFUSED,
    ),
    unwinding(
        "unwind_into_iter_any_control",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().any(|x| { if trip(x) { panic!("p"); } x == 1000 }) as u64);
}
"#,
    ),
    unwinding(
        "unwind_into_iter_find_control",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    out(v.into_iter().find(|x| { if trip(*x) { panic!("p"); } *x == 1000 }).unwrap_or(0));
}
"#,
    ),
    unwinding(
        "unwind_into_iter_for_loop_control",
        r#"fn main() {
    let _r = Rep;
    let v = make(8);
    let mut s = 0u64;
    for x in v { if trip(x) { panic!("p"); } s += x; }
    out(s);
}
"#,
    ),
];

/// `Sum`'s and `Product`'s checked arithmetic panics on overflow inside the
/// drive (`-Coverflow-checks=on`). The panic reports the location of core's
/// own check (its `|a, b| a + b` closure in `accum.rs`), never the reduction's
/// call, also inside a `#[track_caller]` frame; `show_panic_location` writes it.
const INTO_ITER_CHECKED_CASES: &[Case] = &[
    unwinding_low(
        "unwind_into_iter_sum_overflow",
        r#"fn main() {
    let _r = Rep;
    let mut v: Vec<u64> = Vec::with_capacity(8);
    for i in 1..=8u64 { v.push(if i == 5 { std::hint::black_box(u64::MAX - 5) } else { i }); }
    mark();
    out(v.into_iter().map(|x| x + 0).sum::<u64>());
}
"#,
        SUM_REFUSED,
    ),
    both_low(
        "checked_into_iter_sum_overflow_location",
        r#"fn main() {
    show_panic_location();
    let _r = Rep;
    let mut v: Vec<u64> = Vec::with_capacity(8);
    for i in 1..=8u64 { v.push(if i == 5 { std::hint::black_box(u64::MAX - 5) } else { i }); }
    mark();
    out(v.into_iter().map(|x| x + 0).sum::<u64>());
}
"#,
        SUM_REFUSED,
    ),
    Case {
        name: "checked_slice_product_overflow_location_in_track_caller_frame",
        body: r#"#[track_caller]
#[inline(never)]
fn total(v: &[u64]) -> u64 { v.iter().product() }
fn main() {
    show_panic_location();
    let _r = Rep;
    let v = make(30);
    out(total(&v));
}
"#,
        abort: Some(MATCH4),
        unwind: Some(MATCH4),
    },
    // A frame that cannot unwind: the location, then the buffer (32 bytes)
    // freed, then the abort's own panic.
    both_low(
        "checked_into_iter_sum_overflow_location_in_nounwind_frame",
        r#"#[inline(never)]
extern "C" fn total(v: Vec<u64>) -> u64 { v.into_iter().map(|x| x + 0).sum() }
fn main() {
    show_panic_location();
    let mut v: Vec<u64> = Vec::with_capacity(4);
    for i in 1..=4u64 { v.push(if i == 3 { std::hint::black_box(u64::MAX - 1) } else { i }); }
    TRACE_SIZE.store(4 * 8, Relaxed);
    mark();
    out(total(v));
}
"#,
        SUM_REFUSED,
    ),
    Case {
        name: "checked_range_sum_overflow_location_every_level",
        body: r#"fn main() {
    show_panic_location();
    let _r = Rep;
    mark();
    let n = std::hint::black_box(40u8);
    out((0..n).map(|x| x * 1).sum::<u8>() as u64);
}
"#,
        abort: Some(MATCH4),
        unwind: Some(MATCH4),
    },
];

/// No payload panics: each terminal frees its buffer once on its normal exit,
/// under both strategies (the unwind pad is never entered), and each `extend`
/// leaves the capacity std's `SpecExtend` reserves (`note`).
const INTO_ITER_CONTROL_CASES: &[Case] = &[
    both(
        "control_into_iter_terminals_every_level",
        r#"#[inline(never)]
fn count() -> u64 { fresh(8).into_iter().filter(|x| *x % 20 == 0).count() as u64 }
#[inline(never)]
fn max() -> u64 { fresh(8).into_iter().map(|x| x ^ 7).max().unwrap_or(0) }
#[inline(never)]
fn skip_fold() -> u64 { fresh(8).into_iter().skip(2).fold(0u64, |a, x| a + x) }
#[inline(never)]
fn take_sum() -> u64 { fresh(8).into_iter().take(6).map(|x| x * 3).sum() }
fn main() {
    let _r = Rep;
    mark();
    out(count() + max() + skip_fold() + take_sum());
}
"#,
    ),
    Case {
        name: "control_into_iter_terminals_low_levels",
        body: r#"#[inline(never)]
fn for_each() -> u64 { let mut s = 0u64; fresh(8).into_iter().for_each(|x| s += x); s }
#[inline(never)]
fn fold() -> u64 { fresh(8).into_iter().fold(0u64, |a, x| a * 3 + x) }
#[inline(never)]
fn map_sum() -> u64 { fresh(8).into_iter().map(|x| x * 2).sum() }
#[inline(never)]
fn collect() -> u64 { let w: Vec<u32> = fresh(8).into_iter().map(|x| x as u32).collect(); w.len() as u64 + w[3] as u64 }
#[inline(never)]
fn extend() -> u64 { let mut w: Vec<u64> = Vec::with_capacity(16); w.extend(fresh(8).into_iter().map(|x| x + 1)); w.len() as u64 + w[7] }
fn main() {
    let _r = Rep;
    mark();
    out(for_each() + fold() + map_sum() + collect() + extend());
}
"#,
        abort: Some(low_levels(CONTROL_LOW_LEVELS_REFUSED)),
        unwind: Some(low_levels(CONTROL_LOW_LEVELS_REFUSED)),
    },
    // `TrustedLen` sources reserve `n` before the drive: an owning iterator
    // into an empty and into a short destination, a `u8` range twice, a
    // slice's `take` and `skip`; the owning iterator itself into a full
    // destination (`SpecExtend<T, vec::IntoIter<T>>`, `reserve(n)` too).
    both_low(
        "control_extend_trusted_len_reserves",
        r#"fn show(w: &Vec<u64>) { note(w.len(), w.capacity()); }
#[inline(never)]
fn into_empty() { let mut w: Vec<u64> = Vec::new(); w.extend(fresh(8).into_iter().map(|x| x + 1)); show(&w); }
#[inline(never)]
fn into_short() { let mut w: Vec<u64> = Vec::with_capacity(3); w.push(1); w.extend(fresh(8).into_iter().map(|x| x + 1)); show(&w); }
#[inline(never)]
fn range_u8_twice() {
    let mut w: Vec<u8> = Vec::new();
    w.extend((0..11u8).map(|x| x * 2));
    w.extend((0..3u8).map(|x| x + 100));
    note(w.len(), w.capacity());
    out(w[13] as u64);
}
#[inline(never)]
fn slice_take() { let s = fresh(11); let mut w: Vec<u64> = vec![1, 2, 3]; w.extend(s.iter().take(7).copied()); show(&w); }
#[inline(never)]
fn slice_skip() { let s = fresh(9); let mut w: Vec<u64> = Vec::with_capacity(2); w.push(5); w.extend(s.iter().skip(3)); show(&w); }
#[inline(never)]
fn into_full() { let mut w: Vec<u64> = Vec::with_capacity(4); for i in 1..=4u64 { w.push(i); } w.extend(fresh(5).into_iter()); show(&w); }
fn main() {
    let _n = Notes;
    let _r = Rep;
    mark();
    into_empty();
    into_short();
    range_u8_twice();
    slice_take();
    slice_skip();
    into_full();
}
"#,
        Want::Refuse("TCG-MIR-UNSUPPORTED", &[EXTEND_TRUSTED, SPEC_EXTEND]),
    ),
    // Other sources reserve when the destination is full: `size_hint().0 + 1`
    // (`skip` over an owning iterator, `inspect`; `filter`'s zero lower bound
    // grows as a push does).
    both_low(
        "control_extend_desugared_reserves",
        r#"fn show(w: &Vec<u64>) { note(w.len(), w.capacity()); }
#[inline(never)]
fn skip_into_empty() { let mut w: Vec<u64> = Vec::new(); w.extend(fresh(8).into_iter().skip(2).map(|x| x + 1)); show(&w); }
#[inline(never)]
fn skip_into_short() { let mut w: Vec<u64> = Vec::with_capacity(3); w.push(1); w.push(2); w.extend(fresh(11).into_iter().skip(1)); show(&w); }
#[inline(never)]
fn inspect() { let mut n = 0u64; let mut w: Vec<u64> = Vec::with_capacity(5); w.push(7); w.extend((0..9u64).inspect(|_| n += 1).map(|x| x * 3)); show(&w); out(n); }
#[inline(never)]
fn filter() { let mut w: Vec<u64> = Vec::with_capacity(3); w.push(1); w.extend(fresh(11).into_iter().filter(|x| x % 20 != 0)); show(&w); }
fn main() {
    let _n = Notes;
    let _r = Rep;
    mark();
    skip_into_empty();
    skip_into_short();
    inspect();
    filter();
}
"#,
        EXTEND_DESUGARED_REFUSED,
    ),
];

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

enum Built {
    Ran(Ending),
    Refused(String),
}

/// What every guest of a group is built from: the prelude its body follows and
/// the `-Coverflow-checks` setting.
struct Guests {
    prelude: &'static str,
    overflow_checks: bool,
}

/// The in-place `Vec` model guests.
const COMPACT_GUESTS: Guests = Guests {
    prelude: PRELUDE,
    overflow_checks: false,
};

fn compile(
    dir: &Path,
    stem: &str,
    src: &Path,
    strategy: &str,
    opt: u32,
    overflow_checks: bool,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let bin = dir.join(stem);
    let mut cmd = toolchain_support::rustc_command_with_edition("2021");
    cmd.args([
        "--target",
        TARGET,
        "--crate-type",
        "bin",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Cpanic={strategy}"))
    .arg(if overflow_checks {
        "-Coverflow-checks=on"
    } else {
        "-Coverflow-checks=off"
    })
    .arg(format!("-Copt-level={opt}"));
    if let Some(dylib) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(dylib);
        cmd.arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(src);
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(bin)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn run(bin: &Path) -> Ending {
    let mut child = Command::new(bin)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("run the compiled guest");
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("poll the guest") {
            break status;
        }
        if start.elapsed() > RUN_TIMEOUT {
            let _ = child.kill();
            break child.wait().expect("reap the guest");
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let mut stdout = String::new();
    if let Some(mut pipe) = child.stdout.take() {
        use std::io::Read;
        let _ = pipe.read_to_string(&mut stdout);
    }
    Ending {
        code: status.code(),
        signal: status.signal(),
        stdout,
    }
}

/// The bridge's named refusal codes in a failed compile's stderr, or `None`
/// when it failed without one (a crash is never a refusal).
fn refusal_codes(stderr: &str) -> Option<Vec<String>> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let mut codes = Vec::new();
    let mut rest = stderr;
    while let Some(start) = rest.find("[TCG-") {
        let tail = &rest[start + 1..];
        let end = tail.find(']')?;
        codes.push(tail[..end].to_owned());
        rest = &tail[end..];
    }
    (!codes.is_empty()).then_some(codes)
}

/// The per-function reasons of a refusal: the `- symbol: reason` lines the
/// bridge lists under `cannot compile required function`.
fn refused_functions(stderr: &str) -> impl Iterator<Item = &str> {
    stderr
        .lines()
        .map(str::trim_start)
        .filter(|line| line.starts_with("- "))
}

struct Cell<'a> {
    case: &'a Case,
    strategy: &'static str,
    level: usize,
    want: Want,
}

#[derive(Default)]
struct Tally {
    cells: usize,
    matched: usize,
    refused: usize,
    failures: Vec<String>,
}

fn run_cells(group: &str, cases: &[Case]) -> Tally {
    run_guest_cells(group, &COMPACT_GUESTS, cases)
}

fn run_guest_cells(group: &str, guests: &Guests, cases: &[Case]) -> Tally {
    let backend = backend_artifact_support::current_test_backend();
    let root = std::env::temp_dir().join(format!("tcg_vec_compact_{group}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).expect("create the work directory");
    let mut cells = Vec::new();
    for case in cases {
        for (strategy, wants) in [("abort", case.abort), ("unwind", case.unwind)] {
            if let Some(wants) = wants {
                for (level, want) in wants.into_iter().enumerate() {
                    cells.push(Cell {
                        case,
                        strategy,
                        level,
                        want,
                    });
                }
            }
        }
    }
    let next = AtomicUsize::new(0);
    let tally = Mutex::new(Tally::default());
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get().clamp(2, 8));
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(cell) = cells.get(index) else { break };
                    let verdict = judge(&root, guests, cell, &backend);
                    let mut tally = tally.lock().expect("tally lock");
                    tally.cells += 1;
                    match verdict {
                        Ok(Some(())) => tally.matched += 1,
                        Ok(None) => tally.refused += 1,
                        Err(failure) => tally.failures.push(failure),
                    }
                }
            });
        }
    });
    let _ = std::fs::remove_dir_all(&root);
    let mut tally = tally.into_inner().expect("tally lock");
    tally.failures.sort();
    tally
}

/// `Ok(Some(()))` for a matching run, `Ok(None)` for the expected refusal.
fn judge(
    root: &Path,
    guests: &Guests,
    cell: &Cell<'_>,
    backend: &Path,
) -> Result<Option<()>, String> {
    let opt = LEVELS[cell.level];
    let label = format!("{} -Cpanic={} -O{opt}", cell.case.name, cell.strategy);
    let dir = root.join(format!("{}_{}_{opt}", cell.case.name, cell.strategy));
    std::fs::create_dir_all(&dir).expect("create the cell directory");
    let src = dir.join("guest.rs");
    std::fs::write(&src, format!("{}{}", guests.prelude, cell.case.body)).expect("write the guest");
    let checks = guests.overflow_checks;
    let oracle = compile(&dir, "llvm", &src, cell.strategy, opt, checks, None)
        .map(|bin| run(&bin))
        .unwrap_or_else(|stderr| panic!("{label}: the LLVM oracle failed to compile:\n{stderr}"));
    let bridge = match compile(
        &dir,
        "bridge",
        &src,
        cell.strategy,
        opt,
        checks,
        Some(backend),
    ) {
        Ok(bin) => Built::Ran(run(&bin)),
        Err(stderr) => Built::Refused(stderr),
    };
    match (cell.want, bridge) {
        (Want::Match, Built::Ran(ending)) if ending == oracle => Ok(Some(())),
        (Want::Match, Built::Ran(ending)) => Err(format!(
            "{label}: compiled and DIVERGES — LLVM {oracle:?}, trust-cg {ending:?}"
        )),
        (Want::Match, Built::Refused(stderr)) => Err(format!(
            "{label}: refused a cell that must compile and match: {:?}",
            refusal_codes(&stderr).unwrap_or_default()
        )),
        (Want::Refuse(code, reasons), Built::Refused(stderr)) => match refusal_codes(&stderr) {
            Some(codes) if codes.iter().any(|c| c == code) => {
                let tag = format!("[{code}]");
                let missing: Vec<&str> = reasons
                    .iter()
                    .copied()
                    .filter(|reason| !stderr.contains(reason))
                    .collect();
                let unpinned: Vec<&str> = refused_functions(&stderr)
                    .filter(|line| {
                        !line.contains(&tag) && !reasons.iter().any(|reason| line.contains(reason))
                    })
                    .collect();
                if missing.is_empty() && unpinned.is_empty() {
                    Ok(None)
                } else {
                    Err(format!(
                        "{label}: refused with [{code}], but without {missing:?}, or for \
                         other reasons: {unpinned:?}"
                    ))
                }
            }
            Some(codes) => Err(format!("{label}: refused with {codes:?}, not [{code}]")),
            None => Err(format!(
                "{label}: failed WITHOUT a named refusal:\n{stderr}"
            )),
        },
        (Want::Refuse(code, _), Built::Ran(ending)) => Err(format!(
            "{label}: compiled where it must refuse [{code}] (LLVM {oracle:?}, trust-cg {ending:?})"
        )),
    }
}

fn require_clean(group: &str, tally: &Tally) {
    assert!(
        tally.failures.is_empty(),
        "{group}: {} of {} cell(s) failed:\n  {}",
        tally.failures.len(),
        tally.cells,
        tally.failures.join("\n  ")
    );
}

#[test]
fn vec_models_destroy_removed_elements_and_call_key_eq_like_llvm_aarch64() {
    darwin_native::require("vec_compact_user_trait_differential_aarch64", &[]);
    let tally = run_cells("destruction", DESTRUCTION_CASES);
    require_clean("destruction", &tally);
    eprintln!(
        "VEC_COMPACT_DESTRUCTION cases={} cells={} matched={} refused={} opts=0,1,2,3 \
         strategies=abort,unwind",
        DESTRUCTION_CASES.len(),
        tally.cells,
        tally.matched,
        tally.refused
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn vec_models_repair_the_vec_when_a_closure_or_drop_unwinds_aarch64() {
    darwin_native::require("vec_compact_user_trait_differential_aarch64", &[]);
    let tally = run_cells("unwind", UNWIND_CASES);
    require_clean("unwind", &tally);
    eprintln!(
        "VEC_COMPACT_UNWIND cases={} cells={} matched={} opts=0,1,2,3 strategies=unwind",
        UNWIND_CASES.len(),
        tally.cells,
        tally.matched
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn vec_models_still_compile_primitive_and_derived_elements_aarch64() {
    darwin_native::require("vec_compact_user_trait_differential_aarch64", &[]);
    let tally = run_cells("controls", CONTROL_CASES);
    require_clean("controls", &tally);
    eprintln!(
        "VEC_COMPACT_CONTROLS cases={} cells={} matched={} opts=0,1,2,3 strategies=abort,unwind",
        CONTROL_CASES.len(),
        tally.cells,
        tally.matched
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn vec_models_refuse_unlowered_drops_by_name_aarch64() {
    darwin_native::require("vec_compact_user_trait_differential_aarch64", &[]);
    let tally = run_cells("refusals", REFUSAL_CASES);
    require_clean("refusals", &tally);
    eprintln!(
        "VEC_COMPACT_REFUSALS cases={} cells={} refused={} opts=0,1,2,3 strategies=abort,unwind",
        REFUSAL_CASES.len(),
        tally.cells,
        tally.refused
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn vec_into_iter_terminals_free_the_buffer_when_a_payload_unwinds_aarch64() {
    darwin_native::require("vec_compact_user_trait_differential_aarch64", &[]);
    let groups = [
        (
            "into_iter_unwind",
            &INTO_ITER_GUESTS,
            INTO_ITER_UNWIND_CASES,
        ),
        (
            "into_iter_checked",
            &INTO_ITER_CHECKED_GUESTS,
            INTO_ITER_CHECKED_CASES,
        ),
        (
            "into_iter_controls",
            &INTO_ITER_GUESTS,
            INTO_ITER_CONTROL_CASES,
        ),
    ];
    let mut total = Tally::default();
    for (group, guests, cases) in groups {
        let tally = run_guest_cells(group, guests, cases);
        total.cells += tally.cells;
        total.matched += tally.matched;
        total.refused += tally.refused;
        total.failures.extend(tally.failures);
    }
    require_clean("into_iter", &total);
    eprintln!(
        "VEC_INTO_ITER_UNWIND cases={} cells={} matched={} refused={} opts=0,1,2,3 \
         strategies=abort,unwind",
        INTO_ITER_UNWIND_CASES.len()
            + INTO_ITER_CHECKED_CASES.len()
            + INTO_ITER_CONTROL_CASES.len(),
        total.cells,
        total.matched,
        total.refused
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
