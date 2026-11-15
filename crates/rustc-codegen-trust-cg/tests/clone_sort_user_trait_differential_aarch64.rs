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

// The bridge's `vec![x; n]`, `.cloned()` and slice-sort models against the
// user code std runs inside them: a hand-written `Clone`, a `Cell`'s clone, an
// unsigned element order, a key closure with effects. Each guest is compiled by LLVM (the oracle) and by the
// bridge at -O0..-O3 under the panic strategies its row names, and the bridge
// must either build a binary whose exit code, signal, stdout and stderr equal
// LLVM's, or refuse with the exact `[TCG-...]` code the row names for that
// level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// MEASURED before the fix (origin/main 33eefbf58, Trust pack 9192, no-proof-certs,
// `-Coverflow-checks=off` unless the row says otherwise):
//
//   * `from_elem_*`: the struct-element `vec![x; n]` broadcast the prototype's
//     image and never called the user `clone` (e.g. `r=11100` against LLVM's
//     `r=12202` at O0-O3; a `clone` that panics on its second call never
//     panicked). Every row compiled and diverged at O0/O1, and at O2/O3 unless
//     another gate refused first.
//   * `sort_u64_*`, `sort_stable_all_widths`: `<[u64]>::sort` / `sort_unstable`
//     (and `usize`) put values `>= 2^63` first at O0/O1: the insertion-sort
//     helper compared with a signed `Sgt` after a zero-extension that is a no-op
//     at 64 bits.
//   * `by_key_*`, `unstable_by_key_*`: `sort_by_key` / `sort_unstable_by_key`
//     called a key closure with effects a different number of times and in
//     another order (14 against 11 calls; a call-count-dependent key sorted to
//     `6143289` against `4631829`); `sort_unstable_by_key` over 40 elements
//     ordered distinct elements with equal keys differently from std's ipnsort.
//     All at O0..O3.
//   * `cached_key_*`: `sort_by_cached_key` called its key on every comparison
//     (17 against 6 calls), so a key reading its own call count sorted wrong,
//     and never made std's one `(key, index)` allocation. All at O0..O3.
//
// HISTORICAL FIRST FIX (529ace6eb). A `vec![x; n]` image broadcast requires `clone_is_bitwise_copy`
// (`[TCG-FROM-ELEM-CLONE]` otherwise); the sort helper compares unsigned
// elements with `Ugt`; `sort_by_key` keeps its model only for a pure key
// (`[TCG-SORT-KEY-EFFECT]`), and `sort_unstable_by_key` only for a pure,
// injective one, declining any other so std's own body sorts (those rows match
// LLVM at O0..O3); `sort_by_cached_key` has an exact model
// (one allocation of std's pair layout, one key call per element in index
// order) and refuses a key that may unwind under `panic=unwind`
// (`[TCG-SORT-KEY-UNWIND]`). The control rows keep each model on primitive
// elements and keys and on derived clones.
//
// SECOND ROUND, measured at the first fix 529ace6eb (same toolchain):
//
//   * `by_key_two_overflow_sites`, `by_key_two_division_sites`: a pure key
//     with two kept panic sites under `panic=abort` built and aborted at the
//     model's first site, not LLVM's (`:8:62` against `:8:39`), O0..O3:
//     529ace6eb admitted any number of constant-message checks. A key may now
//     keep ONE site; a check in a `#[track_caller]` callee counts once per call
//     reaching it. `by_key_track_caller_site` (one check in such a callee
//     reached from two calls) diverged the same way; `by_key_one_panic_site_control`
//     and `by_key_track_caller_one_call_control` keep the model, and
//     `by_key_two_sites_abs` (split out of `by_key_pure_controls_overflow_checks`,
//     which matched at 529ace6eb because no element overflows) now refuses.
//   * `by_key_union_address` (O0..O3), `by_key_array_pointer_address`
//     (O1..O3) and `by_key_raw_parts_address` (O2/O3): a key that reads its
//     argument's address through a union, a pointer cast or a raw slice pointer
//     sorted by where the model keys the insertee (in place) instead of std (a
//     stack copy): `h=123579` against `h=271359`. At the other levels 529ace6eb
//     already refused them for another construct.
//   * `unstable_by_key_arg_reassign*`: a key that reassigns its argument passed
//     the injectivity check, and the 30/40-element unstable sort ordered its
//     ties as the stable model, not as ipnsort, O0..O3. Such a key now steps
//     aside to std's own body.
//   * `from_elem_copy_self_clones`: 529ace6eb refused (`[TCG-FROM-ELEM-CLONE]`)
//     a derived-`Copy` element whose field has a hand-written `clone` std never
//     calls; 33eefbf58 compiled it and matched. `from_elem_copy_tuple_user_field`
//     refuses before and after: a tuple's clone calls its fields' `clone`.
//   * `by_key_argsort_bounds`, `by_key_debug_profile` (unwind): EVIDENCE
//     BOUNDARY rows. Each refuses with `[TCG-SORT-KEY-EFFECT]` although std
//     runs it (LIMITATIONS.md says why); they pin the refusal, not a fix.
//
// CURRENT CACHED-KEY ROUTE (2026-10-09): the cached-key interception is retired.
// The compiler lowers std's ordinary sort body, preserving its callback and
// cleanup edges. The order-log row must execute and match under unwind too;
// a separate forced-panic row checks the real callback prefix and deallocation
// of the cache allocation before unwind reaches a caller's Drop. This does not
// qualify catching inside a compiled frame or nonprimitive key destructors.
//
// CELL CLONES. `clone_is_bitwise_copy` admits core's `Cell<T>` when `T`'s own
// clone is bitwise: `Cell::clone` is `Cell::new(self.get())`, a typed copy of
// `T` that calls nothing, so the `.cloned()` drive loads the element and
// `vec![x; n]` broadcasts an image whose derived clone reaches it. MEASURED
// before that admission (origin/main b53f9641f, same toolchain): every
// `.cloned()` over `Cell<u32>` / `Cell<i64>` / `Cell<u8|i16|f64|bool>` / a
// derived newtype over one refused at O0..O3 under both strategies
// (`[TCG-ITER-UNMODELED]`, core's real `Cloned` bodies), and
// `from_elem_cell_field` refused (`[TCG-FROM-ELEM-CLONE]`); LLVM ran each.
// The `Match` rows of `cell_clone_rows` now build and match LLVM, including a
// slice written through its `Cell`s while the drive clones it, before the
// clone, and a closure that panics after it. The controls keep refusing: a
// `Cell` over a hand-written `clone`, `RefCell`, `OnceCell`, a local type
// named `Cell`, and `vec![x; n]` over such a `Cell` field. The EVIDENCE
// BOUNDARY rows pin refusals of other constructs the Cell guests reach.
//
// WRITES THROUGH `&clone`. A `Cell` clone is a by-value `!Freeze` item, and a
// closure handed `&Cell` may `set` it. MEASURED at that admission (4e37279d5,
// same toolchain): the `filter` / `take_while` / `skip_while` / `inspect`
// drives and the `find` / `*_by_key` / `min_by` / `max_by` terminals handed
// the closure a stack copy and went on with the value they had stored, so the
// write was lost. `cloned_cell_filter_writes_clone` printed `total=7` against
// LLVM's `total=70` at O0..O3. `cloned_cell_by_key_writes_clone` printed
// `a=9 b=1` against `a=16 b=2` at O0..O3, and the widths row diverged at
// O0..O3. `find` returned the unwritten clone at O0/O1 (`f=2` against `f=6`),
// where b53f9641f had left it to core's real bodies and matched. `inspect`
// lost its writes at O0/O1 (`total=10` against `total=410`), and `max_by`
// / `min_by` lost theirs at O0/O1. `map_to_cell_filter_writes_item`, a `map`
// that returns a fresh `Cell`, already diverged on b53f9641f (`total=10`
// against `total=100`, O0..O3). Each drive now reloads a by-value `!Freeze`
// scalar item from the slot it passed (`shared_ref_item_reload`). Such a
// tuple item refuses by name (`[TCG-ITER-INTERIOR-MUT-ITEM]`).
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Strategy {
    Abort,
    Unwind,
}

impl Strategy {
    fn flag(self) -> &'static str {
        match self {
            Strategy::Abort => "-Cpanic=abort",
            Strategy::Unwind => "-Cpanic=unwind",
        }
    }
    fn label(self) -> &'static str {
        match self {
            Strategy::Abort => "abort",
            Strategy::Unwind => "unwind",
        }
    }
}

/// What the bridge must do with one row at one level.
#[derive(Clone, Copy, Debug)]
enum Expect {
    /// Build, and run exactly as LLVM's binary does.
    Match,
    /// Refuse, with this bracketed code (and this text, when not empty) in the
    /// compiler's stderr.
    Refuse(&'static str, &'static str),
}

use Expect::{Match, Refuse};

const M4: [Expect; 4] = [Match, Match, Match, Match];

struct Row {
    name: &'static str,
    src: &'static str,
    /// The expectation per strategy, at -O0..-O3.
    abort: Option<[Expect; 4]>,
    unwind: Option<[Expect; 4]>,
    overflow_checks: bool,
}

// ---------------------------------------------------------------- vec![x; n]

const FROM_ELEM_CLONE: Expect = Refuse("TCG-FROM-ELEM-CLONE", "");
const FE_REFUSE: [Expect; 4] = [FROM_ELEM_CLONE; 4];

const FROM_ELEM_USER_CLONE: &str = r#"
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CNT: AtomicU32 = AtomicU32::new(0);
struct S { a: u32, b: u32 }
impl Clone for S { fn clone(&self) -> S { CNT.fetch_add(1, SeqCst); S { a: self.a + 1, b: self.b } } }
fn main() {
    let v = vec![S { a: 10, b: 0 }; std::hint::black_box(3)];
    let r = v[0].a * 100 + v[1].a * 1000 + v[2].a * 10 + v[2].b + CNT.load(SeqCst);
    println!("r={r}");
    std::process::exit((r % 251) as i32);
}
"#;

const FROM_ELEM_USER_CLONE_LOG: &str = r#"
use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static LOG: AtomicU64 = AtomicU64::new(0);
static CNT: AtomicU64 = AtomicU64::new(0);
fn ev(x: u64) { LOG.store(LOG.load(SeqCst).wrapping_mul(31).wrapping_add(x), SeqCst); CNT.fetch_add(1, SeqCst); }
struct S { a: u32, b: u32 }
impl Clone for S {
    fn clone(&self) -> S { ev(self.a as u64); S { a: self.a + 1, b: self.b * 2 } }
}
#[inline(never)]
fn make(n: usize, a: u32) -> Vec<S> { vec![S { a, b: 3 }; n] }
fn main() {
    let mut acc: u64 = 0;
    for n in [0usize, 1, 4] {
        let v = make(std::hint::black_box(n), 10);
        for (i, s) in v.iter().enumerate() { acc = acc * 7 + (i as u64 + 1) * (s.a as u64 * 100 + s.b as u64); }
        acc = acc * 13 + v.len() as u64;
    }
    let cnt = CNT.load(SeqCst); let log = LOG.load(SeqCst);
    println!("acc={acc} clones={cnt} log={log}");
    std::process::exit(((acc ^ cnt ^ log) % 251) as i32);
}
"#;

const FROM_ELEM_COUNTER_ONLY_CLONE: &str = r#"
use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct S { a: u32, b: u8 }
impl Clone for S { fn clone(&self) -> S { CNT.fetch_add(1, SeqCst); S { a: self.a, b: self.b } } }
fn main() {
    let v = vec![S { a: 4, b: 1 }; std::hint::black_box(6)];
    let r = std::hint::black_box(v.len()) as u64 * 10 + CNT.load(SeqCst) + (v[5].a + v[5].b as u32) as u64 * 100;
    println!("r={r}");
    std::process::exit((r % 251) as i32);
}
"#;

const FROM_ELEM_TUPLE_USER_CLONE: &str = r#"
use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct S { a: u32 }
impl S { fn get(&self) -> u64 { self.a as u64 } }
impl Clone for S { fn clone(&self) -> S { CNT.fetch_add(1, SeqCst); S { a: self.a + 5 } } }
fn val(p: &(u32, S)) -> u64 { p.0 as u64 * 100 + p.1.get() }
fn main() {
    let v = vec![(7u32, S { a: 1 }); std::hint::black_box(3)];
    let mut acc = 0u64;
    for p in v.iter() { acc = acc * 1000 + val(p); }
    let r = acc * 10 + CNT.load(SeqCst);
    println!("r={r}");
    std::process::exit((r % 251) as i32);
}
"#;

const FROM_ELEM_DERIVED_WITH_USER_FIELD: &str = r#"
use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct In { v: u16 }
impl In { fn get(&self) -> u64 { self.v as u64 } }
impl Clone for In { fn clone(&self) -> In { CNT.fetch_add(1, SeqCst); In { v: self.v ^ 0x55 } } }
#[derive(Clone)]
struct P { a: u32, inner: In, b: u8 }
impl P { fn val(&self) -> u64 { self.a as u64 + self.inner.get() * 1000 + self.b as u64 } }
fn main() {
    let v = vec![P { a: 9, inner: In { v: 1 }, b: 2 }; std::hint::black_box(3)];
    let mut acc = 0u64;
    for p in v.iter() { acc = acc * 100000 + p.val(); }
    let r = acc * 10 + CNT.load(SeqCst);
    println!("r={r}");
    std::process::exit((r % 251) as i32);
}
"#;

const FROM_ELEM_CLONE_PANICS: &str = r#"
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CNT: AtomicU32 = AtomicU32::new(0);
struct S { a: u32, b: u16 }
impl Clone for S {
    fn clone(&self) -> S {
        if CNT.fetch_add(1, SeqCst) == 1 { panic!("second clone") }
        S { a: self.a + 1, b: self.b }
    }
}
fn main() {
    let v = vec![S { a: 7, b: 3 }; std::hint::black_box(5)];
    let len = std::hint::black_box(v.len());
    println!("len={} last={}", len, v[4].a + v[4].b as u32);
    std::process::exit(v.len() as i32);
}
"#;

const FROM_ELEM_DERIVED_CONTROLS: &str = r#"
#[derive(Clone)]
struct D { a: u32, b: u16, c: u8 }
#[derive(Clone, Copy)]
struct C { a: u64, b: i8 }
#[derive(Clone)]
struct N { inner: D, z: i32 }
#[inline(never)]
fn n(x: usize) -> usize { std::hint::black_box(x) }
fn main() {
    let mut acc: u64 = 0;
    for k in [0usize, 1, 5] {
        let d = vec![D { a: 11, b: 22, c: 3 }; n(k)];
        for x in d.iter() { acc = acc.wrapping_mul(31).wrapping_add(x.a as u64 + x.b as u64 * 7 + x.c as u64 * 13); }
        let c = vec![C { a: 1 << 40, b: -5 }; n(k)];
        for x in c.iter() { acc = acc.wrapping_mul(31).wrapping_add(x.a.wrapping_add(x.b as u64)); }
        let t = vec![(9u32, 300u16); n(k)];
        for x in t.iter() { acc = acc.wrapping_mul(31).wrapping_add(x.0 as u64 * 3 + x.1 as u64); }
        let m = vec![N { inner: D { a: 4, b: 5, c: 6 }, z: -9 }; n(k)];
        for x in m.iter() { acc = acc.wrapping_mul(31).wrapping_add(x.inner.a as u64 + x.inner.c as u64 + x.z as u64); }
        acc = acc.wrapping_mul(7).wrapping_add((d.len() + c.len() + t.len() + m.len()) as u64);
    }
    println!("acc={acc}");
    std::process::exit((acc % 251) as i32);
}
"#;

const FROM_ELEM_SCALAR_CONTROLS: &str = r#"
#[inline(never)]
fn n(x: usize) -> usize { std::hint::black_box(x) }
fn main() {
    let mut acc: u64 = 0;
    for k in [0usize, 1, 6] {
        let a = vec![200u8; n(k)]; for x in a.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let b = vec![-100i8; n(k)]; for x in b.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let c = vec![60000u16; n(k)]; for x in c.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let d = vec![-30000i16; n(k)]; for x in d.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let e = vec![u32::MAX; n(k)]; for x in e.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let f = vec![i32::MIN; n(k)]; for x in f.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let g = vec![u64::MAX - 3; n(k)]; for x in g.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x); }
        let h = vec![i64::MIN + 1; n(k)]; for x in h.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let i = vec![true; n(k)]; for x in i.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let j = vec!['z'; n(k)]; for x in j.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64); }
        let l = vec![0u32; n(k)]; for x in l.iter() { acc = acc.wrapping_mul(31).wrapping_add(*x as u64 + 1); }
        acc = acc.wrapping_mul(7).wrapping_add((a.len() + h.len() + j.len()) as u64);
    }
    println!("acc={acc}");
    std::process::exit((acc % 251) as i32);
}
"#;

// A non-generic `#[derive(Clone, Copy)]` type's clone is `*self` and never
// calls its fields' `clone`; so is a hand-written `*self`. std's `extend_with`
// therefore never runs `In::clone` here (`clones=0`), and the image broadcast
// is that program. (`-Cpanic=unwind` O0/O1 refuse this guest's loop with an
// unrelated `[TCG-SSA-071]`, so the row runs under `panic=abort`.)
const FROM_ELEM_COPY_SELF_CLONES: &str = r#"
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CNT: AtomicU32 = AtomicU32::new(0);
#[derive(Copy)]
struct In(u16);
impl Clone for In { fn clone(&self) -> In { CNT.fetch_add(1, SeqCst); In(self.0 + 3) } }
#[derive(Clone, Copy)]
struct O { i: In, a: u32 }
#[derive(Copy)]
struct Me { a: u32, b: u8 }
impl Clone for Me { fn clone(&self) -> Me { *self } }
#[inline(never)]
fn n(x: usize) -> usize { std::hint::black_box(x) }
fn main() {
    let mut acc: u64 = 0;
    for k in [0usize, 1, 4] {
        let o = vec![O { i: In(1), a: 2 }; n(k)];
        for x in o.iter() { acc = acc.wrapping_mul(31).wrapping_add(x.i.0 as u64 * 7 + x.a as u64); }
        let m = vec![Me { a: 70000, b: 9 }; n(k)];
        for x in m.iter() { acc = acc.wrapping_mul(31).wrapping_add(x.a as u64 + x.b as u64 * 3); }
        acc = acc.wrapping_mul(7).wrapping_add((o.len() + m.len()) as u64);
    }
    let c = CNT.load(SeqCst);
    println!("acc={acc} clones={c}");
    std::process::exit(((acc + c as u64) % 251) as i32);
}
"#;

// A tuple's clone is core's field-wise shim even when the tuple is `Copy`:
// LLVM runs the counting `In::clone` three times (`r=3506`), so this element
// is not a `*self` clone and refuses.
const FROM_ELEM_COPY_TUPLE_USER_FIELD: &str = r#"
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CNT: AtomicU32 = AtomicU32::new(0);
#[derive(Copy)]
struct In(u16);
impl Clone for In { fn clone(&self) -> In { CNT.fetch_add(1, SeqCst); In(self.0 + 3) } }
fn main() {
    let t = vec![(In(5), 6u32); std::hint::black_box(4)];
    let r = t[3].0 .0 as u32 * 100 + t[0].1 + CNT.load(SeqCst) * 1000;
    println!("r={r}");
    std::process::exit((r % 251) as i32);
}
"#;

const FROM_ELEM_UNWIND_CONTROL: &str = r#"
#[derive(Clone)]
struct D { a: u32, b: u16 }
#[inline(never)]
fn make(n: usize) -> Vec<D> { vec![D { a: 70000, b: 9 }; n] }
#[inline(never)]
fn digest(v: &[D]) -> u64 {
    let mut h = 0u64;
    for x in v { h = h.wrapping_mul(31).wrapping_add(x.a as u64 * 3 + x.b as u64); }
    h
}
fn main() {
    let v = make(std::hint::black_box(4));
    let h = digest(&v) ^ (std::hint::black_box(v.capacity()) as u64);
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

fn from_elem_rows() -> Vec<Row> {
    vec![
        Row {
            name: "from_elem_user_clone",
            src: FROM_ELEM_USER_CLONE,
            abort: Some(FE_REFUSE),
            unwind: Some(FE_REFUSE),
            overflow_checks: false,
        },
        Row {
            name: "from_elem_user_clone_log",
            src: FROM_ELEM_USER_CLONE_LOG,
            abort: Some(FE_REFUSE),
            unwind: None,
            overflow_checks: false,
        },
        Row {
            name: "from_elem_counter_only_clone",
            src: FROM_ELEM_COUNTER_ONLY_CLONE,
            abort: Some(FE_REFUSE),
            unwind: None,
            overflow_checks: false,
        },
        Row {
            name: "from_elem_tuple_user_clone",
            src: FROM_ELEM_TUPLE_USER_CLONE,
            abort: Some(FE_REFUSE),
            unwind: None,
            overflow_checks: false,
        },
        Row {
            name: "from_elem_derived_with_user_field",
            src: FROM_ELEM_DERIVED_WITH_USER_FIELD,
            abort: Some(FE_REFUSE),
            unwind: None,
            overflow_checks: false,
        },
        Row {
            name: "from_elem_clone_panics",
            src: FROM_ELEM_CLONE_PANICS,
            abort: Some(FE_REFUSE),
            unwind: Some(FE_REFUSE),
            overflow_checks: false,
        },
        Row {
            name: "from_elem_derived_controls",
            src: FROM_ELEM_DERIVED_CONTROLS,
            abort: Some(M4),
            unwind: None,
            overflow_checks: false,
        },
        Row {
            name: "from_elem_scalar_controls",
            src: FROM_ELEM_SCALAR_CONTROLS,
            abort: Some(M4),
            unwind: None,
            overflow_checks: false,
        },
        Row {
            name: "from_elem_unwind_control",
            src: FROM_ELEM_UNWIND_CONTROL,
            abort: Some(M4),
            unwind: Some(M4),
            overflow_checks: false,
        },
        Row {
            name: "from_elem_copy_self_clones",
            src: FROM_ELEM_COPY_SELF_CLONES,
            abort: Some(M4),
            unwind: None,
            overflow_checks: false,
        },
        Row {
            name: "from_elem_copy_tuple_user_field",
            src: FROM_ELEM_COPY_TUPLE_USER_FIELD,
            abort: Some(FE_REFUSE),
            unwind: None,
            overflow_checks: false,
        },
    ]
}

// ---------------------------------------------------------------- slice sorts

/// `sort` at -O2/-O3: MIR inlining exposes core's stable `driftsort_main`,
/// whose monomorphizations the bridge refuses (`Vec::as_uninit_slice_mut` is
/// not an intercepted method). `sort_unstable`'s `heapsort` compiles there.
const DRIFTSORT: Expect = Refuse("TCG-MIR-UNSUPPORTED", "driftsort_main");
const KEY_EFFECT: Expect = Refuse("TCG-SORT-KEY-EFFECT", "");
const KEY_EFFECT_4: [Expect; 4] = [KEY_EFFECT; 4];

const SORT_U64_HIGH_BIT: &str = r#"
fn main() {
    let mut v: Vec<u64> = Vec::new();
    for x in [5u64, u64::MAX, 1 << 63, 0, 7] { v.push(x); }
    v.sort();
    let a = (v[0] == 0) as i32 + 2 * (v[1] == 5) as i32 + 4 * (v[2] == 7) as i32 + 8 * (v[3] == 1 << 63) as i32 + 16 * (v[4] == u64::MAX) as i32;
    let mut w: Vec<u64> = Vec::new();
    for x in [1u64 << 63, 1] { w.push(x); }
    w.sort_unstable();
    let b = (w[0] == 1) as i32;
    let mut u: Vec<u32> = Vec::new();
    for x in [u32::MAX, 1, 1 << 31] { u.push(x); }
    u.sort();
    let c = (u[0] == 1) as i32 + 2 * (u[2] == u32::MAX) as i32;
    let mut s: Vec<usize> = Vec::new();
    for x in [usize::MAX, 3] { s.push(x); }
    s.sort();
    let d = (s[0] == 3) as i32;
    println!("a={} b={} c={} d={}", a, b, c, d);
    std::process::exit(a + b * 32 + c * 64 + d * 128);
}
"#;

const SORT_U64_ORDER: &str = r#"
fn main() {
    let mut v: Vec<u64> = Vec::new();
    for x in [5u64, u64::MAX, 1 << 63, 0, 7, (1 << 63) + 1] { v.push(x); }
    v.sort();
    let (a0, a1, a2, a3, a4, a5) = (v[0], v[1], v[2], v[3], v[4], v[5]);
    println!("u64 {} {} {} {} {} {}", a0, a1, a2, a3, a4, a5);
    let mut w: Vec<usize> = Vec::new();
    for x in [usize::MAX, 3, 1usize << 63, 9] { w.push(x); }
    w.sort_unstable();
    let (b0, b1, b2, b3) = (w[0], w[1], w[2], w[3]);
    println!("usize {} {} {} {}", b0, b1, b2, b3);
    let mut a = [u64::MAX - 1, 2, 1 << 62, 1 << 63];
    a.sort_unstable();
    let (c0, c1, c2, c3) = (a[0], a[1], a[2], a[3]);
    println!("arr {} {} {} {}", c0, c1, c2, c3);
}
"#;

const SORT_U64_STABLE_ORDER: &str = r#"
fn main() {
    let mut v: Vec<u64> = Vec::new();
    for x in [5u64, u64::MAX, 1 << 63, 0, 7, (1 << 63) + 1] { v.push(x); }
    v.sort();
    let (a0, a1, a2, a3, a4, a5) = (v[0], v[1], v[2], v[3], v[4], v[5]);
    println!("u64 {} {} {} {} {} {}", a0, a1, a2, a3, a4, a5);
    let mut w: Vec<usize> = Vec::new();
    for x in [usize::MAX, 3, 1usize << 63, 9] { w.push(x); }
    w.sort();
    let (b0, b1, b2, b3) = (w[0], w[1], w[2], w[3]);
    println!("usize {} {} {} {}", b0, b1, b2, b3);
    std::process::exit((a3 >> 60) as i32 + (b2 >> 61) as i32);
}
"#;

const SORT_WIDTH_CONTROLS: &str = r#"
macro_rules! check {
    ($t:ty, $vals:expr, $h:ident) => {{
        let mut v: Vec<$t> = Vec::new();
        for x in $vals { v.push(x); }
        v.sort();
        for x in v.iter() { $h = $h.wrapping_mul(1_000_003).wrapping_add(*x as u64); }
        let mut w: Vec<$t> = Vec::new();
        for x in $vals { w.push(x); }
        w.reverse();
        w.sort_unstable();
        for x in w.iter() { $h = $h.wrapping_mul(1_000_003).wrapping_add(*x as u64); }
    }};
}
fn main() {
    let mut h: u64 = 0;
    check!(u8, [7u8, u8::MAX, 0, 128, 127, 1], h);
    check!(i8, [7i8, i8::MAX, i8::MIN, -1, 0, 1], h);
    check!(u16, [7u16, u16::MAX, 0, 1 << 15, (1 << 15) - 1], h);
    check!(i16, [7i16, i16::MAX, i16::MIN, -1, 0], h);
    check!(u32, [7u32, u32::MAX, 0, 1 << 31, (1 << 31) - 1], h);
    check!(i32, [7i32, i32::MAX, i32::MIN, -1, 0], h);
    check!(i64, [7i64, i64::MAX, i64::MIN, -1, 0], h);
    check!(isize, [7isize, isize::MAX, isize::MIN, -1, 0], h);
    check!(u64, [7u64, (1 << 63) - 1, 0, 3], h);
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

const STABLE_SORT_ALL_WIDTHS: &str = r#"
macro_rules! check {
    ($t:ty, $vals:expr, $h:ident) => {{
        let mut v: Vec<$t> = Vec::new();
        for x in $vals { v.push(x); }
        v.sort();
        for x in v.iter() { $h = $h.wrapping_mul(1_000_003).wrapping_add(*x as u64); }
    }};
}
fn main() {
    let mut h: u64 = 0;
    check!(u8, [7u8, u8::MAX, 0, 128, 127, 1], h);
    check!(i8, [7i8, i8::MAX, i8::MIN, -1, 0, 1], h);
    check!(u16, [7u16, u16::MAX, 0, 1 << 15, (1 << 15) - 1], h);
    check!(i16, [7i16, i16::MAX, i16::MIN, -1, 0], h);
    check!(u32, [7u32, u32::MAX, 0, 1 << 31, (1 << 31) - 1], h);
    check!(i32, [7i32, i32::MAX, i32::MIN, -1, 0], h);
    check!(u64, [7u64, u64::MAX, 0, 1 << 63, (1 << 63) - 1, (1 << 63) + 1], h);
    check!(i64, [7i64, i64::MAX, i64::MIN, -1, 0], h);
    check!(usize, [7usize, usize::MAX, 0, 1 << 63], h);
    check!(isize, [7isize, isize::MAX, isize::MIN, -1, 0], h);
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

const BY_KEY_COUNTER: &str = r#"
fn main() {
    let mut calls = 0u32;
    let mut v: Vec<u32> = Vec::new();
    for x in [5u32, 3, 9, 1, 7] { v.push(x); }
    v.sort_by_key(|x| { calls += 1; *x });
    let mut h = 0u32; for x in v.iter() { h = h * 10 + *x; }
    println!("calls={} h={}", calls, h);
    std::process::exit(calls as i32);
}
"#;

const BY_KEY_STATIC_LOG: &str = r#"
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::SeqCst};
static LOG: AtomicU64 = AtomicU64::new(0);
static N: AtomicUsize = AtomicUsize::new(0);
fn key(x: &u32) -> u32 {
    N.fetch_add(1, SeqCst);
    LOG.store(LOG.load(SeqCst).wrapping_mul(10).wrapping_add(*x as u64), SeqCst);
    *x
}
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for x in [3u32, 1, 2] { v.push(x); }
    v.sort_by_key(|x| key(x));
    let mut h = 0u32; for x in v.iter() { h = h * 10 + *x; }
    let n = N.load(SeqCst); let l = LOG.load(SeqCst);
    println!("n={} log={} h={}", n, l, h);
    std::process::exit(n as i32);
}
"#;

const BY_KEY_LONG_COUNTER: &str = r#"
fn main() {
    let mut calls = 0u64;
    let mut v: Vec<u64> = (0..40u64).map(|i| (i * 7919) % 101).collect();
    v.sort_by_key(|x| { calls += 1; *x });
    let mut h: u64 = 0;
    for x in &v { h = h.wrapping_mul(31).wrapping_add(*x); }
    println!("calls={} h={}", calls, h);
    std::process::exit((calls % 251) as i32);
}
"#;

const UNSTABLE_BY_KEY_COUNTER: &str = r#"
fn main() {
    let mut calls = 0u32;
    let mut v: Vec<u32> = Vec::new();
    for x in [5u32, 3, 9, 1, 7] { v.push(x); }
    v.sort_unstable_by_key(|x| { calls += 1; *x });
    let mut h = 0u32; for x in v.iter() { h = h * 10 + *x; }
    println!("calls={} h={}", calls, h);
    std::process::exit(calls as i32);
}
"#;

const BY_KEY_STATEFUL: &str = r#"
fn main() {
    let mut calls = 0u32;
    let mut v: Vec<i32> = Vec::new();
    for x in [4i32, 8, 1, 6, 3, 9, 2] { v.push(x); }
    v.sort_by_key(|x| { calls += 1; if calls % 3 == 0 { -*x } else { *x } });
    let mut h = 0i64; for x in v.iter() { h = h * 10 + *x as i64; }
    println!("calls={} h={}", calls, h);
    std::process::exit((h % 251) as i32);
}
"#;

const UNSTABLE_BY_KEY_TIES: &str = r#"
fn main() {
    let mut v: Vec<u64> = Vec::new();
    for i in 0..40u64 { v.push(((i * 7) % 5) * 100 + i); }
    v.sort_unstable_by_key(|x| *x / 100);
    let mut h: u64 = 0;
    for x in v.iter() { h = h.wrapping_mul(31).wrapping_add(*x); }
    let f0 = v[0]; let f1 = v[1]; let f2 = v[2];
    println!("h={} f={} {} {}", h, f0, f1, f2);
    std::process::exit((h % 251) as i32);
}
"#;

const BY_KEY_PURE_CONTROLS: &str = r#"
#[inline(never)]
fn bb<T>(x: T) -> T { std::hint::black_box(x) }
fn main() {
    let mut h: u64 = 0;
    let mut k: Vec<u32> = Vec::new();
    for x in [1u32, 2, 3, 4, 5, 6] { k.push(x); }
    k.sort_by_key(|x| -(*x as i64 % 3));
    for x in k.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    let mut m: Vec<u8> = Vec::new();
    for x in [1u8, 200, 3, 129] { m.push(x); }
    m.sort_by_key(|x| x.wrapping_mul(3));
    for x in m.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    let mut v: Vec<u64> = (0..40u64).map(|i| ((i * 7) % 5) * 100 + i).collect();
    v.sort_by_key(|x| *x / 100);
    for x in v.iter() { h = h.wrapping_mul(31).wrapping_add(*x); }
    let base = bb(5i64);
    let mut c: Vec<i64> = Vec::new();
    for x in [9i64, -3, 5, 6, 1, 4] { c.push(x); }
    c.sort_by_key(|x| (*x - base).abs());
    for x in c.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    let mut u: Vec<u64> = Vec::new();
    for x in [u64::MAX, 3, 1 << 63, 0] { u.push(x); }
    u.sort_unstable_by_key(|x| *x);
    for x in u.iter() { h = h.wrapping_mul(31).wrapping_add(*x); }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// `BY_KEY_PURE_CONTROLS` without its `(*x - base).abs()` key, for the row with
// overflow checks on: that key keeps two checks (the subtraction and `abs`'s
// negation), so it refuses there (`by_key_two_sites_abs`).
const BY_KEY_CHECKED_CONTROLS: &str = r#"
fn main() {
    let mut h: u64 = 0;
    let mut k: Vec<u32> = Vec::new();
    for x in [1u32, 2, 3, 4, 5, 6] { k.push(x); }
    k.sort_by_key(|x| -(*x as i64 % 3));
    for x in k.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    let mut m: Vec<u8> = Vec::new();
    for x in [1u8, 200, 3, 129] { m.push(x); }
    m.sort_by_key(|x| x.wrapping_mul(3));
    for x in m.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    let mut v: Vec<u64> = (0..40u64).map(|i| ((i * 7) % 5) * 100 + i).collect();
    v.sort_by_key(|x| *x / 100);
    for x in v.iter() { h = h.wrapping_mul(31).wrapping_add(*x); }
    let mut u: Vec<u64> = Vec::new();
    for x in [u64::MAX, 3, 1 << 63, 0] { u.push(x); }
    u.sort_unstable_by_key(|x| *x);
    for x in u.iter() { h = h.wrapping_mul(31).wrapping_add(*x); }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// The removed key: a subtraction that may overflow, then `abs`, whose
// negation may overflow too. Two kept checks, so which one a call order
// reaches first is observable for some slice (not for this one).
const BY_KEY_TWO_SITES_ABS: &str = r#"
#[inline(never)]
fn bb<T>(x: T) -> T { std::hint::black_box(x) }
fn main() {
    let base = bb(5i64);
    let mut c: Vec<i64> = Vec::new();
    for x in [9i64, -3, 5, 6, 1, 4] { c.push(x); }
    c.sort_by_key(|x| (*x - base).abs());
    let mut h: u64 = 0;
    for x in c.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// Arithmetic on `&u32` goes through core's `#[track_caller]` operator impls:
// their one check reports the closure's own call, so a key making one such
// call keeps one site and the model. The second sort panics (element 3 under
// `x - 10`) at the same location under std and the model.
const BY_KEY_TRACK_CALLER_ONE_CALL_CONTROL: &str = r#"
fn main() {
    let mut w: Vec<u32> = Vec::new();
    for i in 0..30u32 { w.push((i * 7919) % 1000); }
    w.sort_by_key(|x| x / 3);
    let mut h = 0u64; for x in w.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    println!("h={h}");
    let mut v: Vec<u32> = Vec::new();
    for i in 0..40u32 { v.push(10 + ((i * 7919) % 900)); }
    v[4] = 3;
    v.sort_by_key(|x| x - 10);
    std::process::exit(v[0] as i32 & 0x7f);
}
"#;

const BY_KEY_PURE_UNWIND_CONTROL: &str = r#"
fn main() {
    let mut v: Vec<i64> = Vec::new();
    for x in [9i64, -3, 5, 6, 1, 4, 22, -8] { v.push(x); }
    v.sort_by_key(|x| *x / 3);
    let mut w: Vec<u16> = Vec::new();
    for x in [7u16, 65535, 0, 300, 9] { w.push(x); }
    w.sort_unstable_by_key(|x| !*x);
    let (a0, a1, a2, a3, a7) = (v[0], v[1], v[2], v[3], v[7]);
    let (b0, b1, b4) = (w[0], w[1], w[4]);
    println!("{a0} {a1} {a2} {a3} {a7} {b0} {b1} {b4}");
    std::process::exit((a0 + 2 * a7) as i32 & 0xff);
}
"#;

const UNSTABLE_INJECTIVE_CONTROLS: &str = r#"
fn main() {
    let mut h: u64 = 0;
    let mut v: Vec<u64> = (0..40u64).map(|i| (i * 7919) % 31).collect();
    v.sort_unstable_by_key(|x| *x);
    for x in v.iter() { h = h.wrapping_mul(31).wrapping_add(*x); }
    let mut w: Vec<i32> = (0..30i32).map(|i| (i * 37) % 23 - 11).collect();
    w.sort_unstable_by_key(|x| -(*x as i64));
    for x in w.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    let mut u: Vec<u16> = (0..25u16).map(|i| (i * 4099) % 61).collect();
    u.sort_unstable_by_key(|x| !*x);
    for x in u.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// Two panic sites in a pure key under `panic=abort`: element 3 underflows the
// subtraction, element 2000 overflows the multiplication. std's call order
// reaches the multiplication first, the model's the subtraction (measured at
// 529ace6eb, O0..O3); with one site the message and location are fixed.
const BY_KEY_TWO_OVERFLOW_SITES: &str = r#"
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for i in 0..40u32 { v.push(10 + ((i * 7919) % 900)); }
    v[4] = 3;
    v[5] = 2000;
    v.sort_by_key(|&x| if x >= 1000 { x * 4_000_000 } else { x - 10 });
    std::process::exit(v[0] as i32 & 0x7f);
}
"#;

// The same with two division-by-zero checks, which overflow-checks=off keeps.
const BY_KEY_TWO_DIVISION_SITES: &str = r#"
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for i in 0..40u32 { v.push(10 + ((i * 7919) % 900)); }
    v[4] = 3;
    v[5] = 2000;
    v.sort_by_key(|&x| if x >= 1000 { 7 / (x - 2000) } else { 9000 / (x - 3) });
    std::process::exit(v[0] as i32 & 0x7f);
}
"#;

// One overflow check, but in a `#[track_caller]` function the key calls from
// two places: the one assert reports whichever caller reached it.
const BY_KEY_TRACK_CALLER_SITE: &str = r#"
#[track_caller]
#[inline(never)]
fn dec(x: u32) -> u32 { x - 10 }
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for i in 0..40u32 { v.push(10 + ((i * 7919) % 900)); }
    v[4] = 3;
    v[5] = 1003;
    v.sort_by_key(|&x| if x >= 1000 { dec(x - 1000) } else { dec(x) });
    std::process::exit(v[0] as i32 & 0x7f);
}
"#;

// Control: one kept overflow site under `panic=abort` keeps the model, and
// the panic it reaches is LLVM's.
const BY_KEY_ONE_PANIC_SITE_CONTROL: &str = r#"
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for i in 0..40u32 { v.push(10 + ((i * 7919) % 900)); }
    v[4] = 3;
    v[5] = 2;
    v.sort_by_key(|&x| x - 10);
    std::process::exit(v[0] as i32 & 0x7f);
}
"#;

// A key that reads its argument's address through a union: std keys the
// insertee from a stack copy, the model in place, so the address-dependent
// key sorts differently.
const BY_KEY_UNION_ADDRESS: &str = r#"
#[derive(Clone, Copy)]
union U { p: *const u32, n: usize }
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for x in [5u32, 3, 9, 1, 7, 2] { v.push(x); }
    let lo = v.as_ptr() as usize;
    let hi = lo + v.len() * 4;
    v.sort_by_key(|x| {
        let a = unsafe { U { p: x as *const u32 }.n };
        ((a >= lo && a < hi) as u64) * 1000 + *x as u64
    });
    let mut h = 0u64; for x in v.iter() { h = h * 10 + *x as u64; }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// The same address read back through a pointer cast over a local array that
// holds the argument.
const BY_KEY_ARRAY_POINTER_ADDRESS: &str = r#"
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for x in [5u32, 3, 9, 1, 7, 2] { v.push(x); }
    let lo = v.as_ptr() as usize;
    let hi = lo + v.len() * 4;
    v.sort_by_key(|x| {
        let arr: [&u32; 1] = [x];
        let a = unsafe { *(arr.as_ptr() as *const usize) };
        ((a >= lo && a < hi) as u64) * 1000 + *x as u64
    });
    let mut h = 0u64; for x in v.iter() { h = h * 10 + *x as u64; }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// And through a raw slice pointer built over that array's data pointer.
const BY_KEY_RAW_PARTS_ADDRESS: &str = r#"
#![feature(ptr_metadata)]
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for x in [5u32, 3, 9, 1, 7, 2] { v.push(x); }
    let lo = v.as_ptr() as usize;
    let hi = lo + v.len() * 4;
    v.sort_by_key(|x| {
        let arr: [&u32; 1] = [x];
        let s: *const [usize] = std::ptr::from_raw_parts(arr.as_ptr(), 1);
        let a = unsafe { (*s)[0] };
        ((a >= lo && a < hi) as u64) * 1000 + *x as u64
    });
    let mut h = 0u64; for x in v.iter() { h = h * 10 + *x as u64; }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// A key that reassigns its own argument is not `*arg` at its return: 40
// elements with ties under the reassigned key, so std's ipnsort and the stable
// model order them differently.
const UNSTABLE_BY_KEY_ARG_REASSIGN: &str = r#"
static BIG: u64 = 1000;
fn main() {
    let mut v: Vec<u64> = Vec::new();
    for i in 0..40u64 { v.push(((i * 7) % 5) * 100 + i); }
    v.sort_unstable_by_key(|mut x: &u64| { if *x >= 100 { x = &BIG; } *x });
    let mut h: u64 = 0;
    for x in v.iter() { h = h.wrapping_mul(31).wrapping_add(*x); }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

const UNSTABLE_BY_KEY_ARG_REASSIGN_NEG: &str = r#"
fn main() {
    let mut v: Vec<i64> = Vec::new();
    for i in 0..30i64 { v.push(((i * 7) % 5) * 100 + i); }
    v.sort_unstable_by_key(|mut x: &i64| { let k: &i64 = &-1; if *x >= 200 { x = k; } -*x });
    let mut h: u64 = 0;
    for x in v.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// EVIDENCE BOUNDARY rows: keys this check refuses although std would run them.
// An argsort key's bounds check panics with the index in its message, so the
// first failing element is observable.
const BY_KEY_ARGSORT_BOUNDS: &str = r#"
fn main() {
    let mut scores: Vec<u32> = Vec::new();
    for i in 0..30u32 { scores.push((i * 7919) % 101); }
    let mut idx: Vec<usize> = Vec::new();
    for i in 0..30usize { idx.push(i); }
    idx.sort_by_key(|&i| scores[i]);
    let mut h = 0u64; for i in idx.iter() { h = h.wrapping_mul(31).wrapping_add(*i as u64); }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

// An arithmetic key with its checks kept (overflow-checks=on). Under
// `panic=unwind` it refuses at every level: an unwind out of the model's
// insertion sort would leave a slice std's guards would not. Under
// `panic=abort` it keeps the model at O2/O3, where the division by 3 is inlined
// and proved never to fire, leaving the `+ 1` as its one site; at O0/O1 the
// division's check sits behind a call to core's `<&u32 as Div<u32>>::div`,
// whose divisor the walk does not see, so it counts as a second site.
const BY_KEY_DEBUG_PROFILE: &str = r#"
fn main() {
    let mut v: Vec<u32> = Vec::new();
    for i in 0..30u32 { v.push((i * 7919) % 1000); }
    v.sort_by_key(|x| x / 3 + 1);
    let mut h = 0u64; for x in v.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

const CACHED_KEY_COUNTER: &str = r#"
fn main() {
    let mut calls = 0u32;
    let mut v: Vec<u32> = Vec::new();
    for x in [5u32, 3, 9, 1, 7, 2] { v.push(x); }
    v.sort_by_cached_key(|x| { calls += 1; *x });
    let mut h = 0u32; for x in v.iter() { h = h * 10 + *x; }
    println!("calls={} h={}", calls, h);
    std::process::exit(calls as i32);
}
"#;

const CACHED_KEY_STATEFUL: &str = r#"
fn main() {
    let mut calls = 0u32;
    let mut v: Vec<u32> = Vec::new();
    for x in [5u32, 3, 9, 1, 7, 2] { v.push(x); }
    let n = v.len() as u32;
    v.sort_by_cached_key(|x| { calls += 1; if calls > n { 100 - *x } else { *x } });
    let mut h = 0u32; for x in v.iter() { h = h * 10 + *x; }
    println!("calls={} h={}", calls, h);
    std::process::exit(if h == 123579 { 0 } else { 1 });
}
"#;

const CACHED_KEY_ORDER_LOG: &str = r#"
use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static LOG: AtomicU64 = AtomicU64::new(0);
fn key(x: &u16) -> i32 {
    LOG.store(LOG.load(SeqCst).wrapping_mul(10).wrapping_add(*x as u64), SeqCst);
    -(*x as i32 % 4)
}
fn main() {
    let mut v: Vec<u16> = Vec::new();
    for x in [3u16, 1, 2, 7, 5, 4, 8] { v.push(x); }
    v.sort_by_cached_key(|x| key(x));
    let mut h = 0u64; for x in v.iter() { h = h * 10 + *x as u64; }
    let l = LOG.load(SeqCst);
    println!("log={} h={}", l, h);
    std::process::exit((h % 251) as i32);
}
"#;

// Capture the next actual allocation by pointer, never by an assumed pair
// size. Arm only after the input Vec exists. The real cached-key callback
// panics on its fourth invocation; a caller guard checks that the cache's
// allocation has been freed exactly once before that guard is unwound.
const CACHED_KEY_FORCED_PANIC_CLEANUP: &str = r#"
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering::SeqCst};
static TRACK_NEXT: AtomicBool = AtomicBool::new(false);
static TRACKED_PTR: AtomicUsize = AtomicUsize::new(0);
static TRACKED_FREES: AtomicUsize = AtomicUsize::new(0);
static CALLS: AtomicUsize = AtomicUsize::new(0);
static LOG: AtomicU64 = AtomicU64::new(0);
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if TRACK_NEXT.swap(false, SeqCst) { TRACKED_PTR.store(ptr as usize, SeqCst); }
        ptr
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if ptr as usize == TRACKED_PTR.load(SeqCst) {
            TRACKED_FREES.fetch_add(1, SeqCst);
        }
        unsafe { System.dealloc(ptr, layout) }
    }
}
#[global_allocator]
static GLOBAL: Counting = Counting;
struct Audit;
impl Drop for Audit {
    fn drop(&mut self) {
        let calls = CALLS.load(SeqCst);
        let log = LOG.load(SeqCst);
        let allocated = TRACKED_PTR.load(SeqCst) != 0;
        let frees = TRACKED_FREES.load(SeqCst);
        assert_eq!(calls, 4);
        assert_eq!(log, 3127);
        assert!(allocated);
        assert_eq!(frees, 1);
        println!("calls={calls} log={log} cache_alloc={} cache_frees={frees}", allocated as u8);
    }
}
#[inline(never)]
fn key(x: &u16) -> i32 {
    CALLS.fetch_add(1, SeqCst);
    LOG.store(LOG.load(SeqCst).wrapping_mul(10).wrapping_add(*x as u64), SeqCst);
    if *x == 7 { panic!("cached-key forced panic"); }
    -(*x as i32 % 4)
}
fn main() {
    let mut values: Vec<u16> = Vec::with_capacity(8);
    for x in [3u16, 1, 2, 7, 5, 4, 8] { values.push(x); }
    let _audit = Audit;
    TRACK_NEXT.store(true, SeqCst);
    values.sort_by_cached_key(|x| key(x));
    std::process::exit(9);
}
"#;

const CACHED_KEY_PURE_CONTROLS: &str = r#"
fn main() {
    let mut v: Vec<u64> = (0..30u64).map(|i| (i * 7919) % 101).collect();
    v.sort_by_cached_key(|x| *x % 7);
    let mut h: u64 = 0;
    for x in &v { h = h.wrapping_mul(31).wrapping_add(*x); }
    let mut w: Vec<i32> = Vec::new();
    for x in [4i32, -2, 9, 0, -7, 3, 3] { w.push(x); }
    w.sort_by_cached_key(|x| -(*x as i64));
    for x in w.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    let mut one: Vec<u8> = Vec::new(); one.push(9);
    one.sort_by_cached_key(|x| *x);
    h = h.wrapping_mul(31).wrapping_add(one[0] as u64);
    println!("h={h}");
    std::process::exit((h % 251) as i32);
}
"#;

const CACHED_KEY_ALLOCATION: &str = r#"
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};
struct Counting;
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static FREES: AtomicUsize = AtomicUsize::new(0);
static SIZES: AtomicUsize = AtomicUsize::new(0);
static ALIGNS: AtomicUsize = AtomicUsize::new(0);
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, SeqCst);
        SIZES.store(SIZES.load(SeqCst) * 1000 + l.size(), SeqCst);
        ALIGNS.store(ALIGNS.load(SeqCst) * 100 + l.align(), SeqCst);
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        FREES.fetch_add(1, SeqCst);
        unsafe { System.dealloc(p, l) }
    }
}
#[global_allocator]
static GLOBAL: Counting = Counting;
fn main() {
    let mut v: Vec<u32> = Vec::with_capacity(8);
    for x in [5u32, 3, 9, 1, 7, 2] { v.push(x); }
    let mut w: Vec<i64> = Vec::with_capacity(8);
    for x in [4i64, -9, 7, 0, 3] { w.push(x); }
    let mut one: Vec<u8> = Vec::with_capacity(1);
    one.push(9);
    let base = (ALLOCS.load(SeqCst), FREES.load(SeqCst));
    SIZES.store(0, SeqCst);
    ALIGNS.store(0, SeqCst);
    v.sort_by_cached_key(|x| *x % 4);
    w.sort_by_cached_key(|x| -*x);
    one.sort_by_cached_key(|x| *x as u64);
    let allocs = ALLOCS.load(SeqCst) - base.0;
    let frees = FREES.load(SeqCst) - base.1;
    let sizes = SIZES.load(SeqCst);
    let aligns = ALIGNS.load(SeqCst);
    let mut h: u64 = 0;
    for x in v.iter() { h = h * 10 + *x as u64; }
    for x in w.iter() { h = h.wrapping_mul(31).wrapping_add(*x as u64); }
    println!("allocs={allocs} frees={frees} sizes={sizes} aligns={aligns} h={h}");
    std::process::exit((allocs * 10 + frees) as i32);
}
"#;

fn sort_rows() -> Vec<Row> {
    let row = |name, src, abort: Option<[Expect; 4]>, unwind: Option<[Expect; 4]>| Row {
        name,
        src,
        abort,
        unwind,
        overflow_checks: false,
    };
    vec![
        row(
            "sort_u64_high_bit",
            SORT_U64_HIGH_BIT,
            Some([Match, Match, DRIFTSORT, DRIFTSORT]),
            None,
        ),
        row(
            "sort_u64_order",
            SORT_U64_ORDER,
            Some([Match, Match, DRIFTSORT, DRIFTSORT]),
            None,
        ),
        row(
            "sort_u64_stable_order",
            SORT_U64_STABLE_ORDER,
            Some([Match, Match, DRIFTSORT, DRIFTSORT]),
            None,
        ),
        row(
            "sort_width_controls",
            SORT_WIDTH_CONTROLS,
            Some([Match, Match, DRIFTSORT, DRIFTSORT]),
            None,
        ),
        row(
            "sort_stable_all_widths",
            STABLE_SORT_ALL_WIDTHS,
            Some([Match, Match, DRIFTSORT, DRIFTSORT]),
            None,
        ),
        row(
            "by_key_counter",
            BY_KEY_COUNTER,
            Some(KEY_EFFECT_4),
            Some(KEY_EFFECT_4),
        ),
        row(
            "by_key_static_log",
            BY_KEY_STATIC_LOG,
            Some(KEY_EFFECT_4),
            None,
        ),
        row(
            "by_key_long_counter",
            BY_KEY_LONG_COUNTER,
            Some(KEY_EFFECT_4),
            None,
        ),
        row(
            "unstable_by_key_counter",
            UNSTABLE_BY_KEY_COUNTER,
            Some(M4),
            None,
        ),
        row("by_key_stateful", BY_KEY_STATEFUL, Some(KEY_EFFECT_4), None),
        row("unstable_by_key_ties", UNSTABLE_BY_KEY_TIES, Some(M4), None),
        row("by_key_pure_controls", BY_KEY_PURE_CONTROLS, Some(M4), None),
        Row {
            name: "by_key_pure_controls_overflow_checks",
            src: BY_KEY_CHECKED_CONTROLS,
            abort: Some(M4),
            unwind: None,
            overflow_checks: true,
        },
        Row {
            name: "by_key_two_sites_abs",
            src: BY_KEY_TWO_SITES_ABS,
            abort: Some(KEY_EFFECT_4),
            unwind: None,
            overflow_checks: true,
        },
        Row {
            name: "by_key_track_caller_one_call_control",
            src: BY_KEY_TRACK_CALLER_ONE_CALL_CONTROL,
            abort: Some(M4),
            unwind: None,
            overflow_checks: true,
        },
        row(
            "by_key_pure_unwind_control",
            BY_KEY_PURE_UNWIND_CONTROL,
            Some(M4),
            Some(M4),
        ),
        row(
            "unstable_injective_controls",
            UNSTABLE_INJECTIVE_CONTROLS,
            Some(M4),
            None,
        ),
        Row {
            name: "by_key_two_overflow_sites",
            src: BY_KEY_TWO_OVERFLOW_SITES,
            abort: Some(KEY_EFFECT_4),
            unwind: None,
            overflow_checks: true,
        },
        row(
            "by_key_two_division_sites",
            BY_KEY_TWO_DIVISION_SITES,
            Some(KEY_EFFECT_4),
            None,
        ),
        Row {
            name: "by_key_track_caller_site",
            src: BY_KEY_TRACK_CALLER_SITE,
            abort: Some(KEY_EFFECT_4),
            unwind: None,
            overflow_checks: true,
        },
        Row {
            name: "by_key_one_panic_site_control",
            src: BY_KEY_ONE_PANIC_SITE_CONTROL,
            abort: Some(M4),
            unwind: None,
            overflow_checks: true,
        },
        row(
            "by_key_union_address",
            BY_KEY_UNION_ADDRESS,
            Some(KEY_EFFECT_4),
            None,
        ),
        row(
            "by_key_array_pointer_address",
            BY_KEY_ARRAY_POINTER_ADDRESS,
            Some(KEY_EFFECT_4),
            None,
        ),
        row(
            "by_key_raw_parts_address",
            BY_KEY_RAW_PARTS_ADDRESS,
            Some(KEY_EFFECT_4),
            None,
        ),
        row(
            "unstable_by_key_arg_reassign",
            UNSTABLE_BY_KEY_ARG_REASSIGN,
            Some(M4),
            None,
        ),
        row(
            "unstable_by_key_arg_reassign_neg",
            UNSTABLE_BY_KEY_ARG_REASSIGN_NEG,
            Some(M4),
            None,
        ),
        row(
            "by_key_argsort_bounds",
            BY_KEY_ARGSORT_BOUNDS,
            Some(KEY_EFFECT_4),
            None,
        ),
        Row {
            name: "by_key_debug_profile",
            src: BY_KEY_DEBUG_PROFILE,
            abort: Some([KEY_EFFECT, KEY_EFFECT, Match, Match]),
            unwind: Some(KEY_EFFECT_4),
            overflow_checks: true,
        },
        row("cached_key_counter", CACHED_KEY_COUNTER, Some(M4), Some(M4)),
        row(
            "cached_key_stateful",
            CACHED_KEY_STATEFUL,
            Some(M4),
            Some(M4),
        ),
        row(
            "cached_key_order_log",
            CACHED_KEY_ORDER_LOG,
            Some(M4),
            Some(M4),
        ),
        row(
            "cached_key_forced_panic_cleanup",
            CACHED_KEY_FORCED_PANIC_CLEANUP,
            None,
            Some(M4),
        ),
        row(
            "cached_key_pure_controls",
            CACHED_KEY_PURE_CONTROLS,
            Some(M4),
            None,
        ),
        row(
            "cached_key_allocation",
            CACHED_KEY_ALLOCATION,
            Some(M4),
            Some(M4),
        ),
    ]
}

// ---------------------------------------------------------------- Cell clones

/// The terminal a `.cloned()` left to core's real `Cloned` bodies refuses at:
/// `sum` at -O0/-O1, the `fold` it inlines into at -O2/-O3.
const UNMODELED_SUM_FOLD: [Expect; 4] = [
    Refuse("TCG-ITER-UNMODELED", "iterator `sum` terminal"),
    Refuse("TCG-ITER-UNMODELED", "iterator `sum` terminal"),
    Refuse("TCG-ITER-UNMODELED", "iterator `fold` terminal"),
    Refuse("TCG-ITER-UNMODELED", "iterator `fold` terminal"),
];

const CLONED_CELL_U32: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(3u32), Cell::new(5), Cell::new(7), Cell::new(11)];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().map(|c| c.get() * 2).sum();
    let mut acc = 0u32;
    for c in s.iter().cloned() { acc = acc * 7 + c.get(); }
    let n = s.iter().cloned().filter(|c| c.get() > 4).count();
    let any = s.iter().cloned().any(|c| c.get() == 7);
    println!("total={total} acc={acc} n={n} any={any}");
    std::process::exit(((total + acc + n as u32) % 251) as i32);
}
"#;

const CLONED_CELL_I64: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(-3i64), Cell::new(5), Cell::new(i64::MIN + 9), Cell::new(-11)];
    let s = std::hint::black_box(&s);
    let total: i64 = s.iter().cloned().map(|c| c.get().wrapping_mul(3)).fold(0i64, |a, b| a.wrapping_add(b));
    let neg = s.iter().cloned().filter(|c| c.get() < 0).count();
    println!("total={total} neg={neg}");
    std::process::exit(((total as u64 % 251) as usize + neg) as i32);
}
"#;

const CLONED_CELL_WIDTHS: &str = r#"
use std::cell::Cell;
fn main() {
    let a = [Cell::new(200u8), Cell::new(100), Cell::new(7)];
    let b = [Cell::new(-3i16), Cell::new(-30000), Cell::new(12)];
    let f = [Cell::new(1.5f64), Cell::new(-0.25), Cell::new(1e300)];
    let t = [Cell::new(true), Cell::new(false), Cell::new(true)];
    let (a, b, f, t) = std::hint::black_box((&a, &b, &f, &t));
    let sa: u32 = a.iter().cloned().map(|x| x.get() as u32).sum();
    let sb: i32 = b.iter().cloned().map(|x| x.get() as i32).sum();
    let sf: f64 = f.iter().cloned().map(|x| x.get()).fold(0.0, |p, q| p * 0.5 + q);
    let nt = t.iter().cloned().filter(|x| x.get()).count();
    println!("sa={sa} sb={sb} sf={} nt={nt}", sf.to_bits());
    std::process::exit(((sa as i64 + sb as i64 + nt as i64).rem_euclid(251)) as i32);
}
"#;

/// A derived `Clone` over a `Cell` field reaches `Cell::clone`.
const CLONED_CELL_NEWTYPE: &str = r#"
use std::cell::Cell;
#[derive(Clone)]
struct H(Cell<u32>);
fn main() {
    let s = [H(Cell::new(3)), H(Cell::new(5)), H(Cell::new(7))];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().map(|H(c)| c.get() + 1).sum();
    let mut acc = 0u32;
    for h in s.iter().cloned() { let H(c) = h; acc = acc * 7 + c.get(); }
    println!("total={total} acc={acc}");
    std::process::exit(((total + acc) % 251) as i32);
}
"#;

/// Each step writes the NEXT element through the slice before the iterator
/// clones it: the clone must copy the written value.
const CLONED_CELL_WRITTEN_DURING_DRIVE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(3u32), Cell::new(5), Cell::new(7), Cell::new(11)];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().enumerate().map(|(i, c)| {
        if i + 1 < s.len() { s[i + 1].set(s[i + 1].get() * 10 + c.get()); }
        c.get()
    }).sum();
    println!("total={total} last={}", s[3].get());
    std::process::exit((total % 251) as i32);
}
"#;

/// A `filter` ahead of `.cloned()` writes the element through its shared
/// reference; the clone that follows copies the written value.
const CLONED_CELL_WRITTEN_BEFORE_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(3u32), Cell::new(5), Cell::new(7), Cell::new(11)];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().filter(|c| { c.set(c.get() * 3); c.get() % 2 == 1 }).cloned().map(|c| c.get()).sum();
    let back: u32 = s.iter().rev().cloned().take(2).map(|c| c.get()).fold(0, |a, b| a * 100 + b);
    println!("total={total} back={back} s0={}", s[0].get());
    std::process::exit(((total + back) % 251) as i32);
}
"#;

/// The map closure after `.cloned()` panics on the third element; `Rep`
/// reports the slice while the frame unwinds.
const CLONED_CELL_CLOSURE_PANICS: &str = r#"
use std::cell::Cell;
struct Rep<'a>(&'a [Cell<u32>]);
impl Drop for Rep<'_> {
    fn drop(&mut self) { println!("rep={}", self.0.iter().map(|c| c.get()).sum::<u32>()); }
}
fn main() {
    let s = [Cell::new(3u32), Cell::new(5), Cell::new(7), Cell::new(11)];
    let s = std::hint::black_box(&s);
    let _rep = Rep(s);
    let total: u32 = s.iter().cloned().map(|c| {
        s[0].set(s[0].get() + c.get());
        if c.get() == std::hint::black_box(7) { panic!("seven") }
        c.get()
    }).sum();
    println!("total={total}");
}
"#;

/// `vec![x; n]` of a struct whose derived `Clone` reaches `Cell::clone`.
const FROM_ELEM_CELL_FIELD: &str = r#"
use std::cell::Cell;
#[derive(Clone)]
struct P { c: Cell<u32>, k: u32 }
fn main() {
    let v = vec![P { c: Cell::new(4), k: 9 }; std::hint::black_box(3)];
    v[0].c.set(40);
    let mut w = 0u32;
    for p in v.iter() { w = w * 31 + p.c.get() + p.k; }
    println!("w={w} n={}", v.len());
    std::process::exit((w % 251) as i32);
}
"#;

/// EVIDENCE BOUNDARY: a `Cell<char>` taken by value in a closure refuses at
/// -O2/-O3 (the scalar-cell layout check), whatever produced it.
const CLONED_CELL_CHAR: &str = r#"
use std::cell::Cell;
fn main() {
    let c = [Cell::new('a'), Cell::new('\u{1F600}'), Cell::new('z')];
    let c = std::hint::black_box(&c);
    let sc: u32 = c.iter().cloned().map(|x| x.get() as u32).sum();
    println!("sc={sc}");
    std::process::exit((sc % 251) as i32);
}
"#;

/// EVIDENCE BOUNDARY: `h.0.get()` borrows the `Cell` field of a by-value
/// newtype, which the snapshot guard refuses at -O0/-O1.
const CLONED_CELL_NEWTYPE_FIELD_BORROW: &str = r#"
use std::cell::Cell;
#[derive(Clone)]
struct H(Cell<u32>);
fn main() {
    let s = [H(Cell::new(3)), H(Cell::new(5)), H(Cell::new(7))];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().map(|h| h.0.get() + 1).sum();
    println!("total={total}");
    std::process::exit((total % 251) as i32);
}
"#;

/// EVIDENCE BOUNDARY: collecting the clones builds a `Vec<Cell<u32>>`, an
/// element the collect model does not store.
const CLONED_CELL_COLLECT: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(3u32), Cell::new(5), Cell::new(7), Cell::new(11)];
    let s = std::hint::black_box(&s);
    let v: Vec<Cell<u32>> = s.iter().cloned().collect();
    s[0].set(100);
    v[1].set(50);
    let a: u32 = v.iter().map(|c| c.get()).sum();
    let b: u32 = s.iter().map(|c| c.get()).sum();
    println!("a={a} b={b} n={}", v.len());
    std::process::exit(((a + b) % 251) as i32);
}
"#;

/// EVIDENCE BOUNDARY: a two-leaf element is not a modeled `Cloned` source,
/// bitwise clone or not (a derived `Copy` pair refuses the same way).
const CLONED_CELL_PAIR_STRUCT: &str = r#"
use std::cell::Cell;
#[derive(Clone)]
struct P { c: Cell<u32>, k: u32 }
fn main() {
    let s = [P { c: Cell::new(3), k: 1 }, P { c: Cell::new(5), k: 2 }, P { c: Cell::new(7), k: 3 }];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().map(|p| p.c.get() * 10 + p.k).sum();
    println!("total={total}");
    std::process::exit((total % 251) as i32);
}
"#;

/// CONTROL: `Cell<C>` over a `Copy` `C` with a hand-written `clone`. std's
/// `Cell::clone` never calls `C::clone` (`clones=0`), but the helper admits a
/// `Cell<T>` only when `T`'s own clone is bitwise, so this routes to core's
/// real `Cloned` bodies.
const CLONED_CELL_USER_COPY_CLONE: &str = r#"
use std::cell::Cell;
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CNT: AtomicU32 = AtomicU32::new(0);
#[derive(Copy)]
struct C(u32);
impl Clone for C { fn clone(&self) -> C { CNT.fetch_add(1, SeqCst); C(self.0 + 1) } }
fn main() {
    let s = [Cell::new(C(3)), Cell::new(C(5)), Cell::new(C(7))];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().map(|c| c.get().0).sum();
    let n = CNT.load(SeqCst);
    println!("total={total} clones={n}");
    std::process::exit(((total + n) % 251) as i32);
}
"#;

/// CONTROL: `RefCell::clone` borrows (and panics on a mutably borrowed cell).
const CLONED_REFCELL: &str = r#"
use std::cell::RefCell;
fn main() {
    let s = [RefCell::new(3u32), RefCell::new(5), RefCell::new(7)];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().map(|c| c.into_inner() * 2).sum();
    println!("total={total}");
    let _g = s[2].borrow_mut();
    let again: u32 = s.iter().cloned().map(|c| c.into_inner()).sum();
    println!("again={again}");
}
"#;

/// CONTROL: `OnceCell::clone` clones a set value through `C::clone`.
const CLONED_ONCECELL: &str = r#"
use std::cell::OnceCell;
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CNT: AtomicU32 = AtomicU32::new(0);
struct C(u32);
impl Clone for C { fn clone(&self) -> C { CNT.fetch_add(1, SeqCst); C(self.0 + 1) } }
fn main() {
    let s = [OnceCell::new(), OnceCell::new(), OnceCell::new()];
    let _ = s[0].set(C(3));
    let _ = s[2].set(C(7));
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().map(|c| c.get().map_or(100, |c| c.0)).sum();
    let n = CNT.load(SeqCst);
    println!("total={total} clones={n}");
    std::process::exit(((total + n) % 251) as i32);
}
"#;

/// CONTROL: a local type NAMED `Cell` whose `clone` adds one.
const CLONED_LOCAL_TYPE_NAMED_CELL: &str = r#"
mod m {
    pub struct Cell<T: Copy>(pub T);
    impl<T: Copy + std::ops::Add<Output = T> + From<u8>> Clone for Cell<T> {
        fn clone(&self) -> Self { Cell(self.0 + T::from(1)) }
    }
}
fn main() {
    let s = [m::Cell(3u32), m::Cell(5), m::Cell(7)];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().map(|c| c.0).sum();
    println!("total={total}");
    std::process::exit((total % 251) as i32);
}
"#;

/// CONTROL: `vec![x; n]` of a struct whose `Cell` field holds a `C` with a
/// hand-written `clone` keeps refusing.
const FROM_ELEM_CELL_USER_COPY_FIELD: &str = r#"
use std::cell::Cell;
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CNT: AtomicU32 = AtomicU32::new(0);
#[derive(Copy)]
struct C(u32);
impl Clone for C { fn clone(&self) -> C { CNT.fetch_add(1, SeqCst); C(self.0 + 1) } }
#[derive(Clone)]
struct Q { c: Cell<C>, k: u32 }
fn main() {
    let v = vec![Q { c: Cell::new(C(4)), k: 9 }; std::hint::black_box(3)];
    v[0].c.set(C(40));
    let mut w = 0u32;
    for q in v.iter() { w = w * 31 + q.c.get().0 + q.k; }
    let n = CNT.load(SeqCst);
    println!("w={w} clones={n}");
    std::process::exit(((w + n) % 251) as i32);
}
"#;

/// A `filter` predicate writes the clone it receives as `&Cell<u32>`; the
/// kept clone is the written one (forward, reversed, chained filters), and
/// the slice keeps its values.
const CLONED_CELL_FILTER_WRITES_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(1u32), Cell::new(2), Cell::new(3), Cell::new(4)];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().filter(|c| { c.set(c.get() * 10); c.get() != 30 }).map(|c| c.get()).sum();
    let n = s.iter().cloned().filter(|c| { c.set(c.get() + 1); true }).filter(|c| c.get() % 2 == 0).count();
    let r: u32 = s.iter().rev().cloned().filter(|c| { c.set(c.get() * 7); c.get() > 10 }).map(|c| c.get()).fold(0u32, |a, b| a * 100 + b);
    let orig: u32 = s.iter().map(|c| c.get()).sum();
    println!("total={total} n={n} r={r} orig={orig}");
    std::process::exit(((total + n as u32 + r) % 251) as i32);
}
"#;

/// The same over `Cell<i64>`, into `count` and `fold`.
const CLONED_CELL_I64_FILTER_WRITES_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(-1i64), Cell::new(2), Cell::new(-3), Cell::new(4)];
    let s = std::hint::black_box(&s);
    let n = s.iter().cloned().filter(|c| { c.set(-c.get()); c.get() > 0 }).count();
    let pos: i64 = s.iter().cloned().filter(|c| { c.set(c.get() - 10); c.get() < 0 }).map(|c| c.get()).fold(0i64, |a, x| a * 3 + x);
    println!("n={n} pos={pos}");
    std::process::exit(((n as i64 * 31 + pos).rem_euclid(251)) as i32);
}
"#;

/// `skip_while` / `take_while` predicates write the clone; the yielded items
/// are the written ones, including the one that ends the skipping.
const CLONED_CELL_TAKE_SKIP_WHILE_WRITE_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(1u32), Cell::new(2), Cell::new(3), Cell::new(4)];
    let s = std::hint::black_box(&s);
    let a: u32 = s.iter().cloned().skip_while(|c| { c.set(c.get() + 70); c.get() < 72 }).map(|c| c.get()).fold(0u32, |a, b| a * 1000 + b);
    let b: u32 = s.iter().cloned().take_while(|c| { c.set(c.get() * 9); c.get() < 30 }).map(|c| c.get()).fold(0u32, |a, b| a * 100 + b);
    let c: u32 = s.iter().cloned().take_while(|c| { c.set(c.get() * 3); c.get() < 10 }).map(|c| c.get()).sum();
    println!("a={a} b={b} c={c} s0={}", s[0].get());
    std::process::exit(((a + b + c) % 251) as i32);
}
"#;

/// An `inspect` closure writes the clone; the items after it are the written
/// ones.
const CLONED_CELL_INSPECT_WRITES_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(1u32), Cell::new(2), Cell::new(3), Cell::new(4)];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().inspect(|c| c.set(c.get() + 100)).map(|c| c.get()).sum();
    let m: u32 = s.iter().cloned().inspect(|c| c.set(c.get() << 4)).filter(|c| c.get() > 40).map(|c| c.get()).sum();
    println!("total={total} m={m}");
    std::process::exit(((total + m) % 251) as i32);
}
"#;

/// A `find` predicate writes the clone; `find` returns the written one. (Before
/// the `Cell` admission core's real `Cloned`/`find` bodies built this and
/// matched; the modeled drive must too.)
const CLONED_CELL_FIND_WRITES_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(1u32), Cell::new(2), Cell::new(3), Cell::new(4)];
    let s = std::hint::black_box(&s);
    let f = match s.iter().cloned().find(|c| { c.set(c.get() * 3); c.get() > 5 }) { Some(c) => c.get(), None => 0 };
    let g = s.iter().cloned().find(|c| { c.set(c.get() + 40); c.get() > 1000 }).map_or(7, |c| c.get());
    println!("f={f} g={g} s0={}", s[0].get());
    std::process::exit(((f + g) % 251) as i32);
}
"#;

/// `max_by_key` / `min_by_key` key closures write the clone; the result is the
/// written item (core pairs `(f(&x), x)`).
const CLONED_CELL_BY_KEY_WRITES_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(5u32), Cell::new(2), Cell::new(9), Cell::new(1)];
    let s = std::hint::black_box(&s);
    let a = s.iter().cloned().max_by_key(|c| { c.set(c.get() + 7); c.get() }).map_or(0, |c| c.get());
    let b = s.iter().cloned().min_by_key(|c| { c.set(c.get() * 2); c.get() }).map_or(0, |c| c.get());
    println!("a={a} b={b}");
    std::process::exit(((a * 10 + b) % 251) as i32);
}
"#;

/// `max_by` / `min_by` comparators write the running best (`a`) or the new
/// item (`b`); the kept item is the written one.
const CLONED_CELL_BY_CMP_WRITES_BOTH: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(5u32), Cell::new(1), Cell::new(4), Cell::new(2)];
    let s = std::hint::black_box(&s);
    let m = s.iter().cloned().max_by(|a, b| { b.set(b.get() + 10); a.get().cmp(&b.get()) }).map_or(0, |c| c.get());
    let n = s.iter().cloned().min_by(|a, b| { a.set(a.get() * 3); a.get().cmp(&b.get()) }).map_or(0, |c| c.get());
    let k = s.iter().cloned().max_by(|a, b| { a.set(a.get() + 1); a.get().cmp(&b.get()) }).map_or(0, |c| c.get());
    println!("m={m} n={n} k={k}");
    std::process::exit(((m * 7 + n + k) % 251) as i32);
}
"#;

/// A `filter` writes the `Cell` field of a derived newtype clone.
const CLONED_CELL_NEWTYPE_FILTER_WRITES_CLONE: &str = r#"
use std::cell::Cell;
#[derive(Clone)]
struct H(Cell<u32>);
fn main() {
    let s = [H(Cell::new(3)), H(Cell::new(5)), H(Cell::new(7))];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().filter(|h| { h.0.set(h.0.get() + 1000); true }).map(|H(c)| c.get()).sum();
    println!("total={total}");
    std::process::exit((total % 251) as i32);
}
"#;

/// Clones of `Cell<u8|f64|bool|i16>` written by `inspect`, `filter` and
/// `skip_while`.
const CLONED_CELL_WIDTHS_WRITE_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let a = [Cell::new(200u8), Cell::new(100), Cell::new(7)];
    let f = [Cell::new(1.5f64), Cell::new(-0.25), Cell::new(8.0)];
    let t = [Cell::new(true), Cell::new(false), Cell::new(true)];
    let w = [Cell::new(-3i16), Cell::new(300), Cell::new(-7)];
    let (a, f, t, w) = std::hint::black_box((&a, &f, &t, &w));
    let sa: u32 = a.iter().cloned().inspect(|x| x.set(x.get() / 2)).map(|x| x.get() as u32).sum();
    let sf: f64 = f.iter().cloned().filter(|x| { x.set(x.get() * 4.0); true }).map(|x| x.get()).fold(0.0, |p, q| p + q);
    let nt = t.iter().cloned().filter(|x| { x.set(!x.get()); true }).filter(|x| x.get()).count();
    let sw: i32 = w.iter().cloned().skip_while(|x| { x.set(x.get() * 2); x.get() < 0 }).map(|x| x.get() as i32).sum();
    println!("sa={sa} sf={} nt={nt} sw={sw}", sf.to_bits());
    std::process::exit(((sa as i64 + sf as i64 + nt as i64 + sw as i64).rem_euclid(251)) as i32);
}
"#;

/// A writing `filter` / `inspect` ahead of `last`, `any` and `position`.
const CLONED_CELL_WRITING_FILTER_THEN_LAST_ANY: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(3u32), Cell::new(5), Cell::new(7), Cell::new(11)];
    let s = std::hint::black_box(&s);
    let l = s.iter().cloned().filter(|c| { c.set(c.get() << 4); true }).last().map_or(0, |c| c.get());
    let any = s.iter().cloned().filter(|c| { c.set(c.get() + 1); true }).any(|c| c.get() == 4);
    let p = s.iter().cloned().inspect(|c| c.set(c.get() * 2)).position(|c| c.get() == 14).unwrap_or(99);
    println!("l={l} any={any} p={p}");
    std::process::exit(((l + any as u32 + p as u32) % 251) as i32);
}
"#;

/// EVIDENCE BOUNDARY: a `for` loop over a writing `filter` refuses. core's
/// `Filter::next` hands `find` a `&mut` predicate, which the `find` model does
/// not take (-O0/-O1), and the `try_fold` it inlines into at -O2/-O3 captures
/// that predicate by value.
const CLONED_CELL_FOR_LOOP_WRITING_FILTER: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(1u32), Cell::new(2), Cell::new(3), Cell::new(4), Cell::new(5)];
    let s = std::hint::black_box(&s);
    let mut acc = 0u32;
    for c in s.iter().cloned().filter(|c| { c.set(c.get() + 100); c.get() % 2 == 1 }) {
        acc = acc.wrapping_mul(7).wrapping_add(c.get());
    }
    println!("acc={acc} s0={}", s[0].get());
    std::process::exit((acc % 251) as i32);
}
"#;

/// A `map` closure returns a fresh `Cell`, which the `filter` after it writes.
const MAP_TO_CELL_FILTER_WRITES_ITEM: &str = r#"
use std::cell::Cell;
fn main() {
    let s0 = [1u32, 2, 3, 4];
    let s: &[u32] = std::hint::black_box(&s0);
    let total: u32 = s.iter().map(|&x| Cell::new(x)).filter(|c| { c.set(c.get() * 10); true }).map(|c| c.get()).sum();
    println!("total={total}");
    std::process::exit((total % 251) as i32);
}
"#;

/// REFUSAL: a `filter` writes the `Cell` half of an `(index, clone)` tuple
/// item. The drive's tuple argument is a by-value copy it does not read back,
/// so it refuses by name at -O0/-O1; -O2/-O3 refuse another construct first.
const CLONED_CELL_ENUMERATE_FILTER_WRITES_CLONE: &str = r#"
use std::cell::Cell;
fn main() {
    let s = [Cell::new(1u32), Cell::new(2), Cell::new(3), Cell::new(4)];
    let s = std::hint::black_box(&s);
    let total: u32 = s.iter().cloned().enumerate().filter(|(i, c)| { c.set(c.get() + *i as u32 * 100); true }).map(|(_, c)| c.get()).sum();
    println!("total={total}");
    std::process::exit((total % 251) as i32);
}
"#;

fn cell_clone_rows() -> Vec<Row> {
    let row = |name, src, expects: [Expect; 4]| Row {
        name,
        src,
        abort: Some(expects),
        unwind: Some(expects),
        overflow_checks: false,
    };
    let snapshot = Refuse("TCG-INTERIOR-MUT-SNAPSHOT", "");
    let layout = Refuse("TCG-SCALAR-CELL-LAYOUT", "");
    let collect = Refuse(
        "TCG-MIR-UNSUPPORTED",
        "Vec::collect of a non-integer/non-float-scalar element std::cell::Cell<u32>",
    );
    let tuple_item = Refuse("TCG-ITER-INTERIOR-MUT-ITEM", "`filter` hands its closure");
    let receiver = Refuse(
        "TCG-MIR-UNSUPPORTED",
        "closure call receiver is not a place operand",
    );
    let option_cell = Refuse(
        "TCG-MIR-UNSUPPORTED",
        "Ty::core::option::Option<core::cell::Cell<u32>>",
    );
    let find_payload = Refuse(
        "TCG-MIR-UNSUPPORTED",
        "iterator find payload is not a closure",
    );
    let by_value_check = Refuse(
        "TCG-MIR-UNSUPPORTED",
        "iterator try_fold with a by-value capturing check closure is not modeled",
    );
    vec![
        row("cloned_cell_u32", CLONED_CELL_U32, M4),
        row("cloned_cell_i64", CLONED_CELL_I64, M4),
        row("cloned_cell_widths", CLONED_CELL_WIDTHS, M4),
        row("cloned_cell_newtype", CLONED_CELL_NEWTYPE, M4),
        row(
            "cloned_cell_written_during_drive",
            CLONED_CELL_WRITTEN_DURING_DRIVE,
            M4,
        ),
        row(
            "cloned_cell_written_before_clone",
            CLONED_CELL_WRITTEN_BEFORE_CLONE,
            M4,
        ),
        row("cloned_cell_closure_panics", CLONED_CELL_CLOSURE_PANICS, M4),
        row("from_elem_cell_field", FROM_ELEM_CELL_FIELD, M4),
        row(
            "cloned_cell_filter_writes_clone",
            CLONED_CELL_FILTER_WRITES_CLONE,
            M4,
        ),
        row(
            "cloned_cell_i64_filter_writes_clone",
            CLONED_CELL_I64_FILTER_WRITES_CLONE,
            M4,
        ),
        row(
            "cloned_cell_take_skip_while_write_clone",
            CLONED_CELL_TAKE_SKIP_WHILE_WRITE_CLONE,
            M4,
        ),
        row(
            "cloned_cell_inspect_writes_clone",
            CLONED_CELL_INSPECT_WRITES_CLONE,
            M4,
        ),
        row(
            "cloned_cell_find_writes_clone",
            CLONED_CELL_FIND_WRITES_CLONE,
            M4,
        ),
        row(
            "cloned_cell_by_key_writes_clone",
            CLONED_CELL_BY_KEY_WRITES_CLONE,
            M4,
        ),
        row(
            "cloned_cell_by_cmp_writes_both",
            CLONED_CELL_BY_CMP_WRITES_BOTH,
            M4,
        ),
        row(
            "cloned_cell_newtype_filter_writes_clone",
            CLONED_CELL_NEWTYPE_FILTER_WRITES_CLONE,
            M4,
        ),
        row(
            "cloned_cell_widths_write_clone",
            CLONED_CELL_WIDTHS_WRITE_CLONE,
            M4,
        ),
        row(
            "cloned_cell_writing_filter_then_last_any",
            CLONED_CELL_WRITING_FILTER_THEN_LAST_ANY,
            [Match, Match, option_cell, option_cell],
        ),
        row(
            "map_to_cell_filter_writes_item",
            MAP_TO_CELL_FILTER_WRITES_ITEM,
            M4,
        ),
        row(
            "cloned_cell_enumerate_filter_writes_clone",
            CLONED_CELL_ENUMERATE_FILTER_WRITES_CLONE,
            [tuple_item, tuple_item, receiver, receiver],
        ),
        row(
            "cloned_cell_for_loop_writing_filter",
            CLONED_CELL_FOR_LOOP_WRITING_FILTER,
            [find_payload, find_payload, by_value_check, by_value_check],
        ),
        row(
            "cloned_cell_char",
            CLONED_CELL_CHAR,
            [Match, Match, layout, layout],
        ),
        row(
            "cloned_cell_newtype_field_borrow",
            CLONED_CELL_NEWTYPE_FIELD_BORROW,
            [snapshot, snapshot, Match, Match],
        ),
        row("cloned_cell_collect", CLONED_CELL_COLLECT, [collect; 4]),
        row(
            "cloned_cell_pair_struct",
            CLONED_CELL_PAIR_STRUCT,
            UNMODELED_SUM_FOLD,
        ),
        row(
            "cloned_cell_user_copy_clone",
            CLONED_CELL_USER_COPY_CLONE,
            UNMODELED_SUM_FOLD,
        ),
        row("cloned_refcell", CLONED_REFCELL, UNMODELED_SUM_FOLD),
        row("cloned_oncecell", CLONED_ONCECELL, UNMODELED_SUM_FOLD),
        row(
            "cloned_local_type_named_cell",
            CLONED_LOCAL_TYPE_NAMED_CELL,
            UNMODELED_SUM_FOLD,
        ),
        row(
            "from_elem_cell_user_copy_field",
            FROM_ELEM_CELL_USER_COPY_FIELD,
            FE_REFUSE,
        ),
    ]
}

// Native tuple lanes must carry the component's bits, including narrow values
// and floats, rather than an ill-typed `copy i64`. Before this fix all five
// scalar rows below refused that copy at O0-O3; the word/reference controls
// already matched. The original Cell mutation rows above remain unchanged.
fn tuple_scalar_rows() -> Vec<Row> {
    [
        (
            "tuple_u32",
            r#"fn main() {
                let s = [3u32, 5, 7];
                let total: u32 = std::hint::black_box(&s).iter().map(|x| *x)
                    .enumerate().map(|(i, x)| x + i as u32).sum();
                assert_eq!(total, 18);
                println!("{total}");
            }"#,
        ),
        (
            "tuple_i32",
            r#"fn main() {
                let s = [-100i32, 4, 7];
                let total: i32 = std::hint::black_box(&s).iter().map(|x| *x)
                    .enumerate().map(|(i, x)| x + i as i32).sum();
                assert_eq!(total, -86);
                println!("{total}");
            }"#,
        ),
        (
            "tuple_bool",
            r#"fn main() {
                let s = [true, false, true];
                let total: usize = std::hint::black_box(&s).iter().map(|x| *x)
                    .enumerate().map(|(i, x)| i + x as usize).sum();
                assert_eq!(total, 5);
                println!("{total}");
            }"#,
        ),
        (
            "tuple_f32",
            r#"fn main() {
                let s = [1.5f32, -2.25, 7.0];
                let total: f32 = std::hint::black_box(&s).iter().map(|x| *x)
                    .enumerate().map(|(i, x)| x + i as f32).sum();
                assert_eq!(total.to_bits(), 1091829760);
                println!("{}", total.to_bits());
            }"#,
        ),
        (
            "tuple_f64",
            r#"fn main() {
                let s = [1.5f64, -2.25, 7.0];
                let total: f64 = std::hint::black_box(&s).iter().map(|x| *x)
                    .enumerate().map(|(i, x)| x + i as f64).sum();
                assert_eq!(total.to_bits(), 4621396905123905536);
                println!("{}", total.to_bits());
            }"#,
        ),
        (
            "tuple_word_control",
            r#"fn main() {
                let s = [3u64, 5, 7];
                let total: u64 = std::hint::black_box(&s).iter().map(|x| *x)
                    .enumerate().map(|(i, x)| x + i as u64).sum();
                assert_eq!(total, 18);
                println!("{total}");
            }"#,
        ),
        (
            "tuple_reference_control",
            r#"fn main() {
                let s = [3u32, 5, 7];
                let total: u32 = std::hint::black_box(&s).iter()
                    .enumerate().map(|(i, x)| *x + i as u32).sum();
                assert_eq!(total, 18);
                println!("{total}");
            }"#,
        ),
    ]
    .into_iter()
    .map(|(name, src)| Row {
        name,
        src,
        abort: Some(M4),
        unwind: Some(M4),
        overflow_checks: false,
    })
    .collect()
}

// ---------------------------------------------------------------- the runner

/// How a binary ended.
#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    stderr: String,
}

fn compile(
    dir: &Path,
    exe: &str,
    src: &Path,
    strategy: Strategy,
    opt: u32,
    overflow_checks: bool,
    backend: Option<(&Path, &str)>,
) -> Result<PathBuf, String> {
    let out = dir.join(exe);
    let mut command = toolchain_support::rustc_command();
    command
        .args([
            "--target",
            TARGET,
            "--crate-type",
            "bin",
            "-Ccodegen-units=1",
        ])
        .arg(strategy.flag())
        .arg(format!("-Copt-level={opt}"))
        .arg(if overflow_checks {
            "-Coverflow-checks=on"
        } else {
            "-Coverflow-checks=off"
        });
    if let Some((dylib, knobs)) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(dylib);
        command.arg(arg).arg(knobs);
    }
    command.arg("-o").arg(&out).arg(src);
    let output = command.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(out)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn run(exe: &Path) -> Ending {
    let output = Command::new(exe).output().expect("run a compiled guest");
    Ending {
        code: output.status.code(),
        signal: output.status.signal(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: without_thread_ids(&String::from_utf8_lossy(&output.stderr)),
    }
}

/// A panic message names the thread as `thread 'main' (<id>)`, where the id is
/// the OS thread id of that run; it is replaced by `(TID)` so that two runs'
/// messages compare by their text and location alone.
fn without_thread_ids(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find("thread '") {
        let (head, tail) = rest.split_at(at);
        out.push_str(head);
        let name_end = tail["thread '".len()..]
            .find('\'')
            .map(|end| "thread '".len() + end + 1);
        let Some(name_end) = name_end else {
            out.push_str(tail);
            return out;
        };
        out.push_str(&tail[..name_end]);
        let after = &tail[name_end..];
        let digits = after
            .strip_prefix(" (")
            .map(|inner| inner.bytes().take_while(u8::is_ascii_digit).count())
            .unwrap_or(0);
        if digits > 0 && after[2 + digits..].starts_with(')') {
            out.push_str(" (TID)");
            rest = &after[3 + digits..];
        } else {
            rest = after;
        }
    }
    out.push_str(rest);
    out
}

/// One row at one level under one strategy: `Ok(true)` when it built and
/// matched, `Ok(false)` when it refused as expected, `Err` on any mismatch.
fn check_cell(
    root: &Path,
    row: &Row,
    strategy: Strategy,
    opt: u32,
    expect: Expect,
    dylib: &Path,
    knobs: &str,
) -> Result<bool, String> {
    let label = format!("{} {} O{opt}", row.name, strategy.label());
    let dir = root.join(format!("{}-{}-O{opt}", row.name, strategy.label()));
    std::fs::create_dir_all(&dir).expect("cell dir");
    let src = dir.join("main.rs");
    std::fs::write(&src, row.src).expect("write the guest");
    let oracle = compile(&dir, "llvm", &src, strategy, opt, row.overflow_checks, None)
        .map_err(|e| format!("{label}: the LLVM oracle failed to compile:\n{e}"))?;
    let oracle = run(&oracle);
    if row.name == "cached_key_forced_panic_cleanup"
        && (oracle.code != Some(101)
            || oracle.signal.is_some()
            || oracle.stdout != "calls=4 log=3127 cache_alloc=1 cache_frees=1\n"
            || !oracle.stderr.contains("cached-key forced panic"))
    {
        return Err(format!(
            "{label}: the independent oracle must really panic after four keys and free the cache before the caller guard: {oracle:?}"
        ));
    }
    let bridge = compile(
        &dir,
        "bridge",
        &src,
        strategy,
        opt,
        row.overflow_checks,
        Some((dylib, knobs)),
    );
    match (expect, bridge) {
        (Match, Ok(exe)) => {
            let ending = run(&exe);
            if ending == oracle {
                Ok(true)
            } else {
                Err(format!(
                    "{label}: DIVERGES — LLVM {oracle:?}, trust-cg {ending:?}"
                ))
            }
        }
        (Match, Err(stderr)) => Err(format!(
            "{label}: must build and match LLVM, but the bridge refused:\n{}",
            first_lines(&stderr)
        )),
        (Refuse(code, _), Ok(exe)) => {
            let ending = run(&exe);
            Err(format!(
                "{label}: must refuse with [{code}], but the bridge built a binary \
                 ({}; LLVM {oracle:?}, trust-cg {ending:?})",
                if ending == oracle {
                    "matching"
                } else {
                    "DIVERGING"
                }
            ))
        }
        (Refuse(code, text), Err(stderr)) => {
            let named = stderr.contains(&format!("[{code}]")) && stderr.contains(text);
            let crashed =
                stderr.contains("internal compiler error") || stderr.contains("panicked at");
            if named && !crashed {
                Ok(false)
            } else {
                Err(format!(
                    "{label}: refused, but not with [{code}]{}:\n{}",
                    if text.is_empty() {
                        String::new()
                    } else {
                        format!(" naming {text:?}")
                    },
                    first_lines(&stderr)
                ))
            }
        }
    }
}

fn first_lines(text: &str) -> String {
    text.lines().take(12).collect::<Vec<_>>().join("\n")
}

/// Run every cell of `rows` on a small worker pool and assert the outcome.
/// Returns `(cells, matched, refused)`.
fn run_rows(test: &str, rows: &[Row]) -> (usize, usize, usize) {
    darwin_native::require(test, &[]);
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let root = std::env::temp_dir().join(format!("tcg_clone_sort_{test}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let mut jobs = Vec::new();
    for row in rows {
        for (strategy, expects) in [(Strategy::Abort, row.abort), (Strategy::Unwind, row.unwind)] {
            if let Some(expects) = expects {
                for (opt, expect) in expects.into_iter().enumerate() {
                    jobs.push((row, strategy, opt as u32, expect));
                }
            }
        }
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results = std::sync::Mutex::new(Vec::new());
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .clamp(1, 6);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    let Some(&(row, strategy, opt, expect)) = jobs.get(index) else {
                        break;
                    };
                    let outcome = check_cell(&root, row, strategy, opt, expect, &dylib, &knobs);
                    results.lock().expect("results").push(outcome);
                }
            });
        }
    });
    let results = results.into_inner().expect("results");
    let _ = std::fs::remove_dir_all(&root);
    let failures: Vec<&String> = results.iter().filter_map(|r| r.as_ref().err()).collect();
    assert!(
        failures.is_empty(),
        "{} of {} cells disagree:\n{}",
        failures.len(),
        results.len(),
        failures
            .iter()
            .map(|f| f.as_str())
            .collect::<Vec<_>>()
            .join("\n\n")
    );
    let matched = results.iter().filter(|r| matches!(r, Ok(true))).count();
    (results.len(), matched, results.len() - matched)
}

#[test]
fn tuple_items_keep_their_scalar_bits_aarch64() {
    let rows = tuple_scalar_rows();
    let (cells, matched, refused) = run_rows("tuple_items_keep_their_scalar_bits_aarch64", &rows);
    eprintln!(
        "CLONE_SORT_TUPLE_SCALARS rows={} cells={cells} matched={matched} refused={refused} opts=0,1,2,3 strategies=abort,unwind",
        rows.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn vec_from_elem_runs_the_user_clone_or_refuses_aarch64() {
    let rows = from_elem_rows();
    let (cells, matched, refused) = run_rows(
        "vec_from_elem_runs_the_user_clone_or_refuses_aarch64",
        &rows,
    );
    eprintln!(
        "CLONE_SORT_FROM_ELEM rows={} cells={cells} matched={matched} refused={refused} opts=0,1,2,3 strategies=abort,unwind",
        rows.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn cell_clones_are_bitwise_copies_aarch64() {
    let rows = cell_clone_rows();
    let (cells, matched, refused) = run_rows("cell_clones_are_bitwise_copies_aarch64", &rows);
    eprintln!(
        "CLONE_SORT_CELL_CLONES rows={} cells={cells} matched={matched} refused={refused} opts=0,1,2,3 strategies=abort,unwind",
        rows.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn slice_sorts_keep_std_order_and_key_calls_aarch64() {
    let rows = sort_rows();
    let (cells, matched, refused) =
        run_rows("slice_sorts_keep_std_order_and_key_calls_aarch64", &rows);
    eprintln!(
        "CLONE_SORT_SLICE_SORTS rows={} cells={cells} matched={matched} refused={refused} opts=0,1,2,3 strategies=abort,unwind",
        rows.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
