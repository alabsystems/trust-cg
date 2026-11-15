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

// The bridge's iterator drives over a `Range` or slice source whose `map`
// produces an item with a user `Drop`, against LLVM, when a payload the drive
// calls unwinds.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A by-reference payload (a `find` predicate, a `filter` / `take_while` /
// `skip_while` predicate, an `inspect` closure) borrows an item the drive
// holds in memory; std's frame owns that item while the payload runs and drops
// it when the payload unwinds. A by-value payload (`any`, `all`, `position`,
// `fold`, `for_each`) owns the item itself and drops it in its own body. A
// payload handed `&C` for an interior-mutable `C(Cell<u32>)` (`!Freeze`) may
// write it, and std then keeps, returns, compares or drops the written item
// (`INTERIOR_MUT_CASES`; the `cell_*_writes_then_unwinds` rows of `HELD_CASES`
// drop it while unwinding). A terminal that carries a value needing drop
// across the adapter closures (a `fold` / `reduce` accumulator, the result
// `last` keeps) has no pad that drops it, so it refuses under `panic=unwind`
// (`REFUSAL_CASES`), and a held item in a body without EH lowering refuses by
// site (`NO_EH_LIBRARY`). A `collect` owns the `Vec` it builds and frees it
// when a payload unwinds, after a held item's pad has dropped the item
// (`COLLECT_CASES`); without EH lowering it refuses (`NO_EH_COLLECT_LIBRARY`).
//
// MEASURED (Trust pack 9192, `no-proof-certs`, this file's test binary run
// beside each backend) at origin/main b53f9641f: 71 of the 95 `HELD` cells
// this file marks `Match` under `panic=unwind` diverged, every one but the
// `find` rows, `filter_fold`, `inspect_count` and the `cell_find` /
// `cell_inspect` rows at -O2/-O3, where std's own closures hold the item: the
// item in flight was never dropped (`log: ... 203` against LLVM's
// `log: ... 203 3`); when its destructor panicked during that unwind LLVM
// aborted (a panic during cleanup) and the bridge exited 101; in an
// `extern "C"` frame LLVM printed the in-flight item's drop before the abort
// and the bridge did not. 44 of the 72 `INTERIOR_MUT_CASES` cells failed: 40
// compiled and kept, returned or dropped the item as stored before the
// payload wrote it (`cell_filter_count`: LLVM `log: 11 12 13 14 15 103`,
// bridge `log: 1 2 3 4 5 103`), and the tuple row compiled. 34 of the 56
// `REFUSAL_CASES` cells failed: the 14 `[TCG-ITER-UNWIND-CARRY]` cells
// compiled (a `fold` over a `D` accumulator left LLVM's `53` undropped),
// `refuse_tuple_inspect` compiled at -O0 and leaked the item, three cells
// refused under another code, and no `[TCG-ITER-UNWIND-DROP]` site existed.
// At 3bbbfe2bb (the held-item pad alone): 18 `HELD` cells failed (the 16
// `cell_*_writes_then_unwinds` cells, whose rejected items were dropped as
// stored, and `extend_from_cleanup_free_frame` at -O0/-O1, refused with
// `[TCG-ITER-UNWIND-DROP]` because the drive's chain is `extend`'s second
// argument), the same 44 `INTERIOR_MUT_CASES` cells, and the 14
// `[TCG-ITER-UNWIND-CARRY]` cells. Every control cell matched, or refused as
// it does now, at both. At dcf9d45e5 (backend sha256 7bf62f91...), 24 of the
// 36 `COLLECT_CASES` unwind cells diverged: every `collect` whose payload
// unwound after the first push left the `Vec`'s buffer allocated (`live=7`
// against LLVM's `live=6`), the held-item row too, at -O0..-O3; and the
// collect library compiled without EH lowering at -O0/-O1.
//
// Each `Match` cell must compile and match LLVM on stdout, exit code and
// killing signal. Each refusal cell must fail closed with the named
// `[TCG-...]` code at the level it lists, and every function the bridge
// refuses there must name that code or one of the cell's reasons. A
// `[TCG-MIR-UNSUPPORTED]` cell is a drive this backend does not lower at
// all, pinned by the reason the bridge gives for it, so a refusal raised by
// one of this file's own drives at that level fails the cell.
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

use Want::{Match, Refuse};

const MATCH4: [Want; 4] = [Match; 4];

/// The `[TCG-MIR-UNSUPPORTED]` reasons of the drives this backend does not
/// lower at all. A cell that expects one must refuse for exactly that reason:
/// a refusal raised by this file's own drives (`[TCG-ITER-UNWIND-DROP]`,
/// `[TCG-ITER-DISCARD-DROP]`, `[TCG-ITER-UNWIND-CARRY]`, ...) names none of them.
const TRY_FOLD_BY_VALUE_CHECK: &str =
    "iterator try_fold with a by-value capturing check closure is not modeled";
const FOLD_NON_SCALAR_ACCUMULATOR: &str = "iterator fold over a non-scalar accumulator";
const SPEC_EXTEND: &str = "Vec::<u32>::spec_extend is not an intercepted Vec method";
const REV_INNER_NOT_A_PLACE: &str = "iterator rev inner argument is not a place";
const SKIP_INNER_NOT_A_PLACE: &str = "iterator skip inner argument is not a place";
const MAX_BY_KEY_SELF_NOT_A_PLACE: &str = "iterator max_by_key self argument is not a place";
const CLOSURE_RECEIVER_NOT_A_PLACE: &str = "closure call receiver is not a place operand";
const OPTION_OF_REFERENCE_ITEM: &str = "Ty::core::option::Option<&'{erased} D>";
const OPTION_OF_ITEM: &str = "Ty::core::option::Option<D>";
/// The `inspect` closure of `refuse_nested_drop_inspect`, which reads `o.0 .0`
/// through its `&Outer`, inlined at -O2/-O3.
const NESTED_FIELD_PLACE_PROJECTION: &str = "Place projection";

/// A drive this backend refuses for `reason`.
const fn unsupported(reason: &'static [&'static str]) -> Want {
    Refuse("TCG-MIR-UNSUPPORTED", reason)
}

/// What -O2/-O3 inline these terminals into is a drive this backend refuses
/// for `reason`: a `try_fold` with a by-value capturing check closure (`any`,
/// `position`, `find` after `filter`), a `fold` over a non-scalar accumulator
/// (`for_each`), `Vec::spec_extend` (`extend`), a `max_by_key` or a `last`
/// whose receiver or result is no place the drive reads.
const fn low_match_high_unsupported(reason: &'static [&'static str]) -> [Want; 4] {
    [Match, Match, unsupported(reason), unsupported(reason)]
}
/// -O0/-O1 refuse in a closure body that borrows its scalarized `Cell`
/// argument (`[TCG-INTERIOR-MUT-SNAPSHOT]`); -O2/-O3 must match.
const LOW_SNAPSHOT_HIGH_MATCH: [Want; 4] = [
    Refuse("TCG-INTERIOR-MUT-SNAPSHOT", &[]),
    Refuse("TCG-INTERIOR-MUT-SNAPSHOT", &[]),
    Match,
    Match,
];
/// A terminal that carries a value needing drop across the chain's adapter
/// closures refuses under `panic=unwind` at -O0/-O1, where the bridge drives
/// the adapters itself; at -O2/-O3 std's own `fold` glue holds the value.
const LOW_CARRY_HIGH_MATCH: [Want; 4] = [
    Refuse("TCG-ITER-UNWIND-CARRY", &[]),
    Refuse("TCG-ITER-UNWIND-CARRY", &[]),
    Match,
    Match,
];

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

/// Both strategies, the same expectation per level.
const fn alike(name: &'static str, body: &'static str, wants: [Want; 4]) -> Case {
    Case {
        name,
        body,
        abort: Some(wants),
        unwind: Some(wants),
    }
}

/// A payload unwinds while the drive holds an item that needs drop: std drops
/// that item before the unwind leaves the drive (and aborts when its
/// destructor panics there). Under `panic=abort` the same guests abort at the
/// panic.
const HELD_CASES: &[Case] = &[
    both(
        "find_range",
        r#"fn main() {
    let _r = Rep;
    let hit = (1..6u32).map(|i| D(i)).find(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    both(
        "find_slice",
        r#"fn main() {
    let _r = Rep;
    let v = [1u32, 2, 3, 4, 5];
    let hit = v.iter().map(|&i| D(i)).find(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    both(
        "find_range_inclusive",
        r#"fn main() {
    let _r = Rep;
    let hit = (1..=5u32).map(|i| D(i)).find(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    Case {
        name: "find_rev_range",
        body: r#"fn main() {
    let _r = Rep;
    let hit = (1..6u32).rev().map(|i| D(i)).find(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
        abort: Some([Match, unsupported(&[REV_INNER_NOT_A_PLACE]), Match, Match]),
        unwind: Some([Match, unsupported(&[REV_INNER_NOT_A_PLACE]), Match, Match]),
    },
    // A `&mut self` receiver: the caller's iterator, drained in place.
    both(
        "find_by_mut_ref",
        r#"fn main() {
    let _r = Rep;
    let mut it = (1..6u32).map(|i| D(i));
    let hit = it.find(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    // The `find` call's own unwind action is `Continue` and its frame has no
    // cleanup of its own: the drive's pad resumes the unwind.
    both(
        "find_from_cleanup_free_frame",
        r#"#[inline(never)]
fn first(n: u32) -> Option<D> {
    (1..n).map(|i| D(i)).find(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false })
}
fn main() {
    let _r = Rep;
    let h = first(std::hint::black_box(6));
    log(100 + h.is_some() as u32);
}
"#,
    ),
    // The held item's destructor panics while the predicate's panic unwinds:
    // a panic during cleanup, which aborts.
    both(
        "find_drop_panics_during_unwind",
        r#"struct P(u32);
impl Drop for P { fn drop(&mut self) { log(self.0); if self.0 == 3 { panic!("drop"); } } }
fn main() {
    let _r = Rep;
    let hit = (1..6u32).map(|i| P(i)).find(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    // A frame that cannot unwind (`Terminate` action): the item is dropped,
    // then the process aborts.
    both(
        "find_in_extern_c_frame",
        r#"struct Q(u32);
impl Drop for Q { fn drop(&mut self) { println!("drop {}", self.0); } }
extern "C" fn nounwind(n: u32) -> u32 {
    (1..n).map(|i| Q(i)).find(|d| { if d.0 == 3 { panic!("p"); } false }).map_or(0, |q| q.0)
}
fn main() {
    println!("r {}", nounwind(std::hint::black_box(6)));
}
"#,
    ),
    both(
        "filter_count",
        r#"fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } d.0 % 2 == 1 }).count();
    log(100 + n as u32);
}
"#,
    ),
    both(
        "filter_sum",
        r#"fn main() {
    let _r = Rep;
    let n: u32 = (1..6u32).map(|i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } d.0 % 2 == 1 }).map(|d| d.0).sum();
    log(100 + n);
}
"#,
    ),
    both(
        "filter_fold",
        r#"fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } d.0 % 2 == 1 }).fold(0u32, |a, d| a + d.0);
    log(100 + n);
}
"#,
    ),
    alike(
        "filter_for_each",
        r#"fn main() {
    let _r = Rep;
    (1..6u32).map(|i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } d.0 % 2 == 1 }).for_each(|d| log(300 + d.0));
    log(100);
}
"#,
        low_match_high_unsupported(&[FOLD_NON_SCALAR_ACCUMULATOR]),
    ),
    alike(
        "filter_any",
        r#"fn main() {
    let _r = Rep;
    let hit = (1..6u32).map(|i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } d.0 % 2 == 1 }).any(|d| d.0 == 9);
    log(100 + hit as u32);
}
"#,
        low_match_high_unsupported(&[TRY_FOLD_BY_VALUE_CHECK]),
    ),
    // `filter` drops what it rejects; `find`'s predicate panics on an item
    // the filter kept.
    alike(
        "filter_then_find",
        r#"fn main() {
    let _r = Rep;
    let hit = (1..6u32).map(|i| D(i)).filter(|d| d.0 % 2 == 1).find(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
        low_match_high_unsupported(&[TRY_FOLD_BY_VALUE_CHECK]),
    ),
    both(
        "filter_from_cleanup_free_frame",
        r#"#[inline(never)]
fn odd(n: u32) -> usize {
    (1..n).map(|i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } d.0 % 2 == 1 }).count()
}
fn main() {
    let _r = Rep;
    let n = odd(std::hint::black_box(6));
    log(100 + n as u32);
}
"#,
    ),
    // `Vec::extend` drives its SECOND argument, and `ext`'s frame has no
    // cleanup and no other call that carries the chain: EH lowering must still
    // be on for the drive's pad. -O2/-O3 inline `extend` into
    // `Vec::spec_extend`, which this backend does not intercept.
    alike(
        "extend_from_cleanup_free_frame",
        r#"#[inline(never)]
fn ext<I: Iterator<Item = u32>>(v: &mut Vec<u32>, it: I) {
    v.extend(it);
}
fn main() {
    let _r = Rep;
    let mut v = Vec::new();
    ext(&mut v, (1..6u32).map(|i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } true }).map(|d| d.0));
    log(100 + v.len() as u32);
}
"#,
        low_match_high_unsupported(&[SPEC_EXTEND]),
    ),
    both(
        "filter_in_extern_c_frame",
        r#"struct Q(u32);
impl Drop for Q { fn drop(&mut self) { println!("drop {}", self.0); } }
extern "C" fn nounwind(n: u32) -> usize {
    (1..n).map(|i| Q(i)).filter(|d| { if d.0 == 3 { panic!("p"); } true }).count()
}
fn main() {
    println!("r {}", nounwind(std::hint::black_box(6)));
}
"#,
    ),
    both(
        "filter_slice_count",
        r#"fn main() {
    let _r = Rep;
    let v = [1u32, 2, 3, 4, 5];
    let n = v.iter().map(|&i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } d.0 % 2 == 1 }).count();
    log(100 + n as u32);
}
"#,
    ),
    both(
        "take_while_count",
        r#"fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| D(i)).take_while(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } true }).count();
    log(100 + n as u32);
}
"#,
    ),
    both(
        "skip_while_count",
        r#"fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| D(i)).skip_while(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } true }).count();
    log(100 + n as u32);
}
"#,
    ),
    both(
        "inspect_count",
        r#"fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| D(i)).inspect(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } }).count();
    log(100 + n as u32);
}
"#,
    ),
    // An interior-mutable held item (`C(Cell<u32>)`, `!Freeze`): the payload
    // writes it through its `&C` before it unwinds, so the item std drops is the
    // written one (`13`), not the image the drive stored before the call (`3`).
    // A drop of a rejected item drops the written one too (`11`, `12`).
    both(
        "cell_find_writes_then_unwinds",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let _r = Rep;
    let hit = (1..6u32).map(|i| C(Cell::new(i))).find(|c| { c.0.set(c.0.get() + 10); log(200 + c.0.get()); if c.0.get() == 13 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    both(
        "cell_filter_writes_then_unwinds",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| C(Cell::new(i))).filter(|c| { c.0.set(c.0.get() + 10); log(200 + c.0.get()); if c.0.get() == 13 { panic!("p"); } c.0.get() % 2 == 1 }).count();
    log(100 + n as u32);
}
"#,
    ),
    both(
        "cell_take_while_writes_then_unwinds",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| C(Cell::new(i))).take_while(|c| { c.0.set(c.0.get() + 10); log(200 + c.0.get()); if c.0.get() == 13 { panic!("p"); } true }).count();
    log(100 + n as u32);
}
"#,
    ),
    both(
        "cell_skip_while_writes_then_unwinds",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| C(Cell::new(i))).skip_while(|c| { c.0.set(c.0.get() + 10); log(200 + c.0.get()); if c.0.get() == 13 { panic!("p"); } true }).count();
    log(100 + n as u32);
}
"#,
    ),
    both(
        "cell_inspect_writes_then_unwinds",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let _r = Rep;
    let n = (1..6u32).map(|i| C(Cell::new(i))).inspect(|c| { c.0.set(c.0.get() + 10); log(200 + c.0.get()); if c.0.get() == 13 { panic!("p"); } }).count();
    log(100 + n as u32);
}
"#,
    ),
];

/// A by-reference payload that writes an interior-mutable item (`Cell<u32>`,
/// `!Freeze`) through its `&Item`, with no unwind: core moves on, keeps,
/// returns, compares or drops the item the payload left, so the drive reloads
/// the item from the slot it handed out. A tuple item with such a component
/// refuses, because its `&(A, B)` is a by-value copy the drive does not read
/// back.
const INTERIOR_MUT_CASES: &[Case] = &[
    both(
        "cell_filter_count",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let n = (1..6u32).map(|i| C(Cell::new(i))).filter(|c| { c.0.set(c.0.get() + 10); c.0.get() % 2 == 1 }).count();
    log(100 + n as u32);
    report();
}
"#,
    ),
    both(
        "cell_filter_sum",
        r#"use std::cell::Cell;
fn main() {
    let s: u32 = (1..6u32).map(|i| Cell::new(i)).filter(|c| { c.set(c.get() * 10); c.get() % 20 != 0 }).map(|c| c.get()).sum();
    log(1000 + s);
    report();
}
"#,
    ),
    both(
        "cell_find_returns_the_written_item",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let hit = (1..6u32).map(|i| C(Cell::new(i))).find(|c| { c.0.set(c.0.get() + 10); c.0.get() == 13 });
    log(500 + hit.as_ref().map_or(0, |c| c.0.get()));
    drop(hit);
    report();
}
"#,
    ),
    both(
        "cell_inspect_count",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let n = (1..6u32).map(|i| C(Cell::new(i))).inspect(|c| c.0.set(c.0.get() + 10)).count();
    log(100 + n as u32);
    report();
}
"#,
    ),
    // -O0/-O1: the `map(|c| c.0.get())` closure's own body borrows its
    // scalarized `Cell` argument for `Cell::get`, which the bridge refuses.
    alike(
        "cell_take_while_sum",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let s: u32 = (1..6u32).map(|i| C(Cell::new(i))).take_while(|c| { c.0.set(c.0.get() + 10); c.0.get() < 14 }).map(|c| c.0.get()).sum();
    log(1000 + s);
    report();
}
"#,
        LOW_SNAPSHOT_HIGH_MATCH,
    ),
    alike(
        "cell_skip_while_sum",
        r#"use std::cell::Cell;
struct C(Cell<u32>);
impl Drop for C { fn drop(&mut self) { log(self.0.get()); } }
fn main() {
    let s: u32 = (1..6u32).map(|i| C(Cell::new(i))).skip_while(|c| { c.0.set(c.0.get() + 10); c.0.get() < 13 }).map(|c| c.0.get()).sum();
    log(1000 + s);
    report();
}
"#,
        LOW_SNAPSHOT_HIGH_MATCH,
    ),
    both(
        "cell_min_by_keeps_what_the_comparator_wrote",
        r#"use std::cell::Cell;
fn main() {
    let best = (1..6u32).map(|i| Cell::new(i)).min_by(|a, b| { a.set(a.get() + 10); b.set(b.get() + 100); a.get().cmp(&b.get()) });
    log(500 + best.map_or(0, |c| c.get()));
    report();
}
"#,
    ),
    // -O2/-O3: `max_by_key`'s receiver is no longer a place the drive reads.
    alike(
        "cell_max_by_key_keeps_what_the_key_fn_wrote",
        r#"use std::cell::Cell;
fn main() {
    let best = (1..6u32).map(|i| Cell::new(i)).max_by_key(|c| { c.set(c.get() + 10); c.get() % 3 });
    log(500 + best.map_or(0, |c| c.get()));
    report();
}
"#,
        low_match_high_unsupported(&[MAX_BY_KEY_SELF_NOT_A_PLACE]),
    ),
    // -O2/-O3: the inlined drive's closure call has no place receiver.
    alike(
        "refuse_cell_tuple_filter",
        r#"use std::cell::Cell;
fn main() {
    let s: u32 = (1..6u32).map(|i| Cell::new(i)).enumerate().filter(|(k, c)| { c.set(c.get() * 10); *k != 1 }).map(|(k, c)| k as u32 + c.get()).sum();
    log(1000 + s);
    report();
}
"#,
        [
            Refuse("TCG-ITER-INTERIOR-MUT-ITEM", &[]),
            Refuse("TCG-ITER-INTERIOR-MUT-ITEM", &[]),
            unsupported(&[CLOSURE_RECEIVER_NOT_A_PLACE]),
            unsupported(&[CLOSURE_RECEIVER_NOT_A_PLACE]),
        ],
    ),
];

/// The same drives with nothing held across the payload that unwinds (a
/// by-value payload owns its item; a `map` closure that unwinds has produced
/// none yet; a scalar item needs no drop; `fold`'s own closure owns the
/// accumulator; `last` keeps a reference), with a rejected item's destructor
/// unwinding, and with no unwind at all: they matched before and must still.
const CONTROL_CASES: &[Case] = &[
    both(
        "ctl_find_and_filter_drives_without_unwind",
        r#"#[inline(never)]
fn found() -> u32 { (1..6u32).map(|i| D(i)).find(|d| { log(200 + d.0); d.0 == 3 }).map_or(0, |d| d.0) }
#[inline(never)]
fn counted() -> usize { (1..7u32).map(|i| D(i)).filter(|d| { log(200 + d.0); d.0 % 2 == 0 }).count() }
#[inline(never)]
fn summed() -> u32 { (1..7u32).map(|i| D(i)).filter(|d| d.0 % 3 != 0).map(|d| d.0).sum() }
#[inline(never)]
fn folded() -> u32 { [4u32, 5, 6].iter().map(|&i| D(i)).take_while(|d| d.0 < 6).fold(0, |a, d| a * 10 + d.0) }
#[inline(never)]
fn skipped() -> usize { (1..6u32).map(|i| D(i)).skip_while(|d| d.0 < 3).inspect(|d| log(300 + d.0)).count() }
fn main() {
    log(100 + found());
    log(100 + counted() as u32);
    log(100 + summed());
    log(100 + folded());
    log(100 + skipped() as u32);
    report();
}
"#,
    ),
    both(
        "ctl_scalar_item_find_unwinds",
        r#"fn main() {
    let _r = Rep;
    let hit = (1..6u32).find(|x| { log(200 + *x); if *x == 3 { panic!("p"); } false });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    both(
        "ctl_by_value_any_unwinds",
        r#"#[inline(never)]
fn any() -> bool { (1..6u32).map(|i| D(i)).any(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false }) }
fn main() {
    let _r = Rep;
    log(100 + any() as u32);
}
"#,
    ),
    both(
        "ctl_by_value_all_unwinds",
        r#"fn main() {
    let _r = Rep;
    let v = [1u32, 2, 3, 4];
    let all = v.iter().map(|&i| D(i)).all(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } true });
    log(100 + all as u32);
}
"#,
    ),
    both(
        "ctl_by_value_fold_unwinds",
        r#"fn main() {
    let _r = Rep;
    let s = (1..6u32).map(|i| D(i)).fold(0u32, |a, d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } a + d.0 });
    log(100 + s);
}
"#,
    ),
    alike(
        "ctl_by_value_position_unwinds",
        r#"#[inline(never)]
fn pos() -> Option<usize> { (1..6u32).map(|i| D(i)).position(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } false }) }
fn main() {
    let _r = Rep;
    log(100 + pos().is_some() as u32);
}
"#,
        low_match_high_unsupported(&[TRY_FOLD_BY_VALUE_CHECK]),
    ),
    both(
        "ctl_map_unwinds_before_find",
        r#"fn main() {
    let _r = Rep;
    let hit = (1..6u32).map(|i| { if i == 3 { panic!("p"); } D(i) }).find(|d| { log(200 + d.0); false });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    both(
        "ctl_find_reject_drop_unwinds",
        r#"struct P(u32);
impl Drop for P { fn drop(&mut self) { log(self.0); if self.0 == 2 { panic!("drop"); } } }
fn main() {
    let _r = Rep;
    let hit = (1..6u32).map(|i| P(i)).find(|d| { log(200 + d.0); d.0 == 4 });
    log(100 + hit.is_some() as u32);
}
"#,
    ),
    // A `fold` accumulator that needs drop, over a chain with no adapter
    // closure: only `fold`'s own closure runs, and it owns the accumulator
    // while it does. -O1: the `skip` receiver is no place the drive reads.
    alike(
        "ctl_droppable_fold_accumulator_without_adapter_closures",
        r#"fn main() {
    let _r = Rep;
    let a = (1..6u32).skip(1).fold(D(50), |a, i| { if i == 4 { panic!("p"); } D(a.0 + i) });
    log(100 + a.0);
}
"#,
        [Match, unsupported(&[SKIP_INNER_NOT_A_PLACE]), Match, Match],
    ),
    // `last` over a slice's `&D` items keeps a reference, which needs no drop.
    alike(
        "ctl_last_keeps_a_reference_item",
        r#"fn main() {
    let _r = Rep;
    let v = [D(1), D(2), D(3)];
    let a = v.iter().filter(|d| { log(200 + d.0); if d.0 == 3 { panic!("p"); } true }).last();
    log(100 + a.map_or(0, |d| d.0));
}
"#,
        low_match_high_unsupported(&[OPTION_OF_REFERENCE_ITEM]),
    ),
];

/// What the drive cannot drop when a payload unwinds fails closed under
/// `panic=unwind` instead of leaking: a held item whose destruction the drive
/// does not lower (a tuple item carrying one, `enumerate`; a struct whose drop
/// runs through a field), and a value needing drop that the terminal carries
/// across the adapter closures (`[TCG-ITER-UNWIND-CARRY]`: a `fold` / `reduce`
/// accumulator, the result `last` keeps). Under `panic=abort` the carrying
/// guests compile and match.
const REFUSAL_CASES: &[Case] = &[
    Case {
        name: "refuse_tuple_inspect",
        body: r#"fn main() {
    let _r = Rep;
    let s: u32 = (1..5u32).map(|i| D(i)).enumerate().inspect(|(k, d)| { log(200 + d.0); if *k == 2 { panic!("p"); } }).map(|(k, d)| k as u32 + d.0).sum();
    log(100 + s);
}
"#,
        abort: None,
        unwind: Some([
            Refuse("TCG-ITER-DISCARD-DROP", &[]),
            Refuse("TCG-ITER-DISCARD-DROP", &[]),
            unsupported(&[CLOSURE_RECEIVER_NOT_A_PLACE]),
            unsupported(&[CLOSURE_RECEIVER_NOT_A_PLACE]),
        ]),
    },
    Case {
        name: "refuse_nested_drop_inspect",
        body: r#"struct Outer(D);
fn main() {
    let _r = Rep;
    let s: u32 = (1..5u32).map(|i| Outer(D(i))).inspect(|o| { log(200 + o.0 .0); if o.0 .0 == 3 { panic!("p"); } }).map(|o| o.0 .0).sum();
    log(100 + s);
}
"#,
        abort: None,
        unwind: Some([
            Refuse("TCG-ITER-DISCARD-DROP", &[]),
            Refuse("TCG-ITER-DISCARD-DROP", &[]),
            unsupported(&[NESTED_FIELD_PLACE_PROJECTION]),
            unsupported(&[NESTED_FIELD_PLACE_PROJECTION]),
        ]),
    },
    // A value the terminal carries across the drive that needs drop: std's
    // frame drops it when an adapter closure unwinds (`... 3 53`: the item in
    // flight, then the accumulator), and the drive has no pad that does.
    Case {
        name: "refuse_fold_accumulator_filter_unwinds",
        body: r#"fn main() {
    let _r = Rep;
    let a = (1..6u32).map(|i| D(i)).filter(|d| { if d.0 == 3 { panic!("p"); } true }).fold(D(50), |a, d| D(a.0 + d.0));
    log(100 + a.0);
}
"#,
        abort: Some(MATCH4),
        unwind: Some(LOW_CARRY_HIGH_MATCH),
    },
    Case {
        name: "refuse_fold_accumulator_map_unwinds",
        body: r#"fn main() {
    let _r = Rep;
    let a = (1..6u32).map(|i| { if i == 3 { panic!("p"); } D(i) }).fold(D(50), |a, d| D(a.0 + d.0));
    log(100 + a.0);
}
"#,
        abort: Some(MATCH4),
        unwind: Some(LOW_CARRY_HIGH_MATCH),
    },
    // The same refusal withdraws a drive that never unwinds: its adapter
    // closures may.
    Case {
        name: "refuse_fold_accumulator_without_unwind",
        body: r#"fn main() {
    let a = (1..6u32).map(|i| D(i)).filter(|d| d.0 % 2 == 1).fold(D(50), |a, d| D(a.0 + d.0));
    log(100 + a.0);
    drop(a);
    report();
}
"#,
        abort: Some(MATCH4),
        unwind: Some(LOW_CARRY_HIGH_MATCH),
    },
    // An `extern "C"` frame: LLVM prints the accumulator's drop before the
    // abort.
    Case {
        name: "refuse_fold_accumulator_in_extern_c_frame",
        body: r#"struct Q(u32);
impl Drop for Q { fn drop(&mut self) { println!("drop {}", self.0); } }
extern "C" fn nounwind(n: u32) -> u32 {
    (1..n).map(|i| { if i == 3 { panic!("p"); } i }).fold(Q(50), |a, i| Q(a.0 + i)).0
}
fn main() {
    println!("r {}", nounwind(std::hint::black_box(6)));
}
"#,
        abort: Some(MATCH4),
        unwind: Some(LOW_CARRY_HIGH_MATCH),
    },
    // `reduce` folds over the rest of the chain with the first item as the
    // accumulator, a drive the bridge lowers at every level.
    Case {
        name: "refuse_reduce_accumulator_map_unwinds",
        body: r#"fn main() {
    let _r = Rep;
    let a = (1..6u32).map(|i| { if i == 3 { panic!("p"); } D(i) }).reduce(|a, d| D(a.0 + d.0));
    log(100 + a.is_some() as u32);
}
"#,
        abort: Some(MATCH4),
        unwind: Some([Refuse("TCG-ITER-UNWIND-CARRY", &[]); 4]),
    },
    // `last` keeps the latest item; -O2/-O3 inline it into a `fold` over an
    // `Option<D>` accumulator, which the bridge does not lower.
    Case {
        name: "refuse_last_result_filter_unwinds",
        body: r#"fn main() {
    let _r = Rep;
    let a = (1..6u32).map(|i| D(i)).filter(|d| { if d.0 == 3 { panic!("p"); } true }).last();
    log(100 + a.map_or(0, |d| d.0));
}
"#,
        abort: Some(low_match_high_unsupported(&[OPTION_OF_ITEM])),
        unwind: Some([
            Refuse("TCG-ITER-UNWIND-CARRY", &[]),
            Refuse("TCG-ITER-UNWIND-CARRY", &[]),
            unsupported(&[OPTION_OF_ITEM]),
            unsupported(&[OPTION_OF_ITEM]),
        ]),
    },
];

/// A `collect` into a `Vec` over a source that owns nothing (a `Range`, a
/// slice) whose payload unwinds: std's `from_iter` owns the `Vec` it builds
/// and frees it before the unwind leaves (`live=` counts the counting
/// allocator's live allocations, so a buffer left behind shows as one more).
/// A held item's pad drops the item first, then the collect frees the `Vec`.
/// Under `panic=abort` the same guests abort at the panic.
const COLLECT_CASES: &[Case] = &[
    // A trusted-length chain: `with_capacity` before the first pull.
    both(
        "collect_range_map_unwinds",
        r#"fn main() {
    let _r = Rep;
    let v: Vec<u32> = (1..9u32).map(|x| { log(x); if x == 6 { panic!("p"); } x * 2 }).collect();
    log(100 + v.len() as u32);
}
"#,
    ),
    both(
        "collect_slice_map_unwinds",
        r#"static SL: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
fn main() {
    let _r = Rep;
    let v: Vec<u64> = SL.iter().map(|x| { log(*x); if *x == 6 { panic!("p"); } *x as u64 }).collect();
    log(100 + v.len() as u32);
}
"#,
    ),
    // A chain whose length is not known: the buffer is allocated at the first
    // push and grows.
    both(
        "collect_range_filter_unwinds",
        r#"fn main() {
    let _r = Rep;
    let v: Vec<u32> = (1..9u32).filter(|x| { log(*x); if *x == 6 { panic!("p"); } *x % 2 == 1 }).collect();
    log(100 + v.len() as u32);
}
"#,
    ),
    both(
        "collect_filter_unwinds_before_the_first_push",
        r#"fn main() {
    let _r = Rep;
    let v: Vec<u32> = (1..9u32).filter(|x| { log(*x); if *x == 1 { panic!("p"); } true }).collect();
    log(100 + v.len() as u32);
}
"#,
    ),
    both(
        "collect_filter_unwinds_after_the_buffer_grew",
        r#"fn main() {
    let _r = Rep;
    let v: Vec<u64> = (1..200u64).filter(|x| { if *x == 150 { log(*x as u32); panic!("p"); } x % 3 != 0 }).collect();
    log(100 + v.len() as u32);
}
"#,
    ),
    // The collect's own unwind action is `Continue` and its frame has no
    // cleanup of its own: EH lowering must still be on for the collect's pad.
    both(
        "collect_from_cleanup_free_frame",
        r#"#[inline(never)]
fn build(n: u32) -> Vec<u32> {
    (1..n).map(|x| { log(x); if x == 6 { panic!("p"); } x * 2 }).collect()
}
fn main() {
    let _r = Rep;
    let v = build(std::hint::black_box(9));
    log(100 + v.len() as u32);
}
"#,
    ),
    // A held item and the collected `Vec`: the item is dropped first (`6`),
    // then the `Vec` is freed.
    both(
        "collect_held_item_filter_unwinds",
        r#"fn main() {
    let _r = Rep;
    let v: Vec<u32> = (1..9u32).map(|i| D(i)).filter(|d| { log(200 + d.0); if d.0 == 6 { panic!("p"); } d.0 % 2 == 1 }).map(|d| d.0).collect();
    log(100 + v.len() as u32);
}
"#,
    ),
    // A frame that cannot unwind: the held item is dropped while the `Vec`
    // still holds its buffer (`held=` counts the allocations made since the
    // drive began: the `Vec`'s, then the panic's), then the process aborts.
    both(
        "collect_held_item_in_extern_c_frame",
        r#"static BASE: AtomicIsize = AtomicIsize::new(0);
struct Q(u32);
impl Drop for Q { fn drop(&mut self) { println!("drop {} held={}", self.0, LIVE.load(Relaxed) - BASE.load(Relaxed)); } }
extern "C" fn nounwind(n: u32) -> usize {
    BASE.store(LIVE.load(Relaxed), Relaxed);
    (1..n).map(|i| Q(i)).filter(|q| { if q.0 == 3 { panic!("p"); } true }).map(|q| q.0).collect::<Vec<u32>>().len()
}
fn main() {
    println!("start");
    println!("r {}", nounwind(std::hint::black_box(6)));
}
"#,
    ),
    // The `Vec`s are dropped when `lens` returns: nothing is left live.
    both(
        "collect_without_unwind",
        r#"#[inline(never)]
fn lens() -> u32 {
    let v: Vec<u32> = (1..9u32).map(|x| x * 2).filter(|x| x % 3 != 0).collect();
    let w: Vec<u64> = [5u64, 6, 7].iter().map(|x| x + 1).collect();
    v.len() as u32 * 10 + w.len() as u32
}
fn main() {
    log(lens());
    report();
}
"#,
    ),
];

/// A library whose `collect` builds a `Vec` over a `Range`. Compiled with the
/// `disable-unwind` knob (no EH lowering), it must refuse
/// (`[TCG-COLLECT-UNWIND-RELEASE]`) rather than lose the `Vec`'s free on an
/// unwind; without the knob it compiles.
const NO_EH_COLLECT_LIBRARY: &str = r#"#[inline(never)]
pub fn build(n: u32) -> Vec<u32> { (1..n).map(|x| x * 2).collect() }
"#;

/// A library whose functions drive a chain with a droppable item past each
/// by-reference payload. Compiled with the `disable-unwind` knob (no EH
/// lowering), each drive that holds the item must refuse naming its site
/// (`[TCG-ITER-UNWIND-DROP]`); without the knob the library compiles.
const NO_EH_LIBRARY: &str = r#"pub struct D(pub u32);
impl Drop for D { fn drop(&mut self) { std::hint::black_box(self.0); } }
#[inline(never)]
pub fn by_filter(n: u32) -> usize { (1..n).map(|i| D(i)).filter(|d| d.0 % 2 == 1).count() }
#[inline(never)]
pub fn by_find(n: u32) -> bool { (1..n).map(|i| D(i)).find(|d| d.0 == 3).is_some() }
#[inline(never)]
pub fn by_inspect(n: u32) -> usize { (1..n).map(|i| D(i)).inspect(|d| { std::hint::black_box(d.0); }).count() }
#[inline(never)]
pub fn by_take_while(n: u32) -> usize { (1..n).map(|i| D(i)).take_while(|d| d.0 < 4).count() }
#[inline(never)]
pub fn by_skip_while(n: u32) -> usize { (1..n).map(|i| D(i)).skip_while(|d| d.0 < 4).count() }
"#;

/// The same drives over an item that needs no drop: without EH lowering they
/// refuse elsewhere (a std closure's cleanup edge), never naming
/// `[TCG-ITER-UNWIND-DROP]`.
const NO_EH_PLAIN_LIBRARY: &str = r#"#[inline(never)]
pub fn by_filter(n: u32) -> usize { (1..n).map(|i| i * 3).filter(|d| d % 2 == 1).count() }
#[inline(never)]
pub fn by_find(n: u32) -> bool { (1..n).map(|i| i * 3).find(|d| *d == 9).is_some() }
"#;

/// The sites each level's drives hold the item at: -O2/-O3 inline `find` and
/// `inspect` into std's own closures, whose cleanup edge refuses instead.
const NO_EH_SITES: [&[&str]; 4] = [
    &["filter", "find", "inspect", "skip_while", "take_while"],
    &["filter", "find", "inspect", "skip_while", "take_while"],
    &["filter", "skip_while", "take_while"],
    &["filter", "skip_while", "take_while"],
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

fn compile(
    dir: &Path,
    stem: &str,
    src: &Path,
    strategy: &str,
    opt: u32,
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
    .arg("-Coverflow-checks=off")
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

/// Compile `source` as an object-only library through the bridge with `knobs`,
/// under `-Cpanic=unwind` at `opt`: `Ok(())` when it compiles, else its stderr.
fn compile_library(
    dir: &Path,
    stem: &str,
    source: &str,
    opt: u32,
    knobs: &[&str],
    backend: &Path,
) -> Result<(), String> {
    let src = dir.join(format!("{stem}.rs"));
    std::fs::write(&src, source).expect("write the library");
    let mut cmd = toolchain_support::rustc_command_with_edition("2021");
    cmd.args([
        "--target",
        TARGET,
        "--crate-type",
        "lib",
        "--emit=obj",
        "-Ccodegen-units=1",
        "-Cpanic=unwind",
        "-Coverflow-checks=off",
    ])
    .arg(format!("--crate-name={stem}"))
    .arg(format!("-Copt-level={opt}"));
    let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
    arg.push(backend);
    cmd.arg(arg)
        .arg(toolchain_support::backend_knobs_arg(knobs));
    cmd.arg("-o").arg(dir.join(format!("{stem}.o"))).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Without EH lowering (`disable-unwind`) each drive in `NO_EH_LIBRARY` that
/// holds its item past a by-reference payload refuses, naming its site
/// (`NO_EH_SITES`); the same library compiles with EH lowering on, and the
/// drives over an item that needs no drop never name the code. Returns the
/// number of sites seen refusing, with the failures.
fn check_no_eh_refusals(backend: &Path) -> (usize, Vec<String>) {
    const CODE: &str = "TCG-ITER-UNWIND-DROP";
    let root = std::env::temp_dir().join(format!(
        "tcg_iter_chain_unwind_no_eh_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).expect("create the work directory");
    let mut sites = 0;
    let mut failures = Vec::new();
    for (level, expected) in NO_EH_SITES.iter().enumerate() {
        let opt = LEVELS[level];
        let no_eh: &[&str] = &["no-proof-certs", "disable-unwind"];
        match compile_library(
            &root,
            &format!("held_no_eh_{opt}"),
            NO_EH_LIBRARY,
            opt,
            no_eh,
            backend,
        ) {
            Ok(()) => failures.push(format!(
                "-O{opt}: the held-item library compiled without EH lowering"
            )),
            Err(stderr) => {
                if refusal_codes(&stderr).is_none() {
                    failures.push(format!(
                        "-O{opt}: the held-item library failed WITHOUT a named refusal:\n{stderr}"
                    ));
                }
                for site in *expected {
                    if stderr.contains(&format!("[{CODE}] `{site}` holds")) {
                        sites += 1;
                    } else {
                        failures.push(format!(
                            "-O{opt}: `{site}` did not refuse with [{CODE}] without EH lowering"
                        ));
                    }
                }
            }
        }
        if let Err(stderr) = compile_library(
            &root,
            &format!("held_eh_{opt}"),
            NO_EH_LIBRARY,
            opt,
            &["no-proof-certs"],
            backend,
        ) {
            failures.push(format!(
                "-O{opt}: the held-item library refused with EH lowering on: {:?}",
                refusal_codes(&stderr).unwrap_or_default()
            ));
        }
        if let Err(stderr) = compile_library(
            &root,
            &format!("plain_no_eh_{opt}"),
            NO_EH_PLAIN_LIBRARY,
            opt,
            no_eh,
            backend,
        ) {
            match refusal_codes(&stderr) {
                None => failures.push(format!(
                    "-O{opt}: the plain library failed WITHOUT a named refusal:\n{stderr}"
                )),
                Some(codes) if codes.iter().any(|c| c == CODE) => failures.push(format!(
                    "-O{opt}: the plain library, which holds no droppable item, named [{CODE}]"
                )),
                Some(_) => {}
            }
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    (sites, failures)
}

/// Without EH lowering (`disable-unwind`) `NO_EH_COLLECT_LIBRARY`'s collect
/// refuses with `[TCG-COLLECT-UNWIND-RELEASE]` at every level, and the same
/// library compiles with EH lowering on. Returns the number of levels seen
/// refusing, with the failures.
fn check_no_eh_collect_refusals(backend: &Path) -> (usize, Vec<String>) {
    const CODE: &str = "TCG-COLLECT-UNWIND-RELEASE";
    let root = std::env::temp_dir().join(format!(
        "tcg_iter_chain_unwind_no_eh_collect_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).expect("create the work directory");
    let mut levels = 0;
    let mut failures = Vec::new();
    for opt in LEVELS {
        match compile_library(
            &root,
            &format!("collect_no_eh_{opt}"),
            NO_EH_COLLECT_LIBRARY,
            opt,
            &["no-proof-certs", "disable-unwind"],
            backend,
        ) {
            Ok(()) => failures.push(format!(
                "-O{opt}: the collect library compiled without EH lowering"
            )),
            Err(stderr) => match refusal_codes(&stderr) {
                Some(codes) if codes.iter().any(|c| c == CODE) => levels += 1,
                Some(codes) => failures.push(format!(
                    "-O{opt}: the collect library refused with {codes:?}, not [{CODE}]"
                )),
                None => failures.push(format!(
                    "-O{opt}: the collect library failed WITHOUT a named refusal:\n{stderr}"
                )),
            },
        }
        if let Err(stderr) = compile_library(
            &root,
            &format!("collect_eh_{opt}"),
            NO_EH_COLLECT_LIBRARY,
            opt,
            &["no-proof-certs"],
            backend,
        ) {
            failures.push(format!(
                "-O{opt}: the collect library refused with EH lowering on: {:?}",
                refusal_codes(&stderr).unwrap_or_default()
            ));
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    (levels, failures)
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
    let backend = backend_artifact_support::current_test_backend();
    let root = std::env::temp_dir().join(format!(
        "tcg_iter_chain_unwind_{group}_{}",
        std::process::id()
    ));
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
                    let verdict = judge(&root, cell, &backend);
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
fn judge(root: &Path, cell: &Cell<'_>, backend: &Path) -> Result<Option<()>, String> {
    let opt = LEVELS[cell.level];
    let label = format!("{} -Cpanic={} -O{opt}", cell.case.name, cell.strategy);
    let dir = root.join(format!("{}_{}_{opt}", cell.case.name, cell.strategy));
    std::fs::create_dir_all(&dir).expect("create the cell directory");
    let src = dir.join("guest.rs");
    std::fs::write(&src, format!("{PRELUDE}{}", cell.case.body)).expect("write the guest");
    let oracle = compile(&dir, "llvm", &src, cell.strategy, opt, None)
        .map(|bin| run(&bin))
        .unwrap_or_else(|stderr| panic!("{label}: the LLVM oracle failed to compile:\n{stderr}"));
    let bridge = match compile(&dir, "bridge", &src, cell.strategy, opt, Some(backend)) {
        Ok(bin) => Built::Ran(run(&bin)),
        Err(stderr) => Built::Refused(stderr),
    };
    match (cell.want, bridge) {
        (Match, Built::Ran(ending)) if ending == oracle => Ok(Some(())),
        (Match, Built::Ran(ending)) => Err(format!(
            "{label}: compiled and DIVERGES — LLVM {oracle:?}, trust-cg {ending:?}"
        )),
        (Match, Built::Refused(stderr)) => Err(format!(
            "{label}: refused a cell that must compile and match: {:?}",
            refusal_codes(&stderr).unwrap_or_default()
        )),
        (Refuse(code, reasons), Built::Refused(stderr)) => match refusal_codes(&stderr) {
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
        (Refuse(code, _), Built::Ran(ending)) => Err(format!(
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
fn by_reference_payloads_drop_the_item_they_hold_when_they_unwind_aarch64() {
    darwin_native::require("iter_chain_unwind_item_differential_aarch64", &[]);
    let tally = run_cells("held", HELD_CASES);
    require_clean("held", &tally);
    eprintln!(
        "ITER_CHAIN_UNWIND_HELD cases={} cells={} matched={} refused={} opts=0,1,2,3 \
         strategies=abort,unwind",
        HELD_CASES.len(),
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
fn drives_holding_nothing_across_an_unwind_still_match_aarch64() {
    darwin_native::require("iter_chain_unwind_item_differential_aarch64", &[]);
    let tally = run_cells("controls", CONTROL_CASES);
    require_clean("controls", &tally);
    eprintln!(
        "ITER_CHAIN_UNWIND_CONTROLS cases={} cells={} matched={} refused={} opts=0,1,2,3 \
         strategies=abort,unwind",
        CONTROL_CASES.len(),
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
fn by_reference_payloads_keep_the_item_they_write_aarch64() {
    darwin_native::require("iter_chain_unwind_item_differential_aarch64", &[]);
    let tally = run_cells("interior_mut", INTERIOR_MUT_CASES);
    require_clean("interior_mut", &tally);
    eprintln!(
        "ITER_CHAIN_INTERIOR_MUT_ITEMS cases={} cells={} matched={} refused={} opts=0,1,2,3 \
         strategies=abort,unwind",
        INTERIOR_MUT_CASES.len(),
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
fn collect_frees_the_vec_it_builds_when_a_payload_unwinds_aarch64() {
    darwin_native::require("iter_chain_unwind_item_differential_aarch64", &[]);
    let mut tally = run_cells("collect", COLLECT_CASES);
    let backend = backend_artifact_support::current_test_backend();
    let (levels, no_eh_failures) = check_no_eh_collect_refusals(&backend);
    tally.failures.extend(no_eh_failures);
    require_clean("collect", &tally);
    eprintln!(
        "ITER_CHAIN_UNWIND_COLLECT cases={} cells={} matched={} refused={} no_eh_levels={levels} \
         opts=0,1,2,3 strategies=abort,unwind",
        COLLECT_CASES.len(),
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
fn held_items_the_drive_cannot_drop_refuse_by_name_aarch64() {
    darwin_native::require("iter_chain_unwind_item_differential_aarch64", &[]);
    let mut tally = run_cells("refusals", REFUSAL_CASES);
    let backend = backend_artifact_support::current_test_backend();
    let (sites, no_eh_failures) = check_no_eh_refusals(&backend);
    tally.failures.extend(no_eh_failures);
    require_clean("refusals", &tally);
    eprintln!(
        "ITER_CHAIN_UNWIND_REFUSALS cases={} cells={} matched={} refused={} no_eh_sites={sites} \
         opts=0,1,2,3 strategies=abort,unwind",
        REFUSAL_CASES.len(),
        tally.cells,
        tally.matched,
        tally.refused
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}
