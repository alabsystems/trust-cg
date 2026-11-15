#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: an intercepted iterator terminal owns the closure (and the
// iterator) it takes by value, and must drop it exactly once, after the drive.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD. The bridge replaces `Iterator::for_each(self, f)` and the
// `fold`-family consumers with a synthesized loop over its own model of the
// iterator. The real callee owns `self` and `f`: it drops them when it returns,
// and in its cleanup when a call inside it unwinds. The caller's MIR has moved
// them and drops nothing. A loop that emits no drop glue loses every destructor
// a `move` closure (or a closure inside a `map`/`filter`/... adapter) owns: a
// guard never runs, a `RefMut` keeps its `RefCell` borrowed, an `Rc` count stays
// high. `std` reaches it on its own: `Vec::extend_trusted` passes `for_each` a
// closure owning a `SetLenOnDrop`, whose destructor is the only write of the
// vector's length, so `let v: Vec<&T> = slice.iter().collect()` came back
// empty. Measured on f349c8652 (proofs-off lane, LLVM caller, bridge library):
// every `for_each(move ..)` / `fold(move ..)` row and every `Vec<&u64>` /
// `VecDeque<&u64>` collect or extend row below printed a wrong value at -O0
// and -O3, with no refusal.
//
// THE GATE, per row. Each row is ONE library function `k` compiled by LLVM (the
// oracle) and by the bridge at the row's optimization levels and panic
// strategy; the caller is always compiled by LLVM. `k` builds a guard `d` whose
// destructor appends `tag * 10 + calls % 10` to a caller-owned log, so the log
// records how many times the guard was dropped and how many closure calls had
// run when it was: a drop that is lost, doubled, or early changes the output.
// The caller runs `k` over inputs of 0, 1, 3 and 5 elements; a `panic=unwind`
// row's caller catches a panic from `k` and still prints the log.
//   * `Expect::Match`: the bridge must compile the library and the program must
//     print exactly what the oracle prints and exit with its code.
//   * `Expect::MatchOrRefusal`: the same, OR the bridge refuses with the named
//     `[code]` and a root line that names `root` and carries `root_line`.
//   * Anything else fails: a different stdout or exit code (the miscompile), a
//     run past `RUN_TIMEOUT`, a signal, an ICE, or any other refusal.
// The oracle is asserted first on every row, so a row cannot pass vacuously.
//
// A closure the drive owns is dropped through rustc's own `drop_glue` over the
// closure's frame slot (`owned_closure_drop_plan`); an owned iterator whose drop
// glue would run a destructor the drive skips (a closure or other value with a
// destructor inside an adapter), or an owned payload of any other terminal with
// one, is refused with `[TCG-INTERCEPT-OWNED-DROP]`. The owning sources the chain
// models over a drop-free element (`array::IntoIter`, `vec::IntoIter`) are not
// refused for their own drop (`unaccounted_owned_drop`), so the drive still owes
// their `move` closure its drop. The `panic=unwind` rows pin the cleanup edge:
// a panicking closure call drops the owned closure before the caller's own
// cleanup runs.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin nothing.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const OWNED_DROP: &str = "TCG-INTERCEPT-OWNED-DROP";
const MIR_UNSUPPORTED: &str = "TCG-MIR-UNSUPPORTED";
const IR_LOWER: &str = "TCG-IR-LOWER";
const RUN_TIMEOUT: Duration = Duration::from_secs(30);
/// The input lengths the caller runs `k` over (a prefix of `[10, 20, 30, 40, 50]`).
const LENGTHS: &str = "[0usize, 1, 3, 5]";
const LENGTH_COUNT: usize = 4;
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

/// The v0-mangled tail of the kernel `klib::k`, as a refused root is listed.
const KERNEL_ROOT: &str = "4klib1k ";

/// The library prelude every row shares: the guard `D` whose destructor logs
/// `tag * 10 + calls % 10`, and whose `t` counts closure calls.
const PRELUDE: &str = "#![allow(unused)]\n\
use std::cell::{Cell, RefCell};\n\
use std::collections::VecDeque;\n\
use std::rc::Rc;\n\
pub struct D<'a> { pub log: &'a Cell<u64>, pub calls: &'a Cell<u64>, pub tag: u64 }\n\
impl Drop for D<'_> {\n\
    fn drop(&mut self) { self.log.set(self.log.get() * 100 + self.tag * 10 + self.calls.get() % 10); }\n\
}\n\
impl D<'_> { pub fn t(&self) -> u64 { self.calls.set(self.calls.get() + 1); self.tag } }\n";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Panic {
    Abort,
    Unwind,
}

impl Panic {
    fn flag(self) -> &'static str {
        match self {
            Panic::Abort => "-Cpanic=abort",
            Panic::Unwind => "-Cpanic=unwind",
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// Compiles, and the program's stdout and exit code equal LLVM's.
    Match,
    /// `Match`, or a `[code]` refusal whose root line names `root` and carries
    /// `root_line`.
    MatchOrRefusal {
        code: &'static str,
        root: &'static str,
        root_line: &'static str,
    },
}

use Expect::Match as M;

/// `Match`, or `[TCG-INTERCEPT-OWNED-DROP]` refusing the kernel `k`.
const OWNED: Expect = Expect::MatchOrRefusal {
    code: OWNED_DROP,
    root: KERNEL_ROOT,
    root_line: "[TCG-INTERCEPT-OWNED-DROP]",
};

/// `Match`, or `[TCG-MIR-UNSUPPORTED]` refusing the kernel `k` for `reason`.
const fn unsupported(reason: &'static str) -> Expect {
    Expect::MatchOrRefusal {
        code: MIR_UNSUPPORTED,
        root: KERNEL_ROOT,
        root_line: reason,
    }
}

/// At -O2/-O3 `for_each` over an adapter chain inlines to `fold((), ..)`, whose
/// unit accumulator the fold consumer does not model.
const UNIT_FOLD: Expect = unsupported("iterator fold over a non-scalar accumulator");

/// A closure owning a `Box` whose payload needs drop: its drop glue body, which
/// the bridge compiles, refuses the recursive `Box` drop.
const BOX_GLUE: Expect = Expect::MatchOrRefusal {
    code: MIR_UNSUPPORTED,
    root: "3ptr9drop_glue",
    root_line: "whose payload needs drop (recursive drop glue not lowered)",
};

/// `Rc::clone` at -O0/-O1 reaches `RcInnerPtr::strong_ref`, whose object the
/// backend refuses to emit.
const RC_STRONG_REF: Expect = Expect::MatchOrRefusal {
    code: IR_LOWER,
    root: "10strong_ref",
    root_line: "[TCG-IR-LOWER]",
};

/// At -O2/-O3 `Vec::extend` of a `Map` reaches `Vec::extend_trusted`, which the
/// Vec interception does not model.
const EXTEND_TRUSTED: Expect =
    unsupported("Vec::<u64>::extend_trusted is not an intercepted Vec method");

/// At -O2/-O3 a terminal over `vec::IntoIter` receives the iterator rustc's
/// inlined `into_iter` built in registers, which the chain drive does not read.
const SELF_NOT_MEMORY: Expect = unsupported("self argument is not memory-backed");

struct Row {
    name: &'static str,
    panic: Panic,
    /// The body of `k`, after `let acc = Cell::new(0u64); let s = &acc; let d =
    /// D { log, calls, tag: 7 };`. Its value is `k`'s `u64` result.
    body: &'static str,
    /// Per optimization level, `OPT_LEVELS` order.
    expect: [Expect; 4],
}

const fn row(name: &'static str, panic: Panic, body: &'static str, expect: [Expect; 4]) -> Row {
    Row {
        name,
        panic,
        body,
        expect,
    }
}

use Panic::{Abort, Unwind};

fn rows() -> Vec<Row> {
    vec![
        // `for_each` owns a `move` closure: dropped once, after the last call.
        row(
            "for_each_move_slice",
            Abort,
            "a.iter().for_each(move |&x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, M, M],
        ),
        row(
            "for_each_borrowing_control",
            Abort,
            "a.iter().for_each(|&x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, M, M],
        ),
        row(
            "for_each_move_range",
            Abort,
            "(0..a.len()).for_each(move |i| s.set(s.get() * 3 + a[i] + d.t())); acc.get()",
            [M, M, UNIT_FOLD, UNIT_FOLD],
        ),
        row(
            "for_each_move_copied",
            Abort,
            "a.iter().copied().for_each(move |x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, UNIT_FOLD, UNIT_FOLD],
        ),
        row(
            "for_each_move_enumerate",
            Abort,
            "a.iter().enumerate().for_each(move |(i, &x)| s.set(s.get() * 3 + x + i as u64 + d.t())); acc.get()",
            [M, M, UNIT_FOLD, UNIT_FOLD],
        ),
        row(
            "for_each_move_rev",
            Abort,
            "a.iter().rev().for_each(move |&x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, M, M],
        ),
        row(
            "for_each_move_take",
            Abort,
            "a.iter().take(2).for_each(move |&x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, M, M],
        ),
        row(
            "for_each_move_after_map",
            Abort,
            "a.iter().map(|&x| x * 2).for_each(move |x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, UNIT_FOLD, UNIT_FOLD],
        ),
        row(
            "for_each_move_after_filter",
            Abort,
            "a.iter().filter(|&&x| x != 20).for_each(move |&x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, UNIT_FOLD, UNIT_FOLD],
        ),
        // Two owned guards: dropped in capture order, each once.
        row(
            "for_each_move_two_guards",
            Abort,
            "let d2 = D { log, calls, tag: 8 }; \
             a.iter().for_each(move |&x| s.set(s.get() * 3 + x + d.t() + d2.t())); acc.get()",
            [M, M, M, M],
        ),
        row(
            "for_each_move_boxed_guard",
            Abort,
            "let bx = Box::new(d); a.iter().for_each(move |&x| s.set(s.get() * 3 + x + bx.t())); acc.get()",
            [BOX_GLUE, BOX_GLUE, BOX_GLUE, BOX_GLUE],
        ),
        // A `RefMut` moved into the closure must release the borrow.
        row(
            "for_each_move_refmut",
            Abort,
            "let cell = RefCell::new(0u64); \
             { let mut m = cell.borrow_mut(); a.iter().for_each(move |&x| *m = *m * 3 + x + d.t()); } \
             let r = match cell.try_borrow() { Ok(v) => *v, Err(_) => u64::MAX }; r",
            [M, M, M, M],
        ),
        // An `Rc` clone moved into the closure must give its count back.
        row(
            "for_each_move_rc",
            Abort,
            "let r = Rc::new(5u64); \
             { let r2 = r.clone(); a.iter().for_each(move |&x| s.set(s.get() * 3 + x + *r2 + d.t())); } \
             Rc::strong_count(&r) as u64 * 1_000_000 + acc.get()",
            [RC_STRONG_REF, RC_STRONG_REF, M, M],
        ),
        // `fold` owns its closure the same way.
        row(
            "fold_move_slice",
            Abort,
            "a.iter().fold(1u64, move |t, &x| t * 3 + x + d.t())",
            [M, M, M, M],
        ),
        row(
            "fold_move_range",
            Abort,
            "(0..a.len()).fold(1u64, move |t, i| t * 3 + a[i] + d.t())",
            [M, M, M, M],
        ),
        row(
            "fold_move_copied",
            Abort,
            "a.iter().copied().fold(1u64, move |t, x| t * 3 + x + d.t())",
            [M, M, M, M],
        ),
        row(
            "fold_move_rev",
            Abort,
            "a.iter().rev().fold(1u64, move |t, &x| t * 3 + x + d.t())",
            [M, M, M, M],
        ),
        row(
            "fold_borrowing_control",
            Abort,
            "a.iter().fold(1u64, |t, &x| t * 3 + x + d.t())",
            [M, M, M, M],
        ),
        // The closure owns a guard with mixed-width fields and mutates it on every
        // call: the glue must destroy the environment the calls updated, read at
        // rustc's layout of the closure's (reordered) upvars, in capture order.
        row(
            "for_each_move_mutated_mixed_guard",
            Abort,
            "struct M<'a> { b: u8, log: &'a Cell<u64>, h: u16, n: u64, w: u32 } \
             impl Drop for M<'_> { fn drop(&mut self) { self.log.set(self.log.get() * 1000 \
             + (self.n * 7 + self.b as u64 * 3 + self.h as u64 + self.w as u64 * 11) % 1000) } } \
             impl M<'_> { fn bump(&mut self, x: u64) { self.n += x; self.b = self.b.wrapping_add(1); \
             self.h ^= x as u16; self.w += 1; } } \
             let mut m = M { b: 1, log, h: 2, n: 0, w: 5 }; \
             a.iter().for_each(move |&x| { m.bump(x); s.set(s.get() * 3 + x + d.t()) }); acc.get()",
            [M, M, M, M],
        ),
        row(
            "fold_move_mutated_mixed_guard",
            Abort,
            "struct M<'a> { b: u8, log: &'a Cell<u64>, h: u16, n: u64, w: u32 } \
             impl Drop for M<'_> { fn drop(&mut self) { self.log.set(self.log.get() * 1000 \
             + (self.n * 7 + self.b as u64 * 3 + self.h as u64 + self.w as u64 * 11) % 1000) } } \
             impl M<'_> { fn bump(&mut self, x: u64) { self.n += x; self.b = self.b.wrapping_add(1); \
             self.h ^= x as u16; self.w += 1; } } \
             let mut m = M { b: 1, log, h: 2, n: 0, w: 5 }; \
             a.iter().fold(1u64, move |t, &x| { m.bump(x); t * 3 + x + d.t() })",
            [M, M, M, M],
        ),
        // A `move` closure inside an adapter is owned by the iterator `self`. At
        // -O2/-O3 a reduction inlines to `fold(.., map_fold(f, ..))`, whose glue
        // closure owns `f` and is dropped like any fold closure.
        row(
            "map_move_sum",
            Abort,
            "a.iter().map(move |&x| x + d.t()).sum::<u64>()",
            [OWNED, OWNED, M, M],
        ),
        row(
            "map_move_fold",
            Abort,
            "a.iter().map(move |&x| x + d.t()).fold(1u64, |t, x| t * 3 + x)",
            [OWNED, OWNED, M, M],
        ),
        row(
            "map_move_for_each",
            Abort,
            "a.iter().map(move |&x| x + d.t()).for_each(|x| s.set(s.get() * 3 + x)); acc.get()",
            [OWNED, OWNED, UNIT_FOLD, UNIT_FOLD],
        ),
        row(
            "map_move_collect",
            Abort,
            "let v: Vec<u64> = a.iter().map(move |&x| x + d.t()).collect(); \
             v.len() as u64 * 1000 + v.iter().sum::<u64>()",
            [OWNED, OWNED, OWNED, OWNED],
        ),
        row(
            "map_move_extend",
            Abort,
            "let mut v: Vec<u64> = Vec::new(); v.extend(a.iter().map(move |&x| x + d.t())); \
             v.len() as u64 * 1000 + v.iter().sum::<u64>()",
            [OWNED, OWNED, EXTEND_TRUSTED, EXTEND_TRUSTED],
        ),
        row(
            "map_move_max",
            Abort,
            "a.iter().map(move |&x| x + d.t()).max().unwrap_or(0)",
            [OWNED, OWNED, OWNED, OWNED],
        ),
        row(
            "filter_move_count",
            Abort,
            "a.iter().filter(move |&&x| { d.t(); x != 20 }).count() as u64",
            [OWNED, OWNED, OWNED, OWNED],
        ),
        row(
            "inspect_move_count",
            Abort,
            "a.iter().inspect(move |_| { d.t(); }).count() as u64",
            [OWNED, OWNED, M, M],
        ),
        row(
            "take_while_move_count",
            Abort,
            "a.iter().take_while(move |&&x| { d.t(); x < 35 }).count() as u64",
            [OWNED, OWNED, OWNED, OWNED],
        ),
        row(
            "filter_map_move_sum",
            Abort,
            "a.iter().filter_map(move |&x| { d.t(); Some(x) }).sum::<u64>()",
            [OWNED, OWNED, M, M],
        ),
        row(
            "any_move",
            Abort,
            "a.iter().any(move |&x| { d.t(); x == 20 }) as u64",
            [OWNED, OWNED, OWNED, OWNED],
        ),
        // An owning source the chain models over a drop-free element owes no
        // destructor of its own, so it is not refused; a `move` closure the
        // terminal takes is still dropped once, and a `move` closure inside an
        // adapter over it is still refused. Measured on origin/main 6a57e8ab9
        // without this fix: every `*_move` row here that compiles logged no drop
        // at -O0/-O1. With the blanket `self` refusal this fix first carried
        // (f349c8652), every row here was refused at -O0.
        row(
            "array_into_iter_for_each_move",
            Abort,
            "let arr = [1u64, 2, 3]; \
             arr.into_iter().for_each(move |x| s.set(s.get() * 3 + x + a.len() as u64 + d.t())); acc.get()",
            [M, M, UNIT_FOLD, UNIT_FOLD],
        ),
        row(
            "array_into_iter_fold_move",
            Abort,
            "let arr = [1u64, 2, 3]; arr.into_iter().fold(a.len() as u64, move |t, x| t * 3 + x + d.t())",
            [M, M, M, M],
        ),
        row(
            "array_into_iter_map_sum_control",
            Abort,
            "let arr = [1u64, 2, 3]; arr.into_iter().map(|x| x * 2 + a.len() as u64).sum::<u64>() + d.t()",
            [M, M, M, M],
        ),
        row(
            "vec_into_iter_for_each_move",
            Abort,
            "let v: Vec<u64> = a.to_vec(); v.into_iter().for_each(move |x| s.set(s.get() * 3 + x + d.t())); \
             acc.get()",
            [M, M, SELF_NOT_MEMORY, SELF_NOT_MEMORY],
        ),
        row(
            "vec_into_iter_fold_move",
            Abort,
            "let v: Vec<u64> = a.to_vec(); v.into_iter().fold(1u64, move |t, x| t * 3 + x + d.t())",
            [M, M, SELF_NOT_MEMORY, SELF_NOT_MEMORY],
        ),
        row(
            "vec_into_iter_map_sum_control",
            Abort,
            "let v: Vec<u64> = a.to_vec(); v.into_iter().map(|x| x * 2).sum::<u64>() + d.t()",
            [M, M, SELF_NOT_MEMORY, SELF_NOT_MEMORY],
        ),
        row(
            "vec_into_iter_filter_count_control",
            Abort,
            "let v: Vec<u64> = a.to_vec(); v.into_iter().filter(|&x| x != 20).count() as u64 + d.t()",
            [M, M, M, M],
        ),
        row(
            "vec_into_iter_map_move_sum",
            Abort,
            "let v: Vec<u64> = a.to_vec(); v.into_iter().map(move |x| x + d.t()).sum::<u64>()",
            [OWNED, OWNED, SELF_NOT_MEMORY, SELF_NOT_MEMORY],
        ),
        // The caller owns a `for` loop's iterator and drops it itself.
        row(
            "for_loop_over_map_move_control",
            Abort,
            "let mut t = 0u64; for x in a.iter().map(move |&x| x + d.t()) { t = t * 3 + x; } t",
            [M, M, M, M],
        ),
        // `std`'s collect path: `SetLenOnDrop` commits the length when the
        // `extend_trusted` closure is dropped.
        row(
            "collect_refs",
            Abort,
            "let v: Vec<&u64> = a.iter().collect(); \
             let mut t = 0u64; for &&x in &v { t = t * 3 + x; } v.len() as u64 * 100000 + t",
            [M, M, M, M],
        ),
        row(
            "collect_refs_rev",
            Abort,
            "let v: Vec<&u64> = a.iter().rev().collect(); \
             let mut t = 0u64; for &&x in &v { t = t * 3 + x; } v.len() as u64 * 100000 + t",
            [M, M, M, M],
        ),
        row(
            "collect_refs_take",
            Abort,
            "let v: Vec<&u64> = a.iter().take(2).collect(); \
             let mut t = 0u64; for &&x in &v { t = t * 3 + x; } v.len() as u64 * 100000 + t",
            [M, M, M, M],
        ),
        row(
            "collect_enumerated_refs",
            Abort,
            "let v: Vec<(usize, &u64)> = a.iter().enumerate().collect(); \
             let mut t = 0u64; for &(i, &x) in &v { t = t * 3 + x + i as u64; } v.len() as u64 * 100000 + t",
            [M, M, M, M],
        ),
        row(
            "from_iter_refs",
            Abort,
            "let v = Vec::<&u64>::from_iter(a.iter()); v.len() as u64",
            [M, M, M, M],
        ),
        row(
            "vecdeque_collect_refs",
            Abort,
            "let v: VecDeque<&u64> = a.iter().collect(); v.len() as u64",
            [M, M, M, M],
        ),
        row(
            "extend_refs_onto_nonempty",
            Abort,
            "let first = 99u64; let mut v: Vec<&u64> = Vec::new(); v.push(&first); v.extend(a.iter()); \
             let mut t = 0u64; for &&x in &v { t = t * 3 + x; } v.len() as u64 * 100000 + t",
            [M, M, M, M],
        ),
        row(
            "collect_refs_then_push",
            Abort,
            "let first = 99u64; let mut v: Vec<&u64> = a.iter().collect(); v.push(&first); \
             let mut t = 0u64; for &&x in &v { t = t * 3 + x; } v.len() as u64 * 100000 + t",
            [M, M, M, M],
        ),
        row(
            "push_loop_refs_control",
            Abort,
            "let mut v: Vec<&u64> = Vec::new(); for x in a { v.push(x); } v.len() as u64",
            [M, M, M, M],
        ),
        // panic=unwind: the drive's own calls get a cleanup that drops the owned
        // closure, then continues at the call's own unwind action.
        row(
            "unwind_for_each_move",
            Unwind,
            "a.iter().for_each(move |&x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, M, M],
        ),
        row(
            "unwind_for_each_move_panics",
            Unwind,
            "a.iter().for_each(move |&x| { if x == 30 { panic!(\"boom\") } s.set(s.get() * 3 + x + d.t()) }); \
             acc.get()",
            [M, M, M, M],
        ),
        row(
            "unwind_fold_move",
            Unwind,
            "a.iter().fold(1u64, move |t, &x| t * 3 + x + d.t())",
            [M, M, M, M],
        ),
        row(
            "unwind_fold_move_panics",
            Unwind,
            "a.iter().fold(1u64, move |t, &x| { if x == 30 { panic!(\"boom\") } t * 3 + x + d.t() })",
            [M, M, M, M],
        ),
        // An owning `vec::IntoIter` source: while the drive runs, its payload
        // edges unwind into the owned-closure cleanup
        // (`begin_owned_closure_drive`), which drops the closure and then enters
        // the consumed-owner pad that releases the source
        // (`begin_consumed_owner_drive`), as the callee drops `f` before `self`.
        row(
            "unwind_vec_into_iter_for_each_move_panics",
            Unwind,
            "let v: Vec<u64> = a.to_vec(); \
             v.into_iter().for_each(move |x| { if x == 30 { panic!(\"boom\") } s.set(s.get() * 3 + x + d.t()) }); \
             acc.get()",
            [M, M, SELF_NOT_MEMORY, SELF_NOT_MEMORY],
        ),
        row(
            "unwind_vec_into_iter_fold_move_panics",
            Unwind,
            "let v: Vec<u64> = a.to_vec(); \
             v.into_iter().fold(1u64, move |t, x| { if x == 30 { panic!(\"boom\") } t * 3 + x + d.t() })",
            [M, M, SELF_NOT_MEMORY, SELF_NOT_MEMORY],
        ),
        // A live caller guard: the owned closure is dropped before the caller's
        // cleanup drops `g`.
        row(
            "unwind_for_each_move_panics_under_caller_guard",
            Unwind,
            "let g = D { log, calls, tag: 5 }; \
             a.iter().for_each(move |&x| { if x == 30 { panic!(\"boom\") } s.set(s.get() * 3 + x + d.t()) }); \
             drop(g); acc.get()",
            [M, M, M, M],
        ),
        // A panic in an adapter closure inside the drive takes the same cleanup.
        row(
            "unwind_for_each_move_adapter_panics",
            Unwind,
            "a.iter().map(|&x| if x == 30 { panic!(\"boom\") } else { x * 2 }) \
             .for_each(move |x| s.set(s.get() * 3 + x + d.t())); acc.get()",
            [M, M, UNIT_FOLD, UNIT_FOLD],
        ),
        // A destructor's store before its normal-exit panic remains visible
        // when the caller's cleanup runs, at every optimization level.
        row(
            "unwind_for_each_move_drop_panics",
            Unwind,
            "struct P<'a>(&'a Cell<u64>); \
             impl Drop for P<'_> { fn drop(&mut self) { self.0.set(self.0.get() * 100 + 99); panic!(\"drop\") } } \
             let p = P(log); let g = D { log, calls, tag: 5 }; \
             a.iter().for_each(move |&x| { let _ = &p; s.set(s.get() * 3 + x + d.t()) }); \
             drop(g); acc.get()",
            [M, M, M, M],
        ),
        row(
            "unwind_map_move_sum_panics",
            Unwind,
            "a.iter().map(move |&x| { if x == 30 { panic!(\"boom\") } x + d.t() }).sum::<u64>()",
            [OWNED, OWNED, M, M],
        ),
        // No guard is live across these calls (`d` is dropped first), so their
        // own cleanup edges are trivial.
        row(
            "unwind_collect_refs",
            Unwind,
            "drop(d); let v: Vec<&u64> = a.iter().collect(); let n = v.len(); \
             let t = if n == 0 { 0 } else { *v[0] * 1000 + *v[n - 1] }; n as u64 * 10_000_000 + t",
            [M, M, M, M],
        ),
        row(
            "unwind_for_each_move_refmut",
            Unwind,
            "drop(d); let cell = RefCell::new(0u64); \
             { let mut m = cell.borrow_mut(); a.iter().for_each(move |&x| *m = *m * 3 + x); } \
             let r = match cell.try_borrow() { Ok(v) => *v, Err(_) => u64::MAX }; r",
            [M, M, M, M],
        ),
    ]
}

fn lib_source(row: &Row) -> String {
    format!(
        "{PRELUDE}#[inline(never)]\n\
         pub fn k(a: &[u64], log: &Cell<u64>, calls: &Cell<u64>) -> u64 {{\n    \
         let acc = Cell::new(0u64);\n    \
         let s = &acc;\n    \
         let d = D {{ log, calls, tag: 7 }};\n    \
         {}\n}}\n",
        row.body
    )
}

fn main_source(row: &Row) -> String {
    let (hook, call) = match row.panic {
        Panic::Abort => (
            "",
            "format!(\"{}\", klib::k(black_box(&all[..n]), &log, &calls))",
        ),
        Panic::Unwind => (
            "    std::panic::set_hook(Box::new(|_| {}));\n",
            "match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| \
             klib::k(black_box(&all[..n]), &log, &calls))) {\n\
             \x20           Ok(r) => format!(\"{}\", r),\n\
             \x20           Err(_) => \"panicked\".to_owned(),\n\
             \x20       }",
        ),
    };
    format!(
        "use std::cell::Cell;\n\
         use std::hint::black_box;\n\
         fn main() {{\n\
         {hook}\
         \x20   let all = [10u64, 20, 30, 40, 50];\n\
         \x20   for n in {LENGTHS} {{\n\
         \x20       let log = Cell::new(0u64);\n\
         \x20       let calls = Cell::new(0u64);\n\
         \x20       let r = {call};\n\
         \x20       println!(\"n={{}} r={{}} log={{}} calls={{}}\", n, r, log.get(), calls.get());\n\
         \x20   }}\n\
         }}\n"
    )
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tcg_owned_closure_drop_{stem}_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn base_command(opt: &str, panic: Panic) -> Command {
    let mut cmd = toolchain_support::rustc_command();
    cmd.args([panic.flag(), "-Ccodegen-units=1"]);
    cmd.arg(format!("-Copt-level={opt}"));
    cmd
}

fn add_backend(cmd: &mut Command, dylib: &Path) {
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(backend_arg);
    cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
}

/// Compile the row's library; `Err` carries the compiler's stderr.
fn compile_lib(
    dir: &Path,
    row: &Row,
    opt: &str,
    backend: Option<&Path>,
    rlib: &Path,
) -> Result<(), String> {
    let src = dir.join("klib.rs");
    std::fs::write(&src, lib_source(row)).expect("write library source");
    let mut cmd = base_command(opt, row.panic);
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    if let Some(dylib) = backend {
        add_backend(&mut cmd, dylib);
    }
    cmd.arg("-o").arg(rlib).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Link the LLVM-compiled caller against `rlib`.
fn compile_main(dir: &Path, row: &Row, label: &str, rlib: &Path, bin: &Path) {
    let src = dir.join("kmain.rs");
    std::fs::write(&src, main_source(row)).expect("write caller source");
    let mut cmd = base_command("3", row.panic);
    cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(rlib);
    cmd.arg("--extern").arg(extern_arg);
    cmd.arg("-o").arg(bin).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    assert!(
        output.status.success(),
        "row {label}: the LLVM-compiled caller did not build: <<<{}>>>",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_with_timeout(bin: &Path) -> Option<Output> {
    let mut child = Command::new(bin)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the compiled program");
    let start = Instant::now();
    loop {
        if child
            .try_wait()
            .expect("poll the compiled program")
            .is_some()
        {
            return Some(child.wait_with_output().expect("collect program output"));
        }
        if start.elapsed() >= RUN_TIMEOUT {
            child.kill().expect("kill the timed-out program");
            let _ = child.wait_with_output();
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Every `[TCG-...]` code in `stderr`.
fn refusal_codes(stderr: &str) -> Vec<String> {
    let mut codes = Vec::new();
    let mut rest = stderr;
    while let Some(start) = rest.find("[TCG-") {
        let tail = &rest[start + 1..];
        let Some(end) = tail.find(']') else {
            break;
        };
        codes.push(tail[..end].to_owned());
        rest = &tail[end..];
    }
    codes
}

/// Whether `stderr` is a `[code]` refusal with a root line naming `root` and
/// carrying `root_line`.
fn names_refusal(stderr: &str, code: &str, root: &str, root_line: &str) -> bool {
    stderr.contains(&format!("[{code}]"))
        && stderr
            .lines()
            .any(|line| line.contains(root) && line.contains(root_line))
}

/// The oracle's output, then the bridge's verdict for one row at one level.
fn check_row(dylib: &Path, row: &Row, opt: &str, expect: Expect) -> String {
    let label = format!("{}@O{opt}", row.name);
    let dir = workdir(&label);
    let oracle_rlib = dir.join("llvm").join("libklib.rlib");
    let bridge_rlib = dir.join("bridge").join("libklib.rlib");
    std::fs::create_dir_all(oracle_rlib.parent().unwrap()).expect("create oracle dir");
    std::fs::create_dir_all(bridge_rlib.parent().unwrap()).expect("create bridge dir");

    compile_lib(&dir, row, opt, None, &oracle_rlib).unwrap_or_else(|e| {
        panic!("row {label}: the LLVM oracle library did not build: <<<{e}>>>")
    });
    let oracle_bin = dir.join("llvm_kmain");
    compile_main(&dir, row, &label, &oracle_rlib, &oracle_bin);
    let oracle = run_with_timeout(&oracle_bin)
        .unwrap_or_else(|| panic!("row {label}: the LLVM oracle did not finish"));
    let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
    assert!(
        oracle.status.success() && oracle_stdout.lines().count() == LENGTH_COUNT,
        "row {label}: the LLVM oracle must print one line per input length and exit 0; \
         status {:?}, stdout <<<{oracle_stdout}>>>",
        oracle.status
    );

    let verdict = match compile_lib(&dir, row, opt, Some(dylib), &bridge_rlib) {
        Ok(()) => {
            let bridge_bin = dir.join("bridge_kmain");
            compile_main(&dir, row, &label, &bridge_rlib, &bridge_bin);
            let Some(bridge) = run_with_timeout(&bridge_bin) else {
                panic!(
                    "row {label}: the bridge-compiled library did not finish within \
                     {RUN_TIMEOUT:?}; oracle printed <<<{oracle_stdout}>>>"
                );
            };
            let bridge_stdout = String::from_utf8_lossy(&bridge.stdout).into_owned();
            assert_eq!(
                (bridge.status.code(), bridge_stdout.as_str()),
                (oracle.status.code(), oracle_stdout.as_str()),
                "row {label}: the bridge-compiled library disagrees with LLVM (exit code \
                 None is a signal). A by-value closure or iterator the intercepted call \
                 owns was dropped a different number of times, or at a different point, \
                 than the real callee drops it: drop it once on the drive's exit and \
                 cleanup edges, or refuse the shape with [{OWNED_DROP}], rather than \
                 relaxing this assertion. stderr <<<{}>>>",
                String::from_utf8_lossy(&bridge.stderr)
            );
            "MATCHED LLVM".to_owned()
        }
        Err(stderr) => {
            assert!(
                !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
                "row {label}: the bridge crashed instead of failing closed: <<<{stderr}>>>"
            );
            let codes = refusal_codes(&stderr);
            match expect {
                Expect::Match => panic!(
                    "row {label}: this shape compiles and runs correctly and must not be \
                     refused (codes {codes:?}): <<<{stderr}>>>"
                ),
                Expect::MatchOrRefusal {
                    code,
                    root,
                    root_line,
                } => {
                    assert!(
                        names_refusal(&stderr, code, root, root_line),
                        "row {label}: expected a match or the [{code}] refusal of the root \
                         `…{root}` for `{root_line}`; got codes {codes:?}: <<<{stderr}>>>"
                    );
                    format!("REFUSED [{code}] (fail-closed)")
                }
            }
        }
    };
    let _ = std::fs::remove_dir_all(&dir);
    verdict
}

/// A fixed native contract for capture order, mutation of the actual closure
/// frame, and callback unwind into closure/caller cleanup. Each row must match
/// at every level and all four input lengths; no refusal earns a pass.
#[test]
fn owned_cleanup_layout_order_and_callback_unwind_match_llvm() {
    const TEST: &str = "owned_cleanup_layout_order_and_callback_unwind_match_llvm";
    const CASES: [&str; 6] = [
        "for_each_move_two_guards",
        "for_each_move_mutated_mixed_guard",
        "fold_move_mutated_mixed_guard",
        "unwind_for_each_move_panics",
        "unwind_fold_move_panics",
        "unwind_for_each_move_panics_under_caller_guard",
    ];
    assert!(
        !toolchain_support::skip_without_backend_knobs(TEST),
        "the native cleanup contract requires the pinned Trust backend controls"
    );
    let dylib = backend_artifact_support::current_test_backend();
    let all = rows();
    let mut checked = 0;
    for name in CASES {
        let row = all
            .iter()
            .find(|row| row.name == name)
            .expect("cleanup row");
        assert!(
            row.expect
                .iter()
                .all(|expect| matches!(expect, Expect::Match)),
            "every original cleanup expectation must remain a native match: {name}"
        );
        for opt in OPT_LEVELS {
            let verdict = check_row(&dylib, row, opt, M);
            eprintln!("cleanup edge {name}@O{opt}: {verdict}");
            checked += 1;
        }
    }
    assert_eq!(checked, 24);
    println!(
        "OWNED_CLOSURE_CLEANUP_EDGES rows=6 cells=24 input_lengths=0,1,3,5 matched=24 opts=0,1,2,3"
    );
}

/// Borrowing a pointer-sized owner must expose the owner's stable address,
/// rather than separately materializing snapshots for equal call arguments.
/// Both equal and distinct owners are observed by an out-of-line Rust callee.
#[cfg(all(target_arch = "aarch64", target_os = "linux"))]
#[test]
fn owned_pointer_call_references_preserve_identity() {
    assert!(
        !toolchain_support::skip_without_backend_knobs(
            "owned_pointer_call_references_preserve_identity"
        ),
        "the native owner-reference contract requires the pinned Trust backend controls"
    );
    let dylib = backend_artifact_support::current_test_backend();
    let cases = [
        row(
            "rc_call_reference_identity",
            Abort,
            "#[inline(never)] fn probe(a: &Rc<u64>, b: &Rc<u64>) -> u64 { \
             u64::from(std::ptr::eq(a, b)) * 100 + Rc::strong_count(a) as u64 + **b } \
             let first = Rc::new(5u64); let second = Rc::new(7u64); \
             probe(&first, &first) * 1000 + probe(&first, &second)",
            [M, M, M, M],
        ),
        row(
            "box_call_reference_identity",
            Abort,
            "#[inline(never)] fn probe(a: &Box<u64>, b: &Box<u64>) -> u64 { \
             u64::from(std::ptr::eq(a, b)) * 100 + **a * 10 + **b } \
             let first = Box::new(5u64); let second = Box::new(7u64); \
             probe(&first, &first) * 1000 + probe(&first, &second)",
            [M, M, M, M],
        ),
    ];
    let mut checked = 0;
    for row in &cases {
        for opt in OPT_LEVELS {
            let verdict = check_row(&dylib, row, opt, M);
            eprintln!("owner reference {}@O{opt}: {verdict}", row.name);
            checked += 1;
        }
    }
    assert_eq!(checked, 8);
    println!(
        "OWNED_POINTER_CALL_REFERENCES rows=2 cells=8 input_lengths=0,1,3,5 matched=8 opts=0,1,2,3"
    );
}

#[test]
fn owned_closures_and_iterators_are_dropped_once_or_refused() {
    if toolchain_support::skip_without_backend_knobs(
        "owned_closures_and_iterators_are_dropped_once_or_refused",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let rows = rows();
    let mut report = Vec::new();
    for row in &rows {
        for (opt, expect) in OPT_LEVELS.iter().zip(row.expect) {
            let verdict = check_row(&dylib, row, opt, expect);
            eprintln!("row {}@O{opt} ({:?}): {verdict}", row.name, row.panic);
            report.push(format!("{}@O{opt} {verdict}", row.name));
        }
    }
    assert_eq!(
        report.len(),
        244,
        "the entire owned-closure optimization grid must run"
    );
    eprintln!("owned-closure drop rows ({}): {report:#?}", report.len());
}

/// A destructor's store before panicking must be visible to caller cleanup.
/// The original fixture's historical O2/O3 exclusions provide no qualification.
#[test]
fn destructor_panic_preserves_stores_and_caller_cleanup() {
    const TEST: &str = "destructor_panic_preserves_stores_and_caller_cleanup";
    assert!(
        !toolchain_support::skip_without_backend_knobs(TEST),
        "the destructor-panic contract requires the pinned Trust backend controls"
    );
    let dylib = backend_artifact_support::current_test_backend();
    let all = rows();
    let row = all
        .iter()
        .find(|row| row.name == "unwind_for_each_move_drop_panics")
        .expect("original destructor-panic row");
    for opt in OPT_LEVELS {
        let verdict = check_row(&dylib, row, opt, M);
        eprintln!("destructor panic {}@O{opt}: {verdict}", row.name);
    }
    println!("DESTRUCTOR_PANIC_STORES rows=1 cells=4 matched=4 input_lengths=0,1,3,5 opts=0,1,2,3");
}

/// The rows the bridge now compiles, with the WHOLE program compiled by the
/// bridge as well. The program prints each result and exits with a checksum of
/// them. Bridge-compiled code has no `catch_unwind`, so the `panic=unwind`
/// program runs only rows that do not panic: it pins the unwind-lowering
/// bodies' normal paths. Measured on f349c8652: both programs compiled and
/// printed wrong logs and lengths at -O0 and -O3.
#[test]
fn whole_program_owned_closures_are_dropped_once() {
    if toolchain_support::skip_without_backend_knobs(
        "whole_program_owned_closures_are_dropped_once",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let all = rows();
    let pick = |names: &[&str]| -> Vec<&Row> {
        names
            .iter()
            .map(|name| {
                all.iter()
                    .find(|row| row.name == *name)
                    .unwrap_or_else(|| panic!("no row named {name}"))
            })
            .collect()
    };
    let programs = [
        (
            Panic::Abort,
            pick(&[
                "for_each_move_slice",
                "for_each_move_rev",
                "for_each_move_take",
                "for_each_move_two_guards",
                "for_each_move_refmut",
                "fold_move_slice",
                "fold_move_rev",
                "collect_refs",
                "collect_refs_rev",
                "collect_refs_take",
                "collect_enumerated_refs",
                "from_iter_refs",
                "vecdeque_collect_refs",
                "extend_refs_onto_nonempty",
                "collect_refs_then_push",
            ]),
        ),
        (
            Panic::Unwind,
            pick(&[
                "unwind_for_each_move",
                "unwind_fold_move",
                "unwind_collect_refs",
                "unwind_for_each_move_refmut",
            ]),
        ),
    ];
    let dir = workdir("whole_program");
    for (panic, rows) in &programs {
        let src = dir.join(format!("whole_{panic:?}.rs"));
        std::fs::write(&src, whole_program_source(rows)).expect("write program source");
        for opt in OPT_LEVELS {
            let label = format!("whole program {panic:?} O{opt}");
            let build = |backend: Option<&Path>, bin: &Path| -> Result<(), String> {
                let mut cmd = base_command(opt, *panic);
                cmd.args(["--crate-type", "bin", "--crate-name", "whole"]);
                if let Some(dylib) = backend {
                    add_backend(&mut cmd, dylib);
                }
                cmd.arg("-o").arg(bin).arg(&src);
                let output = cmd.output().expect("spawn the compiler");
                if output.status.success() {
                    Ok(())
                } else {
                    Err(String::from_utf8_lossy(&output.stderr).into_owned())
                }
            };
            let oracle_bin = dir.join(format!("llvm_whole_{panic:?}_O{opt}"));
            build(None, &oracle_bin)
                .unwrap_or_else(|e| panic!("{label}: the LLVM oracle did not build: <<<{e}>>>"));
            let oracle = run_with_timeout(&oracle_bin)
                .unwrap_or_else(|| panic!("{label}: the LLVM oracle did not finish"));
            let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
            assert_eq!(
                oracle_stdout.lines().count(),
                rows.len() * LENGTH_COUNT,
                "{label}: the LLVM oracle must print one line per row and length: \
                 <<<{oracle_stdout}>>>"
            );
            let bridge_bin = dir.join(format!("bridge_whole_{panic:?}_O{opt}"));
            build(Some(&dylib), &bridge_bin).unwrap_or_else(|e| {
                panic!(
                    "{label}: the bridge must compile the whole program (codes {:?}): <<<{e}>>>",
                    refusal_codes(&e)
                )
            });
            let bridge = run_with_timeout(&bridge_bin).unwrap_or_else(|| {
                panic!("{label}: the bridge-compiled program did not finish within {RUN_TIMEOUT:?}")
            });
            assert_eq!(
                (
                    bridge.status.code(),
                    String::from_utf8_lossy(&bridge.stdout).as_ref()
                ),
                (oracle.status.code(), oracle_stdout.as_str()),
                "{label}: the bridge-compiled program disagrees with LLVM (exit code None is \
                 a signal)"
            );
            eprintln!("{label}: MATCHED LLVM");
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// One program holding every row as its own function, called over each input
/// length; `main` exits with a checksum of the printed values.
fn whole_program_source(rows: &[&Row]) -> String {
    let mut src = PRELUDE.to_owned();
    src.push_str("use std::hint::black_box;\n");
    let mut calls = String::new();
    for row in rows {
        src.push_str(&format!(
            "#[inline(never)]\n\
             fn {}(a: &[u64], log: &Cell<u64>, calls: &Cell<u64>) -> u64 {{\n    \
             let acc = Cell::new(0u64);\n    \
             let s = &acc;\n    \
             let d = D {{ log, calls, tag: 7 }};\n    \
             {}\n}}\n",
            row.name, row.body
        ));
        calls.push_str(&format!(
            "        let log = Cell::new(0u64);\n\
             \x20       let calls = Cell::new(0u64);\n\
             \x20       let r = {}(black_box(&all[..n]), &log, &calls);\n\
             \x20       println!(\"{} n={{}} r={{}} log={{}} calls={{}}\", n, r, log.get(), calls.get());\n\
             \x20       h = h.wrapping_mul(31).wrapping_add(r ^ log.get() ^ calls.get());\n",
            row.name, row.name
        ));
    }
    // A `while` over an indexed array: the bridge refuses `{:?}` formatting and
    // a by-value array iterator in `main`, which are not under test here.
    src.push_str(&format!(
        "fn main() {{\n\
         \x20   let all = [10u64, 20, 30, 40, 50];\n\
         \x20   let lengths = {LENGTHS};\n\
         \x20   let mut h = 0u64;\n\
         \x20   let mut i = 0;\n\
         \x20   while i < {LENGTH_COUNT} {{\n\
         \x20       let n = lengths[i];\n\
         \x20       i += 1;\n\
         {calls}\
         \x20   }}\n\
         \x20   std::process::exit((h % 251) as i32);\n\
         }}\n"
    ));
    src
}

#[test]
fn refusal_match_needs_the_code_and_the_root_line() {
    let stderr = "error: [TCG-MIR-UNSUPPORTED] rustc_codegen_trust_cg: cannot compile\n  \
                  - _RNvCs0_4klib1k (reachable): [TCG-INTERCEPT-OWNED-DROP] `Iterator::sum` \
                  takes its iterator `self`";
    assert_eq!(
        refusal_codes(stderr),
        vec![MIR_UNSUPPORTED.to_owned(), OWNED_DROP.to_owned()]
    );
    assert!(names_refusal(
        stderr,
        OWNED_DROP,
        KERNEL_ROOT,
        "[TCG-INTERCEPT-OWNED-DROP]"
    ));
    assert!(!names_refusal(
        stderr,
        OWNED_DROP,
        "3ptr9drop_glue",
        "[TCG-INTERCEPT-OWNED-DROP]"
    ));
    assert!(!names_refusal(
        stderr,
        IR_LOWER,
        KERNEL_ROOT,
        "[TCG-IR-LOWER]"
    ));
    assert!(refusal_codes("no codes here").is_empty());
}

#[test]
fn row_names_are_unique() {
    let rows = rows();
    let mut names: Vec<&str> = rows.iter().map(|row| row.name).collect();
    names.sort_unstable();
    names.dedup();
    assert_eq!(names.len(), rows.len(), "row names must be unique");
}
