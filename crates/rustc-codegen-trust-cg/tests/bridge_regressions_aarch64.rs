// Compiled only on an AArch64 host: another host builds this target with no
// test in it, never one that passes without running (L06-P10).
#![cfg(target_arch = "aarch64")]

#[path = "support/a64_differential.rs"]
mod a64_differential;
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// crates/rustc-codegen-trust-cg/tests/bridge_regressions_aarch64.rs
//
// Minimized regressions for the silent miscompiles the AArch64 bridge
// differential found (ledger L06-P3; `bridge_differential_aarch64`,
// `bridge_feature_suites_aarch64`). Each was a wrong value on
// aarch64-apple-darwin against LLVM, in target-independent bridge lowering.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// (1) CONSUMED CLOSURE DESTRUCTORS. The bridge lowers `for_each`/`fold`/`sum`/`count`/`collect` over a
// `map`/`filter` chain, `Vec::retain`, `Vec::resize_with` and `sort_by_key` as
// loops it synthesizes, calling the closure body directly. The std methods
// take the closure BY VALUE and drop it when done; the synthesized loops never
// ran that drop glue. Measured on aarch64-apple-darwin before the fix
// (`no-proof-certs`, -Copt-level 0 and 3, LLVM against this backend):
//
//     program                                   LLVM   trust-cg
//     m103 `a.iter().collect::<Vec<&i32>>()`       3      0    (core's
//         `extend_trusted` closure owns a `SetLenOnDrop`; its Drop writes `len`)
//     `for_each(move |x| ..)` owning a Drop      106      6
//     `fold(0, move |acc, x| ..)`                106      6
//     `map(move ..).sum()`                       112     12
//     `filter(move ..).sum()`                    102      2
//     `map(move ..).count()`                     104      4
//     `map(move ..).collect::<Vec<_>>()`         118     18
//     `Vec::retain(move ..)`                     102      2
//     `Vec::resize_with(4, move ..)`             117     17
//     `sort_by_key(move ..)` (-O0)               101      1
//
// The first fix refused a closure whose type had a SIGNIFICANT destructor
// (rustc's `has_significant_drop`). That predicate exempts `Rc`/`Arc`
// (`#[rustc_insignificant_dtor]`), whose skipped count decrement the program
// reads back, and it admitted a `Box` whose skipped free a user allocator
// counts; measured the same way on that fix (LLVM against this backend,
// -Copt-level 0 and 3 alike):
//
//     program (a `move` closure)                              LLVM   trust-cg
//     `map(..).sum()`, then `Rc::strong_count`                  22     32
//     `filter(..).count()`, then `Rc::get_mut`                 104      4
//     `fold(..)`, then `Rc::strong_count`                       32     52
//     `for_each(..)`, then `Rc::strong_count`                    1      2
//     `Vec::retain(..)` (`Arc`), then `Arc::strong_count`       12     22
//     `map(..).sum()` owning the `Rc`, then `Weak::upgrade`    118     18
//     `map(..).sum()` owning `Some(rc)`, then `strong_count`    13     23
//     `map(..).sum()` owning a `Box` under a counting
//         `#[global_allocator]`, then its free count           118     18
//
// for_each and fold run rustc's actual closure drop glue on normal and
// unwind exits. Every other modeled consumer must account for all owned
// values or refuse by name; allocation-only owners have no leak exemption.
// The original allocation fixtures remain positive where real cleanup exists,
// or explicit named-refusal controls where it does not. Borrowing controls
// retain native must-match assertions. Independent glibc observation checks
// the actual captured-Box release separately from these value checks.
//
// (2) `None::<Ordering>` FROM A FLOAT `Vec::partial_cmp`. The intercepted
// `Vec<f32/f64>::partial_cmp` called a helper answering 2 for an unordered
// (NaN) lane and stored that byte as `None`. The Trust compiler's layout of
// `Option<Ordering>` reserves 0xFE for `None`, so the result read back as an
// invalid `Option`: `m122`'s IEEE row exited 6 against LLVM's 8, and a `match`
// on it trapped (exit 133). The byte is now rustc's layout's.
//
// (3) `u128::saturating_add`. Its clamp constant was spelled
// `Constant::Int(-1)` at `U128`, which trust-ir's one-spelling rule rejects, so
// every such function failed closed (`i128_saturating` in the corpus). Not a
// wrong value, but the corpus row is now a must-match row, pinned here too.
//
// (4) A `Chain` HALF CORE CLEARED. core's `Chain` bodies set an exhausted
// half to `None` (`next` clears `a`, `next_back` clears `b`, `nth` clears an
// `a` it runs past). The bridge's drive of `a.chain(b)` (`ChainSource::Concat`
// in `emit_source_next`, and its count in `emit_source_exact_remaining`)
// never read the `Option` tags: it advanced a cleared half's payload, which
// for `slice::Iter` is the null `ptr` niche (a null dereference) and for a
// `Range` bytes the `None` write left undefined. Found in review of the leak
// lanes' rebase; pre-existing on main 988fd541d. MEASURED at 14e9bc711 (debug
// bridge, Trust 9192, this test run against that backend): 7 of the 16 cells
// diverged: three of the four `slice` rows at -O0 and -O3, killed by SIGSEGV,
// and `range_count_max_after_next_back_clears_b` at -O3, exiting 31 against
// LLVM's 21. What a cleared `Range` half's leftover bytes hold depends on the
// code around the `None` write, so the other `Range` rows matched there.
//
// (5) A CAPTURED PAIR MAPPER IS NOT THE CALLBACK'S OUTPUT. `974177141` sent
// every `Vec` call whose closure argument CAPTURED a closure returning an
// admitted two-leaf aggregate to std's own body (its capture walk followed
// user closures). For the in-place models that loses a capability: std's
// `resize_with` calls `extend_trusted`, which the bridge refuses by name, so
// `t.resize_with(5, || { k += 1; let (a, b) = mk(k); a + b })` with
// `mk = |x| (x, x * 9)` was refused at -O0..-O3 under both strategies
// (MEASURED at fb96d7a17, debug bridge, Trust 9192) while the same closure
// without the pair capture built and matched. A model calls the closure's
// own body, which calls `mk` with `mk`'s own return ABI, so the models now
// decide by the callback's own output (and std glue custody) alone. The
// iterator drives keep their capture route: the real bodies it selects match
// LLVM where the drives refuse every capturing callback of the same shape
// (`try_fold` breaking with an `Option`, a Map `for_each` and `extend` at
// -O2/-O3, a fold over `enumerate` at -O0/-O1). Callbacks whose OWN output is
// the pair still leave the models and drives for std's bodies.
// The narrowing is the four model arms' alone (`retain`, `retain_mut`,
// `dedup_by`, `resize_with`: the arms that call a closure argument). Every
// other std callee with a modeled `Vec` self or destination has no model that
// calls its closure, and keeps the capture route to std's body. Narrowing it
// for every callee (e1f8d2ec9, found in review) refused `pop_if`, `extract_if`
// and `Option`/`Result::map_or[_else]` producing a `Vec` by name at
// -O0..-O3 under both strategies, where fb96d7a17 matched LLVM (MEASURED,
// debug bridge, Trust 9192: the six non-model rows below, 48 cells).

use a64_differential::{Lane, Panic, Program, Verdict};

const OPT_LEVELS: [&str; 2] = ["0", "3"];

/// A guard whose destructor adds 100 to a counter the program exits with.
const GUARD: &str = "struct D<'a>(&'a mut i32);\n\
                     impl Drop for D<'_> { fn drop(&mut self) { *self.0 += 100; } }\n";

/// `(name, body, LLVM exit)` rows whose closure OWNS the guard: each must
/// match LLVM or refuse by name. The guard's destructor adds 100 to the exit,
/// so the pinned exit counts it and a match proves the closure's glue ran.
const OWNING: &[(&str, &str, i32)] = &[
    (
        "for_each",
        "fn main() { let mut n = 0; { let d = D(&mut n); let a = [1i32, 2, 3]; \
         a.iter().for_each(move |x| { *d.0 += *x; }); } std::process::exit(n); }",
        106,
    ),
    (
        "fold",
        "fn main() { let mut n = 0; let s = { let d = D(&mut n); let a = [1i32, 2, 3]; \
         a.iter().fold(0i32, move |acc, x| { let _ = &d; acc + *x }) }; \
         std::process::exit(n + s); }",
        106,
    ),
    (
        "map_sum",
        "fn main() { let mut n = 0; let s: i32 = { let d = D(&mut n); let a = [1i32, 2, 3]; \
         a.iter().map(move |x| { let _ = &d; *x * 2 }).sum() }; std::process::exit(n + s); }",
        112,
    ),
    (
        "filter_sum",
        "fn main() { let mut n = 0; let s: i32 = { let d = D(&mut n); \
         (0..4i32).filter(move |x| { let _ = &d; x % 2 == 0 }).sum() }; \
         std::process::exit(n + s); }",
        102,
    ),
    (
        "map_count",
        "fn main() { let mut n = 0; let c = { let d = D(&mut n); \
         (0..4i32).map(move |x| { let _ = &d; x }).count() }; std::process::exit(n + c as i32); }",
        104,
    ),
    (
        "map_collect",
        "fn main() { let mut n = 0; let v: Vec<i32> = { let d = D(&mut n); \
         (0..4i32).map(move |x| { let _ = &d; x * 3 }).collect() }; \
         std::process::exit(n + v.iter().sum::<i32>()); }",
        118,
    ),
    (
        "retain",
        "fn main() { let mut n = 0; let mut v = vec![1i32, 2, 3, 4]; { let d = D(&mut n); \
         v.retain(move |x| { let _ = &d; *x % 2 == 0 }); } std::process::exit(n + v.len() as i32); }",
        102,
    ),
    (
        "resize_with",
        "fn main() { let mut n = 0; let mut v = vec![1i32, 2]; { let d = D(&mut n); \
         v.resize_with(4, move || { let _ = &d; 7 }); } \
         std::process::exit(n + v.iter().sum::<i32>()); }",
        117,
    ),
    (
        "dedup_by",
        "fn main() { let mut n = 0; let mut v = vec![1i32, 1, 2, 3, 3]; { let d = D(&mut n); \
         v.dedup_by(move |a, b| { let _ = &d; *a == *b }); } \
         std::process::exit(n + v.len() as i32); }",
        103,
    ),
    (
        "sort_by_key",
        "fn main() { let mut n = 0; let mut v = vec![3i32, 1, 2]; { let d = D(&mut n); \
         v.sort_by_key(move |x| { let _ = &d; *x }); } std::process::exit(n + v[0]); }",
        101,
    ),
];

/// `(name, body, LLVM exit)` rows whose closure owns an `Rc`/`Arc` (bare or
/// in an `Option`), or a `Box` around a user `Drop`. rustc calls the `Rc`/`Arc`
/// destructors insignificant, but their skipped count update is observable.
/// Each must match LLVM or refuse by name; the LLVM exit code is pinned and
/// reads the count or the destructor back.
const OWNING_COUNTED: &[(&str, &str, i32)] = &[
    (
        "rc_map_sum_strong_count",
        "use std::rc::Rc; fn main() { let rc = Rc::new(3i32); \
         let s: i32 = { let r2 = rc.clone(); (0..3i32).map(move |x| x + *r2).sum() }; \
         std::process::exit(s + 10 * Rc::strong_count(&rc) as i32); }",
        22,
    ),
    (
        "rc_filter_count_get_mut",
        "use std::rc::Rc; fn main() { let mut rc = Rc::new(4i32); \
         let c = { let r2 = rc.clone(); (0..6i32).filter(move |x| *x < *r2).count() }; \
         let unique = Rc::get_mut(&mut rc).is_some(); \
         std::process::exit(c as i32 + if unique { 100 } else { 0 }); }",
        104,
    ),
    (
        "rc_fold_strong_count",
        "use std::rc::Rc; fn main() { let rc = Rc::new(2i32); let a = [1i32, 2, 3]; \
         let s = { let r2 = rc.clone(); a.iter().fold(0i32, move |acc, x| acc + *x * *r2) }; \
         std::process::exit(s + 20 * Rc::strong_count(&rc) as i32); }",
        32,
    ),
    (
        "rc_for_each_strong_count",
        "use std::rc::Rc; fn main() { let rc = Rc::new(0i32); let a = [1i32, 2, 3]; \
         { let r2 = rc.clone(); \
         a.iter().for_each(move |x| { let _ = &r2; std::hint::black_box(*x); }); } \
         std::process::exit(Rc::strong_count(&rc) as i32); }",
        1,
    ),
    (
        "arc_retain_strong_count",
        "use std::sync::Arc; fn main() { let a = Arc::new(2i32); let mut v = vec![1i32, 2, 3, 4]; \
         { let a2 = a.clone(); v.retain(move |x| *x % *a2 == 0); } \
         std::process::exit(v.len() as i32 + 10 * Arc::strong_count(&a) as i32); }",
        12,
    ),
    (
        "rc_map_sum_weak_upgrade",
        "use std::rc::Rc; fn main() { let rc = Rc::new(5i32); let w = Rc::downgrade(&rc); \
         let s: i32 = (0..3i32).map(move |x| x + *rc).sum(); \
         std::process::exit(s + if w.upgrade().is_none() { 100 } else { 0 }); }",
        118,
    ),
    (
        "option_of_rc_map_sum",
        "use std::rc::Rc; fn main() { let rc = Rc::new(1i32); \
         let s: i32 = { let o = Some(rc.clone()); \
         (0..2i32).map(move |x| x + match &o { Some(r) => **r, None => 0 }).sum() }; \
         std::process::exit(s + 10 * Rc::strong_count(&rc) as i32); }",
        13,
    ),
    (
        "global_allocator_box_map_sum",
        "use std::alloc::{GlobalAlloc, Layout, System}; struct Counting; \
         static mut FREES: i32 = 0; \
         unsafe impl GlobalAlloc for Counting { \
         unsafe fn alloc(&self, l: Layout) -> *mut u8 { unsafe { System.alloc(l) } } \
         unsafe fn dealloc(&self, p: *mut u8, l: Layout) { \
         unsafe { FREES += 1; System.dealloc(p, l) } } } \
         #[global_allocator] static A: Counting = Counting; \
         fn main() { let before = unsafe { FREES }; let b = Box::new(5i64); \
         let s: i64 = (0..3i64).map(move |i| *b + i).sum(); \
         std::process::exit(s as i32 + 100 * (unsafe { FREES } - before)); }",
        118,
    ),
    (
        "box_of_guard_map_sum",
        "struct D<'a>(&'a mut i32);\n\
         impl Drop for D<'_> { fn drop(&mut self) { *self.0 += 100; } }\n\
         fn main() { let mut n = 0; let s: i32 = { let d = Box::new(D(&mut n)); \
         (0..3i32).map(move |x| { let _ = &d; x }).sum() }; std::process::exit(n + s); }",
        103,
    ),
];

/// The `OWNING_COUNTED` rows whose closure owns a `Box`: a drive that runs
/// their drop glue reaches a `Box` drop in a `drop_glue` body (a projected
/// `Box` place, or a `Box` whose payload has drop glue). A drop-free
/// payload is supported on the Linux pointer lanes too; payload destructors
/// retain their Darwin boundary and may refuse elsewhere by name.
const BOX_OWNING: &[&str] = &["global_allocator_box_map_sum", "box_of_guard_map_sum"];

/// The m103 row: core's own `extend_trusted` closure owns a `SetLenOnDrop`.
const VEC_OF_REFS: &str = "fn main() { let a = [1i32, 2, 3]; let v: Vec<&i32> = a.iter().collect(); \
                           std::process::exit(v.len() as i32); }";

/// `(name, body, LLVM exit)` controls: each must build and match LLVM.
const CONTROLS: &[(&str, &str, i32)] = &[
    (
        "for_each_borrowing",
        "fn main() { let mut n = 0; { let d = D(&mut n); let a = [1i32, 2, 3]; \
         a.iter().for_each(|x| { *d.0 += *x; }); } std::process::exit(n); }",
        106,
    ),
    (
        "map_sum_borrowing",
        "fn main() { let mut n = 0; let s: i32 = { let d = D(&mut n); let a = [1i32, 2, 3]; \
         a.iter().map(|x| { let _ = &d; *x * 2 }).sum() }; std::process::exit(n + s); }",
        112,
    ),
    (
        "retain_borrowing",
        "fn main() { let mut n = 0; let mut v = vec![1i32, 2, 3, 4]; { let d = D(&mut n); \
         v.retain(|x| { let _ = &d; *x % 2 == 0 }); } std::process::exit(n + v.len() as i32); }",
        102,
    ),
    (
        "fold_owning_option_box",
        "fn main() { let o = Some(Box::new(4i32)); let a = [1i32, 2, 3]; \
         let n = a.iter().fold(0i32, move |acc, x| acc + x * match &o { Some(b) => **b, None => 0 }); \
         std::process::exit(n); }",
        24,
    ),
];

/// Every old allocation-owner fixture stays in the corpus. A real cleanup
/// may match; a model without it must refuse rather than admit a leak.
const ALLOCATION_OWNERS: &[(&str, &str, i32)] = &[
    (
        "map_sum_owning_box",
        "fn main() { let b = Box::new(5i64); \
         let s: i64 = (0..3i64).map(move |i| *b + i).sum(); std::process::exit(s as i32); }",
        18,
    ),
    (
        "map_sum_owning_box_pair",
        "fn main() { let p = (Box::new(2i64), Box::new(3i64)); \
         let s: i64 = (0..3i64).map(move |i| *p.0 * i + *p.1).sum(); \
         std::process::exit(s as i32); }",
        15,
    ),
    (
        "retain_owning_box",
        "fn main() { let b = Box::new(2i32); let mut v = vec![1i32, 2, 3, 4, 5, 6]; \
         v.retain(move |x| *x % *b == 0); std::process::exit(10 * v.len() as i32 + v[0]); }",
        32,
    ),
    (
        "dedup_by_owning_box",
        "fn main() { let b = Box::new(3i32); let mut v = vec![1i32, 2, 4, 5, 7, 9]; \
         v.dedup_by(move |x, y| *x / *b == *y / *b); \
         std::process::exit(10 * v.len() as i32 + v[3]); }",
        49,
    ),
    (
        "resize_with_owning_box",
        "fn main() { let b = Box::new(7i32); let mut v = vec![1i32]; let mut k = 0i32; \
         v.resize_with(4, move || { k += 1; *b + k }); \
         std::process::exit(v.iter().sum::<i32>()); }",
        28,
    ),
];

fn program(id: &str, src: String, expected: Option<i32>) -> Program {
    Program {
        id: id.to_owned(),
        src,
        panic: Panic::Abort,
        overflow_checks_off: false,
        expected,
    }
}

/// The verdicts a closure-drop cell may end in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Outcome {
    /// Built, ran and matched LLVM.
    Matched,
    /// `[TCG-CLOSURE-DROP]`: a synthesized loop that would skip the glue.
    ClosureDrop,
    /// `[TCG-INTERCEPT-OWNED-DROP]`: a value the lowering takes by value whose
    /// destructor it neither runs nor admits as a `Global`-memory leak.
    OwnedDrop,
    /// `[TCG-MIR-UNSUPPORTED]` in a `drop_glue` body at a `Box` drop the bridge
    /// does not lower on this target, for a `BOX_OWNING` row only.
    BoxGlue,
}

/// The outcome a consumed-closure cell's verdict counts as, `None` for any
/// other verdict (a divergence, another refusal).
fn consumed_outcome(id: &str, verdict: &Verdict) -> Option<Outcome> {
    match verdict {
        Verdict::Matched => Some(Outcome::Matched),
        Verdict::Refused { code, .. } if last_code(code) == "TCG-CLOSURE-DROP" => {
            Some(Outcome::ClosureDrop)
        }
        Verdict::Refused { code, .. } if last_code(code) == "TCG-INTERCEPT-OWNED-DROP" => {
            Some(Outcome::OwnedDrop)
        }
        Verdict::Refused { code, line }
            if code == "TCG-MIR-UNSUPPORTED"
                && BOX_OWNING.contains(&id)
                && line.contains("3ptr9drop_glue")
                && (line.contains("TerminatorKind::Drop of a projected Box place")
                    || line.contains("TerminatorKind::Drop of Box<")) =>
        {
            Some(Outcome::BoxGlue)
        }
        _ => None,
    }
}

/// The last code of a refusal's code path (`A/B/TCG-CLOSURE-DROP`): the one
/// that names it.
fn last_code(code: &str) -> &str {
    code.rsplit('/').next().unwrap_or(code)
}

/// The outcome of a cell that must match LLVM: only a match counts.
fn must_match_outcome(_id: &str, verdict: &Verdict) -> Option<Outcome> {
    matches!(verdict, Verdict::Matched).then_some(Outcome::Matched)
}

/// Run `programs` at -O0 and -O3 with the proofs-off knob, require every cell
/// to end in an outcome `classify` admits and every pinned LLVM exit to hold,
/// and return each cell's outcome.
fn check(
    test: &str,
    programs: &[Program],
    classify: fn(&str, &Verdict) -> Option<Outcome>,
) -> Vec<Outcome> {
    a64_differential::require_prerequisites(test);
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let dylib = backend_artifact_support::current_test_backend();
    let cells =
        a64_differential::run_cells(test, &dylib, programs, &OPT_LEVELS, Lane::ProofsOff, &knob);
    let mut problems = Vec::new();
    let mut outcomes = Vec::new();
    for cell in &cells {
        match classify(&cell.id, &cell.verdict) {
            Some(outcome) => outcomes.push(outcome),
            None => problems.push(format!(
                "`{}` -Copt-level={}: {:?}",
                cell.id, cell.opt, cell.verdict
            )),
        }
        if let (Some(code), Some(run)) = (cell.expected, &cell.oracle) {
            if run.ending != a64_differential::Ending::Exited(code) {
                problems.push(format!(
                    "`{}`: LLVM ended {:?}, not exit {code}",
                    cell.id, run.ending
                ));
            }
        }
    }
    assert!(
        problems.is_empty(),
        "{test}: {} problem(s):\n{}",
        problems.len(),
        problems.join("\n")
    );
    outcomes
}

/// How many of `outcomes` are `outcome`.
fn count(outcomes: &[Outcome], outcome: Outcome) -> usize {
    outcomes.iter().filter(|seen| **seen == outcome).count()
}

/// Every closure whose drop glue does more than free memory (a user `Drop`,
/// an `Rc`/`Arc` count), consumed by an intercepted std call, either runs that
/// glue and matches LLVM's destructor-counting exit or is refused by name, at
/// -O0 and -O3.
#[test]
fn consumed_closures_with_observable_drop_glue_match_llvm_or_refuse_by_name() {
    let mut programs: Vec<Program> = OWNING
        .iter()
        .map(|(name, body, code)| program(name, format!("{GUARD}{body}"), Some(*code)))
        .collect();
    programs.extend(
        OWNING_COUNTED
            .iter()
            .map(|(name, src, code)| program(name, (*src).to_owned(), Some(*code))),
    );
    programs.push(program(
        "vec_of_refs_collect",
        VEC_OF_REFS.to_owned(),
        Some(3),
    ));
    let outcomes = check(
        "consumed_closures_with_observable_drop_glue_match_llvm_or_refuse_by_name",
        &programs,
        consumed_outcome,
    );
    println!(
        "CLOSURE_DROP_CONSUMED rows={} cells={} matched={} refused_closure_drop={} \
         refused_owned_drop={} refused_box_glue={} opts=0,3",
        programs.len(),
        outcomes.len(),
        count(&outcomes, Outcome::Matched),
        count(&outcomes, Outcome::ClosureDrop),
        count(&outcomes, Outcome::OwnedDrop),
        count(&outcomes, Outcome::BoxGlue),
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}

/// Retained allocation owners must run with their real cleanup or refuse
/// through the shared ownership admission. A value-only match is checked in
/// addition to the independent native allocation observer regression.
#[test]
fn uncleaned_allocation_owners_match_or_refuse_by_name() {
    let programs: Vec<Program> = ALLOCATION_OWNERS
        .iter()
        .map(|(name, body, code)| program(name, (*body).to_owned(), Some(*code)))
        .collect();
    let outcomes = check(
        "uncleaned_allocation_owners_match_or_refuse_by_name",
        &programs,
        consumed_outcome,
    );
    println!(
        "CLOSURE_DROP_ALLOCATION rows={} cells={} matched={} refused_closure_drop={} refused_owned_drop={} opts=0,3",
        programs.len(),
        outcomes.len(),
        count(&outcomes, Outcome::Matched),
        count(&outcomes, Outcome::ClosureDrop),
        count(&outcomes, Outcome::OwnedDrop),
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}

/// Borrowed captures and a fold with real Box cleanup must match natively.
#[test]
fn borrowing_and_cleaned_fold_closures_match_llvm() {
    let programs: Vec<Program> = CONTROLS
        .iter()
        .map(|(name, body, code)| program(name, format!("{GUARD}{body}"), Some(*code)))
        .collect();
    let outcomes = check(
        "borrowing_and_cleaned_fold_closures_match_llvm",
        &programs,
        must_match_outcome,
    );
    println!(
        "CLOSURE_DROP_CONTROLS rows={} cells={} matched={} opts=0,3",
        programs.len(),
        outcomes.len(),
        count(&outcomes, Outcome::Matched),
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// `Vec<f64>`/`Vec<f32>::partial_cmp` with a NaN lane is `None` exactly as
/// rustc lays it out, read back by `is_none`, `==` and a `match`.
#[test]
fn float_vec_partial_cmp_none_matches_llvm() {
    const NAN64: &str = "std::hint::black_box(f64::from_bits(0x7ff8_0000_0000_0042))";
    const NAN32: &str = "std::hint::black_box(f32::from_bits(0x7fc0_0042))";
    let rows = [
        (
            "nan_vs_nan_match",
            format!(
                "fn main() {{ let n = {NAN64}; let r = vec![n].partial_cmp(&vec![n]); \
                 std::process::exit(match r {{ None => 10, Some(std::cmp::Ordering::Less) => 11, \
                 Some(std::cmp::Ordering::Equal) => 12, Some(std::cmp::Ordering::Greater) => 13 }}); }}"
            ),
            10,
        ),
        (
            "nan_vs_one_is_none",
            format!(
                "fn main() {{ let n = {NAN64}; let one = std::hint::black_box(1.0f64); \
                 std::process::exit(vec![n].partial_cmp(&vec![one]).is_none() as i32 + 20); }}"
            ),
            21,
        ),
        (
            "f32_second_lane_nan",
            format!(
                "fn main() {{ let n = {NAN32}; \
                 let r = vec![1.0f32, n].partial_cmp(&vec![1.0f32, 2.0]); \
                 std::process::exit(if r.is_none() {{ 30 }} else {{ 31 }}); }}"
            ),
            30,
        ),
        (
            "ordered_controls",
            "fn main() { use std::cmp::Ordering; let a = vec![std::hint::black_box(1.0f64), 2.0]; \
             let mut s = 0; if a.partial_cmp(&vec![1.0, 3.0]) == Some(Ordering::Less) { s += 1; } \
             if a.partial_cmp(&vec![1.0, 2.0]) == Some(Ordering::Equal) { s += 2; } \
             if a.partial_cmp(&vec![0.5]) == Some(Ordering::Greater) { s += 4; } \
             std::process::exit(s); }"
                .to_owned(),
            7,
        ),
    ];
    let programs: Vec<Program> = rows
        .iter()
        .map(|(name, src, code)| program(name, src.clone(), Some(*code)))
        .collect();
    let outcomes = check(
        "float_vec_partial_cmp_none_matches_llvm",
        &programs,
        must_match_outcome,
    );
    println!(
        "FLOAT_PARTIAL_CMP_NONE rows={} cells={} matched={} opts=0,3",
        programs.len(),
        outcomes.len(),
        count(&outcomes, Outcome::Matched),
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// `u128::saturating_add`/`saturating_sub` clamp to `u128::MAX`/0 and match
/// LLVM (they failed closed before the clamp constant's spelling was fixed).
#[test]
fn u128_saturating_add_sub_match_llvm() {
    let rows = [
        (
            "add_saturates",
            "fn main() { let a = std::hint::black_box(u128::MAX - 0x10); \
             let s = a.saturating_add(std::hint::black_box(0x20u128)); \
             std::process::exit(((s == u128::MAX) as i32) * 40 + (s as u8 % 7) as i32); }",
            43,
        ),
        (
            "add_in_range",
            "fn main() { let a = std::hint::black_box(5u128 << 100); \
             let s = a.saturating_add(std::hint::black_box(9u128)); \
             std::process::exit(((s >> 100) as i32) * 10 + (s & 0xff) as i32); }",
            59,
        ),
        (
            "sub_saturates",
            "fn main() { let a = std::hint::black_box(3u128); \
             let s = a.saturating_sub(std::hint::black_box(9u128)); \
             std::process::exit((s == 0) as i32 + 60); }",
            61,
        ),
    ];
    let programs: Vec<Program> = rows
        .iter()
        .map(|(name, src, code)| program(name, (*src).to_owned(), Some(*code)))
        .collect();
    let outcomes = check(
        "u128_saturating_add_sub_match_llvm",
        &programs,
        must_match_outcome,
    );
    println!(
        "U128_SATURATING rows={} cells={} matched={} opts=0,3",
        programs.len(),
        outcomes.len(),
        count(&outcomes, Outcome::Matched),
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// A `Chain` whose half core's own `next` / `next_back` / `nth` cleared is
/// driven by `sum`, `fold`, `collect`, `count`, `max`, `position` and `any`
/// from the half that is still `Some`, at -O0 and -O3.
#[test]
fn chain_with_a_cleared_half_matches_llvm() {
    let rows = [
        (
            "range_sum_after_next_clears_a",
            "fn main() { let mut it = (std::hint::black_box(0u64)..3)\
             .chain(std::hint::black_box(10u64)..12); for _ in 0..4 { it.next(); } \
             let s: u64 = it.sum(); std::process::exit(s as i32); }",
            11,
        ),
        (
            "slice_fold_after_next_clears_a",
            "fn main() { let s = [std::hint::black_box(1u64), 2, 3]; \
             let t = [std::hint::black_box(4u64), 5, 6]; let mut it = s.iter().chain(t.iter()); \
             for _ in 0..4 { it.next(); } \
             std::process::exit(it.fold(0u64, |a, x| a * 10 + *x) as i32); }",
            56,
        ),
        (
            "slice_collect_after_next_clears_a",
            "fn main() { let s = [std::hint::black_box(1u64), 2, 3]; \
             let t = [std::hint::black_box(4u64), 5, 6]; let mut it = s.iter().chain(t.iter()); \
             for _ in 0..4 { it.next(); } let v: Vec<u64> = it.copied().collect(); \
             std::process::exit((v.capacity() * 40 + v.len() * 10) as i32 + (v[0] + v[1]) as i32); }",
            111,
        ),
        (
            "slice_fold_after_next_back_clears_b",
            "fn main() { let s = [std::hint::black_box(1u64), 2, 3]; \
             let t = [std::hint::black_box(4u64), 5]; let mut it = s.iter().chain(t.iter()); \
             for _ in 0..3 { it.next_back(); } \
             std::process::exit(it.fold(0u64, |a, x| a * 10 + *x) as i32); }",
            12,
        ),
        (
            "range_count_max_after_next_back_clears_b",
            "fn main() { let mut it = (std::hint::black_box(0u32)..3)\
             .chain(std::hint::black_box(10u32)..12); for _ in 0..3 { it.next_back(); } \
             let mut jt = (std::hint::black_box(0u32)..3).chain(std::hint::black_box(10u32)..12); \
             for _ in 0..3 { jt.next_back(); } \
             std::process::exit((it.count() * 10) as i32 + jt.max().unwrap_or(9) as i32); }",
            21,
        ),
        (
            "slice_sum_after_nth_clears_a",
            "fn main() { let s = [std::hint::black_box(1u64), 2, 3]; \
             let t = [std::hint::black_box(4u64), 5, 6, 7]; let mut it = s.iter().chain(t.iter()); \
             let x = it.nth(std::hint::black_box(4)).copied().unwrap_or(0); let r: u64 = it.sum(); \
             std::process::exit((x * 10 + r) as i32); }",
            63,
        ),
        (
            "range_position_any_after_next_clears_a",
            "fn main() { let mut it = (std::hint::black_box(0u32)..3)\
             .chain(std::hint::black_box(10u32)..14); for _ in 0..4 { it.next(); } \
             let p = it.position(|x| x == 13).unwrap_or(9) as i32; \
             let mut jt = (std::hint::black_box(0u32)..3).chain(std::hint::black_box(10u32)..14); \
             for _ in 0..4 { jt.next(); } let a = jt.any(|x| x < 10) as i32; \
             std::process::exit(p * 10 + a); }",
            20,
        ),
        (
            "uncleared_controls",
            "fn main() { let s = [std::hint::black_box(1u64), 2, 3]; \
             let t = [std::hint::black_box(4u64), 5]; let a: u64 = s.iter().chain(t.iter()).sum(); \
             let mut it = (std::hint::black_box(0u64)..3).chain(std::hint::black_box(10u64)..12); \
             it.next(); it.next(); let b: u64 = it.sum(); std::process::exit((a * 3 + b) as i32); }",
            68,
        ),
    ];
    let programs: Vec<Program> = rows
        .iter()
        .map(|(name, src, code)| program(name, (*src).to_owned(), Some(*code)))
        .collect();
    let outcomes = check(
        "chain_with_a_cleared_half_matches_llvm",
        &programs,
        must_match_outcome,
    );
    println!(
        "CHAIN_CLEARED_HALF rows={} cells={} matched={} opts=0,3",
        programs.len(),
        outcomes.len(),
        count(&outcomes, Outcome::Matched),
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The in-place `Vec` models (`resize_with`, `retain`, `retain_mut`,
/// `dedup_by`, and `dedup_by` inside std's `dedup_by_key`) run a closure that
/// captures a pair- or struct-returning closure; the iterator drives and the
/// `Vec`-self / `Vec`-destination std callees no model calls the closure of
/// (`pop_if`, `extract_if`, `Option`/`Result::map_or[_else]`), and model calls
/// whose arm refuses the payload or element (`&mut F`, `u128`,
/// `Option<u64>`), keep std's bodies for such callbacks; closures whose own
/// output is the pair still
/// take std's bodies. -O0..-O3 under both strategies: every cell matches
/// LLVM except std's `resize_with` over a `Vec<(u64, u64)>`, which is
/// refused by name (`extend_trusted` is not intercepted).
#[test]
fn captured_pair_closures_keep_the_vec_models_matching_llvm() {
    const TEST: &str = "captured_pair_closures_keep_the_vec_models_matching_llvm";
    const OPTS: [&str; 4] = ["0", "1", "2", "3"];
    const MK: &str = "let mk = |x: u64| (x, x * 9);";
    const ARR: &str = "let a = [std::hint::black_box(3u64), 14, 15, 92, 65];";
    // (id, body after `mk`, LLVM's exit code, refused by name at every level)
    let rows: [(&str, String, i32, bool); 29] = [
        (
            "resize_with_captured_pair",
            "let mut t: Vec<u64> = vec![1]; let mut k = 0u64; \
             t.resize_with(std::hint::black_box(5), || { k += 1; let (a, b) = mk(k); a + b }); \
             std::process::exit((t.iter().sum::<u64>() + t.len() as u64) as i32);"
                .to_owned(),
            106,
            false,
        ),
        (
            "resize_with_captured_struct",
            "struct P { a: u64, b: u64 } let mk = |x: u64| P { a: x, b: x * 9 }; \
             let mut t: Vec<u64> = vec![1]; let mut k = 0u64; \
             t.resize_with(std::hint::black_box(5), || { k += 1; let p = mk(k); p.a * 3 + p.b }); \
             std::process::exit((t.iter().sum::<u64>() + t.len() as u64) as i32);"
                .to_owned(),
            126,
            false,
        ),
        (
            "resize_with_nested_capture",
            "let f = |x: u64| { let (p, q) = mk(x); p * 2 + q }; let g = |x: u64| f(x) + 1; \
             let mut w: Vec<u64> = vec![std::hint::black_box(1u64)]; let mut k = 0u64; \
             w.resize_with(std::hint::black_box(4), || { k += 1; g(k) }); \
             std::process::exit((w.iter().sum::<u64>() % 251) as i32);"
                .to_owned(),
            70,
            false,
        ),
        (
            "retain_captured_pair",
            "let mk = |x: u64| (x % 3, x * 9); \
             let mut v: Vec<u64> = vec![std::hint::black_box(1u64), 2, 3, 4, 5, 6, 7, 8, 9, 10]; \
             v.retain(|&x| { let (a, b) = mk(x); a != 0 && b > 20 }); \
             std::process::exit((v.iter().sum::<u64>() + 10 * v.len() as u64) as i32);"
                .to_owned(),
            84,
            false,
        ),
        (
            "retain_mut_captured_pair",
            "let f = |x: u64| { let (p, q) = mk(x); p * 2 + q }; \
             let mut w = vec![std::hint::black_box(1u64), 2, 3, 4, 5]; \
             w.retain_mut(|x| { *x = f(*x) % 50; *x % 2 == 1 }); \
             std::process::exit(((w.iter().sum::<u64>() + w.len() as u64) % 251) as i32);"
                .to_owned(),
            52,
            false,
        ),
        (
            "dedup_by_captured_pair",
            "let mk = |x: u64| (x / 10, x % 10); \
             let mut v: Vec<u64> = vec![std::hint::black_box(11u64), 12, 25, 27, 31, 18, 19]; \
             v.dedup_by(|a, b| { let (p, _) = mk(*a); let (q, _) = mk(*b); p == q }); \
             std::process::exit((v.iter().sum::<u64>() + v.len() as u64) as i32);"
                .to_owned(),
            89,
            false,
        ),
        (
            "dedup_by_key_captured_pair",
            "let f = |x: u64| { let (p, q) = mk(x); p * 2 + q }; \
             let mut w = vec![std::hint::black_box(1u64), 1, 2, 2, 7]; \
             w.dedup_by_key(|x| f(*x) / 100); \
             std::process::exit(((w.iter().sum::<u64>() * 10 + w.len() as u64) % 251) as i32);"
                .to_owned(),
            11,
            false,
        ),
        // A model arm refuses these payloads (`&mut F`, `&F`) or elements
        // (`u128`, `Option<u64>`) by name, so the capture walk keeps std's
        // bodies, as at fb96d7a17.
        (
            "retain_by_mut_ref_captured_pair",
            "let mk = |x: u64| (x % 3, x * 9); \
             let mut pred = |x: &u64| { let (a, b) = mk(*x); a != 0 && b > 20 }; \
             let mut v: Vec<u64> = vec![std::hint::black_box(1u64), 2, 3, 4, 5, 6, 7, 8, 9, 10]; \
             v.retain(&mut pred); \
             std::process::exit((v.iter().sum::<u64>() + 10 * v.len() as u64) as i32);"
                .to_owned(),
            84,
            false,
        ),
        (
            "retain_mut_by_mut_ref_captured_pair",
            "let mk = |x: u64| (x % 3, x * 9); \
             let mut f = |x: &mut u64| { let (a, b) = mk(*x); *x = (a + b) % 50; *x % 2 == 1 }; \
             let mut w = vec![std::hint::black_box(1u64), 2, 3, 4, 5]; \
             w.retain_mut(&mut f); \
             std::process::exit(((w.iter().sum::<u64>() + w.len() as u64) % 251) as i32);"
                .to_owned(),
            114,
            false,
        ),
        (
            "dedup_by_by_mut_ref_captured_pair",
            "let mk = |x: u64| (x / 10, x % 10); \
             let mut same = |a: &mut u64, b: &mut u64| { let (p, _) = mk(*a); let (q, _) = mk(*b); p == q }; \
             let mut v: Vec<u64> = vec![std::hint::black_box(11u64), 12, 25, 27, 31, 18, 19]; \
             v.dedup_by(&mut same); \
             std::process::exit((v.iter().sum::<u64>() + v.len() as u64) as i32);"
                .to_owned(),
            89,
            false,
        ),
        (
            "retain_u128_captured_pair",
            "let mk = |x: u64| (x % 3, x * 9); \
             let mut v: Vec<u128> = Vec::new(); \
             for i in 0..std::hint::black_box(10u64) { v.push(i as u128 + (1u128 << 70)); } \
             v.retain(|&e| { let (a, b) = mk(e as u64); a != 0 && b > 20 }); \
             let mut s = 0u64; \
             for i in 0..v.len() { s += (v[i] as u64) + ((v[i] >> 70) as u64); } \
             std::process::exit(((s + 10 * v.len() as u64) % 251) as i32);"
                .to_owned(),
            68,
            false,
        ),
        (
            "retain_option_captured_pair",
            "let mk = |x: u64| (x % 3, x * 9); \
             let mut v: Vec<Option<u64>> = Vec::new(); \
             for i in 0..std::hint::black_box(10u64) { v.push(if i % 4 == 0 { None } else { Some(i) }); } \
             v.retain(|e| match *e { Some(x) => { let (a, b) = mk(x); a != 0 && b > 20 } None => true }); \
             let mut s = 0u64; \
             for i in 0..v.len() { s += match v[i] { Some(x) => x, None => 100 }; } \
             std::process::exit(((s + 10 * v.len() as u64) % 251) as i32);"
                .to_owned(),
            111,
            false,
        ),
        (
            "dedup_by_option_captured_pair",
            "let mk = |x: u64| (x / 10, x % 10); \
             let mut v: Vec<Option<u64>> = Vec::new(); \
             for x in [std::hint::black_box(11u64), 12, 25, 27, 31, 18, 19] { v.push(Some(x)); } \
             v.push(None); v.push(None); \
             v.dedup_by(|a, b| match (*a, *b) { \
                 (Some(p), Some(q)) => { let (p, _) = mk(p); let (q, _) = mk(q); p == q } \
                 (None, None) => true, _ => false }); \
             let mut s = 0u64; \
             for i in 0..v.len() { s += match v[i] { Some(x) => x, None => 100 }; } \
             std::process::exit(((s + 10 * v.len() as u64) % 251) as i32);"
                .to_owned(),
            235,
            false,
        ),
        // No model calls these callees' closures: std's bodies, as at fb96d7a17.
        (
            "pop_if_captured_pair",
            "let mut v: Vec<u64> = vec![std::hint::black_box(3u64), 14, 15]; \
             let r = v.pop_if(|x| { let (a, b) = mk(*x); a + b > 20 }); \
             std::process::exit((r.unwrap_or(7) + 10 * v.len() as u64 + v[0]) as i32);"
                .to_owned(),
            38,
            false,
        ),
        (
            "pop_if_captured_struct",
            "struct P { a: u64, b: u64 } let mk = |x: u64| P { a: x % 2, b: x * 9 }; \
             let mut v: Vec<u64> = vec![std::hint::black_box(3u64), 14, 16]; let mut n = 0u64; \
             while let Some(x) = v.pop_if(|x| { let p = mk(*x); p.a == 0 && p.b > 10 }) { n += x; } \
             std::process::exit((n + 10 * v.len() as u64) as i32);"
                .to_owned(),
            40,
            false,
        ),
        (
            // `extract_if` at -O0/-O1; the `ExtractIf` constructor it inlines to
            // at -O2/-O3.
            "extract_if_captured_pair",
            "let mk = |x: u64| (x % 3, x * 9); \
             let mut v: Vec<u64> = vec![std::hint::black_box(1u64), 2, 3, 4, 5, 6, 7, 8, 9, 10]; \
             let (mut n, mut s) = (0u64, 0u64); \
             for e in v.extract_if(.., |x| { let (a, b) = mk(*x); a == 0 && b > 20 }) { n += 1; s += e; } \
             std::process::exit(((n * 100 + s * 3 + v.len() as u64 + v.iter().sum::<u64>()) % 251) as i32);"
                .to_owned(),
            147,
            false,
        ),
        (
            "option_map_or_else_vec_captured_pair",
            "let o: Option<u64> = std::hint::black_box(Some(4)); \
             let v: Vec<u64> = o.map_or_else(|| Vec::new(), |x| { let (a, b) = mk(x); vec![a, b] }); \
             std::process::exit((v[0] + v[1] + 100 * v.len() as u64) as i32);"
                .to_owned(),
            240,
            false,
        ),
        (
            "option_map_or_vec_captured_pair",
            "let o: Option<u64> = std::hint::black_box(Some(3)); \
             let v: Vec<u64> = o.map_or(Vec::new(), |x| { let (a, b) = mk(x); vec![a, b] }); \
             std::process::exit((v[0] + v[1] + 100 * v.len() as u64) as i32);"
                .to_owned(),
            230,
            false,
        ),
        (
            "result_map_or_else_vec_captured_pair",
            "let o: Result<u64, u64> = std::hint::black_box(Ok(5)); \
             let v: Vec<u64> = o.map_or_else(|e| vec![e], |x| { let (a, b) = mk(x); vec![a, b] }); \
             std::process::exit((v[0] + v[1] + 100 * v.len() as u64) as i32);"
                .to_owned(),
            250,
            false,
        ),
        (
            "try_fold_captured_pair",
            format!(
                "{ARR} let r = a.iter()\
                 .try_fold(0u64, |s, &x| {{ let (p, q) = mk(x); s.checked_add(p + q) }}); \
                 std::process::exit((r.unwrap_or(7) % 251) as i32);"
            ),
            133,
            false,
        ),
        (
            "map_for_each_captured_pair",
            format!(
                "{ARR} let mut acc = 0u64; \
                 a.iter().map(|&x| {{ let (p, q) = mk(x); p * 2 + q }})\
                 .for_each(|y| acc = acc.wrapping_mul(7) + y); \
                 std::process::exit((acc % 251) as i32);"
            ),
            100,
            false,
        ),
        (
            "extend_captured_pair",
            format!(
                "{ARR} let mut t: Vec<u64> = Vec::new(); \
                 t.extend(a.iter().map(|&x| {{ let (p, q) = mk(x); p + q }})); \
                 std::process::exit(((t[0] + t[4]) % 251) as i32 + t.len() as i32);"
            ),
            183,
            false,
        ),
        (
            "rev_map_fold_captured_pair",
            format!(
                "{ARR} let r = a.iter().rev().map(|&x| {{ let (p, q) = mk(x); p + q }})\
                 .fold(0u64, |s, y| s.wrapping_mul(3).wrapping_add(y)); \
                 std::process::exit((r % 251) as i32);"
            ),
            225,
            false,
        ),
        (
            "map_enumerate_fold_captured_pair",
            "let a = [std::hint::black_box(3u64), 14, 15, 92, 65, 35]; \
             let f = |x: u64| { let (p, q) = mk(x); p * 2 + q }; \
             let r = a.iter().map(|&x| f(x)).enumerate().fold(0u64, |s, (i, y)| s + i as u64 * y); \
             std::process::exit((r % 251) as i32);"
                .to_owned(),
            22,
            false,
        ),
        (
            "own_pair_map_collect",
            format!(
                "{ARR} let v: Vec<(u64, u64)> = a.iter().map(|&x| mk(x)).collect(); \
                 std::process::exit(((v[1].0 + v[2].1) % 251) as i32 + v.len() as i32);"
            ),
            154,
            false,
        ),
        (
            "own_pair_map_fold",
            format!(
                "{ARR} let r = a.iter().map(|&x| mk(x))\
                 .fold(0u64, |s, (p, q)| s.wrapping_mul(3).wrapping_add(p * 2 + q)); \
                 std::process::exit((r % 251) as i32);"
            ),
            19,
            false,
        ),
        (
            "own_pair_extend",
            format!(
                "{ARR} let mut v: Vec<(u64, u64)> = Vec::new(); v.push((1, 2)); \
                 v.extend(a.iter().map(|&x| mk(x))); \
                 std::process::exit(((v[1].0 + v[5].1) % 251) as i32 + v.len() as i32);"
            ),
            92,
            false,
        ),
        (
            "own_pair_resize_with",
            "let mut t: Vec<(u64, u64)> = Vec::new(); t.push((1, 2)); let mut k = 0u64; \
             t.resize_with(std::hint::black_box(4), || { k += 1; mk(k) }); \
             std::process::exit((t[3].0 + t[3].1 + t[1].1) as i32 + t.len() as i32);"
                .to_owned(),
            43,
            true,
        ),
        (
            "captured_array_resize_with",
            "let mk = |x: u64| [x, x * 9]; let mut t: Vec<u64> = vec![1]; let mut k = 0u64; \
             t.resize_with(std::hint::black_box(5), || { k += 1; let [a, b] = mk(k); a + b }); \
             std::process::exit((t.iter().sum::<u64>() + t.len() as u64) as i32);"
                .to_owned(),
            106,
            false,
        ),
    ];
    let mut programs = Vec::new();
    let mut refused_ids = Vec::new();
    for (id, body, code, refused) in &rows {
        for (strategy, panic) in [("abort", Panic::Abort), ("unwind", Panic::Unwind)] {
            let id = format!("{id}_{strategy}");
            if *refused {
                refused_ids.push(id.clone());
            }
            programs.push(Program {
                id,
                src: format!("fn main() {{ {MK} {body} }}"),
                panic,
                overflow_checks_off: false,
                expected: Some(*code),
            });
        }
    }
    a64_differential::require_prerequisites(TEST);
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let dylib = backend_artifact_support::current_test_backend();
    let cells = a64_differential::run_cells(TEST, &dylib, &programs, &OPTS, Lane::ProofsOff, &knob);
    assert_eq!(cells.len(), programs.len() * OPTS.len(), "every cell ran");
    let mut problems = Vec::new();
    let (mut matched, mut refused) = (0usize, 0usize);
    for cell in &cells {
        let want_refusal = refused_ids.contains(&cell.id);
        match (&cell.verdict, want_refusal) {
            (Verdict::Matched, false) => matched += 1,
            // std's own `resize_with` reaches `extend_trusted`, which no model
            // intercepts: the ordinary-body route of an own-output pair.
            (Verdict::Refused { code, line }, true)
                if code == "TCG-MIR-UNSUPPORTED" && line.contains("resize_with") =>
            {
                refused += 1
            }
            (verdict, _) => problems.push(format!(
                "`{}` -Copt-level={}: {verdict:?}",
                cell.id, cell.opt
            )),
        }
        if let (Some(code), Some(run)) = (cell.expected, &cell.oracle) {
            if run.ending != a64_differential::Ending::Exited(code) {
                problems.push(format!(
                    "`{}`: LLVM ended {:?}, not exit {code}",
                    cell.id, run.ending
                ));
            }
        }
    }
    assert!(
        problems.is_empty(),
        "{TEST}: {} problem(s):\n{}",
        problems.len(),
        problems.join("\n")
    );
    println!(
        "CAPTURED_PAIR_CALLBACKS rows={} cells={} matched={matched} refused_by_name={refused} \
         opts=0,1,2,3 strategies=abort,unwind",
        rows.len(),
        cells.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
