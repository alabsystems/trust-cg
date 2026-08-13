// trust-cg-sat-host/benches/microsat_c_o3_baseline_bench.rs - "Actually-relevant
// baseline" criterion bench: per-fixture per-propagate-call wall-clock for
//
//   1. MicroSAT's OWN propagate compiled with -O3 -march=native (the C
//      function we are wrapping; see `crates/trust-cg-sat-host/build.rs`
//      for the flag wiring). Reached via the `microsat_native_propagate`
//      symbol exported from the renamed C source.
//   2. The trust-cg JIT watched-literal fixed-capacity kernel
//      (`JitBcpWatchedLiteralKernelProvider`).
//   3. The trust-cg JIT watched-literal CHUNKED kernel
//      (`JitBcpWatchedLiteralChunkedKernelProvider`). Same propagate
//      algorithm as (2) but with a chunked watch-list layout that mirrors
//      MicroSAT's own S->DB watch-chain memory shape (linked chains of
//      DB offsets rather than fixed-capacity per-literal rows). Comparing
//      this column against MicroSAT-C-O3 isolates trust-cg's codegen
//      attribution from the data-layout advantage that the fixed-capacity
//      provider exploits.
//   4. The hand-written native Rust baseline (`BcpState::propagate`),
//      for cross-reference against the existing `bcp_watched_literal_throughput`
//      bench shape.
//
// All three baselines run on the SAME formula (parsed from the same `.cnf`
// fixture) and the SAME initial decision set (DECISION_COUNT positive
// decision literals on variables 1..=DECISION_COUNT). Per-iteration setup
// resets each baseline to its just-after-parse + decisions state so the
// timed call is exactly "one propagate-to-fixpoint" on a known starting
// state.
//
// ## Why this bench exists
//
// The existing `bcp_watched_literal_throughput` bench compares trust-cg JIT
// against the in-tree Rust BCP reference. A reviewer's fair-baseline pushback
// (filed as "Known limitation #4" in `benchmarks/benchmark_study.md`) is that the
// reference is idiomatic-Rust-with-`Vec<Vec<_>>` indirection, not a
// production-tuned C BCP loop at -O3 -march=native. MicroSAT's own
// `propagate` (the C function whose work we are replacing) IS that
// production-tuned baseline -- a flat int-array DB, integer arithmetic on
// raw pointers, no bounds checks, the inner loop the C compiler has had
// since 1999 to optimise. Comparing trust-cg JIT against THAT is the
// headline-honest comparison the verified-codegen claim hinges on.
//
// ## Bench design (style "(b) standalone")
//
// Two viable benchmark shapes are:
//
//   (a) Solver-driven: run a full `sys::parse + sys::solve` and instrument
//       the trampoline to time only the `propagate` body. Multiple
//       propagate calls per solve, average them.
//   (b) Standalone: drive `sys::parse` to set up the solver, push a known
//       decision set onto the trail, time a single direct call to
//       `microsat_native_propagate`. Cleanest comparison because the
//       inputs are pinned per iteration.
//
// We pick (b). MicroSAT's `parse` is reachable from Rust through
// `sys::parse`, and after parse the solver has DB populated and watch
// lists wired. Pushing decisions onto `falseStack` and bumping `assigned`
// is the same sequence MicroSAT's own `solve()` does between propagate
// calls. The timed measurement is then one call into the renamed
// `microsat_native_propagate(s)` function.
//
// ## The decision-injection contract
//
// For decision literal `d > 0`:
//   - MicroSAT: `S->false[-d] = 1; *S->assigned++ = -d; S->reason[d] = 0;`
//     (decision literals have reason 0, matching `solve()`'s convention).
//   - BcpState: `state.assign(d)` (sets `values[d] = True`, pushes onto trail).
//   - JIT WatchedLiteral: pass `(d << 1) | 1` in the input slice (the kernel
//     decodes `(var << 1) | polarity`; polarity=1 means positive).
//
// All three baselines receive the same decision literals in the same order.
//
// ## Parity check
//
// Before the timed loop we run a one-shot parity check that asserts:
//   - BcpState and JIT agree on conflict-vs-no-conflict (their "result"
//     fields are directly comparable: both implement pure propagate-to-
//     fixpoint without conflict analysis).
//   - MicroSAT's `microsat_native_propagate` returns SAT (=1) OR UNSAT (=0).
//     MicroSAT may disagree with the kernel-only baselines on a NON-root
//     conflict because its `propagate` swallows the conflict into
//     `analyze()` and returns SAT after learning a lemma; this is by-design
//     MicroSAT behaviour and not a JIT vs C-baseline correctness signal.
//     For the actually-relevant single-call timing comparison this is OK
//     because all three are still doing real propagation work on the same
//     starting state; only the post-conflict bookkeeping differs.
//
// If BcpState and JIT disagree, the parity check panics before any
// timings are produced. That's the strongest correctness gate we can
// install at the kernel-equivalence layer; it is the same parity check
// `crates/trust-cg-jit-matrix/benches/jit_vs_native_bcp_bench.rs` uses.
//
// ## Per-iteration teardown
//
// MicroSAT's `initCDCL` malloc's `S->DB`. We free it after each iteration
// of the MicroSAT bench. The BcpState and JIT providers free their own
// resources via Rust's drop machinery (BcpState on scope exit, JIT
// provider on bench-group exit since it's reused across iterations).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::ffi::CString;
use std::hint::black_box;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::Ordering;

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};

use trust_cg_jit_matrix::bcp_baseline::BcpState;
use trust_cg_jit_matrix::bcp_kernel::BcpKernelProvider;
use trust_cg_jit_matrix::dimacs::read_dimacs_cnf_file;
use trust_cg_jit_matrix::jit_bcp_kernel::{
    JitBcpWatchedLiteralChunkedKernelProvider, JitBcpWatchedLiteralKernelProvider,
};
use trust_cg_jit_matrix::solver_kernel_abi::SolverKernelHandle;
use trust_cg_sat_host::propagate::{
    JIT_KERNEL_CHOICE, JIT_KERNEL_WATCHED_LITERAL, PRIMARY_JIT_MODE, SHADOW_MODE,
};
use trust_cg_sat_host::sys;

/// MicroSAT's C state is process-global (the renamed
/// `microsat_native_propagate` reads / writes through `S->DB`, watch lists,
/// and the trail). Hold this for every bench iteration so a parallel
/// criterion frame can't clobber another's solver state.
static SOLVER_LOCK: Mutex<()> = Mutex::new(());

/// A five-fixture spread across generated random and pigeonhole families:
///
///   * `uuf50-01` / `uuf75-01` / `uuf100-04` — project-authored random-3SAT
///     UNSAT instances at three sizes, no parse-time unit clauses, so the
///     timed call's propagate workload is *entirely* driven by the
///     injected decisions. Spreads difficulty from ~218 clauses to ~430
///     clauses.
///   * `php-7-6` / `php-10-9` — pigeonhole instances; structured
///     formulas the propagate loop chews on very differently from random
///     3SAT (lots of long clauses, dense propagation cascades).
const FIXTURES: &[&str] = &["uuf50-01", "uuf75-01", "uuf100-04", "php-7-6", "php-10-9"];

/// Number of positive decision literals we push onto the trail before the
/// timed propagate call. Chosen to match the existing
/// `bcp_watched_literal_throughput` bench's `DECISION_COUNT` so the new
/// numbers cross-reference cleanly against the in-tree headline.
const DECISION_COUNT: usize = 8;

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("sat_corpus")
}

fn fixture_path(name: &str) -> PathBuf {
    corpus_dir().join(format!("{name}.cnf"))
}

/// Pick `count` decision literals deterministically from `num_vars`.
/// Vars `1..=count` (positive polarity). The implicit assumption is that
/// `count <= num_vars`; we cap if a fixture has fewer variables (which
/// none of our chosen five do, but defensive nonetheless).
fn pick_decisions(num_vars: usize, count: usize) -> Vec<i32> {
    let take = count.min(num_vars);
    (1..=take as i32).collect()
}

/// Translate a decision slice into the `(var << 1) | polarity` encoding
/// the JIT kernel's `input: &[u32]` arg expects. Per
/// `crates/trust-cg-jit-matrix/src/bcp_kernel.rs`, `polarity == 0`
/// selects `+var` (truth value `1`) and `polarity == 1` selects `-var`,
/// so a positive DIMACS literal maps to `(var << 1) | 0`.
fn decisions_as_jit_input(decisions: &[i32]) -> Vec<u32> {
    decisions
        .iter()
        .map(|&lit| {
            let v = lit.unsigned_abs();
            let pol = if lit > 0 { 0 } else { 1 };
            (v << 1) | pol
        })
        .collect()
}

/// Stack-allocated MicroSAT solver wrapper that frees `S->DB` on drop.
/// `parse()` malloc's the DB; we own the rest of the struct on the stack.
struct OwnedMicroSatSolver {
    inner: MaybeUninit<sys::solver>,
    initialised: bool,
}

impl OwnedMicroSatSolver {
    /// Parse a CNF fixture into a fresh solver. Returns `(solver, parse_rc)`
    /// where `parse_rc` is `sys::UNSAT` if the parser observed a root-level
    /// contradiction, or `sys::SAT` otherwise.
    fn parse_from(cnf_path: &Path) -> (Self, i32) {
        let c_path = CString::new(cnf_path.to_string_lossy().into_owned())
            .expect("cnf path has no NUL bytes");
        let mut inner: MaybeUninit<sys::solver> = MaybeUninit::uninit();
        // SAFETY: matches the upstream MicroSAT `main` pattern --
        // `parse()` runs `initCDCL` and populates every field of `*S`
        // it later reads before returning. Passing uninitialised memory
        // is the documented usage.
        let parse_rc = unsafe {
            sys::parse(
                inner.as_mut_ptr(),
                c_path.as_ptr() as *mut std::os::raw::c_char,
            )
        };
        let initialised = true; // parse() always reaches initCDCL, even on parse-rc UNSAT
        (Self { inner, initialised }, parse_rc)
    }

    /// Pointer into the just-parsed solver. Caller must not retain the
    /// pointer past this owner's drop.
    fn as_mut_ptr(&mut self) -> *mut sys::solver {
        self.inner.as_mut_ptr()
    }

    /// Push `decisions` onto the falseStack as decision literals (reason
    /// = 0). Mirrors MicroSAT `solve()`'s decision-pushing sequence:
    ///
    /// ```text
    /// S->false[-decision] = 1;
    /// *(S->assigned++) = -decision;
    /// S->reason[decision] = 0;
    /// ```
    fn push_decisions(&mut self, decisions: &[i32]) {
        let s_ptr = self.inner.as_mut_ptr();
        for &lit in decisions {
            // SAFETY: `s_ptr` was initialised by `parse`, and the
            // `false`/`reason`/`assigned` fields point into the
            // initialised arena allocated by `initCDCL`. Decision
            // literals stay within [-nVars, nVars] which is the
            // arena's valid range.
            unsafe {
                // SAFETY rationale: `S->false_` is offset by +nVars at
                // construction so indices in [-nVars, nVars] are valid.
                let s = &mut *s_ptr;
                *s.false_.offset(-lit as isize) = 1;
                *s.assigned = -lit;
                s.assigned = s.assigned.add(1);
                *s.reason.offset(lit.unsigned_abs() as isize) = 0;
            }
        }
    }
}

impl Drop for OwnedMicroSatSolver {
    fn drop(&mut self) {
        if !self.initialised {
            return;
        }
        // SAFETY: `parse` ran `initCDCL`, which malloc'd `S->DB`. We
        // own the struct here (it's about to go out of scope), so
        // freeing the DB is the standalone analog of dropping the
        // stack-allocated `S` at the end of MicroSAT's `main()`.
        unsafe {
            let s_ptr = self.inner.as_mut_ptr();
            let db = (*s_ptr).DB;
            if !db.is_null() {
                libc::free(db as *mut libc::c_void);
            }
        }
    }
}

unsafe extern "C" {
    /// The renamed MicroSAT C function the build script produces. See
    /// `crates/trust-cg-sat-host/build.rs` for the text-rewrite pipeline
    /// and `crates/trust-cg-sat-host/src/propagate.rs` for the existing
    /// extern declaration this bench mirrors. We declare it locally so
    /// the bench source is self-contained.
    fn microsat_native_propagate(s: *mut sys::solver) -> std::ffi::c_int;
}

/// Run all four baselines once on the same (clauses, decisions) pair
/// and assert kernel-equivalence between BcpState, the fixed-capacity
/// JIT provider, and the chunked JIT provider. MicroSAT is allowed to
/// disagree on the `result` field because its `propagate` invokes
/// `analyze()` on non-root conflicts and returns SAT after learning;
/// the kernel-only baselines just report "conflict".
fn parity_check(
    fixture: &str,
    num_vars: usize,
    clauses: &[Vec<i32>],
    decisions: &[i32],
) -> (u32, u32, u32, i32) {
    // BcpState
    let mut state = BcpState::new(num_vars, clauses.to_vec());
    for &d in decisions {
        state.assign(d);
    }
    let bcp_result: u32 = if state.propagate().is_some() { 1 } else { 0 };

    // JIT WatchedLiteral (fixed-capacity)
    let jit = JitBcpWatchedLiteralKernelProvider::compile(
        num_vars,
        clauses.to_vec(),
        decisions.len().max(1),
    )
    .unwrap_or_else(|e| panic!("JIT compile failed for `{fixture}`: {e:?}"));
    jit.reset_arena();
    let input = decisions_as_jit_input(decisions);
    let mut handle = SolverKernelHandle::from_provider(&jit);
    let jit_result = handle.call(&input).result;

    // JIT WatchedLiteral (chunked). Same algorithm, MicroSAT-shaped memory.
    let jit_chunked = JitBcpWatchedLiteralChunkedKernelProvider::compile(
        num_vars,
        clauses.to_vec(),
        decisions.len().max(1),
    )
    .unwrap_or_else(|e| panic!("JIT chunked compile failed for `{fixture}`: {e:?}"));
    jit_chunked.reset_arena();
    let mut chunked_handle = SolverKernelHandle::from_provider(&jit_chunked);
    let jit_chunked_result = chunked_handle.call(&input).result;

    // MicroSAT C: separate solver per parity probe so this run's state
    // mutation doesn't bleed into the timed bench.
    let cnf_path = fixture_path(fixture);
    let (mut owner, parse_rc) = OwnedMicroSatSolver::parse_from(&cnf_path);
    let microsat_rc = if parse_rc == sys::UNSAT {
        sys::UNSAT
    } else {
        owner.push_decisions(decisions);
        // SAFETY: post-parse solver is fully initialised.
        unsafe { microsat_native_propagate(owner.as_mut_ptr()) }
    };

    assert_eq!(
        bcp_result, jit_result,
        "fixture `{fixture}`: BcpState and JIT WatchedLiteral disagree on \
         propagate-to-fixpoint result with {DECISION_COUNT} decisions: \
         bcp_result={bcp_result} jit_result={jit_result}. This is a \
         real correctness gate; STOP and investigate."
    );
    assert_eq!(
        bcp_result, jit_chunked_result,
        "fixture `{fixture}`: BcpState and JIT WatchedLiteral CHUNKED disagree \
         on propagate-to-fixpoint result with {DECISION_COUNT} decisions: \
         bcp_result={bcp_result} jit_chunked_result={jit_chunked_result}. \
         This is a real correctness gate; STOP and investigate."
    );

    (bcp_result, jit_result, jit_chunked_result, microsat_rc)
}

fn bench_microsat_c_o3(c: &mut Criterion) {
    // Make sure we drive the renamed `microsat_native_propagate` directly
    // and bypass the trust_cg_propagate trampoline. Belt-and-suspenders:
    // the bench calls `microsat_native_propagate` straight through, so
    // these flags don't actually gate this code path, but a future
    // refactor that re-routes the bench through the trampoline must NOT
    // accidentally enable the JIT shadow under us.
    SHADOW_MODE.store(false, Ordering::SeqCst);
    PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
    JIT_KERNEL_CHOICE.store(JIT_KERNEL_WATCHED_LITERAL, Ordering::SeqCst);

    let mut group = c.benchmark_group("microsat_c_o3_propagate");
    for fixture in FIXTURES {
        let cnf_path = fixture_path(fixture);
        if !cnf_path.exists() {
            eprintln!(
                "fixture `{fixture}` missing at {}; skipping",
                cnf_path.display()
            );
            continue;
        }
        let cnf = read_dimacs_cnf_file(&cnf_path)
            .unwrap_or_else(|e| panic!("read DIMACS for `{fixture}`: {e:?}"));
        let decisions = pick_decisions(cnf.num_vars, DECISION_COUNT);

        // One-shot parity check + diagnostic stderr line. Runs OUTSIDE
        // the timed loop so any disagreement panics before criterion
        // collects a single sample.
        let (bcp_r, jit_r, jit_chunked_r, microsat_r) =
            parity_check(fixture, cnf.num_vars, &cnf.clauses, &decisions);
        eprintln!(
            "fixture `{fixture}` parity: bcp={bcp_r} jit_fixed={jit_r} \
             jit_chunked={jit_chunked_r} microsat={microsat_r}"
        );

        let cnf_path_inner = cnf_path.clone();
        let decisions_inner = decisions.clone();
        group.bench_function(*fixture, |b| {
            // SAFETY of the timed body: every iteration parses fresh,
            // so per-iteration mutations to S->DB / watch lists / trail
            // do not bleed into the next iteration. The Drop impl frees
            // the DB.
            b.iter_batched(
                || {
                    let _lock = SOLVER_LOCK.lock().expect("solver lock poisoned");
                    let (mut owner, parse_rc) = OwnedMicroSatSolver::parse_from(&cnf_path_inner);
                    if parse_rc != sys::UNSAT {
                        owner.push_decisions(&decisions_inner);
                    }
                    (owner, parse_rc)
                },
                |(mut owner, parse_rc)| {
                    if parse_rc == sys::UNSAT {
                        // Parse already detected a root-level conflict;
                        // propagate would do no work. Black-box the
                        // parse_rc so the compiler can't constant-fold
                        // the whole iteration body.
                        black_box(parse_rc);
                    } else {
                        // SAFETY: post-parse solver is fully initialised
                        // and `microsat_native_propagate` is the renamed
                        // upstream `propagate(struct solver*)` function.
                        let rc = unsafe { microsat_native_propagate(owner.as_mut_ptr()) };
                        black_box(rc);
                    }
                    // owner drops here; DB is freed.
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

fn bench_rust_baseline(c: &mut Criterion) {
    let mut group = c.benchmark_group("rust_baseline_propagate");
    for fixture in FIXTURES {
        let cnf_path = fixture_path(fixture);
        if !cnf_path.exists() {
            continue;
        }
        let cnf = read_dimacs_cnf_file(&cnf_path)
            .unwrap_or_else(|e| panic!("read DIMACS for `{fixture}`: {e:?}"));
        let num_vars = cnf.num_vars;
        let clauses = cnf.clauses.clone();
        let decisions = pick_decisions(num_vars, DECISION_COUNT);

        group.bench_function(*fixture, |b| {
            b.iter_batched(
                || {
                    let mut state = BcpState::new(num_vars, clauses.clone());
                    for &d in &decisions {
                        state.assign(d);
                    }
                    Box::new(state)
                },
                |mut state| {
                    // BcpKernelProvider is the same path
                    // `bcp_watched_literal_throughput` measures; using
                    // it directly keeps the numbers cross-comparable.
                    let provider = BcpKernelProvider::new(&mut state);
                    let mut handle = SolverKernelHandle::from_provider(&provider);
                    black_box(handle.call(black_box(&[])));
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

fn bench_trust_cg_jit(c: &mut Criterion) {
    let mut group = c.benchmark_group("trust_cg_jit_propagate");
    for fixture in FIXTURES {
        let cnf_path = fixture_path(fixture);
        if !cnf_path.exists() {
            continue;
        }
        let cnf = read_dimacs_cnf_file(&cnf_path)
            .unwrap_or_else(|e| panic!("read DIMACS for `{fixture}`: {e:?}"));
        let decisions = pick_decisions(cnf.num_vars, DECISION_COUNT);
        let input = decisions_as_jit_input(&decisions);

        // Compile once outside the timed loop. The headline claim is
        // "JIT BCP per-call propagate cost"; including compile cost
        // every iteration is what `satlib_jit_compile_only` measures
        // and is documented as the 1.3-1.8 ms cost in benchmark_study.md.
        let provider = JitBcpWatchedLiteralKernelProvider::compile(
            cnf.num_vars,
            cnf.clauses.clone(),
            decisions.len().max(1),
        )
        .unwrap_or_else(|e| panic!("JIT compile for `{fixture}`: {e:?}"));

        group.bench_function(*fixture, |b| {
            b.iter(|| {
                provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&provider);
                black_box(handle.call(black_box(&input)));
            });
        });
    }
    group.finish();
}

fn bench_trust_cg_jit_chunked(c: &mut Criterion) {
    // Mirror of `bench_trust_cg_jit` but using the CHUNKED watched-literal
    // provider. The chunked layout mirrors MicroSAT's S->DB watch-chain
    // memory shape (linked chains of DB offsets rather than fixed-capacity
    // per-literal rows), so any per-call speedup vs MicroSAT-C-O3 in this
    // column is attributable to trust-cg's codegen quality rather than to
    // the flat-arena vs Vec<Vec<_>> data-layout advantage that the
    // fixed-capacity provider exploits.
    let mut group = c.benchmark_group("trust_cg_jit_chunked_propagate");
    for fixture in FIXTURES {
        let cnf_path = fixture_path(fixture);
        if !cnf_path.exists() {
            continue;
        }
        let cnf = read_dimacs_cnf_file(&cnf_path)
            .unwrap_or_else(|e| panic!("read DIMACS for `{fixture}`: {e:?}"));
        let decisions = pick_decisions(cnf.num_vars, DECISION_COUNT);
        let input = decisions_as_jit_input(&decisions);

        // Compile once outside the timed loop. The chunked provider's
        // `compile` builds the same KernelEntry the fixed-cap provider
        // does, with a chunked arena instead of the fixed-cap arena.
        let provider = JitBcpWatchedLiteralChunkedKernelProvider::compile(
            cnf.num_vars,
            cnf.clauses.clone(),
            decisions.len().max(1),
        )
        .unwrap_or_else(|e| panic!("JIT chunked compile for `{fixture}`: {e:?}"));

        group.bench_function(*fixture, |b| {
            b.iter(|| {
                provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&provider);
                black_box(handle.call(black_box(&input)));
            });
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_microsat_c_o3,
    bench_rust_baseline,
    bench_trust_cg_jit,
    bench_trust_cg_jit_chunked,
);
criterion_main!(benches);
