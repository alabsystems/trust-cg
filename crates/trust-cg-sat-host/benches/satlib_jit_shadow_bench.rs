// trust-cg-sat-host/benches/satlib_jit_shadow_bench.rs - End-to-end
// wall-clock criterion bench for MicroSAT-with-JIT-shadow vs
// MicroSAT-native-only on the in-tree project-authored corpus. The legacy
// `satlib_` benchmark/group names are retained for report compatibility; no
// SATLIB or AIM instance bytes are distributed.
//
// Three bench groups:
//
//   * `satlib_native`           - SHADOW_MODE off, full solve via the
//                                 trampoline that routes through the
//                                 unmodified native propagate path.
//   * `satlib_jit_shadow`       - SHADOW_MODE on, full solve. The JIT'd
//                                 BCP kernel is snapshot-compiled on
//                                 first propagate and consulted once
//                                 against the original formula. Uses
//                                 the watched-literal kernel since the
//                                 default switchover.
//   * `satlib_jit_compile_only` - Times only the
//                                 `JitBcpWatchedLiteralKernelProvider::compile(...)`
//                                 call on the parsed clauses, with no
//                                 MicroSAT involvement.
//
// The first two groups invoke `sys::parse` + `sys::solve` on the
// corpus's `.cnf` paths directly (no tempfiles needed - the corpus
// files are already on disk inside the crate).
//
// SHADOW_MODE is a process-global `AtomicBool`. Criterion may run
// `bench_function` bodies on a single thread per group, but between
// groups MicroSAT's shared C state (DRAT recorder + the
// `trust_cg_propagate` trampoline) must be quiescent. We rely on the
// `SOLVER_LOCK` exposed via `propagate.rs` test machinery; since this
// is a `#[bench]` (not `#[test]`), we instead acquire a local lock to
// serialize the inner closure - criterion already runs bench bodies
// sequentially within a single process, so the local lock is
// defence-in-depth against a hypothetical future parallel runner.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::ffi::CString;
use std::hint::black_box;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::Ordering;

use criterion::{Criterion, criterion_group, criterion_main};

use trust_cg_jit_matrix::dimacs::read_dimacs_cnf_file;
use trust_cg_jit_matrix::jit_bcp_kernel::JitBcpWatchedLiteralKernelProvider;
use trust_cg_sat_host::propagate::{
    JIT_DIVERGENCE_COUNT, JIT_KERNEL_CHOICE, JIT_KERNEL_WATCHED_LITERAL, SHADOW_MODE,
    reset_jit_shadow_for_tests,
};
use trust_cg_sat_host::sys;

/// MicroSAT's C state is process-global. Hold this around every solve
/// to keep concurrent criterion measurement frames from clobbering
/// each other if a future criterion release parallelises bench bodies.
static SOLVER_LOCK: Mutex<()> = Mutex::new(());

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("sat_corpus")
}

/// Discover every `.cnf` fixture under `tests/fixtures/sat_corpus/` and
/// return `(label, path)` pairs sorted by filename so the bench order
/// is deterministic across runs.
fn corpus_fixtures() -> Vec<(String, PathBuf)> {
    let dir = corpus_dir();
    let mut entries: Vec<(String, PathBuf)> = std::fs::read_dir(&dir)
        .unwrap_or_else(|err| panic!("read corpus dir {}: {err}", dir.display()))
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) != Some("cnf") {
                return None;
            }
            let stem = path.file_stem()?.to_string_lossy().into_owned();
            Some((stem, path))
        })
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries
}

/// Drive `sys::parse` + `sys::solve` to completion on `cnf_path` and
/// return the raw MicroSAT result code. The solver is stack-allocated
/// so each call starts from a clean state.
fn solve_path(cnf_path: &Path) -> i32 {
    let c_path =
        CString::new(cnf_path.to_string_lossy().into_owned()).expect("cnf path has no NULs");
    let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
    // SAFETY: matches the upstream MicroSAT `main` pattern. `parse`
    // runs `initCDCL` and populates the solver before any read; `solve`
    // is only called when parse did not short-circuit to UNSAT.
    unsafe {
        let parse_rc = sys::parse(
            solver.as_mut_ptr(),
            c_path.as_ptr() as *mut std::os::raw::c_char,
        );
        if parse_rc == sys::UNSAT {
            return sys::UNSAT;
        }
        sys::solve(solver.as_mut_ptr())
    }
}

fn bench_native(c: &mut Criterion) {
    let mut group = c.benchmark_group("satlib_native");
    for (label, path) in corpus_fixtures() {
        // Pre-resolve any IO outside the timed inner loop. The path
        // itself is what `sys::parse` reads.
        group.bench_function(&label, |b| {
            b.iter(|| {
                let _guard = SOLVER_LOCK.lock().expect("solver lock poisoned");
                SHADOW_MODE.store(false, Ordering::SeqCst);
                black_box(solve_path(black_box(&path)));
            });
        });
    }
    group.finish();
}

fn bench_jit_shadow(c: &mut Criterion) {
    let mut group = c.benchmark_group("satlib_jit_shadow");
    // Pin the JIT kernel for this bench group. The default is already
    // `watched-literal` (the default kernel since the
    // switchover), but storing explicitly makes the choice obvious
    // when reading the bench source and protects against a value
    // left over from a different in-process bench.
    JIT_KERNEL_CHOICE.store(JIT_KERNEL_WATCHED_LITERAL, Ordering::SeqCst);
    for (label, path) in corpus_fixtures() {
        group.bench_function(&label, |b| {
            b.iter(|| {
                let _guard = SOLVER_LOCK.lock().expect("solver lock poisoned");
                // Reset the per-thread JIT cache so each measurement
                // re-incurs the snapshot-and-compile work the first
                // call inside `trust_cg_propagate` does. Without this
                // every iteration after the first would skip JIT
                // compilation, masking the real shadow cost.
                reset_jit_shadow_for_tests();
                SHADOW_MODE.store(true, Ordering::SeqCst);
                let rc = black_box(solve_path(black_box(&path)));
                SHADOW_MODE.store(false, Ordering::SeqCst);
                // Surface a hard failure if shadow divergence ever
                // ticks up: the entire claim depends on the JIT and
                // native agreeing.
                let div = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
                assert_eq!(
                    div, 0,
                    "JIT shadow divergence observed during bench (count = {div})"
                );
                black_box(rc);
            });
        });
    }
    group.finish();
}

fn bench_jit_compile_only(c: &mut Criterion) {
    let mut group = c.benchmark_group("satlib_jit_compile_only");
    for (label, path) in corpus_fixtures() {
        // Parse once outside the timed loop; we are measuring the JIT
        // compile, not the DIMACS reader.
        let cnf = read_dimacs_cnf_file(&path)
            .unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
        let num_vars = cnf.num_vars;
        let clauses = cnf.clauses;
        // Match the kernel exercised by `bench_jit_shadow` (the
        // watched-literal kernel since the headline switchover) so
        // the `compile_only` and `jit_shadow` numbers are directly
        // comparable.
        let trail_hint = num_vars;
        group.bench_function(&label, |b| {
            b.iter(|| {
                // Clone the clauses each iteration: `compile` consumes
                // `Vec<Vec<i32>>`. The clone cost is small relative to
                // codegen (codegen walks every clause and emits IR),
                // and including it keeps the timing apples-to-apples
                // with `compile`'s actual call signature.
                let provider = JitBcpWatchedLiteralKernelProvider::compile(
                    num_vars,
                    clauses.clone(),
                    trail_hint,
                )
                .expect("JIT compile");
                black_box(provider);
            });
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_native,
    bench_jit_shadow,
    bench_jit_compile_only
);
criterion_main!(benches);
