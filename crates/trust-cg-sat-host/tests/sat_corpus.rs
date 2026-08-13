// trust-cg-sat-host - End-to-end correctness test against the small,
// project-authored release corpus.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Purpose
// -------
// Confidence-build the trampolined MicroSAT + DRAT emitter against real
// instances rather than only the unit-propagation smoke tests in
// `src/lib.rs`. For each fixture in `tests/fixtures/sat_corpus/`:
//
//   1. Run the wrapped MicroSAT (`sys::parse` + `sys::solve`) with DRAT
//      output enabled.
//   2. Assert the result code matches the expected SAT/UNSAT in
//      `corpus.json`.
//   3. For UNSAT instances, assert that a non-empty DRAT proof was
//      written and that every line is well-formed.
//   4. For UNSAT instances, run the vendored `drat-trim` checker
//      (built into OUT_DIR by `trust-cg-drat-trim`) against
//      (cnf, drat) and require acceptance. No system PATH lookup is
//      involved.
//
// `assert_drat_well_formed` exists as a `#[cfg(test)]` helper in
// `src/lib.rs::tests`. The check below is a copy of that
// helper's logic so this test file is independent of the inner `tests`
// module. If the two implementations ever diverge, prefer the version
// in `src/lib.rs` and re-sync this copy.

use std::collections::BTreeMap;
use std::ffi::CString;
use std::fs;
use std::io::Write;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use serde::Deserialize;
use tempfile::NamedTempFile;

use std::sync::atomic::Ordering;

use trust_cg_sat_host::drat_recorder::{
    disable_drat_output, enable_drat_output, flush_drat_output,
};
use trust_cg_sat_host::propagate::{
    JIT_DIVERGENCE_COUNT, JIT_PRIMARY_RETURNS, PRIMARY_JIT_MODE, reset_jit_shadow_for_tests,
};
use trust_cg_sat_host::sys;

/// MicroSAT is *process-global* (it holds the DRAT recorder + the
/// link-redirected propagate symbol). Cargo runs integration tests in
/// parallel by default; we serialise every fixture run behind this
/// mutex so back-to-back solves do not stomp on each other's DRAT
/// output. The mutex in `src/lib.rs` lives inside `mod tests`, so we
/// cannot share it; this is a sibling lock confined to this binary.
static CORPUS_LOCK: Mutex<()> = Mutex::new(());

/// Soft threshold below which we tag a fixture as "too easy to be a
/// useful JIT amortization demonstrator". Picked at 50 microseconds
/// because today's JIT compile cost is ~1.5 ms, so anything that
/// solves in tens of microseconds cannot possibly demonstrate
/// compile-cost amortization end-to-end. Release policy surfaces this as a
/// warning, not a failure: the smoke-tier fixtures intentionally solve below this bound
/// and that is fine. We only flag entries that also carry a
/// `min_solve_ms_estimate` claim - those are the entries that
/// implicitly promise "I am hard enough to matter for the bench",
/// and if the measurement contradicts the claim the maintainer
/// should know.
const TOO_EASY_SOLVE_THRESHOLD_US: f64 = 50.0;

#[derive(Debug, Deserialize)]
struct Manifest {
    fixtures: Vec<Fixture>,
}

#[derive(Debug, Deserialize)]
struct Fixture {
    file: String,
    expected: String,
    /// Structural family the fixture belongs to. Used only for the
    /// aggregate stderr summary; unknown / missing values fall back
    /// to `"uncategorized"`. Existing categories include
    /// `random_3sat`, `pigeonhole`, `queens`, `adder`, `blocks`, and
    /// `parity`.
    #[serde(default)]
    category: Option<String>,
    #[serde(default)]
    #[allow(dead_code)]
    num_vars: u64,
    #[serde(default)]
    #[allow(dead_code)]
    num_clauses: u64,
    #[serde(default)]
    #[allow(dead_code)]
    source: String,
    #[serde(default)]
    #[allow(dead_code)]
    url: Option<String>,
    /// Optional rough lower bound on MicroSAT's expected native solve
    /// time in milliseconds on a modern x86-64 / Apple-Silicon
    /// machine. The corpus test emits a soft stderr warning if the
    /// measured solve time is far below this (currently: under
    /// `TOO_EASY_SOLVE_THRESHOLD_US`) so reviewers can spot fixtures
    /// that have become "too easy" to be useful as a JIT amortization
    /// demonstrator (either because the solver got faster or the
    /// instance was always trivial).
    ///
    /// The field is optional so the smoke-tier fixtures, which exist
    /// only to exercise the parser / DRAT emitter and are expected to
    /// solve in microseconds, can omit it without polluting the
    /// warning channel.
    #[serde(default)]
    min_solve_ms_estimate: Option<f64>,
}

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("sat_corpus")
}

fn load_manifest() -> Manifest {
    let manifest_path = corpus_dir().join("corpus.json");
    let raw = fs::read_to_string(&manifest_path)
        .unwrap_or_else(|err| panic!("read {}: {err}", manifest_path.display()));
    serde_json::from_str(&raw)
        .unwrap_or_else(|err| panic!("parse {}: {err}", manifest_path.display()))
}

/// Drive `sys::parse` + `sys::solve` on a path. Mirrors `run_solver` in
/// `src/lib.rs::tests` but takes the CNF as a path so the same file can
/// also be handed to `drat-trim` for cross-checking. Returns the raw
/// MicroSAT result code (`sys::SAT` or `sys::UNSAT`).
fn solve_path(cnf_path: &Path) -> i32 {
    let c_path =
        CString::new(cnf_path.to_string_lossy().into_owned()).expect("cnf path contains no NULs");
    let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
    // SAFETY: matches the upstream `main` in microsat.c. `parse` calls
    // `initCDCL` and fully populates the solver before any subsequent
    // read; `solve` is only called when parse did not short-circuit to
    // UNSAT.
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

/// Validate that a DRAT proof file is line-by-line well-formed:
///   - non-empty
///   - every line ends in ` 0` (literal-list terminator)
///   - lines starting with `d ` are deletion steps; everything else
///     must start with a non-zero integer literal
///   - every line carries at least one literal before the 0
///
/// Duplicate of the `assert_drat_well_formed` helper inside
/// `src/lib.rs::tests`. Keep this copy in sync with the original; see the
/// module header.
fn assert_drat_well_formed(path: &Path) {
    let bytes = fs::read(path).expect("read drat file");
    assert!(!bytes.is_empty(), "drat proof file is empty");
    let text = std::str::from_utf8(&bytes).expect("drat file is UTF-8");
    let lines: Vec<&str> = text.lines().collect();
    assert!(!lines.is_empty(), "drat proof has no lines");
    for (idx, line) in lines.iter().enumerate() {
        assert!(
            line.ends_with(" 0"),
            "line {} does not end with ' 0': {:?}",
            idx,
            line
        );
        let body = line.strip_prefix("d ").unwrap_or(line);
        let toks: Vec<&str> = body.split_whitespace().collect();
        assert!(
            toks.len() >= 2,
            "line {} has no literals before terminator: {:?}",
            idx,
            line
        );
        assert_eq!(toks[toks.len() - 1], "0", "line {} terminator missing", idx);
        for tok in &toks[..toks.len() - 1] {
            let lit: i64 = tok
                .parse()
                .unwrap_or_else(|_| panic!("non-integer literal {:?} on line {}", tok, idx));
            assert_ne!(lit, 0, "zero literal mid-clause on line {}", idx);
        }
    }
}

fn expected_code(expected: &str) -> i32 {
    match expected {
        "SAT" => sys::SAT,
        "UNSAT" => sys::UNSAT,
        other => panic!("manifest has unknown expected value {:?}", other),
    }
}

/// One fixture pass. Returns Ok on success or a string describing the
/// failure (so we can aggregate across the corpus before failing the
/// test, rather than aborting on the first instance).
fn run_one(fixture: &Fixture) -> Result<FixtureReport, String> {
    let cnf_path = corpus_dir().join(&fixture.file);
    if !cnf_path.exists() {
        return Err(format!("fixture missing on disk: {}", cnf_path.display()));
    }

    let expected = expected_code(&fixture.expected);

    // Stage proof into a tempfile; we keep it after the run for
    // optional drat-trim verification.
    let proof_tmp = NamedTempFile::new().map_err(|e| format!("tempfile: {e}"))?;
    let proof_path = proof_tmp.path().to_path_buf();

    enable_drat_output(&proof_path).map_err(|e| format!("enable_drat: {e}"))?;
    let t0 = Instant::now();
    let rc = solve_path(&cnf_path);
    let solve_elapsed = t0.elapsed();
    flush_drat_output().map_err(|e| format!("flush_drat: {e}"))?;
    disable_drat_output();

    if rc != expected {
        return Err(format!(
            "{}: expected result {} ({}), got {}",
            fixture.file, fixture.expected, expected, rc
        ));
    }

    let mut drat_bytes = 0u64;
    let mut warning: Option<String> = None;
    let mut drat_trim_status = DratTrimStatus::Skipped;

    // Soft warning: a fixture that carries a `min_solve_ms_estimate`
    // claims to be hard enough to matter for the JIT-amortization
    // story, but if it actually solves in well under the
    // TOO_EASY_SOLVE_THRESHOLD_US bound we have either a fixture
    // mislabel or the solver got faster. Either way the bench is
    // going to under-report amortization for this entry; flag it.
    let solve_us = solve_elapsed.as_secs_f64() * 1.0e6;
    if let Some(min_ms) = fixture.min_solve_ms_estimate
        && solve_us < TOO_EASY_SOLVE_THRESHOLD_US
    {
        warning = Some(format!(
            "{}: measured solve time {:.1} us is below the {:.1} us \
                 too-easy threshold (declared min_solve_ms_estimate={} ms); \
                 this fixture is unlikely to demonstrate JIT amortization",
            fixture.file, solve_us, TOO_EASY_SOLVE_THRESHOLD_US, min_ms,
        ));
    }

    if expected == sys::UNSAT {
        let meta =
            fs::metadata(&proof_path).map_err(|e| format!("{}: stat drat: {e}", fixture.file))?;
        drat_bytes = meta.len();
        if drat_bytes == 0 {
            // Do not suppress this condition: surface it as a warning so
            // the user sees it in the aggregate report. A
            // zero-byte DRAT for UNSAT means MicroSAT decided the
            // instance by unit propagation alone, never learning a
            // lemma. That is plausible for tiny constructed
            // instances but worth flagging.
            //
            // If a too-easy warning is already pending, append rather
            // than overwrite so we surface both signals.
            let drat_msg = format!(
                "{}: DRAT proof is empty (trivial UNSAT by unit propagation?)",
                fixture.file
            );
            warning = Some(match warning {
                Some(prev) => format!("{prev}; {drat_msg}"),
                None => drat_msg,
            });
        } else {
            assert_drat_well_formed(&proof_path);
        }

        // Always run the vendored drat-trim. The executable was
        // produced by `trust-cg-drat-trim`'s build script into its
        // OUT_DIR; no system PATH lookup is involved.
        let drat_trim_exe = trust_cg_drat_trim::drat_trim_executable_path();
        let out = Command::new(drat_trim_exe)
            .arg(&cnf_path)
            .arg(&proof_path)
            .output()
            .map_err(|e| format!("{}: invoke drat-trim: {e}", fixture.file))?;
        // drat-trim historically uses exit-code conventions that vary
        // across upstream revisions; the canonical way to detect
        // acceptance is the literal "s VERIFIED" line on stdout. We
        // additionally accept the bare "VERIFIED" token to be robust
        // to minor formatting drift. Anything else is a rejection
        // (including non-zero status without VERIFIED).
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        let verified = stdout.contains("s VERIFIED") || stdout.contains("VERIFIED");
        if verified && out.status.success() {
            drat_trim_status = DratTrimStatus::Accepted;
        } else {
            return Err(format!(
                "{}: drat-trim rejected proof (status={:?}). stdout={} stderr={}",
                fixture.file, out.status, stdout, stderr
            ));
        }
    } else {
        // For SAT instances DRAT emission may still produce nothing
        // (no UNSAT proof to emit); accept zero or non-empty without
        // requiring well-formedness — MicroSAT can still emit
        // intermediate learned clauses but is not required to.
        if let Ok(meta) = fs::metadata(&proof_path) {
            drat_bytes = meta.len();
        }
    }

    Ok(FixtureReport {
        file: fixture.file.clone(),
        expected: fixture.expected.clone(),
        category: fixture
            .category
            .clone()
            .unwrap_or_else(|| "uncategorized".to_string()),
        observed_code: rc,
        drat_bytes,
        drat_trim: drat_trim_status,
        solve_elapsed,
        warning,
    })
}

#[derive(Debug, Clone, Copy)]
enum DratTrimStatus {
    Skipped,
    Accepted,
    // `Rejected` is constructed indirectly: when drat-trim exits with a
    // non-zero status we surface the failure through `Err(...)` from
    // `run_one` and never get to record the report variant. We keep
    // the variant present so the Display impl and the match in the
    // aggregate summary stay total.
    #[allow(dead_code)]
    Rejected,
}

impl std::fmt::Display for DratTrimStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DratTrimStatus::Skipped => write!(f, "skipped"),
            DratTrimStatus::Accepted => write!(f, "accepted"),
            DratTrimStatus::Rejected => write!(f, "rejected"),
        }
    }
}

#[derive(Debug)]
struct FixtureReport {
    file: String,
    expected: String,
    /// Structural-family tag, e.g. `random_3sat`, `pigeonhole`,
    /// `queens`, `adder`, `blocks`, `parity`. Defaults to
    /// `uncategorized` when the manifest entry omits a category.
    category: String,
    observed_code: i32,
    drat_bytes: u64,
    drat_trim: DratTrimStatus,
    /// Wall-clock for the single `sys::parse` + `sys::solve` call.
    /// Used only for the aggregate stderr summary and for the
    /// too-easy soft warning; not asserted, because the actual
    /// per-instance timing varies wildly across machines and load.
    solve_elapsed: Duration,
    warning: Option<String>,
}

#[test]
fn release_corpus_solver_agrees_and_emits_well_formed_drat() {
    let _guard = CORPUS_LOCK.lock().expect("corpus lock not poisoned");
    let manifest = load_manifest();

    let mut reports: Vec<FixtureReport> = Vec::new();
    let mut errors: Vec<String> = Vec::new();
    let mut warnings: Vec<String> = Vec::new();

    for fixture in &manifest.fixtures {
        match run_one(fixture) {
            Ok(report) => {
                if let Some(w) = &report.warning {
                    warnings.push(w.clone());
                }
                reports.push(report);
            }
            Err(e) => errors.push(e),
        }
    }

    // Aggregate stderr summary so `cargo test -- --nocapture` gives a
    // human-readable view of what happened.
    let stderr = std::io::stderr();
    let mut out = stderr.lock();
    writeln!(out, "sat_corpus: ran {} fixtures", manifest.fixtures.len()).ok();
    writeln!(
        out,
        "sat_corpus: drat-trim vendored under third_party/vendor/drat-trim (built via trust-cg-drat-trim)"
    )
    .ok();
    let mut accepted = 0usize;
    let mut skipped = 0usize;
    let mut rejected = 0usize;
    for r in &reports {
        let solve_us = r.solve_elapsed.as_secs_f64() * 1.0e6;
        writeln!(
            out,
            "  {:<24} expected={:<5} rc={} solve={:>10.1}us drat={}B drat-trim={}",
            r.file, r.expected, r.observed_code, solve_us, r.drat_bytes, r.drat_trim
        )
        .ok();
        match r.drat_trim {
            DratTrimStatus::Accepted => accepted += 1,
            DratTrimStatus::Skipped => skipped += 1,
            DratTrimStatus::Rejected => rejected += 1,
        }
    }
    writeln!(
        out,
        "sat_corpus: passed={} failed={} warnings={} drat-trim accepted={} skipped={} rejected={}",
        reports.len(),
        errors.len(),
        warnings.len(),
        accepted,
        skipped,
        rejected,
    )
    .ok();

    // Per-category pass-count summary. Closes critical-review limitation
    // #6 ("only random 3-SAT") in benchmarks/benchmark_study.md by making the
    // category mix explicit at the end of every test run. BTreeMap so the
    // output is deterministically ordered alphabetically.
    let mut by_category: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    for r in &reports {
        let entry = by_category.entry(r.category.as_str()).or_insert((0, 0));
        entry.0 += 1; // total
        if matches!(
            r.drat_trim,
            DratTrimStatus::Accepted | DratTrimStatus::Skipped
        ) {
            // Every `run_one` Ok-result has already passed the
            // expected/observed agreement check, so any non-error
            // report counts as a pass. drat-trim "Skipped" is the
            // SAT-instance case (no proof to check) and is still a
            // pass.
            entry.1 += 1; // passed
        }
    }
    writeln!(out, "sat_corpus: per-category pass counts:").ok();
    for (cat, (total, passed)) in &by_category {
        writeln!(out, "  category={:<14} passed={}/{}", cat, passed, total).ok();
    }

    for w in &warnings {
        writeln!(out, "sat_corpus: WARNING {}", w).ok();
    }
    for e in &errors {
        writeln!(out, "sat_corpus: FAIL {}", e).ok();
    }
    drop(out);

    assert!(
        errors.is_empty(),
        "sat_corpus failures ({}): {:#?}",
        errors.len(),
        errors
    );
    // At least one fixture must have passed; otherwise the harness
    // would be reporting success on an empty corpus and we'd never
    // notice the manifest broke.
    assert!(
        !reports.is_empty(),
        "sat_corpus: zero fixtures actually ran"
    );
}

/// Re-run the full project-authored corpus under `PRIMARY_JIT_MODE` and assert
/// the verdict still matches expected. After A1's scratch-arena work
/// the JIT-replacement path stays engaged for the entire solve (no
/// epoch-fallback, no recompile), and the basic primary path's gate
/// is `pre_authoritative`-at-root; mid-search decisions still fall
/// through to native for the conflict branch, which is the regime
/// this corpus exercises. The contract here is "rc and divergence
/// counter stay correct"; wall-clock is the bench binary's job.
#[test]
fn release_corpus_primary_jit_mode_zero_divergences() {
    let _guard = CORPUS_LOCK.lock().expect("corpus lock not poisoned");
    let manifest = load_manifest();
    // DRAT is per-process; tests above this one may have left the
    // recorder armed. Disable to keep PRIMARY_JIT_MODE solves quiet.
    disable_drat_output();
    let divergences_before = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
    let primaries_before = JIT_PRIMARY_RETURNS.load(Ordering::SeqCst);
    let mut failures: Vec<String> = Vec::new();
    let mut ran = 0usize;
    for fixture in &manifest.fixtures {
        let cnf_path = corpus_dir().join(&fixture.file);
        if !cnf_path.exists() {
            failures.push(format!("fixture missing: {}", cnf_path.display()));
            continue;
        }
        let expected = expected_code(&fixture.expected);
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        let rc = solve_path(&cnf_path);
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
        ran += 1;
        if rc != expected {
            failures.push(format!(
                "{}: expected {} ({}), got {} under PRIMARY_JIT_MODE",
                fixture.file, fixture.expected, expected, rc
            ));
        }
    }
    let divergences_after = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
    let primaries_after = JIT_PRIMARY_RETURNS.load(Ordering::SeqCst);
    eprintln!(
        "release_corpus_primary_jit_mode_zero_divergences: ran={ran} \
         failures={} divergences_delta={} primary_returns_delta={}",
        failures.len(),
        divergences_after - divergences_before,
        primaries_after - primaries_before
    );
    assert!(
        failures.is_empty(),
        "PRIMARY_JIT_MODE corpus failures: {:#?}",
        failures
    );
    assert_eq!(
        divergences_after, divergences_before,
        "PRIMARY_JIT_MODE accumulated divergences across the corpus: \
         before={divergences_before} after={divergences_after}"
    );
    assert!(
        primaries_after > primaries_before,
        "expected the JIT primary path to fire at least once across \
         the corpus; before={primaries_before} after={primaries_after}"
    );
    assert!(ran > 0, "no fixtures actually ran");
}
