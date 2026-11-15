#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: core's O(1) `Range` / `RangeInclusive` iterator methods
// (`count`, `last`, `min`, `max`, `nth`, `Skip`'s skip) and `Vec::extend` from a
// range or a `TrustedLen` chain answer exactly as LLVM does — same values, same
// panics, same leftover state, same capacity — over spans no per-item walk
// finishes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT IT PINS.
//   * `fix_range_closed_forms.rs`: core computes `Range::count` with
//     `Step::steps_between`, `last` / `max` with `next_back`, `min` with `next`,
//     `nth` with `Step::forward_checked`, and `Skip`'s skip with ONE source
//     `nth`. The bridge's iterator drives pulled one item per loop trip, so
//     `(0..u64::MAX).count()`, `.last()`, `.skip(1 << 62).next()` and the like
//     never returned (measured on the base backend at -O0..-O3), and core's
//     panics ("count overflowed usize" past `usize::MAX`, `Chain::count`'s add
//     under overflow checks) were never reached. The closed forms act on the
//     source state before the drive (`emit_range_run_*` in `lib.rs`).
//   * `fix_range_extend_reserve.rs`: `v.extend(a..b)` counted a 64-bit range as
//     a wrapping `end - start` (an empty `i64::MAX..i64::MIN` appended
//     `i64::MAX`, a span of 2^63 appended nothing where std panics "capacity
//     overflow"; a `u64` / `usize` range did not lower at all), and
//     `v.extend(chain)` pushed item by item where std's `extend_trusted`
//     reserves the exact length first: a `map` closure ran (the fixture's
//     closure exits 42 on its 1000th call) where std panics before calling it,
//     and the capacity grew by doubling where std reserves once. Its cases run
//     at -O0/-O1: at -O2/-O3 rustc inlines `Vec::extend` to
//     `Vec::extend_trusted`, which the bridge refuses, so there a refusal is
//     accepted only when it names its `[TCG-*]` code.
//
// THE GATE. Each fixture is compiled per CONFIG by both backends and every case
// runs against both binaries (killed after `RUN_TIMEOUT`), compared on exit
// code, killing signal, stdout, and which panic it raised. A bridge refusal of
// a closed-form config fails the test. The oracle's own panics are pinned
// (`*_PANICS`), so a fixture edit cannot silently stop exercising them.
//
// NOT COVERED: the panic Location (the intercepted lowering raises with the
// caller's Location where LLVM reports core's or alloc's line), so stderr is
// reduced to the panic message (`stderr_verdict`); a 32-bit `usize` (wasm32
// keeps its per-item count model).
//
// HOST-NATIVE: no `--target` is passed. Measured on aarch64-apple-darwin. The
// bridge side passes `no-proof-certs` (certs=off: with certificates on, AArch64
// refuses essentially every object at proof promotion, unrelated to this
// lowering).

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const CLOSED_FORMS: &str = include_str!("bridge_corpus/fix_range_closed_forms.rs");
const EXTEND: &str = include_str!("bridge_corpus/fix_range_extend_reserve.rs");

const CLOSED_FORM_CASES: &[&str] = &[
    "count",
    "count_wide",
    "count_incl",
    "count_adapters",
    "count_incl_full",
    "count_skip0_full",
    "count_enumerate_full",
    "count_u128_ovf",
    "count_chain_ovf",
    "last",
    "min_max",
    "nth",
    "skip",
    "windows",
];
/// Cases whose LLVM run panics in every configuration.
const CLOSED_FORM_PANICS: &[&str] = &[
    "count_incl_full",
    "count_skip0_full",
    "count_enumerate_full",
    "count_u128_ovf",
];
/// Cases whose LLVM run panics exactly when overflow checks are on.
const CLOSED_FORM_CHECKED_PANICS: &[&str] = &["count_chain_ovf"];

const EXTEND_CASES: &[&str] = &[
    "range_i64",
    "range_isize",
    "range_u64",
    "range_narrow",
    "range_span_2p63",
    "range_span_full",
    "range_u64_full",
    "map_small",
    "map_huge",
    "map_u8_huge",
    "map_incl_full",
    "map_u128_huge",
    "skip_incl_huge",
];
const EXTEND_PANICS: &[&str] = &[
    "range_span_2p63",
    "range_span_full",
    "range_u64_full",
    "map_huge",
    "map_u8_huge",
    "map_incl_full",
    "map_u128_huge",
    "skip_incl_huge",
];

const RUN_TIMEOUT: Duration = Duration::from_secs(60);

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_range_cf_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `source` with `flags`, through the bridge when `backend` is `Some`.
/// `Err` carries the compiler's stderr.
fn compile(
    dir: &Path,
    source: &str,
    lane: &str,
    flags: &[String],
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let src_path = dir.join("fixture.rs");
    if !src_path.exists() {
        std::fs::write(&src_path, source).expect("write fixture");
    }
    let bin = dir.join(format!("fixture_{lane}"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Ccodegen-units=1"]);
    cmd.args(flags);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    /// stderr reduced by `stderr_verdict`.
    stderr: String,
    timed_out: bool,
}

/// A run's stderr as this test compares it: verbatim when the program did not
/// panic, otherwise only the panic's message (see NOT COVERED).
fn stderr_verdict(stderr: &str) -> String {
    if !stderr.contains("panicked at") {
        return stderr.to_owned();
    }
    for (needle, verdict) in [
        ("count overflowed usize", "count overflowed usize"),
        ("capacity overflow", "capacity overflow"),
        ("attempt to add with overflow", "add with overflow"),
        ("`Add` with overflow", "add with overflow"),
    ] {
        if stderr.contains(needle) {
            return format!("panicked: {verdict}");
        }
    }
    "panicked: <another panic>".to_owned()
}

fn run(bin: &Path, case: &str) -> Ending {
    let mut child = Command::new(bin)
        .env("CASE", case)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run compiled binary");
    let deadline = Instant::now() + RUN_TIMEOUT;
    let mut timed_out = false;
    loop {
        if child.try_wait().expect("poll the binary").is_some() {
            break;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            timed_out = true;
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let out = child
        .wait_with_output()
        .expect("collect the binary's output");
    Ending {
        code: out.status.code(),
        signal: if timed_out { None } else { out.status.signal() },
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: stderr_verdict(&String::from_utf8_lossy(&out.stderr)),
        timed_out,
    }
}

fn stderr_tail(stderr: &str) -> String {
    stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
}

/// The panic an LLVM run must show for a case that panics.
fn oracle_panicked(want: &Ending, strategy: &str) -> bool {
    match strategy {
        "unwind" => want.code == Some(101),
        _ => want.signal == Some(6),
    }
}

struct Tally {
    matched: usize,
    total: usize,
    failures: Vec<String>,
}

/// Run every case of one config against both binaries.
fn compare_cases(
    tally: &mut Tally,
    config: &str,
    oracle: &Path,
    bridge: &Path,
    cases: &[&str],
    expect_panic: &dyn Fn(&str) -> bool,
    strategy: &str,
) {
    for case in cases {
        tally.total += 1;
        let want = run(oracle, case);
        assert!(
            !want.timed_out,
            "{config} CASE={case}: the LLVM oracle timed out"
        );
        let panics = expect_panic(case);
        assert_eq!(
            oracle_panicked(&want, strategy),
            panics,
            "{config} CASE={case}: the LLVM oracle's panic behaviour changed ({want:?}); \
             the fixture no longer exercises this case"
        );
        if !panics {
            assert_eq!(
                want.code,
                Some(0),
                "{config} CASE={case}: the LLVM oracle did not exit 0: {want:?}"
            );
        }
        let got = run(bridge, case);
        if got == want {
            tally.matched += 1;
        } else {
            tally.failures.push(format!(
                "{config} CASE={case}: LLVM {want:?} vs trust-cg {got:?}"
            ));
        }
    }
}

#[test]
fn range_closed_forms_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("range_closed_forms_match_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut tally = Tally {
        matched: 0,
        total: 0,
        failures: Vec::new(),
    };
    for opt in ["0", "1", "2", "3"] {
        for checks in ["on", "off"] {
            for strategy in ["unwind", "abort"] {
                let config = format!("-O{opt} overflow-checks={checks} panic={strategy}");
                let flags = vec![
                    format!("-Copt-level={opt}"),
                    format!("-Coverflow-checks={checks}"),
                    format!("-Cpanic={strategy}"),
                ];
                let dir = workdir(&format!("closed_O{opt}_{checks}_{strategy}"));
                let oracle = compile(&dir, CLOSED_FORMS, "llvm", &flags, None)
                    .unwrap_or_else(|e| panic!("{config}: the LLVM oracle failed: <<<{e}>>>"));
                let bridge = match compile(&dir, CLOSED_FORMS, "bridge", &flags, Some(&dylib)) {
                    Ok(bin) => bin,
                    Err(stderr) => {
                        tally.total += CLOSED_FORM_CASES.len();
                        tally.failures.push(format!(
                            "{config}: the bridge REFUSED the fixture: <<<{}>>>",
                            stderr_tail(&stderr)
                        ));
                        let _ = std::fs::remove_dir_all(&dir);
                        continue;
                    }
                };
                let expect_panic = |case: &str| {
                    CLOSED_FORM_PANICS.contains(&case)
                        || (checks == "on" && CLOSED_FORM_CHECKED_PANICS.contains(&case))
                };
                compare_cases(
                    &mut tally,
                    &config,
                    &oracle,
                    &bridge,
                    CLOSED_FORM_CASES,
                    &expect_panic,
                    strategy,
                );
                let _ = std::fs::remove_dir_all(&dir);
            }
        }
    }
    eprintln!(
        "RANGE_CLOSED_FORMS rows={} matched={} certs=off",
        tally.total, tally.matched
    );
    for failure in &tally.failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        tally.failures.is_empty() && tally.matched == tally.total,
        "{} of {} range closed-form rows diverged from LLVM or never ran: {:#?}",
        tally.total - tally.matched,
        tally.total,
        tally.failures
    );
}

#[test]
fn range_extend_reserve_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs("range_extend_reserve_matches_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut tally = Tally {
        matched: 0,
        total: 0,
        failures: Vec::new(),
    };
    let mut refused_optimized = 0usize;
    for opt in ["0", "1", "2", "3"] {
        for strategy in ["unwind", "abort"] {
            let config = format!("-O{opt} panic={strategy}");
            let flags = vec![format!("-Copt-level={opt}"), format!("-Cpanic={strategy}")];
            let dir = workdir(&format!("extend_O{opt}_{strategy}"));
            let oracle = compile(&dir, EXTEND, "llvm", &flags, None)
                .unwrap_or_else(|e| panic!("{config}: the LLVM oracle failed: <<<{e}>>>"));
            let bridge = match compile(&dir, EXTEND, "bridge", &flags, Some(&dylib)) {
                Ok(bin) => bin,
                // -O2/-O3: `Vec::extend` inlines to `Vec::extend_trusted`, which
                // the bridge refuses, as it refuses the fixture's capacity
                // printing there ([TCG-FMT-LEN]); any refusal must name its code.
                Err(stderr) if opt >= "2" => {
                    assert!(
                        stderr.contains("[TCG-"),
                        "{config}: an unnamed refusal: <<<{}>>>",
                        stderr_tail(&stderr)
                    );
                    refused_optimized += 1;
                    let _ = std::fs::remove_dir_all(&dir);
                    continue;
                }
                Err(stderr) => {
                    tally.total += EXTEND_CASES.len();
                    tally.failures.push(format!(
                        "{config}: the bridge REFUSED the fixture: <<<{}>>>",
                        stderr_tail(&stderr)
                    ));
                    let _ = std::fs::remove_dir_all(&dir);
                    continue;
                }
            };
            let expect_panic = |case: &str| EXTEND_PANICS.contains(&case);
            compare_cases(
                &mut tally,
                &config,
                &oracle,
                &bridge,
                EXTEND_CASES,
                &expect_panic,
                strategy,
            );
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    eprintln!(
        "RANGE_EXTEND_RESERVE rows={} matched={} refused_optimized={refused_optimized} certs=off",
        tally.total, tally.matched
    );
    for failure in &tally.failures {
        eprintln!("  FAILED {failure}");
    }
    // The -O0 and -O1 configs must all have run.
    assert!(
        tally.total >= 4 * EXTEND_CASES.len(),
        "fewer than the -O0/-O1 configs ran"
    );
    assert!(
        tally.failures.is_empty() && tally.matched == tally.total,
        "{} of {} Vec::extend rows diverged from LLVM or never ran: {:#?}",
        tally.total - tally.matched,
        tally.total,
        tally.failures
    );
}
