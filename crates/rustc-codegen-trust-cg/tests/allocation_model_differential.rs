#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the allocations the bridge synthesizes in place of std's
// collection and `Box` constructors are the ones std makes — same requests,
// same failure handling, same unwind edges, same `capacity()`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS (measured on AArch64 Darwin against origin/main 57a83d211,
// the backend before the fixes pinned here):
//
// * `zero_extent_collections_never_reach_a_failing_allocator` — std allocates
//   nothing for `vec![x; 0]`, `repeat(0)`, `[T; 0].repeat(n)`, a
//   `split_off(len)` tail, `BTreeMap::new()`, `HashMap::new()` or a ZST `Box`;
//   the bridge reserved a placeholder element (or a 16-byte map slot) and,
//   with an allocator that fails every request, aborted "memory allocation of
//   N bytes failed" (or freed the ZST box's dangling pointer: SIGABRT).
// * `capacity_values_match_std` — `capacity()` after those constructors and
//   after `collect()` (empty results reported 1; exact-size `collect()` grew
//   by doubling: 3 elements reported 4, 9 reported 16).
// * `allocator_requests_match_std` — `vec![0; n]` called `alloc`, not
//   `alloc_zeroed`; empty constructors made one-element requests.
// * `collect_routes_match_std` — `v.into_iter()...collect()` allocated a fresh
//   buffer and leaked the source where std collects in place, reuses, or
//   frees it.
// * `allocation_failure_calls_the_alloc_error_handler_like_llvm` — a null
//   `Box::new` / `Box::new_uninit` / `Rc::new` / `split_off` allocation was
//   stored through (SIGSEGV) instead of reaching `handle_alloc_error`.
// * `a_panicking_alloc_error_hook_unwinds_on_the_source_edge` — when the
//   allocation-error hook panics, the failure call must unwind on the edge of
//   the source call it stands in for: a live guard's Drop runs (cleanup edge),
//   an `extern "C"` frame aborts (terminate edge), a map insert's helper call
//   carries the insert's edge.
// * `btreemap_model_allocation_failure_reaches_the_handler` — the bridge's
//   BTreeMap model stored through a null buffer (SIGSEGV).
// * `zst_box_drop_frees_nothing` — dropping a ZST box called `free(align)`.
// * `capacity_overflow_raises_on_the_source_edge` — the capacity-overflow
//   panic of `vec![x; n]` / `repeat(n)` in an `extern "C"` frame was refused
//   by name under `panic=unwind`.
//
// THE GATE. Every fixture is compiled by both backends (LLVM first, as the
// oracle) at -O0..-O3 under each listed panic strategy and run per row
// (`ALLOC_SHAPE`, the row selector). The oracle is held to the row's intent
// first, then the bridge's exit status / signal, stdout and stderr must EQUAL
// the oracle's, after dropping only the thread id of the default panic hook's
// first line and forced-backtrace frame lines. Two rows compare at the class
// level because the bridge's map model is not std's B-tree / hash table: its
// requests have other SIZES (`AllocClass`: both abort through "memory
// allocation of"; `HookSizeMasked`: the panicking hook's `hooked N` size is
// masked, everything else equal). A configuration the bridge refuses never
// runs its rows and fails the test, except where a fixture's policy admits a
// NAMED `[TCG-...]` refusal past -O0 (the `StepBy` and owning `vec::IntoIter`
// shapes the bridge refuses by name there).
//
// The bridge compiles pass `no-proof-certs` (the opcode-inventory proof lane
// refuses every AArch64 program with `[TCG-PROOF-465]`, unrelated to these
// paths).

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["0", "1", "2", "3"];
const BOTH: &[&str] = &["abort", "unwind"];

/// What a row's LLVM oracle must show before the bridge is compared with it.
#[derive(Clone, Copy)]
enum Intent {
    /// Exits 0 and prints this line.
    Prints(&'static str),
    /// Aborts through std's allocation-error hook with this message.
    AllocFailure(&'static str),
    /// Panics "capacity overflow" (abort: SIGABRT; unwind: exit 101, or
    /// SIGABRT at a frame that cannot unwind).
    CapacityOverflow,
    /// The panicking hook unwound through the frame: its guard's Drop line is
    /// on stdout and the process left through `lang_start` (exit 101).
    UnwoundThroughGuard(&'static str),
    /// The panicking hook reached a frame that cannot unwind.
    TerminatedInNounwindFrame,
}

/// How the bridge's outcome is compared with the oracle's.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Compare {
    Exact,
    /// Both abort through "memory allocation of", with equal stdout.
    AllocClass,
    /// Equal after masking the size in the hook's `hooked N` message.
    HookSizeMasked,
}

struct Row {
    selector: &'static str,
    what: &'static str,
    intent: Intent,
    compare: Compare,
}

const fn row(selector: &'static str, what: &'static str, intent: Intent) -> Row {
    Row {
        selector,
        what,
        intent,
        compare: Compare::Exact,
    }
}

const fn class_row(
    selector: &'static str,
    what: &'static str,
    intent: Intent,
    compare: Compare,
) -> Row {
    Row {
        selector,
        what,
        intent,
        compare,
    }
}

/// Where the bridge may refuse a configuration.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Policy {
    /// Every configuration must compile.
    Must,
    /// -O0 must compile; -O1..-O3 may refuse with a NAMED `[TCG-...]`
    /// diagnostic, and must match wherever they compile.
    MustAtO0,
}

struct Fixture {
    name: &'static str,
    src: &'static str,
    /// An rlib the fixture links, always compiled by LLVM: (crate name, source).
    rlib: Option<(&'static str, &'static str)>,
    strategies: &'static [&'static str],
    rows: &'static [Row],
    policy: Policy,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Outcome {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    stderr: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_alloc_model_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `name.rs` (in `dir`) as a std binary, with the bridge when `backend`
/// is `Some`. Compiled from inside `dir` with a relative source path so both
/// backends print the same Location file names.
fn compile(
    dir: &Path,
    name: &str,
    opt: &str,
    strategy: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let lane = if backend.is_some() { "bridge" } else { "llvm" };
    let bin = dir.join(format!("{name}_{lane}"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Cpanic={strategy}"))
        .arg("-L")
        .arg(dir);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.current_dir(dir)
        .arg("-o")
        .arg(&bin)
        .arg(format!("{name}.rs"));
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

/// Build the fixture's helper rlib with the LLVM backend into `dir`.
fn compile_rlib(dir: &Path, crate_name: &str, src: &str, strategy: &str) {
    let src_path = dir.join(format!("{crate_name}.rs"));
    std::fs::write(&src_path, src).expect("write rlib source");
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "rlib", "--crate-name", crate_name])
        .arg(format!("-Cpanic={strategy}"))
        .arg("-o")
        .arg(dir.join(format!("lib{crate_name}.rlib")))
        .arg(&src_path)
        .output()
        .expect("spawn the compiler for the helper rlib");
    assert!(
        output.status.success(),
        "{crate_name}: the LLVM-built helper rlib failed to compile: <<<{}>>>",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Drop the thread id of the default hook's `thread '<name>' (<tid>) panicked
/// at` line and forced-backtrace frame lines; keep every other line.
fn normalize_stderr(stderr: &[u8]) -> String {
    let text = String::from_utf8_lossy(stderr);
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        let trimmed = line.trim_start();
        let is_frame = trimmed.split_once(':').is_some_and(|(n, rest)| {
            !n.is_empty()
                && n.bytes().all(|b| b.is_ascii_digit())
                && rest.trim_start().starts_with("0x")
        });
        let is_frame_location = trimmed.starts_with("at ") && line.starts_with("    ");
        if is_frame || is_frame_location {
            continue;
        }
        match (line.find("' ("), line.find(") panicked at ")) {
            (Some(open), Some(close)) if line.starts_with("thread '") && open < close => {
                out.push_str(&line[..open + 1]);
                out.push_str(&line[close + 1..]);
            }
            _ => out.push_str(line),
        }
        out.push('\n');
    }
    out
}

/// Replace the decimal size after every `hooked ` with `N`.
fn mask_hook_sizes(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find("hooked ") {
        let (head, tail) = rest.split_at(at + "hooked ".len());
        out.push_str(head);
        let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
        if digits > 0 {
            out.push('N');
        }
        rest = &tail[digits..];
    }
    out.push_str(rest);
    out
}

/// A row's binary that runs longer than this is killed and reported as
/// `timed out` (a failure path that loops).
const RUN_LIMIT: std::time::Duration = std::time::Duration::from_secs(60);

fn run(bin: &Path, selector: &str) -> Outcome {
    let mut child = Command::new(bin)
        .env("ALLOC_SHAPE", selector)
        .env_remove("RUST_BACKTRACE")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("run compiled binary");
    let mut stdout_pipe = child.stdout.take().expect("piped stdout");
    let mut stderr_pipe = child.stderr.take().expect("piped stderr");
    let readers = (
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = std::io::Read::read_to_end(&mut stdout_pipe, &mut bytes);
            bytes
        }),
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = std::io::Read::read_to_end(&mut stderr_pipe, &mut bytes);
            bytes
        }),
    );
    let started = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("poll compiled binary") {
            break Some(status);
        }
        if started.elapsed() > RUN_LIMIT {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    };
    let stdout = readers.0.join().expect("stdout reader");
    let stderr = readers.1.join().expect("stderr reader");
    let Some(status) = status else {
        return Outcome {
            code: None,
            signal: None,
            stdout: String::from_utf8_lossy(&stdout).into_owned(),
            stderr: format!("timed out after {RUN_LIMIT:?}"),
        };
    };
    #[cfg(unix)]
    let signal = std::os::unix::process::ExitStatusExt::signal(&status);
    #[cfg(not(unix))]
    let signal = None;
    Outcome {
        code: status.code(),
        signal,
        stdout: String::from_utf8_lossy(&stdout).into_owned(),
        stderr: normalize_stderr(&stderr),
    }
}

/// SIGABRT, how std's allocation-error hook and a `panic=abort` panic end.
const SIGABRT: i32 = 6;

fn check_oracle(label: &str, want: &Outcome, intent: Intent, strategy: &str) {
    match intent {
        Intent::Prints(line) => assert!(
            want.code == Some(0) && want.stdout.lines().any(|l| l == line),
            "{label}: the LLVM oracle did not exit 0 printing {line:?}: {want:?}"
        ),
        Intent::AllocFailure(message) => assert!(
            want.signal == Some(SIGABRT) && want.stderr.starts_with(message),
            "{label}: the LLVM oracle did not abort through {message:?}: {want:?}"
        ),
        Intent::CapacityOverflow => assert!(
            (want.signal == Some(SIGABRT) || (strategy == "unwind" && want.code == Some(101)))
                && want.stderr.contains("panicked at ")
                && want.stderr.contains("capacity overflow"),
            "{label}: the LLVM oracle did not panic \"capacity overflow\": {want:?}"
        ),
        Intent::UnwoundThroughGuard(drop_line) => {
            if strategy == "unwind" {
                assert!(
                    want.code == Some(101) && want.stdout.contains(drop_line),
                    "{label}: the LLVM oracle did not unwind through the guard \
                     ({drop_line:?}, exit 101): {want:?}"
                );
            } else {
                assert!(
                    want.signal == Some(SIGABRT) && want.stderr.contains("hooked"),
                    "{label}: the LLVM oracle did not abort from the panicking hook: {want:?}"
                );
            }
        }
        Intent::TerminatedInNounwindFrame => {
            if strategy == "unwind" {
                assert!(
                    want.signal == Some(SIGABRT)
                        && want
                            .stderr
                            .contains("panic in a function that cannot unwind"),
                    "{label}: the LLVM oracle did not stop at the nounwind frame: {want:?}"
                );
            } else {
                assert!(
                    want.signal == Some(SIGABRT) && want.stderr.contains("hooked"),
                    "{label}: the LLVM oracle did not abort from the panicking hook: {want:?}"
                );
            }
        }
    }
}

fn outcomes_match(compare: Compare, want: &Outcome, got: &Outcome) -> bool {
    match compare {
        Compare::Exact => got == want,
        Compare::AllocClass => {
            got.signal == Some(SIGABRT)
                && got.code.is_none()
                && got.stdout == want.stdout
                && got.stderr.starts_with("memory allocation of ")
        }
        Compare::HookSizeMasked => {
            let mask = |o: &Outcome| Outcome {
                stderr: mask_hook_sizes(&o.stderr),
                ..o.clone()
            };
            got.stderr.contains("hooked ") && mask(got) == mask(want)
        }
    }
}

/// The bridge's own named refusal tag, if this stderr is a fail-closed refusal.
fn named_refusal(stderr: &str) -> Option<String> {
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')?;
    Some(stderr[start..start + end + 1].to_owned())
}

/// Compile `fixture` under every configuration and compare every row; returns
/// (rows, rows that failed or never ran, admitted refusals, failures).
fn run_fixture(dylib: &Path, fixture: &Fixture) -> (usize, usize, Vec<String>, Vec<String>) {
    let mut rows = 0;
    let mut failed_rows = 0;
    let mut refusals = Vec::new();
    let mut failures = Vec::new();
    for &opt in OPT_LEVELS {
        for &strategy in fixture.strategies {
            let label = format!("{} -O{opt} panic={strategy}", fixture.name);
            let dir = workdir(&format!("{}_O{opt}_{strategy}", fixture.name));
            std::fs::write(dir.join(format!("{}.rs", fixture.name)), fixture.src)
                .expect("write fixture");
            if let Some((crate_name, src)) = fixture.rlib {
                compile_rlib(&dir, crate_name, src, strategy);
            }
            let (oracle, bridge) = std::thread::scope(|scope| {
                let oracle = scope.spawn(|| compile(&dir, fixture.name, opt, strategy, None));
                let bridge =
                    scope.spawn(|| compile(&dir, fixture.name, opt, strategy, Some(dylib)));
                (
                    oracle.join().expect("oracle compile thread"),
                    bridge.join().expect("bridge compile thread"),
                )
            });
            let oracle =
                oracle.unwrap_or_else(|e| panic!("{label}: LLVM oracle failed: <<<{e}>>>"));
            rows += fixture.rows.len();
            let bridge = match bridge {
                Ok(bin) => bin,
                Err(stderr) => {
                    let tag = named_refusal(&stderr);
                    if fixture.policy == Policy::MustAtO0 && opt != "0" && tag.is_some() {
                        refusals.push(format!("{label}: refused {}", tag.unwrap_or_default()));
                    } else {
                        failed_rows += fixture.rows.len();
                        failures.push(format!(
                            "{label}: the bridge REFUSED, so {} row(s) never ran: <<<{}>>>",
                            fixture.rows.len(),
                            stderr.lines().take(8).collect::<Vec<_>>().join(" | ")
                        ));
                    }
                    let _ = std::fs::remove_dir_all(&dir);
                    continue;
                }
            };
            for row in fixture.rows {
                let row_label = format!("{label} ALLOC_SHAPE={}: {}", row.selector, row.what);
                let want = run(&oracle, row.selector);
                check_oracle(&row_label, &want, row.intent, strategy);
                let got = run(&bridge, row.selector);
                if !outcomes_match(row.compare, &want, &got) {
                    failed_rows += 1;
                    failures.push(format!("{row_label}: LLVM {want:?} vs bridge {got:?}"));
                }
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    (rows, failed_rows, refusals, failures)
}

fn assert_fixture(test: &str, fixture: &Fixture, denominator: usize) {
    if toolchain_support::skip_without_backend_knobs(test) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let (rows, failed_rows, refusals, failures) = run_fixture(&dylib, fixture);
    assert_eq!(rows, denominator, "{test}: the row denominator changed");
    let refused_rows = refusals.len() * fixture.rows.len();
    eprintln!(
        "{test}: {}/{rows} rows matched LLVM ({refused_rows} in configurations refused by name)",
        rows - failed_rows - refused_rows
    );
    for refusal in &refusals {
        eprintln!("  ADMITTED {refusal}");
    }
    for failure in &failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        failures.is_empty(),
        "{test}: {} failure(s). An abort \"memory allocation of N bytes failed\" where LLVM \
         exits 0 is an allocation std never makes; a SIGSEGV where LLVM aborts is a store \
         through a failed allocation; a different capacity or request count is a different \
         reservation; a missing `guard N dropped` line is a skipped cleanup; a refusal never \
         ran the rows. Failures: {failures:#?}",
        failures.len()
    );
}

const ZERO_EXTENT_ROWS: &[Row] = &[
    row("a", "vec![7u32; 0]", Intent::Prints("99 = 0")),
    row("b", "vec![struct; 0]", Intent::Prints("99 = 0")),
    row("c", "[u16; 3].repeat(0)", Intent::Prints("99 = 0")),
    row("d", "\"abc\".repeat(0)", Intent::Prints("99 = 0")),
    row("e", "[u64; 0].repeat(5)", Intent::Prints("99 = 0")),
    row("f", "v.split_off(v.len())", Intent::Prints("99 = 0")),
    row("g", "BTreeMap::new()", Intent::Prints("99 = 0")),
    row("h", "HashMap::new()", Intent::Prints("99 = 0")),
    row("i", "Vec::new()", Intent::Prints("99 = 0")),
    row(
        "j",
        "Box::new(()) and Box::new([0u64; 0])",
        Intent::Prints("99 = 0"),
    ),
    row("k", "vec![0u8; 0]", Intent::Prints("99 = 0")),
    row("z", "nothing armed (control)", Intent::Prints("99 = 0")),
];

#[test]
fn zero_extent_collections_never_reach_a_failing_allocator() {
    assert_fixture(
        "zero_extent_collections_never_reach_a_failing_allocator",
        &Fixture {
            name: "alloc_zero_extent_failing",
            src: include_str!("bridge_corpus/alloc_zero_extent_failing.rs"),
            rlib: None,
            strategies: BOTH,
            rows: ZERO_EXTENT_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * ZERO_EXTENT_ROWS.len(),
    );
}

const CAPACITY_ROWS: &[Row] = &[
    row("a", "vec![x; 0] and vec![x; 3]", Intent::Prints("end")),
    row(
        "b",
        "repeat(0) / repeat(n) / str::repeat",
        Intent::Prints("end"),
    ),
    row(
        "c",
        "split_off(len), split_off(0), split_off(1)",
        Intent::Prints("end"),
    ),
    row(
        "d",
        "slice.iter().copied().collect(): 3, 9, 0",
        Intent::Prints("end"),
    ),
    row("e", "(0..n) and (1..=n) collect", Intent::Prints("end")),
    row("f", "skip / take collect", Intent::Prints("end")),
    row(
        "g",
        "inspect collect (not TrustedLen): 7, 2, 0",
        Intent::Prints("end"),
    ),
    row("h", "filter collect (lower bound 0)", Intent::Prints("end")),
    row("i", "rev / enumerate collect", Intent::Prints("end")),
    row(
        "j",
        "skip above a rev collect (not TrustedLen)",
        Intent::Prints("end"),
    ),
    row("z", "every row", Intent::Prints("end")),
];

#[test]
fn capacity_values_match_std() {
    assert_fixture(
        "capacity_values_match_std",
        &Fixture {
            name: "alloc_capacity_values",
            src: include_str!("bridge_corpus/alloc_capacity_values.rs"),
            rlib: None,
            strategies: BOTH,
            rows: CAPACITY_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * CAPACITY_ROWS.len(),
    );
}

const REQUEST_ROWS: &[Row] = &[
    row(
        "a",
        "vec![0u8; 100] (alloc_zeroed) and vec![1u8; 100]",
        Intent::Prints("allocs=1 zeroed=1 deallocs=2 bytes=200 r=1"),
    ),
    row(
        "b",
        "vec![0u64; 5] and vec![3u64; 5]",
        Intent::Prints("allocs=1 zeroed=1 deallocs=2 bytes=80 r=3"),
    ),
    row(
        "c",
        "vec![0.0f64; 4] (zeroed) and vec![-0.0f64; 4] (filled)",
        Intent::Prints("allocs=1 zeroed=1 deallocs=2 bytes=64 r=1"),
    ),
    row(
        "d",
        "vec![(0, 0); 3] (zeroed), vec![struct; 3], vec![(0, 1); 3]",
        Intent::Prints("allocs=2 zeroed=1 deallocs=3 bytes=96 r=1"),
    ),
    row(
        "e",
        "empty vec![x; 0], repeat(0), split_off(len), str::repeat(0)",
        Intent::Prints("allocs=1 zeroed=0 deallocs=1 bytes=24 r=0"),
    ),
    row(
        "f",
        "ZST boxes",
        Intent::Prints("allocs=0 zeroed=0 deallocs=0 bytes=0 r=0"),
    ),
    row(
        "g",
        "exact-size collect from a slice and a range",
        Intent::Prints("allocs=2 zeroed=0 deallocs=2 bytes=48 r=6"),
    ),
    row(
        "h",
        "BTreeMap::new() and HashMap::new()",
        Intent::Prints("allocs=0 zeroed=0 deallocs=0 bytes=0 r=0"),
    ),
];

#[test]
fn allocator_requests_match_std() {
    assert_fixture(
        "allocator_requests_match_std",
        &Fixture {
            name: "alloc_request_counts",
            src: include_str!("bridge_corpus/alloc_request_counts.rs"),
            rlib: None,
            strategies: BOTH,
            rows: REQUEST_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * REQUEST_ROWS.len(),
    );
}

const COLLECT_ROUTE_ROWS: &[Row] = &[
    row(
        "a",
        "into_iter().map() collects in place",
        Intent::Prints("end"),
    ),
    row(
        "b",
        "into_iter().filter() collects in place",
        Intent::Prints("end"),
    ),
    row(
        "c",
        "into_iter().collect() reuses the buffer",
        Intent::Prints("end"),
    ),
    row(
        "d",
        "advanced into_iter (len >= cap / 2) reuses the buffer",
        Intent::Prints("end"),
    ),
    row(
        "e",
        "advanced into_iter (len < cap / 2) reallocates and frees",
        Intent::Prints("end"),
    ),
    row(
        "f",
        "into_iter().map(u64 -> u32): fresh buffer, source freed",
        Intent::Prints("end"),
    ),
    row(
        "g",
        "into_iter().rev(): fresh buffer, source freed",
        Intent::Prints("end"),
    ),
    row(
        "h",
        "(0..n).step_by(3) and (1..n).step_by(4)",
        Intent::Prints("end"),
    ),
    row(
        "i",
        "slice.iter().copied().step_by(2)",
        Intent::Prints("end"),
    ),
    row("j", "(0..n).chain(5..7)", Intent::Prints("end")),
    row("z", "nothing selected (control)", Intent::Prints("end")),
    row(
        "k",
        "step_by above a rev collect (not TrustedLen)",
        Intent::Prints("end"),
    ),
];

#[test]
fn collect_routes_match_std() {
    assert_fixture(
        "collect_routes_match_std",
        &Fixture {
            name: "alloc_collect_routes_o0",
            src: include_str!("bridge_corpus/alloc_collect_routes_o0.rs"),
            rlib: None,
            strategies: BOTH,
            rows: COLLECT_ROUTE_ROWS,
            policy: Policy::MustAtO0,
        },
        4 * 2 * COLLECT_ROUTE_ROWS.len(),
    );
}

const CHAIN_CONSTANT_ROWS: &[Row] = &[
    row(
        "a",
        "live left and constant right range",
        Intent::Prints(
            "allocs=1 deallocs=1 requested=40 freed=40 cap=5 sum=31874 observed=31874 observations=1",
        ),
    ),
    row(
        "b",
        "constant left and live right range",
        Intent::Prints(
            "allocs=1 deallocs=1 requested=40 freed=40 cap=5 sum=4796384 observed=4796384 observations=1",
        ),
    ),
    row(
        "c",
        "two constant ranges with high-word endpoint bits",
        Intent::Prints(
            "allocs=1 deallocs=1 requested=40 freed=40 cap=5 sum=137439939459 observed=137439939459 observations=1",
        ),
    ),
    row(
        "d",
        "empty constant left range",
        Intent::Prints(
            "allocs=1 deallocs=1 requested=16 freed=16 cap=2 sum=161 observed=161 observations=1",
        ),
    ),
    row(
        "e",
        "two reversed empty ranges",
        Intent::Prints(
            "allocs=0 deallocs=0 requested=0 freed=0 cap=0 sum=0 observed=0 observations=1",
        ),
    ),
    row(
        "f",
        "constant narrow-element range images",
        Intent::Prints(
            "allocs=1 deallocs=1 requested=20 freed=20 cap=5 sum=31874 observed=31874 observations=1",
        ),
    ),
    row(
        "g",
        "constant signed range images",
        Intent::Prints(
            "allocs=1 deallocs=1 requested=40 freed=40 cap=5 sum=18446744073707674944 observed=18446744073707674944 observations=1",
        ),
    ),
    row(
        "h",
        "slice iterator pointer relocations and niche Option payloads",
        Intent::Prints(
            "allocs=1 deallocs=1 requested=40 freed=40 cap=5 sum=127951372658632 observed=127951372658632 observations=1",
        ),
    ),
];

#[test]
fn chain_constant_routes_match_std() {
    assert_fixture(
        "chain_constant_routes_match_std",
        &Fixture {
            name: "alloc_chain_constant_routes",
            src: include_str!("bridge_corpus/alloc_chain_constant_routes.rs"),
            rlib: Some((
                "chain_observer",
                include_str!("support/chain_constant_observer.rs"),
            )),
            strategies: BOTH,
            rows: CHAIN_CONSTANT_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * CHAIN_CONSTANT_ROWS.len(),
    );
}

const NULL_ROWS: &[Row] = &[
    row(
        "a",
        "Box::new(u64)",
        Intent::AllocFailure("memory allocation of 8 bytes failed"),
    ),
    row(
        "b",
        "Box::new(struct)",
        Intent::AllocFailure("memory allocation of 16 bytes failed"),
    ),
    row(
        "c",
        "Box::new([u64; 513])",
        Intent::AllocFailure("memory allocation of 4104 bytes failed"),
    ),
    row(
        "d",
        "Box::<[u32; 7]>::new_uninit()",
        Intent::AllocFailure("memory allocation of 28 bytes failed"),
    ),
    row(
        "e",
        "vec![a, b, c, d, e]",
        Intent::AllocFailure("memory allocation of 40 bytes failed"),
    ),
    row(
        "f",
        "Vec::with_capacity(9)",
        Intent::AllocFailure("memory allocation of 36 bytes failed"),
    ),
    row(
        "g",
        "Vec::push growth",
        Intent::AllocFailure("memory allocation of 64 bytes failed"),
    ),
    row(
        "h",
        "vec![x; 11]",
        Intent::AllocFailure("memory allocation of 22 bytes failed"),
    ),
    row(
        "i",
        "String::push_str growth",
        Intent::AllocFailure("memory allocation of 10 bytes failed"),
    ),
    row(
        "j",
        "Rc::new(u64)",
        Intent::AllocFailure("memory allocation of 24 bytes failed"),
    ),
    row(
        "k",
        "<[u32]>::to_vec",
        Intent::AllocFailure("memory allocation of 12 bytes failed"),
    ),
    row(
        "l",
        "<[u8]>::repeat",
        Intent::AllocFailure("memory allocation of 10 bytes failed"),
    ),
    row(
        "m",
        "Vec::split_off",
        Intent::AllocFailure("memory allocation of 48 bytes failed"),
    ),
    row(
        "n",
        "Box::new in an extern \"C\" frame (terminate edge only)",
        Intent::AllocFailure("memory allocation of 8 bytes failed"),
    ),
    row(
        "z",
        "nothing armed (control)",
        Intent::Prints("unreachable unless z: 191"),
    ),
];

#[test]
fn allocation_failure_calls_the_alloc_error_handler_like_llvm() {
    assert_fixture(
        "allocation_failure_calls_the_alloc_error_handler_like_llvm",
        &Fixture {
            name: "alloc_null_sites",
            src: include_str!("bridge_corpus/alloc_null_sites.rs"),
            rlib: None,
            strategies: BOTH,
            rows: NULL_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * NULL_ROWS.len(),
    );
}

const HOOK_ROWS: &[Row] = &[
    row(
        "a",
        "Box::new([u64; 9]) with a live guard",
        Intent::UnwoundThroughGuard("guard 10 dropped"),
    ),
    row(
        "b",
        "Box::new([u64; 513]) with a live guard",
        Intent::UnwoundThroughGuard("guard 11 dropped"),
    ),
    row(
        "c",
        "vec![x; 51] with a live guard",
        Intent::UnwoundThroughGuard("guard 12 dropped"),
    ),
    row(
        "d",
        "vec![a, ..] with a live guard",
        Intent::UnwoundThroughGuard("guard 13 dropped"),
    ),
    row(
        "f",
        "Box::new in an extern \"C\" frame (terminate edge only)",
        Intent::TerminatedInNounwindFrame,
    ),
    class_row(
        "g",
        "BTreeMap first insert with a live guard",
        Intent::UnwoundThroughGuard("guard 14 dropped"),
        Compare::HookSizeMasked,
    ),
    class_row(
        "h",
        "HashMap first insert with a live guard",
        Intent::UnwoundThroughGuard("guard 15 dropped"),
        Compare::HookSizeMasked,
    ),
    row("z", "nothing armed (control)", Intent::Prints("returned 0")),
];

#[test]
fn a_panicking_alloc_error_hook_unwinds_on_the_source_edge() {
    assert_fixture(
        "a_panicking_alloc_error_hook_unwinds_on_the_source_edge",
        &Fixture {
            name: "alloc_error_hook_unwind",
            src: include_str!("bridge_corpus/alloc_error_hook_unwind.rs"),
            rlib: Some((
                "alloc_error_hook_set",
                include_str!("bridge_corpus/alloc_error_hook_set.rs"),
            )),
            strategies: BOTH,
            rows: HOOK_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * HOOK_ROWS.len(),
    );
}

const BTREEMAP_ROWS: &[Row] = &[
    class_row(
        "a",
        "fail from the first insert",
        Intent::AllocFailure("memory allocation of "),
        Compare::AllocClass,
    ),
    class_row(
        "b",
        "fail from the second insert",
        Intent::AllocFailure("memory allocation of "),
        Compare::AllocClass,
    ),
    class_row(
        "c",
        "fail from the thirteenth insert",
        Intent::AllocFailure("memory allocation of "),
        Compare::AllocClass,
    ),
    row("z", "nothing armed (control)", Intent::Prints("r=61")),
];

#[test]
fn btreemap_model_allocation_failure_reaches_the_handler() {
    assert_fixture(
        "btreemap_model_allocation_failure_reaches_the_handler",
        &Fixture {
            name: "alloc_btreemap_model_null",
            src: include_str!("bridge_corpus/alloc_btreemap_model_null.rs"),
            rlib: None,
            strategies: BOTH,
            rows: BTREEMAP_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * BTREEMAP_ROWS.len(),
    );
}

const ZST_BOX_ROWS: &[Row] = &[
    row("a", "Box::new(())", Intent::Prints("r = 1")),
    row("b", "Box::new([0u64; 0])", Intent::Prints("r = 8")),
    row("c", "Box::<()>::new_uninit()", Intent::Prints("r = 1")),
    row("z", "no box (control)", Intent::Prints("r = 0")),
];

#[test]
fn zst_box_drop_frees_nothing() {
    assert_fixture(
        "zst_box_drop_frees_nothing",
        &Fixture {
            name: "alloc_zst_box_default",
            src: include_str!("bridge_corpus/alloc_zst_box_default.rs"),
            rlib: None,
            strategies: BOTH,
            rows: ZST_BOX_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * ZST_BOX_ROWS.len(),
    );
}

const OVERFLOW_ROWS: &[Row] = &[
    row(
        "a",
        "vec![x; 2^61 + 1] with a live guard",
        Intent::CapacityOverflow,
    ),
    row(
        "b",
        "repeat with a wrapping product, live guard",
        Intent::CapacityOverflow,
    ),
    row(
        "c",
        "vec![x; 2^61 + 1] in an extern \"C\" frame",
        Intent::CapacityOverflow,
    ),
    row(
        "d",
        "repeat with a wrapping product in an extern \"C\" frame",
        Intent::CapacityOverflow,
    ),
    row("e", "repeat through a Vec deref", Intent::CapacityOverflow),
    row(
        "f",
        "repeat through a String deref",
        Intent::CapacityOverflow,
    ),
    row(
        "g",
        "repeat with a capacity past isize::MAX, live guard",
        Intent::CapacityOverflow,
    ),
    row(
        "A",
        "vec![x; 3] with a live guard (control)",
        Intent::Prints("r = 7"),
    ),
    row(
        "B",
        "repeat(3) with a live guard (control)",
        Intent::Prints("r = 1"),
    ),
    row(
        "C",
        "vec![x; 3] in an extern \"C\" frame (control)",
        Intent::Prints("r = 7"),
    ),
    row(
        "D",
        "repeat(3) in an extern \"C\" frame (control)",
        Intent::Prints("r = 1"),
    ),
    row(
        "E",
        "repeat(3) through a Vec deref (control)",
        Intent::Prints("r = 1"),
    ),
    row(
        "F",
        "repeat(3) through a String deref (control)",
        Intent::Prints("r = 97"),
    ),
    row(
        "G",
        "repeat(3) with a live guard (control)",
        Intent::Prints("r = 1"),
    ),
    row("z", "nothing (control)", Intent::Prints("r = 0")),
];

#[test]
fn capacity_overflow_raises_on_the_source_edge() {
    assert_fixture(
        "capacity_overflow_raises_on_the_source_edge",
        &Fixture {
            name: "alloc_capacity_overflow_edges",
            src: include_str!("bridge_corpus/alloc_capacity_overflow_edges.rs"),
            rlib: None,
            strategies: BOTH,
            rows: OVERFLOW_ROWS,
            policy: Policy::Must,
        },
        4 * 2 * OVERFLOW_ROWS.len(),
    );
}
