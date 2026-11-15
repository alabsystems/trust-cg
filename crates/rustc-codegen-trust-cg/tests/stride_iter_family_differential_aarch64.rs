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

// The slice chunk/window iterator family against LLVM: stdout, exit status and
// panic stderr.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE DEFECT. The bridge intercepts `<[T]>::{windows, chunks, chunks_exact,
// rchunks, rchunks_exact}` and their `next` for a scalar `T`. Until 2026-10-04
// its constructor wrote a private `{ ptr@0, end@8, n@16, rem_data@24,
// rem_len@32 }` cursor into the iterator's slot. At -O2/-O3 rustc's MIR inliner
// turns std's methods into field projections of that slot — `count()` becomes
// `PtrMetadata(it.v) / it.chunk_size`, an inlined `next` splits `it.v` — and
// those read the private words as std's `{ v: &[T], rem: &[T], chunk_size }`.
// MEASURED on origin/main 4e80a288e (aarch64-apple-darwin, no-proof-certs):
// `[1u8, 2, 3].chunks_exact(black_box(2)).count()` exited 80 at -O2 and 96 at
// -O3 where LLVM exits 1, and a `for c in [1u32, 2, 3].rchunks_exact(2)` sum
// exited 138/139 (stack garbage) where LLVM exits 4. The bridge now writes
// std's own state at rustc's offsets (`SliceStrideIterLayout`).
//
// THE GATE. Four fixtures (tests/stride_iter_family/), each compiled by both
// backends at -O0..-O3 under panic=abort and panic=unwind (32 cells):
//
//   * `loops.rs` — `for`/`next`/`len`/`size_hint`/`last`/`nth`/`rev`/
//     `next_back`/`nth_back`/`enumerate`/`skip`/`remainder`/`into_remainder`
//     over all nine chunk and window iterators (`_mut` ones writing through
//     their chunks), for u8/u32/u64 and two structs (8 and 3 bytes), slice
//     lengths 0..=9 and sizes 1..=4. Every cell must build and match.
//   * `others.rs` — `as_chunks`/`as_rchunks`/`as_chunks_mut` and
//     `chunk_by`/`chunk_by_mut`, whose `next` builds a `windows(2)` iterator
//     inside core (over scalar elements that refused as
//     [TCG-STRIDE-ITER-INLINE] at every level before). Every cell must build
//     and match. (The slice `split` family is not here:
//     its `next` refuses before and after this change, on capturing-closure
//     `position` and `try_fold` drives this lane does not touch.)
//   * `counts.rs` — `count()` of the nine iterators: the reported -O2/-O3
//     miscompile. -O2/-O3 must build and match; -O0/-O1 refuse with
//     [TCG-ITER-UNMODELED] (the `count` terminal over a source the chain
//     driver does not model), never a wrong value.
//   * `zero.rs` — a zero chunk or window size, one run per constructor: std's
//     default hook must print std's message and the caller Location, then the
//     process aborts or unwinds out of `main`. A synthesized message line
//     would be counted; since the bridge raises std's own entries (OD-170,
//     the MIR-inlined `expect_failed` of `windows(0)` at -O2/-O3 included)
//     there are none, and the count is pinned at zero.
//
// The LLVM oracle is held to the fixture's intent (every row, a clean exit and
// an empty stderr; or `before`, std's message and the strategy's death), so a
// vacuous oracle cannot pass.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::time::Duration;

const TARGET: &str = "aarch64-apple-darwin";
const OPTS: [u32; 4] = [0, 1, 2, 3];
const STRATEGIES: [&str; 2] = ["abort", "unwind"];
/// Slice lengths 0..=9 times sizes 1..=4.
const ROWS_PER_SHAPE_TYPE: usize = 40;
/// Five element types per shape (u8, u32, u64, P, Q).
const TYPES: usize = 5;
/// The bound on one run of a fixture binary. A run takes well under a second;
/// the first execution of a freshly linked binary on this host can spend about
/// ten seconds in the system's scan before it starts.
const RUN_LIMIT: Duration = Duration::from_secs(120);

/// What a cell must do at one opt level.
#[derive(Clone, Copy)]
enum Expect {
    /// Build with the bridge and match LLVM on every run.
    Match,
    /// Refuse to build, naming each of these codes and nothing worse.
    Refuse(&'static [&'static str]),
}

struct Fixture {
    name: &'static str,
    src: &'static str,
    /// The `STRIDE_ZERO` values to run with (`None`: one run, no selector).
    selectors: &'static [Option<&'static str>],
    /// How many `s_<shape>` row functions the fixture prints (LLVM must print
    /// `shapes * TYPES * ROWS_PER_SHAPE_TYPE` lines); `None` for `zero.rs`.
    shapes: Option<usize>,
    expect: fn(u32) -> Expect,
}

fn always_match(_: u32) -> Expect {
    Expect::Match
}

fn counts_expect(opt: u32) -> Expect {
    if opt < 2 {
        Expect::Refuse(&["TCG-ITER-UNMODELED"])
    } else {
        Expect::Match
    }
}

const ZERO_SELECTORS: &[Option<&str>] = &[
    Some("a"),
    Some("b"),
    Some("c"),
    Some("d"),
    Some("e"),
    Some("f"),
    Some("g"),
    Some("h"),
    Some("i"),
];

fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            name: "loops",
            src: include_str!("stride_iter_family/loops.rs"),
            selectors: &[None],
            shapes: Some(91),
            expect: always_match,
        },
        Fixture {
            name: "others",
            src: include_str!("stride_iter_family/others.rs"),
            selectors: &[None],
            shapes: Some(7),
            expect: always_match,
        },
        Fixture {
            name: "counts",
            src: include_str!("stride_iter_family/counts.rs"),
            selectors: &[None],
            shapes: Some(9),
            expect: counts_expect,
        },
        Fixture {
            name: "zero",
            src: include_str!("stride_iter_family/zero.rs"),
            selectors: ZERO_SELECTORS,
            shapes: None,
            expect: always_match,
        },
    ]
}

fn compile(
    dir: &Path,
    fixture: &Fixture,
    opt: u32,
    strategy: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let lane = if backend.is_some() { "bridge" } else { "llvm" };
    let exe = dir.join(format!("{}_{lane}", fixture.name));
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .args([
            "--target",
            TARGET,
            "--crate-type",
            "bin",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Cpanic={strategy}"));
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        command
            .arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    // A relative source path keeps the panic Location's file name the same
    // short string for both backends.
    command
        .current_dir(dir)
        .arg("-o")
        .arg(&exe)
        .arg(format!("{}.rs", fixture.name));
    let output = command.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(exe)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// One run: exit code, signal, stdout, and stderr with the thread id dropped.
#[derive(Debug, PartialEq)]
struct Run {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    stderr: String,
}

/// std's default hook prints `thread 'main' (<tid>) panicked at …`; the thread
/// id differs between any two processes, so it is dropped. Every other byte,
/// the Location and the message included, is kept.
fn normalize_stderr(stderr: &[u8]) -> String {
    let text = String::from_utf8_lossy(stderr);
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
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

/// One bounded run; `Err` is a run killed at [`RUN_LIMIT`].
fn run(exe: &Path, selector: Option<&str>) -> Result<Run, String> {
    let mut command = Command::new(exe);
    match selector {
        Some(value) => command.env("STRIDE_ZERO", value),
        None => command.env_remove("STRIDE_ZERO"),
    };
    match darwin_native::run_with_deadline(&mut command, RUN_LIMIT) {
        Ok(output) => Ok(Run {
            code: output.status.code(),
            signal: std::os::unix::process::ExitStatusExt::signal(&output.status),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: normalize_stderr(&output.stderr),
        }),
        Err(output) => Err(format!(
            "killed after {RUN_LIMIT:?} with {} stdout lines",
            String::from_utf8_lossy(&output.stdout).lines().count()
        )),
    }
}

/// The message std's constructor panics with for `zero.rs` selector `selector`.
fn zero_message(selector: Option<&str>) -> &'static str {
    if selector == Some("e") {
        "window size must be non-zero"
    } else {
        "chunk size must be non-zero"
    }
}

/// Hold the LLVM oracle to the fixture's intent.
fn check_oracle(
    label: &str,
    fixture: &Fixture,
    strategy: &str,
    selector: Option<&str>,
    want: &Run,
) {
    match fixture.shapes {
        Some(shapes) => {
            assert_eq!(
                (want.code, want.stdout.lines().count(), want.stderr.as_str()),
                (Some(0), shapes * TYPES * ROWS_PER_SHAPE_TYPE, ""),
                "{label}: the LLVM oracle did not print every row and exit 0"
            );
        }
        None => {
            let message = zero_message(selector);
            assert!(
                want.stdout == "before\n"
                    && want.stderr.contains("panicked at zero.rs:")
                    && want.stderr.lines().any(|line| line == message),
                "{label}: the LLVM oracle's zero-size row did not panic with {message:?}: {want:?}"
            );
            let died = if strategy == "abort" {
                want.signal == Some(6)
            } else {
                want.code == Some(101)
            };
            assert!(
                died,
                "{label}: the LLVM oracle did not {strategy}: {want:?}"
            );
        }
    }
}

/// The bridge's documented stand-in for a panic message it does not lower: a
/// diverging call to a precompiled std `#[track_caller]` panic helper (here
/// `Option::expect`'s `expect_failed`, MIR-inlined from `windows` at -O2/-O3)
/// raises with this text, the real caller Location and the real hook and
/// unwind behavior (`lower_direct_call_terminator_lanes`, "the accepted
/// cosmetic class").
fn is_synthesized_message(line: &str) -> bool {
    line.starts_with("panic raised via `") && line.ends_with("` (message not lowered by trust-cg)")
}

/// Compare a bridge run with the oracle's: exit status and stdout exactly,
/// stderr line by line except a message line the bridge synthesized (counted).
/// `Err` names the first difference.
fn compare(want: &Run, got: &Run, synthesized: &mut usize) -> Result<(), String> {
    if (want.code, want.signal) != (got.code, got.signal) {
        return Err(format!(
            "LLVM exit {:?} signal {:?} vs bridge exit {:?} signal {:?}",
            want.code, want.signal, got.code, got.signal
        ));
    }
    for (name, a, b) in [
        ("stdout", &want.stdout, &got.stdout),
        ("stderr", &want.stderr, &got.stderr),
    ] {
        let (mut left, mut right) = (a.lines(), b.lines());
        for index in 0.. {
            match (left.next(), right.next()) {
                (None, None) => break,
                (Some(x), Some(y)) if x == y => {}
                (Some(_), Some(y)) if name == "stderr" && is_synthesized_message(y) => {
                    *synthesized += 1;
                }
                (x, y) => {
                    return Err(format!("{name} line {index}: LLVM {x:?} vs bridge {y:?}"));
                }
            }
        }
    }
    Ok(())
}

#[derive(Default)]
struct Tally {
    cells: usize,
    matched_cells: usize,
    refused_cells: usize,
    runs: usize,
    rows: usize,
    synthesized: usize,
    failures: Vec<String>,
}

fn run_cell(
    root: &Path,
    backend: &Path,
    fixture: &Fixture,
    opt: u32,
    strategy: &str,
    tally: &Mutex<Tally>,
) {
    let label = format!("{} -O{opt} panic={strategy}", fixture.name);
    let dir = root.join(format!("{}_O{opt}_{strategy}", fixture.name));
    std::fs::create_dir_all(&dir).expect("cell dir");
    std::fs::write(dir.join(format!("{}.rs", fixture.name)), fixture.src).expect("write fixture");
    let (oracle, bridge) = std::thread::scope(|scope| {
        let oracle = scope.spawn(|| compile(&dir, fixture, opt, strategy, None));
        let bridge = scope.spawn(|| compile(&dir, fixture, opt, strategy, Some(backend)));
        (
            oracle.join().expect("oracle compile thread"),
            bridge.join().expect("bridge compile thread"),
        )
    });
    let oracle = oracle.unwrap_or_else(|e| panic!("{label}: the LLVM oracle failed: <<<{e}>>>"));
    let mut failures = Vec::new();
    let mut matched = false;
    let mut refused = false;
    let mut runs = 0;
    let mut rows = 0;
    let mut synthesized = 0;
    match ((fixture.expect)(opt), bridge) {
        (Expect::Match, Ok(bridge)) => {
            matched = true;
            for selector in fixture.selectors {
                let row = format!("{label} STRIDE_ZERO={selector:?}");
                let want = run(&oracle, *selector)
                    .unwrap_or_else(|e| panic!("{row}: the LLVM oracle's run was {e}"));
                check_oracle(&row, fixture, strategy, *selector, &want);
                runs += 1;
                rows += want.stdout.lines().count();
                let compared =
                    run(&bridge, *selector).and_then(|got| compare(&want, &got, &mut synthesized));
                if let Err(difference) = compared {
                    matched = false;
                    failures.push(format!("{row}: {difference}"));
                }
            }
        }
        (Expect::Match, Err(stderr)) => failures.push(format!(
            "{label}: the bridge REFUSED a fixture that must build: <<<{}>>>",
            stderr.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
        )),
        (Expect::Refuse(codes), Err(stderr)) => {
            let errors: Vec<&str> = stderr
                .lines()
                .map(str::trim)
                .filter(|line| line.starts_with("- "))
                .collect();
            let named = !errors.is_empty()
                && errors
                    .iter()
                    .all(|line| codes.iter().any(|code| line.contains(&format!("[{code}]"))));
            if named {
                refused = true;
            } else {
                failures.push(format!(
                    "{label}: expected only {codes:?} refusals, got: <<<{}>>>",
                    stderr.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
                ));
            }
        }
        (Expect::Refuse(codes), Ok(_)) => failures.push(format!(
            "{label}: expected a {codes:?} refusal, but the bridge built the fixture; if it now \
             matches LLVM, move this cell to Expect::Match (a reviewed denominator change)"
        )),
    }
    let _ = std::fs::remove_dir_all(&dir);
    let mut tally = tally.lock().expect("tally");
    tally.cells += 1;
    tally.matched_cells += usize::from(matched);
    tally.refused_cells += usize::from(refused);
    tally.runs += runs;
    tally.rows += rows;
    tally.synthesized += synthesized;
    tally.failures.extend(failures);
}

#[test]
fn slice_chunk_and_window_iterators_match_llvm_or_refuse_by_name() {
    darwin_native::require("stride_iter_family_differential_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    let root = std::env::temp_dir().join(format!("tcg_stride_family_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let fixtures = fixtures();
    let mut cells = Vec::new();
    for fixture in &fixtures {
        for opt in OPTS {
            for strategy in STRATEGIES {
                cells.push((fixture, opt, strategy));
            }
        }
    }
    let queue = Mutex::new(cells);
    let tally = Mutex::new(Tally::default());
    // Each cell runs two compilers at once; four cells at a time.
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| {
                loop {
                    let next = queue.lock().expect("queue").pop();
                    let Some((fixture, opt, strategy)) = next else {
                        break;
                    };
                    run_cell(&root, &backend, fixture, opt, strategy, &tally);
                }
            });
        }
    });
    let _ = std::fs::remove_dir_all(&root);
    let tally = tally.into_inner().expect("tally");
    for failure in &tally.failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        tally.failures.is_empty(),
        "{} of {} stride-family cells diverged from LLVM or from their expected refusal: {:#?}",
        tally.failures.len(),
        tally.cells,
        tally.failures
    );
    // 4 fixtures x 4 opt levels x 2 strategies; `counts.rs` refuses at -O0/-O1.
    assert_eq!(
        (tally.cells, tally.matched_cells, tally.refused_cells),
        (32, 28, 4),
        "the stride-family cell denominator changed"
    );
    // Runs: one per matching cell of the three row fixtures, nine per zero
    // cell. Rows (stdout lines): (91 + 7) shapes x 5 types x 40 x 8 cells,
    // 9 x 5 x 40 x 4 cells, and one `before` line per zero-size run. Every
    // zero-size run prints std's exact message: the MIR-inlined
    // `expect_failed` of `windows(0)` at -O2/-O3 is std's own entry since the
    // bridge raises std's panics for real (OD-170), so no line is synthesized.
    assert_eq!(
        (tally.runs, tally.rows, tally.synthesized),
        (8 + 8 + 4 + 72, 156_800 + 7_200 + 72, 0),
        "the stride-family row denominator changed"
    );
    // The Darwin gate's execution marker: printed only on the asserted success path.
    println!(
        "STRIDE_ITER_FAMILY fixtures=4 cells={} matched={} refused={} runs={} rows={} \
         synthesized_messages={} opts=0,1,2,3 strategies=abort,unwind",
        tally.cells,
        tally.matched_cells,
        tally.refused_cells,
        tally.runs,
        tally.rows,
        tally.synthesized
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// MUTATION RESULTS (2026-10-04, aarch64-apple-darwin). Each row is this test,
// unchanged, against a backend that differs from the fixed tree in one way.
//
//   * origin/main 4e80a288e (the private cursor): 32 failures. `counts` at
//     -O2/-O3 dies (SIGABRT, or exit 101) where LLVM exits 0; `windows(0)` at
//     -O0/-O1 prints "chunk size must be non-zero"; every `loops` and `others`
//     cell, `counts` at -O0/-O1 and `zero` at -O2/-O3 refuse with
//     [TCG-STRIDE-ITER-METHOD] or [TCG-STRIDE-ITER-INLINE].
//   * the `ChunksExact` constructor leaving the remainder in `v`: 20 failures.
//     The constructor refinement lane refutes it at compile time in every cell
//     that builds a scalar `ChunksExact` (`loops`, `counts` at -O2/-O3, `zero`).
//   * `RChunks::next` without its `saturating_sub`: 8 failures, `loops` aborts in
//     every cell.
