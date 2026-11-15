#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native_prerequisites;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: every failed MIR `Assert` — every `AssertKind` rustc emits
// that the bridge can reach — must behave exactly as LLVM's binary: call the
// exact panic entry rustc's codegen calls (`panic_bounds_check(index, len)`,
// `panic_const_*_overflow`, `panic_const_{div,rem}_by_zero`,
// `panic_misaligned_pointer_dereference(required, found)`,
// `panic_null_pointer_dereference`, `panic_null_reference_constructed`,
// `panic_invalid_enum_construction(source)`, `panic_const_coroutine_resumed`)
// with the exact payload and `#[track_caller]` Location, run the panic hook,
// then unwind (running Drops, reaching `lang_start`'s catch, or stopping at a
// nounwind frame's terminate pad) or abort.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT IT CHECKS. A failed MIR `Assert` is lowered as rustc's
// `codegen_assert_terminator` lowers it (`lower_assert_terminator` ->
// `assert_panic::emit`): a conditional branch into a failure block that calls
// the kind's own entry — chosen by `assert_panic::entry_lang_item` and checked
// against the lang item's source signature and queried `FnAbi`
// (`assert_panic::resolve_entry`) — with the payload rustc passes
// (`assert_panic::payload_operands`: `(index, len)`, `(required, found)`, the
// `u128` enum source) read only in that block, and the `#[track_caller]`
// Location of the assert's own `SourceInfo`. The call honors the entry's actual
// unwind permission and the assert's edge (`emit_diverging_panic_call`): a plain
// call for a nounwind entry, `Continue` or `panic=abort`, an `Invoke` into the
// cleanup pad, or an `Invoke` into the frame's terminate pad
// (`terminate_pad_block`: `panic_cannot_unwind` / `panic_in_cleanup`). An
// INTERCEPTED `Vec` index (`lower_vec_index`) fails through the same checked
// `panic_bounds_check(index, len)` entry
// (`assert_panic::intercepted_bounds_check_fail_target`), not a generic message.
// A by-value-returning call on a terminate edge in the same frame (`black_box`
// in an `extern "C"` fn) keeps that edge through an `Invoke` with a normal
// continuation (`terminate_edge_has_normal_continuation`,
// `push_call_with_normal_continuation`), so the frame compiles at all under
// `panic=unwind`. No failed assert becomes a trap or the generic
// `core::panicking::panic` text.
//
// THE GATE. Four fixtures, each compiled by both backends at -O0..-O3 under
// `panic=abort` and `panic=unwind`, with `-Coverflow-checks` on and off (16
// configurations), and every row run against both binaries:
//
//   * `panic_hook_index_oob.rs` — out-of-bounds array / slice / `Vec` /
//     nested indexing and stores, and the LAST trip of counted loops;
//   * `panic_assert_kinds.rs` — bounds checks (with a live `Drop` guard, in a
//     closure, in a `#[track_caller]` function, in an `extern "C"` frame that
//     cannot unwind), the eight overflow kinds (`+ - * neg << >>` fire only
//     with overflow checks; `/` and `%` overflow always), division and
//     remainder by zero, an assert MIR-inlined from an `#[inline]` helper, and
//     the loop shapes the AArch64 bounds-check eliminator decides (`v`..`y`,
//     `A`): a guard-proven check it folds next to an unproven one whose last
//     trip must still raise with the first failing index;
//   * `panic_assert_ub_check_kinds.rs` (`-Zub-checks=yes`) — misaligned and
//     null dereference, null reference, invalid enum construction (an 8-bit and
//     a 128-bit discriminant: the `u128` payload's high half is printed);
//   * `panic_assert_coroutine_kinds.rs` — resuming a finished coroutine.
//
// Each shape runs twice: with a `set_hook` closure that writes `hook` and exits
// with a code derived from the reported file / line / column (a skipped hook is
// a signal, a wrong Location a different code), and with std's DEFAULT hook,
// whose stderr carries rustc's own message and payload (a generic or wrong
// message, a wrong index / length / address, differs) and whose end — SIGABRT,
// exit 101 after unwinding, the `drop` lines a live guard prints while
// unwinding, `panic in a function that cannot unwind` — must match too. Each
// fixture's `z` row panics nowhere and exits with a checksum of the same
// functions run in range: the success paths compute LLVM's answer.
//
// The oracle is held to the row's intent first: a firing row's LLVM binary
// must leave through the hook / print the kind's message, a non-firing row
// must exit normally; otherwise the row proves nothing.
//
// The floor is EVERY row: a bridge refusal of any configuration fails the
// test. The coroutine fixture's -O0/-O1 `panic=unwind` configurations were
// refused before (`[TCG-EH-CALL-EDGE]`: the `resume` call returns its
// `CoroutineState` by value, and its cleanup edge drops the coroutine); a
// by-value lane on Darwin AArch64 now keeps such an OBSERVABLE cleanup edge
// through an `Invoke` with a normal continuation
// (`observable_cleanup_continuation`, `cleanup_edge_has_normal_continuation`),
// and its default-hook row unwinds through that pad to `lang_start`'s catch.
//
// NOT COVERED: `ResumedAfterPanic` and `catch_unwind` (the bridge does not
// lower `catch_unwind`), the `async fn` / `gen` resumed kinds (the bridge
// refuses `async fn` coroutine types), `ResumedAfterDrop` (async drop), and
// `panic=immediate-abort` (needs a rebuilt std).
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes
// `no-proof-certs` for the reason `panic_hook_differential.rs` gives; the knob
// goes to the bridge side only.
//
// FALSIFIED: see `MUTATION RESULTS` at the bottom of this file.

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["0", "1", "2", "3"];
const STRATEGIES: &[&str] = &["abort", "unwind"];
const OVERFLOW_CHECKS: &[&str] = &["on", "off"];

/// When a shape's assert fails.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fires {
    Always,
    /// An optional overflow check: present only with `-Coverflow-checks=on`;
    /// with checks off the arithmetic wraps and the row exits normally.
    WithOverflowChecks,
}

struct Shape {
    selector: &'static str,
    what: &'static str,
    fires: Fires,
    /// A substring of rustc's own message that the default hook prints.
    message: &'static str,
}

const fn always(selector: &'static str, what: &'static str, message: &'static str) -> Shape {
    Shape {
        selector,
        what,
        fires: Fires::Always,
        message,
    }
}

const fn checked(selector: &'static str, what: &'static str, message: &'static str) -> Shape {
    Shape {
        selector,
        what,
        fires: Fires::WithOverflowChecks,
        message,
    }
}

struct Fixture {
    name: &'static str,
    src: &'static str,
    flags: &'static [&'static str],
    shapes: &'static [Shape],
}

const OOB_SHAPES: &[Shape] = &[
    always(
        "a",
        "`a[i]` on a `[u32; 4]`",
        "the len is 4 but the index is 9",
    ),
    always(
        "b",
        "`s[i]` on a runtime-length slice",
        "the len is 6 but the index is 17",
    ),
    always(
        "c",
        "`v[i]` on a `Vec<u32>`",
        "the len is 3 but the index is 5",
    ),
    always("d", "`a[i] = x` store", "the len is 4 but the index is 4"),
    always(
        "e",
        "`m[i][j]` inner index",
        "the len is 3 but the index is 3",
    ),
    always(
        "f",
        "last trip of a counted array loop",
        "the len is 8 but the index is 8",
    ),
    always(
        "g",
        "last trip of a counted slice loop",
        "the len is 12 but the index is 12",
    ),
    always(
        "h",
        "last trip of a counted `Vec` store loop",
        "the len is 12 but the index is 12",
    ),
    always(
        "i",
        "`v[i]` on a `Vec<u32>` inside an `extern \"C\"` fn",
        "the len is 3 but the index is 3",
    ),
    always(
        "j",
        "`v[i] = x` on a `Vec<u32>` inside an `extern \"C\"` fn",
        "the len is 3 but the index is 4",
    ),
];

const KIND_SHAPES: &[Shape] = &[
    always(
        "a",
        "array index, live Drop guard",
        "the len is 4 but the index is 9",
    ),
    always(
        "b",
        "slice index, live Drop guard",
        "the len is 12 but the index is 17",
    ),
    always("c", "`Vec` index", "the len is 3 but the index is 5"),
    always("e", "nested array index", "the len is 3 but the index is 3"),
    always(
        "g",
        "last trip of a counted slice loop",
        "the len is 12 but the index is 12",
    ),
    checked("f", "`u32 + u32` overflow", "attempt to add with overflow"),
    checked(
        "h",
        "`u64 - u64` overflow",
        "attempt to subtract with overflow",
    ),
    checked(
        "i",
        "`i32 * i32` overflow",
        "attempt to multiply with overflow",
    ),
    checked("j", "`-i32::MIN`", "attempt to negate with overflow"),
    checked("k", "`u32 << 40`", "attempt to shift left with overflow"),
    checked("l", "`u64 >> 70`", "attempt to shift right with overflow"),
    always("m", "`i32::MIN / -1`", "attempt to divide with overflow"),
    always(
        "n",
        "`i64::MIN % -1`",
        "attempt to calculate the remainder with overflow",
    ),
    always("o", "`u32 / 0`", "attempt to divide by zero"),
    always(
        "p",
        "`i16 % 0`",
        "attempt to calculate the remainder with a divisor of zero",
    ),
    always(
        "q",
        "index in a `#[track_caller]` fn (caller's Location)",
        "the len is 12 but the index is 40",
    ),
    always(
        "r",
        "`/ 0` MIR-inlined from an `#[inline]` helper, live Drop guard",
        "attempt to divide by zero",
    ),
    always(
        "s",
        "index in an `extern \"C\"` frame (terminate edge)",
        "the len is 3 but the index is 3",
    ),
    always(
        "u",
        "index in a closure",
        "the len is 12 but the index is 12",
    ),
    always(
        "v",
        "`while i < n` over a `[u32; 8]` after a guard-proven `while j < a.len()`",
        "the len is 8 but the index is 8",
    ),
    always(
        "w",
        "`while k < n` over a slice after a `while k < s.len()`",
        "the len is 12 but the index is 12",
    ),
    always(
        "x",
        "`while i < n` over a `[u32; 4096]` after a guard-proven `while j < 4096`",
        "the len is 4096 but the index is 4096",
    ),
    always(
        "y",
        "byte index: a `[u32; 256]` table (proven) then a `[u32; 255]` one",
        "the len is 255 but the index is 255",
    ),
    always(
        "A",
        "`while k < a.len()` indexing a shorter `Vec` `b`",
        "the len is 12 but the index is 12",
    ),
];

const UB_CHECK_SHAPES: &[Shape] = &[
    always(
        "a",
        "misaligned `*const u32` read",
        "misaligned pointer dereference: address must be a multiple of 0x4 but is 0x1001",
    ),
    always(
        "b",
        "null `*const u64` read",
        "null pointer dereference occurred",
    ),
    always("c", "`&*p` with a null `p`", "null reference produced"),
    always(
        "e",
        "invalid `repr(u8)` enum",
        "trying to construct an enum from an invalid value 0x7\n",
    ),
    always(
        "f",
        "invalid `repr(u128)` enum",
        "trying to construct an enum from an invalid value 0x123456789abcdef00fedcba987654321",
    ),
];

const COROUTINE_SHAPES: &[Shape] = &[always(
    "a",
    "resume a finished coroutine",
    "coroutine resumed after completion",
)];

fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            name: "panic_hook_index_oob",
            src: include_str!("bridge_corpus/panic_hook_index_oob.rs"),
            flags: &[],
            shapes: OOB_SHAPES,
        },
        Fixture {
            name: "panic_assert_kinds",
            src: include_str!("bridge_corpus/panic_assert_kinds.rs"),
            flags: &[],
            shapes: KIND_SHAPES,
        },
        Fixture {
            name: "panic_assert_ub_check_kinds",
            src: include_str!("bridge_corpus/panic_assert_ub_check_kinds.rs"),
            flags: &["-Zub-checks=yes"],
            shapes: UB_CHECK_SHAPES,
        },
        Fixture {
            name: "panic_assert_coroutine_kinds",
            src: include_str!("bridge_corpus/panic_assert_coroutine_kinds.rs"),
            flags: &[],
            shapes: COROUTINE_SHAPES,
        },
    ]
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Exited {
        code: i32,
        stdout: String,
        stderr: String,
    },
    Signalled {
        signal: i32,
        stdout: String,
        stderr: String,
    },
}

impl Outcome {
    fn stderr(&self) -> &str {
        match self {
            Outcome::Exited { stderr, .. } | Outcome::Signalled { stderr, .. } => stderr,
        }
    }
}

fn skip_without_prerequisites(test: &str) -> bool {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        darwin_native_prerequisites::require(test, &[]);
        false
    }
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    {
        toolchain_support::skip_without_backend_knobs(test)
    }
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_assert_kinds_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

#[derive(Clone, Copy)]
struct Config {
    opt: &'static str,
    strategy: &'static str,
    overflow_checks: &'static str,
}

impl Config {
    fn label(&self) -> String {
        format!(
            "-O{} panic={} overflow-checks={}",
            self.opt, self.strategy, self.overflow_checks
        )
    }
}

/// Compile `fixture` as a std binary under `config`, with the bridge when
/// `backend` is `Some`. `Err` carries the compiler's stderr.
fn compile(
    dir: &Path,
    fixture: &Fixture,
    config: Config,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let lane = if backend.is_some() { "bridge" } else { "llvm" };
    let bin = dir.join(format!("{}_{lane}", fixture.name));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={}", config.opt))
        .arg(format!("-Cpanic={}", config.strategy))
        .arg(format!("-Coverflow-checks={}", config.overflow_checks))
        .args(fixture.flags);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    // Compile from inside `dir` with a relative source path, so the Location
    // file name the hook folds into its exit code is the same short string
    // for both backends.
    cmd.current_dir(dir)
        .arg("-o")
        .arg(&bin)
        .arg(format!("{}.rs", fixture.name));
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

/// The default hook prints `thread 'main' (<tid>) panicked at …`, and the
/// `panic_cannot_unwind` abort prints a forced backtrace of addresses and
/// symbols: both differ between ANY two binaries, so the thread id and the
/// backtrace frame lines are dropped before comparing. The messages, the
/// Locations and every other line are kept.
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

fn run(bin: &Path, selector: &str) -> Outcome {
    let out = Command::new(bin)
        .env("PANIC_SHAPE", selector)
        .output()
        .expect("run compiled binary");
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = normalize_stderr(&out.stderr);
    if let Some(code) = out.status.code() {
        return Outcome::Exited {
            code,
            stdout,
            stderr,
        };
    }
    #[cfg(unix)]
    let signal = std::os::unix::process::ExitStatusExt::signal(&out.status).unwrap_or(-1);
    #[cfg(not(unix))]
    let signal = -1;
    Outcome::Signalled {
        signal,
        stdout,
        stderr,
    }
}

/// Hold the LLVM oracle to the row's intent: a firing row must leave through
/// the custom hook (`hook` on stdout, an exit code) or print the kind's
/// message through the default hook; a non-firing row must exit normally with
/// the program's checksum.
fn check_oracle(label: &str, want: &Outcome, fires: bool, default_hook: bool, message: &str) {
    if !fires {
        match want {
            Outcome::Exited { code, stdout, .. } => {
                assert!(
                    (1..=200).contains(code) && !stdout.contains("hook"),
                    "{label}: the LLVM oracle's no-panic exit is not a checksum: {want:?}"
                );
            }
            _ => panic!("{label}: the LLVM oracle died by a signal on a no-panic row: {want:?}"),
        }
        return;
    }
    if default_hook {
        assert!(
            want.stderr().contains("panicked at") && want.stderr().contains(message),
            "{label}: the LLVM oracle's default hook did not print rustc's message \
             {message:?}: {want:?}"
        );
    } else {
        match want {
            Outcome::Exited { stdout, .. } => assert_eq!(
                stdout, "hook\n",
                "{label}: the LLVM oracle exited without running the set_hook closure"
            ),
            _ => panic!(
                "{label}: the LLVM oracle died by a signal; the fixture is not exercising the \
                 hook: {want:?}"
            ),
        }
    }
}

struct Tally {
    total: usize,
    matched: usize,
    failures: Vec<String>,
}

fn run_config(dylib: &Path, fixture: &Fixture, config: Config, tally: &mut Tally) {
    let rows = 2 * fixture.shapes.len() + 1;
    tally.total += rows;
    let dir = workdir(&format!(
        "{}_O{}_{}_{}",
        fixture.name, config.opt, config.strategy, config.overflow_checks
    ));
    std::fs::write(dir.join(format!("{}.rs", fixture.name)), fixture.src).expect("write source");
    let (oracle, bridge) = std::thread::scope(|scope| {
        let oracle = scope.spawn(|| compile(&dir, fixture, config, None));
        let bridge = scope.spawn(|| compile(&dir, fixture, config, Some(dylib)));
        (
            oracle.join().expect("oracle compile thread"),
            bridge.join().expect("bridge compile thread"),
        )
    });
    let label = format!("{} {}", fixture.name, config.label());
    let oracle = oracle.unwrap_or_else(|e| panic!("{label}: LLVM oracle failed: <<<{e}>>>"));
    let bridge = match bridge {
        Ok(bin) => bin,
        Err(stderr) => {
            tally.failures.push(format!(
                "{label}: the bridge REFUSED the fixture, so {rows} row(s) never ran: <<<{}>>>",
                stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
            ));
            let _ = std::fs::remove_dir_all(&dir);
            return;
        }
    };
    let mut selectors: Vec<(String, bool, bool, &str, String)> = Vec::new();
    for shape in fixture.shapes {
        let fires = shape.fires == Fires::Always || config.overflow_checks == "on";
        selectors.push((
            shape.selector.to_owned(),
            fires,
            false,
            shape.message,
            format!("{}, set_hook", shape.what),
        ));
        selectors.push((
            format!("{}d", shape.selector),
            fires,
            true,
            shape.message,
            format!("{}, default hook", shape.what),
        ));
    }
    selectors.push((
        "z".to_owned(),
        false,
        false,
        "",
        "no panic (control)".to_owned(),
    ));
    for (selector, fires, default_hook, message, what) in selectors {
        let row = format!("{label} PANIC_SHAPE={selector}: {what}");
        let want = run(&oracle, &selector);
        check_oracle(&row, &want, fires, default_hook, message);
        let got = run(&bridge, &selector);
        if got == want {
            tally.matched += 1;
        } else {
            tally
                .failures
                .push(format!("{row}: LLVM {want:?} vs bridge {got:?}"));
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn every_failed_assert_calls_rustcs_panic_entry_like_llvm() {
    const TEST: &str = "every_failed_assert_calls_rustcs_panic_entry_like_llvm";
    if skip_without_prerequisites(TEST) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut tally = Tally {
        total: 0,
        matched: 0,
        failures: Vec::new(),
    };
    for fixture in fixtures() {
        for &opt in OPT_LEVELS {
            for &strategy in STRATEGIES {
                for &overflow_checks in OVERFLOW_CHECKS {
                    let config = Config {
                        opt,
                        strategy,
                        overflow_checks,
                    };
                    run_config(&dylib, &fixture, config, &mut tally);
                }
            }
        }
    }
    // 16 configurations x (17 + 49 + 11 + 3) rows.
    assert_eq!(tally.total, 1344, "the assert-kind row denominator changed");
    eprintln!(
        "assert-kind panic rows: {}/{} matched LLVM",
        tally.matched, tally.total
    );
    for failure in &tally.failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        tally.failures.is_empty() && tally.matched == tally.total,
        "{} of {} assert-kind rows diverged from LLVM or never ran. A signal where LLVM \
         exits through the hook skipped the hook; a different exit code is a different \
         Location; a different stderr is a different message or payload; a missing `drop` \
         line is a skipped cleanup. Failures: {:#?}",
        tally.total - tally.matched,
        tally.total,
        tally.failures
    );
    // The Darwin gate's execution marker: printed only on the asserted success
    // path, so a different split of the denominator is a reviewed edit there.
    println!(
        "ASSERT_PANIC_KIND_ROWS fixtures=4 configs=16 rows={} matched={} refused=0",
        tally.total, tally.matched
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// MUTATION RESULTS (2026-10-01, aarch64-apple-darwin). Each mutant is the
// fixed backend with one capability reverted, built as this test's backend and
// run through this test; the fixed tree passes 1280/1280.
//
//   * `lower_vec_index` failing through the generic-message
//     `intercepted_bounds_check_fail_target` instead of
//     `assert_panic::intercepted_bounds_check_fail_target`: 1248/1280 — the
//     default-hook rows of the intercepted `Vec` indexes (`panic_hook_index_
//     oob.rs` `cd`, `hd`; `panic_assert_kinds.rs` `cd`, `Ad`) at -O0/-O1 x
//     abort/unwind x overflow checks on/off print "index out of bounds" with
//     no "the len is .. but the index is ..".
//   * that route passing `(len, index)`: 1264/1280 — the `cd` default-hook
//     rows of both fixtures at -O0/-O1 print "the len is 5 but the index is 3"
//     (`hd` / `Ad` fail at index == len, so the swap is invisible there).
//   * `assert_panic::payload_operands` returning a MIR bounds check's payload
//     as `(len, index)`: 1184/1280 — the default-hook `ad`, `bd`, `qd` rows of
//     `panic_assert_kinds.rs` and `ad`, `bd` of `panic_hook_index_oob.rs` in all
//     16 configurations, and both fixtures' `cd` at -O2/-O3 (where the `Vec`
//     index is a MIR assert after inlining).
//   * `terminate_edge_has_normal_continuation` false (a by-value call on a
//     terminate edge stays a plain call): 1084/1280 — `panic_assert_kinds.rs`
//     is refused at -O0/-O1 under `panic=unwind` (`nounwind_index`'s
//     `black_box::<[u64; 3]>` call: "[TCG-EH-CALL-EDGE] a call with a
//     terminate unwind edge was lowered without its terminate pad"), 196 rows.
//   * `emit_diverging_panic_call` lowering a `Terminate` edge as a plain call
//     (no terminate pad): 1272/1280 — row `sd` under `panic=unwind` at every
//     opt level exits 101 after walking past the `extern "C"` frame, where LLVM
//     aborts after "panic in a function that cannot unwind".
//   * `cleanup_edge_has_normal_continuation` false: 1268/1280 —
//     `panic_assert_coroutine_kinds.rs` is refused at -O0/-O1 under
//     `panic=unwind` ("[TCG-EH-CALL-EDGE] ... the call to
//     `resumed_after_return::{closure#0}` has an unwind cleanup edge into bb20"),
//     12 rows.
//   * `InvalidEnumConstruction` removed from `assert_panic::entry_lang_item`:
//     1104/1280 — `panic_assert_ub_check_kinds.rs` is refused in all 16
//     configurations ("[TCG-ASSERT-PANIC] InvalidEnumConstruction(..):
//     unsupported MIR panic kind"), 176 rows.
