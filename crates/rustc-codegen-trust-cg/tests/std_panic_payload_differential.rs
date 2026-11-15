#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native_prerequisites;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a panic std raises — through a call the bridge INTERCEPTS
// (replaces with its own lowering), a panic entry a bridge-compiled body CALLS,
// or a debug-assertion precondition check — must reach the hook exactly as
// under LLVM: std's own payload TEXT and TYPE (`&'static str` for a literal
// message, `String` for a formatted one) and std's own `#[track_caller]`
// Location, then the same abort or unwind. No synthesized message, no
// substituted Location, no trap in place of the hook.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT IT CHECKS. Three fixtures:
//
//   * `std_panic_intercepted.rs` — the failure edge of every interception
//     that checks a precondition (`std_panic_route::fail_target`): `Vec` /
//     array / `str` range indexing (`slice_index_fail`, `slice_error_fail`),
//     `<[T]>::split_at[_mut]` (`panic!("mid > len")`), `str::split_at[_mut]`
//     (`slice_error_fail(self, 0, mid)`, past the end and inside a char,
//     through `String`'s deref and a `#[track_caller]` wrapper), `Vec::insert` / `remove` /
//     `split_off` (their `#[track_caller]` `assert_failed`), `swap_remove`
//     (an untracked `assert_failed`: a Location inside alloc),
//     `extend_from_within` and `drain` (`into_slice_range`'s end and start
//     sites, each at its own Location inside core), `<[T]>::swap` (the second
//     index's MIR bounds check), `rotate_left` / `rotate_right` (an untracked
//     `assert!`), `chunks` / `chunks_exact` / `windows` (`assert!` /
//     `expect`), and `Iterator::sum` / `product` over `u8` (the overflow
//     assertion of std's `#[rustc_inherit_overflow_checks]` closure in
//     `accum.rs`);
//   * `std_panic_calls.rs` — panic calls in bridge-compiled bodies: formatted
//     `panic!` / `assert!` / `assert_eq!` / `assert_ne!` / `unreachable!`,
//     `panic!("{}", x)` (`panic_display`), `Option` / `Result` `unwrap` /
//     `expect`, `u32::pow` and `ilog2` (core's own overflow / argument
//     helpers), `copy_within` (`slice_index_fail` from a compiled std body),
//     `{:?}` of a struct with a `&str` field, a tuple holding a `&str`,
//     `Option<Option<u32>>` and `Vec<u32>`, `assert_eq!` on a `Vec<u32>` (the
//     same asserts passing in the control row), and a hook that itself panics
//     with a formatted message;
//   * `std_panic_ub_checks.rs` (`-Cdebug-assertions=on`) — the
//     `panic_nounwind_fmt` of `get_unchecked`, `from_raw_parts`,
//     `unchecked_add` and `NonNull::new_unchecked` precondition checks, which
//     run the hook and abort under both strategies.
//
// Each fixture is compiled by both backends at -O0..-O3 under `panic=abort`
// and `panic=unwind` (8 configurations, overflow checks on), and every shape
// runs under each hook against both binaries:
//
//   * the OBSERVER (`std_panic_observer.rs`, compiled once per strategy by
//     LLVM and linked into both lanes' binaries, so the code that reads the
//     payload is the same in both): prints the payload's type and text and
//     the Location;
//   * a BRIDGE-compiled hook printing the Location through raw `write`;
//   * std's DEFAULT hook: message and Location on stderr;
//   * (`std_panic_calls.rs` only) a bridge-compiled hook that panics with a
//     formatted message: std prints the nested panic's Location, an EMPTY
//     message line (it prints only a literal message there) and "thread
//     panicked while processing panic. aborting." — a hook panic raised with a
//     substituted literal message prints that text instead.
//
// Stdout (hook lines, the `drop` line a live guard prints while unwinding),
// stderr (thread ids normalized, backtrace frames dropped) and the exit
// status must match. Each fixture's `z` shape panics nowhere and exits with a
// checksum of its functions run in range: the success paths compute LLVM's
// answer. The LLVM oracle is held to each row's intent first (a firing row
// prints std's message; the control exits normally).
//
// The floor is EVERY row: a bridge refusal of any configuration fails the
// test.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes
// `no-proof-certs` for the reason `panic_hook_differential.rs` gives; the knob
// goes to the bridge side only.
//
// NOT COVERED: `panic=immediate-abort` (needs a rebuilt std; the route keeps
// its trap there), wasm32 (the narrow-`usize` `Vec` index and the wasm32
// `count` / `position` overflow routes share the derived route but are not
// executed here), and `catch_unwind` (the bridge does not lower it).
//
// FALSIFIED: see `MUTATION RESULTS` at the bottom of this file.

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["0", "1", "2", "3"];
const STRATEGIES: &[&str] = &["abort", "unwind"];

struct Shape {
    selector: &'static str,
    what: &'static str,
    /// A substring of std's own message (the default hook prints it; the
    /// observer prints its debug-escaped payload).
    message: &'static str,
}

const fn shape(selector: &'static str, what: &'static str, message: &'static str) -> Shape {
    Shape {
        selector,
        what,
        message,
    }
}

/// The hooks a fixture's rows run under: `o` the LLVM-compiled observer, `b`
/// a bridge-compiled Location hook, `d` std's default hook, `p` a
/// bridge-compiled hook that panics with a formatted message.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Hook {
    Observer,
    Bridge,
    Default,
    Panicking,
}

impl Hook {
    fn env(self) -> Option<&'static str> {
        match self {
            Hook::Observer => None,
            Hook::Bridge => Some("b"),
            Hook::Default => Some("d"),
            Hook::Panicking => Some("p"),
        }
    }

    fn label(self) -> &'static str {
        match self {
            Hook::Observer => "observer hook",
            Hook::Bridge => "bridge-compiled hook",
            Hook::Default => "default hook",
            Hook::Panicking => "panicking hook",
        }
    }
}

struct Fixture {
    name: &'static str,
    src: &'static str,
    /// Flags for both lanes at `opt`.
    flags: fn(&str) -> Vec<&'static str>,
    hooks: &'static [Hook],
    shapes: &'static [Shape],
}

const INTERCEPTED_SHAPES: &[Shape] = &[
    shape(
        "a",
        "`v[a..b]` on a `Vec`, end out of range",
        "range end index 9 out of range for slice of length 4",
    ),
    shape(
        "b",
        "`v[a..b]` on a `Vec`, start after end",
        "slice index starts at 3 but ends at 2",
    ),
    shape(
        "c",
        "`v[a..]` on a `Vec`",
        "range start index 6 out of range for slice of length 4",
    ),
    shape(
        "e",
        "`v[..b]` on a `Vec`",
        "range end index 7 out of range for slice of length 4",
    ),
    shape(
        "f",
        "`a[x..y]` on a local array, end out of range",
        "range end index 8 out of range for slice of length 5",
    ),
    shape(
        "g",
        "`a[x..y]` on a local array, start after end",
        "slice index starts at 4 but ends at 1",
    ),
    shape(
        "h",
        "`s[a..b]` on a `str`, end out of bounds",
        "end byte index 9 is out of bounds",
    ),
    shape(
        "i",
        "`s[a..b]` on a `str`, not a char boundary",
        "is not a char boundary",
    ),
    shape(
        "j",
        "`s[a..b]` on a `str`, start after end",
        "byte range starts at 4 but ends at 1",
    ),
    shape(
        "k",
        "`s[a..]` on a `str`",
        "start byte index 7 is out of bounds",
    ),
    shape(
        "l",
        "`s[..b]` on a `str`, not a char boundary",
        "is not a char boundary",
    ),
    shape("m", "`<[T]>::split_at`", "mid > len"),
    shape("n", "`<[T]>::split_at_mut`", "mid > len"),
    shape(
        "o",
        "`Vec::insert`",
        "insertion index (is 5) should be <= len (is 3)",
    ),
    shape(
        "p",
        "`Vec::remove`",
        "removal index (is 3) should be < len (is 3)",
    ),
    shape(
        "q",
        "`Vec::swap_remove` (an untracked helper: a Location in alloc)",
        "swap_remove index (is 4) should be < len (is 3)",
    ),
    shape(
        "r",
        "`Vec::split_off`",
        "`at` split index (is 4) should be <= len (is 3)",
    ),
    shape(
        "s",
        "`Vec::extend_from_within`, end out of range (core's end site)",
        "range end index 6 out of range for slice of length 3",
    ),
    shape(
        "t",
        "`Vec::extend_from_within`, start after end (core's start site)",
        "slice index starts at 2 but ends at 1",
    ),
    shape(
        "u",
        "`Vec::drain(a..)` (core's start site)",
        "range start index 5 out of range for slice of length 3",
    ),
    shape(
        "v",
        "`<[T]>::swap`, second index out of bounds",
        "the len is 3 but the index is 7",
    ),
    shape(
        "w",
        "`<[T]>::swap`, first index out of bounds",
        "the len is 3 but the index is 8",
    ),
    shape(
        "x",
        "`rotate_left` (an untracked `assert!`)",
        "assertion failed: mid <= self.len()",
    ),
    shape(
        "y",
        "`rotate_right` (an untracked `assert!`)",
        "assertion failed: k <= self.len()",
    ),
    shape("A", "`chunks(0)`", "chunk size must be non-zero"),
    shape("B", "`chunks_exact(0)`", "chunk size must be non-zero"),
    shape("C", "`windows(0)`", "window size must be non-zero"),
    shape(
        "D",
        "`iter().sum::<u8>()` overflow (std's closure)",
        "attempt to add with overflow",
    ),
    shape(
        "E",
        "`iter().product::<u8>()` overflow (std's closure)",
        "attempt to multiply with overflow",
    ),
    shape(
        "F",
        "`iter().copied().sum::<u8>()` overflow (std's closure)",
        "attempt to add with overflow",
    ),
    shape(
        "G",
        "`str::split_at` past the end (`slice_error_fail`)",
        "byte index 4 is out of bounds",
    ),
    shape(
        "H",
        "`str::split_at` inside a char (`slice_error_fail`)",
        "byte index 2 is not a char boundary",
    ),
    shape(
        "I",
        "`String` deref `split_at` past the end",
        "byte index 9 is out of bounds",
    ),
    shape(
        "J",
        "`str::split_at_mut` inside a char",
        "byte index 2 is not a char boundary",
    ),
    shape(
        "K",
        "`str::split_at_mut` past the end",
        "byte index 7 is out of bounds",
    ),
    shape(
        "L",
        "`str::split_at` in a `#[track_caller]` wrapper",
        "byte index 5 is out of bounds",
    ),
];

const CALL_SHAPES: &[Shape] = &[
    shape("a", "formatted `panic!`", "bad value 9 of 3"),
    shape("b", "`panic!(\"{}\", x)` (`panic_display`)", "9"),
    shape("c", "formatted `assert!`", "x was 9"),
    shape("e", "`assert_eq!`", "assertion `left == right` failed"),
    shape("f", "formatted `assert_eq!`", "context 10"),
    shape("g", "`assert_ne!`", "assertion `left != right` failed"),
    shape("h", "formatted `unreachable!`", "x=9"),
    shape("i", "literal `unreachable!`", "entered unreachable code"),
    shape(
        "j",
        "`Option::unwrap` on `None`",
        "called `Option::unwrap()` on a `None` value",
    ),
    shape("k", "`Option::expect` on `None`", "wanted a value"),
    shape(
        "l",
        "`Result::unwrap` on `Err`",
        "called `Result::unwrap()` on an `Err` value: -5",
    ),
    shape("m", "`Result::expect` on `Err`", "wanted ok: -5"),
    shape(
        "n",
        "`u32::pow` overflow (core's helper)",
        "attempt to exponentiate with overflow",
    ),
    shape(
        "o",
        "`u32::ilog2(0)` (core's helper)",
        "argument of integer logarithm must be positive",
    ),
    shape(
        "q",
        "`copy_within` (`slice_index_fail` from std's body)",
        "range end index 9 out of range for slice of length 4",
    ),
    shape(
        "r",
        "formatted `assert!` with `{:?}` of a struct with a `&str` field",
        "bad config: Config { port: 0, host: \"h\" }",
    ),
    shape("s", "`{:?}` of a tuple holding a `&str`", "(9, \"t\", 'c')"),
    shape("t", "`{:?}` of `Option<Option<u32>>`", "Some(Some(9))"),
    shape(
        "u",
        "`assert_eq!` on a `Vec<u32>`",
        "assertion `left == right` failed\n  left: [1, 2]\n right: [1, 5]",
    ),
    shape("v", "`{:?}` of a `Vec<u32>`", "[9, 7]"),
];

const UB_CHECK_SHAPES: &[Shape] = &[
    shape(
        "a",
        "`get_unchecked` out of bounds",
        "unsafe precondition(s) violated: slice::get_unchecked requires",
    ),
    shape(
        "b",
        "`slice::from_raw_parts` of null",
        "unsafe precondition(s) violated: slice::from_raw_parts requires",
    ),
    shape(
        "c",
        "`unchecked_add` overflow",
        "unsafe precondition(s) violated: u32::unchecked_add cannot overflow",
    ),
    shape(
        "e",
        "`NonNull::new_unchecked` of null",
        "unsafe precondition(s) violated: NonNull::new_unchecked requires",
    ),
];

fn intercepted_flags(opt: &str) -> Vec<&'static str> {
    // The fixture's `chunks` / `windows` shapes iterate with `for` where the
    // bridge intercepts the constructor (-O0/-O1); see the fixture header.
    if matches!(opt, "0" | "1") {
        vec!["--cfg", "stride_loop"]
    } else {
        Vec::new()
    }
}

fn no_flags(_: &str) -> Vec<&'static str> {
    Vec::new()
}

fn ub_check_flags(_: &str) -> Vec<&'static str> {
    vec!["-Cdebug-assertions=on"]
}

fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            name: "std_panic_intercepted",
            src: include_str!("bridge_corpus/std_panic_intercepted.rs"),
            flags: intercepted_flags,
            hooks: &[Hook::Observer, Hook::Bridge, Hook::Default],
            shapes: INTERCEPTED_SHAPES,
        },
        Fixture {
            name: "std_panic_calls",
            src: include_str!("bridge_corpus/std_panic_calls.rs"),
            flags: no_flags,
            hooks: &[Hook::Observer, Hook::Bridge, Hook::Default, Hook::Panicking],
            shapes: CALL_SHAPES,
        },
        Fixture {
            name: "std_panic_ub_checks",
            src: include_str!("bridge_corpus/std_panic_ub_checks.rs"),
            flags: ub_check_flags,
            hooks: &[Hook::Observer, Hook::Bridge, Hook::Default],
            shapes: UB_CHECK_SHAPES,
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
    fn stdout(&self) -> &str {
        match self {
            Outcome::Exited { stdout, .. } | Outcome::Signalled { stdout, .. } => stdout,
        }
    }

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
    let dir = std::env::temp_dir().join(format!(
        "tcg_std_panic_payload_{stem}_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile the observer rlib with LLVM for `strategy`, once for both lanes.
fn build_observer(root: &Path, strategy: &str) -> PathBuf {
    let dir = root.join(format!("observer_{strategy}"));
    std::fs::create_dir_all(&dir).expect("create observer dir");
    std::fs::write(
        dir.join("std_panic_observer.rs"),
        include_str!("bridge_corpus/std_panic_observer.rs"),
    )
    .expect("write observer source");
    let rlib = dir.join("libpanic_observer.rlib");
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "rlib", "--crate-name", "panic_observer"])
        .arg(format!("-Cpanic={strategy}"))
        .current_dir(&dir)
        .arg("-o")
        .arg(&rlib)
        .arg("std_panic_observer.rs")
        .output()
        .expect("spawn the compiler");
    assert!(
        output.status.success(),
        "the LLVM observer rlib for panic={strategy} failed to compile: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    rlib
}

#[derive(Clone, Copy)]
struct Config {
    opt: &'static str,
    strategy: &'static str,
}

impl Config {
    fn label(&self) -> String {
        format!("-O{} panic={}", self.opt, self.strategy)
    }
}

/// Compile `fixture` as a std binary under `config`, with the bridge when
/// `backend` is `Some`. `Err` carries the compiler's stderr.
fn compile(
    dir: &Path,
    fixture: &Fixture,
    config: Config,
    observer: &Path,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let lane = if backend.is_some() { "bridge" } else { "llvm" };
    let bin = dir.join(format!("{}_{lane}", fixture.name));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={}", config.opt))
        .arg(format!("-Cpanic={}", config.strategy))
        .arg("-Coverflow-checks=on")
        .args((fixture.flags)(config.opt));
    let mut extern_arg = std::ffi::OsString::from("panic_observer=");
    extern_arg.push(observer);
    cmd.arg("--extern").arg(extern_arg);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    // Compile from inside `dir` with a relative source path, so the Location
    // file name of a fixture panic is the same short string for both backends.
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

/// The default hook prints `thread 'main' (<tid>) panicked at …`, and an
/// abort may print a forced backtrace of addresses and symbols: both differ
/// between ANY two binaries, so the thread id and the backtrace frame lines
/// are dropped before comparing. The messages, the Locations and every other
/// line are kept.
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

fn run(bin: &Path, selector: &str, hook: Hook) -> Outcome {
    let mut cmd = Command::new(bin);
    cmd.env("PANIC_SHAPE", selector).env_remove("PANIC_HOOK");
    if let Some(value) = hook.env() {
        cmd.env("PANIC_HOOK", value);
    }
    let out = cmd.output().expect("run compiled binary");
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

/// Hold the LLVM oracle to the row's intent: a firing row's hook ran and saw
/// std's message (the observer prints the payload, the default hook the
/// message); the control row exits normally with the program's checksum.
fn check_oracle(label: &str, want: &Outcome, message: Option<&str>, hook: Hook) {
    let Some(message) = message else {
        match want {
            Outcome::Exited { code, stdout, .. } => assert!(
                (1..=200).contains(code) && !stdout.contains("hook"),
                "{label}: the LLVM oracle's no-panic exit is not a checksum: {want:?}"
            ),
            _ => panic!("{label}: the LLVM oracle died by a signal on a no-panic row: {want:?}"),
        }
        return;
    };
    let intent = match hook {
        Hook::Observer => {
            // The observer prints the payload debug-escaped.
            let escaped = format!("{message:?}");
            let escaped = &escaped[1..escaped.len() - 1];
            want.stdout().starts_with("hook ") && want.stdout().contains(escaped)
        }
        Hook::Bridge => want.stdout().starts_with("bridge-hook @ "),
        Hook::Default => want.stderr().contains("panicked at") && want.stderr().contains(message),
        // std reports a panic raised while processing a panic by its Location
        // and aborts; it prints only a literal message (a formatted one, the
        // hook's, prints as an empty line).
        Hook::Panicking => want
            .stderr()
            .contains("thread panicked while processing panic. aborting."),
    };
    assert!(
        intent,
        "{label}: the LLVM oracle did not raise std's panic {message:?} through the {}: \
         {want:?}",
        hook.label()
    );
}

struct Tally {
    total: usize,
    matched: usize,
    failures: Vec<String>,
}

fn run_config(dylib: &Path, fixture: &Fixture, config: Config, observer: &Path, tally: &mut Tally) {
    let rows = (fixture.shapes.len() + 1) * fixture.hooks.len();
    tally.total += rows;
    let dir = workdir(&format!(
        "{}_O{}_{}",
        fixture.name, config.opt, config.strategy
    ));
    std::fs::write(dir.join(format!("{}.rs", fixture.name)), fixture.src).expect("write source");
    let (oracle, bridge) = std::thread::scope(|scope| {
        let oracle = scope.spawn(|| compile(&dir, fixture, config, observer, None));
        let bridge = scope.spawn(|| compile(&dir, fixture, config, observer, Some(dylib)));
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
    let mut selectors: Vec<(&str, &str, Option<&str>)> = fixture
        .shapes
        .iter()
        .map(|shape| (shape.selector, shape.what, Some(shape.message)))
        .collect();
    selectors.push(("z", "no panic (control)", None));
    for (selector, what, message) in selectors {
        for &hook in fixture.hooks {
            let row = format!("{label} PANIC_SHAPE={selector}: {what}, {}", hook.label());
            let want = run(&oracle, selector, hook);
            check_oracle(&row, &want, message, hook);
            let got = run(&bridge, selector, hook);
            if got == want {
                tally.matched += 1;
            } else {
                tally
                    .failures
                    .push(format!("{row}: LLVM {want:?} vs bridge {got:?}"));
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn std_panics_reach_the_hook_with_stds_payload_and_location_like_llvm() {
    const TEST: &str = "std_panics_reach_the_hook_with_stds_payload_and_location_like_llvm";
    if skip_without_prerequisites(TEST) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let root = workdir("observers");
    let observers: Vec<(&str, PathBuf)> = STRATEGIES
        .iter()
        .map(|&strategy| (strategy, build_observer(&root, strategy)))
        .collect();
    let mut tally = Tally {
        total: 0,
        matched: 0,
        failures: Vec::new(),
    };
    for fixture in fixtures() {
        for &opt in OPT_LEVELS {
            for (strategy, observer) in &observers {
                let config = Config { opt, strategy };
                run_config(&dylib, &fixture, config, observer, &mut tally);
            }
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    // 8 configurations x ((36 + 1) x 3 + (20 + 1) x 4 + (4 + 1) x 3) rows.
    assert_eq!(tally.total, 1680, "the std-panic row denominator changed");
    eprintln!(
        "std-panic payload rows: {}/{} matched LLVM",
        tally.matched, tally.total
    );
    for failure in &tally.failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        tally.failures.is_empty() && tally.matched == tally.total,
        "{} of {} std-panic rows diverged from LLVM or never ran. A different observer \
         line is a different payload type, text or Location; a different stderr is a \
         different message; a signal where LLVM unwinds, or a missing `drop` line, is a \
         skipped hook or cleanup. Failures: {:#?}",
        tally.total - tally.matched,
        tally.total,
        tally.failures
    );
    // The Darwin gate's execution marker: printed only on the asserted success
    // path, so a different split of the denominator is a reviewed edit there.
    println!(
        "STD_PANIC_PAYLOAD_ROWS fixtures=3 configs=8 rows={} matched={} refused=0",
        tally.total, tally.matched
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// MUTATION RESULTS (2026-10-03, aarch64-apple-darwin). Each mutant is the
// fixed backend with one capability reverted, run over this test's rows (the
// three fixtures, 8 configurations, every hook: 1376 rows before the `str`
// `split_at` and `Debug` rows were added) by a scratch replay of the same
// comparison against the self-hosted stage1 compiler; the fixed tree, built
// the same way, matches 1376/1376.
//
//   * every derived site Location replaced by the intercepted call's own
//     (`std_panic_route::fail_target` passing `SiteLocation::Caller`):
//     1208/1376 — `rotate_left` / `rotate_right`, both `extend_from_within`
//     sites, `drain` and the `Sum` / `Product` overflow rows report the
//     caller's line instead of core's.
//   * `Payload::Bound` accepting any operand: 632/1376 —
//     `std_panic_intercepted.rs` is refused in all 8 configurations
//     (`[TCG-STD-PANIC-ROUTE]`: `into_slice_range`'s `Included` and
//     `Excluded` sites disagree), 744 rows.
//   * `<[T]>::swap` always reporting the second index: 1368/1376 — row `w`
//     (observer and default hook) at -O0/-O1 reports index 7 for 8.
//   * every `#[track_caller]` panic-runtime call a panic block again, raised
//     with the entry-naming "message not lowered" text, on the base's edges
//     (a trap where the edge cannot unwind): 1048/1376 — the formatted
//     `panic!` / `assert!` / `assert_eq!` / `assert_ne!` / `unreachable!` and
//     `panic_display` rows, every precondition-check row, and every
//     panicking-hook row.
//   * the entry-naming raise for diverging std `#[track_caller]` helpers
//     restored: 840/1376 — `Option` / `Result` `unwrap` / `expect`, `pow`,
//     `ilog2`, `copy_within`, and at -O2/-O3 the range and `str` indexing and
//     `windows` that are compiled from std's body (`slice_index_fail`,
//     `slice_error_fail`, `expect_failed`).
//   * the overflow route calling the multiply entry for an add: 1352/1376 —
//     the `sum::<u8>` rows print "attempt to multiply with overflow".
//
// MUTATION RESULTS, round 2 (2026-10-04, the same replay over all 1680 rows;
// one environment-gated mutant build, which with no mutant set matches
// 1680/1680):
//
//   * `str::split_at[_mut]` routed as a constant-payload panic again (the
//     route round 1 shipped), guard kept: 792/1680 — `std_panic_intercepted.rs`
//     is refused in all 8 configurations (`[TCG-STD-PANIC-ROUTE]`: a
//     `slice_error_fail` call in `str::split_at` at depth 0, above the
//     constant site at depth 4), 888 rows.
//   * the same route with the shallower-site guard removed as well:
//     1584/1680 — rows `G` `H` `I` `L` at -O0/-O1 and `J` `K` at -O0..-O3
//     (every hook) report `is_aligned_to: align is not a power-of-two` at
//     `core/src/ptr/const_ptr.rs`, a debug-only precondition check under
//     `slice_error_fail`: the review's finding, 96 rows.
//   * the guard removed alone: 1680/1680. No route this test reaches needs it
//     once `str` names its helper; it is the refusal that turns the next such
//     route into a named error instead of a wrong message (the first mutant).
//   * the direct `<Vec<T> as Debug>::fmt` call and the `fmt::rt::Argument`
//     constructor on a `&Vec` refused again (`lower_vec_call`): 1008/1680 —
//     `std_panic_calls.rs` is refused in all 8 configurations
//     (`Vec::<u32>::fmt` / `new_debug is not an intercepted Vec method`),
//     672 rows.
//   * the address-only field borrow not admitted on aarch64 macOS:
//     1008/1680 — `std_panic_calls.rs` is refused in all 8 configurations
//     (`Config` and the tuple: `memory leaf type is a fat pointer`;
//     `Option<Option<u32>>`: `Ty::core::option::Option<u32>`), 672 rows.
