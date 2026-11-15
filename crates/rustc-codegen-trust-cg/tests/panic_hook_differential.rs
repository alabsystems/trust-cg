#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native_prerequisites;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: under `-Cpanic=abort` a panic must run the program's panic
// HOOK — with the Location the real panic entry reports — before it aborts.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. The bridge lowered every panic edge of a `panic=abort`
// build to libc `abort()` on the theory that "the process dies on the spot
// either way; only the message text differs". It does not: the panic runtime
// runs the panic hook first (the default hook prints the message; a
// `std::panic::set_hook` closure can do anything, including exiting with a code
// of its choosing), and only then aborts. Measured on aarch64-apple-darwin
// against the LLVM oracle, every shape below exited through the hook under LLVM
// and died of SIGABRT under the bridge, with the hook never run:
//
//   * `Option::unwrap` / `Option::expect` at -O2/-O3, where rustc's MIR inliner
//     folds the `#[track_caller]` helper into the caller and the bridge's
//     std-panic-helper substitution trapped it (`bridge_corpus/
//     panic_location_unwrap.rs`; at -O0 the shared upstream monomorphization
//     ran instead and matched);
//   * `panic!("lit")`, `panic!("{v}")`, `unreachable!()`, `assert!(c, "msg")`
//     at every opt level — the whole-block `core::panicking::*` trap;
//   * integer division by zero at every opt level — the `Assert` failure trap;
//   * `&a[1..i]` and `<[T]>::split_at` out of range at every opt level — the
//     intercepted-call bounds-check trap;
//   * a `copy_nonoverlapping` whose byte count overflows, at -O0 — the
//     precondition raises `core::panicking::panic_nounwind`, which is NOT
//     `#[track_caller]`, so the hook sees a Location inside `core`. A
//     synthesized `core::panicking::panic` raise would hand the hook the CALL
//     SITE instead; the bridge must call the real entry.
//
// `Result::unwrap` (row `c`) already matched — its upstream MIR carries a
// `Continue` edge, which the bridge raised — and is kept as a control, as is
// row `z` (no panic: `exit(51)`).
//
// A `#![no_std]` executable has no hook; its own `#[panic_handler]` is what a
// panic runs (`bridge_corpus/panic_handler_no_std.rs`, rows `a`..`c`). Before
// the fix the bridge aborted at the panic site and the handler never ran
// (SIGABRT at -O2/-O3; at -O0 the link failed on `rust_begin_unwind`). The
// handler is reached only through `core` (`panic` -> `panic_fmt` ->
// `panic_impl`), so raising for real is not enough on its own: the bridge's
// reachability fixpoint must keep the handler (an unconditional root,
// `is_called_by_symbol_from_upstream`), or it is dropped as unreachable and the
// link fails.
//
// THE GATE. Each fixture is compiled ONCE per opt level by both backends and
// every row is run against both binaries. The LLVM oracle must exit through
// the hook (an exit code, never a signal), or the fixture is not exercising the
// hook at all; the bridge must then produce the SAME exit code and stdout. The
// hook's exit code is derived from the reported file length, line and column,
// so a skipped hook (SIGABRT) and a wrong Location (a different code) both
// fail. The floor is EVERY row: a bridge refusal of a fixture fails the test,
// because the regression class this file pins includes "the raise could not be
// lowered", and a floor that tolerated a refusal would tolerate exactly that.
//
// NOT COVERED HERE: direct out-of-bounds `a[i]` / `v[i]` rows. At this
// fixture's original checkpoint, canonical MIR bounds guards failed by a
// machine trap without invoking the panic hook. The current native MIR route
// instead resolves the genuine kind-specific panic entry and actual FnAbi;
// general TrustIR `Inst::Assert` remains a separate refused input. These two
// tests still omit direct bounds rows, so their passes provide no direct
// bounds-payload credit. `assert_panic_differential` checks the separate
// fourteen-form matrix on Darwin; its platform scope must remain explicit.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
// The bridge side passes `no-proof-certs` for the reason
// `short_circuit_loop_condition_differential.rs` gives: with certificates on,
// this backend refuses essentially every AArch64 object at proof promotion
// (`[TCG-PROOF-465]`), and the test would pin nothing. The knob goes to the
// bridge side only, so the compared values are still the two backends' answers
// to the same program.
//
// FALSIFIED: see `MUTATION RESULTS` at the bottom of this file.

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["0", "2", "3"];

/// The exit code of the shapes fixture's no-panic row (`(250 % 200) + 1`): the
/// control that the selector and the program itself ran.
const NO_PANIC_EXIT: i32 = 51;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn skip_without_panic_prerequisites(test: &str) -> bool {
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
    let dir = std::env::temp_dir().join(format!("tcg_panic_hook_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// One fixture and the rows it is run with.
struct Fixture {
    name: &'static str,
    src: &'static str,
    /// A `#![no_std] #![no_main]` program: rustc links it with `-nodefaultlibs`,
    /// so the C library its `main` and `getenv`/`_exit` come from is named
    /// explicitly, for both backends alike.
    no_std: bool,
    rows: &'static [Row],
}

/// One run of a fixture binary: `shape` is the `PANIC_SHAPE` value (`None` for
/// a fixture without a selector), `opts` the opt levels it is run at.
struct Row {
    shape: Option<&'static str>,
    what: &'static str,
    opts: &'static [&'static str],
    /// The oracle's exit code is this value (the no-panic control) rather than
    /// a hook-derived one.
    expect_exit: Option<i32>,
}

const ALL: &[&str] = OPT_LEVELS;

const fn row(shape: &'static str, what: &'static str) -> Row {
    Row {
        shape: Some(shape),
        what,
        opts: ALL,
        expect_exit: None,
    }
}

/// The rows of `bridge_corpus/panic_hook_shapes.rs`, one per `PANIC_SHAPE`.
const SHAPE_ROWS: &[Row] = &[
    Row {
        shape: Some("z"),
        what: "no panic (control)",
        opts: ALL,
        expect_exit: Some(NO_PANIC_EXIT),
    },
    row("a", "`Option::unwrap` on `None`"),
    row("b", "`Option::expect` on `None`"),
    row(
        "c",
        "`Result::unwrap` on `Err` (control: matched before the fix)",
    ),
    row("d", "`panic!(\"boom\")`"),
    row("e", "`panic!(\"boom {v}\")`"),
    row("f", "`unreachable!()`"),
    row("g", "`assert!(v < 2, \"too big\")`"),
    row("h", "integer division by zero (`Assert` failure)"),
    row("i", "`&a[1..i]` out of range (intercepted bounds check)"),
    row(
        "j",
        "`<[T]>::split_at` out of range (intercepted bounds check)",
    ),
    Row {
        shape: Some("k"),
        what: "`copy_nonoverlapping` count overflow: the real, NOT \
               `#[track_caller]` `panic_nounwind` entry (UB-checked -O0 only)",
        opts: &["0"],
        expect_exit: None,
    },
];

/// The rows of `bridge_corpus/panic_handler_no_std.rs`: the program's own
/// `#[panic_handler]` is the hook.
const NO_STD_ROWS: &[Row] = &[
    Row {
        shape: Some("z"),
        what: "no panic (control)",
        opts: ALL,
        expect_exit: Some(NO_PANIC_EXIT),
    },
    row(
        "a",
        "no_std `Option::unwrap` on `None` reaches the local `#[panic_handler]`",
    ),
    row(
        "b",
        "no_std `panic!(\"boom\")` reaches the local `#[panic_handler]`",
    ),
    row(
        "c",
        "no_std division by zero reaches the local `#[panic_handler]`",
    ),
];

fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            name: "panic_location_unwrap",
            src: include_str!("bridge_corpus/panic_location_unwrap.rs"),
            no_std: false,
            rows: &[Row {
                shape: None,
                what: "`Option::unwrap` on `None` (the original fixture)",
                opts: ALL,
                expect_exit: None,
            }],
        },
        Fixture {
            name: "panic_hook_shapes",
            src: include_str!("bridge_corpus/panic_hook_shapes.rs"),
            no_std: false,
            rows: SHAPE_ROWS,
        },
        Fixture {
            name: "panic_handler_no_std",
            src: include_str!("bridge_corpus/panic_handler_no_std.rs"),
            no_std: true,
            rows: NO_STD_ROWS,
        },
    ]
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Exited { code: i32, stdout: String },
    Signalled,
}

/// Compile `src` as a std binary with `-Cpanic=abort` at `opt`, with the bridge
/// when `backend` is `Some`. `Err` carries the compiler's stderr.
fn compile(
    dir: &Path,
    fixture: &Fixture,
    opt: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    compile_with_panic(dir, fixture, opt, backend, "abort")
}

fn compile_with_panic(
    dir: &Path,
    fixture: &Fixture,
    opt: &str,
    backend: Option<&Path>,
    panic_strategy: &str,
) -> Result<PathBuf, String> {
    let (name, src) = (fixture.name, fixture.src);
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let lane = if backend.is_some() { "bridge" } else { "llvm" };
    let bin = dir.join(format!("{name}_{lane}_O{opt}"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args([
        "--crate-type",
        "bin",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg(format!("-Cpanic={panic_strategy}"));
    if fixture.no_std {
        cmd.arg(if cfg!(target_os = "macos") {
            "-Clink-arg=-lSystem"
        } else {
            "-Clink-arg=-lc"
        });
    }
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        // Bridge side ONLY: see the module doc's `no-proof-certs` paragraph.
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

fn run(bin: &Path, shape: Option<&str>) -> Outcome {
    let mut cmd = Command::new(bin);
    match shape {
        Some(shape) => cmd.env("PANIC_SHAPE", shape),
        None => cmd.env_remove("PANIC_SHAPE"),
    };
    let out = cmd.output().expect("run compiled binary");
    match out.status.code() {
        Some(code) => Outcome::Exited {
            code,
            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        },
        None => Outcome::Signalled,
    }
}

#[test]
fn panic_abort_runs_the_hook_with_the_real_location_like_llvm() {
    if skip_without_panic_prerequisites(
        "panic_abort_runs_the_hook_with_the_real_location_like_llvm",
    ) {
        return;
    }
    let dylib = ensure_dylib_built();
    let mut matched = 0usize;
    let mut total = 0usize;
    let mut failures: Vec<String> = Vec::new();
    for fixture in fixtures() {
        for opt in OPT_LEVELS {
            let rows: Vec<&Row> = fixture
                .rows
                .iter()
                .filter(|r| r.opts.contains(opt))
                .collect();
            if rows.is_empty() {
                continue;
            }
            total += rows.len();
            let dir = workdir(&format!("{}_O{opt}", fixture.name));
            let oracle = compile(&dir, &fixture, opt, None).unwrap_or_else(|e| {
                panic!("{} (-O{opt}): LLVM oracle failed: <<<{e}>>>", fixture.name)
            });
            let bridge = match compile(&dir, &fixture, opt, Some(&dylib)) {
                Ok(bin) => bin,
                Err(stderr) => {
                    failures.push(format!(
                        "{} (-O{opt}): the bridge REFUSED the fixture, so {} row(s) never ran: \
                         <<<{}>>>",
                        fixture.name,
                        rows.len(),
                        stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                    ));
                    let _ = std::fs::remove_dir_all(&dir);
                    continue;
                }
            };
            for row in rows {
                let label = format!(
                    "{} -O{opt} shape={}: {}",
                    fixture.name,
                    row.shape.unwrap_or("-"),
                    row.what
                );
                let want = run(&oracle, row.shape);
                // The oracle must leave through the hook (or the control's own
                // exit): a signal here means the fixture does not exercise the
                // hook, and a matching bridge signal would prove nothing.
                let Outcome::Exited {
                    code: want_code, ..
                } = &want
                else {
                    panic!(
                        "{label}: the LLVM oracle died by a signal; the fixture is not exercising the hook"
                    );
                };
                if let Some(expected) = row.expect_exit {
                    assert_eq!(
                        *want_code, expected,
                        "{label}: the LLVM oracle's control exit changed"
                    );
                } else {
                    assert_ne!(
                        *want_code, NO_PANIC_EXIT,
                        "{label}: the LLVM oracle did not panic; the row selects nothing"
                    );
                }
                let got = run(&bridge, row.shape);
                if got == want {
                    matched += 1;
                } else {
                    failures.push(format!("{label}: LLVM {want:?} vs bridge {got:?}"));
                }
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    assert_eq!(total, 49, "the original panic-hook row denominator changed");
    eprintln!("panic-hook rows: {matched}/{total} matched LLVM");
    for failure in &failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        failures.is_empty() && matched == total,
        "{} of {total} panic-hook rows diverged from LLVM or never ran. A bridge \
         binary that dies of a signal where LLVM exits through the hook skipped \
         the panic hook; a different exit code handed the hook a different \
         Location. Failures: {failures:#?}",
        total - matched
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// A panic hook observes writes executed before the panic. The bridge used to
// skip the whole panic block, losing the store while still running the hook.
// Abort and unwind are separate source admission paths; the hook exits before
// unwinding, so each strategy must preserve the same preceding store. This pins
// hook-observed effects, not cleanup unwinding or arbitrary payload fidelity.
#[test]
fn panic_hook_observes_preceding_stores_abort_and_unwind_like_llvm() {
    const TEST: &str = "panic_hook_observes_preceding_stores_abort_and_unwind_like_llvm";
    if skip_without_panic_prerequisites(TEST) {
        return;
    }
    let dylib = ensure_dylib_built();
    let fixture = Fixture {
        name: "panic_preceding_store",
        src: include_str!("bridge_corpus/panic_preceding_store.rs"),
        no_std: false,
        rows: &[],
    };
    let expected = Outcome::Exited {
        code: 73,
        stdout: String::new(),
    };
    let mut matched = 0;
    for strategy in ["abort", "unwind"] {
        for opt in OPT_LEVELS {
            let dir = workdir(&format!("preceding_store_{strategy}_O{opt}"));
            let oracle = compile_with_panic(&dir, &fixture, opt, None, strategy)
                .unwrap_or_else(|e| panic!("LLVM {strategy} -O{opt} compile failed: {e}"));
            let bridge = compile_with_panic(&dir, &fixture, opt, Some(&dylib), strategy)
                .unwrap_or_else(|e| panic!("CG {strategy} -O{opt} refused: {e}"));
            for shape in ["c", "l", "u", "f"] {
                let label = format!("{strategy} -O{opt} shape={shape}");
                let want = run(&oracle, Some(shape));
                assert_eq!(
                    want, expected,
                    "LLVM {label}: the store/hook control must exit 73"
                );
                let got = run(&bridge, Some(shape));
                assert_eq!(
                    got, want,
                    "CG {label}: the hook must observe the preceding store"
                );
                matched += 1;
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    assert_eq!(matched, 24);
    eprintln!("PRE_PANIC_EFFECTS matched=24 strategies=abort,unwind opts=0,2,3");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// MUTATION RESULTS (2026-09-30, aarch64-apple-darwin, backend built by
// `targo --unverified test --release` with the atpkg Trust pack 9192; exit
// codes depend on the temp path the fixture is compiled from, so they are
// quoted for shape, not as constants):
//
//   * fixed tree: 49/49 rows match LLVM.
//   * the bridge's `src/lib.rs` reverted whole to its pre-fix text: 11/49. Every
//     hook row fails except `Result::unwrap` (`c`) and `Option::unwrap`/`expect`
//     at -O0 (an upstream shared monomorphization runs there) — e.g.
//     `panic_location_unwrap -O2: LLVM Exited { code: 231 } vs bridge
//     Signalled`; the `no_std` rows die by a signal at -O2/-O3 and the -O0
//     `no_std` fixture fails to link.
//   * `panic_edge_raises` answering `false` for `PanicStrategy::Abort` only:
//     7/49 — every hook / handler row fails as `Signalled`; row `k` still
//     matches because the non-`#[track_caller]` entry is called for real.
//   * the `requires_caller_location` conjunct removed from
//     `block_diverges_via_panic`: 48/49 — ONLY row `k` fails, and not by a
//     signal: `LLVM Exited { code: 105 } vs bridge Exited { code: 35 }`. The
//     synthesized raise ran the hook with the CALL SITE where the real
//     `panic_nounwind` reports a Location inside `core` — a silently wrong
//     value, which is why that conjunct exists.
//   * (measured on the first form of the handler edge, a conditional
//     `PanicHandlerEdge`, since replaced by the unconditional root)
//     `PanicHandlerEdge::seed_if_referenced` made a no-op: 37/49 — exactly the
//     12 `no_std` rows fail: the local `#[panic_handler]` is dropped as
//     unreachable and the link fails on `rust_begin_unwind` at every opt level.
