// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Integration test: an intercepted std call that panics must raise the panic
// the replaced std entry raises — the same payload type and text, at the same
// `&'static Location` — and a panic in a frame that cannot unwind must run the
// hook and then abort in that frame's terminate pad, exactly as the LLVM
// backend's binary does.
//
// WHY THIS FILE EXISTS. Two panic-path miscompiles, measured on
// aarch64-apple-darwin against the LLVM oracle:
//
//   * An interception repeated its std entry's precondition check and, on
//     failure, raised `core::panicking::panic` with a synthesized message at
//     the INTERCEPTED CALL's location. That location is rustc's only when every
//     frame of the replaced entry down to its panic is `#[track_caller]`.
//     `Vec::swap_remove`, `<[T]>::rotate_left` / `rotate_right`, `Vec::drain`,
//     `Vec::extend_from_within`, `str::split_at` / `split_at_mut` and the
//     integer `Sum` / `Product` closures are not, so the hook saw this crate's
//     line where rustc reports a line inside `alloc` / `core`; and every
//     synthesized message differed from std's
//     (`Vec::insert`, `remove`, `split_off`, `<[T]>::swap`, range indexing of
//     `Vec` / arrays / `str`, `<[T]>::split_at`, `<[T]>::windows`).
//   * A panic whose MIR unwind edge is `Terminate` (a panic inside an
//     `extern "C"` function under `panic=unwind`) was lowered to libc
//     `abort()`: SIGABRT with no hook, no message and no "panic in a function
//     that cannot unwind".
//
// The raises are std's own entries through `std_panic_route` (main's OD-170),
// which replaced the differential-hunt landing's `std_panic_replay` (OD-173)
// in its merge of origin/main `7c60cee46`. The payload's TYPE is part of the transcript: on the merge of
// `c5919a122` the four `windows_len` cells at -O0/-O1 printed `HOOK str` where
// LLVM printed `HOOK string` (std's `windows` fails through `expect_failed`,
// which formats its message; `std_panic_replay` raised the literal itself),
// and unmodified main printed `HOOK string` there. The zero-size rows of the
// other stride constructors (`chunks_exact`, `rchunks`, `rchunks_exact`,
// whose `assert!` literal is a `&str`) pin the same route.
//
// THE GATE. The callee crate (`support/intercept_panic/callee.rs`) is compiled
// by each backend at -O0..-O3 under `panic=abort` and `panic=unwind`, with
// overflow checks on; the driver is always LLVM's. Each case runs in a child
// whose returning hook prints the payload's type and text and the full
// location; the parent prints the child's stdout, exit status or signal and
// stderr. Every case's transcript must equal LLVM's. A bridge refusal of the
// callee fails the test.
//
// HOST-NATIVE: no `--target` is passed. The terminate rows run only where the
// bridge lowers a Rust terminate pad (AArch64 Linux and Darwin); elsewhere a
// terminate edge keeps its documented trap. The bridge side passes
// `no-proof-certs` (see `short_circuit_loop_condition_differential.rs`).

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["0", "1", "2", "3"];
const STRATEGIES: &[&str] = &["abort", "unwind"];
const CALLEE: &str = "intercept_panic_callee";

/// Whether the bridge lowers a Rust terminate pad on this host
/// (`supports_rust_terminate_filter`).
const TERMINATE_PAD_HOST: bool = cfg!(all(
    target_arch = "aarch64",
    any(target_os = "linux", target_os = "macos")
));

fn workdir(stem: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("tcg_intercept_panic_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn clear_untracked_controls(command: &mut Command) {
    for (key, _) in std::env::vars_os() {
        if key
            .to_str()
            .is_some_and(|name| name.starts_with("TRUST_CG_") || name.starts_with("TCG_"))
        {
            command.env_remove(key);
        }
    }
}

/// Build one cell: the callee rlib by `backend` (LLVM when `None`) and the
/// LLVM driver linked against it. `Err` carries the failing compile's stderr.
fn build(
    root: &Path,
    dir: &Path,
    strategy: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    std::fs::create_dir_all(dir).expect("create cell directory");
    let mut compile = toolchain_support::rustc_command();
    clear_untracked_controls(&mut compile);
    compile
        .arg(format!("--crate-name={CALLEE}"))
        .args([
            "--crate-type=rlib",
            "-Ccodegen-units=1",
            "-Coverflow-checks=yes",
        ])
        .arg(format!("-Cpanic={strategy}"))
        .arg(format!("-Copt-level={opt}"))
        .args(if matches!(opt, "0" | "1") {
            &["--cfg", "stride_next"][..]
        } else {
            &[][..]
        })
        .arg(root.join("callee.rs"))
        .arg("--out-dir")
        .arg(dir);
    if let Some(dylib) = backend {
        let mut argument = std::ffi::OsString::from("-Zcodegen-backend=");
        argument.push(dylib);
        compile
            .arg(argument)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
            .env("XDG_CACHE_HOME", dir.join("cache"));
    }
    let output = compile.output().expect("spawn the callee compile");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let driver = dir.join("driver");
    let mut link = toolchain_support::rustc_command();
    clear_untracked_controls(&mut link);
    let output = link
        .args(["-Ccodegen-units=1", "-Copt-level=0"])
        .arg(format!("-Cpanic={strategy}"))
        .arg("--extern")
        .arg(format!(
            "{CALLEE}={}",
            dir.join(format!("lib{CALLEE}.rlib")).display()
        ))
        .arg(root.join("driver.rs"))
        .arg("-o")
        .arg(&driver)
        .output()
        .expect("spawn the driver compile");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(driver)
}

fn run(driver: &Path, case: &str) -> String {
    let output = Command::new(driver)
        .arg(case)
        .output()
        .expect("run the driver");
    assert!(
        output.status.success(),
        "the driver's parent process failed on {case}: {output:?}"
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn intercepted_std_panics_and_terminate_edges_match_llvm() {
    const TEST: &str = "intercepted_std_panics_and_terminate_edges_match_llvm";
    if toolchain_support::skip_without_backend_knobs(TEST) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let root = workdir("sources");
    std::fs::write(
        root.join("callee.rs"),
        include_str!("support/intercept_panic/callee.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.rs"),
        include_str!("support/intercept_panic/driver.rs"),
    )
    .unwrap();
    let mut failures: Vec<String> = Vec::new();
    let (mut compared, mut hooks, mut terminates) = (0usize, 0usize, 0usize);
    for strategy in STRATEGIES {
        for opt in OPT_LEVELS {
            let cell = format!("{strategy}-O{opt}");
            let oracle = build(
                &root,
                &root.join(format!("llvm-{cell}")),
                strategy,
                opt,
                None,
            )
            .unwrap_or_else(|e| panic!("{cell}: the LLVM oracle failed to build: <<<{e}>>>"));
            let bridge = match build(
                &root,
                &root.join(format!("cg-{cell}")),
                strategy,
                opt,
                Some(&dylib),
            ) {
                Ok(driver) => driver,
                Err(stderr) => {
                    failures.push(format!(
                        "{cell}: the bridge REFUSED the callee: <<<{}>>>",
                        stderr.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
                    ));
                    continue;
                }
            };
            let cases = run(&oracle, "--list");
            for case in cases.lines().filter(|line| !line.is_empty()) {
                let terminate_row = case.starts_with("c_") && *strategy == "unwind";
                if terminate_row && !TERMINATE_PAD_HOST {
                    continue;
                }
                let want = run(&oracle, case);
                if case == "controls" {
                    assert!(
                        want.contains("STATUS exit 0") && !want.contains("HOOK "),
                        "{cell} controls: the LLVM oracle panicked: {want}"
                    );
                } else {
                    assert!(
                        want.contains("HOOK ") && !want.contains("RETURNED"),
                        "{cell} {case}: the LLVM oracle did not panic through the hook: {want}"
                    );
                    hooks += 1;
                }
                if terminate_row {
                    assert!(
                        want.contains("panic in a function that cannot unwind"),
                        "{cell} {case}: the LLVM oracle did not reach the terminate pad: {want}"
                    );
                    terminates += 1;
                }
                let got = run(&bridge, case);
                compared += 1;
                if got != want {
                    failures.push(format!(
                        "{cell} {case}:\n  LLVM:   {}\n  bridge: {}",
                        want.trim_end().replace('\n', "\n          "),
                        got.trim_end().replace('\n', "\n          ")
                    ));
                }
            }
        }
    }
    eprintln!(
        "INTERCEPT_PANIC_ROWS compared={compared} hooks={hooks} terminates={terminates} \
         diverged={}",
        failures.len()
    );
    for failure in &failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        failures.is_empty(),
        "{} intercepted-panic rows diverged from LLVM or never ran: a different payload or \
         location is a wrong panic; a signal with no HOOK line skipped the hook",
        failures.len()
    );
    let expected_terminates = if TERMINATE_PAD_HOST { 28 } else { 0 };
    assert_eq!(
        terminates, expected_terminates,
        "the terminate row denominator changed"
    );
    let _ = std::fs::remove_dir_all(&root);
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
