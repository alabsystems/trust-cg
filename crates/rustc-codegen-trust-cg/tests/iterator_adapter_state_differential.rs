#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: std iterator adapters whose state crosses between
// bridge-compiled and LLVM-compiled code keep std's layout and semantics —
// `Chain`'s `Option` halves, `TakeWhile`'s done flag, `FlatMap`'s
// `FlattenCompat` state and `StepBy`'s `SpecRangeSetup` countdown.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. The bridge drives std iterator chains itself
// (`resolve_iter_chain` + `emit_chain_next`, the bounded `flat_map` driver,
// `lower_step_by_next`) and builds some adapters itself (`lower_chain_ctor`,
// `lower_flatmap_bounded_ctor`, the `.step_by(k)` arm of
// `lower_iter_structural_ctor`). Four of those private models disagreed with
// std (hunt clusters on origin/main c8b07006b, aarch64-apple-darwin):
//
//   * Chain: the drivers never read either half's `Option` tag, so a `Chain`
//     whose half std had already cleared to `None` was driven through dead
//     payload bytes — a null `slice::Iter` cursor (SIGSEGV) or stale `Range`
//     bounds (phantom items). R2T-CHAIN-OPTION-TAG-IGNORED.
//   * TakeWhile: its done `flag` was never read or written, so a `TakeWhile`
//     that had already stopped restarted on the rest of its source.
//     R3-TAKEWHILE-FLAG-ELIDED.
//   * FlatMap: the ctor wrote a private `{start, end}` into the `FlatMap` slot;
//     std code reading the value (a returned `impl Iterator`, `size_hint`)
//     read uninitialized `Option` tags. R2T-FLATMAP-PRIVATE-ENCODING-ESCAPE.
//   * StepBy: an unsigned `Range` source kept a packed `(k-1)<<32 | countdown`
//     word and no `SpecRangeSetup` rewrite of `end`; `RangeInclusive` / `Chain`
//     sources never wrote `first_take`. Any std body on the other side of a
//     crate boundary (or a share-generics instance) read garbage. A `&mut`
//     terminal (`any` / `position`) whose drive ran the source out mid-skip
//     also handed std its running countdown in place of `step_minus_one`.
//     R2T-STEPBY-PACKED-STATE-AT-BOUNDARY.
//
// THE GATE. Each fixture is a library plus a driver. The library is compiled
// once by LLVM and once by the bridge (`no-proof-certs`); the driver is always
// LLVM-compiled and linked against each, so every case runs with std code on
// the far side of the boundary. Every case's exit code, killing signal and
// stdout must match the all-LLVM build. A bridge refusal of a fixture fails the
// test: every shape here lowers. `StepBy` is admitted only at -Copt-level=0
// (`[TCG-STEPBY-OPT-LEVEL]` refuses it above), so its fixture runs at O0; the
// in-library `Chain::next` fixture runs at O1..O3 (its own lib.rs says why); the
// main fixture runs at O0..O3.
//
// HOST-NATIVE: no `--target` is passed. Measured on aarch64-apple-darwin only.
// `-Cpanic=abort` on both sides (the fixtures never panic).
//
// FALSIFIED: see `BASELINE RESULTS` at the bottom of this file.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

struct Fixture {
    name: &'static str,
    lib: &'static str,
    driver: &'static str,
    opt_levels: &'static [&'static str],
}

const FIXTURES: &[Fixture] = &[
    Fixture {
        name: "iter_adapter_state",
        lib: include_str!("bridge_corpus/iter_adapter_state/lib.rs"),
        driver: include_str!("bridge_corpus/iter_adapter_state/main.rs"),
        opt_levels: &["0", "1", "2", "3"],
    },
    Fixture {
        name: "iter_adapter_state_local",
        lib: include_str!("bridge_corpus/iter_adapter_state_local/lib.rs"),
        driver: include_str!("bridge_corpus/iter_adapter_state_local/main.rs"),
        opt_levels: &["1", "2", "3"],
    },
    Fixture {
        name: "iter_adapter_state_stepby",
        lib: include_str!("bridge_corpus/iter_adapter_state_stepby/lib.rs"),
        driver: include_str!("bridge_corpus/iter_adapter_state_stepby/main.rs"),
        opt_levels: &["0"],
    },
];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_iter_state_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn common_flags(cmd: &mut Command, opt: &str) {
    cmd.args(["-Ccodegen-units=1", "-Cpanic=abort"]);
    cmd.arg(format!("-Copt-level={opt}"));
}

/// Compile the fixture library as `libklib.rlib` in `dir`, through the bridge
/// when `backend` is `Some`. `Err` carries the compiler's stderr.
fn compile_lib(
    dir: &Path,
    src: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    std::fs::create_dir_all(dir).expect("create lib dir");
    let src_path = dir.join("klib.rs");
    std::fs::write(&src_path, src).expect("write fixture library");
    let rlib = dir.join("libklib.rlib");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    common_flags(&mut cmd, opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&rlib).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(rlib)
}

/// Compile the fixture driver with LLVM against `rlib`.
fn compile_driver(dir: &Path, src: &str, opt: &str, rlib: &Path) -> PathBuf {
    let src_path = dir.join("kmain.rs");
    std::fs::write(&src_path, src).expect("write fixture driver");
    let bin = dir.join("kmain");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
    common_flags(&mut cmd, opt);
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(rlib);
    cmd.arg("--extern").arg(extern_arg);
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    assert!(
        output.status.success(),
        "the LLVM driver failed to compile against {rlib:?}: <<<{}>>>",
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn run(bin: &Path, case: &str) -> Ending {
    let out = Command::new(bin)
        .arg(case)
        .output()
        .expect("run compiled binary");
    Ending {
        code: out.status.code(),
        signal: out.status.signal(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
    }
}

fn list_cases(bin: &Path) -> Vec<String> {
    let out = Command::new(bin)
        .arg("--list")
        .output()
        .expect("list cases");
    assert!(out.status.success(), "`{bin:?} --list` failed");
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect()
}

fn stderr_tail(stderr: &str) -> String {
    stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
}

#[test]
fn iterator_adapter_state_matches_llvm_across_the_boundary() {
    if toolchain_support::skip_without_backend_knobs(
        "iterator_adapter_state_matches_llvm_across_the_boundary",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut matched = 0usize;
    let mut total = 0usize;
    let mut failures: Vec<String> = Vec::new();
    for fixture in FIXTURES {
        for opt in fixture.opt_levels {
            let config = format!("{} -O{opt}", fixture.name);
            let dir = workdir(&format!("{}_O{opt}", fixture.name));
            let llvm_lib = compile_lib(&dir.join("llvm"), fixture.lib, opt, None)
                .unwrap_or_else(|e| panic!("{config}: the LLVM library failed: <<<{e}>>>"));
            let oracle = compile_driver(&dir.join("llvm"), fixture.driver, opt, &llvm_lib);
            let cases = list_cases(&oracle);
            assert!(!cases.is_empty(), "{config}: the driver lists no cases");
            total += cases.len();
            let bridge_lib = match compile_lib(&dir.join("bridge"), fixture.lib, opt, Some(&dylib))
            {
                Ok(rlib) => rlib,
                Err(stderr) => {
                    failures.push(format!(
                        "{config}: the bridge REFUSED the library, so {} case(s) never \
                         ran: <<<{}>>>",
                        cases.len(),
                        stderr_tail(&stderr)
                    ));
                    let _ = std::fs::remove_dir_all(&dir);
                    continue;
                }
            };
            let bridge = compile_driver(&dir.join("bridge"), fixture.driver, opt, &bridge_lib);
            for case in &cases {
                let want = run(&oracle, case);
                assert_eq!(
                    want.code,
                    Some(0),
                    "{config} {case}: the LLVM oracle did not exit 0: {want:?}"
                );
                let got = run(&bridge, case);
                if got == want {
                    matched += 1;
                } else {
                    failures.push(format!(
                        "{config} {case}: LLVM {want:?} vs trust-cg {got:?}"
                    ));
                }
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    eprintln!("iterator adapter state rows: {matched}/{total} matched LLVM");
    for failure in &failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        failures.is_empty() && matched == total,
        "{} of {total} iterator adapter state rows diverged from LLVM or never ran: \
         {failures:#?}",
        total - matched
    );
}

// BASELINE RESULTS (2026-10-05, aarch64-apple-darwin, Trust pack 9192). The
// same fixtures, as `klib.rs` / `kmain.rs`, through the hunt harness
// (`run_probe.py`: bridge-built library, LLVM driver, one process per case):
//
//   * the base backend (origin/main c8b07006b; its bridge source is
//     byte-identical to 6b108b81d): `iter_adapter_state` O0..O3 CRASH=13
//     HANG=3 WRONG=30 MATCH=58 of 104 — `Chain` slice halves cleared to `None`
//     SIGSEGV at -O1..-O3, a flagged `TakeWhile` sums 39 (std: 0) at every
//     level, a returned `FlatMap` yields `[]` / garbage at -O0/-O1 and its
//     `rev()` / `clone()` hang at -O1;
//     `iter_adapter_state_local` O1..O3 CRASH=5 MATCH=7 of 12;
//     `iter_adapter_state_stepby` O0 CRASH=1 WRONG=22 MATCH=7 of 30 — e.g.
//     `ret_u32_take` `[0, 4294967295, ...]` (std `[0, 2, 4, 6, 8]`),
//     `shared_driver_for` `[]` (std `[5, 11, 17, 23, 29]`),
//     `ret_u8_step_over_max` `(Some(3), Some(2), Some(1))` (std
//     `(Some(3), None, None)`), `ret_u64_near_max` aborts with "capacity
//     overflow", `ref_any_exhausted_mid_skip` leaves `step_minus_one: 2`
//     (std `3`).
//   * this tree's build-profile backend: 104/104, 12/12 and 30/30 MATCH.
