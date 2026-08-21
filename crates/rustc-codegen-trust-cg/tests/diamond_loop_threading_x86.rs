#[path = "support/target_dir.rs"]
mod target_dir_support;

// crates/rustc-codegen-trust-cg/tests/diamond_loop_threading_x86.rs
//
// #84 (proof-gap program) — DIAMOND-BODY loop back-edge threading VC e2e.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Extends `loop_threading_x86.rs` (the straight-line euclid-class VC) to a loop
// whose body contains a SINGLE 2-WAY DIAMOND (`if/else`) before the rotation
// that trips P1.3 sub-check (2) (`LoopCarriedSlotMisthreaded`). The semantic
// back-edge threading VC now models the diamond: it walks each arm, merges the
// per-arm values at the join with `select(cond, then, else)`, and proves the
// emitted back-edge threading equals that MIR spec.
//
// What this asserts (the diamond extension's contract):
//
//   1. GATE ON (`TCG_P3C_REFINE=1`): a CORRECT diamond-body loop that P1.3
//      structurally false-rejects COMPILES, and the trace shows the back-edge
//      threading PROVEN (the diamond VC fired and Refined — not skipped).
//   2. GATE ON: the compiled program RUNS and matches the rustc reference
//      backend (the admitted diamond code is value-correct, not just accepted).
//   3. GATE OFF: the SAME program fails closed (the structural P1.3 rejection
//      stands; a `#[no_mangle]` root surfaces the failure as a fatal compile
//      error). Zero behavior change to the default-on perimeter.
//   4. OUT-OF-MODEL (a >2-way `match` in the loop body) fails closed EVEN under
//      the gate — the diamond modeling refuses anything it cannot model exactly,
//      so it can never over-admit.
//
// The "deliberately wrong arm stays REFUTED" bite is exercised at the verifier
// UNIT level (`loop_backedge_symexec::tests::diamond_loop_end_to_end_refines_and_swap_refutes`
// and `mir_semantics::tests::{swapped_arm,wrong_then_value}_select_diamond_is_refuted`):
// the bridge lowers faithfully, so a wrong-arm misthread cannot be produced from
// correct source at the compile level — the genuine swap/wrong-value refutation
// is built directly over the real interpreter + verifier there.
//
// Run (requires the target-bridge toolchain + x86_64-apple-darwin std, x86 host):
//     cd crates/rustc-codegen-trust-cg
//     cargo +nightly-2026-04-20 test --release --test diamond_loop_threading_x86 -- --nocapture

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

// A diamond-body GCD-by-subtraction loop. The `if a > b { .. } else { .. }` is a
// 2-way diamond reassigning `t`; the subsequent `a = b; b = t` is the rotation
// that structurally trips P1.3 sub-check (2). `#[no_mangle]` makes it a required
// root so a fail-closed verdict is a FATAL compile error (not a silent skip);
// `black_box` keeps the call from being const-folded away. gcd(252,105) == 21.
const DIAMOND_LOOP_PROGRAM: &str = r#"
use std::hint::black_box;

#[no_mangle]
#[inline(never)]
pub fn diff_rotate(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t;
        if a > b {
            t = a - b;
        } else {
            t = b - a;
        }
        a = b;
        b = t;
    }
    a
}

fn main() {
    let a = black_box(252u64);
    let b = black_box(105u64);
    std::process::exit((diff_rotate(a, b) & 0x7f) as i32);
}
"#;

// A >2-way (3-arm `match`) loop body: NOT a 2-way bool diamond, so it is out of
// the VC slice and must fail closed even under the gate.
const THREE_WAY_PROGRAM: &str = r#"
use std::hint::black_box;

#[no_mangle]
#[inline(never)]
pub fn threeway(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t;
        match a % 3 {
            0 => t = a - b,
            1 => t = b - a,
            _ => t = a + b,
        }
        a = b;
        b = t;
    }
    a
}

fn main() {
    let a = black_box(252u64);
    let b = black_box(105u64);
    std::process::exit((threeway(a, b) & 0x7f) as i32);
}
"#;

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            let Some((_, value)) = raw_channel.split_once('=') else {
                continue;
            };
            return value.trim().trim_matches('"').to_owned();
        }
    }
    panic!("rust-toolchain.toml did not contain a channel");
}

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let name = dylib_name();
    let candidates = [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run diamond-loop test");
    let built = target_dir.join("release").join(&name);
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn x86_64_std_available() -> bool {
    let output = Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output();
    match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line.trim() == TARGET),
        Err(_) => false,
    }
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_diamondvc_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` through the trust-cg backend to an object. With `refine` the
/// FULL refinement lane (`TCG_P3C_REFINE=1`) + `TCG_REFINE_TRACE=1` are set.
/// Returns `(success, stderr)`.
fn compile_object(stem: &str, src: &str, dylib: &Path, refine: bool) -> (bool, String) {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    if refine {
        cmd.env("TCG_P3C_REFINE", "1");
        cmd.env("TCG_REFINE_TRACE", "1");
    } else {
        cmd.env_remove("TCG_P3C_REFINE");
        cmd.env_remove("TCG_REFINE");
        cmd.env_remove("TCG_REFINE_TRACE");
    }
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(&backend_arg);
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg("-Copt-level=0")
    .arg("--emit=obj")
    .arg("--out-dir")
    .arg(&dir)
    .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let mut success = output.status.success();
    if success {
        success = std::fs::read_dir(&dir)
            .expect("read workdir")
            .filter_map(|e| e.ok().map(|e| e.path()))
            .any(|p| p.extension().is_some_and(|x| x == "o"));
    }
    let _ = std::fs::remove_dir_all(&dir);
    (success, stderr)
}

/// Compile `src` to a full binary through the trust-cg backend (gate ON) and run
/// it, returning the process exit code. `None` if the compile/link failed.
fn compile_run(stem: &str, src: &str, dylib: &Path) -> Option<i32> {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    let bin_path = dir.join("prog_bin");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    cmd.env("TCG_P3C_REFINE", "1");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"]);
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(&backend_arg);
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
        "-Copt-level=0",
    ])
    .arg("-o")
    .arg(&bin_path)
    .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    if !output.status.success() || !bin_path.exists() {
        let _ = std::fs::remove_dir_all(&dir);
        return None;
    }
    let run = Command::new(&bin_path).status().ok();
    let _ = std::fs::remove_dir_all(&dir);
    run.and_then(|s| s.code())
}

/// The rustc reference-backend exit code for `src` (the ground truth).
fn reference_run(stem: &str, src: &str) -> Option<i32> {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    let bin_path = dir.join("prog_ref");
    std::fs::write(&src_path, src).expect("write source");
    let output = Command::new("rustup")
        .env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET)
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Coverflow-checks=off",
        ])
        .arg("-o")
        .arg(&bin_path)
        .arg(&src_path)
        .output()
        .expect("failed to spawn reference rustc");
    if !output.status.success() || !bin_path.exists() {
        let _ = std::fs::remove_dir_all(&dir);
        return None;
    }
    let run = Command::new(&bin_path).status().ok();
    let _ = std::fs::remove_dir_all(&dir);
    run.and_then(|s| s.code())
}

#[test]
fn diamond_loop_threading_vc_proves_and_runs() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 compile requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();

    // 1. GATE ON: the diamond-body loop must COMPILE and the trace must show the
    //    back-edge threading PROVEN (the structural misthread admitted via the
    //    semantic VC — the diamond fired and Refined).
    let (ok, stderr) = compile_object("diamond_on", DIAMOND_LOOP_PROGRAM, &dylib, true);
    assert!(
        ok,
        "TCG_P3C_REFINE=1 must compile the correct diamond-body loop, but it FAILED.\nstderr:\n{}",
        stderr.lines().rev().take(20).collect::<Vec<_>>().join("\n")
    );
    assert!(
        stderr.contains("back-edge threading PROVEN"),
        "expected the trace to show the back-edge threading PROVEN for the diamond loop; \
         got:\n{}",
        stderr
            .lines()
            .filter(|l| l.contains("PROVEN") || l.contains("diamond") || l.contains("misthread"))
            .collect::<Vec<_>>()
            .join("\n")
    );

    // 2. GATE ON: the admitted code is VALUE-CORRECT (matches the rustc ref).
    let got = compile_run("diamond_run", DIAMOND_LOOP_PROGRAM, &dylib);
    let want = reference_run("diamond_ref", DIAMOND_LOOP_PROGRAM);
    if let Some(want) = want {
        assert_eq!(
            got,
            Some(want),
            "diamond loop runtime result must match the rustc reference backend \
             (trust-cg={got:?} vs rustc={want:?})"
        );
        assert_eq!(want, 21, "gcd(252,105) & 0x7f must be 21 (sanity on the reference)");
    } else {
        eprintln!("skipping run-differential: reference backend produced no binary (linker env)");
    }

    // 3. GATE OFF: the same program fails closed (P1.3 structural rejection).
    let (ok_off, stderr_off) = compile_object("diamond_off", DIAMOND_LOOP_PROGRAM, &dylib, false);
    assert!(
        !ok_off,
        "with the refinement lane unset the diamond-body loop must FAIL CLOSED (P1.3), \
         but it compiled."
    );
    assert!(
        stderr_off.contains("ssa/loop-completeness check failed")
            && stderr_off.contains("set TCG_P3C_REFINE to model it"),
        "gate-off failure must be the structural P1.3 rejection pointing at the gated \
         diamond model; got:\n{}",
        stderr_off.lines().rev().take(8).collect::<Vec<_>>().join("\n")
    );
    assert!(
        !stderr_off.contains("back-edge threading PROVEN"),
        "gate-off compile must NOT prove the diamond back-edge"
    );

    // 4. OUT-OF-MODEL (3-way match) must fail closed EVEN under the gate.
    let (ok_3way, stderr_3way) = compile_object("threeway_on", THREE_WAY_PROGRAM, &dylib, true);
    assert!(
        !ok_3way,
        "a >2-way match loop body is out of the VC slice and must fail closed even under \
         the gate, but it compiled."
    );
    assert!(
        stderr_3way.contains("out of VC slice") || stderr_3way.contains("non-bool discriminant"),
        "3-way out-of-model failure must name the VC-slice limit; got:\n{}",
        stderr_3way.lines().rev().take(8).collect::<Vec<_>>().join("\n")
    );

    eprintln!(
        "diamond_loop_threading_x86: diamond VC fired + PROVEN under TCG_P3C_REFINE=1, \
         runtime result matched rustc, gate-off fails closed (P1.3), 3-way fails closed."
    );
}
