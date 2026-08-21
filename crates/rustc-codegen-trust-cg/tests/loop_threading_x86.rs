#[path = "support/target_dir.rs"]
mod target_dir_support;

// crates/rustc-codegen-trust-cg/tests/loop_threading_x86.rs
//
// Item 6 (proof-gap program) — LOOP-CARRIED threading VC e2e smoke.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Compiles a euclid-shaped guarded-rem loop (`while b != 0 { a += a % b;
// b -= 1; }`) through the trust-cg backend with the FULL refinement lane on
// (`TCG_P3C_REFINE=1`) and `TCG_REFINE_TRACE=1`, and asserts:
//
//   1. The compile SUCCEEDS — i.e. the loop-carried threading obligation the
//      bridge raised on its (correct) threading proved `Refined` (a falsely-
//      refuting VC would fail the compile closed and surface here).
//   2. The trace shows the loop obligation actually FIRED and REFINED — the
//      VC is LIVE, not silently skipped (the anti-vacuity check: without this,
//      an always-skipping wiring would pass test 1 trivially).
//   3. GATE OFF: the same program compiles with the refinement lane unset
//      (the loop VC is dormant by default; zero behavior change).
//
// WHY NOT THE LITERAL EUCLID ROTATION (`let t = b; b = a % b; a = t;`): the
// DEFAULT-ON structural P1.3 gate (`ssa_loop_complete`, run BEFORE the
// refinement tail) fail-closes the euclid rotation today — its sub-check (2)
// cannot structurally distinguish a correct rotation from a swapped-slot
// miscompile, so the function never reaches the semantic VC (it is dropped /
// errored, the documented sound-but-incomplete state). The rotation class is
// therefore exercised at the UNIT level (`trust_ir_interp::tests`): the REAL
// interpreter over a hand-built emitted euclid latch against the REAL verifier
// — correct rotation Refines, swapped/stale back-edge args Refute. Relaxing
// the default-on structural gate (using this semantic VC as the replacement
// evidence) is a separate, deliberate policy change out of this item's scope.
//
// Follows the refinement_x86.rs harness pattern (object emission only).
//
// Run (requires the target-bridge toolchain + x86_64-apple-darwin std, x86 host):
//     cd crates/rustc-codegen-trust-cg
//     cargo +nightly-2026-04-20 test --release --test loop_threading_x86 -- --nocapture

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

// A euclid-shaped single-latch loop over two loop-carried u64 scalars: the
// `while b != 0` guard + an in-loop `a % b` (the guarded-rem core of the
// euclid class), with slot-preserving updates so the default-on structural
// P1.3 gate admits it (see the header comment for why the literal rotation
// cannot reach the semantic VC yet). UNSIGNED `%` so the body is inside the
// covered slice (signed Div/Rem is deliberately out — the INT_MIN/-1
// trap-sentinel spec has no per-statement precondition channel).
const GUARDED_REM_LOOP_PROGRAM: &str = r#"
#[inline(never)]
fn step_sum(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        a = a + (a % b);
        b = b - 1;
    }
    a
}

fn main() {
    std::process::exit((step_sum(252, 105) & 0x7f) as i32);
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
    assert!(status.success(), "cargo build failed; cannot run loop-threading test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_loopvc_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` through the trust-cg backend to an object. With `refine` the
/// FULL refinement lane (`TCG_P3C_REFINE=1`) plus `TCG_REFINE_TRACE=1` are set
/// on the rustc subprocess. Returns `(success, stderr)` — a refuted /
/// inconclusive loop obligation surfaces as a failed compile; the trace lines
/// show which loop VCs fired/skipped.
fn compile_object(stem: &str, src: &str, opt: &str, dylib: &Path, refine: bool) -> (bool, String) {
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
    .arg(format!("-Copt-level={opt}"))
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

#[test]
fn loop_carried_threading_vc_fires_and_refines() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 compile requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();

    // 1. + 2. Gate ON: the compile must SUCCEED (every obligation — including
    // the loop-carried threading VC on the correct guarded-rem loop — Refined)
    // AND the trace must show at least one loop-threading obligation REFINED
    // (the VC fired; it was not silently skipped).
    let (ok, stderr) = compile_object("rem_loop_on", GUARDED_REM_LOOP_PROGRAM, "0", &dylib, true);
    assert!(
        ok,
        "TCG_P3C_REFINE=1 must compile the correct guarded-rem loop, but it FAILED.\nstderr:\n{}",
        stderr.lines().rev().take(20).collect::<Vec<_>>().join("\n")
    );
    let refined_lines: Vec<&str> = stderr
        .lines()
        .filter(|l| l.contains("loop-threading") && l.contains("REFINED"))
        .collect();
    assert!(
        !refined_lines.is_empty(),
        "expected at least one `loop-threading ... REFINED` trace line (the loop VC \
         must FIRE on the guarded-rem loop, not be skipped).\nloop-related stderr:\n{}",
        stderr
            .lines()
            .filter(|l| l.contains("loop-threading"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    // The loop threads TWO loop-carried slots (a, b).
    assert!(
        refined_lines.iter().any(|l| l.contains("2 slot(s)")),
        "expected the loop obligation to carry 2 loop-carried slots; got:\n{}",
        refined_lines.join("\n")
    );

    // 3. GATE OFF: dormant by default — the same program still compiles.
    let (ok_off, stderr_off) =
        compile_object("rem_loop_off", GUARDED_REM_LOOP_PROGRAM, "0", &dylib, false);
    assert!(
        ok_off,
        "with the refinement lane unset the program must still compile.\nstderr:\n{}",
        stderr_off.lines().rev().take(20).collect::<Vec<_>>().join("\n")
    );
    assert!(
        !stderr_off.contains("loop-threading"),
        "gate-off compile must not run the loop-threading VC"
    );

    eprintln!(
        "loop_threading_x86: guarded-rem loop VC fired and REFINED under TCG_P3C_REFINE=1 \
         ({} refined loop obligation(s)); gate-off compile clean.",
        refined_lines.len()
    );
}
