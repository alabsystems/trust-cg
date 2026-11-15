#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

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
//   1. A CORRECT diamond-body loop that P1.3 structurally false-rejects
//      COMPILES, and the trace shows the back-edge threading PROVEN (the diamond
//      VC fired and Refined — not skipped).
//   2. The compiled program RUNS and matches the rustc reference backend (the
//      admitted diamond code is value-correct, not just accepted).
//   2b. It compiles on the DEFAULT lane too. Diamond modeling has its own knob
//      (`TCG_NO_VC_DIAMOND`, default ON) rather than riding on the per-op P3C
//      lane: the two are unrelated, and conflating them left half of this
//      program class unrescuable even with `TCG_P3C_REFINE=1` set (the per-op
//      lane fails first on `SDiv`/`SRem` certificates). Default-on cannot slow a
//      compile that succeeds today — this VC only runs AFTER the structural
//      check has already produced a violation.
//   3. KILL SWITCH (`TCG_NO_VC_DIAMOND=1`): the SAME program fails closed (the
//      structural P1.3 rejection stands; a `#[no_mangle]` root surfaces the
//      failure as a fatal compile error).
//   4. OUT-OF-MODEL (a >2-way `match` in the loop body): the VC DECLINES it EVEN
//      with modeling on — the diamond modeling refuses anything it cannot model
//      exactly, so it can never over-admit. Pinned with the SSA-071 cell retry
//      OFF (`no-ssa071-cell-retry`): that is the VC's own posture.
//   4b. On the DEFAULT lane that decline (never a refutation) hands the loop to
//      the SSA-071 cell retry: the flagged slot is re-lowered in a memory cell,
//      every gate re-runs, and the program COMPILES. Compile-only: with
//      `-Coverflow-checks=off` it does not terminate for (252, 105).
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
//     targo --unverified test --release --locked --test diamond_loop_threading_x86 -- --nocapture

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;
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

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
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
    compile_object_env(stem, src, dylib, refine, &[])
}

/// As [`compile_object`], plus extra environment variables (used to exercise the
/// `TCG_NO_VC_DIAMOND` kill switch).
fn compile_object_env(
    stem: &str,
    src: &str,
    dylib: &Path,
    refine: bool,
    extra_knobs: &[&str],
) -> (bool, String) {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = toolchain_support::rustc_command();
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    // This test exercises the back-edge threading VC, not proof-certificate
    // promotion. Mirrors ssa071_shape_a_rescue.rs, which sets the same var:
    // without it the compile dies in the (currently upstream-broken)
    // promotion policy with [TCG-PROOF-465] and tells us nothing about
    // diamond modelling.
    cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    // Backend knobs travel on the TRACKED `-Ztrust-ir-cg-args` option, never in
    // the child's environment: trustc refuses every `TCG_*`/`TRUST_CG_*`
    // variable as an untracked semantic/codegen control, so an environment
    // overlay here would fail the compile before the backend loaded.
    if !extra_knobs.is_empty() {
        cmd.arg(toolchain_support::backend_knobs_arg(extra_knobs));
    }
    if refine {
        cmd.arg(toolchain_support::backend_knobs_arg(&["p3c-refine"]));
        cmd.arg(toolchain_support::backend_knobs_arg(&["refine-trace"]));
    } else {
        cmd.env_remove("TCG_P3C_REFINE");
        cmd.env_remove("TCG_REFINE");
        cmd.env_remove("TCG_REFINE_TRACE");
    }
    cmd.arg("--crate-type").arg("bin");
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
    let output = cmd.output().expect("failed to spawn trustc");
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

    let mut cmd = toolchain_support::rustc_command();
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    // This test exercises the back-edge threading VC, not proof-certificate
    // promotion. Mirrors ssa071_shape_a_rescue.rs, which sets the same var:
    // without it the compile dies in the (currently upstream-broken)
    // promotion policy with [TCG-PROOF-465] and tells us nothing about
    // diamond modelling.
    cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    cmd.arg(toolchain_support::backend_knobs_arg(&["p3c-refine"]));
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
    let output = cmd.output().expect("failed to spawn trustc");
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
    let output = toolchain_support::rustc_command()
        .env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET)
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
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
        assert_eq!(
            want, 21,
            "gcd(252,105) & 0x7f must be 21 (sanity on the reference)"
        );
    } else {
        eprintln!("skipping run-differential: reference backend produced no binary (linker env)");
    }

    // 2b. DEFAULT LANE: the diamond model is no longer keyed off the per-op P3C
    //     lane — it has its own knob (`TCG_NO_VC_DIAMOND`), default ON. So the
    //     SAME program must compile and prove with NO environment set at all.
    //     (Default-on cannot slow any compile that succeeds today: this VC only
    //     runs after the structural check has already produced a violation, i.e.
    //     on a compile that fails without it.)
    let (ok_default, stderr_default) =
        compile_object("diamond_default", DIAMOND_LOOP_PROGRAM, &dylib, false);
    assert!(
        ok_default,
        "the diamond-body loop must compile on the DEFAULT lane (diamond modeling is \
         default-on), but it FAILED.\nstderr:\n{}",
        stderr_default
            .lines()
            .rev()
            .take(20)
            .collect::<Vec<_>>()
            .join("\n")
    );

    // 3. KILL SWITCH: with `TCG_NO_VC_DIAMOND=1` the same program fails closed
    //    (the P1.3 structural rejection stands).
    let (ok_off, stderr_off) = compile_object_env(
        "diamond_off",
        DIAMOND_LOOP_PROGRAM,
        &dylib,
        false,
        &["no-vc-diamond"],
    );
    assert!(
        !ok_off,
        "with TCG_NO_VC_DIAMOND=1 the diamond-body loop must FAIL CLOSED (P1.3), \
         but it compiled."
    );
    assert!(
        stderr_off.contains("ssa/loop-completeness check failed")
            && stderr_off.contains("-Ztrust-ir-cg-args=no-vc-diamond disables modeling it"),
        "kill-switch failure must be the structural P1.3 rejection naming the disabled \
         diamond model; got:\n{}",
        stderr_off
            .lines()
            .rev()
            .take(8)
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        !stderr_off.contains("back-edge threading PROVEN"),
        "kill-switch compile must NOT prove the diamond back-edge"
    );

    // 4. OUT-OF-MODEL (3-way match): the VC must DECLINE it EVEN under the gate.
    //    Measured with the SSA-071 cell retry OFF — the VC's own posture (4b pins
    //    the default lane).
    let (ok_3way, stderr_3way) = compile_object_env(
        "threeway_on",
        THREE_WAY_PROGRAM,
        &dylib,
        true,
        &["no-ssa071-cell-retry"],
    );
    assert!(
        !ok_3way,
        "a >2-way match loop body is out of the VC slice and must fail closed even under \
         the gate, but it compiled."
    );
    assert!(
        stderr_3way.contains("out of VC slice")
            || stderr_3way.contains("non-bool discriminant")
            || stderr_3way.contains("distinct switch successors"),
        "3-way out-of-model failure must name the VC-slice limit; got:\n{}",
        stderr_3way
            .lines()
            .rev()
            .take(8)
            .collect::<Vec<_>>()
            .join("\n")
    );

    // 4b. DEFAULT LANE: the decline is not a refutation, so the SSA-071 cell retry
    //     re-lowers the flagged slot in a memory cell and re-runs every gate; the
    //     3-way loop must COMPILE, admitted BY THE RETRY, with no refutation.
    //     Compile-only (the program does not terminate; see the header).
    let (ok_3way_default, stderr_3way_default) = compile_object_env(
        "threeway_default",
        THREE_WAY_PROGRAM,
        &dylib,
        false,
        &["refine-trace"],
    );
    assert!(
        ok_3way_default,
        "on the default lane the SSA-071 cell retry must admit the 3-way loop the VC \
         declines, but it FAILED.\nstderr:\n{}",
        stderr_3way_default
            .lines()
            .rev()
            .take(20)
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        stderr_3way_default.contains("SSA-071 cell retry admitted"),
        "the 3-way loop must be admitted BY THE CELL RETRY (re-lowered trust-ir, every \
         gate re-run), not by a weakened check; got:\n{}",
        stderr_3way_default
            .lines()
            .filter(|l| l.contains("cell retry") || l.contains("PROVEN") || l.contains("SSA-071"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        !stderr_3way_default.contains("REFUTED"),
        "an admitted compile must not have produced any refutation:\n{stderr_3way_default}"
    );

    eprintln!(
        "diamond_loop_threading_x86: diamond VC fired + PROVEN (under TCG_P3C_REFINE=1 and on \
         the default lane), runtime result matched rustc, TCG_NO_VC_DIAMOND=1 fails closed \
         (P1.3), 3-way declined by the VC (cell retry off) and admitted by the SSA-071 cell \
         retry on the default lane."
    );
}
