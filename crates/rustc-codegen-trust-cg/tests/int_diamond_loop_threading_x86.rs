#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// crates/rustc-codegen-trust-cg/tests/int_diamond_loop_threading_x86.rs
//
// #84 (proof-gap program) — INTEGER-DISCRIMINANT in-loop diamond back-edge
// threading VC, end to end.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `diamond_loop_threading_x86.rs` covers the BOOL diamond (`if a > b { .. }`),
// which the bridge lowers to `Inst::CondBr`. This file covers the shape that
// actually dominates real optimized code: rustc's INLINED `checked_div` /
// `checked_rem` zero-guard, whose `switchInt` tests an INTEGER discriminant and
// which the bridge therefore lowers to `Inst::Switch`. On a fuzz corpus this one
// shape was the single largest remaining source of compile declines.
//
// Modeling it required three things, each pinned below:
//   * the MIR-spec walk must accept a non-bool switch and MATERIALIZE the arm
//     predicate `OR_i (discr == case_i)` as VC statements;
//   * the trust-ir symexec must model an `Inst::Switch` 2-way diamond at all
//     (it previously bailed with "multiple distinct in-loop successors");
//   * the symexec must FORWARD the `Option<iN>` payload the bridge materializes
//     through a stack slot (`Alloca` / `Store` / `Load`), or the threaded value
//     is an opaque the spec can never match.
//
// What this asserts:
//
//   1. An unsigned `checked_div` guard loop that P1.3 structurally
//      false-rejects COMPILES on the DEFAULT lane, the trace shows
//      "back-edge threading PROVEN (structural misthread admitted via semantic
//      VC)", and the binary's exit code matches the rustc reference backend.
//   2. Same for `checked_rem` at a narrower width.
//   3. KILL SWITCH: `TCG_NO_VC_DIAMOND=1` makes both fail closed with the
//      structural P1.3 rejection.
//   4. NEGATIVE — SIGNED `checked_div`: the signed guard chain is `d != 0` AND
//      NOT(`n == INT_MIN` AND `d == -1`), which is a nested DAG this walker does
//      not model. It must fail closed, and — critically — must NOT report
//      REFUTED: a refutation reads to an operator exactly like a miscompile, and
//      here the model simply stops short. (Were the outer zero-guard modeled
//      alone, the spec's trap-sentinel encoding of `INT_MIN / -1` and the
//      symexec's plain `bvsdiv` would genuinely disagree there and REFUTE.)
//   5. NEGATIVE — an array load inside a diamond arm: fail closed, again with NO
//      REFUTED.
//   6. SSA-071 CELL RETRY: (4) and (5) are declines of the VC MODEL, never
//      refutations, so on the DEFAULT lane the bridge re-lowers them with the
//      misthreaded accumulator in a memory cell (every gate re-run); that compile
//      must be admitted by the retry, with NO refutation, and match the rustc
//      reference. The fail-closed posture of (4)/(5) is asserted with the retry
//      OFF (`no-ssa071-cell-retry`), i.e. it pins what the VC itself does.
//
// Everything is compiled at `-Copt-level=2`: the guard chain only exists once
// rustc has inlined `checked_div`/`checked_rem`.
//
// Run (requires the target-bridge toolchain + x86_64-apple-darwin std, x86 host):
//     cd crates/rustc-codegen-trust-cg
//     targo --unverified test --release --locked --test int_diamond_loop_threading_x86 -- --nocapture

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

// (1) UNSIGNED `checked_div` guard loop. `t0` is an opaque PRE-LOOP local, so
// the bridge threads it through the loop as an INVARIANT header param and the
// accumulator's new value syntactically derives from a DIFFERENT header slot —
// which is exactly what makes P1.3 sub-check (2) fire on correct code. At -O2
// the `checked_div` inlines to `switchInt(p1) -> [0: cold, otherwise: div]`,
// with the division arm building an `Option<u64>` in a stack slot.
// `#[no_mangle]` makes it a required root, so a fail-closed verdict is a FATAL
// compile error rather than a silent skip.
const UDIV_GUARD_PROGRAM: &str = r#"
use std::hint::black_box as bb;

#[no_mangle]
#[inline(never)]
pub fn udiv_guard_loop(p0: u64, p1: u64) -> u64 {
    let t0 = bb(p0);
    let mut a1 = 3u64;
    let mut i1 = 0u64;
    while i1 < 7u64 {
        a1 = (i1).wrapping_mul((t0).checked_div(p1).unwrap_or(1));
        i1 = i1.wrapping_add(1);
    }
    a1
}

fn main() {
    let r = udiv_guard_loop(bb(210u64), bb(7u64));
    std::process::exit((r & 0x7f) as i32);
}
"#;

// (2) The same shape with `checked_rem` at u32 — a different opcode and a
// different discriminant width, so the case-value width check and the URem
// encoders are both exercised.
const UREM_GUARD_PROGRAM: &str = r#"
use std::hint::black_box as bb;

#[no_mangle]
#[inline(never)]
pub fn urem_guard_loop(p0: u32, p1: u32) -> u32 {
    let t0 = bb(p0);
    let mut a1 = 3u32;
    let mut i1 = 0u32;
    while i1 < 9u32 {
        a1 = (i1).wrapping_add((t0).checked_rem(p1).unwrap_or(1));
        i1 = i1.wrapping_add(1);
    }
    a1
}

fn main() {
    let r = urem_guard_loop(bb(211u32), bb(7u32));
    std::process::exit((r & 0x7f) as i32);
}
"#;

// (4) NEGATIVE: SIGNED `checked_div`. rustc emits the `INT_MIN / -1` guards as a
// nested, SHARED-MERGE DAG (not a nested diamond — the arms reconverge outside
// their own arm), which is out of this walker's model.
const SDIV_GUARD_PROGRAM: &str = r#"
use std::hint::black_box as bb;

#[no_mangle]
#[inline(never)]
pub fn sdiv_guard_loop(p0: i64, p1: i64) -> i64 {
    let t0 = bb(p0);
    let mut a1 = 3i64;
    let mut i1 = 0i64;
    while i1 < 7i64 {
        a1 = (i1).wrapping_mul((t0).checked_div(p1).unwrap_or(1));
        i1 = i1.wrapping_add(1);
    }
    a1
}

fn main() {
    let r = sdiv_guard_loop(bb(210i64), bb(7i64));
    std::process::exit((r & 0x7f) as i32);
}
"#;

// (5) NEGATIVE: an ARRAY LOAD inside a diamond arm. Memory the model cannot
// forward must decline, never refute.
const ARRAY_LOAD_ARM_PROGRAM: &str = r#"
use std::hint::black_box as bb;

#[no_mangle]
#[inline(never)]
pub fn arm_array_load(p0: u64, p1: u64) -> u64 {
    let t0 = bb(p0);
    let v: [u64; 4] = [bb(1u64), bb(2u64), bb(3u64), bb(4u64)];
    let mut a1 = 3u64;
    let mut i1 = 0u64;
    while i1 < 7u64 {
        a1 = (i1).wrapping_mul(if p1 > 2 { v[(i1 & 3) as usize] } else { t0 });
        i1 = i1.wrapping_add(1);
    }
    a1
}

fn main() {
    let r = arm_array_load(bb(210u64), bb(7u64));
    std::process::exit((r & 0x7f) as i32);
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
    let dir = std::env::temp_dir().join(format!("rcl2_intdiamond_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` through the trust-cg backend to an object at `-Copt-level=2`
/// (the guard chain only exists after rustc inlines `checked_div`). Returns
/// `(success, stderr)`. `extra_env` carries the `TCG_NO_VC_DIAMOND` kill switch.
fn compile_object(stem: &str, src: &str, dylib: &Path, extra_knobs: &[&str]) -> (bool, String) {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = toolchain_support::rustc_command();
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    // The diamond VC is DEFAULT-ON, so nothing is set to enable it. The trace is
    // what lets the assertions below see the PROVEN line.
    cmd.arg(toolchain_support::backend_knobs_arg(&["refine-trace"]));
    cmd.env_remove("TCG_P3C_REFINE");
    cmd.env_remove("TCG_REFINE");
    cmd.env_remove("TCG_NO_VC_DIAMOND");
    // Backend knobs travel on the TRACKED `-Ztrust-ir-cg-args` option, never in
    // the child's environment: trustc refuses every `TCG_*`/`TRUST_CG_*`
    // variable as an untracked semantic/codegen control, so an environment
    // overlay here would fail the compile before the backend loaded.
    if !extra_knobs.is_empty() {
        cmd.arg(toolchain_support::backend_knobs_arg(extra_knobs));
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
        "-Copt-level=2",
    ])
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

/// Compile `src` to a full binary through the trust-cg backend and run it,
/// returning the process exit code. `None` if the compile/link failed.
fn compile_run(stem: &str, src: &str, dylib: &Path) -> Option<i32> {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    let bin_path = dir.join("prog_bin");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = toolchain_support::rustc_command();
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(&backend_arg);
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
        "-Copt-level=2",
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

/// The rustc reference-backend exit code for `src` — the GROUND TRUTH a newly
/// admitted program must match.
fn reference_run(stem: &str, src: &str) -> Option<i32> {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    let bin_path = dir.join("prog_ref");
    std::fs::write(&src_path, src).expect("write source");
    let output = toolchain_support::rustc_command()
        .env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET)
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
            "-Copt-level=2",
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

/// Assert that `src` compiles on the DEFAULT lane through the semantic VC, that
/// the kill switch turns it back into a fail-closed structural rejection, and
/// that the admitted binary matches the rustc reference exit code.
fn assert_proves_and_matches(stem: &str, src: &str, dylib: &Path) {
    let (ok, stderr) = compile_object(stem, src, dylib, &[]);
    assert!(
        ok,
        "{stem}: the integer-discriminant guard loop must compile on the DEFAULT lane, \
         but it FAILED.\nstderr:\n{}",
        stderr.lines().rev().take(20).collect::<Vec<_>>().join("\n")
    );
    assert!(
        stderr
            .contains("back-edge threading PROVEN (structural misthread admitted via semantic VC)"),
        "{stem}: the compile must be admitted BY PROOF through the semantic VC, not by a \
         weakened structural check; got:\n{}",
        stderr
            .lines()
            .filter(|l| l.contains("PROVEN") || l.contains("diamond") || l.contains("misthread"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        !stderr.contains("REFUTED"),
        "{stem}: an admitted compile must not have produced any refutation:\n{stderr}"
    );

    // GROUND TRUTH: a newly admitted program that does not match LLVM is a
    // miscompile, not a win.
    let got = compile_run(&format!("{stem}_run"), src, dylib);
    let want = reference_run(&format!("{stem}_ref"), src);
    if let Some(want) = want {
        assert_eq!(
            got,
            Some(want),
            "{stem}: admitted program's exit code must match the rustc reference backend \
             (trust-cg={got:?} vs rustc={want:?})"
        );
    } else {
        eprintln!("{stem}: skipping run-differential (reference backend produced no binary)");
    }

    // KILL SWITCH: the same program must fail closed again.
    let (ok_off, stderr_off) =
        compile_object(&format!("{stem}_off"), src, dylib, &["no-vc-diamond"]);
    assert!(
        !ok_off,
        "{stem}: with TCG_NO_VC_DIAMOND=1 the loop must FAIL CLOSED (P1.3), but it compiled."
    );
    assert!(
        stderr_off.contains("ssa/loop-completeness check failed")
            && stderr_off.contains("-Ztrust-ir-cg-args=no-vc-diamond disables modeling it"),
        "{stem}: kill-switch failure must be the structural P1.3 rejection naming the \
         disabled diamond model; got:\n{}",
        stderr_off
            .lines()
            .rev()
            .take(8)
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// Assert that `src` fails closed WITHOUT a refutation — the operator-facing
/// contract for anything the model does not understand. Measured with the
/// SSA-071 cell retry OFF: this pins the VC's own decline posture
/// (`assert_cell_retry_compiles_and_matches` pins the default lane).
fn assert_fails_closed_without_refutation(stem: &str, src: &str, dylib: &Path, why: &str) {
    let (ok, stderr) = compile_object(stem, src, dylib, &["no-ssa071-cell-retry"]);
    assert!(!ok, "{stem}: {why} must fail closed, but it compiled.");
    assert!(
        stderr.contains("[TCG-SSA-071]"),
        "{stem}: the decline must be the SSA-071 structural rejection; got:\n{}",
        stderr.lines().rev().take(8).collect::<Vec<_>>().join("\n")
    );
    assert!(
        !stderr.contains("REFUTED"),
        "{stem}: an out-of-model shape must NEVER read as a refutation — a REFUTED tells \
         an operator the compiler found a real disagreement. Got:\n{}",
        stderr.lines().rev().take(10).collect::<Vec<_>>().join("\n")
    );
}

/// Assert that `src` — a loop the threading VC declines (see
/// `assert_fails_closed_without_refutation`) — COMPILES on the DEFAULT lane
/// through the SSA-071 cell retry (the misthreaded accumulator re-lowered in a
/// memory cell, every gate re-run), with no refutation anywhere, and that the
/// binary matches the rustc reference backend.
fn assert_cell_retry_compiles_and_matches(stem: &str, src: &str, dylib: &Path) {
    let (ok, stderr) = compile_object(stem, src, dylib, &[]);
    assert!(
        ok,
        "{stem}: the SSA-071 cell retry must admit this VC-declined loop on the DEFAULT \
         lane, but it FAILED.\nstderr:\n{}",
        stderr.lines().rev().take(20).collect::<Vec<_>>().join("\n")
    );
    assert!(
        stderr.contains("SSA-071 cell retry admitted"),
        "{stem}: the compile must be admitted BY THE CELL RETRY (re-lowered trust-ir, \
         every gate re-run), not by a weakened check; got:\n{}",
        stderr
            .lines()
            .filter(|l| l.contains("cell retry") || l.contains("PROVEN") || l.contains("SSA-071"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        !stderr.contains("REFUTED"),
        "{stem}: an admitted compile must not have produced any refutation:\n{stderr}"
    );
    let got = compile_run(&format!("{stem}_run"), src, dylib);
    let want = reference_run(&format!("{stem}_ref"), src);
    if let Some(want) = want {
        assert_eq!(
            got,
            Some(want),
            "{stem}: the cell-retry binary's exit code must match the rustc reference \
             backend (trust-cg={got:?} vs rustc={want:?})"
        );
    } else {
        eprintln!("{stem}: skipping run-differential (reference backend produced no binary)");
    }
}

#[test]
fn unsigned_checked_div_loop_proves_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 compile requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    assert_proves_and_matches("udiv", UDIV_GUARD_PROGRAM, &dylib);
}

#[test]
fn unsigned_checked_rem_loop_proves_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 compile requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    assert_proves_and_matches("urem", UREM_GUARD_PROGRAM, &dylib);
}

#[test]
fn signed_checked_div_vc_declines_and_the_cell_retry_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 compile requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    assert_fails_closed_without_refutation(
        "sdiv",
        SDIV_GUARD_PROGRAM,
        &dylib,
        "a signed `checked_div` guard chain (a nested shared-merge DAG)",
    );
    assert_cell_retry_compiles_and_matches("sdiv_cells", SDIV_GUARD_PROGRAM, &dylib);
}

#[test]
fn array_load_in_a_diamond_arm_vc_declines_and_the_cell_retry_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 compile requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    assert_fails_closed_without_refutation(
        "arrload",
        ARRAY_LOAD_ARM_PROGRAM,
        &dylib,
        "an array load inside a diamond arm",
    );
    assert_cell_retry_compiles_and_matches("arrload_cells", ARRAY_LOAD_ARM_PROGRAM, &dylib);
}
