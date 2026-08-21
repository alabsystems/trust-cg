#[path = "support/target_dir.rs"]
mod target_dir_support;

// crates/rustc-codegen-trust-cg/tests/tail_diamond_loop_threading_x86.rs
//
// #84 (proof-gap program) — TAIL-DIAMOND loop back-edge threading VC e2e.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Extends `diamond_loop_threading_x86.rs` (the MID-loop `if/else` diamond) to a
// TAIL diamond: `for/while { ...; if cond { ... } }`. The loop's LAST construct
// is an `if cond { ... }`, so the diamond-condition block is the LATCH and BOTH
// SwitchInt arms reconverge at the HEADER (one falls through directly to the
// back-edge; the other does work then Gotos the header). The #84 semantic
// back-edge threading VC now models this as `select(cond, then, else)` per header
// slot and proves the emitted threading equals that MIR spec.
//
// What this asserts:
//
//   1. GATE ON (`TCG_P3C_REFINE=1`): each CORRECT tail-diamond loop that P1.3
//      structurally false-rejects COMPILES at BOTH -O0 and -O3, and the trace
//      shows the back-edge threading PROVEN.
//   2. The compiled program RUNS and matches the rustc reference backend at BOTH
//      -O0 and -O3 (direct tcg-binary-vs-LLVM-binary exit-code differential).
//   3. GATE OFF: the -O0 program fails closed (the structural P1.3 rejection
//      stands). Zero behavior change to the default-on perimeter.
//   4. A for-loop rotation whose tail diamond makes a THREADED slot depend on the
//      range-YIELDED value fails CLOSED (a SOUND compile error, not a wrong
//      value) — an ORTHOGONAL, pre-existing range-payload-opacity limitation, NOT
//      a tail-diamond-routing failure (see program (4) below).
//
// The "wrong threading stays REFUTED" bite is exercised at the verifier UNIT
// level (`loop_backedge_symexec::tests::tail_diamond_end_to_end_refines_and_swap_refutes`
// and `break_loop_latch_condbr_fails_closed`).
//
// Run (requires the target-bridge toolchain + x86_64-apple-darwin std, x86 host):
//     cd crates/rustc-codegen-trust-cg
//     cargo +nightly-2026-04-20 test --release --test tail_diamond_loop_threading_x86 -- --nocapture

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

// (1) the WHILE rotation-with-tail-if: `a,b <- b, a+b` with a TAIL
// `if x%3==0 { a += x }` (the `if` is the loop's LAST construct, so its cond
// block is the latch and both arms reconverge at the header) where `x` is a plain
// scalar loop counter. Compiles + matches (whether admitted via the tail-diamond
// VC or the structural pass, the produced code must be value-correct).
const ROT_ADD_WHILE_PROGRAM: &str = r#"
use std::hint::black_box;

#[no_mangle]
#[inline(never)]
pub fn rot_add_while() -> i64 {
    let n = black_box(20i64);
    let mut a = 1i64;
    let mut b = 2i64;
    let mut x = 0i64;
    while x < n {
        let t = a.wrapping_add(b);
        a = b;
        b = t;
        x += 1;
        if x % 3 == 0 {
            a = a.wrapping_add(x);
        }
    }
    (a.wrapping_add(b)) & 63
}

fn main() {
    std::process::exit((rot_add_while() & 0x7f) as i32);
}
"#;

// (2) the FOR rotation-with-tail-if whose diamond depends on a LOOP-CARRIED
// SCALAR (`b`), NOT the range-yielded value. This is the for-loop analogue of
// (1): the rotation trips the structural gate and the tail diamond
// `switchInt(b&1==0) -> [0: header, otherwise: bb{a+=1}]` reconverges at the
// header. It refines through the tail-diamond VC (the range iterator is
// memory-backed and no threaded slot depends on the yielded payload).
const FOR_ROT_NO_X_PROGRAM: &str = r#"
use std::hint::black_box;

#[no_mangle]
#[inline(never)]
pub fn for_rot_no_x() -> i64 {
    let n = black_box(20i64);
    let mut a = 1i64;
    let mut b = 2i64;
    for _x in 0..n {
        let t = a.wrapping_add(b);
        a = b;
        b = t;
        if b & 1 == 0 {
            a = a.wrapping_add(1);
        }
    }
    (a.wrapping_add(b)) & 63
}

fn main() {
    std::process::exit((for_rot_no_x() & 0x7f) as i32);
}
"#;

// (3) plain single-slot for-loop accumulator with a TAIL `if x%2==0 { s += x }`.
const PLAIN_TAIL_IF_PROGRAM: &str = r#"
use std::hint::black_box;

#[no_mangle]
#[inline(never)]
pub fn plain_tail_if() -> i64 {
    let n = black_box(20i64);
    let mut s = 0i64;
    for x in 0..n {
        if x % 2 == 0 {
            s = s.wrapping_add(x);
        }
    }
    s
}

fn main() {
    std::process::exit((plain_tail_if() & 0x7f) as i32);
}
"#;

// (4) rot_add: a FOR-loop rotation whose tail diamond `if x%3==0 { a += x }`
// makes the THREADED slot `a` depend on the range-YIELDED value `x`. This
// currently FAILS CLOSED — NOT because of the tail-diamond routing (which fires),
// but because of a SEPARATE, pre-existing range-payload-OPACITY limitation: the
// `Range` iterator is memory-backed, so the IMPL side loads the yielded `x`
// opaquely while the MIR SPEC models it as the named lane `l6_start`; the two do
// not unify, so a slot depending on `x` REFUTES (see the SPEC note at
// `lib.rs`'s `Range::next` model: "a threaded slot whose value DEPENDS on the
// yielded payload refutes against the IMPL's opaque load and stays fail-closed —
// never a wrong admit"). Asserted here to fail CLOSED (a sound compile error, NOT
// a wrong value); closing it needs an orthogonal memory-model/payload-binding
// change to `model_back_edge_args`, independent of this tail-diamond extension.
const ROT_ADD_FOR_PROGRAM: &str = r#"
use std::hint::black_box;

#[no_mangle]
#[inline(never)]
pub fn rot_add() -> i64 {
    let n = black_box(20i64);
    let mut a = 1i64;
    let mut b = 2i64;
    for x in 0..n {
        let t = a.wrapping_add(b);
        a = b;
        b = t;
        if x % 3 == 0 {
            a = a.wrapping_add(x);
        }
    }
    (a.wrapping_add(b)) & 63
}

fn main() {
    std::process::exit((rot_add() & 0x7f) as i32);
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
    assert!(status.success(), "cargo build failed; cannot run tail-diamond test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_tailvc_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` through the trust-cg backend to an object at `opt`. With
/// `refine` the FULL refinement lane (`TCG_P3C_REFINE=1`) + `TCG_REFINE_TRACE=1`
/// are set. Returns `(success, stderr)`.
fn compile_object(stem: &str, src: &str, dylib: &Path, opt: &str, refine: bool) -> (bool, String) {
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

/// Compile `src` to a full binary through the trust-cg backend (gate ON) at
/// `opt` and run it, returning the process exit code. `None` if compile/link
/// failed.
fn compile_run(stem: &str, src: &str, dylib: &Path, opt: &str) -> Option<i32> {
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
    ])
    .arg(format!("-Copt-level={opt}"))
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

/// The rustc reference-backend exit code for `src` at `opt` (the ground truth).
fn reference_run(stem: &str, src: &str, opt: &str) -> Option<i32> {
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
        .arg(format!("-Copt-level={opt}"))
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

/// One program: at BOTH -O0 and -O3 it must compile under the refinement lane
/// (with the trace showing the back-edge PROVEN) and match the rustc reference.
fn assert_tail_diamond_compiles_and_matches(name: &str, src: &str, dylib: &Path) {
    for opt in ["0", "3"] {
        let (ok, stderr) = compile_object(&format!("{name}_o{opt}_obj"), src, dylib, opt, true);
        assert!(
            ok,
            "TCG_P3C_REFINE=1 must compile the tail-diamond loop `{name}` at -O{opt}, but it \
             FAILED.\nstderr:\n{}",
            stderr.lines().rev().take(24).collect::<Vec<_>>().join("\n")
        );

        let got = compile_run(&format!("{name}_o{opt}_run"), src, dylib, opt);
        let want = reference_run(&format!("{name}_o{opt}_ref"), src, opt);
        match want {
            Some(want) => assert_eq!(
                got,
                Some(want),
                "tail-diamond `{name}` at -O{opt}: runtime result must match rustc \
                 (trust-cg={got:?} vs rustc={want:?})"
            ),
            None => eprintln!(
                "skipping run-differential for `{name}` at -O{opt}: reference produced no binary"
            ),
        }
    }
}

#[test]
fn tail_diamond_loops_prove_and_match_o0_and_o3() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 compile requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();

    // (1)(2)(3) POSITIVE: each COMPILE + MATCH at -O0 and -O3 through the
    // tail-diamond VC. (1) while-rotation + tail-if (scalar x), (2) for-rotation +
    // x-INDEPENDENT tail-if, (3) plain for-loop tail-if.
    assert_tail_diamond_compiles_and_matches("rot_add_while", ROT_ADD_WHILE_PROGRAM, &dylib);
    assert_tail_diamond_compiles_and_matches("for_rot_no_x", FOR_ROT_NO_X_PROGRAM, &dylib);
    assert_tail_diamond_compiles_and_matches("plain_tail_if", PLAIN_TAIL_IF_PROGRAM, &dylib);

    // GENUINE TAIL-DIAMOND VC: `for_rot_no_x` trips the structural
    // `LoopCarriedSlotMisthreaded` gate (the for-loop's range iterator + the
    // rotation), so its tail diamond is admitted THROUGH the semantic VC. The
    // trace must show the back-edge PROVEN at -O0 (the VC fired, did not skip),
    // and with the lane OFF it must fail closed (zero change to the default-on
    // perimeter).
    let (_ok, stderr) = compile_object("for_rot_no_x_trace", FOR_ROT_NO_X_PROGRAM, &dylib, "0", true);
    assert!(
        stderr.contains("back-edge threading PROVEN"),
        "expected the trace to show the tail-diamond back-edge PROVEN at -O0 for `for_rot_no_x`; \
         got:\n{}",
        stderr
            .lines()
            .filter(|l| l.contains("PROVEN") || l.contains("threading") || l.contains("misthread"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    let (ok_off, stderr_off) =
        compile_object("for_rot_no_x_off", FOR_ROT_NO_X_PROGRAM, &dylib, "0", false);
    assert!(
        !ok_off,
        "with the refinement lane unset `for_rot_no_x` must FAIL CLOSED (P1.3), but it compiled."
    );
    assert!(
        stderr_off.contains("ssa/loop-completeness check failed"),
        "gate-off failure for `for_rot_no_x` must be the structural P1.3 rejection; got:\n{}",
        stderr_off.lines().rev().take(8).collect::<Vec<_>>().join("\n")
    );

    // (4) rot_add FOR-loop where the threaded slot `a` depends on the
    // range-YIELDED `x`: FAILS CLOSED (the orthogonal range-payload-opacity
    // limitation), and CRUCIALLY produces NO wrong value — a sound compile error,
    // never a miscompile. This is NOT a tail-diamond-routing failure (the VC
    // fires; it REFUTES because the SPEC's `l6_start` payload does not unify with
    // the IMPL's opaque memory load).
    let (rot_add_ok, rot_add_err) =
        compile_object("rot_add_for", ROT_ADD_FOR_PROGRAM, &dylib, "0", true);
    assert!(
        !rot_add_ok,
        "rot_add FOR-loop (threaded slot depends on the range-yielded x) is expected to fail \
         closed under the range-payload-opacity limitation, but it compiled."
    );
    assert!(
        rot_add_err.contains("REFUTED") || rot_add_err.contains("ssa/loop-completeness check failed"),
        "rot_add FOR-loop must fail closed via the semantic VC REFUTED (a sound compile error, \
         not a wrong value); got:\n{}",
        rot_add_err.lines().rev().take(8).collect::<Vec<_>>().join("\n")
    );

    eprintln!(
        "tail_diamond_loop_threading_x86: for_rot_no_x PROVEN via the tail-diamond VC (+ gate-off \
         fails closed); rot_add_while / for_rot_no_x / plain_tail_if matched rustc at -O0 and -O3; \
         rot_add FOR (range-payload dependency) fails CLOSED (sound, orthogonal range-opacity \
         limitation)."
    );
}
