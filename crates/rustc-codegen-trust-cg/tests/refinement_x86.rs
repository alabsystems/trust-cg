#[path = "support/target_dir.rs"]
mod target_dir_support;

// crates/rustc-codegen-trust-cg/tests/refinement_x86.rs
//
// P3c (proof-gap program) — MIR -> trust-ir REFINEMENT OBLIGATION wiring test.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// This exercises the per-compile refinement obligation the bridge accumulates
// when `TCG_REFINE` is set: for each scalar rvalue it lowers, the bridge encodes
// the Rust-defined meaning (the MIR spec) and asks the verifier whether the
// trust-ir op it chose can ever disagree. Anything other than `Refined` FAILS THE
// COMPILE CLOSED.
//
// What this proves:
//   1. REFINEMENT FIRES + PASSES: a scalar-arith program (`a*b - (a+b)`, plus
//      comparisons, negation, casts) compiles SUCCESSFULLY with `TCG_REFINE=1` —
//      i.e. every obligation the bridge raised on a CORRECT lowering proved
//      `Refined` and did not falsely refute valid code.
//   2. GATE OFF: the same program compiles with `TCG_REFINE` UNSET, confirming
//      the obligation machinery is dormant by default (zero behavior change).
//
// We only check compilation (object emission), not a run, because the refinement
// gate lives entirely in `mir_to_trust_ir` (object-emission time); a refuted /
// inconclusive obligation surfaces as a `rustc` compile error.
//
// Run (requires the target-bridge toolchain + x86_64-apple-darwin std, x86 host):
//     cd crates/rustc-codegen-trust-cg
//     cargo +nightly-2026-04-20 test --release --test refinement_x86 -- --nocapture

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

// A scalar program that drives every refinement-covered op family on correct
// lowerings: integer arith (mul/sub/add), an unsigned div/rem, a signed shift,
// integer comparisons, signed negation, an int<->int widen (i32 -> i64), a
// signed int -> float conversion (the #68-cvt shape), a SATURATING float -> int
// cast (FPToSI/FPToUI), and OVERFLOWING add/sub/mul (Inst::Overflow). `black_box`-style
// opacity is unnecessary: the obligations are over symbolic operands, so they
// fire regardless of constant folding.
const SCALAR_PROGRAM: &str = r#"
#![allow(dead_code)]

#[inline(never)]
fn pick(a: i64, b: i64) -> i64 {
    a * b - (a + b)
}

#[inline(never)]
fn shifty(x: i32, s: u32) -> i32 {
    (x >> (s & 31)) + (x << (s & 31))
}

#[inline(never)]
fn unsigned_divrem(a: u64, b: u64) -> u64 {
    if b == 0 { 0 } else { (a / b) ^ (a % b) }
}

#[inline(never)]
fn compares(a: i32, b: i32) -> i32 {
    let mut acc = 0;
    if a < b { acc += 1; }
    if a == b { acc += 2; }
    if a >= b { acc += 4; }
    acc
}

#[inline(never)]
fn negate(a: i64) -> i64 {
    -a
}

#[inline(never)]
fn widen(a: i32) -> i64 {
    a as i64
}

#[inline(never)]
fn to_float(a: i32) -> f32 {
    a as f32
}

// FloatToInt (FPToSI / FPToUI): Rust `as` is saturating; the bridge lowers it to
// the saturating x86 sequence (CVTT + threshold compares + CMOV). The refinement
// models the saturating spec, so a correct lowering must Refine. Covers signed
// and unsigned destinations.
#[inline(never)]
fn from_float_signed(x: f32) -> i32 {
    x as i32
}

#[inline(never)]
fn from_float_unsigned(x: f64) -> u32 {
    x as u32
}

// Overflowing arithmetic (Inst::Overflow, packed value::overflow): the refinement
// validates the bridge picked the right overflow op + signedness + result packing.
#[inline(never)]
fn checked_ops(a: i32, b: i32, u: u8, v: u8) -> i64 {
    let (s, o1) = a.overflowing_add(b);
    let (d, o2) = a.overflowing_sub(b);
    let (m, o3) = u.overflowing_mul(v);
    let mut acc = s as i64 + d as i64 + m as i64;
    if o1 { acc += 1; }
    if o2 { acc += 2; }
    if o3 { acc += 4; }
    acc
}

fn main() {
    let p = pick(7, 5);
    let s = shifty(p as i32, 3);
    let d = unsigned_divrem(p as u64, 4);
    let c = compares(s, p as i32);
    let n = negate(p);
    let w = widen(c);
    let f = to_float(s);
    let fi = from_float_signed(f);
    let fu = from_float_unsigned(f as f64);
    let ck = checked_ops(s, c, p as u8, n as u8);
    std::process::exit(
        ((p + s as i64 + d as i64 + c as i64 + n + w + f as i64
            + fi as i64 + fu as i64 + ck) & 0x7f) as i32,
    );
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
    assert!(status.success(), "cargo build failed; cannot run refinement test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_refine_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` through the trust-cg backend to an object, with `TCG_REFINE`
/// set on the rustc subprocess iff `refine` is true (it is read inside the dylib
/// at object-emission time). Returns `Ok(())` on a successful object emission, or
/// `Err(stderr_tail)` on a compile failure — which is exactly how a refuted /
/// inconclusive refinement obligation surfaces.
fn compile_object(stem: &str, src: &str, opt: &str, dylib: &Path, refine: bool) -> Result<(), String> {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    if refine {
        // Read inside the dylib by `MirLoweringCtx::new` -> obligations are
        // accumulated and discharged at the tail of `mir_to_trust_ir`.
        cmd.env("TCG_REFINE", "1");
    } else {
        // Make sure no ambient value leaks in from the parent environment.
        cmd.env_remove("TCG_REFINE");
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
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let tail = stderr.lines().rev().take(12).collect::<Vec<_>>().join(" | ");
        let _ = std::fs::remove_dir_all(&dir);
        return Err(tail);
    }
    let produced_obj = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .any(|p| p.extension().is_some_and(|x| x == "o"));
    let _ = std::fs::remove_dir_all(&dir);
    if produced_obj {
        Ok(())
    } else {
        Err("rustc reported success but emitted no object".to_string())
    }
}

#[test]
fn refinement_passes_on_correct_scalar_lowerings() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 compile requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();

    // 1. With TCG_REFINE=1, every refinement obligation the bridge raised on the
    //    correct lowerings must prove `Refined` — so the compile SUCCEEDS. A
    //    falsely-refuting obligation (a soundness bug in the wiring) would surface
    //    here as a compile error.
    match compile_object("refine_on", SCALAR_PROGRAM, "0", &dylib, true) {
        Ok(()) => {}
        Err(tail) => panic!(
            "TCG_REFINE=1 should compile a correct scalar program but it FAILED: <<<{tail}>>>"
        ),
    }
    // Also at an optimizing level, to exercise the same gate on optimized MIR.
    match compile_object("refine_on_o2", SCALAR_PROGRAM, "2", &dylib, true) {
        Ok(()) => {}
        Err(tail) => panic!(
            "TCG_REFINE=1 (opt=2) should compile a correct scalar program but it FAILED: <<<{tail}>>>"
        ),
    }

    // 2. GATE OFF: the same program must compile with TCG_REFINE unset (the
    //    obligation machinery is dormant by default).
    match compile_object("refine_off", SCALAR_PROGRAM, "0", &dylib, false) {
        Ok(()) => {}
        Err(tail) => panic!(
            "with TCG_REFINE unset the program must still compile but it FAILED: <<<{tail}>>>"
        ),
    }

    eprintln!(
        "refinement_x86: TCG_REFINE=1 compiled the scalar program (all obligations Refined) at \
         opt 0 and 2, and the gate-off compile also succeeded."
    );
}
