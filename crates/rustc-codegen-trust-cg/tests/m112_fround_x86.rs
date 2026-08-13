// Integration test: `f32::round()` / `f64::round()` via the `roundf*` intrinsic.
//
// `x.round()` lowers (through the float method) to the `roundf32`/`roundf64`
// intrinsic — round to the nearest integer, ties rounded AWAY from zero
// (`round(2.5) = 3`, `round(-2.5) = -3`, `round(0.5) = 1`). It USED to fail
// closed ("unsupported intrinsic `roundf64`"): there is NO SSE round-to-integral
// mode for "ties away from zero" (ROUNDSD/ROUNDSS covers nearest-ties-EVEN /
// floor / ceil / trunc only). The bridge now synthesizes it as a BRANCHLESS
// compose of ALREADY-PROVEN float primitives (no new opcode/proof — the same
// discipline `copysign` follows):
//
//     t      = trunc(x);                      // integer part toward zero (FTrunc)
//     frac   = x - t;                         // EXACT fractional part (FSub)
//     half   = fabs(frac) >= 0.5;             // FAbs + OGe float compare -> Bool
//     bump   = half ? copysign(1.0, x) : copysign(0.0, x);   // select over consts
//     result = t + bump;                      // FAdd
//
// EXACTNESS: the half-way test compares the EXACT fractional part `frac` (which
// is `x - trunc(x)`, exact in IEEE), NOT the naive `trunc(x + 0.5)`. So the
// CRITICAL precision edge `0.49999999999999994` rounds to `0` (its `frac` is
// `< 0.5`) — the value where `trunc(x + 0.5)` would wrongly produce `1`. The
// `else_bump = copysign(0.0, x)` preserves the sign of `-0.0` and of an
// already-integral / infinite input; `copysign(1.0, x)` makes ties round away
// from zero for both signs. f16/f128 fail closed.
//
// Each program is compiled by trust-cg AND LLVM at BOTH -Copt-level=0 and =3,
// run, and the exit codes asserted equal. The hard invariant: trust-cg MUST
// match LLVM or fail closed (produce no binary) — NEVER a different exit code.
// A wrong `round()` would be the exact silent miscompile this forbids.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";

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

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m112_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` at `opt`; returns `Some(bin)` on success, `None` on (trust-cg)
/// compile/link failure (the fail-closed case).
fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: u8,
) -> Option<PathBuf> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if output.status.success() && bin.exists() {
        Some(bin)
    } else {
        None
    }
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// For each (name, body, expected) program, at BOTH O0 and O3: LLVM must produce
/// `expected`, and trust-cg must either MATCH LLVM or FAIL CLOSED (no binary).
fn assert_match_or_fail_closed(dir: &Path, shapes: &[(&str, &str, i32)]) {
    let dylib = ensure_dylib_built();
    for (name, body, expected) in shapes {
        let src = body.to_string();
        for opt in [0u8, 3u8] {
            let llvm_bin = try_compile(dir, &format!("{name}_llvm_{opt}"), &src, None, opt)
                .unwrap_or_else(|| panic!("LLVM compile of `{name}` @O{opt} failed"));
            let llvm_exit = run_exit_code(&llvm_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` @O{opt} is {llvm_exit}, expected {expected}"
            );
            match try_compile(dir, &format!("{name}_tcg_{opt}"), &src, Some(&dylib), opt) {
                Some(tcg_bin) => {
                    let tcg_exit = run_exit_code(&tcg_bin);
                    assert_eq!(
                        tcg_exit, llvm_exit,
                        "MISCOMPILE: trust-cg exit for `{name}` @O{opt} is {tcg_exit}, \
                         LLVM is {llvm_exit} (must match or fail closed)"
                    );
                }
                None => {
                    eprintln!("note: `{name}` @O{opt} failed closed under trust-cg (safe)");
                }
            }
        }
    }
}

#[test]
fn fround_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("re");
    // Each program black_box-es its float input (so `round()` runs on a runtime
    // value, not a const-fold), rounds, and derives the exit code from the result
    // so a wrong rounding flips the observable exit code. The `+offset` keeps the
    // exit in `0..=125`.
    let shapes: &[(&str, &str, i32)] = &[
        // ===================== f64 — the precision-critical edge =====================
        // 0.49999999999999994 MUST round to 0. The naive `trunc(x+0.5)` would give 1
        // (x+0.5 rounds UP to exactly 1.0). This is the whole reason for the exact
        // `x - trunc(x)` fractional-part compare.
        ("f64_edge_below_half",
         "fn main(){ let x=std::hint::black_box(0.49999999999999994f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         50),                                   // round -> 0
        ("f64_edge_neg_below_half",
         "fn main(){ let x=std::hint::black_box(-0.49999999999999994f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         50),                                   // round -> 0
        // ===================== f64 — ties away from zero =====================
        ("f64_half_pos",
         "fn main(){ let x=std::hint::black_box(0.5f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         51),                                   // -> 1
        ("f64_half_neg",
         "fn main(){ let x=std::hint::black_box(-0.5f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         49),                                   // -> -1
        ("f64_2p5",
         "fn main(){ let x=std::hint::black_box(2.5f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         53),                                   // -> 3
        ("f64_neg2p5",
         "fn main(){ let x=std::hint::black_box(-2.5f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         47),                                   // -> -3
        ("f64_3p7",
         "fn main(){ let x=std::hint::black_box(3.7f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         54),                                   // -> 4
        ("f64_2p4",
         "fn main(){ let x=std::hint::black_box(2.4f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         52),                                   // -> 2
        ("f64_neg2p4",
         "fn main(){ let x=std::hint::black_box(-2.4f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         48),                                   // -> -2
        // ===================== f64 — already integral / large =====================
        ("f64_2p0",
         "fn main(){ let x=std::hint::black_box(2.0f64); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         52),                                   // -> 2
        // 1e16 is a large EXACT integer (> 2^53? no, 1e16 < 2^54 and is exactly
        // representable). round() is the identity; fold mod 126 to keep in range.
        ("f64_1e16",
         "fn main(){ let x=std::hint::black_box(1e16f64); \
          std::process::exit((((x.round() as i64).rem_euclid(126))) as i32); }",
         (1e16_f64 as i64).rem_euclid(126) as i32),
        // -0.0 round is -0.0 (LLVM). As an integer both -0.0 and +0.0 are 0; we also
        // probe the sign bit via `is_sign_negative()` so a +0.0 result would flip it.
        ("f64_neg_zero_sign",
         "fn main(){ let x=std::hint::black_box(-0.0f64); let r=x.round(); \
          std::process::exit((((r.is_sign_negative() as i64)*2 + (r==0.0) as i64) + 40) as i32); }",
         43),                                   // -0.0: sign_negative=1, ==0.0=1 -> 40+3
        ("f64_pos_zero_sign",
         "fn main(){ let x=std::hint::black_box(0.0f64); let r=x.round(); \
          std::process::exit((((r.is_sign_negative() as i64)*2 + (r==0.0) as i64) + 40) as i32); }",
         41),                                   // +0.0: sign_negative=0, ==0.0=1 -> 40+1
        // ===================== f64 — NaN / inf via predicates =====================
        ("f64_nan_is_nan",
         "fn main(){ let x=std::hint::black_box(f64::NAN); \
          std::process::exit(((x.round().is_nan() as i64) + 60) as i32); }",
         61),                                   // round(NaN).is_nan() -> 1
        ("f64_inf",
         "fn main(){ let x=std::hint::black_box(f64::INFINITY); let r=x.round(); \
          std::process::exit((((r.is_infinite() as i64)*2 + (r > 0.0) as i64) + 60) as i32); }",
         63),                                   // +inf: infinite=1, >0=1 -> 60+3
        ("f64_neg_inf",
         "fn main(){ let x=std::hint::black_box(f64::NEG_INFINITY); let r=x.round(); \
          std::process::exit((((r.is_infinite() as i64)*2 + (r < 0.0) as i64) + 60) as i32); }",
         63),                                   // -inf: infinite=1, <0=1 -> 60+3
        // ===================== f32 analogues =====================
        // 0.49999997f32 is the largest f32 strictly below 0.5 -> rounds to 0.
        ("f32_edge_below_half",
         "fn main(){ let x=std::hint::black_box(0.49999997f32); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         50),                                   // -> 0
        ("f32_half_pos",
         "fn main(){ let x=std::hint::black_box(0.5f32); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         51),                                   // -> 1
        ("f32_half_neg",
         "fn main(){ let x=std::hint::black_box(-0.5f32); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         49),                                   // -> -1
        // 4.5f32 round-half-away -> 5 (NOT 4 as round-ties-even would give).
        ("f32_4p5",
         "fn main(){ let x=std::hint::black_box(4.5f32); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         55),                                   // -> 5
        ("f32_neg4p5",
         "fn main(){ let x=std::hint::black_box(-4.5f32); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         45),                                   // -> -5
        ("f32_2p4",
         "fn main(){ let x=std::hint::black_box(2.4f32); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         52),                                   // -> 2
        ("f32_3p7",
         "fn main(){ let x=std::hint::black_box(3.7f32); \
          std::process::exit(((x.round() as i64) + 50) as i32); }",
         54),                                   // -> 4
        ("f32_neg_zero_sign",
         "fn main(){ let x=std::hint::black_box(-0.0f32); let r=x.round(); \
          std::process::exit((((r.is_sign_negative() as i64)*2 + (r==0.0) as i64) + 40) as i32); }",
         43),                                   // -0.0 preserved
        ("f32_nan_is_nan",
         "fn main(){ let x=std::hint::black_box(f32::NAN); \
          std::process::exit(((x.round().is_nan() as i64) + 60) as i32); }",
         61),
        ("f32_inf",
         "fn main(){ let x=std::hint::black_box(f32::INFINITY); let r=x.round(); \
          std::process::exit((((r.is_infinite() as i64)*2 + (r > 0.0) as i64) + 60) as i32); }",
         63),
        // ===================== CONTROL: no round, must stay correct =====================
        ("control_no_round",
         "fn main(){ let a=std::hint::black_box(40u32); let b=std::hint::black_box(2u32); \
          std::process::exit((a+b) as i32); }",
         42),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}
