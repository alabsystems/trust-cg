#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Differential regression test for Rust's SATURATING float->int `as` casts on x86_64,
// run under the DEFAULT per-compile proof gate (certs ON).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY DEFAULT CERTS. The x86 CVTT*2SI family (CVTTSS2SI / CVTTSD2SI / ...) returns the
// "integer indefinite" value (the type's MIN, e.g. 0x8000_0000 for 32-bit) on overflow
// or a NaN input — it does NOT saturate. Rust's `as` cast, by contrast, is SATURATING:
// out-of-range -> the target type's MIN/MAX, NaN -> 0, and narrow targets (`f as u8`)
// saturate rather than truncate. So the bridge must lower a float->int cast as the raw
// instruction PLUS saturation fix-ups, and the proof model must verify that COMPOSITE
// against Rust's saturating semantics. The verifier's instruction model was corrected to
// "integer-indefinite on overflow/NaN" (commit b2842e0, #99); this test pins that the
// corrected proof model still (a) ACCEPTS the correct saturating-cast lowering (does not
// fail closed) and (b) the emitted code MATCHES LLVM bit-for-bit. It therefore guards both
// a codegen regression (wrong saturation) AND a proof-completeness regression (correct
// code newly rejected) in one shot — exactly the failure mode a model change can introduce.
//
// ORACLE. The same program compiled by rustc's own LLVM backend at -Copt-level 0 and 3 is
// ground truth (LLVM implements Rust's saturating cast). Each program reduces its cast
// result through a COLLISION-RESISTANT key so a wrong result changes the exit code: for an
// integer result, `((r as <unsigned-same-width> as u64) % 113)` (zero-extend the bits then
// mod a prime <=112 — a naive sign-extended fold would map MIN and MAX to the same value
// and hide the very bug under test). The invariant is exact-MATCH at BOTH opt levels under
// default certs. `black_box` keeps the float input live so the cast runs at runtime.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m117_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn write_panic_stubs(dir: &Path, objs: &[PathBuf]) -> PathBuf {
    let mut nm = Command::new("nm");
    nm.arg("-u");
    for obj in objs {
        nm.arg(obj);
    }
    let nm = nm.output().expect("nm");
    let mut seen = std::collections::BTreeSet::new();
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if toolchain_support::is_abort_stub_symbol(sym) && seen.insert(sym.to_owned()) {
            let c = sym.strip_prefix('_').unwrap_or(sym);
            stubs.push_str(&format!(
                "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
            ));
        }
    }
    let stubs_path = dir.join("stubs.c");
    std::fs::write(&stubs_path, stubs).expect("write stubs");
    stubs_path
}

/// The outcome of compiling+running one program with one backend.
enum Outcome {
    Exit(i32),
    /// The bridge failed to compile / link (fail-closed). Only trust-cg may fail closed.
    FailedClosed,
}

fn compile_link_run(stem: &str, body: &str, opt: &str, dylib: Option<&Path>) -> Outcome {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    let src = format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box as bb;\n{body}\n"
    );
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = toolchain_support::rustc_command();
    cmd.arg("--crate-type").arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
        // NOTE: deliberately do NOT set TCG_NO_PROOF_CERTS — this test exercises the
        // DEFAULT per-compile proof gate so it guards proof-completeness too.
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn trustc");
    if !output.status.success() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!(
            "{stem} (opt={opt}, LLVM): failed to compile. stderr: <<<{}>>>",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    if objs.is_empty() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!("{stem} (opt={opt}, LLVM): no object file produced");
    }

    let stubs_path = write_panic_stubs(&dir, &objs);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    if !link.status.success() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!(
            "{stem} (opt={opt}, LLVM): link failed. stderr: <<<{}>>>",
            String::from_utf8_lossy(&link.stderr)
        );
    }

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    Outcome::Exit(run.status.code().expect("process terminated by signal"))
}

/// Exact MATCH at BOTH opt levels under DEFAULT certs (must compile — not fail closed —
/// and match LLVM). A saturating float->int cast is a fully-supported, proven shape.
fn matches_both_opts(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    for opt in ["0", "3"] {
        let llvm = match compile_link_run(stem, body, opt, None) {
            Outcome::Exit(code) => code,
            Outcome::FailedClosed => unreachable!("LLVM never fails closed"),
        };
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        match compile_link_run(stem, body, opt, Some(&dylib)) {
            Outcome::Exit(trust) => assert_eq!(
                trust, llvm,
                "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} \
                 (float->int saturating-cast MISCOMPILE)"
            ),
            Outcome::FailedClosed => panic!(
                "{stem} (opt={opt}): trust-cg unexpectedly FAILED CLOSED under default certs — \
                 a saturating float->int cast must compile + be proven (proof-completeness regression)"
            ),
        }
    }
}

/// Build a one-cast program: `let f: <fty> = bb(<val>); let r = f as <ity>; reduce(r)`.
/// `uw` is the unsigned type of the same width as `ity` (zero-extend the result bits).
fn cast_prog(fty: &str, val: &str, ity: &str, uw: &str) -> String {
    format!(
        "#[no_mangle] pub extern \"C\" fn main()->i32{{ \
            let f: {fty} = bb({val}); \
            let r = f as {ity}; \
            ((r as {uw} as u64) % 113) as i32 }}"
    )
}

// ───────────────────────────────────────────────────────────────────────────
// Overflow / NaN / infinity on SIGNED targets — must SATURATE to MIN/MAX (NaN->0),
// NOT return the x86 integer-indefinite value.
// ───────────────────────────────────────────────────────────────────────────

/// 1e30_f32 as i32 -> i32::MAX (2147483647). 2147483647 % 113 = 7. (indefinite MIN -> 8.)
#[test]
fn f32_overflow_high_to_i32_saturates_max() {
    matches_both_opts(
        "f32_ovf_hi_i32",
        &cast_prog("f32", "1e30f32", "i32", "u32"),
        7,
    );
}

/// f32::NAN as i32 -> 0. (indefinite -> i32::MIN -> 8.)
#[test]
fn f32_nan_to_i32_is_zero() {
    matches_both_opts(
        "f32_nan_i32",
        &cast_prog("f32", "f32::NAN", "i32", "u32"),
        0,
    );
}

/// +inf as i32 -> i32::MAX -> 7. -inf as i32 -> i32::MIN (2147483648 as u32 % 113 = 8).
#[test]
fn f32_pos_inf_to_i32_saturates_max() {
    matches_both_opts(
        "f32_pinf_i32",
        &cast_prog("f32", "f32::INFINITY", "i32", "u32"),
        7,
    );
}
#[test]
fn f32_neg_inf_to_i32_saturates_min() {
    matches_both_opts(
        "f32_ninf_i32",
        &cast_prog("f32", "f32::NEG_INFINITY", "i32", "u32"),
        8,
    );
}

/// f64 1e300 as i64 -> i64::MAX ; f64::NAN as i64 -> 0.
#[test]
fn f64_overflow_high_to_i64_saturates_max() {
    matches_both_opts(
        "f64_ovf_hi_i64",
        &cast_prog("f64", "1e300f64", "i64", "u64"),
        14,
    );
}
#[test]
fn f64_nan_to_i64_is_zero() {
    matches_both_opts(
        "f64_nan_i64",
        &cast_prog("f64", "f64::NAN", "i64", "u64"),
        0,
    );
}

// ───────────────────────────────────────────────────────────────────────────
// UNSIGNED targets — negative/NaN -> 0, overflow -> type MAX.
// ───────────────────────────────────────────────────────────────────────────

/// 1e30_f32 as u32 -> u32::MAX (4294967295 % 113 = 15).
#[test]
fn f32_overflow_to_u32_saturates_max() {
    matches_both_opts(
        "f32_ovf_u32",
        &cast_prog("f32", "1e30f32", "u32", "u32"),
        15,
    );
}

/// -5.0_f32 as u32 -> 0 (negative -> 0 for unsigned). f32::NAN as u32 -> 0.
#[test]
fn f32_negative_to_u32_is_zero() {
    matches_both_opts("f32_neg_u32", &cast_prog("f32", "-5.0f32", "u32", "u32"), 0);
}
#[test]
fn f32_nan_to_u32_is_zero() {
    matches_both_opts(
        "f32_nan_u32",
        &cast_prog("f32", "f32::NAN", "u32", "u32"),
        0,
    );
}

/// 1e300_f64 as u64 -> u64::MAX (% 113 = 29).
#[test]
fn f64_overflow_to_u64_saturates_max() {
    matches_both_opts(
        "f64_ovf_u64",
        &cast_prog("f64", "1e300f64", "u64", "u64"),
        29,
    );
}

// ───────────────────────────────────────────────────────────────────────────
// NARROW targets — must SATURATE to the narrow range, NOT truncate the low bits.
// (300 as u8 -> 255, not 300 & 0xff = 44.)
// ───────────────────────────────────────────────────────────────────────────

/// 300.0_f32 as u8 -> 255 (saturate). 255 % 113 = 29. (truncation would give 44.)
#[test]
fn f32_to_u8_saturates_not_truncates() {
    matches_both_opts("f32_u8_sat", &cast_prog("f32", "300.0f32", "u8", "u8"), 29);
}

/// -7.0_f32 as u8 -> 0 ; f64 256.7 as u8 -> 255 (29).
#[test]
fn f32_negative_to_u8_is_zero() {
    matches_both_opts("f32_neg_u8", &cast_prog("f32", "-7.0f32", "u8", "u8"), 0);
}
#[test]
fn f64_just_over_u8_saturates_max() {
    matches_both_opts("f64_u8_sat", &cast_prog("f64", "256.7f64", "u8", "u8"), 29);
}

/// 70000.0_f32 as u16 -> 65535 (saturate; truncation would give 4464). 65535 % 113 = 108.
#[test]
fn f32_to_u16_saturates_not_truncates() {
    matches_both_opts(
        "f32_u16_sat",
        &cast_prog("f32", "70000.0f32", "u16", "u16"),
        108,
    );
}

/// 200.0_f32 as i8 -> 127 (14) ; -200.0_f32 as i8 -> -128 (15).
#[test]
fn f32_to_i8_saturates_max() {
    matches_both_opts("f32_i8_hi", &cast_prog("f32", "200.0f32", "i8", "u8"), 14);
}
#[test]
fn f32_to_i8_saturates_min() {
    matches_both_opts("f32_i8_lo", &cast_prog("f32", "-200.0f32", "i8", "u8"), 15);
}

// ───────────────────────────────────────────────────────────────────────────
// In-range truncation (toward zero) — the ordinary path, must stay correct.
// ───────────────────────────────────────────────────────────────────────────

/// 2.9_f64 as i32 -> 2 ; -1.5_f64 as i32 -> -1 (truncate toward zero).
#[test]
fn f64_in_range_truncates_toward_zero_positive() {
    matches_both_opts(
        "f64_trunc_pos",
        &cast_prog("f64", "2.9f64", "i32", "u32"),
        2,
    );
}
#[test]
fn f64_in_range_truncates_toward_zero_negative() {
    matches_both_opts(
        "f64_trunc_neg",
        &cast_prog("f64", "-1.5f64", "i32", "u32"),
        15,
    );
}
