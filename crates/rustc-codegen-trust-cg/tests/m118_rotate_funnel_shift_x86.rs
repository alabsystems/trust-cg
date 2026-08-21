#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential regression test for `{u,i}*::rotate_left` / `rotate_right` on x86_64,
// run under the DEFAULT per-compile proof gate (certs ON).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// COMPLETENESS FIX UNDER TEST. On this toolchain, `x.rotate_left(c)` /
// `x.rotate_right(c)` lower (in the rotate fallback body) to the funnel-shift
// intrinsics `unchecked_funnel_shl` / `unchecked_funnel_shr` plus `disjoint_bitor`,
// which the bridge previously did NOT handle — so every rotate FAILED CLOSED. The
// bridge now synthesizes the funnel shift over ALREADY-PROVEN primitives (no new
// opcode/proof), entirely in a clean masked I64 carrier so a narrow / signed
// operand rotates LOGICALLY:
//   eff        = count & (w-1)
//   funnel_shl = ((a << eff) | ((b >> (w-1-eff)) >> 1)) & maskW
//   funnel_shr = (((a << (w-1-eff)) << 1) | (b >> eff)) & maskW
//   disjoint_bitor(a,b) = a | b
// The SPLIT shift keeps every shift amount in [0, w-1], so a count of 0 (or any
// multiple of w) is well-defined WITHOUT a shift-by-width (UB): the second term
// vanishes and the result is the operand unchanged. For a rotate, a == b.
//
// This test pins that rotate now (a) COMPILES under the default proof gate (no
// fail-close — the composition discharges) and (b) MATCHES LLVM bit-for-bit across
// widths u8/u16/u32/u64 + signed i8/i32/i64, shift amounts 0 / 1 / mid / w-1 /
// >= w (masked mod w), and a runtime (non-constant) shift. The differential oracle
// is rustc's own LLVM backend at -Copt-level 0 and 3; each program reduces the
// rotated value through `(bits-as-unsigned % 113)` so a wrong rotation changes the
// exit. `black_box` keeps the input (and any runtime shift) live.

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
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m118 test");
    let built = target_dir
        .join("release")
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

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m118_{stem}_{}", std::process::id()));
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
        if sym.contains("panic") && seen.insert(sym.to_owned()) {
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

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
        // Default proof gate (no TCG_NO_PROOF_CERTS): rotate must compile AND prove.
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
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

/// Exact MATCH at BOTH opt levels under DEFAULT certs (rotate must compile — not
/// fail closed — and match LLVM). The funnel-shift composition is a proven shape.
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
                "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} (rotate MISCOMPILE)"
            ),
            Outcome::FailedClosed => panic!(
                "{stem} (opt={opt}): trust-cg unexpectedly FAILED CLOSED — rotate must compile + \
                 prove (the funnel-shift completeness fix regressed)"
            ),
        }
    }
}

/// `let x: <ty> = bb(<val>); ((x.<method>(<shift>) as <uw> as u64) % 113) as i32`.
fn rot_prog(ty: &str, val: &str, method: &str, shift: &str, uw: &str) -> String {
    format!(
        "#[no_mangle] pub extern \"C\" fn main()->i32{{ \
            let x: {ty} = bb({val}); \
            ((x.{method}({shift}) as {uw} as u64) % 113) as i32 }}"
    )
}

// ── u32 rotate_left: shift 0 / 1 / mid / w-1 / >= w (masked mod w) ──────────────

#[test]
fn u32_rotate_left_by_zero_is_identity() {
    // shift 0 -> identity. 0x12345678 % 113 = 106. (Pins the split-shift no-UB path.)
    matches_both_opts("u32_rotl_0", &rot_prog("u32", "0x12345678", "rotate_left", "0", "u32"), 106);
}
#[test]
fn u32_rotate_left_by_one() {
    matches_both_opts("u32_rotl_1", &rot_prog("u32", "0x12345678", "rotate_left", "1", "u32"), 99);
}
#[test]
fn u32_rotate_left_by_eight() {
    matches_both_opts("u32_rotl_8", &rot_prog("u32", "0x12345678", "rotate_left", "8", "u32"), 85);
}
#[test]
fn u32_rotate_left_by_width_minus_one() {
    matches_both_opts("u32_rotl_31", &rot_prog("u32", "0x12345678", "rotate_left", "31", "u32"), 53);
}
#[test]
fn u32_rotate_left_by_more_than_width_is_masked() {
    // 35 mod 32 = 3. Pins the count & (w-1) masking.
    matches_both_opts("u32_rotl_35", &rot_prog("u32", "0x12345678", "rotate_left", "35", "u32"), 57);
}

// ── u32 rotate_right ───────────────────────────────────────────────────────────

#[test]
fn u32_rotate_right_by_zero_is_identity() {
    matches_both_opts("u32_rotr_0", &rot_prog("u32", "0x12345678", "rotate_right", "0", "u32"), 106);
}
#[test]
fn u32_rotate_right_by_twelve() {
    matches_both_opts("u32_rotr_12", &rot_prog("u32", "0x12345678", "rotate_right", "12", "u32"), 108);
}
#[test]
fn u32_rotate_right_by_width_minus_one() {
    matches_both_opts("u32_rotr_31", &rot_prog("u32", "0x12345678", "rotate_right", "31", "u32"), 99);
}

// ── u64 ──────────────────────────────────────────────────────────────────────

#[test]
fn u64_rotate_left_by_zero_is_identity() {
    matches_both_opts("u64_rotl_0", &rot_prog("u64", "0x0123456789ABCDEF", "rotate_left", "0", "u64"), 98);
}
#[test]
fn u64_rotate_left_by_twenty() {
    matches_both_opts("u64_rotl_20", &rot_prog("u64", "0x0123456789ABCDEF", "rotate_left", "20", "u64"), 64);
}
#[test]
fn u64_rotate_right_by_sixtythree() {
    matches_both_opts("u64_rotr_63", &rot_prog("u64", "0x0123456789ABCDEF", "rotate_right", "63", "u64"), 83);
}

// ── u8 / u16 (narrow carriers) ────────────────────────────────────────────────

#[test]
fn u8_rotate_left_by_zero_is_identity() {
    matches_both_opts("u8_rotl_0", &rot_prog("u8", "0b10110010", "rotate_left", "0", "u8"), 65);
}
#[test]
fn u8_rotate_left_by_three() {
    matches_both_opts("u8_rotl_3", &rot_prog("u8", "0b10110010", "rotate_left", "3", "u8"), 36);
}
#[test]
fn u8_rotate_left_by_width_is_identity() {
    // shift 8 == 8 mod 8 == 0 -> identity (== u8_rotl_0).
    matches_both_opts("u8_rotl_8", &rot_prog("u8", "0b10110010", "rotate_left", "8", "u8"), 65);
}
#[test]
fn u16_rotate_right_by_four() {
    matches_both_opts("u16_rotr_4", &rot_prog("u16", "0xABCD", "rotate_right", "4", "u16"), 61);
}

// ── SIGNED rotates — must rotate LOGICALLY (bits move regardless of sign) ───────

#[test]
fn i32_rotate_left_negative_is_logical() {
    matches_both_opts("i32_rotl_8", &rot_prog("i32", "-1000003i32", "rotate_left", "8", "u32"), 99);
}
#[test]
fn i8_rotate_left_negative_is_logical() {
    matches_both_opts("i8_rotl_3", &rot_prog("i8", "-100i8", "rotate_left", "3", "u8"), 2);
}
#[test]
fn i64_rotate_right_negative_is_logical() {
    matches_both_opts("i64_rotr_16", &rot_prog("i64", "-77i64", "rotate_right", "16", "u64"), 34);
}

// ── runtime (non-constant) shift amount ───────────────────────────────────────

#[test]
fn u32_rotate_left_runtime_shift() {
    matches_both_opts(
        "u32_rotl_var",
        "#[no_mangle] pub extern \"C\" fn main()->i32{ \
            let x:u32=bb(0xDEADBEEF); let s:u32=bb(13); \
            ((x.rotate_left(s) as u64) % 113) as i32 }",
        41,
    );
}
#[test]
fn u32_rotate_left_runtime_shift_zero() {
    // runtime shift == 0 -> identity. 0xDEADBEEF % 113 = 77.
    matches_both_opts(
        "u32_rotl_var0",
        "#[no_mangle] pub extern \"C\" fn main()->i32{ \
            let x:u32=bb(0xDEADBEEF); let s:u32=bb(0); \
            ((x.rotate_left(s) as u64) % 113) as i32 }",
        77,
    );
}
