// Differential regression tests for MISCOMPILES #59, #60, #61, #62, #63 — five
// x86-64 lowering bugs found by adversarial differential fuzzing of the bridge
// against rustc's default LLVM backend:
//
//   #59  Float-to-int `as` casts were non-saturating: the narrow-unsigned path
//        trapped (`UD2` -> SIGILL) and the 64-bit path emitted a bare
//        `cvtt..2si` returning the x86 integer-indefinite (0x8000…0) for
//        NaN/overflow instead of Rust's saturation (NaN->0, clamp to MIN/MAX).
//        Fix: saturating fp-to-int lowering (CMOV-clamped) in `x86_64_isel.rs`.
//   #60  Narrow (i8/u8/i16/u16) shift counts were not masked to `width-1`. The
//        32-bit carrier shift masks the count mod 32, but Rust masks mod 8/16,
//        so `1u8 << 8` gave 0 instead of 1. Fix: AND the count to `width-1`.
//   #61  Wide (>=2^31) `u64` switch/match case constants — already handled by
//        register-materialized `CmpRR`; locked in here as a guard.
//   #62  High-bit narrow-unsigned switch case constants (`0xFF`u8, `0x8000`u16)
//        were SIGN-normalized (0xFF -> -1), but the selector is zero-extended
//        before the equality compare, so the case never matched. Fix:
//        zero-extend narrow case constants in `adapter.rs`.
//   #63  O0 array-element loads under register pressure — already fixed on the
//        current O0 regalloc; locked in here as a determinism guard.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend. Each case is compiled twice — once with `-Zcodegen-backend=<trust-cg
// dylib>` and once without — linked the same way, run, and the process exit
// codes are required to be EQUAL (and equal to the documented expected value).
// `core::hint::black_box` defeats const-folding so the narrowing cast and the
// signed op are materialized as real runtime instructions at every -Copt-level.
//
// The crate is `#![no_std] #![no_main]` exposing `#[no_mangle] pub extern "C" fn
// main() -> i32`, so the bridge compiles `main` directly and we avoid the std
// `std::rt::lang_start` entry path. Abort stubs are supplied for any referenced
// `panic_const_*` symbols (the overflow / div-by-zero checks never fire at the
// chosen inputs), so the LLVM object links standalone exactly like the trust-cg
// object (which drops those unreachable checks).

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m51 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m5963_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Write a C file with `abort()` stubs for every undefined `panic*` symbol the
/// object references, so the object links standalone (these checks never fire at
/// the chosen inputs). Returns the path to the generated stub file.
fn write_panic_stubs(dir: &Path, obj: &Path) -> PathBuf {
    let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if sym.contains("panic") {
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

/// Compile `src` (with the given backend), link with abort stubs, run, and
/// return the process exit code. When `dylib` is `Some`, the trust-cg codegen
/// backend is used; when `None`, rustc's default LLVM backend is used (the
/// differential oracle). All emitted `.o` codegen units are linked together (a
/// `black_box` call may live in its own CGU object).
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> i32 {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        // `--out-dir` (not `-o`) so EVERY codegen unit object is written with a
        // `.o` extension under both backends: rustc's LLVM backend emits a single
        // `prog.o`, while the trust-cg backend emits one `prog.<cgu>.rcgu.o` per
        // CGU (a `black_box` call lives in its own CGU). A bare `-o <name>` would
        // instead produce an extension-less file for the single-CGU LLVM build.
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{stem} (opt={opt}, backend={}): failed to compile. stderr: <<<{stderr}>>>",
        if dylib.is_some() { "trust-cg" } else { "llvm" }
    );

    // Collect every emitted object codegen unit (the bridge / rustc name them
    // after the CGU, and a `black_box` call may be its own CGU).
    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(
        !objs.is_empty(),
        "{stem} (opt={opt}): no object file produced"
    );

    let stubs_path = write_panic_stubs(&dir, &objs[0]);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "{stem} (opt={opt}): link failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    run.status.code().expect("process terminated by signal")
}

/// Compile `body` with BOTH backends at -Copt-level 0 and 3 and require the
/// trust-cg exit code to equal the LLVM exit code AND the documented `expected`.
fn differential_case(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         #[no_mangle]\npub extern \"C\" fn main() -> i32 {{\n{body}\n}}\n"
    );
    for opt in ["0", "3"] {
        let llvm = compile_link_run(stem, &src, opt, None);
        let trust = compile_link_run(stem, &src, opt, Some(&dylib));
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        assert_eq!(
            trust, llvm,
            "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} (miscompile)"
        );
    }
}

// ---------------------------------------------------------------------------
// #59 — saturating float-to-int `as` casts
// ---------------------------------------------------------------------------

/// `-1.0f32 as u8` saturates to 0 (was a `UD2` SIGILL trap).
#[test]
fn m59_neg_float_to_u8_saturates_to_zero() {
    differential_case("f32_neg_u8", "    core::hint::black_box(-1.0f32) as u8 as i32", 0);
}

/// `300.0f32 as u8` saturates to 255 (out-of-range high).
#[test]
fn m59_big_float_to_u8_saturates_to_max() {
    differential_case("f32_big_u8", "    core::hint::black_box(300.0f32) as u8 as i32", 255);
}

/// `NaN as u8` is 0.
#[test]
fn m59_nan_to_u8_is_zero() {
    differential_case("f32_nan_u8", "    core::hint::black_box(f32::NAN) as u8 as i32", 0);
}

/// `1e30f64 as i64` saturates to `i64::MAX` (was a silent indefinite 0x8000…0).
#[test]
fn m59_huge_f64_to_i64_saturates_to_max() {
    differential_case(
        "f64_huge_i64",
        "    ((core::hint::black_box(1e30f64) as i64) == i64::MAX) as i32",
        1,
    );
}

/// `-1e30f64 as i64` saturates to `i64::MIN`.
#[test]
fn m59_huge_neg_f64_to_i64_saturates_to_min() {
    differential_case(
        "f64_hugeneg_i64",
        "    ((core::hint::black_box(-1e30f64) as i64) == i64::MIN) as i32",
        1,
    );
}

/// `1e30f64 as u64` saturates to `u64::MAX` (the bias-split + clamp path).
#[test]
fn m59_huge_f64_to_u64_saturates_to_max() {
    differential_case(
        "f64_huge_u64",
        "    ((core::hint::black_box(1e30f64) as u64) == u64::MAX) as i32",
        1,
    );
}

/// `-5.0f64 as u32` saturates to 0.
#[test]
fn m59_neg_f64_to_u32_is_zero() {
    differential_case("f64_neg_u32", "    core::hint::black_box(-5.0f64) as u32 as i32", 0);
}

/// `1e20f32 as i32` saturates to `i32::MAX`.
#[test]
fn m59_huge_f32_to_i32_saturates_to_max() {
    differential_case(
        "f32_huge_i32",
        "    ((core::hint::black_box(1e20f32) as i32) == i32::MAX) as i32",
        1,
    );
}

// ---------------------------------------------------------------------------
// #60 — narrow shift count masked to width-1
// ---------------------------------------------------------------------------

/// `1u8 << 8` is `1u8 << (8 & 7) == 1`, not `1u8 << 8 == 0`.
#[test]
fn m60_u8_shl_count_masked_to_width() {
    differential_case(
        "u8_shl8",
        "    let n = core::hint::black_box(8u32);\n\
         \x20   (core::hint::black_box(1u8) << (n as u8)) as i32",
        1,
    );
}

/// `0x80u8 >> 8` is `0x80 >> (8 & 7) == 0x80 == 128`.
#[test]
fn m60_u8_shr_count_masked_to_width() {
    differential_case(
        "u8_shr8",
        "    let n = core::hint::black_box(8u32);\n\
         \x20   (core::hint::black_box(0x80u8) >> (n as u8)) as i32",
        128,
    );
}

/// `1u16 << 16` is `1u16 << (16 & 15) == 1`.
#[test]
fn m60_u16_shl_count_masked_to_width() {
    differential_case(
        "u16_shl16",
        "    let n = core::hint::black_box(16u32);\n\
         \x20   (core::hint::black_box(1u16) << (n as u16)) as i32",
        1,
    );
}

/// Signed narrow arithmetic shift with a masked count: `-1i8 >> 9` is
/// `-1i8 >> (9 & 7 == 1) == -1`; `-1i8 as u8 == 255`.
#[test]
fn m60_i8_sar_count_masked_to_width() {
    differential_case(
        "i8_sar9",
        "    let n = core::hint::black_box(9u32);\n\
         \x20   ((core::hint::black_box(-1i8) >> (n as i8)) as u8) as i32",
        255,
    );
}

// ---------------------------------------------------------------------------
// #61 — wide u64 switch/match case constant (guard, already-correct)
// ---------------------------------------------------------------------------

/// A `u64` match case above 2^31 must compare register-to-register, not via a
/// truncated `imm32`.
#[test]
fn m61_wide_u64_switch_case_matches() {
    differential_case(
        "u64_wide_switch",
        "    match core::hint::black_box(5_000_000_000u64) {\n\
         \x20       5_000_000_000u64 => 42,\n\
         \x20       3_000_000_000u64 => 7,\n\
         \x20       _ => 9,\n\
         \x20   }",
        42,
    );
}

// ---------------------------------------------------------------------------
// #62 — high-bit narrow-unsigned switch/match case constant
// ---------------------------------------------------------------------------

/// A `u8` match case with the high bit set (`0xFF`) selects its arm; the case
/// must be zero-extended (255), not sign-normalized to -1.
#[test]
fn m62_u8_high_bit_switch_case_matches() {
    differential_case(
        "u8_highbit_switch",
        "    match core::hint::black_box(0xFFu8) {\n\
         \x20       0xFF => 42,\n\
         \x20       0x01 => 7,\n\
         \x20       _ => 9,\n\
         \x20   }",
        42,
    );
}

/// `u16` high-bit case (`0x8000`) selects its arm.
#[test]
fn m62_u16_high_bit_switch_case_matches() {
    differential_case(
        "u16_highbit_switch",
        "    match core::hint::black_box(0x8000u16) {\n\
         \x20       0x8000 => 5,\n\
         \x20       0x0001 => 3,\n\
         \x20       _ => 1,\n\
         \x20   }",
        5,
    );
}

// ---------------------------------------------------------------------------
// #63 — O0 array-element loads under pressure (determinism guard)
// ---------------------------------------------------------------------------

/// Four `let`-bound products of array-indexed loads must not read uninitialized
/// spill slots at O0. `(3*13 + 5*17 + 7*19 + 11*23) & 0xFF == 510 & 0xFF == 254`.
#[test]
fn m63_o0_array_element_loads_under_pressure() {
    differential_case(
        "o0_array_pressure",
        "    let a = [3i32, 5, 7, 11, 13, 17, 19, 23];\n\
         \x20   let l0 = a[0] * a[4];\n\
         \x20   let l1 = a[1] * a[5];\n\
         \x20   let l2 = a[2] * a[6];\n\
         \x20   let l3 = a[3] * a[7];\n\
         \x20   ((l0 + l1 + l2 + l3) & 0xFF) as i32",
        254,
    );
}
