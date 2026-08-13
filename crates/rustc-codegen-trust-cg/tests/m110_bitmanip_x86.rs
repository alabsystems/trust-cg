// Integration test: #110 — INTEGER BIT-MANIPULATION METHODS / INTRINSICS —
//
// `count_ones`/`count_zeros`/`leading_zeros`/`trailing_zeros`/`leading_ones`/
// `trailing_ones`/`rotate_left`/`rotate_right`/`swap_bytes`/`reverse_bits`/
// `is_power_of_two` all USED to fail closed: at -O0 each is a CALL to
// `core::num::<impl T>::method` whose body uses the `ctpop`/`ctlz`/`cttz`/`bswap`/
// `bitreverse`/`rotate_*` intrinsics this backend does not lower (so the symbol
// fell off and the link failed), and at -O3 each inlines to that bare intrinsic
// the backend rejected as "unsupported intrinsic". The bridge now intercepts BOTH
// forms and synthesizes the result from the one PROVEN bit primitive it carries —
// `UnOp::CtPop` (POPCNT, verified for I8/I16/I32/I64, masking narrow operands) —
// composed with shifts/masks/selects, all proven lowerings.
//
// CARRIER-HYGIENE FOCUS: on x86 a u8/u16/i8/i16 value lives in a wider register
// whose high bits are DIRTY; these ops are width-sensitive, so a dirty carrier is
// the silent-miscompile trap. The bridge lifts the operand into a clean masked
// I64 first. This test hammers EXACTLY that: narrow widths, all-ones, alternating
// bits, MIN/MAX, and rotate amounts of 0/1/width-1/width/width+1 (mod-width).
//
// Each program is compiled by trust-cg AND LLVM at BOTH -Copt-level=0 and =3, run,
// and the exit codes asserted equal. The hard invariant: trust-cg MUST match LLVM
// or fail closed (produce no binary) — NEVER a different exit code. A wrong
// popcount / lzcnt / rotate would be the exact silent miscompile this forbids.
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
    let dir = std::env::temp_dir().join(format!("rcl2_m110_{stem}_{}", std::process::id()));
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

/// Helper to wrap a body that computes a `u32` exit code via `std::process::exit`.
/// We funnel each result through `black_box` to keep the operand runtime (so the
/// op is not const-folded away at O3) and keep the exit value in `[0, 255]`.
#[test]
fn bitmanip_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("bm");
    // Each program black_box-es its inputs (runtime values), computes the op, and
    // exits with the low byte of the result (so the exit code is the observable).
    let shapes: &[(&str, &str, i32)] = &[
        // ---- count_ones ----
        ("co_u8_alt",
         "fn main(){ let x=std::hint::black_box(0b1010_1010u8); std::process::exit(x.count_ones() as i32); }",
         4),
        ("co_u8_max",
         "fn main(){ let x=std::hint::black_box(0xffu8); std::process::exit(x.count_ones() as i32); }",
         8),
        ("co_u16",
         "fn main(){ let x=std::hint::black_box(0xF0F0u16); std::process::exit(x.count_ones() as i32); }",
         8),
        ("co_u32",
         "fn main(){ let x=std::hint::black_box(0xFFFF_0001u32); std::process::exit(x.count_ones() as i32); }",
         17),
        ("co_u64",
         "fn main(){ let x=std::hint::black_box(0xFFFF_FFFF_FFFF_FFFFu64); std::process::exit(x.count_ones() as i32); }",
         64),
        ("co_i32_neg",
         "fn main(){ let x=std::hint::black_box(-1i32); std::process::exit(x.count_ones() as i32); }",
         32),
        ("co_zero",
         "fn main(){ let x=std::hint::black_box(0u32); std::process::exit(x.count_ones() as i32); }",
         0),
        // ---- count_zeros ----
        ("cz_u8",
         "fn main(){ let x=std::hint::black_box(0b1010_1010u8); std::process::exit(x.count_zeros() as i32); }",
         4),
        ("cz_u32_zero",
         "fn main(){ let x=std::hint::black_box(0u32); std::process::exit(x.count_zeros() as i32); }",
         32),
        ("cz_u64",
         "fn main(){ let x=std::hint::black_box(1u64); std::process::exit(x.count_zeros() as i32); }",
         63),
        ("cz_i16_neg",
         "fn main(){ let x=std::hint::black_box(-1i16); std::process::exit(x.count_zeros() as i32); }",
         0),
        // ---- leading_zeros ----
        ("lz_u8_one",
         "fn main(){ let x=std::hint::black_box(1u8); std::process::exit(x.leading_zeros() as i32); }",
         7),
        ("lz_u8_zero",
         "fn main(){ let x=std::hint::black_box(0u8); std::process::exit(x.leading_zeros() as i32); }",
         8),
        ("lz_u8_max",
         "fn main(){ let x=std::hint::black_box(0xffu8); std::process::exit(x.leading_zeros() as i32); }",
         0),
        ("lz_u16",
         "fn main(){ let x=std::hint::black_box(0x00FFu16); std::process::exit(x.leading_zeros() as i32); }",
         8),
        ("lz_u32",
         "fn main(){ let x=std::hint::black_box(0x0000_1000u32); std::process::exit(x.leading_zeros() as i32); }",
         19),
        ("lz_u64",
         "fn main(){ let x=std::hint::black_box(0x0000_0000_0000_00FFu64); std::process::exit(x.leading_zeros() as i32); }",
         56),
        ("lz_i32_neg",
         "fn main(){ let x=std::hint::black_box(-1i32); std::process::exit(x.leading_zeros() as i32); }",
         0),
        ("lz_u64_zero",
         "fn main(){ let x=std::hint::black_box(0u64); std::process::exit(x.leading_zeros() as i32); }",
         64),
        // ---- trailing_zeros ----
        ("tz_u8",
         "fn main(){ let x=std::hint::black_box(0b1000_0000u8); std::process::exit(x.trailing_zeros() as i32); }",
         7),
        ("tz_u8_zero",
         "fn main(){ let x=std::hint::black_box(0u8); std::process::exit(x.trailing_zeros() as i32); }",
         8),
        ("tz_u32",
         "fn main(){ let x=std::hint::black_box(0x0001_0000u32); std::process::exit(x.trailing_zeros() as i32); }",
         16),
        ("tz_u64_zero",
         "fn main(){ let x=std::hint::black_box(0u64); std::process::exit(x.trailing_zeros() as i32); }",
         64),
        ("tz_u16_one",
         "fn main(){ let x=std::hint::black_box(1u16); std::process::exit(x.trailing_zeros() as i32); }",
         0),
        ("tz_i64_neg",
         "fn main(){ let x=std::hint::black_box(-2i64); std::process::exit(x.trailing_zeros() as i32); }",
         1),
        // ---- leading_ones ----
        ("lo_u8",
         "fn main(){ let x=std::hint::black_box(0b1110_0000u8); std::process::exit(x.leading_ones() as i32); }",
         3),
        ("lo_u32_max",
         "fn main(){ let x=std::hint::black_box(0xFFFF_FFFFu32); std::process::exit(x.leading_ones() as i32); }",
         32),
        ("lo_u16_zero",
         "fn main(){ let x=std::hint::black_box(0u16); std::process::exit(x.leading_ones() as i32); }",
         0),
        // ---- trailing_ones ----
        ("to_u8",
         "fn main(){ let x=std::hint::black_box(0b0000_0111u8); std::process::exit(x.trailing_ones() as i32); }",
         3),
        ("to_u64_max",
         "fn main(){ let x=std::hint::black_box(0xFFFF_FFFF_FFFF_FFFFu64); std::process::exit((x.trailing_ones() & 0xff) as i32); }",
         64),
        // ---- rotate_left ----
        ("rl_u8_1",
         "fn main(){ let x=std::hint::black_box(0b1000_0001u8); let k=std::hint::black_box(1u32); std::process::exit(x.rotate_left(k) as i32); }",
         0b0000_0011),
        ("rl_u8_0",
         "fn main(){ let x=std::hint::black_box(0xABu8); let k=std::hint::black_box(0u32); std::process::exit(x.rotate_left(k) as i32); }",
         0xAB),
        ("rl_u8_w",
         "fn main(){ let x=std::hint::black_box(0xABu8); let k=std::hint::black_box(8u32); std::process::exit(x.rotate_left(k) as i32); }",
         0xAB),
        ("rl_u8_wp1",
         "fn main(){ let x=std::hint::black_box(0b1000_0001u8); let k=std::hint::black_box(9u32); std::process::exit(x.rotate_left(k) as i32); }",
         0b0000_0011),
        ("rl_u16_15",
         "fn main(){ let x=std::hint::black_box(0x0001u16); let k=std::hint::black_box(15u32); std::process::exit((x.rotate_left(k) >> 8) as i32); }",
         0x80),
        ("rl_u32",
         "fn main(){ let x=std::hint::black_box(0x8000_0001u32); let k=std::hint::black_box(1u32); std::process::exit((x.rotate_left(k) & 0xff) as i32); }",
         0x03),
        ("rl_u64",
         "fn main(){ let x=std::hint::black_box(0x8000_0000_0000_0001u64); let k=std::hint::black_box(1u32); std::process::exit((x.rotate_left(k) & 0xff) as i32); }",
         0x03),
        ("rl_i32_neg",
         "fn main(){ let x=std::hint::black_box(-1i32); let k=std::hint::black_box(5u32); std::process::exit((x.rotate_left(k) & 0xff) as i32); }",
         0xff),
        // ---- rotate_right ----
        ("rr_u8_1",
         "fn main(){ let x=std::hint::black_box(0b0000_0011u8); let k=std::hint::black_box(1u32); std::process::exit(x.rotate_right(k) as i32); }",
         0b1000_0001),
        ("rr_u8_wp1",
         "fn main(){ let x=std::hint::black_box(0b0000_0011u8); let k=std::hint::black_box(9u32); std::process::exit(x.rotate_right(k) as i32); }",
         0b1000_0001),
        ("rr_u32",
         "fn main(){ let x=std::hint::black_box(0x0000_0003u32); let k=std::hint::black_box(1u32); std::process::exit((x.rotate_right(k) >> 24) as i32); }",
         0x80),
        ("rr_u64_0",
         "fn main(){ let x=std::hint::black_box(0xABu64); let k=std::hint::black_box(0u32); std::process::exit((x.rotate_right(k) & 0xff) as i32); }",
         0xAB),
        // ---- swap_bytes ----
        ("sb_u8",
         "fn main(){ let x=std::hint::black_box(0xABu8); std::process::exit(x.swap_bytes() as i32); }",
         0xAB),
        ("sb_u16",
         "fn main(){ let x=std::hint::black_box(0x1234u16); std::process::exit((x.swap_bytes() & 0xff) as i32); }",
         0x12),
        ("sb_u16_hi",
         "fn main(){ let x=std::hint::black_box(0x1234u16); std::process::exit((x.swap_bytes() >> 8) as i32); }",
         0x34),
        ("sb_u32",
         "fn main(){ let x=std::hint::black_box(0x1122_3344u32); std::process::exit((x.swap_bytes() & 0xff) as i32); }",
         0x11),
        ("sb_u64",
         "fn main(){ let x=std::hint::black_box(0x1122_3344_5566_7788u64); std::process::exit((x.swap_bytes() & 0xff) as i32); }",
         0x11),
        ("sb_i16_neg",
         "fn main(){ let x=std::hint::black_box(0x00FFu16 as i16); std::process::exit(((x.swap_bytes() as u16) >> 8) as i32); }",
         0xFF),
        // ---- reverse_bits ----
        ("rb_u8",
         "fn main(){ let x=std::hint::black_box(0b0000_0001u8); std::process::exit(x.reverse_bits() as i32); }",
         0b1000_0000),
        ("rb_u8_alt",
         "fn main(){ let x=std::hint::black_box(0b1010_1010u8); std::process::exit(x.reverse_bits() as i32); }",
         0b0101_0101),
        ("rb_u16",
         "fn main(){ let x=std::hint::black_box(0x0001u16); std::process::exit((x.reverse_bits() >> 8) as i32); }",
         0x80),
        ("rb_u32",
         "fn main(){ let x=std::hint::black_box(0x0000_0001u32); std::process::exit((x.reverse_bits() >> 24) as i32); }",
         0x80),
        ("rb_u64",
         "fn main(){ let x=std::hint::black_box(0x0000_0000_0000_0001u64); std::process::exit((x.reverse_bits() >> 56) as i32); }",
         0x80),
        // ---- is_power_of_two ----
        ("ipot_yes",
         "fn main(){ let x=std::hint::black_box(64u32); std::process::exit(if x.is_power_of_two() {1} else {0}); }",
         1),
        ("ipot_no",
         "fn main(){ let x=std::hint::black_box(63u32); std::process::exit(if x.is_power_of_two() {1} else {0}); }",
         0),
        ("ipot_zero",
         "fn main(){ let x=std::hint::black_box(0u32); std::process::exit(if x.is_power_of_two() {1} else {0}); }",
         0),
        ("ipot_u8_max",
         "fn main(){ let x=std::hint::black_box(128u8); std::process::exit(if x.is_power_of_two() {1} else {0}); }",
         1),
        ("ipot_u64",
         "fn main(){ let x=std::hint::black_box(0x8000_0000_0000_0000u64); std::process::exit(if x.is_power_of_two() {1} else {0}); }",
         1),
        // ---- CONTROL: a plain arithmetic exit that never touches a bitmanip op
        // (already worked; must STAY correct).
        ("control_add",
         "fn main(){ let a=std::hint::black_box(40u32); let b=std::hint::black_box(2u32); std::process::exit((a+b) as i32); }",
         42),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}
