#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential regression test for the o0-overflow-tuple completeness gap: a primitive
// `x.overflowing_add/sub/mul(y)` call returns a `(T, bool)` tuple. At -Copt-level 3
// rustc inlines it into a `CheckedBinaryOp` rvalue the bridge already lowers; at
// -Copt-level 0 it emits a real CALL to the core method whose `(T, bool)` return the
// bridge could not type as an ABI value (it failed closed "Ty::(u32, bool)").
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs): intercept the overflowing_add/sub/mul
// method at the Call terminator and lower it to the SAME `Inst::Overflow` the inlined
// rvalue uses (bind tuple field 0 = wrapped, field 1 = overflow bool), so O0 reproduces
// the O3 lowering bit-for-bit with no new tuple ABI. O3 is the correctness oracle: it
// already compiled these correctly, so the O0 fix only has to match O3 (and LLVM).
//
// The differential oracle is the SAME program compiled by rustc's default LLVM backend
// at -Copt-level 0 and 3; `black_box` materializes the operands so the overflow is a
// real runtime event, and each program consumes BOTH the wrapped value and the bool.

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
    assert!(status.success(), "cargo build failed; cannot run m83 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m83_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

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

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(!objs.is_empty(), "{stem} (opt={opt}): no object file produced");

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

fn differential_program(stem: &str, body: &str, expected: i32) {
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
         use core::hint::black_box as bb;\n{body}\n"
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

/// `overflowing_add` on u8 that wraps; consume BOTH the wrapped value and the bool.
#[test]
fn m83_overflowing_add_u8_matches_llvm() {
    differential_program(
        "add_u8",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = bb(250u8).overflowing_add(bb(10u8)); \
            ((r as i32) + if o { 100 } else { 0 }) & 0x7f }",
        // 250+10 = 260 wraps to 4, overflow true: 4 + 100 = 104; 104 & 0x7f = 104
        104,
    );
}

/// `overflowing_sub` on u32 underflow.
#[test]
fn m83_overflowing_sub_u32_matches_llvm() {
    differential_program(
        "sub_u32",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = bb(5u32).overflowing_sub(bb(8u32)); \
            (((r & 0x7) as i32) + if o { 8 } else { 0 }) & 0x7f }",
        // 5-8 wraps to 4294967293; &7 = 5; overflow true: 5 + 8 = 13
        13,
    );
}

/// `overflowing_mul` on u16 — non-overflowing case (bool false).
#[test]
fn m83_overflowing_mul_u16_matches_llvm() {
    differential_program(
        "mul_u16",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = bb(20u16).overflowing_mul(bb(6u16)); \
            (((r % 100) as i32) + if o { 50 } else { 0 }) & 0x7f }",
        // 20*6 = 120, no overflow; 120 % 100 = 20; o false: 20
        20,
    );
}

/// `overflowing_add` in a LOOP, wrapped value carried, bool discarded — exercises the
/// intercept inside a loop (the destination tuple temp rebound each iteration).
#[test]
fn m83_overflowing_add_loop_matches_llvm() {
    differential_program(
        "add_loop",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut x = bb(1u8); let mut i = 0i32; \
            while i < bb(20i32) { let (w, _) = x.overflowing_add(bb(30u8)); x = w; i += 1; } \
            (x % 100) as i32 }",
        // 1 + 20*30 = 601; 601 mod 256 = 89; 89 % 100 = 89
        89,
    );
}

/// Signed `overflowing_mul` at i16::MAX boundary.
#[test]
fn m83_overflowing_mul_i16_overflow_matches_llvm() {
    differential_program(
        "mul_i16",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = bb(20000i16).overflowing_mul(bb(3i16)); \
            ((((r as i32) & 0x7f)) + if o { 1 } else { 0 }) & 0x7f }",
        // 20000*3 = 60000 overflows i16 (wraps to 60000-65536 = -5536); (-5536 as i32)&0x7f
        // = (0x...EA60)&0x7f = 0x60 = 96; overflow true: 96+1 = 97; &0x7f = 97
        97,
    );
}

// ---------------------------------------------------------------------------
// MEMORY-BACKED destination (the `(iN, bool)` tuple RETURNED BY VALUE across a
// `#[inline(never)]` call boundary — the SysV aggregate-return ABI places the
// return local in a memory slot). This is the D-remainder: `overflowing_shl`,
// `overflowing_shr`, `overflowing_div`, and `overflowing_rem` compose their pair
// from proven primitives (masked shift + `Uge` compare; div/rem safe-divisor +
// override selects) then STORE both fields at their layout offsets via
// `store_overflow_pair_into_memory_slot`. Pre-fix these fail-closed
// ("... into a memory-backed destination ... not yet supported"); the bare inline
// destructures above only exercised the scalar-field-binding path.
// ---------------------------------------------------------------------------

/// `overflowing_shl` on u32 with an out-of-range count, tuple returned by value.
#[test]
fn m83_overflowing_shl_u32_byval_matches_llvm() {
    differential_program(
        "shl_u32_byval",
        "#[inline(never)] fn shl(x: u32, n: u32) -> (u32, bool) { x.overflowing_shl(n) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = shl(bb(0xFFu32), bb(40u32)); \
            (((r % 100) as i32) + if o { 5 } else { 0 }) & 0x7f }",
        // 40 & 31 = 8; 255 << 8 = 65280; ov = (40 >= 32) = true; 65280 % 100 = 80; 80+5 = 85
        85,
    );
}

/// `overflowing_shr` on i32 (arithmetic), out-of-range count, tuple returned by value.
#[test]
fn m83_overflowing_shr_i32_byval_matches_llvm() {
    differential_program(
        "shr_i32_byval",
        "#[inline(never)] fn shr(x: i32, n: u32) -> (i32, bool) { x.overflowing_shr(n) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = shr(bb(-256i32), bb(35u32)); \
            ((r & 0x7f) + if o { 1 } else { 0 }) & 0x7f }",
        // 35 & 31 = 3; -256 >> 3 = -32; ov = (35 >= 32) = true; (-32)&0x7f = 96; 96+1 = 97
        97,
    );
}

/// `overflowing_shl` on u64 (16-byte tuple), out-of-range count, returned by value.
#[test]
fn m83_overflowing_shl_u64_byval_matches_llvm() {
    differential_program(
        "shl_u64_byval",
        "#[inline(never)] fn shl(x: u64, n: u32) -> (u64, bool) { x.overflowing_shl(n) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = shl(bb(1u64), bb(70u32)); \
            (((r % 100) as i32) + if o { 3 } else { 0 }) & 0x7f }",
        // 70 & 63 = 6; 1 << 6 = 64; ov = (70 >= 64) = true; 64 % 100 = 64; 64+3 = 67
        67,
    );
}

/// Signed `overflowing_div` at the `iN::MIN / -1` overflow (must return `(MIN, true)`
/// WITHOUT trapping), tuple returned by value.
#[test]
fn m83_overflowing_div_i32_min_byval_matches_llvm() {
    differential_program(
        "div_i32min_byval",
        "#[inline(never)] fn dv(x: i32, y: i32) -> (i32, bool) { x.overflowing_div(y) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = dv(bb(i32::MIN), bb(-1i32)); \
            ((r & 0x7) + if o { 42 } else { 0 }) & 0x7f }",
        // MIN/-1 overflows: value = MIN (0x8000_0000), (MIN & 0x7) = 0; ov = true; 0+42 = 42
        42,
    );
}

/// Signed `overflowing_rem` at the `iN::MIN / -1` overflow (must return `(0, true)`),
/// tuple returned by value.
#[test]
fn m83_overflowing_rem_i32_min_byval_matches_llvm() {
    differential_program(
        "rem_i32min_byval",
        "#[inline(never)] fn rm(x: i32, y: i32) -> (i32, bool) { x.overflowing_rem(y) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = rm(bb(i32::MIN), bb(-1i32)); \
            ((r & 0x7f) + if o { 7 } else { 0 }) & 0x7f }",
        // MIN % -1 overflows: value = 0; ov = true; 0+7 = 7
        7,
    );
}

/// Unsigned `overflowing_div` (never overflows), tuple returned by value — exercises the
/// unsigned no-overflow memory-backed store branch.
#[test]
fn m83_overflowing_udiv_u32_byval_matches_llvm() {
    differential_program(
        "udiv_u32_byval",
        "#[inline(never)] fn dv(x: u32, y: u32) -> (u32, bool) { x.overflowing_div(y) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (r, o) = dv(bb(100u32), bb(7u32)); \
            ((r as i32) + if o { 1 } else { 0 }) & 0x7f }",
        // 100 / 7 = 14; ov = false; 14 + 0 = 14
        14,
    );
}
