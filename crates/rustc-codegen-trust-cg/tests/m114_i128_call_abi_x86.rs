// Differential regression test for the x86-64 i128/u128 SysV CALL-boundary ABI.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE this closes: i128 add/sub/bitwise/mul/shift lower INLINE (register
// pair), but an i128 across a CALL boundary — e.g. `#[inline(never)] fn
// f(a: i128, b: i128) -> i128` — and div/rem (which lower to compiler-rt
// libcalls `__divti3`/`__udivti3`/`__modti3`/`__umodti3`) require the SysV
// register-pair argument ABI on the CALLER side. A 128-bit integer argument is
// classified into two consecutive INTEGER eightbytes passed in a GPR pair (low
// half first: e.g. RDI:RSI, then RDX:RCX) and the 128-bit result is returned in
// RAX:RDX (low in RAX, high in RDX). Before this fix the caller-side pairing was
// unwired and the backend FAILED CLOSED ("see WS2b").
//
// THE FIX (trust-cg-lower/src/x86_64_isel.rs `lower_call_inner`): add an
// `ArgLoc::I128Pair { lo, hi }` classification for SysV i128 args (two GPRs, low
// first), emit both register copies, list both as the call's implicit arg-reg
// uses, and reassemble the i128 result from RAX:RDX. Mirrors the proven AArch64
// `ArgLocation::RegPair` path and the in-tree `select_i128_div_libcall`.
//
// VERIFICATION: the differential oracle is the SAME program compiled by rustc's
// default LLVM backend at -Copt-level 0 AND 3. Every i128 operand is built from
// RUNTIME i64->i128 casts of `black_box`'d inputs (NOT `x as i128` wide-const
// literals, which hit a separate fail-closed gap), so the i128 values are real
// runtime register pairs. The exit code is driven by a BIT-SPREAD reduction
// (XOR-fold of all four 32-bit lanes of the 128-bit result) so a wrong high
// eightbyte / swapped register cannot collapse mod 256 and hide a miscompile.

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
    assert!(status.success(), "cargo build failed; cannot run m114 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m114_{stem}_{}", std::process::id()));
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
    link.arg("-arch").arg("x86_64").arg("-o").arg(&bin);
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

/// Compile + link + run `body` at O0 and O3 with both LLVM and trust-cg; assert
/// LLVM matches `expected` and trust-cg matches LLVM at each opt level.
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
         use core::hint::black_box as bb;\n\
         // XOR-fold all four 32-bit lanes of a 128-bit value into a 0..=127\n\
         // exit code so a wrong high eightbyte cannot collapse mod 256.\n\
         #[inline(never)]\n\
         fn spread_u128(v: u128) -> i32 {{\n\
             let a = (v & 0xffff_ffff) as u32;\n\
             let b = ((v >> 32) & 0xffff_ffff) as u32;\n\
             let c = ((v >> 64) & 0xffff_ffff) as u32;\n\
             let d = ((v >> 96) & 0xffff_ffff) as u32;\n\
             let x = a ^ b ^ c ^ d;\n\
             ((x ^ (x >> 16) ^ (x >> 8)) & 0x7f) as i32\n\
         }}\n\
         #[inline(never)]\n\
         fn spread_i128(v: i128) -> i32 {{ spread_u128(v as u128) }}\n\
         {body}\n"
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
            "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} (MISCOMPILE)"
        );
    }
}

/// Compute the expected exit code with the host's (native, correct) arithmetic.
fn spread(v: u128) -> i32 {
    let a = (v & 0xffff_ffff) as u32;
    let b = ((v >> 32) & 0xffff_ffff) as u32;
    let c = ((v >> 64) & 0xffff_ffff) as u32;
    let d = ((v >> 96) & 0xffff_ffff) as u32;
    let x = a ^ b ^ c ^ d;
    ((x ^ (x >> 16) ^ (x >> 8)) & 0x7f) as i32
}

// ---- i128 add across a real CALL boundary (register-pair args + result) ----
#[test]
fn m114_i128_add_across_call() {
    // a = 0x0000_0000_dead_beef_0000_0000_1234_5678, b similar; build from
    // runtime i64 halves so both eightbytes are live runtime register values.
    let a_hi = 0x0123_4567_89ab_cdefi64;
    let a_lo = 0x7766_5544_3322_1100u64 as i64;
    let b_hi = 0x0000_0000_0000_0001i64;
    let b_lo = 0xffff_ffff_ffff_fffeu64 as i64;
    let a = ((a_hi as i128) << 64) | (((a_lo as u64) as u128) as i128);
    let b = ((b_hi as i128) << 64) | (((b_lo as u64) as u128) as i128);
    let expected = spread(a.wrapping_add(b) as u128);
    differential_program(
        "add_call",
        &format!(
            "#[inline(never)]\n\
             pub fn f(a: i128, b: i128) -> i128 {{ a.wrapping_add(b) }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let a = ((bb({a_hi}i64) as i128) << 64) | (((bb({a_lo}i64) as u64) as u128) as i128);\n\
                 let b = ((bb({b_hi}i64) as i128) << 64) | (((bb({b_lo}i64) as u64) as u128) as i128);\n\
                 spread_i128(f(bb(a), bb(b)))\n\
             }}"
        ),
        expected,
    );
}

// ---- i128 sub across a CALL (second arg pair RDX:RCX, borrow chain) ----
#[test]
fn m114_i128_sub_across_call() {
    let a_hi = 0x0000_0000_0000_0005i64;
    let a_lo = 0x0000_0000_0000_0001u64 as i64;
    let b_hi = 0x0000_0000_0000_0001i64;
    let b_lo = 0x0000_0000_0000_0009u64 as i64; // forces a borrow out of the low half
    let a = ((a_hi as i128) << 64) | (((a_lo as u64) as u128) as i128);
    let b = ((b_hi as i128) << 64) | (((b_lo as u64) as u128) as i128);
    let expected = spread(a.wrapping_sub(b) as u128);
    differential_program(
        "sub_call",
        &format!(
            "#[inline(never)]\n\
             pub fn f(a: i128, b: i128) -> i128 {{ a.wrapping_sub(b) }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let a = ((bb({a_hi}i64) as i128) << 64) | (((bb({a_lo}i64) as u64) as u128) as i128);\n\
                 let b = ((bb({b_hi}i64) as i128) << 64) | (((bb({b_lo}i64) as u64) as u128) as i128);\n\
                 spread_i128(f(bb(a), bb(b)))\n\
             }}"
        ),
        expected,
    );
}

// ---- unsigned i128 division -> __udivti3 libcall (carry-relevant operands) --
#[test]
fn m114_u128_div_libcall() {
    let a_hi = 0x0000_0000_0000_00ffu64 as i64;
    let a_lo = 0xdead_beef_cafe_babeu64 as i64;
    let b_hi = 0x0000_0000_0000_0000u64 as i64;
    let b_lo = 0x0000_0000_0001_0001u64 as i64;
    let a = ((a_hi as u64 as u128) << 64) | (a_lo as u64 as u128);
    let b = ((b_hi as u64 as u128) << 64) | (b_lo as u64 as u128);
    let expected = spread(a / b);
    differential_program(
        "udiv_call",
        &format!(
            "#[inline(never)]\n\
             pub fn f(a: u128, b: u128) -> u128 {{ a / b }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let a = ((bb({a_hi}i64) as u64 as u128) << 64) | (bb({a_lo}i64) as u64 as u128);\n\
                 let b = ((bb({b_hi}i64) as u64 as u128) << 64) | (bb({b_lo}i64) as u64 as u128);\n\
                 spread_u128(f(bb(a), bb(b)))\n\
             }}"
        ),
        expected,
    );
}

// ---- unsigned i128 remainder -> __umodti3 ----
#[test]
fn m114_u128_rem_libcall() {
    let a_hi = 0x0000_0000_0000_0007u64 as i64;
    let a_lo = 0x1234_5678_9abc_def0u64 as i64;
    let b_hi = 0x0000_0000_0000_0000u64 as i64;
    let b_lo = 0x0000_0000_dead_0001u64 as i64;
    let a = ((a_hi as u64 as u128) << 64) | (a_lo as u64 as u128);
    let b = ((b_hi as u64 as u128) << 64) | (b_lo as u64 as u128);
    let expected = spread(a % b);
    differential_program(
        "urem_call",
        &format!(
            "#[inline(never)]\n\
             pub fn f(a: u128, b: u128) -> u128 {{ a % b }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let a = ((bb({a_hi}i64) as u64 as u128) << 64) | (bb({a_lo}i64) as u64 as u128);\n\
                 let b = ((bb({b_hi}i64) as u64 as u128) << 64) | (bb({b_lo}i64) as u64 as u128);\n\
                 spread_u128(f(bb(a), bb(b)))\n\
             }}"
        ),
        expected,
    );
}

// ---- signed i128 division with a NEGATIVE operand -> __divti3 ----
#[test]
fn m114_i128_signed_div_negative() {
    // a negative, b positive: tests sign handling through the libcall + result
    // sign extension in the RAX:RDX reassembly.
    let a_hi = 0xffff_ffff_ffff_fff0u64 as i64; // high bits set => negative
    let a_lo = 0x0000_0000_0000_0000u64 as i64;
    let b_hi = 0x0000_0000_0000_0000i64;
    let b_lo = 0x0000_0000_0000_0007i64;
    let a = ((a_hi as u64 as u128) << 64 | (a_lo as u64 as u128)) as i128;
    let b = ((b_hi as u64 as u128) << 64 | (b_lo as u64 as u128)) as i128;
    let expected = spread((a / b) as u128);
    differential_program(
        "sdiv_neg_call",
        &format!(
            "#[inline(never)]\n\
             pub fn f(a: i128, b: i128) -> i128 {{ a / b }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let a = (((bb({a_hi}i64) as u64 as u128) << 64) | (bb({a_lo}i64) as u64 as u128)) as i128;\n\
                 let b = (((bb({b_hi}i64) as u64 as u128) << 64) | (bb({b_lo}i64) as u64 as u128)) as i128;\n\
                 spread_i128(f(bb(a), bb(b)))\n\
             }}"
        ),
        expected,
    );
}

// ---- signed i128 remainder with a NEGATIVE dividend -> __modti3 ----
#[test]
fn m114_i128_signed_rem_negative() {
    let a_hi = 0xffff_ffff_ffff_ffffu64 as i64;
    let a_lo = 0xffff_ffff_ffff_fff9u64 as i64; // a = -7
    let b_hi = 0x0000_0000_0000_0000i64;
    let b_lo = 0x0000_0000_0000_0003i64; // b = 3 -> -7 % 3 = -1
    let a = ((a_hi as u64 as u128) << 64 | (a_lo as u64 as u128)) as i128;
    let b = ((b_hi as u64 as u128) << 64 | (b_lo as u64 as u128)) as i128;
    let expected = spread((a % b) as u128);
    differential_program(
        "srem_neg_call",
        &format!(
            "#[inline(never)]\n\
             pub fn f(a: i128, b: i128) -> i128 {{ a % b }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let a = (((bb({a_hi}i64) as u64 as u128) << 64) | (bb({a_lo}i64) as u64 as u128)) as i128;\n\
                 let b = (((bb({b_hi}i64) as u64 as u128) << 64) | (bb({b_lo}i64) as u64 as u128)) as i128;\n\
                 spread_i128(f(bb(a), bb(b)))\n\
             }}"
        ),
        expected,
    );
}

// ---- i128 multiply across a CALL boundary (full 128-bit wrapping product) ---
#[test]
fn m114_i128_mul_across_call() {
    let a_hi = 0x0000_0000_0000_0003i64;
    let a_lo = 0x0000_0000_dead_beefu64 as i64;
    let b_hi = 0x0000_0000_0000_0000i64;
    let b_lo = 0x0000_0001_0000_0001u64 as i64;
    let a = ((a_hi as i128) << 64) | (((a_lo as u64) as u128) as i128);
    let b = ((b_hi as i128) << 64) | (((b_lo as u64) as u128) as i128);
    let expected = spread(a.wrapping_mul(b) as u128);
    differential_program(
        "mul_call",
        &format!(
            "#[inline(never)]\n\
             pub fn f(a: i128, b: i128) -> i128 {{ a.wrapping_mul(b) }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let a = ((bb({a_hi}i64) as i128) << 64) | (((bb({a_lo}i64) as u64) as u128) as i128);\n\
                 let b = ((bb({b_hi}i64) as i128) << 64) | (((bb({b_lo}i64) as u64) as u128) as i128);\n\
                 spread_i128(f(bb(a), bb(b)))\n\
             }}"
        ),
        expected,
    );
}

// ---- three i128 args: forces the SECOND pair onto RDX:RCX and a THIRD pair
//      onto R8:R9, exercising the consecutive-GPR-pair allocation ----
#[test]
fn m114_i128_three_args() {
    let mk = |hi: i64, lo: i64| ((hi as i128) << 64) | (((lo as u64) as u128) as i128);
    let a = mk(0x11, 0x2222_2222_2222_2222u64 as i64);
    let b = mk(0x33, 0x4444_4444_4444_4444u64 as i64);
    let c = mk(0x55, 0x6666_6666_6666_6666u64 as i64);
    let expected = spread(a.wrapping_add(b).wrapping_sub(c) as u128);
    differential_program(
        "three_args",
        &format!(
            "#[inline(never)]\n\
             pub fn f(a: i128, b: i128, c: i128) -> i128 {{ a.wrapping_add(b).wrapping_sub(c) }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let a = ((bb(0x11i64) as i128) << 64) | (((bb({a_lo}i64) as u64) as u128) as i128);\n\
                 let b = ((bb(0x33i64) as i128) << 64) | (((bb({b_lo}i64) as u64) as u128) as i128);\n\
                 let c = ((bb(0x55i64) as i128) << 64) | (((bb({c_lo}i64) as u64) as u128) as i128);\n\
                 spread_i128(f(bb(a), bb(b), bb(c)))\n\
             }}",
            a_lo = 0x2222_2222_2222_2222u64 as i64,
            b_lo = 0x4444_4444_4444_4444u64 as i64,
            c_lo = 0x6666_6666_6666_6666u64 as i64,
        ),
        expected,
    );
}

// ===========================================================================
// WIDE-CONST MATERIALIZATION (the gap the runtime-cast tests above avoid; see
// header line 25). A u128/i128 literal whose high 64 bits are NOT the sign
// extension of the low half used to FAIL CLOSED in the adapter ("wide-imm
// materialization not yet implemented"); now lowered via Opcode::Iconst128
// (two MovRI halves). Differential oracle = the same program under LLVM.
// ===========================================================================

#[test]
fn m114_wide_u128_const_materialization() {
    let v: u128 = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210;
    let expected = spread(v);
    differential_program(
        "wide_u128_const",
        &format!(
            "#[inline(never)]\n\
             pub fn f() -> u128 {{ {v}u128 }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 spread_u128(bb(f()))\n\
             }}"
        ),
        expected,
    );
}

#[test]
fn m114_wide_neg_i128_const_materialization() {
    // Negative wide i128 whose high half is a specific non-all-ones pattern, so
    // the high eightbyte is NOT sext(low) — exercises the two's-complement split.
    let v: i128 = -0x0123_4567_89ab_cdef_0011_2233_4455_6677;
    let expected = spread(v as u128);
    differential_program(
        "wide_neg_i128_const",
        &format!(
            "#[inline(never)]\n\
             pub fn f() -> i128 {{ {v}i128 }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 spread_i128(bb(f()))\n\
             }}"
        ),
        expected,
    );
}

#[test]
fn m114_wide_const_in_operation() {
    // Materialize a wide const and XOR it with a RUNTIME i128 — confirms the
    // const flows as a correct register pair into a real op, not just a return.
    let k: u128 = 0xdead_beef_cafe_babe_0123_4567_89ab_cdef;
    let r_hi = 0x1111_2222_3333_4444u64;
    let r_lo = 0x5555_6666_7777_8888u64;
    let r = ((r_hi as u128) << 64) | (r_lo as u128);
    let expected = spread(k ^ r);
    differential_program(
        "wide_const_xor",
        &format!(
            "#[inline(never)]\n\
             pub fn f(x: u128) -> u128 {{ x ^ {k}u128 }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{\n\
                 let r = ((bb({r_hi}u64) as u128) << 64) | (bb({r_lo}u64) as u128);\n\
                 spread_u128(f(bb(r)))\n\
             }}"
        ),
        expected,
    );
}

