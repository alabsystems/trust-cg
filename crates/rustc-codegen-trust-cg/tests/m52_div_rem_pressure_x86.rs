#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Differential regression test for MISCOMPILE #52 (m52): unsigned division/
// remainder under register pressure, where the live-range splitter's join /
// edge split-copy placement does not model the fixed-physical-register
// constraints of x86-64 `DIV`/`IDIV`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. x86-64 integer division pins the dividend in RAX (and the high
// half in RDX) and clobbers RDX with the remainder; the same fixed-register
// constraints apply to `MUL`, `CDQ`/`CQO`, `CMPXCHG`, and the atomic CAS loops.
// In the trust-cg regalloc these constraints are carried as IMPLICIT def/use
// edges (`add_x86_fixed_implicit_operands` adds RAX/RDX as implicit defs/uses),
// NOT as explicit instruction operands. The greedy live-range splitter does not
// model those implicit fixed-register edges when it places its split copies:
// under register pressure a value whose live range crosses the `DIV` can have
// its split copy spilled to / reloaded from a slot that the `DIV` corrupted (it
// clobbered RAX/RDX) or that was never written on the chosen edge, so a later
// use reads a stale slot and the function returns the wrong value. The symptom
// is opt-level dependent: it only manifests once the optimizer has produced
// enough simultaneously-live values to force splitting across the divide.
//
// THE FIX (in `trust-cg-codegen/src/x86_64/pipeline.rs`) admits live-range
// splitting only for CFG shapes whose split-copy replay is sound. It now also
// fails the splitting admission CLOSED whenever the function contains a
// fixed-physical-register-clobbering instruction (`DIV`/`IDIV`/`MUL`,
// `CDQ`/`CQO`, `CMPXCHG`, atomic CAS): `x86_regalloc_func_first_fixed_reg_clobber`
// reports the clobber, `x86_regalloc_splitting_cfg_diagnostic` returns
// `FixedRegClobber`, and the allocator falls back to the plain greedy spill
// path (which spills instead of splits — always sound). Splitting is a pure
// code-quality optimization, so disabling it for these shapes never changes
// observable behavior, only register-allocation quality.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend. The program is compiled twice — once with `-Zcodegen-backend=<trust-cg
// dylib>` and once without — linked the same way, run, and the process exit
// codes are required to be EQUAL (and equal to the documented expected value).
//
// The crate is `#![no_std] #![no_main]` exposing `#[no_mangle] pub extern "C" fn
// main() -> i32`, so the bridge compiles `main` directly and we avoid the std
// `std::rt::lang_start` entry path. Abort stubs are supplied for any referenced
// `panic*` symbols (the overflow / div-by-zero checks never fire at the chosen
// inputs — every divisor is OR'd with 1, so it is always non-zero), so the LLVM
// object links standalone exactly like the trust-cg object.

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
    let dir = std::env::temp_dir().join(format!("rcl2_m52_{stem}_{}", std::process::id()));
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
        if toolchain_support::is_abort_stub_symbol(sym) {
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
/// differential oracle). All emitted `.o` codegen units are linked together.
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> i32 {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = toolchain_support::rustc_command();
    cmd.arg("--crate-type").arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        // `--out-dir` (not `-o`) so EVERY codegen unit object is written with a
        // `.o` extension under both backends.
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn trustc");
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

/// Compile a FULL `#![no_std] #![no_main]` program `src` with BOTH backends at
/// -Copt-level 0 and 3 and require the trust-cg exit code to equal the LLVM exit
/// code AND the documented `expected`.
fn differential_program(stem: &str, src: &str, expected: i32) {
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
        let llvm = compile_link_run(stem, src, opt, None);
        let trust = compile_link_run(stem, src, opt, Some(&dylib));
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

/// The canonical m52 repro. `work` builds a long chain of `wrapping_*` mixes and
/// then TWO unsigned divisions (`v0 / (v1|1)` and `v2 / (v3|1)`), keeping many
/// intermediate values simultaneously live across each `DIV`. `fold` xors the
/// eight bytes of the result down to a single `u8`. At -Copt-level 3 the
/// optimizer produces enough live values to force the live-range splitter to
/// split a value across the `DIV` fixed-register clobber; before the fix that
/// split copy was misplaced / read from a `DIV`-corrupted slot and the program
/// returned the wrong byte (101 instead of 187). The `|1` keeps every divisor
/// non-zero, so the div-by-zero check never fires.
#[test]
fn m52_div_rem_under_register_pressure_matches_llvm() {
    let src = "\
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn work(s: u64) -> u64 {
    let v0 = s.wrapping_mul(0x9E3779B97F4A7C15);
    let v1 = v0.wrapping_add(0x1234567);
    let v2 = v1 ^ (v0 >> 7);
    let v3 = v2.wrapping_mul(3);
    let v4 = v3.wrapping_sub(v0);
    let v5 = v4.wrapping_add(v1);
    let v6 = v5 ^ (v2 << 5);
    let v7 = v6.wrapping_mul(5);
    let d1 = v0 / (v1 | 1);
    let d2 = v2 / (v3 | 1);
    v0 ^ v1 ^ v2 ^ v3 ^ v4 ^ v5 ^ v6 ^ v7 ^ d1 ^ d2
}
#[inline(never)]
fn fold(r: u64) -> u8 {
    (r as u8)
        ^ ((r >> 8) as u8)
        ^ ((r >> 16) as u8)
        ^ ((r >> 24) as u8)
        ^ ((r >> 32) as u8)
        ^ ((r >> 40) as u8)
        ^ ((r >> 48) as u8)
        ^ ((r >> 56) as u8)
}
#[no_mangle]
pub extern \"C\" fn main() -> i32 {
    fold(work(0xCAFEBABEDEADBEEF)) as i32
}
";
    differential_program("div_rem_pressure", src, 187);
}

/// A signed companion: `IDIV` (and the `CQO` sign-extension) carry the same
/// fixed RAX/RDX register constraints as unsigned `DIV`, so signed division
/// under the same pressure must also match the LLVM oracle. Uses i64 mixing and
/// two signed divisions whose divisors are kept non-zero (`| 1`, which sets the
/// low bit and so is never 0). Exercises the `IDIV`/`CQO` arm of the clobber set.
#[test]
fn m52_signed_div_under_register_pressure_matches_llvm() {
    let src = "\
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn work(s: i64) -> i64 {
    let v0 = s.wrapping_mul(-0x61C8864680B583EB);
    let v1 = v0.wrapping_add(0x1234567);
    let v2 = v1 ^ (v0 >> 7);
    let v3 = v2.wrapping_mul(3);
    let v4 = v3.wrapping_sub(v0);
    let v5 = v4.wrapping_add(v1);
    let v6 = v5 ^ (v2 << 5);
    let v7 = v6.wrapping_mul(5);
    let d1 = v0 / (v1 | 1);
    let d2 = v2 / (v3 | 1);
    v0 ^ v1 ^ v2 ^ v3 ^ v4 ^ v5 ^ v6 ^ v7 ^ d1 ^ d2
}
#[inline(never)]
fn fold(r: i64) -> u8 {
    let r = r as u64;
    (r as u8)
        ^ ((r >> 8) as u8)
        ^ ((r >> 16) as u8)
        ^ ((r >> 24) as u8)
        ^ ((r >> 32) as u8)
        ^ ((r >> 40) as u8)
        ^ ((r >> 48) as u8)
        ^ ((r >> 56) as u8)
}
#[no_mangle]
pub extern \"C\" fn main() -> i32 {
    fold(work(0xCAFEBABEDEADBEEFu64 as i64)) as i32
}
";
    differential_program("signed_div_pressure", src, 187);
}
