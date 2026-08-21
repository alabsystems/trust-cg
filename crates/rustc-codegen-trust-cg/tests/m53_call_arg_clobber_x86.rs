#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential regression test for MISCOMPILE #53 (m53): a multi-argument call
// whose arguments PERMUTE between registers and the stack, where an argument
// register populated by an early setup move was clobbered by a later value
// before the call.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. When lowering a call, the x86-64 ISel emits, for each argument, a
// move into the System V outgoing-argument register (`mov RDI, vN`, `mov RSI,
// vM`, ...) immediately before the `CALL`. The value loaded into e.g. RDI lives
// in RDI from its setup move to the call, but RDI is a physical register, not a
// virtual register, so that lifetime was invisible to the register allocator:
// the arg-setup `mov RDI, vN` looked like a DEAD def (nothing reads RDI before
// the call's caller-saved clobber). The allocator was therefore free to reuse
// RDI for an UNRELATED value (another argument's source) still live across the
// argument-setup span, writing `mov RDI, vK` *after* `mov RDI, vN` and so
// clobbering a populated argument register before the call. The bug surfaces
// when the arguments permute (so a later argument's source is live across an
// earlier argument's register) and there is enough register pressure that the
// later source lands in an already-populated argument register — e.g. a call
// forwarding 8 arguments in a rotated order, the trailing two passed on the
// stack.
//
// THE FIX models a call's argument registers as implicit USES of the call:
//   * `trust-cg-lower/src/x86_64_isel.rs` records, on each `CALL`/`CALLR`, the
//     physical argument registers it consumes (`X86ISelInst::call_arg_regs`).
//   * `trust-cg-codegen/src/x86_64/pipeline.rs` turns those into the call's
//     `implicit_uses` for the register allocator.
//   * `trust-cg-regalloc/src/lib.rs` (`implicit_def_reservations`) reserves each
//     argument register for the WHOLE span from its setup move to the call, not
//     merely at the two endpoints, so no other value can occupy a populated
//     argument register before the call.
// The allocator then keeps each argument register live across its setup span and
// places the conflicting value elsewhere (or spills) — always sound.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend, compiled twice (once with `-Zcodegen-backend=<trust-cg dylib>`, once
// without), linked identically, run, and the process exit codes required to be
// EQUAL (and equal to the documented expected value).
//
// The crate is `#![no_std] #![no_main]` exposing `#[no_mangle] pub extern "C" fn
// main() -> i32`, so the bridge compiles `main` directly and avoids the std
// `std::rt::lang_start` entry path. `#[inline(never)]` keeps the callee distinct
// so the permuting argument-forwarding call is actually emitted.

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
    assert!(status.success(), "cargo build failed; cannot run m53 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m53_{stem}_{}", std::process::id()));
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
/// backend is used; when `None`, rustc's default LLVM backend is used.
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
        // `.o` extension under both backends.
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

/// The canonical m53 repro. `level_b` forwards its eight arguments to `level_d`
/// in a ROTATED order — `level_d(c, d, e, f, g, h, a, b+2)` — so the first six
/// destination argument registers are populated from a permutation of the
/// incoming six argument registers, and the last two arguments (`a`, `b+2`) go
/// on the stack. `level_d` returns its FIRST argument, which is `c == 33`. The
/// rotation makes the source of the sixth argument (`h`) live across the first
/// argument register (RDI); before the fix the allocator reused RDI for `h`,
/// clobbering the first argument (`c`) and returning the wrong value (88).
#[test]
fn m53_permuting_multi_arg_call_does_not_clobber_arg_register() {
    let src = "\
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn level_d(a: u64, _b: u64, _c: u64, _d: u64, _e: u64, _f: u64, _g: u64, _h: u64) -> u64 {
    a
}
#[inline(never)]
fn level_b(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    level_d(c, d, e, f, g, h, a, b.wrapping_add(2))
}
#[no_mangle]
pub extern \"C\" fn main() -> i32 {
    level_b(11, 22, 33, 44, 55, 66, 77, 88) as i32
}
";
    differential_program("permute_rotate", src, 33);
}

/// A companion that returns a SUM mixing several rotated arguments (so the test
/// fails if ANY argument register is clobbered, not only the first). `level_d`
/// returns `a + d + g` where, after the rotation `level_d(c,d,e,f,g,h,a,b+2)`,
/// `a==c==33`, `d==f==66`, `g==a==11`, so the result is `33 + 66 + 11 == 110`.
#[test]
fn m53_permuting_multi_arg_call_sum_matches_llvm() {
    let src = "\
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn level_d(a: u64, _b: u64, _c: u64, d: u64, _e: u64, _f: u64, g: u64, _h: u64) -> u64 {
    a.wrapping_add(d).wrapping_add(g)
}
#[inline(never)]
fn level_b(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    level_d(c, d, e, f, g, h, a, b.wrapping_add(2))
}
#[no_mangle]
pub extern \"C\" fn main() -> i32 {
    level_b(11, 22, 33, 44, 55, 66, 77, 88) as i32
}
";
    differential_program("permute_sum", src, 110);
}

/// A reverse-order forwarding variant: `level_d(h, g, f, e, d, c, b, a)` fully
/// reverses the eight arguments, maximizing the register/stack permutation. The
/// callee returns its first argument (`h == 88`), so any clobber of the first
/// argument register surfaces as a wrong exit code.
#[test]
fn m53_reverse_order_multi_arg_call_matches_llvm() {
    let src = "\
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn callee(a: u64, _b: u64, _c: u64, _d: u64, _e: u64, _f: u64, _g: u64, _h: u64) -> u64 {
    a
}
#[inline(never)]
fn forward(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 {
    callee(h, g, f, e, d, c, b, a)
}
#[no_mangle]
pub extern \"C\" fn main() -> i32 {
    forward(11, 22, 33, 44, 55, 66, 77, 88) as i32
}
";
    differential_program("reverse_order", src, 88);
}
