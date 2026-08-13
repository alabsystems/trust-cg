// Differential regression test for the o0-byval-array completeness gap: a by-value
// array `[T; N]` crossing a CALL boundary (a by-value array parameter / return /
// call destination) failed closed "Ty::[T; N]" — the scalarized path represents array
// LOCALS as per-element values but has no whole-array ABI value.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs `memory_aggregate_layout`): admit
// `ty::Array(elem, N)` whose element bottoms out at a memory scalar leaf — an array is
// a single-variant aggregate whose `Variants::Single` "fields" are its N elements, so
// the existing field-leaf validation + slot layout (N*size_of::<T>(), no tag) handle it.
// Only call-crossing arrays (params/returns/destinations) become memory-backed; plain
// array LOCALS are not params/returns/dests so they stay on the scalarized path.
//
// Gated O0+O3 vs the LLVM oracle: array param, array return, array-of-struct param, a
// larger array, and a plain local array control (must stay correct).

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
    assert!(status.success(), "cargo build failed; cannot run m84 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m84_{stem}_{}", std::process::id()));
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

/// A by-value `[i64; 3]` PARAMETER read across a call (was fail-closed "Ty::[i64; 3]").
#[test]
fn m84_array_param_matches_llvm() {
    differential_program(
        "param",
        "#[inline(never)] fn sum3(a: [i64; 3]) -> i64 { a[0] + a[1]*2 + a[2]*3 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = [bb(1i64), bb(2), bb(3)]; (sum3(a) & 0x7f) as i32 }",
        // 1 + 4 + 9 = 14
        14,
    );
}

/// A by-value `[i64; 4]` RETURN.
#[test]
fn m84_array_return_matches_llvm() {
    differential_program(
        "ret",
        "#[inline(never)] fn make(x: i64) -> [i64; 4] { [x, x*2, x*3, x*4] }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = make(bb(2)); ((a[0]+a[1]+a[2]+a[3]) & 0x7f) as i32 }",
        // [2,4,6,8] -> 20
        20,
    );
}

/// An array OF STRUCTS by value — the element leaf validation descends into the struct.
#[test]
fn m84_array_of_struct_param_matches_llvm() {
    differential_program(
        "structs",
        "#[derive(Clone,Copy)] struct P { a: i32, b: i32 }\n\
         #[inline(never)] fn red(a: [P; 3]) -> i32 { a[0].a + a[1].b + a[2].a*2 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = [P{a:bb(1),b:bb(2)}, P{a:bb(3),b:bb(4)}, P{a:bb(5),b:bb(6)}]; \
            (red(a) & 0x7f) as i32 }",
        // 1 + 4 + 10 = 15
        15,
    );
}

/// A larger `[u8; 8]` by-value param with an asymmetric reduction.
#[test]
fn m84_array_u8_param_matches_llvm() {
    differential_program(
        "u8x8",
        "#[inline(never)] fn dot(a: [u8; 8]) -> i32 { \
            let mut s = 0i32; let mut i = 0; \
            while i < 8 { s = s.wrapping_add(a[i] as i32 * (i as i32 + 1)); i += 1; } s }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = [bb(1u8),bb(2),bb(3),bb(4),bb(5),bb(6),bb(7),bb(8)]; (dot(a) & 0x7f) as i32 }",
        // sum a[i]*(i+1) = 1+4+9+16+25+36+49+64 = 204; 204 & 0x7f = 76
        76,
    );
}

/// Control: a plain local array (no call boundary) must STILL work via scalarization.
#[test]
fn m84_plain_local_array_control_matches_llvm() {
    differential_program(
        "plain",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = [bb(1i64), bb(2), bb(3)]; ((a[0] + a[1]*2 + a[2]*3) & 0x7f) as i32 }",
        14,
    );
}
