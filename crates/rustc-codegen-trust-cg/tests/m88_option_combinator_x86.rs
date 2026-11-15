#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Differential regression test for option-map sub-gap (b): `Option::unwrap_or` on a
// runtime-branch Option failed closed at -O0 ("ADT Use source discriminant before
// aggregate binding") — the scalarized-enum model cannot pack a RUNTIME-VARIANT enum
// into the by-value aggregate ABI from per-field values (the variant is not statically
// known at the Use site).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE FIX (lib.rs `compute_memory_backed_locals`): memory-back a by-value MULTI-VARIANT
// ENUM local passed as a CALL argument, so each constructed variant (with its tag) is
// stored into a slot and the slot is passed — variant-agnostic. Structs / arrays keep
// the scalarized-packing path (their fields ARE statically known). Regression-clean
// across the enum-heavy corpus (reference_union 35/35, try_operator, memory_model, heap).
//
// Gated O0+O3 vs LLVM. (Combinators whose body pulls an out-of-line closure / std helper
// can hit a macOS-version linker-version artifact at -O0 in the differential harness;
// those are covered at -O3 by the gate, not asserted here.)

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

/// `Option::unwrap_or` on a runtime Some (was -O0 fail-closed).
#[test]
fn m88_option_unwrap_or_some_matches_llvm() {
    differential_program(
        "uor_some",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let o: Option<i32> = if bb(true) { Some(bb(7)) } else { None }; \
            (o.unwrap_or(0) * 3) & 0x7f }",
        21,
    );
}

/// `Option::unwrap_or` selecting the default (None branch).
#[test]
fn m88_option_unwrap_or_none_matches_llvm() {
    differential_program(
        "uor_none",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let o: Option<i32> = if bb(false) { Some(bb(7)) } else { None }; \
            o.unwrap_or(bb(42)) & 0x7f }",
        42,
    );
}

/// Two `unwrap_or`s combined.
#[test]
fn m88_option_unwrap_or_combined_matches_llvm() {
    differential_program(
        "uor_combo",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a: Option<i32> = if bb(true) { Some(bb(10)) } else { None }; \
            let b: Option<i32> = if bb(false) { Some(bb(20)) } else { None }; \
            (a.unwrap_or(0) + b.unwrap_or(5)) & 0x7f }",
        // 10 + 5 = 15
        15,
    );
}
