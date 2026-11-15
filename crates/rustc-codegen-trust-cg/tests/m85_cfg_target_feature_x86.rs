#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Differential regression test for the target-feature / cfg gap: the bridge's
// `target_config` returned `target_features: vec![]`, so rustc evaluated
// `cfg!(target_feature = "sse2")` (and the rest of the x86_64 hardfloat baseline) to
// FALSE — diverging from the LLVM backend, which reports the baseline as enabled. A
// `#[cfg(target_feature = ...)]`-gated program therefore took the WRONG branch under
// the bridge (a real value divergence, not just a warning).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs `target_config`): declare the
// architecture's baseline ABI features (x86_64: x87/sse/sse2/fxsr/sse3/ssse3/sse4.1/
// cmpxchg16b). These are always present for the default hardfloat ABI, so cfg now
// agrees with LLVM; the bridge still fails closed on any feature-gated MIR it cannot
// lower (never a wrong value).
//
// Gated O0+O3 vs the LLVM oracle.

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

/// `cfg!(target_feature = "sse2")` must be TRUE on x86_64 (matching LLVM), so the
/// program takes the `then` branch (was the `else` branch: trust=2 vs llvm=1).
#[test]
fn m85_cfg_sse2_matches_llvm() {
    differential_program(
        "sse2",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            if cfg!(target_feature = \"sse2\") { bb(11) } else { bb(22) } }",
        11,
    );
}

/// Combine several baseline-feature cfgs; all true on x86_64.
#[test]
fn m85_cfg_baseline_combo_matches_llvm() {
    differential_program(
        "combo",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = 0i32; \
            if cfg!(target_feature = \"sse\") { s += bb(1); } \
            if cfg!(target_feature = \"sse2\") { s += bb(2); } \
            if cfg!(target_feature = \"fxsr\") { s += bb(4); } \
            if cfg!(target_feature = \"x87\") { s += bb(8); } \
            if cfg!(target_feature = \"avx512f\") { s += bb(100); } \
            s }",
        // sse+sse2+fxsr+x87 = 1+2+4+8 = 15; avx512f is NOT baseline (false)
        15,
    );
}
