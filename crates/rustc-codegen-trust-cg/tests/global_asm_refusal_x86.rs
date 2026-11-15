#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: `global_asm!` FAILS CLOSED through the bridge.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// HAZARD PINNED: `MonoItem::GlobalAsm` used to fall through the mono-item
// driver's Fn/Static chain SILENTLY — raw module-level assembly was dropped
// with zero diagnostic (side-effect-only asm simply vanished; symbol-defining
// asm surfaced later as a confusing undefined-symbol link error). The driver
// now refuses it with a tagged `[TCG-GLOBAL-ASM]` failed root: the backend
// cannot parse, model, or verify raw asm bytes, so the only sound outcome is
// a refusal. This test pins BOTH directions:
//   * a crate containing `global_asm!` must FAIL to compile with the tag in
//     stderr (never compile-and-drop);
//   * an asm-free control program must still compile and run (the arm does
//     not over-fire).

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
    let dir = std::env::temp_dir().join(format!("rcl2_gasm_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` via the bridge at `opt_level`; return (success, stderr).
fn compile_bridge(dir: &Path, dylib: &Path, src: &str, opt_level: &str) -> (bool, String, PathBuf) {
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("bridge_out_{opt_level}"));
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "bin"])
        .arg(backend_arg(dylib))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt_level}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc (bridge)");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        bin,
    )
}

/// A crate containing `global_asm!` must be REFUSED with the [TCG-GLOBAL-ASM]
/// tag at every opt level — never compiled with the asm silently dropped. The
/// asm block here is side-effect-shaped (defines a symbol `main` never
/// references), which is exactly the shape that previously vanished without
/// even a link error.
#[test]
fn global_asm_is_refused_with_tag_never_silently_dropped() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("refusal");

    let src = "core::arch::global_asm!(\".globl _tcg_ga_probe\\n_tcg_ga_probe:\\n ret\");\n\
               fn main(){ std::process::exit(7); }";
    for opt in ["0", "2", "3"] {
        let (ok, stderr, _) = compile_bridge(&dir, &dylib, src, opt);
        assert!(
            !ok,
            "global_asm! crate COMPILED at -O{opt} — the asm was silently dropped \
             (the exact hazard this refusal closes)"
        );
        assert!(
            stderr.contains("[TCG-GLOBAL-ASM]"),
            "global_asm! refusal at -O{opt} must carry the [TCG-GLOBAL-ASM] tag; stderr: <<<{stderr}>>>"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Control: the refusal arm must not over-fire — an asm-free program still
/// compiles through the bridge and runs with the expected exit code.
#[test]
fn asm_free_control_still_compiles_and_runs() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("control");

    let src = "fn main(){ let x = std::hint::black_box(30i32); std::process::exit(x + 12); }";
    let (ok, stderr, bin) = compile_bridge(&dir, &dylib, src, "0");
    assert!(ok, "asm-free control failed to compile: <<<{stderr}>>>");
    assert!(
        !stderr.contains("[TCG-GLOBAL-ASM]"),
        "control program tripped the GlobalAsm refusal: <<<{stderr}>>>"
    );
    let code = Command::new(&bin)
        .status()
        .expect("run control binary")
        .code()
        .expect("control binary exit code");
    assert_eq!(code, 42, "control program exit code");
    let _ = std::fs::remove_dir_all(&dir);
}
