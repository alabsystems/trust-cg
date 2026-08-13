// Differential regression test for MISCOMPILE #93: `i32::MIN / -1` (and `% -1`)
// SILENTLY WRAPPED under `-Coverflow-checks=off` instead of panicking.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. The #75 fix in `lower_assert_terminator` removed ALL
// `AssertKind::Overflow(..)` asserts when `-Coverflow-checks=off` — but rustc
// only removes the OPTIONAL overflow checks (`BinOp::is_checkable`:
// Add/Sub/Mul/Shl/Shr, plus OverflowNeg). `Overflow(Div)` / `Overflow(Rem)` —
// the `INT_MIN / -1` guards — are NOT governed by `-Coverflow-checks`:
// `i32::MIN / -1` panics in release rustc (LLVM `sdiv` would be UB there).
// With the guard dropped, the bridge's raw trust-ir `SDiv` reached the x86
// division-free lowering, which WRAPS: the program SILENTLY CONTINUED with
// `i32::MIN` where rustc panics — a silent wrong-value execution (empirically:
// exit 42 from the wrap-signature program below; rustc/LLVM exits via panic).
//
// THE FIX narrows the removal to exactly rustc's checkable set, so the Div/Rem
// overflow guard is always lowered (conditional trap), matching rustc's
// always-panic semantics. This test locks that in: the guard programs must
// TERMINATE ABNORMALLY (the bridge traps; LLVM's panic aborts via the stub) and
// must never exit normally with the wrap-signature codes. A control case proves
// normal signed division still computes real values (the test is not passing
// because everything aborts).

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
    assert!(status.success(), "cargo build failed; cannot run m93 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m93_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Stub every unresolved panic symbol with `abort()` so a panic path terminates
/// the process with SIGABRT instead of hanging or failing to link (same trick as
/// the m75 harness).
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

/// Compile `src` (a `#![no_std]` `#[no_mangle] main` program) with the given
/// backend at `-Coverflow-checks=off`, link, run; return `Some(code)` for a
/// normal exit or `None` if the process was killed by a signal (trap / abort).
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> Option<i32> {
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
    run.status.code()
}

const PRELUDE: &str = "#![no_std]\n#![no_main]\n\
    #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {\n\
        extern \"C\" { fn abort() -> !; }\n        unsafe { abort() }\n    }\n";

/// The wrap-signature program: exits 42 IFF the division silently wrapped.
fn guard_program(op: &str, wrap_value: &str) -> String {
    format!(
        "{PRELUDE}\
         #[no_mangle]\npub extern \"C\" fn main() -> i32 {{\n\
             let a = core::hint::black_box(i32::MIN);\n\
             let b = core::hint::black_box(-1i32);\n\
             let c = a {op} b;\n\
             if c == {wrap_value} {{ 42 }} else {{ 43 }}\n\
         }}\n"
    )
}

fn assert_guard_aborts(stem: &str, op: &str, wrap_value: &str) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = guard_program(op, wrap_value);
    for opt in ["0", "3"] {
        // Oracle: rustc/LLVM panics (the stub aborts) — never a normal exit.
        let llvm = compile_link_run(&format!("{stem}_llvm"), &src, opt, None);
        assert!(
            llvm.is_none() || !matches!(llvm, Some(42) | Some(43)),
            "{stem} (opt={opt}): LLVM oracle unexpectedly continued past \
             INT_MIN {op} -1 with exit {llvm:?}"
        );
        // Bridge: the kept Overflow(Div|Rem) guard must trap. A NORMAL exit —
        // above all the wrap-signature 42 — is the #93 silent miscompile.
        let bridge = compile_link_run(&format!("{stem}_trust"), &src, opt, Some(&dylib));
        assert!(
            bridge.is_none(),
            "{stem} (opt={opt}): bridge continued past INT_MIN {op} -1 with \
             exit {bridge:?} (42 = the silent-wrap #93 signature; the \
             Overflow(Div|Rem) assert was dropped)"
        );
    }
}

/// #93 div leg: `i32::MIN / -1` must abort (wrapped value would be `i32::MIN`).
#[test]
fn m93_int_min_div_neg1_guard_kept() {
    assert_guard_aborts("div_guard", "/", "i32::MIN");
}

/// #93 rem leg: `i32::MIN % -1` must abort (wrapped value would be `0`).
#[test]
fn m93_int_min_rem_neg1_guard_kept() {
    assert_guard_aborts("rem_guard", "%", "0");
}

/// CONTROL: ordinary signed division still computes real values and exits
/// normally with the same result as LLVM — the guard tests above are not passing
/// merely because every division aborts.
#[test]
fn m93_normal_signed_division_still_works() {
    if !x86_64_std_available() || !cfg!(target_arch = "x86_64") {
        eprintln!("skipping control: toolchain/host unavailable");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = format!(
        "{PRELUDE}\
         #[no_mangle]\npub extern \"C\" fn main() -> i32 {{\n\
             let a = core::hint::black_box(-91i32);\n\
             let b = core::hint::black_box(7i32);\n\
             // -91 / 7 = -13, -91 % 7 = 0 -> exit 13.\n\
             let q = a / b;\n\
             let r = a % b;\n\
             (-q) + r\n\
         }}\n"
    );
    for opt in ["0", "3"] {
        let llvm = compile_link_run("div_control_llvm", &src, opt, None);
        let bridge = compile_link_run("div_control_trust", &src, opt, Some(&dylib));
        assert_eq!(llvm, Some(13), "LLVM control wrong (opt={opt})");
        assert_eq!(bridge, llvm, "bridge control diverges from LLVM (opt={opt})");
    }
}
