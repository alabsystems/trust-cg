#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: a REACHABLE-but-not-taken diverging std `#[track_caller]`
// panic edge (`Option::unwrap` / `Result::expect` / slice index) under
// `-Cpanic=abort` at -O0/-O2/-O3, compiled for x86_64 via the
// rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, exit codes checked
// against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE GAP (PERF-L3, lever-map lane 3). At -O3, rustc inlines `Vec`/iterator
// machinery down to a bare `.unwrap()` / `.expect()` whose FAILURE arm is a
// DIVERGING call to a precompiled std `#[track_caller]` panic helper
// (`core::option::unwrap_failed`, `core::result::unwrap_failed`, …). Under
// `-Cpanic=abort` — THE BENCH CONFIG — rustc's `AbortUnwindingCalls` pass marks
// that diverging call `UnwindAction::Unreachable` (nothing unwinds under
// abort). The bridge's diverging-track_caller arm previously handled only
// `Continue`/`Cleanup` unwind actions and FAILED CLOSED on any other action
// with
//
//     "diverging #[track_caller] std call with a nounwind unwind action"
//
// — rejecting the WHOLE enclosing function. So EVERY -O3 function containing a
// reachable-but-never-taken `.unwrap()`/`.expect()` edge (e.g.
// `*v.iter().max().unwrap()`) failed closed under `panic=abort`, even though the
// unwrap SUCCEEDS at runtime and the non-panic path returns a correct value.
//
// THE FIX reuses the SAME trap-for-abort lowering the assert / intercepted
// bounds-check fail targets already use for a nounwind unwind action: a
// `nounwind` (`Unreachable`/`Terminate`) diverging panic cannot unwind — the
// process dies on the spot either way — so the panic edge is trapped
// (`Inst::Unreachable` -> ud2). Only the panic MESSAGE differs (the long-
// established accepted cosmetic class); a wrong VALUE is never produced. The
// NON-panic path (the whole point) now lowers and returns the value.
//
// This test pins BOTH halves:
//   * `unwrap_succeeds`: the unwrap/expect/index SUCCEEDS — trust-cg must
//     COMPILE at O0/O2/O3 and return the SAME value as LLVM (the completeness
//     gain; a fail-closed here is the regression this test guards).
//   * `panic_taken`: the unwrap/index FAILS — both backends must ABORT (die via
//     a signal, no clean exit). trust-cg traps (SIGILL) where LLVM aborts
//     (SIGABRT); the exact signal differs (accepted cosmetic class), but
//     NEITHER produces a clean exit code, and neither returns a wrong value.

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
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run track_caller test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m94tc_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
) -> (std::process::Output, PathBuf) {
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
    (output, bin)
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
    let (output, bin) = try_compile(dir, name, src, backend, opt);
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend, -Copt-level={opt}). stderr: <<<{}>>>",
        if backend.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

/// Run and demand a REAL (clean) exit code — a signal death fails loudly. Used
/// for the `unwrap_succeeds` shapes, where the panic edge is never taken.
fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// Whether a run terminated ABNORMALLY (via a signal, no clean exit code) — an
/// abort (`SIGABRT`, LLVM) or a trap (`SIGILL`, trust-cg's nounwind trap). Used
/// for the `panic_taken` shapes: the exact signal differs (accepted cosmetic
/// class) but NEITHER backend may exit cleanly, and neither may return a value.
fn died_via_signal(bin: &Path) -> bool {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .is_none()
}

/// The completeness gain: a reachable-but-SUCCEEDING diverging std
/// `#[track_caller]` panic edge (`unwrap`/`expect`/index) must COMPILE at
/// O0/O2/O3 under `panic=abort` and return the SAME value as LLVM. Before the
/// PERF-L3 fix these fail-closed WHOLE at -O3 ("diverging #[track_caller] std
/// call with a nounwind unwind action").
#[test]
fn track_caller_unwrap_succeeds_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("ok");

    // (name, source, expected exit code). Each has a reachable `.unwrap()` /
    // `.expect()` / index panic edge that is NOT taken (the value is present).
    let shapes: &[(&str, &str, i32)] = &[
        // `iter().max().unwrap()` — the canonical -O3 shape: max = 3, 3 % 250.
        (
            "iter_max_unwrap",
            "fn main() { let v = vec![1i64, 2, 3]; \
             let x = *v.iter().max().unwrap(); \
             std::process::exit((x % 250) as i32); }",
            3,
        ),
        // `iter().min().expect(..)` — the `Result`/`Option` `expect` helper.
        (
            "iter_min_expect",
            "fn main() { let v = vec![9i64, 4, 7, 2, 8]; \
             let x = *v.iter().min().expect(\"nonempty\"); \
             std::process::exit((x + 40) as i32); }",
            42,
        ),
        // `Vec::get(i).unwrap()` — the inlined slice-index `get` path.
        (
            "get_unwrap",
            "fn main() { let mut v: Vec<i64> = Vec::new(); let mut i = 1i64; \
             while i <= 10 { v.push(i); i += 1; } \
             let x = *v.get(3).unwrap(); std::process::exit(x as i32); }",
            4,
        ),
        // A reachable unwrap INSIDE a loop body (the panic edge is emitted once
        // per iteration, never taken): running max of a growing accumulator.
        (
            "loop_unwrap",
            "fn main() { let data = [3i64, 1, 4, 1, 5, 9, 2, 6]; \
             let mut best = 0i64; let mut k = 0usize; \
             while k < data.len() { \
             let cur = [best, data[k]]; \
             best = *cur.iter().max().unwrap(); k += 1; } \
             std::process::exit((best % 250) as i32); }",
            9,
        ),
    ];

    for (name, src, expected) in shapes {
        for opt in ["0", "2", "3"] {
            let suffix = format!("o{opt}");
            let llvm_bin = compile(&dir, &format!("{name}_{suffix}_llvm"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_{suffix}_tcg"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit code for `{name}` (-Copt-level={opt}) is {llvm_exit}, \
                 expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{name}` (-Copt-level={opt}) is {tcg_exit}, \
                 LLVM is {llvm_exit} (must match — a fail-closed or wrong value is the \
                 PERF-L3 regression)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// The panic-TAKEN half: when the diverging `#[track_caller]` panic edge IS
/// taken (unwrap on `None` / OOB index), BOTH backends must terminate the
/// process ABNORMALLY under `panic=abort` — no clean exit, no wrong value. LLVM
/// aborts (SIGABRT); trust-cg traps the nounwind panic edge (SIGILL). The exact
/// signal differs (accepted cosmetic class), but the die-on-the-spot semantics
/// match: this test pins that the panic edge never falls through to a clean
/// exit / a returned value.
#[test]
fn track_caller_panic_taken_aborts_like_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("panic");

    // Both shapes derive the OOB index from a RUNTIME value (`v.len()` + k) so
    // rustc cannot const-fold the panic away (a compile-time `None` lowers to a
    // `ConstValue::Indirect` the bridge fails closed on for its OWN reason —
    // that would not exercise this arm). The panic edge is thus a genuine
    // runtime `Option::unwrap` on `None`.
    let shapes: &[(&str, &str)] = &[
        // `Vec::get(runtime-OOB).unwrap()` -> `None.unwrap()` panics.
        (
            "get_rt_oob_unwrap",
            "fn main() { let mut v: Vec<i64> = Vec::new(); \
             let mut i = 1i64; while i <= 3 { v.push(i * 10); i += 1; } \
             let bad = (v.len() + 6) as usize; \
             let x = *v.get(bad).unwrap(); std::process::exit(x as i32); }",
        ),
        // A different runtime-OOB derivation (index scaled by len).
        (
            "get_rt_oob_scaled",
            "fn main() { let mut v: Vec<i64> = Vec::new(); \
             let mut i = 0i64; while i < 4 { v.push(i + 1); i += 1; } \
             let bad = v.len() * 3 + 1; \
             let x = *v.get(bad).unwrap(); std::process::exit(x as i32); }",
        ),
    ];

    for (name, src) in shapes {
        for opt in ["0", "3"] {
            let suffix = format!("o{opt}");
            // LLVM aborts (no clean exit).
            let llvm_bin = compile(&dir, &format!("{name}_{suffix}_llvm"), src, None, opt);
            assert!(
                died_via_signal(&llvm_bin),
                "LLVM `{name}` (-Copt-level={opt}) exited cleanly; a taken panic under \
                 panic=abort must terminate abnormally"
            );
            // trust-cg must ALSO terminate abnormally — never a clean exit / wrong value.
            let tcg_bin = compile(&dir, &format!("{name}_{suffix}_tcg"), src, Some(&dylib), opt);
            assert!(
                died_via_signal(&tcg_bin),
                "trust-cg `{name}` (-Copt-level={opt}) exited cleanly; the taken panic \
                 edge must trap/abort, never fall through to a value"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
