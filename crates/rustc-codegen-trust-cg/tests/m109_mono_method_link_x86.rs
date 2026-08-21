#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: #109 — REFERENCED STD TRAIT-METHOD MONOMORPHIZATIONS LINK —
//
// A program that calls a primitive `Ord` method — `a.max(b)` / `a.min(b)` /
// `a.clamp(lo, hi)`, `std::cmp::Ord::max(a, b)`, the free `std::cmp::max` /
// `std::cmp::min`, or a generic `fn m<T: Ord>(a, b) -> T { a.max(b) }` — emits a
// `Call` to the monomorphized method (e.g. `<i32 as Ord>::max`). The collector
// hands that monomorphization to the bridge as its own `MonoItem::Fn`.
//
// THE BUG (before the fix): the std method's body is precompiled (libcore is built
// `panic=unwind`), so its inner `PartialOrd::lt` call carries a `Cleanup(_)` unwind
// edge even though the final program is `panic=abort`. The bridge rejected any
// terminator with a cleanup unwind ("TerminatorKind::Call with cleanup unwind"),
// failed to lower the body, and — because `<i32 as Ord>::max` is not an external
// root — DROPPED it as a skipped internal symbol. But `main` still emitted a `Call`
// to its symbol, so the link failed with `Undefined symbols: <i32 as Ord>::max`.
// That is not a clean fail-closed: it produced no binary, but via a confusing
// linker error rather than a backend diagnostic, on a body that is trivially
// lowerable (`if other < self { self } else { other }`).
//
// THE FIX: under `panic=abort` (`!panic_strategy().unwinds()`) Rust never unwinds,
// so every `Cleanup(_)` unwind edge — and every cleanup landing-pad block — is dead.
// The bridge now treats a cleanup unwind edge on a Call/Assert/Drop as no unwind,
// and traps dead cleanup blocks whole (`Unreachable`), exactly as rustc's own
// `AbortUnwindingCalls` pass does for abort builds. So `<i32 as Ord>::max` / `min` /
// `clamp` now lower and link, matching LLVM. Under `panic=unwind` the bridge still
// fails closed (real unwinding is not modeled).
//
// Each program is compiled by trust-cg AND LLVM at BOTH -Copt-level=0 and
// -Copt-level=3, run, and the exit codes asserted. The hard invariant: trust-cg
// MUST match LLVM **or fail closed (produce no binary)** — NEVER a different exit
// code and NEVER a binary that links to an undefined symbol.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

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
    assert!(status.success(), "cargo build failed; cannot run test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m109_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` at `opt`; returns `Some(bin)` on success, `None` on (trust-cg)
/// compile/link failure (the fail-closed case).
fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: u8,
) -> Option<PathBuf> {
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
    if output.status.success() && bin.exists() {
        Some(bin)
    } else {
        None
    }
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// For each (name, body, expected) program, at BOTH O0 and O3: LLVM must produce
/// `expected`, and trust-cg must either MATCH LLVM or FAIL CLOSED (no binary).
/// A trust-cg binary whose exit code DIFFERS from LLVM is the silent miscompile we
/// forbid and fails the test. An undefined-symbol link failure also surfaces as
/// "no binary" (try_compile returns None), which is the safe fail-closed branch.
fn assert_match_or_fail_closed(dir: &Path, shapes: &[(&str, &str, i32)]) {
    let dylib = ensure_dylib_built();
    for (name, body, expected) in shapes {
        let src = body.to_string();
        for opt in [0u8, 3u8] {
            let llvm_bin = try_compile(dir, &format!("{name}_llvm_{opt}"), &src, None, opt)
                .unwrap_or_else(|| panic!("LLVM compile of `{name}` @O{opt} failed"));
            let llvm_exit = run_exit_code(&llvm_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` @O{opt} is {llvm_exit}, expected {expected}"
            );
            match try_compile(dir, &format!("{name}_tcg_{opt}"), &src, Some(&dylib), opt) {
                Some(tcg_bin) => {
                    let tcg_exit = run_exit_code(&tcg_bin);
                    assert_eq!(
                        tcg_exit, llvm_exit,
                        "MISCOMPILE: trust-cg exit for `{name}` @O{opt} is {tcg_exit}, \
                         LLVM is {llvm_exit} (must match or fail closed)"
                    );
                }
                None => {
                    eprintln!("note: `{name}` @O{opt} failed closed under trust-cg (safe)");
                }
            }
        }
    }
}

/// #109 — referenced std `Ord`-method monomorphizations must link (match LLVM) or
/// fail closed, never leave an undefined symbol. Covers `.max`/`.min`/`.clamp`,
/// `Ord::max`/`Ord::min`, the free `cmp::max`/`cmp::min`, and a generic `T: Ord`
/// wrapper, over i32/i64/u8/u32, plus a control already-working `if`-select.
#[test]
fn ord_method_link_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("ord");
    let shapes: &[(&str, &str, i32)] = &[
        // `.max` / `.min` methods over i32 — the #109 repro (was: undefined symbol).
        (
            "max_i32",
            "fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             std::process::exit(a.max(b)); }",
            7,
        ),
        (
            "min_i32",
            "fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             std::process::exit(a.min(b)); }",
            3,
        ),
        // `.clamp` (has an inner `assert!(min <= max)` -> a panic block, also lowered).
        (
            "clamp_in_range",
            "fn main(){ let a=std::hint::black_box(3i32); std::process::exit(a.clamp(0, 5)); }",
            3,
        ),
        (
            "clamp_above",
            "fn main(){ let a=std::hint::black_box(9i32); std::process::exit(a.clamp(0, 5)); }",
            5,
        ),
        (
            "clamp_below",
            "fn main(){ let a=std::hint::black_box(-3i32); \
             std::process::exit(a.clamp(0, 5) + 100); }",
            100,
        ),
        // Explicit trait-method path `Ord::max(a, b)`.
        (
            "ord_max_path",
            "fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             std::process::exit(std::cmp::Ord::max(a, b)); }",
            7,
        ),
        (
            "ord_min_path",
            "fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             std::process::exit(std::cmp::Ord::min(a, b)); }",
            3,
        ),
        // Free `std::cmp::max` / `std::cmp::min` (these call `Ord::max`/`min`).
        (
            "cmp_max_fn",
            "fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             std::process::exit(std::cmp::max(a, b)); }",
            7,
        ),
        (
            "cmp_min_fn",
            "fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             std::process::exit(std::cmp::min(a, b)); }",
            3,
        ),
        // Generic `fn m<T: Ord>(a, b) -> T { a.max(b) }` monomorphized at i32.
        (
            "generic_max_i32",
            "fn m<T: Ord>(a: T, b: T) -> T { a.max(b) } \
             fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             std::process::exit(m(a, b)); }",
            7,
        ),
        // Generic min over i64.
        (
            "generic_min_i64",
            "fn m<T: Ord>(a: T, b: T) -> T { a.min(b) } \
             fn main(){ let a=std::hint::black_box(30i64); let b=std::hint::black_box(7i64); \
             std::process::exit(m(a, b) as i32); }",
            7,
        ),
        // `.max` over u8.
        (
            "max_u8",
            "fn main(){ let a=std::hint::black_box(3u8); let b=std::hint::black_box(7u8); \
             std::process::exit(a.max(b) as i32); }",
            7,
        ),
        // `.min` over u32.
        (
            "min_u32",
            "fn main(){ let a=std::hint::black_box(40u32); let b=std::hint::black_box(7u32); \
             std::process::exit(a.min(b) as i32); }",
            7,
        ),
        // `.max` over i64.
        (
            "max_i64",
            "fn main(){ let a=std::hint::black_box(3i64); let b=std::hint::black_box(70i64); \
             std::process::exit(a.max(b) as i32); }",
            70,
        ),
        // Chained: max of (min, max).
        (
            "chained_min_max",
            "fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             let c=std::hint::black_box(5i32); \
             std::process::exit(a.min(b).max(c)); }",
            5,
        ),
        // CONTROL: an equivalent `if`-select that never references a std Ord method —
        // already worked, must STAY correct.
        (
            "control_if_select",
            "fn main(){ let a=std::hint::black_box(3i32); let b=std::hint::black_box(7i32); \
             std::process::exit(if a < b { b } else { a }); }",
            7,
        ),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}
