// Differential test for BY-VALUE FLOAT-AGGREGATE RETURNS at -Copt-level=0.
//
// THE GAP (and fix): a function returning a BARE TUPLE of float scalar leaves by
// value — e.g. `fn mk(x: f64) -> (f64, f64) { (x, x*2.0) }` — failed closed at O0
// with "Ty::(f64, f64)" (the scalarized path cannot represent a whole float-tuple
// value crossing the by-value ABI boundary), while it compiled at O3 (inlined away)
// and a NAMED struct of the same float fields (`struct S { a: f64, b: f64 }`)
// compiled correctly at BOTH levels.
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs `integer_byval_tuple_eligible`): the
// eligibility predicate that admits a bare scalar-leaf tuple onto the verified SysV
// `memory_aggregate_layout` register-pair / sret machinery was extended from
// integer/bool leaves to ALSO accept 32-/64-bit FLOAT leaves. A float tuple is laid
// out by rustc IDENTICALLY to a named struct of the same float fields (same size /
// offsets / SSE eightbyte classification), and the named-struct float-aggregate
// by-value path is already verified-correct (returned in XMM0:XMM1), so the tuple
// reuses the SAME proven construction / load-store + SysV classification — differing
// only in `ty::Tuple`-vs-`ty::Adt`, which the byte-offset addressing is agnostic to.
//
// The hard invariant (shared with m111): for EVERY program, at BOTH O0 and O3,
// trust-cg MUST match LLVM **or fail closed (produce no binary)** — NEVER a
// different exit code.
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
    let dir = std::env::temp_dir().join(format!("rcl2_m117_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile a COMPLETE program `src` (top-level items + `fn main`) at `opt`;
/// returns `Some(bin)` on success, `None` on (trust-cg) compile failure (the
/// fail-closed case).
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

/// For each `(name, full_program_src, expected)` program, at BOTH O0 and O3: LLVM
/// must produce `expected`, and trust-cg must either MATCH LLVM or FAIL CLOSED (no
/// binary). A trust-cg binary whose exit code DIFFERS from LLVM is the silent
/// miscompile we forbid and fails the test.
fn assert_match_or_fail_closed(dir: &Path, shapes: &[(&str, &str, i32)]) {
    let dylib = ensure_dylib_built();
    for (name, src, expected) in shapes {
        for opt in [0u8, 3u8] {
            let llvm_bin = try_compile(dir, &format!("{name}_llvm_{opt}"), src, None, opt)
                .unwrap_or_else(|| panic!("LLVM compile of `{name}` @O{opt} failed"));
            let llvm_exit = run_exit_code(&llvm_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` @O{opt} is {llvm_exit}, expected {expected}"
            );
            match try_compile(dir, &format!("{name}_tcg_{opt}"), src, Some(&dylib), opt) {
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

/// The fixed sub-case (a by-value FLOAT tuple / struct RETURN) plus int-tuple/struct
/// regression controls and a >16-byte MEMORY-class neighbor. Each must match LLVM or
/// fail closed at O0 AND O3.
#[test]
fn byval_float_aggregate_return_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("byval_float_ret");
    let shapes: &[(&str, &str, i32)] = &[
        // --- THE FIXED SUB-CASE: a by-value FLOAT TUPLE return (was O0 fail-closed
        // "Ty::(f64, f64)"). (3.0) + (6.0) = 9.0 -> 9.
        (
            "ret_tuple_f64f64",
            "fn mk(x: f64) -> (f64, f64) { (x, x * 2.0) }\n\
             fn main() { let t = mk(3.0); std::process::exit(((t.0 + t.1) as i32) & 0xff); }",
            9,
        ),
        // {f32,f32} tuple return.
        (
            "ret_tuple_f32f32",
            "fn mk(x: f32) -> (f32, f32) { (x, x * 2.0) }\n\
             fn main() { let t = mk(3.0); std::process::exit(((t.0 + t.1) as i32) & 0xff); }",
            9,
        ),
        // Mixed {i32,f64} tuple return (one INTEGER eightbyte + one SSE eightbyte).
        (
            "ret_tuple_i32f64",
            "fn mk(x: f64) -> (i32, f64) { (x as i32, x * 2.0) }\n\
             fn main() { let t = mk(3.0); std::process::exit(((t.0 as f64 + t.1) as i32) & 0xff); }",
            9,
        ),
        // Mixed {f64,i32} tuple return (the reverse eightbyte order).
        (
            "ret_tuple_f64i32",
            "fn mk(x: f64) -> (f64, i32) { (x * 2.0, x as i32) }\n\
             fn main() { let t = mk(3.0); std::process::exit(((t.0 + t.1 as f64) as i32) & 0xff); }",
            9,
        ),
        // --- FLOAT STRUCT returns (already correct; locked in as controls). ---
        (
            "ret_struct_f64f64",
            "#[derive(Clone, Copy)] struct S { a: f64, b: f64 }\n\
             fn mk(x: f64) -> S { S { a: x, b: x * 2.0 } }\n\
             fn main() { let s = mk(3.0); std::process::exit(((s.a + s.b) as i32) & 0xff); }",
            9,
        ),
        (
            "ret_struct_mix_i32f64",
            "#[derive(Clone, Copy)] struct S { a: i32, b: f64 }\n\
             fn mk(x: f64) -> S { S { a: x as i32, b: x * 2.0 } }\n\
             fn main() { let s = mk(3.0); std::process::exit(((s.a as f64 + s.b) as i32) & 0xff); }",
            9,
        ),
        // --- INTEGER tuple / struct returns (regression: must stay correct). ---
        (
            "ret_tuple_i64i64",
            "fn mk(x: i64) -> (i64, i64) { (x, x * 2) }\n\
             fn main() { let t = mk(3); std::process::exit(((t.0 + t.1) & 0xff) as i32); }",
            9,
        ),
        (
            "ret_tuple_i32i64",
            "fn mk(x: i64) -> (i32, i64) { (x as i32, x * 2) }\n\
             fn main() { let t = mk(3); \
                std::process::exit((((t.0 as i64) + t.1) & 0xff) as i32); }",
            9,
        ),
        // --- >16-byte MEMORY-class (sret) returns: a 4-field float tuple. ---
        (
            "ret_tuple_f64x4_mem",
            "fn mk(x: f64) -> (f64, f64, f64, f64) { (x, x * 2.0, x * 3.0, x * 4.0) }\n\
             fn main() { let t = mk(2.0); \
                std::process::exit(((t.0 + t.1 + t.2 + t.3) as i32) & 0xff); }",
            20,
        ),
        // A 3-field i64 tuple return (24 bytes, MEMORY class / sret).
        (
            "ret_tuple_i64x3_mem",
            "fn mk(x: i64) -> (i64, i64, i64) { (x, x * 2, x * 3) }\n\
             fn main() { let t = mk(3); std::process::exit(((t.0 + t.1 + t.2) & 0xff) as i32); }",
            18,
        ),
        // --- A float tuple THREADED through a second by-value-arg call. ---
        (
            "ret_tuple_f64f64_pipe",
            "fn mk(x: f64) -> (f64, f64) { (x, x * 2.0) }\n\
             fn use_t(t: (f64, f64)) -> f64 { t.0 + t.1 }\n\
             fn main() { let t = mk(3.0); std::process::exit((use_t(t) as i32) & 0xff); }",
            9,
        ),
        // --- A bool+float tuple return. ---
        (
            "ret_tuple_boolf64",
            "fn mk(x: f64) -> (bool, f64) { (x > 0.0, x * 2.0) }\n\
             fn main() { let t = mk(3.0); let v = if t.0 { t.1 } else { 0.0 }; \
                std::process::exit((v as i32) & 0xff); }",
            6,
        ),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}
