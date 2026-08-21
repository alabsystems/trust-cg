#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential test for by-value aggregate ABI (gap #48), focused on the bounded
// sub-case hardened this round: a CONST TUPLE / CONST SCALAR-FIELD STRUCT used BY
// VALUE as a scalarized operand (`let t = SOME_CONST_TUPLE; ... t.0 ...`).
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs `lower_const_scalarized_struct_or_tuple_use`).
// At O0 a by-value const tuple / struct can arrive as a bare const `Use` into a
// scalarized aggregate local; the prior path failed closed with "tuple Use from
// non-place operand". The new handler reads each INTEGER field's scalar out of the
// const allocation AT ITS RUSTC LAYOUT OFFSET (`layout.fields.offset(i)`) — never
// declaration order, so a layout-reordered struct (`{i8,i64}` -> `i64@0, i8@8`) is
// read correctly — and binds `dst`'s projected per-field values, mirroring how an
// inline `(a, b)` / `S { a, b }` aggregate binds them. It is deliberately narrow:
//   * tuple / scalar-field struct / single-variant enum, every field a single
//     INTEGER scalar leaf (flattened-leaf count == MIR field count);
//   * a nested-aggregate field, a float / bool / pointer field, a pointer-bearing
//     const allocation, or a multi-variant enum all FALL THROUGH to fail closed.
//
// The hard invariant (shared with m108): for EVERY program, at BOTH O0 and O3,
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
    let dir = std::env::temp_dir().join(format!("rcl2_m111_{stem}_{}", std::process::id()));
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

/// The fixed sub-case (const tuple / scalar-field struct by value) PLUS its
/// fail-closed neighbors (nested / float / pointer fields) and inline-literal
/// controls. Each is asserted to match LLVM or fail closed at O0 AND O3.
#[test]
fn const_byval_aggregate_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("const_byval");
    let shapes: &[(&str, &str, i32)] = &[
        // --- THE FIXED SUB-CASE: const tuple by value, scalarized field reads. ---
        // {i32,i32} const tuple: 7*3 + 11*5 = 76. (was O0 fail-closed: "tuple Use
        // from non-place operand".)
        (
            "const_tuple_i32i32",
            "const C: (i32, i32) = (7, 11);\n\
             fn main() { let t = C; std::process::exit(((t.0 * 3 + t.1 * 5) & 0xff) as i32); }",
            76,
        ),
        // {i32,i64} const tuple (mixed width): (7 as i64)*3 + 11*5 = 76.
        (
            "const_tuple_i32i64",
            "const C: (i32, i64) = (7, 11);\n\
             fn main() { let t = C; \
                std::process::exit((((t.0 as i64) * 3 + t.1 * 5) & 0xff) as i32); }",
            76,
        ),
        // Mixed-width const tuple that rustc REORDERS: (u8,u32,u16) -> u32@0,u16@4,u8@6.
        // (3) + (70000 & 0xff trunc via i64)*3 + 500*5; assert via & 0xff.
        // 3 + 70000*3 + 500*5 = 212503; & 0xff = 23.
        (
            "const_tuple_reorder",
            "const C: (u8, u32, u16) = (3, 70000, 500);\n\
             fn main() { let t = C; \
                std::process::exit((((t.0 as i64) + (t.1 as i64) * 3 + (t.2 as i64) * 5) & 0xff) as i32); }",
            (3i64 + 70000 * 3 + 500 * 5) as i32 & 0xff,
        ),
        // --- THE FIXED SUB-CASE: const scalar-field struct by value. ---
        // {i32,i32} const struct: 76.
        (
            "const_struct_i32i32",
            "#[derive(Clone, Copy)] struct S { a: i32, b: i32 }\n\
             const C: S = S { a: 7, b: 11 };\n\
             fn main() { let s = C; std::process::exit(((s.a * 3 + s.b * 5) & 0xff) as i32); }",
            76,
        ),
        // {i8,i64} const struct that rustc REORDERS to i64@0, i8@8 — read each field
        // at its layout offset, NOT declaration order. (-5 as i64) + 1000*7 = 6995;
        // & 0xff = 83.
        (
            "const_struct_reorder_i8i64",
            "#[derive(Clone, Copy)] struct S { a: i8, b: i64 }\n\
             const C: S = S { a: -5, b: 1000 };\n\
             fn main() { let s = C; \
                std::process::exit((((s.a as i64) + s.b * 7) & 0xff) as i32); }",
            ((-5i64 + 1000 * 7) & 0xff) as i32,
        ),
        // {u8,u8,u8,u8} packed const struct: 1 + 2*2 + 3*4 + 4*8 = 49.
        (
            "const_struct_u8x4",
            "#[derive(Clone, Copy)] struct S { a: u8, b: u8, c: u8, d: u8 }\n\
             const C: S = S { a: 1, b: 2, c: 3, d: 4 };\n\
             fn main() { let s = C; std::process::exit((((s.a as i32) + (s.b as i32) * 2 \
                + (s.c as i32) * 4 + (s.d as i32) * 8) & 0xff) as i32); }",
            49,
        ),
        // Extreme-value mixed-sign reordered const struct.
        // a=-1,b=255,c=-2,d=65535: (-1) + 255*2 + (-2)*4 + 65535*8 = 524781; & 0xff.
        (
            "const_struct_extreme",
            "#[derive(Clone, Copy)] struct S { a: i8, b: u8, c: i16, d: u16 }\n\
             const C: S = S { a: -1, b: 255, c: -2, d: 65535 };\n\
             fn main() { let s = C; std::process::exit((((s.a as i64) + (s.b as i64) * 2 \
                + (s.c as i64) * 4 + (s.d as i64) * 8) & 0xff) as i32); }",
            ((-1i64 + 255 * 2 + (-2) * 4 + 65535 * 8) & 0xff) as i32,
        ),
        // --- CONTROLS: already-working memory-backed const aggregate by value. ---
        // A const struct passed BY VALUE to a fn (memory-backed ABI path). 76.
        (
            "const_struct_byval_call",
            "#[derive(Clone, Copy)] struct S { a: i32, b: i32 }\n\
             const C: S = S { a: 7, b: 11 };\n\
             #[inline(never)] fn f(s: S) -> i32 { s.a * 3 + s.b * 5 }\n\
             fn main() { std::process::exit((f(C) & 0xff) as i32); }",
            76,
        ),
        // An INLINE struct literal (not const) — the pre-existing scalarized path. 76.
        (
            "inline_struct_ctrl",
            "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }\n\
             #[derive(Clone, Copy)] struct S { a: i32, b: i32 }\n\
             fn main() { let s = S { a: bb(7), b: bb(11) }; \
                std::process::exit(((s.a * 3 + s.b * 5) & 0xff) as i32); }",
            76,
        ),
        // --- FAIL-CLOSED-OR-CORRECT neighbors: shapes the fix deliberately excludes.
        // A const struct with a NESTED aggregate field (out of scope -> fail closed). 26.
        (
            "const_struct_nested_neighbor",
            "#[derive(Clone, Copy)] struct In { x: i32, y: i32 }\n\
             #[derive(Clone, Copy)] struct S { a: In, b: i32 }\n\
             const C: S = S { a: In { x: 1, y: 2 }, b: 3 };\n\
             fn main() { let s = C; \
                std::process::exit(((s.a.x * 3 + s.a.y * 5 + s.b * 7) & 0xff) as i32); }",
            (1 * 3 + 2 * 5 + 3 * 7) & 0xff,
        ),
        // A const struct with a FLOAT field (out of scope -> fail closed). 76.
        (
            "const_struct_float_neighbor",
            "#[derive(Clone, Copy)] struct S { a: i32, b: f64 }\n\
             const C: S = S { a: 7, b: 11.0 };\n\
             fn main() { let s = C; \
                std::process::exit(((s.a * 3 + (s.b as i32) * 5) & 0xff) as i32); }",
            76,
        ),
        // A const tuple with a BOOL field (out of scope -> fail closed). 21.
        (
            "const_tuple_bool_neighbor",
            "const C: (bool, i32) = (true, 7);\n\
             fn main() { let t = C; \
                std::process::exit(((if t.0 { t.1 * 3 } else { t.1 * 5 }) & 0xff) as i32); }",
            21,
        ),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}
