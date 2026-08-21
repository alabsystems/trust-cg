#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: `<[T]>::to_vec` / `<[T] as ToOwned>::to_owned` and the
// `&str -> String` constructors (`String::from` / `str::to_string` /
// `str::to_owned`) compiled for x86_64 via the rustc_codegen_trust_cg bridge —
// COMPILED, LINKED, and RUN, with exit codes checked against the default LLVM
// backend (X1: the `Vec::<u8>::to_vec is not an intercepted Vec method` gap).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The bridge lowers these as a CALL-SITE materialization (never the real std
// bodies, which would return an escaping frame slot): a fresh `{ptr,cap,len}`
// stack slot, `__rust_alloc(max(n,1) * size, align)`, a proven typed copy loop
// of the `n` source elements, `len = n` — `lower_slice_to_vec`, mirroring
// `lower_vec_new` + the `extend_from_slice` copy path. A `String` destination
// is the byte-identical slot over `u8` (`lower_fmt_call` routes the three
// `&str -> String` constructor names to the same materialization).
//
// The differential pins CONTENT, not just lengths: byte reads through
// `as_bytes`, a negative `i32` element, a runtime (memory-backed fat-pointer)
// source slice, and CLONE INDEPENDENCE (mutating the source `Vec` after
// `to_vec` must not change the clone — an aliased buffer diverges). The
// negative test pins that a USER method named `to_vec`, a `Box` (needs-drop)
// element, and a `String`-returning user fn (the collection return-escape
// guard) all stay FAIL-CLOSED — never a silent wrong value.

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
    let dir = std::env::temp_dir().join(format!("rcl2_m122_{stem}_{}", std::process::id()));
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
        "compile of `{name}` failed ({} backend, opt={opt}). stderr: <<<{}>>>",
        if backend.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The O0 differential: each program is compiled by trust-cg AND LLVM, run, and
/// the exit codes must match each other and the expected value. Content (byte
/// reads, a negative element, clone independence) is part of every exit code, so
/// a wrong copied byte, wrong length, or aliased clone buffer diverges.
#[test]
fn to_vec_and_string_from_match_llvm_at_o0() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("run");

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        // `String::from(&str)`: length + byte content ('h' = 104).
        (
            "string_from_len_and_content",
            "fn main() { let s = String::from(\"hi\"); \
             std::process::exit(s.len() as i32 * 10 + (s.as_bytes()[0] as i32 - 100)); }",
            24,
        ),
        // `str::to_string`.
        (
            "str_to_string_len",
            "fn main() { let s = \"hey\".to_string(); std::process::exit(s.len() as i32); }",
            3,
        ),
        // `str::to_owned`: byte content ('c' = 99).
        (
            "str_to_owned_content",
            "fn main() { let s = \"abc\".to_owned(); \
             std::process::exit(s.as_bytes()[2] as i32 + s.len() as i32); }",
            102,
        ),
        // `<[u8]>::to_vec` from a const array literal: length + content.
        (
            "slice_to_vec_u8_content",
            "fn main() { let v = [10u8, 20, 30].to_vec(); \
             std::process::exit(v.len() as i32 + v[0] as i32 + v[2] as i32); }",
            43,
        ),
        // A non-u8 element with a NEGATIVE value (sign-correct element copy).
        (
            "slice_to_vec_i32_negative",
            "fn main() { let v = [100i32, -3, 7].to_vec(); \
             std::process::exit(v[0] + v[1] * 10 + v[2]); }",
            77,
        ),
        // FLOAT BYTE-MOVEMENT CONTRACT: exercise every Vec/slice operation that
        // is sound as a typed bitwise copy for `f32`/`f64`: `to_vec`, `extend`,
        // `extend_from_slice`, `append`, `split_off`, `clone_from`, and `repeat`.
        // Signed-zero bit checks ensure the path preserves payload bits rather
        // than accidentally converting through an integer or numeric value.
        (
            "float_vec_byte_movement_ops",
            "fn main() { \
             let base = [0.0f64, -0.0, f64::from_bits(0x7ff8_0000_0000_0042), 3.25]; \
             let mut a = base.to_vec(); \
             a.extend_from_slice(&[1.5, -2.5]); \
             let mut b = [7.0f64, 8.0].to_vec(); a.append(&mut b); \
             let tail = a.split_off(5); \
             let mut c = [9.0f64].to_vec(); c.clone_from(&tail); \
             let rep = [1.25f32, -0.0].repeat(3); \
             let mut d = [11.0f32].to_vec(); d.extend(&rep); \
             let mut code = (a.len()+b.len()+tail.len()+c.len()+rep.len()+d.len()) as i32; \
             if a[1].to_bits() == (-0.0f64).to_bits() { code += 11; } \
             if tail[0].to_bits() == (-2.5f64).to_bits() { code += 13; } \
             if c[2].to_bits() == 8.0f64.to_bits() { code += 17; } \
             if rep[3].to_bits() == (-0.0f32).to_bits() { code += 19; } \
             if d[2].to_bits() == (-0.0f32).to_bits() { code += 23; } \
             std::process::exit(code); }",
            107,
        ),
        // Float Vec equality must follow IEEE `PartialEq`, not bit equality:
        // signed zeros compare equal while every NaN comparison is unequal.
        (
            "float_vec_equality_partial_eq",
            "fn main() { \
             let mut score = 0; \
             if [1.0f64, 2.0].to_vec() == [1.0f64, 2.0].to_vec() { score += 1; } \
             if [1.0f64, 2.0].to_vec() != [1.0f64, 3.0].to_vec() { score += 1; } \
             if [1.0f64].to_vec() != [1.0f64, 2.0].to_vec() { score += 1; } \
             if [0.0f64].to_vec() == [-0.0f64].to_vec() { score += 1; } \
             let n64 = f64::from_bits(0x7ff8_0000_0000_0042); \
             if [n64].to_vec() != [n64].to_vec() { score += 1; } \
             if [1.0f32, 2.0].to_vec() == [1.0f32, 2.0].to_vec() { score += 1; } \
             if [0.0f32].to_vec() == [-0.0f32].to_vec() { score += 1; } \
             let n32 = f32::from_bits(0x7fc0_0042); \
             if [n32].to_vec() != [n32].to_vec() { score += 1; } \
             std::process::exit(score); }",
            8,
        ),
        // Float slice `contains` uses IEEE ordered equality: signed zero matches,
        // while a NaN needle never does. Cover both supported widths.
        (
            "float_slice_contains_partial_eq",
            "fn main() { \
             let mut score = 0; \
             if [1.0f64, 2.0].contains(&2.0) { score += 1; } \
             if ![1.0f64, 2.0].contains(&3.0) { score += 1; } \
             if [0.0f64].contains(&-0.0) { score += 1; } \
             if ![f64::NAN].contains(&f64::NAN) { score += 1; } \
             if [1.0f32, 2.0].contains(&2.0) { score += 1; } \
             if ![f32::NAN].contains(&f32::NAN) { score += 1; } \
             std::process::exit(score); }",
            6,
        ),
        // Float Vec/slice lexicographic `partial_cmp` uses IEEE ordering. Prefix
        // ordering remains decisive, signed zero compares equal, and any first
        // differing NaN lane returns `None` (the Ordering option's niche value).
        (
            "float_vec_partial_cmp_ieee",
            "fn main() { \
             use std::cmp::Ordering; let mut score = 0; \
             if [1.0f64, 2.0].to_vec().partial_cmp(&[1.0f64, 3.0].to_vec()) == Some(Ordering::Less) { score += 1; } \
             if [1.0f64, 4.0].to_vec().partial_cmp(&[1.0f64, 3.0].to_vec()) == Some(Ordering::Greater) { score += 1; } \
             if [1.0f64, 2.0].to_vec().partial_cmp(&[1.0f64, 2.0].to_vec()) == Some(Ordering::Equal) { score += 1; } \
             if [1.0f64].to_vec().partial_cmp(&[1.0f64, 2.0].to_vec()) == Some(Ordering::Less) { score += 1; } \
             let n64 = f64::from_bits(0x7ff8_0000_0000_0042); \
             if [n64].to_vec().partial_cmp(&[n64].to_vec()).is_none() { score += 1; } \
             if [0.0f64].to_vec().partial_cmp(&[-0.0f64].to_vec()) == Some(Ordering::Equal) { score += 1; } \
             if [2.0f32].to_vec().partial_cmp(&[1.0f32].to_vec()) == Some(Ordering::Greater) { score += 1; } \
             let n32 = f32::from_bits(0x7fc0_0042); \
             if [1.0f32, n32].to_vec().partial_cmp(&[1.0f32, 2.0].to_vec()).is_none() { score += 1; } \
             std::process::exit(score); }",
            8,
        ),
        // Float `Vec::resize` retains existing lanes, writes every grown lane with
        // the exact fill payload (including NaN payload bits), and shrinks without
        // perturbing the retained prefix. Exercise both f64 and f32 helpers.
        (
            "float_vec_resize_typed_fill",
            "fn main() { \
             let fill64 = f64::from_bits(0x7ff8_0000_0000_0042); \
             let mut a = [1.5f64, -0.0].to_vec(); a.resize(4, fill64); \
             let mut score = 0; \
             if a.len() == 4 { score += 1; } \
             if a[0].to_bits() == 1.5f64.to_bits() && a[1].to_bits() == (-0.0f64).to_bits() { score += 1; } \
             if a[2].to_bits() == fill64.to_bits() && a[3].to_bits() == fill64.to_bits() { score += 1; } \
             a.resize(1, 9.0); \
             if a.len() == 1 && a[0].to_bits() == 1.5f64.to_bits() { score += 1; } \
             let fill32 = f32::from_bits(0x7fc0_0042); \
             let mut b = [2.5f32].to_vec(); b.resize(3, fill32); \
             if b.len() == 3 { score += 1; } \
             if b[0].to_bits() == 2.5f32.to_bits() { score += 1; } \
             if b[1].to_bits() == fill32.to_bits() { score += 1; } \
             if b[2].to_bits() == fill32.to_bits() { score += 1; } \
             std::process::exit(score); }",
            8,
        ),
        // `<[u16] as ToOwned>::to_owned` through a borrowed slice.
        (
            "slice_to_owned_u16",
            "fn main() { let a: [u16; 4] = [10, 20, 30, 40]; let s = &a[..]; \
             let v: Vec<u16> = s.to_owned(); std::process::exit((v[3] + v[1]) as i32); }",
            60,
        ),
        // The source slice is a RUNTIME fat pointer (a fn parameter).
        (
            "runtime_slice_param_to_vec",
            "#[inline(never)] fn dup(s: &[u8]) -> u8 { let v = s.to_vec(); v[1] } \
             fn main() { let a = [3u8, 44, 5]; std::process::exit(dup(&a) as i32); }",
            44,
        ),
        // CLONE INDEPENDENCE: mutating the source after `v.to_vec()` must not
        // change the clone; both vecs are dropped (frees both buffers).
        (
            "clone_independence",
            "fn main() { let mut v: Vec<u8> = Vec::new(); \
             v.push(11); v.push(22); v.push(33); \
             let w = v.to_vec(); v.push(44); v.truncate(1); \
             std::process::exit((w.len() as i32) * 10 + (w[2] as i32 - 30) \
             + (v.len() as i32 * 100)); }",
            133,
        ),
        // The String is dropped on the normal return path (its buffer is freed
        // through the same `{ptr,cap,len}` slot Drop the Vec model uses).
        (
            "string_from_drop_path",
            "fn code() -> i32 { let s = String::from(\"hello\"); \
             (s.len() as i32) * 10 + (s.as_bytes()[4] as i32 - 100) } \
             fn main() { std::process::exit(code()); }",
            61,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None, "0");
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib), "0");
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            tcg_exit, llvm_exit,
            "`{name}`: trust-cg exit {tcg_exit} != LLVM exit {llvm_exit} (MISCOMPILE)"
        );
        assert_eq!(
            tcg_exit, *expected,
            "`{name}`: exit {tcg_exit} != expected {expected}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// The Vec-kept-alive `to_vec` shape ALSO compiles at O2/O3 (the inlined form
/// routes through the existing `try_allocate_in` chain + `copy_nonoverlapping`
/// machinery once the `Vec` local survives): all three opt levels must match.
#[test]
fn to_vec_push_shape_matches_llvm_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("opt");
    let src = "fn main() { let mut v = [1u8, 2, 3].to_vec(); v.push(4); \
               let mut s = 0i64; let mut j = 0usize; \
               while j < v.len() { s += v[j] as i64; j += 1; } \
               std::process::exit(s as i32); }";
    for opt in ["0", "2", "3"] {
        let llvm_bin = compile(&dir, &format!("tvp_o{opt}_llvm"), src, None, opt);
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_bin = compile(&dir, &format!("tvp_o{opt}_tcg"), src, Some(&dylib), opt);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            tcg_exit, llvm_exit,
            "to_vec+push (opt={opt}): trust-cg exit {tcg_exit} != LLVM {llvm_exit}"
        );
        assert_eq!(tcg_exit, 10, "to_vec+push (opt={opt}): exit != 10");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Unsupported shapes stay FAIL-CLOSED (a loud [TCG-MIR-UNSUPPORTED], never a
/// wrong value): a USER method named `to_vec` (must not be misrouted into the
/// std interception), a needs-drop (`Box`) element, and a user fn RETURNING a
/// `String` by value (the collection return-escape guard — its `{ptr,cap,len}`
/// slot would die with the callee frame).
#[test]
fn unsupported_to_vec_shapes_stay_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("neg");

    let negatives: &[(&str, &str, &str)] = &[
        (
            "user_to_vec_not_misrouted",
            "struct W; impl W { fn to_vec(&self) -> Vec<u8> { \
             let mut v = Vec::new(); v.push(9); v } } \
             fn main() { let v = W.to_vec(); std::process::exit(v[0] as i32); }",
            "is not an intercepted Vec method",
        ),
        (
            "box_element_to_vec",
            "fn main() { let v = [Box::new(1i64), Box::new(2)].to_vec(); \
             std::process::exit(*v[0] as i32); }",
            "TCG-MIR-UNSUPPORTED",
        ),
        (
            "string_return_escape_guard",
            "fn make() -> String { String::new() } \
             fn main() { let a = make(); std::process::exit(a.len() as i32 + 41); }",
            "escape its frame-local",
        ),
    ];

    for (name, src, needle) in negatives {
        let (output, _bin) = try_compile(&dir, name, src, Some(&dylib), "0");
        assert!(
            !output.status.success(),
            "`{name}`: expected trust-cg to FAIL CLOSED but it compiled"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(needle),
            "`{name}`: fail-closed message does not contain {needle:?}: <<<{stderr}>>>"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
