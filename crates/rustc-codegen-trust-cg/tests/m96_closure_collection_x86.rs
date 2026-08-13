// Integration test: CLOSURES that CAPTURE an intercepted collection
// (`Vec`/`HashMap`/`BTreeMap`/`String`) BY REFERENCE — compiled for x86_64 via
// the rustc_codegen_trust_cg bridge, COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS LOCKS IN. An intercepted collection is modeled as a single `Ptr`
// (the address of its `{ ptr, cap, len }` slot). A closure that captures
// `&Vec` / `&mut Vec` / `&mut HashMap` by reference captures that POINTER as a
// thin-scalar upvar, so the closure-env machinery (scalarized for a stored /
// directly-called closure, memory-backed for a closure passed by value into a
// generic `fn f<F: FnMut(..)>`) threads it and the body's method interception
// (`vec_self_slot_addr`) re-derefs it. These by-reference capture shapes RUN
// and MATCH LLVM at -O0 (the opt level at which each collection's interception
// is active):
//   * `&mut Vec` captured + `push`ed in a stored `FnMut` closure called in a loop.
//   * `&mut Vec` captured + a closure passed by value into a generic FnMut caller.
//   * `&Vec` captured + indexed in a stored closure.
//   * two collections captured by one closure.
//   * a closure stored in a local and called twice, mutating a captured Vec.
//   * `&mut HashMap` captured + `insert`/`get`/`len` (the interception-supported
//     HashMap methods) in a stored closure.
//
// WHAT FAILS CLOSED (and why — never a miscompile):
//   * BY-VALUE (`move`) capture of a collection: rustc lays the value out as its
//     full `{ ptr, cap, len }` struct inline in the env while the bridge models
//     it as one `Ptr`; the moved-in handle also routes through the un-lowered
//     `FnOnce::call_once` shim. `closure_memory_layout` rejects the collection
//     leaf, so the compile fails closed.
//   * A NESTED closure capturing an intercepted-collection reference ALONGSIDE
//     another upvar (`let mut outer = |base| { let mut inner = |x| v.push(x +
//     base); inner(0); };`): the doubled env indirection mis-threads the
//     two-pointer env and would MISCOMPILE the captured-collection write (a real
//     differential showed wrong Vec elements). A dedicated soundness guard
//     (`reject_unsound_nested_collection_ref_closure`) fails this closed.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A divergence is a
// miscompile, so equal exit codes are the differential we assert.

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
    assert!(status.success(), "cargo build failed; cannot run closure-collection test");
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

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m96_{stem}_{}", std::process::id()));
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

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

fn assert_match(dir: &Path, dylib: &Path, name: &str, src: &str, expected: i32, opt: &str) {
    let suffix = format!("o{opt}");
    let llvm_bin = compile(dir, &format!("{name}_{suffix}_llvm"), src, None, opt);
    let tcg_bin = compile(dir, &format!("{name}_{suffix}_tcg"), src, Some(dylib), opt);
    let llvm_exit = run_exit_code(&llvm_bin);
    let tcg_exit = run_exit_code(&tcg_bin);
    assert_eq!(
        llvm_exit, expected,
        "LLVM backend exit code for `{name}` (-Copt-level={opt}) is {llvm_exit}, expected {expected}"
    );
    assert_eq!(
        tcg_exit, llvm_exit,
        "trust-cg exit code for `{name}` (-Copt-level={opt}) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
    );
}

fn assert_fails_closed(dir: &Path, dylib: &Path, name: &str, src: &str, opt: &str) {
    // The program must be a VALID Rust program (LLVM compiles+links it) that
    // trust-cg refuses to compile — i.e. fails closed rather than miscompiling.
    let _llvm_bin = compile(dir, &format!("{name}_o{opt}_llvm"), src, None, opt);
    let (output, bin) = try_compile(dir, &format!("{name}_o{opt}_tcg"), src, Some(dylib), opt);
    assert!(
        !output.status.success() && !bin.exists(),
        "trust-cg unexpectedly compiled `{name}` at -O{opt}; if it now lowers CORRECTLY \
         (verify against LLVM!), promote it into the run+match set — but a captured-collection \
         write must never be allowed to miscompile"
    );
}

/// The by-REFERENCE closure-over-collection shapes that RUN and MATCH LLVM.
#[test]
fn closure_collection_by_ref_programs_run_and_match_llvm() {
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

    // (name, source, expected exit code). All gated at -O0, where each
    // collection's interception is active and the closure-env path threads the
    // captured slot pointer.
    let shapes: &[(&str, &str, i32)] = &[
        // &mut Vec captured + pushed in a stored FnMut closure called in a loop.
        (
            "vec_push_stored_loop",
            "fn main(){ let mut v: Vec<i64> = Vec::new(); \
             let mut p = |x: i64| v.push(x); \
             let mut k = 0i64; while k < 5 { p(k * 2); k += 1; } \
             let mut s = 0i64; let mut j = 0; let n = v.len(); \
             while j < n { s += v[j]; j += 1; } \
             std::process::exit(s as i32); }",
            20, // 0+2+4+6+8
        ),
        // &mut Vec captured + closure passed by value into a generic FnMut caller.
        (
            "vec_push_generic_fnmut",
            "#[inline(never)] fn go<F: FnMut(i64)>(mut f: F) { f(1); f(2); f(3); } \
             fn main(){ let mut v: Vec<i64> = Vec::new(); \
             go(|x| v.push(x * x)); \
             let mut s = 0i64; let mut j = 0; let n = v.len(); \
             while j < n { s += v[j]; j += 1; } \
             std::process::exit(s as i32); }",
            14, // 1+4+9
        ),
        // &Vec captured + indexed in a stored closure.
        (
            "vec_index_ref",
            "fn main(){ let mut v: Vec<i64> = Vec::new(); \
             v.push(3); v.push(1); v.push(4); \
             let pick = |i: usize| v[i]; \
             let r = pick(0) + pick(2); \
             std::process::exit(r as i32); }",
            7, // 3+4
        ),
        // Two collections captured by one closure (mutual push).
        (
            "two_vecs_one_closure",
            "fn main(){ let mut a: Vec<i64> = Vec::new(); let mut b: Vec<i64> = Vec::new(); \
             let mut both = |x: i64| { a.push(x); b.push(x * 10); }; \
             both(1); both(2); both(3); \
             let mut s = 0i64; let mut j = 0; let n = a.len(); \
             while j < n { s += a[j] + b[j]; j += 1; } \
             std::process::exit(s as i32); }",
            66, // (1+2+3)+(10+20+30)
        ),
        // Closure stored in a local, called twice, mutating a captured Vec.
        (
            "closure_stored_called_twice",
            "use std::hint::black_box; \
             fn main(){ let mut acc: Vec<i64> = Vec::new(); \
             let mut push2 = |x: i64| { acc.push(x); acc.push(x + 1); }; \
             push2(black_box(10)); push2(black_box(20)); \
             let mut s = 0i64; let mut j = 0; let n = acc.len(); \
             while j < n { s += acc[j]; j += 1; } \
             std::process::exit(s as i32); }",
            62, // 10+11+20+21
        ),
        // Closure returns a value derived from a captured &Vec.
        (
            "closure_returns_from_ref",
            "fn main(){ let mut v: Vec<i64> = Vec::new(); \
             v.push(7); v.push(8); v.push(9); \
             let sum = || { let mut s = 0i64; let mut j = 0; let n = v.len(); \
             while j < n { s += v[j]; j += 1; } s }; \
             std::process::exit(sum() as i32); }",
            24, // 7+8+9
        ),
        // SINGLE-upvar NESTED collection-ref capture: `|x| v.push(x)` inside an
        // outer closure. One upvar threads correctly and is left working.
        (
            "nested_single_upvar_vec",
            "fn main(){ let mut v: Vec<i64> = Vec::new(); \
             let mut outer = || { let mut inner = |x: i64| v.push(x); inner(5); inner(6); }; \
             outer(); outer(); \
             let mut s = 0i64; let mut j = 0; let n = v.len(); \
             while j < n { s += v[j]; j += 1; } \
             std::process::exit((s & 0xff) as i32); }",
            22, // 5+6+5+6
        ),
        // NESTED closure capturing TWO collection references (all-collection-ref
        // env, uniform pointer lanes) — `|x| { a.push(x); b.push(x + 1) }` inside
        // an outer closure. Uniform lanes thread correctly and MATCH (the soundness
        // guard only fires when a collection ref is MIXED with a non-collection
        // upvar).
        (
            "nested_two_collection_refs",
            "fn main(){ let mut a: Vec<i64> = Vec::new(); let mut b: Vec<i64> = Vec::new(); \
             let mut outer = || { \
                let mut inner = |x: i64| { a.push(x); b.push(x + 1); }; \
                inner(0); inner(1); \
             }; \
             outer(); outer(); \
             let mut s = 0i64; let mut j = 0; let n = a.len(); \
             while j < n { s += a[j] + b[j]; j += 1; } \
             std::process::exit((s & 0xff) as i32); }",
            8, // a=[0,1,0,1] b=[1,2,1,2] -> sum(a)+sum(b) = 2 + 6 = 8
        ),
        // &mut HashMap captured + insert/get/len (the interception-supported
        // HashMap methods) in a stored closure.
        (
            "hashmap_insert_stored",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main(){ let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut put = |k: i64, v: i64| { m.insert(k, v); }; \
             put(black_box(3), black_box(30)); \
             put(black_box(1), black_box(10)); \
             let s = m.get(&3).copied().unwrap_or(0) + m.len() as i64; \
             std::process::exit(s as i32); }",
            32, // 30+2
        ),
    ];

    for (name, src, expected) in shapes {
        assert_match(&dir, &dylib, name, src, *expected, "0");
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// Shapes that must FAIL CLOSED (never miscompile a captured-collection write).
#[test]
fn closure_collection_unsound_shapes_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("failclosed");

    // BY-VALUE (`move`) capture of a Vec: the moved-in handle's `{ptr,cap,len}`
    // env layout and the `FnOnce::call_once` shim are not modeled. Fails closed.
    assert_fails_closed(
        &dir,
        &dylib,
        "vec_by_move_capture",
        "#[inline(never)] fn run<F: FnOnce() -> i64>(f: F) -> i64 { f() } \
         fn main(){ let mut v: Vec<i64> = Vec::new(); v.push(5); v.push(7); \
         let total = move || { let mut s = 0i64; let mut j = 0; let n = v.len(); \
         while j < n { s += v[j]; j += 1; } s }; \
         std::process::exit(run(total) as i32); }",
        "0",
    );

    // NESTED closure capturing a `&mut Vec` reference ALONGSIDE a second upvar
    // (`base`): the doubled env indirection would MISCOMPILE the captured-Vec
    // write. The soundness guard fails it closed. (Differential before the guard:
    // llvm=90, trust-cg=2 — a silent wrong accumulation.)
    assert_fails_closed(
        &dir,
        &dylib,
        "nested_vec_ref_plus_base_miscompile_guard",
        "fn main(){ let mut v: Vec<i64> = Vec::new(); \
         let mut outer = |base: i64| { \
            let mut inner = |x: i64| v.push(x + base); \
            inner(0); inner(1); \
         }; \
         outer(100); outer(200); \
         let mut s = 0i64; let mut j = 0; let n = v.len(); \
         while j < n { s += v[j]; j += 1; } \
         std::process::exit((s & 0xff) as i32); }",
        "0",
    );

    let _ = std::fs::remove_dir_all(&dir);
}
