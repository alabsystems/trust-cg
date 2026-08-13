// Integration test (#m93): passing an intercepted COLLECTION BY REFERENCE
// (`&Vec`/`&mut Vec`, `&HashMap`/`&mut HashMap`, `&BTreeMap`/`&mut BTreeMap`) to
// a USER-DEFINED helper function — compiled for x86_64 via the
// rustc_codegen_trust_cg bridge, LINKED, RUN, and checked against the default
// LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE GAP THIS CLOSES. `Vec<T>` / `BTreeMap<K,V>` / `HashMap<K,V>` are intercepted
// as a single `Ptr` to a `{ptr,cap,len}` stack slot, and their methods are
// intercepted at the Call terminator. The interceptors RECOGNIZED a call as a
// collection method purely by the SHAPE of the first argument's type — `&mut Vec`,
// `&mut HashMap` — so a user helper whose first parameter is a collection,
//
//     fn fill(v: &mut Vec<i64>, n: i64) { while .. { v.push(..); } }
//     fill(&mut v, n);
//
// was MIS-ROUTED into the interceptor and failed closed ("`Vec::<i64>::fill` is
// not an intercepted Vec method"). The fix gates self-keyed recognition on the
// callee actually being a std/alloc/core/hashbrown collection method
// (`is_std_collection_method_callee`); a user helper falls through to the general
// call path, which passes the collection by reference (a pointer to its
// slot-address `Ptr`). Inside the helper, the genuine std method on `*v` is
// intercepted, and `vec_self_slot_addr` LOADS the slot pointer through the
// reference parameter (one extra indirection vs. a direct `v.method()` call).
//
// At `-O3` rustc inlines the public `HashMap`/`BTreeMap` `insert`/`get` and
// borrows the INNER `hashbrown` map THROUGH the `&mut` parameter
// (`_10 = &mut ((*_1).0)`); that projected-deref reborrow is also handled (the
// `.0`/`.base` field is at offset 0 and aliases the slot pointer).
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (a wrong collection result would be a miscompile,
// so equal exit codes are the differential we assert). This file gates exactly
// the by-reference-collection-to-helper shapes that compile + run today.

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
    assert!(status.success(), "cargo build failed; cannot run m93 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m93_{stem}_{}", std::process::id()));
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
        "compile of `{name}` failed ({} backend, {opt}). stderr: <<<{}>>>",
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

/// The opt levels each shape's collection backing is supported at.
#[derive(Clone, Copy)]
enum Opt {
    /// Both `-O0` and `-O3` (the map shapes: their read-back is `get`/`len`).
    Both,
    /// Only `-O0`. Used by the immutable `&BTreeMap` get-through-reference shape:
    /// at `-O3` rustc inlines `BTreeMap::get` THROUGH the `&BTreeMap` parameter
    /// into the real B-tree node descent (no inner-`hashbrown` indirection to
    /// intercept, unlike `HashMap`), which is unlowerable — so the helper fails
    /// CLOSED at `-O3` (never miscompiles). (The `Vec` shapes USED to be restricted
    /// here by a since-fixed `Vec`-at-`-O3` aggregate-construction gap; they now
    /// run at both levels — see `m94_vec_o3_x86.rs`.)
    ZeroOnly,
}

/// The differential: each by-reference-collection-to-helper program is compiled
/// by trust-cg AND LLVM and run; the exit codes must match each other and the
/// expected value. A divergence would be a miscompile.
#[test]
fn mutref_collection_to_helper_runs_and_matches_llvm() {
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

    // (name, source, expected exit code, opt support).
    let shapes: &[(&str, &str, i32, Opt)] = &[
        // (1) `&mut Vec` to a helper that pushes in a loop; main reads len.
        (
            "vec_mut_push_len",
            "use std::hint::black_box; \
             fn fill(v: &mut Vec<i64>, n: i64) { let mut i = 0; while i < n { v.push(i); i += 1; } } \
             fn main() { let mut v: Vec<i64> = Vec::new(); fill(&mut v, black_box(5)); \
             std::process::exit(v.len() as i32); }",
            5,
            Opt::Both,
        ),
        // (2) `&mut Vec` helper pushes `i*2`; main sums via `v[j]`. Sum 0+2+4+6+8=20.
        (
            "vec_mut_sum",
            "use std::hint::black_box; \
             fn fill(v: &mut Vec<i64>, n: i64) { let mut i = 0; while i < n { v.push(i*2); i += 1; } } \
             fn main() { let mut v: Vec<i64> = Vec::new(); fill(&mut v, black_box(5)); \
             let mut s = 0i64; let mut j = 0usize; while j < v.len() { s += v[j]; j += 1; } \
             std::process::exit(s as i32); }",
            20,
            Opt::Both,
        ),
        // (3) helper READS a `Vec` via `&` (immutable) and returns its len.
        (
            "vec_imm_len",
            "use std::hint::black_box; \
             fn total(v: &Vec<i64>) -> i64 { v.len() as i64 } \
             fn main() { let mut v: Vec<i64> = Vec::new(); let mut i = 0; \
             while i < black_box(7i64) { v.push(i); i += 1; } \
             std::process::exit(total(&v) as i32); }",
            7,
            Opt::Both,
        ),
        // (4) nested: `fill` calls `push_one(&mut v, ..)` (the &mut threads through
        // two helper frames).
        (
            "vec_nested_helper",
            "use std::hint::black_box; \
             fn push_one(v: &mut Vec<i64>, x: i64) { v.push(x); } \
             fn fill(v: &mut Vec<i64>, n: i64) { let mut i = 0; while i < n { push_one(v, i); i += 1; } } \
             fn main() { let mut v: Vec<i64> = Vec::new(); fill(&mut v, black_box(6)); \
             std::process::exit(v.len() as i32); }",
            6,
            Opt::Both,
        ),
        // (5) two `Vec`s passed to ONE helper that mutates both.
        (
            "vec_two_collections",
            "use std::hint::black_box; \
             fn fill2(a: &mut Vec<i64>, b: &mut Vec<i64>, n: i64) \
             { let mut i = 0; while i < n { a.push(i); b.push(i*i); i += 1; } } \
             fn main() { let mut a: Vec<i64> = Vec::new(); let mut b: Vec<i64> = Vec::new(); \
             fill2(&mut a, &mut b, black_box(4)); \
             std::process::exit((a.len() + b.len()) as i32); }",
            8,
            Opt::Both,
        ),
        // (6) `&mut HashMap` to a helper that inserts in a loop. get(&3)=30, len=5 -> 35.
        (
            "map_mut_insert",
            "use std::hint::black_box; use std::collections::HashMap; \
             fn fill(m: &mut HashMap<i64,i64>, n: i64) \
             { let mut i = 0; while i < n { m.insert(i, i*10); i += 1; } } \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); fill(&mut m, black_box(5)); \
             let s = m.get(&3).copied().unwrap_or(0) + m.len() as i64; std::process::exit(s as i32); }",
            35,
            Opt::Both,
        ),
        // (7) helper READS a `HashMap` via `&` (immutable) and returns get. -> 40.
        (
            "map_imm_get",
            "use std::hint::black_box; use std::collections::HashMap; \
             fn lookup(m: &HashMap<i64,i64>, k: i64) -> i64 { m.get(&k).copied().unwrap_or(-1) } \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(4i64), black_box(40i64)); \
             std::process::exit(lookup(&m, 4) as i32); }",
            40,
            Opt::Both,
        ),
        // (8) nested: `fill` calls `ins(&mut m, ..)`. get(&2)=200, len=5 -> 205.
        (
            "map_nested_helper",
            "use std::hint::black_box; use std::collections::HashMap; \
             fn ins(m: &mut HashMap<i64,i64>, k: i64, v: i64) { m.insert(k, v); } \
             fn fill(m: &mut HashMap<i64,i64>, n: i64) \
             { let mut i = 0; while i < n { ins(m, i, i*100); i += 1; } } \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); fill(&mut m, black_box(5)); \
             std::process::exit((m.get(&2).copied().unwrap_or(0) + m.len() as i64) as i32); }",
            205,
            Opt::Both,
        ),
        // (9) two `HashMap`s passed to ONE helper that inserts into both.
        // a.get(&3)=3, b.get(&3)=6 -> 9.
        (
            "map_two_collections",
            "use std::hint::black_box; use std::collections::HashMap; \
             fn fill2(a: &mut HashMap<i64,i64>, b: &mut HashMap<i64,i64>, n: i64) \
             { let mut i = 0; while i < n { a.insert(i,i); b.insert(i,i*2); i += 1; } } \
             fn main() { let mut a: HashMap<i64,i64> = HashMap::new(); \
             let mut b: HashMap<i64,i64> = HashMap::new(); fill2(&mut a, &mut b, black_box(5)); \
             std::process::exit((a.get(&3).copied().unwrap_or(0) \
             + b.get(&3).copied().unwrap_or(0)) as i32); }",
            9,
            Opt::Both,
        ),
        // (10) `&mut BTreeMap` to a helper that inserts in a loop. get(&3)=30, len=5 -> 35.
        (
            "btm_mut_insert",
            "use std::hint::black_box; use std::collections::BTreeMap; \
             fn fill(m: &mut BTreeMap<i64,i64>, n: i64) \
             { let mut i = 0; while i < n { m.insert(i, i*10); i += 1; } } \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); fill(&mut m, black_box(5)); \
             let s = m.get(&3).copied().unwrap_or(0) + m.len() as i64; std::process::exit(s as i32); }",
            35,
            Opt::Both,
        ),
        // (11) helper READS a `BTreeMap` via `&` and returns get + len. get(&2)=20, len=3 -> 23.
        // `-O0` only: at `-O3` rustc inlines `BTreeMap::get` THROUGH the `&BTreeMap`
        // parameter into the real B-tree node descent (no inner-`hashbrown`
        // indirection to intercept, unlike `HashMap`), which is unlowerable, so the
        // helper fails CLOSED at `-O3` (never miscompiles). The mutable-insert
        // BTreeMap helper (shape 10) does intercept at `-O3` and matches.
        (
            "btm_imm_get",
            "use std::hint::black_box; use std::collections::BTreeMap; \
             fn lookup(m: &BTreeMap<i64,i64>) -> i64 \
             { m.get(&2).copied().unwrap_or(0) + m.len() as i64 } \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             let mut i = 0; while i < black_box(3i64) { m.insert(i, i*10); i += 1; } \
             std::process::exit(lookup(&m) as i32); }",
            23,
            Opt::ZeroOnly,
        ),
    ];

    for (name, src, expected, opt_support) in shapes {
        let opts: &[&str] = match opt_support {
            Opt::Both => &["0", "3"],
            Opt::ZeroOnly => &["0"],
        };
        for opt in opts {
            let suffix = format!("o{opt}");
            let llvm_bin = compile(&dir, &format!("{name}_{suffix}_llvm"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_{suffix}_tcg"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM backend exit code for `{name}` (-Copt-level={opt}) is {llvm_exit}, \
                 expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{name}` (-Copt-level={opt}) is {tcg_exit}, LLVM is \
                 {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// The `Vec`-by-reference-to-helper shape now RUNS and MATCHES LLVM at `-O3`
/// (the `Vec`-at-`-O3` inlined-construction/index gap this test once pinned as
/// fail-closed is fixed — see `m94_vec_o3_x86.rs`). A `&mut Vec` helper pushes a
/// loop; `main` reads back `v.len()` through the inlined `len`-field projection.
/// The exit code must equal LLVM's at `-O3` (a divergence is a miscompile).
#[test]
fn vec_mutref_helper_runs_and_matches_llvm_o3() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("vec_o3");

    let src = "use std::hint::black_box; \
               fn fill(v: &mut Vec<i64>, n: i64) { let mut i = 0; while i < n { v.push(i); i += 1; } } \
               fn main() { let mut v: Vec<i64> = Vec::new(); fill(&mut v, black_box(5)); \
               std::process::exit(v.len() as i32); }";

    let llvm_bin = compile(&dir, "vec_o3_llvm", src, None, "3");
    let tcg_bin = compile(&dir, "vec_o3_tcg", src, Some(&dylib), "3");
    let llvm_exit = run_exit_code(&llvm_bin);
    let tcg_exit = run_exit_code(&tcg_bin);
    assert_eq!(llvm_exit, 5, "LLVM Vec helper len -O3 should be 5");
    assert_eq!(
        tcg_exit, llvm_exit,
        "trust-cg Vec helper len -O3 is {tcg_exit}, LLVM is {llvm_exit} (must match)"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
