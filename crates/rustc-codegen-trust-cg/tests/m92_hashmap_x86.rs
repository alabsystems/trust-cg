#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: std Rust using `HashMap<K, V>` (integer keys/values)
// compiled for x86_64 via the rustc_codegen_trust_cg bridge — COMPILED, LINKED,
// and RUN, with exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS — keyed collections (`HashMap<K, V>`) RUN on x86_64 via trust-cg
// for INTEGER keys and values.
//
// The real `HashMap` method bodies descend into the `hashbrown` SwissTable /
// SipHash machinery the backend cannot lower, so — exactly as `BTreeMap<K, V>`
// is intercepted — the bridge intercepts the methods a simple integer map needs
// and synthesizes them against the SAME `{ ptr, cap, len }` slot whose heap
// buffer is a flat array of fixed 16-byte `[ key:i64 | value:i64 ]` entries
// (sharing the `__trustcg_btm_insert` / `__trustcg_btm_get` runtime helpers).
// This is sound because the differential only observes MAP SEMANTICS — `get`
// returns the last-inserted value for a key, `insert` overwrites, `len` counts
// distinct keys — never iteration order, so the hash/bucket layout (and SipHash)
// is unobservable and need not be replicated. `new`/`with_capacity`/
// `with_hasher`/`len`/`is_empty` are inline; `insert`/`get` call the helpers.
// The default `RandomState` hasher construction (a thread-local read at -O3) is
// dead for the backing store and is treated as a no-op.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A wrong map result is
// a miscompile, so equal exit codes are the differential we assert. This file
// gates exactly the `HashMap` shapes that compile + run today; iteration and
// non-integer-key/value shapes fail closed (asserted separately below).

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
    assert!(status.success(), "cargo build failed; cannot run HashMap test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_hm_{stem}_{}", std::process::id()));
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

/// The full differential: each `HashMap` program is compiled by trust-cg AND
/// LLVM at -O0 and -O3, run, and the exit codes must match each other and the
/// expected value. A divergence is a miscompile. Because the programs read only
/// `get`/`len`/value sums (order-independent), the sorted-vec backing matches
/// LLVM's SwissTable despite never replicating SipHash.
#[test]
fn hashmap_programs_run_and_match_llvm() {
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
        // The canonical goal program: new + two inserts (distinct keys) + get(hit)
        // + len. get(&3)=30, len=2 -> 32.
        (
            "hm_new_insert_get_len",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(3i64), black_box(30i64)); \
             m.insert(black_box(1i64), black_box(10i64)); \
             let s = m.get(&3).copied().unwrap_or(0) + m.len() as i64; \
             std::process::exit(s as i32); }",
            32,
        ),
        // get MISS returns the unwrap_or default. get(&9) miss -> 0, +len(2)=2.
        (
            "hm_get_miss",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(3i64), black_box(30i64)); \
             m.insert(black_box(1i64), black_box(10i64)); \
             let s = m.get(&9).copied().unwrap_or(0) + m.len() as i64; \
             std::process::exit(s as i32); }",
            2,
        ),
        // insert-overwrite-same-key: the second insert(3, ..) replaces the value
        // and len stays 1. get(&3)=99, len=1 -> 100.
        (
            "hm_overwrite",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(3i64), black_box(30i64)); \
             m.insert(black_box(3i64), black_box(99i64)); \
             let s = m.get(&3).copied().unwrap_or(0) + m.len() as i64; \
             std::process::exit(s as i32); }",
            100,
        ),
        // insert returns the previous value as Option<V>: the second insert(3, 99)
        // returns Some(30). unwrap_or(0) on it -> 30; +len(1) -> 31.
        (
            "hm_insert_returns_old",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(3i64), black_box(30i64)); \
             let old = m.insert(black_box(3i64), black_box(99i64)).unwrap_or(0); \
             std::process::exit((old + m.len() as i64) as i32); }",
            31,
        ),
        // first insert of a key returns None -> unwrap_or(0) = 0; +len(1) = 1.
        (
            "hm_insert_first_none",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let r = m.insert(black_box(7i64), black_box(70i64)).unwrap_or(0); \
             std::process::exit((r + m.len() as i64) as i32); }",
            1,
        ),
        // Sum over values by getting each known key. A loop of inserts forces the
        // backing buffer to grow several times (cap 1 -> 2 -> 4 -> ...). Keys
        // 1..=20, value = key*2; sum of all values via get = 2*(1+..+20)=420;
        // 420 % 251 = 169.
        (
            "hm_grow_sum_get",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut i = 1i64; while i <= 20 { m.insert(black_box(i), black_box(i*2)); i += 1; } \
             let mut s = 0i64; let mut k = 1i64; \
             while k <= 20 { s += m.get(&k).copied().unwrap_or(0); k += 1; } \
             std::process::exit(((s % 251) + (m.len() as i64 - 20)) as i32); }",
            (420 % 251) as i32,
        ),
        // Narrow integer key/value (i32). get(&2)=200, len=2 -> 202.
        (
            "hm_i32_kv",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i32, i32> = HashMap::new(); \
             m.insert(black_box(2i32), black_box(200i32)); \
             m.insert(black_box(5i32), black_box(500i32)); \
             let s = m.get(&2).copied().unwrap_or(0) + m.len() as i32; \
             std::process::exit(s); }",
            202,
        ),
        // Mixed key/value widths (i32 key, i64 value): get(&7)=70, len=2 -> 72.
        // The narrow key is zero/sign-extended into the i64 key lane; the i64
        // value avoids the small-`Option<u8>`-return ABI gap.
        (
            "hm_i32_key_i64_val",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i32, i64> = HashMap::new(); \
             m.insert(black_box(7i32), black_box(70i64)); \
             m.insert(black_box(9i32), black_box(90i64)); \
             let s = m.get(&7).copied().unwrap_or(0) + m.len() as i64; \
             std::process::exit(s as i32); }",
            72,
        ),
        // Unsigned 32-bit key/value: get(&200)=9, len=2 -> 11.
        (
            "hm_u32_kv",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<u32, u32> = HashMap::new(); \
             m.insert(black_box(100u32), black_box(7u32)); \
             m.insert(black_box(200u32), black_box(9u32)); \
             let s = m.get(&200).copied().unwrap_or(0) + m.len() as u32; \
             std::process::exit(s as i32); }",
            11,
        ),
        // Unsigned 64-bit key (large value) round-trips through the i64 lane.
        // get(&9999999999)=123 -> 123.
        (
            "hm_u64_key",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<u64, u64> = HashMap::new(); \
             m.insert(black_box(9999999999u64), black_box(123u64)); \
             let s = m.get(&9999999999).copied().unwrap_or(0); \
             std::process::exit(s as i32); }",
            123,
        ),
        // `with_capacity` yields an empty map (the hint is unobservable). After one
        // insert: get(&4)=40, len=1 -> 41.
        (
            "hm_with_capacity",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::with_capacity(8); \
             m.insert(black_box(4i64), black_box(40i64)); \
             let s = m.get(&4).copied().unwrap_or(0) + m.len() as i64; \
             std::process::exit(s as i32); }",
            41,
        ),
        // `is_empty`: true (10) before any insert, false (0) after; len=1.
        // e0=true -> 10, e1=false -> 0, +len(1) = 11.
        (
            "hm_is_empty",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let e0 = m.is_empty(); m.insert(black_box(1i64), black_box(5i64)); \
             let e1 = m.is_empty(); \
             std::process::exit((e0 as i32) * 10 + (e1 as i32) + m.len() as i32); }",
            11,
        ),
        // Negative i64 keys/values exercise sign-extension into the i64 lane.
        // get(&-5)=-50, get(&-3)=7 -> -43; +100 = 57.
        (
            "hm_negative_keys",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(-5i64), black_box(-50i64)); \
             m.insert(black_box(-3i64), black_box(7i64)); \
             let s = m.get(&-5).copied().unwrap_or(0) + m.get(&-3).copied().unwrap_or(0); \
             std::process::exit((s + 100) as i32); }",
            57,
        ),
        // Many overwrites of one key: len stays 1, the LAST value wins. value=49,
        // +len(1) = 50.
        (
            "hm_many_overwrite",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut i = 0i64; while i < 50 { m.insert(black_box(7i64), black_box(i)); i += 1; } \
             let s = m.get(&7).copied().unwrap_or(0) + m.len() as i64; \
             std::process::exit(s as i32); }",
            50,
        ),
        // Empty map: len() == 0, get miss -> default. 0 + 0 + 5 = 5.
        (
            "hm_empty",
            "use std::collections::HashMap; \
             fn main() { let m: HashMap<i64, i64> = HashMap::new(); \
             let s = m.get(&1).copied().unwrap_or(0) + m.len() as i64 + 5; \
             std::process::exit(s as i32); }",
            5,
        ),
    ];

    for (name, src, expected) in shapes {
        for opt in ["0", "3"] {
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

/// Iteration over a `HashMap` (`.values().sum()`, `for (_, v) in &m`, ...) is
/// NOT intercepted — it goes through the `hashbrown` iterator machinery the
/// backend cannot lower. The bridge must fail CLOSED (no binary, a precise
/// diagnostic), never miscompile. This pins the next `HashMap` step explicitly.
#[test]
fn hashmap_iter_fails_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("iter");

    let src = "use std::collections::HashMap; use std::hint::black_box; \
               fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
               m.insert(black_box(1i64), black_box(10i64)); \
               m.insert(black_box(2i64), black_box(20i64)); \
               let s: i64 = m.values().sum(); std::process::exit(s as i32); }";

    // LLVM compiles + runs it (=30); trust-cg must fail CLOSED.
    let llvm_bin = compile(&dir, "hm_iter_llvm", src, None, "0");
    assert_eq!(run_exit_code(&llvm_bin), 30, "LLVM HashMap values-sum should be 30");

    let (output, bin) = try_compile(&dir, "hm_iter_tcg", src, Some(&dylib), "0");
    assert!(
        !output.status.success() && !bin.exists(),
        "trust-cg unexpectedly compiled the HashMap iteration; if it now lowers, \
         promote this into the run+match set"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A non-integer key (`HashMap<String, _>`) is NOT intercepted — the flat
/// `[key:i64|value:i64]` backing store only models integer lanes (<= 64 bits),
/// so a `String` key (or any non-integer / wider-than-64-bit `K`/`V`) must fail
/// CLOSED rather than misencode the key. This pins the soundness boundary.
#[test]
fn hashmap_non_integer_key_fails_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("strkey");

    let src = "use std::collections::HashMap; \
               fn main() { let mut m: HashMap<String, i64> = HashMap::new(); \
               m.insert(\"a\".to_string(), 5i64); \
               std::process::exit(m.len() as i32); }";

    // LLVM compiles + runs it (len = 1); trust-cg must fail CLOSED.
    let llvm_bin = compile(&dir, "hm_strkey_llvm", src, None, "0");
    assert_eq!(run_exit_code(&llvm_bin), 1, "LLVM HashMap<String,_> len should be 1");

    let (output, bin) = try_compile(&dir, "hm_strkey_tcg", src, Some(&dylib), "0");
    assert!(
        !output.status.success() && !bin.exists(),
        "trust-cg unexpectedly compiled HashMap<String, _>; a non-integer key must fail closed"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
