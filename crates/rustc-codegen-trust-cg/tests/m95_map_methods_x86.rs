#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: `HashMap`/`BTreeMap` method-coverage extension (integer
// keys/values) — `entry().or_insert*()`, `contains_key`, `get_mut`, `remove` —
// compiled for x86_64 via the rustc_codegen_trust_cg bridge, COMPILED, LINKED,
// and RUN, with exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS — the word-count idiom `*m.entry(k).or_insert(0) += 1` RUNS on
// x86_64 via trust-cg for integer keys/values, plus `or_insert_with(|| CONST)`,
// `or_default()`, `contains_key`, `get_mut`, and `remove`.
//
// HOW `entry` IS LOWERED. std's `entry(k)` returns an `Entry<K, V>` enum that
// is consumed by `or_insert*`. The bridge lowers `entry(k)` to NOTHING but a
// compile-time record (the map's `{ptr,cap,len}` slot address + the extended
// key lane, keyed by the `Entry`-typed local); the consuming `or_insert*` call
// then performs the actual find-or-insert via the `__trustcg_btm_entry`
// runtime helper (on a hit the existing value is kept and the default
// discarded; on a miss `(key, default)` is appended) and binds its `&mut V`
// result to the returned value-lane ADDRESS inside the map's heap buffer — so
// the read-modify-write `*e += 1` lands in the real backing store. Deferring
// the helper call to the consumer keeps a bare un-consumed `m.entry(k);` a
// correct no-op, and any OTHER use of the `Entry` value (a `match` on it)
// finds no binding and FAILS CLOSED — it can never silently miscompile.
//
// OPT-LEVEL COVERAGE. All four method families work at -O0 AND -O3 for
// `BTreeMap` (its method calls survive the -O3 inliner). For `HashMap`,
// `contains_key`/`get_mut`/`remove` work at -O0 and -O3 (the inliner stops at
// the inner `hashbrown` methods the interception also recognizes). `entry()` at
// -O3 is inlined into a `rustc_entry` + `Entry`-enum-rewrap DIAMOND (the
// `RustcEntry` is discriminant-switched and rebuilt variant by variant); the
// bridge now RECOGNIZES that diamond — it propagates the recorded entry through
// the re-wrap to the same get-or-insert the -O0 path uses (see
// `propagate_map_entry_pending`) — so HashMap `entry` now works at -O3 too.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A wrong map result
// is a miscompile, so equal exit codes are the differential we assert.

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
    assert!(status.success(), "cargo build failed; cannot run map test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m95_{stem}_{}", std::process::id()));
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

fn assert_match(dir: &Path, dylib: &Path, name: &str, src: &str, expected: i32, opt: &str) {
    let suffix = format!("o{opt}");
    let llvm_bin = compile(dir, &format!("{name}_{suffix}_llvm"), src, None, opt);
    let tcg_bin = compile(dir, &format!("{name}_{suffix}_tcg"), src, Some(dylib), opt);
    let llvm_exit = run_exit_code(&llvm_bin);
    let tcg_exit = run_exit_code(&tcg_bin);
    assert_eq!(
        llvm_exit, expected,
        "LLVM backend exit code for `{name}` (-Copt-level={opt}) is {llvm_exit}, \
         expected {expected}"
    );
    assert_eq!(
        tcg_exit, llvm_exit,
        "trust-cg exit code for `{name}` (-Copt-level={opt}) is {tcg_exit}, LLVM is \
         {llvm_exit} (must match)"
    );
}

fn assert_fails_closed(dir: &Path, dylib: &Path, name: &str, src: &str, expected: i32, opt: &str) {
    let llvm_bin = compile(dir, &format!("{name}_o{opt}_llvm"), src, None, opt);
    assert_eq!(
        run_exit_code(&llvm_bin),
        expected,
        "LLVM exit for `{name}` at -O{opt}"
    );
    let (output, bin) = try_compile(dir, &format!("{name}_o{opt}_tcg"), src, Some(dylib), opt);
    assert!(
        !output.status.success() && !bin.exists(),
        "trust-cg unexpectedly compiled `{name}` at -O{opt}; if it now lowers correctly, \
         promote it into the run+match set"
    );
}

/// The full differential: every program is compiled by trust-cg AND LLVM at
/// each gated opt level, run, and the exit codes must match each other and the
/// expected value. A divergence is a miscompile.
#[test]
fn map_method_programs_run_and_match_llvm() {
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

    // (name, source, expected exit code, gated opt levels).
    // `BTreeMap` method calls survive the -O3 inliner, so every BTreeMap shape is
    // gated at O0+O3. `HashMap` `entry()` at -O3 inlines into the inner
    // `rustc_entry` + a discriminant-switch that rewraps the std `Entry` enum; the
    // bridge now recognizes that diamond (propagating the recorded entry through the
    // re-wrap to the same get-or-insert the -O0 path uses; see
    // `propagate_map_entry_pending`), so HashMap entry shapes are ALSO gated O0+O3.
    let o0_o3: &[&str] = &["0", "3"];
    let shapes: &[(&str, &str, i32, &[&str])] = &[
        // THE PRIZE: the word-count idiom over a fixed key sequence. Counts:
        // 3 -> 3, 1 -> 2, 7 -> 1; s = 3*100 + 2*10 + 3(len) = 323; 323 % 256 = 67.
        (
            "wordcount_hashmap",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let xs = [3i64, 1, 3, 7, 1, 3]; \
             let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut i = 0usize; while i < 6 { \
             *m.entry(black_box(xs[i])).or_insert(0) += 1; i += 1; } \
             let s = m.get(&3).copied().unwrap_or(0) * 100 \
                 + m.get(&1).copied().unwrap_or(0) * 10 + m.len() as i64; \
             std::process::exit(s as i32); }",
            67,
            o0_o3,
        ),
        (
            "wordcount_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let xs = [3i64, 1, 3, 7, 1, 3]; \
             let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             let mut i = 0usize; while i < 6 { \
             *m.entry(black_box(xs[i])).or_insert(0) += 1; i += 1; } \
             let s = m.get(&3).copied().unwrap_or(0) * 100 \
                 + m.get(&1).copied().unwrap_or(0) * 10 + m.len() as i64; \
             std::process::exit(s as i32); }",
            67,
            o0_o3,
        ),
        // or_insert on a HIT discards the default and returns the live value
        // lane; on a MISS inserts it. 40+2 (miss), +1 (hit, keeps 42+1=43);
        // or_default inserts V::default()=0 then += 7. 43 + 7 + 2(len) = 52.
        (
            "or_insert_with_or_default_hashmap",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             *m.entry(black_box(5)).or_insert_with(|| 40) += 2; \
             *m.entry(black_box(5)).or_insert_with(|| 99) += 1; \
             *m.entry(black_box(6)).or_default() += 7; \
             let s = m.get(&5).copied().unwrap_or(0) + m.get(&6).copied().unwrap_or(0) \
                 + m.len() as i64; \
             std::process::exit(s as i32); }",
            52,
            o0_o3,
        ),
        (
            "or_insert_with_or_default_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             *m.entry(black_box(5)).or_insert_with(|| 40) += 2; \
             *m.entry(black_box(5)).or_insert_with(|| 99) += 1; \
             *m.entry(black_box(6)).or_default() += 7; \
             let s = m.get(&5).copied().unwrap_or(0) + m.get(&6).copied().unwrap_or(0) \
                 + m.len() as i64; \
             std::process::exit(s as i32); }",
            52,
            o0_o3,
        ),
        // A bare un-consumed `entry(k)` mutates NOTHING (std semantics); len 0.
        (
            "entry_unconsumed_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             m.entry(black_box(5)); \
             std::process::exit(m.len() as i32); }",
            0,
            o0_o3,
        ),
        // Conditional consumption: the `Entry` may be or_inserted in only one
        // branch. 10 + (1+1) = 12.
        (
            "entry_conditional_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             let c = black_box(1i64) == 1; \
             let e = m.entry(black_box(4)); \
             if c { e.or_insert(10); } \
             let e2 = m.entry(black_box(8)); \
             if c { *e2.or_insert(1) += 1; } else { m.insert(black_box(8), black_box(50)); } \
             std::process::exit((m.get(&4).copied().unwrap_or(0) \
                 + m.get(&8).copied().unwrap_or(0)) as i32); }",
            12,
            o0_o3,
        ),
        // contains_key hit + miss, both maps. 1*10 + 0 + 2(len) = 12.
        (
            "contains_key_hashmap",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(3), black_box(30)); m.insert(black_box(9), black_box(90)); \
             let hit = m.contains_key(&3) as i32; let miss = m.contains_key(&4) as i32; \
             std::process::exit(hit * 10 + miss + m.len() as i32); }",
            12,
            o0_o3,
        ),
        (
            "contains_key_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             m.insert(black_box(3), black_box(30)); m.insert(black_box(9), black_box(90)); \
             let hit = m.contains_key(&3) as i32; let miss = m.contains_key(&4) as i32; \
             std::process::exit(hit * 10 + miss + m.len() as i32); }",
            12,
            o0_o3,
        ),
        // get_mut: mutate through the Option<&mut V>, then read back; a miss
        // arm must not fire. 30 + 12 = 42.
        (
            "get_mut_hashmap",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(3), black_box(30)); \
             if let Some(v) = m.get_mut(&3) { *v += 12; } \
             if let Some(v) = m.get_mut(&77) { *v += 1000; } \
             std::process::exit(m.get(&3).copied().unwrap_or(0) as i32); }",
            42,
            o0_o3,
        ),
        (
            "get_mut_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             m.insert(black_box(3), black_box(30)); \
             if let Some(v) = m.get_mut(&3) { *v += 12; } \
             if let Some(v) = m.get_mut(&77) { *v += 1000; } \
             std::process::exit(m.get(&3).copied().unwrap_or(0) as i32); }",
            42,
            o0_o3,
        ),
        // remove of a MIDDLE entry (exercises the shift-delete), an absent key,
        // len decrement, and a survivor's value. 20 + 5 + 2 + 30 = 57.
        (
            "remove_hashmap",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(black_box(1), black_box(10)); m.insert(black_box(2), black_box(20)); \
             m.insert(black_box(3), black_box(30)); \
             let r1 = m.remove(&2).unwrap_or(0); let r2 = m.remove(&9).unwrap_or(5); \
             let s = r1 + r2 + m.len() as i64 + m.get(&3).copied().unwrap_or(0); \
             std::process::exit(s as i32); }",
            57,
            o0_o3,
        ),
        (
            "remove_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             m.insert(black_box(1), black_box(10)); m.insert(black_box(2), black_box(20)); \
             m.insert(black_box(3), black_box(30)); \
             let r1 = m.remove(&2).unwrap_or(0); let r2 = m.remove(&9).unwrap_or(5); \
             let s = r1 + r2 + m.len() as i64 + m.get(&3).copied().unwrap_or(0); \
             std::process::exit(s as i32); }",
            57,
            o0_o3,
        ),
        // Narrow / unsigned / negative K,V widths through every new method.
        // a: -1-4 = -5 (i32, negative key); b: 3+1, hit keeps 4+1=5 (u32);
        // c: remove(-3) = 7 (i64 negative key); -5+5+7+50 = 57.
        (
            "widths_mixed",
            "use std::collections::HashMap; use std::collections::BTreeMap; \
             use std::hint::black_box; \
             fn main() { let mut a: HashMap<i32,i32> = HashMap::new(); \
             *a.entry(black_box(-7i32)).or_insert(-1) -= 4; \
             let mut b: BTreeMap<u32,u32> = BTreeMap::new(); \
             *b.entry(black_box(9u32)).or_insert(3) += 1; \
             *b.entry(black_box(9u32)).or_insert(100) += 1; \
             let mut c: BTreeMap<i64,i64> = BTreeMap::new(); \
             c.insert(black_box(-3), black_box(7)); \
             let r = c.remove(&-3).unwrap_or(0); \
             let s = a.get(&-7).copied().unwrap_or(0) as i64 \
                 + b.get(&9).copied().unwrap_or(0) as i64 + r; \
             std::process::exit((s + 50) as i32); }",
            57,
            o0_o3,
        ),
        // Interleaved entry-increment / insert-overwrite / remove in one loop,
        // then a get+contains_key fold. (Result computed by the LLVM oracle.)
        (
            "interleave_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             let mut i = 0i64; while i < 12 { let k = black_box(i % 5); \
             *m.entry(k).or_insert(0) += i; \
             if i % 3 == 0 { m.insert(k, black_box(i)); } \
             if i % 4 == 0 { let _ = m.remove(&black_box((i + 1) % 5)); } \
             i += 1; } \
             let mut s = 0i64; let mut k = 0i64; while k < 5 { \
             s = s * 7 + m.get(&k).copied().unwrap_or(-1) + m.contains_key(&k) as i64; \
             k += 1; } \
             std::process::exit(((s % 251 + 251) % 251) as i32); }",
            245,
            o0_o3,
        ),
        (
            "interleave_hashmap",
            "use std::collections::HashMap; use std::hint::black_box; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut i = 0i64; while i < 12 { let k = black_box(i % 5); \
             *m.entry(k).or_insert(0) += i; \
             if i % 3 == 0 { m.insert(k, black_box(i)); } \
             if i % 4 == 0 { let _ = m.remove(&black_box((i + 1) % 5)); } \
             i += 1; } \
             let mut s = 0i64; let mut k = 0i64; while k < 5 { \
             s = s * 7 + m.get(&k).copied().unwrap_or(-1) + m.contains_key(&k) as i64; \
             k += 1; } \
             std::process::exit(((s % 251 + 251) % 251) as i32); }",
            245,
            o0_o3,
        ),
        // entry-driven GROWTH: 8 distinct keys force the backing buffer to grow
        // through the entry helper's realloc path (cap 1 -> 2 -> 4 -> 8).
        // Values k*3 summed via get: 3*(0+..+7) = 84; + len 8 = 92.
        (
            "entry_grow_btreemap",
            "use std::collections::BTreeMap; use std::hint::black_box; \
             fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
             let mut k = 0i64; while k < 8 { \
             *m.entry(black_box(k)).or_insert(0) += k * 3; k += 1; } \
             let mut s = 0i64; let mut j = 0i64; while j < 8 { \
             s += m.get(&j).copied().unwrap_or(0); j += 1; } \
             std::process::exit((s + m.len() as i64) as i32); }",
            92,
            o0_o3,
        ),
    ];

    for (name, src, expected, opts) in shapes {
        for opt in *opts {
            assert_match(&dir, &dylib, name, src, *expected, opt);
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// `HashMap::entry` at -O3 inlines into the inner `rustc_entry` call plus a
/// discriminant-switch that rebuilds the std `Entry` enum variant by variant
/// (`_d = discriminant(rustc_entry); switchInt(_d) -> [Occupied, Vacant]`, both
/// arms re-wrapping the inner entry into `Entry::{Occupied,Vacant}(..)` before the
/// consuming `or_insert*`). The bridge now recognizes that diamond: it propagates
/// the recorded `{slot,key}` entry through the re-wrap chain (a constant Vacant
/// discriminant keeps the switch well-formed; BOTH arms reach the same
/// find-or-insert), so the consuming `or_insert*` performs the SAME get-or-insert
/// the -O0 path does (see `propagate_map_entry_pending`). So a `HashMap` `entry`
/// idiom now compiles and MATCHES LLVM at -O3 as it does at -O0.
#[test]
fn hashmap_entry_o3_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("entry_o3");

    let src = "use std::collections::HashMap; use std::hint::black_box; \
               fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
               *m.entry(black_box(3)).or_insert(0) += 1; \
               std::process::exit(m.len() as i32); }";
    // -O3 and -O0 both compile + match LLVM (= 1: one entry inserted).
    assert_match(&dir, &dylib, "hm_entry", src, 1, "3");
    assert_match(&dir, &dylib, "hm_entry", src, 1, "0");

    let _ = std::fs::remove_dir_all(&dir);
}

/// An `Entry` that ESCAPES its `or_insert*` consumer (here: `match`ed on) is
/// not modeled — the bridge records the entry hand-off but never materializes
/// the `Entry` enum value, so the `match`'s discriminant read finds no binding
/// and must FAIL CLOSED, never guess.
#[test]
fn escaping_entry_fails_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("escape");

    let src = "use std::collections::BTreeMap; use std::collections::btree_map::Entry; \
               use std::hint::black_box; \
               fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
               m.insert(black_box(3), black_box(30)); \
               let e = m.entry(black_box(3)); \
               let r = match e { Entry::Occupied(o) => *o.get(), Entry::Vacant(_) => -1 }; \
               std::process::exit(r as i32); }";
    for opt in ["0", "3"] {
        assert_fails_closed(&dir, &dylib, "btm_escape", src, 30, opt);
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// `or_insert_with` with a CAPTURING (or otherwise non-trivial) closure cannot
/// be const-folded; calling it eagerly could change observable behavior, so
/// only the trivial `|| CONST` shape is lowered. A capturing closure must FAIL
/// CLOSED.
#[test]
fn capturing_or_insert_with_fails_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("capture");

    let src = "use std::collections::BTreeMap; use std::hint::black_box; \
               fn main() { let mut m: BTreeMap<i64,i64> = BTreeMap::new(); \
               let d = black_box(41i64); \
               *m.entry(black_box(5)).or_insert_with(|| d + 1) += 0; \
               std::process::exit(m.get(&5).copied().unwrap_or(0) as i32); }";
    for opt in ["0", "3"] {
        assert_fails_closed(&dir, &dylib, "btm_capture", src, 42, opt);
    }

    let _ = std::fs::remove_dir_all(&dir);
}
