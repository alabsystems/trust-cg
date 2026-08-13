// Integration test: two -O3-inlining completeness gaps closed in the bridge —
// `Vec::with_capacity` and `HashMap::entry()` — compiled for x86_64 via the
// rustc_codegen_trust_cg bridge at BOTH -O0 AND -O3, COMPILED, LINKED, RUN, and
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS — two O3-inlining gaps that previously failed CLOSED at -O3 now
// MATCH LLVM:
//
//   * `Vec::with_capacity(n)` @ -O3. rustc inlines `with_capacity` into a real
//     `RawVecInner::try_allocate_in(n, ..)` allocator call returning
//     `Result<RawVecInner, TryReserveError>`, a discriminant-switch, an Ok-arm
//     unwrap + `assume`-bounds scratch, and finally the SAME empty-`Vec`
//     aggregate (`Vec { buf, len: const 0 }`) the inlined `Vec::new()` builds.
//     The capacity is unobservable (the slot reserves a 1-element buffer and
//     `push` grows unconditionally), so the whole allocator chain is DEAD
//     scaffolding around that empty-`Vec` aggregate. The bridge recognizes it
//     (`compute_vec_with_capacity_chain`): dead intermediates skipped, the
//     `Result` switch redirected to its always-Ok arm, the `handle_error` Err arm
//     trapped, and the empty-`Vec` aggregate routed through the slot model.
//
//   * `HashMap::entry(k)` @ -O3. rustc inlines `entry()` into the inner
//     `rustc_entry()` (returns a `RustcEntry::{Occupied,Vacant}` enum the bridge
//     records as a pending `{slot,key}`), then a discriminant-switch DIAMOND whose
//     BOTH arms re-wrap that inner entry into the public
//     `Entry::{Occupied,Vacant}(..)` before the consuming `or_insert*`. The bridge
//     propagates the recorded entry through the re-wrap chain (a constant Vacant
//     discriminant keeps the switch well-formed; both arms reach the same
//     find-or-insert), so the `or_insert*` performs the SAME get-or-insert the -O0
//     path uses (`propagate_map_entry_pending`).
//
// Each program is compiled with BOTH backends at each gated opt level and run; the
// trust-cg exit code must equal the LLVM exit code (and the expected value). A
// wrong capacity behavior / wrong count is a miscompile, so equal exit codes are
// the differential we assert. The few -O0-only pins are pre-existing UNRELATED
// gaps (the -O0 `Vec::deref` iterator path; -O0 `HashMap` index/`unwrap` linking),
// not the gaps under test.

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
    assert!(status.success(), "cargo build failed; cannot run O3-gaps test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m101_{stem}_{}", std::process::id()));
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
    let llvm_bin = compile(dir, &format!("{name}_o{opt}_llvm"), src, None, opt);
    let tcg_bin = compile(dir, &format!("{name}_o{opt}_tcg"), src, Some(dylib), opt);
    let llvm_exit = run_exit_code(&llvm_bin);
    let tcg_exit = run_exit_code(&tcg_bin);
    assert_eq!(
        llvm_exit, expected,
        "LLVM exit for `{name}` (-O{opt}) is {llvm_exit}, expected {expected}"
    );
    assert_eq!(
        tcg_exit, llvm_exit,
        "trust-cg exit for `{name}` (-O{opt}) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
    );
}

/// `Vec::with_capacity` at -O0 AND -O3: each pushes PAST the requested capacity
/// (forcing a grow) and reads back by index / len, so a wrong capacity behavior or
/// dropped element diverges from LLVM. The capacity argument is unobservable, so
/// the values must match `Vec::new` exactly.
#[test]
fn vec_with_capacity_o3_matches() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("wc");

    // (name, source, expected). Gated at O0 AND O3.
    let shapes: &[(&str, &str, i32)] = &[
        (
            "i64_push_past",
            "fn main() { let mut v: Vec<i64> = Vec::with_capacity(4); \
             let mut i = 1i64; while i <= 10 { v.push(i); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } std::process::exit(s as i32); }",
            55,
        ),
        (
            "i64_zero_cap",
            "fn main() { let mut v: Vec<i64> = Vec::with_capacity(0); \
             v.push(7); v.push(8); std::process::exit((v[0] + v[1]) as i32); }",
            15,
        ),
        (
            "i32_last",
            "fn main() { let mut v: Vec<i32> = Vec::with_capacity(2); let mut i = 0i32; \
             while i < 13 { v.push((i * i) % 17); i += 1; } \
             let last = v[v.len() - 1]; std::process::exit(last); }",
            (12 * 12) % 17,
        ),
        (
            "u8_sum",
            "fn main() { let mut v: Vec<u8> = Vec::with_capacity(8); let mut i = 0u8; \
             while i < 37 { v.push(i); i += 1; } let mut s = 0u32; let mut k = 0usize; \
             while k < v.len() { s += v[k] as u32; k += 1; } \
             std::process::exit((s % 200) as i32); }",
            ((0u32..37).sum::<u32>() % 200) as i32,
        ),
        (
            "len_only",
            "fn build() -> i64 { let v: Vec<i64> = Vec::with_capacity(10); v.len() as i64 } \
             fn main() { std::process::exit((build() + 9) as i32); }",
            9,
        ),
        // `with_capacity` behind a user `&mut Vec` helper (the inlined push inside
        // the helper is intercepted); construction still goes through the chain.
        (
            "mutref_helper",
            "fn fill(v: &mut Vec<i64>, n: i64) { let mut i = 1i64; \
             while i <= n { v.push(i); i += 1; } } \
             fn main() { let mut v: Vec<i64> = Vec::with_capacity(3); fill(&mut v, 10); \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } std::process::exit(s as i32); }",
            55,
        ),
    ];
    for (name, src, expected) in shapes {
        for opt in ["0", "3"] {
            assert_match(&dir, &dylib, name, src, *expected, opt);
        }
    }

    // `with_capacity` + `iter().sum()`: the `Vec::deref`-into-slice iterator path
    // is now handled and MATCHES LLVM at BOTH -O0 and -O3 (verified sound over an
    // adversarial vec-iter corpus: empty / negatives / rev+enumerate / nested /
    // count / max / map).
    let iter_src = "fn main() { let mut v: Vec<i64> = Vec::with_capacity(16); \
                    for i in 0..50i64 { v.push(i); } let s: i64 = v.iter().sum(); \
                    std::process::exit((s % 256) as i32); }";
    for opt in ["0", "3"] {
        assert_match(
            &dir,
            &dylib,
            "wc_iter_sum",
            iter_src,
            ((0i64..50).sum::<i64>() % 256) as i32,
            opt,
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// `HashMap::entry(k).or_insert*()` at -O0 AND -O3. The accessor side avoids the
/// pre-existing -O0 `HashMap` index/`unwrap`-linking gap by reading values through
/// a `match m.get(&k)` (the get path is intercepted at both opt levels). A wrong
/// count / wrong len diverges from LLVM.
#[test]
fn hashmap_entry_o3_matches() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("hm");

    let shapes: &[(&str, &str, i32)] = &[
        // Word-count via `or_insert(0)`: k = i%3 over 0..10 -> {0:4, 1:3, 2:3}.
        // len=3, count(0)=4 -> 3*10 + 4 = 34.
        (
            "or_insert_count",
            "use std::collections::HashMap; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut i = 0i64; while i < 10 { \
             *m.entry(std::hint::black_box(i % 3)).or_insert(0) += 1; i += 1; } \
             let n = m.len() as i64; \
             let c0 = match m.get(&0) { Some(v) => *v, None => -1 }; \
             std::process::exit((n * 10 + c0) as i32); }",
            34,
        ),
        // `or_default()`: V::default()=0 then += 1. k=i%2 over 0..7 -> {0:4, 1:3}.
        (
            "or_default_count",
            "use std::collections::HashMap; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut i = 0i64; while i < 7 { \
             *m.entry(std::hint::black_box(i % 2)).or_default() += 1; i += 1; } \
             let a = match m.get(&0) { Some(v) => *v, None => 0 }; \
             let b = match m.get(&1) { Some(v) => *v, None => 0 }; \
             std::process::exit((a * 10 + b) as i32); }",
            43,
        ),
        // `or_insert_with(|| CONST)`: a side-effect-free closure folded to 100; on
        // the first MISS the value is 100 then += 1 -> 101, subsequent HITs += 1.
        (
            "or_insert_with_const",
            "use std::collections::HashMap; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut i = 0i64; while i < 5 { \
             *m.entry(std::hint::black_box(0)).or_insert_with(|| 100) += 1; i += 1; } \
             let a = match m.get(&0) { Some(v) => *v, None => 0 }; \
             std::process::exit(a as i32); }",
            105,
        ),
        // i32 keys/values through the entry path. k=i%4 over 0..12 -> {0..3: 3 each}.
        (
            "i32_count",
            "use std::collections::HashMap; \
             fn main() { let mut m: HashMap<i32,i32> = HashMap::new(); \
             let mut i = 0i32; while i < 12 { \
             *m.entry(std::hint::black_box(i % 4)).or_insert(0) += 1; i += 1; } \
             let n = m.len() as i32; \
             let c = match m.get(&0) { Some(v) => *v, None => -1 }; \
             std::process::exit(n * 10 + c); }",
            43,
        ),
        // A bare un-consumed `entry(k)` mutates nothing (std semantics): len stays 1.
        (
            "bare_entry_noop",
            "use std::collections::HashMap; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             m.insert(1, 1); m.entry(std::hint::black_box(2)); \
             std::process::exit(m.len() as i32); }",
            1,
        ),
        // entry-driven growth: 8 distinct keys force backing-buffer reallocs.
        (
            "entry_grow",
            "use std::collections::HashMap; \
             fn main() { let mut m: HashMap<i64,i64> = HashMap::new(); \
             let mut k = 0i64; while k < 8 { \
             *m.entry(std::hint::black_box(k)).or_insert(0) += k * 3; k += 1; } \
             let mut s = 0i64; let mut j = 0i64; while j < 8 { \
             s += match m.get(&j) { Some(v) => *v, None => 0 }; j += 1; } \
             std::process::exit((s + m.len() as i64) as i32); }",
            92,
        ),
    ];
    for (name, src, expected) in shapes {
        for opt in ["0", "3"] {
            assert_match(&dir, &dylib, name, src, *expected, opt);
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
