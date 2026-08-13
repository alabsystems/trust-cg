// Integration test: SLICE / ARRAY INDEXING — element reads `s[i]`, element
// writes `s[i] = v`, subslicing `&s[a..b]`, an in-place index-swap algorithm,
// and out-of-bounds bounds-check behavior — compiled for x86_64 via the
// rustc_codegen_trust_cg bridge, COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend at the SAME optimization level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The keystone covered here is RUNTIME indexing through the memory model:
//   * `arr[i]` for a fixed array with a RUNTIME index (the projection walker
//     computes `slot + i*stride` and loads the element);
//   * summing a slice by an index loop (`for i in 0..s.len() { acc += s[i] }`);
//   * `s[i] = v` into a `&mut [i64]` whose change is OBSERVED by the caller
//     after the function returns (the write goes through the mutable backing,
//     not a copy);
//   * an in-place algorithm (reverse a `&mut [i64]` by index swaps) whose whole
//     result is compared to LLVM;
//   * subslicing `&arr[1..4]` and summing it;
//   * a deliberately OUT-OF-BOUNDS index, which must ABORT (a fatal signal, not
//     a normal exit, and never the in-bounds success value) — matching LLVM's
//     `-Cpanic=abort` behavior of NOT continuing past the bounds violation.
//
// Each value-returning program is compiled with BOTH backends and run; the
// trust-cg exit code must equal the LLVM exit code (and the expected value). A
// wrong element address, length, write-through, or skipped bounds check shows up
// as a mismatched exit code (or a continued-past-OOB success).

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const OPT_LEVEL: &str = "-Copt-level=3";

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
    assert!(status.success(), "cargo build failed; cannot run slice-index test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_six_{stem}_{}", std::process::id()));
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
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", OPT_LEVEL])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if output.status.success() {
        Ok(bin)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    match try_compile(dir, name, src, backend) {
        Ok(bin) => bin,
        Err(stderr) => panic!(
            "compile of `{name}` failed ({} backend). stderr: <<<{stderr}>>>",
            if backend.is_some() { "trust-cg" } else { "llvm" },
        ),
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

/// Run a binary and report (normal_exit_code, killed_by_signal). Exactly one of
/// the two carries information: a process that exits normally has `Some(code)`
/// and `false`; a process killed by a signal (a trap / abort) has `None` and
/// `true`.
fn run_status(bin: &Path) -> (Option<i32>, bool) {
    let status = Command::new(bin).output().expect("run binary").status;
    (status.code(), status.code().is_none())
}

/// The differential for value-returning index programs: each `fn main` is
/// compiled by trust-cg AND LLVM, run, and the exit codes must match each other
/// and the expected value.
#[test]
fn slice_index_runs_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("cases");

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // 1. A fixed array indexed by a RUNTIME index resolved from a
        //    non-inlinable helper, so the index is a genuine runtime value (not a
        //    constant the compiler folds). `arr[idx()]` -> slot + idx*8 load.
        //    arr = [10,20,30,40,50]; idx = 3 -> 40.
        (
            "array_runtime_index",
            "#[inline(never)] fn idx() -> usize { 3 } \
             fn main(){ let a: [i64; 5] = [10,20,30,40,50]; \
                 std::process::exit((a[idx()] % 256) as i32); }",
            40,
        ),
        // 2. Sum a fixed array by an index loop `for i in 0..N { acc += a[i] }`.
        //    Every read is a runtime `a[i]`. 1+..+10 = 55.
        (
            "array_index_sum",
            "fn main(){ let a: [i64; 10] = [1,2,3,4,5,6,7,8,9,10]; \
                 let mut acc = 0i64; \
                 for i in 0..a.len() { acc += a[i]; } \
                 std::process::exit((acc % 256) as i32); }",
            55,
        ),
        // 3. Write `s[i] = v` into a `&mut [i64]` THROUGH a real (non-inlined)
        //    function boundary, then OBSERVE the change after the call. The write
        //    must go through the mutable backing, not a copy. set s[0]=7, s[2]=9
        //    in `a=[1,2,3,4]`, then read a[0]+a[2] = 16.
        (
            "slice_mut_write_observed",
            "#[inline(never)] fn fill(s: &mut [i64]) { s[0] = 7; s[2] = 9; } \
             fn main(){ let mut a: [i64; 4] = [1,2,3,4]; \
                 fill(&mut a); \
                 std::process::exit(((a[0] + a[2]) % 256) as i32); }",
            16,
        ),
        // 4. An in-place algorithm: reverse a `&mut [i64]` by index swaps, then
        //    sum `i * a[i]` so the whole reordered result (not just one element)
        //    is compared to LLVM. a = [1,2,3,4,5] -> [5,4,3,2,1];
        //    sum i*a[i] = 0*5+1*4+2*3+3*2+4*1 = 4+6+6+4 = 20.
        (
            "in_place_reverse",
            "#[inline(never)] fn reverse(s: &mut [i64]) { \
                 let n = s.len(); let mut i = 0usize; \
                 while i < n / 2 { let t = s[i]; s[i] = s[n-1-i]; s[n-1-i] = t; i += 1; } } \
             fn main(){ let mut a: [i64; 5] = [1,2,3,4,5]; \
                 reverse(&mut a); \
                 let mut acc = 0i64; \
                 for i in 0..a.len() { acc += (i as i64) * a[i]; } \
                 std::process::exit((acc % 256) as i32); }",
            20,
        ),
        // 5. An in-place selection sort of a small array (a real algorithm doing
        //    reads, runtime-indexed comparisons, and swaps), then read the
        //    minimum (now at index 0). [5,3,8,1,9,2] sorted -> 1.
        (
            "selection_sort_min",
            "#[inline(never)] fn sort(s: &mut [i64]) { \
                 let n = s.len(); let mut i = 0usize; \
                 while i < n { \
                     let mut m = i; let mut j = i + 1; \
                     while j < n { if s[j] < s[m] { m = j; } j += 1; } \
                     let t = s[i]; s[i] = s[m]; s[m] = t; \
                     i += 1; } } \
             fn main(){ let mut a: [i64; 6] = [5,3,8,1,9,2]; \
                 sort(&mut a); \
                 std::process::exit((a[0] % 256) as i32); }",
            1,
        ),
        // 6. Subslice `&arr[1..4]` summed: a `{ data + 1*8, 3 }` subslice pair,
        //    iterated by index. a[1]+a[2]+a[3] = 20+30+40 = 90.
        (
            "subslice_sum",
            "#[inline(never)] fn sub_and_sum(a: &[i64]) -> i64 { \
                 let s = &a[1..4]; \
                 let mut t = 0i64; let mut i = 0usize; \
                 while i < s.len() { t += s[i]; i += 1; } t } \
             fn main(){ let a: [i64; 6] = [10,20,30,40,50,60]; \
                 std::process::exit((sub_and_sum(&a) % 256) as i32); }",
            90,
        ),
        // 7. A `&mut` bounded-range subslice that is element-WRITTEN through, and
        //    the change observed by the caller: `&mut s[1..4]` is a
        //    `{ data + 1*8, 3 }` mutable subslice; `mid[i] += 100` writes through
        //    the original backing. a=[10,20,30,40,50,60] -> elements 1..4 each
        //    +100 -> [10,120,130,140,50,60]; sum = 510 -> 510 % 256 = 254.
        (
            "subslice_mut_write_observed",
            "#[inline(never)] fn bump(s: &mut [i64]) { \
                 let mid = &mut s[1..4]; \
                 let mut i = 0usize; \
                 while i < mid.len() { mid[i] += 100; i += 1; } } \
             fn main(){ let mut a: [i64; 6] = [10,20,30,40,50,60]; \
                 bump(&mut a); \
                 let mut acc = 0i64; let mut i = 0usize; \
                 while i < 6 { acc += a[i]; i += 1; } \
                 std::process::exit((acc % 256) as i32); }",
            254,
        ),
        // 8. A full slice `&a[..]` taken over a LOCAL ARRAY (not a slice parameter),
        //    bound to a local, then indexed by a runtime value + `.len()`. This forces
        //    the local array to be materialized in a memory slot so the slice's
        //    `{ data, len }` data pointer is a real address (the source-array
        //    materialization path). a=[10,20,30,40]; s[k()=2] + len(4) = 30 + 4 = 34.
        (
            "local_array_full_slice_read",
            "#[inline(never)] fn k() -> usize { 2 } \
             fn main(){ let a: [i64; 4] = [10,20,30,40]; \
                 let s = &a[..]; \
                 std::process::exit(((s[k()] + s.len() as i64) % 256) as i32); }",
            34,
        ),
        // 9. A `&mut a[..]` full mutable slice over a LOCAL ARRAY, element-written at a
        //    runtime index, the change observed after the borrow ends. a=[10,20,30,40];
        //    s[k()=1]=99 -> a[0]+a[1] = 10 + 99 = 109.
        (
            "local_array_full_slice_mut_write",
            "#[inline(never)] fn k() -> usize { 1 } \
             fn main(){ let mut a: [i64; 4] = [10,20,30,40]; \
                 { let s = &mut a[..]; s[k()] = 99; } \
                 std::process::exit(((a[0] + a[1]) % 256) as i32); }",
            109,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib));
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM backend exit code for `{name}` is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for `{name}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// A deliberately OUT-OF-BOUNDS index must ABORT — i.e. the bounds check rustc
/// inserts before the index is lowered to a real conditional branch to a trap,
/// so the program does NOT continue to the in-bounds success path (which would
/// be a miscompile of a panicking program). Under `-Cpanic=abort` LLVM kills the
/// process with a fatal signal (SIGABRT); the trust-cg trap kills it with a
/// fatal signal too (the bridge's trap convention). We require:
///   * BOTH backends are killed by a signal (neither exits normally),
///   * the in-bounds success value (42) is NEVER observed from either,
/// which is the observable parity that matters: a bounds violation aborts rather
/// than silently proceeding. (The exact signal number — SIGILL vs SIGABRT — can
/// differ because the bridge traps via an illegal instruction rather than a
/// libc `abort()` call; both are non-continuing fatal aborts.)
#[test]
fn out_of_bounds_index_aborts_like_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("oob");

    // `bad_index()` is `#[inline(never)]` so the compiler cannot fold the bounds
    // check away: `get(&a, 7)` indexes a length-3 slice out of bounds. If the
    // bounds check were skipped, control would reach `std::process::exit(42)`.
    let src = "#[inline(never)] fn get(s: &[i64], i: usize) -> i64 { s[i] } \
               #[inline(never)] fn bad_index() -> usize { 7 } \
               fn main(){ let a: [i64; 3] = [1,2,3]; \
                   let v = get(&a, bad_index()); \
                   if v == 0 { std::process::exit(7); } \
                   std::process::exit(42); }";

    let llvm_bin = compile(&dir, "oob_llvm", src, None);
    let tcg_bin = compile(&dir, "oob_tcg", src, Some(&dylib));

    let (llvm_code, llvm_signaled) = run_status(&llvm_bin);
    let (tcg_code, tcg_signaled) = run_status(&tcg_bin);

    // LLVM under panic=abort must die by signal (it never exits normally).
    assert!(
        llvm_signaled,
        "LLVM OOB program exited normally with {llvm_code:?}; expected a fatal abort signal"
    );
    // trust-cg must ALSO abort (die by signal), not continue to the success path.
    assert!(
        tcg_signaled,
        "trust-cg OOB program exited normally with {tcg_code:?}; the bounds check was \
         skipped (a miscompile) — it must abort like LLVM"
    );
    // Neither backend may ever produce the in-bounds success value (42), which is
    // only reachable if the bounds violation were silently ignored.
    assert_ne!(
        llvm_code,
        Some(42),
        "LLVM OOB program reached the in-bounds success path"
    );
    assert_ne!(
        tcg_code,
        Some(42),
        "trust-cg OOB program reached the in-bounds success path (bounds check skipped)"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
