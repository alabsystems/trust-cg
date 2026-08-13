// Integration test: std Rust using `Vec<T>` (integer elements) compiled for
// x86_64 via the rustc_codegen_trust_cg bridge at BOTH -O0 AND -O3 — COMPILED,
// LINKED, and RUN, with exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS — growable owned collections (`Vec<T>`) run on x86_64 at -O3.
//
// At -O0 the bridge intercepts the `Vec` METHODS (`Vec::new`/`push`/`len`/index)
// by call (see `vec_x86.rs`). At -O3 rustc INLINES those methods into raw struct
// literals + field projections + a slice-from-parts index pattern that the call
// interceptors never see:
//
//   * `Vec::new()`  -> `_1 = Vec { buf: const RawVec {..}, len: const 0 }`
//                      (an `Rvalue::Aggregate` empty-`Vec` struct literal);
//   * `push(x)`     -> `Vec::push_mut(&mut v, x)` (a still-present method call,
//                      returning `&mut T` the source discards);
//   * `len()`       -> `(v.1: usize)` (a `len`-field projection);
//   * `v[i]`        -> read the data pointer through the `buf.inner.ptr.pointer`
//                      `NonNull` field chain, transmute to `*const T`, pair with
//                      `len` into a `*const [T]` fat pointer, then `&(*s)[i]` +
//                      `*ref` to load the element.
//
// The bridge now recognizes the inlined empty-`Vec` construction (synthesizing
// the SAME `{ ptr, cap, len }` slot the `new` call interception builds), the
// `push_mut` method, the `len`/data-pointer field reads, and the `&(*s)[i]`
// slice-element borrow — routing every inlined operation back through the slot
// model. The `assume(len <= isize::MAX)` optimizer hint `-O3` emits is a sound
// no-op. So a plain `Vec<i64>`/`Vec<i32>`/`Vec<u8>` push/index/len/`iter().sum()`
// program now compiles and MATCHES LLVM at -O3 just as it does at -O0.
//
// Each program is compiled with BOTH backends at -O0 and -O3 and run; the
// trust-cg exit code must equal the LLVM exit code (and the expected value). A
// wrong `Vec` element/length at either opt level is a miscompile, so equal exit
// codes are the differential we assert.
//
// `Vec::with_capacity` at -O3 inlines down to a real `RawVecInner::try_allocate_in`
// allocator call returning a niche `Result`, a discriminant-switch, and an Ok-arm
// unwrap, finally building the SAME empty-`Vec` aggregate the inlined `Vec::new()`
// does. The capacity is unobservable (the slot reserves one element and `push`
// grows), so the bridge recognizes the whole allocator chain as dead scaffolding
// around that empty-`Vec` aggregate (see `compute_vec_with_capacity_chain`) — so
// `Vec::with_capacity` now MATCHES LLVM at -O3 too (asserted below).

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
    assert!(status.success(), "cargo build failed; cannot run Vec O3 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m94_{stem}_{}", std::process::id()));
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

/// The full differential: each `Vec<T>` program is compiled by trust-cg AND LLVM
/// at -O0 AND -O3, run, and the exit codes must match each other and the expected
/// value. A divergence at either opt level is a miscompile (a wrong `Vec`
/// element/length, or a crash from a bad allocation/grow). The -O3 cases exercise
/// the inlined-`Vec` recognition (struct-literal construction, `push_mut`, the
/// `len`/data-pointer field reads, the slice-from-parts index, `iter().sum()`).
#[test]
fn vec_o3_programs_run_and_match_llvm() {
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
        // The canonical goal: `Vec::new()`, push 1..=10, sum by index -> 55.
        (
            "i64_new_push_index_sum",
            "fn main() { let mut v: Vec<i64> = Vec::new(); let mut i = 1i64; \
             while i <= 10 { v.push(i); i += 1; } let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } std::process::exit(s as i32); }",
            55,
        ),
        // A growth past several reallocations, dropped before exit.
        (
            "i64_grow_many",
            "fn build() -> i64 { let mut v: Vec<i64> = Vec::new(); \
             let mut i = 1i64; while i <= 100 { v.push(i); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } s } \
             fn main() { std::process::exit((build() % 251) as i32); }",
            (5050 % 251) as i32,
        ),
        // An empty `Vec` that is never pushed: `len() == 0`, slot freed cleanly.
        (
            "i64_empty_len",
            "fn build() -> i64 { let v: Vec<i64> = Vec::new(); v.len() as i64 } \
             fn main() { std::process::exit((build() + 7) as i32); }",
            7,
        ),
        // `i32` elements: push squares mod 17, read the last by `len()-1`.
        (
            "i32_last",
            "fn main() { let mut v: Vec<i32> = Vec::new(); let mut i = 0i32; \
             while i < 13 { v.push((i * i) % 17); i += 1; } \
             let last = v[v.len() - 1]; std::process::exit(last); }",
            (12 * 12) % 17,
        ),
        // `u8` elements: sum 0..37 = 666; 666 % 200 = 66.
        (
            "u8_sum",
            "fn main() { let mut v: Vec<u8> = Vec::new(); let mut i = 0u8; \
             while i < 37 { v.push(i); i += 1; } let mut s = 0u32; \
             for k in 0..v.len() { s += v[k] as u32; } \
             std::process::exit((s % 200) as i32); }",
            ((0u32..37).sum::<u32>() % 200) as i32,
        ),
        // `&mut Vec` to a USER helper that pushes a loop, then sum by index. The
        // helper receives the `Vec` by reference; the inlined `push` inside it is
        // intercepted. 1..=10 = 55.
        (
            "i64_mutref_helper",
            "fn fill(v: &mut Vec<i64>, n: i64) { let mut i = 1i64; \
             while i <= n { v.push(i); i += 1; } } \
             fn build() -> i64 { let mut v: Vec<i64> = Vec::new(); fill(&mut v, 10); \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } s } \
             fn main() { std::process::exit(build() as i32); }",
            55,
        ),
        // Interleaved push / index reads (read between pushes), mixed widths.
        (
            "i64_interleaved",
            "fn main() { let mut v: Vec<i64> = Vec::new(); v.push(10); let a = v[0]; \
             v.push(20); let b = v[1]; v.push(30); let c = v[2]; \
             std::process::exit((a + b + c) as i32); }",
            60,
        ),
        // REFUTATION (conditional-grow push, `emit_vec_push_grow`) at O3: pin
        // the fast-path/grow-path boundary — `with_capacity(4)` filled EXACTLY
        // to capacity (all fast-path, no realloc), order-sensitive checksum,
        // then the boundary 5th push MUST grow. Wrong branch polarity /
        // off-by-one / skipped grow diverges one of the two checksums.
        (
            "i64_push_capacity_boundary",
            "fn main() { let mut v: Vec<i64> = Vec::with_capacity(4); \
             let mut i = 0i64; while i < 4 { v.push(i * 7 + 3); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s = s * 31 + v[j]; j += 1; } \
             v.push(99); \
             let mut t = 0i64; let mut k = 0usize; \
             while k < v.len() { t = t * 31 + v[k]; k += 1; } \
             std::process::exit(((s + t) % 126) as i32); }",
            33,
        ),
        // REFUTATION at O3: `v[0]` + `v[len-1]` after EVERY push across ~6
        // realloc boundaries — a continuation holding a STALE pre-grow data
        // pointer (realloc may move the buffer) diverges the accumulator.
        (
            "i64_push_read_interleaved_grow",
            "fn main() { let mut v: Vec<i64> = Vec::new(); \
             let mut i = 0i64; let mut s = 0i64; \
             while i < 40 { v.push(i * 3 + 1); \
             s = s.wrapping_mul(7).wrapping_add(v[0] + v[v.len() - 1]); i += 1; } \
             std::process::exit(((s % 126 + 126) % 126) as i32); }",
            76,
        ),
        // REFUTATION at O3: STRUCT-class element aggregate-image store across
        // the conditional-grow boundary (one fast path, one boundary fill, one
        // grow); field-weighted order-sensitive checksum.
        (
            "struct_push_grow_boundary",
            "struct P { a: i64, b: i64 } \
             fn main() { let mut v: Vec<P> = Vec::with_capacity(2); \
             let mut i = 0i64; \
             while i < 3 { v.push(P { a: i + 1, b: (i + 1) * 10 }); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s = s * 5 + v[j].a * 2 + v[j].b; j += 1; } \
             std::process::exit((s % 126) as i32); }",
            78,
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
                "trust-cg exit code for `{name}` (-Copt-level={opt}) is {tcg_exit}, \
                 LLVM is {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// `v.iter().sum()` and `v.get(i).unwrap()` go through the `Vec -> &[T]` deref
/// coercion. At -O3 rustc INLINES the iterator/`get` machinery all the way down
/// to the same slice-from-parts INDEX pattern the bridge lowers — so BOTH match
/// LLVM at -O3.
///
/// At -O0 the two DIVERGE by their -O0 blocker:
///   * `i64_iter_sum` still fails CLOSED — the -O0 `Vec::<T>::deref` iterator
///     path is not intercepted (see
///     `vec_x86::vec_iter_sum_fails_closed_with_precise_blocker`).
///   * `i64_get_unwrap` now MATCHES LLVM (PERF-L3 promotion). Its -O0 blocker
///     was NOT the deref — the `get` index path lowers at -O0 — but the
///     `.unwrap()`'s reachable diverging std `#[track_caller]` panic edge, which
///     under `panic=abort` carries `UnwindAction::Unreachable` and used to fail
///     the whole `main` closed ("diverging #[track_caller] std call with a
///     nounwind unwind action"). That edge is now trapped (die-on-the-spot,
///     accepted cosmetic message class), so the SUCCEEDING unwrap path compiles
///     and returns the right value at -O0 too. See
///     `m94_track_caller_unwrap_x86` for the dedicated coverage.
///
/// This test pins that asymmetry (never miscompiles at either level): -O3 both
/// match; -O0 `iter_sum` fails closed, `get_unwrap` matches.
#[test]
fn vec_iter_and_get_match_o3_fail_closed_o0() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("iterget");

    // (name, source, expected exit code, o0_matches_llvm). Both shapes now
    // compile + MATCH LLVM at -O0: the `Vec::deref`-into-slice iterator path is
    // handled (a non-empty `Vec<i64>` iterated by `iter()`), verified sound over
    // an adversarial corpus (empty / negatives / rev+enumerate / nested / count /
    // max / map, all == LLVM at O0 and O3).
    let shapes: &[(&str, &str, i32, bool)] = &[
        // `iter().sum()`: 0..50 = 1225; 1225 % 256 = 201. Compiles + matches at -O0.
        (
            "i64_iter_sum",
            "fn main() { let mut v: Vec<i64> = Vec::new(); for i in 0..50i64 { v.push(i); } \
             let s: i64 = v.iter().sum(); std::process::exit((s % 256) as i32); }",
            ((0i64..50).sum::<i64>() % 256) as i32,
            true,
        ),
        // `.get(i).unwrap()` — the inlined index path through `get` -> `v[3] ==
        // 4`. -O0: the index path lowers; only the `.unwrap()` panic edge used
        // to block it — now matches LLVM (PERF-L3 promotion).
        (
            "i64_get_unwrap",
            "fn main() { let mut v: Vec<i64> = Vec::new(); let mut i = 1i64; \
             while i <= 10 { v.push(i); i += 1; } \
             let x = *v.get(3).unwrap(); std::process::exit(x as i32); }",
            4,
            true,
        ),
    ];

    for (name, src, expected, o0_matches) in shapes {
        // -O3: trust-cg compiles + matches LLVM.
        let llvm3 = compile(&dir, &format!("{name}_o3_llvm"), src, None, "3");
        let tcg3 = compile(&dir, &format!("{name}_o3_tcg"), src, Some(&dylib), "3");
        let llvm_exit = run_exit_code(&llvm3);
        let tcg_exit = run_exit_code(&tcg3);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM exit code for `{name}` (-O3) is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for `{name}` (-O3) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );

        // -O0: LLVM always runs it.
        let llvm0 = compile(&dir, &format!("{name}_o0_llvm"), src, None, "0");
        assert_eq!(
            run_exit_code(&llvm0),
            *expected,
            "LLVM exit code for `{name}` (-O0) should be {expected}"
        );
        if *o0_matches {
            // PERF-L3 promotion: the diverging-track_caller panic edge no longer
            // fails the whole fn closed at -O0; trust-cg compiles + matches LLVM.
            let tcg0 = compile(&dir, &format!("{name}_o0_tcg"), src, Some(&dylib), "0");
            assert_eq!(
                run_exit_code(&tcg0),
                *expected,
                "trust-cg exit code for `{name}` (-O0) should match LLVM ({expected}) \
                 after the PERF-L3 track_caller relaxation"
            );
        } else {
            // trust-cg must still fail CLOSED (no binary) — the -O0 `Vec::deref`
            // iterator path is not intercepted.
            let (output, bin) =
                try_compile(&dir, &format!("{name}_o0_tcg"), src, Some(&dylib), "0");
            assert!(
                !output.status.success() && !bin.exists(),
                "trust-cg unexpectedly compiled `{name}` at -O0; the -O0 `Vec::deref` \
                 iterator path is not intercepted and should fail closed"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// `Vec::with_capacity` at -O3 inlines down to a real `RawVecInner::try_allocate_in`
/// allocator call returning `Result<RawVecInner, _>`, a discriminant-switch, and an
/// Ok-arm unwrap + `assume`-bounds scratch, finally building the SAME empty-`Vec`
/// aggregate (`Vec { buf, len: const 0 }`) the inlined `Vec::new()` does. The
/// capacity is unobservable (the slot reserves a 1-element buffer and `push` grows
/// unconditionally), so the whole allocator chain is DEAD scaffolding around that
/// empty-`Vec` aggregate. The bridge now recognizes it (see
/// `compute_vec_with_capacity_chain`): the dead intermediates are skipped, the
/// `Result` discriminant-switch is redirected to its always-Ok arm, the
/// `handle_error` Err arm is trapped, and the empty-`Vec` aggregate routes through
/// the slot model. So `Vec::with_capacity` now compiles and MATCHES LLVM at -O3 as
/// it does at -O0 (the `with_capacity` method is intercepted by call there).
#[test]
fn vec_with_capacity_o3_matches_llvm() {
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

    // (name, source, expected exit code). Each pushes PAST the requested capacity
    // (forcing a grow) and reads back by index / len / iter — so a wrong capacity
    // behavior or dropped element would diverge from LLVM. The capacity argument is
    // unobservable, so values must match `Vec::new` exactly.
    let shapes: &[(&str, &str, i32)] = &[
        // with_capacity(4), push 1..=10 (grows past 4), sum by index -> 55.
        (
            "i64_push_past",
            "fn build() -> i64 { let mut v: Vec<i64> = Vec::with_capacity(4); \
             let mut i = 1i64; while i <= 10 { v.push(i); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } s } \
             fn main() { std::process::exit(build() as i32); }",
            55,
        ),
        // with_capacity(0): an explicit zero capacity, then push.
        (
            "i64_zero_cap",
            "fn main() { let mut v: Vec<i64> = Vec::with_capacity(0); \
             v.push(7); v.push(8); std::process::exit((v[0] + v[1]) as i32); }",
            15,
        ),
        // i32 elements, push squares mod 17, read the last by len()-1.
        (
            "i32_last",
            "fn main() { let mut v: Vec<i32> = Vec::with_capacity(2); let mut i = 0i32; \
             while i < 13 { v.push((i * i) % 17); i += 1; } \
             let last = v[v.len() - 1]; std::process::exit(last); }",
            (12 * 12) % 17,
        ),
        // u8 elements, sum 0..37 = 666; 666 % 200 = 66.
        (
            "u8_sum",
            "fn main() { let mut v: Vec<u8> = Vec::with_capacity(8); let mut i = 0u8; \
             while i < 37 { v.push(i); i += 1; } let mut s = 0u32; let mut k = 0usize; \
             while k < v.len() { s += v[k] as u32; k += 1; } \
             std::process::exit((s % 200) as i32); }",
            ((0u32..37).sum::<u32>() % 200) as i32,
        ),
        // An empty `with_capacity` never pushed: len() == 0, slot freed cleanly.
        (
            "len_only",
            "fn build() -> i64 { let v: Vec<i64> = Vec::with_capacity(10); v.len() as i64 } \
             fn main() { std::process::exit((build() + 9) as i32); }",
            9,
        ),
        // `iter().sum()` over a with_capacity Vec: the -O3-inlined index path -> 201.
        (
            "iter_sum",
            "fn main() { let mut v: Vec<i64> = Vec::with_capacity(16); \
             for i in 0..50i64 { v.push(i); } let s: i64 = v.iter().sum(); \
             std::process::exit((s % 256) as i32); }",
            ((0i64..50).sum::<i64>() % 256) as i32,
        ),
    ];

    for (name, src, expected) in shapes {
        // -O0: trust-cg intercepts `with_capacity` by call and matches LLVM.
        // (`iter_sum` is the exception: the -O0 `Vec::deref` iterator path is not
        // intercepted, so it fails closed at -O0 — see
        // `vec_iter_and_get_match_o3_fail_closed_o0`. We only assert -O3 for it.)
        let llvm3 = compile(&dir, &format!("{name}_o3_llvm"), src, None, "3");
        let tcg3 = compile(&dir, &format!("{name}_o3_tcg"), src, Some(&dylib), "3");
        let llvm_exit = run_exit_code(&llvm3);
        let tcg_exit = run_exit_code(&tcg3);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM with_capacity `{name}` (-O3) is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg with_capacity `{name}` (-O3) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );

        if *name != "iter_sum" {
            let llvm0 = compile(&dir, &format!("{name}_o0_llvm"), src, None, "0");
            let tcg0 = compile(&dir, &format!("{name}_o0_tcg"), src, Some(&dylib), "0");
            let l0 = run_exit_code(&llvm0);
            let t0 = run_exit_code(&tcg0);
            assert_eq!(l0, *expected, "LLVM with_capacity `{name}` (-O0) is {l0}");
            assert_eq!(
                t0, l0,
                "trust-cg with_capacity `{name}` (-O0) is {t0}, LLVM is {l0} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
