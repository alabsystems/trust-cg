#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: FLOAT ITERATOR REDUCTIONS / ADAPTERS / COLLECT — `.sum()`,
// `.product()`, `.fold()`, `.map()`, `.filter()`, `.collect::<Vec<_>>()` over
// `f32`/`f64` elements (ranges mapped to floats and `[f64; N]` / `[f32; N]`
// array slices), plus float-returning `Option::unwrap`/`unwrap_or`, compiled for
// x86_64 via the rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with
// results checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// BACKGROUND. The bridge models an iterator chain's element as a single scalar
// LANE; before this test floats were rejected by `is_integer` gates in the
// chain's `sum` consumer and the `Vec::collect` loop (the #105 integer-collect
// guard), so any float iterator reduction failed closed. This test pins the SOUND
// float subset that now compiles:
//   * `.sum::<f64>()` / `.sum::<f32>()` — the accumulator is a memory-backed slot
//     threaded by load/store across the loop back-edge (NOT an SSA phi), so the
//     float recurrence is carried correctly (the #104 accumulator-threading class).
//     The IR-level reduction is `FAdd`, the SAME left-associative fold rustc's
//     `Sum for f32/f64` performs, starting at the additive identity `-0.0` (std's
//     `fold(-0.0, Add::add)`) — so an EMPTY float sum returns `-0.0` and the result
//     is bit-identical to LLVM.
//   * `.product::<f64>()` / `.product::<f32>()` — the same memory-backed float
//     accumulator, seeded at the multiplicative identity `1.0` and updated by
//     `FMul` (including the empty-product identity).
//   * `.fold(init, |a, x| a + x)` over floats — the closure is the monomorphized
//     `FAdd`; the float `init`/`acc` thread through the same memory slot.
//   * `.map(|x| x * k)` / `.filter(|x| *x > c)` producing/threading a float lane.
//   * `.collect::<Vec<f64>>()` — the per-element push stores one `f64` lane.
//
// CORRECTNESS ENCODING. Each program reduces to a float `s`, then exits with
// `(s.to_bits() % 126) as i32` — a deterministic, bit-exact projection of the
// float result (so a wrong reduction, a dropped/duplicated element, a `+0.0`-vs-
// `-0.0` identity slip, or a wrong rounding diverges from LLVM's exit). The corpus
// uses values whose float sum is EXACTLY representable in `f64`/`f32` (small
// integers and halves), so the projection is fully deterministic. Edge cases:
// EMPTY iterator (`-0.0`), single element, negatives, a `*.5` set.
//
// SAFETY INVARIANT (the whole point — a wrong float reduction is a MISCOMPILE):
// at -O0 AND -O3, trust-cg must MATCH LLVM exactly or FAIL CLOSED (produce no
// binary). A trust-cg binary whose exit differs from LLVM is a forbidden silent
// miscompile and fails the test.
//
// PROOF-CERTS. The correctness differential runs under `TCG_NO_PROOF_CERTS=1` (the
// lowering differential proper). A second pass runs at DEFAULT proof-certs-on,
// where a closure-bearing chain emits a `call_once` FnOnce dynamic-dispatch shim
// the x86 proof path cannot yet certify (tracking #465) and so emits a TRAPPING
// stub: the binary then dies LOUDLY by SIGILL. That loud trap is a SAFE outcome
// (never a silent wrong answer) — the default-certs pass asserts trust-cg either
// MATCHES LLVM, fails closed, or traps by signal, but NEVER returns a wrong exit.
//
// FAIL-CLOSED (safe, asserted to never miscompile): a `vec![…]` source (the
// pre-existing `MaybeUninit … Unit` Vec-literal gap, integer too), and most chains
// at -O3 (std generics inline so the bridge interception does not trigger) fail
// closed — these are coverage gaps, not miscompiles.

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
    assert!(status.success(), "cargo build failed; cannot run float-iter test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m115_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` at `opt`; returns `Some(bin)` on success, `None` on (trust-cg)
/// compile failure (the fail-closed case). `certs` selects proof-cert mode:
/// `false` sets `TCG_NO_PROOF_CERTS=1` (the lowering differential), `true` leaves
/// the default certs-on path.
fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: u8,
    certs: bool,
) -> Option<PathBuf> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
        if !certs {
            cmd.env("TCG_NO_PROOF_CERTS", "1");
        }
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

/// Run `bin`; return `Some(exit_code)` for a normal exit, `None` if the process
/// died by SIGNAL (a loud trap — e.g. the proof-cert trapping stub's SIGILL).
fn run_outcome(bin: &Path) -> Option<i32> {
    Command::new(bin).output().expect("run binary").status.code()
}

const BB: &str = "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }";

/// For each (name, body, expected) program, at BOTH O0 and O3, under the given
/// proof-cert mode: LLVM must produce `expected`, and trust-cg must either MATCH
/// LLVM, FAIL CLOSED (no binary), or — only at default certs-on — die LOUDLY by
/// signal (the #465 trapping stub). A trust-cg binary that EXITS NORMALLY with a
/// code differing from LLVM is the silent miscompile we forbid.
fn assert_float_match_or_safe(dir: &Path, shapes: &[(&str, &str, i32)], certs: bool) {
    let dylib = ensure_dylib_built();
    let tag = if certs { "certs" } else { "nocert" };
    for (name, body, expected) in shapes {
        let src = format!("{BB}\nfn main() {{ {body} }}\n");
        for opt in [0u8, 3u8] {
            let llvm_bin = try_compile(dir, &format!("{name}_llvm_{opt}"), &src, None, opt, true)
                .unwrap_or_else(|| panic!("LLVM compile of `{name}` @O{opt} failed"));
            let llvm_exit = run_outcome(&llvm_bin)
                .unwrap_or_else(|| panic!("LLVM binary `{name}` @O{opt} died by signal"));
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` @O{opt} is {llvm_exit}, expected {expected}"
            );
            match try_compile(dir, &format!("{name}_tcg_{opt}_{tag}"), &src, Some(&dylib), opt, certs) {
                Some(tcg_bin) => match run_outcome(&tcg_bin) {
                    Some(tcg_exit) => assert_eq!(
                        tcg_exit, llvm_exit,
                        "MISCOMPILE: trust-cg exit for `{name}` @O{opt} ({tag}) is {tcg_exit}, \
                         LLVM is {llvm_exit} (must match, fail closed, or trap by signal)"
                    ),
                    None => {
                        // Loud trap (SIGILL from the #465 trapping stub). Acceptable
                        // ONLY at default certs-on; never a silent wrong answer.
                        assert!(
                            certs,
                            "trust-cg binary `{name}` @O{opt} died by signal under \
                             TCG_NO_PROOF_CERTS=1 (a trap is only expected at default certs-on)"
                        );
                        eprintln!("note: `{name}` @O{opt} ({tag}) trapped loudly (safe, #465)");
                    }
                },
                None => eprintln!("note: `{name}` @O{opt} ({tag}) failed closed under trust-cg (safe)"),
            }
        }
    }
}

/// The sound float-iterator subset: every reduction result is exactly representable
/// in `f64`/`f32`, so `(s.to_bits() % 126)` is deterministic; the unwrap oracle uses
/// readable exact-value checks. The expected exit is computed against the LLVM run
/// inside the harness (and the literal is asserted equal so staleness is caught).
fn float_iter_shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        // --- f64 range -> map -> sum ---
        // (0..5).map(|i| i as f64 * 1.5).sum() = 0+1.5+3+4.5+6 = 15.0.
        (
            "range_map_sum_f64",
            "let n = bb(5i64); let s: f64 = (0..n).map(|i| i as f64 * 1.5).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            50,
        ),
        // (0..n).map(|i| i as f64).sum() over 0..6 = 15.0 — the float ACCUMULATOR
        // THREADING case (the #104 risk at O3: a dropped float recurrence).
        (
            "range_sum_f64_acc",
            "let n = bb(6i64); let s: f64 = (0..n).map(|i| i as f64).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            50,
        ),
        // EMPTY range sum -> the `-0.0` identity (bits 0x8000…, %126 = 8).
        (
            "range_sum_f64_empty",
            "let n = bb(0i64); let s: f64 = (0..n).map(|i| i as f64).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            8,
        ),
        // SINGLE element.
        (
            "range_sum_f64_single",
            "let n = bb(1i64); let s: f64 = (0..n).map(|i| (i as f64 + 3.5) * 2.0).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            32,
        ),
        // --- f64 fold ---
        // (0..6).map(|i| i as f64).fold(0.0, |a,x| a+x) = 15.0.
        (
            "range_fold_f64",
            "let n = bb(6i64); let s = (0..n).map(|i| i as f64).fold(0.0f64, |a, x| a + x); \
             std::process::exit((s.to_bits() % 126) as i32);",
            50,
        ),
        // --- f64 array slice -> map -> sum (NEGATIVES + halves) ---
        // [1.5,2.5,3.0,-1.0] * 2 = 3+5+6-2 = 12.0.
        (
            "arr_map_sum_f64",
            "let a = [bb(1.5f64), bb(2.5), bb(3.0), bb(-1.0)]; \
             let s: f64 = a.iter().map(|x| x * 2.0).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            44,
        ),
        // --- f64 array slice -> copied -> filter -> sum ---
        // keep > 0: 3.0 + 4.0 + 0.5 = 7.5.
        (
            "arr_filter_sum_f64",
            "let a = [bb(-2.0f64), bb(3.0), bb(-1.0), bb(4.0), bb(0.5)]; \
             let s: f64 = a.iter().copied().filter(|x| *x > 0.0).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            34,
        ),
        // --- f32 array slice -> map -> sum ---
        // [1.5,2.5,4.0]*2 = 3+5+8 = 16.0 (f32).
        (
            "arr_map_sum_f32",
            "let a = [bb(1.5f32), bb(2.5), bb(4.0)]; \
             let s: f32 = a.iter().map(|x| x * 2.0).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            34,
        ),
        // --- f32 range -> map -> sum ---
        // (0..4).map(|i| i as f32 * 0.5).sum() = 0+0.5+1+1.5 = 3.0.
        (
            "range_map_sum_f32",
            "let n = bb(4i64); let s: f32 = (0..n).map(|i| i as f32 * 0.5).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            80,
        ),
        // --- f64 collect then sum (range source) ---
        // collect (0..5).map(|i| i as f64 * 1.5) -> Vec<f64>, then sum = 15.0.
        (
            "range_collect_sum_f64",
            "let n = bb(5i64); let v: Vec<f64> = (0..n).map(|i| i as f64 * 1.5).collect(); \
             let s: f64 = v.iter().sum(); std::process::exit((s.to_bits() % 126) as i32);",
            50,
        ),
        // --- f64 negatives sum (all negative; result -6.0) ---
        (
            "range_sum_f64_neg",
            "let n = bb(3i64); let s: f64 = (0..n).map(|i| -(i as f64) - 1.0).sum(); \
             std::process::exit((s.to_bits() % 126) as i32);",
            36,
        ),
        // --- float product terminal ---
        // 1.5 * 2 * 3 = 9.0 (f64).
        (
            "arr_product_f64",
            "let a = [bb(1.5f64), bb(2.0), bb(3.0)]; \
             let p: f64 = a.iter().product(); \
             std::process::exit((p.to_bits() % 126) as i32);",
            38,
        ),
        // A map chain before product: (1.5+1) * (2+1) = 7.5.
        (
            "arr_map_product_f64",
            "let a = [bb(1.5f64), bb(2.0)]; \
             let p: f64 = a.iter().map(|x| x + 1.0).product(); \
             std::process::exit((p.to_bits() % 126) as i32);",
            34,
        ),
        // f32 accumulator: 2 * 2.5 = 5.0.
        (
            "arr_product_f32",
            "let a = [bb(2.0f32), bb(2.5)]; let p: f32 = a.iter().product(); \
             std::process::exit((p.to_bits() % 126) as i32);",
            104,
        ),
        // Empty product uses the multiplicative identity +1.0 (not sum's -0.0).
        (
            "empty_product_f64_identity",
            "let a: [f64; 0] = []; let p: f64 = a.iter().product(); \
             std::process::exit((p.to_bits() % 126) as i32);",
            114,
        ),
        // `unwrap`'s panic arm ends in `Unreachable` inside a float-returning
        // monomorphization. The live arm must return the payload, never its typed
        // unreachable-edge placeholder; `unwrap_or` covers Some and None paths.
        (
            "float_option_unwrap_and_unwrap_or",
            "let a = Some(bb(3.5f64)).unwrap(); \
             let b = Some(bb(4.5f64)).unwrap_or(bb(8.0)); \
             let c = None::<f64>.unwrap_or(bb(9.0)); \
             let d = Some(bb(2.5f32)).unwrap(); \
             let mut score = 0; if a == 3.5 { score += 1; } \
             if b == 4.5 { score += 1; } if c == 9.0 { score += 1; } \
             if d == 2.5 { score += 1; } std::process::exit(score);",
            4,
        ),
    ]
}

/// CORRECTNESS DIFFERENTIAL under `TCG_NO_PROOF_CERTS=1`: trust-cg must MATCH LLVM
/// (bit-exact float projection) or FAIL CLOSED, at O0 and O3.
#[test]
fn float_iter_match_or_fail_closed_nocert() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("nocert");
    assert_float_match_or_safe(&dir, &float_iter_shapes(), false);
    let _ = std::fs::remove_dir_all(&dir);
}

/// SAFETY at DEFAULT proof-certs-on: trust-cg must MATCH LLVM, fail closed, or trap
/// LOUDLY by signal (#465 stub) — NEVER return a wrong exit, at O0 and O3.
#[test]
fn float_iter_safe_at_default_certs() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("certs");
    assert_float_match_or_safe(&dir, &float_iter_shapes(), true);
    let _ = std::fs::remove_dir_all(&dir);
}
