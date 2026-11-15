#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the x86-64 SSE2 vectorizer's beat-llvm tiers fire on the
// p4_matmul / h1_vec_push_sum / v2_memfill program shapes through the bridge
// at -Copt-level=3, and the vectorized binaries exit with the manifest codes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: task m143 — the Linux x86-64 vectorization regression pin. Each
// program is compiled with the TRACKED `-Ztrust-ir-cg-args=trace-vectorize`
// knob (trustc refuses the `TCG_TRACE_VECTORIZE` environment spelling), so the
// pass's per-loop decision lands on stderr; the test asserts the EXACT accept
// line of the tier that owns each kernel (`x86_vectorize::run_impl`'s trace
// strings), runs the binary, and pins its exit code to
// `benchmarks/beat-llvm/progs/manifest.json` (p4 111, h1 60, v2 44), which is
// also cross-checked against rustc's LLVM backend on the same source.
//
// The three sources are verbatim copies of the benchmark programs. The shapes
// they pin are: the bridge's fused-`Assert` inline bounds carriers inside a
// saxpy-Q row-register nest (p4); the intercepted `Vec` index check with the
// `Jcc E -> trap` guard polarity feeding the heap-sum tier (h1); and the
// compile-time u8 fill routed to one `memset` libcall, plus the tracked
// `no-x86-fill-memset` opt-out that keeps the inline MOVDQU loop (v2). A tier
// that silently stops firing shows up here as a missing trace line rather than
// as a timing regression noticed later.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;

/// `benchmarks/beat-llvm/progs/p4_matmul.rs` (manifest `expected_exit` 111).
const P4_MATMUL: &str = r#"
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
const N: usize = 24;
fn main() {
    let seed = bb(3u64);
    let mut a = [0i64; N * N];
    let mut b = [0i64; N * N];
    let mut i = 0usize;
    while i < N * N {
        a[i] = ((i as u64).wrapping_mul(seed).wrapping_add(7) % 100) as i64;
        b[i] = ((i as u64).wrapping_mul(seed.wrapping_add(11)).wrapping_add(3) % 100) as i64;
        i += 1;
    }
    let reps = bb(20_000u32);
    let mut acc: i64 = 0;
    let mut r = 0u32;
    while r < reps {
        let mut c = [0i64; N * N];
        let mut i = 0usize;
        while i < N {
            let mut k = 0usize;
            while k < N {
                let aik = a[i * N + k];
                let mut j = 0usize;
                while j < N {
                    c[i * N + j] = c[i * N + j].wrapping_add(aik.wrapping_mul(b[k * N + j]));
                    j += 1;
                }
                k += 1;
            }
            i += 1;
        }
        acc = acc.wrapping_add(c[(r as usize * 37) % (N * N)]);
        a[(r as usize * 13) % (N * N)] = acc & 0xFF;
        r += 1;
    }
    done((acc as u64));
}
"#;

/// `benchmarks/beat-llvm/progs/h1_vec_push_sum.rs` (manifest `expected_exit` 60).
const H1_VEC_PUSH_SUM: &str = r#"
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let n = bb(300_000usize);
    let mut x: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        v.push(x);
        i += 1;
    }
    let passes = bb(300u32);
    let mut acc: u64 = 0;
    let mut p = 0u32;
    while p < passes {
        let mut k = 0usize;
        while k < v.len() {
            acc = acc.wrapping_add(v[k]);
            k += 1;
        }
        p += 1;
    }
    done(acc);
}
"#;

/// `benchmarks/beat-llvm/progs/v2_memfill.rs` (manifest `expected_exit` 44).
const V2_MEMFILL: &str = r#"
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
const N: usize = 8192;
fn main() {
    let reps = bb(100_000u32);
    let mut a = [0u8; N];
    let mut acc: u64 = 0;
    let mut r = 0u32;
    while r < reps {
        let v = (r as u8) | 1;
        let mut i = 0usize;
        while i < N {
            a[i] = v;
            i += 1;
        }
        let idx = bb((r as usize).wrapping_mul(31)) % N;
        acc = acc.wrapping_add(a[idx] as u64);
        r += 1;
    }
    done(acc);
}
"#;

/// The exact accept lines `x86_vectorize::run_impl` prints for each tier
/// (the prefix up to the plan-specific detail), and the v2 route suffixes.
const TRACE_SAXPYQ_ROWREG: &str = "VECTORIZED saxpy-Q ROW-REGISTER nest:";
const TRACE_SAXPYQ_INNER: &str = "VECTORIZED saxpy-Q (i64 RMW accumulate) loop:";
const TRACE_HEAP_SUMQ: &str = "VECTORIZED heap-slice i64 sum reduction:";
const TRACE_FILL: &str = "VECTORIZED fill loop:";
const TRACE_FILL_MEMSET: &str = "route=memset libcall (8192 bytes";
const TRACE_FILL_MOVDQU: &str = "route=movdqu store loop";

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m143_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn exit_code(bin: &Path) -> i32 {
    let out = Command::new(bin).output().expect("run binary");
    out.status
        .code()
        .unwrap_or_else(|| panic!("{bin:?} died by signal: {:?}", out.status))
}

/// Ground truth: the same source through rustc's LLVM backend with the same
/// `--target` / panic / opt flags the beat-llvm harness uses.
fn llvm_exit_code(dir: &Path, stem: &str, src: &str) -> i32 {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("{stem}_llvm"));
    let status = toolchain_support::rustc_command()
        .args([
            "--crate-type",
            "bin",
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Copt-level=3",
        ])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .status()
        .expect("spawn rustc (LLVM)");
    assert!(status.success(), "LLVM reference failed to compile {stem}");
    exit_code(&bin)
}

/// Bridge lane at -Copt-level=3 with the tracked vectorizer trace knob (plus
/// `extra_knobs`); returns the binary and the compile's stderr. A compile
/// failure is a test failure: these shapes are pinned as supported.
fn compile_bridge(
    dir: &Path,
    dylib: &Path,
    stem: &str,
    src: &str,
    extra_knobs: &[&str],
) -> (PathBuf, String) {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("{stem}_bridge{}", extra_knobs.len()));
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    let mut knobs = vec!["trace-vectorize"];
    knobs.extend_from_slice(extra_knobs);
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "bin"])
        .arg(backend_arg)
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=3"])
        .arg(toolchain_support::backend_knobs_arg(&knobs))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc (bridge)");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "bridge failed to compile {stem} at -O3 with knobs {knobs:?}: <<<{stderr}>>>"
    );
    (bin, stderr)
}

fn assert_trace_lines(stem: &str, stderr: &str, expected: &[&str]) {
    let trace: Vec<&str> = stderr
        .lines()
        .filter(|l| l.starts_with("x86-vectorize:"))
        .collect();
    for needle in expected {
        assert!(
            trace.iter().any(|l| l.contains(needle)),
            "{stem}: expected vectorizer trace line containing {needle:?}; trace lines:\n{}",
            trace.join("\n")
        );
    }
}

struct Case {
    stem: &'static str,
    src: &'static str,
    expected_exit: i32,
    trace: &'static [&'static str],
}

const CASES: &[Case] = &[
    Case {
        stem: "p4_matmul",
        src: P4_MATMUL,
        expected_exit: 111,
        // The k-loop takes the row-register tier and the j-loop the inner
        // saxpy-Q tier (the row tier's fail path), both through the inline
        // `TrapBoundsCheckExact` carrier arms.
        trace: &[TRACE_SAXPYQ_ROWREG, TRACE_SAXPYQ_INNER],
    },
    Case {
        stem: "h1_vec_push_sum",
        src: H1_VEC_PUSH_SUM,
        expected_exit: 60,
        trace: &[TRACE_HEAP_SUMQ],
    },
    Case {
        stem: "v2_memfill",
        src: V2_MEMFILL,
        expected_exit: 44,
        trace: &[TRACE_FILL, TRACE_FILL_MEMSET],
    },
];

/// Every beat-llvm kernel's tier fires at -O3 (exact trace line) and the
/// vectorized binary exits with the manifest code, which LLVM reproduces.
#[test]
fn beat_llvm_vector_tiers_fire_and_exit_codes_match_manifest() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("tiers");
    for case in CASES {
        let llvm = llvm_exit_code(&dir, case.stem, case.src);
        assert_eq!(
            llvm, case.expected_exit,
            "{}: LLVM lane exit differs from the manifest pin",
            case.stem
        );
        let (bin, stderr) = compile_bridge(&dir, &dylib, case.stem, case.src, &[]);
        assert_trace_lines(case.stem, &stderr, case.trace);
        assert_eq!(
            exit_code(&bin),
            case.expected_exit,
            "{}: vectorized binary exit differs from the manifest pin",
            case.stem
        );
    }
}

/// The tracked `no-x86-fill-memset` opt-out keeps v2's fill on the inline
/// MOVDQU store loop (the tier still fires) with the same exit code.
#[test]
fn v2_fill_memset_opt_out_keeps_the_movdqu_loop() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("memset_opt_out");
    let (bin, stderr) = compile_bridge(
        &dir,
        &dylib,
        "v2_memfill",
        V2_MEMFILL,
        &["no-x86-fill-memset"],
    );
    assert_trace_lines("v2_memfill", &stderr, &[TRACE_FILL, TRACE_FILL_MOVDQU]);
    assert!(
        !stderr.contains(TRACE_FILL_MEMSET),
        "the opt-out must not take the memset route: <<<{stderr}>>>"
    );
    assert_eq!(exit_code(&bin), 44);
}
