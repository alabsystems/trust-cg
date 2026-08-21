#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: the `-O2`/`-O3`-inlined & SROA'd `<[T]>::to_vec` /
// `<[T] as ToOwned>::to_owned` allocation compiled for x86_64 via the
// rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend (lane X1).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// VEC-1 lowers `to_vec` at `-O0` (a real call → `lower_slice_to_vec`); at
// `-O2`/`-O3` rustc fully SROA's away the `Vec` local, leaving the freshly-
// allocated buffer's data pointer + capacity as bare `RawVecInner`-Ok-arm
// projections (`ptr @ (Ok).0.0.0`, `cap @ (Ok).0.1`) plus a `copy_nonoverlapping`
// fill — with NO `Vec { .., len: const 0 }` aggregate. `compute_slice_to_vec_-`
// `sroa_chains` binds the data-pointer projection to a fresh `__rust_alloc`, the
// capacity projection to the (const) element count, redirects the discriminant
// switch to the Ok arm + traps the `handle_error` Err arm, and leaves the buffer
// fill to the existing sound `copy_nonoverlapping` memcpy lowering.
//
// The differential is exhaustive by design: the HIGHEST risk is a wrong
// `RawVecInner` field mapping (ptr vs cap), which would silently produce a wrong
// data address or wrong length. So every program pins CONTENT (indexed reads,
// including a negative element), LENGTH, a full-buffer loop-sum (cross-block data-
// pointer flow), and — critically — CAPACITY (`v.capacity()` must equal the length;
// a ptr/cap field swap makes `capacity()` a garbage pointer value, diverging). The
// negatives pin that a non-integer element (`String`/`Box`/tuple/array/ZST) and an
// empty slice (count 0 → `__rust_alloc(0)` would be unsound) all stay FAIL-CLOSED.

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
    let dir = std::env::temp_dir().join(format!("rcl2_m127_{stem}_{}", std::process::id()));
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

/// The SROA'd `to_vec`/`to_owned` differential: each program is compiled by
/// trust-cg AND LLVM at `-O2` and `-O3`, run, and the exit codes must match each
/// other and the expected value. CONTENT (indexed reads, a negative element), the
/// LENGTH, a full-buffer loop-sum (cross-block data-pointer flow), and the CAPACITY
/// are all folded into each exit code, so a wrong copied byte, wrong length, wrong
/// capacity, or a ptr/cap field swap diverges.
#[test]
fn to_vec_sroa_matches_llvm_at_o2_o3() {
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

    // (name, source, expected exit code). Each exit code mixes content + length +
    // (where used) capacity so a wrong field mapping cannot hide.
    let shapes: &[(&str, &str, i32)] = &[
        // u8: content (v[0]+v[2]) + length.
        (
            "u8_content_len",
            "fn main() { let v = [10u8, 20, 30].to_vec(); \
             std::process::exit(v.len() as i32 + v[0] as i32 + v[2] as i32); }",
            43,
        ),
        // i32 with a NEGATIVE element (sign-correct copy).
        (
            "i32_negative",
            "fn main() { let v = [100i32, -3, 7].to_vec(); \
             std::process::exit(v[0] + v[1] * 10 + v[2]); }",
            77,
        ),
        // i8 negatives + loop-sum (cross-block data-pointer flow).
        (
            "i8_loop_sum",
            "fn main() { let v = [10i8, -20, 30, -40].to_vec(); \
             let mut s = 0i32; let mut i = 0usize; \
             while i < v.len() { s += v[i] as i32; i += 1; } \
             std::process::exit(s + 100 + v.len() as i32); }",
            84,
        ),
        // i64 loop-sum + CAPACITY (cap must equal len == 4).
        (
            "i64_sum_cap",
            "fn main() { let v = [1000i64, -500, 250, 125].to_vec(); \
             let mut s = 0i64; let mut i = 0usize; \
             while i < v.len() { s += v[i]; i += 1; } \
             std::process::exit((s / 5) as i32 + v.capacity() as i32); }",
            179,
        ),
        // u16 to_owned through a borrowed const slice.
        (
            "u16_to_owned",
            "fn main() { let a: [u16; 4] = [10, 20, 30, 40]; let s = &a[..]; \
             let v: Vec<u16> = s.to_owned(); std::process::exit((v[3] + v[1]) as i32); }",
            60,
        ),
        // u64 loop-sum + length.
        (
            "u64_sum_len",
            "fn main() { let v = [7u64, 11, 13, 17, 19].to_vec(); \
             let mut s = 0u64; let mut i = 0usize; \
             while i < v.len() { s += v[i]; i += 1; } \
             std::process::exit(s as i32 + v.len() as i32); }",
            72,
        ),
        // An offset sub-slice `a[1..4]` — the copy must start at the RIGHT element.
        (
            "offset_subslice",
            "fn main() { let a = [10u8, 20, 30, 40, 50]; let v = a[1..4].to_vec(); \
             std::process::exit(v.len() as i32 + v[0] as i32 + v[2] as i32); }",
            63,
        ),
        // Two independent SROA'd `to_vec`s in one body must not cross-wire.
        (
            "two_to_vecs",
            "fn main() { let a = [1i32, 2, 3].to_vec(); let b = [10i32, 20].to_vec(); \
             std::process::exit(a[2] + b[1] + a.len() as i32 + b.len() as i32); }",
            28,
        ),
        // The Vec is DROPPED on a normal return (its buffer freed through the slot
        // Drop the Vec model uses).
        (
            "drop_on_return",
            "#[inline(never)] fn compute() -> i32 { let v = [5i32, 10, 15, 20].to_vec(); \
             v[0] + v[3] } fn main() { std::process::exit(compute()); }",
            25,
        ),
    ];

    for opt in ["2", "3"] {
        for (name, src, expected) in shapes {
            let llvm_bin = compile(&dir, &format!("{name}_o{opt}_llvm"), src, None, opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_bin = compile(&dir, &format!("{name}_o{opt}_tcg"), src, Some(&dylib), opt);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                tcg_exit, llvm_exit,
                "`{name}` (opt={opt}): trust-cg exit {tcg_exit} != LLVM exit {llvm_exit} (MISCOMPILE)"
            );
            assert_eq!(
                tcg_exit, *expected,
                "`{name}` (opt={opt}): exit {tcg_exit} != expected {expected}"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A dedicated capacity probe: `v.capacity()` must equal the length for `to_vec`
/// (`cap == len == count`). This is the single most direct check that the ptr and
/// cap `RawVecInner` projections are NOT swapped — a swap yields the data POINTER
/// (a huge, run-varying value) where the length is expected.
#[test]
fn to_vec_sroa_capacity_equals_len_no_field_swap() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("cap");
    // `capacity() * 10 + len` — for `to_vec` cap == len, so this is `len * 11`. A
    // ptr/cap swap makes `capacity()` a pointer value and the product diverges.
    let src = "fn main() { let v = [10u8, 20, 30, 40, 50].to_vec(); \
               std::process::exit(v.capacity() as i32 * 10 + v.len() as i32); }";
    for opt in ["2", "3"] {
        let llvm_bin = compile(&dir, &format!("cap_o{opt}_llvm"), src, None, opt);
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_bin = compile(&dir, &format!("cap_o{opt}_tcg"), src, Some(&dylib), opt);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            tcg_exit, llvm_exit,
            "capacity probe (opt={opt}): trust-cg {tcg_exit} != LLVM {llvm_exit} (ptr/cap SWAP?)"
        );
        assert_eq!(tcg_exit, 55, "capacity probe (opt={opt}): exit != 55 (cap==len==5)");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Unsupported SROA'd `to_vec` shapes stay FAIL-CLOSED at `-O2`/`-O3` (a loud
/// [TCG-MIR-UNSUPPORTED], never a wrong value): a `String`/`Box`/tuple/array/ZST
/// element (all non-integer — a non-`Copy`/`Drop`/padded element uses `ConvertVec`
/// clone-per-element with different MIR, and the recognizer's integer gate rejects
/// the rest) and an EMPTY slice (count 0 → `try_allocate_in` returns a dangling
/// `NonNull` with NO allocation, so `__rust_alloc(0)` would be unsound).
#[test]
fn to_vec_sroa_unsupported_shapes_stay_fail_closed() {
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

    let negatives: &[(&str, &str)] = &[
        // `Vec<String>::to_vec` — `ConvertVec` clone-per-element (no memcpy).
        (
            "string_element",
            "fn main() { let v = [String::from(\"a\"), String::from(\"b\")].to_vec(); \
             std::process::exit(v.len() as i32); }",
        ),
        // A needs-drop (`Box`) element.
        (
            "box_element",
            "fn main() { let v = [Box::new(1i64), Box::new(2)].to_vec(); \
             std::process::exit(*v[0] as i32); }",
        ),
        // A `Copy` but non-scalar tuple element.
        (
            "tuple_element",
            "fn main() { let v = [(1i32, 2i32), (3, 4)].to_vec(); \
             std::process::exit(v[1].0); }",
        ),
        // A `Copy` but non-scalar array element.
        (
            "array_element",
            "fn main() { let v = [[1u8, 2], [3, 4], [5, 6]].to_vec(); \
             std::process::exit(v[2][1] as i32); }",
        ),
        // A float (non-integer scalar) element.
        (
            "f64_element",
            "fn main() { let v = [1.5f64, 2.5, 3.5].to_vec(); \
             std::process::exit((v[0] + v[2]) as i32); }",
        ),
        // An EMPTY slice (count 0).
        (
            "empty_slice",
            "fn main() { let a: [i32; 0] = []; let v = a.to_vec(); \
             std::process::exit(v.len() as i32 + 7); }",
        ),
    ];

    for opt in ["2", "3"] {
        for (name, src) in negatives {
            // LLVM must still compile + run it (these are valid programs).
            let _ = compile(&dir, &format!("{name}_o{opt}_llvm"), src, None, opt);
            // trust-cg must FAIL CLOSED (no binary), never emit a wrong-value binary.
            let (output, bin) = try_compile(&dir, &format!("{name}_o{opt}_tcg"), src, Some(&dylib), opt);
            assert!(
                !output.status.success() && !bin.exists(),
                "`{name}` (opt={opt}): expected trust-cg to FAIL CLOSED but it compiled"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}
