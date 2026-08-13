// Integration test: NICHE-ENCODED ENUM memory-model lowering, compiled for
// x86_64 via the rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with
// exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The keystone here is the *niche optimization*: an `Option<&T>` /
// `Option<Box<T>>` / `Option<NonZero<T>>` has NO separate tag word — the
// discriminant is stored in an otherwise-invalid bit pattern of a payload field
// (null for the `None` of a `NonNull` pointer; zero for `Option<NonZeroU64>`),
// while the untagged variant (`Some`) is encoded by the field holding its own
// valid value. The bridge gives such an enum a real stack slot and:
//   * DECODEs the discriminant on `match` with the standard niche formula
//     (mirrors `rustc_codegen_ssa::mir::operand::codegen_get_discr`), and
//   * ENCODEs construction by storing the niche value for a niche variant and
//     the plain payload for the untagged variant.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A wrong discriminant
// or payload (Option drives control flow everywhere) shows up as a mismatched
// exit code — a strict differential.

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
    assert!(status.success(), "cargo build failed; cannot run niche-enum test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_niche_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the given backend (None = default LLVM). On success returns
/// `Ok(binary_path)`; on a compile failure returns `Err(stderr)`.
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
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
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

/// The full differential: each niche-encoded-enum `fn main` is compiled by
/// trust-cg AND LLVM, run, and the exit codes must match each other and the
/// expected value. `#[inline(never)]` keeps the niche enum crossing a real
/// call/return boundary (not inlined away). `black_box` hides the runtime choice
/// so the discriminant is a genuine runtime niche-decode, not a constant fold.
#[test]
fn niche_enum_runs_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("enum");

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // Option<&i64>: Some(&x) read through the pointer (untagged variant; the
        // niche field holds the valid non-null reference).
        (
            "opt_ref_some",
            "use std::hint::black_box; \
             #[inline(never)] fn make(s: bool, x: &i64) -> Option<&i64> { if s { Some(x) } else { None } } \
             fn main(){ let a: i64 = 42; let o = make(black_box(true), &a); \
             let v = match o { Some(p)=>*p, None=>-1 }; std::process::exit(v as i32); }",
            42,
        ),
        // Option<&i64>: None (the niche variant; the niche field holds null).
        (
            "opt_ref_none",
            "use std::hint::black_box; \
             #[inline(never)] fn make(s: bool, x: &i64) -> Option<&i64> { if s { Some(x) } else { None } } \
             fn main(){ let a: i64 = 42; let o = make(black_box(false), &a); \
             let v = match o { Some(p)=>*p, None=>7 }; std::process::exit(v as i32); }",
            7,
        ),
        // A function RETURNING Option<&i64> by value, the CALLER matching it.
        (
            "opt_ref_return_some",
            "use std::hint::black_box; \
             #[inline(never)] fn find(y: bool, x: &i64) -> Option<&i64> { if y { Some(x) } else { None } } \
             fn main(){ let a: i64 = 99; let r = find(black_box(true), &a); \
             let v = match r { Some(p)=>*p, None=>-1 }; std::process::exit(v as i32); }",
            99,
        ),
        (
            "opt_ref_return_none",
            "use std::hint::black_box; \
             #[inline(never)] fn find(y: bool, x: &i64) -> Option<&i64> { if y { Some(x) } else { None } } \
             fn main(){ let a: i64 = 99; let r = find(black_box(false), &a); \
             let v = match r { Some(p)=>*p, None=>13 }; std::process::exit(v as i32); }",
            13,
        ),
        // `if let Some(p) = opt { *p } else { default }` — both branches.
        (
            "opt_ref_iflet_some",
            "use std::hint::black_box; \
             #[inline(never)] fn make(s: bool, x: &i64) -> Option<&i64> { if s { Some(x) } else { None } } \
             fn main(){ let a: i64 = 88; let o = make(black_box(true), &a); \
             let v = if let Some(p) = o { *p } else { 5 }; std::process::exit(v as i32); }",
            88,
        ),
        (
            "opt_ref_iflet_none",
            "use std::hint::black_box; \
             #[inline(never)] fn make(s: bool, x: &i64) -> Option<&i64> { if s { Some(x) } else { None } } \
             fn main(){ let a: i64 = 88; let o = make(black_box(false), &a); \
             let v = if let Some(p) = o { *p } else { 5 }; std::process::exit(v as i32); }",
            5,
        ),
        // Option<Box<i64>>: Some — read the value AND free the Box on drop.
        (
            "opt_box_some",
            "use std::hint::black_box; \
             #[inline(never)] fn make(s: bool, v: i64) -> Option<Box<i64>> { if s { Some(Box::new(v)) } else { None } } \
             fn main(){ let o = make(black_box(true), black_box(40)); \
             let v = match o { Some(p)=>*p+2, None=>0 }; std::process::exit(v as i32); }",
            42,
        ),
        // Option<Box<i64>>: None.
        (
            "opt_box_none",
            "use std::hint::black_box; \
             #[inline(never)] fn make(s: bool, v: i64) -> Option<Box<i64>> { if s { Some(Box::new(v)) } else { None } } \
             fn main(){ let o = make(black_box(false), black_box(40)); \
             let v = match o { Some(p)=>*p+2, None=>17 }; std::process::exit(v as i32); }",
            17,
        ),
        // Option<NonZeroU64>: Some — payload read through `.get()` (an integer
        // niche: 0 is the reserved niche value for None).
        (
            "opt_nonzero_some",
            "use std::hint::black_box; use core::num::NonZeroU64; \
             const NZ: NonZeroU64 = match NonZeroU64::new(55) { Some(x)=>x, None=>unreachable!() }; \
             #[inline(never)] fn make(s: bool) -> Option<NonZeroU64> { if s { Some(NZ) } else { None } } \
             fn main(){ let o = make(black_box(true)); \
             let v = match o { Some(p)=>p.get() as i32, None=>9 }; std::process::exit(v); }",
            55,
        ),
        // Option<NonZeroU64>: None.
        (
            "opt_nonzero_none",
            "use std::hint::black_box; use core::num::NonZeroU64; \
             const NZ: NonZeroU64 = match NonZeroU64::new(55) { Some(x)=>x, None=>unreachable!() }; \
             #[inline(never)] fn make(s: bool) -> Option<NonZeroU64> { if s { Some(NZ) } else { None } } \
             fn main(){ let o = make(black_box(false)); \
             let v = match o { Some(p)=>p.get() as i32, None=>9 }; std::process::exit(v); }",
            9,
        ),
        // A custom enum with MULTIPLE niche variants over a `bool` field
        // (relative_max > 0): exercises the general `relative_tag <=u relative_max`
        // niche-decode path, not just the single-variant `== niche_start` case.
        (
            "niche_multi_y",
            "use std::hint::black_box; \
             enum E { Flag(bool), X, Y, Z } \
             #[inline(never)] fn make(n: i64, b: bool) -> E { match n { 0=>E::Flag(b), 1=>E::X, 2=>E::Y, _=>E::Z } } \
             fn main(){ let e = make(black_box(2), black_box(true)); \
             let v = match e { E::Flag(b)=> if b {1} else {2}, E::X=>10, E::Y=>20, E::Z=>30 }; \
             std::process::exit(v); }",
            20,
        ),
        (
            "niche_multi_flag",
            "use std::hint::black_box; \
             enum E { Flag(bool), X, Y, Z } \
             #[inline(never)] fn make(n: i64, b: bool) -> E { match n { 0=>E::Flag(b), 1=>E::X, 2=>E::Y, _=>E::Z } } \
             fn main(){ let e = make(black_box(0), black_box(false)); \
             let v = match e { E::Flag(b)=> if b {1} else {2}, E::X=>10, E::Y=>20, E::Z=>30 }; \
             std::process::exit(v); }",
            2,
        ),
        (
            "niche_multi_z",
            "use std::hint::black_box; \
             enum E { Flag(bool), X, Y, Z } \
             #[inline(never)] fn make(n: i64, b: bool) -> E { match n { 0=>E::Flag(b), 1=>E::X, 2=>E::Y, _=>E::Z } } \
             fn main(){ let e = make(black_box(3), black_box(false)); \
             let v = match e { E::Flag(b)=> if b {1} else {2}, E::X=>10, E::Y=>20, E::Z=>30 }; \
             std::process::exit(v); }",
            30,
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
