// Integration test: ARRAY EQUALITY `[E; N] == [E; N]` via the `raw_eq` intrinsic.
//
// `==` on a fixed-size array lowers (through the array `PartialEq` impl) to the
// `raw_eq::<[E; N]>(a: &T, b: &T) -> bool` intrinsic — a BYTE comparison of `*a`
// and `*b`. It USED to fail closed: at -O3 the inlined `raw_eq` intrinsic was
// rejected ("unsupported intrinsic"), and at -O0 the `<[E; N] as PartialEq>::eq`
// body — itself codegenned — calls the same intrinsic, so the symbol fell off and
// the link failed. The bridge now intercepts `raw_eq` for arrays of SCALAR
// integer / bool elements and synthesizes it from ALREADY-PROVEN primitives (no
// new opcode/proof):
//   * MEMORY-BACKED side (`-O0` / address-taken): `Load E` at each `i*size` byte
//     offset through the array pointer (PtrToInt/add/IntToPtr address math), then
//   * SCALARIZED side (`-O3`, elements held as per-field SSA values): read the
//     element SSA value directly (no load through a nonexistent address), then
//   * `ICmp Eq` per element pair, AND-reduced with the verified Bool
//     `Select(acc, eq, false)` idiom seeded with `true`.
//
// SOUNDNESS: for a `[E; N]` of a scalar integer / bool element the array has NO
// inter-element padding (`size_of::<[E;N]>() == N*size_of::<E>()`, asserted) and
// a scalar has no padding bits, so byte equality == element-wise `==`. Float /
// pointer / nested-aggregate elements, padded layouts, and oversize `N` fail
// closed — never a wrong answer.
//
// Each program is compiled by trust-cg AND LLVM at BOTH -Copt-level=0 and =3, run,
// and the exit codes asserted equal. The hard invariant: trust-cg MUST match LLVM
// or fail closed (produce no binary) — NEVER a different exit code. A wrong array
// comparison would be the exact silent miscompile this forbids.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

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
    let dir = std::env::temp_dir().join(format!("rcl2_m113_{stem}_{}", std::process::id()));
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
/// compile/link failure (the fail-closed case).
fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: u8,
) -> Option<PathBuf> {
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
    if output.status.success() && bin.exists() {
        Some(bin)
    } else {
        None
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

/// For each (name, body, expected) program, at BOTH O0 and O3: LLVM must produce
/// `expected`, and trust-cg must either MATCH LLVM or FAIL CLOSED (no binary).
fn assert_match_or_fail_closed(dir: &Path, shapes: &[(&str, &str, i32)]) {
    let dylib = ensure_dylib_built();
    for (name, body, expected) in shapes {
        let src = body.to_string();
        for opt in [0u8, 3u8] {
            let llvm_bin = try_compile(dir, &format!("{name}_llvm_{opt}"), &src, None, opt)
                .unwrap_or_else(|| panic!("LLVM compile of `{name}` @O{opt} failed"));
            let llvm_exit = run_exit_code(&llvm_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` @O{opt} is {llvm_exit}, expected {expected}"
            );
            match try_compile(dir, &format!("{name}_tcg_{opt}"), &src, Some(&dylib), opt) {
                Some(tcg_bin) => {
                    let tcg_exit = run_exit_code(&tcg_bin);
                    assert_eq!(
                        tcg_exit, llvm_exit,
                        "MISCOMPILE: trust-cg exit for `{name}` @O{opt} is {tcg_exit}, \
                         LLVM is {llvm_exit} (must match or fail closed)"
                    );
                }
                None => {
                    eprintln!("note: `{name}` @O{opt} failed closed under trust-cg (safe)");
                }
            }
        }
    }
}

#[test]
fn array_raw_eq_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("re");
    // Each program black_box-es its SCALAR inputs (so the arrays carry runtime
    // values, exercising the real comparison rather than a const-fold), builds two
    // arrays, and exits with `(eq as i64)`-derived low byte. The `==` drives the
    // exit so a wrong comparison flips the observable exit code.
    let shapes: &[(&str, &str, i32)] = &[
        // ---- equal / unequal i32 3-element ----
        ("i32_3_eq",
         "fn main(){ let x=std::hint::black_box(2i32); let y=std::hint::black_box(2i32); \
          let a=[1i32,x,3]; let b=[1i32,y,3]; \
          std::process::exit((((a==b) as i64)+10 & 0xff) as i32); }",
         11),
        ("i32_3_ne_mid",
         "fn main(){ let x=std::hint::black_box(2i32); let y=std::hint::black_box(9i32); \
          let a=[1i32,x,3]; let b=[1i32,y,3]; \
          std::process::exit((((a==b) as i64)+10 & 0xff) as i32); }",
         10),
        ("i32_3_ne_first",
         "fn main(){ let x=std::hint::black_box(7i32); \
          let a=[x,2,3]; let b=[1i32,2,3]; \
          std::process::exit((((a==b) as i64)+10 & 0xff) as i32); }",
         10),
        // ---- u8 4-element zeros (the `[0u8; N]` shape) ----
        ("u8_4_zeros_eq",
         "fn main(){ let z=std::hint::black_box(0u8); \
          let a=[z,z,z,z]; let b=[0u8,0,0,0]; \
          std::process::exit((((a==b) as i64)+10 & 0xff) as i32); }",
         11),
        ("u8_4_ne_last",
         "fn main(){ let z=std::hint::black_box(0u8); \
          let a=[z,z,z,z]; let b=[0u8,0,0,1]; \
          std::process::exit((((a==b) as i64)+10 & 0xff) as i32); }",
         10),
        // ---- i64 2-element (eq scores 2, ne scores 1) ----
        ("i64_2_mix",
         "fn main(){ let p=std::hint::black_box(100i64); let q=std::hint::black_box(200i64); \
          let a=[p,q]; let b=[100i64,200]; let c=[100i64,201]; \
          std::process::exit(((((a==b) as i64)*2 + ((a==c) as i64) + 10) & 0xff) as i32); }",
         12),
        // ---- i32 5-element, differ only at the last ----
        ("i32_5_last",
         "fn main(){ let v=std::hint::black_box(5i32); \
          let a=[1i32,2,3,4,v]; let b=[1i32,2,3,4,5]; let c=[1i32,2,3,4,6]; \
          std::process::exit(((((a==b) as i64)*4 + ((a==c) as i64) + 10) & 0xff) as i32); }",
         14),
        // ---- bool 3-element ----
        ("bool_3_mix",
         "fn main(){ let t=std::hint::black_box(true); let f=std::hint::black_box(false); \
          let a=[t,f,t]; let b=[true,false,true]; let c=[true,true,true]; \
          std::process::exit(((((a==b) as i64)*4 + ((a==c) as i64) + 10) & 0xff) as i32); }",
         14),
        // ---- u16 / i8 element widths ----
        ("u16_3_eq",
         "fn main(){ let x=std::hint::black_box(0x1234u16); \
          let a=[x,2,3]; let b=[0x1234u16,2,3]; \
          std::process::exit((((a==b) as i64)+10 & 0xff) as i32); }",
         11),
        ("i8_3_ne",
         "fn main(){ let x=std::hint::black_box(-5i8); \
          let a=[x,2,3]; let b=[-6i8,2,3]; \
          std::process::exit((((a==b) as i64)+10 & 0xff) as i32); }",
         10),
        // ---- by-reference comparison through a non-inlined fn (`*a == *b`) ----
        ("ref_cmp",
         "#[inline(never)] fn cmp(a:&[i32;3], b:&[i32;3])->bool { *a==*b } \
          fn main(){ let x=std::hint::black_box(2i32); \
          let a=[1i32,x,3]; let b=[1i32,2,3]; let c=[1i32,9,3]; \
          std::process::exit(((((cmp(&a,&b)) as i64)*2 + ((cmp(&a,&c)) as i64) + 10) & 0xff) as i32); }",
         12),
        // ---- CONTROL: arithmetic that never touches an array eq (must stay correct) ----
        ("control_add",
         "fn main(){ let a=std::hint::black_box(40u32); let b=std::hint::black_box(2u32); \
          std::process::exit((a+b) as i32); }",
         42),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}
