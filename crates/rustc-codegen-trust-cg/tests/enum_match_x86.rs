#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: ENUM + MATCH std `fn main` programs compiled for x86_64 via
// the rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: enum + match support. Rust is enum-heavy (`Option`/`Result`/custom
// enums + `match`), so this is the highest-value gap on the road to compiling
// real Rust. The bridge represents a scalarized enum as a statically-known
// discriminant binding plus per-variant payload fields, lowers `match` as
// `SwitchInt(discriminant(local))`, and reads variant payloads through
// `Downcast + Field` projections.
//
// The keystone covered here is the *dead variant-field read*: rustc lowers a
// `match` into a per-variant block that the bridge lowers wholesale, so an arm
// whose variant was never constructed (e.g. the `Some` arm when matching a
// statically-`None` value) still reads an unbound payload field. The guarding
// `SwitchInt` provably never branches there, so the bridge emits a typed default
// and the dead block lowers — sound because any value is observably correct on a
// provably-unreachable edge.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). Layouts/cases the
// scalarization model cannot represent (e.g. an enum nested inside another
// enum's payload) fail closed with a precise diagnostic rather than miscompile,
// and are exercised in `enum_layouts_fail_closed_not_miscompile`.

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
    assert!(status.success(), "cargo build failed; cannot run enum-match test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_enum_{stem}_{}", std::process::id()));
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
/// `Ok(binary_path)`; on a compile failure returns `Err(stderr)` so callers can
/// assert a fail-closed diagnostic.
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

/// The full differential: each enum/match `fn main` is compiled by trust-cg AND
/// LLVM, run, and the exit codes must match each other and the expected value.
#[test]
fn enum_match_shapes_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("shapes");

    // (name, source, expected exit code). All values are in 0..=255 (process exit
    // truncates to a byte).
    let shapes: &[(&str, &str, i32)] = &[
        // Option<i64> + match: the Some arm.
        (
            "opt_some",
            "fn main(){ let o:Option<i64>=Some(7); let r=match o { Some(x)=>x, None=>0 }; \
             std::process::exit(r as i32); }",
            7,
        ),
        // Option<i64> + match: the None arm. This exercises the *dead variant-field
        // read* — the unreachable `Some` arm still reads `(o as Some).0`.
        (
            "opt_none",
            "fn main(){ let o:Option<i64>=None; let r=match o { Some(x)=>x, None=>3 }; \
             std::process::exit(r as i32); }",
            3,
        ),
        // Result<i64,i64> + match: Ok arm.
        (
            "result_ok",
            "fn main(){ let o:Result<i64,i64>=Ok(42); let r=match o { Ok(x)=>x, Err(e)=>e+100 }; \
             std::process::exit(r as i32); }",
            42,
        ),
        // Result<i64,i64> + match: Err arm.
        (
            "result_err",
            "fn main(){ let o:Result<i64,i64>=Err(5); let r=match o { Ok(x)=>x, Err(e)=>e+100 }; \
             std::process::exit(r as i32); }",
            105,
        ),
        // Custom 3-variant enum with payloads: unit, single-payload, two-payload.
        (
            "enum3_c",
            "enum E { A, B(i64), C(i64,i64) } \
             fn main(){ let e=E::C(11,22); \
             let r=match e { E::A=>1, E::B(x)=>x, E::C(a,b)=>a+b }; \
             std::process::exit(r as i32); }",
            33,
        ),
        // Same enum, the single-payload variant.
        (
            "enum3_b",
            "enum E { A, B(i64), C(i64,i64) } \
             fn main(){ let e=E::B(17); \
             let r=match e { E::A=>1, E::B(x)=>x, E::C(a,b)=>a+b }; \
             std::process::exit(r as i32); }",
            17,
        ),
        // Same enum, the unit variant (no payload bound on any arm path).
        (
            "enum3_a",
            "enum E { A, B(i64), C(i64,i64) } \
             fn main(){ let e=E::A; \
             let r=match e { E::A=>1, E::B(x)=>x, E::C(a,b)=>a+b }; \
             std::process::exit(r as i32); }",
            1,
        ),
        // Explicit (non-index) discriminant values: the SwitchInt must match the
        // *discriminant*, not the variant index.
        (
            "enum_explicit",
            "enum E { A=10, B=20, C=30 } \
             fn main(){ let e=E::B; let r=match e { E::A=>1, E::B=>20, E::C=>3 }; \
             std::process::exit(r); }",
            20,
        ),
        // `if let` on Some.
        (
            "if_let_some",
            "fn main(){ let o:Option<i64>=Some(9); let r= if let Some(x)=o { x } else { 0 }; \
             std::process::exit(r as i32); }",
            9,
        ),
        // `if let` on None (else branch; dead Some payload read).
        (
            "if_let_none",
            "fn main(){ let o:Option<i64>=None; let r= if let Some(x)=o { x } else { 11 }; \
             std::process::exit(r as i32); }",
            11,
        ),
        // `matches!` macro (enum discriminant compared to a pattern).
        (
            "matches_macro",
            "fn main(){ let o:Option<i32>=Some(3); \
             std::process::exit(if matches!(o, Some(_)) {1} else {0}); }",
            1,
        ),
        // Wildcard arm over a 3-variant payload enum.
        (
            "wildcard",
            "enum E{A(i64),B(i64),C(i64)} \
             fn main(){ let e=E::B(7); let r=match e { E::A(_)=>0, E::B(x)=>x, _=>99 }; \
             std::process::exit(r as i32); }",
            7,
        ),
        // Match over an enum with FLOAT-carrying variants: the non-matched arm's field
        // read is provably dead, and a float field needs a typed FLOAT zero default (an
        // int 0 would be wrong-typed). `Rect(3.0, 4.0)` -> w*h = 12; the dead `Circle(f64)`
        // read is the case this exercises.
        (
            "float_variant_rect",
            "enum Shape{Circle(f64),Rect(f64,f64)} \
             fn main(){ let s=Shape::Rect(3.0,4.0); \
             std::process::exit(match s{Shape::Circle(r)=>r as i32,Shape::Rect(w,h)=>(w*h) as i32}); }",
            12,
        ),
        // Mixed int/float enum, INT variant selected — the dead read is the `f64` `Flt`
        // field, so the F64 typed-zero default path is the one exercised. -> 42.
        (
            "float_variant_mixed_int",
            "enum M{Int(i32),Flt(f64)} \
             fn main(){ let m=M::Int(42); \
             std::process::exit(match m{M::Int(i)=>i,M::Flt(f)=>f as i32}); }",
            42,
        ),
        // A SINGLE-VARIANT single-field enum by-value match: `((e as Only).0)`. The enum
        // is `adt_maps_to_single_scalar`, so its local is bound as ONE scalar (no per-field
        // projected value); the `[Downcast, Field(0)]` read must passthrough to that scalar
        // (the DowncastField newtype-passthrough term, welded to the Lean spec) rather than
        // fail-close "field 0 before aggregate binding". -> 29.
        (
            "single_variant_match",
            "enum E{Only(i32)} \
             fn main(){ let e=E::Only(29); let r=match e { E::Only(x)=>x }; \
             std::process::exit(r); }",
            29,
        ),
        // The irrefutable-let form of the same single-scalar-enum payload read. -> 23.
        (
            "single_variant_let",
            "enum E{Only(i32)} \
             fn main(){ let e=E::Only(23); let E::Only(x)=e; std::process::exit(x); }",
            23,
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

/// Layouts the scalarization model cannot represent must FAIL CLOSED with a
/// precise diagnostic — never miscompile. A nested enum-in-enum payload
/// (`Option<Result<_,_>>`) is the canonical such case: the inner multi-variant
/// enum carries its own discriminant that cannot nest under an outer field in the
/// single-level scalar binding model. We assert the trust-cg compile fails AND
/// that the diagnostic names the construct (so the blocker is actionable), while
/// LLVM compiles+runs it (confirming the program itself is valid).
#[test]
fn enum_layouts_fail_closed_not_miscompile() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("failclosed");

    let nested = "fn main(){ let o:Option<Result<i64,i64>>=Some(Ok(5)); \
         let r=match o { Some(Ok(x))=>x, Some(Err(e))=>e, None=>0 }; \
         std::process::exit(r as i32); }";

    // LLVM compiles + runs the (valid) program.
    let llvm_bin = compile(&dir, "nested_llvm", nested, None);
    assert_eq!(run_exit_code(&llvm_bin), 5, "LLVM nested enum exit code");

    // The invariant is NEVER MISCOMPILE — not "always refuse". Either outcome is
    // acceptable, and each is checked on its own terms:
    //
    //   * REFUSE -> the diagnostic must NAME the construct, so the blocker stays
    //     actionable;
    //   * COMPILE -> the program must produce LLVM's answer exactly.
    //
    // This was previously written as "must fail closed", which asserted an
    // IMPLEMENTATION LIMIT rather than the safety property. That limit has since
    // been lifted (the bridge now lowers this nested `Option<Result<_,_>>` and
    // returns the correct 5), so the old form failed on a CORRECT compiler — it
    // would have forced a real capability to be reverted to keep a test green.
    // Asserting the property instead means this test keeps its teeth either way:
    // a wrong answer still fails, and so does a silent refusal with no diagnostic.
    match try_compile(&dir, "nested_tcg", nested, Some(&dylib)) {
        Ok(tcg_bin) => {
            assert_eq!(
                run_exit_code(&tcg_bin),
                5,
                "trust-cg compiled the nested enum-in-enum payload but MISCOMPILED it \
                 (LLVM exits 5)"
            );
        }
        Err(stderr) => {
            assert!(
                stderr.contains("nested multi-variant enum")
                    || stderr.contains("nested enum-in-enum"),
                "trust-cg failed closed but without a precise nested-enum diagnostic. \
                 stderr: <<<{stderr}>>>"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
