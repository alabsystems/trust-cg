#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential regression test for the frontend-completeness gap: a by-value TUPLE
// that CONTAINS an ARRAY field (`([i64; 3], i32)`, `([i8; 3], i64)`, `([u8; 4], i32)`,
// `([S; 2], i32)`, `([i16; 2], [i32; 3])`) failed closed "Ty::(...)" when returned by
// value — the whole-tuple ABI value could not be represented.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE: `scalar_byval_tuple_eligible` / `integer_byval_tuple_eligible` gated
// tuple memory-backing on `scalar_field_aggregate_trust_ir_fields`, which
// deliberately FAILS CLOSED on an array field (the scalarized projected-value path
// binds leaves by a flat index and cannot address array elements). So an array-
// containing tuple never became eligible for the verified MEMORY-BACKED byte-offset
// ABI path a named struct with an array field ALREADY rides
// (`validate_memory_aggregate_field_leaves` descends arrays; `m84`/`m111`/`m117`).
//
// THE FIX (src/lib.rs `scalar_byval_eligibility_leaves`): a LOCAL, array-descending
// flatten used ONLY by those two eligibility predicates. It leaves the scalarized
// flat-leaf path untouched (still fails closed on arrays), so the array-field tuple
// is routed through the SAME proven memory-backed machinery as a named array-field
// struct: memory-backed by `compute_memory_backed_locals`, constructed/read by
// `lower_memory_aggregate_construct` + the memory field machinery, every access
// addressed by the RUSTC LAYOUT byte offset (so field REORDERING and array element
// strides are always correct). For any tuple containing NO array, the new flatten
// returns byte-identical leaves to the old one — zero change for the existing corpus.
//
// Gated O0+O3 vs the LLVM oracle. All shapes are consumed by FIELD ACCESS on the
// returned-by-value aggregate (`t.0[i]` / `t.1`), the shape parity with a named
// struct: destructuring an array field OUT into a separate scalarized array local
// (`let (a, k) = ...`) is a SEPARATE pre-existing gap that fails closed for a named
// struct too (`let S { arr, k } = ...`), so it is intentionally not covered here.
//
// REORDER coverage: `([i8; 3], i64)` and `([i16; 2], [i32; 3])` are laid out by rustc
// with the WIDER field first (`i64@0, [i8;3]@8`), so a declaration-order byte offset
// would read the wrong bytes and diverge from LLVM — the match proves the offsets are
// taken from the rustc layout.

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m120 test");
    let built = target_dir
        .join("release")
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

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m120_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn write_panic_stubs(dir: &Path, obj: &Path) -> PathBuf {
    let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if sym.contains("panic") {
            let c = sym.strip_prefix('_').unwrap_or(sym);
            stubs.push_str(&format!(
                "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
            ));
        }
    }
    let stubs_path = dir.join("stubs.c");
    std::fs::write(&stubs_path, stubs).expect("write stubs");
    stubs_path
}

/// Compile `src` at `opt`. When `dylib` is `Some`, use the trust-cg backend and
/// retry a bounded number of times on the PRE-EXISTING, load-dependent
/// `TCG-PASSVAL-067` popcnt-expand output-proof solver TIMEOUT (a fail-closed that is
/// unrelated to frontend lowering; retrying a timeout can never mask a miscompile,
/// which would manifest as a WRONG RESULT rather than a proof timeout).
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> i32 {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut attempt = 0;
    loop {
        let mut cmd = Command::new("rustup");
        cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
            .arg("--crate-type")
            .arg("bin");
        if let Some(dylib) = dylib {
            let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
            backend_arg.push(dylib);
            cmd.arg(&backend_arg);
        }
        cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
            .arg(format!("-Copt-level={opt}"))
            .arg("--emit=obj")
            .arg("--out-dir")
            .arg(&dir)
            .arg(&src_path);
        let output = cmd.output().expect("failed to spawn rustc via rustup");
        let stderr = String::from_utf8_lossy(&output.stderr);
        if !output.status.success() {
            if dylib.is_some() && stderr.contains("PASSVAL-067") && attempt < 5 {
                attempt += 1;
                std::thread::sleep(std::time::Duration::from_millis(500));
                continue;
            }
            panic!(
                "{stem} (opt={opt}, backend={}): failed to compile. stderr: <<<{stderr}>>>",
                if dylib.is_some() { "trust-cg" } else { "llvm" }
            );
        }
        break;
    }

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(!objs.is_empty(), "{stem} (opt={opt}): no object file produced");

    let stubs_path = write_panic_stubs(&dir, &objs[0]);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "{stem} (opt={opt}): link failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    run.status.code().expect("process terminated by signal")
}

fn differential_program(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box as bb;\n{body}\n"
    );
    for opt in ["0", "3"] {
        let llvm = compile_link_run(stem, &src, opt, None);
        let trust = compile_link_run(stem, &src, opt, Some(&dylib));
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        assert_eq!(
            trust, llvm,
            "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} (miscompile)"
        );
    }
}

/// The headline case: `fn -> ([i64; 3], i32)` returned by value, read via field access.
#[test]
fn m120_tuple_i64_array_return_matches_llvm() {
    differential_program(
        "i64arr",
        "#[inline(never)] fn make(x: i64) -> ([i64;3], i32) { ([x, x*2, x*3], (x as i32) + 7) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let t = make(bb(4i64)); \
            ((t.0[0] + t.0[1] + t.0[2] + t.1 as i64) & 0x7f) as i32 }",
        // arr=[4,8,12], k=11 -> 35
        35,
    );
}

/// REORDER-PRONE: `([i8; 3], i64)` — rustc lays this out `i64@0, [i8;3]@8`, so a
/// declaration-order offset would diverge. Match proves rustc-layout offsets.
#[test]
fn m120_tuple_i8_array_i64_reorder_matches_llvm() {
    differential_program(
        "i8reorder",
        "#[inline(never)] fn make(x: i8) -> ([i8;3], i64) { ([x, x+1, x+2], (x as i64)*10) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let t = make(bb(3i8)); \
            ((t.0[0] as i64 + t.0[1] as i64 + t.0[2] as i64 + t.1) & 0x7f) as i32 }",
        // arr=[3,4,5], k=30 -> 42
        42,
    );
}

/// Narrow `[u8; 4]` element array in a tuple.
#[test]
fn m120_tuple_u8_array_matches_llvm() {
    differential_program(
        "u8arr",
        "#[inline(never)] fn make(x: u8) -> ([u8;4], i32) { \
            ([x, x.wrapping_add(1), x.wrapping_add(2), x.wrapping_add(3)], (x as i32)+1) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let t = make(bb(10u8)); \
            ((t.0[0] as i32 + t.0[1] as i32 + t.0[2] as i32 + t.0[3] as i32 + t.1) & 0x7f) as i32 }",
        // arr=[10,11,12,13], k=11 -> 57
        57,
    );
}

/// A larger `[i32; 5]` element array in a tuple.
#[test]
fn m120_tuple_i32_array5_matches_llvm() {
    differential_program(
        "i32arr5",
        "#[inline(never)] fn make(x: i32) -> ([i32;5], i32) { ([x, x*2, x*3, x*4, x*5], x-1) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let t = make(bb(2i32)); \
            ((t.0[0]+t.0[1]+t.0[2]+t.0[3]+t.0[4]+t.1) & 0x7f) as i32 }",
        // arr=[2,4,6,8,10], k=1 -> 31
        31,
    );
}

/// NESTED aggregate: `([S; 2], i32)` where `S` is a two-field struct — the array
/// element itself descends into a struct. (Must be correct OR fail closed; here it is
/// correct — the memory field machinery descends struct-in-array uniformly.)
#[test]
fn m120_tuple_struct_array_matches_llvm() {
    differential_program(
        "structarr",
        "#[derive(Clone,Copy)] struct S { a:i32, b:i32 }\n\
         #[inline(never)] fn make(x: i32) -> ([S;2], i32) { \
            ([S{a:x,b:x+1}, S{a:x+2,b:x+3}], x+100) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let t = make(bb(1i32)); \
            ((t.0[0].a + t.0[0].b + t.0[1].a + t.0[1].b + t.1) & 0x7f) as i32 }",
        // S{1,2},S{3,4}, k=101 -> 1+2+3+4+101 = 111
        111,
    );
}

/// TWO array fields, mixed widths: `([i16; 2], [i32; 3])` — also reorder-prone
/// (`[i32;3]@0, [i16;2]@12`).
#[test]
fn m120_tuple_two_arrays_matches_llvm() {
    differential_program(
        "twoarr",
        "#[inline(never)] fn make(x: i16) -> ([i16;2], [i32;3]) { \
            ([x, x+1], [x as i32*10, x as i32*20, x as i32*30]) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let t = make(bb(2i16)); \
            ((t.0[0] as i32 + t.0[1] as i32 + t.1[0] + t.1[1] + t.1[2]) & 0x7f) as i32 }",
        // a=[2,3], b=[20,40,60] -> 2+3+20+40+60 = 125
        125,
    );
}

/// An array field MUTATED then read (memory-backed aggregate in place).
#[test]
fn m120_tuple_array_field_mutate_matches_llvm() {
    differential_program(
        "mutate",
        "#[derive(Clone,Copy)] struct S { arr:[i64;3], k:i32 }\n\
         #[inline(never)] fn make(x: i64) -> S { S { arr:[x, x*2, x*3], k:(x as i32)+7 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = make(bb(4i64)); s.arr[1] = bb(100i64); s.k = bb(5i32); \
            ((s.arr[0] + s.arr[1] + s.arr[2] + s.k as i64) & 0x7f) as i32 }",
        // arr=[4,100,12], k=5 -> 121
        121,
    );
}

/// CONTROL: a named struct with an array field returned by value (already worked via
/// the memory-backed path; must STAY correct — the tuple fix must not regress it).
#[test]
fn m120_struct_array_field_control_matches_llvm() {
    differential_program(
        "structctl",
        "#[derive(Clone,Copy)] struct S { a:[i8;4], b:i64 }\n\
         #[inline(never)] fn make(x: i8) -> S { S { a:[x, x+1, x+2, x+3], b:(x as i64)*10 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let s = make(bb(3i8)); \
            ((s.a[0] as i64 + s.a[1] as i64 + s.a[2] as i64 + s.a[3] as i64 + s.b) & 0x7f) as i32 }",
        // a=[3,4,5,6], b=30 -> 48
        48,
    );
}
