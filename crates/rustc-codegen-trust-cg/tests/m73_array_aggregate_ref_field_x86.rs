// Differential regression test for MISCOMPILE #73: a field write/read through a
// `&`/`&mut [T; N]` ARRAY reference, where the element is a field-reordered
// aggregate, addressed the field in DECLARATION order instead of rustc's order.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. rustc reorders an aggregate's fields by descending alignment:
// `(u8, u64, u16)` places its `.1` (the u64) at offset 0, not 8. An array of such
// tuples/structs is stored at those rustc offsets (one `Alloca`, laid out by
// `array_memory_layout`), and `&arr` passes that slot pointer directly. But a
// `(*a)[i].field` access through the reference was routed to the scalarized
// `aggregate_field_memory_access` path, which addresses the element's fields
// through a DECLARATION-ORDER flattened trust-ir tuple. For a reordered element
// the write landed on the wrong bytes — `tweak(&mut a){ a[0].1 += 1000 }` left
// `a[0].1` unchanged (the write hit the padding region) — a silent wrong value at
// -Copt-level 0 AND 3. A 2-field `(u8, u64)` element (which rustc does NOT reorder)
// worked, masking the bug.
//
// THE FIX (in rustc-codegen-trust-cg/src/lib.rs). `memory_aggregate_ref_pointee`
// now routes a `&`/`&mut [T; N]` array reference (whose element is a fixed-offset
// all-scalar-leaf aggregate) through the rustc-layout byte-offset walker
// (`memory_aggregate_ref_address` -> `walk_memory_projection_runtime_address`),
// which resolves the element stride and the field offset via rustc's `layout_of` —
// identical to how the array's storage was written. Scoped to ARRAY pointees: a
// by-ref struct arg of a scalarized local is materialized at declaration order and
// is internally consistent there, so it is left unchanged.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 0 and 3; each reduction over the array is ASYMMETRIC so a
// dropped or misplaced field write changes the result. `core::hint::black_box`
// keeps every element value materialized at runtime.

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m73 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m73_{stem}_{}", std::process::id()));
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

fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> i32 {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

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
    assert!(
        output.status.success(),
        "{stem} (opt={opt}, backend={}): failed to compile. stderr: <<<{stderr}>>>",
        if dylib.is_some() { "trust-cg" } else { "llvm" }
    );

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

/// The canonical #73 repro: write `a[0].1` (the u64, which rustc places at offset 0)
/// through `&mut [(u8,u64,u16);2]`, then read it back. Before the fix the write was
/// dropped and the readback returned the original value (2 instead of 1002).
#[test]
fn m73_array_of_reordered_tuple_mut_field_write_matches_llvm() {
    differential_program(
        "tuple_mut",
        "#[inline(never)] fn tweak(a: &mut [(u8, u64, u16); 2]) { \
            a[0].1 = a[0].1.wrapping_add(1000); }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut a: [(u8,u64,u16);2] = [(bb(1),bb(2),bb(3)), (bb(4),bb(5),bb(6))]; \
            tweak(&mut a); (a[0].1 & 0xff) as i32 }",
        // 2 + 1000 = 1002; 1002 & 0xff = 234
        234,
    );
}

/// The full fuzz repro: three elements, three different field mutations, asymmetric
/// weighted reduction over every field.
#[test]
fn m73_array_of_reordered_tuple_full_repro_matches_llvm() {
    differential_program(
        "tuple_full",
        "#[inline(never)] fn tweak(a: &mut [(u8, u64, u16); 3]) { \
            a[0].1 = a[0].1.wrapping_add(1000); \
            a[1].0 = a[1].0.wrapping_add(5); \
            a[2].2 = a[2].2.wrapping_mul(2); }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut a: [(u8,u64,u16);3] = [(bb(1),bb(2),bb(3)),(bb(4),bb(5),bb(6)),(bb(7),bb(8),bb(9))]; \
            tweak(&mut a); \
            let mut acc: i64 = 0; let mut i = 0usize; \
            let wa: [i64;3]=[1,31,61]; let wb: [i64;3]=[7,37,67]; let wc: [i64;3]=[13,43,73]; \
            while i < 3 { acc = acc.wrapping_add(a[i].0 as i64 * wa[i]); \
                acc = acc.wrapping_add(a[i].1 as i64 * wb[i]); \
                acc = acc.wrapping_add(a[i].2 as i64 * wc[i]); i += 1; } \
            ((acc as i32) & 0xff) as i32 }",
        69,
    );
}

/// An array of reordered STRUCTS (not tuples) mutated through `&mut [S; 2]`.
#[test]
fn m73_array_of_reordered_struct_mut_field_write_matches_llvm() {
    differential_program(
        "struct_mut",
        "#[derive(Clone,Copy)] struct S { a: u8, b: u64, c: u16 }\n\
         #[inline(never)] fn tw(a: &mut [S; 2]) { \
            a[0].b = a[0].b.wrapping_add(50); a[1].a = a[1].a.wrapping_add(9); }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut a = [S{a:bb(1),b:bb(2),c:bb(3)}, S{a:bb(4),b:bb(5),c:bb(6)}]; \
            tw(&mut a); \
            let mut acc=0i64; let mut i=0; let w:[i64;6]=[1,7,13,17,23,29]; \
            while i<2 { acc=acc.wrapping_add(a[i].a as i64*w[i*3]); \
                acc=acc.wrapping_add(a[i].b as i64*w[i*3+1]); \
                acc=acc.wrapping_add(a[i].c as i64*w[i*3+2]); i+=1; } \
            ((acc as i32)&0xff) as i32 }",
        146,
    );
}

/// Read-only `&[(u8,u64,u16); N]` field reads through the shared reference.
#[test]
fn m73_array_of_reordered_tuple_shared_field_read_matches_llvm() {
    differential_program(
        "tuple_read",
        "#[inline(never)] fn rd(a: &[(u8,u64,u16); 2]) -> i64 { \
            let mut acc=0i64; let mut i=0; let w:[i64;6]=[1,7,13,17,23,29]; \
            while i<2 { acc=acc.wrapping_add(a[i].0 as i64*w[i*3]); \
                acc=acc.wrapping_add(a[i].1 as i64*w[i*3+1]); \
                acc=acc.wrapping_add(a[i].2 as i64*w[i*3+2]); i+=1; } acc }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a: [(u8,u64,u16);2] = [(bb(1),bb(2),bb(3)),(bb(4),bb(5),bb(6))]; \
            ((rd(&a) as i32) & 0xff) as i32 }",
        // 1*1+2*7+3*13 + 4*17+5*23+6*29 = 54 + 357 = 411; 411 & 0xff = 155
        411 & 0xff,
    );
}
