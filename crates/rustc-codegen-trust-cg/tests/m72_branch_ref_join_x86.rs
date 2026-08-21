#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential regression test for MISCOMPILE #72: a `&mut` to a control-flow
// join (a branch-varying mutable reference) silently dropped the write.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. A scalar local whose address is taken (`&mut a`) is normally NOT
// memory-backed; the bridge models the reference with a "borrowed scalar"
// SNAPSHOT — it records the borrowed *value* at the point of the borrow, not a
// runtime address. That snapshot is sound only while the reference statically
// names ONE local. When a reference is assembled across control flow
// (`let rp = match c { 0 => &mut a, _ => &mut b }`) it is BRANCH-VARYING: at
// runtime it holds the address of either `a` or `b`. The snapshot model collapses
// the merge to the reference local itself (`preserve_self_borrow`), so a
// `*rp = 9` store updated only the snapshot and the underlying `a`/`b` stayed
// stale — a silent wrong value at -Copt-level 0 AND 3 (`a` read back as its
// initial value).
//
// THE FIX (in `rustc-codegen-trust-cg/src/lib.rs`). `compute_scalar_cell_locals`
// now detects a branch-varying mutable reference — one reference local that can
// address two or more distinct scalar leaves, propagated across reference copies
// to a fixpoint — and CELLS every such referent (a stack slot, like a
// closure-captured scalar). `&mut a` then binds the reference to the cell pointer
// (re-typed through a `Copy` to the reference's own trust-ir type so a
// branch-varying phi accepts it), the match becomes an ordinary pointer phi,
// `*rp = v` is a real store, and a later direct read of `a`/`b` reloads from the
// cell. `lower_operand` gained the same scalar-cell read intercept that
// `lower_operand_to_value` already had, so a whole-local read of a celled scalar
// is a typed `Load` rather than a copy of an undefined SSA value.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend, at -Copt-level 0 and 3. `core::hint::black_box` defeats const-folding
// so the branch and the store are materialized as real runtime instructions.

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
    assert!(status.success(), "cargo build failed; cannot run m72 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m72_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Write a C file with `abort()` stubs for every undefined `panic*` symbol the
/// object references, so the object links standalone.
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

/// Compile `src` (with the given backend), link with abort stubs, run, and
/// return the process exit code.
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
    assert!(
        !objs.is_empty(),
        "{stem} (opt={opt}): no object file produced"
    );

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

/// Compile `body` with BOTH backends at -Copt-level 0 and 3 and require the
/// trust-cg exit code to equal the LLVM exit code AND the documented `expected`.
fn differential_case(stem: &str, body: &str, expected: i32) {
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
         use core::hint::black_box as bb;\n\
         #[no_mangle]\npub extern \"C\" fn main() -> i32 {{\n{body}\n}}\n"
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

/// The canonical #72 repro: a 2-way `match` selects `&mut a` / `&mut b`, the
/// store through it must hit `a` (the selected local) and a later direct read of
/// `a` must observe it. Before the fix trust-cg returned the initial value `1`.
#[test]
fn m72_match_select_store_reads_underlying_matches_llvm() {
    differential_case(
        "match_underlying",
        "    let mut a: i64 = bb(1);\n\
         \x20   let mut b: i64 = bb(2);\n\
         \x20   let rp: &mut i64 = match bb(0i32) { 0 => &mut a, _ => &mut b };\n\
         \x20   *rp = 9;\n\
         \x20   ((a + b) & 0xFF) as i32",
        11,
    );
}

/// The OTHER selection arm: `bb(1)` picks `&mut b`, so the store must land on
/// `b` and leave `a` untouched.
#[test]
fn m72_match_select_other_arm_matches_llvm() {
    differential_case(
        "match_other_arm",
        "    let mut a: i64 = bb(1);\n\
         \x20   let mut b: i64 = bb(2);\n\
         \x20   let rp: &mut i64 = match bb(1i32) { 0 => &mut a, _ => &mut b };\n\
         \x20   *rp = 9;\n\
         \x20   ((a * 100 + b) & 0xFFFF) as i32",
        109,
    );
}

/// A 3-way `match` among three distinct scalars; `bb(2)` selects `&mut c`.
#[test]
fn m72_threeway_match_matches_llvm() {
    differential_case(
        "threeway",
        "    let mut a: i64 = bb(1);\n\
         \x20   let mut b: i64 = bb(2);\n\
         \x20   let mut c: i64 = bb(3);\n\
         \x20   let rp: &mut i64 = match bb(2i32) { 0 => &mut a, 1 => &mut b, _ => &mut c };\n\
         \x20   *rp = 9;\n\
         \x20   ((a + b * 10 + c * 100) & 0xFFFF) as i32",
        // 1 + 2*10 + 9*100 = 921; the process exit code is the low 8 bits: 921 & 0xFF.
        921 & 0xFF,
    );
}

/// An `if`/`else` selected narrow (`u8`) reference: width-correct cell load/store.
#[test]
fn m72_if_select_u8_matches_llvm() {
    differential_case(
        "if_u8",
        "    let mut a: u8 = bb(10);\n\
         \x20   let mut b: u8 = bb(20);\n\
         \x20   let rp: &mut u8 = if bb(1i32) != 0 { &mut a } else { &mut b };\n\
         \x20   *rp = 99;\n\
         \x20   (a as i32) + (b as i32)",
        119,
    );
}

/// Read-modify-write through the branch-varying reference, then read BOTH
/// underlying locals (`a` updated, `b` untouched).
#[test]
fn m72_read_modify_write_then_read_both_matches_llvm() {
    differential_case(
        "rmw_both",
        "    let mut a: i32 = bb(5);\n\
         \x20   let mut b: i32 = bb(7);\n\
         \x20   let rp: &mut i32 = if bb(0i32) != 0 { &mut a } else { &mut b };\n\
         \x20   *rp = *rp + 100;\n\
         \x20   (a * 1000 + b) & 0xFFFF",
        // bb(0)!=0 is false -> rp=&mut b; b=7+100=107; 5*1000+107 = 5107; exit = 5107 & 0xFF.
        5107 & 0xFF,
    );
}

/// The branch-varying `&mut` ESCAPES into a tuple and is dereferenced THROUGH the
/// tuple — the escaped reference still names the selected local's storage.
#[test]
fn m72_escape_into_tuple_then_deref_matches_llvm() {
    differential_case(
        "escape_deref",
        "    let mut left: i64 = bb(11);\n\
         \x20   let mut right: i64 = bb(29);\n\
         \x20   let selected: &mut i64 = if bb(0i32) != 0 { &mut right } else { &mut left };\n\
         \x20   let escaped = (selected,);\n\
         \x20   *escaped.0 = 7;\n\
         \x20   ((left * 100 + right) & 0xFFFF) as i32",
        729 & 0xFF,
    );
}
