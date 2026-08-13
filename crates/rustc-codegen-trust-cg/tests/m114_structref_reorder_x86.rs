// Differential regression test for the STRUCT-REORDER-THROUGH-REFERENCE miscompile:
// a struct rustc REORDERS (a small field declared before a wider one, so descending-
// alignment layout moves the wide field to offset 0) accessed THROUGH a reference
// (`&S` / `&mut S`) read/wrote its fields at DECLARATION byte offsets instead of
// rustc LAYOUT offsets — but ONLY when the struct's bytes were actually produced in
// rustc layout order (a by-value return into a borrowed local, or a `&mut`-writeback
// memory-backed slot). Every field then landed at the wrong byte: a SILENT wrong
// value.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. A `&S` reference pointee was represented as a DECLARATION-ORDER
// trust-ir tuple; the callee read/wrote `(*r).field` by that tuple's lane offset.
// That is internally consistent ONLY when the bytes were ALSO materialized in
// declaration order — which holds for a SCALARIZED source (`let s = S{..}; rd(&s)`
// materializes a fresh declaration-order slot). But a struct RETURNED BY VALUE, or
// mutated through `&mut` in a loop, is MEMORY-BACKED in rustc layout order, and the
// declaration-order access then read every field at the wrong offset.
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs). `memory_aggregate_ref_pointee` now
// fires for a REORDERED scalar-leaf struct/tuple pointee, routing `(*r).field…`
// read/write through the rustc-layout byte-offset walker (`walk_memory_projection_
// offset`, which resolves each field via `cur_layout.fields.offset(i)`). The
// borrowed reordered source local is additionally forced MEMORY-BACKED
// (`compute_memory_backed_locals` case 4b) so its bytes ARE laid out in rustc order
// — materialization and access now AGREE on rustc layout. A struct rustc keeps in
// DECLARATION order (`{u64,u8,u8}`, `repr(C)`, same-alignment fields) has identical
// declaration and rustc offsets, so it is UNCHANGED on the existing scalarized path
// (no working case is perturbed).
//
// OUTCOME. Every reordered-struct-through-reference shape that the bridge compiles
// is now CORRECT. The `&mut`-writeback-IN-A-LOOP shape (repro 2/3) additionally
// trips a PRE-EXISTING, unrelated O0 loop-iterator lowering limitation
// (`RangeIteratorImpl::spec_next`: "Rvalue::Ref source projection is not scalar-
// bindable") — confirmed identical for a NON-reordered struct in the same loop — so
// it FAILS CLOSED at O0 (no binary) rather than producing a wrong value, and is
// CORRECT at O3. The invariant this test enforces is therefore MATCH-OR-FAIL-CLOSED
// (never a wrong value) at both opt levels, plus exact-MATCH for the non-loop repros
// and the reorder controls.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 0 and 3. Each reader uses an ASYMMETRIC reduction over the
// fields so a field swap changes the result. `core::hint::black_box` keeps the
// struct materialized at runtime.

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
    assert!(status.success(), "cargo build failed; cannot run m114 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m114_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn write_panic_stubs(dir: &Path, objs: &[PathBuf]) -> PathBuf {
    let mut nm = Command::new("nm");
    nm.arg("-u");
    for obj in objs {
        nm.arg(obj);
    }
    let nm = nm.output().expect("nm");
    let mut seen = std::collections::BTreeSet::new();
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if sym.contains("panic") && seen.insert(sym.to_owned()) {
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

/// The outcome of compiling+running one program with one backend.
enum Outcome {
    /// Exit code of the run binary.
    Exit(i32),
    /// The backend failed to compile / link the program (fail-closed). Only the
    /// trust-cg backend may fail closed; LLVM must always compile.
    FailedClosed,
}

/// Compile a FULL `#![no_std] #![no_main]` program `body` (after the shared
/// preamble) with the given backend at `opt`, link with abort stubs, run, and
/// return the outcome. A trust-cg COMPILE or LINK failure is reported as
/// `FailedClosed` (a safe coverage gap); LLVM must always succeed.
fn compile_link_run(stem: &str, body: &str, opt: &str, dylib: Option<&Path>) -> Outcome {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    let src = format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box as bb;\n{body}\n"
    );
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
        cmd.env("TCG_NO_PROOF_CERTS", "1");
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    if !output.status.success() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!(
            "{stem} (opt={opt}, LLVM): failed to compile. stderr: <<<{}>>>",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    if objs.is_empty() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!("{stem} (opt={opt}, LLVM): no object file produced");
    }

    let stubs_path = write_panic_stubs(&dir, &objs);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    if !link.status.success() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!(
            "{stem} (opt={opt}, LLVM): link failed. stderr: <<<{}>>>",
            String::from_utf8_lossy(&link.stderr)
        );
    }

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    Outcome::Exit(run.status.code().expect("process terminated by signal"))
}

/// MATCH-OR-FAIL-CLOSED invariant at BOTH opt levels: at each of -Copt-level 0 and
/// 3, the LLVM oracle exits `expected`, and trust-cg either matches it exactly OR
/// fails closed (never a wrong value). `must_match_o3` additionally REQUIRES an
/// exact match at O3 (for shapes the bridge fully supports there).
fn match_or_fail_closed(stem: &str, body: &str, expected: i32, must_match_o3: bool) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    for opt in ["0", "3"] {
        let llvm = match compile_link_run(stem, body, opt, None) {
            Outcome::Exit(code) => code,
            Outcome::FailedClosed => unreachable!("LLVM never fails closed"),
        };
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        match compile_link_run(stem, body, opt, Some(&dylib)) {
            Outcome::Exit(trust) => assert_eq!(
                trust, llvm,
                "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} \
                 (struct-reorder-through-reference MISCOMPILE)"
            ),
            Outcome::FailedClosed => {
                assert!(
                    !(must_match_o3 && opt == "3"),
                    "{stem} (opt=3): trust-cg unexpectedly failed closed (must support this shape)"
                );
            }
        }
    }
}

/// Exact MATCH at BOTH opt levels (for shapes the bridge fully supports).
fn matches_both_opts(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    for opt in ["0", "3"] {
        let llvm = match compile_link_run(stem, body, opt, None) {
            Outcome::Exit(code) => code,
            Outcome::FailedClosed => unreachable!(),
        };
        assert_eq!(llvm, expected, "{stem} (opt={opt}): LLVM oracle {llvm} != expected {expected}");
        match compile_link_run(stem, body, opt, Some(&dylib)) {
            Outcome::Exit(trust) => assert_eq!(
                trust, llvm,
                "{stem} (opt={opt}): trust-cg {trust} != LLVM {llvm} (miscompile)"
            ),
            Outcome::FailedClosed => panic!(
                "{stem} (opt={opt}): trust-cg unexpectedly failed closed (must support this shape)"
            ),
        }
    }
}

// ───────────────────────────────────────────────────────────────────────────
// THE 3 CONFIRMED REPROS (match-or-fail-closed, never wrong).
// ───────────────────────────────────────────────────────────────────────────

/// Repro 1: `Q{a:u8,b:u64,c:u8}` (rustc moves `b` to offset 0) RETURNED BY VALUE,
/// then read through `&Q`. The return slot is rustc-ordered; the declaration-order
/// read mis-read every field. Now CORRECT at both opt levels (no loop). LLVM=60.
#[test]
fn repro1_return_by_value_then_borrow() {
    matches_both_opts(
        "repro1_ret_borrow",
        "#[inline(never)] fn bbn<T>(x:T)->T{ bb(x) }\n\
         struct Q{a:u8,b:u64,c:u8}\n\
         #[inline(never)] fn mk()->Q{ Q{a:bbn(9),b:bbn(40),c:bbn(2)} }\n\
         #[inline(never)] fn rd(q:&Q)->u64{ q.a as u64 * 2 + q.b + q.c as u64 }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ let q=mk(); ((rd(&q))%126) as i32 }",
        60,
    );
}

/// Repro 2: `S{a:u8,b:u64,c:u16}` mutated through `&mut S` in a loop. The slot is
/// rustc-ordered; the declaration-order write mis-placed the accumulation. CORRECT
/// at O3; FAILS CLOSED at O0 (pre-existing loop-iterator limitation — never wrong).
/// LLVM=50.
#[test]
fn repro2_mut_writeback_in_loop() {
    match_or_fail_closed(
        "repro2_mut_loop",
        "struct S{a:u8,b:u64,c:u16}\n\
         #[inline(never)] fn xfer(s:&mut S){ s.b += s.a as u64 + s.c as u64; }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ let mut s=S{a:bb(20),b:bb(0),c:bb(30)}; \
            for _ in 0..bb(1){ xfer(&mut s); } (s.b%126) as i32 }",
        50,
        true,
    );
}

/// Repro 3: `Flag{on:bool,count:u64,tag:u8}` conditionally accumulated through
/// `&mut` in a loop — same root cause. CORRECT at O3; fail-closed at O0. LLVM=35.
#[test]
fn repro3_flag_conditional_accumulate_loop() {
    match_or_fail_closed(
        "repro3_flag_loop",
        "struct Flag{on:bool,count:u64,tag:u8}\n\
         #[inline(never)] fn step(f:&mut Flag){ if f.on { f.count += f.tag as u64; } }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut f=Flag{on:bb(true),count:bb(0u64),tag:bb(7u8)}; \
            for _ in 0..bb(5){ step(&mut f); } (f.count%126) as i32 }",
        35,
        true,
    );
}

// ───────────────────────────────────────────────────────────────────────────
// REORDERED-STRUCT-THROUGH-REFERENCE shapes the bridge fully supports (exact MATCH).
// ───────────────────────────────────────────────────────────────────────────

/// `&S` READ of a reordered `{bool,u64,u16}` returned by value. LLVM=45.
#[test]
fn ref_read_bool_u64_u16_returned() {
    matches_both_opts(
        "ref_read_b_u64_u16",
        "struct S{a:bool,b:u64,c:u16}\n\
         #[inline(never)] fn mk()->S{ S{a:bb(true),b:bb(40),c:bb(2)} }\n\
         #[inline(never)] fn rd(s:&S)->u64{ (s.a as u64)*3 + s.b + s.c as u64 }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ let s=mk(); (rd(&s)%126) as i32 }",
        45,
    );
}

/// `&mut S` WRITE (no loop) of a reordered `{u8,u64,u16}`. LLVM=50.
#[test]
fn ref_mut_write_u8_u64_u16_no_loop() {
    matches_both_opts(
        "ref_mut_u8_u64_u16",
        "struct S{a:u8,b:u64,c:u16}\n\
         #[inline(never)] fn wr(s:&mut S){ s.b = s.a as u64 + s.c as u64; }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut s=S{a:bb(20),b:bb(0),c:bb(30)}; wr(&mut s); (s.b%126) as i32 }",
        50,
    );
}

/// Four-field reorder `{u8,u32,u8,u64}` returned by value, asymmetric reduction.
/// rustc orders `d@0,b@8,a@12,c@13`. LLVM=76.
#[test]
fn ref_read_u8_u32_u8_u64_quad() {
    matches_both_opts(
        "ref_read_quad",
        "struct S{a:u8,b:u32,c:u8,d:u64}\n\
         #[inline(never)] fn mk()->S{ S{a:bb(1),b:bb(2),c:bb(3),d:bb(4)} }\n\
         #[inline(never)] fn rd(s:&S)->u64{ s.a as u64 + s.b as u64*5 + s.c as u64*7 + s.d*11 }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ let s=mk(); (rd(&s)%126) as i32 }",
        76,
    );
}

/// Signed reordered `{i16,i64,i8}` read by reference. LLVM=48.
#[test]
fn ref_read_i16_i64_i8_signed() {
    matches_both_opts(
        "ref_read_signed",
        "struct S{a:i16,b:i64,c:i8}\n\
         #[inline(never)] fn mk()->S{ S{a:bb(3),b:bb(40),c:bb(2)} }\n\
         #[inline(never)] fn rd(s:&S)->i64{ s.a as i64*2 + s.b + s.c as i64 }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ let s=mk(); (rd(&s)%126) as i32 }",
        48,
    );
}

// ───────────────────────────────────────────────────────────────────────────
// CONTROLS: NON-reordered structs (declaration order == rustc order) — must stay
// EXACT MATCH on the unchanged scalarized path (no regression, no new fail-closed).
// ───────────────────────────────────────────────────────────────────────────

/// `{u64,u8,u8}` is already in descending-alignment (declaration) order — rustc
/// does NOT reorder it, so it stays on the existing scalarized reference path. LLVM=60.
#[test]
fn control_non_reordered_u64_u8_u8() {
    matches_both_opts(
        "ctrl_u64_u8_u8",
        "struct S{a:u64,b:u8,c:u8}\n\
         #[inline(never)] fn mk()->S{ S{a:bb(40),b:bb(9),c:bb(2)} }\n\
         #[inline(never)] fn rd(s:&S)->u64{ s.a + s.b as u64*2 + s.c as u64 }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ let s=mk(); (rd(&s)%126) as i32 }",
        60,
    );
}

/// `repr(C)` PINS declaration order, so even `{u8,u64,u8}` is NOT reordered and must
/// keep the existing path with correct results. LLVM=60.
#[test]
fn control_repr_c_u8_u64_u8() {
    matches_both_opts(
        "ctrl_repr_c",
        "#[repr(C)] struct S{a:u8,b:u64,c:u8}\n\
         #[inline(never)] fn mk()->S{ S{a:bb(9),b:bb(40),c:bb(2)} }\n\
         #[inline(never)] fn rd(s:&S)->u64{ s.a as u64*2 + s.b + s.c as u64 }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ let s=mk(); (rd(&s)%126) as i32 }",
        60,
    );
}

/// All-same-alignment `{u32,u32,u32}` — rustc keeps declaration order. LLVM=44.
#[test]
fn control_same_alignment_u32x3() {
    matches_both_opts(
        "ctrl_same_align",
        "struct S{a:u32,b:u32,c:u32}\n\
         #[inline(never)] fn mk()->S{ S{a:bb(10),b:bb(20),c:bb(14)} }\n\
         #[inline(never)] fn rd(s:&S)->u32{ s.a + s.b + s.c }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ let s=mk(); (rd(&s)%126) as i32 }",
        44,
    );
}

/// Control `&mut` write (no loop) on a NON-reordered struct `{u64,u8,u16}`. LLVM=50.
#[test]
fn control_non_reordered_mut_write() {
    matches_both_opts(
        "ctrl_mut_write",
        "struct S{a:u64,b:u8,c:u16}\n\
         #[inline(never)] fn wr(s:&mut S){ s.a = s.b as u64 + s.c as u64; }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut s=S{a:bb(0),b:bb(20),c:bb(30)}; wr(&mut s); (s.a%126) as i32 }",
        50,
    );
}
