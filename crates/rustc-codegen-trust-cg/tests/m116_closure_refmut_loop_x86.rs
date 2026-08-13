// Differential regression test for the CLOSURE-&mut-IN-A-LOOP reference-escape
// miscompile family (a SILENT WRONG VALUE at O3) and its proper de-scalarize fix.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. A closure taking a `&mut` parameter, called inside a loop, has its
// body INLINED at O3 — leaving a bare `*r = ..` store-through with NO Call
// terminator. The bridge's loop-carried-`&mut` detection keys on a Call def-site,
// so the inlined store was missed: the borrowed-scalar SNAPSHOT model kept the
// referent's ENTRY value and dropped the in-loop writeback across the back-edge.
//   * scalar referent (`let mut acc=0; let mut f=|r:&mut i64,v|{*r+=v};
//     while.. { f(&mut acc,i); }`): acc stayed 0 at O3 (LLVM 45) — a silent miscompile.
//   * aggregate referent (`&mut s.field` / `&mut a[i]`): the struct field / array
//     element stayed at its init value at O3 — same silent miscompile.
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs, three parts):
//   1. `compute_scalar_cell_locals`: cell a primitive-scalar local whose `&mut` is
//      STORED-THROUGH (`*r = v`) inside a loop (not just one reaching a Call) — the
//      closure-inlined no-Call form. The cell gives `&mut x` a real slot address.
//   2. `compute_memory_backed_locals` (4a-#81): the same, one level up — memory-back
//      the BASE aggregate of a `&mut s.field` / `&mut a[i]` stored-through in a loop.
//   3. `Rvalue::Ref` lowering: a DIRECT projected borrow of a MEMORY-BACKED base is
//      lowered to a real field/element GEP (`memory_place_address`) instead of the
//      borrowed-scalar snapshot, so the store-through lands and reads observe it.
// Celling / memory-backing is semantically inert (reads/writes route through the
// slot), and the GEP arm fires ONLY for a memory-backed base (where the snapshot
// path already failed), so no working case is perturbed.
//
// OUTCOME. The closure-&mut-in-a-loop shapes COMPILE to the CORRECT value at O3 (a
// closure body is not lowerable at O0 — `Rvalue::Ref of unsupported closure` — so
// the closure shapes FAIL CLOSED at O0, never a wrong value). The plain-fn and
// direct-mutation controls MATCH at BOTH opt levels. The invariant enforced here is
// MATCH-OR-FAIL-CLOSED at both opt levels, plus exact-MATCH at O3 for the closure
// shapes and at both levels for the controls.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 0 and 3. Each program READS BACK the mutated state through
// a modulus, so a dropped/stale store-through changes the exit. `black_box` keeps
// the seed inputs live so the accumulation is not const-folded away.

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
    assert!(status.success(), "cargo build failed; cannot run m116 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m116_{stem}_{}", std::process::id()));
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
    Exit(i32),
    /// The bridge failed to compile / link (fail-closed). Only trust-cg may fail
    /// closed; LLVM must always compile.
    FailedClosed,
}

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

/// MATCH-OR-FAIL-CLOSED at BOTH opt levels; `must_match_o3` additionally REQUIRES an
/// exact O3 match (the closure shapes compile correctly at O3, fail closed at O0).
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
                 (closure-&mut-in-loop MISCOMPILE)"
            ),
            Outcome::FailedClosed => assert!(
                !(must_match_o3 && opt == "3"),
                "{stem} (opt=3): trust-cg unexpectedly failed closed (must compile correctly)"
            ),
        }
    }
}

/// Exact MATCH at BOTH opt levels (the plain-fn / direct-mutation controls).
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
// CLOSURE-&mut-IN-A-LOOP repros — compile CORRECTLY at O3 (fail closed at O0 on the
// unsupported-closure-Ref limitation), never a wrong value.
// ───────────────────────────────────────────────────────────────────────────

/// Scalar referent: `f(&mut acc, i)` accumulating in a loop. acc = 0+..+9 = 45.
/// Was acc==0 at O3 (dropped store) before the scalar-cell store-through fix.
#[test]
fn closure_refmut_scalar_in_loop() {
    match_or_fail_closed(
        "closure_scalar",
        "#[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut acc: i64 = bb(0); \
            let mut f = |r:&mut i64, v:i64| { *r = r.wrapping_add(v); }; \
            let mut i: i64 = 0; \
            while i < 10 { f(&mut acc, i); i += 1; } \
            (acc % 126) as i32 }",
        45,
        true,
    );
}

/// Struct-field referent: `f(&mut s.a, i)` in a loop. s.a = 0+..+10 = 55. Was s.a==0
/// at O3 before the aggregate memory-backing + memory-backed-field-GEP fix.
#[test]
fn closure_refmut_struct_field_in_loop() {
    match_or_fail_closed(
        "closure_field",
        "struct S{a:i32,b:i32}\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut s = S{a:bb(0), b:bb(0)}; \
            let mut f = |r:&mut i32, v:i32| { *r = r.wrapping_add(v); }; \
            let mut i: i32 = 0; \
            while i < 11 { f(&mut s.a, i); i += 1; } \
            (s.a % 126) as i32 }",
        55,
        true,
    );
}

/// Two struct fields updated conditionally via the closure in a loop.
/// a=0+2+4+6+8=20, b=1+3+5+7+9=25, exit = a*2+b = 65.
#[test]
fn closure_refmut_two_fields_conditional_in_loop() {
    match_or_fail_closed(
        "closure_two_fields",
        "struct S{a:i64,b:i64}\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut s = S{a:bb(0), b:bb(0)}; \
            let mut f = |r:&mut i64, v:i64| { *r += v; }; \
            let mut i: i64 = 0; \
            while i < 10 { if i % 2 == 0 { f(&mut s.a, i); } else { f(&mut s.b, i); } i += 1; } \
            ((s.a * 2 + s.b) % 126) as i32 }",
        65,
        true,
    );
}

/// Array-element referent: `f(&mut a[k%5], k)` in a loop. Per-bucket sums total 190;
/// 190 % 126 = 64. Was the array unchanged at O3 before the fix.
#[test]
fn closure_refmut_array_elem_in_loop() {
    match_or_fail_closed(
        "closure_array",
        "#[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut a = [bb(0i64); 5]; \
            let mut f = |r:&mut i64, v:i64| { *r = r.wrapping_add(v); }; \
            let mut k: i64 = 0; \
            while k < 20 { f(&mut a[(k % 5) as usize], k); k += 1; } \
            let mut s: i64 = 0; let mut j = 0; \
            while j < 5 { s = s.wrapping_add(a[j]); j += 1; } \
            (s % 126) as i32 }",
        64,
        true,
    );
}

/// Nested struct field `&mut o.inner.x` via the closure in a loop. 0+..+10 = 55.
#[test]
fn closure_refmut_nested_field_in_loop() {
    match_or_fail_closed(
        "closure_nested",
        "struct Inner{x:i32,y:i32} struct Outer{inner:Inner, t:i64}\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut o = Outer{inner:Inner{x:bb(0), y:bb(0)}, t:bb(0)}; \
            let mut f = |r:&mut i32, v:i32| { *r = r.wrapping_add(v); }; \
            let mut i: i32 = 0; \
            while i < 11 { f(&mut o.inner.x, i); i += 1; } \
            (o.inner.x % 126) as i32 }",
        55,
        true,
    );
}

// ───────────────────────────────────────────────────────────────────────────
// CONTROLS — must MATCH at BOTH opt levels (no regression from the cell /
// memory-backing / GEP passes).
// ───────────────────────────────────────────────────────────────────────────

/// Plain `#[inline(never)] fn` taking `&mut scalar`, called in a loop. The Call
/// terminator already makes the referent a celled loop-carried local. acc = 45.
#[test]
fn control_plain_fn_refmut_scalar_in_loop() {
    matches_both_opts(
        "ctrl_fn_scalar",
        "#[inline(never)] fn add(r:&mut i64, v:i64){ *r = r.wrapping_add(v); }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut acc: i64 = bb(0); let mut i: i64 = 0; \
            while i < 10 { add(&mut acc, i); i += 1; } \
            (acc % 126) as i32 }",
        45,
    );
}

/// Plain `#[inline(never)] fn` taking `&mut s.field`, called in a loop. Now compiles
/// at BOTH opt levels (memory-backed base + field GEP). s.a = 55.
#[test]
fn control_plain_fn_refmut_field_in_loop() {
    matches_both_opts(
        "ctrl_fn_field",
        "struct S{a:i32,b:i32}\n\
         #[inline(never)] fn add(r:&mut i32, v:i32){ *r = r.wrapping_add(v); }\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut s = S{a:bb(0), b:bb(0)}; let mut i: i32 = 0; \
            while i < 11 { add(&mut s.a, i); i += 1; } \
            (s.a % 126) as i32 }",
        55,
    );
}

/// Direct field mutation (no fn/closure) in a loop — the existing scalarized path.
/// NO reference is taken, so the memory-backing/GEP passes do NOT fire and the struct
/// stays scalarized: at O0 this is a loop-carried scalarized aggregate with no header
/// phi, which the bridge correctly FAILS CLOSED on (TCG-MIR-UNSUPPORTED, documented
/// safe — never a wrong value). At O3 the optimizer lifts `s.a` into an SSA loop
/// variable, so it compiles to the correct value. The invariant: match-or-fail-closed,
/// with an exact O3 match. s.a = 0+..+10 = 55. (This pins that the closure-&mut fix did
/// not silently start mis-COMPILING the unreferenced direct-mutation path.)
#[test]
fn control_direct_field_mutation_in_loop() {
    match_or_fail_closed(
        "ctrl_direct_field",
        "struct S{a:i32,b:i32}\n\
         #[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut s = S{a:bb(0), b:bb(0)}; let mut i: i32 = 0; \
            while i < 11 { s.a = s.a.wrapping_add(i); i += 1; } \
            (s.a % 126) as i32 }",
        55,
        true,
    );
}

/// Plain scalar accumulator in a loop (no fn, no closure, no reference) — the canonical
/// loop-carried scalar with a header phi. This ALWAYS compiles at both opt levels and is
/// the genuine no-regression anchor: the cell / memory-backing / GEP passes must leave
/// the ordinary scalarized loop path completely unperturbed. acc = 0+..+9 = 45.
#[test]
fn control_direct_scalar_accumulator_in_loop() {
    matches_both_opts(
        "ctrl_scalar_acc",
        "#[no_mangle] pub extern \"C\" fn main()->i32{ \
            let mut acc: i64 = bb(0); let mut i: i64 = 0; \
            while i < 10 { acc = acc.wrapping_add(i); i += 1; } \
            (acc % 126) as i32 }",
        45,
    );
}
