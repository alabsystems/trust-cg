// Differential regression test for MISCOMPILE #69: a by-value struct whose fields
// rustc REORDERS was passed with the fields in declaration order, so the callee
// (which reads each field at rustc's byte offset) saw every field wrong.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. rustc lays out a non-`repr(C)` struct's fields in descending
// alignment order, not declaration order: `struct S { a: i32, b: f64 }` becomes
// `b @ 0, a @ 8`. A by-value memory-backed callee parameter reads each field at
// that rustc byte offset. But when the caller's struct value is SCALARIZED (held
// as separate per-field SSA values, the common `let s = S {..}; f(s);` case), the
// bridge materialized the by-value argument slot from a flat DECLARATION-ORDER
// trust-ir tuple (`aggregate_reference_pointee_to_trust_ir_ty`), placing projected
// field `i` at lane `i`. For a reordered struct the lanes disagreed with the
// callee's rustc offsets and every field was read from the wrong place (silent
// wrong value at -Copt-level 0 AND 3). The earlier "mixed INTEGER+SSE eightbyte"
// framing was a red herring — an all-integer reordered struct (`{u8,u32,u16}`)
// miscompiled identically; `{i32,f64}` is simply the smallest case rustc reorders.
//
// THE FIX (in rustc-codegen-trust-cg/src/lib.rs `pack_scalarized_aggregate_byval_slot`).
// Pack each scalar-leaf projected field at its rustc BYTE offset
// (`variant.fields.offset(i)`) into a fresh `slot_ty` lane slot, exactly as the
// memory-backed callee reads it. (`repr(C)` structs and already-ordered structs
// were unaffected and remain correct; a nested-aggregate-field struct still fails
// closed, a pre-existing coverage gap.)
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 0 and 3; each `use_s` uses an ASYMMETRIC reduction over
// the fields so a field swap changes the result. `core::hint::black_box` keeps the
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
    assert!(status.success(), "cargo build failed; cannot run m80 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m80_{stem}_{}", std::process::id()));
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

/// Compile a FULL program `src` (with the given backend), link with abort stubs,
/// run, and return the process exit code.
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

/// Compile a complete `#![no_std] #![no_main]` program with BOTH backends at
/// -Copt-level 0 and 3 and require the trust-cg exit code to equal the LLVM exit
/// code AND the documented `expected` (process exit codes are 8-bit).
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


// #80: a `&mut local` passed to a fn inside a loop dropped the writeback — the
// scalarized model reloaded the local after the call but did not thread that reload
// across the loop back-edge, so the local stayed at its initial value. The fix cells
// a scalar whose mutable `&mut` escapes to a call (a stable in-memory home the callee
// mutates in place). (A `&mut s.a` field reference / `&mut a[i]` element is a separate
// case — #81 — not covered here.)

/// `while .. { upd(&mut s); }` must accumulate (was 0).
#[test]
fn m80_loop_refmut_scalar_accumulates_matches_llvm() {
    differential_program(
        "loop_scalar",
        "#[inline(never)] fn upd(p: &mut i64) { *p = *p + 1; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s: i64 = bb(0); let mut i = 0i32; \
            while i < bb(10i32) { upd(&mut s); i = i.wrapping_add(1); } \
            (s & 0xff) as i32 }",
        10,
    );
}

/// Two &mut-to-call locals carried across the same loop with an asymmetric reduction.
#[test]
fn m80_loop_two_refmut_locals_matches_llvm() {
    differential_program(
        "loop_two",
        "#[inline(never)] fn add(p: &mut i64, v: i64) { *p = *p + v; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut a: i64 = bb(0); let mut b: i64 = bb(0); let mut i = 0i32; \
            while i < bb(5i32) { add(&mut a, 2); add(&mut b, 3); i = i.wrapping_add(1); } \
            ((a.wrapping_mul(7).wrapping_add(b.wrapping_mul(11))) & 0xff) as i32 }",
        // a=10, b=15; 10*7 + 15*11 = 235
        235,
    );
}

/// Nested loop, &mut-to-call accumulator carried across both levels.
#[test]
fn m80_nested_loop_refmut_matches_llvm() {
    differential_program(
        "nested",
        "#[inline(never)] fn upd(p: &mut i64) { *p = *p + 1; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s: i64 = bb(0); let mut i = 0i32; \
            while i < bb(3i32) { let mut j = 0i32; \
                while j < bb(4i32) { upd(&mut s); j = j.wrapping_add(1); } \
                i = i.wrapping_add(1); } \
            (s & 0xff) as i32 }",
        12,
    );
}

/// Control: a single (non-loop) &mut-to-call still works.
#[test]
fn m80_noloop_refmut_control_matches_llvm() {
    differential_program(
        "noloop",
        "#[inline(never)] fn upd(p: &mut i64) { *p = *p + 1; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s: i64 = bb(0); upd(&mut s); upd(&mut s); upd(&mut s); (s & 0xff) as i32 }",
        3,
    );
}

// #82: a BARE `&mut <aggregate>` (an array / struct, NOT a scalar) passed to a fn
// inside a loop dropped the callee's writeback the same way #80 did for a scalar, but
// the #80 scalar cell does not cover aggregates. The fix memory-backs such a base
// aggregate (case 4a, the `None` projection arm). For an ARRAY the indexed read goes
// through the memory GEP path, so this is a FULL fix (exact match), found by the
// round-5 large-match-jumptable fuzz: a `match`-dispatch helper mutating `&mut [u32;4]`.

/// `while .. { dispatch(op, &mut acc); }` mutating `&mut [u32;4]` through a match must
/// accumulate (was the untouched initial array — 4, not 51).
#[test]
fn m82_loop_refmut_array_match_dispatch_matches_llvm() {
    differential_program(
        "arr_dispatch",
        "#[inline(never)] fn dispatch(op: u32, acc: &mut [u32; 4]) { match op { \
            0 => acc[0] = acc[0].wrapping_add(1), 1 => acc[1] = acc[1].wrapping_add(2), \
            2 => acc[2] = acc[2].wrapping_add(3), 3 => acc[3] = acc[3].wrapping_add(4), \
            4 => { acc[0] = acc[0].wrapping_mul(2); } 5 => { acc[1] = acc[1].wrapping_mul(2); } \
            6 => { acc[2] = acc[2].wrapping_mul(2); } 7 => { acc[3] = acc[3].wrapping_mul(2); } \
            _ => {} } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut acc = [1u32, 1, 1, 1]; let mut i: u32 = 0; \
            while i < bb(24) { dispatch(bb(i % 8), &mut acc); i = i.wrapping_add(1); } \
            let s = acc[0].wrapping_add(acc[1]).wrapping_add(acc[2]).wrapping_add(acc[3]); \
            (s % 121) as i32 }",
        51,
    );
}

/// Simpler bare `&mut [i64;3]`: each iteration bumps one element by its index weight.
#[test]
fn m82_loop_refmut_array_bump_matches_llvm() {
    differential_program(
        "arr_bump",
        "#[inline(never)] fn bump(a: &mut [i64; 3], k: usize) { a[k] = a[k] + (k as i64 + 1); }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut a: [i64; 3] = [bb(0), bb(0), bb(0)]; let mut i = 0i32; \
            while i < bb(9i32) { bump(&mut a, (i % 3) as usize); i = i.wrapping_add(1); } \
            ((a[0] + a[1] + a[2]) & 0xff) as i32 }",
        // each index hit 3 times: 3*1 + 3*2 + 3*3 = 18
        18,
    );
}

// #71 / gap A: a loop-carried SCALARIZED aggregate (struct/array/tuple) local that
// is mutated IN-PLACE inside the loop (field/index store) — NOT via a `&mut`-to-call.
// Previously the in-loop store was dropped across the back-edge (the scalarized
// field had no loop-header phi) and fail-closed at O0; the bridge now memory-backs
// the loop-carried aggregate so the update round-trips through its stable slot.
// These differential tests verify the accumulation is CORRECT (no store-drop).

/// `let mut q = Q{a,b}; while .. { q.a += 1 }` — struct FIELD accumulator.
#[test]
fn m71_loop_carried_aggregate_field_accumulates_matches_llvm() {
    differential_program(
        "m71_struct_field",
        "#[derive(Clone, Copy)] struct Q { a: i32, b: i32 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut q = Q { a: bb(7i32), b: bb(0i32) }; let mut i = 0i32; \
            while i < bb(5i32) { q.a = q.a.wrapping_add(1); i = i.wrapping_add(1); } \
            (q.a & 0xff) as i32 }",
        // 7 + 5 = 12
        12,
    );
}

/// `let mut a = [..]; while .. { a[k] += .. }` — array INDEX accumulator.
#[test]
fn m71_loop_carried_array_index_accumulates_matches_llvm() {
    differential_program(
        "m71_array_index",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut a: [i32; 4] = [bb(0i32); 4]; let mut i = 0i32; \
            while i < bb(20i32) { let k = (i % 4) as usize; a[k] = a[k].wrapping_add(i).wrapping_add(1); i = i.wrapping_add(1); } \
            ((a[0] + a[1] + a[2] + a[3]) & 0xff) as i32 }",
        // sum_{i=0}^{19} (i+1) = 210; 210 & 0xff = 210
        210,
    );
}

/// `let mut t = (..,..); while .. { t.0 += t.1; t.1 += i }` — tuple accumulator.
#[test]
fn m71_loop_carried_tuple_accumulates_matches_llvm() {
    differential_program(
        "m71_tuple",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut t = (bb(0i64), bb(1i64)); let mut i = 0i64; \
            while i < bb(15i64) { t.0 = t.0.wrapping_add(t.1); t.1 = t.1.wrapping_add(i); i = i.wrapping_add(1); } \
            ((t.0 + t.1) % 123) as i32 }",
        84,
    );
}

// Gap B (forward range iteration at O0): `for i in 0..n` lowers a reachable
// `*::precondition_check` (the unsafe-precondition debug helper the Range iterator's
// spec_next calls via `hint::unreachable_unchecked`) whose dead panic arm builds the
// unmodelable `core::fmt::rt::ArgumentType`; it is now lowered as a no-op `Return`
// (sound — a no-op when the precondition holds, as in LLVM release). These verify the
// loop computes the CORRECT result (the no-op preserves behavior).

/// `for i in 0..n { s += i }` — the canonical forward range loop.
#[test]
fn gapb_forward_range_sum_matches_llvm() {
    differential_program(
        "gapb_range_sum",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let n = bb(10i32); let mut s = 0i32; \
            for i in 0..n { s = s.wrapping_add(i); } \
            (s % 123) as i32 }",
        // sum 0..10 = 45
        45,
    );
}

/// `for i in 0..N { s += a[i] }` — range loop indexing an array.
#[test]
fn gapb_range_index_array_matches_llvm() {
    differential_program(
        "gapb_range_index",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = [bb(3i32), bb(1), bb(4), bb(1), bb(5)]; let mut s = 0i32; \
            for i in 0..5usize { s = s.wrapping_add(a[i]); } \
            (s % 123) as i32 }",
        // 3+1+4+1+5 = 14
        14,
    );
}

/// Nested forward range loops.
#[test]
fn gapb_nested_range_matches_llvm() {
    differential_program(
        "gapb_nested_range",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let n = bb(5i32); let mut s = 0i32; \
            for i in 0..n { for j in 0..n { s = s.wrapping_add(i.wrapping_mul(j)); } } \
            (s % 123) as i32 }",
        // (sum 0..5)^2 = 100
        100,
    );
}

// Gap D (nested enum projected discriminant at O0): matching `Outer::X(Inner::B(b))`
// reads `discriminant((o as X).0)` — the inner enum's tag at a Downcast/Field
// projection of the memory-backed Outer slot, which used to fail closed
// ("Rvalue::Discriminant projected source"). It is now decoded at the projected
// byte offset (lower_memory_projected_discriminant). These exercise EVERY arm so a
// wrong nested discriminant (wrong match arm) would change the result.

/// Custom nested enum, all arms.
#[test]
fn gapd_nested_enum_all_arms_matches_llvm() {
    differential_program(
        "gapd_nested",
        "enum Inner { A(i32), B(i32) } enum Outer { X(Inner), Y(i32) }\n\
         #[inline(never)] fn ev(sel: i32) -> i32 { \
            let o = match sel { 0 => Outer::X(Inner::A(bb(7))), 1 => Outer::X(Inner::B(bb(20))), _ => Outer::Y(bb(3)) }; \
            match o { Outer::X(Inner::A(a)) => a, Outer::X(Inner::B(b)) => b + 10, Outer::Y(c) => c + 100 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            ((ev(bb(0)) + ev(bb(1)) + ev(bb(2))) % 123) as i32 }",
        // 7 + 30 + 103 = 140; 140 % 123 = 17
        17,
    );
}

/// `Option<Result<i32,i32>>` — niche-encoded nested enum, all arms.
#[test]
fn gapd_nested_option_result_niche_matches_llvm() {
    differential_program(
        "gapd_opt_res",
        "#[inline(never)] fn ev(sel: i32) -> i32 { \
            let v: Option<Result<i32, i32>> = match sel { 0 => Some(Ok(bb(5))), 1 => Some(Err(bb(9))), _ => None }; \
            match v { Some(Ok(x)) => x, Some(Err(e)) => e + 30, None => 99 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            ((ev(bb(0)) + ev(bb(1)) + ev(bb(2))) % 123) as i32 }",
        // 5 + 39 + 99 = 143; 143 % 123 = 20
        20,
    );
}

// Follow-up to gap A: a memory-backed loop-carried struct/tuple/array whose scalar
// FIELD is updated by a RAW BinaryOp (`s.field = a OP b`, not a wrapping_* method)
// used to fail closed ("memory-backed aggregate assignment Rvalue::BinaryOp") once
// gap A memory-backed the aggregate. Now the projected scalar BinaryOp is computed
// and stored at the field offset. Verify correctness.

/// struct fields updated by raw `*`, `%`, `-` in a loop.
#[test]
fn gapa_struct_field_raw_binop_update_matches_llvm() {
    differential_program(
        "gapa_struct_rawbinop",
        "#[repr(C)] struct S { a: i64, b: i64 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { a: bb(2i64), b: bb(100i64) }; \
            let mut i = 0i64; \
            while i < bb(10i64) { s.a = s.a * bb(2) % 1000; s.b = s.b - i; i = i.wrapping_add(1); } \
            ((s.a + s.b).rem_euclid(123)) as i32 }",
        103,
    );
}

/// tuple fields updated by raw `+` and `%` in a loop.
#[test]
fn gapa_tuple_field_raw_binop_update_matches_llvm() {
    differential_program(
        "gapa_tuple_rawbinop",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut t = (bb(7i32), bb(3i32)); \
            let mut i = 0i32; \
            while i < bb(8i32) { t.0 = t.0 + t.1; t.1 = t.0 % bb(13); i = i.wrapping_add(1); } \
            ((t.0 + t.1).rem_euclid(123)) as i32 }",
        51,
    );
}

// gap A (call-dest accumulator): `let mut s; while .. { s = step(s); }` where the
// loop-carried aggregate `s` is REASSIGNED from a by-value-returning CALL each
// iteration. gap-A memory-backs `s`, but the by-value call-argument copy
// `_arg = copy s` (scalarized arg temp <- now-memory-backed source) then read its
// source's scalar field bindings, which no longer exist (the source is in a slot)
// -> "ADT/tuple Use source field N before aggregate binding" fail-closed at BOTH O0
// and O3. The fix (`lower_memory_whole_aggregate_to_scalarized_use`) loads each leaf
// from the memory-backed source's slot into the arg temp's scalar field bindings,
// matching the straight-line (scalarized-source) path. Nested-aggregate fields stay
// fail-closed (never miscompiled).

/// 16-byte struct {i64,i64} accumulator via a by-value call in a loop.
#[test]
fn gapa_call_dest_struct16_accum_matches_llvm() {
    differential_program(
        "gapa_call_struct16",
        "#[derive(Clone, Copy)] struct S { a: i64, b: i64 }\n\
         #[inline(never)] fn step(s: S) -> S { S { a: s.a + 1, b: s.b + 2 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { a: bb(0i64), b: bb(0i64) }; let mut i = 0i32; \
            while i < bb(5i32) { s = step(s); i = i.wrapping_add(1); } \
            ((s.a + s.b) & 0xff) as i32 }",
        15,
    );
}

/// REORDER-PRONE {i8,i64} struct (rustc lays i64 first): the slot-leaf reads must
/// use the rustc layout offsets, not declaration order, or the fields swap.
#[test]
fn gapa_call_dest_struct_reorder_matches_llvm() {
    differential_program(
        "gapa_call_reorder",
        "#[derive(Clone, Copy)] struct S { a: i8, b: i64 }\n\
         #[inline(never)] fn step(s: S) -> S { S { a: s.a.wrapping_add(1), b: s.b + 10 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { a: bb(0i8), b: bb(0i64) }; let mut i = 0i32; \
            while i < bb(5i32) { s = step(s); i = i.wrapping_add(1); } \
            ((s.a as i64 + s.b) & 0xff) as i32 }",
        55,
    );
}

/// Tuple (i64,i64) accumulator via a by-value call in a loop.
#[test]
fn gapa_call_dest_tuple_accum_matches_llvm() {
    differential_program(
        "gapa_call_tuple",
        "#[inline(never)] fn step(s: (i64, i64)) -> (i64, i64) { (s.0 + 1, s.1 + 2) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = (bb(0i64), bb(0i64)); let mut i = 0i32; \
            while i < bb(5i32) { s = step(s); i = i.wrapping_add(1); } \
            ((s.0 + s.1) & 0xff) as i32 }",
        15,
    );
}

/// Two distinct struct accumulators carried across the same loop.
#[test]
fn gapa_call_dest_two_accumulators_matches_llvm() {
    differential_program(
        "gapa_call_two",
        "#[derive(Clone, Copy)] struct S { a: i64, b: i64 }\n\
         #[inline(never)] fn f(s: S) -> S { S { a: s.a + 1, b: s.b + 2 } }\n\
         #[inline(never)] fn g(s: S) -> S { S { a: s.a + 10, b: s.b + 20 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut p = S { a: bb(0i64), b: bb(0i64) }; let mut q = S { a: bb(0i64), b: bb(0i64) }; \
            let mut i = 0i32; \
            while i < bb(3i32) { p = f(p); q = g(q); i = i.wrapping_add(1); } \
            ((p.a + p.b + q.a + q.b) & 0xff) as i32 }",
        99,
    );
}

// gap A (inverse): a per-iteration construction temp `_t = S { .. }` (scalarized,
// not loop-carried -> not memory-backed) written back into a gap-A memory-backed
// loop-carried local (`s = S {..}` -> `_t = ..; s = move _t`), OR a constructed
// aggregate RETURNED by value into the memory-backed return slot. This is the
// inverse of the call-arg case: a SCALARIZED struct/tuple source -> a MEMORY-backed
// dest, which failed closed "memory aggregate whole assignment from non-memory
// source". `lower_memory_aggregate_use_from_scalarized_struct` stores each bound
// field value into the dest slot at its rustc layout offset.

/// A struct built/accumulated in a loop, RETURNED by value (the return slot is
/// memory-backed; the loop reconstruct temp is scalarized).
#[test]
fn gapa_return_loop_built_struct_matches_llvm() {
    differential_program(
        "gapa_ret_struct",
        "#[derive(Clone, Copy)] struct S { a: i64, b: i64 }\n\
         #[inline(never)] fn build() -> S { \
            let mut s = S { a: bb(0i64), b: bb(0i64) }; let mut i = 0i32; \
            while i < bb(5i32) { s = S { a: s.a + 1, b: s.b + s.a }; i = i.wrapping_add(1); } s }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { let s = build(); ((s.a + s.b) & 0xff) as i32 }",
        15,
    );
}

/// REORDER-PRONE {i8,i64} struct built in a loop and returned by value.
#[test]
fn gapa_return_loop_built_reorder_matches_llvm() {
    differential_program(
        "gapa_ret_reorder",
        "#[derive(Clone, Copy)] struct S { a: i8, b: i64 }\n\
         #[inline(never)] fn build() -> S { \
            let mut s = S { a: bb(0i8), b: bb(0i64) }; let mut i = 0i32; \
            while i < bb(5i32) { s = S { a: s.a.wrapping_add(1), b: s.b + 10 }; i = i.wrapping_add(1); } s }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { let s = build(); ((s.a as i64 + s.b) & 0xff) as i32 }",
        55,
    );
}

/// A tuple built in a loop and returned by value.
#[test]
fn gapa_return_loop_built_tuple_matches_llvm() {
    differential_program(
        "gapa_ret_tuple",
        "#[inline(never)] fn build() -> (i64, i64) { \
            let mut s = (bb(0i64), bb(0i64)); let mut i = 0i32; \
            while i < bb(6i32) { s = (s.0 + 1, s.1 + s.0); i = i.wrapping_add(1); } s }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { let s = build(); ((s.0 + s.1) & 0xff) as i32 }",
        21,
    );
}

// gap A (array extension): the scalarized<->memory whole-aggregate copy now also
// handles a SCALAR-ELEMENT array (each element is one leaf at i*stride, bound by
// element index). Closes a by-value `[T; N]` accumulator (`s = step(s)`) and a
// returned-by-value array builder at O0. The shared `flat_scalar_aggregate_copy_plan`
// + the field-copy faithfulness gate cover struct/tuple/array uniformly; an array of
// AGGREGATES (multi-leaf element) falls through (Ok(None)).

/// `[i64; 3]` accumulator passed by value to a fn in a loop.
#[test]
fn gapa_call_dest_array_accum_matches_llvm() {
    differential_program(
        "gapa_call_array",
        "#[inline(never)] fn step(s: [i64; 3]) -> [i64; 3] { [s[0] + 1, s[1] + 2, s[2] + 3] }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = [bb(0i64), bb(0i64), bb(0i64)]; let mut i = 0i32; \
            while i < bb(5i32) { s = step(s); i = i.wrapping_add(1); } \
            ((s[0] + s[1] + s[2]) & 0xff) as i32 }",
        30,
    );
}

/// A narrow `[u8; 4]` array built in a loop and returned by value (store path,
/// element stride 1).
#[test]
fn gapa_return_loop_built_array_matches_llvm() {
    differential_program(
        "gapa_ret_array",
        "#[inline(never)] fn build() -> [u8; 4] { \
            let mut s = [bb(0u8), bb(0u8), bb(0u8), bb(0u8)]; let mut i = 0i32; \
            while i < bb(7i32) { s = [s[0].wrapping_add(1), s[1].wrapping_add(2), \
                s[2].wrapping_add(3), s[3].wrapping_add(4)]; i = i.wrapping_add(1); } s }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { let s = build(); \
            ((s[0] as u32 + s[1] as u32 + s[2] as u32 + s[3] as u32) % 251) as i32 }",
        70,
    );
}

// gap (closure by-value aggregate arg): a struct/tuple passed BY VALUE to a closure
// (`|s: S| ..` invoked as `s = f(s)` in a loop) failed closed at O0 —
// `lower_closure_call_terminator` required every untupled arg to be a scalar. The
// tupled-args tuple is now memory-backed when it carries a by-value aggregate element
// (compute_memory_backed_locals 3c), and each aggregate element is materialized by
// value from the tuple slot at its layout offset (the same lane-copy the direct-call
// by-value aggregate path uses); sibling SCALAR elements are loaded from the slot.
// Arrays-by-value to a closure remain a sound fail-closed (separate layout path).

/// `|s: S| -> S` closure accumulator called by value in a loop (Fn, non-capturing).
#[test]
fn closure_byval_struct_accum_matches_llvm() {
    differential_program(
        "closure_struct",
        "#[derive(Clone, Copy)] struct S { a: i64, b: i64 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f = |s: S| S { a: s.a + 1, b: s.b + s.a }; \
            let mut s = S { a: bb(0i64), b: bb(0i64) }; let mut i = 0i32; \
            while i < bb(5i32) { s = f(s); i = i.wrapping_add(1); } \
            ((s.a + s.b) & 0xff) as i32 }",
        15,
    );
}

/// MIXED aggregate + scalar closure args (the tuple is `(S, i64)` — the aggregate
/// element is materialized, the scalar element is loaded from the same slot).
#[test]
fn closure_byval_mixed_agg_scalar_args_matches_llvm() {
    differential_program(
        "closure_mixed",
        "#[derive(Clone, Copy)] struct S { a: i64, b: i64 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f = |s: S, k: i64| S { a: s.a + k, b: s.b + 2 * k }; \
            let mut s = S { a: bb(0i64), b: bb(0i64) }; let mut i = 0i64; \
            while i < bb(5i64) { s = f(s, bb(3i64)); i = i.wrapping_add(1); } \
            ((s.a + s.b) & 0xff) as i32 }",
        45,
    );
}

/// TWO aggregate args (the second is at a non-zero tuple offset) + reorder-prone
/// element, exercising the element-offset arithmetic.
#[test]
fn closure_byval_two_aggregate_args_matches_llvm() {
    differential_program(
        "closure_two_agg",
        "#[derive(Clone, Copy)] struct S { a: i64, b: i64 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f = |p: S, q: S| S { a: p.a + q.a, b: p.b + q.b }; \
            let mut s = S { a: bb(1i64), b: bb(2i64) }; let mut i = 0i32; \
            while i < bb(4i32) { s = f(s, S { a: bb(1i64), b: bb(1i64) }); i = i.wrapping_add(1); } \
            ((s.a + s.b) & 0xff) as i32 }",
        11,
    );
}

/// A capturing FnMut closure taking a reorder-prone `{i8,i64}` struct by value.
#[test]
fn closure_byval_reorder_fnmut_matches_llvm() {
    differential_program(
        "closure_reorder",
        "#[derive(Clone, Copy)] struct S { a: i8, b: i64 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f = |s: S| S { a: s.a.wrapping_add(1), b: s.b + 10 }; \
            let mut s = S { a: bb(0i8), b: bb(0i64) }; let mut i = 0i32; \
            while i < bb(5i32) { s = f(s); i = i.wrapping_add(1); } \
            ((s.a as i64 + s.b) & 0xff) as i32 }",
        55,
    );
}

// Regression for a FALSE-REJECT in the field-copy faithfulness gate (introduced with
// the gate itself): `trust_ir_leaf_byte_size` computed `bits/8`, which truncates a
// 1-bit `bool` leaf to 0 bytes, so the gate wrongly rejected EVERY memory-backed
// aggregate copy containing a `bool` field ("field N uses a 0-byte access but its
// layout field is 1 byte"). A `bool` occupies one byte; the size now rounds up
// (`div_ceil(8)`). These exercise bool fields through both copy paths + the closure
// path. (Also unblocked a loop-carried `(i32,bool)` overflow tuple at O0.)

/// A `bool` field in a loop-carried struct accumulator (read + store copy paths).
#[test]
fn bool_field_struct_accum_matches_llvm() {
    differential_program(
        "bool_struct",
        "#[derive(Clone, Copy)] struct S { x: i32, flag: bool }\n\
         #[inline(never)] fn step(s: S) -> S { S { x: s.x + 1, flag: !s.flag } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { x: bb(0i32), flag: bb(false) }; let mut i = 0i32; \
            while i < bb(7i32) { s = step(s); i = i.wrapping_add(1); } \
            ((s.x & 0x7f) + if s.flag { 1 } else { 0 }) as i32 }",
        8,
    );
}

/// MULTIPLE bool fields interleaved with ints (reorder-prone), exercising several
/// 1-byte leaves at distinct offsets.
#[test]
fn bool_fields_multi_reorder_matches_llvm() {
    differential_program(
        "bool_multi",
        "#[derive(Clone, Copy)] struct S { a: bool, b: i64, c: bool, d: i32 }\n\
         #[inline(never)] fn step(s: S) -> S { S { a: !s.a, b: s.b + 1, c: s.c ^ s.a, d: s.d + 2 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { a: bb(false), b: bb(0i64), c: bb(true), d: bb(0i32) }; let mut i = 0i32; \
            while i < bb(6i32) { s = step(s); i = i.wrapping_add(1); } \
            ((s.b + s.d as i64 + if s.a { 10 } else { 0 } + if s.c { 100 } else { 0 }) & 0xff) as i32 }",
        18,
    );
}

/// A `(i32, bool)` tuple passed by value to a closure (the bool element through the
/// closure tuple-slot path).
#[test]
fn bool_tuple_closure_arg_matches_llvm() {
    differential_program(
        "bool_closure",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f = |t: (i32, bool)| (t.0 + 1, !t.1); \
            let mut s = (bb(0i32), bb(false)); let mut i = 0i32; \
            while i < bb(7i32) { s = f(s); i = i.wrapping_add(1); } \
            ((s.0 & 0x7f) + if s.1 { 1 } else { 0 }) as i32 }",
        8,
    );
}

// PROOF-EXTENSION (loop-threading z3 VC, #71/#84): a rotation/swap loop whose bound
// or inputs are `black_box`-ed (the standard benchmark idiom) used to fail-closed —
// the z3 back-edge refinement could not model `black_box` on the loop path, so it
// fell back to the structural false-reject. `black_box` is value-identity, now
// modeled as `dst = x` on both the spec walk and the impl symexec (the bridge
// registers the genuine std `black_box` FuncIds), so the prover ADMITS the rotation
// by PROOF. These compile only because z3 proves the threading value-correct.

/// Euclid's gcd — a ROTATION (`a' = old b`) — with the loop bound `black_box`-ed.
#[test]
fn proof_euclid_rotation_blackbox_bound_matches_llvm() {
    differential_program(
        "proof_euclid_bb",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut a = bb(48i32); let mut b = bb(18i32); \
            while b != bb(0i32) { let t = b; b = a % b; a = t; } \
            (a & 0x7f) as i32 }",
        6,
    );
}

/// Fibonacci — a ROTATION (`b' = old a`) — with the loop bound `black_box`-ed.
#[test]
fn proof_fib_rotation_blackbox_bound_matches_llvm() {
    differential_program(
        "proof_fib_bb",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut a = bb(1i32); let mut b = bb(1i32); \
            while a < bb(1000i32) { let t = a; a = a.wrapping_add(b); b = t; } \
            (a & 0x7f) as i32 }",
        61,
    );
}
