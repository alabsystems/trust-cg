// Differential regression pins for the TWO live P0 silent miscompiles found
// 2026-07-02 in `lower_aggregate_memory_store`'s memory-backed whole-copy arm
// (`*r = s` where `r: &mut Agg` and `s` is a memory-backed aggregate value).
//
// Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
//
// P0 #1 (commit 6f19ce8): a struct with a POINTER field read the pointer at a
// 1-byte stride (bit_width(Ptr) became None post trust-ir 6ed4bf0 → unwrap_or(8)
// /8 = 1) → corrupt pointer → SIGSEGV/wrong value.
// P0 #2 (commit db92e24): a MIXED-WIDTH struct/tuple read+wrote each field at
// `field_index * lane_bytes` instead of its rustc `layout.fields.offset(i)` —
// e.g. `S{i64,i32}` read the i32 from slot+4 not 8. Both sides now use rustc
// layout offsets for struct/tuple (enums keep uniform-lane addressing).
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 0 and 3. Neither shape is in the general differential
// corpus (that blind spot is why both were live for weeks) — these pins guard
// them permanently. Asymmetric reductions make any field-offset swap observable.
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
    assert!(status.success(), "cargo build failed; cannot run m69 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m69_{stem}_{}", std::process::id()));
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


/// P0 #2 — `S{i64,i32}` written by value through `&mut`. The i32 (`b`) lives at
/// rustc offset 8; the buggy `field_index*4 = 4` read it from the middle of `a`.
/// Pre-fix: tcg 40, LLVM 49.
#[test]
fn mixed_i64_i32_refmut_matches_llvm() {
    differential_program(
        "mw_i64_i32",
        "#[derive(Clone,Copy)] struct S { a: i64, b: i32 }\n\
         #[inline(never)] fn w(r: &mut S, s: S) { *r = s; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { a: bb(1), b: bb(2) }; w(&mut s, S { a: bb(40), b: bb(9) }); \
            ((s.a + s.b as i64) % 126) as i32 }",
        49,
    );
}

/// P0 #2 — `T{i8,i8,i64}`: the i64 (`c`) is at rustc offset 8, but `field_index
/// *8 = 16` read past the slot. Pre-fix: tcg 109, LLVM 49.
#[test]
fn mixed_i8_i8_i64_refmut_matches_llvm() {
    differential_program(
        "mw_i8_i8_i64",
        "#[derive(Clone,Copy)] struct T { a: i8, b: i8, c: i64 }\n\
         #[inline(never)] fn w(r: &mut T, s: T) { *r = s; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut t = T { a: bb(1), b: bb(2), c: bb(3) }; \
            w(&mut t, T { a: bb(10), b: bb(20), c: bb(19) }); \
            ((t.a as i64 + t.b as i64 + t.c) % 126) as i32 }",
        49,
    );
}

/// P0 #2 — a 4-field heavily-mixed struct `U{i16,i64,i32,i8}`, asymmetric.
#[test]
fn mixed_quad_refmut_matches_llvm() {
    differential_program(
        "mw_quad",
        "#[derive(Clone,Copy)] struct U { a: i16, b: i64, c: i32, d: i8 }\n\
         #[inline(never)] fn w(r: &mut U, s: U) { *r = s; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut u = U { a: bb(1), b: bb(2), c: bb(3), d: bb(4) }; \
            w(&mut u, U { a: bb(5), b: bb(30), c: bb(9), d: bb(5) }); \
            ((u.a as i64 + u.b + u.c as i64 + u.d as i64) % 126) as i32 }",
        49,
    );
}

/// P0 #1 — a struct with a raw-POINTER field written by value through `&mut`;
/// the pointer must survive the copy (deref reads the pointee). Pre-fix the
/// pointer was read at a 1-byte stride → corrupt.
#[test]
fn pointer_field_refmut_matches_llvm() {
    differential_program(
        "ptr_field",
        "#[derive(Clone,Copy)] struct S { a: i64, p: *const i64 }\n\
         #[inline(never)] fn w(r: &mut S, s: S) { *r = s; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let y: i64 = bb(9); \
            let mut s = S { a: bb(1), p: bb(&y as *const i64) }; \
            w(&mut s, S { a: bb(40), p: bb(&y as *const i64) }); \
            ((s.a + unsafe { *s.p }) % 126) as i32 }",
        49,
    );
}

/// Regression guard: an ENUM through `&mut` keeps its (correct) uniform-lane
/// path — the mixed-width fix must not disturb it.
#[test]
fn enum_refmut_still_matches_llvm() {
    differential_program(
        "enum_refmut",
        "#[inline(never)] fn w(r: &mut Option<i64>, v: Option<i64>) { *r = v; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut o: Option<i64> = Some(bb(1)); w(&mut o, Some(bb(49))); \
            (match o { Some(x) => x, None => 0 } % 126) as i32 }",
        49,
    );
}

/// Blind-spot pin: an int+FLOAT struct (INTEGER + SSE eightbyte) through &mut.
/// Not in the general corpus; the layout-offset fix must handle f64 leaves.
#[test]
fn int_float_refmut_matches_llvm() {
    differential_program(
        "int_float",
        "#[derive(Clone,Copy)] struct S { a: i64, b: f64 }\n\
         #[inline(never)] fn w(r: &mut S, s: S) { *r = s; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { a: bb(1), b: bb(2.0f64) }; w(&mut s, S { a: bb(40), b: bb(9.0f64) }); \
            ((s.a + s.b as i64) % 126) as i32 }",
        49,
    );
}

/// Blind-spot pin: mixed float widths `{f64,f32,i32}` through &mut.
#[test]
fn mixed_float_widths_refmut_matches_llvm() {
    differential_program(
        "mixed_float",
        "#[derive(Clone,Copy)] struct S { a: f64, b: f32, c: i32 }\n\
         #[inline(never)] fn w(r: &mut S, s: S) { *r = s; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { a: bb(1.0f64), b: bb(2.0f32), c: bb(3) }; \
            w(&mut s, S { a: bb(30.0f64), b: bb(10.0f32), c: bb(9) }); \
            ((s.a as i64 + s.b as i64 + s.c as i64) % 126) as i32 }",
        49,
    );
}

/// Blind-spot pin: an enum with a STRUCT payload `E::B(P{i32,i64})` through &mut
/// — exercises payload-field offsets inside the enum's active variant.
#[test]
fn enum_struct_payload_refmut_matches_llvm() {
    differential_program(
        "enum_struct_payload",
        "#[derive(Clone,Copy)] struct P { x: i32, y: i64 }\n\
         #[derive(Clone,Copy)] enum E { A(i8), B(P) }\n\
         #[inline(never)] fn w(r: &mut E, s: E) { *r = s; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut e = E::A(bb(1)); w(&mut e, E::B(P { x: bb(19), y: bb(30) })); \
            (match e { E::A(a) => a as i64, E::B(p) => p.x as i64 + p.y } % 126) as i32 }",
        49,
    );
}

/// Blind-spot pin: a large (>16 byte, MEMORY-class) 5-field mixed struct via &mut.
#[test]
fn large_mixed_struct_refmut_matches_llvm() {
    differential_program(
        "large_mixed",
        "#[derive(Clone,Copy)] struct S { a: i64, b: i64, c: i32, d: i16, e: i8 }\n\
         #[inline(never)] fn w(r: &mut S, s: S) { *r = s; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut s = S { a: bb(0), b: bb(0), c: bb(0), d: bb(0), e: bb(0) }; \
            w(&mut s, S { a: bb(10), b: bb(10), c: bb(10), d: bb(10), e: bb(9) }); \
            ((s.a + s.b + s.c as i64 + s.d as i64 + s.e as i64) % 126) as i32 }",
        49,
    );
}
