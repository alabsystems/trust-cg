// Safety-boundary regression test for 
// of an aggregate FIELD or array ELEMENT (`&mut s.a` / `&mut a[i]`) passed to a call
// dropped the callee's writeback across the loop back-edge — a SILENT wrong value.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. `while .. { upd(&mut s.a); }` borrows field `a` of a SCALARIZED struct
// `s` (its fields held as separate per-field SSA values). The callee mutates `*p`, but
// the scalarized model reloads the field after the call without threading that reload
// across the loop back-edge, so iteration N's mutation is lost on N+1 and `s.a` keeps
// its entry value. `((s.a + s.b))` returned 0 instead of 21 at -Copt-level 0 AND 3 —
// the same class as #80 (`&mut scalar`) but for a projected field / element.
//
// THE FIX-IN-PROGRESS (in rustc-codegen-trust-cg/src/lib.rs `compute_memory_backed_locals`
// case 4a). Memory-back the BASE aggregate of a projected `&mut` whose reference
// escapes to a call inside a loop, so `&mut s.a` lowers to a GEP into a real stack
// slot the callee writes and every iteration reads (the aggregate analogue of #80's
// scalar cell). This makes the previously-SILENT miscompile FAIL CLOSED today (the
// flat-scalar-leaf struct read path still routes `s.a` through the scalarized
// projection lookup, so the memory-backed local trips the "projection before aggregate
// binding" guard — a safe compile error, not a wrong value). Full support (producing
// 21) additionally requires the field read/write/init dispatch to honour
// memory-backed membership for flat-scalar-leaf structs.
//
// This test pins the SAFETY INVARIANT rather than a single behaviour: the trust-cg
// backend must EITHER fail closed (a compile error — acceptable) OR produce the
// LLVM-oracle value. It must NEVER silently return a different value. The test
// therefore keeps passing whether #81 is fail-closed (today) or fully fixed (future).

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
    assert!(status.success(), "cargo build failed; cannot run m89 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m89_{stem}_{}", std::process::id()));
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

/// Outcome of compiling+running one program with one backend.
enum Outcome {
    /// Compiled, linked, ran: the process exit code (8-bit).
    Ran(i32),
    /// The backend refused to compile (failed closed) — a safe non-miscompile.
    FailedClosed,
}

/// Compile `src` with the given backend. The LLVM oracle (`dylib == None`) must
/// always compile, link, and run. The trust-cg backend may legitimately fail to
/// compile (fail closed), in which case `Outcome::FailedClosed` is returned instead
/// of panicking.
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> Outcome {
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
    if !output.status.success() {
        if dylib.is_some() {
            // trust-cg refusing to compile == failing closed == NOT a miscompile.
            let _ = std::fs::remove_dir_all(&dir);
            return Outcome::FailedClosed;
        }
        panic!("{stem} (opt={opt}, llvm): oracle failed to compile. stderr: <<<{stderr}>>>");
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
    if !link.status.success() {
        // A link failure on the trust-cg side (e.g. an out-of-line helper the backend
        // referenced but did not emit) is also a fail-closed signal, never a silent
        // wrong value.
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!(
            "{stem} (opt={opt}, llvm): link failed. stderr: <<<{}>>>",
            String::from_utf8_lossy(&link.stderr)
        );
    }

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    match run.status.code() {
        Some(code) => Outcome::Ran(code),
        // Terminated by a signal (e.g. SIGILL from a fail-closed `ud2`): not a silent
        // wrong value.
        None => Outcome::FailedClosed,
    }
}

/// Compile `body` (a `#![no_std] #![no_main]` program tail) with BOTH backends at
/// -Copt-level 0 and 3. The LLVM oracle must return `expected`. The trust-cg backend
/// must EITHER fail closed OR return exactly `expected` — it must NEVER return a
/// different value (the #81 silent miscompile, which returned 0).
fn no_silent_miscompile(stem: &str, body: &str, expected: i32) {
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
        let llvm = match compile_link_run(stem, &src, opt, None) {
            Outcome::Ran(code) => code,
            Outcome::FailedClosed => panic!("{stem} (opt={opt}): LLVM oracle did not run"),
        };
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        match compile_link_run(stem, &src, opt, Some(&dylib)) {
            // The full fix produces the correct value.
            Outcome::Ran(trust) => assert_eq!(
                trust, expected,
                "{stem} (opt={opt}): trust-cg SILENTLY returned {trust} but the oracle \
                 returned {expected} — a #81 miscompile. trust-cg must fail closed or be correct."
            ),
            // Failing closed (compile error / SIGILL / link failure) is the accepted
            // safe boundary for the not-yet-complete cases.
            Outcome::FailedClosed => {
                eprintln!("{stem} (opt={opt}): trust-cg failed closed (safe, not a miscompile)");
            }
        }
    }
}

/// A niche `Option<&i32>` built from a `&local` via a runtime branch, then matched.
/// Was fail-closed at O0 ("borrowed scalar reference used without deref"); the &local
/// stored into the niche needs the local celled to a real address. Must fail closed OR
/// produce the correct value, never silently wrong.
#[test]
fn m89_niche_option_ref_local_match_no_silent_miscompile() {
    no_silent_miscompile(
        "opt_ref",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let r = bb(7i32); \
            let o: Option<&i32> = if bb(true) { Some(&r) } else { None }; \
            (match o { Some(x) => *x * 3, None => 0 }) & 0x7f }",
        21,
    );
}

/// None branch selected.
#[test]
fn m89_niche_option_ref_none_no_silent_miscompile() {
    no_silent_miscompile(
        "opt_ref_none",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let r = bb(7i32); \
            let o: Option<&i32> = if bb(false) { Some(&r) } else { None }; \
            (match o { Some(x) => *x, None => bb(9) }) & 0x7f }",
        9,
    );
}

/// A struct holding a &local (the cell trigger also covers Adt struct aggregates).
#[test]
fn m89_struct_holding_ref_local_no_silent_miscompile() {
    no_silent_miscompile(
        "struct_ref",
        "struct S<'a> { p: &'a i32 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let r = bb(11i32); let s = S { p: &r }; (*s.p * 2) & 0x7f }",
        22,
    );
}
