#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Safety-boundary regression test for MISCOMPILE #81: a loop-carried mutable borrow
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

const TARGET: &str = host_target_support::X86_64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m81_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn write_panic_stubs(dir: &Path, obj: &Path) -> PathBuf {
    let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if toolchain_support::is_abort_stub_symbol(sym) {
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

    let mut cmd = toolchain_support::rustc_command();
    cmd.arg("--crate-type").arg("bin");
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
    let output = cmd.output().expect("failed to spawn trustc");
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

const UPD: &str = "#[inline(never)] fn upd(p: &mut i64) { *p = *p + 3; }\n";

/// `while .. { upd(&mut s.a); }` — a struct FIELD `&mut` in a loop. Must accumulate to
/// 21 or fail closed; must NOT silently return 0 (the original miscompile).
#[test]
fn m81_loop_struct_field_refmut_no_silent_miscompile() {
    no_silent_miscompile(
        "field",
        &format!(
            "{UPD}\
             #[derive(Clone,Copy)] struct S {{ a: i64, b: i64 }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
                let mut s = S {{ a: bb(0i64), b: bb(0i64) }}; \
                let mut i = 0i32; \
                while i < bb(7i32) {{ upd(&mut s.a); i = i.wrapping_add(1); }} \
                ((s.a + s.b) & 0xff) as i32 }}"
        ),
        // 7 iterations * 3 = 21
        21,
    );
}

/// `while .. { upd(&mut a[k]); }` — an array ELEMENT `&mut` in a loop. Must reduce to
/// the oracle value or fail closed; must NOT silently return a wrong value.
#[test]
fn m81_loop_array_element_refmut_no_silent_miscompile() {
    no_silent_miscompile(
        "array",
        &format!(
            "{UPD}\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
                let mut a: [i64; 3] = [bb(0i64), bb(0i64), bb(0i64)]; \
                let mut i = 0i32; \
                while i < bb(10i32) {{ let k = (i % 3) as usize; upd(&mut a[k]); i = i.wrapping_add(1); }} \
                ((a[0] + a[1] + a[2]) & 0xff) as i32 }}"
        ),
        // 10 increments of 3 distributed over the array, summed back = 30
        30,
    );
}

/// Two distinct fields each borrowed `&mut` in the loop — exercises more than one
/// projected writeback. Must be correct or fail closed, never silently wrong.
#[test]
fn m81_loop_two_struct_fields_refmut_no_silent_miscompile() {
    no_silent_miscompile(
        "two_fields",
        &format!(
            "{UPD}\
             #[derive(Clone,Copy)] struct S {{ a: i64, b: i64 }}\n\
             #[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
                let mut s = S {{ a: bb(0i64), b: bb(0i64) }}; \
                let mut i = 0i32; \
                while i < bb(5i32) {{ upd(&mut s.a); upd(&mut s.b); i = i.wrapping_add(1); }} \
                ((s.a + s.b) & 0xff) as i32 }}"
        ),
        // 5 iterations * (3 + 3) = 30
        30,
    );
}
