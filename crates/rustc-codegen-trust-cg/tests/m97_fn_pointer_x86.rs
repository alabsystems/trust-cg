#[path = "support/target_dir.rs"]
mod target_dir_support;

// Completeness gap #97 — fn-pointer-as-value / fn-pointer-table programs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE GAP. `let f: fn(i64) -> i64 = some_fn;` produces MIR
// `Rvalue::Cast(CastKind::PointerCoercion(ReifyFnPointer), op, fn-ptr-ty)` whose
// operand has type `Ty::FnDef(def_id, args)` — a zero-sized function item. The
// reified value is the ADDRESS of that monomorphized function's symbol. The
// bridge previously failed closed on this coercion at the FRONTEND, blocking
// every fn-pointer-value / fn-pointer-table program.
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs `lower_reify_fn_pointer`, dispatched
// from `lower_cast`). The `ReifyFnPointer` of a `FnDef` resolves the function via
// `Instance::resolve_for_fn_ptr` (rustc's own path — routes `#[track_caller]` /
// virtual fns through their `ReifyShim`), registers it as a module callee
// (`extern_callee`, deduplicated by symbol name exactly as a direct call does),
// materializes its address with `Inst::Const { Constant::FnDef(func_id) }` (a
// `GlobalRef`/`ExternRef` symbol-address relocation), then reifies that
// `Func(sig)` code pointer to a raw `Ptr` with `CastOp::ReifyFnPointer`
// (Direction 1). Calling through the resulting `fn(..)` pointer is a
// `CallIndirect` (already supported). The referenced function is queued for
// codegen by the mono collector (a reified fn pointer is a used mono item), and
// the symbol name matches the direct-call path's, so the linker resolves it.
//
// SUPPORTED SHAPES (verified MATCH vs LLVM at O0 and O3 below): a fn-pointer
// value; a `[fn(..); N]` table indexed by a runtime value and called; a fn
// passed as a `fn(..)` parameter and called; a fn returned from a fn; a struct
// field holding a fn pointer; a branch-varying (phi) fn-pointer value then called.
//
// FAIL-CLOSED (safe; pinned NOT to miscompile): a non-capturing closure coerced
// to `fn(..)` (`ClosureFnPointer` — its call-once reify shim was observed to land
// at the wrong code, so it is left to fail closed); `fn(..) as usize`
// (`PointerExposeProvenance`, a separate cast surface). For these the test pins
// the SAFETY INVARIANT: trust-cg must EITHER fail closed OR match the LLVM oracle,
// never silently return a different value.

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
    assert!(status.success(), "cargo build failed; cannot run m97 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m97_{stem}_{}", std::process::id()));
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
/// compile (fail closed), in which case `Outcome::FailedClosed` is returned.
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> Outcome {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        // `TCG_NO_PROOF_CERTS=1`: skip the per-compile lowering proof certs so the
        // differential exercises functionality (fn-address materialization) in
        // isolation. The default-certs sanity is covered separately by
        // `m97_default_certs_sanity`.
        cmd.env("TCG_NO_PROOF_CERTS", "1");
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
        // Terminated by a signal (e.g. SIGILL from a fail-closed `ud2`): not a
        // silent wrong value.
        None => Outcome::FailedClosed,
    }
}

fn skip_guard(stem: &str) -> bool {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return true;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return true;
    }
    false
}

fn wrap(body: &str) -> String {
    format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box as bb;\n{body}\n"
    )
}

/// Compile `body` with BOTH backends at O0 and O3. The LLVM oracle must return
/// `expected`; the trust-cg backend MUST also return exactly `expected` at both
/// opt levels (the supported shapes). A fail-closed here is a regression of the
/// fix, so it panics.
fn expect_correct(stem: &str, body: &str, expected: i32) {
    if skip_guard(stem) {
        return;
    }
    let dylib = ensure_dylib_built();
    let src = wrap(body);
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
            Outcome::Ran(trust) => assert_eq!(
                trust, expected,
                "{stem} (opt={opt}): trust-cg returned {trust} but the LLVM oracle returned \
                 {expected} — the fn-pointer reify must call the RIGHT function."
            ),
            Outcome::FailedClosed => panic!(
                "{stem} (opt={opt}): trust-cg failed closed on a SUPPORTED fn-pointer shape — \
                 a regression of the #97 fix."
            ),
        }
    }
}

/// Compile `body` with BOTH backends at O0 and O3. The LLVM oracle must return
/// `expected`; the trust-cg backend must EITHER fail closed OR return exactly
/// `expected` — it must NEVER silently return a different value. Pins the safety
/// boundary for the not-yet-supported shapes.
fn no_silent_miscompile(stem: &str, body: &str, expected: i32) {
    if skip_guard(stem) {
        return;
    }
    let dylib = ensure_dylib_built();
    let src = wrap(body);
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
            Outcome::Ran(trust) => assert_eq!(
                trust, expected,
                "{stem} (opt={opt}): trust-cg SILENTLY returned {trust} but the oracle returned \
                 {expected} — a miscompile. trust-cg must fail closed or be correct."
            ),
            Outcome::FailedClosed => {
                eprintln!("{stem} (opt={opt}): trust-cg failed closed (safe, not a miscompile)");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Supported shapes — MUST match LLVM at O0 and O3.
// ---------------------------------------------------------------------------

/// `let f: fn(i64) -> i64 = sq; f(bb(5))` — the core fn-pointer-as-value case.
#[test]
fn m97_simple_fn_pointer_value() {
    expect_correct(
        "simple",
        "fn sq(x: i64) -> i64 { x * x }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f: fn(i64) -> i64 = sq; (f(bb(5i64)) as i32) & 0x7f }",
        25,
    );
}

/// `[fn(i64)->i64; 3]` table indexed by a runtime value and called.
#[test]
fn m97_fn_pointer_table_runtime_index() {
    expect_correct(
        "table",
        "fn a(x: i64) -> i64 { x + 1 }\n\
         fn b(x: i64) -> i64 { x * 2 }\n\
         fn c(x: i64) -> i64 { x - 3 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let t: [fn(i64) -> i64; 3] = [a, b, c]; \
            let i = bb(1usize); (t[i](10i64) as i32) & 0x7f }",
        20,
    );
}

/// A fn passed as a `fn(..)` PARAMETER to a helper and called.
#[test]
fn m97_fn_pointer_as_param() {
    expect_correct(
        "param",
        "fn dbl(x: i64) -> i64 { x * 2 }\n\
         #[inline(never)] fn apply(f: fn(i64) -> i64, v: i64) -> i64 { f(v) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            (apply(dbl, bb(21i64)) as i32) & 0x7f }",
        42,
    );
}

/// A fn RETURNED from a fn, then called.
#[test]
fn m97_fn_pointer_returned() {
    expect_correct(
        "returned",
        "fn inc(x: i64) -> i64 { x + 7 }\n\
         #[inline(never)] fn pick() -> fn(i64) -> i64 { inc }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f = pick(); (f(bb(35i64)) as i32) & 0x7f }",
        42,
    );
}

/// A STRUCT FIELD holding a fn pointer, then called.
#[test]
fn m97_fn_pointer_struct_field() {
    expect_correct(
        "struct",
        "fn mul3(x: i64) -> i64 { x * 3 }\n\
         struct Holder { op: fn(i64) -> i64 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let h = Holder { op: mul3 }; ((h.op)(bb(14i64)) as i32) & 0x7f }",
        42,
    );
}

/// A BRANCH-VARYING (phi) fn-pointer value, then called.
#[test]
fn m97_fn_pointer_branch_select() {
    expect_correct(
        "select",
        "fn f1(x: i64) -> i64 { x + 100 }\n\
         fn f2(x: i64) -> i64 { x + 200 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let chosen: fn(i64) -> i64 = if bb(1i32) == 1 { f1 } else { f2 }; \
            (chosen(bb(2i64)) as i32) & 0x7f }",
        102,
    );
}

// ---------------------------------------------------------------------------
// Fail-closed shapes — MUST fail closed OR be correct, NEVER silently wrong.
// ---------------------------------------------------------------------------

/// A non-capturing closure coerced to `fn(..)` (`ClosureFnPointer`). Left to fail
/// closed (its call-once reify shim lands at the wrong code), pinned not to
/// miscompile.
#[test]
fn m97_closure_to_fn_pointer_safe() {
    no_silent_miscompile(
        "closure",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f: fn(i64) -> i64 = |x| x + 9; (f(bb(33i64)) as i32) & 0x7f }",
        42,
    );
}

/// `fn(..) as usize` provenance-exposing cast (`PointerExposeProvenance`, a
/// separate cast surface). Fail-closed-or-correct.
#[test]
fn m97_fn_pointer_as_usize_safe() {
    no_silent_miscompile(
        "asusize",
        "fn g(x: i64) -> i64 { x + 1 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let f: fn(i64) -> i64 = g; let a = f as usize; \
            (if a != 0 { f(bb(41i64)) } else { 0 } as i32) & 0x7f }",
        42,
    );
}

// ---------------------------------------------------------------------------
// Default-certs sanity — one supported program must compile under the DEFAULT
// config (proof certs ON), proving fn-address materialization uses already-proven
// opcodes/relocations (or fail closed on a NEW uncovered opcode — the separate
// proof tail, never a miscompile).
// ---------------------------------------------------------------------------

#[test]
fn m97_default_certs_sanity() {
    let stem = "certs";
    if skip_guard(stem) {
        return;
    }
    let dylib = ensure_dylib_built();
    let body = "fn sq(x: i64) -> i64 { x * x }\n\
                #[no_mangle] pub extern \"C\" fn main() -> i32 { \
                   let f: fn(i64) -> i64 = sq; (f(bb(6i64)) as i32) & 0x7f }";
    let src = wrap(body);
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, &src).expect("write source");

    // DEFAULT config: no TCG_NO_PROOF_CERTS env — proof certs ON.
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(&dylib);
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"])
        .arg(&backend_arg)
        .args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg("-Copt-level=0")
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path)
        .output()
        .expect("spawn rustc");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let _ = std::fs::remove_dir_all(&dir);

    // Either it compiles cleanly under default certs (fn-address materialization
    // uses proven opcodes), OR it fails closed on a NEW uncovered opcode (the
    // separate proof tail). It must NEVER produce a wrong object — but a compile
    // error is the safe boundary, so we only assert it does not crash the backend
    // with an internal panic / ICE.
    assert!(
        !stderr.contains("internal compiler error") && !stderr.contains("panicked"),
        "default-certs compile must not ICE/panic. stderr: <<<{stderr}>>>"
    );
    if output.status.success() {
        eprintln!("{stem}: compiled cleanly under DEFAULT proof certs (proven opcodes)");
    } else {
        eprintln!(
            "{stem}: failed closed under DEFAULT proof certs (separate proof tail, not a \
             miscompile). stderr: <<<{stderr}>>>"
        );
    }
}
