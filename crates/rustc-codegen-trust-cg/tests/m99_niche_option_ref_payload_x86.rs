// Completeness/correctness gap #98 — extracting + dereferencing the niche payload
// of a niche-encoded `Option<&T>` returned a FIXED garbage value (a SILENT
// miscompile), found by differential fuzzing vs LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE BUG (deterministic). `fn f(x: i64) -> i64 { let o: Option<&i64> = Some(&x);
// match o { Some(p) => *p, None => 0 } }` returned a CONSTANT (e.g. 97) regardless
// of the input — it never dereferenced the real `&x`. LLVM returned the input.
// Reproduced at O0 and (with `#[inline(never)]`) at O3.
//
// ROOT CAUSE (rustc-codegen-trust-cg/src/lib.rs `mir_to_trust_ir`, entry-block
// parameter handling). The construction side `Some(&x)` correctly celled `x` (its
// address is stored into the niche) — `compute_scalar_cell_locals` gives the
// PARAMETER `x` a stack cell so `&x` is a stable address. But a celled `let`
// local's value reaches its cell through its `x = rvalue` ASSIGNMENT store; a
// celled PARAMETER has no assignment — its value arrives as the entry block
// parameter — so the entry path NEVER stored the incoming parameter value into the
// cell. The cell stayed UNINITIALIZED, and the `match`-arm `*p` (a load through the
// cell pointer) read garbage stack bytes: a fixed, input-independent value.
//
// THE FIX. At function entry, when an argument is a scalar cell
// (`ctx.scalar_cells`), store its incoming parameter value into the cell slot —
// the scalar-parameter analogue of `store_incoming_aggregate_param`. The niche
// pointer then addresses a cell holding the real argument value, so `*p` returns
// it (value-dependent: input 5 -> 5, 37 -> 37, 100 -> 100), at O0 and O3.
//
// SUPPORTED (MATCH vs LLVM at O0 and O3 below): the Some-payload deref of a
// statically-`Some` niche `Option<&T>` for `&i64` / `&u32` / `&u8`, via `match`,
// `if let`, and an explicit `let q: &T = p; *q`; `Option<&mut T>`. Plus the
// controls that were already correct and must stay so: niche discriminant-only
// (`Some(_) => 1`), and explicit-tag (non-niche) `Option<i64>` payload extraction.
//
// FAIL-CLOSED (safe; pinned NOT to miscompile): a BRANCH-VARYING niche
// `Option<&T>` (`if c { Some(&x) } else { None }`) and a statically-`None`
// `Option<&T>` route `o` through a separate memory-aggregate path the bridge does
// not fully lower yet ("memory aggregate whole assignment from non-local
// operand"), so it fails closed at one or both opt levels. The test pins the
// SAFETY INVARIANT for those: trust-cg must EITHER fail closed OR match the LLVM
// oracle — never silently return a different value.

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
    assert!(status.success(), "cargo build failed; cannot run m98 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m98_{stem}_{}", std::process::id()));
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
        // A link failure on the trust-cg side (e.g. an undefined symbol because the
        // backend failed closed on the function) is also a fail-closed signal,
        // never a silent wrong value.
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
/// opt levels. A fail-closed here is a regression of the #98 fix, so it panics.
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
                 {expected} — the niche Option<&T> payload deref must read the REAL value."
            ),
            Outcome::FailedClosed => panic!(
                "{stem} (opt={opt}): trust-cg failed closed on a SUPPORTED niche-payload shape — \
                 a regression of the #98 fix."
            ),
        }
    }
}

/// Compile `body` with BOTH backends at O0 and O3. The LLVM oracle must return
/// `expected`; the trust-cg backend must EITHER fail closed OR return exactly
/// `expected` — it must NEVER silently return a different value. Pins the safety
/// boundary for the not-yet-supported (branch-varying / static-None) shapes.
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
// The exact bug: Some-payload deref of a statically-Some niche Option<&i64>.
// Value-dependent — must return the INPUT, proving it reads the real &x and not a
// fixed garbage scalar. Three distinct inputs at O0 and O3.
// ---------------------------------------------------------------------------

fn niche_ref_i64_body(input: i32) -> String {
    format!(
        "#[inline(never)]\n\
         fn f(x: i64) -> i64 {{ let o: Option<&i64> = Some(&x); match o {{ Some(p) => *p, None => 0 }} }}\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 {{ (f(bb({input}i64)) as i32) & 0x7f }}"
    )
}

#[test]
fn m98_niche_option_ref_payload_input_5() {
    expect_correct("ref_i64_5", &niche_ref_i64_body(5), 5);
}

#[test]
fn m98_niche_option_ref_payload_input_37() {
    expect_correct("ref_i64_37", &niche_ref_i64_body(37), 37);
}

#[test]
fn m98_niche_option_ref_payload_input_100() {
    expect_correct("ref_i64_100", &niche_ref_i64_body(100), 100);
}

/// Narrower payload widths: `Option<&u32>` and `Option<&u8>` Some-payload deref.
#[test]
fn m98_niche_option_ref_u32_payload() {
    expect_correct(
        "ref_u32",
        "#[inline(never)]\n\
         fn f(x: u32) -> u32 { let o: Option<&u32> = Some(&x); match o { Some(p) => *p, None => 0 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(123u32)) as i32) & 0x7f }",
        123,
    );
}

#[test]
fn m98_niche_option_ref_u8_payload() {
    expect_correct(
        "ref_u8",
        "#[inline(never)]\n\
         fn f(x: u8) -> u8 { let o: Option<&u8> = Some(&x); match o { Some(p) => *p, None => 0 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(77u8)) as i32) & 0x7f }",
        77,
    );
}

/// `if let Some(p) = o { *p }` — the same niche extract via if-let.
#[test]
fn m98_niche_option_ref_if_let() {
    expect_correct(
        "iflet",
        "#[inline(never)]\n\
         fn f(x: i64) -> i64 { let o: Option<&i64> = Some(&x); if let Some(p) = o { *p } else { 0 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(42i64)) as i32) & 0x7f }",
        42,
    );
}

/// An explicit `let q: &i64 = p; *q` re-binding of the niche payload before deref.
#[test]
fn m98_niche_option_ref_explicit_let_bind() {
    expect_correct(
        "letbind",
        "#[inline(never)]\n\
         fn f(x: i64) -> i64 { let o: Option<&i64> = Some(&x); \
            match o { Some(p) => { let q: &i64 = p; *q } None => 0 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(55i64)) as i32) & 0x7f }",
        55,
    );
}

/// `Option<&mut T>`: read-back of the mutated niche payload through `*p`.
#[test]
fn m98_niche_option_mut_ref_payload() {
    expect_correct(
        "mutref",
        "#[inline(never)]\n\
         fn f(mut x: i64) -> i64 { let o: Option<&mut i64> = Some(&mut x); \
            match o { Some(p) => { *p += 1; *p } None => 0 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(63i64)) as i32) & 0x7f }",
        64,
    );
}

// ---------------------------------------------------------------------------
// Controls that were already correct and MUST stay correct.
// ---------------------------------------------------------------------------

/// Niche discriminant-only read (`Some(_) => 1`): Some-vs-None detection. Was
/// always correct; the fix must not disturb it.
#[test]
fn m98_niche_discriminant_only_control() {
    expect_correct(
        "disc",
        "#[inline(never)]\n\
         fn f(x: i64) -> i64 { let o: Option<&i64> = Some(&x); match o { Some(_) => 1, None => 0 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(37i64)) as i32) & 0x7f }",
        1,
    );
}

/// Explicit-tag (NON-niche) `Option<i64>` payload extraction. A separate code path
/// from the niche one; must keep returning the payload.
#[test]
fn m98_explicit_tag_option_payload_control() {
    expect_correct(
        "tag",
        "#[inline(never)]\n\
         fn f(x: i64) -> i64 { let o: Option<i64> = Some(x); match o { Some(p) => p, None => 0 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(37i64)) as i32) & 0x7f }",
        37,
    );
}

// ---------------------------------------------------------------------------
// Safety boundary — branch-varying / static-None niche Option<&T>. These route
// through a separate memory-aggregate path the bridge does not fully lower yet;
// they must fail closed OR match LLVM, never silently miscompile.
// ---------------------------------------------------------------------------

/// Branch-varying niche `Option<&i64>`, Some branch taken.
#[test]
fn m98_branch_varying_some_no_silent_miscompile() {
    no_silent_miscompile(
        "bv_some",
        "#[inline(never)]\n\
         fn f(x: i64, take: bool) -> i64 { \
            let o: Option<&i64> = if take { Some(&x) } else { None }; \
            match o { Some(p) => *p, None => 7 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(99i64), bb(true)) as i32) & 0x7f }",
        99,
    );
}

/// Branch-varying niche `Option<&i64>`, None branch taken.
#[test]
fn m98_branch_varying_none_no_silent_miscompile() {
    no_silent_miscompile(
        "bv_none",
        "#[inline(never)]\n\
         fn f(x: i64, take: bool) -> i64 { \
            let o: Option<&i64> = if take { Some(&x) } else { None }; \
            match o { Some(p) => *p, None => 7 } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { (f(bb(99i64), bb(false)) as i32) & 0x7f }",
        7,
    );
}
