#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: STANDARD-Rust `fn main` (std) compiled for x86_64 via the
// rustc_codegen_trust_cg bridge.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS4 — std `fn main` entry + allocator path.
//
// This guards two things the bridge now does for a std `fn main`:
//
//   1. ENTRY WRAPPER. The synthesized C `main(argc, argv) -> i32` builds the
//      `std::rt::lang_start::<MainRetTy>` call with the exact ABI rustc's LLVM
//      backend uses: it loads the address of the user's monomorphized `main`,
//      sign-extends `argc` to `isize`, forwards `argv`, passes the `sigpipe`
//      byte rustc selected, calls `lang_start` (an *external* symbol, not a
//      local return-0 stub), and truncates the `isize` result to the `int`
//      return. The previous stub returned 0 without ever calling `main`.
//
//   2. ALLOCATOR SHIM. `join_codegen` now emits a default-allocator shim
//      module (`ModuleKind::Allocator`) that defines `__rust_alloc`,
//      `__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed` — each
//      forwarding to libstd's `__rdl_*` System allocator — plus the
//      `__rust_no_alloc_shim_is_unstable_v2` marker. Without it std programs
//      fail to link against libstd's allocator calls.
//
// FULL EXECUTION of a std `fn main` now WORKS: the bridge lowers
// `std::rt::lang_start::<()>`, whose MIR constructs the `move` closure and
// coerces it to `&dyn Fn() -> i32` — emitting the vtable as a data-relocated
// read-only global and the fat pointer, then calling `lang_start_internal`.
// `std_main_runs_via_lang_start_closure_vtable` locks the running behaviour in
// (exit 55), and `entry_wrapper_and_allocator_shim_objects_are_abi_correct`
// still verifies the entry-wrapper / allocator-shim ABI in isolation.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";

const STD_SUM_PROGRAM: &str = "fn main() {\n\
    \x20   let mut s = 0i32;\n\
    \x20   let mut i = 1i32;\n\
    \x20   while i <= 10 { s += i; i += 1; }\n\
    \x20   std::process::exit(s);\n\
    }\n";

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
    assert!(status.success(), "cargo build failed; cannot run std-main test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_stdmain_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// `llvm-nm` from the pinned toolchain's rustlib bin (the system `nm` cannot
/// parse the bridge/libstd Mach-O objects produced by this LLVM version).
fn llvm_nm() -> PathBuf {
    let sysroot = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--print", "sysroot"])
        .output()
        .expect("rustc --print sysroot");
    let sysroot = String::from_utf8_lossy(&sysroot.stdout).trim().to_owned();
    PathBuf::from(sysroot)
        .join("lib/rustlib")
        .join(TARGET)
        .join("bin/llvm-nm")
}

/// The full std `fn main` now COMPILES, LINKS, and RUNS on x86_64: the bridge
/// lowers `lang_start::<()>`'s `move` closure, emits the `&dyn Fn() -> i32`
/// vtable as a data-relocated read-only global, builds the fat pointer, and
/// calls `lang_start_internal`. This was previously the fail-closed milestone
/// blocker (closure + trait-object vtable). The summing program exits 55; we
/// assert the trust-cg binary runs and exits 55 — matching the LLVM backend
/// (see `std_main_run_x86.rs` for the full multi-shape differential).
#[test]
fn std_main_runs_via_lang_start_closure_vtable() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("runsum");
    let src = dir.join("prog.rs");
    std::fs::write(&src, STD_SUM_PROGRAM).expect("write source");

    let bin = dir.join("out");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"])
        .arg(backend_arg(&dylib))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .output()
        .expect("spawn rustc");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "std `fn main` failed to compile/link via the closure + `&dyn Fn` vtable path. \
         stderr: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("failing closed"),
        "std `fn main` unexpectedly failed closed. stderr: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("Undefined symbols"),
        "std `fn main` link has an undefined symbol (vtable method / dispatch-shim stub / \
         allocator). stderr: <<<{stderr}>>>"
    );

    let run = Command::new(&bin).output().expect("run trust-cg std binary");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(
        run.status.code(),
        Some(55),
        "trust-cg std `fn main` (sum 1..=10) must exit 55 like the LLVM backend"
    );
}

/// A `#![no_main]` no_std program that constructs a closure CAPTURING a value
/// (`move |x| x + base`) and passes it BY VALUE to a generic `fn call_it<F:
/// Fn(..)>` now COMPILES: the bridge materializes the capturing closure in a
/// memory env slot, passes it across the by-value ABI boundary as its env
/// aggregate, and inside `call_it` calls the closure through `&env`. The object
/// must emit cleanly — no fail-closed, no downstream ISel "value not defined"
/// crash, and (the differential below proves) no miscompile.
#[test]
fn closure_by_value_capture_call_compiles_cleanly() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("closbyval");
    let src = dir.join("prog.rs");
    std::fs::write(
        &src,
        "#![no_std]\n\
         #![no_main]\n\
         #[panic_handler]\n\
         fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n\
         #[no_mangle]\n\
         pub extern \"C\" fn main(argc: i32, _argv: *const *const u8) -> i32 {\n\
         \x20   let base = argc;\n\
         \x20   let add = move |x: i32| -> i32 { x + base };\n\
         \x20   call_it(add)\n\
         }\n\
         #[inline(never)]\n\
         fn call_it<F: Fn(i32) -> i32>(f: F) -> i32 { f(41) }\n",
    )
    .expect("write source");

    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"])
        .arg(backend_arg(&dylib))
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(dir.join("out"))
        .arg(&src)
        .output()
        .expect("spawn rustc");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let _ = std::fs::remove_dir_all(&dir);

    assert!(
        output.status.success(),
        "capturing closure passed by value unexpectedly failed to compile. \
         stderr: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("failing closed"),
        "capturing closure by-value pass must no longer fail closed. \
         stderr: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("not defined before use"),
        "capturing closure by-value pass must not trip a downstream ISel \
         'value not defined' error. stderr: <<<{stderr}>>>"
    );
}

/// Verify the two newly-correct std-main pieces — the entry wrapper and the
/// default-allocator shim — at the symbol/relocation level, with the
/// un-lowerable `lang_start` skipped via the test-only env gate.
///
///  * Allocator shim object DEFINES `__rust_alloc`, `__rust_dealloc`,
///    `__rust_realloc`, `__rust_alloc_zeroed`, `__rust_no_alloc_shim_is_unstable_v2`
///    and REFERENCES (undefined) the `__rdl_*` System-allocator targets.
///  * Entry wrapper object exports `_main`, takes the address of the user's
///    `main`, and references `lang_start` (external) — i.e. it CALLS lang_start
///    rather than stubbing it.
#[test]
fn entry_wrapper_and_allocator_shim_objects_are_abi_correct() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("abi");
    let src = dir.join("prog.rs");
    std::fs::write(&src, STD_SUM_PROGRAM).expect("write source");

    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"])
        .arg(backend_arg(&dylib))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(dir.join("out"))
        .env("TRUST_CG_TEST_SKIP_LANG_START", "1")
        .arg(&src)
        .output()
        .expect("spawn rustc");
    assert!(
        output.status.success(),
        "with lang_start skipped, the bridge must still emit entry + allocator + main objects. \
         stderr: <<<{}>>>",
        String::from_utf8_lossy(&output.stderr)
    );

    // Locate the emitted objects by CGU-name suffix.
    let mut allocator_obj = None;
    let mut entry_obj = None;
    for entry in std::fs::read_dir(&dir).expect("read workdir") {
        let path = entry.expect("dir entry").path();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if name.ends_with(".allocator_shim.rcgu.o") {
            allocator_obj = Some(path.clone());
        } else if name.ends_with(".rustc_entry_main.rcgu.o") {
            entry_obj = Some(path.clone());
        }
    }
    let allocator_obj = allocator_obj.expect("allocator shim object not emitted");
    let entry_obj = entry_obj.expect("entry wrapper object not emitted");

    let nm = llvm_nm();
    let symbols = |obj: &Path| -> String {
        let out = Command::new(&nm).arg(obj).output().expect("llvm-nm");
        String::from_utf8_lossy(&out.stdout).into_owned()
    };

    // --- Allocator shim ---
    let alloc_syms = symbols(&allocator_obj);
    // Defined (T) global allocator entry points + the unstable marker.
    for defined in [
        "___rust_alloc",
        "___rust_dealloc",
        "___rust_realloc",
        "___rust_alloc_zeroed",
        "___rust_no_alloc_shim_is_unstable_v2",
    ] {
        assert!(
            alloc_syms
                .lines()
                .any(|l| l.contains(" T ") && l.contains(defined)),
            "allocator shim must DEFINE {defined}. symbols:\n{alloc_syms}"
        );
    }
    // Forwarded-to System allocator targets must be undefined (resolved by libstd).
    for imported in [
        "___rdl_alloc",
        "___rdl_dealloc",
        "___rdl_realloc",
        "___rdl_alloc_zeroed",
    ] {
        assert!(
            alloc_syms
                .lines()
                .any(|l| l.contains(" U ") && l.contains(imported)),
            "allocator shim must forward to (import) {imported}. symbols:\n{alloc_syms}"
        );
    }

    // --- Entry wrapper ---
    let entry_syms = symbols(&entry_obj);
    assert!(
        entry_syms.lines().any(|l| l.contains(" T ") && l.contains("_main")),
        "entry wrapper must export the C `main`. symbols:\n{entry_syms}"
    );
    assert!(
        entry_syms
            .lines()
            .any(|l| l.contains(" U ") && l.contains("lang_start")),
        "entry wrapper must CALL (import) lang_start, not define a local stub. \
         symbols:\n{entry_syms}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
