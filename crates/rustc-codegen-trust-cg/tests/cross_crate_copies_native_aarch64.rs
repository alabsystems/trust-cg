// Other hosts compile no native test; a Darwin host must meet every prerequisite.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Native execution differential (aarch64-apple-darwin): two crates, each built
// by rustc/LLVM or by this backend, linked into one program.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// An `rlib` (`xlib`, overflow checks OFF) and a `staticlib` using it (overflow
// checks ON) are compiled in every backend pairing but LLVM/LLVM, which is the
// oracle, at `-Copt-level=0`, `1` and `2`, with one and with sixteen codegen
// units, linked with one C driver and run. The program covers:
//
// * CRATE-AGNOSTIC COPIES. rustc copies a non-generic `#[inline]` core
//   function into every crate that uses it under a symbol that names no crate
//   (`str::as_ptr` at `-Copt-level=0`; `u32::pow`, `overflowing_pow` and
//   `isqrt` at `1` and above). Each crate's copy must stay its own: two
//   crates of this backend defining it as one strong symbol fail to link, and
//   a crate whose copy was compiled without overflow checks must not bind to
//   another crate's checked copy (`lib_pow(3, 21)` wraps in `xlib`; bound to
//   the staticlib's checked `pow` it panics).
// * STATIC IDENTITY. An upstream static is one location, whichever crate
//   names it: `ptr::eq` between the staticlib's references and `xlib`'s own,
//   including a `&str` and a reference stored in upstream statics.
//
// PROOF GATE: compiled with `no-proof-certs`; this is an execution
// differential, not a certification claim.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

const LIB: &str = r#"
#![no_std]
pub static S: u32 = 5;
pub static T: [u16; 4] = [1, 2, 3, 4];
pub static STR: &str = "hello";
pub static REF: &u32 = &S;
#[inline(never)] pub fn addr_s() -> *const u32 { &S }
#[inline(never)] pub fn addr_t2() -> *const u16 { &T[2] }
#[inline(never)] pub fn str_ptr() -> *const u8 { STR.as_ptr() }
#[inline(never)] pub fn ref_ptr() -> *const u32 { REF }
#[inline(never)] pub fn lib_ptr(s: &str) -> usize { s.as_ptr() as usize }
pub mod other {
    #[inline(never)] pub fn lib_ptr2(s: &str) -> usize { s.as_ptr() as usize }
}
#[inline(never)] pub fn lib_pow(x: u32, y: u32) -> u32 { x.pow(y) }
#[inline(never)]
pub fn lib_mix(x: u32, y: u32) -> u32 { x.pow(y & 7) ^ x.isqrt() ^ (x as u64).isqrt() as u32 }
"#;

const MAIN: &str = r#"
#![no_std]
extern "C" { fn abort() -> !; }
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { unsafe { abort() } }
use core::ptr::eq;
use xlib::*;
#[no_mangle]
pub extern "C" fn m_as_ptr(i: u32) -> u32 {
    let s = if i & 1 == 0 { "abc" } else { "defgh" };
    let s = core::hint::black_box(s);
    (s.as_ptr() as usize == lib_ptr(s)) as u32 | ((other::lib_ptr2(s) == lib_ptr(s)) as u32) << 1
}
#[no_mangle]
pub extern "C" fn m_pow(i: u32) -> u32 {
    let x = core::hint::black_box(i % 4 + 3);
    x.pow(2) ^ lib_pow(x, 21)
}
#[no_mangle]
pub extern "C" fn m_mix(i: u32) -> u32 {
    let x = core::hint::black_box(i % 20);
    (x.pow(x & 7) ^ x.isqrt() ^ (x as u64).isqrt() as u32) ^ lib_mix(x, x).rotate_left(8)
}
#[no_mangle]
pub extern "C" fn m_statics() -> u32 {
    eq(&S, addr_s()) as u32
        | (eq(&T[2], addr_t2()) as u32) << 1
        | (eq(STR.as_ptr(), str_ptr()) as u32) << 2
        | (eq(REF, ref_ptr()) as u32) << 3
        | (eq(REF, &S) as u32) << 4
        | (eq(REF, addr_s()) as u32) << 5
        | (S + T[3] as u32 + STR.len() as u32 + *REF) << 8
}
"#;

const DRIVER_C: &str = r#"
#include <stdio.h>
#include <stdint.h>
__attribute__((weak)) void rust_eh_personality(void) {}
extern uint32_t m_as_ptr(uint32_t), m_pow(uint32_t), m_mix(uint32_t), m_statics(void);
int main(void) {
    for (uint32_t i = 0; i < 24; i++) {
        printf("%u %u %u\n", m_as_ptr(i), m_pow(i), m_mix(i));
    }
    printf("%u\n", m_statics());
    return 0;
}
"#;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_cc_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// One compile with this backend when `backend` is set, LLVM otherwise.
fn rustc(backend: Option<&Path>, opt: u32, cgus: u32, overflow_checks: bool) -> Command {
    let mut command = toolchain_support::rustc_command();
    command
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Ccodegen-units={cgus}"))
        .arg(format!(
            "-Coverflow-checks={}",
            if overflow_checks { "on" } else { "off" }
        ));
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        command
            .arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    command
}

fn run_checked(mut command: Command, what: &str) {
    let output = command.output().expect("spawn compiler");
    assert!(
        output.status.success(),
        "{what} failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Build `xlib` with `lib_backend` and the staticlib with `main_backend`,
/// link them with the C driver, run it and return its stdout.
fn build_and_run(
    dir: &Path,
    label: &str,
    lib_backend: Option<&Path>,
    main_backend: Option<&Path>,
    opt: u32,
    cgus: u32,
    sources: (&Path, &Path, &Path),
) -> String {
    let (lib_source, main_source, driver) = sources;
    let out = dir.join(label);
    std::fs::create_dir_all(&out).expect("config dir");
    let rlib = out.join("libxlib.rlib");
    let mut lib = rustc(lib_backend, opt, cgus, false);
    lib.args(["--crate-type", "rlib", "--crate-name", "xlib", "-o"])
        .arg(&rlib)
        .arg(lib_source);
    run_checked(lib, &format!("{label}: xlib compile"));
    let staticlib = out.join("libmain.a");
    let mut extern_arg = std::ffi::OsString::from("xlib=");
    extern_arg.push(&rlib);
    let mut main = rustc(main_backend, opt, cgus, true);
    main.args([
        "--crate-type",
        "staticlib",
        "--crate-name",
        "ccmain",
        "--extern",
    ])
    .arg(extern_arg)
    .arg("-L")
    .arg(&out)
    .arg("-o")
    .arg(&staticlib)
    .arg(main_source);
    run_checked(main, &format!("{label}: staticlib compile"));
    let exe = out.join("prog");
    let link = Command::new("cc")
        .arg(driver)
        .arg(&staticlib)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("spawn cc");
    assert!(
        link.status.success(),
        "{label}: link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&exe).output().expect("run driver");
    assert!(
        run.status.success(),
        "{label}: driver exited {:?}",
        run.status
    );
    let _ = std::fs::remove_dir_all(&out);
    String::from_utf8(run.stdout).expect("utf-8 stdout")
}

#[test]
fn cross_crate_inline_copies_and_static_identity_agree_with_llvm_aarch64() {
    darwin_native::require("cross_crate_copies_native_aarch64", &["cc"]);
    let backend = backend_artifact_support::current_test_backend();
    let dir = workdir("diff");
    let lib_source = dir.join("xlib.rs");
    std::fs::write(&lib_source, LIB).expect("write xlib");
    let main_source = dir.join("ccmain.rs");
    std::fs::write(&main_source, MAIN).expect("write main");
    let driver = dir.join("driver.c");
    std::fs::write(&driver, DRIVER_C).expect("write driver");
    let sources = (
        lib_source.as_path(),
        main_source.as_path(),
        driver.as_path(),
    );
    for opt in [0, 1, 2] {
        for cgus in [1, 16] {
            let config = format!("O{opt}-cgu{cgus}");
            let oracle = build_and_run(
                &dir,
                &format!("llvm-llvm-{config}"),
                None,
                None,
                opt,
                cgus,
                sources,
            );
            // Every upstream static reference agrees and the sum is 5+4+5+5.
            assert!(
                oracle.ends_with(&format!("{}\n", 0x3f | (19 << 8))),
                "{config}: unexpected oracle output:\n{oracle}"
            );
            for (lib, main, pairing) in [
                (Some(backend.as_path()), Some(backend.as_path()), "tcg-tcg"),
                (None, Some(backend.as_path()), "llvm-tcg"),
                (Some(backend.as_path()), None, "tcg-llvm"),
            ] {
                let label = format!("{pairing}-{config}");
                let ours = build_and_run(&dir, &label, lib, main, opt, cgus, sources);
                assert_eq!(ours, oracle, "{label}: output differs from LLVM/LLVM");
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    eprintln!("CROSS_CRATE_COPIES cells=6 llvm_runs=6 cg_runs=18 opts=0,1,2 cgus=1,16");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
