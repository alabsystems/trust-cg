#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the ONE-LANE WIDE-POINTER BOUNDARY GUARD on x86-64 — a
// NEGATIVE pin. A by-value `NonNull<[T]>` / `Unique<[T]>` / `Box<[T]>`
// parameter or return is a `repr(transparent)` newtype chain over a
// `*const [T] is !null` pattern type. Inside a body the bridge deliberately
// carries such a value as its DATA pointer with the length in a side table;
// at a FUNCTION BOUNDARY that model has no channel for the length, and rustc
// (and every LLVM-built caller or callee) places `{data, len}` in RDI:RSI /
// RAX:RDX (`PassMode::Pair`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Measured 2026-09-22 on the bridge BEFORE the guard: `fn ident(p:
// NonNull<[u8]>) -> NonNull<[u8]>` was emitted as `mov rcx, rdi; mov rax,
// rcx; ret` — one register in, one out — and `fn mk(s: &[u8]) -> NonNull<[u8]>`
// returned RAX alone, so an LLVM caller read the length out of whatever RDX
// held. Neither ABI gate saw it: the argument gate ran only on the by-value
// AGGREGATE branch and the return gate only for a memory-aggregate output.
//
// The capability half landed the same day (`wide_slice_carrier_layout`:
// the transparent slice / `str` newtype chain takes the two-lane slot `&[T]`
// has), so the `NonNull<[u8]>` / `NonNull<str>` shapes now COMPILE here and
// their register agreement lives in `m141`'s four-combination matrix. What
// this file pins is the guard that remains: `Box<[u8]>` (the `owned_box`
// lang struct is not `repr(transparent)` and keeps its one-scalar in-body
// model) must REFUSE by name — as argument and as return, at O0 and O2 —
// while the LLVM oracle compiles it; a real slice fat pointer (`&[u8]`, `*const [u8]`) and a
// `NonNull<dyn Debug>` (already the two-lane `{data, vtable}` image through the
// thin-raw-pointer-to-`dyn` lane, never one scalar) must keep compiling.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

const TARGET: &str = host_target_support::X86_64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m142_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` as an rlib with `backend` (None = LLVM) at `opt`; `Ok(())` on
/// success, `Err(stderr)` on a compile failure.
fn compile_rlib(
    dir: &Path,
    dylib: Option<&Path>,
    opt: &str,
    krate: &str,
    src: &str,
) -> Result<(), String> {
    let src_path = dir.join(format!("{krate}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let out_dir = dir.join(format!(
        "{krate}_{}_O{opt}",
        if dylib.is_some() { "tcg" } else { "llvm" }
    ));
    std::fs::create_dir_all(&out_dir).expect("create out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", krate]);
    if let Some(dylib) = dylib {
        let mut backend_arg = OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
    }
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("--out-dir")
    .arg(&out_dir)
    .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// `(crate name, source, the refusal tag trust-cg must raise; None = must compile)`.
fn shapes() -> Vec<(&'static str, &'static str, Option<&'static str>)> {
    vec![
        (
            "identarg",
            "#![no_std]\nuse core::ptr::NonNull;\n\
             #[inline(never)] pub fn ident(p: NonNull<[u8]>) -> NonNull<[u8]> { p }\n",
            None,
        ),
        (
            "mkret",
            "#![no_std]\nuse core::ptr::NonNull;\n\
             #[inline(never)] pub fn mk(s: &[u8]) -> NonNull<[u8]> { NonNull::from(s) }\n",
            None,
        ),
        (
            "strarg",
            "#![no_std]\nuse core::ptr::NonNull;\n\
             #[inline(never)] pub fn take(p: NonNull<str>) -> usize { let _ = p; 1 }\n",
            None,
        ),
        (
            "boxarg",
            "#![no_std]\nextern crate alloc;\nuse alloc::boxed::Box;\n\
             #[inline(never)] pub fn bx(b: Box<[u8]>) -> usize { b.len() }\n",
            Some("[TCG-ARG-ABI]"),
        ),
        (
            "boxret",
            "#![no_std]\nextern crate alloc;\nuse alloc::boxed::Box;\n\
             #[inline(never)] pub fn mkbx(b: Box<[u8]>) -> Box<[u8]> { b }\n",
            Some("[TCG-ARG-ABI]"),
        ),
        (
            "dynarg",
            "#![no_std]\nuse core::ptr::NonNull;\n\
             #[inline(never)] pub fn take(p: NonNull<dyn core::fmt::Debug>) -> usize { let _ = p; 1 }\n",
            None,
        ),
        // IN-BODY shapes (2026-09-22 review): a slotted two-lane newtype must
        // never be read or written through the generic ONE-lane scalar path. The
        // deref-store through `&mut NonNull<[u8]>` emitted one lane silently
        // before the fail-closed rule landed and must REFUSE; a struct with a
        // `NonNull<[u8]>` field built from a slotted parameter writes both lanes
        // (measured against LLVM with a poisoned stack:
        // `bridge_corpus/nonnull_holder_field.rs`, exit 77) and must COMPILE.
        (
            "torn",
            "#![no_std]\nuse core::ptr::NonNull;\n\
             #[inline(never)] pub fn set(slot: &mut NonNull<[u8]>, p: NonNull<[u8]>) { *slot = p; }\n",
            Some("[TCG-MIR-UNSUPPORTED]"),
        ),
        (
            "holder",
            "#![no_std]\nuse core::ptr::NonNull;\npub struct Holder { pub p: NonNull<[u8]>, pub n: u64 }\n\
             #[inline(never)] pub fn mk(p: NonNull<[u8]>, n: u64) -> Holder { Holder { p, n } }\n",
            None,
        ),
        (
            "sliceok",
            "#![no_std]\n\
             #[inline(never)] pub fn len(s: &[u8]) -> usize { s.len() }\n\
             #[inline(never)] pub fn first(s: &[u8]) -> &[u8] { s }\n",
            None,
        ),
        (
            "rawsliceok",
            "#![no_std]\n\
             #[inline(never)] pub fn raw(s: &[u8]) -> *const [u8] { s as *const [u8] }\n",
            None,
        ),
    ]
}

/// Shapes rustc's O2 pipeline folds away (the closure inlines, the raw store
/// becomes a plain copy), so they are pinned at O0 only.
fn o0_only_shapes() -> Vec<(&'static str, &'static str, Option<&'static str>)> {
    vec![
        (
            "clo",
            "#![no_std]\nuse core::ptr::NonNull;\n\
             #[inline(never)] pub fn clo(p: NonNull<[u8]>) -> usize { let f = |q: NonNull<[u8]>| q.len(); f(p) }\n",
            Some("[TCG-MIR-UNSUPPORTED]"),
        ),
        (
            "rawstore",
            "#![no_std]\nuse core::ptr::NonNull;\n\
             #[inline(never)] pub fn f(p: NonNull<[u8]>, q2: NonNull<[u8]>) -> usize { let mut q = p; unsafe { *(&raw mut q) = q2; } q.len() }\n",
            Some("[TCG-MIR-UNSUPPORTED]"),
        ),
    ]
}

#[test]
fn transparent_wide_newtype_signatures_lower_and_box_slice_still_refuses_x86_64() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("guard");
    let mut failures = Vec::new();
    for (opt, list) in [("0", shapes()), ("2", shapes()), ("0", o0_only_shapes())] {
        for (krate, src, expect_tag) in list {
            compile_rlib(&dir, None, opt, krate, src)
                .unwrap_or_else(|e| panic!("LLVM `{krate}` failed at O{opt}: <<<{e}>>>"));
            match (
                compile_rlib(&dir, Some(&dylib), opt, krate, src),
                expect_tag,
            ) {
                (Ok(()), Some(tag)) => failures.push(format!(
                    "O{opt} `{krate}`: trust-cg COMPILED a one-lane wide-pointer signature \
                     that must refuse with {tag}"
                )),
                (Err(stderr), Some(tag)) => {
                    if !stderr.contains(tag) {
                        failures.push(format!(
                            "O{opt} `{krate}`: refused, but not by name ({tag} absent): <<<{}>>>",
                            stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                        ));
                    }
                }
                (Err(stderr), None) => failures.push(format!(
                    "O{opt} `{krate}`: a real slice fat pointer must keep compiling: <<<{}>>>",
                    stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                )),
                (Ok(()), None) => {}
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} boundary-guard expectation(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
