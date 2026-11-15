#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a reference to a FIELD of the pointee of a thin reference
// ENTRY ARGUMENT, stored into a scalar cell, is the field's real address
// (`arg + rustc layout offset`), checked ACROSS the backend boundary in all four
// rlib x bin combinations at every optimization level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The shape is derived `Debug`'s last field: `&&self.reg_save_area`. The
// field reference `_n = &(*self).3` is itself borrowed and the borrow unsized
// to `&dyn Debug`, so `compute_scalar_cell_locals`'s unsize pass gives `_n` a
// cell and the assignment becomes a store through a deref place. That store
// path admitted a field address only for a primitive leaf or a pointee
// `memory_aggregate_ref_pointee` routes, so on x86-64 macOS a raw-pointer field
// of a flat `#[repr(C)]` struct refused:
//
//     Place deref memory store from Rvalue::Ref (projected source's base is not
//     a reference to a memory-eligible aggregate): source local _1 projection
//     [Deref, Field(3, *const c_void)] ... entry_arg=true
//
// That is `<core::ffi::va_list::VaListInner as Debug>::fmt`, the one
// `library/core` lowering refusal on this host at O0. A nested-struct field
// (`&&self.inner`) refused one step later, from the scalar-leaf query of
// `memory_aggregate_ref_address` (`Ty::Adt multi-field struct Inner`).
//
// Rows. `Peek` is a callee trait implemented for field REFERENCES, so `&r as
// &dyn Peek` is the cell-forcing unsize without any formatting machinery, and
// its method reads the field through the stored address: a wrong offset reads
// a sibling field and the row exits 7. `write_reg` also WRITES through a
// `&mut` field reference and re-reads the field through the argument, and the
// caller checks the write landed in its own struct and nowhere else. The
// `debug_*` rows drive the real derived/hand-written `Debug::fmt` into a
// comparing `fmt::Write` sink: `debug_valike` etc. instantiate it in the
// callee crate, `debug_is` in whichever crate instantiates the generic.
// `peek_q` (a `repr(Rust)` struct rustc reorders) and `pass_inner` (a field
// reference passed on as `&&Inner`, never celled) lowered before the fix and
// pin that it moved nothing.
//
// The bridge compiles with `no-proof-certs`, as `tests/tools/m145_xback.py`
// does: the rows judge addresses across the backend boundary, not proof
// promotion. Executes only on an x86-64 host with the host x86-64 `rust-std`.
// The cargo harness cannot dlopen a stage1-linked bridge under the pinned pack
// compiler; `tests/tools/m145_xback.py --test
// tests/m148_x86_entry_ref_field_addr_xback.rs` drives the same callee and rows
// (extracted from this file) with a `trustc` that can.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m148_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Backend {
    Llvm,
    TrustCg,
}

impl Backend {
    fn tag(self) -> &'static str {
        match self {
            Backend::Llvm => "llvm",
            Backend::TrustCg => "tcg",
        }
    }
}

fn compile_callee_rlib(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    knobs: &[&str],
) -> Result<PathBuf, String> {
    let src_path = dir.join("callee.rs");
    std::fs::write(&src_path, CALLEE_SRC).expect("write callee source");
    let out_dir = dir.join(format!(
        "callee_{}_O{opt}_{}",
        backend.tag(),
        knobs.join("_")
    ));
    std::fs::create_dir_all(&out_dir).expect("create callee out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", "callee"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib))
            .arg(toolchain_support::backend_knobs_arg(knobs));
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
    let output = cmd.output().expect("spawn rustc for the callee rlib");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(out_dir.join("libcallee.rlib"))
}

#[allow(clippy::too_many_arguments)]
fn compile_caller_bin(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    shape: &str,
    body: &str,
    rlib: &Path,
    rlib_backend: Backend,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("caller_{shape}.rs"));
    std::fs::write(&src_path, format!("{CALLER_HDR}{body}")).expect("write caller source");
    let bin = dir.join(format!(
        "caller_{shape}_{}rlib_{}bin_O{opt}",
        rlib_backend.tag(),
        backend.tag()
    ));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let mut extern_arg = OsString::from("callee=");
    extern_arg.push(rlib);
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("--extern")
    .arg(&extern_arg)
    .arg("-L")
    .arg(rlib.parent().expect("rlib directory"))
    .arg("-o")
    .arg(&bin)
    .arg(&src_path);
    let output = cmd.output().expect("spawn rustc for the caller bin");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

fn run_exit_code(bin: &Path) -> i32 {
    let out = Command::new(bin).output().expect("run binary");
    out.status
        .code()
        .unwrap_or_else(|| panic!("{bin:?} exited via signal: {:?}", out.status))
}

/// The callee crate. Every `peek_*` borrows a field through its argument,
/// borrows THAT reference and unsizes it to `&dyn Peek`: the unsize is what
/// cells the field reference. `Peek` reads the field back through the stored
/// address.
const CALLEE_SRC: &str = r#"
#![feature(formatting_options)]
use core::ffi::c_void;
use core::fmt;
#[derive(Debug, Clone, Copy)] #[repr(C)]
pub struct VaLike { pub gp_offset: i32, pub fp_offset: i32, pub overflow_arg_area: *const c_void, pub reg_save_area: *const c_void }
#[derive(Debug, Clone, Copy)]
pub struct Reordered { pub a: u8, pub p: *const u8, pub b: u16, pub q: *const u32 }
#[derive(Debug, Clone, Copy)] #[repr(C)]
pub struct Inner { pub x: u64, pub p: *const u8 }
#[derive(Debug, Clone, Copy)] #[repr(C)]
pub struct Outer { pub tag: u64, pub inner: Inner }
#[derive(Debug, Clone, Copy)] #[repr(transparent)]
pub struct W(pub *const u8);
#[derive(Clone, Copy)] #[repr(C)]
pub struct Wrapped { pub n: u32, pub w: W }
impl fmt::Debug for Wrapped {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { let p = &self.w.0; f.debug_struct("Wrapped").field("n", &self.n).field("w0", &p).finish() }
}
pub trait Peek { fn peek(&self) -> u64; }
impl Peek for &*const c_void { fn peek(&self) -> u64 { **self as u64 } }
impl Peek for &mut *const c_void { fn peek(&self) -> u64 { **self as u64 } }
impl Peek for &*const u8 { fn peek(&self) -> u64 { **self as u64 } }
impl Peek for &*const u32 { fn peek(&self) -> u64 { **self as u64 } }
impl Peek for &Inner { fn peek(&self) -> u64 { self.x + self.p as u64 } }
#[inline(never)] pub fn peek_reg(v: &VaLike) -> u64 { let r = &v.reg_save_area; let d: &dyn Peek = &r; d.peek() }
#[inline(never)] pub fn peek_overflow(v: &VaLike) -> u64 { let r = &v.overflow_arg_area; let d: &dyn Peek = &r; d.peek() }
#[inline(never)] pub fn write_reg(v: &mut VaLike, np: *const c_void) -> u64 { let r = &mut v.reg_save_area; let d: &dyn Peek = &r; let old = d.peek(); *r = np; old + v.reg_save_area as u64 }
#[inline(never)] pub fn peek_q(v: &Reordered) -> u64 { let r = &v.q; let d: &dyn Peek = &r; d.peek() }
#[inline(never)] pub fn peek_w(v: &Wrapped) -> u64 { let r = &v.w.0; let d: &dyn Peek = &r; d.peek() }
#[inline(never)] pub fn peek_inner(v: &Outer) -> u64 { let r = &v.inner; let d: &dyn Peek = &r; d.peek() }
#[inline(never)] pub fn peek_tuple(t: &(u32, *const u8)) -> u64 { let r = &t.1; let d: &dyn Peek = &r; d.peek() }
#[inline(never)] fn take(r: &&Inner) -> u64 { r.x + r.p as u64 }
#[inline(never)] pub fn pass_inner(v: &Outer) -> u64 { let r = &v.inner; take(&r) }
struct Cmp<'a> { want: &'a [u8], pos: usize, ok: bool }
impl fmt::Write for Cmp<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for &b in s.as_bytes() { if self.pos >= self.want.len() || self.want[self.pos] != b { self.ok = false; } self.pos += 1; }
        Ok(())
    }
}
#[inline(never)] pub fn debug_is<T: fmt::Debug>(v: &T, want: &str) -> bool {
    let mut c = Cmp { want: want.as_bytes(), pos: 0, ok: true };
    let mut f = fmt::Formatter::new(&mut c, fmt::FormattingOptions::new());
    let r = fmt::Debug::fmt(v, &mut f).is_ok();
    r && c.ok && c.pos == c.want.len()
}
#[inline(never)] pub fn debug_valike(v: &VaLike, want: &str) -> bool { debug_is(v, want) }
#[inline(never)] pub fn debug_outer(v: &Outer, want: &str) -> bool { debug_is(v, want) }
#[inline(never)] pub fn debug_wrapped(v: &Wrapped, want: &str) -> bool { debug_is(v, want) }
#[inline(never)] pub fn debug_reordered(v: &Reordered, want: &str) -> bool { debug_is(v, want) }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    use core::ffi::c_void;\n\
    use callee::*;\n\
    fn exit(ok: bool) -> ! { std::process::exit(if ok { 42 } else { 7 }) }\n\
    fn va() -> VaLike { black_box(VaLike { gp_offset: 1, fp_offset: 2, overflow_arg_area: 0x1000 as *const c_void, reg_save_area: 0x2468 as *const c_void }) }\n\
    fn outer() -> Outer { black_box(Outer { tag: 9, inner: Inner { x: 5, p: 0x3000 as *const u8 } }) }\n\
    fn wrapped() -> Wrapped { black_box(Wrapped { n: 3, w: W(0x4400 as *const u8) }) }\n\
    fn reordered() -> Reordered { black_box(Reordered { a: 1, p: 0x10 as *const u8, b: 2, q: 0x5550 as *const u32 }) }\n";

/// `(shape, caller body, expected exit code)`. Every row exits 42 exactly when
/// each value read back through a field reference is that field's.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        (
            "va_peek_reg",
            r#"fn main() { exit(peek_reg(&va()) == 0x2468) }"#,
            42,
        ),
        (
            "va_peek_overflow",
            r#"fn main() { exit(peek_overflow(&va()) == 0x1000) }"#,
            42,
        ),
        (
            "va_write_reg",
            r#"fn main() { let mut v = va(); let s = write_reg(&mut v, black_box(0x1357 as *const c_void)); exit(s == 0x2468 + 0x1357 && v.reg_save_area as u64 == 0x1357 && v.overflow_arg_area as u64 == 0x1000 && v.gp_offset == 1 && v.fp_offset == 2) }"#,
            42,
        ),
        (
            "va_debug_in_callee",
            r#"fn main() { exit(debug_valike(&va(), black_box("VaLike { gp_offset: 1, fp_offset: 2, overflow_arg_area: 0x1000, reg_save_area: 0x2468 }"))) }"#,
            42,
        ),
        (
            "va_debug_in_caller",
            r#"fn main() { exit(debug_is(&va(), black_box("VaLike { gp_offset: 1, fp_offset: 2, overflow_arg_area: 0x1000, reg_save_area: 0x2468 }"))) }"#,
            42,
        ),
        (
            "field_of_field",
            r#"fn main() { exit(peek_w(&wrapped()) == 0x4400) }"#,
            42,
        ),
        (
            "field_of_field_debug",
            r#"fn main() { exit(debug_wrapped(&wrapped(), black_box("Wrapped { n: 3, w0: 0x4400 }"))) }"#,
            42,
        ),
        (
            "aggregate_field",
            r#"fn main() { exit(peek_inner(&outer()) == 5 + 0x3000) }"#,
            42,
        ),
        (
            "aggregate_field_debug",
            r#"fn main() { exit(debug_outer(&outer(), black_box("Outer { tag: 9, inner: Inner { x: 5, p: 0x3000 } }")) && debug_is(&outer(), black_box("Outer { tag: 9, inner: Inner { x: 5, p: 0x3000 } }"))) }"#,
            42,
        ),
        (
            "aggregate_field_passed_on",
            r#"fn main() { exit(pass_inner(&outer()) == 5 + 0x3000) }"#,
            42,
        ),
        (
            "tuple_field",
            r#"fn main() { exit(peek_tuple(&black_box((7u32, 0x6600 as *const u8))) == 0x6600) }"#,
            42,
        ),
        (
            "reordered_field",
            r#"fn main() { let r = reordered(); exit(peek_q(&r) == 0x5550 && debug_reordered(&r, black_box("Reordered { a: 1, p: 0x10, b: 2, q: 0x5550 }"))) }"#,
            42,
        ),
    ]
}

#[test]
fn entry_reference_field_addresses_cross_the_backend_boundary() {
    if !cfg!(target_arch = "x86_64") || !host_target_support::HOST_OS_SUPPORTED {
        eprintln!("skipping: the lane runs natively on an x86-64 Linux or macOS host");
        return;
    }
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("skipping: rust-std for {TARGET} not installed for the pinned toolchain");
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("addr");
    let mut failures = Vec::new();
    for opt in ["0", "1", "2", "3"] {
        let llvm_rlib = compile_callee_rlib(&dir, &dylib, Backend::Llvm, opt, &[])
            .unwrap_or_else(|e| panic!("LLVM `callee` rlib failed at O{opt}: <<<{e}>>>"));
        let tcg_rlib =
            match compile_callee_rlib(&dir, &dylib, Backend::TrustCg, opt, &["no-proof-certs"]) {
                Ok(rlib) => rlib,
                Err(e) => {
                    failures.push(format!(
                        "O{opt}: trust-cg callee rlib failed closed: <<<{}>>>",
                        e.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
                    ));
                    continue;
                }
            };
        for (shape, body, expected) in shapes() {
            let oracle = compile_caller_bin(
                &dir,
                &dylib,
                Backend::Llvm,
                opt,
                shape,
                body,
                &llvm_rlib,
                Backend::Llvm,
            )
            .unwrap_or_else(|e| panic!("LLVM caller `{shape}` failed at O{opt}: <<<{e}>>>"));
            let oracle_exit = run_exit_code(&oracle);
            assert_eq!(
                oracle_exit, expected,
                "oracle (LLVM+LLVM) exit for `{shape}` at O{opt} is {oracle_exit}, expected {expected}"
            );
            for (bin_backend, rlib, rlib_backend, label) in [
                (
                    Backend::TrustCg,
                    &llvm_rlib,
                    Backend::Llvm,
                    "LLVM callee + trust-cg caller",
                ),
                (
                    Backend::Llvm,
                    &tcg_rlib,
                    Backend::TrustCg,
                    "trust-cg callee + LLVM caller",
                ),
                (
                    Backend::TrustCg,
                    &tcg_rlib,
                    Backend::TrustCg,
                    "trust-cg callee + trust-cg caller",
                ),
            ] {
                match compile_caller_bin(
                    &dir,
                    &dylib,
                    bin_backend,
                    opt,
                    shape,
                    body,
                    rlib,
                    rlib_backend,
                ) {
                    Ok(bin) => {
                        let exit = run_exit_code(&bin);
                        if exit != oracle_exit {
                            failures.push(format!(
                                "O{opt} `{shape}` {label}: exit {exit}, oracle {oracle_exit}"
                            ));
                        }
                    }
                    Err(e) => failures.push(format!(
                        "O{opt} `{shape}` {label}: trust-cg caller failed closed: <<<{}>>>",
                        e.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                    )),
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} field-address combination(s) disagreed or refused:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

/// The opt-out restores the refusal this lane closes, from the same backend
/// build: the fails-before half of the evidence, without a second dylib.
#[test]
fn the_opt_out_restores_the_deref_store_refusal() {
    if !cfg!(target_arch = "x86_64") || !host_target_support::HOST_OS_SUPPORTED {
        eprintln!("skipping: the lane runs natively on an x86-64 Linux or macOS host");
        return;
    }
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("skipping: rust-std for {TARGET} not installed for the pinned toolchain");
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("optout");
    let err = compile_callee_rlib(
        &dir,
        &dylib,
        Backend::TrustCg,
        "0",
        &["no-proof-certs", "no-x86-entry-ref-field-addr"],
    )
    .expect_err("with the opt-out the callee must refuse the entry-reference field borrow");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        err.contains(
            "Place deref memory store from Rvalue::Ref (projected source's base is not a \
             reference to a memory-eligible aggregate)"
        ) && err.contains("[Deref, Field(3, *const std::ffi::c_void)]"),
        "the opt-out refused, but not with the deref-store refusal: <<<{err}>>>"
    );
}
