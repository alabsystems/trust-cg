#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a bridge-compiled function reads a `bool` whose byte is
// not 0 or 1 as `byte != 0`, trust-ir's `Load Bool`, and hands a valid bool
// across the backend boundary, in the rlib x bin cells whose LLVM half never
// reads the byte as a `bool`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// trust-ir's reference interpreter decodes a stored `bool` byte `m` as
// `m != 0`, the bridge lowers `*(p as *const bool)` to trust-ir `Load Bool`,
// and no trust-ir rule makes `m` 0 or 1. In Rust such a read is undefined
// behaviour, so the byte never reaches an LLVM-compiled read: the caller (the
// bin, either backend) writes each byte 0, 1, 2, 0x80 and 0xFF through a
// `*mut u8`-typed buffer and passes its address to callee functions in the
// rlib, which the BRIDGE compiles. Only the two cells with a trust-cg rlib run
// (`XBACK_CELLS`); an LLVM rlib would read an invalid bool, which is
// undefined behaviour there, so those cells have no oracle.
//
// Each callee reads the bool and returns it (read as `b as u32` by the
// caller), widens it, branches on it, reads it as a `#[repr(C)]` field, passes
// it to a `fn(bool) -> u32` the caller supplies (an LLVM or trust-cg `b as
// u32`, or a `fn(u32) -> u32` identity behind the pointer, which returns the
// whole argument register), or `&`s two of them. A row exits 42 exactly when
// every byte (every pair, for `&`) yields the trust-ir value `m != 0`; the
// expected value is that closed form, not an LLVM cell.
//
// Executes natively on an x86-64 or AArch64 Linux or macOS host with that
// target's `rust-std`. The cargo harness cannot dlopen a stage1-linked bridge
// under the pinned pack compiler; `tests/tools/m145_xback.py --test
// tests/m147_bool_byte_xback.rs` drives the same callee and rows (extracted
// from this file, `XBACK_CELLS` included) with a `trustc` that can.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The cells this matrix runs: only those whose callee rlib the bridge
/// compiles (`m145_xback.py` reads this line).
const XBACK_CELLS: &str = "tcg-rlib";

fn target() -> Option<&'static str> {
    if cfg!(target_arch = "x86_64") {
        Some(host_target_support::X86_64_TARGET)
    } else if cfg!(target_arch = "aarch64") {
        Some(host_target_support::AARCH64_TARGET)
    } else {
        None
    }
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m147_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn compile(
    dir: &Path,
    dylib: &Path,
    trust_cg: bool,
    opt: &str,
    target: &str,
    configure: impl FnOnce(&mut Command),
) -> Result<(), String> {
    let _ = dir;
    let mut cmd = toolchain_support::rustc_command();
    if trust_cg {
        cmd.arg(backend_arg(dylib))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.args([
        "--target",
        target,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"));
    configure(&mut cmd);
    let output = cmd.output().expect("spawn rustc");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// The callee crate, compiled by the bridge. Every read of a `bool` from a
/// byte the caller wrote is here.
const CALLEE_SRC: &str = r#"
#[repr(C)] pub struct Flags { pub n: u32, pub on: bool, pub w: u16 }
#[inline(never)] pub fn load_at(p: *const u8) -> bool { unsafe { *(p as *const bool) } }
#[inline(never)] pub fn widen_at(p: *const u8) -> u32 { unsafe { *(p as *const bool) as u32 } }
#[inline(never)] pub fn branch_at(p: *const u8) -> u32 { if unsafe { *(p as *const bool) } { 7 } else { 3 } }
#[inline(never)] pub fn field_at(p: *const u8) -> u32 { unsafe { (*(p as *const Flags)).on as u32 } }
#[inline(never)] pub fn pass_at(sink: fn(bool) -> u32, p: *const u8) -> u32 { sink(unsafe { *(p as *const bool) }) }
#[inline(never)] pub fn and_at(p: *const u8, q: *const u8) -> bool { unsafe { *(p as *const bool) & *(q as *const bool) } }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    use callee::*;\n\
    const BYTES: [u8; 5] = [0, 1, 2, 0x80, 0xff];\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n\
    fn every(f: impl Fn(u8) -> u32, want: impl Fn(bool) -> u32) -> u64 { let mut i = 0; while i < BYTES.len() { let m = BYTES[i]; if f(black_box(m)) != want(m != 0) { return 7; } i += 1; } 42 }\n\
    fn at(m: u8, f: impl Fn(*const u8) -> u32) -> u32 { let mut b = [0xa5u8; 8]; b[0] = m; f(black_box(b.as_mut_ptr() as *const u8)) }\n\
    #[inline(never)] fn sink(b: bool) -> u32 { b as u32 }\n\
    #[inline(never)] fn raw_u32(x: u32) -> u32 { x }\n\
    fn raw() -> fn(bool) -> u32 { unsafe { std::mem::transmute::<fn(u32) -> u32, fn(bool) -> u32>(black_box(raw_u32 as fn(u32) -> u32)) } }\n";

/// `(shape, caller body, expected exit code)`. Every row exits 42 exactly when
/// each byte `m` yields `m != 0`.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        (
            "byte_ret",
            r#"fn main() { exit(every(|m| at(m, |p| black_box(load_at(p)) as u32), |t| t as u32)) }"#,
            42,
        ),
        (
            "byte_widen",
            r#"fn main() { exit(every(|m| at(m, |p| widen_at(p)), |t| t as u32)) }"#,
            42,
        ),
        (
            "byte_branch",
            r#"fn main() { exit(every(|m| at(m, |p| branch_at(p)), |t| if t { 7 } else { 3 })) }"#,
            42,
        ),
        (
            "byte_field",
            r#"fn main() { exit(every(|m| { let mut b = [0xa5u8; 8]; b[4] = m; field_at(black_box(b.as_mut_ptr() as *const u8)) }, |t| t as u32)) }"#,
            42,
        ),
        (
            "byte_pass_sink",
            r#"fn main() { exit(every(|m| at(m, |p| pass_at(black_box(sink), p)), |t| t as u32)) }"#,
            42,
        ),
        (
            "byte_pass_raw",
            r#"fn main() { exit(every(|m| at(m, |p| pass_at(raw(), p)), |t| t as u32)) }"#,
            42,
        ),
        (
            "byte_and",
            r#"fn main() { let mut i = 0; while i < BYTES.len() { let m = BYTES[i]; if every(|n| at(m, |p| at(n, |q| black_box(and_at(p, q)) as u32)), |t| (t && m != 0) as u32) != 42 { exit(7) } i += 1; } exit(42) }"#,
            42,
        ),
    ]
}

#[test]
fn bool_bytes_other_than_zero_and_one_are_read_as_nonzero_across_the_boundary() {
    assert_eq!(XBACK_CELLS, "tcg-rlib");
    let Some(target) = target() else {
        eprintln!("skipping: the lane runs natively on an x86-64 or AArch64 host");
        return;
    };
    if !host_target_support::HOST_OS_SUPPORTED {
        eprintln!("skipping: the lane runs natively on a Linux or macOS host");
        return;
    }
    if !toolchain_support::target_std_available(target) {
        eprintln!("skipping: rust-std for {target} not installed for the pinned toolchain");
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("bool_byte");
    let mut failures = Vec::new();
    for opt in ["0", "1", "2", "3"] {
        let src = dir.join("callee.rs");
        std::fs::write(&src, CALLEE_SRC).expect("write callee source");
        let out = dir.join(format!("callee_tcg_O{opt}"));
        std::fs::create_dir_all(&out).expect("create callee out dir");
        if let Err(e) = compile(&dir, &dylib, true, opt, target, |cmd| {
            cmd.args([
                "--crate-type",
                "rlib",
                "--crate-name",
                "callee",
                "--out-dir",
            ])
            .arg(&out)
            .arg(&src);
        }) {
            failures.push(format!(
                "O{opt}: trust-cg callee rlib failed closed: <<<{}>>>",
                e.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
            ));
            continue;
        }
        let rlib = out.join("libcallee.rlib");
        for (shape, body, expected) in shapes() {
            let src = dir.join(format!("caller_{shape}.rs"));
            std::fs::write(&src, format!("{CALLER_HDR}{body}")).expect("write caller source");
            for (bin_trust_cg, label) in [(false, "LLVM caller"), (true, "trust-cg caller")] {
                let bin = dir.join(format!("caller_{shape}_{bin_trust_cg}_O{opt}"));
                let mut extern_arg = OsString::from("callee=");
                extern_arg.push(&rlib);
                let built = compile(&dir, &dylib, bin_trust_cg, opt, target, |cmd| {
                    cmd.args(["--crate-type", "bin", "--extern"])
                        .arg(&extern_arg)
                        .arg("-L")
                        .arg(&out)
                        .arg("-o")
                        .arg(&bin)
                        .arg(&src);
                });
                match built {
                    Ok(()) => {
                        let status = Command::new(&bin).status().expect("run binary");
                        let exit = status.code().unwrap_or(-1);
                        if exit != expected {
                            failures.push(format!(
                                "O{opt} `{shape}` trust-cg callee + {label}: exit {exit}, \
                                 expected {expected}"
                            ));
                        }
                    }
                    Err(e) => failures.push(format!(
                        "O{opt} `{shape}` trust-cg callee + {label}: failed closed: <<<{}>>>",
                        e.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                    )),
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} bool-byte combination(s) disagreed or refused:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
