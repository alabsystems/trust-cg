#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/x86_rosetta.rs"]
mod x86_rosetta_support;

// Integration test: a `bool` the backend LOADS from memory and passes as a call
// argument arrives as the clean 32-bit bool an LLVM callee relies on, checked
// ACROSS the backend boundary in all four rlib x bin combinations at every
// optimization level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The x86-64 selector lowered a `B1` load to `mov r8, m` alone. That writes
// only the low byte of its destination, and register allocation treats the
// destination as a pure definition, so bits 8..31 were whatever the assigned
// register held, and the value then left the function at 32 bits: passed as
// an argument with a 32-bit copy, or returned with `mov eax, r32`. An LLVM
// callee of a `bool` argument relies on all 32 (`fn(b: bool) -> u32 { b as u32
// }` is `movl %edi, %eax` at O1 and above). The selector now defines every
// `B1` byte load (plain, volatile, atomic) as the byte read as `!= 0` in a
// clean 32-bit register (`movzx; add 255; shr 8`) and zero-extends a `bool`
// parameter read from the stack. Bytes other than 0 and 1 are
// `m147_bool_byte_xback`'s rows.
//
// Rows. Every function in the callee crate takes junk integer arguments ahead
// of the bool, so the argument registers hold `0x1234_5678_9abc_def0` on entry
// and a register the load reuses is dirty above its low byte. It loads the
// `bool` (`*p`, a struct field, a `bool` parameter passed on the stack after
// six integers) and passes it to a callee the caller supplies: `sink` (`b as
// u32`, the LLVM callee that relies on the extension; at O0 LLVM re-reads the
// byte, so it tells only at O1-O3), `raw` (a `fn(u32) -> u32` identity behind
// a `fn(bool) -> u32` pointer, which returns the whole argument register at
// every level), or a closure through `&dyn Fn`. Each row calls with `false`
// and `true` and exits 42 only when both come back exactly 0 and 1.
//
// The RETURN direction has no LLVM oracle here: an LLVM callee returns a `bool`
// in AL and its callers read AL (at O0, `fn(p: &bool) -> bool { *p }` itself
// leaves EAX bits 8..31 set: an EAX observer exits 7 in the LLVM x LLVM cell).
// The backend's clean 32-bit result is checked natively by trust-cg-codegen's
// `x86_64_bool_load_abi` and by the x86-64 body theorem.
//
// The bridge compiles with `no-proof-certs`, as `tests/tools/m145_xback.py`
// does: the rows judge ABI agreement, not proof promotion. The bridge
// refuses `read_volatile` (`unsupported intrinsic volatile_load`), so the
// volatile load is covered below the bridge only.
//
// Runs natively on an x86-64 Linux or macOS host with the host x86-64
// `rust-std`, and under Rosetta on an aarch64-apple-darwin host
// (`support/x86_rosetta.rs`: the same callee and rows as `#![no_std]` programs
// against a `core` built from the compiler's own library source). A run under
// Rosetta qualifies Rosetta's execution of the x86-64 code, not a native
// x86-64 machine. `tests/tools/m145_xback.py --test
// tests/m146_x86_bool_load_xback.rs` drives the same callee and rows
// (extracted from this file) with a given `trustc` and dylib.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use x86_rosetta_support::XbackLane;

const TARGET: &str = host_target_support::X86_64_TARGET;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m146_{stem}_{}", std::process::id()));
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
    lane: &XbackLane,
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join("callee.rs");
    std::fs::write(&src_path, lane.callee_source(CALLEE_SRC)).expect("write callee source");
    let out_dir = dir.join(format!("callee_{}_O{opt}", backend.tag()));
    std::fs::create_dir_all(&out_dir).expect("create callee out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", "callee"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.args(lane.compile_args(opt))
        .args([
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

fn compile_caller_bin(
    lane: &XbackLane,
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
    std::fs::write(
        &src_path,
        lane.caller_source(&format!("{CALLER_HDR}{body}")),
    )
    .expect("write caller source");
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
    cmd.args(lane.compile_args(opt))
        .args([
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

fn run_exit_code(lane: &XbackLane, bin: &Path, opt: &str) -> i32 {
    lane.run(bin, opt)
        .unwrap_or_else(|why| panic!("{} {bin:?}: {why}", lane.label()))
}

/// The callee crate. The leading `u64`s are junk: the caller passes
/// `0x1234_5678_9abc_def0` in each, so the argument registers are dirty above
/// their low byte when the `bool` is loaded.
const CALLEE_SRC: &str = r#"
pub struct Flags { pub n: u32, pub on: bool, pub w: u16 }
#[inline(never)] pub fn fwd(sink: fn(bool) -> u32, _b: u64, _c: u64, _d: u64, _e: u64, p: &bool) -> u32 { sink(*p) }
#[inline(never)] pub fn fwd_field(sink: fn(bool) -> u32, _b: u64, _c: u64, _d: u64, _e: u64, f: &Flags) -> u32 { sink(f.on) }
#[inline(never)] pub fn fwd_stack(sink: fn(bool) -> u32, _b: u64, _c: u64, _d: u64, _e: u64, _f: u64, x: bool) -> u32 { sink(x) }
#[inline(never)] pub fn fwd_dyn(sink: &dyn Fn(bool) -> u32, _c: u64, _d: u64, _e: u64, p: &bool) -> u32 { sink(*p) }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    use callee::*;\n\
    const J: u64 = 0x1234_5678_9abc_def0;\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n\
    fn both(f: impl Fn(bool) -> u32) -> u64 { if f(black_box(false)) == 0 && f(black_box(true)) == 1 { 42 } else { 7 } }\n\
    #[inline(never)] fn sink(b: bool) -> u32 { b as u32 }\n\
    #[inline(never)] fn raw_u32(x: u32) -> u32 { x }\n\
    fn raw() -> fn(bool) -> u32 { unsafe { std::mem::transmute::<fn(u32) -> u32, fn(bool) -> u32>(black_box(raw_u32 as fn(u32) -> u32)) } }\n\
    fn flags(on: bool) -> Flags { black_box(Flags { n: J as u32, on, w: J as u16 }) }\n";

/// `(shape, caller body, expected exit code)`. Every row exits 42 exactly when
/// the `false` and `true` calls return 0 and 1.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        (
            "load_sink",
            r#"fn main() { exit(both(|b| fwd(black_box(sink), J, J, J, J, &b))) }"#,
            42,
        ),
        (
            "load_raw",
            r#"fn main() { exit(both(|b| fwd(raw(), J, J, J, J, &b))) }"#,
            42,
        ),
        (
            "field_sink",
            r#"fn main() { exit(both(|b| fwd_field(black_box(sink), J, J, J, J, &flags(b)))) }"#,
            42,
        ),
        (
            "field_raw",
            r#"fn main() { exit(both(|b| fwd_field(raw(), J, J, J, J, &flags(b)))) }"#,
            42,
        ),
        (
            "stack_sink",
            r#"fn main() { exit(both(|b| fwd_stack(black_box(sink), J, J, J, J, J, b))) }"#,
            42,
        ),
        (
            "stack_raw",
            r#"fn main() { exit(both(|b| fwd_stack(raw(), J, J, J, J, J, b))) }"#,
            42,
        ),
        (
            "dyn_sink",
            r#"fn main() { let s = |b: bool| b as u32; exit(both(|b| fwd_dyn(black_box(&s), J, J, J, &b))) }"#,
            42,
        ),
    ]
}

#[test]
fn loaded_bools_cross_the_backend_boundary_as_clean_32_bit_bools() {
    let lane = match XbackLane::for_host(TARGET) {
        Ok(lane) => lane,
        Err(why) => {
            eprintln!("skipping: {why}");
            return;
        }
    };
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("bool");
    let mut failures = Vec::new();
    for opt in ["0", "1", "2", "3"] {
        let llvm_rlib = compile_callee_rlib(&lane, &dir, &dylib, Backend::Llvm, opt)
            .unwrap_or_else(|e| panic!("LLVM `callee` rlib failed at O{opt}: <<<{e}>>>"));
        let tcg_rlib = match compile_callee_rlib(&lane, &dir, &dylib, Backend::TrustCg, opt) {
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
                &lane,
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
            let oracle_exit = run_exit_code(&lane, &oracle, opt);
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
                    &lane,
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
                        let exit = run_exit_code(&lane, &bin, opt);
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
        "{}: {} loaded-bool combination(s) disagreed or refused:\n  {}",
        lane.label(),
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
