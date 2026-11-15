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

// Integration test: the TWO-REGISTER `PassMode::Pair` ARGUMENT on x86-64,
// checked ACROSS the backend boundary — the one shape a whole-program
// differential cannot see, because both sides of such a test are built by the
// same backend. The argument twin of `m140_x86_scalar_pair_return_xback.rs`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc passes a `BackendRepr::ScalarPair` aggregate (`Option<u8>`,
// `Range<u8>`, `(i16, i16)`, `Result<u8, u8>`, a `{u32, u16}` struct, ...) as
// its TWO scalars, each in the next argument register of its class. Before the
// argument lane the bridge declared such a parameter as ONE lane-tuple value
// and `[TCG-ARG-ABI]` refused it — 74 of the 226 `core` roots measured on
// 2026-09-22 on this host. With the lane (`scalar_pair_param_plan`, the port of
// the AArch64-measured 62befd1db) the callee's declaration, its entry block and
// every call site take two values; a `Zext` lane narrower than 32 bits travels
// as its zero-extended 32-bit carrier, and the callee masks a `bool`-valued
// lane to bit 0 before storing it, for the LLVM `i1` convention measured on the
// return side.
//
// Each shape below is a callee rlib and a caller bin, compiled in all FOUR
// backend combinations at every optimization level:
//
//   LLVM rlib + LLVM bin      the oracle (must equal the expected constant)
//   trust-cg rlib + LLVM bin  the callee reads, LLVM places   (ENTRY side)
//   LLVM rlib + trust-cg bin  LLVM reads, the caller places   (CALL side)
//   trust-cg rlib + trust-cg bin
//
// Every combination must exit with the oracle's code. A trust-cg fail-closed
// refusal is a test FAILURE here, not a skip: this file exists to hold the lane
// open, and a refusal would silently narrow it.
//
// The shapes cover the census's own sub-families: the 1@0/1@1 `zeroext`-tag
// pair (`Option<u8>`, `Range<u8>`, `Result<u8, u8>`, `ControlFlow<u8, u8>`,
// both variants exercised so a dirty upper byte is a wrong exit code), the
// tagged 4@0/4@4 enum (`Option<u32>`), the 2@0/2@2 tuple (`(i16, i16)`, the
// `flt2dec` shape), a MIXED-width 4@0/2@4 struct (`fmt::PostPadding`), register
// NUMBERING after three scalar arguments and with two pairs in one list, an
// EXHAUSTION shape whose second lane must go to the stack, and a pair passed
// through a trait-object method (the virtual lane's hand-built signature).
//
// Runs natively on an x86-64 Linux or macOS host with the host x86-64
// `rust-std`, and under Rosetta on an aarch64-apple-darwin host
// (`support/x86_rosetta.rs`: the same callee and shapes as `#![no_std]`
// programs against a `core` built from the compiler's own library source). A
// run under Rosetta qualifies Rosetta's execution of the x86-64 code, not a
// native x86-64 machine. The same register placement is what the bridge's
// signature check re-checks against rustc's `FnAbi` at every declaration, so a
// wrong placement would be refused at compile time and a wrong VALUE would
// show up here as a mismatched exit code.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use x86_rosetta_support::XbackLane;

const TARGET: &str = host_target_support::X86_64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

/// The bridge's knob argument on this lane. The Rosetta lane compiles with
/// the proof certificates off (`no-proof-certs`), as the family matrix and
/// `m146` do: with them on, every trust-cg x86-64 rlib of this file is refused
/// `[TCG-PROOF-465]` on an Apple-silicon host (proof promotion finds the emitted
/// x86-64 opcode inventory uncovered; measured 2026-09-30), which says nothing
/// about argument placement. A native x86-64 host keeps them on, as the lane
/// was measured there.
fn backend_knobs(lane: &XbackLane) -> Option<String> {
    matches!(lane, XbackLane::Rosetta)
        .then(|| toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m141_{stem}_{}", std::process::id()));
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

/// One callee rlib named `krate` compiled by `backend` at `opt`. The shapes of
/// a crate share one compile, so one refusal names every shape in it.
fn compile_callee_rlib(
    lane: &XbackLane,
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    krate: &str,
    src: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{krate}.rs"));
    std::fs::write(&src_path, lane.callee_source(src)).expect("write callee source");
    let out_dir = dir.join(format!("{krate}_{}_O{opt}", backend.tag()));
    std::fs::create_dir_all(&out_dir).expect("create callee out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", krate]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.args(backend_knobs(lane));
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
    let rlib = out_dir.join(format!("lib{krate}.rlib"));
    if !rlib.is_file() {
        return Err(format!("no rlib produced at {rlib:?}"));
    }
    Ok(rlib)
}

/// One caller bin for `shape`, compiled by `backend` at `opt` against `rlib`.
fn compile_caller_bin(
    lane: &XbackLane,
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    shape: &str,
    body: &str,
    rlib: &Path,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("caller_{shape}.rs"));
    std::fs::write(
        &src_path,
        lane.caller_source(&format!("{CALLER_HDR}{body}")),
    )
    .expect("write caller source");
    let bin = dir.join(format!(
        "caller_{shape}_{}rlib_{}bin_O{opt}",
        rlib_backend_tag(rlib),
        backend.tag()
    ));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.args(backend_knobs(lane));
    }
    let krate = rlib
        .file_stem()
        .and_then(|s| s.to_str())
        .and_then(|s| s.strip_prefix("lib"))
        .expect("rlib file name");
    let mut extern_arg = OsString::from(format!("{krate}="));
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

fn rlib_backend_tag(rlib: &Path) -> &'static str {
    let dir = rlib
        .parent()
        .and_then(|d| d.file_name())
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    if dir.contains("_tcg_") { "tcg" } else { "llvm" }
}

fn run_exit_code(lane: &XbackLane, bin: &Path, opt: &str) -> i32 {
    lane.run(bin, opt)
        .unwrap_or_else(|why| panic!("{} {bin:?}: {why}", lane.label()))
}

/// The callee crate: one `#[inline(never)]` function per shape taking the pair
/// BY VALUE and folding its lanes asymmetrically into a scalar, so a swapped,
/// truncated or dirty lane is a different exit code. The caller passes every
/// input through `black_box`, so nothing constant-folds across the boundary.
const CALLEE_SRC: &str = r#"
#![no_std]
use core::ops::{ControlFlow, Range};

pub struct M { pub a: u32, pub b: u16 }

pub trait Take { fn take(&self, o: Option<u32>) -> u32; }
pub struct T1(pub u32);
impl Take for T1 {
    fn take(&self, o: Option<u32>) -> u32 { match o { Some(v) => v.wrapping_add(self.0), None => self.0.wrapping_mul(2) } }
}

#[inline(never)] pub fn opt_u8(o: Option<u8>) -> u32 { match o { Some(v) => v as u32 * 3 + 1, None => 7 } }
#[inline(never)] pub fn opt_u16(o: Option<u16>) -> u32 { match o { Some(v) => v as u32 * 5 + 2, None => 9 } }
#[inline(never)] pub fn opt_u32(o: Option<u32>) -> u32 { match o { Some(v) => v.wrapping_mul(7).wrapping_add(3), None => 11 } }
#[inline(never)] pub fn pair_i16(q: (i16, i16)) -> i32 { q.0 as i32 * 2 + q.1 as i32 }
#[inline(never)] pub fn mixed(m: M) -> u32 { m.a.wrapping_mul(2).wrapping_add(m.b as u32) }
#[inline(never)] pub fn res_u8(r: Result<u8, u8>) -> u32 { match r { Ok(v) => v as u32, Err(e) => e as u32 * 1000 } }
#[inline(never)] pub fn flow_u8(c: ControlFlow<u8, u8>) -> u32 { match c { ControlFlow::Continue(v) => v as u32, ControlFlow::Break(v) => v as u32 * 1000 } }
#[inline(never)] pub fn rng_u8(r: Range<u8>) -> u32 { (r.end - r.start) as u32 }
#[inline(never)] pub fn after3(a: u64, b: u64, c: u64, q: (i16, i16)) -> i64 { (a + b + c) as i64 + q.0 as i64 * 100 + q.1 as i64 }
#[inline(never)] pub fn two_pairs(a: Option<u32>, b: (i16, i16), c: u64) -> u64 {
    let x = match a { Some(v) => v as u64, None => 1000 };
    x * 3 + (b.0 as i64 * 10 + b.1 as i64) as u64 + c
}
#[inline(never)] pub fn spill(a: u64, b: u64, c: u64, d: u64, e: u64, p: Option<u32>) -> u64 {
    a + 2 * b + 3 * c + 4 * d + 5 * e + match p { Some(v) => v as u64 * 1000, None => 77 }
}
#[inline(never)] pub fn via_dyn(t: &dyn Take, o: Option<u32>) -> u32 { t.take(o) }
use core::ptr::NonNull;
#[inline(never)] pub fn nn_mk(s: &[u8]) -> NonNull<[u8]> { NonNull::from(s) }
#[inline(never)] pub fn nn_mk_mut(s: &mut [u8]) -> NonNull<[u8]> { NonNull::from(s) }
#[inline(never)] pub fn nn_ident(p: NonNull<[u8]>) -> NonNull<[u8]> { p }
#[inline(never)] pub fn nn_len(p: NonNull<[u8]>) -> usize { p.len() }
#[inline(never)] pub fn nn_first(p: NonNull<[u8]>) -> u8 { unsafe { *p.cast::<u8>().as_ptr() } }
#[inline(never)] pub fn nn_mk_str(s: &str) -> NonNull<str> { NonNull::from(s) }
#[inline(never)] pub fn nn_str_len(p: NonNull<str>) -> usize { unsafe { (&*p.as_ptr()).len() } }
#[inline(never)] pub fn nn_after3(a: u64, b: u64, c: u64, p: NonNull<[u8]>) -> u64 { a + b + c + p.len() as u64 }
#[inline(never)] pub fn nn_two(p: NonNull<[u8]>, q: NonNull<[u8]>) -> u64 { p.len() as u64 * 10 + q.len() as u64 }
#[inline(never)] pub fn nn_spill(a: u64, b: u64, c: u64, d: u64, e: u64, p: NonNull<[u8]>) -> u64 { a + b + c + d + e + p.len() as u64 * 100 }
#[inline(never)] pub fn slice_spill(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8]) -> u64 { a + b + c + d + e + s.len() as u64 * 100 }
#[inline(never)] pub fn nn_after6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, p: NonNull<[u8]>) -> u64 { a + b + c + d + e + f + p.len() as u64 * 100 }
#[inline(never)] pub fn nn_bump(p: NonNull<[u8]>) { unsafe { (&mut *p.as_ptr())[0] += 1 } }
pub trait TakeNn { fn take(&self, p: NonNull<[u8]>) -> u64; }
pub struct N1(pub u64);
impl TakeNn for N1 { fn take(&self, p: NonNull<[u8]>) -> u64 { self.0 + p.len() as u64 } }
#[inline(never)] pub fn nn_via_dyn(t: &dyn TakeNn, p: NonNull<[u8]>) -> u64 { t.take(p) }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n";

/// `(shape, caller body, expected exit code)`. The expected code is the
/// oracle's (LLVM callee + LLVM caller) and is asserted so a corrupted oracle
/// cannot make every combination agree on a wrong value.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        (
            "opt_u8",
            "fn main() { exit(callee::opt_u8(black_box(Some(3))) as u64 + callee::opt_u8(black_box(None)) as u64) }",
            ((3u64 * 3 + 1 + 7) % 251) as i32,
        ),
        (
            "opt_u16",
            "fn main() { exit(callee::opt_u16(black_box(Some(300))) as u64 + callee::opt_u16(black_box(None)) as u64) }",
            ((300u64 * 5 + 2 + 9) % 251) as i32,
        ),
        (
            "opt_u32",
            "fn main() { exit(callee::opt_u32(black_box(Some(70_001))) as u64 + callee::opt_u32(black_box(None)) as u64) }",
            ((70_001u64 * 7 + 3 + 11) % 251) as i32,
        ),
        (
            "pair_i16",
            "fn main() { exit((callee::pair_i16(black_box((-7, 300))) + callee::pair_i16(black_box((5, -3)))) as u64) }",
            (((-14i64 + 300) + (10 - 3)) as u64 % 251) as i32,
        ),
        (
            "mixed",
            "fn main() { exit(callee::mixed(callee::M { a: black_box(5), b: black_box(6) }) as u64 \
             + callee::mixed(callee::M { a: black_box(100_000), b: black_box(65_535) }) as u64) }",
            ((5u64 * 2 + 6 + 100_000 * 2 + 65_535) % 251) as i32,
        ),
        (
            "res_u8",
            "fn main() { exit(callee::res_u8(black_box(Ok(30))) as u64 + callee::res_u8(black_box(Err(31))) as u64) }",
            ((30u64 + 31_000) % 251) as i32,
        ),
        (
            "flow_u8",
            "fn main() { use std::ops::ControlFlow; exit(callee::flow_u8(black_box(ControlFlow::Continue(31))) as u64 \
             + callee::flow_u8(black_box(ControlFlow::Break(33))) as u64) }",
            ((31u64 + 33_000) % 251) as i32,
        ),
        (
            "rng_u8",
            "fn main() { exit(callee::rng_u8(black_box(3..10)) as u64 + callee::rng_u8(black_box(250..255)) as u64) }",
            ((7u64 + 5) % 251) as i32,
        ),
        (
            "after3",
            "fn main() { exit(callee::after3(black_box(10), black_box(20), black_box(30), black_box((7, 9))) as u64) }",
            ((60u64 + 700 + 9) % 251) as i32,
        ),
        (
            "two_pairs",
            "fn main() { exit(callee::two_pairs(black_box(Some(4)), black_box((2, 3)), black_box(100)) \
             + callee::two_pairs(black_box(None), black_box((1, 5)), black_box(7))) }",
            (((4u64 * 3 + 23 + 100) + (3000 + 15 + 7)) % 251) as i32,
        ),
        (
            "spill",
            "fn main() { exit(callee::spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(Some(6))) \
             + callee::spill(black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), black_box(None))) }",
            (((1u64 + 4 + 9 + 16 + 25 + 6000) + (15 + 77)) % 251) as i32,
        ),
        (
            "nn_roundtrip",
            "fn main() { let p = callee::nn_mk(black_box(&b\"hello\"[..])); let q = callee::nn_ident(p); \
             exit(callee::nn_len(q) as u64 * 10 + callee::nn_first(q) as u64) }",
            ((5u64 * 10 + 104) % 251) as i32,
        ),
        (
            "nn_str",
            "fn main() { exit(callee::nn_str_len(callee::nn_mk_str(black_box(\"abcd\"))) as u64 * 7) }",
            28,
        ),
        (
            "nn_after3",
            "fn main() { exit(callee::nn_after3(black_box(1), black_box(2), black_box(3), callee::nn_mk(black_box(&b\"xyz\"[..])))) }",
            9,
        ),
        (
            "nn_two",
            "fn main() { exit(callee::nn_two(callee::nn_mk(black_box(&[0u8; 3][..])), callee::nn_mk(black_box(&[0u8; 4][..])))) }",
            34,
        ),
        (
            "nn_after6",
            "fn main() { exit(callee::nn_after6(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), callee::nn_mk(black_box(&b\"ab\"[..])))) }",
            221,
        ),
        (
            "nn_ident_twice",
            "fn main() { let p = callee::nn_ident(callee::nn_ident(callee::nn_mk(black_box(&b\"0123456789\"[..])))); \
             exit(callee::nn_len(p) as u64 + callee::nn_first(p) as u64) }",
            ((10u64 + 48) % 251) as i32,
        ),
        (
            "in_bin_only",
            "fn main() { let p = callee::nn_mk(black_box(&[9u8; 6][..])); exit(unsafe { (&*p.as_ptr()).len() } as u64) }",
            6,
        ),
        (
            "nn_via_dyn",
            "fn main() { let t = callee::N1(black_box(40)); exit(callee::nn_via_dyn(&t, callee::nn_mk(black_box(&[0u8; 2][..])))) }",
            42,
        ),
        (
            "nn_bump_write",
            "fn main() { let mut b = [7u8, 0]; let p = callee::nn_mk_mut(black_box(&mut b[..])); callee::nn_bump(p); \
             exit(b[0] as u64 * 10 + b[1] as u64) }",
            80,
        ),
        (
            "via_dyn",
            "fn main() { let t = callee::T1(black_box(10)); let u = callee::T1(black_box(3)); \
             exit(callee::via_dyn(&t, black_box(Some(5))) as u64 + callee::via_dyn(&u, black_box(None)) as u64) }",
            ((15u64 + 6) % 251) as i32,
        ),
    ]
}

#[test]
fn scalar_pair_arguments_agree_across_backends_at_every_opt_level_x86_64() {
    let lane = match XbackLane::for_host(TARGET) {
        Ok(lane) => lane,
        Err(why) => {
            eprintln!("skipping: {why}");
            return;
        }
    };
    let dylib = ensure_dylib_built();
    let dir = workdir("xback");
    let mut failures = Vec::new();
    let krate = "callee";
    for opt in ["0", "1", "2", "3"] {
        let llvm_rlib =
            compile_callee_rlib(&lane, &dir, &dylib, Backend::Llvm, opt, krate, CALLEE_SRC)
                .unwrap_or_else(|e| panic!("LLVM `{krate}` rlib failed at O{opt}: <<<{e}>>>"));
        let tcg_rlib = match compile_callee_rlib(
            &lane,
            &dir,
            &dylib,
            Backend::TrustCg,
            opt,
            krate,
            CALLEE_SRC,
        ) {
            Ok(rlib) => rlib,
            Err(e) => {
                failures.push(format!(
                    "O{opt} `{krate}`: trust-cg callee rlib failed closed: <<<{}>>>",
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
            )
            .unwrap_or_else(|e| panic!("LLVM caller `{shape}` failed at O{opt}: <<<{e}>>>"));
            let oracle_exit = run_exit_code(&lane, &oracle, opt);
            assert_eq!(
                oracle_exit, expected,
                "oracle (LLVM+LLVM) exit for `{shape}` at O{opt} is {oracle_exit}, expected {expected}"
            );
            let combos = [
                (
                    Backend::TrustCg,
                    &llvm_rlib,
                    "LLVM callee + trust-cg caller",
                ),
                (Backend::Llvm, &tcg_rlib, "trust-cg callee + LLVM caller"),
                (
                    Backend::TrustCg,
                    &tcg_rlib,
                    "trust-cg callee + trust-cg caller",
                ),
            ];
            for (backend, rlib, label) in combos {
                match compile_caller_bin(&lane, &dir, &dylib, backend, opt, shape, body, rlib) {
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
        "{}: {} scalar-pair argument combination(s) disagreed or refused:\n  {}",
        lane.label(),
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        if matches!(lane, XbackLane::Rosetta) {
            positive_evidence::Certs::Off
        } else {
            positive_evidence::Certs::On
        },
    );
}
