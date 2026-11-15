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

// Integration test: the TWO-REGISTER `PassMode::Pair` RETURN on x86-64, checked
// ACROSS the backend boundary — the one shape a whole-program differential
// cannot see, because both sides of such a test are built by the same backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc returns a `BackendRepr::ScalarPair` aggregate (`Option<u8>`,
// `(u32, u32)`, `(u64, f64)`, `&str`, ...) as its TWO scalars, each in the next
// return register of its class: RAX then RDX for integers, XMM0 then XMM1 for
// floats. Before the x86-64 pair lane, the bridge declared such a return as ONE
// lane-tuple value (`[u8; 2]` in RAX) and `[TCG-RET-ABI]` refused it — 282 of
// the 726 `core` roots measured on 2026-09-20 on this host. With the lane, the
// callee returns two values and the caller stores each at rustc's own lane
// offset; a `Zext` lane narrower than 32 bits (a `bool`-valued `Option` tag)
// travels as its zero-extended 32-bit carrier, which is what an LLVM caller
// compiled against `zeroext` reads.
//
// Each shape below is a callee rlib and a caller bin, compiled in all FOUR
// backend combinations at every optimization level:
//
//   LLVM rlib + LLVM bin      the oracle (must equal the expected constant)
//   trust-cg rlib + LLVM bin  the callee places, LLVM reads   (RET side)
//   LLVM rlib + trust-cg bin  LLVM places, the caller reads   (CALL side)
//   trust-cg rlib + trust-cg bin
//
// Every combination must exit with the oracle's code. A trust-cg fail-closed
// refusal is a test FAILURE here, not a skip: this file exists to hold the lane
// open, and a refusal would silently narrow it.
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
    let dir = std::env::temp_dir().join(format!("rcl2_pairret_{stem}_{}", std::process::id()));
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

/// The callee crate: one `#[inline(never)]` pair-returning function per shape.
/// Each returns BOTH variants/lanes from data the caller passes through
/// `black_box`, so neither the tag nor the payload can be constant-folded.
const CALLEE_SRC: &str = r#"
#![no_std]
use core::ops::ControlFlow;

#[inline(never)] pub fn opt_u8(n: u32) -> Option<u8> { if n % 2 == 0 { Some((n as u8).wrapping_mul(3).wrapping_add(1)) } else { None } }
#[inline(never)] pub fn opt_u16(n: u32) -> Option<u16> { if n % 2 == 0 { Some((n as u16).wrapping_mul(300).wrapping_add(7)) } else { None } }
#[inline(never)] pub fn opt_u32(n: u32) -> Option<u32> { if n % 2 == 0 { Some(n.wrapping_mul(70_001).wrapping_add(11)) } else { None } }
#[inline(never)] pub fn opt_i32(n: u32) -> Option<i32> { if n % 2 == 0 { Some(-(n as i32) * 13 - 5) } else { None } }
#[inline(never)] pub fn pair_u8(n: u32) -> (u8, u8) { ((n as u8).wrapping_add(200), (n as u8).wrapping_mul(7)) }
#[inline(never)] pub fn pair_u16(n: u32) -> (u16, u16) { ((n as u16).wrapping_add(60_000), (n as u16).wrapping_mul(1_000)) }
#[inline(never)] pub fn pair_u32(n: u32) -> (u32, u32) { (n.wrapping_mul(3), n.wrapping_add(0xFFFF_0000)) }
#[inline(never)] pub fn pair_u8_bool(n: u32) -> (u8, bool) { ((n as u8).wrapping_add(250), n % 3 == 0) }
#[inline(never)] pub fn pair_i8(n: u32) -> (i8, i8) { (-(n as i8), (n as i8).wrapping_sub(100)) }
#[inline(never)] pub fn pair_u64(n: u32) -> (u64, u64) { ((n as u64) << 40 | 5, (n as u64).wrapping_mul(0x1_0000_0001)) }
#[inline(never)] pub fn pair_f64(n: u32) -> (f64, f64) { (n as f64 * 1.5, n as f64 - 0.25) }
#[inline(never)] pub fn pair_u64_f64(n: u32) -> (u64, f64) { ((n as u64).wrapping_mul(1_000_003), n as f64 * 0.5) }
#[inline(never)] pub fn pair_f32_u64(n: u32) -> (f32, u64) { (n as f32 * 2.5, (n as u64) + 0x1_0000_0000) }
#[inline(never)] pub fn res_u8(n: u32) -> Result<u8, u8> { if n % 2 == 0 { Ok((n as u8).wrapping_add(9)) } else { Err((n as u8).wrapping_add(90)) } }
#[inline(never)] pub fn flow_u8(n: u32) -> ControlFlow<u8, u8> { if n % 2 == 0 { ControlFlow::Continue((n as u8).wrapping_add(1)) } else { ControlFlow::Break((n as u8).wrapping_add(2)) } }
"#;

/// The fat-pointer pair returns (`&[T]` / `&str`: `{data, len}`), in their own
/// crate so a refusal of the constant allocation they point at is reported
/// against these shapes alone rather than masking the scalar pairs.
const CALLEE_FAT_SRC: &str = r#"
#![no_std]
const A: [u32; 5] = [10, 20, 30, 40, 50];
#[inline(never)] pub fn slice_ref(n: u32) -> &'static [u32] { &A[..(n as usize % 5) + 1] }
#[inline(never)] pub fn str_ref(n: u32) -> &'static str { if n % 2 == 0 { "even!" } else { "odd" } }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n";

/// `(callee crate, shape, caller body, expected exit code)`. The expected code
/// is the oracle's (LLVM callee + LLVM caller) and is asserted so a corrupted
/// oracle cannot make every combination agree on a wrong value.
fn shapes() -> Vec<(&'static str, &'static str, &'static str, i32)> {
    vec![
        (
            "callee",
            "opt_u8",
            "fn main() { let a = callee::opt_u8(black_box(4)); let b = callee::opt_u8(black_box(5)); \
             exit(match a { Some(x) => x as u64 * 3 + 1, None => 7 } + match b { Some(x) => x as u64 * 5, None => 1000 }) }",
            ((13u64 * 3 + 1 + 1000) % 251) as i32,
        ),
        (
            "callee",
            "opt_u16",
            "fn main() { let a = callee::opt_u16(black_box(6)); let b = callee::opt_u16(black_box(7)); \
             exit(match a { Some(x) => x as u64, None => 7 } + match b { Some(x) => x as u64, None => 100_000 }) }",
            ((1807u64 + 100_000) % 251) as i32,
        ),
        (
            "callee",
            "opt_u32",
            "fn main() { let a = callee::opt_u32(black_box(8)); let b = callee::opt_u32(black_box(9)); \
             exit(match a { Some(x) => x as u64, None => 7 } + match b { Some(x) => x as u64, None => 3 }) }",
            ((8u64 * 70_001 + 11 + 3) % 251) as i32,
        ),
        (
            "callee",
            "opt_i32",
            "fn main() { let a = callee::opt_i32(black_box(10)); let b = callee::opt_i32(black_box(11)); \
             exit(match a { Some(x) => (-x) as u64, None => 7 } + match b { Some(x) => x as u64, None => 40 }) }",
            ((135u64 + 40) % 251) as i32,
        ),
        (
            "callee",
            "pair_u8",
            "fn main() { let (a, b) = callee::pair_u8(black_box(30)); exit(a as u64 * 256 + b as u64) }",
            ((230u64 * 256 + 210) % 251) as i32,
        ),
        (
            "callee",
            "pair_u16",
            "fn main() { let (a, b) = callee::pair_u16(black_box(30)); exit(a as u64 * 65_536 + b as u64) }",
            ((60_030u64 * 65_536 + 30_000) % 251) as i32,
        ),
        (
            "callee",
            "pair_u32",
            "fn main() { let (a, b) = callee::pair_u32(black_box(30)); exit(a as u64 * 4_294_967_296 + b as u64) }",
            ((90u64 * 4_294_967_296 + 0xFFFF_0000 + 30) % 251) as i32,
        ),
        (
            "callee",
            "pair_u8_bool",
            "fn main() { let (a, b) = callee::pair_u8_bool(black_box(30)); let (c, d) = callee::pair_u8_bool(black_box(31)); \
             exit(a as u64 + if b { 1000 } else { 1 } + c as u64 + if d { 10_000 } else { 3 }) }",
            ((24u64 + 1000 + 25 + 3) % 251) as i32,
        ),
        (
            "callee",
            "pair_i8",
            "fn main() { let (a, b) = callee::pair_i8(black_box(30)); exit((a as i64 + 1000) as u64 * 1000 + (b as i64 + 1000) as u64) }",
            ((970u64 * 1000 + 930) % 251) as i32,
        ),
        (
            "callee",
            "pair_u64",
            "fn main() { let (a, b) = callee::pair_u64(black_box(30)); exit(a.wrapping_add(b)) }",
            ((((30u64 << 40) | 5).wrapping_add(30u64.wrapping_mul(0x1_0000_0001))) % 251) as i32,
        ),
        (
            "callee",
            "pair_f64",
            "fn main() { let (a, b) = callee::pair_f64(black_box(30)); exit((a * 4.0) as u64 * 1000 + (b * 4.0) as u64) }",
            ((180u64 * 1000 + 119) % 251) as i32,
        ),
        (
            "callee",
            "pair_u64_f64",
            "fn main() { let (a, b) = callee::pair_u64_f64(black_box(30)); exit(a + (b * 4.0) as u64) }",
            ((30u64 * 1_000_003 + 60) % 251) as i32,
        ),
        (
            "callee",
            "pair_f32_u64",
            "fn main() { let (a, b) = callee::pair_f32_u64(black_box(30)); exit((a * 4.0) as u64 + b) }",
            ((300u64 + 30 + 0x1_0000_0000) % 251) as i32,
        ),
        (
            "callee",
            "res_u8",
            "fn main() { let a = callee::res_u8(black_box(30)); let b = callee::res_u8(black_box(31)); \
             exit(match a { Ok(x) => x as u64, Err(e) => e as u64 * 1000 } + match b { Ok(x) => x as u64 * 1000, Err(e) => e as u64 }) }",
            ((39u64 + 121) % 251) as i32,
        ),
        (
            "callee",
            "flow_u8",
            "fn main() { use std::ops::ControlFlow; let a = callee::flow_u8(black_box(30)); let b = callee::flow_u8(black_box(31)); \
             exit(match a { ControlFlow::Continue(x) => x as u64, ControlFlow::Break(x) => x as u64 * 1000 } \
                + match b { ControlFlow::Continue(x) => x as u64 * 1000, ControlFlow::Break(x) => x as u64 }) }",
            ((31u64 + 33) % 251) as i32,
        ),
        (
            "calleefat",
            "slice_ref",
            "fn main() { let s = calleefat::slice_ref(black_box(2)); exit(s.len() as u64 * 1000 + s.iter().map(|&x| x as u64).sum::<u64>()) }",
            ((3u64 * 1000 + 60) % 251) as i32,
        ),
        (
            "calleefat",
            "str_ref",
            "fn main() { let a = calleefat::str_ref(black_box(2)); let b = calleefat::str_ref(black_box(3)); \
             exit(a.len() as u64 * 100 + b.len() as u64 + a.as_bytes()[4] as u64) }",
            ((5u64 * 100 + 3 + b'!' as u64) % 251) as i32,
        ),
    ]
}

#[test]
fn scalar_pair_returns_agree_across_backends_at_every_opt_level_x86_64() {
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
    let crates = [("callee", CALLEE_SRC), ("calleefat", CALLEE_FAT_SRC)];
    for opt in ["0", "1", "2", "3"] {
        for (krate, src) in crates {
            let llvm_rlib =
                compile_callee_rlib(&lane, &dir, &dylib, Backend::Llvm, opt, krate, src)
                    .unwrap_or_else(|e| panic!("LLVM `{krate}` rlib failed at O{opt}: <<<{e}>>>"));
            let tcg_rlib =
                match compile_callee_rlib(&lane, &dir, &dylib, Backend::TrustCg, opt, krate, src) {
                    Ok(rlib) => rlib,
                    Err(e) => {
                        failures.push(format!(
                            "O{opt} `{krate}`: trust-cg callee rlib failed closed: <<<{}>>>",
                            e.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
                        ));
                        continue;
                    }
                };
            for (shape_crate, shape, body, expected) in shapes() {
                if shape_crate != krate {
                    continue;
                }
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
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{}: {} scalar-pair return combination(s) disagreed or refused:\n  {}",
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
