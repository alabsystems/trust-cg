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

// A `match` on a signed integer with negative arms compiles and takes LLVM's
// arm at every width.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// MIR stores a `SwitchInt` case as the scrutinee's bits zero-extended to
// `u128`; trust-ir's typed switch-case admission (52771502e) takes the case in
// the scrutinee type's range. The bridge passed the raw bits, so every negative
// arm of an `i8`/`i16`/`i32`/`i64`/`isize` match was refused ("const type
// mismatch: expected i8, got int"): measured on trust-cg main 86424f20d
// (2026-10-09, -Cpanic=abort -Ccodegen-units=1), `signed` was refused
// `[TCG-IR-LOWER]` at every level. b53f9641f's `switch_case_literal`
// sign-extends a signed case from its width; its unit test checks the literal,
// and this test checks that the switch codegen then emits takes LLVM's arm.
//
// `unsigned` is the control: cases at and above each type's sign bit must keep
// their bits (it matched LLVM before the fix and must still). Every cell must
// match LLVM's exit code; a refusal fails the test.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::path::Path;
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

struct Case {
    name: &'static str,
    src: &'static str,
    oracle: i32,
}

const CASES: &[Case] = &[
    Case {
        name: "signed",
        src: r#"use std::hint::black_box as bb;
#[inline(never)] fn m8(x: i8) -> u64 { match x { -128 => 1, -1 => 2, 0 => 3, 127 => 4, -100 => 5, _ => 6 } }
#[inline(never)] fn m16(x: i16) -> u64 { match x { i16::MIN => 1, -1 => 2, 300 => 3, -300 => 4, _ => 5 } }
#[inline(never)] fn m32(x: i32) -> u64 { match x { i32::MIN => 1, -1 => 2, -70000 => 3, 7 => 4, _ => 5 } }
#[inline(never)] fn m64(x: i64) -> u64 { match x { i64::MIN => 1, -1 => 2, -5_000_000_000 => 3, 9 => 4, _ => 5 } }
#[inline(never)] fn mis(x: isize) -> u64 { match x { isize::MIN => 1, -1 => 2, -3 => 3, 4 => 4, _ => 5 } }
fn main() {
    let mut h: u64 = 1469598103934665603;
    let mut f = |r: u64| h = (h ^ r).wrapping_mul(1099511628211);
    for v in [-128i8, -127, -100, -1, 0, 1, 127, 126] { f(m8(bb(v))); }
    for v in [i16::MIN, -32767, -300, -1, 0, 300, i16::MAX] { f(m16(bb(v))); }
    for v in [i32::MIN, -70000, -1, 0, 7, i32::MAX] { f(m32(bb(v))); }
    for v in [i64::MIN, -5_000_000_000, -1, 0, 9, i64::MAX] { f(m64(bb(v))); }
    for v in [isize::MIN, -3, -1, 0, 4, isize::MAX] { f(mis(bb(v))); }
    std::process::exit((h % 239) as i32);
}
"#,
        oracle: 219,
    },
    Case {
        name: "unsigned",
        src: r#"use std::hint::black_box as bb;
#[inline(never)] fn mu8(x: u8) -> u64 { match x { 255 => 1, 128 => 2, 0 => 3, 9 => 4, _ => 5 } }
#[inline(never)] fn mu16(x: u16) -> u64 { match x { 65535 => 1, 32768 => 2, 0 => 3, _ => 4 } }
#[inline(never)] fn mu32(x: u32) -> u64 { match x { u32::MAX => 1, 2147483648 => 2, 0 => 3, 70000 => 4, _ => 5 } }
#[inline(never)] fn mu64(x: u64) -> u64 { match x { u64::MAX => 1, 9223372036854775808 => 2, 0 => 3, 5 => 4, _ => 5 } }
#[inline(never)] fn mus(x: usize) -> u64 { match x { usize::MAX => 1, 9223372036854775808 => 2, 3 => 3, _ => 4 } }
fn main() {
    let mut h: u64 = 1469598103934665603;
    let mut f = |r: u64| h = (h ^ r).wrapping_mul(1099511628211);
    for v in [255u8, 254, 128, 127, 0, 9] { f(mu8(bb(v))); }
    for v in [65535u16, 32768, 32767, 0, 1] { f(mu16(bb(v))); }
    for v in [u32::MAX, 2147483648, 2147483647, 0, 70000] { f(mu32(bb(v))); }
    for v in [u64::MAX, 1u64 << 63, (1u64 << 63) - 1, 0, 5] { f(mu64(bb(v))); }
    for v in [usize::MAX, 1usize << 63, 3, 0] { f(mus(bb(v))); }
    std::process::exit((h % 251) as i32);
}
"#,
        oracle: 234,
    },
];

enum Outcome {
    Exit(i32),
    Refused(String),
}

fn compile_and_run(dir: &Path, case: &Case, backend: Option<&Path>, opt: u32) -> Outcome {
    let label = if backend.is_some() { "tcg" } else { "llvm" };
    let out = dir.join(format!("{}-{label}-O{opt}", case.name));
    std::fs::create_dir_all(&out).expect("cell dir");
    let src = out.join("main.rs");
    std::fs::write(&src, case.src).expect("write source");
    let exe = out.join("prog");
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .args(["--target", TARGET, "-Cpanic=abort", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&exe)
        .arg(&src);
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        command
            .arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let built = command.output().expect("spawn compiler");
    if !built.status.success() {
        let stderr = String::from_utf8_lossy(&built.stderr);
        let code = stderr
            .split('[')
            .skip(1)
            .find_map(|rest| {
                let tag = rest.split(']').next()?;
                tag.starts_with("TCG-").then(|| tag.to_owned())
            })
            .unwrap_or_default();
        return Outcome::Refused(code);
    }
    let run = Command::new(&exe).output().expect("run program");
    Outcome::Exit(run.status.code().unwrap_or(-1))
}

#[test]
fn signed_switch_cases_take_llvms_arm() {
    darwin_native::require("switch_case_signed_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("rcl2_switch_case_a64_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let (mut cells, mut matched) = (0, 0);
    let mut wrong = Vec::new();
    for case in CASES {
        for opt in 0..=3 {
            match compile_and_run(&dir, case, None, opt) {
                Outcome::Exit(code) => assert_eq!(
                    code, case.oracle,
                    "{} O{opt}: the LLVM oracle is not the case's answer",
                    case.name
                ),
                Outcome::Refused(_) => panic!("{} O{opt}: LLVM failed to compile", case.name),
            }
            cells += 1;
            match compile_and_run(&dir, case, Some(&backend), opt) {
                Outcome::Exit(code) if code == case.oracle => matched += 1,
                Outcome::Exit(code) => wrong.push(format!(
                    "{} O{opt}: exit {code}, LLVM {}",
                    case.name, case.oracle
                )),
                Outcome::Refused(tag) => wrong.push(format!(
                    "{} O{opt}: refused [{tag}] where it must match LLVM",
                    case.name
                )),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        wrong.is_empty(),
        "signed switch cases disagree with LLVM:\n{}",
        wrong.join("\n")
    );
    eprintln!(
        "SWITCH_CASE_SIGNED cases={} cells={cells} matched={matched} opts=0,1,2,3",
        CASES.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
