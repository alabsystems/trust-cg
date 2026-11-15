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

// The bridge's slice-sort interception orders unsigned 64-bit elements and
// unstable key sorts the way std does.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Two wrong values, measured on trust-cg main c279e5d5a (2026-10-08, Trust pack
// 9192, -Cpanic=abort -Ccodegen-units=1, against LLVM):
//
// * `__trustcg_vec_sort_*` compared zero-extended elements with a SIGNED `Sgt`.
//   For a 64-bit unsigned element zero-extension is the identity, so `u64` /
//   `usize` values at or above 2^63 sorted before every smaller one (`u64s`:
//   exit 231 against LLVM's 76 at O0 and O1).
// * `sort_unstable_by_key` was routed to the STABLE insertion sort used for
//   `sort_by_key`. std's unstable sort may leave equal keys in another order,
//   so the results differed (`unstable_key_u32`: 136 against 191 at O0/O1;
//   `unstable_key_u64`: 182 against 120 at every level).
//
// Each program depends on exactly one of the two fixes, so the base build is
// the mutant for each. A cell must match LLVM's exit code or be refused by a
// named diagnostic, never print a different value; the levels in `must_match`
// must match.
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
    must_match: &'static [u32],
}

const CASES: &[Case] = &[
    Case {
        name: "u64s",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let mut v: Vec<u64> = vec![bb(u64::MAX), 1, 2, 1 << 63, 7, (1 << 63) + 5, 0];
    v.sort_unstable();
    let mut w: Vec<u64> = vec![bb(1u64 << 63), 5, u64::MAX - 1, 3];
    w.sort();
    let mut u: Vec<usize> = vec![bb(usize::MAX), 9, 0, 1 << 63];
    u.sort();
    let mut h: u64 = 1469598103934665603;
    for x in v.iter().chain(w.iter()) { h = (h ^ *x).wrapping_mul(1099511628211); }
    for x in u.iter() { h = (h ^ *x as u64).wrapping_mul(1099511628211); }
    std::process::exit((h % 251) as i32);
}
"#,
        oracle: 76,
        must_match: &[0, 1],
    },
    Case {
        name: "unstable_key_u32",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let mut v: Vec<u32> = vec![bb(323),412,16,405,35,264,267,273,284,102,60,72,454,20,142,64,11,260,418,383,222];
    v.sort_unstable_by_key(|x| x % 10);
    let code = v[0] as u64 * 1_000_000 + v[1] as u64 * 1000 + v[2] as u64;
    std::process::exit((code % 251) as i32);
}
"#,
        oracle: 191,
        must_match: &[0, 1],
    },
    Case {
        name: "unstable_key_u64",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let mut v: Vec<u64> = (0..40u64).map(|i| bb(i * 37 % 101)).collect();
    v.sort_unstable_by_key(|x| x % 7);
    let mut h: u64 = 1469598103934665603;
    for x in v.iter() { h = (h ^ *x).wrapping_mul(1099511628211); }
    std::process::exit((h % 251) as i32);
}
"#,
        oracle: 120,
        must_match: &[0, 1, 2, 3],
    },
    // The interception that stays: signed and narrow unsigned plain sorts, and
    // the stable key sorts.
    Case {
        name: "kept_sorts",
        src: r#"use std::hint::black_box as bb;
fn h(xs: &[i64]) -> u64 { let mut h: u64 = 1469598103934665603; for x in xs { h = (h ^ *x as u64).wrapping_mul(1099511628211); } h }
fn main() {
    let mut a: Vec<i64> = vec![bb(-5), 3, i64::MIN, i64::MAX, 0, -1, 3];
    a.sort();
    let mut b: Vec<i64> = vec![bb(9), -9, 4, -4, 0, 4];
    b.sort_unstable();
    let mut c: Vec<u8> = vec![bb(255u8), 0, 128, 127, 1];
    c.sort();
    let mut d: Vec<i32> = vec![bb(-3i32), 30, 13, -23, 3, 33];
    d.sort_by_key(|x| x.abs() % 10);
    let mut e: Vec<u32> = vec![bb(41u32), 12, 31, 22, 1];
    e.sort_by_cached_key(|x| x % 10);
    let mut f: Vec<u16> = vec![bb(65535u16), 0, 32768, 32767];
    f.sort_unstable();
    let mut t = h(&a) ^ h(&b).rotate_left(7);
    for x in c.iter() { t = (t ^ *x as u64).wrapping_mul(1099511628211); }
    for x in d.iter() { t = (t ^ *x as u64).wrapping_mul(1099511628211); }
    for x in e.iter() { t = (t ^ *x as u64).wrapping_mul(1099511628211); }
    for x in f.iter() { t = (t ^ *x as u64).wrapping_mul(1099511628211); }
    std::process::exit((t % 251) as i32);
}
"#,
        oracle: 19,
        must_match: &[0, 1],
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
fn slice_sorts_order_like_std_or_refuse_by_name() {
    darwin_native::require("slice_sort_order_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("rcl2_slice_sort_a64_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let (mut cells, mut matched, mut refused) = (0, 0, 0);
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
                Outcome::Refused(tag) if tag.is_empty() => wrong.push(format!(
                    "{} O{opt}: compile failed with no named diagnostic",
                    case.name
                )),
                Outcome::Refused(tag) if case.must_match.contains(&opt) => wrong.push(format!(
                    "{} O{opt}: refused [{tag}] where it must match LLVM",
                    case.name
                )),
                Outcome::Refused(_) => refused += 1,
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        wrong.is_empty(),
        "slice sort order disagrees with std:\n{}",
        wrong.join("\n")
    );
    eprintln!(
        "SLICE_SORT_ORDER cases={} cells={cells} matched={matched} refused={refused} opts=0,1,2,3",
        CASES.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
