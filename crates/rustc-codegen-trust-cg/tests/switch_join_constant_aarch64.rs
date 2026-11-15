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

// A switch case constant is not reused on the paths that skipped it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The AArch64 switch cascade (`select_switch_cascade`, and `switch.rs`'s
// linear scan for binary-search leaves) compares the selector case by case in
// one block: `cmp; b.eq; cmp; b.eq; ...`. A case value outside `CMP`'s 12-bit
// immediate was materialized just before its own compare, AFTER the earlier
// `b.eq`s, so it ran only on the paths that did not take them. GVN and CSE
// treat a value defined in a block as available in every block that block
// dominates. Each merged the case constant into an equal constant in the
// switch's join block, which then read a register the earlier exits never
// wrote. Measured on trust-cg main 72a46f7ed and cb0c8c873 (2026-10-09,
// against LLVM): after `match bb(E2::Y) {..}` on a `#[repr(u16)] enum E2 {
// X = 1000, Y = 7, Z = 65535 }`, a later `bb(E2::Z) as u16` read 7 at -O2 and
// 2364 at -O3 (`enum_u16_join`, `enum_mix`; both panic strategies; -O0/-O1
// were right).
// Disabling GVN and CSE together cured it; either alone did not.
//
// The fix materializes every case register before the block's first exit,
// and GVN and CSE make a value defined after a mid-block conditional exit
// available only to the rest of its own block. The `u32`, negative `i64` and
// binary-search-leaf programs are controls of the same shape that matched
// before. Every cell must match LLVM's pinned stdout.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

const TARGET: &str = "aarch64-apple-darwin";
const OPTS: [u32; 4] = [0, 1, 2, 3];
const PANICS: [&str; 2] = ["abort", "unwind"];

struct Program {
    name: &'static str,
    src: &'static str,
    /// The LLVM oracle's stdout (every program exits 0), so a broken oracle
    /// cannot pass.
    stdout: &'static str,
}

const PROGRAMS: &[Program] = &[
    Program {
        name: "enum_u16_join",
        src: r##"use std::hint::black_box as bb;
#[derive(Clone, Copy)] #[repr(u16)] enum E2 { X = 1000, Y = 7, Z = 65535 }
fn main() {
    let b = { let e = bb(E2::Y); match e { E2::X => 1, E2::Y => 2, E2::Z => 3 } };
    let d = { let e = bb(E2::Z); e as u16 as i64 };
    println!("{} {}", b, d);
}
"##,
        stdout: "2 65535\n",
    },
    Program {
        name: "enum_mix",
        src: r##"use std::hint::black_box as bb;
fn mix(h: u64, v: i128) -> u64 { (h ^ (v as u64) ^ ((v >> 64) as u64)).wrapping_mul(1099511628211) }
#[derive(Clone, Copy)] #[repr(i8)] enum E1 { A = -3, B = 5, C = 100, D = -128 }
#[derive(Clone, Copy)] #[repr(u16)] enum E2 { X = 1000, Y = 7, Z = 65535 }
#[derive(Clone, Copy)] enum P { Unit, One(u8), Two(i32, i64), Big { a: u64, b: u16 } }
#[derive(Clone, Copy)] enum N { Q(Option<u32>), R(Option<char>), S }
fn main() {
    let a = { let e = bb(E1::B); (e as i8 as i128) * 1000 + match e { E1::A => 1, E1::B => 2, E1::C => 3, E1::D => 4 } };
    let b = { let e = bb(E2::Y); (e as u16 as i128) * 10 + match e { E2::X => 1, E2::Y => 2, E2::Z => 3 } };
    let c = match bb(P::One(bb(200))) { P::Unit => 1, P::One(x) => x as i128 + 10, P::Two(a, b) => a as i128 * 3 + b as i128, P::Big { a, b } => a as i128 - b as i128 };
    let d = { let e = bb(E2::Z); (e as u16 as i128) * 10 + match e { E2::X => 1, E2::Y => 2, E2::Z => 3 } };
    let f = match bb(N::Q(bb(Some(7)))) { N::Q(Some(x)) => x as i128, N::Q(None) => -1, N::R(Some(c)) => c as i128 * 2, N::R(None) => -2, N::S => -3 };
    println!("{} {} {} {} {}", a as i64, b as i64, c as i64, d as i64, f as i64);
}
"##,
        stdout: "5002 72 210 655353 7\n",
    },
    Program {
        name: "u32_join",
        src: r##"use std::hint::black_box as bb;
fn main() {
    let s = match bb(7u32) { 1000 => 1, 7 => 2, 300000 => 3, _ => 4 };
    let k = bb(300000u32);
    let t = match bb(1000u32) { 1000 => 5, 7 => 6, 300000 => 7, _ => 8 };
    let j = bb(300000u32);
    println!("{} {} {} {}", s, k, t, j);
}
"##,
        stdout: "2 300000 5 300000\n",
    },
    Program {
        name: "i64_neg_join",
        src: r##"use std::hint::black_box as bb;
fn main() {
    let s = match bb(5i64) { 1 => 1, 5 => 2, -70000 => 3, _ => 4 };
    let k = bb(-70000i64);
    let t = match bb(1i64) { 1 => 5, 5 => 6, -1 => 7, _ => 8 };
    let j = bb(-1i64);
    println!("{} {} {} {}", s, k, t, j);
}
"##,
        stdout: "2 -70000 5 -1\n",
    },
    Program {
        name: "bst_leaf_join",
        src: r##"use std::hint::black_box as bb;
#[inline(never)]
fn class(x: u64) -> u64 {
    match x { 1 => 11, 2 => 12, 100000 => 13, 200000 => 14, 300000 => 15, 400000 => 16, 500000 => 17, 9000000 => 18, _ => 19 }
}
fn main() {
    let a = class(bb(2));
    let k = bb(300000u64);
    let b = class(bb(1));
    let j = bb(9000000u64);
    let c = class(bb(400000));
    let m = bb(500000u64);
    println!("{} {} {} {} {} {}", a, k, b, j, c, m);
}
"##,
        stdout: "12 300000 11 9000000 16 500000\n",
    },
];

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    stderr: String,
}

fn workdir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_switch_join_constant_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `program` with LLVM (`backend == None`) or the bridge and run it.
fn compile_and_run(
    dir: &Path,
    program: &Program,
    opt: u32,
    panic: &str,
    backend: Option<(&Path, &str)>,
) -> Result<Ending, String> {
    let side = if backend.is_some() { "tcg" } else { "llvm" };
    let stem = format!("{}_O{opt}_{panic}_{side}", program.name);
    let src = dir.join(format!("{stem}.rs"));
    std::fs::write(&src, program.src).expect("write source");
    let exe = dir.join(&stem);
    let mut cmd = toolchain_support::rustc_command_with_edition("2021");
    cmd.args([
        "--target",
        TARGET,
        "--crate-type",
        "bin",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Cpanic={panic}"))
    .arg(format!("-Copt-level={opt}"));
    if let Some((dylib, knobs)) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(dylib);
        cmd.arg(arg).arg(knobs);
    }
    cmd.arg("-o").arg(&exe).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&exe).output().expect("run the program");
    Ok(Ending {
        code: run.status.code(),
        signal: run.status.signal(),
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&run.stderr).into_owned(),
    })
}

/// One cell: the LLVM oracle must be the pinned run, and the bridge must
/// compile and match it exactly.
fn judge_cell(
    dir: &Path,
    program: &Program,
    opt: u32,
    panic: &str,
    backend: &Path,
    knobs: &str,
) -> Result<(), String> {
    let cell = format!("{} -O{opt} -Cpanic={panic}", program.name);
    let oracle = compile_and_run(dir, program, opt, panic, None)
        .map_err(|stderr| format!("{cell}: LLVM failed to compile: {stderr}"))?;
    if (oracle.code, oracle.signal, oracle.stdout.as_str()) != (Some(0), None, program.stdout) {
        return Err(format!(
            "{cell}: the LLVM oracle is not the pinned run: {oracle:?}"
        ));
    }
    match compile_and_run(dir, program, opt, panic, Some((backend, knobs))) {
        Ok(bridge) if bridge == oracle => Ok(()),
        Ok(bridge) => Err(format!(
            "{cell}: compiled and DIVERGES -- LLVM {oracle:?}, trust-cg {bridge:?}"
        )),
        Err(stderr) => Err(format!("{cell}: refused: <<<{stderr}>>>")),
    }
}

#[test]
fn a_switch_case_constant_is_not_reused_where_it_was_skipped_aarch64() {
    darwin_native::require("switch_join_constant_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    // Built once on the test's own thread, so its knob trace lands in this
    // test's captured output.
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let dir = workdir();
    let cells: Vec<(&Program, u32, &str)> = PROGRAMS
        .iter()
        .flat_map(|p| {
            OPTS.iter()
                .flat_map(move |&o| PANICS.iter().map(move |&k| (p, o, k)))
        })
        .collect();
    let next = Mutex::new(0usize);
    let failures: Mutex<Vec<(usize, String)>> = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| {
                loop {
                    let index = {
                        let mut next = next.lock().unwrap();
                        let index = *next;
                        *next += 1;
                        index
                    };
                    let Some(&(program, opt, panic)) = cells.get(index) else {
                        break;
                    };
                    if let Err(why) = judge_cell(&dir, program, opt, panic, &backend, &knobs) {
                        failures.lock().unwrap().push((index, why));
                    }
                }
            });
        }
    });
    let _ = std::fs::remove_dir_all(&dir);
    let mut failures = failures.into_inner().unwrap();
    failures.sort();
    assert!(
        failures.is_empty(),
        "{} cell(s) failed:\n  {}",
        failures.len(),
        failures
            .into_iter()
            .map(|(_, why)| why)
            .collect::<Vec<_>>()
            .join("\n  ")
    );
    eprintln!(
        "SWITCH_JOIN_CONSTANT programs={} cells={} matched={} opts=0,1,2,3 strategies=abort,unwind",
        PROGRAMS.len(),
        cells.len(),
        cells.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
