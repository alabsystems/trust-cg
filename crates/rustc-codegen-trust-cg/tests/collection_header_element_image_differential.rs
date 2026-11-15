#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a default-`Global` `Vec<T>` / `String` held INSIDE other
// storage -- an array element, the `vec` field of a `String`, an element moved
// by `ptr::copy_nonoverlapping` -- is rustc's whole 24-byte `{cap, ptr, len}`
// image, never the one-word carrier the bridge binds a header LOCAL with.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. A header LOCAL is bound to the address of its own
// 24-byte slot, so its trust-ir type is a one-word `Ptr` CARRIER, and
// `memory_scalar_leaf_ty` answers that carrier for the header TYPE. Three sites
// took it for the header's memory image:
//
//   * A memory-backed `[Vec<i64>; N]` / `[String; N]` went down the SCALAR
//     element arms: `[x, y]` stored one word (the source's slot address) per
//     24-byte element -- SIGSEGV at -O0..-O3, a wrong `[String; 3]` digest --
//     and `[const { Vec::new() }; N]` refused.
//   * A PROJECTED header read (`_61 = move (_6.0: Vec<u8>)`, the inlined
//     `String::into_bytes`) loaded the image's FIRST WORD (the capacity) as the
//     image address: SIGSEGV at -O2/-O3.
//   * `copy_nonoverlapping(src, dst, 1)` of a header element (what
//     `Vec<String>::retain` compacts with) was unrolled as ONE `Ptr` load/store:
//     a wrong digest, then a trap freeing a stale pointer, at -O0..-O3.
//
// THE GATE. Each row is compiled by the bridge (`no-proof-certs`, isolating MIR
// lowering from this host's opcode-proof inventory) and by LLVM with the same
// flags, run, and compared on STDOUT, EXIT CODE and KILLING SIGNAL.
//   * `Must`: the bridge must COMPILE and MATCH.
//   * `RefuseOrMatch(needles)`: the bridge must MATCH, or REFUSE with every
//     needle in its diagnostics -- a refusal for the named reason, never one a
//     dead backend or an unrelated refusal would satisfy. A row of this kind
//     must never compile and diverge.
//
// FALSIFIED (2026-10-01, aarch64-apple-darwin), one mutant per site, each
// with only that site's non-test source reverted:
//   * array images reverted: the array fixture DIVERGES (SIGSEGV) at -O0..-O3,
//     the const-repeat fixture refuses, the projected-read fixture DIVERGES at
//     -O2/-O3 (its `ptr::write` into an array element);
//   * projected header reads reverted: the projected-read fixture DIVERGES
//     (SIGSEGV) at -O2/-O3;
//   * the `copy_nonoverlapping` unroll reverted: the retain fixture DIVERGES
//     (a trap) at -O0..-O3.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy)]
enum Expect {
    Must,
    RefuseOrMatch(&'static [&'static str]),
}

struct Row {
    fixture: &'static str,
    src: &'static str,
    flags: &'static [&'static str],
    /// The LLVM oracle's exit status and stdout line count: a fixture whose
    /// oracle does not reach its end is not exercising the stored headers.
    oracle_code: i32,
    oracle_lines: usize,
    expect: Expect,
}

macro_rules! fixture {
    ($name:literal) => {
        ($name, include_str!(concat!("bridge_corpus/", $name, ".rs")))
    };
}

const O0: &[&str] = &["-Copt-level=0"];
const O1: &[&str] = &["-Copt-level=1"];
const O2: &[&str] = &["-Copt-level=2"];
const O3: &[&str] = &["-Copt-level=3"];
const LEVELS: [&[&str]; 4] = [O0, O1, O2, O3];

fn rows() -> Vec<Row> {
    let mut rows = Vec::new();
    let mut add = |(fixture, src): (&'static str, &'static str),
                   flags: &'static [&'static str],
                   oracle_code: i32,
                   oracle_lines: usize,
                   expect: Expect| {
        rows.push(Row {
            fixture,
            src,
            flags,
            oracle_code,
            oracle_lines,
            expect,
        })
    };
    for flags in LEVELS {
        add(
            fixture!("fix_collection_header_array_image"),
            flags,
            0,
            5,
            Expect::Must,
        );
        add(
            fixture!("fix_collection_header_const_repeat_array"),
            flags,
            0,
            1,
            Expect::Must,
        );
        add(
            fixture!("fix_collection_header_copy_nonoverlapping"),
            flags,
            0,
            2,
            Expect::Must,
        );
        // Refused by name at -O0/-O1: the un-inlined `String::into_bytes` and
        // `ptr::write::<Vec<i64>>` calls are not intercepted methods.
        let projected = if flags == O0 || flags == O1 {
            Expect::RefuseOrMatch(&["[TCG-MIR-UNSUPPORTED]", "into_bytes"])
        } else {
            Expect::Must
        };
        add(
            fixture!("fix_collection_header_projected_read"),
            flags,
            0,
            2,
            projected,
        );
    }
    rows
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tcg_collection_header_image_{stem}_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    flags: &[&str],
    backend: Option<&Path>,
) -> Result<Ending, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(if backend.is_some() {
        format!("{name}_bridge")
    } else {
        format!("{name}_llvm")
    });
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.args(flags);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    Ok(Ending {
        code: run.status.code(),
        signal: run.status.signal(),
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

#[test]
fn collection_headers_inside_other_storage_are_whole_images() {
    if toolchain_support::skip_without_backend_knobs(
        "collection_headers_inside_other_storage_are_whole_images",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures: Vec<String> = Vec::new();
    let (mut matched, mut refused) = (0usize, 0usize);
    for (index, row) in rows().iter().enumerate() {
        let dir = workdir(&format!("{}_{index}", row.fixture));
        let oracle =
            compile_and_run(&dir, row.fixture, row.src, row.flags, None).unwrap_or_else(|e| {
                panic!(
                    "{} {:?}: the LLVM oracle failed to compile: <<<{e}>>>",
                    row.fixture, row.flags
                )
            });
        assert_eq!(
            (oracle.code, oracle.signal, oracle.stdout.lines().count()),
            (Some(row.oracle_code), None, row.oracle_lines),
            "{} {:?}: the LLVM oracle did not reach the fixture's end: {oracle:?}",
            row.fixture,
            row.flags
        );
        match (
            compile_and_run(&dir, row.fixture, row.src, row.flags, Some(&dylib)),
            row.expect,
        ) {
            (Ok(bridge), _) if bridge == oracle => {
                matched += 1;
                eprintln!("{} {:?}: MATCH", row.fixture, row.flags);
            }
            (Ok(bridge), _) => failures.push(format!(
                "{} {:?}: compiled and DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}",
                row.fixture, row.flags
            )),
            (Err(stderr), Expect::Must) => failures.push(format!(
                "{} {:?}: the bridge refused a row that must compile: <<<{stderr}>>>",
                row.fixture, row.flags
            )),
            (Err(stderr), Expect::RefuseOrMatch(needles)) => {
                let missing: Vec<&str> = needles
                    .iter()
                    .copied()
                    .filter(|n| !stderr.contains(n))
                    .collect();
                if missing.is_empty() {
                    refused += 1;
                    eprintln!(
                        "{} {:?}: REFUSED by name {needles:?}",
                        row.fixture, row.flags
                    );
                } else {
                    failures.push(format!(
                        "{} {:?}: refused, but not for the named reason (missing {missing:?}): \
                         <<<{stderr}>>>",
                        row.fixture, row.flags
                    ));
                }
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    eprintln!("collection-header image rows: {matched} MATCH, {refused} REFUSED by name");
    assert!(
        failures.is_empty(),
        "{} collection-header image row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
