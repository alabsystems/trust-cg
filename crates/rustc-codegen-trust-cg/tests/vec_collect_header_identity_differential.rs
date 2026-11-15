#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: an intercepted `collect::<Vec<T>>()` must leave its elements
// in the header the destination local OWNS.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. The real-layout Vec/String header change (b56846c55)
// made every `Vec`/`String` local memory-backed and taught `finish_assign_target`
// to COPY a producer's scratch header into the local's own slot at the bind.
// Every constructor that finishes its header before binding stayed correct.
// `lower_vec_collect` binds FIRST and then drives a push loop over the header,
// and kept pushing into the scratch: the destination was left at the bind-time
// snapshot (len 0, cap 0, dangling pointer), so `(0..n).collect::<Vec<_>>()` and
// `slice.iter().map(..).collect()` returned an EMPTY Vec with exit status 0 at
// every opt level, and the drop freed nothing (the grown buffer leaked). A
// later `v[i]` panicked "index out of bounds" (-O0/-O1) or trapped (-O2/-O3).
//
// THE GATE. Each row is compiled by the bridge (`no-proof-certs`, isolating MIR
// lowering from this host's opcode-proof inventory) and by LLVM with the same
// flags, run, and compared on STDOUT, EXIT CODE and KILLING SIGNAL.
//
//   * `Must`: the bridge must COMPILE and MATCH. Every row diverged before the
//     fix (measured on aarch64-apple-darwin against origin/main 7b2412bc8).
//   * `MatchOrRefuse`: the bridge may refuse with a NAMED `[TCG-...]` diagnostic
//     (the companion fixture's `StepBy` and owning-`IntoIter` shapes are refused
//     past -O0/-O1); if it compiles, it must match.
//
// FALSIFIED (2026-09-30, aarch64-apple-darwin): with the fix reverted (the
// collect loop pushing into the scratch header again), all five `Must` rows
// fail — `fix_vec_collect_header_identity` diverges at -O0..-O3 (zeros, then an
// "index out of bounds" panic at -O0/-O1 and SIGTRAP at -O2/-O3) and
// `fix_vec_collect_header_identity_o0` prints `0 0` for `7078 67620` at -O0. The
// three `MatchOrRefuse` rows are refused `[TCG-MIR-UNSUPPORTED]` either way.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Policy {
    Must,
    MatchOrRefuse,
}

struct Row {
    fixture: &'static str,
    src: &'static str,
    flags: &'static [&'static str],
    policy: Policy,
}

macro_rules! fixture {
    ($name:literal) => {
        ($name, include_str!(concat!("bridge_corpus/", $name, ".rs")))
    };
}

fn row(
    fixture: (&'static str, &'static str),
    flags: &'static [&'static str],
    policy: Policy,
) -> Row {
    Row {
        fixture: fixture.0,
        src: fixture.1,
        flags,
        policy,
    }
}

fn rows() -> Vec<Row> {
    use Policy::{MatchOrRefuse, Must};
    const O0: &[&str] = &["-Copt-level=0"];
    const O1: &[&str] = &["-Copt-level=1"];
    const O2: &[&str] = &["-Copt-level=2"];
    const O3: &[&str] = &["-Copt-level=3"];
    vec![
        row(fixture!("fix_vec_collect_header_identity"), O0, Must),
        row(fixture!("fix_vec_collect_header_identity"), O1, Must),
        row(fixture!("fix_vec_collect_header_identity"), O2, Must),
        row(fixture!("fix_vec_collect_header_identity"), O3, Must),
        row(fixture!("fix_vec_collect_header_identity_o0"), O0, Must),
        row(
            fixture!("fix_vec_collect_header_identity_o0"),
            O1,
            MatchOrRefuse,
        ),
        row(
            fixture!("fix_vec_collect_header_identity_o0"),
            O2,
            MatchOrRefuse,
        ),
        row(
            fixture!("fix_vec_collect_header_identity_o0"),
            O3,
            MatchOrRefuse,
        ),
    ]
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_vec_collect_{stem}_{}", std::process::id()));
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

/// The bridge's own named refusal tag, if this stderr is a fail-closed refusal
/// rather than a crash.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

#[test]
fn collect_into_vec_fills_the_destination_header() {
    if toolchain_support::skip_without_backend_knobs(
        "collect_into_vec_fills_the_destination_header",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures: Vec<String> = Vec::new();
    for (index, row) in rows().iter().enumerate() {
        let dir = workdir(&format!("{}_{index}", row.fixture));
        let oracle =
            compile_and_run(&dir, row.fixture, row.src, row.flags, None).unwrap_or_else(|e| {
                panic!(
                    "{} {:?}: the LLVM oracle failed to compile: <<<{e}>>>",
                    row.fixture, row.flags
                )
            });
        // The oracle must have run the program to completion: a fixture whose
        // LLVM build does not exit 0 is not exercising the collected Vecs.
        assert_eq!(
            (oracle.code, oracle.signal),
            (Some(0), None),
            "{} {:?}: the LLVM oracle did not exit cleanly: {oracle:?}",
            row.fixture,
            row.flags
        );
        match compile_and_run(&dir, row.fixture, row.src, row.flags, Some(&dylib)) {
            Ok(bridge) if bridge == oracle => {
                eprintln!("{} {:?}: MATCH", row.fixture, row.flags);
            }
            Ok(bridge) => failures.push(format!(
                "{} {:?}: compiled and DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}",
                row.fixture, row.flags
            )),
            Err(stderr) => match (row.policy, named_refusal(&stderr)) {
                (Policy::MatchOrRefuse, Some(tag)) => {
                    eprintln!(
                        "{} {:?}: REFUSED {tag} (fail-closed)",
                        row.fixture, row.flags
                    );
                }
                (Policy::Must, Some(tag)) => failures.push(format!(
                    "{} {:?}: refused ({tag}) a row that must compile",
                    row.fixture, row.flags
                )),
                (_, None) => failures.push(format!(
                    "{} {:?}: failed WITHOUT a named [TCG-...] refusal: <<<{stderr}>>>",
                    row.fixture, row.flags
                )),
            },
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(
        failures.is_empty(),
        "{} collect row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
