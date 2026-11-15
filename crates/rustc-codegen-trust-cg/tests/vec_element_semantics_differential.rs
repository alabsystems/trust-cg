#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a `Vec` intercept runs the element type's OWN semantics —
// its `Drop`, its `Clone`, its `PartialEq` — never those of the scalar the
// element maps to.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. Class-1 `Vec` admission (`vec_element_ty`) keys on the
// scalar an element maps to, which sees through single-field and nested
// newtypes (`W(u32)`, `F(f64)`, `std::fs::File`), and a class-2 struct is a
// byte image whatever its `Clone`. Four intercepts relied on the mapped type's
// semantics instead of the element's:
//
//   * `retain`/`retain_mut`, `dedup_by` and the shrink of `resize_with` removed
//     elements without dropping them, and `dedup` did the same through its
//     bit-comparing helper (`fix_vec_newtype_removed_drop`);
//   * `dedup` of a float newtype compared bits, not IEEE `==`
//     (`fix_vec_newtype_float_dedup`);
//   * `dedup_by_key` was synthesized with one key call per element, a bitwise
//     key comparison and no key drop, where std's body is
//     `dedup_by(|a, b| key(a) == key(b))` (`fix_vec_dedup_by_key_std_body`);
//   * `vec![x; n]` of a class-2 struct broadcast the bytes of `x` instead of
//     running a hand-written `Clone` (`fix_vec_from_elem_user_clone`).
//
// Under `panic=unwind` the same rows run too (`fix_vec_newtype_removed_drop`),
// and a hand-written `eq` that panics in `dedup` leaves the Vec as std's
// `FillGapOnDrop` does (`fix_vec_dedup_user_eq_unwind`): std's body runs, and
// the intercepted `dedup_by` it calls closes the gap in its model's landing
// pad (`emit_vec_compaction_guard_pad`). A
// `resize_with` shrink whose element drop panics drops the rest of the tail,
// as `truncate`'s slice drop glue does (`fix_vec_shrink_drop_panics_unwind`).
//
// THE GATE. Each row is compiled by the bridge (`no-proof-certs`, isolating MIR
// lowering from this host's opcode-proof inventory) and by LLVM with the same
// flags, run, and compared on STDOUT, EXIT CODE and KILLING SIGNAL.
//   * `Must`: the bridge must COMPILE and MATCH.
//   * `RefuseOrMatch(needles)`: the bridge must MATCH, or REFUSE with every
//     needle in its diagnostics. A row of this kind must never compile and
//     diverge.
//
// FALSIFIED (2026-10-05, aarch64-apple-darwin) against the pre-fix bridge
// (origin/main c8b07006b): every `fix_vec_newtype_removed_drop`,
// `fix_vec_dedup_by_key_std_body` and `fix_vec_from_elem_user_clone` row, the
// -O0/-O1 `fix_vec_newtype_float_dedup` rows and every
// `fix_vec_shrink_drop_panics_unwind` row COMPILE and DIVERGE. The
// `panic=unwind` rows were refused by name before the landing's intercept
// unwind guard (`fix_vec_dedup_user_eq_unwind` at -O0/-O1,
// `fix_vec_newtype_removed_drop` and `fix_vec_shrink_drop_panics_unwind` at
// every level); without that guard's gap closing, the
// `fix_vec_dedup_user_eq_unwind` rows COMPILE and DIVERGE. Since the merge of
// origin/main `7c60cee46` main's landing pads replace that guard; this
// falsification was not repeated on them.

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
    /// The LLVM oracle's stdout line count: a fixture whose oracle does not
    /// reach its end is not exercising the intercepts.
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
const O0_UNWIND: &[&str] = &["-Copt-level=0", "-Cpanic=unwind"];
const O1_UNWIND: &[&str] = &["-Copt-level=1", "-Cpanic=unwind"];
const O2_UNWIND: &[&str] = &["-Copt-level=2", "-Cpanic=unwind"];
const O3_UNWIND: &[&str] = &["-Copt-level=3", "-Cpanic=unwind"];
const UNWIND_LEVELS: [&[&str]; 4] = [O0_UNWIND, O1_UNWIND, O2_UNWIND, O3_UNWIND];

fn rows() -> Vec<Row> {
    let mut rows = Vec::new();
    let mut add = |(fixture, src): (&'static str, &'static str),
                   flags: &'static [&'static str],
                   oracle_lines: usize,
                   expect: Expect| {
        rows.push(Row {
            fixture,
            src,
            flags,
            oracle_lines,
            expect,
        })
    };
    for flags in LEVELS {
        add(
            fixture!("fix_vec_newtype_removed_drop"),
            flags,
            7,
            Expect::Must,
        );
        add(
            fixture!("fix_vec_newtype_float_dedup"),
            flags,
            2,
            Expect::Must,
        );
        add(
            fixture!("fix_vec_dedup_by_key_std_body"),
            flags,
            4,
            Expect::Must,
        );
        add(
            fixture!("fix_vec_from_elem_user_clone"),
            flags,
            1,
            Expect::RefuseOrMatch(&["[TCG-FROM-ELEM-CLONE]"]),
        );
        add(
            fixture!("fix_vec_from_elem_derived_clone"),
            flags,
            1,
            Expect::Must,
        );
    }
    // A later `-Cpanic` overrides the harness's `-Cpanic=abort`.
    for flags in UNWIND_LEVELS {
        add(
            fixture!("fix_vec_newtype_removed_drop"),
            flags,
            7,
            Expect::Must,
        );
        add(
            fixture!("fix_vec_dedup_user_eq_unwind"),
            flags,
            1,
            Expect::Must,
        );
        add(
            fixture!("fix_vec_shrink_drop_panics_unwind"),
            flags,
            9,
            Expect::Must,
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
        "tcg_vec_element_semantics_{stem}_{}",
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
fn vec_intercepts_run_the_element_types_own_semantics() {
    if toolchain_support::skip_without_backend_knobs(
        "vec_intercepts_run_the_element_types_own_semantics",
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
            (Some(0), None, row.oracle_lines),
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
    eprintln!("vec element-semantics rows: {matched} MATCH, {refused} REFUSED by name");
    assert!(
        failures.is_empty(),
        "{} vec element-semantics row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
