#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a call with a `Vec` first argument is lowered as a `Vec`
// method only when it runs the standard library's own code for that `Vec`, and
// a modeled comparison or extend only when its other operand has the types the
// model reads.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. `lower_vec_call` recognized a `Vec` method from a crate
// test on the callee (any core/alloc/std def), the first argument's type with
// one reference or raw pointer peeled, and the bare item name, and took the
// element type from that first argument alone. That replaced:
//   * `core::ptr::eq::<Vec<T>>` (a free function) with content equality;
//   * a USER `impl PartialEq<P>` / `PartialOrd<P>` / `FromIterator<Q>` for
//     `Vec<u32>`, reached through core's provided `ne` / `lt` / `collect`, with
//     the built-in comparison or collect;
//   * alloc's `Vec<T> == [T; N]` / `== [T]` and `Vec<T> == Vec<U>` (with the
//     user's `T: PartialEq<U>`) with a raw lane scan of a second "Vec header";
//   * `v.extend([&a, &b])` (alloc's `Extend<&T>`) with a copy of the pointers.
// The slice `contains` interception had the same crate-and-name identity and
// replaced core's provided `RangeBounds::contains` on a user `[u32]` impl. The
// map interceptors had it too; a std callee taking a modeled map that is not
// the map's own inherent method (`ptr::eq`) is refused by name
// (`[TCG-MAP-CALLEE]`). Each fixture's header names its measured behavior on
// 6b108b81d.
//
// THE GATE. Each row is compiled by the bridge (`no-proof-certs`, isolating MIR
// lowering from this host's opcode-proof inventory) and by LLVM with the same
// flags, run, and compared on STDOUT, EXIT CODE and KILLING SIGNAL.
//   * `Match`: the bridge must build the program and match LLVM.
//   * `RefuseOrMatch(needles)`: the bridge must match, or refuse with every
//     needle in its diagnostics. It must never compile and diverge.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy)]
enum Expect {
    Match,
    RefuseOrMatch(&'static [&'static str]),
}

struct Row {
    fixture: &'static str,
    src: &'static str,
    flags: &'static [&'static str],
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

/// Every fixture exits 3 with no stdout under LLVM; each wrong answer sets one
/// more bit of the exit code.
const ORACLE_CODE: i32 = 3;

fn rows() -> Vec<Row> {
    let mut rows = Vec::new();
    for flags in LEVELS {
        for (fixture, src) in [
            fixture!("fix_vec_eq_untyped_rhs"),
            fixture!("fix_vec_eq_foreign_element"),
            fixture!("fix_vec_ptr_eq_free_fn"),
            fixture!("fix_vec_user_impl_provided"),
            fixture!("fix_slice_contains_range_bounds"),
        ] {
            rows.push(Row {
                fixture,
                src,
                flags,
                expect: Expect::Match,
            });
        }
        // At -O2/-O3 rustc inlines `extend` into std's `Vec::extend_trusted`,
        // which the bridge does not model and refuses by name.
        rows.push(Row {
            fixture: fixture!("fix_vec_extend_ref_array").0,
            src: fixture!("fix_vec_extend_ref_array").1,
            flags,
            expect: if flags == O0 || flags == O1 {
                Expect::Match
            } else {
                Expect::RefuseOrMatch(&["[TCG-MIR-UNSUPPORTED]", "extend_trusted"])
            },
        });
        // Where `ptr::eq` over maps reaches the bridge (-O0/-O1) it is refused by
        // name; at -O2/-O3 rustc inlines it into a raw-pointer comparison.
        rows.push(Row {
            fixture: fixture!("fix_map_ptr_eq_callee").0,
            src: fixture!("fix_map_ptr_eq_callee").1,
            flags,
            expect: Expect::RefuseOrMatch(&["[TCG-MAP-CALLEE]"]),
        });
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
        "tcg_vec_callee_identity_{stem}_{}",
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
fn a_vec_method_is_the_standard_librarys_own_code_for_that_vec() {
    if toolchain_support::skip_without_backend_knobs(
        "a_vec_method_is_the_standard_librarys_own_code_for_that_vec",
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
            (oracle.code, oracle.signal, oracle.stdout.as_str()),
            (Some(ORACLE_CODE), None, ""),
            "{} {:?}: the LLVM oracle did not answer every check correctly: {oracle:?}",
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
            (Err(stderr), Expect::Match) => failures.push(format!(
                "{} {:?}: refused, but this row must build and match: <<<{stderr}>>>",
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
    eprintln!("callee-identity rows: {matched} MATCH, {refused} REFUSED by name");
    assert!(
        failures.is_empty(),
        "{} callee-identity row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
