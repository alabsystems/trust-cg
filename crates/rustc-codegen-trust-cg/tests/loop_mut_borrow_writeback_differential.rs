#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a one-lane local that a loop changes ONLY through a
// mutable borrow of it compiles and matches LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. A `&mut x` call argument of a scalarized one-lane local is
// lowered by value: the bridge stores `x` into a borrow home, passes the home's
// address, and after the call reloads it and REBINDS `x`
// (`reload_mutable_reference_call_args`). A store through a `&mut x` taken
// before the loop rebinds `x` the same way. Neither is an assignment of `x`,
// so the loop-header analysis (`compute_loop_header_params`) gave a pointer
// whose only pre-loop definition is a call result no header phi, and the
// completeness gate (`loop_carried_completeness_error`) did not count the
// write-back as an in-loop change. Every iteration re-stored the PRE-LOOP
// value into the home and the loop exit read it: wrong pointers, references,
// `fn` pointers and `NonNull`s, a store through a stale `&mut` into the wrong
// array, and, for `Box`, a use-after-free plus a double free (libmalloc abort)
// at -O0 through -O3. Both analyses now read one `MutableBorrowReach`; the
// local is threaded through the header phi, and a one-lane local the phi
// cannot carry is refused by name ([TCG-LOOP-MUT-BORROW]).
//
// THE GATE. The LLVM oracle runs first and must print the fixture's known
// values; the bridge must compile the fixture and match its stdout and exit
// code at every level. A dropped write-back prints the pre-loop value; the
// `Box` rows abort on the double free instead.
//
// HOST-NATIVE: no `--target`. The bridge side passes `no-proof-certs` for the
// reason `fat_thin_reborrow_differential.rs` states: with certificates on,
// every AArch64 program is refused by `[TCG-PROOF-465]` first.

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &[
    "-Copt-level=0",
    "-Copt-level=1",
    "-Copt-level=2",
    "-Copt-level=3",
];

const FIXTURE: &str = "fix_p_loop_mut_borrow_writeback";

const EXPECTED: &str = "\
raw_ptr 1 1 1
ref 6
fn_ptr 700 8
non_null 6
ref_mut 51 3456 304051
newtype 6
while_ptr 6
nested 2703
two_borrows 34506
header_borrow 306 3
generic 6
loop_break 6
via_struct 6
preloop_store 6
box_swap 5 50025
box_user 1 32
cond_borrow 6
two_args 63
newtype_field 6
rc 2 59
reborrow_through 32
";

fn workdir(stem: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("tcg_loop_mut_borrow_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code + stdout, or the compiler's diagnostic lines when it refuses.
fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<Run, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(if backend.is_some() {
        "bridge"
    } else {
        "oracle"
    });

    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr)
            .lines()
            .filter(|line| {
                line.contains("[TCG-") || line.contains(" - ") || line.starts_with("error")
            })
            .take(12)
            .collect::<Vec<_>>()
            .join(" | "));
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    let Some(code) = run.status.code() else {
        return Err(format!(
            "the compiled program died on a signal ({:?}) after printing <<<{}>>>",
            run.status,
            String::from_utf8_lossy(&run.stdout)
        ));
    };
    Ok(Run {
        code,
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

#[test]
fn loop_mut_borrow_writeback_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs("loop_mut_borrow_writeback_matches_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let src = include_str!("bridge_corpus/fix_p_loop_mut_borrow_writeback.rs");
    for opt in OPT_LEVELS {
        let dir = workdir(&opt.replace('=', "_"));
        let oracle = compile_and_run(&dir, FIXTURE, src, opt, None)
            .unwrap_or_else(|e| panic!("{FIXTURE} ({opt}): LLVM oracle failed: <<<{e}>>>"));
        assert_eq!(
            oracle.stdout, EXPECTED,
            "{FIXTURE} ({opt}): the oracle does not print the fixture's known values, so this \
             test is measuring something else"
        );
        let bridge = compile_and_run(&dir, FIXTURE, src, opt, Some(&dylib)).unwrap_or_else(|e| {
            panic!(
                "{FIXTURE} ({opt}): trust-cg refused or crashed on a loop that changes a local \
                 only through a mutable borrow: <<<{e}>>>"
            )
        });
        assert_eq!(
            bridge.stdout, oracle.stdout,
            "{FIXTURE} ({opt}): STDOUT differs from LLVM (a dropped write-back prints the \
             pre-loop value)"
        );
        assert_eq!(
            bridge.code, oracle.code,
            "{FIXTURE} ({opt}): exit code differs from LLVM"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
