#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a loop that stores THROUGH a pointer it carries compiles
// and matches LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. Once thin pointers became loop-header phis (275e8973a), a
// `&mut` live across a loop is threaded through the header as an identity phi.
// The back-edge faithfulness check (`patch_loop_header_edge`) keyed its "mutated
// inside the loop" set on every assigned place's base local, so a store through
// the pointer (`(*_2) = Add(copy (*_2), ..)`) counted as a mutation OF the
// pointer, and the unchanged pointer on the back edge was reported as a dropped
// update:
//
//     loop-carried local _2 is mutated inside the loop but its back-edge value is
//     the unchanged loop-header phi parameter
//
// The completeness gate beside it already skipped `Deref`-led stores; both now
// read one def-site map (`own_storage_assign_blocks`). Revert that and
// `ref_store` is refused at -O0, `closure_store`/`closure_store_u64` at -O2 and
// -O3 (Trust run-make `trust-ir-cg-borrow-join-lanes`, 2026-09-28).
//
// THE GATE. The LLVM oracle runs first; the bridge must compile every row and
// match its stdout and exit code. Every printed value is the pointee after the
// loop, so a store that WAS dropped — the miscompile the check exists for —
// prints the entry value instead of passing.
//
// HOST-NATIVE: no `--target`. The bridge side passes `no-proof-certs` for the
// reason `fat_thin_reborrow_differential.rs` states: with certificates on,
// every AArch64 program is refused by `[TCG-PROOF-465]` first.

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2", "-Copt-level=3"];

fn workdir(stem: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("tcg_loop_store_ptr_{stem}_{}", std::process::id()));
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
    let code = run
        .status
        .code()
        .expect("compiled program exited via signal, not an exit code");
    Ok(Run {
        code,
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

#[test]
fn loop_store_through_carried_pointer_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs(
        "loop_store_through_carried_pointer_matches_llvm",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let name = "fix_p_loop_store_through_pointer";
    let src = include_str!("bridge_corpus/fix_p_loop_store_through_pointer.rs");
    for opt in OPT_LEVELS {
        let dir = workdir(&format!("o{}", opt.len()));
        let oracle = compile_and_run(&dir, name, src, opt, None)
            .unwrap_or_else(|e| panic!("{name} ({opt}): LLVM oracle failed: <<<{e}>>>"));
        assert_eq!(
            oracle.stdout, "s1 4\ns2 123\ns3 362\n",
            "{name} ({opt}): the oracle does not print the fixture's known values, so this \
             test is measuring something else"
        );
        let bridge = compile_and_run(&dir, name, src, opt, Some(&dylib)).unwrap_or_else(|e| {
            panic!(
                "{name} ({opt}): trust-cg REFUSED a loop that stores through a carried \
                 pointer: <<<{e}>>>"
            )
        });
        assert_eq!(
            bridge.stdout, oracle.stdout,
            "{name} ({opt}): STDOUT differs from LLVM"
        );
        assert_eq!(
            bridge.code, oracle.code,
            "{name} ({opt}): exit code differs from LLVM"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
