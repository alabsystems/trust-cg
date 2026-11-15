#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a slice-tail DST prefix-field borrow whose DESTINATION is a
// scalar cell (`bridge_corpus/fix_slice_tail_celled_field_borrow.rs`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `slice_tail::assign` lowers `_3 = &((*_1).f)` before `lower_assign`'s
// whole-local cell store runs. When `_3` is a scalar cell (its address is taken
// by `&_3`), the borrow must be stored into the cell; an SSA-only binding leaves
// the cell uninitialized. Measured on aarch64-apple-darwin before the fix: the
// bridge binary aborted with a stack overflow at `-Copt-level=0` and died with
// SIGSEGV at `-Copt-level=2`, where LLVM prints the field value three times.
//
// THE GATE is strict: at every level the bridge must COMPILE and produce the
// same stdout and exit code as LLVM. A refusal fails the test too, because it
// would hide the regression the row pins.
//
// PROOF CERTIFICATES are disabled on the bridge side (`no-proof-certs`). On the
// host this was measured on, the opcode-proof inventory rejects every function
// (`[TCG-PROOF-465]`, including `std::rt::lang_start`), so a proof-required
// compile produces no binary and could not observe a lowering defect at all.
// Passing is lowering evidence, not proof evidence.
//
// HOST-NATIVE: no `--target`, so this runs on the host that builds the crate.

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];
const NAME: &str = "fix_slice_tail_celled_field_borrow";
const SRC: &str = include_str!("bridge_corpus/fix_slice_tail_celled_field_borrow.rs");

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_stcell_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` (with the bridge when `backend` is `Some`) and run it. `Err`
/// carries the compiler's stderr; a run killed by a signal is reported as such.
fn compile_and_run(
    dir: &Path,
    src: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<(Option<i32>, String), String> {
    let src_path = dir.join(format!("{NAME}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(if backend.is_some() { "cg" } else { "llvm" });
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg("-Ztrust-ir-cg-args=no-proof-certs");
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    Ok((
        run.status.code(),
        String::from_utf8_lossy(&run.stdout).into_owned(),
    ))
}

#[test]
fn celled_slice_tail_field_borrow_matches_llvm() {
    let backend = backend_artifact_support::current_test_backend();
    let mut failures = Vec::new();
    for opt in OPT_LEVELS {
        let dir = workdir(&opt.replace('=', "_"));
        let reference = compile_and_run(&dir, SRC, opt, None)
            .unwrap_or_else(|stderr| panic!("FIXTURE BROKEN: LLVM {opt}: {stderr}"));
        assert_eq!(
            reference.0,
            Some(0),
            "LLVM oracle must exit normally at {opt}"
        );
        assert_eq!(
            reference.1, "direct=72623859790382856\nraw=72623859790382856\ntup=72623859790382856\n",
            "LLVM oracle output changed at {opt}"
        );
        match compile_and_run(&dir, SRC, opt, Some(&backend)) {
            Err(stderr) => failures.push(format!(
                "{opt}: the bridge refused (this row must compile): {}",
                stderr
                    .lines()
                    .filter(|l| l.contains("[TCG-") || l.contains(" - "))
                    .collect::<Vec<_>>()
                    .join(" | ")
            )),
            Ok(outcome) if outcome != reference => failures.push(format!(
                "{opt}: MISCOMPILE: bridge exit {:?} stdout {:?}, LLVM exit {:?} stdout {:?}",
                outcome.0, outcome.1, reference.0, reference.1
            )),
            Ok(_) => eprintln!("{NAME} {opt}: compiled and matched LLVM"),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
