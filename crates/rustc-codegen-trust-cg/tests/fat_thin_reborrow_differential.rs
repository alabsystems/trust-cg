#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a REBORROW of the thin pointer the fat -> thin cast seam
// produced compiles and matches LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. `lower_wide_to_thin_ptr_cast` (and its trait-object twin
// `lower_dyn_fat_to_thin_ptr_cast`) binds the narrowed destination to the fat
// pointer's DATA lane, a plain `Ptr`. A later `&*p` of that destination goes
// through `retype_thin_pointer_to_local`, which declares the SOURCE local's own
// type (`PtrConst([u8; N])`, `PtrConst(u8)`) as its `PtrToPtr` source — so with
// the lane bound untyped every such reborrow was refused at the adapter's
// cast-source gate:
//
//     CastOp::PtrToPtr source type mismatch: declared src_ty=PtrConst(Tuple([U8,
//     ..])), operand ValueId(..) has type Ptr
//
// That is `<[T]>::as_array` and therefore every `<[T] as PartialEq<[T; N]>>::eq`
// (`slice == b"..."`), which stopped the Trust run-make programs
// `trust-ir-cg-scalarized-fat-leaf` and `trust-ir-cg-box-dyn-param` when the
// seam reached Trust (2026-09-28). The fix binds the kept lane at the
// destination local's own type (`retype_plain_address_to_local`). Revert it and
// every row below refuses at `-O0`, and `head4`/`is_hello` refuse at `-O2`.
//
// THE GATE. The oracle (LLVM, same compiler, same optimization level) runs
// first. The bridge must COMPILE every row — these are exactly the shapes the
// fix admits, so a refusal is a failure here — and match the oracle's stdout
// and exit code; every printed value is read THROUGH the reborrowed pointer, so
// a data lane from the wrong half is a wrong number, not a refusal.
//
// HOST-NATIVE: no `--target` is passed. WHY THE BRIDGE SIDE PASSES
// `no-proof-certs`: with proof certificates on, this backend refuses every
// AArch64 program with `[TCG-PROOF-465]` (the opcode-inventory proof lane, a
// whole-target fact unrelated to this seam), which would hide the refusal this
// test exists to catch behind an unrelated one. The knob is applied to the
// bridge side only; the compared values are the two backends' answers to the
// same program.

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_fatthin_rb_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code + stdout, or the compiler's stderr tail when it refuses.
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
            .filter(|line| line.contains("[TCG-") || line.starts_with("error"))
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
fn fat_thin_seam_reborrow_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs("fat_thin_seam_reborrow_matches_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let name = "fix_p_fat_thin_reborrow";
    let src = include_str!("bridge_corpus/fix_p_fat_thin_reborrow.rs");
    for opt in OPT_LEVELS {
        let dir = workdir(&format!("o{}", opt.len()));
        let oracle = compile_and_run(&dir, name, src, opt, None)
            .unwrap_or_else(|e| panic!("{name} ({opt}): LLVM oracle failed: <<<{e}>>>"));
        assert!(
            oracle.stdout.contains("r4 true") && oracle.stdout.contains("r7 41 42"),
            "{name} ({opt}): the oracle does not print the fixture's known values, so this \
             test is measuring something else: {:?}",
            oracle.stdout
        );
        let bridge = compile_and_run(&dir, name, src, opt, Some(&dylib)).unwrap_or_else(|e| {
            panic!(
                "{name} ({opt}): trust-cg REFUSED a reborrow of a fat -> thin cast result: \
                 <<<{e}>>>"
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
