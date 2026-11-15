#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: two `alloc` shapes every program that builds a `vec![..]`
// or an `Rc<[T]>` / `Arc<[T]>` reaches compile and match LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS (both measured 2026-09-28 on AArch64 Darwin, refused before
// the fix at exactly the levels below; the Trust run-make recipes
// `trust-ir-cg-rawptr-scalar-newtype` and `trust-ir-cg-type-refusal-carries-fix`
// reach the same two seams):
//
// * `fix_p_vec_macro_o3_chain` — `vec![a, b, c]` at `-O2`/`-O3`. The current
//   std's MIR fuses the `Box.0.0` Field(0) descent into the transmute that
//   reads the box's fat pointer (`_13 = copy ((_9.0: Unique<[T]>).0:
//   NonNull<[T]>) as *const [T] (Transmute)`), which the box -> Vec chain
//   recognizer (`compute_box_into_vec_chains`) accepted only as two
//   statements, so the chain abandoned and the `Box<[T; N]> -> Box<[T]>`
//   Unsize refused (`memory-backed aggregate assignment Rvalue::Cast`).
// * `fix_p_rc_slice_layout_eq` — `Rc::<[u8]>::from` / `Arc::<[u8]>::from` at
//   every level. `try_allocate_for_layout` / `initialize_arcinner` compare two
//   `Layout`s (`debug_assert_eq!` at O0, the inlined `PartialEq` elsewhere);
//   the tag-only-enum field discriminant arm read `discriminant((_33.0:
//   AlignmentEnum))` of the single-scalar `Alignment` newtype through a
//   hand-built `Projection` key the local never has (`Place projection field 0
//   before aggregate binding`). It now reads through the place kernel
//   (`place_to_value`).
//
// THE GATE. The oracle (LLVM, same compiler, same optimization level) runs
// first. The bridge must COMPILE every row and match the oracle's exit code,
// which folds every value read back. HOST-NATIVE; the bridge side passes
// `no-proof-certs` (the opcode-inventory proof lane refuses every AArch64
// program with `[TCG-PROOF-465]`, unrelated to these seams).

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2", "-Copt-level=3"];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_alloc_shape_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code, or the compiler's refusal lines when it refuses.
fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<i32, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(if backend.is_some() {
        "bridge"
    } else {
        "oracle"
    });
    let mut cmd = toolchain_support::rustc_command_with_edition("2021");
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
                line.contains("[TCG-")
                    || line.starts_with("error")
                    || line.trim_start().starts_with("- ")
            })
            .take(12)
            .collect::<Vec<_>>()
            .join(" | "));
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    Ok(run
        .status
        .code()
        .expect("compiled program exited via signal, not an exit code"))
}

#[test]
fn std_alloc_shapes_compile_and_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("std_alloc_shapes_compile_and_match_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let rows: &[(&str, &str, i32)] = &[
        (
            "fix_p_vec_macro_o3_chain",
            include_str!("bridge_corpus/fix_p_vec_macro_o3_chain.rs"),
            230,
        ),
        (
            "fix_p_rc_slice_layout_eq",
            include_str!("bridge_corpus/fix_p_rc_slice_layout_eq.rs"),
            16,
        ),
    ];
    let mut failures = Vec::new();
    for (name, src, expected) in rows {
        for opt in OPT_LEVELS {
            let dir = workdir(&format!("{name}_{}", opt.len()));
            let oracle = compile_and_run(&dir, name, src, opt, None)
                .unwrap_or_else(|e| panic!("{name} ({opt}): LLVM oracle failed: <<<{e}>>>"));
            assert_eq!(
                oracle, *expected,
                "{name} ({opt}): the oracle does not compute the fixture's known value, so \
                 this test is measuring something else"
            );
            match compile_and_run(&dir, name, src, opt, Some(&dylib)) {
                Ok(code) if code == oracle => {}
                Ok(code) => failures.push(format!("{name} ({opt}): exit {code}, LLVM {oracle}")),
                Err(e) => failures.push(format!("{name} ({opt}): trust-cg REFUSED: <<<{e}>>>")),
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
