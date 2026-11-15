#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a WHOLE-OBJECT store `(*p) = move src` of an aggregate that
// holds a WIDE pointer leaf (`NonNull<dyn Trait>`, `NonNull<[T]>`,
// `NonNull<str>`) compiles and matches LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. `reference_pointee_to_trust_ir_ty` types such a pointee as a
// uniform lane TILING of its rustc image, because the scalar-leaf flattener
// refuses the wide `{data, metadata}` leaf. `lower_aggregate_memory_store` asks
// `flattened_leaf_layout_offsets` whether the slot is the flattened-leaf typing;
// it used to PROPAGATE the flattener's refusal instead of answering "no", so the
// store was refused although the lane-tiling copy it should have taken is a
// whole-image byte copy. The first row is `Box::<core::io::error::Custom>::new`'s
// own body (`write_via_move` of a struct holding `NonNull<dyn Error>`, two fn
// pointers and a one-byte enum) spelled in a user crate; the others store the
// three wide-leaf kinds through `&mut T`, `*mut T::write` and a `*const T` cast.
// Revert the fix and every row refuses with `aggregate reference nested field is
// a fat pointer ... not scalarizable`.
//
// The tiling copy is checked, not assumed (`image_copy_lane_tiling_covers`): one
// lane type, lanes `0..n` in order at `k * lane_bytes`, and `n * lane_bytes`
// equal to rustc's size of BOTH the source and the destination pointee. Every
// printed value is read back THROUGH the stored object — a vtable dispatch, a
// slice/str length and sum, an fn-pointer call, the enum byte — so a lane copied
// to the wrong offset, a dropped metadata half, or a truncated image prints a
// different number rather than refusing.
//
// THE GATE. The oracle (LLVM, same compiler, same optimization level) runs
// first. The bridge must COMPILE every row — these are exactly the shapes the
// fix admits, so a refusal is a failure here — and match the oracle's stdout and
// exit code. Only `-Copt-level=0` for most rows: at higher levels rustc's
// inliner turns these programs into shapes this backend refuses for unrelated
// reasons (`trait-object unsize source is not a place operand`), which would
// hide the store this test exists to cover.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes
// `no-proof-certs`: with proof certificates on, this backend refuses every
// AArch64 program with `[TCG-PROOF-465]` (the opcode-inventory proof lane, a
// whole-target fact unrelated to this store), which would hide the refusal this
// test exists to catch behind an unrelated one.

use std::path::{Path, PathBuf};
use std::process::Command;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_wide_tiling_{stem}_{}", std::process::id()));
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
            .filter(|line| {
                line.contains("[TCG-") || line.starts_with("error") || line.contains(" - _R")
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

struct Case {
    name: &'static str,
    src: &'static str,
    opts: &'static [&'static str],
    /// A line the LLVM oracle must print, so a fixture that stopped exercising
    /// the store (or an oracle that stopped running it) is caught, not passed.
    oracle_marker: &'static str,
}

const CASES: &[Case] = &[
    Case {
        name: "wide_leaf_tiling_box_custom",
        src: include_str!("bridge_corpus/wide_leaf_tiling_box_custom.rs"),
        opts: &["-Copt-level=0"],
        oracle_marker: "405601",
    },
    Case {
        name: "wide_leaf_tiling_nndyn_mutref",
        src: include_str!("bridge_corpus/wide_leaf_tiling_nndyn_mutref.rs"),
        opts: &["-Copt-level=0", "-Copt-level=1"],
        oracle_marker: "acc 5415296569634",
    },
    Case {
        name: "wide_leaf_tiling_nnslice_rawmut",
        src: include_str!("bridge_corpus/wide_leaf_tiling_nnslice_rawmut.rs"),
        opts: &["-Copt-level=0"],
        oracle_marker: "acc 5496949424234",
    },
    Case {
        name: "wide_leaf_tiling_nnstr_constptr",
        src: include_str!("bridge_corpus/wide_leaf_tiling_nnstr_constptr.rs"),
        opts: &["-Copt-level=0"],
        oracle_marker: "acc 5511022201954",
    },
];

#[test]
fn wide_leaf_lane_tiling_store_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs("wide_leaf_lane_tiling_store_matches_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures = Vec::new();
    for case in CASES {
        for opt in case.opts {
            let name = case.name;
            let dir = workdir(&format!("{name}_o{}", opt.len()));
            let oracle = compile_and_run(&dir, name, case.src, opt, None)
                .unwrap_or_else(|e| panic!("{name} ({opt}): LLVM oracle failed: <<<{e}>>>"));
            assert!(
                oracle.stdout.lines().any(|line| line == case.oracle_marker),
                "{name} ({opt}): the oracle does not print the fixture's known value {:?}, \
                 so this test is measuring something else: {:?}",
                case.oracle_marker,
                oracle.stdout
            );
            match compile_and_run(&dir, name, case.src, opt, Some(&dylib)) {
                Err(e) => failures.push(format!(
                    "{name} ({opt}): trust-cg REFUSED a whole-object store of a wide-leaf \
                     aggregate: <<<{e}>>>"
                )),
                Ok(bridge) if bridge.stdout != oracle.stdout || bridge.code != oracle.code => {
                    failures.push(format!(
                        "{name} ({opt}): differs from LLVM: bridge rc={} {:?}, oracle rc={} {:?}",
                        bridge.code, bridge.stdout, oracle.code, oracle.stdout
                    ))
                }
                Ok(_) => {}
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
