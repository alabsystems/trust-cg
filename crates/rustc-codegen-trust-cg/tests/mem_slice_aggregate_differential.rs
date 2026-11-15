#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the MEMORY / SLICE / AGGREGATE lane — a fat pointer inside a
// UNION field, a fat->fat `PtrToPtr` cast feeding a slice reborrow, and a flat
// aggregate with a trailing zero-sized field moved across the scalarized <->
// memory boundary.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. Each row's header comment carries the measured `library/core`
// refusal class it closes and the exact wrong-lowering it would catch. Every
// printed value is built from a LENGTH (or from a scalar field placed AFTER a fat
// one), so a dropped metadata lane, a one-lane store or a shifted later field
// changes stdout rather than merely refusing.
//
// Each program below is compiled BY THE BRIDGE and BY LLVM at the SAME
// optimization level, run, and compared. A dropped vtable lane, a truncated
// fat pointer, a lane written at the wrong offset, or a torn (data-without-
// metadata) read shows up as different STDOUT or a different exit code.
//
// WHY STDOUT AND EXIT CODE ONLY: panic text legitimately differs between the
// two backends (panic machinery, formatting of the location), so the
// comparison is deliberately restricted to the values a correct program
// prints and the status it exits with.
//
// HOST-NATIVE: no `--target` is passed, so this runs on whatever host builds
// the crate (unlike the x86-pinned differentials, which need an x86 host and
// its rust-std). A single codegen unit keeps every function in one object, as
// the other differentials do.
//
// WHY THE BRIDGE SIDE PASSES `no-proof-certs`. With proof certificates ON (the
// default), this backend currently refuses essentially every AArch64 object at
// proof promotion with `[TCG-PROOF-465] ... emitted opcode inventory found N
// uncovered non-pseudo opcode(s)`. That is a whole-lane fact about the AArch64
// opcode inventory and has nothing to do with lane placement. Left on, every row
// would report a refusal after lowering had already succeeded, and the test would
// pin NOTHING. The knob is the one `impostor_std_crate_name_differential.rs` and
// `m142_bridge_bookkeeping_aarch64.rs` pass. It is applied only to the bridge side
// (the LLVM oracle has no such lane), so the compared values are still the two
// backends' answers to the same program. A fail-closed LOWERING refusal is
// unaffected and still fails the row.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Every case is run at BOTH of these. `-O0` exercises the un-inlined shape
/// (real `&dyn` parameters, real aggregate constructions); `-O2` exercises the
/// shape after rustc's inliner has folded the aggregates and re-materialized
/// the fat pointers, which is where a lane-offset mistake usually surfaces.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_dynleaf_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code + stdout. `Err` carries the compiler's stderr tail: the bridge
/// FAILS CLOSED on a shape it cannot lower, which is a legitimate outcome for
/// the backend in general but a test failure here, since these programs are
/// exactly the shapes this lane added.
fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<Run, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

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
            .rev()
            .take(10)
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
    what: &'static str,
    src: &'static str,
}

fn corpus() -> Vec<Case> {
    vec![
        Case {
            name: "fix_mem_union_fat_leaf",
            what: "a `{data, metadata}` FAT POINTER inside a UNION field — the \
                   `MaybeUninit<T>` shape whose slot is opaque bytes and whose \
                   active field is written at offset 0. `union_memory_layout` \
                   refused any such union outright (19 `core` roots, every one \
                   `MaybeUninit<core::num::fmt::Part<'_>>`); the union slot has no \
                   per-field leaf model at all, so that gate could only turn a \
                   correct emission or a later precise refusal into an early \
                   blanket one",
            src: include_str!("bridge_corpus/fix_mem_union_fat_leaf.rs"),
        },
        Case {
            name: "fix_mem_slice_ptrcast_reborrow",
            what: "a fat -> fat `PtrToPtr` CAST feeding a slice REBORROW \
                   (`&*(s as *const [U])`). The lowering arm existed; the \
                   memory-backing classifier's cast list did not name `PtrToPtr`, \
                   so the destination got no slot, the cast bound it as a single \
                   SCALAR (the data half, length dropped) and the reborrow failed \
                   closed on it — 6 `core` roots",
            src: include_str!("bridge_corpus/fix_mem_slice_ptrcast_reborrow.rs"),
        },
        Case {
            name: "fix_mem_trailing_zst_flat_copy",
            what: "a flat scalar-leaf aggregate with a TRAILING zero-sized field \
                   (`slice::Iter<'a, T>`'s `PhantomData`) moved whole across the \
                   scalarized <-> memory boundary. A REGRESSION pin: it matches on \
                   both sides of the fix (the 3 `core` roots it derives from are \
                   only reachable when `core` is compiled as a library), and it \
                   keeps the trailing-ZST plan from being narrowed again",
            src: include_str!("bridge_corpus/fix_mem_trailing_zst_flat_copy.rs"),
        },
    ]
}

#[test]
fn memory_slice_aggregate_lane_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs("memory_slice_aggregate_lane_matches_llvm") {
        return;
    }
    let dylib = ensure_dylib_built();
    for case in corpus() {
        for opt in OPT_LEVELS {
            let dir = workdir(&format!("{}_{}", case.name, opt.len()));
            let oracle = compile_and_run(&dir, case.name, case.src, opt, None)
                .unwrap_or_else(|e| panic!("{} ({opt}): LLVM oracle failed: <<<{e}>>>", case.name));
            let bridge = compile_and_run(&dir, case.name, case.src, opt, Some(&dylib))
                .unwrap_or_else(|e| {
                    panic!(
                        "{} ({opt}): trust-cg REFUSED or failed to compile {}: <<<{e}>>>",
                        case.name, case.what
                    )
                });
            assert_eq!(
                bridge.stdout, oracle.stdout,
                "{} ({opt}): STDOUT differs from LLVM for {}",
                case.name, case.what
            );
            assert_eq!(
                bridge.code, oracle.code,
                "{} ({opt}): exit code differs from LLVM for {}",
                case.name, case.what
            );
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
}
