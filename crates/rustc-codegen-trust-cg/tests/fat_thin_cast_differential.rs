#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the FAT -> THIN pointer CAST SEAM and the `repr(transparent)`
// fat-pointer CARRIER (`NonNull<[T]>` / `NonNull<str>`) that reaches it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. Each row's header comment carries the measured `library/core`
// refusal class it closes and the exact wrong-lowering it would catch. Every
// printed value is either an ELEMENT read through the narrowed thin pointer
// (`.add(k)` reaching a LATER element, so a wrong data lane or stride is a wrong
// number) or a LENGTH read from the carrier's metadata half — so a dropped or
// reinvented metadata lane changes stdout rather than merely refusing.
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
// default) the bridge currently refuses every AArch64 object at proof promotion
// (`[TCG-PROOF-465] ... emitted opcode inventory found N uncovered non-pseudo
// opcode(s)`) -- a whole-lane fact about the opcode inventory, unrelated to the
// fat -> thin seam. Left on, every row would stop at that refusal after lowering
// succeeded and pin NOTHING. As in `impostor_std_crate_name_differential.rs`, the
// knob is applied only to the bridge side (the LLVM oracle has no such lane), so
// the compared values are still the two backends' answers to the same program,
// and a lowering refusal still fails the test.

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
    let dir = std::env::temp_dir().join(format!("tcg_fatthin_{stem}_{}", std::process::id()));
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
            name: "fix_p_fat_thin_ptr_cast",
            what: "a FAT -> THIN pointer cast (`*const [T] as *const T`, \
                   `*mut str as *mut u8`, `NonNull::<[T]>::cast::<T>()`) and the \
                   `repr(transparent)` CARRIER it narrows from. Before the seam the \
                   carrier was mapped to a single thin `Ptr` — the metadata was \
                   never modeled, which is the silent-truncation channel itself — so \
                   the carrier's LENGTH half was unreachable (`NonNull::<[u8]>::len` \
                   refused: \"slice pointer metadata before known array length\"), \
                   and 11 `core` roots stopped at `NonNull::<[T]>::as_ptr`",
            src: include_str!("bridge_corpus/fix_p_fat_thin_ptr_cast.rs"),
        },
        Case {
            name: "fix_p_slice_for_loop_carrier",
            what: "`for b in s { }` over a `&[u8]` at `-O2`. A REGRESSION pin: it \
                   matches on BOTH sides of this change, because the shape compiles \
                   today. It is here because rustc inlines `slice::Iter::new` at \
                   `-O2`, and that body builds a `NonNull<[T]>` carrier and narrows \
                   it with `.cast()` — so modeling the carrier as two lanes WITHOUT \
                   the fat -> thin seam loses codegen for the most ordinary loop in \
                   Rust (measured: `-O0` fine, `-O2` fails closed)",
            src: include_str!("bridge_corpus/fix_p_slice_for_loop_carrier.rs"),
        },
    ]
}

#[test]
fn fat_thin_cast_seam_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs("fat_thin_cast_seam_matches_llvm") {
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
