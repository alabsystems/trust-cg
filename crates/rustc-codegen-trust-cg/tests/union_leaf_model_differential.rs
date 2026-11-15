#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the UNION LEAF MODEL — a union whose field is not a scalar,
// an aggregate element stored into a slice, and the whole-value carrier of a
// scalar-ABI union.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. Three refusal classes of a `library/core` census, 19 failed
// roots between them, all of which bottomed out at a UNION whose field has no
// single trust-ir scalar — and one SILENT WRONG READ found while closing them.
//
//   * `Ty::num::imp::fmt::Part<'_>` (10 roots): `parts[i] = MaybeUninit::new(..)`,
//     an AGGREGATE element store into a `&mut [T]` slice. The scalar element path
//     propagated the union's "no scalar ABI carrier" error as if it were the
//     store's.
//   * `Ty::[ascii::ascii_char::AsciiChar; 10_usize]` (4 roots): a TUPLE carrying
//     `core::escape`'s `union { escape_seq: [ascii::Char; N], literal: char }`.
//     The scalarized flattening cannot spell it and the memory layout refused
//     plain tuples.
//   * `whole scalarized aggregate …` (5 roots): a `MaybeUninit<scalar>` read
//     WHOLE out of a by-value parameter. The entry-arg seeding bound the union's
//     per-field projections but not its whole-value carrier.
//
//   * AND the wrong read: `rebind_union_sibling_projections` re-derived every
//     FIELD after `u.f = x` but left the whole-union CARRIER at its construction
//     value, so a whole-value read observed the PRE-WRITE union. Measured on the
//     unpatched backend at `-Copt-level=0`, a 3-line program printed 0xAABBCC00
//     where LLVM printed 0x42. `union_scalar_carrier_byvalue.rs` section (3) is
//     the pin; a mutation that removes only the carrier rebinding reproduces the
//     wrong value.
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
// default) this backend currently refuses every AArch64 object at proof
// promotion with `[TCG-PROOF-465] … emitted opcode inventory found N uncovered
// non-pseudo opcode(s)` — a whole-lane fact about the AArch64 opcode inventory,
// unrelated to the union leaf model. Left on, the first row's bridge compile is
// refused on an AArch64 host and the test panics there, having compared NOTHING.
// The knob is the one `impostor_std_crate_name_differential.rs` passes for the
// same reason, and it is applied only to the bridge side (the LLVM oracle has no
// such lane), so the compared STDOUT and exit code are still the two backends'
// answers to the same program. A compiler that cannot express the knob SKIPS
// loudly (`skip_without_backend_knobs`) rather than passing.

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
    let dir = std::env::temp_dir().join(format!("tcg_unionleaf_{stem}_{}", std::process::id()));
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
        // Bridge side only; see "WHY THE BRIDGE SIDE PASSES `no-proof-certs`".
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
            name: "union_parts_slice_store",
            what: "an AGGREGATE element store into a `&mut [MaybeUninit<Part>]` \
                   slice — `core::num::imp::flt2dec`'s output buffer. A wrong \
                   element stride, a one-lane store of the `Copy(&[u8])` payload, \
                   a tag at the wrong offset, or a from-END index resolved \
                   against the pattern's minimum length each show up as a \
                   different printed part",
            src: include_str!("bridge_corpus/union_parts_slice_store.rs"),
        },
        Case {
            name: "union_array_leaf_aggregate",
            what: "a UNION whose field is an ARRAY (`core::escape`'s \
                   `MaybeEscapedCharacter<N>`), carried through a struct, a \
                   newtype and a TUPLE. Every buffer position is printed, both \
                   union variants are exercised through the same slot, and the \
                   tuple's scalar second element is printed after each buffer",
            src: include_str!("bridge_corpus/union_array_leaf_aggregate.rs"),
        },
        Case {
            name: "union_scalar_carrier_byvalue",
            what: "the WHOLE-VALUE read of a scalar-ABI union — \
                   `MaybeUninit<u32>` / `MaybeUninit<u8>` passed and returned by \
                   value, relayed across two boundaries, written through \
                   `as_mut_ptr`, and (section 3) read WHOLE after a union FIELD \
                   write, which is where the carrier used to go stale",
            src: include_str!("bridge_corpus/union_scalar_carrier_byvalue.rs"),
        },
    ]
}

#[test]
fn union_leaf_model_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs("union_leaf_model_matches_llvm") {
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
