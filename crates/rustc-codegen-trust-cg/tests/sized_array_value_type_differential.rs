#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the SIZED ARRAY value-type lane — `[T; N]` where the length
// is part of the type.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. `rust_ty_to_trust_ir_ty` maps no sized array except
// `[T; 0]`, and `memory_aggregate_reference_pointee_lane_ty` — the byte-offset
// fallback that types an aggregate pointee the scalar-field flattening cannot
// represent — enumerated the array shapes it would serve BY SHAPE (enum-leaf
// element, niche-enum-leaf element, nested-array element) and covered bare
// TUPLE pointees not at all. Those three shapes are instances of one property,
// "the flattening failed", and enumerating them left the fourth instance
// refusing for no reason: `&[(u16, [u16; 3]); N]` and `&(u16, [u16; 3])` — the
// `core::unicode::unicode_data::conversions` multi-character case-mapping table
// and the element reference `get_unchecked` hands back from it. The
// `library/core` census measured 10 roots stopping there — and after eleven
// lanes merged (`…-d` @ `fa9ee589`, 143 roots) all ten were still live, so none
// of this was swept by a neighbour.
//
// DO NOT RE-NARROW AN ARM TO A SHAPE LIST, and do not drop a decline's REASON:
// a sibling lane gave every exit of this function a reason string, and the
// 45-root UNSIZED-DST diagnosis (`Ty::[u<n>]` 21 + `Ty::[i<n>]` 9 + `IndexRange`
// 15) is read off those strings. The arms here are gated on `ty::Array` /
// `ty::Tuple`, which a DST pointee reaches neither of, so that cluster's counts
// and reasons are byte-identical across this change.
//
// THE TRAP THIS HARNESS EXISTS TO CATCH. An array's failure mode is a WRONG
// ELEMENT, not a refusal: a stride taken from the register width instead of
// `size_of::<T>()`, or a tuple whose rustc layout REORDERED its fields while the
// lowering assumed declaration order. Both produce a plausible number that a
// folded checksum can absorb. So every fixture here prints EVERY element it
// reads to stdout, and the harness compares stdout byte-for-byte with LLVM's in
// addition to the exit code.
//
// THE GATE (the `fat_pointer_lane_differential.rs` doctrine):
//   * bridge output differs from LLVM        -> HARD FAIL (a miscompile).
//   * bridge FAILS CLOSED with a named
//     `[TCG-...]` diagnostic                 -> INCOMPLETE row, reported.
//   * bridge crashes / refuses with no named
//     diagnostic                             -> HARD FAIL.
//   * fewer than `COMPILED_FLOOR` rows
//     COMPILE                                -> HARD FAIL.
//
// NEVER lower the floor to make the gate pass — a newly-refusing fixture is a
// coverage regression to fix.
//
// MEASURED (backend built from this tree against the 2026-09-14 stage1
// `0cb693917a`, trust-cg `lane/integration-2026-09-14-d` @ `fa9ee589` plus this
// lane; identical scores on `…-b` @ `5e6a978c`): 8 of 8 rows COMPILE and MATCH.
// On the UNPATCHED backend the same
// harness scores 4 of 8 — `sized_array_tuple_element_table` and
// `sized_array_large_table_cost` are both INCOMPLETE at BOTH opt levels with
// `Ty::(u16, [u16; 3_usize])` / `Ty::[u16; 3_usize]`, and they are the lane's
// live falsifiers. `sized_array_escape_union_buf` and `sized_array_controls`
// compile on both backends and are live controls that must keep matching —
// every shape in them is one the lane must NOT move.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
//
// WHY THE BRIDGE SIDE PASSES `no-proof-certs`. With proof certificates ON (the
// default) this backend currently refuses essentially every AArch64 object at
// proof promotion with `[TCG-PROOF-465] … emitted opcode inventory found N
// uncovered non-pseudo opcode(s)` — a whole-lane fact about the AArch64 opcode
// inventory, unrelated to array stride or tuple field order. Left on, every row
// reports INCOMPLETE on the patched and the unpatched backend alike, no stdout
// or exit code is ever compared, and the test pins NOTHING. The knob is the one
// `impostor_std_crate_name_differential.rs` and `m142_bridge_bookkeeping_aarch64.rs`
// pass, and it is applied only to the bridge side (the LLVM oracle has no such
// lane), so the compared values are still the two backends' answers to the same
// program.
// What the knob changes (the bridge sets `emit_proofs = false`): no proof
// certificate is generated or promoted and the bridge re-checks no proof bundle;
// exception tables are not refused as unproved; the verifier is not pre-warmed;
// the non-vacuity post-check on the raw TV-3 dataflow observation is skipped (the
// gate itself still enforces); an `artifact-cache-dir` cache, if set, uses the
// unchecked partition; and AArch64 publication runs at the compatibility policy
// instead of proof grade (`with_proof_grade_aarch64_publication_if`), so
// decode-allowlisted words are counted rather than refused, the final-layout
// cross-check does not bind encoded edges to the recorded CFG, and `TCG_*`
// downgrades of the post-RA and decode nets and late-layout controls are honored
// rather than refused (with none set, those nets enforce). The -O1+ inliner
// may also splice inline-only (`AvailableExternally`) bodies that no
// authenticated import defines, which a proof compile withholds
// (`InlineOnlyAdmission::for_proof_claim`); the bridge emits no such body, so
// that changes nothing here. MIR lowering is unchanged.
// So a genuine lowering refusal is still a named INCOMPLETE, a crash is still a
// HARD FAIL, and `COMPILED_FLOOR` is unchanged.

use std::path::{Path, PathBuf};
use std::process::Command;

/// `-O0` is the un-inlined shape (real by-value arrays and real reference
/// pointees crossing call boundaries); `-O2` is the shape after rustc's inliner
/// has folded constructions into constants and branch-varying joins, which is
/// where a stride or field-order mistake usually surfaces.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

/// Of `cases().len() * OPT_LEVELS.len()` rows, at least this many must COMPILE.
const COMPILED_FLOOR: usize = 8;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_sizedarr_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code + stdout. `Err` carries the compiler's stderr tail.
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
    // These fixtures are `#![no_std] #![no_main]` with a `#[no_mangle] extern
    // "C" fn main`. rustc links a `no_std` binary with `-nodefaultlibs`, so
    // libSystem — which carries the C runtime that calls `main`, and the `write`
    // these fixtures print through — has to be asked for explicitly. Passed to
    // BOTH the LLVM-oracle and the trust-cg compile, so the differential stays
    // apples-to-apples.
    cmd.arg("-Clink-arg=-lSystem");
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
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
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

/// The bridge's own named refusal tag, if this stderr is a fail-closed refusal
/// rather than a crash. An ICE, a panic, or a refusal with no `[TCG-...]` tag is
/// NOT an honest INCOMPLETE and must fail the gate.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

struct Case {
    name: &'static str,
    what: &'static str,
    src: &'static str,
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "sized_array_tuple_element_table",
            what: "THE LANE'S FALSIFIER — `&[(u16, [u16; 3]); N]` (the \
                   `core::unicode::unicode_data::conversions` table shape) read \
                   through the slice, copied out by value, and round-tripped \
                   through an `#[inline(never)]` callee. Every key and every \
                   array element is printed, so a wrong stride or a reordered \
                   tuple field diverges from LLVM rather than folding away. \
                   INCOMPLETE on the unpatched backend at both opt levels",
            src: include_str!("bridge_corpus/sized_array_tuple_element_table.rs"),
        },
        Case {
            name: "sized_array_escape_union_buf",
            what: "the `core::escape` shape — `([u8; 10], Range<u8>)` returned \
                   by value, stored in a struct beside a scalar range, indexed \
                   element by element, and passed by value into a callee; plus \
                   THE FIELD-SHIFT class (an array field with a SCALAR FIELD \
                   AFTER it, where a mis-sized array reads `tail` from inside \
                   the buffer). Compiles on both backends — a live control that \
                   must keep matching",
            src: include_str!("bridge_corpus/sized_array_escape_union_buf.rs"),
        },
        Case {
            name: "sized_array_controls",
            what: "THE CONTROLS — `[T; 0]` keeps its `Unit` mapping and its \
                   unsize keeps length 0; a thin `&[u16; 6]` reference to a \
                   SCALAR-element array keeps its flattened representation \
                   (the widened arm must return `Ok(None)` for it); a `&[u16]` \
                   SLICE (a different family, another lane's) is untouched; and \
                   a `&[[u8; 4]; 3]` nested-array pointee — one of the three \
                   shape triggers the widening generalizes — keeps working",
            src: include_str!("bridge_corpus/sized_array_controls.rs"),
        },
        Case {
            name: "sized_array_large_table_cost",
            what: "THE SIZE-CLIFF control — an 8192-entry `[(u16, [u16; 3]); N]` \
                   table (64 KiB, two orders of magnitude above anything \
                   `library/core` holds) probed at 8 positions including the \
                   last. The widened arm routes it onto the O(1) \
                   `Ty::Array(lane, n)` memory-slot spelling rather than the \
                   O(N) one-leaf-per-element flattening, so no new size bound is \
                   needed; this row is the measurement that says so, and it is a \
                   VALUE check as well as a cost one",
            src: include_str!("bridge_corpus/sized_array_large_table_cost.rs"),
        },
    ]
}

#[test]
fn sized_array_value_type_fixtures_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("sized_array_value_type_fixtures_match_llvm") {
        return;
    }
    let dylib = ensure_dylib_built();
    let mut compiled = 0usize;
    let mut incomplete: Vec<String> = Vec::new();
    for case in cases() {
        for opt in OPT_LEVELS {
            let dir = workdir(&format!("{}_{}", case.name, opt.len()));
            let oracle = compile_and_run(&dir, case.name, case.src, opt, None)
                .unwrap_or_else(|e| panic!("{} ({opt}): LLVM oracle failed: <<<{e}>>>", case.name));
            match compile_and_run(&dir, case.name, case.src, opt, Some(&dylib)) {
                Ok(bridge) => {
                    compiled += 1;
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
                }
                Err(stderr) => {
                    let tag = named_refusal(&stderr).unwrap_or_else(|| {
                        panic!(
                            "{} ({opt}): trust-cg failed WITHOUT a named [TCG-...] \
                             refusal, which is a crash rather than a fail-closed \
                             outcome: <<<{stderr}>>>",
                            case.name
                        )
                    });
                    incomplete.push(format!("{} ({opt}): {tag}", case.name));
                }
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    let total = cases().len() * OPT_LEVELS.len();
    eprintln!("sized-array value-type lane rows: {compiled}/{total} COMPILED+MATCHED");
    for row in &incomplete {
        eprintln!("  INCOMPLETE {row}");
    }
    assert!(
        compiled >= COMPILED_FLOOR,
        "only {compiled}/{total} rows compiled, below the committed floor of \
         {COMPILED_FLOOR}. A newly-refusing fixture is a coverage regression — \
         fix it rather than lowering the floor. Incomplete rows: {incomplete:?}"
    );
}
