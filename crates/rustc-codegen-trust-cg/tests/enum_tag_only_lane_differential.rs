#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the TAG-ONLY ENUM lane fixtures — an enum every one of whose
// variants carries only ZERO-SIZED fields, so the value is nothing but its tag.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. `rust_ty_to_trust_ir_ty`'s scalar-enum arm used to gate
// on `v.fields.is_empty()` — genuinely FIELDLESS variants. `Result<(),
// fmt::Error>` fails that by HAVING a field, a zero-sized one, and it is the
// return type of every `core::fmt::Write` / `Debug` method: the `library/core`
// census measured 16 failed roots stopping there, all in `core::fmt::builders`.
// The gate is now "every variant's every field is zero-sized"
// (`enum_all_variant_fields_zero_sized`).
//
// THE TRAP THIS HARNESS EXISTS TO CATCH. `Result<(), fmt::Error>` and
// `Option<NonZeroU8>` have an IDENTICAL repr signature — `size 1`, `align 1`,
// `BackendRepr::Scalar(Primitive::Int(I8, unsigned))` — and OPPOSITE semantics:
// the second is `TagEncoding::Niche`, where the scalar IS THE PAYLOAD. A
// repr-only widening would compile `Some(x)` to a tag, and a census that counts
// failed roots would score that miscompile as PROGRESS. `enum_niche_payload_
// control.rs` is the falsifier and it is NOT optional: it must run, and it must
// agree with LLVM on every payload value.
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
// `0cb693917a`, trust-cg `lane/integration-2026-09-14` @ `07e37c28` plus this
// lane): 9 of 12 rows COMPILE and MATCH. The three INCOMPLETE rows are
// `enum_niche_payload_field_control` at both levels — the trap control, which
// must NOT be admitted — and `enum_uninhabited_residual_try` at `-O2`, which now
// stops in the unrelated `memory-backed slice reborrow` class
// (`core::array::Guard<u8>::drop`), tracked separately. On the UNPATCHED backend
// the same harness scores 4 of 12.
//
// RE-MEASURED 2026-09-21 (backend built from this tree with the atpkg Trust
// pack `321aaeda7 2026-09-17`; identical on the 2026-09-14 stage1 with a dylib
// built from the same source): **10 of 12**. The `-O2` reborrow refusal above
// had since been closed by another lane, and what was left behind it was NOT a
// named refusal: `Guard<u8>::drop` lowered and CALLED `core::ptr::drop_glue::
// <[u8]>` — rustc's EMPTY drop glue, `Shim(DropGlue(_, None))`, which has no
// body and no symbol — and the link died on an undefined symbol, which this
// harness rightly reports as a crash. The direct-call lowering now folds an
// empty-drop-glue call to its successor branch, exactly as
// `rustc_codegen_ssa` does, and the row compiles and matches at both levels.
// The floor is raised to 10 so that a regression of that fold fails here.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
//
// WHY THE BRIDGE SIDE PASSES `no-proof-certs`. With proof certificates ON (the
// default) this backend currently refuses essentially every AArch64 object at
// proof promotion — `[TCG-PROOF-465] … emitted opcode inventory found N uncovered
// non-pseudo opcode(s)` — a whole-lane fact about the AArch64 opcode inventory,
// unrelated to tag-only enum lowering. Left on, every row that LOWERS would report
// INCOMPLETE on that tag and the harness would pin NOTHING. The knob is the one
// `impostor_std_crate_name_differential.rs` and `m142_bridge_bookkeeping_aarch64.rs`
// pass, applied only to the bridge side (the LLVM oracle has no such lane), so the
// compared values are still the two backends' answers to the same program.
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
// So a LOWERING refusal (the
// `enum_niche_payload_field_control` trap control's among them) still fails closed
// under its own `[TCG-...]` tag, every row that compiles is still value-checked
// against LLVM, and `COMPILED_FLOOR` is not moved.

use std::path::{Path, PathBuf};
use std::process::Command;

/// `-O0` is the un-inlined shape (real by-value enum parameters and returns);
/// `-O2` is the shape after rustc's inliner has folded the constructions into
/// constants and branch-varying joins, which is where a tag-vs-payload mistake
/// usually surfaces.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

/// Of `cases().len() * OPT_LEVELS.len()` rows, at least this many must COMPILE.
const COMPILED_FLOOR: usize = 10;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_tagonly_{stem}_{}", std::process::id()));
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
    // "C" fn main`, which keeps them off the unrelated refusal classes a full
    // `std` program drags in. rustc links a `no_std` binary with
    // `-nodefaultlibs`, so libSystem — which carries the C runtime that calls
    // `main` — has to be asked for explicitly. Passed to BOTH the LLVM-oracle
    // and the trust-cg compile, so the differential stays apples-to-apples.
    cmd.arg("-Clink-arg=-lSystem");
    cmd.arg(opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        // Bridge side only — see "WHY THE BRIDGE SIDE PASSES `no-proof-certs`".
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
            name: "enum_tag_only_result_fmt_error",
            what: "`Result<(), core::fmt::Error>` — both payloads zero-sized, one \
                   Direct `u8` tag: construct + match, `?`, by-value across a \
                   call boundary, `mem::discriminant`, and a branch-varying value \
                   through a join",
            src: include_str!("bridge_corpus/enum_tag_only_result_fmt_error.rs"),
        },
        Case {
            name: "enum_tag_only_option_and_repr",
            what: "`Option<()>` / `Option<PhantomData<u64>>` (the predicate must \
                   ask the INSTANTIATED field type) and a `#[repr(i8)]` enum with \
                   NEGATIVE explicit discriminants over three zero-sized payload \
                   shapes (width and signedness from rustc's layout)",
            src: include_str!("bridge_corpus/enum_tag_only_option_and_repr.rs"),
        },
        Case {
            name: "enum_niche_payload_control",
            what: "THE TRAP CONTROL — `Option<NonZeroU8>` has this lane's exact \
                   repr signature and is `TagEncoding::Niche`, where the scalar IS \
                   THE PAYLOAD. Every payload value is checked against LLVM, so a \
                   predicate that admits it fails here rather than reading as \
                   progress in the census. BY-VALUE half: this one COMPILES on \
                   both the patched and the unpatched backend, so it is a LIVE \
                   falsifier rather than a row that passes by refusing",
            src: include_str!("bridge_corpus/enum_niche_payload_control.rs"),
        },
        Case {
            name: "enum_niche_payload_field_control",
            what: "THE TRAP CONTROL in the STRUCT-FIELD position the widening \
                   actually opens up — `Option<NonZeroU8>` as a field of a \
                   memory-candidate aggregate. Fails closed today (an honest \
                   INCOMPLETE); what it forbids is COMPILING to a 0/1 tag where \
                   the payload belongs",
            src: include_str!("bridge_corpus/enum_niche_payload_field_control.rs"),
        },
        Case {
            name: "enum_uninhabited_residual_try",
            what: "`?` whose RESIDUAL TYPE IS UNINHABITED — `array::from_fn` / \
                   `Iterator::fold` over `NeverShortCircuit`, whose \
                   `Try::Residual` is an EMPTY enum, so the `from_residual` call \
                   and the `discriminant` of its residual are provably dead. \
                   Refused at `-O2` only before this lane (an opt-level-dependent \
                   refusal); its `-O2` row now stops in the unrelated \
                   memory-backed-slice-reborrow class",
            src: include_str!("bridge_corpus/enum_uninhabited_residual_try.rs"),
        },
        Case {
            name: "enum_infallible_err_payload_control",
            what: "SOUNDNESS-EDGE CONTROL — `Result<Infallible, u64>`: a \
                   payload-bearing enum with an UNINHABITED sibling, whose value \
                   IS its payload, not a tag. `g(Err(7))` must exit 7",
            src: include_str!("bridge_corpus/enum_infallible_err_payload_control.rs"),
        },
    ]
}

#[test]
fn enum_tag_only_lane_fixtures_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("enum_tag_only_lane_fixtures_match_llvm") {
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
    eprintln!("tag-only enum lane rows: {compiled}/{total} COMPILED+MATCHED");
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
