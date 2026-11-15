#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the [TCG-REGALLOC-063] GUARD-PSEUDO lane — a trap/guard
// carrier followed by ordinary code in the SAME machine block.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. AArch64 — alone among the three backends — stamps the
// guard carriers (`TrapBoundsCheckExact`, `TrapDivZeroIfZero`,
// `TrapShiftRangeIfOOB`, `TrapOverflowExact`, `TrapNullIfZero`) `IS_BRANCH |
// IS_TERMINATOR` and NOT `IS_PSEUDO`. TV-3's `MachFunction` view read those
// instance flags through `is_terminator() && !is_conditional_branch()`, so a
// guard read as an UNCONDITIONAL TERMINATOR and every real instruction after it
// in the same block was reported "dead/fused code — the switch-BST
// block-collision signature". A guard expands LATE to `CMP; B.<cc> +2; BRK`,
// which FALLS THROUGH: nothing after it is dead. The x86 view names its
// terminators explicitly (`Jmp | Ret | Ud2`) and asks the OPCODE for
// `is_pseudo`, which is why the x86 default could be flipped to ENFORCE 0-hit
// while aarch64's could not.
//
// Measured on `library/core` at trust-cg `lane/integration-2026-09-14-b` @
// `5e6a978c`: 12 of the 14 `[TCG-REGALLOC-063]` failed roots were this false
// positive, every one an ordinary guarded table index or guarded divide
// (`str::validations::utf8_char_width`, `unicode_data::white_space::lookup`,
// `dec2flt::Lemire::pow10_fast_path`, `flt2dec::dragon::mul_pow10`,
// `int_log10::u128_impl`, the four `escape::*` monomorphizations).
//
// THE TRAP THIS HARNESS EXISTS TO CATCH. This class fails by producing a WRONG
// VALUE silently — a clobbered register or a mis-dispatched block — not by
// crashing. Every fixture therefore checks each guarded result against a
// literal computed offline from Rust semantics AND is differenced against LLVM
// on stdout and exit code at both `-O0` and `-O2`.
//
// THE CONTROL that must stay refused lives in the validator's own unit tests
// (`dataflow_integrity::a64_switch_bst_collision_is_rejected` and
// `a64_trap_guard_pseudo_after_a_real_terminator_is_still_rejected`): a REAL
// `B` followed by foreign code, and a guard carrier appended BEHIND a real `B`,
// both still fail closed. Excluding guards from the TERMINATOR classification
// must never also excuse them from being CODE.
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
// MEASURED: on the UNPATCHED backend both rows of
// `regalloc063_guard_pseudo_then_code` fail closed with
// `[TCG-REGALLOC-063]`; with the lane they COMPILE and MATCH LLVM.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
//
// WHY THE BRIDGE SIDE PASSES `no-proof-certs` (the
// `impostor_std_crate_name_differential.rs` convention). With proof
// certificates ON (the default) this backend currently refuses essentially
// every AArch64 object at proof promotion with `[TCG-PROOF-465] … emitted
// opcode inventory found N uncovered non-pseudo opcode(s)` — a whole-lane fact
// about the AArch64 opcode inventory, unrelated to the guard-pseudo lane. Left
// on, both rows report INCOMPLETE on the patched and the unpatched backend
// alike and pin NOTHING. The knob is applied only to the bridge side (the LLVM
// oracle has no such lane), so the compared values are still the two backends'
// answers to the same program.
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
// It does not relax the gate this file pins: the
// TV-3 raw dataflow-integrity policy that raises `[TCG-REGALLOC-063]` is
// independent of proof emission (pinned by `trust_cg_codegen::compiler`'s
// `raw_dataflow_policy_is_independent_of_proof_emission`).

use std::path::{Path, PathBuf};
use std::process::Command;

/// `-O0` is the un-inlined shape (real by-value enum parameters and returns);
/// `-O2` is the shape after rustc's inliner has folded the constructions into
/// constants and branch-varying joins, which is where a tag-vs-payload mistake
/// usually surfaces.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

/// Of `cases().len() * OPT_LEVELS.len()` rows, at least this many must COMPILE.
const COMPILED_FLOOR: usize = 2;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_ra063_{stem}_{}", std::process::id()));
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
        // Bridge side only: see WHY THE BRIDGE SIDE PASSES `no-proof-certs`.
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
    vec![Case {
        name: "regalloc063_guard_pseudo_then_code",
        what: "a trap/guard carrier followed by ordinary code in the same \
               machine block: a constant-bound table index (the \
               `utf8_char_width` shape), two guards with arithmetic between \
               them, a runtime-LENGTH slice index (the `GuardBoundsCheckDyn` \
               carrier), a guard followed by a CALL (the `Bl`-after-terminator \
               row), a runtime divisor and remainder, a runtime shift amount, \
               and a checked add — each result checked against a literal",
        src: include_str!("bridge_corpus/regalloc063_guard_pseudo_then_code.rs"),
    }]
}

#[test]
fn regalloc063_guard_pseudo_fixtures_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("regalloc063_guard_pseudo_fixtures_match_llvm")
    {
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
    eprintln!("[TCG-REGALLOC-063] guard-pseudo lane rows: {compiled}/{total} COMPILED+MATCHED");
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
