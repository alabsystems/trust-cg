#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a loop whose body branches on a SHORT-CIRCUIT CONDITION —
// the end-to-end pin for `vc_short_circuit_shape` (`src/lib.rs`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. `(a < b && !flag) || (a > b && flag)` is ONE source
// branch, but MIR lowers it to a CHAIN of bool `SwitchInt`s converging on two
// blocks. The back-edge walker's arm recognizer sees the second link as "an arm
// ending in a switch with two in-loop targets" and refuses — correctly, because
// it is not an arm — and the loop-completeness check then fails closed on the
// whole function. `core::str::pattern::TwoWaySearcher::maximal_suffix` is
// exactly that shape and was the LAST failed root of `library/core` in the
// trust-ir-cg census; `vc_short_circuit_shape` collapses the chain to a single
// diamond (or, when only one exit reaches the latch, a compound guard) and is
// what closed it. Until this file, nothing in this crate's own suite exercised
// that recognizer end to end: the census does, but the census is not a test
// that anything runs on a push.
//
// THE PIN. The fixture (`bridge_corpus/short_circuit_loop_condition.rs`) is
// `maximal_suffix` verbatim in shape, called over inputs that drive all three
// branches under both `flag` polarities. It must COMPILE through the bridge at
// BOTH opt levels and match LLVM's stdout and exit code byte-for-byte. The floor
// is the WHOLE row set, not a fraction of it, because the failure mode this pin
// exists for is a REFUSAL: with the recognizer disabled the function does not
// compile at all, and a floor that tolerated one refusing row would tolerate
// exactly the regression it was written against.
//
// FALSIFIED (2026-09-21, backend built from this tree with the atpkg Trust pack
// `321aaeda7 2026-09-17`): with `vc_short_circuit_shape` mutated to return
// `Ok(None)` unconditionally, the `-O0` row REFUSES on `maximal_suffix` with
// `[TCG-SSA-071] … semantic back-edge threading VC did not refine: diamond arm
// bb7 ends in a SwitchInt with 2 in-loop target(s)` — the arm walker's refusal
// of the second link, verbatim — and this test fails on the floor. The `-O2`
// row still compiles and matches under that mutant (the inliner and SimplifyCfg
// reshape the chain into something the plain diamond lane already handles), so
// `-O0` is THE recognizer pin and `-O2` is the value control that keeps the
// optimized shape honest. Restored, both rows compile and match LLVM (exit
// code 38, 33 printed values).
//
// THE TRAP THIS HARNESS EXISTS TO CATCH, beyond the refusal: every branch of
// the loop mutates a DIFFERENT subset of the four loop-carried locals, so a
// wrong reaching condition, a link hoisted out of its guard, or a clobbered
// link temp yields a plausible `(left, period)` pair rather than a trap. Every
// result is printed and compared, not folded into a checksum alone.
//
// THE GATE (the `fat_pointer_lane_differential.rs` doctrine):
//   * bridge output differs from LLVM        -> HARD FAIL (a miscompile).
//   * bridge FAILS CLOSED with a named
//     `[TCG-...]` diagnostic                 -> INCOMPLETE row, reported —
//                                              and, because the floor is the
//                                              whole row set, a FAIL.
//   * bridge crashes / refuses with no named
//     diagnostic                             -> HARD FAIL.
//
// NEVER lower the floor to make the gate pass — a newly-refusing row here IS
// the regression this file was written to catch.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
//
// WHY THE BRIDGE SIDE PASSES `no-proof-certs` (the
// `impostor_std_crate_name_differential.rs` convention). With proof certificates
// ON (the default) this backend currently refuses essentially every AArch64
// object at proof promotion with `[TCG-PROOF-465] … emitted opcode inventory
// found N uncovered non-pseudo opcode(s)`. That is a whole-lane fact about the
// AArch64 opcode inventory and has nothing to do with the short-circuit
// recognizer. With it left on, both rows report INCOMPLETE on the patched and the
// mutated backend alike, and the test pins NOTHING.
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
// The `[TCG-SSA-071]` refusal this pin keys on is raised during MIR
// lowering, before promotion, so a disabled recognizer still refuses the `-O0`
// row. The knob goes to the bridge side only (the LLVM oracle has no such lane),
// so the compared values are still the two backends' answers to the same program,
// and the floor is still the whole row set.

use std::path::{Path, PathBuf};
use std::process::Command;

/// `-O0` is the un-inlined shape — `arr.get(..)` is a real call on the loop
/// path and the condition chain is exactly as MIR built it; `-O2` is the shape
/// after rustc's inliner and SimplifyCfg have reshaped the chain.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

/// EVERY row must compile: `cases().len() * OPT_LEVELS.len()`. See the module
/// doc for why this is not a fraction.
fn compiled_floor() -> usize {
    cases().len() * OPT_LEVELS.len()
}

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_shortcirc_{stem}_{}", std::process::id()));
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
    // The fixture is `#![no_std] #![no_main]` with a `#[no_mangle] extern "C"
    // fn main`. rustc links a `no_std` binary with `-nodefaultlibs`, so
    // libSystem — the C runtime that calls `main`, and the `write` the fixture
    // prints through — has to be asked for explicitly. Passed to BOTH the
    // LLVM-oracle and the trust-cg compile, so the differential stays
    // apples-to-apples.
    cmd.arg("-Clink-arg=-lSystem");
    cmd.arg(opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        // Bridge side ONLY: see the module doc's `no-proof-certs` paragraph.
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
    /// Every line the fixture prints is one `maximal_suffix` result component
    /// (or the final checksum); a run that prints fewer lines than this took a
    /// wrong exit from the loop and must not be mistaken for a match by an
    /// accidentally-equal exit code.
    expected_lines: usize,
}

fn cases() -> Vec<Case> {
    vec![Case {
        name: "short_circuit_loop_condition",
        what: "THE PIN — `TwoWaySearcher::maximal_suffix`'s loop: \
               `while let Some(&a) = arr.get(i) { let b = arr[j]; \
               if (a < b && !flag) || (a > b && flag) { .. } else if a == b \
               { .. } else { .. } }`, over 8 inputs x both `flag` polarities. \
               REFUSES ([TCG-SSA-071]) on a backend whose short-circuit \
               recognizer is disabled",
        src: include_str!("bridge_corpus/short_circuit_loop_condition.rs"),
        // 8 inputs x 2 polarities x (left, period) + the checksum line.
        expected_lines: 8 * 2 * 2 + 1,
    }]
}

#[test]
fn short_circuit_loop_condition_matches_llvm_at_every_opt_level() {
    if toolchain_support::skip_without_backend_knobs(
        "short_circuit_loop_condition_matches_llvm_at_every_opt_level",
    ) {
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
            // The ORACLE must itself exercise the loop, or a matching empty
            // output would pass a fixture that never ran its body.
            assert_eq!(
                oracle.stdout.lines().count(),
                case.expected_lines,
                "{} ({opt}): the LLVM oracle printed an unexpected number of lines; \
                 the fixture and `expected_lines` disagree: <<<{}>>>",
                case.name,
                oracle.stdout
            );
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
    eprintln!("short-circuit loop-condition rows: {compiled}/{total} COMPILED+MATCHED");
    for row in &incomplete {
        eprintln!("  INCOMPLETE {row}");
    }
    let floor = compiled_floor();
    assert!(
        compiled >= floor,
        "only {compiled}/{total} rows compiled, below the committed floor of \
         {floor} (every row). A refusing row here is the regression this pin \
         exists to catch — `vc_short_circuit_shape` no longer collapses the \
         `&&`/`||` chain — fix it rather than lowering the floor. Incomplete \
         rows: {incomplete:?}"
    );
}
