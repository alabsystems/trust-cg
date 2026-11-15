#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: REFERENCE-RETURNING callees over non-primitive referents —
// the host-native runner for the `bridge_corpus/fix_o_*referent*` rows.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. Without a real address, `&mut x` reaches a reference-returning
// callee as a materialized TEMP the caller reloads after the call, so a `&mut` the
// callee derives from it addresses a DEAD temp and a later `*r = v` is silently
// dropped. 4c961dcbb cured that with the ADDRESS: the reference-escaping arm of
// `compute_scalar_cell_locals` cells every referent `cellable_reference_referent_ty`
// admits, not only `Int/Uint/Float/Bool/Char`. Main's corpus pinned it with ONE
// row, `fix_refret_cell_nonprimitive.rs` — an integer newtype through a LOCAL
// callee — and that row cannot see the regression that matters most: with the
// narrowing restored, a LOCAL callee is refused by name
// (`direct_scalar_ref_select_return`), which the x86 corpus harness reports as a
// safe fail-closed.
//
// A NON-LOCAL callee has no such refusal. Measured on trust-cg main `ad7ee9c4e`
// (aarch64-apple-darwin, driver `0cb693917`) with the primitive-only narrowing
// restored: `fix_o_identity_nonlocal_callee` COMPILES at -O0 and prints the stale
// `seen=5`, exit 1, against LLVM's `seen=9`, exit 0. That row is the SOUNDNESS
// pin here; the other two VALUE rows are capability pins for referent kinds no
// other row covers (a pointer-valued `NonNull` whose callee returns the address it
// HOLDS — `IterMut::next` — and a raw `*mut u64` re-aimed through the returned
// `&mut`), both refused by name under the same mutation.
//
// THE GATE.
//   * VALUE row: must COMPILE and equal LLVM (stdout AND exit code) at every opt
//     level. A refusal is a regression of a claimed surface, not an INCOMPLETE.
//   * PROBE row: equal LLVM, or fail closed with a named `[TCG-...]` refusal. A
//     wrong value is a HARD FAIL; so is a crash or an unnamed refusal. Today both
//     probes refuse by name (`[TCG-SCALAR-CELL-LAYOUT]` for the `Box` referent;
//     "borrowed scalar reference used without deref" inside
//     `[TCG-MIR-UNSUPPORTED]` for the `&u32` partial chain), which is exactly what
//     their headers accept.
// The oracle is asserted FIRST on every row, against the value the fixture's own
// header states, so a changed fixture cannot pass vacuously.
//
// WHY THE BRIDGE SIDE PASSES `no-proof-certs` — the
// `impostor_std_crate_name_differential.rs` doctrine, re-measured here: with proof
// certificates ON (the default) this backend refuses EVERY program on
// aarch64-apple-darwin with `[TCG-PROOF-465] … emitted opcode inventory found …
// uncovered non-pseudo opcode(s)`, starting at `std::rt::lang_start` — a
// whole-lane fact about the AArch64 opcode inventory, unrelated to reference
// returns. Left on, every row here would be refused on the patched and the
// narrowed backend alike and pin NOTHING. The knob is applied only to the bridge
// side (the LLVM oracle has no such lane), so the compared values are still the
// two backends' answers to the same program. The CONTROL row of this family
// (`fix_o_refret_wrap_control.rs`) runs with certificates on, in
// `unsupported_program.rs`, because a refusal needs no certificate lane.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
// The x86_64 corpus harness (`bridge_differential_x86.rs`) registers the same rows.

use std::path::{Path, PathBuf};
use std::process::Command;

/// `-O0` is the un-inlined shape (the real call, the real borrowed argument);
/// `-O3` is the shape after rustc's inliner. The soundness row diverges at `-O0`
/// only — `-O3` inlines `identity` and happens to match — so `-O0` is mandatory.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=3"];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_refret_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

#[derive(Debug, PartialEq, Eq)]
struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code + stdout. `Err` carries the compiler's stderr.
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
        "llvm_oracle"
    });

    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.args([opt, "-Clink-arg=-lSystem"]);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    Ok(Run {
        code: run
            .status
            .code()
            .expect("compiled program exited via signal, not an exit code"),
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

/// The bridge's own named refusal tag, if this stderr is a fail-closed refusal
/// rather than a crash. An ICE, a panic, or a refusal with no `[TCG-...]` tag is
/// NOT an honest fail-closed outcome.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Contract {
    /// Must compile and equal LLVM.
    Value,
    /// Equal LLVM, or a named refusal; never a wrong value.
    Probe,
}

struct Case {
    name: &'static str,
    contract: Contract,
    src: &'static str,
    /// What the LLVM oracle MUST print (the fixture header's stated value).
    oracle_stdout: &'static str,
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "fix_o_identity_nonlocal_callee",
            contract: Contract::Value,
            src: include_str!("bridge_corpus/fix_o_identity_nonlocal_callee.rs"),
            oracle_stdout: "seen=9\n",
        },
        Case {
            name: "fix_o_nonnull_as_mut_scalarized_temp",
            contract: Contract::Value,
            src: include_str!("bridge_corpus/fix_o_nonnull_as_mut_scalarized_temp.rs"),
            oracle_stdout: "a=42 b=100 s=142\n",
        },
        Case {
            name: "fix_o_wrapping_and_rawptr_referents",
            contract: Contract::Value,
            src: include_str!("bridge_corpus/fix_o_wrapping_and_rawptr_referents.rs"),
            oracle_stdout: "w=42 a=1 b=42\n",
        },
        Case {
            name: "fix_o_box_referent_probe",
            contract: Contract::Probe,
            src: include_str!("bridge_corpus/fix_o_box_referent_probe.rs"),
            oracle_stdout: "seen=9\n",
        },
        Case {
            name: "fix_o_ref_of_ref_referent_probe",
            contract: Contract::Probe,
            src: include_str!("bridge_corpus/fix_o_ref_of_ref_referent_probe.rs"),
            oracle_stdout: "seen=9\n",
        },
    ]
}

#[test]
fn reference_return_referents_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("reference_return_referents_match_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut refused: Vec<String> = Vec::new();
    let mut matched = 0usize;
    for case in cases() {
        for opt in OPT_LEVELS {
            let dir = workdir(&format!("{}_{}", case.name, &opt["-Copt-level=".len()..]));
            let oracle = compile_and_run(&dir, case.name, case.src, opt, None)
                .unwrap_or_else(|e| panic!("{} ({opt}): LLVM oracle failed: <<<{e}>>>", case.name));
            assert_eq!(
                oracle,
                Run {
                    code: 0,
                    stdout: case.oracle_stdout.to_owned(),
                },
                "{} ({opt}): the LLVM oracle no longer returns the fixture's stated value; \
                 this row is measuring something else",
                case.name
            );
            match compile_and_run(&dir, case.name, case.src, opt, Some(&dylib)) {
                Ok(bridge) => {
                    assert_eq!(
                        bridge, oracle,
                        "{} ({opt}): the bridge COMPILED this reference-return program and \
                         disagrees with LLVM — a store through the returned `&mut` was lost \
                         or misdirected. If `fix_o_identity_nonlocal_callee` printed \
                         `seen=5`, the reference-escaping cell arm lost its widening (see \
                         `cellable_reference_referent_ty`); restore the ADDRESS, do not \
                         relax this assertion.",
                        case.name
                    );
                    matched += 1;
                    eprintln!("{} ({opt}): COMPILED and MATCHED LLVM", case.name);
                }
                Err(stderr) => {
                    let tag = named_refusal(&stderr).unwrap_or_else(|| {
                        panic!(
                            "{} ({opt}): refused WITHOUT a named [TCG-...] diagnostic, which \
                             is a crash rather than a fail-closed outcome: <<<{stderr}>>>",
                            case.name
                        )
                    });
                    assert!(
                        case.contract == Contract::Probe,
                        "{} ({opt}): a VALUE row is a claimed supported surface and must \
                         compile; it failed closed with {tag}: <<<{stderr}>>>",
                        case.name
                    );
                    refused.push(format!("{} ({opt}) {tag}", case.name));
                    eprintln!(
                        "{} ({opt}): PROBE refused by name {tag} (fail-closed, correct)",
                        case.name
                    );
                }
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    eprintln!(
        "reference-return referent rows: {matched} matched LLVM, {} probe refusal(s) {:?}",
        refused.len(),
        refused
    );
}
