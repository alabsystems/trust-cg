// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-9 x86-64 body
//! theorems (acyclic control flow over the DAG; tool-gated: the admitted AY
//! and a Clean checker). The fixtures, golden snapshots and solver-free
//! controls are in `slice9`, which the `x86_source_bound_body::tests::slice9::`
//! library gate runs; these tests need the replayer pair their recorded
//! outcomes were measured with.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{SLICE_NINE, slice_nine_refutations, slice9_pair};
use super::*;

/// The outcome of a theorem whose AY certificate has one unproved step.
const INCOMPLETE_CERTIFICATE: &str = "Unknown(\"incomplete AY proof certificate: c \
     ay.proof.certificate path=<path> unproved_steps=1 foreign_assumes=no trust_free=no \
     ay_self_checkable=no unsat_admission=strict-proof\")";

/// Slice-9 qualification cases whose canonical theorem the qualified AY/Clean
/// pair does NOT certify: a recorded replayer gap, never a credit route. On
/// the qualification host ([`QUALIFIED_AY`], Clean 5f09e36c) `LongChain` is a
/// strict self-check rejection within a second (a one-equation theorem,
/// which slice 18's spelling leaves plain), on build 12713 and on build
/// 13556 alike. With AY build 10530 every fixture with
/// 64-bit arithmetic across its joins, and `SlotJoin`, `BoolDag` and
/// `NestedTree`, were AY rejecting its own proof, most after the strict
/// bit-blast certification's 3 s wall; build 12713 certified `SlotJoin` and
/// `BoolDag`, `NestedTree` from main's balanced canonical conjunctions
/// (`71c2eb632`), and ran past the 30 s deadline on `Diamonds5`, `Diamonds6`,
/// `GuardChain9`, `SwitchChain`, `LongArm`, `CallJoin` and `LoadDag`. Since
/// slice 18's spelling (OD-187) all seven certify on the same pair, in 0.25 to
/// 6.1 s (one test per process, 2026-10-19,
/// `reports/perf/2026-10-19-darwin-x86-64-slice18-spelling/`).
pub(crate) const KNOWN_UNCERTIFIED_SLICE_NINE: &[Uncertified] = &[Uncertified {
    label: "LongChain",
    outcome: SELF_CHECK_REJECTED,
    proof_gate_class: "SOUNDNESS",
    tool_output: "ay: `computed UNSAT rejected by mandatory strict certification: strict UNSAT \
         proof validation failed: step t1 uses unverified trust rule` (within 0.6 s; build 12713 \
         named step t0, within 0.1 s) / `unknown` `(:reason-unknown (incomplete \
         self-check-rejected))`",
}];

/// A diagnostic, not a check: every slice-9 fixture's LIR, machine rows and
/// theorem (or refusal). It lives here, outside the solver-free gate's
/// `slice9::` filter, which counts an ignored test as a skip.
#[test]
#[ignore]
fn print_slice_nine_fixtures() {
    for shape in SLICE_NINE {
        let (source, machine) = slice9_pair(shape);
        println!(
            "==== {shape:?}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        match source_bound_x86_body(&source, &machine, SYSV) {
            Ok(owner) => println!(
                "{}",
                generate_smt2_query_raw(owner.obligation(), &replay_config())
            ),
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
}

/// A diagnostic, not a check: every several-path slice-6 fixture's theorem
/// under the slice-6 per-path claims and over its DAG (slice 9), and every
/// slice-9 fixture's under both, written as SMT-LIB to
/// `$TCG_X86_BODY_QUALIFY_DUMP/{paths,dag}/` for an offline replay of the
/// two encodings on the same pairs.
#[test]
#[ignore]
fn dump_the_two_encodings_of_every_fixture() {
    let Some(dir) = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from)
    else {
        return;
    };
    let mut pairs: Vec<(String, Function, X86ISelFunction)> = super::slice6::all_slice_six_shapes()
        .into_iter()
        .map(|shape| {
            let (source, machine) = super::slice6::slice6_pair(shape);
            (format!("s6_{shape:?}"), source, machine)
        })
        .collect();
    for shape in SLICE_NINE {
        let (source, machine) = slice9_pair(shape);
        pairs.push((format!("s9_{shape:?}"), source, machine));
    }
    for (label, source, machine) in pairs {
        for (name, dag) in [("paths", false), ("dag", true)] {
            let encoding = PathEncoding {
                dag: Some(dag),
                ..PathEncoding::CANONICAL
            };
            let Ok(theorem) = theorem_with_path_encoding(&source, &machine, SYSV, encoding) else {
                continue;
            };
            let out = dir.join(name);
            std::fs::create_dir_all(&out).unwrap();
            std::fs::write(
                out.join(format!("{label}.smt2")),
                generate_smt2_query_raw(&theorem, &replay_config()),
            )
            .unwrap();
        }
    }
}

/// The canonical slice-9 theorems, generated THROUGH THE REAL BUILDER,
/// replay on this host's admitted AY with a Clean-accepted proof (or are
/// recorded gaps with their exact outcome), and every wrong lowering is
/// refuted with a counterexample. The recorded gaps are compared only under
/// the replayer pair they were measured with
/// ([`assert_qualification_replayer`]).
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_nine_body_theorems() {
    let test = "host_qualification_replays_the_slice_nine_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in SLICE_NINE {
            let label = format!("{shape:?}");
            let (source, machine) = slice9_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(dir.join(format!("{label}.smt2")), &smt2).unwrap();
            }
            let started = std::time::Instant::now();
            let result = request
                .ay()
                .verify_fresh_source_bound(&owner, &replay_config());
            eprintln!(
                "X86_BODY_SLICE9_QUALIFICATION shape={label} rows={} result={result:?} ms={}",
                owner.bound_rows().len(),
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_SLICE9_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label.clone(), stable_outcome(&result)));
            }
        }
        for (label, source, machine) in slice_nine_refutations() {
            let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let refuted =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_SLICE9_QUALIFICATION refutation={label} result={:?}",
                refuted.result
            );
            assert!(
                matches!(refuted.result, AYResult::CounterExample(_)),
                "{label} must be refuted: {:?}",
                refuted.result
            );
        }
        uncertified
    });
    let qualified = assert_qualification_replayer(&edits);
    // Each recorded gap shows its recorded outcome. The one tolerance is
    // between AY's two rejections of its own proof (a strict self-check
    // rejection or a certificate with an unproved step), which with AY build
    // 10530 depended on the host's load at the strict certification's 3 s
    // wall: measured 2026-10-02, `SwitchTree` (then a gap, before inlined
    // identities were dropped) showed each on two runs. Any other outcome, a
    // gap that certifies, or a certified fixture that no longer does is a
    // change to review.
    let self_rejections = [SELF_CHECK_REJECTED, INCOMPLETE_CERTIFICATE];
    let changed: Vec<(&String, &String, &str)> = uncertified
        .iter()
        .filter_map(|(label, outcome)| {
            let recorded = KNOWN_UNCERTIFIED_SLICE_NINE
                .iter()
                .find(|gap| gap.label == label)?
                .outcome;
            let interchangeable =
                self_rejections.contains(&outcome.as_str()) && self_rejections.contains(&recorded);
            (outcome != recorded && !interchangeable).then_some((label, outcome, recorded))
        })
        .collect();
    assert!(
        changed.is_empty(),
        "a recorded slice-9 gap changed outcome on this host (label, outcome, recorded): \
         {changed:?}"
    );
    let labels: Vec<&str> = uncertified
        .iter()
        .map(|(label, _)| label.as_str())
        .collect();
    let recorded = super::recorded_gap_labels(
        KNOWN_UNCERTIFIED_SLICE_NINE,
        "KNOWN_UNCERTIFIED_SLICE_NINE",
        &qualified,
    );
    assert_eq!(
        labels, recorded,
        "the certified slice-9 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// With the real tools, every covered row of every certified slice-9 shape is
/// Formal under the body theorem (every block's rows and every `jcc`), the
/// function is promotable and its exports bind the ABI; a wrong lowering the
/// Rust check cannot judge fails every covered row.
#[test]
fn verifier_credits_every_bound_slice_nine_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_nine_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    // The per-host gap view this lane branches on was recorded with one
    // replayer pair: check the pair before the first replay.
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_NINE {
            let label = format!("{shape:?}");
            let (source, machine) = slice9_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if super::gap_applies_here(
                KNOWN_UNCERTIFIED_SLICE_NINE,
                "KNOWN_UNCERTIFIED_SLICE_NINE",
                &label,
                &qualified,
            ) {
                assert_eq!(
                    covered_rows_matching(&owner, report.report(), is_needs_replay),
                    owner.bound_rows().len(),
                    "{label}"
                );
                assert!(!report.report().has_failures(), "{label}");
                assert!(exports.is_empty(), "{label}");
                continue;
            }
            for row in &report.report().instructions {
                if owner.covers(row.inst_index) {
                    assert!(
                        is_body_credit(&row.result),
                        "{label} row {} {:?}: {:?}",
                        row.inst_index,
                        row.opcode,
                        row.result
                    );
                }
            }
            let inventory = report.report().emitted_opcode_inventory();
            assert!(inventory.is_promotable(), "{label}: {inventory:?}");
            assert_eq!(exports.len(), owner.bound_rows().len(), "{label}");
            assert!(report.matches_x86_input(&machine, Some(&source), SYSV));
        }
        for (label, source, machine) in slice_nine_refutations() {
            let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) else {
                continue;
            };
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            assert_eq!(
                covered_rows_matching(&owner, report.report(), |result| matches!(
                    result,
                    InstructionVerificationResult::Failed { proof_name, .. }
                        if proof_name == X86_BODY_OBLIGATION_NAME
                )),
                owner.bound_rows().len(),
                "{label}: {:?}",
                report.report()
            );
            assert!(exports.is_empty(), "{label}");
        }
    });
}

/// Encoding evidence, never credit: every slice-9 fixture's theorem under the
/// Boolean guard spelling (`PathEncoding::bool_guards`), under the slice-6
/// per-path claims and under slice 9's own spellings without slice 18's
/// value numbering (plain, uninlined, an untrimmed chain), replayed on the
/// admitted AY/Clean pair beside the canonical one. No spelling may be refuted (they state one theorem); the
/// outcomes are printed for the record (`X86_BODY_SLICE9_SPELLING`).
#[test]
fn host_qualification_records_the_slice_nine_spellings() {
    let test = "host_qualification_records_the_slice_nine_spellings";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        for shape in SLICE_NINE {
            let label = format!("{shape:?}");
            let (source, machine) = slice9_pair(shape);
            for (spelling, encoding) in [
                ("canonical", PathEncoding::CANONICAL),
                (
                    "bool-guards",
                    PathEncoding {
                        bool_guards: true,
                        ..PathEncoding::CANONICAL
                    },
                ),
                (
                    "per-path",
                    PathEncoding {
                        dag: Some(false),
                        ..PathEncoding::CANONICAL
                    },
                ),
                // Slice 9's spellings before slice 18's value numbering.
                (
                    "plain",
                    PathEncoding {
                        value_number: ValueNumbering::Off,
                        ..PathEncoding::CANONICAL
                    },
                ),
                (
                    "no-inlining",
                    PathEncoding {
                        inline_single_use: false,
                        value_number: ValueNumbering::Off,
                        ..PathEncoding::CANONICAL
                    },
                ),
                (
                    "untrimmed-chain",
                    PathEncoding {
                        trim_long_chains: false,
                        inline_single_use: false,
                        value_number: ValueNumbering::Off,
                        ..PathEncoding::CANONICAL
                    },
                ),
            ] {
                let theorem = match theorem_with_path_encoding(&source, &machine, SYSV, encoding) {
                    Ok(theorem) => theorem,
                    Err(refusal) => {
                        eprintln!(
                            "X86_BODY_SLICE9_SPELLING shape={label} spelling={spelling} \
                             refused={refusal}"
                        );
                        continue;
                    }
                };
                let started = std::time::Instant::now();
                let result =
                    crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config())
                        .result;
                eprintln!(
                    "X86_BODY_SLICE9_SPELLING shape={label} spelling={spelling} result={} ms={}",
                    stable_outcome(&result),
                    started.elapsed().as_millis()
                );
                assert!(
                    !matches!(result, AYResult::CounterExample(_)),
                    "{label} {spelling}: a correct lowering was refuted"
                );
            }
        }
    });
    assert_qualification_replayer(&edits);
}
