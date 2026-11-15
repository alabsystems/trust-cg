// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of slice 16's theorems in parts
//! (tool-gated: the admitted AY and a Clean checker). The fixtures and the
//! solver-free controls are in `slice16`, which the
//! `x86_source_bound_body::tests::slice16::` library gate runs; these tests
//! need the replayer pair their recorded outcomes were measured with. Run
//! each test in its own process (`--test-threads=1` and one filter per run):
//! an in-process session memo would otherwise answer a sibling test's
//! queries.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice16::{CONTROLS, SLICE_SIXTEEN, control_cut, control_pair, in_parts, slice16_pair};
use super::*;

/// Slice-16 qualification parts the qualified AY/Clean pair does NOT
/// certify: recorded replayer gaps (`<shape> part <k>`), never a credit
/// route. `LongChain`'s machine is the source's computation spelled step for
/// step, so every region's claims become identities once value-numbered and
/// its theorem is stated plainly (never by identities alone): ninety 64-bit
/// `x ^ (x << 3)` and `+ k` steps on each side, under different names.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_SIXTEEN: &[Uncertified] = &[
    Uncertified {
        label: "LongChain part 1",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: "ay: no answer within the 30 s deadline; offline with a 300 s budget it \
             computes UNSAT and rejects its own proof after 187.8 s: `computed UNSAT rejected by \
             mandatory strict certification: strict UNSAT proof validation failed: step t1 uses \
             unverified trust rule` / `unknown` / `(:reason-unknown (incomplete \
             self-check-rejected))`; no proof for clean (build 12713: `unknown` / \
             `(:reason-unknown timeout)` after 300.1 s)",
    },
    Uncertified {
        label: "LongChain part 2",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: "ay: no answer within the 30 s deadline; offline with a 300 s budget it \
             computes UNSAT and rejects its own proof after 180.0 s: `computed UNSAT rejected by \
             mandatory strict certification: strict UNSAT proof validation failed: step t1 uses \
             unverified trust rule` / `unknown` / `(:reason-unknown (incomplete \
             self-check-rejected))`; no proof for clean (build 12713: `unknown` / \
             `(:reason-unknown timeout)` after 300.1 s)",
    },
    Uncertified {
        label: "LongChain part 3",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: "ay: no answer within the 30 s deadline; offline with a 300 s budget it \
             computes UNSAT and rejects its own proof after 291.6 s: `computed UNSAT rejected by \
             mandatory strict certification: strict UNSAT proof validation failed: step t1 uses \
             unverified trust rule` / `unknown` / `(:reason-unknown (incomplete \
             self-check-rejected))`; no proof for clean (build 12713: `unknown` / \
             `(:reason-unknown timeout)` after 305.9 s)",
    },
];

/// Wrong lowerings stated in parts whose live replay finds no counterexample
/// within the deadline: the parts without a Valid replay, never credited.
/// None since slice 18 spells each part again (OD-189): `a branch inverted
/// mid-chain` (`DiamondChain`), whose part 2 the live replay's resident
/// (`--incremental`) AY ran out its 30 s on (the one-shot `ay -smt2`
/// answered `sat` in 0.1 s), is refuted with a counterexample in 0.7 s (one
/// test per process, 2026-10-19,
/// `reports/perf/2026-10-19-darwin-x86-64-slice18-spelling/`).
const KNOWN_UNREFUTED_SLICE_SIXTEEN: &[(&str, &str)] = &[];

/// Every part of `owner`, replayed: `(part name, outcome)`.
fn replay_parts(
    request: &FunctionVerificationRequest,
    owner: &SourceBoundX86Body<'_>,
    label: &str,
    dump: Option<&std::path::Path>,
) -> Vec<(String, AYResult)> {
    owner
        .replay_parts()
        .enumerate()
        .map(|(k, part)| {
            if let Some(dir) = dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!(
                        "{}.part{}.smt2",
                        label.replace([' ', '/'], "_"),
                        k + 1
                    )),
                    generate_smt2_query_raw(part.obligation(), &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let result = request
                .ay()
                .verify_fresh_source_bound(&part, &replay_config());
            eprintln!(
                "X86_BODY_SLICE16_QUALIFICATION shape={label} part={} result={result:?} ms={}",
                k + 1,
                started.elapsed().as_millis()
            );
            (format!("{label} part {}", k + 1), result)
        })
        .collect()
}

/// The correct pairs stated in parts: every control cut at its block, every
/// size shape by the production planner.
fn qualified_pairs() -> Vec<(String, Function, X86ISelFunction, bool)> {
    let mut pairs = Vec::new();
    for shape in CONTROLS {
        let (source, machine) = control_pair(shape);
        pairs.push((format!("{shape:?}"), source, machine, false));
    }
    for shape in SLICE_SIXTEEN {
        let (source, machine) = slice16_pair(shape);
        pairs.push((format!("{shape:?}"), source, machine, true));
    }
    pairs
}

/// Every part of every slice-16 qualification pair, generated THROUGH THE
/// REAL BUILDER, replays on this host's admitted AY with a Clean-accepted
/// proof (or is a recorded gap with its exact outcome), and the wrong
/// lowerings stated in parts (the controls' mis-models at their cut, and a
/// wrong lowering of each size shape by the production planner) are refuted
/// with a counterexample in some part, every part replayed.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_sixteen_parts() {
    let test = "host_qualification_replays_the_slice_sixteen_parts";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let (uncertified, unrefuted) = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for (label, source, machine, production) in qualified_pairs() {
            let owner = if production {
                source_bound_x86_body(&source, &machine, SYSV)
            } else {
                in_parts(&source, &machine, vec![(control_cut(&source), 0)])
            }
            .unwrap_or_else(|refusal| {
                panic!(
                    "{label}: {refusal}\n{}{}",
                    describe_lir(&source),
                    describe(&machine)
                )
            });
            for (part, result) in replay_parts(&request, &owner, &label, dump.as_deref()) {
                assert!(
                    !matches!(result, AYResult::CounterExample(_)),
                    "{part}: a correct lowering was refuted: {result:?}"
                );
                if result != AYResult::Verified {
                    eprintln!(
                        "X86_BODY_SLICE16_QUALIFICATION gap={part} outcome={} proof_gate_class={}",
                        stable_outcome(&result),
                        proof_gate_class(&result)
                    );
                    uncertified.push((part, stable_outcome(&result)));
                }
            }
        }
        let controls = slice_sixteen_refutations()
            .into_iter()
            .map(|case| (case, false));
        let sizes = super::slice16::size_refutations()
            .into_iter()
            .map(|case| (case, true));
        let mut unrefuted = Vec::new();
        for ((label, source, machine), production) in controls.chain(sizes) {
            let owner = if production {
                source_bound_x86_body(&source, &machine, SYSV)
            } else {
                in_parts(&source, &machine, vec![(control_cut(&source), 0)])
            }
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let outcomes = replay_parts(
                &request,
                &owner,
                &format!("refutation {label}"),
                dump.as_deref(),
            );
            let refuted = outcomes
                .iter()
                .any(|(_, result)| matches!(result, AYResult::CounterExample(_)));
            eprintln!("X86_BODY_SLICE16_QUALIFICATION refutation={label} refuted={refuted}");
            if refuted {
                continue;
            }
            // Not refuted within the deadline: never credited only while
            // some part has no Valid replay. Each such part is recorded.
            let open: Vec<(String, String)> = outcomes
                .into_iter()
                .filter(|(_, result)| *result != AYResult::Verified)
                .map(|(part, result)| (part, stable_outcome(&result)))
                .collect();
            assert!(
                !open.is_empty(),
                "{label}: a wrong lowering stated in parts replays Valid in every part"
            );
            unrefuted.extend(open);
        }
        (uncertified, unrefuted)
    });
    assert_qualification_replayer(&edits);
    let recorded_unrefuted: Vec<(String, String)> = KNOWN_UNREFUTED_SLICE_SIXTEEN
        .iter()
        .map(|(part, outcome)| ((*part).to_owned(), (*outcome).to_owned()))
        .collect();
    assert_eq!(
        unrefuted, recorded_unrefuted,
        "the refuted slice-16 set changed on this host: update the recorded parts after \
         reviewing each outcome above"
    );
    let recorded: Vec<(String, String)> = KNOWN_UNCERTIFIED_SLICE_SIXTEEN
        .iter()
        .map(|gap| (gap.label.to_owned(), gap.outcome.to_owned()))
        .collect();
    assert_eq!(
        uncertified, recorded,
        "the certified slice-16 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// The wrong lowerings of the slice-16 controls (the mis-models the cut
/// rules exist for), each stated in parts at its control's cut: a mismatch
/// a cut would hide, values swapped across a cut, a value read from another
/// register after a cut, a slot byte changed before a cut, a wrong value on
/// one edge into a join cut, and bits an edge leaves above a byte returned
/// after a cut without its zero extension.
pub(crate) fn slice_sixteen_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    super::slice16::control_refutations()
}

/// With the real tools, every covered row of every size shape is Formal
/// under its theorem in parts (every part replayed Valid), the function is
/// promotable and each export carries the complete part inventory; a wrong
/// lowering of one region is never credited (a refuted part refutes the
/// theorem; a part before it without a verdict leaves it unverified).
#[test]
fn verifier_credits_every_bound_row_of_a_function_in_parts() {
    let test = "verifier_credits_every_bound_row_of_a_function_in_parts";
    let edits = replay_environment(test);
    // The recorded gap parts this lane branches on were measured with one
    // replayer pair: check the pair before the first replay.
    assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_SIXTEEN {
            let label = format!("{shape:?}");
            let (source, machine) = slice16_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            assert!(owner.is_stated_in_parts(), "{label}");
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if KNOWN_UNCERTIFIED_SLICE_SIXTEEN
                .iter()
                .any(|gap| gap.label.starts_with(&format!("{label} part")))
            {
                assert_eq!(
                    covered_rows_matching(&owner, report.report(), is_needs_replay),
                    owner.bound_rows().len(),
                    "{label}"
                );
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
            for export in &exports {
                let published = export.replayed_obligations().expect("a complete inventory");
                assert_eq!(published.len(), owner.parts().len(), "{label}");
            }
        }
        // A wrong lowering of one region is never credited: every covered
        // row fails when the replay reaches the refuted part, and stays
        // unverified when an earlier part has no verdict (the serial replay
        // stops at the first part without a Valid one).
        for (label, source, machine) in super::slice16::size_refutations() {
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            let failed = covered_rows_matching(&owner, report.report(), |result| {
                matches!(result, InstructionVerificationResult::Failed { .. })
            });
            let unverified = covered_rows_matching(&owner, report.report(), is_needs_replay);
            eprintln!(
                "X86_BODY_SLICE16_CREDIT refutation={label} parts={} failed={failed} \
                 unverified={unverified}",
                owner.parts().len()
            );
            assert!(
                failed == owner.bound_rows().len() || unverified == owner.bound_rows().len(),
                "{label}: {:?}",
                report.report()
            );
            assert!(exports.is_empty(), "{label}");
        }
    });
}
