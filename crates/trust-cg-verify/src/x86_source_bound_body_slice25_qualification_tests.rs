// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-25 x86-64 body
//! theorems (scaled-index memory rows and memory-destination `add`/`xor`,
//! OD-227; tool-gated: the admitted AY and a Clean checker). The fixtures and
//! solver-free controls are in `slice25`, which the
//! `x86_source_bound_body::tests::slice25::` library gate runs. Each test
//! here is run in a process of its own (a session memo would answer a
//! sibling's queries otherwise).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice16::{every_point, in_parts};
use super::slice25::{QUALIFIED_EDITS, REFUTED, SLICE_TWENTY_FIVE, case25, owner25, slice25_pair};
use super::*;

/// Every slice-25 subject the replay lane certifies, by label: each fixture's
/// whole-body theorem; each fixture's statement in parts at every point
/// (`slice16::every_point`), where the split route states it and the
/// solver-free sampler finds every part holding (one that does not fails
/// exactly as its decomposition does, `slice25::scaled_index_and_rmw_rows_are_stated_in_parts`,
/// and is never credited); and the
/// correct hand edits whose theorem differs from their fixture's
/// (`QUALIFIED_EDITS`: the nonzero displacements, the constant index folded
/// into the displacement, and the slot base reached through a frame or an
/// indexed register), so the solver, and not only the sampler, judges them.
fn qualification_subjects() -> Vec<(String, Function, X86ISelFunction, bool)> {
    let mut subjects = Vec::new();
    for shape in SLICE_TWENTY_FIVE {
        let (source, machine) = slice25_pair(shape);
        subjects.push((format!("{shape:?}"), source.clone(), machine.clone(), false));
        if in_parts(&source, &machine, every_point(&source, &machine))
            .is_ok_and(|owner| super::slice24::owner_holds(&owner).is_ok())
        {
            subjects.push((format!("{shape:?} in parts"), source, machine, true));
        }
    }
    for label in QUALIFIED_EDITS {
        let (source, machine) = case25(label);
        subjects.push((format!("edit {label}"), source, machine, false));
    }
    subjects
}

/// Slice-25 qualification theorems the qualified AY/Clean pair does NOT
/// certify: recorded replayer gaps, never a credit route by themselves.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_TWENTY_FIVE: &[Uncertified] = &[];

/// A diagnostic, not a check: every slice-25 fixture's LIR, machine rows and
/// theorem (or refusal).
#[test]
#[ignore]
fn print_slice_twenty_five_qualification_fixtures() {
    for shape in SLICE_TWENTY_FIVE {
        let (source, machine) = slice25_pair(shape);
        println!(
            "==== {shape:?}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        match owner25(&source, &machine) {
            Ok(owner) => {
                for unit in owner.replayed_units() {
                    println!("{}", generate_smt2_query_raw(unit, &replay_config()));
                }
            }
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
}

/// The slice-25 theorems, generated THROUGH THE REAL BUILDER over each
/// fixture's O2 stream, replay on this host's admitted AY with a
/// Clean-accepted proof (or are recorded gaps with their exact outcome). No
/// correct lowering is refuted, and at least one theorem certifies.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_twenty_five_body_theorems() {
    let test = "host_qualification_replays_the_slice_twenty_five_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let (uncertified, verified) = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        let mut verified = 0usize;
        let mut split = 0usize;
        for (label, source, machine, parts) in qualification_subjects() {
            let owner = if parts {
                split += 1;
                in_parts(&source, &machine, every_point(&source, &machine))
            } else {
                owner25(&source, &machine)
            }
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            assert_eq!(owner.is_stated_in_parts(), parts, "{label}");
            let units = owner.replayed_units();
            let single = units.len() == 1;
            for (k, unit) in units.into_iter().enumerate() {
                let label = if single {
                    label.clone()
                } else {
                    format!("{label} part {}", k + 1)
                };
                if let Some(dir) = &dump {
                    std::fs::create_dir_all(dir).unwrap();
                    std::fs::write(
                        dir.join(format!("{}.smt2", label.replace([' ', '\''], "_"))),
                        generate_smt2_query_raw(unit, &replay_config()),
                    )
                    .unwrap();
                }
                let started = std::time::Instant::now();
                let result = request
                    .ay()
                    .verify_fresh_source_bound(&X86BodyPart { obligation: unit }, &replay_config());
                eprintln!(
                    "X86_BODY_SLICE25_QUALIFICATION shape={label} result={result:?} ms={}",
                    started.elapsed().as_millis()
                );
                assert!(
                    !matches!(result, AYResult::CounterExample(_)),
                    "{label}: a correct lowering was refuted: {result:?}"
                );
                if result == AYResult::Verified {
                    verified += 1;
                } else {
                    eprintln!(
                        "X86_BODY_SLICE25_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                        stable_outcome(&result),
                        proof_gate_class(&result)
                    );
                    uncertified.push((label, stable_outcome(&result), proof_gate_class(&result)));
                }
            }
        }
        assert!(split > 0, "no slice-25 fixture was replayed in parts");
        (uncertified, verified)
    });
    let qualified = assert_qualification_replayer(&edits);
    assert!(verified > 0, "no slice-25 theorem certified");
    let uncertified = super::settle_here(
        uncertified,
        KNOWN_UNCERTIFIED_SLICE_TWENTY_FIVE,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_FIVE",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_TWENTY_FIVE,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_FIVE",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-25 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// Every slice-25 must-refute control's theorem (built without the affine
/// refusal, so the solver judges what the owner may name in Rust) is refuted
/// by AY with a counterexample.
#[test]
fn host_qualification_refutes_the_slice_twenty_five_wrong_lowerings() {
    let test = "host_qualification_refutes_the_slice_twenty_five_wrong_lowerings";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        let mut replayed = 0;
        for label in REFUTED {
            let (source, machine) = case25(label);
            let theorem = match theorem_without_affine_refusal(&source, &machine, SYSV) {
                Ok(theorem) => theorem,
                Err(refusal) => {
                    eprintln!(
                        "X86_BODY_SLICE25_QUALIFICATION wrong={label} result=named ({refusal})"
                    );
                    continue;
                }
            };
            replayed += 1;
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("wrong_{}.smt2", label.replace([' ', '\''], "_"))),
                    generate_smt2_query_raw(&theorem, &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let attributed =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_SLICE25_QUALIFICATION wrong={label} result={:?} ms={}",
                attributed.result,
                started.elapsed().as_millis()
            );
            assert!(
                matches!(attributed.result, AYResult::CounterExample(_)),
                "{label}: AY must refute a wrong lowering's theorem with a counterexample"
            );
        }
        assert!(replayed > 0, "no wrong lowering was stated to refute");
    });
    assert_qualification_replayer(&edits);
}

/// With the real tools, every covered row of every certified slice-25
/// fixture is Formal under the replayed body theorem through the production
/// route, its exports bind the pair, and a wrong lowering is never credited.
#[test]
fn verifier_credits_every_bound_slice_twenty_five_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_twenty_five_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let mut credited = 0;
        for shape in SLICE_TWENTY_FIVE {
            let label = format!("{shape:?}");
            let (source, machine) = slice25_pair(shape);
            let owner =
                owner25(&source, &machine).unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if super::gap_branch_here(
                KNOWN_UNCERTIFIED_SLICE_TWENTY_FIVE,
                "KNOWN_UNCERTIFIED_SLICE_TWENTY_FIVE",
                &label,
                covered_rows_matching(&owner, report.report(), is_needs_replay),
                &qualified,
            ) {
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
            assert_eq!(exports.len(), owner.bound_rows().len(), "{label}");
            assert!(
                report.matches_x86_input(&machine, Some(&source), SYSV),
                "{label}: the report binds the pair"
            );
            credited += 1;
        }
        assert!(credited > 0, "no slice-25 body was credited");
        for label in REFUTED {
            let (source, machine) = case25(label);
            let Ok(owner) = owner25(&source, &machine) else {
                continue;
            };
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            let credited = covered_rows_matching(&owner, report.report(), is_body_credit);
            assert_eq!(credited, 0, "{label}: {:?}", report.report());
            assert!(exports.is_empty(), "{label}");
        }
    });
}
