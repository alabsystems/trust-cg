// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification of the OD-233 statements in parts (defined cut inputs;
//! tool-gated: the admitted AY and a Clean checker). The fixtures and the
//! solver-free controls are in `od233`, which the
//! `x86_source_bound_body::tests::od233::` library gate runs. Each test here
//! is run in a process of its own (a session memo would answer a sibling's
//! queries otherwise).

use super::od233::{
    POSITIVE, SLOT_FIXTURES, WRONG, od233_pair, owner233, slot_owner, slot_wrong, wrong233,
};
use super::slice25::slice25_pair;
use super::*;

/// Every OD-233 subject the replay lane certifies, by label: each positive
/// fixture stated in parts at its points (P1-P5, P7) and slice 25's three
/// slot fixtures stated in parts at every point (P6).
fn qualification_subjects() -> Vec<(String, Function, X86ISelFunction, bool)> {
    let mut subjects = Vec::new();
    for shape in POSITIVE {
        let (source, machine) = od233_pair(shape);
        subjects.push((
            format!("{} {shape:?}", shape.label()),
            source,
            machine,
            false,
        ));
    }
    for shape in SLOT_FIXTURES {
        let (source, machine) = slice25_pair(shape);
        subjects.push((format!("P6 {shape:?}"), source, machine, true));
    }
    subjects
}

/// OD-233 qualification parts the qualified AY/Clean pair does NOT certify:
/// recorded replayer gaps, never a credit route by themselves.
pub(crate) const KNOWN_UNCERTIFIED_OD233: &[Uncertified] = &[];

/// Every part of every OD-233 statement in parts, generated THROUGH THE REAL
/// BUILDER over each fixture's O2 stream, replays on this host's admitted AY
/// with a Clean-accepted proof (or is a recorded gap with its exact
/// outcome). No correct lowering is refuted, and at least one part
/// certifies.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_od233_parts() {
    let test = "host_qualification_replays_the_od233_parts";
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
        let mut defining = 0usize;
        for (label, source, machine, slot) in qualification_subjects() {
            let owner = if slot {
                slot_owner(&source, &machine)
            } else {
                let shape = POSITIVE
                    .into_iter()
                    .find(|shape| label == format!("{} {shape:?}", shape.label()))
                    .expect("a positive fixture");
                owner233(shape, &source, &machine)
            }
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            assert!(owner.is_stated_in_parts(), "{label}");
            let (bytes, items) = owner.defined_cut_inputs();
            if bytes + items > 0 {
                defining += 1;
            }
            eprintln!(
                "X86_BODY_OD233_QUALIFICATION subject={label} parts={} defined bytes={bytes} \
                 items={items}",
                owner.parts().len()
            );
            for (k, part) in owner.parts().iter().enumerate() {
                let label = format!("{label} part {}", k + 1);
                if let Some(dir) = &dump {
                    std::fs::create_dir_all(dir).unwrap();
                    std::fs::write(
                        dir.join(format!("{}.smt2", label.replace([' ', '\''], "_"))),
                        generate_smt2_query_raw(part, &replay_config()),
                    )
                    .unwrap();
                }
                let started = std::time::Instant::now();
                let result = request
                    .ay()
                    .verify_fresh_source_bound(&X86BodyPart { obligation: part }, &replay_config());
                eprintln!(
                    "X86_BODY_OD233_QUALIFICATION shape={label} result={result:?} ms={}",
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
                        "X86_BODY_OD233_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                        stable_outcome(&result),
                        proof_gate_class(&result)
                    );
                    uncertified.push((label, stable_outcome(&result), proof_gate_class(&result)));
                }
            }
        }
        assert!(defining > 0, "no OD-233 subject defines a cut input");
        (uncertified, verified)
    });
    let qualified = assert_qualification_replayer(&edits);
    assert!(verified > 0, "no OD-233 part certified");
    let uncertified = super::settle_here(
        uncertified,
        KNOWN_UNCERTIFIED_OD233,
        "KNOWN_UNCERTIFIED_OD233",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_OD233,
        "KNOWN_UNCERTIFIED_OD233",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified OD-233 set changed on this host: update the recorded replayer gaps (and \
         LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// Every OD-233 wrong lowering (W1-W6) stated in parts has a part AY
/// refutes with a counterexample (a wrong lowering named a mismatch before a
/// theorem exists is refuted by name).
#[test]
fn host_qualification_refutes_the_od233_wrong_lowerings() {
    let test = "host_qualification_refutes_the_od233_wrong_lowerings";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        let mut cases: Vec<(
            String,
            Function,
            X86ISelFunction,
            Option<super::od233::Shape233>,
        )> = WRONG
            .into_iter()
            .map(|wrong| {
                let (source, machine) = wrong233(wrong);
                (
                    format!("{} {wrong:?}", wrong.label()),
                    source,
                    machine,
                    Some(wrong.shape()),
                )
            })
            .collect();
        let (source, machine) = slot_wrong();
        cases.push(("W5 SlotConstU64 imul by 16".into(), source, machine, None));
        let mut refuted = 0;
        for (label, source, machine, shape) in &cases {
            let owner = match shape {
                Some(shape) => owner233(*shape, source, machine),
                None => slot_owner(source, machine),
            };
            let owner = match owner {
                Ok(owner) => owner,
                Err(X86BodyRefusal::Mismatch(mismatch)) => {
                    eprintln!(
                        "X86_BODY_OD233_QUALIFICATION wrong={label} result=named ({mismatch})"
                    );
                    refuted += 1;
                    continue;
                }
                Err(refusal) => panic!("{label}: a wrong lowering is not stated: {refusal}"),
            };
            let mut counterexample = false;
            for (k, part) in owner.parts().iter().enumerate() {
                if let Some(dir) = &dump {
                    std::fs::create_dir_all(dir).unwrap();
                    std::fs::write(
                        dir.join(format!(
                            "wrong_{}_part_{}.smt2",
                            label.replace([' ', '\''], "_"),
                            k + 1
                        )),
                        generate_smt2_query_raw(part, &replay_config()),
                    )
                    .unwrap();
                }
                let started = std::time::Instant::now();
                let attributed =
                    crate::ay_bridge::verify_with_cli_raw_attributed(part, &replay_config());
                eprintln!(
                    "X86_BODY_OD233_QUALIFICATION wrong={label} part={} result={:?} ms={}",
                    k + 1,
                    attributed.result,
                    started.elapsed().as_millis()
                );
                counterexample |= matches!(attributed.result, AYResult::CounterExample(_));
            }
            assert!(
                counterexample,
                "{label}: AY must refute a part of a wrong lowering's statement with a \
                 counterexample"
            );
            refuted += 1;
        }
        assert_eq!(refuted, cases.len(), "every wrong lowering is refuted");
    });
    assert_qualification_replayer(&edits);
}

/// Measurement, not a gate (OD-233's re-cut cost): every part of slice 20's
/// `ManySlots` stated in parts at every clean point, the sweep's largest
/// re-cut (its parts, without the rule and with it), replayed on this
/// host's AY, each part's verdict and time printed
/// (`X86_BODY_OD233_RECUT_TIME`). Without the rule is the `od233-off`
/// test-only switch on this thread alone.
#[test]
#[ignore = "measurement"]
fn host_qualification_times_the_largest_recut_statement() {
    let test = "host_qualification_times_the_largest_recut_statement";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let (label, source, machine) = super::slice24::later_fixtures()
            .into_iter()
            .find(|(label, _, _)| label == "s20 ManySlots")
            .expect("slice 20's ManySlots");
        let points = super::slice16::every_point(&source, &machine);
        for names in ["od233-off", ""] {
            let _mutant = super::super::quotient::mutant::set(names);
            let owner = super::slice16::in_parts(&source, &machine, points.clone())
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let n = owner.parts().len();
            let (mut total, mut most, mut verified) = (0u128, 0u128, 0usize);
            for (k, part) in owner.parts().iter().enumerate() {
                let started = std::time::Instant::now();
                let result = request
                    .ay()
                    .verify_fresh_source_bound(&X86BodyPart { obligation: part }, &replay_config());
                let ms = started.elapsed().as_millis();
                total += ms;
                most = most.max(ms);
                if result == AYResult::Verified {
                    verified += 1;
                }
                eprintln!(
                    "X86_BODY_OD233_RECUT_TIME {label} mutants={names:?} part {} of {n} \
                     result={result:?} ms={ms}",
                    k + 1
                );
            }
            eprintln!(
                "X86_BODY_OD233_RECUT_TIME {label} mutants={names:?} parts={n} \
                 verified={verified} total_ms={total} most_ms={most} defined={:?}",
                owner.defined_cut_inputs()
            );
        }
    });
    assert_qualification_replayer(&edits);
}
