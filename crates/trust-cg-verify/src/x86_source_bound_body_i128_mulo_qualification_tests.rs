// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification of the OD-224 x86-64 body theorems (the division-free
//! 128-bit checked multiply; tool-gated: the admitted AY and a Clean
//! checker). The fixtures and solver-free controls are in `i128_mulo`, which
//! the `x86_source_bound_body::tests::i128_mulo::` library gate runs. Each test
//! here is run in a process of its own (a session memo would answer a
//! sibling's queries otherwise). Slice 22's own qualification replays its five
//! checked-multiply shapes, which OD-224 changed too.

use super::i128_mulo::{MULO_SHAPES, division_free_wrong_lowerings, mulo_pair};
use super::slice22::fixture_owner;
use super::*;

/// OD-224 qualification theorems the qualified AY/Clean pair does NOT
/// certify by their exact replay: recorded replayer gaps, never a credit
/// route by themselves. AY 13556 computes UNSAT on each limb check's exact
/// theorem and rejects its own proof in its strict certification (the class
/// of slice 23's `U64OverflowingPowLeaf`); every one's OD-206 generalization
/// certifies, which the replay lane below requires, and which the production
/// route credits. The constant-operand compare's exact theorem certifies.
pub(crate) const KNOWN_UNCERTIFIED_I128_MULO: &[Uncertified] = &[
    Uncertified {
        label: "U128Flag",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: SELF_CHECK_OUTPUT,
    },
    Uncertified {
        label: "I128OverflowingMul",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: SELF_CHECK_OUTPUT,
    },
    Uncertified {
        label: "U128SaturatingMul",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: SELF_CHECK_OUTPUT,
    },
    Uncertified {
        label: "I128SaturatingMul",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: SELF_CHECK_OUTPUT,
    },
];

/// AY's answer to the exact limb-check theorems (2026-11-03, AY 13556 with
/// Clean 5f09e36c, load 2.4-2.7).
const SELF_CHECK_OUTPUT: &str = "ay computes UNSAT in 0.9-3.3 s and rejects its own proof in its \
     mandatory strict certification (`(:reason-unknown (incomplete self-check-rejected))`); the \
     OD-206 generalization certifies in 0.4-2.8 s";

/// The OD-206 generalization of every slice-22 checked multiply whose exact
/// theorem AY does not certify (`KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO`'s OD-224
/// rows), each unit and each part at every block of the shapes slice 22 cuts,
/// certifies on the qualification pair: the production route's credit.
#[test]
fn host_qualification_replays_the_generalizations_of_slice_twenty_two_s_checked_multiplies() {
    use super::slice22::{Shape22, cut_everywhere, slice22_owner, slice22_pair};
    let test =
        "host_qualification_replays_the_generalizations_of_slice_twenty_two_s_checked_multiplies";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        for shape in [
            Shape22::U128CheckedMul,
            Shape22::I128OverflowingMul,
            Shape22::U128MulAcrossCut,
            Shape22::U128MulZextOperand,
        ] {
            let (source, machine) = slice22_pair(shape);
            let owner = fixture_owner(&source, &machine)
                .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
            let mut owners = vec![(format!("{shape:?}"), owner)];
            if cut_everywhere(shape) {
                let cut = slice22_owner(shape, &source, &machine)
                    .unwrap_or_else(|refusal| panic!("{shape:?} (cut): {refusal}"));
                owners.push((format!("{shape:?} cut"), cut));
            }
            for (label, owner) in owners {
                for k in 0..owner.replayed_units().len() {
                    let general = owner
                        .replay_generalized(k)
                        .unwrap_or_else(|why| panic!("{label} unit {k}: {why}"));
                    let started = std::time::Instant::now();
                    let result = request
                        .ay()
                        .verify_fresh_source_bound(&general, &replay_config());
                    eprintln!(
                        "X86_BODY_I128_MULO_QUALIFICATION slice22-generalized={label} unit={k} \
                         result={result:?} ms={}",
                        started.elapsed().as_millis()
                    );
                    assert_eq!(result, AYResult::Verified, "{label} unit {k}");
                }
            }
        }
    });
    assert_qualification_replayer(&edits);
}

/// The OD-224 theorems, generated THROUGH THE REAL BUILDER, replay on this
/// host's admitted AY with a Clean-accepted proof (or are recorded gaps with
/// their exact outcome). No correct lowering is refuted. Each unit whose exact
/// replay has no verdict is replayed once more as its OD-206 generalization,
/// as the production route does, and must certify there
/// (`X86_BODY_I128_MULO_QUALIFICATION generalized=`).
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_division_free_checked_multiply_theorems() {
    let test = "host_qualification_replays_the_division_free_checked_multiply_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in MULO_SHAPES {
            let (source, machine) = mulo_pair(shape);
            let owner = fixture_owner(&source, &machine)
                .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
            let units = owner.replayed_units();
            let single = units.len() == 1;
            for (k, unit) in units.into_iter().enumerate() {
                let label = if single {
                    format!("{shape:?}")
                } else {
                    format!("{shape:?} part {}", k + 1)
                };
                if let Some(dir) = &dump {
                    std::fs::create_dir_all(dir).unwrap();
                    std::fs::write(
                        dir.join(format!("{}.smt2", label.replace([' ', '(', ')'], "_"))),
                        generate_smt2_query_raw(unit, &replay_config()),
                    )
                    .unwrap();
                }
                let started = std::time::Instant::now();
                let result = request
                    .ay()
                    .verify_fresh_source_bound(&X86BodyPart { obligation: unit }, &replay_config());
                eprintln!(
                    "X86_BODY_I128_MULO_QUALIFICATION shape={label} result={result:?} ms={}",
                    started.elapsed().as_millis()
                );
                assert!(
                    !matches!(result, AYResult::CounterExample(_)),
                    "{label}: a correct lowering was refuted: {result:?}"
                );
                if result != AYResult::Verified {
                    eprintln!(
                        "X86_BODY_I128_MULO_QUALIFICATION gap={label} outcome={} \
                         proof_gate_class={}",
                        stable_outcome(&result),
                        proof_gate_class(&result)
                    );
                    let general = owner
                        .replay_generalized(k)
                        .unwrap_or_else(|why| panic!("{label}: no generalization: {why}"));
                    if let Some(dir) = &dump {
                        std::fs::write(
                            dir.join(format!(
                                "{}_generalized.smt2",
                                label.replace([' ', '(', ')'], "_")
                            )),
                            generate_smt2_query_raw(general.obligation(), &replay_config()),
                        )
                        .unwrap();
                    }
                    let started = std::time::Instant::now();
                    let generalized = request
                        .ay()
                        .verify_fresh_source_bound(&general, &replay_config());
                    eprintln!(
                        "X86_BODY_I128_MULO_QUALIFICATION generalized={label} result={generalized:?} \
                         ms={}",
                        started.elapsed().as_millis()
                    );
                    assert_eq!(
                        generalized,
                        AYResult::Verified,
                        "{label}: neither the exact theorem nor its generalization certifies"
                    );
                    uncertified.push((label, stable_outcome(&result), proof_gate_class(&result)));
                }
            }
        }
        uncertified
    });
    let qualified = assert_qualification_replayer(&edits);
    let uncertified = super::settle_here(
        uncertified,
        KNOWN_UNCERTIFIED_I128_MULO,
        "KNOWN_UNCERTIFIED_I128_MULO",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_I128_MULO,
        "KNOWN_UNCERTIFIED_I128_MULO",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified OD-224 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// Every wrong lowering of the division-free check (the carry dropped or
/// compared signed, the both-high test dropped, a cross product's high-half
/// test dropped, a sign read unsigned) is refuted by AY with a counterexample
/// on the qualification pair.
#[test]
fn host_qualification_refutes_every_division_free_wrong_lowering() {
    let test = "host_qualification_refutes_every_division_free_wrong_lowering";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        for (label, source, machine) in division_free_wrong_lowerings() {
            let owner = fixture_owner(&source, &machine)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let mut refuted = false;
            for (k, theorem) in owner.replayed_units().into_iter().enumerate() {
                if let Some(dir) = &dump {
                    std::fs::create_dir_all(dir).unwrap();
                    std::fs::write(
                        dir.join(format!("wrong_{}_{k}.smt2", label.replace(['/', '-'], "_"))),
                        generate_smt2_query_raw(theorem, &replay_config()),
                    )
                    .unwrap();
                }
                let started = std::time::Instant::now();
                let attributed =
                    crate::ay_bridge::verify_with_cli_raw_attributed(theorem, &replay_config());
                eprintln!(
                    "X86_BODY_I128_MULO_QUALIFICATION wrong={label} unit={k} result={:?} ms={}",
                    attributed.result,
                    started.elapsed().as_millis()
                );
                if matches!(attributed.result, AYResult::CounterExample(_)) {
                    refuted = true;
                    break;
                }
            }
            assert!(
                refuted,
                "{label}: AY must refute a wrong lowering's theorem with a counterexample"
            );
        }
    });
    assert_qualification_replayer(&edits);
}
