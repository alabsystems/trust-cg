// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-23 x86-64 body
//! theorems (arithmetic congruence pairing, OD-205; the generalization over
//! arithmetic leaves, OD-206; tool-gated: the admitted AY and a Clean
//! checker). The fixtures and solver-free controls are in `slice23`, which
//! the `x86_source_bound_body::tests::slice23::` library gate runs. Each test
//! here is run in a process of its own (a session memo would answer a
//! sibling's queries otherwise).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice23::{SLICE_TWENTY_THREE, Shape23, slice_twenty_three_refutations, slice23_pair};
use super::*;

/// Slice-23 qualification theorems the qualified AY/Clean pair does NOT
/// certify by their exact replay: recorded replayer gaps, never a credit
/// route by themselves. Three of them are credited through OD-206's
/// generalization ([`GENERALIZATION_CREDITED_HERE`]); u8 `carrying_mul_add`'s
/// generalization is satisfiable (it needs the product's range), so its rows
/// stay unverified on this host, never refuted.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE: &[Uncertified] = &[
    Uncertified {
        label: "SremPaired",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: SREM_PAIRED_OFFLINE,
    },
    Uncertified {
        label: "U64OverflowingPowLeaf",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: OVERFLOWING_POW_OFFLINE,
    },
    Uncertified {
        label: "ScalarMulLeaf",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: SCALAR_MUL_OFFLINE,
    },
    Uncertified {
        label: "U8CarryingMulAdd",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: U8_CARRYING_MUL_ADD_OFFLINE,
    },
];

/// `AY`'s answer to `SremPaired`'s exact theorem (an `idiv` the pairing
/// never pairs: AY bit-blasts two 64-bit signed remainders).
const SREM_PAIRED_OFFLINE: &str = "ay: no answer within the 30 s deadline; offline with a 300 s budget, \
     still no answer (`(:reason-unknown timeout)` at 300.2 s, 2026-10-28, load 4.2)";
/// `AY`'s answer to `U64OverflowingPowLeaf`'s exact theorem (two 128-bit
/// widening products, one term on both sides: the real root's census stop).
const OVERFLOWING_POW_OFFLINE: &str = "ay computes UNSAT in 0.5 s and rejects its own proof in its mandatory \
     strict certification (`(:reason-unknown (incomplete self-check-rejected))`; offline \
     the same in 0.6 s, 2026-10-28, load 5.4)";
/// `AY`'s answer to `ScalarMulLeaf`'s exact theorem (the 128-bit product's
/// three 64-bit multipliers: the real root's census stop).
const SCALAR_MUL_OFFLINE: &str = "ay: no answer within the 30 s deadline; offline with a 300 s budget, \
     `unsat` after 59.4 s with a strict certificate Clean accepts in 6.9 s (2026-10-28, load \
     5.2)";
/// `AY`'s answer to `U8CarryingMulAdd`'s exact theorem (the selector's
/// 32-bit `imul` of the zero-extended bytes against the source's 16-bit
/// product: two keys, not paired).
const U8_CARRYING_MUL_ADD_OFFLINE: &str = "ay: no answer within the 30 s deadline; offline with a 300 s budget it \
     computes UNSAT after 57.4 s and rejects its own proof in its mandatory strict \
     certification (`(:reason-unknown (incomplete self-check-rejected))`, 2026-10-28, load 5.3)";

/// The recorded gaps whose generalization (OD-206) the qualified pair
/// certifies, so that the production route credits their rows with a
/// generalization record (measured on AY 13556 with Clean 5f09e36c).
const GENERALIZATION_CREDITED_HERE: [Shape23; 3] = [
    Shape23::SremPaired,
    Shape23::U64OverflowingPowLeaf,
    Shape23::ScalarMulLeaf,
];

/// The complete diagnostic printer stays outside the solver-free gate's
/// selected module, so that gate selects only executable checks. The
/// diagnostic remains available explicitly with `--ignored`.
#[test]
#[ignore]
fn print_slice_twenty_three_fixtures() {
    super::slice23::print_slice_twenty_three_fixtures();
}

/// A diagnostic, not a check: every slice-23 fixture's LIR, machine rows and
/// theorem (or refusal).
#[test]
#[ignore]
fn print_slice_twenty_three_qualification_fixtures() {
    for shape in SLICE_TWENTY_THREE {
        let (source, machine) = slice23_pair(shape);
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

/// The slice-23 theorems, generated THROUGH THE REAL BUILDER (OD-205's
/// pairing on), replay on this host's admitted AY with a Clean-accepted proof
/// (or are recorded gaps with their exact outcome). No correct lowering is
/// refuted.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_twenty_three_body_theorems() {
    let test = "host_qualification_replays_the_slice_twenty_three_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in SLICE_TWENTY_THREE {
            let label = format!("{shape:?}");
            let (source, machine) = slice23_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
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
                    "X86_BODY_SLICE23_QUALIFICATION shape={label} result={result:?} ms={}",
                    started.elapsed().as_millis()
                );
                assert!(
                    !matches!(result, AYResult::CounterExample(_)),
                    "{label}: a correct lowering was refuted: {result:?}"
                );
                if result != AYResult::Verified {
                    eprintln!(
                        "X86_BODY_SLICE23_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                        stable_outcome(&result),
                        proof_gate_class(&result)
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
        KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-23 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// The generalizations of the slice-23 leaf shapes (OD-206) on the
/// qualification pair: `overflowing_pow`'s and `scalar_mul`'s shapes
/// certify (`align_offset`'s paired theorem states no arithmetic node); u8
/// `carrying_mul_add`'s is SATISFIABLE (its claim needs the product's range),
/// which is why a generalization never refutes and never replaces the exact
/// theorem, which certifies.
#[test]
fn host_qualification_replays_the_slice_twenty_three_generalizations() {
    let test = "host_qualification_replays_the_slice_twenty_three_generalizations";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        for (shape, expected) in [
            (Shape23::SremPaired, "Verified"),
            (Shape23::U64OverflowingPowLeaf, "Verified"),
            (Shape23::ScalarMulLeaf, "Verified"),
            (Shape23::U8CarryingMulAdd, "CounterExample"),
        ] {
            let label = format!("{shape:?}");
            let (source, machine) = slice23_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let general = owner
                .replay_generalized(0)
                .unwrap_or_else(|why| panic!("{label}: no generalization: {why}"));
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("{label}_generalized.smt2")),
                    generate_smt2_query_raw(general.obligation(), &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let result = request
                .ay()
                .verify_fresh_source_bound(&general, &replay_config());
            eprintln!(
                "X86_BODY_SLICE23_QUALIFICATION generalized={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            let outcome = match &result {
                AYResult::Verified => "Verified",
                AYResult::CounterExample(_) => "CounterExample",
                _ => "other",
            };
            assert_eq!(outcome, expected, "{label}: {result:?}");
        }
    });
    assert_qualification_replayer(&edits);
}

/// Every slice-23 wrong lowering is refuted by AY with a counterexample on
/// the qualification pair (the exact spelling, the pairing on).
#[test]
fn host_qualification_refutes_every_slice_twenty_three_wrong_lowering() {
    let test = "host_qualification_refutes_every_slice_twenty_three_wrong_lowering";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        for (label, source, machine) in slice_twenty_three_refutations() {
            let owner = source_bound_x86_body(&source, &machine, SYSV)
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
                    "X86_BODY_SLICE23_QUALIFICATION wrong={label} unit={k} result={:?} ms={}",
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

/// With the real tools, every covered row of every certified slice-23 shape
/// is Formal under the replayed body theorem through the production route
/// (the exact replay first; a generalization only after it has no
/// verdict); a wrong lowering is never credited.
#[test]
fn verifier_credits_every_bound_slice_twenty_three_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_twenty_three_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_TWENTY_THREE {
            let label = format!("{shape:?}");
            let (source, machine) = slice23_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            // A recorded exact gap whose generalization certifies here is
            // credited through it (OD-206), with its record.
            let generalized = GENERALIZATION_CREDITED_HERE.contains(&shape)
                && super::gap_applies_here(
                    KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE,
                    "KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE",
                    &label,
                    &qualified,
                );
            if !generalized
                && super::gap_branch_here(
                    KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE,
                    "KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE",
                    &label,
                    covered_rows_matching(&owner, report.report(), is_needs_replay),
                    &qualified,
                )
            {
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
            for export in &exports {
                // Every record re-derives; a generalization is recorded
                // exactly where the exact theorem is a recorded gap; a
                // paired theorem's export carries its pairing record, which
                // re-derives it (OD-205).
                assert!(export.check_x86_body_claims().is_ok(), "{label}");
                assert!(export.check_x86_body_pairing().is_ok(), "{label}");
                assert_eq!(
                    export.x86_body_pairing().is_some(),
                    export.is_x86_body_paired(),
                    "{label}"
                );
                if export.obligation() == owner.obligation() {
                    assert_eq!(export.is_x86_body_paired(), owner.is_paired(), "{label}");
                }
                let recorded = export
                    .x86_body_claims()
                    .is_some_and(|record| record.generalized_of(0).is_some());
                assert_eq!(
                    recorded,
                    generalized,
                    "{label}: {:?}",
                    export.x86_body_claims()
                );
            }
            assert!(report.matches_x86_input(&machine, Some(&source), SYSV));
        }
        for (label, source, machine) in slice_twenty_three_refutations() {
            let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) else {
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
