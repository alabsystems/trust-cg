// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-22 x86-64 body
//! theorems (the `i128` division class; tool-gated: the admitted AY and a
//! Clean checker). The fixtures and solver-free controls are in `slice22`,
//! which the `x86_source_bound_body::tests::slice22::` library gate runs.
//! Each test here is run in a process of its own (a session memo would
//! answer a sibling's queries otherwise).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice22::{
    Routine, SLICE_TWENTY_TWO, Shape22, cut_everywhere, fixture_module, fixture_owner,
    routine_pair, slice_twenty_two_refutations, slice22_owner, slice22_pair, wrong_multiplies,
};
use super::*;

/// Slice-22 qualification theorems the qualified AY/Clean pair does NOT
/// certify: recorded replayer gaps, never a credit route. `U128MulConst`
/// (`n - q * 10^16`): its product spells alike on both sides (OD-203), and
/// the claim left is the 128-bit difference's high half with the product's
/// high limb an atom, which AY 13556 bit-blasts (the slice-22 design's
/// `scalar_mul` finding, s19's A3); `div_rem_1e16` itself closes through
/// OD-204.
///
/// OD-224 (2026-11-03): the checked multiplies of two full operands are the
/// division-free limb check; their exact theorems state the two cross
/// products' `mul` rows, and AY 13556 computes UNSAT and rejects its own proof
/// in its strict certification on each (the class of slice 23's
/// `U64OverflowingPowLeaf`). Each one's OD-206 generalization certifies
/// ([`super::i128_mulo_qualification`]), so the production route credits
/// their rows (`verifier_credits_every_bound_slice_twenty_two_row_...`).
pub(crate) const KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO: &[Uncertified] = &[
    Uncertified {
        label: "U128CheckedMul",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: OD224_SELF_CHECK,
    },
    Uncertified {
        label: "I128OverflowingMul",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: OD224_SELF_CHECK,
    },
    Uncertified {
        label: "U128MulConst",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: "ay: no answer within the 30 s deadline; offline with a 300 s budget, \
             `unsat` after 88.8 s with a strict certificate Clean accepts in 1.5 s (2026-10-27, \
             load 1.9)",
    },
    Uncertified {
        label: "U128MulAcrossCut",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: OD224_SELF_CHECK,
    },
    Uncertified {
        label: "U128MulAcrossCut cut part 1",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: OD224_SELF_CHECK,
    },
    Uncertified {
        label: "U128MulZextOperand",
        outcome: SELF_CHECK_REJECTED,
        proof_gate_class: "SOUNDNESS",
        tool_output: OD224_SELF_CHECK,
    },
];

/// The recorded exact gaps whose OD-206 generalization the qualified pair
/// certifies (OD-224), so that the production route credits their rows
/// (measured on AY 13556 with Clean 5f09e36c,
/// `host_qualification_replays_the_generalizations_of_slice_twenty_two_s_checked_multiplies`).
const GENERALIZATION_CREDITED_HERE: [Shape22; 4] = [
    Shape22::U128CheckedMul,
    Shape22::I128OverflowingMul,
    Shape22::U128MulAcrossCut,
    Shape22::U128MulZextOperand,
];

/// AY's answer to the exact theorem of each slice-22 checked multiply after
/// OD-224 (measured 2026-11-03 on AY 13556 with Clean 5f09e36c, load 2.4-2.7).
const OD224_SELF_CHECK: &str = "ay computes UNSAT in 0.6-1.2 s and rejects its own proof in its \
     mandatory strict certification (`(:reason-unknown (incomplete self-check-rejected))`); its \
     OD-206 generalization certifies in 0.4-1.5 s";

/// A diagnostic, not a check: every slice-22 fixture's LIR, machine rows and
/// theorem (or refusal), and every wrong lowering's machine rows.
#[test]
#[ignore]
fn print_slice_twenty_two_fixtures() {
    for shape in SLICE_TWENTY_TWO {
        let (source, machine) = slice22_pair(shape);
        println!(
            "==== {shape:?}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        match fixture_owner(&source, &machine) {
            Ok(owner) => println!(
                "{}",
                generate_smt2_query_raw(owner.obligation(), &replay_config())
            ),
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
    for (label, _, machine) in slice_twenty_two_refutations()
        .into_iter()
        .chain(wrong_multiplies())
    {
        println!("==== {label} (wrong lowering)\n{}", describe(&machine));
    }
}

/// The slice-22 theorems, generated THROUGH THE REAL BUILDER, replay on this
/// host's admitted AY with a Clean-accepted proof (or are recorded gaps with
/// their exact outcome). No correct lowering is refuted.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_twenty_two_body_theorems() {
    let test = "host_qualification_replays_the_slice_twenty_two_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        let mut theorems: Vec<(String, ProofObligation)> = Vec::new();
        for shape in SLICE_TWENTY_TWO {
            let label = format!("{shape:?}");
            let (source, machine) = slice22_pair(shape);
            let owner = fixture_owner(&source, &machine)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let units = owner.replayed_units();
            let single = units.len() == 1;
            for (k, unit) in units.into_iter().enumerate() {
                let label = if single {
                    label.clone()
                } else {
                    format!("{label} part {}", k + 1)
                };
                theorems.push((label, unit.clone()));
            }
            // The shapes the library gate also states in parts at every
            // block: every part.
            if cut_everywhere(shape) {
                let cut = slice22_owner(shape, &source, &machine)
                    .unwrap_or_else(|refusal| panic!("{label} (cut): {refusal}"));
                for (k, part) in cut.parts().iter().enumerate() {
                    theorems.push((format!("{label} cut part {}", k + 1), part.clone()));
                }
            }
        }
        for (label, theorem) in theorems {
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("{}.smt2", label.replace([' ', '(', ')'], "_"))),
                    generate_smt2_query_raw(&theorem, &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let result = request.ay().verify_fresh_source_bound(
                &X86BodyPart {
                    obligation: &theorem,
                },
                &replay_config(),
            );
            eprintln!(
                "X86_BODY_SLICE22_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_SLICE22_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label, stable_outcome(&result), proof_gate_class(&result)));
            }
        }
        uncertified
    });
    let qualified = assert_qualification_replayer(&edits);
    let uncertified = super::settle_here(
        uncertified,
        KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-22 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// Every slice-22 wrong lowering, and every wrong 128-bit multiply under
/// OD-203's spelling, is refuted by AY with a counterexample on the
/// qualification pair.
#[test]
fn host_qualification_refutes_every_slice_twenty_two_wrong_lowering() {
    let test = "host_qualification_refutes_every_slice_twenty_two_wrong_lowering";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        for (label, source, machine) in slice_twenty_two_refutations()
            .into_iter()
            .chain(wrong_multiplies())
        {
            let owner = fixture_owner(&source, &machine)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let units = owner.replayed_units();
            let mut refuted = false;
            for (k, theorem) in units.into_iter().enumerate() {
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
                    "X86_BODY_SLICE22_QUALIFICATION wrong={label} unit={k} result={:?} ms={}",
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

/// With the real tools, every covered row of every certified slice-22 shape
/// is Formal under the replayed body theorem (the routine's `call` row and
/// its argument and result moves included), the function is promotable and
/// its exports bind the ABI; a wrong lowering is never credited.
#[test]
fn verifier_credits_every_bound_slice_twenty_two_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_twenty_two_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_TWENTY_TWO {
            let label = format!("{shape:?}");
            let (source, machine) = slice22_pair(shape);
            let owner = fixture_owner(&source, &machine)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let module = fixture_module(&source);
            let (report, exports) = verifier.verify_with_request_for_export_in_module(
                &machine,
                Some(&source),
                SYSV,
                &module,
                &request,
            );
            // A recorded exact gap whose generalization certifies here is
            // credited through it (OD-206; OD-224's checked multiplies).
            let generalized = GENERALIZATION_CREDITED_HERE.contains(&shape)
                && super::gap_applies_here(
                    KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO,
                    "KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO",
                    &label,
                    &qualified,
                );
            if !generalized
                && super::gap_branch_here(
                    KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO,
                    "KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO",
                    &label,
                    covered_rows_matching(&owner, report.report(), is_needs_replay),
                    &qualified,
                )
            {
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
            assert!(report.matches_x86_input_in_module(
                &machine,
                Some(&source),
                SYSV,
                Some(&module)
            ));
        }
        for (label, source, machine) in slice_twenty_two_refutations()
            .into_iter()
            .chain(wrong_multiplies())
        {
            let Ok(owner) = fixture_owner(&source, &machine) else {
                continue;
            };
            let (report, exports) = verifier.verify_with_request_for_export_in_module(
                &machine,
                Some(&source),
                SYSV,
                &fixture_module(&source),
                &request,
            );
            let credited = covered_rows_matching(&owner, report.report(), is_body_credit);
            assert_eq!(credited, 0, "{label}: {:?}", report.report());
            assert!(exports.is_empty(), "{label}");
        }
    });
}

/// OD-210 (the review of slice 22), with the real tools. Beside the module's
/// own `__udivti3` (returning 0), `div`'s theorem as the owner stated it
/// before OD-210 replays Valid: the verifier then credited every covered row
/// Formal although every quotient is 0. So does a circular `__udivti3`'s own
/// theorem. Now the verifier, naming the module, credits no row and exports
/// nothing for either; a module that only declares the routine keeps the
/// credit.
#[test]
fn verifier_credits_no_row_whose_routine_the_module_defines() {
    let test = "verifier_credits_no_row_whose_routine_the_module_defines";
    let edits = replay_environment(test);
    // This regression reads no recorded qualification outcome: it checks
    // fresh proofs and credits below, so the admitted replay pair is enough.
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for (routine, name) in [
            (Routine::DefinedZero, "div"),
            (Routine::Circular, "__udivti3"),
            (Routine::Circular, "div"),
        ] {
            let label = format!("{routine:?} {name}");
            let (source, machine, definitions) = routine_pair(routine, name);
            let unchecked = build_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label} before OD-210: {refusal}"));
            for unit in unchecked.replayed_units() {
                let result = request
                    .ay()
                    .verify_fresh_source_bound(&X86BodyPart { obligation: unit }, &replay_config());
                eprintln!("X86_BODY_SLICE22_OD210 {label} before={result:?}");
                assert_eq!(
                    result,
                    AYResult::Verified,
                    "{label}: the theorem stated before OD-210 replays Valid"
                );
            }
            let (report, exports) = verifier.verify_with_request_for_export_in_module(
                &machine,
                Some(&source),
                SYSV,
                &definitions,
                &request,
            );
            let credited = covered_rows_matching(&unchecked, report.report(), is_body_credit);
            eprintln!(
                "X86_BODY_SLICE22_OD210 {label} after: {credited} of {} covered rows credited",
                unchecked.bound_rows().len()
            );
            assert_eq!(credited, 0, "{label}: {:?}", report.report());
            assert!(exports.is_empty(), "{label}");
        }
        let (source, machine, definitions) = routine_pair(Routine::Declared, "div");
        let owner = source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&definitions))
            .unwrap_or_else(|refusal| panic!("a declared __udivti3: {refusal}"));
        let (report, exports) = verifier.verify_with_request_for_export_in_module(
            &machine,
            Some(&source),
            SYSV,
            &definitions,
            &request,
        );
        for row in &report.report().instructions {
            if owner.covers(row.inst_index) {
                assert!(
                    is_body_credit(&row.result),
                    "a declared __udivti3: row {} {:?}: {:?}",
                    row.inst_index,
                    row.opcode,
                    row.result
                );
            }
        }
        assert_eq!(exports.len(), owner.bound_rows().len());
    });
}
