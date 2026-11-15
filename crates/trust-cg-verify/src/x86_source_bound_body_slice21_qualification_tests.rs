// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-21 x86-64 body
//! theorems (floating-point operations as paired rounding events, the
//! saturating conversion, an abstract theorem's satisfying model, the `I128`
//! atomic load and the atomic exchange; tool-gated: the admitted AY and a
//! Clean checker). The fixtures and solver-free controls are in `slice21`,
//! which the `x86_source_bound_body::tests::slice21::` library gate runs.
//! Each test here is run in a process of its own (a session memo would
//! answer a sibling's queries otherwise).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice16::{cut_at, every_block};
use super::slice21::{
    Control21, Expect21, SLICE_TWENTY_ONE_VARIANTS, region_fixtures, slice_twenty_one,
    slice_twenty_one_controls, slice21_pair, variant_pair,
};
use super::*;

/// Slice-21 qualification theorems the qualified AY/Clean pair does NOT
/// certify: recorded replayer gaps, never a credit route. Empty: every
/// fixture's theorem certifies on the pair (see the slice-21 report).
pub(crate) const KNOWN_UNCERTIFIED_SLICE_TWENTY_ONE: &[Uncertified] = &[];

/// A diagnostic, not a check: every slice-21 fixture's LIR, machine rows and
/// theorem, and every control's.
#[test]
#[ignore]
fn print_slice_twenty_one_fixtures() {
    for shape in slice_twenty_one() {
        let (source, machine) = slice21_pair(shape);
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
    for variant in SLICE_TWENTY_ONE_VARIANTS {
        let (source, machine) = variant_pair(variant);
        println!(
            "==== {variant:?} (variant)\n{}{}",
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
    for Control21 {
        label,
        source,
        machine,
        expect,
    } in slice_twenty_one_controls()
    {
        println!("==== {label} (control, {expect:?})\n{}", describe(&machine));
        match source_bound_x86_body(&source, &machine, SYSV) {
            Ok(owner) => println!(
                "{}",
                generate_smt2_query_raw(owner.obligation(), &replay_config())
            ),
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
}

/// The canonical slice-21 theorems, generated THROUGH THE REAL BUILDER,
/// replay on this host's admitted AY with a Clean-accepted proof (or are
/// recorded gaps with their exact outcome). No correct lowering is refuted.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_twenty_one_body_theorems() {
    let test = "host_qualification_replays_the_slice_twenty_one_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        // The fixtures, then the region fixtures as the production owner
        // states them and every part of each cut at every block.
        let mut theorems: Vec<(String, ProofObligation)> = Vec::new();
        for shape in slice_twenty_one() {
            let label = format!("{shape:?}");
            let (source, machine) = slice21_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            theorems.push((label, owner.obligation().clone()));
        }
        for (source, machine) in region_fixtures() {
            let name = source.name.clone();
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{name}: {refusal}"));
            let units = owner.replayed_units();
            let single = units.len() == 1;
            for (k, unit) in units.into_iter().enumerate() {
                let label = if single {
                    name.clone()
                } else {
                    format!("{name} production part {}", k + 1)
                };
                theorems.push((label, unit.clone()));
            }
            let cut = source_bound_x86_body_in_parts(
                &source,
                &machine,
                SYSV,
                &cut_at(every_block(&source)),
            )
            .unwrap_or_else(|refusal| panic!("{name} (cut): {refusal}"));
            for (k, part) in cut.parts().iter().enumerate() {
                theorems.push((format!("{name} cut part {}", k + 1), part.clone()));
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
                "X86_BODY_SLICE21_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_SLICE21_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
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
        KNOWN_UNCERTIFIED_SLICE_TWENTY_ONE,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_ONE",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_TWENTY_ONE,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_ONE",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-21 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// Every slice-21 control on the qualification pair: a pure bit-vector one
/// (no FP leaf) is refuted by AY with a counterexample; an FP-abstract one is
/// satisfiable (AY finds a model of its negation), which the verifier
/// reports as no counterexample (OD-200); a refused one builds no theorem.
#[test]
fn host_qualification_refutes_or_leaves_uncredited_every_slice_twenty_one_mis_model() {
    let test = "host_qualification_refutes_or_leaves_uncredited_every_slice_twenty_one_mis_model";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        for Control21 {
            label,
            source,
            machine,
            expect,
        } in slice_twenty_one_controls()
        {
            let outcome = source_bound_x86_body(&source, &machine, SYSV);
            let owner = match (expect, outcome) {
                (Expect21::Refused(needle), Err(X86BodyRefusal::Unsupported(reason))) => {
                    let reason = reason.to_string();
                    assert!(reason.contains(needle), "{label}: {reason}");
                    eprintln!("X86_BODY_SLICE21_QUALIFICATION control={label} refused={reason}");
                    continue;
                }
                (Expect21::Refuted | Expect21::Uncredited, Ok(owner)) => owner,
                (expect, outcome) => panic!(
                    "{label}: expected {expect:?}, got {:?}",
                    outcome.map(|_| "a theorem")
                ),
            };
            let theorem = owner.obligation();
            assert_eq!(
                owner.is_fp_abstract(),
                expect == Expect21::Uncredited,
                "{label}"
            );
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("control_{}.smt2", label.replace(['/', '-'], "_"))),
                    generate_smt2_query_raw(theorem, &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let attributed =
                crate::ay_bridge::verify_with_cli_raw_attributed(theorem, &replay_config());
            eprintln!(
                "X86_BODY_SLICE21_QUALIFICATION control={label} expect={expect:?} result={:?} \
                 ms={}",
                attributed.result,
                started.elapsed().as_millis()
            );
            assert!(
                matches!(attributed.result, AYResult::CounterExample(_)),
                "{label}: AY must satisfy the negation of a wrong lowering's theorem: {:?}",
                attributed.result
            );
        }
    });
    assert_qualification_replayer(&edits);
}

/// With the real tools, every covered row of every certified slice-21 shape
/// is Formal under the replayed body theorem, the function is promotable and
/// its exports bind the ABI; every control the owner binds leaves its rows
/// failed (a pure bit-vector refutation) or uncredited with the FP
/// abstraction's reason (OD-200), never credited.
#[test]
fn verifier_credits_every_bound_slice_twenty_one_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_twenty_one_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in slice_twenty_one() {
            let label = format!("{shape:?}");
            let (source, machine) = slice21_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if super::gap_branch_here(
                KNOWN_UNCERTIFIED_SLICE_TWENTY_ONE,
                "KNOWN_UNCERTIFIED_SLICE_TWENTY_ONE",
                &label,
                covered_rows_matching(&owner, report.report(), is_needs_replay),
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
        let abstract_sat = |result: &InstructionVerificationResult| {
            matches!(
                result,
                InstructionVerificationResult::Unverified { reason }
                    if reason == crate::x86_64_function_verifier::X86_BODY_FP_ABSTRACT_SAT
            )
        };
        for Control21 {
            label,
            source,
            machine,
            expect,
        } in slice_twenty_one_controls()
        {
            let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) else {
                continue;
            };
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            // A row the body theorem fails, and a row it credits.
            let refuted = covered_rows_matching(&owner, report.report(), |result| {
                matches!(
                    result,
                    InstructionVerificationResult::Failed { proof_name, .. }
                        if proof_name == X86_BODY_OBLIGATION_NAME
                )
            });
            let credited = covered_rows_matching(&owner, report.report(), is_body_credit);
            let uncredited = covered_rows_matching(&owner, report.report(), abstract_sat);
            assert_eq!(credited, 0, "{label}: {:?}", report.report());
            match expect {
                Expect21::Refuted => assert_eq!(
                    refuted,
                    owner.bound_rows().len(),
                    "{label}: {:?}",
                    report.report()
                ),
                // Every covered row uncredited by OD-200, or failed by another
                // check (the signed-only control's `cvtsi2sd` carries the
                // stamp of the signed conversion it was selected from, which
                // TV-2's digest check fails), never refuted by the theorem.
                _ => {
                    assert_eq!(refuted, 0, "{label}: {:?}", report.report());
                    assert!(uncredited > 0, "{label}: {:?}", report.report());
                }
            }
            assert!(exports.is_empty(), "{label}");
        }
    });
}
