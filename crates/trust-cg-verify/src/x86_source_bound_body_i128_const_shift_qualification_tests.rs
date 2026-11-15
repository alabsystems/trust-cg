// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the x86-64 body theorems of the
//! constant-amount `I128` shift fold (ruling OD-215; tool-gated: the
//! admitted AY and a Clean checker). The fixtures, golden snapshots and
//! solver-free controls are in `i128_const_shift`, which the
//! `x86_source_bound_body::tests::i128_const_shift::` library gate runs. Each
//! test here is run in a process of its own (a session memo would answer a
//! sibling's queries otherwise).

use super::i128_const_shift::{const_shift_fixtures, const_shift_pair, const_shift_refutations};
use super::slice5::describe;
use super::slice6::describe_lir;
use super::*;

/// Constant-shift qualification cases whose canonical theorem the qualified
/// AY/Clean pair does NOT certify: a recorded replayer gap, never a credit
/// route. Empty: every fixture certifies on the qualification host.
pub(crate) const KNOWN_UNCERTIFIED_I128_CONST_SHIFT: &[Uncertified] = &[];

/// A diagnostic, not a check: every fixture's LIR, machine rows and theorem
/// (or refusal).
#[test]
#[ignore]
fn print_i128_const_shift_fixtures() {
    for shape in const_shift_fixtures() {
        let (source, machine) = const_shift_pair(shape);
        println!(
            "==== {}\n{}{}",
            shape.label(),
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

/// Every constant-shift theorem, generated THROUGH THE REAL BUILDER, replays
/// on this host's admitted AY with a Clean-accepted proof (or is a recorded
/// gap with its exact outcome), and every wrong lowering (a wrong half, a
/// wrong fill, an amount off by one) is refuted with a counterexample.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_i128_const_shift_body_theorems() {
    let test = "host_qualification_replays_the_i128_const_shift_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in const_shift_fixtures() {
            let label = shape.label();
            let (source, machine) = const_shift_pair(shape);
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
                "X86_BODY_I128_CONST_SHIFT_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_I128_CONST_SHIFT_QUALIFICATION gap={label} outcome={} \
                     proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label.clone(), stable_outcome(&result)));
            }
        }
        for (label, source, machine) in const_shift_refutations() {
            let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            if let Some(dir) = &dump {
                let smt2 = generate_smt2_query_raw(&theorem, &replay_config());
                std::fs::write(
                    dir.join(format!("refutation_{}.smt2", label.replace('/', "__"))),
                    smt2,
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let refuted =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_I128_CONST_SHIFT_QUALIFICATION refutation={label} result={:?} ms={}",
                refuted.result,
                started.elapsed().as_millis()
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
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_I128_CONST_SHIFT,
        "KNOWN_UNCERTIFIED_I128_CONST_SHIFT",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified constant-shift set changed on this host: update the recorded replayer \
         gaps (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// With the real tools, every covered row of every certified constant-shift
/// fixture is Formal under the body theorem (the immediate shifts, the `or`
/// and the moves included), the function is promotable and its exports bind
/// the ABI; a wrong lowering the Rust check cannot judge fails every covered
/// row.
#[test]
fn verifier_credits_every_bound_i128_const_shift_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_i128_const_shift_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in const_shift_fixtures() {
            let label = shape.label();
            let (source, machine) = const_shift_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if super::gap_applies_here(
                KNOWN_UNCERTIFIED_I128_CONST_SHIFT,
                "KNOWN_UNCERTIFIED_I128_CONST_SHIFT",
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
        for (label, source, machine) in const_shift_refutations() {
            let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) else {
                continue;
            };
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            // Every covered row fails: under the refuted body theorem, or (a
            // mutant that changes a row's opcode class) first under the TV-2
            // provenance cross-check of that row.
            assert_eq!(
                covered_rows_matching(&owner, report.report(), |result| matches!(
                    result,
                    InstructionVerificationResult::Failed { .. }
                )),
                owner.bound_rows().len(),
                "{label}: {:?}",
                report.report()
            );
            assert!(exports.is_empty(), "{label}");
        }
    });
}
