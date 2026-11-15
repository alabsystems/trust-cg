// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-8 x86-64 body
//! theorems (aggregates in general-purpose registers; tool-gated: the
//! admitted AY and a Clean checker). The fixtures, golden snapshots and
//! solver-free controls are in `slice8`, which the
//! `x86_source_bound_body::tests::slice8::` library gate runs; these tests
//! need the replayer pair their recorded outcomes were measured with.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice8::{SLICE_EIGHT, all_slice_eight_shapes, slice_eight_refutations, slice8_pair};
use super::*;

/// Slice-8 qualification cases whose canonical theorem the qualified AY/Clean
/// pair does NOT certify: a recorded replayer gap, never a credit route.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_EIGHT: &[Uncertified] = &[];

/// A diagnostic, not a check: every slice-8 fixture's LIR, machine rows and
/// theorem (or refusal). It lives here, outside the solver-free gate's
/// `slice8::` filter, which counts an ignored test as a skip.
#[test]
#[ignore]
fn print_slice_eight_fixtures() {
    for shape in all_slice_eight_shapes() {
        let (source, machine) = slice8_pair(shape);
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

/// The canonical slice-8 theorems, generated THROUGH THE REAL BUILDER,
/// replay on this host's admitted AY with a Clean-accepted proof (or are
/// recorded gaps with their exact outcome), and every wrong lowering is
/// refuted with a counterexample. The recorded gaps are compared only under
/// the replayer pair they were measured with
/// ([`assert_qualification_replayer`]).
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_eight_body_theorems() {
    let test = "host_qualification_replays_the_slice_eight_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in SLICE_EIGHT {
            let label = format!("{shape:?}");
            let (source, machine) = slice8_pair(shape);
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
                "X86_BODY_SLICE8_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_SLICE8_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label.clone(), stable_outcome(&result)));
            }
        }
        for (label, source, machine) in slice_eight_refutations() {
            let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let refuted =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_SLICE8_QUALIFICATION refutation={label} result={:?}",
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
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_EIGHT,
        "KNOWN_UNCERTIFIED_SLICE_EIGHT",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-8 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// With the real tools, every covered row of every certified slice-8 shape is
/// Formal under the body theorem (the parameter copies, the eightbyte loads
/// into and stores from the ABI registers included), the function is
/// promotable and its exports bind the ABI; a wrong lowering the Rust check
/// cannot judge fails every covered row.
#[test]
fn verifier_credits_every_bound_slice_eight_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_eight_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    // The per-host gap view this lane branches on was recorded with one
    // replayer pair: check the pair before the first replay.
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_EIGHT {
            let label = format!("{shape:?}");
            let (source, machine) = slice8_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if super::gap_applies_here(
                KNOWN_UNCERTIFIED_SLICE_EIGHT,
                "KNOWN_UNCERTIFIED_SLICE_EIGHT",
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
        for (label, source, machine) in slice_eight_refutations() {
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
