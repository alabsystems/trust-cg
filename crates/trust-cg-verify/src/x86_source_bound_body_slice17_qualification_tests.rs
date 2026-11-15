// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-17 x86-64 body
//! theorems (indexed private accesses, dead header bytes; tool-gated: the
//! admitted AY and a Clean checker). The fixtures and solver-free controls
//! are in `slice17`, which the `x86_source_bound_body::tests::slice17::`
//! library gate runs. Each test here is run in a process of its own (a
//! session memo would answer a sibling's queries otherwise).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice17::{
    SLICE_SEVENTEEN, slice_seventeen_machine_variants, slice_seventeen_refutations, slice17_pair,
};
use super::slice22::{fixture_module, fixture_owner};
use super::*;

/// Slice-17 qualification cases whose canonical theorem the qualified
/// AY/Clean pair does NOT certify: recorded replayer gaps, never a credit
/// route.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_SEVENTEEN: &[Uncertified] = &[];

/// A diagnostic, not a check: every slice-17 fixture's LIR, machine rows and
/// theorem (or refusal).
#[test]
#[ignore]
fn print_slice_seventeen_fixtures() {
    for shape in SLICE_SEVENTEEN {
        let (source, machine) = slice17_pair(shape);
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
}

/// The canonical slice-17 theorems, generated THROUGH THE REAL BUILDER,
/// replay on this host's admitted AY with a Clean-accepted proof (or are
/// recorded gaps with their exact outcome). The selects they state have 4
/// to 256 arms (`NarrowIndex`'s 256-byte table).
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_seventeen_body_theorems() {
    let test = "host_qualification_replays_the_slice_seventeen_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        let cases = SLICE_SEVENTEEN
            .iter()
            .map(|shape| {
                let (source, machine) = slice17_pair(*shape);
                (format!("{shape:?}"), source, machine)
            })
            .chain(
                slice_seventeen_machine_variants()
                    .into_iter()
                    .map(|(label, source, machine)| (label.to_owned(), source, machine)),
            );
        for (label, source, machine) in cases {
            let owner = fixture_owner(&source, &machine)
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
                "X86_BODY_SLICE17_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_SLICE17_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label.clone(), stable_outcome(&result)));
            }
        }
        uncertified
    });
    let qualified = assert_qualification_replayer(&edits);
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_SEVENTEEN,
        "KNOWN_UNCERTIFIED_SLICE_SEVENTEEN",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-17 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// Every slice-17 wrong lowering is refuted by AY with a counterexample (the
/// out-of-bounds source's theorem built without the bound finder).
#[test]
fn host_qualification_refutes_every_slice_seventeen_mis_model() {
    let test = "host_qualification_refutes_every_slice_seventeen_mis_model";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        for (label, source, machine, unbounded) in slice_seventeen_refutations() {
            let theorem = if unbounded {
                theorem_without_indexed_bounds(&source, &machine, SYSV)
            } else {
                theorem_without_affine_refusal(&source, &machine, SYSV)
            }
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                let smt2 = generate_smt2_query_raw(&theorem, &replay_config());
                std::fs::write(
                    dir.join(format!(
                        "refutation_{}.smt2",
                        label.replace([' ', '/', '(', ')', '=', '<'], "_")
                    )),
                    smt2,
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let refuted =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_SLICE17_QUALIFICATION refutation={label} result={:?} ms={}",
                refuted.result,
                started.elapsed().as_millis()
            );
            assert!(
                matches!(refuted.result, AYResult::CounterExample(_)),
                "{label} must be refuted: {:?}",
                refuted.result
            );
        }
    });
    assert_qualification_replayer(&edits);
}

/// With the real tools, every covered row of every certified slice-17 shape
/// is Formal under the body theorem, the function is promotable and its
/// exports bind the ABI; a wrong lowering fails every covered row.
#[test]
fn verifier_credits_every_bound_slice_seventeen_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_seventeen_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    // The per-host gap view this lane branches on was recorded with one
    // replayer pair: check the pair before the first replay.
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_SEVENTEEN {
            let label = format!("{shape:?}");
            let (source, machine) = slice17_pair(shape);
            let owner = fixture_owner(&source, &machine).unwrap();
            let (report, exports) = verifier.verify_with_request_for_export_in_module(
                &machine,
                Some(&source),
                SYSV,
                &fixture_module(&source),
                &request,
            );
            if super::gap_applies_here(
                KNOWN_UNCERTIFIED_SLICE_SEVENTEEN,
                "KNOWN_UNCERTIFIED_SLICE_SEVENTEEN",
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
            assert!(report.matches_x86_input_in_module(
                &machine,
                Some(&source),
                SYSV,
                Some(&fixture_module(&source))
            ));
        }
        for (label, source, machine, _) in slice_seventeen_refutations() {
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
