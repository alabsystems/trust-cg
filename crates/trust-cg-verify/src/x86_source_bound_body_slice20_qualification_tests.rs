// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-20 x86-64 body
//! theorems (a switch's binary-search blocks, a stored address dead at a
//! join, `I128` items as two halves, the singleton rules and the bounds;
//! tool-gated: the admitted AY and a Clean checker). The fixtures and
//! solver-free controls are in `slice20`, which the
//! `x86_source_bound_body::tests::slice20::` library gate runs. Each test here
//! is run in a process of its own (a session memo would answer a sibling's
//! queries otherwise).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice16::{cut_at, every_block};
use super::slice20::{
    SLICE_TWENTY, SLICE_TWENTY_VARIANTS, cut_everywhere, refutation_obligations,
    slice_twenty_refutations, slice20_owner, slice20_pair, variant_pair,
};
use super::*;

/// Slice-20 qualification theorems (`<shape>`, or `<shape> part <k>` for one
/// stated in parts) the qualified AY/Clean pair does NOT certify: recorded
/// replayer gaps, never a credit route.
///
/// Empty since slice 19's spelling (OD-195..197). Slice 20 recorded two: the
/// production owner's one-query theorems of `U128LiveAcrossCut` and
/// `U128CutParam` (slice 11's `I128` arithmetic in one query), where AY build
/// 13556 proved the theorem and Clean 5f09e36c rejected one `equiv_simplify`
/// step of the proof it printed (`carcara error: checking failed on step
/// 't1.packed.13410'` / `'t1.packed.10931'`, the slice-20 design's
/// `full_div_rem` class). Re-spelled, both certify (3.8 s and 0.2 s, one test
/// per process, 2026-10-26,
/// `reports/perf/2026-10-26-darwin-x86-64-slice19-spelling/`). The three
/// variable `I128` shifts are deadline-bound on the Darwin x86-64 host
/// (`DEADLINE_BOUND_HERE_BY_HOST`).
pub(crate) const KNOWN_UNCERTIFIED_SLICE_TWENTY: &[Uncertified] = &[];

/// A diagnostic, not a check: every slice-20 fixture's LIR, machine rows and
/// theorem (every part of one stated in parts), or refusal.
#[test]
#[ignore]
fn print_slice_twenty_fixtures() {
    for shape in SLICE_TWENTY {
        let (source, machine) = slice20_pair(shape);
        println!(
            "==== {shape:?}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        match slice20_owner(shape, &source, &machine) {
            Ok(owner) => {
                println!(
                    "{}",
                    generate_smt2_query_raw(owner.obligation(), &replay_config())
                );
                for (k, part) in owner.parts().iter().enumerate() {
                    println!(
                        ";;;; part {}\n{}",
                        k + 1,
                        generate_smt2_query_raw(part, &replay_config())
                    );
                }
            }
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
    // The variants: the production owner's verdict, and (for the one stated
    // in parts by its control) the verdict cut at every block.
    for variant in SLICE_TWENTY_VARIANTS {
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
        if let Err(refusal) =
            source_bound_x86_body_in_parts(&source, &machine, SYSV, &cut_at(every_block(&source)))
        {
            println!("REFUSED in parts at every block: {refusal}");
        }
    }
}

/// The theorems one fixture replays: its single theorem, or every part.
fn replayed(owner: &SourceBoundX86Body<'_>, label: &str) -> Vec<(String, ProofObligation)> {
    if owner.is_stated_in_parts() {
        owner
            .replay_parts()
            .enumerate()
            .map(|(k, part)| (format!("{label} part {}", k + 1), part.obligation().clone()))
            .collect()
    } else {
        vec![(label.to_owned(), owner.obligation().clone())]
    }
}

/// The canonical slice-20 theorems (every part of a fixture stated in
/// parts), generated THROUGH THE REAL BUILDER, replay on this host's
/// admitted AY with a Clean-accepted proof (or are recorded gaps with their
/// exact outcome). A shape the library gate states in parts at every block
/// is also replayed as the production owner states it, in one query under
/// the shape's own label: the theorem the credit lane needs.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_twenty_body_theorems() {
    let test = "host_qualification_replays_the_slice_twenty_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in SLICE_TWENTY {
            let (source, machine) = slice20_pair(shape);
            let owner = slice20_owner(shape, &source, &machine)
                .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
            let mut theorems = replayed(&owner, &format!("{shape:?}"));
            if cut_everywhere(shape) {
                let production = source_bound_x86_body(&source, &machine, SYSV)
                    .unwrap_or_else(|refusal| panic!("{shape:?} (production): {refusal}"));
                assert!(!production.is_stated_in_parts(), "{shape:?}");
                theorems.push((format!("{shape:?}"), production.obligation().clone()));
            }
            for (label, theorem) in theorems {
                if let Some(dir) = &dump {
                    std::fs::create_dir_all(dir).unwrap();
                    std::fs::write(
                        dir.join(format!("{}.smt2", label.replace(' ', "_"))),
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
                    "X86_BODY_SLICE20_QUALIFICATION shape={label} result={result:?} ms={}",
                    started.elapsed().as_millis()
                );
                assert!(
                    !matches!(result, AYResult::CounterExample(_)),
                    "{label}: a correct lowering was refuted: {result:?}"
                );
                if result != AYResult::Verified {
                    eprintln!(
                        "X86_BODY_SLICE20_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
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
    // This host's deadline-bound gaps are settled first: each may carry only
    // an answer measured for it at the deadline.
    let uncertified = super::settle_here(
        uncertified,
        KNOWN_UNCERTIFIED_SLICE_TWENTY,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_TWENTY,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-20 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// Every slice-20 wrong lowering is refuted by AY with a counterexample (in
/// some part, for one stated in parts).
#[test]
fn host_qualification_refutes_every_slice_twenty_mis_model() {
    let test = "host_qualification_refutes_every_slice_twenty_mis_model";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        for (label, source, machine, built) in slice_twenty_refutations() {
            let theorems = refutation_obligations(&source, &machine, built)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
            let mut refuted = false;
            for (k, theorem) in theorems.iter().enumerate() {
                if let Some(dir) = &dump {
                    std::fs::create_dir_all(dir).unwrap();
                    std::fs::write(
                        dir.join(format!(
                            "refutation_{}.{}.smt2",
                            label.replace([' ', '/', '(', ')', '=', '<', '>', '\'', ','], "_"),
                            k + 1
                        )),
                        generate_smt2_query_raw(theorem, &replay_config()),
                    )
                    .unwrap();
                }
                let started = std::time::Instant::now();
                let outcome =
                    crate::ay_bridge::verify_with_cli_raw_attributed(theorem, &replay_config());
                eprintln!(
                    "X86_BODY_SLICE20_QUALIFICATION refutation={label} part={} result={:?} ms={}",
                    k + 1,
                    outcome.result,
                    started.elapsed().as_millis()
                );
                if matches!(outcome.result, AYResult::CounterExample(_)) {
                    refuted = true;
                    break;
                }
            }
            assert!(refuted, "{label} must be refuted");
        }
    });
    assert_qualification_replayer(&edits);
}

/// With the real tools, every covered row of every certified slice-20 shape
/// is Formal under the body theorem the production owner states (the shapes
/// the library gate states in parts at every block are small, and the
/// production planner states them in one query), the function is promotable
/// and its exports bind the ABI; a wrong lowering the production owner builds
/// fails every covered row.
#[test]
fn verifier_credits_every_bound_slice_twenty_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_twenty_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_TWENTY {
            let label = format!("{shape:?}");
            let (source, machine) = slice20_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            // A gap some runs certify on this host takes whichever whole
            // branch its replay produced, never a mix (the production owner
            // states every slice-20 shape in one query, so a gap's label is
            // its shape's).
            if super::gap_branch_here(
                KNOWN_UNCERTIFIED_SLICE_TWENTY,
                "KNOWN_UNCERTIFIED_SLICE_TWENTY",
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
        for (label, source, machine, _) in slice_twenty_refutations() {
            let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) else {
                continue;
            };
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            let failed = covered_rows_matching(&owner, report.report(), |result| {
                matches!(result, InstructionVerificationResult::Failed { .. })
            });
            let unverified = covered_rows_matching(&owner, report.report(), is_needs_replay);
            assert!(
                failed == owner.bound_rows().len() || unverified == owner.bound_rows().len(),
                "{label}: {:?}",
                report.report()
            );
            assert!(exports.is_empty(), "{label}");
        }
    });
}
