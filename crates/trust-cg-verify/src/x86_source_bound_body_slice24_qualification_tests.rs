// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-24a x86-64 body
//! theorems (the exact merged-chain quotient, OD-226; tool-gated: the
//! admitted AY and a Clean checker). The fixtures and solver-free controls
//! are in `slice24`, which the `x86_source_bound_body::tests::slice24::`
//! library gate runs. Each test here is run in a process of its own (a
//! session memo would answer a sibling's queries otherwise).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice24::{
    SLICE_TWENTY_FOUR, Shape24, extra24, owner24, parts_fixtures, parts24,
    slice_twenty_four_refutations, slice24_lir, slice24_pair,
};
use super::*;

/// Slice-24a qualification theorems the qualified AY/Clean pair does NOT
/// certify: recorded replayer gaps, never a credit route by themselves.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR: &[Uncertified] = &[];

/// The wrong lowerings the refutation lane replays: those the owner states
/// (the rest make no claim, which the library gate checks).
const REPLAYED_REFUTATIONS: [&str; 4] = [
    "W4 rows restamped",
    "W6 op swapped",
    "W7 seam jcc inverted",
    "W13 jcc before the carrier",
];

/// The walk ordinals of the rows that lower a LIR block no source path
/// reaches.
fn dead_rows(source: &Function, machine: &X86ISelFunction) -> HashSet<usize> {
    let dead = source_cfg(source).expect("an admitted source").dead;
    rows(machine)
        .into_iter()
        .filter(|(_, block, index)| {
            machine.blocks[block].insts[*index]
                .lowering_provenance
                .source_id()
                .is_some_and(|id| dead.contains(&Block(id.block)))
        })
        .map(|(ordinal, _, _)| ordinal)
        .collect()
}

/// A laid-out dead block lies on no path, so no theorem claims its rows: the
/// report has no failure, every row that keeps the function's opcode
/// inventory from promotion lowers a dead block, and nothing is exported.
fn dead_rows_withhold_exports(
    label: &str,
    source: &Function,
    machine: &X86ISelFunction,
    report: &crate::FunctionVerificationReport,
    exports: &[crate::SourceBoundArithmeticObligation],
) {
    assert!(!report.has_failures(), "{label}: {report:?}");
    let dead = dead_rows(source, machine);
    let inventory = report.emitted_opcode_inventory();
    let uncovered: Vec<usize> = inventory
        .uncovered_non_pseudo_opcodes()
        .iter()
        .map(|entry| entry.inst_index)
        .collect();
    assert!(
        !uncovered.is_empty(),
        "{label}: the dead rows are uncovered"
    );
    assert!(
        uncovered.iter().all(|row| dead.contains(row)),
        "{label}: uncovered {uncovered:?}, dead {dead:?}"
    );
    assert!(exports.is_empty(), "{label}: {} exports", exports.len());
}

/// Every slice-24a pair the replay lane states: label, pair, and the policy
/// points of one stated in parts.
#[allow(clippy::type_complexity)]
fn qualification_pairs() -> Vec<(
    String,
    Function,
    X86ISelFunction,
    Option<Vec<(Block, usize)>>,
)> {
    let mut pairs = Vec::new();
    for shape in SLICE_TWENTY_FOUR {
        let (source, machine) = slice24_pair(shape);
        pairs.push((format!("{shape:?}"), source, machine, None));
    }
    for (label, source, machine, points) in parts_fixtures() {
        pairs.push((format!("{label} (parts)"), source, machine, Some(points)));
    }
    // The production route's parts over a quotient: past the single-query
    // bounds, the planner cuts the one merged machine block.
    let (source, machine) = extra24("long chain");
    pairs.push(("LongChain (production parts)".into(), source, machine, None));
    // A no-parameter entry that a dead `Jump` enters still heads its own
    // chain: the dead block never absorbs it.
    let (source, machine) = extra24("entry behind a dead Jump");
    pairs.push((
        "NoParamEntry behind a dead Jump".into(),
        source,
        machine,
        None,
    ));
    pairs
}

/// A diagnostic, not a check: every slice-24a pair's LIR, machine rows and
/// theorem (or refusal).
#[test]
#[ignore]
fn print_slice_twenty_four_qualification_fixtures() {
    for (label, source, machine, points) in qualification_pairs() {
        println!(
            "==== {label}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        let result = match points {
            None => owner24(&source, &machine),
            Some(points) => parts24(&source, &machine, points),
        };
        match result {
            Ok(owner) => {
                for unit in owner.replayed_units() {
                    println!("{}", generate_smt2_query_raw(unit, &replay_config()));
                }
            }
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
}

/// The slice-24a theorems, generated THROUGH THE REAL BUILDER over each
/// pair's merged-chain quotient, replay on this host's admitted AY with a
/// Clean-accepted proof (or are recorded gaps with their exact outcome). No
/// correct lowering is refuted, and at least one merged body certifies.
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_twenty_four_body_theorems() {
    let test = "host_qualification_replays_the_slice_twenty_four_body_theorems";
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
        for (label, source, machine, points) in qualification_pairs() {
            let owner = match points {
                None => owner24(&source, &machine),
                Some(points) => parts24(&source, &machine, points),
            }
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            assert!(
                owner.merged_chains().is_some(),
                "{label}: not over a quotient"
            );
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
                    "X86_BODY_SLICE24_QUALIFICATION shape={label} result={result:?} ms={}",
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
                        "X86_BODY_SLICE24_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                        stable_outcome(&result),
                        proof_gate_class(&result)
                    );
                    uncertified.push((label, stable_outcome(&result), proof_gate_class(&result)));
                }
            }
        }
        (uncertified, verified)
    });
    let qualified = assert_qualification_replayer(&edits);
    assert!(verified > 0, "no merged-chain theorem certified");
    let uncertified = super::settle_here(
        uncertified,
        KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-24a set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// Every slice-24a wrong lowering the owner states is refuted by AY with a
/// counterexample on the qualification pair.
#[test]
fn host_qualification_refutes_the_slice_twenty_four_wrong_lowerings() {
    let test = "host_qualification_refutes_the_slice_twenty_four_wrong_lowerings";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        let mut replayed = 0;
        for (label, source, machine) in slice_twenty_four_refutations() {
            if !REPLAYED_REFUTATIONS.contains(&label) {
                continue;
            }
            let Ok(owner) = owner24(&source, &machine) else {
                eprintln!("X86_BODY_SLICE24_QUALIFICATION wrong={label} result=no-claim");
                continue;
            };
            replayed += 1;
            let mut refuted = false;
            for (k, theorem) in owner.replayed_units().into_iter().enumerate() {
                if let Some(dir) = &dump {
                    std::fs::create_dir_all(dir).unwrap();
                    std::fs::write(
                        dir.join(format!("wrong_{}_{k}.smt2", label.replace([' ', '/'], "_"))),
                        generate_smt2_query_raw(theorem, &replay_config()),
                    )
                    .unwrap();
                }
                let started = std::time::Instant::now();
                let attributed =
                    crate::ay_bridge::verify_with_cli_raw_attributed(theorem, &replay_config());
                eprintln!(
                    "X86_BODY_SLICE24_QUALIFICATION wrong={label} unit={k} result={:?} ms={}",
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
        assert!(replayed > 0, "no wrong lowering was stated to refute");
    });
    assert_qualification_replayer(&edits);
}

/// With the real tools, every covered row of every certified slice-24a
/// shape, the rows lowering an absorbed member's instructions included, is
/// Formal under the replayed body theorem through the production route; its
/// exports bind the ORIGINAL pair; a wrong lowering is never credited.
#[test]
fn verifier_credits_every_bound_slice_twenty_four_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_twenty_four_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let mut credited = 0;
        for shape in SLICE_TWENTY_FOUR {
            let label = format!("{shape:?}");
            let (source, machine) = slice24_pair(shape);
            let owner =
                owner24(&source, &machine).unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if super::gap_branch_here(
                KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR,
                "KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR",
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
            if shape == Shape24::DeadChain {
                dead_rows_withhold_exports(&label, &source, &machine, report.report(), &exports);
                credited += 1;
                continue;
            }
            assert_eq!(exports.len(), owner.bound_rows().len(), "{label}");
            assert!(
                report.matches_x86_input(&machine, Some(&source), SYSV),
                "{label}: the report binds the original pair"
            );
            credited += 1;
        }
        assert!(credited > 0, "no merged-chain body was credited");
        // The dead chain's rows withhold the exports without a quotient too:
        // the selector's unmerged stream, stated over the original pair.
        let source = slice24_lir(Shape24::DeadChain);
        let machine = select(&source, X86CallAbi::SystemV);
        let owner = owner24(&source, &machine).expect("the unmerged dead chain is stated");
        assert!(owner.merged_chains().is_none(), "unmerged: no quotient");
        let (report, exports) =
            verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
        for row in &report.report().instructions {
            if owner.covers(row.inst_index) {
                assert!(
                    is_body_credit(&row.result),
                    "unmerged dead chain row {}",
                    row.inst_index
                );
            }
        }
        dead_rows_withhold_exports(
            "unmerged dead chain",
            &source,
            &machine,
            report.report(),
            &exports,
        );
        for (label, source, machine) in slice_twenty_four_refutations() {
            let Ok(owner) = owner24(&source, &machine) else {
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
