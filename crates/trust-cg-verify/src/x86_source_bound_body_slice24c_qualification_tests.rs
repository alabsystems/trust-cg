// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-24c x86-64 body
//! theorems (segments: the if-converted regions, OD-228; tool-gated: the
//! admitted AY and a Clean checker). The fixtures and solver-free controls
//! are in `slice24c`, which the `x86_source_bound_body::tests::slice24c::`
//! library gate runs. Each test here is run in a process of its own (a
//! session memo would answer a sibling's queries otherwise).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice24::text;
use super::slice24c::{
    CASES24C, REFUTED24C, SLICE_TWENTY_FOUR_C, case24c, composition24c, encodings_of_p1, owner24c,
    pair24c,
};
use super::*;

/// Every slice-24c subject the replay and credit lanes take, by label: each
/// fixture's theorem over its segments (P1 to P6, P9, P11), the long
/// diamond's production statement through the parts route (P8, one part),
/// and the composition ([`composition24c`]: the O2 pipeline over five
/// earlier slices' fixtures, the short tail over OD-226's quotient and the
/// forked tail in parts). P1's DAG theorem (P7) is replayed besides; its
/// path theorem is P1's own (asserted), so it is not replayed twice.
pub(crate) fn qualification_subjects() -> Vec<(String, Function, X86ISelFunction)> {
    let mut subjects = Vec::new();
    for shape in SLICE_TWENTY_FOUR_C {
        let (source, machine) = pair24c(shape);
        subjects.push((format!("{shape:?}"), source, machine));
    }
    let (source, machine) = case24c("P8");
    subjects.push(("LongDiamond in parts".into(), source, machine));
    subjects.extend(composition24c());
    subjects
}

/// Whether a subject is a recorded gap here: its label, or the label of any
/// of its `parts` (`<label> part <k>`).
fn subject_gap_here(
    label: &str,
    parts: usize,
    awaiting: usize,
    qualified: &super::qualified_pair::QualifiedPair,
) -> bool {
    let branch = |label: &str| {
        super::gap_branch_here(
            KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C,
            "KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C",
            label,
            awaiting,
            qualified,
        )
    };
    branch(label) || (parts > 1 && (1..=parts).any(|k| branch(&format!("{label} part {k}"))))
}

/// Slice-24c qualification theorems the qualified AY/Clean pair does NOT
/// certify: recorded replayer gaps, never a credit route by themselves (their
/// rows stay unverified, never credited and never refuted).
pub(crate) const KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C: &[Uncertified] = &[
    Uncertified {
        label: "LongDiamond in parts",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: LONG_DIAMOND_OFFLINE,
    },
    Uncertified {
        label: "s9 Diamonds5 O2",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: DIAMONDS5_OFFLINE,
    },
    Uncertified {
        label: "s16 DiamondChain O2",
        outcome: "Timeout",
        proof_gate_class: "PENDING(solver-capacity)",
        tool_output: DIAMOND_CHAIN_OFFLINE,
    },
];

/// `AY`'s answer to `LongDiamond in parts`'s exact theorem: P8 is past the
/// single-query block bound, and over OD-226's quotient its one region fits,
/// so the production planner states it in one part. Both sides add the same
/// 141 constants to the join's value, which the source spells as the `ite`
/// of its edge guard and the machine as the `cmov`'s `ite` of its flags: the
/// two chains share no term, and AY bit-blasts both.
const LONG_DIAMOND_OFFLINE: &str = "ay: no answer within the 30 s deadline; offline with a 300 s budget, \
     still no answer (`(:reason-unknown timeout)` at 300.2 s, 2026-11-05, load 15.5)";

/// `AY`'s answer to `s9 Diamonds5 O2`'s exact theorem: five diamonds in
/// sequence (`v = if v < b { v + k } else { v ^ k }`, `k` from 1 to 5), five
/// segments in one query. The source spells each join's value as the `ite`
/// of its edge guard and the machine as its `cmov`'s `ite` of the flags,
/// equal but never the same term, so no join value is shared and AY
/// bit-blasts five chained compare-and-select stages on each side (as for
/// the long diamond).
const DIAMONDS5_OFFLINE: &str = "ay: no answer within the 30 s deadline (30.0 s in the lane, \
     2026-11-05); offline with a 300 s budget, still no answer (`(:reason-unknown timeout)` at \
     300.2 s, 2026-11-06, load 14.2 at the start)";

/// `AY`'s answer to `s16 DiamondChain O2`'s exact theorem: slice 16's chain
/// of 34 diamonds through the O2 pipeline, 34 segments in one query, each
/// join's value spelled as on `s9 Diamonds5 O2`.
const DIAMOND_CHAIN_OFFLINE: &str = "ay: no answer within the 30 s deadline (2026-11-05); \
     offline with a 300 s budget, still no answer (`(:reason-unknown timeout)` at 300.4 s, \
     2026-11-06, load 25.3 at the start)";

/// A diagnostic, not a check: every slice-24c fixture's LIR, machine rows,
/// segments and theorem (or refusal).
#[test]
#[ignore]
fn print_slice_twenty_four_c_qualification_fixtures() {
    for (label, source, machine) in qualification_subjects() {
        println!(
            "==== {label}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        match owner24c(&source, &machine) {
            Ok(owner) => {
                println!("SEGMENTS {:?}", owner.segments());
                for unit in owner.replayed_units() {
                    println!("{}", generate_smt2_query_raw(unit, &replay_config()));
                }
            }
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
}

/// The slice-24c theorems, generated THROUGH THE REAL BUILDER over each
/// fixture's real pipeline stream, replay on this host's admitted AY with a
/// Clean-accepted proof (or are recorded gaps with their exact outcome). No
/// correct lowering is refuted, and every segment kind the fixtures state
/// certifies at least once (`kinds=` names the kinds of each line).
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_twenty_four_c_body_theorems() {
    let test = "host_qualification_replays_the_slice_twenty_four_c_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let (uncertified, verified, kinds) = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        let mut verified = 0usize;
        // Each kind stated, and whether a theorem over it certified.
        let mut kinds: std::collections::BTreeMap<String, bool> = std::collections::BTreeMap::new();
        let mut replay = |label: String, kind: String, unit: &ProofObligation| {
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("{}.smt2", label.replace([' ', '\''], "_"))),
                    generate_smt2_query_raw(unit, &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let result = request
                .ay()
                .verify_fresh_source_bound(&X86BodyPart { obligation: unit }, &replay_config());
            eprintln!(
                "X86_BODY_SLICE24C_QUALIFICATION shape={label} kinds={kind} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            let certified = result == AYResult::Verified;
            for one in kind.trim_matches(['[', ']']).split(',') {
                *kinds.entry(one.to_owned()).or_default() |= certified;
            }
            if certified {
                verified += 1;
            } else {
                eprintln!(
                    "X86_BODY_SLICE24C_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label, stable_outcome(&result), proof_gate_class(&result)));
            }
        };
        let mut split = 0usize;
        for (label, source, machine) in qualification_subjects() {
            let owner =
                owner24c(&source, &machine).unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let (_, _, kind) = owner
                .segments()
                .unwrap_or_else(|| panic!("{label}: stated over no segment"));
            if owner.is_stated_in_parts() {
                split += 1;
            }
            let units = owner.replayed_units();
            let single = units.len() == 1;
            for (k, unit) in units.into_iter().enumerate() {
                let label = if single {
                    label.clone()
                } else {
                    format!("{label} part {}", k + 1)
                };
                replay(label, kind.clone(), unit);
            }
        }
        assert!(split > 0, "no slice-24c fixture was replayed in parts");
        let (p1_source, p1_machine) = pair24c(super::slice24c::Shape24c::AlignOffset);
        let p1 = owner24c(&p1_source, &p1_machine).expect("P1 is stated");
        for (encoding, theorem) in encodings_of_p1() {
            let theorem = theorem.unwrap_or_else(|refusal| panic!("P7 {encoding}: {refusal}"));
            if encoding == "paths" {
                assert_eq!(
                    text(&theorem),
                    text(p1.obligation()),
                    "P7: the path theorem is P1's own"
                );
                continue;
            }
            replay(
                format!("AlignOffset {encoding}"),
                "[diamond]".into(),
                &theorem,
            );
        }
        (uncertified, verified, kinds)
    });
    let qualified = assert_qualification_replayer(&edits);
    assert!(verified > 0, "no slice-24c theorem certified");
    let uncertified = super::settle_here(
        uncertified,
        KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C",
        &qualified,
    );
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C,
        "KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-24c set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
    eprintln!("X86_BODY_SLICE24C_QUALIFICATION kinds={kinds:?}");
    let uncertified_kinds: Vec<&String> = kinds
        .iter()
        .filter(|(_, certified)| !**certified)
        .map(|(kind, _)| kind)
        .collect();
    assert!(
        uncertified_kinds.is_empty(),
        "no theorem over a {uncertified_kinds:?} segment certified"
    );
}

/// Every slice-24c must-refute control's theorem (built without the affine
/// refusal, so the solver judges what the owner may name in Rust) is refuted
/// by AY with a counterexample.
#[test]
fn host_qualification_refutes_the_slice_twenty_four_c_wrong_lowerings() {
    let test = "host_qualification_refutes_the_slice_twenty_four_c_wrong_lowerings";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    with_edits(&edits, || {
        let mut replayed = 0;
        for label in REFUTED24C {
            let (source, machine) = case24c(label);
            let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: not stated: {refusal}"));
            replayed += 1;
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("wrong_{}.smt2", label.replace([' ', '\''], "_"))),
                    generate_smt2_query_raw(&theorem, &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let attributed =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_SLICE24C_QUALIFICATION wrong={label} result={:?} ms={}",
                attributed.result,
                started.elapsed().as_millis()
            );
            assert!(
                matches!(attributed.result, AYResult::CounterExample(_)),
                "{label}: AY must refute a wrong lowering's theorem with a counterexample"
            );
        }
        assert_eq!(replayed, REFUTED24C.len());
    });
    assert_qualification_replayer(&edits);
}

/// With the real tools, every covered row of every certified slice-24c
/// fixture (the rows of each segment's machine block among them) is Formal
/// under the replayed body theorem through the production route, its
/// exports bind the pair, and no wrong lowering or refusal control is ever
/// credited.
#[test]
fn verifier_credits_every_bound_slice_twenty_four_c_row_with_the_replayed_body_theorem() {
    let test =
        "verifier_credits_every_bound_slice_twenty_four_c_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let mut credited = 0;
        for (label, source, machine) in qualification_subjects() {
            let owner =
                owner24c(&source, &machine).unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if subject_gap_here(
                &label,
                owner.replayed_units().len(),
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
            assert_eq!(exports.len(), owner.bound_rows().len(), "{label}");
            assert!(
                report.matches_x86_input(&machine, Some(&source), SYSV),
                "{label}: the report binds the pair"
            );
            eprintln!(
                "X86_BODY_SLICE24C_QUALIFICATION credit={label} rows={}",
                exports.len()
            );
            credited += 1;
        }
        assert!(credited > 0, "no slice-24c body was credited");
        for label in CASES24C {
            let (source, machine) = case24c(label);
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            let credited = match owner24c(&source, &machine) {
                Ok(owner) => covered_rows_matching(&owner, report.report(), is_body_credit),
                Err(_) => 0,
            };
            eprintln!("X86_BODY_SLICE24C_QUALIFICATION wrong_credit={label} rows={credited}");
            assert_eq!(credited, 0, "{label}: {:?}", report.report());
            assert!(exports.is_empty(), "{label}");
        }
    });
}
