// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-13 x86-64 body
//! theorems (private addresses stored as data, the incoming and outgoing
//! stack argument areas, the C memory routines and scalar atomics;
//! tool-gated: the admitted AY and a Clean checker). The fixtures, golden
//! snapshots and solver-free controls are in `slice13`, which the
//! `x86_source_bound_body::tests::slice13::` library gate runs; these tests
//! need the replayer pair their recorded outcomes were measured with.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice13::{
    MEMORY_ROUTINES, SLICE_THIRTEEN, all_slice_thirteen_shapes, slice_thirteen_refutations,
    slice13_pair,
};
use super::slice22::{Routine, fixture_module, fixture_owner, routine_pair};
use super::*;

/// Slice-13 qualification cases whose canonical theorem the qualified
/// AY/Clean pair does NOT certify: a recorded replayer gap, never a credit
/// route.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_THIRTEEN: &[Uncertified] = &[];

/// A diagnostic, not a check: every slice-13 fixture's LIR, machine rows and
/// theorem (or refusal). It lives here, outside the solver-free gate's
/// `slice13::` filter, which counts an ignored test as a skip.
#[test]
#[ignore]
fn print_slice_thirteen_fixtures() {
    for shape in all_slice_thirteen_shapes() {
        let (source, machine) = slice13_pair(shape);
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

/// The canonical slice-13 theorems, generated THROUGH THE REAL BUILDER,
/// replay on this host's admitted AY with a Clean-accepted proof (or are
/// recorded gaps with their exact outcome), and every wrong lowering is
/// refuted with a counterexample. The recorded gaps are compared only under
/// the replayer pair they were measured with
/// ([`assert_qualification_replayer`]).
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_thirteen_body_theorems() {
    let test = "host_qualification_replays_the_slice_thirteen_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in SLICE_THIRTEEN {
            let label = format!("{shape:?}");
            let (source, machine) = slice13_pair(shape);
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
                "X86_BODY_SLICE13_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_SLICE13_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label.clone(), stable_outcome(&result)));
            }
        }
        for (label, source, machine) in slice_thirteen_refutations() {
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
            let refuted =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_SLICE13_QUALIFICATION refutation={label} result={:?}",
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
        KNOWN_UNCERTIFIED_SLICE_THIRTEEN,
        "KNOWN_UNCERTIFIED_SLICE_THIRTEEN",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-13 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// With the real tools, every covered row of every certified slice-13 shape
/// is Formal under the body theorem (the stored addresses, the stack
/// parameter loads, the outgoing argument stores and RSP adjustments, the
/// memory-routine calls' argument moves and the atomic accesses included),
/// the function is promotable and its exports bind the ABI; a wrong lowering
/// the Rust check cannot judge fails every covered row.
#[test]
fn verifier_credits_every_bound_slice_thirteen_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_thirteen_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    // The per-host gap view this lane branches on was recorded with one
    // replayer pair: check the pair before the first replay.
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_THIRTEEN {
            let label = format!("{shape:?}");
            let (source, machine) = slice13_pair(shape);
            let owner = fixture_owner(&source, &machine).unwrap();
            // OD-217: the fixture's module (it defines no C memory routine)
            // is named, as the compiler names it.
            let module = fixture_module(&source);
            let (report, exports) = verifier.verify_with_request_for_export_in_module(
                &machine,
                Some(&source),
                SYSV,
                &module,
                &request,
            );
            if super::gap_applies_here(
                KNOWN_UNCERTIFIED_SLICE_THIRTEEN,
                "KNOWN_UNCERTIFIED_SLICE_THIRTEEN",
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
                Some(&module)
            ));
        }
        for (label, source, machine) in slice_thirteen_refutations() {
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

/// OD-216 and OD-217 with the real tools. A `Memcpy`, `Memmove` or `Memset`
/// shape's theorem, and the theorem of a division by a declared
/// `__udivti3`, replay Valid; the verifier naming the module alone (as it
/// named a crate's codegen unit before OD-216, whatever a sibling unit
/// defined) credits every covered row Formal. Naming a link unit that
/// defines the routine (a sibling codegen unit of the crate), or a module
/// that defines it, the verifier credits no row and exports nothing.
#[test]
fn verifier_credits_no_row_whose_routine_the_crate_defines() {
    let test = "verifier_credits_no_row_whose_routine_the_crate_defines";
    let edits = replay_environment(test);
    assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let mut cases: Vec<(
            String,
            Function,
            X86ISelFunction,
            X86ModuleDefinitions,
            &str,
        )> = MEMORY_ROUTINES
            .iter()
            .map(|&(shape, routine)| {
                let (source, machine) = slice13_pair(shape);
                let module = fixture_module(&source);
                (format!("{shape:?}"), source, machine, module, routine)
            })
            .collect();
        let (source, machine, definitions) = routine_pair(Routine::Declared, "div");
        cases.push(("div".into(), source, machine, definitions, "__udivti3"));
        for (label, source, machine, module, routine) in &cases {
            let alone = source_bound_x86_body_in_module(source, machine, SYSV, Some(module))
                .unwrap_or_else(|refusal| panic!("{label} alone: {refusal}"));
            assert_eq!(alone.trusted_routines().collect::<Vec<_>>(), [*routine]);
            for unit in alone.replayed_units() {
                let result = request
                    .ay()
                    .verify_fresh_source_bound(&X86BodyPart { obligation: unit }, &replay_config());
                assert_eq!(
                    result,
                    AYResult::Verified,
                    "{label}: the theorem replays Valid"
                );
            }
            let (report, exports) = verifier.verify_with_request_for_export_in_module(
                machine,
                Some(source),
                SYSV,
                module,
                &request,
            );
            let credited = covered_rows_matching(&alone, report.report(), is_body_credit);
            eprintln!(
                "X86_BODY_OD216 {label} module alone: {credited} of {} covered rows credited",
                alone.bound_rows().len()
            );
            assert_eq!(
                credited,
                alone.bound_rows().len(),
                "{label}: {:?}",
                report.report()
            );
            assert_eq!(exports.len(), alone.bound_rows().len(), "{label}");
            for (state, definitions) in [
                (
                    "a sibling unit defines it",
                    module.clone().with_link_unit([*routine]),
                ),
                (
                    "the module defines it",
                    X86ModuleDefinitions::of_symbols([source.name.as_str(), *routine]),
                ),
            ] {
                let (report, exports) = verifier.verify_with_request_for_export_in_module(
                    machine,
                    Some(source),
                    SYSV,
                    &definitions,
                    &request,
                );
                let credited = covered_rows_matching(&alone, report.report(), is_body_credit);
                eprintln!(
                    "X86_BODY_OD216 {label} {state}: {credited} of {} covered rows credited",
                    alone.bound_rows().len()
                );
                assert_eq!(credited, 0, "{label}, {state}: {:?}", report.report());
                assert!(exports.is_empty(), "{label}, {state}");
                assert!(report.matches_x86_input_in_module(
                    machine,
                    Some(source),
                    SYSV,
                    Some(&definitions)
                ));
                assert!(!report.matches_x86_input_in_module(
                    machine,
                    Some(source),
                    SYSV,
                    Some(module)
                ));
            }
        }
    });
}
