// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-11 x86-64 body
//! theorems (`I128` register pairs and float bit patterns in SSE registers;
//! tool-gated: the admitted AY and a Clean checker). The fixtures, golden
//! snapshots and solver-free controls are in `slice11`, which the
//! `x86_source_bound_body::tests::slice11::` library gate runs; these tests
//! need the replayer pair their recorded outcomes were measured with.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice11::{
    SLICE_ELEVEN, all_slice_eleven_shapes, slice_eleven_refutations, slice11_pair,
};
use super::*;

/// Slice-11 qualification cases whose canonical theorem the qualified
/// AY/Clean pair does NOT certify: a recorded replayer gap, never a credit
/// route.
///
/// `MulU128` is the 128-bit multiply: the source's `bvmul` at 128 bits
/// against the selector's `mul` of the low halves and two `imul` cross
/// products (AY's word-level multiply gap, as slice 10's 64-bit
/// multiplies); the solve runs out of its 30 s budget on every pair
/// measured.
///
/// `SubU128` (`u128::wrapping_sub`) was an AY REGRESSION of build 12713, not
/// a capability gap: AY build 10530 certified it in 6-12 s, and build 12713
/// found the same UNSAT but spent 30-44 s of CPU producing and
/// self-checking a proof 4.4 times larger, past the replay's 30 s deadline
/// (`reports/perf/2026-10-05-darwin-x86-64-ay12713-requalification/`). AY
/// build 13556 compares a printed literal with its own spelling up to
/// literal spelling in its circuit lane (AY DR-50), and [`QUALIFIED_AY`]
/// (build 13556) certifies it in 3.6 s (one test per process, 2026-10-19,
/// `reports/perf/2026-10-19-darwin-x86-64-ay13556-requalification/`): it
/// is no longer a gap.
///
/// `SlotU128` (an `I128` through a private slot, then added) was a spelling
/// regression of build 12713: main's balanced canonical conjunctions
/// (`71c2eb632`) took it 32 s where the right spine took 1.7 s (paired
/// runs, 2026-10-09), past the replay's 30 s deadline. Since slice 18's
/// spelling (OD-187) it certifies (2.6 s on build 12713, one test per
/// process, 2026-10-19,
/// `reports/perf/2026-10-19-darwin-x86-64-slice18-spelling/`), and it is no
/// longer a gap.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_ELEVEN: &[Uncertified] = &[Uncertified {
    label: "MulU128",
    outcome: "Timeout",
    proof_gate_class: "PENDING(solver-capacity)",
    tool_output: "ay: no answer within the 30 s deadline; offline with a 300 s budget, \
         `unknown` / `(:reason-unknown timeout)` after 300.1 s (build 12713: the same after \
         298.8 s of CPU, and in slice 18's spelling after 300.1 s; AY build 10530: the same at \
         its 30 s budget, after 29.3-29.6 s); no proof for clean",
}];

/// A diagnostic, not a check: every slice-11 fixture's LIR, machine rows and
/// theorem (or refusal). It lives here, outside the solver-free gate's
/// `slice11::` filter, which counts an ignored test as a skip.
#[test]
#[ignore]
fn print_slice_eleven_fixtures() {
    for shape in all_slice_eleven_shapes() {
        let (source, machine) = slice11_pair(shape);
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

/// The canonical slice-11 theorems, generated THROUGH THE REAL BUILDER,
/// replay on this host's admitted AY with a Clean-accepted proof (or are
/// recorded gaps with their exact outcome), and every wrong lowering is
/// refuted with a counterexample. The recorded gaps are compared only under
/// the replayer pair they were measured with
/// ([`assert_qualification_replayer`]).
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
#[test]
fn host_qualification_replays_the_slice_eleven_body_theorems() {
    let test = "host_qualification_replays_the_slice_eleven_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let uncertified = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in SLICE_ELEVEN {
            let label = format!("{shape:?}");
            let (source, machine) = slice11_pair(shape);
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
                "X86_BODY_SLICE11_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_SLICE11_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label.clone(), stable_outcome(&result)));
            }
        }
        for (label, source, machine) in slice_eleven_refutations() {
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
                "X86_BODY_SLICE11_QUALIFICATION refutation={label} result={:?}",
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
        KNOWN_UNCERTIFIED_SLICE_ELEVEN,
        "KNOWN_UNCERTIFIED_SLICE_ELEVEN",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-11 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
}

/// With the real tools, every covered row of every certified slice-11 shape
/// is Formal under the body theorem (the `adc`/`sbb` rows, the shifts by CL
/// of the halves, and the SSE moves included), the function is promotable
/// and its exports bind the ABI; a wrong lowering the Rust check cannot judge
/// fails every covered row.
#[test]
fn verifier_credits_every_bound_slice_eleven_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_eleven_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    // The per-host gap view this lane branches on was recorded with one
    // replayer pair: check the pair before the first replay.
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_ELEVEN {
            let label = format!("{shape:?}");
            let (source, machine) = slice11_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if super::gap_applies_here(
                KNOWN_UNCERTIFIED_SLICE_ELEVEN,
                "KNOWN_UNCERTIFIED_SLICE_ELEVEN",
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
        for (label, source, machine) in slice_eleven_refutations() {
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
