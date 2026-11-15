// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Host qualification and verifier credit of the slice-6 x86-64 body
//! theorems (tool-gated: the admitted AY and a Clean checker). The fixtures,
//! golden snapshots and solver-free controls are in `slice6`, which the
//! `x86_source_bound_body::tests::slice6::` library gate runs; these tests
//! need the replayer pair their recorded outcomes were measured with.
//!
//! Encoding evidence: the canonical several-path theorem (one `(or (not C)
//! X)` claim per source path, copies substituted rather than defined, and
//! only the definitions the claims depend on) certifies on every fixture.
//! The qualification test also replays four rejected spellings of every
//! several-path fixture and pins their outcomes: the same claims spelled
//! `(=> C X)`; every definition stated (copies and dead definitions
//! included); the nested `ite` case split `(ite C_1 X_1 (ite C_2 X_2 ...))`;
//! and the merged `ite` of the observable (the path taken as a number, and
//! each item, each chosen by nested `ite`s over the conditions: merging at
//! the join), where every path observes items of one shape.

use super::slice6::{
    SLICE_SIX, path_claims, slice_six_refutations, slice_six_variants, slice6_pair,
};
use super::*;

/// Slice-6 qualification cases whose canonical theorem the qualified AY/Clean
/// pair does NOT certify: a recorded replayer gap, never a credit route.
pub(crate) const KNOWN_UNCERTIFIED_SLICE_SIX: &[Uncertified] = &[];

/// Every slice-6 qualification case: the fixtures and the alternative
/// machine forms.
pub(super) fn slice_six_qualification_cases() -> Vec<(String, Function, X86ISelFunction)> {
    let mut cases: Vec<(String, Function, X86ISelFunction)> = SLICE_SIX
        .iter()
        .map(|shape| {
            let (source, machine) = slice6_pair(*shape);
            (format!("{shape:?}"), source, machine)
        })
        .collect();
    cases.extend(slice_six_variants());
    cases
}

/// A minimal SMT-LIB s-expression, for respelling a rendered query.
#[derive(Clone)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn parse_sexps(text: &str) -> Vec<Sexp> {
    let mut stack: Vec<Vec<Sexp>> = vec![Vec::new()];
    let mut atom = String::new();
    let flush = |atom: &mut String, stack: &mut Vec<Vec<Sexp>>| {
        if !atom.is_empty() {
            stack
                .last_mut()
                .unwrap()
                .push(Sexp::Atom(std::mem::take(atom)));
        }
    };
    for c in text.chars() {
        match c {
            '(' => {
                flush(&mut atom, &mut stack);
                stack.push(Vec::new());
            }
            ')' => {
                flush(&mut atom, &mut stack);
                let list = stack.pop().unwrap();
                stack.last_mut().unwrap().push(Sexp::List(list));
            }
            c if c.is_whitespace() => flush(&mut atom, &mut stack),
            c => atom.push(c),
        }
    }
    flush(&mut atom, &mut stack);
    stack.pop().unwrap()
}

fn show(sexp: &Sexp) -> String {
    match sexp {
        Sexp::Atom(atom) => atom.clone(),
        Sexp::List(items) => format!("({})", items.iter().map(show).collect::<Vec<_>>().join(" ")),
    }
}

fn is_atom(sexp: &Sexp, name: &str) -> bool {
    matches!(sexp, Sexp::Atom(atom) if atom == name)
}

/// The canonical query of a several-path theorem with each path claim
/// `(or (not C) X)` of its goal spelled `(=> C X)`.
pub(super) fn implies_spelling(smt2: &str) -> String {
    fn respell_goal(goal: &Sexp) -> Sexp {
        match goal {
            Sexp::List(items) if items.len() == 3 && is_atom(&items[0], "and") => Sexp::List(vec![
                items[0].clone(),
                respell_goal(&items[1]),
                respell_goal(&items[2]),
            ]),
            Sexp::List(items) if items.len() == 3 && is_atom(&items[0], "or") => {
                let Sexp::List(negated) = &items[1] else {
                    panic!("a path claim is (or (not C) X)")
                };
                assert!(is_atom(&negated[0], "not"));
                Sexp::List(vec![
                    Sexp::Atom("=>".into()),
                    negated[1].clone(),
                    items[2].clone(),
                ])
            }
            other => panic!("not a path claim: {}", show(other)),
        }
    }
    // (assert (and d0 (and d1 ... (not (= true GOAL)))))
    fn respell(sexp: &Sexp) -> Sexp {
        match sexp {
            Sexp::List(items)
                if items.len() == 3 && is_atom(&items[0], "=") && is_atom(&items[1], "true") =>
            {
                Sexp::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    respell_goal(&items[2]),
                ])
            }
            Sexp::List(items) => Sexp::List(items.iter().map(respell).collect()),
            atom => atom.clone(),
        }
    }
    let mut out = String::new();
    for command in parse_sexps(smt2) {
        let command = match &command {
            Sexp::List(items) if is_atom(&items[0], "assert") => respell(&command),
            _ => command,
        };
        out.push_str(&show(&command));
        out.push('\n');
    }
    out
}

/// The nested `ite` case split of a canonical several-path theorem.
pub(super) fn case_split(obligation: &ProofObligation) -> ProofObligation {
    let claims = path_claims(obligation);
    let (_, last) = claims.last().unwrap().clone();
    let goal = claims[..claims.len() - 1]
        .iter()
        .rev()
        .fold(last, |otherwise, (condition, claim)| {
            E::ite(condition.clone(), claim.clone(), otherwise)
        });
    let mut form = obligation.clone();
    form.aarch64_expr = goal;
    form
}

/// A spelling's replay outcome, host paths removed.
fn outcome(result: &AYResult) -> String {
    stable_outcome(result)
}

/// The recorded outcome of each rejected spelling of every several-path
/// qualification case on the qualification host ([`QUALIFIED_AY`], Clean
/// 5f09e36c), in qualification-case order: evidence for the canonical
/// encoding, never a credit route. `-` marks a merged spelling that does not
/// exist (its paths observe items of different shapes).
/// AY's outcome for the `(=> C X)` spelling of every several-path fixture:
/// it computes UNSAT but its proof keeps a trusted step, so it publishes
/// none (`(:reason-unknown (incomplete proof-trusted))`). AY build 10530,
/// which chose the canonical spelling, printed one validated rule as a
/// `hole` instead (`c ay.proof.decline ... mechanism=printer-rule-without-
/// external-spelling`), which Clean rejected as holey.
const TRUSTED_IMPLIES: &str = "Unknown(\"(:reason-unknown (incomplete proof-trusted))\")";

/// A spelling whose proof AY produces within the budget but Clean checks in
/// about the 30 s budget itself, so the outcome is `Verified` on a quiet host
/// and `Timeout` under load: `PairJoin`'s merged spelling with AY build 12713
/// (AY 5.0 s and a 10.4 MB proof, then Clean 30.6 s at load 10; AY build
/// 10530: 1.2 s, a 4.6 MB proof, Clean 0.5 s). Either outcome matches this
/// record; any other is a change to review. [`QUALIFIED_AY`] (build 13556,
/// with AY DR-50's circuit-lane fix, which AY measured on this root as a
/// 4.6 MB proof that Clean checks in 0.5 s) certified it in every run of
/// the 2026-10-19 requalification; the record keeps accepting either
/// outcome until a run measures its Clean time on the qualification host.
/// Since OD-223 the check has its own deadline (180 s, not the 30 s solve
/// budget it shared), and a check that runs out of it is a Clean check
/// timeout ([`crate::ay_bridge::CLEAN_CHECK_TIMEOUT`]), never `Timeout`,
/// which is now AY's alone: the record accepts `Verified` or that.
const VERIFIED_OR_CHECKER_TIMEOUT: &str =
    "Verified, or a Clean check timeout at the checker's own deadline";

const REJECTED_SPELLINGS: &[(&str, &str, &str, &str, &str)] = &[
    ("MinU64", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("MaxI32", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("AbsI64", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("EarlyReturn", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("BoolParam", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("BoolInOut", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("U8Test", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("NestedIf", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("TwoDiamonds", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    (
        "PairJoin",
        TRUSTED_IMPLIES,
        VERIFIED,
        VERIFIED,
        VERIFIED_OR_CHECKER_TIMEOUT,
    ),
    ("EdgeCopies", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("TrapArm", TRUSTED_IMPLIES, VERIFIED, VERIFIED, "-"),
    ("PanicArm", TRUSTED_IMPLIES, VERIFIED, VERIFIED, "-"),
    ("CallArm", TRUSTED_IMPLIES, VERIFIED, VERIFIED, "-"),
    (
        "CallThenBranch",
        TRUSTED_IMPLIES,
        VERIFIED,
        VERIFIED,
        VERIFIED,
    ),
    ("StoreArm", TRUSTED_IMPLIES, VERIFIED, VERIFIED, "-"),
    ("LoadBranch", TRUSTED_IMPLIES, VERIFIED, VERIFIED, "-"),
    ("Switch3", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("SwitchU8", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    (
        "SwitchI32Neg",
        TRUSTED_IMPLIES,
        VERIFIED,
        VERIFIED,
        VERIFIED,
    ),
    ("SwitchWide", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("SwitchBool", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    ("PartialInit", TRUSTED_IMPLIES, VERIFIED, VERIFIED, VERIFIED),
    (
        "MinU64/fused",
        TRUSTED_IMPLIES,
        VERIFIED,
        VERIFIED,
        VERIFIED,
    ),
    (
        "BoolParam/fallthrough",
        TRUSTED_IMPLIES,
        VERIFIED,
        VERIFIED,
        VERIFIED,
    ),
    (
        "EarlyReturn/test",
        TRUSTED_IMPLIES,
        VERIFIED,
        VERIFIED,
        VERIFIED,
    ),
];

/// Step 1 of slice 6: the canonical theorems, generated THROUGH THE REAL
/// BUILDER, replay on this host's admitted AY with a Clean-accepted proof;
/// the rejected spellings replay to their pinned outcomes; and every wrong
/// lowering is refuted with a counterexample. The recorded gaps are compared
/// only under the replayer pair they were measured with
/// ([`assert_qualification_replayer`]).
///
/// `TCG_X86_BODY_QUALIFY_DUMP=<dir>` writes every replayed query there.
/// A diagnostic, not a check: every slice-6 fixture's LIR, machine rows and
/// theorem (or refusal). It lives here, outside the solver-free gate's
/// `slice6::` filter, which counts an ignored test as a skip.
#[test]
#[ignore]
fn print_slice_six_fixtures() {
    use super::slice5::describe;
    use super::slice6::{all_slice_six_shapes, describe_lir, slice6_pair};
    for shape in all_slice_six_shapes() {
        let (source, machine) = slice6_pair(shape);
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

#[test]
fn host_qualification_replays_the_slice_six_body_theorems() {
    let test = "host_qualification_replays_the_slice_six_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let (uncertified, spellings) = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        let mut spellings = Vec::new();
        for (label, source, machine) in slice_six_qualification_cases() {
            let owner = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("{}.smt2", label.replace('/', "__"))),
                    &smt2,
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let result = request
                .ay()
                .verify_fresh_source_bound(&owner, &replay_config());
            eprintln!(
                "X86_BODY_SLICE6_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_SLICE6_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push((label.clone(), stable_outcome(&result)));
            }
            // The rejected spellings of a several-path theorem, each a
            // re-spelling of its plain spelling (the claims as built; slice
            // 18's canonical spelling value-numbers them).
            let plain = plain_theorem(&source, &machine);
            let plain_smt2 = generate_smt2_query_raw(&plain, &replay_config());
            if plain.trust_ir_expr != E::bool_const(true)
                || !matches!(&plain.aarch64_expr, E::And { lhs, .. }
                    if matches!(lhs.as_ref(), E::Or { .. }))
            {
                continue;
            }
            let replay = |form: &ProofObligation, text: Option<&str>| {
                let verdict = match text {
                    Some(text) => {
                        crate::ay_bridge::verify_respelled_query(form, &replay_config(), text)
                    }
                    None => {
                        crate::ay_bridge::verify_with_cli_raw_attributed(form, &replay_config())
                    }
                };
                assert!(
                    !matches!(verdict.result, AYResult::CounterExample(_)),
                    "{label}: a spelling of a correct lowering was refuted: {:?}",
                    verdict.result
                );
                outcome(&verdict.result)
            };
            let implies = replay(&plain, Some(&implies_spelling(&plain_smt2)));
            let every = theorem_with_path_encoding(
                &source,
                &machine,
                SYSV,
                PathEncoding {
                    elide_aliases: false,
                    cone_of_influence: false,
                    merge_at_observation: false,
                    dag: None,
                    bool_guards: false,
                    trim_long_chains: false,
                    inline_single_use: false,
                    value_number: ValueNumbering::Off,
                    bit_moves: false,
                    fold: false,
                    normal: normal::Groups::NONE,
                    pair_arithmetic: ArithPairs::Off,
                },
            )
            .unwrap();
            let every = replay(&every, None);
            let split = replay(&case_split(&plain), None);
            let merged = match theorem_with_path_encoding(
                &source,
                &machine,
                SYSV,
                PathEncoding {
                    merge_at_observation: true,
                    ..PathEncoding::CANONICAL
                },
            ) {
                Ok(form) => replay(&form, None),
                Err(_) => "-".to_owned(),
            };
            eprintln!(
                "X86_BODY_SLICE6_QUALIFICATION spellings={label} implies={implies} \
                 every-definition={every} case-split={split} merged={merged}"
            );
            spellings.push((label.clone(), implies, every, split, merged));
        }
        for (label, source, machine) in slice_six_refutations() {
            let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let refuted =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_SLICE6_QUALIFICATION refutation={label} result={:?}",
                refuted.result
            );
            assert!(
                matches!(refuted.result, AYResult::CounterExample(_)),
                "{label} must be refuted: {:?}",
                refuted.result
            );
        }
        (uncertified, spellings)
    });
    // The recorded outcomes are evidence about one replayer pair: compare
    // them only under that pair.
    let qualified = assert_qualification_replayer(&edits);
    let recorded = super::recorded_gaps(
        KNOWN_UNCERTIFIED_SLICE_SIX,
        "KNOWN_UNCERTIFIED_SLICE_SIX",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified slice-6 set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
    let recorded: Vec<(String, String, String, String, String)> = REJECTED_SPELLINGS
        .iter()
        .map(|(label, implies, every, split, merged)| {
            (
                (*label).to_owned(),
                (*implies).to_owned(),
                (*every).to_owned(),
                (*split).to_owned(),
                (*merged).to_owned(),
            )
        })
        .collect();
    // The one load-dependent record ([`VERIFIED_OR_CHECKER_TIMEOUT`]) matches
    // either of its two outcomes.
    assert_eq!(
        spellings.len(),
        recorded.len(),
        "the several-path qualification cases changed: {spellings:?}"
    );
    let spellings: Vec<(String, String, String, String, String)> = spellings
        .into_iter()
        .zip(&recorded)
        .map(|((label, implies, every, split, merged), expected)| {
            let merged = if expected.4 == VERIFIED_OR_CHECKER_TIMEOUT
                && (merged == VERIFIED || merged.contains(crate::ay_bridge::CLEAN_CHECK_TIMEOUT))
            {
                VERIFIED_OR_CHECKER_TIMEOUT.to_owned()
            } else {
                merged
            };
            (label, implies, every, split, merged)
        })
        .collect();
    assert_eq!(
        spellings, recorded,
        "a rejected slice-6 spelling changed outcome on this host; review the encoding note in \
         build_theorem"
    );
}

/// With the real tools, every covered row of every certified slice-6 shape is
/// Formal under the body theorem (the conditional jumps and the compares that
/// feed them included), the function is promotable and its exports bind the
/// ABI; a wrong lowering the Rust check cannot judge fails every covered row.
#[test]
fn verifier_credits_every_bound_slice_six_row_with_the_replayed_body_theorem() {
    let test = "verifier_credits_every_bound_slice_six_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    // The per-host gap view this lane branches on was recorded with one
    // replayer pair: check the pair before the first replay.
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in SLICE_SIX {
            let label = format!("{shape:?}");
            let (source, machine) = slice6_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            if super::gap_applies_here(
                KNOWN_UNCERTIFIED_SLICE_SIX,
                "KNOWN_UNCERTIFIED_SLICE_SIX",
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
            // The conditional jumps are covered, and credited, like the
            // value rows.
            for ordinal in find(&machine, X86Opcode::Jcc) {
                assert!(owner.covers(ordinal), "{label}: Jcc row {ordinal}");
            }
            let inventory = report.report().emitted_opcode_inventory();
            assert!(inventory.is_promotable(), "{label}: {inventory:?}");
            assert_eq!(exports.len(), owner.bound_rows().len(), "{label}");
            assert!(report.matches_x86_input(&machine, Some(&source), SYSV));
        }
        // Wrong lowerings the Rust check cannot judge: refuted, every covered
        // row fails and nothing is exported.
        for (label, source, machine) in slice_six_refutations() {
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
