//! Vacuous-sample regression tests (TRUSTCG-02).
//!
//! A sampling sweep in which no sampled point satisfies the preconditions has
//! compared nothing, so it must end in an explicit `Unknown`, never `Valid` —
//! on every sampling route: the shared-width and multi-input sweeps, batched,
//! scalar-compiled and interpreted evaluation, sequential and chunked, the
//! structural-identity short-circuit and the process-wide memo. And a
//! precondition the evaluator cannot interpret is named even when an earlier
//! precondition is false at every point.

use super::*;
use crate::smt::SmtSort;

/// The reason prefix of [`sampled_sweep_verdict`]'s `Unknown`.
const VACUOUS: &str = "vacuous sample";

/// Every edge value either sweep assigns a 64-bit input.
const EDGES_64: [u64; 6] = [0, 1, u64::MAX, u64::MAX - 1, 1 << 63, (1 << 63) - 1];

fn var(name: &str) -> SmtExpr {
    SmtExpr::var(name, 64)
}

/// `a + b (+ c) == b + a (+ c)`: correct but NOT identical-sided (so the
/// structural-identity short-circuit cannot fire), over 64-bit inputs `names`.
/// Two names take the shared-width sweep; three take the multi-input sweep.
fn commuted_sum(name: &str, names: &[&str], preconditions: Vec<SmtExpr>) -> ProofObligation {
    let mut source = var(names[0]).bvadd(var(names[1]));
    let mut machine = var(names[1]).bvadd(var(names[0]));
    for extra in &names[2..] {
        source = source.bvadd(var(extra));
        machine = machine.bvadd(var(extra));
    }
    ProofObligation {
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: names.iter().map(|n| (n.to_string(), 64)).collect(),
        preconditions,
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

/// A precondition no point satisfies, in the compiled (batchable) subset.
fn never() -> SmtExpr {
    var("a").eq_expr(var("a")).not_expr()
}

/// A satisfiable precondition pinning `a` to one 64-bit value that is not an
/// edge case. The shared-width sweep never samples it; the multi-input
/// sweep's precondition-directed trials take the constant it names.
fn needle() -> SmtExpr {
    var("a").eq_expr(SmtExpr::bv_const(0x0123_4567_89ab_cdef, 64))
}

/// A satisfiable precondition no sweep samples, the directed trials included:
/// `a * K == C` holds at one 64-bit `a` (K is odd), which is neither a
/// constant the precondition names, a small value, an edge value nor an
/// aligned draw of any useful probability.
fn hidden_needle() -> SmtExpr {
    var("a")
        .bvmul(SmtExpr::bv_const(0x9e37_79b9_7f4a_7c15, 64))
        .eq_expr(SmtExpr::bv_const(0x0123_4567_89ab_cdef, 64))
}

/// Preconditions excluding every edge value of `a`: no edge-battery point of
/// either sweep satisfies them, while almost every random sample does.
fn not_an_edge() -> Vec<SmtExpr> {
    EDGES_64
        .iter()
        .map(|edge| var("a").eq_expr(SmtExpr::bv_const(*edge, 64)).not_expr())
        .collect()
}

fn is_vacuous(result: &VerificationResult) -> bool {
    matches!(result, VerificationResult::Unknown { reason } if reason.contains(VACUOUS))
}

/// Every sampling route for `ob`: the public entry, the memo, a pooled
/// (chunked) public entry, and the dispatch over batched, scalar-compiled and
/// interpreted evaluation.
fn every_route(
    ob: &ProofObligation,
    config: &VerificationConfig,
) -> Vec<(&'static str, VerificationResult)> {
    let batched = CompiledObligation::try_new(ob);
    let scalar = CompiledObligation::try_new_scalar_only(ob);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .expect("test pool");
    vec![
        ("public", verify_by_evaluation_with_config(ob, config)),
        ("memo", memoized_verify_by_evaluation(ob, config)),
        (
            "pooled",
            pool.install(|| verify_by_evaluation_with_config(ob, config)),
        ),
        (
            "batched",
            verify_by_evaluation_with_compiled(ob, config, batched.as_ref()),
        ),
        (
            "scalar",
            verify_by_evaluation_with_compiled(ob, config, scalar.as_ref()),
        ),
        (
            "interpreted",
            verify_by_evaluation_with_compiled(ob, config, None),
        ),
    ]
}

/// THE DEFECT: a precondition that no sampled point satisfies used to end the
/// sweep in `Valid`, although nothing was compared. Both sampling sweeps, on
/// every route, must now answer the explicit vacuous-sample `Unknown` — for an
/// unsatisfiable precondition and for a satisfiable one sampling never hits.
#[test]
fn sweep_with_no_satisfying_sample_is_unknown_not_valid() {
    let config = VerificationConfig::default();
    for names in [&["a", "b"][..], &["a", "b", "c"][..]] {
        for (label, pre) in [("never", never()), ("hidden needle", hidden_needle())] {
            let ob = commuted_sum(
                &format!("vacuous-sample {label} {names:?}"),
                names,
                vec![pre],
            );
            assert!(exhaustive_input_count(&ob, &config).is_none());
            assert_eq!(needs_multi_input_sampling(&ob), names.len() == 3);
            assert!(
                CompiledObligation::try_new(&ob).is_some_and(|co| co.batch.is_some()),
                "{}: must exercise the batched lane too",
                ob.name
            );
            for (route, result) in every_route(&ob, &config) {
                assert!(
                    is_vacuous(&result),
                    "{} via {route}: no sampled point satisfies the precondition, so the \
                     sweep compared nothing and must be the vacuous-sample Unknown, got \
                     {result:?}",
                    ob.name
                );
            }
        }
    }
}

/// The vacuous-sample reason reports how many points were tried: the 36-point
/// edge battery plus the configured random trials, on both sweeps, plus as
/// many precondition-directed trials on the multi-input sweep.
#[test]
fn vacuous_sample_reason_counts_every_attempted_point() {
    let config = VerificationConfig::with_sample_count(1_000);
    for (names, attempted) in [(&["a", "b"][..], 1036), (&["a", "b", "c"][..], 2036)] {
        let ob = commuted_sum("vacuous-sample attempt count", names, vec![never()]);
        let result = verify_by_evaluation_with_config(&ob, &config);
        assert!(
            matches!(&result, VerificationResult::Unknown { reason }
                if reason.contains(&format!("none of the {attempted} sampled inputs"))),
            "{names:?}: {result:?}"
        );
    }
}

/// NEW-CG-SAMPLER, THE DEFECT: the multi-input sweep draws an obligation's
/// inputs as consecutive outputs of one power-of-two-modulus LCG, so two
/// inputs are never both even, never equal, and never equal to a named
/// 64-bit constant. An obligation whose preconditions RELATE its inputs got
/// no evidence at all — and a claim that is FALSE exactly there was reported
/// as a vacuous sample instead of refuted. The precondition-directed trials
/// reach such points: the correct claim is `Valid`, the wrong one `Invalid`.
#[test]
fn directed_trials_reach_relational_preconditions_and_refute_there() {
    // Two 8-aligned, non-wrapping, disjoint addresses `a`, `b` and a value `c`.
    let aligned = |name: &str| {
        var(name)
            .bvand(SmtExpr::bv_const(7, 64))
            .eq_expr(SmtExpr::bv_const(0, 64))
    };
    let eight = || SmtExpr::bv_const(8, 64);
    let preconditions = vec![
        aligned("a"),
        aligned("b"),
        var("a").bvadd(eight()).bvugt(var("a")),
        var("b").bvadd(eight()).bvugt(var("b")),
        var("b")
            .bvuge(var("a").bvadd(eight()))
            .or_expr(var("a").bvuge(var("b").bvadd(eight()))),
    ];
    let correct = commuted_sum(
        "directed: relational",
        &["a", "b", "c"],
        preconditions.clone(),
    );
    // Wrong exactly when `b` is the address right after `a`.
    let mut wrong = correct.clone();
    wrong.name = "directed: relational, wrong when adjacent".to_string();
    wrong.aarch64_expr = SmtExpr::ite(
        var("b").eq_expr(var("a").bvadd(eight())),
        wrong.aarch64_expr.clone().bvadd(SmtExpr::bv_const(1, 64)),
        wrong.aarch64_expr.clone(),
    );
    let config = VerificationConfig::default();
    for ob in [&correct, &wrong] {
        assert!(needs_multi_input_sampling(ob));
        // The uniform half compares nothing: this is what the directed trials fix.
        let mut env = multi_input_sweep_env(ob);
        let mut scratch = Vec::new();
        let edge = multi_input_edge_battery(ob, None, &mut env, &mut scratch)
            .expect("the edge battery meets no precondition");
        let uniform = random_chunk_multi(ob, None, sample_seed(&ob.name), 0, 20_000, &env)
            .expect("no uniform point meets the preconditions");
        assert_eq!((edge, uniform), (0, 0), "{}", ob.name);
    }
    for (route, result) in every_route(&correct, &config) {
        assert!(
            matches!(result, VerificationResult::Valid),
            "{} via {route}: {result:?}",
            correct.name
        );
    }
    for (route, result) in every_route(&wrong, &config) {
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "{} via {route}: the claim is false at every adjacent aligned pair, got {result:?}",
            wrong.name
        );
    }
    let mut env = multi_input_sweep_env(&correct);
    let directed = directed_chunk_multi(&correct, None, DIRECTED_TRIAL_CAP, &mut env)
        .expect("a correct obligation has no terminal directed point");
    assert!(
        directed >= MIN_DIRECTED_EVIDENCE,
        "only {directed} directed points met the preconditions"
    );
}

/// The directed trials take the constants a precondition names, so the
/// multi-input sweep reaches `a == C` for a non-edge `C`; the shared-width
/// sweep has no directed trials and still reports the vacuous sample.
#[test]
fn directed_trials_reach_a_named_constant_on_the_multi_input_sweep_only() {
    let config = VerificationConfig::default();
    let multi = commuted_sum("directed: needle multi", &["a", "b", "c"], vec![needle()]);
    for (route, result) in every_route(&multi, &config) {
        assert!(
            matches!(result, VerificationResult::Valid),
            "{} via {route}: {result:?}",
            multi.name
        );
    }
    let two = commuted_sum("directed: needle two", &["a", "b"], vec![needle()]);
    for (route, result) in every_route(&two, &config) {
        assert!(is_vacuous(&result), "{} via {route}: {result:?}", two.name);
    }
}

/// A multi-input obligation with no preconditions gets no directed trials:
/// every uniform draw already satisfies them, and its sweep is unchanged.
#[test]
fn directed_trials_run_only_under_preconditions() {
    let free = commuted_sum("directed: none", &["a", "b", "c"], Vec::new());
    assert_eq!(directed_trial_count(&free, 100_000), 0);
    let guarded = commuted_sum("directed: guarded", &["a", "b", "c"], vec![needle()]);
    assert_eq!(directed_trial_count(&guarded, 100_000), DIRECTED_TRIAL_CAP);
    assert_eq!(directed_trial_count(&guarded, 1_000), 1_000);
    assert_eq!(directed_trial_count(&guarded, 0), 0);
}

/// Positive controls: one satisfying point is enough evidence to keep `Valid`,
/// whether it comes from the edge battery alone (no random trials at all) or
/// only from random samples (every edge value excluded).
#[test]
fn a_satisfying_sampled_point_keeps_valid() {
    for names in [&["a", "b"][..], &["a", "b", "c"][..]] {
        let edge_only = commuted_sum(
            "vacuous-sample control: edge witness",
            names,
            vec![var("a").eq_expr(SmtExpr::bv_const(0, 64))],
        );
        for (route, result) in every_route(&edge_only, &VerificationConfig::with_sample_count(0)) {
            assert!(
                matches!(result, VerificationResult::Valid),
                "{names:?} via {route}: an edge point satisfies `a == 0`: {result:?}"
            );
        }
        let random_only = commuted_sum(
            "vacuous-sample control: random witness",
            names,
            not_an_edge(),
        );
        for (route, result) in every_route(&random_only, &VerificationConfig::default()) {
            assert!(
                matches!(result, VerificationResult::Valid),
                "{names:?} via {route}: random samples satisfy `a` not an edge: {result:?}"
            );
        }
        // …and with the random half removed, the same preconditions leave the
        // edge battery with nothing to compare.
        let edges_only_config = VerificationConfig::with_sample_count(0);
        for (route, result) in every_route(&random_only, &edges_only_config) {
            assert!(
                is_vacuous(&result),
                "{names:?} via {route}: no edge point satisfies `a` not an edge: {result:?}"
            );
        }
    }
}

/// THE DEFECT, identity form: identical, trap-free, compiled sides used to
/// short-circuit to `Valid` whatever the preconditions, so the vacuous
/// obligation never reached the sweep. The short-circuit (and the memo's
/// lockstep copy) must return exactly what the full sweep returns: `Valid`
/// with an edge witness (short-circuited), `Valid` with only a random witness
/// (the sweep runs), and the vacuous-sample `Unknown` with no witness.
#[test]
fn identical_sides_do_not_short_circuit_a_vacuous_sample_to_valid() {
    let config = VerificationConfig::default();
    for names in [&["a", "b"][..], &["a", "b", "c"][..]] {
        let identical = |label: &str, preconditions: Vec<SmtExpr>| {
            let mut ob = commuted_sum(
                &format!("identical {label} {names:?}"),
                names,
                preconditions,
            );
            ob.aarch64_expr = ob.trust_ir_expr.clone();
            assert!(crate::smt::collect_trap_poison_decls(&ob.trust_ir_expr).is_empty());
            ob
        };
        let cases = [
            (identical("never", vec![never()]), false),
            (identical("hidden needle", vec![hidden_needle()]), false),
            // The multi-input sweep's directed trials take the named constant.
            (identical("needle", vec![needle()]), names.len() == 3),
            (identical("random witness", not_an_edge()), true),
            (
                identical(
                    "edge witness",
                    vec![var("a").eq_expr(SmtExpr::bv_const(0, 64))],
                ),
                true,
            ),
            (identical("no preconditions", Vec::new()), true),
        ];
        for (ob, valid) in cases {
            let compiled = CompiledObligation::try_new(&ob);
            let sweep = verify_by_evaluation_with_compiled(&ob, &config, compiled.as_ref());
            let public = verify_by_evaluation_with_config(&ob, &config);
            let memo = memoized_verify_by_evaluation(&ob, &config);
            for (route, result) in [("sweep", &sweep), ("public", &public), ("memo", &memo)] {
                if valid {
                    assert!(
                        matches!(result, VerificationResult::Valid),
                        "{} via {route}: {result:?}",
                        ob.name
                    );
                } else {
                    assert!(
                        is_vacuous(result),
                        "{} via {route}: identical sides with no sampled satisfying point \
                         must be the vacuous-sample Unknown, got {result:?}",
                        ob.name
                    );
                }
            }
        }
    }
}

/// THE DEFECT, ordering form: `preconditions_hold` stopped at the first false
/// precondition, so an unsupported precondition listed after one that is
/// false everywhere was never evaluated — the statistical sweep then ended in
/// `Valid`, and the exhaustive one in an Unknown that did not name it. The
/// uninterpretable precondition must be named on every sweep.
#[test]
fn unsupported_precondition_after_a_false_one_is_named() {
    let guard = || SmtExpr::uf("late_unsupported_guard", vec![], SmtSort::Bool);
    let exhaustive = {
        let a = SmtExpr::var("a", 4);
        let b = SmtExpr::var("b", 4);
        ProofObligation {
            name: "late guard exhaustive".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: b.bvadd(a.clone()),
            inputs: vec![("a".to_string(), 4), ("b".to_string(), 4)],
            preconditions: vec![a.clone().eq_expr(a).not_expr(), guard()],
            fp_inputs: Vec::new(),
            category: Some(TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::StaticDb,
        }
    };
    let two_input = commuted_sum("late guard 2-input", &["a", "b"], vec![never(), guard()]);
    let multi = commuted_sum("late guard multi", &["a", "b", "c"], vec![never(), guard()]);
    let config = VerificationConfig::with_sample_count(64);
    for ob in [&exhaustive, &two_input, &multi] {
        assert!(CompiledObligation::try_new(ob).is_none());
        for result in [
            verify_by_evaluation_with_config(ob, &config),
            memoized_verify_by_evaluation(ob, &config),
        ] {
            assert!(
                matches!(&result, VerificationResult::Unknown { reason }
                    if reason.contains("precondition 1") && reason.contains("late_unsupported_guard")),
                "{}: the unsupported precondition after a false one must be named, got \
                 {result:?}",
                ob.name
            );
        }
    }
    // Order does not matter: the same guard listed FIRST is named too.
    let mut first = two_input.clone();
    first.name = "late guard listed first".to_string();
    first.preconditions.reverse();
    assert!(matches!(
        verify_by_evaluation_with_config(&first, &config),
        VerificationResult::Unknown { reason } if reason.contains("late_unsupported_guard")
    ));
}

/// The chunk functions' evidence counts are the same number whichever
/// evaluator computes them — batched lanes, scalar tapes or the interpreter —
/// and are exactly the count of in-precondition samples: every sample with no
/// preconditions, none under an unsatisfiable one.
#[test]
fn chunk_satisfied_counts_agree_across_evaluators() {
    let quarter = var("a").bvult(SmtExpr::bv_const(1 << 62, 64));
    for names in [&["a", "b"][..], &["a", "b", "c"][..]] {
        for (label, preconditions) in [
            ("none", Vec::new()),
            ("never", vec![never()]),
            ("quarter", vec![quarter.clone()]),
            ("not an edge", not_an_edge()),
        ] {
            let ob = commuted_sum(&format!("chunk count {label}"), names, preconditions);
            let batched = CompiledObligation::try_new(&ob);
            assert!(batched.as_ref().is_some_and(|co| co.batch.is_some()));
            let scalar = CompiledObligation::try_new_scalar_only(&ob);
            let seed = sample_seed(&ob.name);
            let (start, count) = (1_000u64, 5_003u64);
            let run = |compiled: Option<&CompiledObligation>| {
                let chunk = if names.len() == 2 {
                    let env = two_input_sweep_env(&ob);
                    random_chunk_2(&ob, compiled, 64, seed, start, count, &env)
                } else {
                    let env = multi_input_sweep_env(&ob);
                    random_chunk_multi(&ob, compiled, seed, start, count, &env)
                };
                chunk.expect("a correct obligation has no terminal point")
            };
            let counts = [run(batched.as_ref()), run(scalar.as_ref()), run(None)];
            assert_eq!(counts[0], counts[1], "{label} {names:?}: batched vs scalar");
            assert_eq!(
                counts[1], counts[2],
                "{label} {names:?}: scalar vs interpreted"
            );
            match label {
                "none" => assert_eq!(counts[0], count),
                "never" => assert_eq!(counts[0], 0),
                // A quarter of uniform draws, give or take; the exact value is
                // pinned by the three-way agreement above.
                "quarter" => assert!((1_000..1_500).contains(&counts[0]), "{counts:?}"),
                _ => assert!(counts[0] >= count - 2, "{counts:?}"),
            }
        }
    }
}
