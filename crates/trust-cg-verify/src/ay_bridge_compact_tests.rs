// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Compact text is only a proof-producer input. Original raw bytes remain the
//! independently checked problem, counterexample/model source and identity.
//! Managed negative controls run real admitted AY and the captured checker;
//! they never synthesize a successful proof, receipt or cache authority.

use super::*;
use crate::FunctionVerificationRequest;
use crate::lowering_proof::{MachineSideProvenance, TransvalCheckKind};
use crate::provenance_xcheck::ProvenanceXCheckMode;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use crate::source_bound_frame::bind_read_only_source;
use crate::{FunctionVerifier, VerificationConfig};
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use sha2::{Digest, Sha256};
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use trust_cg_codegen::CoreHostJitTarget;

fn obligation(name: &str, lhs: SmtExpr, rhs: SmtExpr) -> ProofObligation {
    ProofObligation {
        name: name.into(),
        trust_ir_expr: lhs,
        aarch64_expr: rhs,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn with_original_query(check: impl FnOnce(&ProofObligation)) {
    with_original_query_lir(|_| {}, check);
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn with_original_query_lir(
    prepare: impl FnOnce(&mut trust_cg_lower::Function),
    check: impl FnOnce(&ProofObligation),
) {
    let capture: serde_json::Value = serde_json::from_str(include_str!(
        "../tests/fixtures/ty_original_read_only_predicate.json"
    ))
    .unwrap();
    assert_eq!(capture["selection"]["unit_key"], "inv:Second");
    let original: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    assert!(original.target_info.is_none());
    assert_eq!(original.functions.len(), 1);
    assert_eq!(original.functions[0].id.index(), 60_004);
    let mut module = original.clone();
    module.target_info = Some(
        CoreHostJitTarget::detect()
            .expect("actual supported host")
            .trust_ir_target_info()
            .clone(),
    );
    let mut restored = module.clone();
    restored.target_info = None;
    assert_eq!(
        serde_json::to_value(restored).unwrap(),
        serde_json::to_value(original).unwrap()
    );
    let (mut lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    prepare(&mut lir);
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    assert_eq!(source.read_requirements().len(), 3);
    assert_eq!(source.return_obligation().preconditions.len(), 6);
    check(source.return_obligation());
}

fn canonical_config() -> AYConfig {
    // Historical captured raw-artifact options, for deterministic byte golden
    // checking only. Live controls use live_source_bound_config below.
    AYConfig {
        solver: None,
        timeout_ms: 30_000,
        produce_models: true,
    }
}

fn prelude(script: &str) -> &str {
    script
        .split_once("\n(assert ")
        .expect("one canonical assertion")
        .0
}

#[test]
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn original_ty_historical_byte_gep_query_is_reproducible() {
    // Historical artifact reconstruction only. The adapter used Iadd before
    // the byte-address carrier migration; production never substitutes it.
    with_original_query_lir(
        |lir| {
            let mut replaced = 0;
            for block in lir.blocks.values_mut() {
                for instruction in &mut block.instructions {
                    if matches!(
                        instruction.opcode,
                        trust_cg_lower::instructions::Opcode::ArrayGep {
                            elem_ty: trust_cg_lower::Type::I8
                        }
                    ) {
                        instruction.opcode = trust_cg_lower::instructions::Opcode::Iadd;
                        replaced += 1;
                    }
                }
            }
            assert_eq!(replaced, 3, "exact retained fixture's three byte offsets");
        },
        |ob| {
            let config = canonical_config();
            let legacy = legacy_right_spine_query_for_test(ob, &config);
            assert_eq!(legacy.len(), 529_206);
            assert_eq!(
                format!("{:x}", Sha256::digest(legacy.as_bytes())),
                "a09a5dfcbf719c336ab087dd55a37f66360cf9abeff8aac89e6441bc9c4acc06"
            );
            let canonical = generate_smt2_query_raw(ob, &config);
            assert_eq!(canonical.len(), 529_206);
            assert_eq!(
                format!("{:x}", Sha256::digest(canonical.as_bytes())),
                "0399f60323fc9b6a21f3697fc650665d09eb5ce4871f19fdd899cb6bcf08df79"
            );
        },
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn original_ty_byte_gep_canonical_query_retains_entire_query_envelope() {
    with_original_query(|ob| {
        let config = canonical_config();
        let before = generate_smt2_query_raw(ob, &config);
        let (original, producer) = source_bound_query_scripts(ob, &config);
        assert_eq!(original, before);
        // The current adapter's ArrayGep query has its own identity. The
        // separate historical reconstruction retains the pre-migration bytes.
        let legacy = legacy_right_spine_query_for_test(ob, &config);
        assert_eq!(legacy.len(), 419_230);
        assert_eq!(
            format!("{:x}", Sha256::digest(legacy.as_bytes())),
            "33b92052cca3d978114e9d858393a8a4408184c7b7d8522ba0f79c089d7d95a4"
        );
        assert_eq!(prelude(&original), prelude(&legacy));
        assert_eq!(original.len(), 419_230);
        assert_ne!(original, legacy);
        let canonical_sha256 = format!("{:x}", Sha256::digest(original.as_bytes()));
        assert_eq!(
            canonical_sha256, "5d786615949b33670102030daec0bf09d1ac36e6d4bfafb0f35818b169312a9f",
            "byte-GEP midpoint-conjunction-v2 original query identity"
        );
        let producer = producer
            .expect("actual large shared original source must obtain a compact producer view");
        assert_eq!(
            prelude(&producer),
            prelude(&original),
            "ALL declarations/options/logic remain original, not a compact census"
        );
        assert!(producer.ends_with(")\n(check-sat)\n(exit)"));
        assert!(original.ends_with(")\n(check-sat)\n(exit)"));
        assert!(producer.contains("(assert (let ("));
        assert!(producer.len() <= original.len() * 3 / 4);
        assert!(
            prelude(&producer)
                .contains("(declare-fun entry_memory () (Array (_ BitVec 64) (_ BitVec 8)))")
        );
        for declaration in original
            .lines()
            .filter(|line| line.starts_with("(declare-") || line.starts_with("(set-"))
        {
            assert!(producer.lines().any(|line| line == declaration));
        }
        println!(
            "TY_COMPACT_BYTE_GEP_CANONICAL_QUERY original_bytes={} producer_bytes={} right_spine_sha256=33b92052cca3d978114e9d858393a8a4408184c7b7d8522ba0f79c089d7d95a4 canonical_sha256={canonical_sha256} formula_protocol={} independent_proof=false",
            original.len(),
            producer.len(),
            crate::lowering_proof::CANONICAL_PROOF_FORMULA_PROTOCOL,
        );
    });
}

fn combine(mut values: Vec<SmtExpr>) -> SmtExpr {
    assert!(values.len().is_power_of_two());
    while values.len() > 1 {
        values = values
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| pair[0].clone().and_expr(pair[1].clone()))
            .collect();
    }
    values.pop().unwrap()
}

#[test]
fn small_unsupported_and_less_than_twenty_five_percent_savings_remain_raw() {
    let config = canonical_config();
    let mut small = obligation(
        "compact small control",
        SmtExpr::var("x", 32),
        SmtExpr::bv_const(1, 32),
    );
    small.inputs = vec![("x".into(), 32)];
    let (raw, candidate) = source_bound_query_scripts(&small, &config);
    assert!(raw.len() < 16_384);
    assert!(candidate.is_none());
    assert_eq!(raw, generate_smt2_query_raw(&small, &config));

    let mut wide = obligation(
        "compact reduction threshold control",
        SmtExpr::BoolConst(true),
        combine(
            (0..256)
                .map(|i| {
                    SmtExpr::var(format!("ordinary_input_{i:03}_{}", "x".repeat(64)), 32)
                        .eq_expr(SmtExpr::bv_const(i, 32))
                })
                .collect(),
        ),
    );
    wide.inputs = (0..256)
        .map(|i| (format!("ordinary_input_{i:03}_{}", "x".repeat(64)), 32))
        .collect();
    let formula = wide.negated_equivalence();
    let (raw, candidate) = source_bound_query_scripts(&wide, &config);
    assert!(raw.len() >= 16_384);
    let view = crate::smt_raw_print::compact_formula(&formula, &raw)
        .unwrap()
        .unwrap();
    assert!(
        prelude(&raw).len() + view.text.len() + 33 > raw.len() * 3 / 4,
        "not an unsupported-printer refusal: actual generic geometry fails the savings threshold"
    );
    assert!(candidate.is_none());
    assert_eq!(raw, generate_smt2_query_raw(&wide, &config));

    // Large declared input inventory clears the size threshold, while the
    // explicit implicit-memory operation remains outside compact printing.
    wide.aarch64_expr = SmtExpr::MemLoad {
        addr: Arc::new(SmtExpr::var(
            "ordinary_input_000_".to_owned() + &"x".repeat(64),
            32,
        )),
        load_bits: 32,
        signed: false,
        result_width: 32,
    };
    wide.trust_ir_expr = SmtExpr::bv_const(0, 32);
    let (raw, candidate) = source_bound_query_scripts(&wide, &config);
    assert!(raw.len() >= 16_384);
    assert!(candidate.is_none());
    assert_eq!(raw, generate_smt2_query_raw(&wide, &config));
}

#[test]
fn replay_protocol_requires_original_check_persistence_and_raw_sat_fallback() {
    let protocol = replay_protocol_description();
    for required in [
        crate::lowering_proof::CANONICAL_PROOF_FORMULA_PROTOCOL,
        "query=original raw (no arithmetic simplifier)",
        "bounded QF DAG-let producer candidate",
        "independently checked/persisted ONLY against original raw",
        "candidate falls back raw without SAT or negative-memo credit",
        "compact occurrences bypass negative caching",
        "checker/persistence still bound to the original conjunction",
    ] {
        assert!(
            protocol.contains(required),
            "actual replay protocol lacks {required:?}"
        );
    }
}

#[test]
fn quantifier_free_view_borrows_the_exact_shared_graph_without_clone_or_expansion() {
    let leaf = Arc::new(SmtExpr::var("qf_shared", 32));
    let mut expression = Arc::new(SmtExpr::BvAdd {
        lhs: leaf.clone(),
        rhs: leaf,
        width: 32,
    });
    // The expanded expression tree has over a billion nodes. The actual DAG
    // and the exhaustive quantifier census stay linear in its 33 nodes.
    for _ in 0..30 {
        expression = Arc::new(SmtExpr::BvAdd {
            lhs: expression.clone(),
            rhs: expression,
            width: 32,
        });
    }
    assert!(!has_quantifiers(&expression));
    let view = quantifier_expanded_view(&expression);
    assert!(matches!(view, std::borrow::Cow::Borrowed(_)));
    assert!(std::ptr::eq(view.as_ref(), expression.as_ref()));
}

#[test]
fn quantifier_census_visits_inline_uf_and_untaken_arms_without_scope_substitution() {
    let quantified = SmtExpr::forall(
        "bound",
        32,
        SmtExpr::bv_const(0, 32),
        SmtExpr::bv_const(2, 32),
        SmtExpr::var("bound", 32).bvult(SmtExpr::bv_const(3, 32)),
    );
    let formula = SmtExpr::ite(
        SmtExpr::BoolConst(false),
        SmtExpr::uf("holds", vec![quantified], SmtSort::Bool),
        SmtExpr::BoolConst(true),
    );
    assert!(has_quantifiers(&formula));
    let view = quantifier_expanded_view(&formula);
    assert!(matches!(view, std::borrow::Cow::Owned(_)));
    assert_eq!(view.as_ref(), &expand_bounded_quantifiers(&formula));
}

fn with_managed_request(check: impl FnOnce(&FunctionVerificationRequest, &AYConfig)) {
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active());
            assert!(request.reuse_identity().is_none());
            request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                assert!(config.produce_models);
                let authority = request
                    .ay()
                    .authority
                    .as_ref()
                    .expect("actual admitted managed solver authority required, no skip");
                assert_eq!(
                    authority.solver().sha256(),
                    request.ay_solver().unwrap().sha256()
                );
                assert!(
                    authority.checker().is_some(),
                    "actual pinned capable independent checker required, no skip"
                );
                check(&request, &config);
            });
        },
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn prepared_compact_query_key_is_the_original_under_the_same_real_authority() {
    with_managed_request(|request, config| {
        with_original_query(|ob| {
            let queries = source_bound_query_scripts(ob, config);
            let original = queries.0.clone();
            let producer = queries
                .1
                .clone()
                .expect("actual original source compact view");
            let captured = request.ay();
            let authority = captured.authority.as_ref().unwrap();
            let identity = authority.solver().sha256().to_owned();
            let authority_id = authority
                .cache_id_with_solver_identity(&identity)
                .expect("real captured checker/solver/environment identity");
            // Inspect construction only: do not execute this metadata object
            // or give the deliberately nonreusable request a reuse receipt.
            let prepared = PreparedAyQuery::from_queries(
                ob,
                AYConfig {
                    solver: config.solver.clone(),
                    timeout_ms: config.timeout_ms,
                    produce_models: config.produce_models,
                },
                captured.selection.clone(),
                authority.clone(),
                identity.clone(),
                authority_id,
                (queries.0, queries.1, true),
            );
            assert_eq!(prepared.smt2, original);
            assert_eq!(prepared.producer_smt2.as_deref(), Some(producer.as_str()));
            assert_eq!(
                prepared.query_key(),
                verdict_cache_key_v2(&identity, &original)
            );
            assert_ne!(
                prepared.query_key(),
                verdict_cache_key_v2(&identity, &producer)
            );
            assert_eq!(
                prepared.binding().query_key,
                verdict_cache_key_v2(&identity, &original)
            );
            assert_eq!(prepared.authority_id(), authority_id);
            assert!(prepared.source_bound);
            assert!(request.reuse_identity().is_none());
        });
    });
}

fn substituted_assertion(original: &str, assertion: &str) -> String {
    format!(
        "{}\n(assert {assertion})\n(check-sat)\n(exit)",
        prelude(original)
    )
}

#[test]
fn managed_malicious_unsat_producer_cannot_certify_an_original_sat_problem() {
    with_managed_request(|request, config| {
        let ob = obligation(
            "compact malicious UNSAT producer control",
            SmtExpr::BoolConst(true),
            SmtExpr::BoolConst(false),
        );
        let original = generate_smt2_query_raw(&ob, config);
        let malicious = substituted_assertion(&original, "false");
        let captured = request.ay();
        let authority = captured.authority.as_ref().unwrap();
        let query = AyQueryText {
            original: &original,
            producer: Some(&malicious),
            closed_definitions: false,
            fresh_after_resident_timeout: false,
        };
        let candidate =
            run_fresh_producer_query_once(authority, &ob, config, query, &ReplayWitness::new(None));
        assert!(
            !matches!(candidate, AYResult::Verified),
            "a proof of assert-false cannot certify the ORIGINAL definitely SAT problem: {candidate:?}"
        );
        let (result, source) = verify_with_cli_smt2_under_authority(
            &ob,
            config,
            query,
            &captured.selection,
            authority,
            request.recording_active(),
            None,
        );
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "common funnel must return real ORIGINAL SAT, not producer refusal/UNSAT/Unknown: {result:?}"
        );
        assert!(matches!(source, AyVerdictSource::LiveSolve));
        assert_eq!(
            authority.solver().sha256(),
            request.ay_solver().unwrap().sha256()
        );
        assert!(request.reuse_identity().is_none());
        println!(
            "COMPACT_MALICIOUS_PRODUCER candidate={candidate:?} original_result={result:?} source={source:?} solver_sha256={} certified=false",
            authority.solver().sha256()
        );
    });
}

#[test]
fn managed_sat_producer_cannot_supply_another_problem_model() {
    with_managed_request(|request, config| {
        let mut ob = obligation(
            "compact different SAT model control",
            SmtExpr::BoolConst(true),
            SmtExpr::BoolConst(false),
        );
        ob.inputs = vec![("x".into(), 32)];
        ob.preconditions = vec![SmtExpr::var("x", 32).eq_expr(SmtExpr::bv_const(1, 32))];
        let original = generate_smt2_query_raw(&ob, config);
        let other = substituted_assertion(&original, "(= x (_ bv2 32))");
        let captured = request.ay();
        let authority = captured.authority.as_ref().unwrap();
        let query = AyQueryText {
            original: &original,
            producer: Some(&other),
            closed_definitions: false,
            fresh_after_resident_timeout: false,
        };
        let candidate =
            run_fresh_producer_query_once(authority, &ob, config, query, &ReplayWitness::new(None));
        assert!(
            matches!(candidate, AYResult::CounterExample(_)),
            "actual producer x=2 query must be SAT, not structurally refused: {candidate:?}"
        );
        let (result, source) = verify_with_cli_smt2_under_authority(
            &ob,
            config,
            query,
            &captured.selection,
            authority,
            request.recording_active(),
            None,
        );
        let AYResult::CounterExample(values) = &result else {
            panic!(
                "common funnel must rerun ORIGINAL SAT and its model, not producer SAT: {result:?}"
            )
        };
        assert_eq!(
            values,
            &[("x".into(), 1)],
            "only the ORIGINAL x=1 model is an actual counterexample"
        );
        assert!(matches!(source, AyVerdictSource::LiveSolve));
        assert!(request.reuse_identity().is_none());
        println!(
            "COMPACT_SAT_MODEL_PRODUCER candidate={candidate:?} original_result={result:?} source={source:?} solver_sha256={} certified=false producer_model_authority=false",
            authority.solver().sha256()
        );
    });
}

#[test]
fn boolean_constant_equalities_preserve_all_small_word_assignments() {
    let a = SmtExpr::var("a", 2).eq_expr(SmtExpr::bv_const(1, 2));
    let b = SmtExpr::var("b", 2).eq_expr(SmtExpr::bv_const(2, 2));
    for condition in [a.clone(), a.clone().and_expr(b.clone()), a.or_expr(b)] {
        for value in [false, true] {
            for expression in [
                condition.clone().eq_expr(SmtExpr::bool_const(value)),
                SmtExpr::bool_const(value).eq_expr(condition.clone()),
            ] {
                let simplified = simplify_solver_expr(&expression);
                assert!(
                    !matches!(&simplified, SmtExpr::Eq { lhs, rhs }
                        if matches!(lhs.as_ref(), SmtExpr::BoolConst(_))
                            || matches!(rhs.as_ref(), SmtExpr::BoolConst(_))),
                    "Boolean constant wrapper must disappear; the inner word equality stays"
                );
                for bits in 0..16 {
                    let mut env = crate::smt::EvalEnv::default();
                    env.insert("a".into(), bits & 3);
                    env.insert("b".into(), bits >> 2);
                    assert_eq!(
                        expression.try_eval(&env).unwrap(),
                        simplified.try_eval(&env).unwrap()
                    );
                }
            }
        }
    }
}
