// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::smt::{EvalEnv, SmtSort};
use std::convert::Infallible;

fn observed() -> NativeAggregateTargetObservations {
    let (m, l, c, s, t, b) = super::super::tests::fixture(1);
    observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &b).unwrap()
}

// Concrete evaluation of independent outcomes is a control, not a provider
// proof. Assign every unconstrained leaf explicitly and preserve array sorts.
fn value(expression: &E, assignments: &[(&E, E)]) -> bool {
    expression
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok(assignments
                .iter()
                .find(|(key, _)| *key == node)
                .map(|(_, v)| v.clone())
                .or_else(|| match node {
                    E::UF { args, ret_sort, .. } if args.is_empty() => Some(match ret_sort {
                        SmtSort::Bool => E::BoolConst(true),
                        SmtSort::BitVec(bits) => E::bv_const(0, *bits),
                        SmtSort::Array(_, _) => {
                            E::const_array(SmtSort::BitVec(64), E::bv_const(0, 8))
                        }
                        _ => panic!("non-scalar fixture"),
                    }),
                    E::Var { width, .. } => Some(E::bv_const(0, *width)),
                    _ => None,
                }))
        })
        .unwrap()
        .unwrap_or_else(|| expression.clone())
        .eval(&EvalEnv::default())
        .as_bool()
}

#[test]
fn actual_pair_outcome_requires_both_lanes_normality_and_post_world() {
    let observed = observed();
    let requirements = observed
        .provider_footprint_requirements(observed.calls()[0].site(), &[])
        .unwrap();
    let source = requirements.source_event();
    let call = requirements.call();
    assert!(std::ptr::eq(call, &observed.calls()[0]));
    assert_eq!(call.before_registers().len(), 32);
    assert_eq!(call.after_registers().len(), 32);
    assert_eq!(source.record().fields().len(), 2);
    let relation = requirements.required_outcome_relation();
    assert!(value(relation, &[]));
    let mut missing_event = self::observed();
    missing_event.effects.calls[0].guard = E::BoolConst(false);
    let missing = missing_event
        .provider_footprint_requirements(missing_event.calls()[0].site(), &[])
        .unwrap();
    assert!(!value(missing.required_outcome_relation(), &[]));
    assert!(value(
        relation,
        &[
            (source.returned_normally(), E::BoolConst(false)),
            (call.returned_normally(), E::BoolConst(false)),
            (&call.after_registers()[1], E::bv_const(999, 64)),
        ]
    ));
    for lane in [0, 1] {
        assert!(!value(
            relation,
            &[(&call.after_registers()[lane], E::bv_const(1, 64))]
        ));
    }
    assert!(!value(
        relation,
        &[(call.returned_normally(), E::BoolConst(false))]
    ));
    let changed = E::store(
        E::const_array(SmtSort::BitVec(64), E::bv_const(0, 8)),
        E::bv_const(201, 64),
        E::bv_const(1, 8),
    );
    assert!(!value(relation, &[(call.post_world(), changed)]));
    // Error status is still a normally returned two-lane outcome. Its payload
    // cannot be dropped merely because status is nonzero.
    assert!(value(
        relation,
        &[
            (&source.record().fields()[0], E::bv_const(8, 64)),
            (&call.after_registers()[0], E::bv_const(8, 64)),
        ]
    ));
    assert!(!value(
        relation,
        &[
            (&source.record().fields()[0], E::bv_const(8, 64)),
            (&call.after_registers()[0], E::bv_const(8, 64)),
            (&call.after_registers()[1], E::bv_const(99, 64)),
        ]
    ));
}

#[test]
fn provider_regions_do_not_prove_effect_completeness_or_abi() {
    let observed = observed();
    let regions =
        [NativeProviderWriteRegion::new(E::bv_const(100, 64), E::bv_const(16, 64)).unwrap()];
    let requirements = observed
        .provider_footprint_requirements(observed.calls()[0].site(), &regions)
        .unwrap();
    let call = requirements.call();
    let memory = E::const_array(SmtSort::BitVec(64), E::bv_const(0, 8));
    let changed = E::store(memory, E::bv_const(201, 64), E::bv_const(1, 8));
    assert!(!value(
        requirements.required_outside_byte_relation(),
        &[
            (call.post_world(), changed),
            (&E::var("observe", 64), E::bv_const(201, 64)),
        ]
    ));
    assert!(!value(
        requirements.required_register_preservation(),
        &[(&call.after_registers()[19], E::bv_const(7, 64)),]
    ));
    assert!(value(
        requirements.required_register_preservation(),
        &[
            (&call.after_registers()[0], E::bv_const(7, 64)),
            (&call.after_registers()[30], E::bv_const(9, 64)),
        ]
    ));
    assert_eq!(call.outstanding_requirements().len(), 6);
    let query = requirements
        .conditional_framing_obligation(E::bv_const(200, 64), 8)
        .unwrap();
    assert!(
        query
            .preconditions
            .contains(requirements.required_outside_byte_relation())
    );
    assert_ne!(
        &query.trust_ir_expr,
        requirements.required_outside_byte_relation()
    );
    assert!(
        requirements
            .conditional_framing_obligation(E::bv_const(200, 64), 0)
            .is_err()
    );
}

#[test]
fn regions_preserve_modular_geometry_and_refuse_foreign_or_excess_inputs() {
    for name in [
        "x) (assert false) (",
        "|quoted|",
        "white space",
        "line\nbreak",
    ] {
        assert!(NativeProviderWriteRegion::new(E::var(name, 64), E::bv_const(8, 64)).is_err());
    }
    assert!(NativeProviderWriteRegion::new(E::BoolConst(true), E::bv_const(8, 64)).is_err());
    assert!(NativeProviderWriteRegion::new(E::bv_const(1, 64), E::bv_const(8, 32)).is_err());
    for (start, length, expected) in [
        (u64::MAX, 1, true),
        (u64::MAX, 2, false),
        (u64::MAX, 0, true),
    ] {
        let region =
            NativeProviderWriteRegion::new(E::bv_const(start, 64), E::bv_const(length, 64))
                .unwrap();
        assert_eq!(value(&region.nonwrapping_demand(), &[]), expected);
    }
    let observed = observed();
    let symbolic =
        [
            NativeProviderWriteRegion::new(E::var("write_base", 64), E::var("write_size", 64))
                .unwrap(),
        ];
    let symbolic_requirements = observed
        .provider_footprint_requirements(observed.calls()[0].site(), &symbolic)
        .unwrap();
    let query = symbolic_requirements
        .conditional_framing_obligation(E::var("saved_base", 64), 8)
        .unwrap();
    for name in ["write_base", "write_size", "saved_base"] {
        assert_eq!(
            query
                .inputs
                .iter()
                .filter(|(input, bits)| input == name && *bits == 64)
                .count(),
            1
        );
    }
    let E::UF { name, .. } = observed.calls()[0].post_world() else {
        panic!("stored world")
    };
    let collision = [NativeProviderWriteRegion::new(E::var(name, 64), E::bv_const(8, 64)).unwrap()];
    let collision = observed
        .provider_footprint_requirements(observed.calls()[0].site(), &collision)
        .unwrap();
    assert!(
        collision
            .conditional_framing_obligation(E::bv_const(200, 64), 8)
            .is_err()
    );
    assert!(
        observed
            .provider_footprint_requirements(
                ReadOnlySite {
                    block: 99,
                    instruction: 99
                },
                &[]
            )
            .is_err()
    );
    let regions = (0..65)
        .map(|_| NativeProviderWriteRegion::new(E::bv_const(0, 64), E::bv_const(0, 64)).unwrap())
        .collect::<Vec<_>>();
    assert!(matches!(
        observed.provider_footprint_requirements(observed.calls()[0].site(), &regions),
        Err(ReadOnlySourceError::Budget("native provider write regions"))
    ));
}

#[test]
fn framing_queries_retain_actual_definitions_and_missing_law_controls() {
    let observed = observed();
    let regions =
        [NativeProviderWriteRegion::new(E::bv_const(100, 64), E::bv_const(16, 64)).unwrap()];
    let requirement = observed
        .provider_footprint_requirements(observed.calls()[0].site(), &regions)
        .unwrap();
    let query = requirement
        .conditional_framing_obligation(E::bv_const(200, 64), 8)
        .unwrap();
    match crate::closed_definition_alethe::compose(&query) {
        Ok(candidate) => println!(
            "PROVIDER_FRAMING_CANDIDATE={}",
            serde_json::json!({
                "proof":candidate.text,"steps":candidate.steps,"definitions":candidate.definitions,
                "checked":false,
            })
        ),
        Err(error) => println!("PROVIDER_FRAMING_CANDIDATE_REFUSAL={error}"),
    }
    let original_definitions = observed
        .source()
        .definitions()
        .iter()
        .chain(observed.definitions())
        .count();
    assert_eq!(query.preconditions.len(), original_definitions + 4);
    assert!(
        query.preconditions[..original_definitions]
            .iter()
            .eq(observed
                .source()
                .definitions()
                .iter()
                .chain(observed.definitions()))
    );
    let mut missing = query.clone();
    missing.name.push_str(" without provider law");
    assert_eq!(
        missing.preconditions.pop().as_ref(),
        Some(requirement.required_outside_byte_relation())
    );
    for (name, query, verdict) in [
        ("with-law", query, "unsat"),
        ("missing-law", missing, "sat"),
    ] {
        let raw = crate::ay_bridge::generate_smt2_query_raw(
            &query,
            &crate::ay_bridge::AYConfig {
                solver: None,
                timeout_ms: crate::ay_bridge::DEFAULT_AY_TIMEOUT_MS,
                produce_models: true,
            },
        );
        println!(
            "PROVIDER_FOOTPRINT_CONTROL={}",
            serde_json::json!({
                "name":name,"expected":verdict,"query":raw,"provider_law_proved":false,
                "outcome_proved":false,"native_credit":false,
            })
        );
    }
}
