// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Candidate construction controls ONLY. Independent original-query checking
//! is performed under the captured authority by the connected replay controls.

use super::*;
use crate::lowering_proof::MachineSideProvenance;
use crate::memory_proofs::memory_sort;

fn obligation(left: E, right: E, premises: Vec<E>) -> ProofObligation {
    ProofObligation {
        name: "ordinary closed definition equality".into(),
        trust_ir_expr: left,
        aarch64_expr: right,
        inputs: vec![],
        preconditions: premises,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

fn word(name: &str) -> E {
    E::uf(name, vec![], SmtSort::BitVec(64))
}

fn inspect(original: &ProofObligation, definitions: usize) -> ClosedDefinitionCandidate {
    let before = original.clone();
    let candidate = compose(original).unwrap();
    assert_eq!(original, &before);
    assert_eq!(candidate.premises, original.preconditions.len());
    assert_eq!(candidate.definitions, definitions);
    assert_eq!(candidate.text.matches("(assume ").count(), 1);
    assert!(candidate.text.starts_with(&format!(
        "(assume cd0 {})\n",
        original.negated_equivalence()
    )));
    assert_eq!(candidate.steps, candidate.text.matches("(step ").count());
    assert!(!candidate.text.contains(":rule trust"));
    assert!(!candidate.text.contains(":rule hole"));
    // Only proof-local exact term macros; no new input declaration exists.
    assert!(!candidate.text.contains("declare-const"));
    assert!(!candidate.text.contains("declare-fun"));
    assert!(
        candidate
            .text
            .lines()
            .last()
            .unwrap()
            .contains("(cl) :rule resolution")
    );
    candidate
}

#[test]
fn actual_equations_not_names_establish_literal_address_correspondence() {
    let base = E::var("base", 64);
    let original = word("unrelated_source_name");
    let lower = word("no_ordinal_or_stage_prefix");
    let geometry = base
        .clone()
        .bvand(E::bv_const(7, 64))
        .eq_expr(E::bv_const(0, 64));
    let query = obligation(
        original.clone(),
        lower.clone(),
        vec![
            geometry.clone(),
            original.eq_expr(
                base.clone()
                    .bvadd(E::bv_const(8, 64).bvmul(E::bv_const(1, 64))),
            ),
            lower.eq_expr(base.bvadd(E::bv_const(8, 64))),
        ],
    );
    let candidate = inspect(&query, 2);
    assert!(candidate.text.contains(&geometry.to_string()));
    assert!(candidate.text.contains(":rule evaluate"));
    assert!(candidate.text.contains(":rule cong"));
    assert_eq!(candidate.text.matches(":rule and ").count(), 6);
    let mut mutant = query.clone();
    mutant.preconditions[2] =
        word("no_ordinal_or_stage_prefix").eq_expr(E::var("base", 64).bvadd(E::bv_const(9, 64)));
    assert_eq!(
        compose(&mutant).unwrap_err(),
        ClosedDefinitionRefusal::Unsupported("no congruence derivation")
    );
}

#[test]
fn bool_ite_current_array_and_indexed_congruence_keep_all_arms() {
    let memory = E::uf("entry_memory", vec![], memory_sort());
    let address = E::var("address", 64);
    let observe = E::var("observe", 64);
    let source_address = word("original_address");
    let target_address = word("target_address");
    let source_memory = E::uf("original_memory", vec![], memory_sort());
    let target_memory = E::uf("target_memory", vec![], memory_sort());
    let source_bool = E::uf("original_bool", vec![], SmtSort::Bool);
    let target_bool = E::uf("target_bool", vec![], SmtSort::Bool);
    let byte = E::var("word", 64).extract(7, 0);
    let query = obligation(
        E::ite(
            source_bool.clone().not_expr(),
            E::select(source_memory.clone(), observe.clone()),
            E::bv_const(255, 8),
        ),
        E::ite(
            target_bool.clone().not_expr(),
            E::select(target_memory.clone(), observe),
            E::bv_const(255, 8),
        ),
        vec![
            source_address.clone().eq_expr(
                address
                    .clone()
                    .bvadd(E::bv_const(4, 64).bvmul(E::bv_const(1, 64))),
            ),
            target_address
                .clone()
                .eq_expr(address.bvadd(E::bv_const(4, 64))),
            source_memory.clone().eq_expr(E::store(
                memory.clone(),
                source_address.clone(),
                byte.clone(),
            )),
            target_memory
                .clone()
                .eq_expr(E::store(memory, target_address.clone(), byte)),
            source_bool.eq_expr(source_address.eq_expr(E::var("other", 64))),
            target_bool.eq_expr(target_address.eq_expr(E::var("other", 64))),
        ],
    );
    let candidate = inspect(&query, 6);
    assert!(candidate.text.contains("(ite (not original_bool)"));
    assert!(candidate.text.contains("(store entry_memory"));
    assert!(candidate.text.contains("((_ extract 7 0) word)"));
    assert!(candidate.text.contains("(_ bv255 8)"));
    let mut mutant = query.clone();
    mutant.aarch64_expr = E::ite(
        E::uf("target_bool", vec![], SmtSort::Bool),
        E::select(target_memory, E::var("observe", 64)),
        E::bv_const(255, 8),
    );
    assert!(matches!(
        compose(&mutant),
        Err(ClosedDefinitionRefusal::Unsupported(_))
    ));
}

#[test]
fn extra_lowered_dynamic_product_is_unfolded_from_its_original_equation() {
    let base = E::var("base", 64);
    let index = E::var("index", 64);
    let source = word("source_address");
    let product = word("unshared_lowering_intermediate");
    let target = word("target_address");
    let query = obligation(
        source.clone(),
        target.clone(),
        vec![
            // Equation order is not correspondence authority, nor required to be
            // topological in a logical conjunction. The dependencies ARE acyclic.
            target.eq_expr(base.clone().bvadd(product.clone())),
            product.eq_expr(index.clone().bvmul(E::bv_const(8, 64))),
            source.eq_expr(base.bvadd(index.bvmul(E::bv_const(8, 64)))),
        ],
    );
    let candidate = inspect(&query, 3);
    assert!(!candidate.text.contains(":rule evaluate"));
    assert!(candidate.text.contains(":rule trans"));
    let mut mutant = query.clone();
    mutant.preconditions[1] = word("unshared_lowering_intermediate")
        .eq_expr(E::var("index", 64).bvmul(E::bv_const(4, 64)));
    assert!(matches!(
        compose(&mutant),
        Err(ClosedDefinitionRefusal::Unsupported(_))
    ));
}

#[test]
fn unused_cycles_duplicates_nonclosed_operators_and_wrong_sorts_refuse() {
    let x = word("x");
    let y = word("y");
    let same = E::bv_const(0, 64);
    let cycle = obligation(
        same.clone(),
        same.clone(),
        vec![x.clone().eq_expr(y.clone()), y.clone().eq_expr(x.clone())],
    );
    assert_eq!(
        compose(&cycle).unwrap_err(),
        ClosedDefinitionRefusal::Malformed("cyclic definitions")
    );
    let duplicate = obligation(
        same.clone(),
        same.clone(),
        vec![
            x.clone().eq_expr(same.clone()),
            x.eq_expr(E::bv_const(1, 64)),
        ],
    );
    assert_eq!(
        compose(&duplicate).unwrap_err(),
        ClosedDefinitionRefusal::Malformed("duplicate definition")
    );
    let call = E::uf("opaque", vec![E::var("input", 64)], SmtSort::BitVec(64));
    let unsupported = obligation(same.clone(), same.clone(), vec![y.eq_expr(call)]);
    assert_eq!(
        compose(&unsupported).unwrap_err(),
        ClosedDefinitionRefusal::Unsupported("argumented uninterpreted function")
    );
    let bad = E::BvAdd {
        lhs: Arc::new(E::var("narrow", 32)),
        rhs: Arc::new(same.clone()),
        width: 64,
    };
    assert!(matches!(
        compose(&obligation(bad, same.clone(), vec![])),
        Err(ClosedDefinitionRefusal::Malformed(
            "operand/result sort mismatch"
        ))
    ));
    let conflict = obligation(E::var("ambiguous", 64), word("ambiguous"), vec![]);
    assert_eq!(
        compose(&conflict).unwrap_err(),
        ClosedDefinitionRefusal::Malformed("conflicting symbol declaration")
    );
    // The ordinary constructor canonicalizes low bits. Forge the raw invalid
    // AST to test preflight, not an already-corrected literal.
    let noncanonical = obligation(
        E::BvConst {
            value: 256,
            width: 8,
        },
        E::bv_const(0, 8),
        vec![],
    );
    assert_eq!(
        compose(&noncanonical).unwrap_err(),
        ClosedDefinitionRefusal::Malformed("noncanonical bitvector literal")
    );
}

#[test]
fn existing_shape_and_output_budgets_bound_candidates_without_raising_caps() {
    let zero = E::bv_const(0, 64);
    let mut deep_component = E::BoolConst(true);
    for _ in 1..MAX_DEPTH {
        deep_component = deep_component.and_expr(E::BoolConst(true));
    }
    let deep = obligation(zero.clone(), zero.clone(), vec![deep_component]);
    assert_eq!(
        compose(&deep).unwrap_err(),
        ClosedDefinitionRefusal::Budget("expression depth")
    );
    // Aggregate borrowed components still refuse before cloning/building the
    // envelope. Many shallow leaves no longer masquerade as deep expressions.
    let inventory = obligation(
        zero.clone(),
        zero.clone(),
        vec![E::BoolConst(true); MAX_NODES],
    );
    assert_eq!(
        compose(&inventory).unwrap_err(),
        ClosedDefinitionRefusal::Budget("original component nodes")
    );
    let boundary = obligation(
        zero.clone(),
        zero.clone(),
        vec![E::BoolConst(true); MAX_DEPTH - 3],
    );
    assert_eq!(compose(&boundary).unwrap().premises, MAX_DEPTH - 3);
    let shallow = obligation(
        zero.clone(),
        zero.clone(),
        vec![E::BoolConst(true); MAX_DEPTH + 1],
    );
    let candidate = inspect(&shallow, 0);
    assert_eq!(candidate.premises, MAX_DEPTH + 1);
    assert_eq!(
        candidate.text.matches(":rule and ").count(),
        2 * (MAX_DEPTH + 1)
    );
    let mut shared = Arc::new(E::BoolConst(true));
    for _ in 0..21 {
        shared = Arc::new(E::And {
            lhs: shared.clone(),
            rhs: shared,
        });
    }
    // Existing DAG shape is tiny, but the SOLE original assume must remain
    // verbatim. Its expanded text still has the existing output bound.
    let large = obligation(zero.clone(), zero, vec![shared.as_ref().clone()]);
    assert_eq!(
        compose(&large).unwrap_err(),
        ClosedDefinitionRefusal::Budget("output bytes")
    );
}

#[test]
fn wide_shallow_payload_refuses_in_borrowed_components_before_owned_clone() {
    let zero = E::bv_const(0, 64);
    let premises = (0..257)
        .map(|index| {
            let prefix = format!("wide_payload_{index}_");
            let name = format!("{prefix}{}", "x".repeat(4096 - prefix.len()));
            let term = E::uf(name, vec![], SmtSort::Bool);
            let bounded = preflight(&term).expect("each root fits unchanged caps");
            assert_eq!(bounded.order.len(), 1);
            assert!(bounded.payload < MAX_PAYLOAD_BYTES);
            term
        })
        .collect::<Vec<_>>();
    let query = obligation(zero.clone(), zero, premises);
    assert_eq!(
        compose(&query).unwrap_err(),
        ClosedDefinitionRefusal::Budget("original component payload")
    );
}

#[test]
fn proof_local_macros_are_fresh_even_against_quoted_and_unused_declarations() {
    let input = E::uf("|tcg!cd0_quoted|", vec![], SmtSort::BitVec(64));
    let source = word("original");
    let lower = word("lowered");
    let mut query = obligation(
        source.clone(),
        lower.clone(),
        vec![
            source.eq_expr(
                input
                    .clone()
                    .bvadd(E::bv_const(8, 64).bvmul(E::bv_const(1, 64))),
            ),
            lower.eq_expr(input.bvadd(E::bv_const(8, 64))),
        ],
    );
    query.inputs.push(("tcg!cd1_unused".into(), 64));
    query.fp_inputs.push(("tcg!cd2_unused_fp".into(), 8, 24));
    let candidate = inspect(&query, 2);
    assert!(candidate.text.contains("(define-fun tcg!cd3_"));
    assert!(!candidate.text.contains("(define-fun tcg!cd0_"));
    assert!(!candidate.text.contains("(define-fun tcg!cd1_"));
    assert!(!candidate.text.contains("(define-fun tcg!cd2_"));
    // Every macro is exact typed shallow syntax, not an assumed equality.
    assert!(
        candidate
            .text
            .contains(" () (_ BitVec 64) (bvmul (_ bv8 64) (_ bv1 64)))")
    );
    assert!(candidate.text.contains(" () Bool (= original tcg!cd3_"));
    assert!(candidate.text.contains(":rule evaluate"));
    query
        .inputs
        .extend((3..MAX_PREFIX_ATTEMPTS).map(|i| (format!("tcg!cd{i}_unused"), 64)));
    assert_eq!(
        compose(&query).unwrap_err(),
        ClosedDefinitionRefusal::Budget("fresh-name attempts")
    );
}

#[test]
fn shared_closed_literals_are_evaluated_bottom_up_with_shallow_values() {
    let mut shared = Arc::new(E::bv_const(1, 64));
    for _ in 0..20 {
        shared = Arc::new(E::BvMul {
            lhs: shared.clone(),
            rhs: shared,
            width: 64,
        });
    }
    let formula = shared.as_ref().clone().eq_expr(E::bv_const(1, 64));
    let graph = Graph::new(&formula).unwrap();
    let E::Eq { lhs, .. } = &formula else {
        unreachable!()
    };
    let value = &graph.nodes[graph.pointers[&Arc::as_ptr(lhs)]];
    assert_eq!(value.literal, Some(E::bv_const(1, 64)));
    assert_eq!(
        graph.nodes.len(),
        22,
        "linear distinct-node census, not 2^20 expansion"
    );
}

fn access_demand() -> ProofObligation {
    let source = word("original_address");
    let lower = word("lowered_address");
    let original_guard = E::uf("original_guard", vec![], SmtSort::Bool);
    let lowered_guard = E::uf("lowered_guard", vec![], SmtSort::Bool);
    let guard_value = E::var("input", 64).eq_expr(E::bv_const(0, 64));
    let needed = |guard: E, address: E, width| {
        guard.and_expr(
            E::var("observe", 64).bvuge(address.clone()).and_expr(
                E::var("observe", 64)
                    .bvsub(address)
                    .bvult(E::bv_const(width, 64)),
            ),
        )
    };
    let geometry = original_guard
        .clone()
        .not_expr()
        .or_expr(crate::scalar_memory_relations::valid_access(&source, 8, 8));
    let coverage = E::BoolConst(false)
        .or_expr(E::uf("unrelated_before", vec![], SmtSort::Bool))
        .or_expr(needed(original_guard.clone(), source.clone(), 8))
        .or_expr(E::uf("unrelated_after", vec![], SmtSort::Bool));
    let demand = lowered_guard
        .clone()
        .not_expr()
        .or_expr(crate::scalar_memory_relations::valid_access(&lower, 8, 8))
        .and_expr(
            needed(lowered_guard.clone(), lower.clone(), 8)
                .not_expr()
                .or_expr(coverage),
        );
    obligation(
        E::BoolConst(true),
        demand,
        vec![
            geometry,
            source.eq_expr(E::var("base", 64).bvadd(E::bv_const(8, 64).bvmul(E::bv_const(1, 64)))),
            lower.eq_expr(E::var("base", 64).bvadd(E::bv_const(8, 64))),
            original_guard.eq_expr(guard_value.clone()),
            lowered_guard.eq_expr(guard_value),
        ],
    )
}

#[test]
fn guarded_access_is_true_by_original_premise_and_complementary_or_embedding() {
    let query = access_demand();
    let candidate = inspect(&query, 4);
    for rule in [
        "and_neg",
        "resolution",
        "or_neg",
        "equiv1",
        "contraction",
        "equiv_simplify",
    ] {
        assert!(
            candidate.text.contains(&format!(":rule {rule}")),
            "required original-term rule {rule}"
        );
    }
    assert!(candidate.text.contains("unrelated_before"));
    assert!(candidate.text.contains("unrelated_after"));
    assert_eq!(candidate.text.matches(":rule and ").count(), 10);
    assert!(!candidate.text.contains(":rule eq_mp"));
    assert!(!candidate.text.contains(":rule and_intro"));
}

#[test]
fn changed_geometry_definition_and_missing_or_witness_decline_without_search() {
    for mutation in 0..5 {
        let mut query = access_demand();
        match mutation {
            0 => {
                query.preconditions[2] =
                    word("lowered_address").eq_expr(E::var("base", 64).bvadd(E::bv_const(9, 64)))
            }
            1 => {
                query.preconditions[4] = E::uf("lowered_guard", vec![], SmtSort::Bool)
                    .eq_expr(E::var("input", 64).eq_expr(E::bv_const(1, 64)))
            }
            2 => {
                // No corresponding target-byte witness; neither unrelated row
                // is assumed true. The complete original geometry stays present.
                let E::And {
                    lhs: valid,
                    rhs: coverage,
                } = &query.aarch64_expr
                else {
                    unreachable!()
                };
                let E::Or { lhs: unneeded, .. } = coverage.as_ref() else {
                    unreachable!()
                };
                query.aarch64_expr =
                    valid
                        .as_ref()
                        .clone()
                        .and_expr(unneeded.as_ref().clone().or_expr(E::uf(
                            "unrelated_before",
                            vec![],
                            SmtSort::Bool,
                        )));
            }
            3 => {
                // Mutate ONLY the target-needed interval, retaining the entire
                // original coverage witness forest and source geometry.
                let E::And { lhs: valid, rhs } = &query.aarch64_expr else {
                    unreachable!()
                };
                let E::Or {
                    lhs: unneeded,
                    rhs: coverage,
                } = rhs.as_ref()
                else {
                    unreachable!()
                };
                let changed = unneeded
                    .try_rewrite_dag::<Infallible>(&mut |node| {
                        Ok(matches!(
                            node,
                            E::BvConst {
                                value: 8,
                                width: 64
                            }
                        )
                        .then(|| E::bv_const(16, 64)))
                    })
                    .unwrap()
                    .unwrap();
                query.aarch64_expr = valid
                    .as_ref()
                    .clone()
                    .and_expr(changed.or_expr(coverage.as_ref().clone()));
            }
            _ => {
                query.preconditions.remove(0);
            }
        }
        assert!(
            matches!(
                compose(&query),
                Err(ClosedDefinitionRefusal::Unsupported(
                    "no Boolean entailment"
                ))
            ),
            "mutation {mutation} cannot mint a Boolean proof"
        );
    }
}

#[test]
fn ordinary_boolean_conjunction_or_truth_and_odd_negation_are_composed() {
    let p = E::uf("p", vec![], SmtSort::Bool);
    let q = E::uf("q", vec![], SmtSort::Bool);
    let known_leaf = obligation(
        E::BoolConst(true),
        p.clone().or_expr(q.clone()),
        vec![p.clone()],
    );
    let candidate = inspect(&known_leaf, 0);
    assert!(candidate.text.contains(":rule or_neg"));
    let negations = p.clone().not_expr().not_expr().not_expr();
    let tautology = obligation(
        E::BoolConst(true),
        E::BoolConst(false).or_expr(negations).or_expr(p),
        vec![],
    );
    inspect(&tautology, 0);
    let closed = obligation(
        E::BoolConst(true),
        E::BoolConst(true).or_expr(E::BoolConst(false)),
        vec![],
    );
    inspect(&closed, 0);
    let unsupported = obligation(E::BoolConst(true), q, vec![]);
    assert_eq!(
        compose(&unsupported).unwrap_err(),
        ClosedDefinitionRefusal::Unsupported("no Boolean entailment")
    );
}

fn literal_status_query() -> ProofObligation {
    let movz = word("literal_movz");
    let movk = word("literal_movk");
    let status = word("literal_status");
    obligation(
        E::bv_const(4_294_967_297, 64),
        status.clone(),
        vec![
            // Logical premise order is deliberately not dependency order.
            status.eq_expr(movk.clone()),
            movz.clone().eq_expr(E::bv_const(1, 64)),
            movk.eq_expr(
                movz.bvand(E::bv_const(!(0xffffu64 << 32), 64))
                    .bvor(E::bv_const(1u64 << 32, 64)),
            ),
        ],
    )
}

#[test]
fn definition_literals_keep_full_movz_movk_status_and_original_equations() {
    let query = literal_status_query();
    let candidate = inspect(&query, 3);
    assert!(candidate.text.contains("(_ bv4294967297 64)"));
    for rule in ["cong", "evaluate", "trans"] {
        assert!(candidate.text.contains(&format!(":rule {rule}")));
    }
    let evaluations = candidate
        .text
        .lines()
        .filter(|line| line.contains(":rule evaluate"))
        .collect::<Vec<_>>();
    assert!(!evaluations.is_empty());
    for line in evaluations {
        // A defining equality is an original premise, not an assignment that
        // permits evaluate to treat the still-free original UF as a literal.
        for symbol in ["literal_movz", "literal_movk", "literal_status"] {
            assert!(!line.contains(symbol), "nonliteral evaluation: {line}");
        }
    }
    let mut reordered = query.clone();
    reordered.preconditions.reverse();
    inspect(&reordered, 3);
    assert_eq!(compose(&query).unwrap().text, candidate.text);
}

#[test]
fn definition_literals_preserve_i32_wrap_and_boolean_false_and_true() {
    let seed = E::uf("narrow_seed", vec![], SmtSort::BitVec(32));
    let sum = E::uf("narrow_sum", vec![], SmtSort::BitVec(32));
    let product = E::uf("narrow_product", vec![], SmtSort::BitVec(32));
    let integer = obligation(
        E::bv_const(0x60, 32),
        product.clone(),
        vec![
            sum.clone()
                .eq_expr(seed.clone().bvadd(E::bv_const(0x30, 32))),
            seed.eq_expr(E::bv_const(0xffff_fff0, 32)),
            product.clone().eq_expr(sum.bvmul(E::bv_const(3, 32))),
        ],
    );
    let candidate = inspect(&integer, 3);
    assert!(candidate.text.contains("(_ bv96 32)"));
    assert!(candidate.text.contains(":rule cong"));
    for expected in [false, true] {
        let comparison = E::uf("literal_comparison", vec![], SmtSort::Bool);
        let negated = E::uf("literal_negated", vec![], SmtSort::Bool);
        let result = E::uf("literal_boolean", vec![], SmtSort::Bool);
        let mut premises = integer.preconditions.clone();
        premises.extend([
            result.clone().eq_expr(negated.clone().not_expr()),
            comparison.clone().eq_expr(
                product
                    .clone()
                    .eq_expr(E::bv_const(if expected { 0x60 } else { 0x61 }, 32)),
            ),
            negated.eq_expr(comparison.not_expr()),
        ]);
        let query = obligation(E::BoolConst(expected), result, premises);
        let candidate = inspect(&query, 6);
        assert!(candidate.text.contains(":rule evaluate"));
        let mut wrong = query.clone();
        wrong.trust_ir_expr = E::BoolConst(!expected);
        assert!(matches!(
            compose(&wrong),
            Err(ClosedDefinitionRefusal::Unsupported(_))
        ));
    }
}

#[test]
fn definition_literals_do_not_hide_status_highword_mask_or_equation_mutations() {
    for mutation in 0..3 {
        let mut query = literal_status_query();
        match mutation {
            0 => query.trust_ir_expr = E::bv_const(1, 64),
            1 => {
                query.preconditions[2] = word("literal_movk").eq_expr(
                    word("literal_movz")
                        .bvand(E::bv_const(!(0xffffu64 << 32) & !1, 64))
                        .bvor(E::bv_const(1u64 << 32, 64)),
                );
            }
            _ => query.preconditions[1] = word("literal_movz").eq_expr(E::bv_const(2, 64)),
        }
        assert!(
            matches!(
                compose(&query),
                Err(ClosedDefinitionRefusal::Unsupported(_))
            ),
            "semantically different status mutation {mutation} must decline"
        );
    }
    let mut wrong_width = literal_status_query();
    wrong_width.preconditions[1] = word("literal_movz").eq_expr(E::bv_const(1, 32));
    assert_eq!(
        compose(&wrong_width).unwrap_err(),
        ClosedDefinitionRefusal::Malformed("operand/result sort mismatch")
    );
}

#[test]
fn definition_literals_require_unique_acyclic_closed_equations() {
    let mut missing = literal_status_query();
    missing.preconditions.remove(1);
    assert!(matches!(
        compose(&missing),
        Err(ClosedDefinitionRefusal::Unsupported(_))
    ));
    let mut symbolic = literal_status_query();
    symbolic.preconditions[1] = word("literal_movz").eq_expr(E::var("arbitrary_input", 64));
    assert!(matches!(
        compose(&symbolic),
        Err(ClosedDefinitionRefusal::Unsupported(_))
    ));
    let mut duplicate = literal_status_query();
    duplicate
        .preconditions
        .push(duplicate.preconditions[1].clone());
    assert_eq!(
        compose(&duplicate).unwrap_err(),
        ClosedDefinitionRefusal::Malformed("duplicate definition")
    );
    let mut cyclic = literal_status_query();
    cyclic.preconditions[1] = word("literal_movz").eq_expr(word("literal_status"));
    assert_eq!(
        compose(&cyclic).unwrap_err(),
        ClosedDefinitionRefusal::Malformed("cyclic definitions")
    );
}

#[test]
fn definition_literals_do_not_expand_the_existing_evaluate_operator_subset() {
    let seed = word("unsupported_literal_seed");
    for rhs in [
        seed.clone().bvsub(E::bv_const(1, 64)),
        seed.clone().bvlshr(E::bv_const(1, 64)),
    ] {
        let result = word("unsupported_literal_result");
        let query = obligation(
            E::bv_const(1, 64),
            result.clone(),
            vec![
                result.eq_expr(rhs),
                seed.clone().eq_expr(E::bv_const(2, 64)),
            ],
        );
        assert!(matches!(
            compose(&query),
            Err(ClosedDefinitionRefusal::Unsupported(_))
        ));
    }
    let mut with_unused_symbolic = literal_status_query();
    with_unused_symbolic
        .preconditions
        .push(word("unused_symbolic_definition").eq_expr(E::var("unconstrained", 64)));
    let candidate = inspect(&with_unused_symbolic, 4);
    assert!(candidate.text.contains("unused_symbolic_definition"));
    assert!(candidate.text.contains("unconstrained"));
}

fn shared_definition_literal_chain(count: usize) -> ProofObligation {
    assert!(count > 0);
    let mut previous = word("shared_literal_0");
    let mut premises = vec![previous.clone().eq_expr(E::bv_const(1, 64))];
    let mut expected = 1u64;
    for index in 1..count {
        let next = word(&format!("shared_literal_{index}"));
        // Both children are the SAME prior definition. Literal derivation must
        // share established equalities, not expand a binary history per use.
        let twice = Arc::new(E::BvAdd {
            lhs: Arc::new(previous.clone()),
            rhs: Arc::new(previous),
            width: 64,
        });
        let rhs = E::BvAdd {
            lhs: twice,
            rhs: Arc::new(E::bv_const(1, 64)),
            width: 64,
        };
        premises.push(next.clone().eq_expr(rhs));
        previous = next;
        expected = expected.wrapping_mul(2).wrapping_add(1);
    }
    premises.reverse();
    obligation(E::bv_const(expected, 64), previous, premises)
}

#[test]
fn definition_literals_share_long_histories_with_linear_candidate_census() {
    let mut candidates = Vec::new();
    for count in [40, 80] {
        let query = shared_definition_literal_chain(count);
        let candidate = inspect(&query, count);
        assert!(candidate.steps >= count);
        assert!(candidate.steps <= 24 * count + 64);
        assert!(candidate.text.len() < MAX_OUTPUT_BYTES);
        assert!(candidate.text.len() <= 4096 * count);
        assert_eq!(compose(&query).unwrap().text, candidate.text);
        candidates.push(candidate);
    }
    assert!(candidates[1].steps <= 2 * candidates[0].steps + 32);
    assert!(candidates[1].text.len() <= 2 * candidates[0].text.len() + 16_384);
}

#[test]
fn definition_literals_selection_obeys_the_actual_aggregate_work_caps() {
    let formula = word("bounded_literal").eq_expr(E::bv_const(7, 64));
    let mut graph = Graph::new(&formula).unwrap();
    let root = graph.pointers[&(&formula as *const E)];
    // The arbitrary ID is only selection metadata in this construction test;
    // no proof text or certificate is produced from it.
    graph.definition(root, 0).unwrap();
    let mut order = Vec::new();
    graph.acyclic(Some(&mut order)).unwrap();
    let needed_edges = order
        .iter()
        .map(|id| {
            if graph.definitions.contains_key(id) {
                1
            } else {
                graph.nodes[*id].children.len()
            }
        })
        .sum::<usize>();
    let mut visits = MAX_NODES - order.len();
    let mut edges = MAX_EDGES - needed_edges;
    graph
        .prepare_literals(&order, &mut visits, &mut edges)
        .unwrap();
    assert_eq!((visits, edges), (MAX_NODES, MAX_EDGES));
    let alias = graph.nodes[root].children[0];
    assert_eq!(graph.nodes[alias].literal, Some(E::bv_const(7, 64)));
    assert_eq!(
        graph
            .prepare_literals(&order, &mut visits, &mut edges)
            .unwrap_err(),
        ClosedDefinitionRefusal::Budget("equality visits")
    );
    assert_eq!((visits, edges), (MAX_NODES, MAX_EDGES));

    visits = 0;
    edges = MAX_EDGES - needed_edges + 1;
    assert_eq!(
        graph
            .prepare_literals(&order, &mut visits, &mut edges)
            .unwrap_err(),
        ClosedDefinitionRefusal::Budget("equality work edges")
    );
    assert!(visits <= MAX_NODES && edges <= MAX_EDGES);
}

#[test]
fn definition_literals_proof_memo_hits_do_not_repeat_derivation_work() {
    let formula = E::bv_const(1, 64).bvadd(E::bv_const(2, 64));
    let graph = Graph::new(&formula).unwrap();
    let root = graph.pointers[&(&formula as *const E)];
    let children = graph.nodes[root].children.clone();
    let mut composer = Composer {
        graph,
        text: Text {
            text: String::new(),
            next: 0,
            steps: 0,
        },
        equalities: HashMap::new(),
        literal_equalities: HashMap::new(),
        keys: vec![],
        known_true: HashMap::new(),
        truths: HashMap::new(),
        root_facts: None,
        selected_ites: HashMap::new(),
        modular_candidate: false,
        visits: MAX_NODES - 1,
        edges: 0,
    };
    let first = composer.literal_equality(children[0]).unwrap();
    let bytes = composer.text.text.len();
    assert_eq!(composer.visits, MAX_NODES);
    assert_eq!(composer.literal_equality(children[0]).unwrap(), first);
    assert_eq!(composer.text.text.len(), bytes);
    assert_eq!(composer.visits, MAX_NODES);
    assert_eq!(
        composer.literal_equality(children[1]).unwrap_err(),
        ClosedDefinitionRefusal::Budget("equality visits")
    );
    assert_eq!(composer.text.text.len(), bytes);
    assert_eq!(composer.literal_equalities.len(), 1);

    // For this two-child shell: two scheduled visits + one continuation,
    // two congruence references and two transitivity references = seven.
    composer.visits = 0;
    composer.edges = MAX_EDGES - 7;
    composer.literal_equalities.clear();
    let proof = composer.literal_equality(root).unwrap();
    assert_eq!(composer.edges, MAX_EDGES);
    let work = (
        composer.visits,
        composer.text.steps,
        composer.text.text.len(),
    );
    assert_eq!(composer.literal_equality(root).unwrap(), proof);
    assert_eq!(
        work,
        (
            composer.visits,
            composer.text.steps,
            composer.text.text.len()
        )
    );
    composer.literal_equalities.clear();
    assert_eq!(
        composer.literal_equality(root).unwrap_err(),
        ClosedDefinitionRefusal::Budget("equality work edges")
    );
    assert_eq!(work.1, composer.text.steps);
    assert_eq!(work.2, composer.text.text.len());
}

#[test]
fn equal_ground_predicates_prove_original_values_before_same_operator_congruence() {
    let left = E::bv_const(0x1000, 64).eq_expr(E::bv_const(0x1000, 64));
    let right = E::bv_const(0x2000, 64).eq_expr(E::bv_const(0x2000, 64));
    let original = obligation(left, right, vec![]);
    let candidate = inspect(&original, 0);
    assert!(candidate.text.contains(":rule evaluate"));
    let mut wrong = original.clone();
    wrong.aarch64_expr = E::bv_const(0x2000, 64).eq_expr(E::bv_const(0x2008, 64));
    assert!(
        compose(&wrong).is_err(),
        "same operator never licenses a false ground predicate"
    );
}
