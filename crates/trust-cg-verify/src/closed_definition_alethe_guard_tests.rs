// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Untrusted construction/refusal controls, not independent proof checking.
//! Every fact starts in the complete original refutation and its projected
//! premises. Captured Clean replay and compiler admission remain separate.

use super::*;
use crate::lowering_proof::MachineSideProvenance;

fn boolean(name: &str) -> E {
    E::uf(name, vec![], SmtSort::Bool)
}

fn obligation(source: E, target: E, premises: Vec<E>) -> ProofObligation {
    ProofObligation {
        name: "ordinary original guarded ITE".into(),
        trust_ir_expr: source,
        aarch64_expr: target,
        inputs: vec![],
        preconditions: premises,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

fn guarded(guard: E, condition: E, then_value: E, else_value: E, positive: bool) -> E {
    let chosen = if positive {
        then_value.clone()
    } else {
        else_value.clone()
    };
    guard
        .not_expr()
        .or_expr(E::ite(condition, then_value, else_value).eq_expr(chosen))
}

fn branch_fixture(then_value: E, else_value: E, positive: bool) -> ProofObligation {
    let guard = boolean("guard");
    let condition = boolean("condition");
    let rhs = if positive {
        condition.clone()
    } else {
        condition.clone().not_expr()
    };
    obligation(
        E::BoolConst(true),
        guarded(guard.clone(), condition, then_value, else_value, positive),
        vec![guard.eq_expr(rhs)],
    )
}

struct Endpoints {
    source: Id,
    goal: Id,
    terminal: Id,
    terminal_unit: Id,
    premises: Vec<(Id, Id)>,
}

/// Prepare actual original occurrence projections, not synthetic units. The
/// midpoint traversal treats each original premise as an opaque leaf, exactly
/// as the canonical negated-equivalence envelope does.
fn prepare<'a>(
    original: &ProofObligation,
    formula: &'a E,
) -> Result<(Composer<'a>, Endpoints), ClosedDefinitionRefusal> {
    let mut graph = Graph::new(formula)?;
    let mut text = Text {
        text: String::new(),
        next: 0,
        steps: 0,
    };
    let root = graph.pointers[&(formula as *const E)];
    let assumption = text.assume(formula)?;
    graph.sharing(original, &mut text)?;
    let leaves = original.preconditions.len() + 1;
    let mut pending = vec![(root, assumption, 0usize, leaves)];
    let mut premises = Vec::new();
    let mut terminal = None;
    let mut next_leaf = 0;
    while let Some((id, unit, start, count)) = pending.pop() {
        if count == 1 {
            assert_eq!(start, next_leaf);
            next_leaf += 1;
            if start == original.preconditions.len() {
                terminal = Some((id, unit));
            } else {
                graph.definition(id, unit)?;
                premises.push((id, unit));
            }
            continue;
        }
        assert!(matches!(graph.nodes[id].original, E::And { .. }));
        let [left, right] = [graph.nodes[id].children[0], graph.nodes[id].children[1]];
        let left_unit = text.unit(graph.nodes[left].spelled(), "and", &[unit], Some(0))?;
        let right_unit = text.unit(graph.nodes[right].spelled(), "and", &[unit], Some(1))?;
        let left_count = count / 2;
        pending.push((right, right_unit, start + left_count, count - left_count));
        pending.push((left, left_unit, start, left_count));
    }
    assert_eq!(next_leaf, leaves);
    let (terminal, terminal_unit) = terminal.unwrap();
    assert!(matches!(graph.nodes[terminal].original, E::Not { .. }));
    let equality = graph.nodes[terminal].children[0];
    assert!(matches!(graph.nodes[equality].original, E::Eq { .. }));
    let [source, goal] = [
        graph.nodes[equality].children[0],
        graph.nodes[equality].children[1],
    ];
    let mut order = Vec::new();
    graph.acyclic(Some(&mut order))?;
    let mut visits = 0;
    let mut edges = 0;
    graph.prepare_literals(&order, &mut visits, &mut edges)?;
    reserve_visits(&mut visits, order.len())?;
    let (keys, key_edges) = graph.canonical_keys(&order)?;
    reserve_work::<Id>(&[], &mut edges, key_edges)?;
    let mut known_true = HashMap::new();
    for &(node, proof) in &premises {
        known_true.entry(keys[node]).or_insert((node, proof));
    }
    Ok((
        Composer {
            graph,
            text,
            equalities: HashMap::new(),
            literal_equalities: HashMap::new(),
            keys,
            known_true,
            truths: HashMap::new(),
            root_facts: None,
            selected_ites: HashMap::new(),
            modular_candidate: false,
            visits,
            edges,
        },
        Endpoints {
            source,
            goal,
            terminal,
            terminal_unit,
            premises,
        },
    ))
}

fn node(composer: &Composer<'_>, expression: &E) -> Id {
    // Fixtures use bounded shallow needles; this is not an expanded evaluator.
    composer
        .graph
        .nodes
        .iter()
        .position(|node| node.original == expression)
        .unwrap()
}

fn literals(composer: &Composer<'_>) -> Vec<Option<E>> {
    composer
        .graph
        .nodes
        .iter()
        .map(|node| node.literal.clone())
        .collect()
}

fn facts(
    composer: &mut Composer<'_>,
    endpoints: &Endpoints,
) -> Result<guard::RootFacts, ClosedDefinitionRefusal> {
    composer.root_boolean_facts(
        endpoints.source,
        endpoints.goal,
        endpoints.terminal,
        endpoints.terminal_unit,
        &endpoints.premises,
    )
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
    assert!(!candidate.text.contains("declare-fun"));
    assert!(!candidate.text.contains("declare-const"));
    assert!(!candidate.text.contains(":rule trust"));
    assert!(!candidate.text.contains(":rule hole"));
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
fn original_guard_selects_both_distinct_branches_in_bool_and_bv_sorts() {
    let arms = [
        (E::BoolConst(true), E::BoolConst(false)),
        (E::bv_const(0xa5, 8), E::bv_const(0x5a, 8)),
        (E::bv_const(0x8000_0001, 32), E::bv_const(7, 32)),
        (E::bv_const(0x0000_0001_0000_0001, 64), E::bv_const(7, 64)),
    ];
    for (then_value, else_value) in arms {
        for positive in [true, false] {
            let original = branch_fixture(then_value.clone(), else_value.clone(), positive);
            let before = original.clone();
            let formula = original.negated_equivalence();
            let (mut composer, endpoints) = prepare(&original, &formula).unwrap();
            let condition = node(&composer, &boolean("condition"));
            let ite = node(
                &composer,
                &E::ite(boolean("condition"), then_value.clone(), else_value.clone()),
            );
            let literal_before = literals(&composer);
            let root_facts = facts(&mut composer, &endpoints).unwrap();
            let fact = root_facts.get(condition, positive).unwrap();
            assert_eq!(fact.node(), condition);
            assert_eq!(fact.positive(), positive);
            assert!(root_facts.get(condition, !positive).is_none());
            let (branch, proof) = composer.ite_branch_equality(ite, fact).unwrap();
            let expected = if positive { &then_value } else { &else_value };
            assert_eq!(composer.graph.nodes[branch].original, expected);
            assert!(proof < composer.text.next);
            assert!(composer.text.text.contains(":rule ite_intro"));
            assert!(composer.text.text.contains(if positive {
                ":rule ite2"
            } else {
                ":rule ite1"
            }));
            assert_eq!(literals(&composer), literal_before);
            assert!(composer.literal_equalities.is_empty());
            assert_eq!(original, before);
            let candidate = inspect(&original, 1);
            assert!(candidate.text.contains(":rule not_or"));
            assert!(candidate.text.contains(":rule ite_intro"));
        }
    }
}

#[test]
fn nested_and_not_aliases_transport_real_signed_units_without_literal_mutation() {
    let p = boolean("p");
    let q = boolean("q");
    let conjunction = p.clone().and_expr(q.clone().not_expr());
    let seed = boolean("seed");
    let negative = boolean("negative");
    let guard = boolean("guard");
    let premises = vec![
        guard.clone().eq_expr(negative.clone().not_expr()),
        negative.clone().eq_expr(seed.clone().not_expr()),
        seed.clone().eq_expr(conjunction.clone()),
    ];
    for (condition, positive) in [(p.clone(), true), (q.clone(), false)] {
        let original = obligation(
            E::BoolConst(true),
            guarded(
                guard.clone(),
                condition,
                E::bv_const(11, 64),
                E::bv_const(29, 64),
                positive,
            ),
            premises.clone(),
        );
        let formula = original.negated_equivalence();
        let (mut composer, endpoints) = prepare(&original, &formula).unwrap();
        let ids = [
            (node(&composer, &guard), true),
            (node(&composer, &negative), false),
            (node(&composer, &seed), true),
            (node(&composer, &conjunction), true),
            (node(&composer, &p), true),
            (node(&composer, &q), false),
        ];
        let literal_before = literals(&composer);
        let root_facts = facts(&mut composer, &endpoints).unwrap();
        for (id, positive) in ids {
            assert_eq!(root_facts.get(id, positive).unwrap().node(), id);
            assert!(root_facts.get(id, !positive).is_none());
        }
        assert_eq!(literals(&composer), literal_before);
        assert!(composer.literal_equalities.is_empty());
        let candidate = inspect(&original, 3);
        assert!(candidate.text.contains(":rule not_simplify"));
        assert!(candidate.text.contains(":rule and "));
    }
}

#[test]
fn unknown_condition_never_becomes_a_fact_literal_or_candidate() {
    let guard = boolean("guard");
    let p = boolean("p");
    let unknown = boolean("unknown");
    let original = obligation(
        E::BoolConst(true),
        guarded(
            guard.clone(),
            unknown.clone(),
            E::bv_const(1, 32),
            E::bv_const(2, 32),
            true,
        ),
        vec![guard.eq_expr(p)],
    );
    let before = original.clone();
    let formula = original.negated_equivalence();
    let (mut composer, endpoints) = prepare(&original, &formula).unwrap();
    let unknown = node(&composer, &unknown);
    let literal_before = literals(&composer);
    let root_facts = facts(&mut composer, &endpoints).unwrap();
    assert!(root_facts.get(unknown, true).is_none());
    assert!(root_facts.get(unknown, false).is_none());
    assert!(composer.graph.nodes[unknown].literal.is_none());
    assert_eq!(literals(&composer), literal_before);
    assert!(composer.literal_equalities.is_empty());
    assert!(matches!(
        compose(&original),
        Err(ClosedDefinitionRefusal::Unsupported(_))
    ));
    assert_eq!(original, before);
    // This is a construction refusal, not a solver-backed counterexample.
}

#[test]
fn nonoriginal_source_terminal_and_root_profile_refuse_before_fact_emission() {
    let good = branch_fixture(E::bv_const(1, 8), E::bv_const(2, 8), true);
    let mut wrong_source = good.clone();
    wrong_source.trust_ir_expr = E::BoolConst(false);
    let mut wrong_left = good.clone();
    wrong_left.aarch64_expr = boolean("guard").or_expr(
        E::ite(boolean("condition"), E::bv_const(1, 8), E::bv_const(2, 8))
            .eq_expr(E::bv_const(1, 8)),
    );
    let mut nonguarded = good.clone();
    nonguarded.aarch64_expr = E::ite(boolean("condition"), E::bv_const(1, 8), E::bv_const(2, 8))
        .eq_expr(E::bv_const(1, 8));
    for (original, expected) in [
        (
            wrong_source,
            ClosedDefinitionRefusal::Malformed("original guarded disequality"),
        ),
        (
            wrong_left,
            ClosedDefinitionRefusal::Unsupported("guarded Boolean root"),
        ),
        (
            nonguarded,
            ClosedDefinitionRefusal::Unsupported("guarded Boolean root"),
        ),
    ] {
        let formula = original.negated_equivalence();
        let (mut composer, endpoints) = prepare(&original, &formula).unwrap();
        let text_before = composer.text.text.clone();
        assert_eq!(facts(&mut composer, &endpoints).err().unwrap(), expected);
        assert_eq!(composer.text.text, text_before);
    }
    let formula = good.negated_equivalence();
    let (mut composer, mut endpoints) = prepare(&good, &formula).unwrap();
    let text_before = composer.text.text.clone();
    endpoints.terminal_unit = composer.text.next;
    assert_eq!(
        facts(&mut composer, &endpoints).err().unwrap(),
        ClosedDefinitionRefusal::Malformed("original guarded disequality")
    );
    assert_eq!(composer.text.text, text_before);
}

#[test]
fn wrong_condition_and_foreign_composer_facts_cannot_select_an_ite() {
    let original = branch_fixture(E::bv_const(1, 64), E::bv_const(2, 64), true);
    let formula = original.negated_equivalence();
    let (mut first, endpoints) = prepare(&original, &formula).unwrap();
    let ite_expression = E::ite(boolean("condition"), E::bv_const(1, 64), E::bv_const(2, 64));
    let ite = node(&first, &ite_expression);
    let guard = node(&first, &boolean("guard"));
    let condition = node(&first, &boolean("condition"));
    let root_facts = facts(&mut first, &endpoints).unwrap();
    let text_before = first.text.text.clone();
    assert_eq!(
        first
            .ite_branch_equality(ite, root_facts.get(guard, true).unwrap())
            .unwrap_err(),
        ClosedDefinitionRefusal::Malformed("ITE condition fact")
    );
    assert_eq!(first.text.text, text_before);
    // Identical endpoint text/IDs are insufficient: both graph allocations
    // remain alive, so the private fact must still belong to this composer.
    let (mut second, _) = prepare(&original, &formula).unwrap();
    let second_ite = node(&second, &ite_expression);
    let text_before = second.text.text.clone();
    assert_eq!(
        second
            .ite_branch_equality(second_ite, root_facts.get(condition, true).unwrap())
            .unwrap_err(),
        ClosedDefinitionRefusal::Malformed("ITE condition fact")
    );
    assert_eq!(second.text.text, text_before);
    assert_eq!(
        first
            .ite_branch_equality(
                first.graph.nodes.len(),
                root_facts.get(condition, true).unwrap()
            )
            .unwrap_err(),
        ClosedDefinitionRefusal::Malformed("ITE node")
    );
}

#[test]
fn malformed_branch_sorts_duplicate_and_cyclic_definitions_stay_refused() {
    let mut bad_width = branch_fixture(E::bv_const(1, 8), E::bv_const(2, 8), true);
    bad_width.aarch64_expr = guarded(
        boolean("guard"),
        boolean("condition"),
        E::bv_const(1, 8),
        E::bv_const(2, 32),
        true,
    );
    let mut bad_condition = bad_width.clone();
    bad_condition.aarch64_expr = guarded(
        boolean("guard"),
        E::bv_const(1, 64),
        E::bv_const(1, 8),
        E::bv_const(2, 8),
        true,
    );
    for original in [bad_width, bad_condition] {
        let before = original.clone();
        assert_eq!(
            compose(&original).unwrap_err(),
            ClosedDefinitionRefusal::Malformed("operand/result sort mismatch")
        );
        assert_eq!(original, before);
    }
    let original = branch_fixture(E::bv_const(1, 8), E::bv_const(2, 8), true);
    let mut duplicate = original.clone();
    duplicate
        .preconditions
        .push(duplicate.preconditions[0].clone());
    let mut cycle = original;
    cycle
        .preconditions
        .push(boolean("condition").eq_expr(boolean("guard")));
    for (original, expected) in [
        (
            duplicate,
            ClosedDefinitionRefusal::Malformed("duplicate definition"),
        ),
        (
            cycle,
            ClosedDefinitionRefusal::Malformed("cyclic definitions"),
        ),
    ] {
        let before = original.clone();
        assert_eq!(compose(&original).unwrap_err(), expected);
        assert_eq!(original, before);
    }
}

#[test]
fn fact_and_ite_work_preflight_preserves_existing_exact_caps() {
    let original = branch_fixture(E::bv_const(1, 64), E::bv_const(2, 64), true);
    let formula = original.negated_equivalence();
    for visit_limit in [true, false] {
        let (mut composer, endpoints) = prepare(&original, &formula).unwrap();
        if visit_limit {
            composer.visits = MAX_NODES;
        } else {
            composer.visits = 0;
            composer.edges = MAX_EDGES;
        }
        let text_before = composer.text.text.clone();
        assert_eq!(
            facts(&mut composer, &endpoints).err().unwrap(),
            ClosedDefinitionRefusal::Budget(if visit_limit {
                "equality visits"
            } else {
                "equality work edges"
            })
        );
        assert_eq!(composer.text.text, text_before);
    }
    let (mut composer, endpoints) = prepare(&original, &formula).unwrap();
    let ite = node(
        &composer,
        &E::ite(boolean("condition"), E::bv_const(1, 64), E::bv_const(2, 64)),
    );
    let condition = node(&composer, &boolean("condition"));
    let root_facts = facts(&mut composer, &endpoints).unwrap();
    let fact = root_facts.get(condition, true).unwrap();
    composer.visits = MAX_NODES - 1;
    // The ITE's ten-edge reservation plus the shared signed transport's three
    // edges use the real production budget; no test cap or bypass is installed.
    composer.edges = MAX_EDGES - 13;
    composer.ite_branch_equality(ite, fact).unwrap();
    assert_eq!(composer.visits, MAX_NODES);
    assert_eq!(composer.edges, MAX_EDGES);
    let text_before = composer.text.text.clone();
    assert_eq!(
        composer.ite_branch_equality(ite, fact).unwrap_err(),
        ClosedDefinitionRefusal::Budget("equality visits")
    );
    assert_eq!(composer.text.text, text_before);
    composer.visits = 0;
    composer.edges = MAX_EDGES - 9;
    assert_eq!(
        composer.ite_branch_equality(ite, fact).unwrap_err(),
        ClosedDefinitionRefusal::Budget("equality work edges")
    );
    assert_eq!(composer.text.text, text_before);
}

#[test]
fn shared_guard_chains_are_memoized_bounded_and_deterministic() {
    let mut census = Vec::new();
    for count in [40, 80] {
        let seed = boolean("seed");
        let mut previous = seed.clone();
        let mut premises = Vec::new();
        let mut aliases = Vec::new();
        for index in 0..count {
            let alias = boolean(&format!("guard_alias_{index}"));
            premises.push(alias.clone().eq_expr(previous));
            previous = alias.clone();
            aliases.push(alias);
        }
        premises.reverse();
        let original = obligation(
            E::BoolConst(true),
            guarded(previous, seed, E::bv_const(1, 64), E::bv_const(2, 64), true),
            premises,
        );
        let formula = original.negated_equivalence();
        let (mut composer, endpoints) = prepare(&original, &formula).unwrap();
        let ids: Vec<_> = aliases.iter().map(|alias| node(&composer, alias)).collect();
        let literal_before = literals(&composer);
        let root_facts = facts(&mut composer, &endpoints).unwrap();
        let before = (
            composer.text.text.len(),
            composer.text.steps,
            composer.visits,
            composer.edges,
        );
        for id in ids {
            let first = root_facts.get(id, true).unwrap();
            assert_eq!(first.proof(), root_facts.get(id, true).unwrap().proof());
            assert!(root_facts.get(id, false).is_none());
        }
        assert_eq!(
            (
                composer.text.text.len(),
                composer.text.steps,
                composer.visits,
                composer.edges
            ),
            before
        );
        assert_eq!(literals(&composer), literal_before);
        assert!(composer.literal_equalities.is_empty());
        let candidate = inspect(&original, count);
        assert_eq!(candidate.text, compose(&original).unwrap().text);
        assert!(candidate.steps <= 32 * count + 128);
        assert!(candidate.text.len() < MAX_OUTPUT_BYTES);
        census.push((candidate.steps, candidate.text.len()));
    }
    assert!(census[1].0 <= 2 * census[0].0 + 128);
    assert!(census[1].1 <= 2 * census[0].1 + 32_768);
}

#[test]
fn original_nested_boolean_premises_entail_only_their_actual_children() {
    let p = boolean("range");
    let q = boolean("alignment");
    let guard = boolean("guard");
    let source_geometry = E::BoolConst(true)
        .not_expr()
        .or_expr(p.clone().and_expr(q.clone()))
        .and_expr(E::BoolConst(true));
    let original = obligation(
        E::BoolConst(true),
        p.clone().and_expr(q.clone()),
        vec![source_geometry],
    );
    let candidate = inspect(&original, 0);
    assert!(candidate.text.contains(":rule or "));
    assert!(candidate.text.contains(":rule and "));
    for premise in [
        guard.not_expr().or_expr(p.clone().and_expr(q.clone())),
        E::BoolConst(false)
            .not_expr()
            .or_expr(p.clone().and_expr(q.clone())),
        p.clone(),
    ] {
        let loss = obligation(E::BoolConst(true), q.clone(), vec![premise]);
        assert!(matches!(
            compose(&loss),
            Err(ClosedDefinitionRefusal::Unsupported(_))
        ));
    }
}

#[test]
fn original_disjunction_needs_the_correct_negated_sibling() {
    let p = boolean("p");
    let q = boolean("q");
    for (left, right) in [(p.clone(), q.clone()), (q.clone(), p.clone())] {
        let original = obligation(
            E::BoolConst(true),
            right.clone(),
            vec![left.clone().or_expr(right.clone()), left.clone().not_expr()],
        );
        let candidate = inspect(&original, 0);
        assert!(candidate.text.contains(":rule or "));
        for premises in [
            vec![left.clone().or_expr(right.clone())],
            vec![
                left.clone().or_expr(right.clone()),
                right.clone().not_expr(),
            ],
        ] {
            let loss = obligation(E::BoolConst(true), right.clone(), premises);
            assert!(matches!(
                compose(&loss),
                Err(ClosedDefinitionRefusal::Unsupported(_))
            ));
        }
    }
}
