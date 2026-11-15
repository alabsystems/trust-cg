// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Untrusted candidate-fragment controls, NOT independent proof acceptance.
//! The ordinary original-query checker remains the qualification boundary.

use super::*;

fn fragment(
    left: E,
    right: E,
    predicate: bool,
    collide_keys: bool,
) -> Result<(Option<Id>, String), ClosedDefinitionRefusal> {
    let original = left.eq_expr(right);
    let graph = Graph::new(&original)?;
    let root = graph.pointers[&(&original as *const E)];
    let pair = (graph.nodes[root].children[0], graph.nodes[root].children[1]);
    let keys = (0..graph.nodes.len())
        .map(|id| if collide_keys { 0 } else { id })
        .collect();
    let mut composer = Composer {
        graph,
        text: Text {
            text: String::new(),
            next: 0,
            steps: 0,
        },
        equalities: HashMap::new(),
        literal_equalities: HashMap::new(),
        keys,
        known_true: HashMap::new(),
        truths: HashMap::new(),
        root_facts: None,
        selected_ites: HashMap::new(),
        modular_candidate: false,
        visits: 0,
        edges: 0,
    };
    let result = if predicate {
        composer.polynomial_predicate_equality(pair)?
    } else {
        composer.polynomial_equality(pair)?
    };
    Ok((result, composer.text.text))
}

fn inspect(left: E, right: E, predicate: bool) -> String {
    let (proof, text) = fragment(left, right, predicate, false).unwrap();
    assert!(proof.is_some());
    assert!(text.contains(":rule poly_simp)"));
    assert!(text.contains(":rule trans "));
    assert!(!text.contains("(assume "));
    assert!(!text.contains("declare-"));
    assert!(!text.contains(":rule trust"));
    assert!(!text.contains(":rule hole"));
    text
}

#[test]
fn polynomial_modular_identities_keep_exact_width_and_original_terms() {
    for bits in [1, 8, 32, 64] {
        let x = E::var("ordinary_input", bits);
        let zero = E::bv_const(0, bits);
        let one = E::bv_const(1, bits);
        for (left, right) in [
            (x.clone().bvadd(zero.clone()), x.clone()),
            (x.clone().bvmul(one.clone()), x.clone()),
            (x.clone().bvsub(zero.clone()), x.clone()),
            (zero.bvsub(x.clone()), x.clone().bvneg()),
            (
                x.clone().bvadd(E::bv_const(mask(bits), bits)).bvadd(one),
                x.clone(),
            ),
        ] {
            let original = left.to_string();
            let text = inspect(left, right, false);
            assert!(text.contains(&original));
            assert!(
                text.contains(&format!("(_ bv0 {bits})"))
                    || text.contains(&format!("(_ bv1 {bits})"))
            );
        }
    }
}

#[test]
fn polynomial_shallow_reassociation_and_constant_products_are_modular() {
    for bits in [8, 32, 64] {
        let x = E::var("x", bits);
        let y = E::uf("unrelated_atom", vec![], SmtSort::BitVec(bits));
        inspect(
            x.clone().bvadd(E::bv_const(3, bits)).bvadd(y.clone()),
            x.clone().bvadd(y.clone().bvadd(E::bv_const(3, bits))),
            false,
        );
        inspect(
            x.clone().bvmul(E::bv_const(2, bits)).bvadd(x.clone()),
            E::bv_const(3, bits).bvmul(x),
            false,
        );
    }
}

#[test]
fn polynomial_zero_comparison_uses_literal_odd_one_relation_schema() {
    for bits in [1, 8, 32, 64] {
        let x = E::var("x", bits);
        let constant = E::bv_const(1, bits);
        let text = inspect(
            x.clone()
                .bvsub(constant.clone())
                .eq_expr(E::bv_const(0, bits)),
            x.eq_expr(constant),
            true,
        );
        assert!(text.contains(":rule poly_simp_rel "));
        assert_eq!(text.matches(":rule poly_simp_rel ").count(), 1);
        assert!(text.contains(&format!("(bvmul (_ bv1 {bits}) (bvsub ")));
    }
}

#[test]
fn polynomial_even_cancellation_and_changed_terms_do_not_get_candidates() {
    for bits in [8, 32, 64] {
        let x = E::var("x", bits);
        let zero = E::bv_const(0, bits);
        for (left, right, predicate) in [
            (x.clone().bvadd(E::bv_const(1, bits)), x.clone(), false),
            (x.clone().bvmul(E::bv_const(2, bits)), x.clone(), false),
            (
                x.clone().bvmul(E::bv_const(2, bits)).eq_expr(zero.clone()),
                x.clone().eq_expr(zero.clone()),
                true,
            ),
            (
                x.clone().bvsub(E::bv_const(3, bits)).eq_expr(zero),
                x.eq_expr(E::bv_const(4, bits)),
                true,
            ),
        ] {
            let (proof, text) = fragment(left, right, predicate, false).unwrap();
            assert!(proof.is_none());
            assert!(text.is_empty());
        }
    }
}

#[test]
fn polynomial_unknown_nonlinear_mixed_and_outside_widths_stay_unsupported() {
    let x = E::var("x", 64);
    let y = E::var("y", 64);
    for left in [
        x.clone().bvand(E::bv_const(u64::MAX, 64)),
        x.clone().bvmul(y),
    ] {
        assert!(fragment(left, x.clone(), false, false).unwrap().0.is_none());
    }
    let mixed = E::BvAdd {
        lhs: Arc::new(E::var("narrow", 32)),
        rhs: Arc::new(x.clone()),
        width: 64,
    };
    assert!(matches!(
        fragment(mixed, x, false, false),
        Err(ClosedDefinitionRefusal::Malformed(_))
    ));
    for bits in [0, 65] {
        let invalid = E::BvConst {
            value: 0,
            width: bits,
        };
        let result = fragment(
            invalid.clone().bvadd(invalid.clone()),
            invalid,
            false,
            false,
        );
        assert!(result.is_err() || result.unwrap().0.is_none());
    }
}

#[test]
fn polynomial_equal_metadata_does_not_prove_distinct_original_atoms() {
    let left = E::var("first", 64).bvadd(E::bv_const(0, 64));
    let right = E::var("second", 64);
    let formula = left.clone().eq_expr(right.clone());
    let graph = Graph::new(&formula).unwrap();
    let root = graph.pointers[&(&formula as *const E)];
    let [a, b] = graph.nodes[root].children.as_slice() else {
        panic!("binary equality")
    };
    let a = polynomial_key(&graph, *a, |_| Some(0)).unwrap();
    let b = polynomial_key(&graph, *b, |_| Some(0)).unwrap();
    assert_eq!(a.key, b.key);
    assert!(matches!(
        fragment(left, right, false, true),
        Err(ClosedDefinitionRefusal::Unsupported(_))
    ));
}

#[test]
fn polynomial_shared_shell_census_is_bounded_and_fragment_depth_is_not_raised() {
    let common = E::var("x", 32).bvadd(E::bv_const(1, 32));
    let original = common.clone().bvadd(common);
    let graph = Graph::new(&original).unwrap();
    let root = graph.pointers[&(&original as *const E)];
    let shape = polynomial_key(&graph, root, Some).unwrap();
    assert_eq!(shape.visits, 4);
    assert_eq!(shape.edges, 6);
    assert_eq!(shape.key.constant, 2);
    assert_eq!(shape.key.terms.len(), 1);
    assert_eq!(shape.key.terms[0].1, 2);
    let mut deep = E::var("x", 32);
    for _ in 0..MAX_SHELL_DEPTH {
        deep = deep.bvadd(E::bv_const(0, 32));
    }
    let graph = Graph::new(&deep).unwrap();
    let root = graph.pointers[&(&deep as *const E)];
    assert!(polynomial_key(&graph, root, Some).is_none());
}

#[test]
fn polynomial_shared_subtree_reused_deeper_keeps_exact_expanded_depth_floor() {
    let common = E::var("x", 32).bvadd(E::bv_const(1, 32));
    // The first occurrence caches height two at depth two. Its occurrence at
    // depth three is legal, but depth four would hide children at depth five.
    let nearby = common.clone().bvadd(common.clone().bvadd(common.clone()));
    let graph = Graph::new(&nearby).unwrap();
    let root = graph.pointers[&(&nearby as *const E)];
    assert!(polynomial_key(&graph, root, Some).is_some());
    let too_deep = common
        .clone()
        .bvadd(common.clone().bvadd(common.clone().bvadd(common)));
    let graph = Graph::new(&too_deep).unwrap();
    let root = graph.pointers[&(&too_deep as *const E)];
    let (mut visits, mut edges) = (0, 0);
    assert!(
        shell(&graph, root, &Some, &mut visits, &mut edges)
            .unwrap()
            .is_none()
    );
    assert!(visits <= MAX_SHELL_NODES);
    assert!(edges <= MAX_EDGES);
}

#[test]
fn polynomial_shell_charges_existing_aggregate_visits_and_work_edges() {
    let original = E::var("x", 32).bvadd(E::bv_const(0, 32));
    let graph = Graph::new(&original).unwrap();
    let root = graph.pointers[&(&original as *const E)];
    let (mut visits, mut edges) = (MAX_NODES, 0);
    assert_eq!(
        shell(&graph, root, &Some, &mut visits, &mut edges)
            .err()
            .unwrap(),
        ClosedDefinitionRefusal::Budget("equality visits")
    );
    let (mut visits, mut edges) = (0, MAX_EDGES);
    assert_eq!(
        shell(&graph, root, &Some, &mut visits, &mut edges)
            .err()
            .unwrap(),
        ClosedDefinitionRefusal::Budget("equality work edges")
    );
}

#[test]
fn polynomial_fresh_atom_alignment_bounds_actual_definitions_before_recursion() {
    let atoms: Vec<_> = (0..7)
        .map(|index| E::uf(format!("atom{index}"), vec![], SmtSort::BitVec(64)))
        .collect();
    let mut original = E::BoolConst(true);
    for pair in atoms.windows(2) {
        original = original.and_expr(pair[0].clone().eq_expr(pair[1].clone()));
    }
    let mut graph = Graph::new(&original).unwrap();
    let equations: Vec<_> = graph
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(id, node)| matches!(node.original, E::Eq { .. }).then_some(id))
        .collect();
    for equation in equations {
        graph.definition(equation, 0).unwrap();
    }
    graph.acyclic(None).unwrap();
    let first = graph
        .nodes
        .iter()
        .position(|node| node.original == &atoms[0])
        .unwrap();
    let last = graph
        .nodes
        .iter()
        .position(|node| node.original == &atoms[6])
        .unwrap();
    let (mut visits, mut edges) = (0, 0);
    assert!(!bounded_atom_dependencies(&graph, (first, last), &mut visits, &mut edges).unwrap());
    assert!(visits <= MAX_SHELL_DEPTH + 1);
    assert!(edges <= MAX_SHELL_DEPTH);
    let (mut visits, mut edges) = (MAX_NODES, 0);
    assert_eq!(
        bounded_atom_dependencies(&graph, (last, last), &mut visits, &mut edges).unwrap_err(),
        ClosedDefinitionRefusal::Budget("equality visits")
    );
}
