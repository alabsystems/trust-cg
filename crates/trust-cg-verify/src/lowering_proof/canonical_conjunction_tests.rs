// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Canonical query construction is not a proof or a native admission receipt.

use super::*;
use crate::smt::{EvalResult, SmtSort};

fn obligation(premises: Vec<SmtExpr>) -> ProofObligation {
    ProofObligation {
        name: "canonical ordered conjunction control".into(),
        trust_ir_expr: SmtExpr::bv_const(0, 1),
        aarch64_expr: SmtExpr::var("endpoint", 1),
        inputs: vec![("endpoint".into(), 1)],
        preconditions: premises,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

fn atom(index: usize) -> SmtExpr {
    SmtExpr::uf(format!("premise_{index}"), vec![], SmtSort::Bool)
}

// The test leaves have no And root: inspect actual connectors, not the
// construction helper's partition algorithm.
fn envelope(formula: &SmtExpr) -> (Vec<&SmtExpr>, usize, usize) {
    let mut pending = vec![(formula, 0)];
    let mut leaves = Vec::new();
    let mut connectors = 0;
    let mut height = 0;
    while let Some((node, depth)) = pending.pop() {
        if let SmtExpr::And { lhs, rhs } = node {
            connectors += 1;
            pending.push((rhs, depth + 1));
            pending.push((lhs, depth + 1));
        } else {
            height = height.max(depth);
            leaves.push(node);
        }
    }
    (leaves, connectors, height)
}

#[test]
fn every_ordered_occurrence_has_minimal_logarithmic_connector_height() {
    for count in [0, 1, 2, 3, 4, 6, 7, 8, 15, 16, 31, 32, 255, 256, 4096] {
        let original = obligation((0..count).map(atom).collect());
        let before = original.clone();
        let formula = original.negated_equivalence();
        let (leaves, connectors, height) = envelope(&formula);
        let expected = original
            .preconditions
            .iter()
            .rev()
            .cloned()
            .chain(std::iter::once(
                original
                    .trust_ir_expr
                    .clone()
                    .eq_expr(original.aarch64_expr.clone())
                    .not_expr(),
            ))
            .collect::<Vec<_>>();
        assert_eq!(original, before);
        assert_eq!(leaves.len(), expected.len());
        assert!(leaves.iter().zip(&expected).all(|(a, b)| *a == b));
        assert_eq!(connectors, count, "no dropped or invented connective");
        assert_eq!(height, (count + 1).next_power_of_two().ilog2() as usize);
    }
}

#[test]
fn duplicate_true_false_and_compound_premises_remain_original_occurrences() {
    let compound = atom(10).and_expr(atom(11));
    let original = obligation(vec![
        atom(1),
        SmtExpr::BoolConst(true),
        compound.clone(),
        atom(1),
        SmtExpr::BoolConst(false),
        compound,
    ]);
    let formula = original.negated_equivalence();
    let tail = original
        .trust_ir_expr
        .clone()
        .eq_expr(original.aarch64_expr.clone())
        .not_expr();
    let expected = original
        .preconditions
        .iter()
        .rev()
        .chain(std::iter::once(&tail))
        .collect::<Vec<_>>();
    let mut pending = vec![&formula];
    let mut actual = Vec::new();
    while let Some(node) = pending.pop() {
        // An original compound premise stays a leaf of the envelope. Unique
        // atom names distinguish it from any newly constructed connector.
        if expected.contains(&node) {
            actual.push(node);
        } else if let SmtExpr::And { lhs, rhs } = node {
            pending.push(rhs);
            pending.push(lhs);
        } else {
            panic!("invented canonical leaf: {node:?}");
        }
    }
    assert_eq!(actual, expected);
    assert_eq!(original.preconditions.len(), 6);
}

#[test]
fn every_boolean_assignment_matches_the_original_conjunction_semantics() {
    for count in 0..=8 {
        let premises = (0..count)
            .map(|i| SmtExpr::var(format!("p{i}"), 1).eq_expr(SmtExpr::bv_const(1, 1)))
            .collect::<Vec<_>>();
        let original = obligation(premises);
        let formula = original.negated_equivalence();
        for assignment in 0..1usize << (count + 1) {
            let mut env = EvalEnv::default();
            let endpoint = (assignment >> count) & 1;
            env.insert("endpoint".into(), endpoint as u64);
            for i in 0..count {
                env.insert(format!("p{i}"), ((assignment >> i) & 1) as u64);
            }
            let expected = endpoint != 0 && (0..count).all(|i| assignment & (1 << i) != 0);
            assert_eq!(formula.eval(&env), EvalResult::Bool(expected));
        }
    }
}

#[test]
fn zero_and_one_premise_queries_keep_the_exact_existing_small_shape() {
    let empty = obligation(vec![]);
    let tail = empty
        .trust_ir_expr
        .clone()
        .eq_expr(empty.aarch64_expr.clone())
        .not_expr();
    assert_eq!(empty.negated_equivalence(), tail);
    let single = obligation(vec![atom(1)]);
    assert_eq!(single.negated_equivalence(), atom(1).and_expr(tail));
}
