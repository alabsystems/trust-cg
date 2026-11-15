// trust-cg-verify/src/array_row_lowering_tests.rs - tests for array elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::smt::{EvalEnv, EvalResult};

fn eval_bool(expr: &SmtExpr, env: &EvalEnv) -> Option<bool> {
    match expr.try_eval(env) {
        Ok(EvalResult::Bool(b)) => Some(b),
        _ => None,
    }
}

fn const_array(value: SmtExpr) -> SmtExpr {
    SmtExpr::ConstArray {
        index_sort: SmtSort::BitVec(2),
        value: Arc::new(value),
    }
}

fn store(array: SmtExpr, index: SmtExpr, value: SmtExpr) -> SmtExpr {
    SmtExpr::Store {
        array: Arc::new(array),
        index: Arc::new(index),
        value: Arc::new(value),
    }
}

fn select(array: SmtExpr, index: SmtExpr) -> SmtExpr {
    SmtExpr::Select {
        array: Arc::new(array),
        index: Arc::new(index),
    }
}

fn arbitrary_array(name: &str) -> SmtExpr {
    SmtExpr::uf(name, vec![], SmtSort::bv_array(2, 2))
}

#[test]
fn arbitrary_memory_reads_keep_total_function_identity_and_aliases() {
    let (i, j, v) = (
        SmtExpr::var("i", 2),
        SmtExpr::var("j", 2),
        SmtExpr::var("v", 2),
    );
    let array = arbitrary_array("memory");
    let formula =
        select(store(array.clone(), i.clone(), v.clone()), j.clone()).eq_expr(SmtExpr::ite(
            i.clone().eq_expr(j.clone()),
            v,
            SmtExpr::uf("memory", vec![j.clone()], SmtSort::BitVec(2)),
        ));
    // The mixed-signature formula is deliberately invalid even if a solver
    // would simplify the read-over-write equality to true.
    assert!(matches!(
        eliminate_arrays(&formula),
        Err(ArrayDecline::Unsupported(_))
    ));
    let lowered = eliminate_arrays(
        &select(store(array, i.clone(), SmtExpr::var("v", 2)), j.clone())
            .eq_expr(SmtExpr::bv_const(1, 2)),
    )
    .unwrap();
    let expected = SmtExpr::ite(
        i.eq_expr(j.clone()),
        SmtExpr::var("v", 2),
        SmtExpr::uf("memory", vec![j], SmtSort::BitVec(2)),
    )
    .eq_expr(SmtExpr::bv_const(1, 2));
    assert_eq!(lowered, expected);
    assert!(!mentions_arrays(&lowered));
    // Concrete sampling remains unable to grant credit to opaque memory.
    assert!(eval_bool(&lowered, &EvalEnv::default()).is_none());
}

#[test]
fn arbitrary_memory_signature_and_cold_scope_conflicts_decline() {
    let i = SmtExpr::var("i", 2);
    let read = select(arbitrary_array("memory"), i.clone());
    let formula = read.clone().eq_expr(SmtExpr::bv_const(0, 2));
    assert!(eliminate_arrays_with_reserved(&formula, &["memory"]).is_err());
    for conflict in [
        SmtExpr::var("memory", 2),
        SmtExpr::var("|memory|", 2),
        SmtExpr::uf("memory", vec![], SmtSort::BitVec(2)),
        SmtExpr::uf_decl("memory", vec![SmtSort::BitVec(2)], SmtSort::BitVec(2)),
        select(
            SmtExpr::uf("memory", vec![], SmtSort::bv_array(2, 8)),
            i.clone(),
        ),
        select(
            SmtExpr::uf("other", vec![i.clone()], SmtSort::bv_array(2, 2)),
            i.clone(),
        ),
        select(arbitrary_array("other"), SmtExpr::var("wide_index", 8)),
    ] {
        let cold = SmtExpr::ite(SmtExpr::bool_const(true), read.clone(), conflict);
        assert!(matches!(
            eliminate_arrays(&cold.eq_expr(SmtExpr::bv_const(0, 2))),
            Err(ArrayDecline::Unsupported(_))
        ));
    }
    assert!(
        eliminate_arrays(&arbitrary_array("memory").eq_expr(arbitrary_array("other"))).is_err()
    );
    assert!(eliminate_arrays_with_reserved(&formula, &["|memory|"]).is_err());
    let oversized = "x".repeat(MAX_REWRITTEN_NODES);
    assert!(eliminate_arrays_with_reserved(&formula, &[&oversized]).is_err());
}

#[test]
fn arbitrary_memory_bridge_checks_even_unused_input_declarations() {
    use crate::lowering_proof::{MachineSideProvenance, ProofObligation};
    let mut obligation = ProofObligation {
        name: "arbitrary memory declaration collision".into(),
        trust_ir_expr: SmtExpr::bool_const(true),
        aarch64_expr: select(arbitrary_array("memory"), SmtExpr::bv_const(0, 2))
            .eq_expr(SmtExpr::bv_const(0, 2)),
        inputs: vec![("unused_input".into(), 2)],
        fp_inputs: vec![],
        preconditions: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    let config = crate::ay_bridge::AYConfig::default();
    assert_eq!(
        crate::ay_bridge::generate_lowered_queries(&obligation, &config).len(),
        1
    );
    obligation.inputs[0].0 = "memory".into();
    assert!(crate::ay_bridge::generate_lowered_queries(&obligation, &config).is_empty());
    obligation.inputs[0].0 = "|memory|".into();
    assert!(crate::ay_bridge::generate_lowered_queries(&obligation, &config).is_empty());
}

/// Read-over-write is an EQUIVALENCE: over every assignment of 2-bit
/// indices and values, the rewritten formula has exactly the original's truth
/// value — including aliasing stores, an overwritten slot, and a read of the
/// constant default.
#[test]
fn read_over_write_is_exact_on_every_small_assignment() {
    let v = |name: &str| SmtExpr::var(name, 2);
    let (d, i, j, k, a, b) = (v("d"), v("i"), v("j"), v("k"), v("a"), v("b"));
    let memory = store(
        store(const_array(d.clone()), i.clone(), a.clone()),
        j.clone(),
        b.clone(),
    );
    let chosen = SmtExpr::ite(
        a.clone().eq_expr(b.clone()),
        memory.clone(),
        store(memory.clone(), k.clone(), d.clone()),
    );
    // Offset addresses over one base: provably equal or distinct by offset,
    // and still exact where two different bases meet.
    let at = |base: &SmtExpr, offset: u64| base.clone().bvadd(SmtExpr::bv_const(offset, 2));
    let bytes = store(
        store(
            store(const_array(d.clone()), at(&i, 1), a.clone()),
            at(&i, 2),
            b.clone(),
        ),
        at(&j, 1),
        d.clone(),
    );
    let formulas = [
        select(bytes.clone(), at(&i, 1)).eq_expr(a.clone()),
        select(bytes.clone(), at(&i, 5)).eq_expr(a.clone()),
        select(bytes.clone(), at(&i, 2)).eq_expr(b.clone()),
        select(bytes, k.clone()).eq_expr(d.clone()),
        select(memory.clone(), k.clone()).eq_expr(a.clone()),
        select(memory.clone(), i.clone())
            .eq_expr(select(memory.clone(), j.clone()))
            .not_expr(),
        select(chosen, k.clone()).eq_expr(d.clone()),
    ];
    for formula in &formulas {
        let lowered = eliminate_arrays(formula).expect("store chains over a constant lower");
        assert!(!mentions_arrays(&lowered), "{lowered}");
        for bits in 0u64..(1 << 12) {
            let mut env = EvalEnv::default();
            for (slot, name) in ["d", "i", "j", "k", "a", "b"].iter().enumerate() {
                env.insert((*name).to_string(), (bits >> (2 * slot)) & 3);
            }
            assert_eq!(
                eval_bool(formula, &env),
                eval_bool(&lowered, &env),
                "{formula} at {env:?}"
            );
        }
    }
}

#[test]
fn every_other_array_construct_declines() {
    let array_var = SmtExpr::Var {
        name: "mem".to_string(),
        width: 8,
    };
    let x = SmtExpr::var("x", 2);
    // A read of an array VARIABLE: its contents are not given by an axiom.
    assert!(matches!(
        eliminate_arrays(&select(array_var, x.clone()).eq_expr(x.clone())),
        Err(ArrayDecline::Unsupported(_))
    ));
    // An equality between arrays needs extensionality, not read-over-write.
    let one = store(const_array(x.clone()), x.clone(), x.clone());
    let two = const_array(x.clone());
    assert!(matches!(
        eliminate_arrays(&one.eq_expr(two)),
        Err(ArrayDecline::Unsupported(_))
    ));
    // Nothing to do without arrays.
    assert_eq!(
        eliminate_arrays(&x.clone().eq_expr(x)),
        Err(ArrayDecline::NoArrays)
    );
}

/// Every array obligation in the proof database either declines or lowers to
/// a formula with the SAME truth value as the original on sampled inputs
/// (the crate's own evaluator reads the arrays).
#[test]
fn every_database_array_obligation_lowers_to_an_equivalent_formula() {
    let db = crate::proof_database::ProofDatabase::new();
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let (mut lowered_count, mut checked) = (0usize, 0usize);
    for proof in db.all() {
        let ob = &proof.obligation;
        let formula = crate::ay_bridge::expand_bounded_quantifiers(&ob.negated_equivalence());
        let Ok(lowered) = eliminate_arrays(&formula) else {
            continue;
        };
        assert!(!mentions_arrays(&lowered), "{}", ob.name);
        lowered_count += 1;
        for point in 0..32u64 {
            let mut env = EvalEnv::default();
            for (name, width) in &ob.inputs {
                let mask = if *width >= 64 {
                    u64::MAX
                } else {
                    (1u64 << width) - 1
                };
                // Small values collide often, which is what exercises aliasing.
                let value = if point % 2 == 0 { next() % 4 } else { next() };
                env.insert(name.clone(), value & mask);
            }
            let (Some(original), Some(image)) =
                (eval_bool(&formula, &env), eval_bool(&lowered, &env))
            else {
                continue;
            };
            assert_eq!(original, image, "{} at {env:?}", ob.name);
            checked += 1;
        }
    }
    assert!(
        lowered_count >= 30,
        "only {lowered_count} array obligations lowered"
    );
    assert!(
        checked >= lowered_count * 16,
        "only {checked} points checked"
    );
}

#[test]
fn array_presence_declines_shared_array_free_dag_without_expansion() {
    let mut expr = SmtExpr::var("x", 64);
    for _ in 0..64 {
        let shared = Arc::new(expr);
        expr = SmtExpr::BvAdd {
            lhs: shared.clone(),
            rhs: shared,
            width: 64,
        };
    }
    assert!(!mentions_arrays(&expr));
    assert!(matches!(
        eliminate_arrays(&expr),
        Err(ArrayDecline::NoArrays)
    ));
}

#[test]
fn array_presence_keeps_nested_ite_and_declaration_distinctions() {
    let array = const_array(SmtExpr::bv_const(0, 8));
    let selected = SmtExpr::ite(SmtExpr::bool_const(false), array.clone(), array);
    let application = SmtExpr::uf("array_argument", vec![selected], SmtSort::Bool);
    assert!(mentions_arrays(&application));
    // A declaration by itself was never an array expression to eliminate.
    assert!(!mentions_arrays(&SmtExpr::uf_decl(
        "decl",
        vec![],
        SmtSort::bv_array(64, 8)
    )));
}

#[test]
fn nested_modular_addresses_match_concrete_small_words_and_keep_wide_refusal() {
    for width in [2, 3, 8, 64] {
        let base = SmtExpr::var("base", width);
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        for (left, right) in [
            (
                base.clone()
                    .bvadd(SmtExpr::bv_const(3, width))
                    .bvadd(SmtExpr::bv_const(4, width)),
                base.clone().bvadd(SmtExpr::bv_const(7, width)),
            ),
            (
                base.clone()
                    .bvadd(SmtExpr::bv_const(mask, width))
                    .bvadd(SmtExpr::bv_const(1, width)),
                base.clone(),
            ),
            (
                base.clone()
                    .bvsub(SmtExpr::bv_const(1, width))
                    .bvadd(SmtExpr::bv_const(2, width)),
                base.clone().bvadd(SmtExpr::bv_const(1, width)),
            ),
            (
                base.clone().bvsub(SmtExpr::bv_const(1, width)),
                base.clone(),
            ),
        ] {
            let result = same_address(&left, &right, &mut || Ok(()))
                .unwrap()
                .unwrap();
            let equality = left.eq_expr(right);
            let values: Vec<u64> = if width == 64 {
                vec![0, 1, 80, u64::MAX]
            } else {
                (0..=mask).collect()
            };
            for value in values {
                let mut env = EvalEnv::default();
                env.insert("base".into(), value);
                assert_eq!(eval_bool(&equality, &env), Some(result));
            }
        }
    }
    let wide = SmtExpr::var("wide", 128);
    assert_eq!(
        same_address(
            &wide.clone().bvsub(SmtExpr::bv_const(1, 128)),
            &wide.bvadd(SmtExpr::bv_const(u64::MAX, 128)),
            &mut || Ok(())
        )
        .unwrap(),
        None,
        "u64 negative offsets must not be mistaken for 128-bit modular offsets"
    );
    // These two 128-bit addresses differ by 2^64. The old u64-only
    // offset inference must not turn this satisfiable read into #x01.
    let wide = SmtExpr::var("wide", 128);
    let memory = SmtExpr::uf("wide_memory", vec![], SmtSort::bv_array(128, 8));
    let written = wide.clone().bvsub(SmtExpr::bv_const(1, 128));
    let read = wide.bvadd(SmtExpr::bv_const(u64::MAX, 128));
    let source = select(store(memory, written, SmtExpr::bv_const(1, 8)), read)
        .eq_expr(SmtExpr::bv_const(0, 8));
    let lowered = eliminate_arrays(&source).unwrap();
    assert!(
        lowered.any_node(|node| matches!(node, SmtExpr::Ite { .. })),
        "unsupported wide offset inference must retain the conditional read"
    );
    if let Some(directory) = std::env::var_os("QUERY_SHARING_TEST_OUTPUT_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        let prelude = "(set-logic QF_AUFBV)\n(declare-const wide (_ BitVec 128))\n";
        std::fs::write(directory.join("wide128.original.smt2"), format!(
            "{prelude}(declare-fun wide_memory () (Array (_ BitVec 128) (_ BitVec 8)))\n(assert {source})\n(check-sat)\n(exit)\n")).unwrap();
        std::fs::write(directory.join("wide128.image.smt2"), format!(
            "{prelude}(declare-fun wide_memory ((_ BitVec 128)) (_ BitVec 8))\n(assert {lowered})\n(check-sat)\n(exit)\n")).unwrap();
    }
    let expression = SmtExpr::var("base", 64)
        .bvadd(SmtExpr::bv_const(1, 64))
        .bvadd(SmtExpr::bv_const(2, 64));
    let mut remaining = 1usize;
    assert!(
        affine_address(&expression, &mut || {
            remaining = remaining
                .checked_sub(1)
                .ok_or_else(|| "existing budget exhausted".to_owned())?;
            Ok(())
        })
        .is_err(),
        "the iterative walk must propagate the shared owner's refusal"
    );
}
