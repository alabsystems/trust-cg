// trust-cg-verify/src/derived_operator_lowering_tests.rs - tests for the derived-operator lowering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::smt::{EvalEnv, EvalResult};

fn eval(expr: &SmtExpr, env: &EvalEnv) -> Option<EvalResult> {
    expr.try_eval(env).ok()
}

fn mentions_derived(expr: &SmtExpr) -> bool {
    let text = expr.to_string();
    [
        "(bvule ", "(bvuge ", "(bvugt ", "(bvsle ", "(bvsge ", "(bvsgt ", "(bvsdiv ", "(bvashr ",
    ]
    .iter()
    .any(|op| text.contains(op))
}

/// Every derived comparison, `bvsdiv` and `bvashr` (overshift included), at 4
/// bits over every assignment. The evaluator uses a zero sentinel for BOTH
/// division operations: agreement there is not evidence of SMT-LIB's actual
/// division-by-zero value (the spelling test below is a separate control).
#[test]
fn each_definition_agrees_with_its_operator_on_every_small_input() {
    let (a, b) = (SmtExpr::var("a", 4), SmtExpr::var("b", 4));
    let build = |name: &str| -> SmtExpr {
        let (lhs, rhs, width) = (Arc::new(a.clone()), Arc::new(b.clone()), 4);
        match name {
            "bvule" => SmtExpr::BvUle { lhs, rhs, width },
            "bvuge" => SmtExpr::BvUge { lhs, rhs, width },
            "bvugt" => SmtExpr::BvUgt { lhs, rhs, width },
            "bvsle" => SmtExpr::BvSle { lhs, rhs, width },
            "bvsge" => SmtExpr::BvSge { lhs, rhs, width },
            "bvsgt" => SmtExpr::BvSgt { lhs, rhs, width },
            "bvashr" => SmtExpr::BvAshr { lhs, rhs, width },
            _ => SmtExpr::BvSDiv { lhs, rhs, width },
        }
    };
    for name in [
        "bvule", "bvuge", "bvugt", "bvsle", "bvsge", "bvsgt", "bvsdiv", "bvashr",
    ] {
        let original = build(name);
        let lowered = lower_derived_operators(&original).expect("a derived operator lowers");
        assert!(!mentions_derived(&lowered), "{name}: {lowered}");
        for bits in 0..256_u64 {
            let mut env = EvalEnv::default();
            env.insert("a".to_string(), bits & 15);
            env.insert("b".to_string(), bits >> 4);
            assert_eq!(
                original.try_eval(&env).expect("small original evaluates"),
                lowered.try_eval(&env).expect("small definition evaluates"),
                "{name} at a={} b={}",
                bits & 15,
                bits >> 4
            );
        }
    }
}

/// The `bvsdiv` spelling IS the SMT-LIB definition, character for character:
/// its zero-divisor values are the standard's, whatever an evaluator's
/// convention for them.
#[test]
fn signed_division_is_spelled_as_the_standard_defines_it() {
    let lowered = lower_derived_operators(&SmtExpr::var("s", 8).bvsdiv(SmtExpr::var("t", 8)))
        .expect("bvsdiv lowers");
    let msb = |x: &str| format!("((_ extract 7 7) {x})");
    let is = |x: &str, v: u8| format!("(= {} (_ bv{v} 1))", msb(x));
    let expected = format!(
        "(ite (and {} {}) (bvudiv s t) (ite (and {} {}) (bvneg (bvudiv (bvneg s) t)) \
         (ite (and {} {}) (bvneg (bvudiv s (bvneg t))) (bvudiv (bvneg s) (bvneg t)))))",
        is("s", 0),
        is("t", 0),
        is("s", 1),
        is("t", 0),
        is("s", 0),
        is("t", 1)
    );
    assert_eq!(lowered.to_string(), expected);
}

#[test]
fn a_formula_without_derived_operators_is_left_alone() {
    let x = SmtExpr::var("x", 8);
    let formula = x.clone().bvadd(x.clone()).eq_expr(x);
    assert!(lower_derived_operators(&formula).is_none());
}

#[test]
fn lowering_preserves_shared_rewritten_nodes() {
    let shared = Arc::new(SmtExpr::var("a", 8).bvule(SmtExpr::var("b", 8)));
    let original = SmtExpr::And {
        lhs: shared.clone(),
        rhs: shared,
    };
    let lowered = lower_derived_operators(&original).expect("comparison lowers");
    let SmtExpr::And { lhs, rhs } = lowered else {
        panic!("outer conjunction changed")
    };
    assert!(
        Arc::ptr_eq(&lhs, &rhs),
        "one shared input must yield one shared output"
    );
}

#[test]
fn lowering_reuses_unchanged_shared_children() {
    let shared = Arc::new(SmtExpr::var("a", 8).bvadd(SmtExpr::var("b", 8)));
    let original = SmtExpr::BvUgt {
        lhs: shared.clone(),
        rhs: shared.clone(),
        width: 8,
    };
    let lowered = lower_derived_operators(&original).expect("comparison lowers");
    let SmtExpr::BvUlt { lhs, rhs, .. } = lowered else {
        panic!("expected swapped comparison")
    };
    assert!(
        Arc::ptr_eq(&lhs, &shared),
        "unchanged arithmetic should retain its allocation"
    );
    assert!(
        Arc::ptr_eq(&rhs, &shared),
        "unchanged arithmetic should remain shared"
    );
}

#[test]
fn lowering_keeps_binders_and_shared_boundaries() {
    let lower = Arc::new(SmtExpr::bv_const(0, 8));
    let upper = Arc::new(SmtExpr::bv_const(255, 8));
    let body = Arc::new(SmtExpr::var("x", 8).bvugt(SmtExpr::bv_const(3, 8)));
    let input = SmtExpr::And {
        lhs: Arc::new(SmtExpr::ForAll {
            var: "x".into(),
            var_width: 8,
            lower: lower.clone(),
            upper: upper.clone(),
            body: body.clone(),
        }),
        rhs: Arc::new(SmtExpr::Exists {
            var: "y".into(),
            var_width: 8,
            lower: lower.clone(),
            upper: upper.clone(),
            body,
        }),
    };
    let result = lower_derived_operators(&input).unwrap();
    let SmtExpr::And { lhs, rhs } = result else {
        panic!("conjunction changed")
    };
    let SmtExpr::ForAll {
        var,
        var_width,
        lower: lo,
        upper: hi,
        body: left,
    } = lhs.as_ref()
    else {
        panic!("universal binder changed")
    };
    assert_eq!(var, "x");
    assert_eq!(*var_width, 8);
    assert!(Arc::ptr_eq(lo, &lower) && Arc::ptr_eq(hi, &upper));
    let SmtExpr::Exists {
        var,
        var_width,
        lower: lo,
        upper: hi,
        body: right,
    } = rhs.as_ref()
    else {
        panic!("existential binder changed")
    };
    assert_eq!(var, "y");
    assert_eq!(*var_width, 8);
    assert!(Arc::ptr_eq(lo, &lower) && Arc::ptr_eq(hi, &upper));
    assert!(Arc::ptr_eq(left, right));
    assert_eq!(left.to_string(), "(bvult (_ bv3 8) x)");
}

#[test]
fn lowering_uses_stable_inline_uf_argument_identity() {
    let input = SmtExpr::uf(
        "predicate",
        vec![
            SmtExpr::var("x", 8).bvugt(SmtExpr::bv_const(3, 8)),
            SmtExpr::var("y", 8).bvule(SmtExpr::bv_const(7, 8)),
        ],
        crate::smt::SmtSort::Bool,
    );
    let lowered = lower_derived_operators(&input).expect("UF arguments lower");
    assert_eq!(
        lowered.to_string(),
        "(predicate (bvult (_ bv3 8) x) (not (bvult (_ bv7 8) y)))"
    );
    let SmtExpr::UF {
        name,
        args,
        ret_sort,
    } = lowered
    else {
        panic!("UF changed")
    };
    assert_eq!(name, "predicate");
    assert_eq!(args.len(), 2);
    assert_eq!(ret_sort, crate::smt::SmtSort::Bool);
}

/// Every proof-database obligation that mentions a derived operator lowers to
/// a formula with none, and with the original's value on sampled inputs.
#[test]
fn every_database_obligation_lowers_to_an_equivalent_formula() {
    // The database is built deep; give it the stack its own tests use.
    let run = || {
        let db = crate::proof_database::ProofDatabase::new();
        let mut state = 0x243f_6a88_85a3_08d3_u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let (mut lowered_count, mut checked) = (0_usize, 0_usize);
        for proof in db.all() {
            let ob = &proof.obligation;
            if !ob.fp_inputs.is_empty() {
                continue;
            }
            let formula = crate::ay_bridge::expand_bounded_quantifiers(&ob.negated_equivalence());
            let Some(lowered) = lower_derived_operators(&formula) else {
                continue;
            };
            assert!(!mentions_derived(&lowered), "{}", ob.name);
            lowered_count += 1;
            for point in 0..16_u64 {
                let mut env = EvalEnv::default();
                for (name, width) in &ob.inputs {
                    let mask = if *width >= 64 {
                        u64::MAX
                    } else {
                        (1_u64 << width) - 1
                    };
                    let value = if point % 2 == 0 { next() % 5 } else { next() };
                    env.insert(name.clone(), value & mask);
                }
                let (Some(original), Some(image)) = (eval(&formula, &env), eval(&lowered, &env))
                else {
                    continue;
                };
                assert_eq!(original, image, "{} at {env:?}", ob.name);
                checked += 1;
            }
        }
        assert!(
            lowered_count >= 20,
            "only {lowered_count} obligations mention a derived operator"
        );
        assert!(
            checked >= lowered_count * 4,
            "only {checked} points checked"
        );
    };
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(run)
        .expect("test thread")
        .join()
        .expect("the database check panicked");
}

/// Above 64 bits the complement is `(bvsub (bvneg x) 1)`: a 128-bit
/// `bvashr` keeps its value on sampled operands and amounts, overshift
/// included.
#[test]
fn a_wide_arithmetic_shift_agrees_with_its_definition() {
    // Environments hold 64-bit values: the operand is `(concat hi lo)`, so
    // its sign bit — the half the complement spelling serves — is exercised.
    let a = SmtExpr::Concat {
        hi: Arc::new(SmtExpr::var("hi", 64)),
        lo: Arc::new(SmtExpr::var("lo", 64)),
        width: 128,
    };
    let b = SmtExpr::ZeroExtend {
        operand: Arc::new(SmtExpr::var("b", 64)),
        extra_bits: 64,
        width: 128,
    };
    let original = SmtExpr::BvAshr {
        lhs: Arc::new(a),
        rhs: Arc::new(b),
        width: 128,
    };
    let lowered = lower_derived_operators(&original).expect("bvashr lowers");
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    // Deterministic sign, limb and overshift boundaries, with an independent
    // arithmetic oracle. None==None or skipped evaluation cannot pass a row.
    for hi in [0, (1_u64 << 63) - 1, 1_u64 << 63, u64::MAX] {
        for lo in [0, u64::MAX] {
            for amount in [0, 1, 63, 64, 127, 128, 129, u64::MAX] {
                let mut env = EvalEnv::default();
                env.insert("hi".into(), hi);
                env.insert("lo".into(), lo);
                env.insert("b".into(), amount);
                let signed = (((hi as u128) << 64) | lo as u128) as i128;
                let expected = if amount >= 128 {
                    if signed < 0 { u128::MAX } else { 0 }
                } else {
                    (signed >> amount) as u128
                };
                let expected = EvalResult::Bv128(expected);
                assert_eq!(
                    original.try_eval(&env).expect("boundary original"),
                    expected,
                    "{env:?}"
                );
                assert_eq!(
                    lowered.try_eval(&env).expect("boundary definition"),
                    expected,
                    "{env:?}"
                );
            }
        }
    }
    for _ in 0..200 {
        let mut env = EvalEnv::default();
        env.insert("hi".to_string(), next());
        env.insert("lo".to_string(), next());
        env.insert("b".to_string(), next() % 140);
        let expected = original.try_eval(&env).expect("sample original evaluates");
        let actual = lowered.try_eval(&env).expect("sample definition evaluates");
        assert_eq!(expected, actual, "at {env:?}");
    }
}
