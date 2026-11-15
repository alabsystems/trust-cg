// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact print-view/storage controls, not a proof or semantic simplifier.
//! No new SMT parser is introduced. Each private binding is compared against
//! the original constructor through the existing AST rewrite and Display APIs.

use super::*;
use crate::memory_proofs::{encode_load_le, memory_sort};
use crate::smt::{SmtExpr as E, SmtSort};
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use crate::source_bound_frame::bind_read_only_source;
use std::convert::Infallible;
use std::sync::Arc;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use trust_cg_codegen::CoreHostJitTarget;

fn boolean_word() -> E {
    E::var("x", 64)
        .bvadd(E::bv_const(1, 64))
        .eq_expr(E::var("y", 64))
}

fn inspect_views(formula: &E, script: &str) {
    let plan = plan(formula, script).expect("exact private print plan");
    for (index, binding) in plan.bindings.iter().enumerate() {
        fn replace(node: &E, earlier: &[Binding<'_>]) -> E {
            if let Some(binding) = earlier.iter().find(|b| std::ptr::eq(node, b.original)) {
                return E::uf(binding.name.clone(), vec![], binding.sort.clone());
            }
            // Preserve ORIGINAL inline UF argument slots in this independent
            // expansion check, rather than mapping temporary Arc wrappers.
            match node {
                E::UF {
                    name,
                    args,
                    ret_sort,
                } => E::UF {
                    name: name.clone(),
                    args: args.iter().map(|arg| replace(arg, earlier)).collect(),
                    ret_sort: ret_sort.clone(),
                },
                node => node
                    .try_map_children::<Infallible>(&mut |child| {
                        Ok(Arc::new(replace(child, earlier)))
                    })
                    .unwrap(),
            }
        }
        let expected = replace(binding.original, &plan.bindings[..index]);
        assert_eq!(
            binding.definition,
            expected.to_string(),
            "only earlier exact node aliases replace children"
        );
        assert_eq!(binding.view.to_string(), expected.to_string());
        assert_eq!(binding.view, expected);
        let sort = match &expected {
            E::Ite { then_expr, .. } => then_expr.sort(),
            _ => expected.sort(),
        };
        assert_eq!(binding.sort, sort);
        binding.view.any_node(|node| {
            if let E::UF { name, args, .. } = node
                && args.is_empty()
                && let Some(dependency) = plan.bindings[..index].iter().find(|b| b.name == *name)
            {
                assert!(
                    dependency.level < binding.level,
                    "even dependencies through inline nodes need an earlier LET level"
                );
            }
            false
        });
        assert!(!script.contains(&binding.name));
    }
    let root = plan.bindings.last().expect("compound formula is bound");
    assert!(std::ptr::eq(root.original, formula));
    assert_eq!(plan.root.to_string(), root.name);
}

#[test]
fn leaf_formulas_have_no_compact_bindings_and_compounds_keep_literal_false() {
    assert!(compact_formula(&E::BoolConst(false), "").unwrap().is_none());
    assert!(compact_formula(&E::BoolConst(true), "").unwrap().is_none());
    let formula = E::BoolConst(false).and_expr(E::BoolConst(true));
    let printed = compact_formula(&formula, "").unwrap().unwrap();
    assert!(
        printed.text.contains("(and false true)"),
        "printer never folds a Boolean constructor"
    );
    assert!(printed.text.contains("(let ((tcg!raw0_0 "));
    assert_eq!(printed.bindings, 1);
    assert_eq!(printed.output_bytes, printed.text.len());
    inspect_views(&formula, "");
}

#[test]
fn small_shared_dag_has_a_deterministic_exact_golden_let_view() {
    let shared = Arc::new(E::var("x", 64).bvadd(E::bv_const(1, 64)));
    let formula = E::Eq {
        lhs: shared.clone(),
        rhs: shared,
    };
    let printed = compact_formula(&formula, "").unwrap().unwrap();
    assert_eq!(printed.bindings, 2);
    assert_eq!(printed.levels, 2);
    assert_eq!(printed.text.matches("(bvadd ").count(), 1);
    assert!(printed.text.contains("(tcg!raw0_0 (bvadd x (_ bv1 64)))"));
    assert!(
        printed
            .text
            .contains("(tcg!raw0_1 (= tcg!raw0_0 tcg!raw0_0))")
    );
    assert!(printed.text.trim_end().ends_with("tcg!raw0_1))"));
    for _ in 0..4 {
        let again = compact_formula(&formula, "").unwrap().unwrap();
        assert_eq!(again.text, printed.text);
        assert_eq!(again.distinct_nodes, printed.distinct_nodes);
        assert_eq!(again.edges, printed.edges);
    }
    inspect_views(&formula, "");
}

#[test]
fn full_word_statuses_and_constant_untaken_arms_are_not_folded_or_narrowed() {
    let statuses = [0, 1u64 << 32, (3u64 << 32) | 1, (3u64 << 32) | 4, u64::MAX];
    let mut result = E::bv_const(statuses[0], 64);
    for status in statuses.into_iter().skip(1) {
        result = E::ite(E::BoolConst(false), E::bv_const(status, 64), result);
    }
    let formula = result.eq_expr(E::var("full_status", 64));
    let printed = compact_formula(&formula, "").unwrap().unwrap();
    for status in statuses {
        assert!(
            printed.text.contains(&format!("(_ bv{status} 64)")),
            "retain full status {status}, even in an untaken branch"
        );
    }
    assert_eq!(printed.text.matches("(ite false ").count(), 4);
    inspect_views(&formula, "");
}

#[test]
fn one_arbitrary_array_preserves_aliasable_and_memory_dependent_addresses() {
    let memory = E::uf("entry_memory", vec![], memory_sort());
    let x = E::var("ctx", 64);
    let y = E::var("parent", 64);
    let pool = encode_load_le(&memory, &x.clone().bvadd(E::bv_const(8, 64)), 8);
    let nested = encode_load_le(&memory, &pool.bvadd(E::bv_const(24, 64)), 8);
    let direct = encode_load_le(&memory, &y, 8);
    let formula = x
        .eq_expr(E::var("parent", 64))
        .not_expr()
        .or_expr(nested.eq_expr(direct));
    let printed = compact_formula(&formula, "").unwrap().unwrap();
    assert!(printed.text.contains("entry_memory"));
    assert!(printed.text.contains("ctx"));
    assert!(printed.text.contains("parent"));
    assert_eq!(printed.text.matches("(select ").count(), 24);
    assert!(
        !printed.text.contains("as const"),
        "arbitrary memory cannot become uniform"
    );
    assert!(
        !printed.text.contains("distinct"),
        "no disjointness premise may be invented"
    );
    inspect_views(&formula, "");
}

#[test]
fn boolean_and_array_ite_sorts_preserve_all_arms_and_store_select_constructors() {
    let condition = E::uf("condition", vec![], SmtSort::Bool);
    let boolean = E::ite(condition.clone(), E::BoolConst(true), E::BoolConst(false))
        .eq_expr(E::uf("expected_boolean", vec![], SmtSort::Bool));
    let printed = compact_formula(&boolean, "").unwrap().unwrap();
    assert!(printed.text.contains("(ite condition true false)"));
    inspect_views(&boolean, "");

    let left = E::uf("left_memory", vec![], memory_sort());
    let right = E::uf("right_memory", vec![], memory_sort());
    let array = E::ite(condition, left, right);
    let address = E::var("address", 64);
    let stored = E::Store {
        array: Arc::new(array),
        index: Arc::new(address.clone()),
        value: Arc::new(E::bv_const(9, 8)),
    };
    let read = E::Select {
        array: Arc::new(stored),
        index: Arc::new(address),
    }
    .eq_expr(E::bv_const(9, 8));
    let printed = compact_formula(&read, "").unwrap().unwrap();
    assert!(
        printed
            .text
            .contains("(ite condition left_memory right_memory)")
    );
    assert!(printed.text.contains("(store "));
    assert!(
        printed.text.contains("(select "),
        "printer does not apply read-over-write simplification"
    );
    inspect_views(&read, "");
}

#[test]
fn aliases_are_fresh_against_quoted_free_uf_and_original_script_names() {
    let formula = E::uf(
        "|tcg!raw1_quoted function|",
        vec![E::var("tcg!raw2_free", 64)],
        SmtSort::Bool,
    )
    .and_expr(E::var("|quoted source word|", 64).eq_expr(E::bv_const(0, 64)));
    let script = "; tcg!raw0_ appears even in a comment\n(declare-fun unused () Bool)";
    let plan = plan(&formula, script).unwrap();
    assert!(
        plan.bindings
            .iter()
            .all(|binding| binding.name.starts_with("tcg!raw3_"))
    );
    let printed = compact_formula(&formula, script).unwrap().unwrap();
    assert!(printed.text.contains("|tcg!raw1_quoted function|"));
    assert!(printed.text.contains("tcg!raw2_free"));
    assert!(printed.text.contains("|quoted source word|"));
    inspect_views(&formula, script);
}

#[test]
fn prefix_search_is_bounded_and_never_accepts_capture() {
    let script = (0..MAX_PREFIX_ATTEMPTS)
        .map(|i| format!("tcg!raw{i}_"))
        .collect::<Vec<_>>()
        .join(" ");
    assert!(matches!(
        compact_formula(&boolean_word(), &script),
        Err(CompactPrintRefusal::Budget(_))
    ));
}

#[test]
fn quantified_and_implicit_memory_or_poison_forms_fail_closed() {
    let x = E::var("x", 64);
    let quantified = [
        E::forall(
            "x",
            64,
            E::bv_const(0, 64),
            E::bv_const(4, 64),
            x.clone().eq_expr(E::bv_const(0, 64)),
        ),
        E::exists(
            "x",
            64,
            E::bv_const(0, 64),
            E::bv_const(4, 64),
            x.clone().eq_expr(E::bv_const(0, 64)),
        ),
        E::uf_decl("declaration_only", vec![SmtSort::BitVec(64)], SmtSort::Bool),
        x.clone()
            .trap_if_zero(x.clone())
            .eq_expr(E::bv_const(0, 64)),
        E::MemLoad {
            addr: Arc::new(x),
            load_bits: 64,
            signed: false,
            result_width: 64,
        }
        .eq_expr(E::bv_const(0, 64)),
    ];
    for formula in quantified {
        assert!(matches!(
            compact_formula(&formula, ""),
            Err(CompactPrintRefusal::Unsupported(_))
        ));
    }
}

#[test]
fn malformed_sort_width_and_shape_are_refusals_not_panics_or_partial_output() {
    let malformed = [
        E::Eq {
            lhs: Arc::new(E::var("x", 32)),
            rhs: Arc::new(E::var("y", 64)),
        },
        E::And {
            lhs: Arc::new(E::var("x", 64)),
            rhs: Arc::new(E::BoolConst(true)),
        },
        E::Select {
            array: Arc::new(E::var("not_an_array", 64)),
            index: Arc::new(E::var("index", 64)),
        }
        .eq_expr(E::bv_const(0, 8)),
        E::var("zero_width", 0).eq_expr(E::var("other_zero_width", 0)),
    ];
    for formula in malformed {
        assert!(matches!(
            compact_formula(&formula, ""),
            Err(CompactPrintRefusal::Sort(_))
        ));
    }
    let too_wide = E::var("wide", MAX_BIT_WIDTH + 1).eq_expr(E::var("wide2", MAX_BIT_WIDTH + 1));
    assert!(matches!(
        compact_formula(&too_wide, ""),
        Err(CompactPrintRefusal::Budget(_)) | Err(CompactPrintRefusal::Sort(_))
    ));
}

fn diamond(depth: usize) -> E {
    let mut node = Arc::new(E::var("x", 64));
    for _ in 0..depth {
        node = Arc::new(E::BvAdd {
            lhs: node.clone(),
            rhs: node,
            width: 64,
        });
    }
    E::Eq {
        lhs: node.clone(),
        rhs: node,
    }
}

#[test]
fn exponentially_shared_formula_has_bounded_linear_print_storage() {
    let formula = diamond(40);
    let printed = compact_formula(&formula, "").unwrap().unwrap();
    assert_eq!(printed.distinct_nodes, 42);
    assert_eq!(printed.bindings, 41);
    assert!(printed.edges <= 82);
    assert_eq!(printed.text.matches("(bvadd ").count(), 40);
    assert!(
        printed.output_bytes < 16_384,
        "no exponentially expanded tree text"
    );
    inspect_views(&formula, "");
}

#[test]
fn depth_node_arity_symbol_and_script_limits_are_bounded_before_output() {
    let mut deep = E::BoolConst(false);
    for _ in 0..=MAX_DEPTH {
        deep = deep.not_expr();
    }
    assert!(matches!(
        compact_formula(&deep, ""),
        Err(CompactPrintRefusal::Budget(_))
    ));
    let mut layer: Vec<_> = (0..MAX_NODES)
        .map(|i| E::uf(format!("leaf_{i}"), vec![], SmtSort::Bool))
        .collect();
    while layer.len() > 1 {
        layer = layer
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| pair[0].clone().and_expr(pair[1].clone()))
            .collect();
    }
    assert!(matches!(
        compact_formula(&layer[0], ""),
        Err(CompactPrintRefusal::Budget(_))
    ));
    let arity = E::uf(
        "too_many_arguments",
        vec![E::bv_const(0, 64); MAX_ARITY + 1],
        SmtSort::Bool,
    );
    assert!(matches!(
        compact_formula(&arity, ""),
        Err(CompactPrintRefusal::Budget(_))
    ));
    let long = E::var("x".repeat(MAX_SYMBOL_BYTES + 1), 64).eq_expr(E::var("y", 64));
    assert!(matches!(
        compact_formula(&long, ""),
        Err(CompactPrintRefusal::Budget(_))
    ));
    assert!(matches!(
        compact_formula(&E::var("", 64).eq_expr(E::var("y", 64)), ""),
        Err(CompactPrintRefusal::Budget("symbol bytes"))
    ));
    assert!(matches!(
        compact_formula(&boolean_word(), &" ".repeat(MAX_SCRIPT_BYTES + 1)),
        Err(CompactPrintRefusal::Budget(_))
    ));
}

fn combine(mut values: Vec<E>) -> E {
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
fn aggregate_payload_output_and_nested_sort_limits_are_independent_caps() {
    let payload = combine(
        (0..512)
            .map(|i| {
                let label = format!("v{i}_");
                let name = format!("{label}{}", "x".repeat(MAX_SYMBOL_BYTES - label.len()));
                E::var(name, 64).eq_expr(E::bv_const(i, 64))
            })
            .collect(),
    );
    assert!(matches!(
        compact_formula(&payload, ""),
        Err(CompactPrintRefusal::Budget("payload bytes"))
    ));

    // ONE shared long leaf stays within payload/node caps but appears in
    // enough shallow definitions to exceed the separate output-text limit.
    let long = Arc::new(E::var("x".repeat(MAX_SYMBOL_BYTES), 64));
    let output = combine(
        (0..1024)
            .map(|i| E::Eq {
                lhs: long.clone(),
                rhs: Arc::new(E::bv_const(i, 64)),
            })
            .collect(),
    );
    assert!(matches!(
        compact_formula(&output, ""),
        Err(CompactPrintRefusal::Budget("output bytes"))
    ));

    let mut sort = SmtSort::BitVec(8);
    for _ in 0..MAX_SORT_DEPTH {
        sort = SmtSort::Array(Box::new(SmtSort::BitVec(64)), Box::new(sort));
    }
    let nested = E::uf("nested_sort", vec![], sort.clone()).eq_expr(E::uf(
        "other_nested_sort",
        vec![],
        sort,
    ));
    assert!(matches!(
        compact_formula(&nested, ""),
        Err(CompactPrintRefusal::Budget("sort shape"))
    ));
}

#[test]
fn initial_fp_profile_is_explicitly_unsupported_without_lossy_printing() {
    let fp = E::uf("float_input", vec![], SmtSort::fp64());
    assert!(matches!(
        compact_formula(&fp.clone().eq_expr(fp), ""),
        Err(CompactPrintRefusal::Unsupported(_))
    ));
}

#[test]
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn original_ty_core_lir_raw_formula_preserves_geometry_memory_status_and_load_demands() {
    let capture: serde_json::Value = serde_json::from_str(include_str!(
        "../tests/fixtures/ty_original_read_only_predicate.json"
    ))
    .unwrap();
    assert_eq!(capture["selection"]["unit_key"], "inv:Second");
    let original: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    assert!(original.target_info.is_none());
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
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    assert_eq!(source.read_requirements().len(), 3);
    assert_eq!(source.load_obligations().len(), 3);
    let raw = crate::ay_bridge::generate_smt2_query_raw(
        source.return_obligation(),
        &crate::ay_bridge::AYConfig::default(),
    );
    let formula = source.return_obligation().negated_equivalence();
    let full_tree_bytes = formula.to_string().len();
    let printed = compact_formula(&formula, &raw).unwrap().unwrap();
    assert!(
        printed.output_bytes < full_tree_bytes,
        "actual source DAG sharing must reduce storage without changing constructors"
    );
    assert!(printed.text.contains("entry_memory"));
    assert!(raw.contains("(declare-fun entry_memory () (Array (_ BitVec 64) (_ BitVec 8)))"));
    for status in [0, 1u64 << 32, (3u64 << 32) | 1, (3u64 << 32) | 4] {
        assert!(
            printed.text.contains(&format!("(_ bv{status} 64)")),
            "retain original full status {status}"
        );
    }
    inspect_views(&formula, &raw);
    for geometry in &source.return_obligation().preconditions {
        let plan = plan(&formula, &raw).unwrap();
        assert!(
            plan.bindings
                .iter()
                .any(|binding| binding.original == geometry),
            "every original geometry predicate remains reachable in the exact raw formula"
        );
    }
    for obligation in source.load_obligations() {
        let demand = obligation.negated_equivalence();
        let script = crate::ay_bridge::generate_smt2_query_raw(
            obligation,
            &crate::ay_bridge::AYConfig::default(),
        );
        let printed = compact_formula(&demand, &script).unwrap().unwrap();
        assert!(printed.bindings > 0);
        inspect_views(&demand, &script);
    }
    println!(
        "TY_ORIGINAL_COMPACT_PRINT source=inv:Second function=60004 tree_bytes={full_tree_bytes} compact_bytes={} nodes={} edges={} bindings={} source_geometry={} load_demands=3 proof_credit=false",
        printed.output_bytes,
        printed.distinct_nodes,
        printed.edges,
        printed.bindings,
        source.return_obligation().preconditions.len()
    );
}

#[test]
fn exact_print_match_requires_every_byte_and_retains_existing_admission() {
    let expression = SmtExpr::var("source", 8).eq_expr(SmtExpr::bv_const(7, 8));
    let expected = expression.to_string();
    assert!(prints_exactly(&expression, &expected));
    assert!(!prints_exactly(&expression, &format!("{expected}x")));
    assert!(!prints_exactly(
        &expression,
        &expected[..expected.len() - 1]
    ));
    assert!(!prints_exactly(
        &expression,
        &expected.replace("source", "other")
    ));
    assert!(!prints_exactly(
        &expression,
        &"x".repeat(MAX_OUTPUT_BYTES + 1)
    ));
}

#[test]
fn single_use_word_spines_inline_without_losing_nested_binding_dependencies() {
    let condition = boolean_word();
    let value = E::ite(condition, E::var("a", 8), E::var("b", 8))
        .bvadd(E::bv_const(3, 8))
        .bvadd(E::bv_const(4, 8));
    let formula = value.eq_expr(E::var("expected", 8));
    let printed = compact_formula(&formula, "").unwrap().unwrap();
    assert_eq!(
        printed.bindings, 2,
        "only the Bool condition and root need bindings"
    );
    assert_eq!(
        printed.levels, 2,
        "inline spines retain their condition dependency"
    );
    assert_eq!(printed.text.matches("(bvadd ").count(), 3);
    inspect_views(&formula, "");
}
