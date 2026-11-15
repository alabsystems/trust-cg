// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Classification and serialization controls only; no solver or proof credit.

use super::*;

fn array(index: SmtSort, element: SmtSort) -> SmtSort {
    SmtSort::Array(Box::new(index), Box::new(element))
}

fn sort_cases() -> Vec<(SmtSort, &'static str)> {
    vec![
        (SmtSort::Bool, "QF_BV"),
        (SmtSort::BitVec(64), "QF_BV"),
        (SmtSort::bv_array(64, 8), "QF_ABV"),
        (SmtSort::fp64(), "QF_BVFP"),
        (
            array(
                SmtSort::BitVec(64),
                array(SmtSort::BitVec(8), SmtSort::fp32()),
            ),
            "QF_ABVFP",
        ),
        (
            array(array(SmtSort::fp32(), SmtSort::BitVec(8)), SmtSort::Bool),
            "QF_ABVFP",
        ),
    ]
}

fn obligation(body: SmtExpr) -> ProofObligation {
    ProofObligation {
        name: "logic sort census".into(),
        trust_ir_expr: SmtExpr::bool_const(true),
        aarch64_expr: body,
        inputs: Vec::new(),
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: None,
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    }
}

fn config() -> AYConfig {
    AYConfig {
        solver: None,
        timeout_ms: DEFAULT_AY_TIMEOUT_MS,
        produce_models: true,
    }
}

#[test]
fn nullary_applications_and_declarations_keep_all_sort_features_without_uf() {
    for (sort, expected) in sort_cases() {
        for expression in [
            SmtExpr::uf("constant", Vec::new(), sort.clone()),
            SmtExpr::uf_decl("constant", Vec::new(), sort.clone()),
        ] {
            let features = collect_logic_features(&expression);
            assert!(!features.has_uf, "{expression:?}");
            assert!(!features.has_quantifier);
            assert_eq!(infer_logic(&expression), expected, "{expression:?}");
        }
    }
}

#[test]
fn nonnullary_applications_and_declarations_keep_result_only_theories() {
    for (sort, nullary_logic) in sort_cases() {
        let expected = if nullary_logic == "QF_BV" {
            "QF_UFBV"
        } else {
            "ALL"
        };
        for expression in [
            SmtExpr::uf("function", vec![SmtExpr::var("x", 64)], sort.clone()),
            SmtExpr::uf_decl("function", vec![SmtSort::BitVec(64)], sort),
        ] {
            assert!(collect_logic_features(&expression).has_uf);
            assert_eq!(infer_logic(&expression), expected, "{expression:?}");
        }
    }
}

#[test]
fn function_argument_theories_are_retained_for_applications_and_declarations() {
    for (sort, nullary_logic) in sort_cases() {
        let expected = if nullary_logic == "QF_BV" {
            "QF_UFBV"
        } else {
            "ALL"
        };
        for expression in [
            SmtExpr::uf(
                "function",
                vec![SmtExpr::uf("argument", Vec::new(), sort.clone())],
                SmtSort::Bool,
            ),
            SmtExpr::uf_decl("function", vec![sort], SmtSort::Bool),
        ] {
            assert_eq!(infer_logic(&expression), expected, "{expression:?}");
        }
    }
}

#[test]
fn constant_array_index_sorts_contribute_without_relaxing_constructor_validation() {
    for index_sort in [SmtSort::fp32(), array(SmtSort::BitVec(8), SmtSort::fp64())] {
        assert!(SmtExpr::try_const_array(index_sort.clone(), SmtExpr::bv_const(0, 8)).is_err());
        // The public enum permits a raw node even though the checked builder
        // refuses it. Census must not hide its FP theory; it grants no validity.
        let expression = SmtExpr::ConstArray {
            index_sort,
            value: Arc::new(SmtExpr::bv_const(0, 8)),
        };
        assert_eq!(infer_logic(&expression), "QF_ABVFP");
        assert!(!collect_logic_features(&expression).has_uf);
    }
    let expression = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
    assert_eq!(infer_logic(&expression), "QF_ABV");
}

#[test]
fn sibling_order_never_erases_uf_array_or_fp_features() {
    let constant = SmtExpr::uf("constant", Vec::new(), SmtSort::Bool);
    let function = SmtExpr::uf("function", vec![SmtExpr::var("x", 64)], SmtSort::Bool);
    let array_value = SmtExpr::uf("memory", Vec::new(), SmtSort::bv_array(64, 8));
    let fp_value = SmtExpr::uf("floating", Vec::new(), SmtSort::fp64());
    for (body, expected) in [
        (function.clone(), "QF_UFBV"),
        (array_value.clone().eq_expr(array_value), "QF_ABV"),
        (fp_value.clone().eq_expr(fp_value), "QF_BVFP"),
        (
            SmtExpr::uf_decl("declared", vec![SmtSort::BitVec(64)], SmtSort::Bool),
            "QF_UFBV",
        ),
    ] {
        for tail in [
            constant.clone(),
            SmtExpr::uf_decl("nullary", Vec::new(), SmtSort::Bool),
        ] {
            assert_eq!(infer_logic(&body.clone().and_expr(tail.clone())), expected);
            assert_eq!(infer_logic(&tail.and_expr(body.clone())), expected);
        }
    }
    let memory = SmtExpr::uf("memory", Vec::new(), SmtSort::bv_array(64, 8));
    let read = SmtExpr::select(memory, SmtExpr::var("address", 64));
    let mixed = function.and_expr(read.eq_expr(SmtExpr::bv_const(0, 8)));
    assert_eq!(infer_logic(&mixed), "ALL");
}

#[test]
fn memory_load_remains_a_genuine_uninterpreted_function() {
    let load = SmtExpr::mem_load(SmtExpr::var("address", 64), 8, false, 64);
    assert!(collect_logic_features(&load).has_uf);
    assert_eq!(infer_logic(&load), "QF_UFBV");
}

#[test]
fn quantifier_classification_tracks_emitted_quantifiers_without_losing_sorts() {
    let memory = SmtExpr::uf("memory", Vec::new(), SmtSort::bv_array(64, 8));
    let body = SmtExpr::select(memory, SmtExpr::var("i", 64)).eq_expr(SmtExpr::bv_const(0, 8));
    for upper in [SmtExpr::bv_const(2, 64), SmtExpr::var("end", 64)] {
        let raw = SmtExpr::forall("i", 64, SmtExpr::bv_const(0, 64), upper, body.clone());
        assert_eq!(infer_logic(&raw), "ABV");
        assert!(has_quantifiers(&raw));
        let emitted = expand_bounded_quantifiers(&raw);
        let expected = if has_quantifiers(&emitted) {
            "ABV"
        } else {
            "QF_ABV"
        };
        assert_eq!(infer_logic(&emitted), expected);
        assert_eq!(
            infer_obligation_logic_for_smt2(&obligation(raw.clone()), &raw, &emitted, &[]),
            expected,
        );
    }
}

#[test]
fn omitted_expression_theories_still_come_from_raw_formula_and_declarations() {
    let empty = SmtExpr::bool_const(false);
    let plain = obligation(empty.clone());
    for (sort, expected) in sort_cases() {
        let value = SmtExpr::uf("value", Vec::new(), sort.clone());
        let raw = value.clone().eq_expr(value);
        assert_eq!(
            infer_obligation_logic_for_smt2(&plain, &raw, &empty, &[]),
            expected
        );
        assert_eq!(
            infer_obligation_logic_for_smt2(&plain, &empty, &empty, &[("extra".into(), sort)]),
            expected,
        );
    }
    let mut floating = plain;
    floating.fp_inputs.push(("fp_input".into(), 11, 53));
    assert_eq!(
        infer_obligation_logic_for_smt2(&floating, &empty, &empty, &[]),
        "QF_BVFP"
    );
    assert_eq!(
        infer_obligation_logic_for_smt2(
            &floating,
            &empty,
            &empty,
            &[("memory".into(), SmtSort::bv_array(64, 8))],
        ),
        "QF_ABVFP",
    );
}

#[test]
fn raw_captured_saved_pair_query_changes_only_its_logic_header() {
    use crate::aarch64_pair_memory::check_pair_encoding;
    use crate::aarch64_saved_pair::conditional_saved_pair;
    use sha2::{Digest, Sha256};
    use trust_cg_ir::regs::PReg;
    use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, SpecialReg};

    let instruction = |opcode, offset| {
        MachInst::new(
            opcode,
            vec![
                MachOperand::PReg(PReg::new(26)),
                MachOperand::PReg(PReg::new(25)),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(offset),
            ],
        )
    };
    let save = instruction(AArch64Opcode::StpPreIndex, -80);
    let restore = instruction(AArch64Opcode::LdpPostIndex, 80);
    let owner = conditional_saved_pair(
        check_pair_encoding(&save, &0xa9bb_67fa_u32.to_le_bytes()).unwrap(),
        check_pair_encoding(&restore, &0xa8c5_67fa_u32.to_le_bytes()).unwrap(),
    )
    .unwrap();
    let query = generate_smt2_query_raw(owner.obligation(), &config());
    assert_eq!(query.matches("(set-logic QF_ABV)").count(), 1);
    assert_eq!(query.matches("(store ").count(), 256);
    assert_eq!(query.matches("(select ").count(), 48);
    assert!(!query.contains("as const"));
    assert_eq!(query.len(), 33_070);
    // The historical right-spine query (OD-134) is reconstructed, not
    // relabelled: it still reproduces both retained pre-change digests, so the
    // logic-header fix changed only that header.
    let legacy = legacy_right_spine_query_for_test(owner.obligation(), &config());
    assert_eq!(legacy.matches("(set-logic QF_ABV)").count(), 1);
    assert_eq!(legacy.len(), 33_070);
    let before = legacy.replacen("(set-logic QF_ABV)", "(set-logic ALL)", 1);
    assert_eq!(before.len(), 33_067);
    assert_eq!(
        format!("{:x}", Sha256::digest(before.as_bytes())),
        "fedb17b798d57c00eec598ece3af26b5fd9f492046f77285921b2af7779c66a1",
    );
    assert_eq!(
        format!("{:x}", Sha256::digest(legacy.as_bytes())),
        "b49fc64db62fd3c11b9f81af946182ebef02a7ffc2ce7bad2564370ba1612658",
    );
    // The canonical query reassociates the conjunction and nothing else: the
    // same declarations, the same number of `and` nodes, and the same leaves
    // in the same written order once the connectives are erased.
    let prelude = |script: &str| {
        script
            .split_once("\n(assert ")
            .expect("one assertion")
            .0
            .to_owned()
    };
    let leaves = |script: &str| {
        script
            .replace("(and ", " ")
            .replace(')', " ")
            .split_whitespace()
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    assert_ne!(query, legacy);
    assert_eq!(prelude(&query), prelude(&legacy));
    assert_eq!(
        query.matches("(and ").count(),
        legacy.matches("(and ").count()
    );
    assert_eq!(leaves(&query), leaves(&legacy));
    // Erasing every `(and ` cannot see a conjunction re-associated INSIDE an
    // opaque leaf (this obligation's machine leaf holds two). So each leaf,
    // printed on its own, must appear verbatim and in OD-134's written order
    // (reversed preconditions, then the negated equality) in both queries.
    let obligation = owner.obligation();
    let leaf_texts: Vec<String> = obligation
        .preconditions
        .iter()
        .rev()
        .cloned()
        .chain(std::iter::once(
            obligation
                .trust_ir_expr
                .clone()
                .eq_expr(obligation.aarch64_expr.clone())
                .not_expr(),
        ))
        .map(|leaf| quantifier_expanded_view(&leaf).to_string())
        .collect();
    assert_eq!(leaf_texts.len(), 6);
    for script in [&query, &legacy] {
        let (_, assertion) = script.split_once("\n(assert ").expect("one assertion");
        let mut at = 0;
        for leaf in &leaf_texts {
            let offset = assertion[at..]
                .find(leaf.as_str())
                .expect("every leaf verbatim, in written order");
            at += offset + leaf.len();
        }
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(query.as_bytes())),
        "a89ff1b269d539688ddf5d97a2b0fd1738f3e753b4e16ab0a2fdd9ffb7314007",
        "reviewed midpoint-conjunction-v2 original query identity"
    );
}
