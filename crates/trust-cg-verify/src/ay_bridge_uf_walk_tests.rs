// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
use std::collections::HashSet;

// Frozen pre-change reference routines from 3d7164b2. Keeping the exhaustive
// legacy collector, rather than another identity walker, makes declaration
// order/signature and complete query-byte compatibility independently testable.
fn legacy_collect_uf_declarations(
    expr: &SmtExpr,
    decls: &mut Vec<(String, Vec<SmtSort>, SmtSort)>,
) {
    match expr {
        SmtExpr::UF {
            name,
            args,
            ret_sort,
        } => {
            // Add declaration if not already present
            if !decls.iter().any(|(n, _, _)| n == name) {
                let arg_sorts: Vec<SmtSort> = args.iter().map(|a| a.sort()).collect();
                decls.push((name.clone(), arg_sorts, ret_sort.clone()));
            }
            // Recurse into arguments
            for arg in args {
                legacy_collect_uf_declarations(arg, decls);
            }
        }
        SmtExpr::UFDecl {
            name,
            arg_sorts,
            ret_sort,
        } => {
            if !decls.iter().any(|(n, _, _)| n == name) {
                decls.push((name.clone(), arg_sorts.clone(), ret_sort.clone()));
            }
        }
        // Binary operators
        SmtExpr::BvAdd { lhs, rhs, .. }
        | SmtExpr::BvSub { lhs, rhs, .. }
        | SmtExpr::BvMul { lhs, rhs, .. }
        | SmtExpr::BvSDiv { lhs, rhs, .. }
        | SmtExpr::BvUDiv { lhs, rhs, .. }
        | SmtExpr::BvURem { lhs, rhs, .. }
        | SmtExpr::BvAnd { lhs, rhs, .. }
        | SmtExpr::BvOr { lhs, rhs, .. }
        | SmtExpr::BvXor { lhs, rhs, .. }
        | SmtExpr::BvShl { lhs, rhs, .. }
        | SmtExpr::BvLshr { lhs, rhs, .. }
        | SmtExpr::BvAshr { lhs, rhs, .. }
        | SmtExpr::Eq { lhs, rhs }
        | SmtExpr::BvSlt { lhs, rhs, .. }
        | SmtExpr::BvSge { lhs, rhs, .. }
        | SmtExpr::BvSgt { lhs, rhs, .. }
        | SmtExpr::BvSle { lhs, rhs, .. }
        | SmtExpr::BvUlt { lhs, rhs, .. }
        | SmtExpr::BvUge { lhs, rhs, .. }
        | SmtExpr::BvUgt { lhs, rhs, .. }
        | SmtExpr::BvUle { lhs, rhs, .. }
        | SmtExpr::And { lhs, rhs }
        | SmtExpr::Or { lhs, rhs }
        | SmtExpr::FPAdd { lhs, rhs, .. }
        | SmtExpr::FPSub { lhs, rhs, .. }
        | SmtExpr::FPMul { lhs, rhs, .. }
        | SmtExpr::FPDiv { lhs, rhs, .. }
        | SmtExpr::FPEq { lhs, rhs }
        | SmtExpr::FPLt { lhs, rhs }
        | SmtExpr::FPGt { lhs, rhs }
        | SmtExpr::FPGe { lhs, rhs }
        | SmtExpr::FPLe { lhs, rhs } => {
            legacy_collect_uf_declarations(lhs, decls);
            legacy_collect_uf_declarations(rhs, decls);
        }
        // Unary operators
        SmtExpr::BvNeg { operand, .. }
        | SmtExpr::Not { operand }
        | SmtExpr::Extract { operand, .. }
        | SmtExpr::ZeroExtend { operand, .. }
        | SmtExpr::SignExtend { operand, .. }
        | SmtExpr::FPNeg { operand }
        | SmtExpr::FPAbs { operand }
        | SmtExpr::FPSqrt { operand, .. }
        | SmtExpr::FPRoundToIntegral { operand, .. }
        | SmtExpr::FPIsNaN { operand }
        | SmtExpr::FPIsInf { operand }
        | SmtExpr::FPIsZero { operand }
        | SmtExpr::FPIsNormal { operand }
        | SmtExpr::FPToSBv { operand, .. }
        | SmtExpr::FPToUBv { operand, .. }
        | SmtExpr::BvToFP { operand, .. }
        | SmtExpr::FPToFP { operand, .. }
        | SmtExpr::BvBitsToFP { operand, .. } => {
            legacy_collect_uf_declarations(operand, decls);
        }
        SmtExpr::Concat { hi, lo, .. } => {
            legacy_collect_uf_declarations(hi, decls);
            legacy_collect_uf_declarations(lo, decls);
        }
        SmtExpr::TrapIfZero { guard, value, .. } => {
            legacy_collect_uf_declarations(guard, decls);
            legacy_collect_uf_declarations(value, decls);
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            legacy_collect_uf_declarations(cond, decls);
            legacy_collect_uf_declarations(then_expr, decls);
            legacy_collect_uf_declarations(else_expr, decls);
        }
        SmtExpr::FPFma { a, b, c, .. } => {
            legacy_collect_uf_declarations(a, decls);
            legacy_collect_uf_declarations(b, decls);
            legacy_collect_uf_declarations(c, decls);
        }
        SmtExpr::Select { array, index } => {
            legacy_collect_uf_declarations(array, decls);
            legacy_collect_uf_declarations(index, decls);
        }
        SmtExpr::Store {
            array,
            index,
            value,
        } => {
            legacy_collect_uf_declarations(array, decls);
            legacy_collect_uf_declarations(index, decls);
            legacy_collect_uf_declarations(value, decls);
        }
        SmtExpr::ConstArray { value, .. } => {
            legacy_collect_uf_declarations(value, decls);
        }
        // A memory load is an uninterpreted function `mem_load_W_s : BV(addr) ->
        // BV(load_bits)` (one symbol per load width + signedness). Declare it so
        // the SMT-LIB query is well-formed; the surrounding sign/zero-extend to
        // result_width is emitted inline by `Display`. Same congruence the
        // evaluator's deterministic `mix` gives: equal addresses ⇒ equal loads.
        SmtExpr::MemLoad {
            addr,
            load_bits,
            signed,
            ..
        } => {
            let s = if *signed { "s" } else { "u" };
            let name = format!("mem_load_{load_bits}_{s}");
            if !decls.iter().any(|(n, _, _)| n == &name) {
                let addr_sort = SmtSort::BitVec(addr.try_bv_width().unwrap_or(64));
                decls.push((name, vec![addr_sort], SmtSort::BitVec(*load_bits)));
            }
            legacy_collect_uf_declarations(addr, decls);
        }
        SmtExpr::ForAll {
            lower, upper, body, ..
        }
        | SmtExpr::Exists {
            lower, upper, body, ..
        } => {
            legacy_collect_uf_declarations(lower, decls);
            legacy_collect_uf_declarations(upper, decls);
            legacy_collect_uf_declarations(body, decls);
        }
        // Leaves: no children to recurse into
        SmtExpr::Var { .. }
        | SmtExpr::BvConst { .. }
        | SmtExpr::BoolConst(_)
        | SmtExpr::FPConst { .. } => {}
    }
}

fn legacy_query_from_formula(
    obligation: &ProofObligation,
    config: &AYConfig,
    extra_decls: &[(String, SmtSort)],
    raw_formula: &SmtExpr,
    formula: &SmtExpr,
) -> String {
    let mut lines = Vec::new();

    // Solver options are start-mode commands in AY.  They MUST precede
    // `(set-logic ...)`; AY correctly rejects a late `:produce-models` option.
    if config.timeout_ms > 0 {
        // AY's SMT-LIB interface accepts :timeout in milliseconds.
        lines.push(format!("(set-option :timeout {})", config.timeout_ms));
    }
    if config.produce_models {
        lines.push("(set-option :produce-models true)".to_string());
    }

    // Logic declaration -- infer theories from both the emitted formula and
    // declarations. The emitted formula may be simplified to `false`, but the
    // SMT-LIB2 script still needs a logic that admits declared FP/array inputs.
    let logic = infer_obligation_logic_for_smt2(obligation, raw_formula, formula, extra_decls);
    lines.push(format!("(set-logic {})", logic));

    // Declare symbolic bitvector inputs
    for (name, width) in &obligation.inputs {
        lines.push(format!("(declare-const {} (_ BitVec {}))", name, width));
    }

    // Declare symbolic floating-point inputs
    for (name, eb, sb) in &obligation.fp_inputs {
        lines.push(format!(
            "(declare-const {} (_ FloatingPoint {} {}))",
            name, eb, sb
        ));
    }

    // Declare additional non-bitvector inputs (arrays, FP, etc.)
    for (name, sort) in extra_decls {
        lines.push(format!("(declare-const {} {})", name, sort_to_smt2(sort)));
    }

    // Scan the formula for uninterpreted function applications and emit
    // `(declare-fun ...)` for each unique function name found.
    let mut uf_decls = Vec::new();
    legacy_collect_uf_declarations(formula, &mut uf_decls);
    for (name, arg_sorts, ret_sort) in &uf_decls {
        let arg_sorts_str: Vec<String> = arg_sorts.iter().map(sort_to_smt2).collect();
        lines.push(format!(
            "(declare-fun {} ({}) {})",
            name,
            arg_sorts_str.join(" "),
            sort_to_smt2(ret_sort)
        ));
    }

    // Assert the negated equivalence (with quantifiers expanded where possible)
    lines.push(format!("(assert {})", formula));

    // Check satisfiability
    lines.push("(check-sat)".to_string());

    lines.push("(exit)".to_string());

    lines.join("\n")
}

fn declaration_pair(expr: &SmtExpr) -> Vec<(String, Vec<SmtSort>, SmtSort)> {
    let mut old = Vec::new();
    let mut new = Vec::new();
    legacy_collect_uf_declarations(expr, &mut old);
    collect_uf_declarations(expr, &mut new);
    assert_eq!(new, old);
    new
}

fn assert_query_bytes_unchanged(expr: SmtExpr) {
    let obligation = ProofObligation {
        name: "UF walk byte compatibility, not solver qualification".into(),
        trust_ir_expr: expr.clone(),
        aarch64_expr: expr,
        inputs: vec![("x".into(), 64), ("address".into(), 64)],
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: None,
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    };
    let raw = obligation.negated_equivalence();
    let formula = expand_bounded_quantifiers(&raw);
    declaration_pair(&formula);
    for (timeout_ms, produce_models) in [(0, false), (123, true)] {
        let config = AYConfig {
            solver: None,
            timeout_ms,
            produce_models,
        };
        assert_eq!(
            generate_smt2_query_raw(&obligation, &config),
            legacy_query_from_formula(&obligation, &config, &[], &raw, &formula)
        );
    }
}

fn memory_reads(stores: usize, reads: usize) -> SmtExpr {
    let mut memory = SmtExpr::uf("entry_memory", Vec::new(), memory_sort());
    let address = SmtExpr::var("address", 64);
    let value = SmtExpr::var("x", 64);
    for index in 0..stores {
        let offset = address
            .clone()
            .bvadd(SmtExpr::bv_const((index * 8) as u64, 64));
        memory = encode_store_le(&memory, &offset, &value, 8);
    }
    let mut formula = SmtExpr::bool_const(true);
    for index in 0..reads {
        let offset = address
            .clone()
            .bvadd(SmtExpr::bv_const((index * 8) as u64, 64));
        formula = formula.and_expr(encode_load_le(&memory, &offset, 8).eq_expr(value.clone()));
    }
    formula
}

fn tree_visits(expr: &SmtExpr) -> usize {
    let mut count = 1;
    expr.for_each_child(&mut |child| count += tree_visits(child));
    count
}

#[test]
fn uf_walk_shared_store_chains_have_linear_unique_visits() {
    for stores in [1, 2, 4, 8, 16, 32, 64] {
        for reads in [1, 2, 4, 8] {
            let expr = memory_reads(stores, reads);
            let mut visited = HashSet::new();
            let mut actual = Vec::new();
            collect_uf_declarations_unique(&expr, &mut actual, &mut visited);
            assert_eq!(actual, declaration_pair(&expr));
            assert_eq!(
                actual,
                vec![("entry_memory".into(), Vec::new(), memory_sort())]
            );
            // Structural work bound, not a wall-clock/performance claim.
            assert!(visited.len() <= 128 * (stores + reads + 1));
            assert!(tree_visits(&expr) > visited.len() * 2);
        }
    }
}

#[test]
fn uf_walk_preserves_complete_memory_query_bytes() {
    for stores in [1, 2, 4, 8, 16] {
        assert_query_bytes_unchanged(memory_reads(stores, 2));
    }
}

#[test]
fn uf_walk_same_name_applications_still_visit_distinct_arguments() {
    let g = SmtExpr::uf("g", vec![SmtExpr::var("x", 64)], SmtSort::BitVec(64));
    let h = SmtExpr::uf("h", vec![SmtExpr::var("x", 64)], SmtSort::BitVec(64));
    let left = SmtExpr::uf("f", vec![g], SmtSort::BitVec(64));
    let right = SmtExpr::uf("f", vec![h], SmtSort::BitVec(64));
    let expr = left.eq_expr(right);
    let declarations = declaration_pair(&expr);
    assert_eq!(
        declarations
            .iter()
            .map(|row| row.0.as_str())
            .collect::<Vec<_>>(),
        ["f", "g", "h"]
    );
    assert_query_bytes_unchanged(expr);

    // Preserve the old first-declaration behavior even for conflicting UF
    // signatures. This is a metadata compatibility test, not well-typed input
    // or solver acceptance of that malformed expression.
    let declared = SmtExpr::uf_decl("f", vec![SmtSort::BitVec(32)], SmtSort::BitVec(32));
    let applied = SmtExpr::uf("f", vec![SmtExpr::var("x", 64)], SmtSort::BitVec(64));
    let malformed = declared.eq_expr(applied);
    assert_eq!(
        declaration_pair(&malformed),
        vec![("f".into(), vec![SmtSort::BitVec(32)], SmtSort::BitVec(32))]
    );
}

#[test]
fn uf_walk_preserves_shared_nodes_across_shadowing_binders() {
    let shared = Arc::new(SmtExpr::uf(
        "predicate",
        vec![SmtExpr::var("x", 64)],
        SmtSort::Bool,
    ));
    let forall = SmtExpr::ForAll {
        var: "x".into(),
        var_width: 64,
        lower: Arc::new(SmtExpr::bv_const(0, 64)),
        upper: Arc::new(SmtExpr::bv_const(300, 64)),
        body: shared.clone(),
    };
    let exists = SmtExpr::Exists {
        var: "x".into(),
        var_width: 64,
        lower: Arc::new(SmtExpr::bv_const(0, 64)),
        upper: Arc::new(SmtExpr::bv_const(300, 64)),
        body: Arc::new(forall.and_expr((*shared).clone())),
    };
    let expr = SmtExpr::And {
        lhs: shared,
        rhs: Arc::new(exists),
    };
    assert_eq!(
        declaration_pair(&expr),
        vec![("predicate".into(), vec![SmtSort::BitVec(64)], SmtSort::Bool)]
    );
    assert_query_bytes_unchanged(expr);
}

#[test]
fn uf_walk_preserves_memory_load_and_poison_symbol_identity() {
    let address = SmtExpr::uf(
        "address_fn",
        vec![SmtExpr::var("address", 64)],
        SmtSort::BitVec(64),
    );
    let load = SmtExpr::mem_load(address, 8, true, 64);
    let guard = SmtExpr::uf("guard_fn", vec![SmtExpr::var("x", 64)], SmtSort::BitVec(64));
    let trap = load.trap_if_zero(guard);
    let before = trap.to_string();
    let poison = crate::smt::collect_trap_poison_decls(&trap);
    let declarations = declaration_pair(&trap);
    assert_eq!(
        declarations
            .iter()
            .map(|row| row.0.as_str())
            .collect::<Vec<_>>(),
        ["guard_fn", "mem_load_8_s", "address_fn"]
    );
    assert_eq!(trap.to_string(), before);
    assert_eq!(crate::smt::collect_trap_poison_decls(&trap), poison);
    assert_eq!(poison.len(), 1);
    assert_query_bytes_unchanged(trap);
}

#[test]
fn uf_walk_identity_is_not_structural_and_does_not_escape_one_call() {
    let make = || SmtExpr::uf("same", vec![SmtExpr::var("x", 64)], SmtSort::BitVec(64));
    let expr = make().eq_expr(make());
    let mut visited = HashSet::new();
    let mut declarations = Vec::new();
    collect_uf_declarations_unique(&expr, &mut declarations, &mut visited);
    assert_eq!(visited.len(), 5); // Eq + two distinct UF values + two arguments.
    assert_eq!(declarations, declaration_pair(&expr));
    drop(expr);
    let next = SmtExpr::uf("next", Vec::new(), SmtSort::Bool);
    assert_eq!(
        declaration_pair(&next),
        vec![("next".into(), Vec::new(), SmtSort::Bool)]
    );
}
