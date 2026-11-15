// crates/trust-cg-eqsat/tests/engine_optimize.rs - optimize_function rewrites, derivations, classification, declines
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `optimize_function` with the integer identities on hand-written bodies:
//! every rewritten body validates, behaves like the input on the reference
//! interpreter at boundary inputs, is strictly cheaper, and carries a
//! derivation that decodes canonically and whose claims replay (test-only
//! decoder, `engine_common`). Also: the classification of section 2.3 as
//! seen in `Stats`, the no-change contract, determinism, and one test per
//! decline class.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod engine_common;

use engine_common::{assert_same_behaviour, check_derivation, function, module, substitute};
use trust_cg_eqsat::derivation::header_only;
use trust_cg_eqsat::rules::{INTEGER_IDENTITIES, RuleSet};
use trust_cg_eqsat::{Decline, EngineConfig, Optimized, optimize_function, round_trip};
use trust_cg_eqsat_check::{Registry, check};
use trust_ir::{Function, Inst, Module};

fn rules() -> RuleSet {
    RuleSet::parse(INTEGER_IDENTITIES).expect("rules")
}

/// Optimize `name` and check every contract that applies to the result.
fn optimize(text: &str, name: &str) -> (Module, Function, Optimized) {
    let module = module(text);
    let input = function(&module, name).clone();
    let registry = rules();
    let result = optimize_function(&module, &input, &registry, &EngineConfig::default())
        .unwrap_or_else(|d| panic!("declined: {d}"));
    assert_eq!(result.stats.blocks, input.blocks.len());
    if result.rewritten {
        assert!(
            result.stats.cost_after < result.stats.cost_before,
            "{:?}",
            result.stats
        );
        substitute(&module, &result.function);
        assert_same_behaviour(&module, &input, &result.function, 600);
        let decoded = check_derivation(&result.derivation, &registry);
        assert_eq!(decoded.function, input.name);
    } else {
        assert_eq!(result.function, input);
        assert_eq!(result.derivation, header_only(&input.name));
        assert_eq!(result.stats.cost_after, result.stats.cost_before);
    }
    (module, input, result)
}

fn ret_operand_inst(function: &Function, index: usize) -> Option<&Inst> {
    let block = function.blocks.last()?;
    let Inst::Return { values } = &block.body.last()?.inst else {
        return None;
    };
    let value = values.get(index)?;
    function
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .find(|n| n.results.contains(value))
        .map(|n| &n.inst)
}

const IDENTITIES: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (i32, i32) -> (i32)

fn @f(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = const i32 0
    %3 = xor i32 %0, %2
    %4 = xor i32 %1, %2
    %5 = const i32 1
    %6 = mul i32 %3, %5
    %7 = add i32 %6, %2
    %8 = sub i32 %4, %4
    %9 = add i32 %7, %8
    %10 = const i32 3
    %11 = const i32 4
    %12 = add i32 %10, %11
    %13 = mul i32 %9, %12
    ret %13
}
"#;

#[test]
fn identities_on_defined_operands_rewrite_and_replay() {
    let (_, _, result) = optimize(IDENTITIES, "f");
    assert!(result.rewritten);
    for rule in ["mul_one", "add_zero", "sub_self", "fold_add"] {
        assert!(
            result.stats.rule_matches.contains_key(rule),
            "{rule} did not fire: {:?}",
            result.stats.rule_matches
        );
    }
    // ret %13 is now `mul %3, 7`.
    let Some(Inst::BinOp { op, rhs, .. }) = ret_operand_inst(&result.function, 0) else {
        panic!("ret operand is not a binop")
    };
    assert_eq!(*op, trust_ir::BinOp::Mul);
    let constant = result
        .function
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .find(|n| n.results.contains(rhs))
        .map(|n| n.inst.clone());
    assert_eq!(
        constant,
        Some(Inst::Const {
            ty: trust_ir::Ty::I32,
            value: trust_ir::Constant::Int(7)
        })
    );
    // Cost: the input's 4 consts + mul + add + sub + add + add + mul = 14.
    // The output keeps the two frontier xors (and their const 0) in the
    // skeleton and adds const 7 + mul: 5.
    assert_eq!(result.stats.cost_before, 14);
    assert_eq!(result.stats.cost_after, 5);
    let decoded = check_derivation(&result.derivation, &rules());
    assert_eq!(decoded.claims.len(), 1);
}

const REFINES: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (u64, u64) -> (u64, u64)

fn @f(functy.0) {
bb0(%0: u64, %1: u64):
    %2 = const u64 0
    %3 = or u64 %0, %2
    %4 = mul u64 %3, %2
    %5 = const u64 18446744073709551615
    %6 = or u64 %3, %5
    %7 = add u64 %6, %4
    ret %7, %4
}
"#;

#[test]
fn refines_rules_give_refines_claims() {
    let (_, _, result) = optimize(REFINES, "f");
    assert!(result.rewritten);
    assert!(result.stats.rule_matches.contains_key("mul_zero"));
    assert!(result.stats.rule_matches.contains_key("or_ones"));
    let decoded = engine_common::decode(&result.derivation).unwrap();
    let (_, claims) = engine_common::replay(&decoded, &rules()).unwrap();
    assert!(!claims.is_empty());
    assert!(claims.iter().all(|(_, _, equiv)| !equiv), "{claims:?}");
}

const BOOLEANS: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (i8, i8, bool) -> (i8, bool)

fn @f(functy.0) {
bb0(%0: i8, %1: i8, %2: bool):
    %3 = const i8 0
    %4 = add i8 %0, %3
    %5 = add i8 %1, %3
    %6 = icmp eq i8 %4, %4
    %7 = select i8 %6, %4, %5
    %8 = const bool true
    %9 = icmp ne bool %2, %8
    %10 = band bool %9, %6
    %11 = icmp ult i8 %5, %5
    %12 = bor bool %10, %11
    ret %7, %12
}
"#;

#[test]
fn comparisons_and_selects_fold() {
    let (_, _, result) = optimize(BOOLEANS, "f");
    assert!(result.rewritten);
    for rule in [
        "icmp_eq_self",
        "select_true",
        "band_true",
        "icmp_ult_self",
        "bor_false",
    ] {
        assert!(
            result.stats.rule_matches.contains_key(rule),
            "{rule}: {:?}",
            result.stats.rule_matches
        );
    }
}

const SHARED: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (i32) -> (i32, i32)

fn @f(functy.0) {
bb0(%0: i32):
    %1 = const i32 0
    %2 = xor i32 %0, %1
    %3 = add i32 %2, %1
    %4 = const i32 5
    %5 = mul i32 %3, %4
    %6 = mul i32 %2, %4
    ret %5, %6
}
"#;

#[test]
fn hash_cons_hits_across_a_union_are_explained() {
    // `%6 = mul %2, 5` hash-conses to `%5`'s node (`%3` and `%2` are one
    // class after add_zero), so its entry proof goes through the class's
    // explanation edges.
    let (_, _, result) = optimize(SHARED, "f");
    assert!(result.rewritten);
    let muls = result
        .function
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| {
            matches!(
                n.inst,
                Inst::BinOp {
                    op: trust_ir::BinOp::Mul,
                    ..
                }
            )
        })
        .count();
    assert_eq!(muls, 1);
}

const BRANCHES: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (u16, u16) -> (u16)

fn @f(functy.0) {
bb0(%0: u16, %1: u16):
    %2 = const u16 0
    %3 = or u16 %0, %2
    %4 = or u16 %1, %2
    %5 = icmp ult u16 %3, %4
    condbr %5, bb1, bb2
bb1:
    %6 = const u16 1
    %7 = mul u16 %3, %6
    %8 = add u16 %7, %4
    br bb3(%8)
bb2:
    %9 = sub u16 %4, %4
    %10 = add u16 %3, %9
    %11 = neg u16 %10
    %12 = neg u16 %11
    br bb3(%12)
bb3(%13: u16):
    %14 = const u16 7
    %15 = add u16 %14, %13
    %16 = add u16 %15, %2
    ret %16
}
"#;

#[test]
fn rewrites_across_blocks_keep_dominance() {
    let (_, _, result) = optimize(BRANCHES, "f");
    assert!(result.rewritten);
    assert!(result.stats.rule_matches.contains_key("neg_neg"));
}

const LOOP: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (u8, u8) -> (u8)

fn @f(functy.0) {
bb0(%0: u8, %1: u8):
    %2 = const u8 0
    %3 = const u8 1
    %4 = and u8 %1, %1
    %5 = const u8 7
    %6 = and u8 %4, %5
    br bb1(%2, %0)
bb1(%7: u8, %8: u8):
    %9 = xor u8 %8, %2
    %10 = mul u8 %9, %3
    %11 = add u8 %10, %10
    %12 = add u8 %7, %3
    %13 = sub u8 %6, %2
    %14 = icmp ult u8 %12, %13
    condbr %14, bb1(%12, %11), bb2
bb2:
    %15 = and u8 %11, %11
    ret %15
}
"#;

#[test]
fn rewrites_inside_a_loop() {
    let (_, _, result) = optimize(LOOP, "f");
    assert!(result.rewritten);
}

const CHAIN_HEAD: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (u64) -> (u64)

fn @f(functy.0) {
bb0(%0: u64):
    %1 = const u64 1
    %2 = xor u64 %0, %1
"#;

#[test]
fn a_long_chain_folds_without_deep_recursion() {
    let length = 1500u32;
    let mut text = CHAIN_HEAD.to_owned();
    for i in 0..length {
        text.push_str(&format!("    %{} = add u64 %{}, %1\n", i + 3, i + 2));
    }
    text.push_str(&format!("    ret %{}\n}}\n", length + 2));
    let (_, _, result) = optimize(&text, "f");
    assert!(result.rewritten);
    // add_add_const folds runs of the chain; the counted budgets (rewrite
    // depth, matches per node) bound how far each instruction's class
    // reaches back, so the fold is partial but far cheaper.
    assert!(
        result.stats.cost_after * 10 < result.stats.cost_before,
        "{:?}",
        result.stats
    );
    assert!(result.stats.budget_hits > 0);
    // The arena only grows, so ending below the default arena bound means
    // the bound never stopped a firing here: the partial fold comes from
    // the depth and match budgets alone (it saturates near 132 ids per
    // instruction; `EngineConfig::default`).
    let count = length as usize + 3;
    let bound = EngineConfig::default().max_ids_per_instruction as usize;
    assert!(result.stats.ids < bound * (count + 1), "{:?}", result.stats);
}

const NOT_CHEAPER: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (i32, i32) -> (i32)

fn @f(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = add i32 %0, %1
    %3 = mul i32 %2, %2
    ret %3
}
"#;

#[test]
fn nothing_cheaper_returns_the_input_unchanged() {
    let (_, input, result) = optimize(NOT_CHEAPER, "f");
    assert!(!result.rewritten);
    assert_eq!(result.function, input);
    let decoded = engine_common::decode(&result.derivation).unwrap();
    assert!(decoded.rules.is_empty() && decoded.terms.is_empty());
    assert!(decoded.proofs.is_empty() && decoded.claims.is_empty());
    assert_eq!(result.stats.graph_instructions, 1);
    assert_eq!(result.stats.frontier_instructions, 1);
    assert!(result.stats.nodes >= 2);
}

const CLASSES: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (i32, i32) -> (i32, i32)

fn @f(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = const i32 1
    %3 = add i32 %0, %2
    %4 = copy i32 %0
    %5 = add i32 %4, %2
    %6 = add i32 %3, %5
    %7 = copy i32 %6
    %8 = undef i32
    %9 = mul i32 %8, %2
    %10 = icmp eq i32 %7, %9
    %11 = select i32 %10, %0, %6
    %12 = add i32 %11, %2
    %13 = udiv i32 %6, %2
    %14 = add i32 %13, %2
    %15 = select i32 %10, %6, %14
    %16, %17 = add.overflow i32 %15, %2
    %18 = select i32 %17, %16, %15
    ret %18, %12
}
"#;

#[test]
fn classification_of_graph_frontier_and_skeleton_instructions() {
    let module = module(CLASSES);
    let input = function(&module, "f");
    let result = optimize_function(&module, input, &RuleSet::empty(), &EngineConfig::default())
        .expect("not declined");
    let stats = &result.stats;
    // Graph: %2 %6 %10 %14 %15 %18. Copies: %4 %7.
    assert_eq!(stats.graph_instructions, 6, "{stats:?}");
    assert_eq!(stats.see_through_copies, 2, "{stats:?}");
    // Frontier: %3 and %5 (a parameter, and a copy of one), %9 (undef), %11
    // (a select with a parameter arm), %12 (the select's result may be
    // poison). Skeleton besides: %8 undef, %13 udiv, the overflow, ret.
    assert_eq!(stats.frontier_instructions, 5, "{stats:?}");
    assert_eq!(stats.skeleton_instructions, 9, "{stats:?}");
    // The two copies are removed, so the body is cheaper even without rules.
    assert!(result.rewritten);
    assert_eq!(stats.cost_before, 2 + 6);
    let output = round_trip(&module, input).unwrap();
    substitute(&module, &output);
}

#[test]
fn optimization_is_deterministic() {
    for text in [IDENTITIES, BOOLEANS, SHARED, BRANCHES, LOOP, REFINES] {
        let module = module(text);
        let input = function(&module, "f");
        let first = optimize_function(&module, input, &rules(), &EngineConfig::default()).unwrap();
        let second = optimize_function(&module, input, &rules(), &EngineConfig::default()).unwrap();
        assert_eq!(first.derivation, second.derivation);
        assert_eq!(first.function, second.function);
        assert_eq!(first.stats, second.stats);
        assert_eq!(
            round_trip(&module, input).unwrap(),
            round_trip(&module, input).unwrap()
        );
    }
}

#[test]
fn budgets_are_counted_not_timed() {
    let module = module(IDENTITIES);
    let input = function(&module, "f");
    let tight = EngineConfig {
        max_rewrite_depth: 0,
        max_matches_per_node: 1,
        max_ids_per_instruction: 4,
    };
    let result = optimize_function(&module, input, &rules(), &tight).unwrap();
    assert!(result.stats.budget_hits > 0, "{:?}", result.stats);
    if result.rewritten {
        substitute(&module, &result.function);
        assert_same_behaviour(&module, input, &result.function, 600);
        check_derivation(&result.derivation, &rules());
    }
}

// ---- declines ----------------------------------------------------------------

fn declined(module: &Module, function: &Function) -> Decline {
    let decline = optimize_function(module, function, &rules(), &EngineConfig::default())
        .expect_err("declined");
    assert_eq!(round_trip(module, function).err(), Some(decline.clone()));
    assert!(!decline.to_string().is_empty());
    decline
}

fn base() -> (Module, Function) {
    let module = module(IDENTITIES);
    let function = function(&module, "f").clone();
    (module, function)
}

#[test]
fn declines_a_function_without_a_body() {
    let (module, mut function) = base();
    function.blocks.clear();
    assert_eq!(declined(&module, &function), Decline::NoBody);
    assert_eq!(Decline::NoBody.class(), "no_body");
}

#[test]
fn declines_function_proofs() {
    let (module, mut function) = base();
    function.proofs.push(trust_ir::ProofAnnotation::Pure);
    assert_eq!(declined(&module, &function).class(), "function_proofs");
}

#[test]
fn declines_a_summary() {
    let (module, mut function) = base();
    function.summary = Some(trust_ir::FunctionSummary::default());
    assert_eq!(declined(&module, &function).class(), "summary");
}

#[test]
fn declines_a_body_gate() {
    let (module, mut function) = base();
    function.body_gate = Some(trust_ir::BodyGate::Ungated);
    assert_eq!(declined(&module, &function).class(), "body_gate");
}

#[test]
fn declines_source_provenance() {
    let (module, mut function) = base();
    let digest = trust_ir::ProofDigest::sha256_domain("test", b"");
    function.source_provenance = Some(trust_ir::SourceProvenance::new(digest, digest, Vec::new()));
    assert_eq!(declined(&module, &function).class(), "source_provenance");
}

#[test]
fn declines_instruction_proofs() {
    let (module, mut function) = base();
    function.blocks[0].body[0]
        .proofs
        .push(trust_ir::ProofAnnotation::Pure);
    assert_eq!(declined(&module, &function).class(), "instruction_proofs");
}

#[test]
fn declines_a_module_obligation() {
    let (mut module, function) = base();
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::ObligationKind::Postcondition,
            trust_ir::ProofStatus::Pending,
            "about f",
        )
        .with_function(function.id),
    );
    assert_eq!(declined(&module, &function).class(), "module_obligation");
}

#[test]
fn declines_an_unreachable_block() {
    let (module, mut function) = base();
    let mut dead = function.blocks[0].clone();
    dead.id = trust_ir::BlockId(9);
    function.blocks.push(dead);
    assert_eq!(declined(&module, &function), Decline::UnreachableBlock);
}

#[test]
fn declines_unsupported_shapes() {
    let (module, mut function) = base();
    // A value defined twice.
    let results = function.blocks[0].body[1].results.clone();
    function.blocks[0].body[2].results = results;
    let decline = declined(&module, &function);
    assert_eq!(decline.class(), "unsupported", "{decline}");
}

#[test]
fn declines_obligations_by_function_site_or_none_and_spec_modules() {
    let obligation = || {
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::ObligationKind::Postcondition,
            trust_ir::ProofStatus::Pending,
            "an obligation",
        )
    };
    // Named by its site only.
    let (mut module, function) = base();
    module
        .proof_obligations
        .push(obligation().with_site(trust_ir::ObligationSite::new(
            function.id,
            function.entry,
            0,
        )));
    assert_eq!(declined(&module, &function), Decline::ModuleObligation);
    // Naming no function: refuses every function.
    let (mut module, function) = base();
    module.proof_obligations.push(obligation());
    assert_eq!(declined(&module, &function), Decline::UnscopedObligation);
    assert_eq!(Decline::UnscopedObligation.class(), "unscoped_obligation");
    // Naming another function only: not a refusal.
    let (mut module, function) = base();
    module
        .proof_obligations
        .push(obligation().with_function(trust_ir::FuncId::new(function.id.0 + 1)));
    assert!(optimize_function(&module, &function, &rules(), &EngineConfig::default()).is_ok());
    // Spec modules: refuses every function.
    let (mut module, function) = base();
    module.spec_modules.push(trust_ir::SpecModule::new("spec"));
    assert_eq!(declined(&module, &function), Decline::SpecModules);
    assert_eq!(Decline::SpecModules.class(), "spec_modules");
}

/// Every [`Decline`] variant; the match below has no wildcard, so a new
/// variant fails to compile until it is listed here.
fn every_decline() -> Vec<Decline> {
    let all = vec![
        Decline::NoBody,
        Decline::FunctionProofs,
        Decline::Summary,
        Decline::BodyGate,
        Decline::SourceProvenance,
        Decline::InstructionProofs,
        Decline::ModuleObligation,
        Decline::UnscopedObligation,
        Decline::SpecModules,
        Decline::RefinementPredicates,
        Decline::UnreachableBlock,
        Decline::Unsupported(String::new()),
    ];
    for decline in &all {
        match decline {
            Decline::NoBody
            | Decline::FunctionProofs
            | Decline::Summary
            | Decline::BodyGate
            | Decline::SourceProvenance
            | Decline::InstructionProofs
            | Decline::ModuleObligation
            | Decline::UnscopedObligation
            | Decline::SpecModules
            | Decline::RefinementPredicates
            | Decline::UnreachableBlock
            | Decline::Unsupported(_) => {}
        }
    }
    all
}

/// The class names section 2.5 of the contract lists (`* `name`: ...`).
fn spec_refusal_classes() -> Vec<String> {
    let spec = include_str!("../../../docs/eqsat-tier-e.md");
    let start = spec.find("### 2.5 ").expect("the contract has section 2.5");
    let end = start + spec[start..].find("\n## 3.").expect("section 3 follows");
    spec[start..end]
        .lines()
        .filter_map(|line| line.strip_prefix("* `"))
        .filter_map(|rest| rest.split_once("`:").map(|(name, _)| name.to_owned()))
        .collect()
}

#[test]
fn decline_classes_are_the_contract_refusal_classes() {
    let spec = spec_refusal_classes();
    assert_eq!(spec.len(), 11, "{spec:?}");
    let mut engine: Vec<String> = every_decline()
        .iter()
        .map(|decline| decline.class().to_owned())
        .filter(|class| class != "unsupported")
        .collect();
    let mut sorted_spec = spec.clone();
    engine.sort();
    sorted_spec.sort();
    assert_eq!(engine, sorted_spec);
    assert_eq!(Decline::Unsupported(String::new()).class(), "unsupported");
}

// ---- constants (section 2.2 `Const` row) ------------------------------------

/// A module `f: () -> (T)` whose body is `%0 = <constant>; ret %0`, at the
/// given pointer width.
fn constant_module(ty: &str, target: &str, constant: trust_ir::Constant) -> (Module, Function) {
    let zero = if ty == "bool" { "false" } else { "0" };
    let text = format!(
        "; TrustIr text format v1\nmodule \"m\"\n{target}\nfuncty.0 = () -> ({ty})\n\n\
         fn @f(functy.0) {{\nbb0:\n    %0 = const {ty} {zero}\n    ret %0\n}}\n"
    );
    let mut module = module(&text);
    let index = module.functions.iter().position(|f| f.name == "f").unwrap();
    let Inst::Const { ty, .. } = module.functions[index].blocks[0].body[0].inst.clone() else {
        panic!("not a const")
    };
    module.functions[index].blocks[0].body[0].inst = Inst::Const {
        ty,
        value: constant,
    };
    let function = module.functions[index].clone();
    (module, function)
}

#[test]
fn constants_are_graph_constants_only_in_range_and_canonical() {
    use trust_ir::Constant as C;
    const WASM: &str = "target \"wasm32-unknown-unknown\" 4 little\n";
    let cases: Vec<(&str, &str, trust_ir::Constant, bool)> = vec![
        ("u8", "", C::Int(255), true),
        ("u8", "", C::Int(256), false),
        ("u8", "", C::Int(-1), false),
        ("i8", "", C::Int(-128), true),
        ("i8", "", C::Int(-129), false),
        ("i8", "", C::Int(128), false),
        ("u8", "", C::U128(5), false),
        ("u64", "", C::U128(5), false),
        ("u128", "", C::U128(5), false),
        ("u128", "", C::U128(1u128 << 127), true),
        ("u128", "", C::U128(u128::MAX), true),
        ("u128", "", C::Int(-1), false),
        ("i128", "", C::Int(i128::MIN), true),
        ("usize", "", C::Int(1i128 << 32), true),
        ("usize", WASM, C::Int(1i128 << 32), false),
        ("usize", WASM, C::Int((1i128 << 32) - 1), true),
        ("isize", WASM, C::Int(-(1i128 << 31) - 1), false),
        ("bool", "", C::Bool(true), true),
        ("bool", "", C::Int(1), false),
        ("u8", "", C::Bool(true), false),
    ];
    for (ty, target, constant, graph) in cases {
        let (module, function) = constant_module(ty, target, constant.clone());
        let result = optimize_function(
            &module,
            &function,
            &RuleSet::empty(),
            &EngineConfig::default(),
        )
        .unwrap_or_else(|d| panic!("{ty} {constant:?}: declined {d}"));
        assert_eq!(
            result.stats.graph_instructions,
            usize::from(graph),
            "{ty} {constant:?} at {target:?}: {:?}",
            result.stats
        );
        // Neither reading has anything to rewrite in this body.
        assert!(!result.rewritten);
    }
}

#[test]
fn a_u128_spelling_at_a_narrow_type_is_skeleton_and_its_result_may_be_poison() {
    // The reviewer's case: `const u8 U128(5)` is a TypeError in the
    // interpreter, not a total operator. It stays skeleton; its result is
    // not defined (section 2.3), so `add` over it is a frontier instruction
    // and nothing folds: the output runs into the same TypeError.
    let text = r#"; TrustIr text format v1
module "m"

functy.0 = (u8) -> (u8)

fn @k(functy.0) {
bb0(%0: u8):
    %1 = const u8 5
    %2 = const u8 0
    %3 = add u8 %1, %2
    ret %3
}
"#;
    let mut module = module(text);
    module.functions[0].blocks[0].body[0].inst = Inst::Const {
        ty: trust_ir::Ty::U8,
        value: trust_ir::Constant::U128(5),
    };
    let input = module.functions[0].clone();
    let result = optimize_function(&module, &input, &rules(), &EngineConfig::default()).unwrap();
    assert_eq!(result.stats.graph_instructions, 1, "{:?}", result.stats);
    assert_eq!(result.stats.frontier_instructions, 1, "{:?}", result.stats);
    assert!(!result.rewritten);
    assert_eq!(result.function, input);
    let registry = Registry::parse(INTEGER_IDENTITIES).unwrap();
    check(
        &module,
        &input,
        &result.function,
        &result.derivation,
        &registry,
    )
    .unwrap_or_else(|r| panic!("checker refused: {r:?}"));
}

// ---- availability of terminator results (section 4) ---------------------------

fn parse_unvalidated(text: &str) -> Module {
    trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

/// Optimize, round-trip and check with the independent checker.
fn optimize_and_check(module: &Module, name: &str) -> Optimized {
    let input = function(module, name);
    let registry = Registry::parse(INTEGER_IDENTITIES).unwrap();
    let result = optimize_function(module, input, &rules(), &EngineConfig::default())
        .unwrap_or_else(|d| panic!("declined: {d}"));
    check(
        module,
        input,
        &result.function,
        &result.derivation,
        &registry,
    )
    .unwrap_or_else(|r| panic!("checker refused the engine output: {r:?}"));
    if result.rewritten {
        let substituted = substitute(module, &result.function);
        let errors = trust_ir_build::validate_module(&substituted);
        assert!(errors.is_empty(), "{errors:?}");
    }
    let trip = round_trip(module, input).unwrap_or_else(|d| panic!("round trip declined: {d}"));
    substitute(module, &trip);
    check(module, input, &trip, &header_only(&input.name), &registry)
        .unwrap_or_else(|r| panic!("checker refused the round trip: {r:?}"));
    result
}

const INVOKE_NORMAL_ARGS: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little

functy.0 = (i64) -> (i64)

fn @callee(functy.0) {
}

fn @f(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1(%1) unwind bb2
bb1(%2: i64):
    %3 = const i64 3
    %4 = const i64 4
    %5 = add i64 %3, %4
    ret %5
bb2:
    %6, %7 = landingpad cleanup
    resume %6
}
"#;

#[test]
fn an_invoke_result_in_its_own_normal_edge_arguments_is_available() {
    let module = module(INVOKE_NORMAL_ARGS);
    let result = optimize_and_check(&module, "f");
    assert!(result.rewritten, "{:?}", result.stats);
}

// The normal successor is a loop header: its other incoming edge is its own
// back edge, from a block it dominates, so the normal edge dominates it.
const INVOKE_LOOP_HEADER: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little

functy.0 = (i64) -> (i64)

fn @callee(functy.0) {
}

fn @g(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1() unwind bb3
bb1:
    %2 = icmp eq i64 %1, %0
    condbr %2, bb1, bb2
bb2:
    %5 = const i64 3
    %6 = const i64 4
    %7 = add i64 %5, %6
    ret %7
bb3:
    %3, %4 = landingpad cleanup
    resume %3
}
"#;

#[test]
fn an_invoke_result_below_a_loop_header_normal_successor_is_available() {
    let module = module(INVOKE_LOOP_HEADER);
    let result = optimize_and_check(&module, "g");
    assert!(result.rewritten, "{:?}", result.stats);
}

fn declined_unavailable(text: &str, name: &str) {
    let module = parse_unvalidated(text);
    let input = function(&module, name);
    let decline = optimize_function(&module, input, &rules(), &EngineConfig::default())
        .expect_err("an unavailable use is declined");
    assert_eq!(decline.class(), "unsupported", "{decline}");
    assert!(decline.to_string().contains("section 4"), "{decline}");
    assert_eq!(round_trip(&module, input).err(), Some(decline));
}

#[test]
fn an_invoke_result_read_outside_its_normal_edge_is_declined() {
    // Read in the unwind successor (the invoking block dominates it, the
    // normal successor does not).
    declined_unavailable(
        r#"; TrustIr text format v1
module "m"

functy.0 = (i64) -> (i64)

fn @callee(functy.0) {
}

fn @u(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad cleanup
    %4 = copy i64 %1
    ret %4
}
"#,
        "u",
    );
    // Read in the normal successor, which the landing pad also enters: the
    // normal edge does not dominate it.
    declined_unavailable(
        r#"; TrustIr text format v1
module "m"

functy.0 = (i64) -> (i64)

fn @callee(functy.0) {
}

fn @v(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad cleanup
    br bb1
}
"#,
        "v",
    );
    // Read by its own invoke as a call argument.
    declined_unavailable(
        r#"; TrustIr text format v1
module "m"

functy.0 = (i64) -> (i64)

fn @callee(functy.0) {
}

fn @w(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%1) to bb1(%1) unwind bb2
bb1(%4: i64):
    ret %4
bb2:
    %2, %3 = landingpad cleanup
    resume %2
}
"#,
        "w",
    );
}

#[test]
fn a_landing_pad_after_another_instruction_is_declined() {
    let module_text = INVOKE_NORMAL_ARGS;
    let mut module = module(module_text);
    let index = module.functions.iter().position(|f| f.name == "f").unwrap();
    let pad_block = &mut module.functions[index].blocks[2];
    assert!(matches!(pad_block.body[0].inst, Inst::LandingPad { .. }));
    pad_block.body.insert(
        0,
        trust_ir::InstrNode::new(Inst::Const {
            ty: trust_ir::Ty::I64,
            value: trust_ir::Constant::Int(1),
        })
        .with_result(trust_ir::ValueId(40)),
    );
    let input = module.functions[index].clone();
    let decline = optimize_function(&module, &input, &rules(), &EngineConfig::default())
        .expect_err("a misplaced landing pad is declined");
    assert_eq!(decline.class(), "unsupported", "{decline}");
    assert!(decline.to_string().contains("LandingPad"), "{decline}");
}

#[test]
fn a_block_without_one_terminator_at_its_end_is_declined() {
    let (module, function) = base();
    let terminator = function.blocks[0].body.last().unwrap().clone();
    // A terminator before the end.
    let mut early = function.clone();
    early.blocks[0].body.insert(0, terminator);
    // No terminator.
    let mut open = function.clone();
    open.blocks[0].body.pop();
    // No instruction at all.
    let mut empty = function.clone();
    empty.blocks[0].body.clear();
    for body in [early, open, empty] {
        let decline = declined(&module, &body);
        assert_eq!(decline.class(), "unsupported", "{decline}");
        assert!(decline.to_string().contains("terminator"), "{decline}");
    }
}

// ---- resources (section 6 budgets; extraction proofs) --------------------------

fn instructions(function: &Function) -> usize {
    function.blocks.iter().map(|block| block.body.len()).sum()
}

/// `%x_k = select (icmp eq %d, k), %x_{k-1}, %x_{k-1}` links, each used by a
/// skeleton `udiv`: every link is a `select_same` union and every use
/// extracts through the whole chain below it.
fn select_chain(n: usize) -> String {
    let mut text = String::from(
        "; TrustIr text format v1\nmodule \"m\"\n\nfuncty.0 = (i32) -> (i32)\n\n\
         fn @f(functy.0) {\nbb0(%0: i32):\n    %1 = const i32 0\n    %2 = xor i32 %0, %1\n    \
         %3 = const i32 3\n",
    );
    let mut next = 4;
    let mut cur = 2;
    for k in 0..n {
        text.push_str(&format!(
            "    %{c} = const i32 {k}\n    %{b} = icmp eq i32 %2, %{c}\n    \
             %{v} = select i32 %{b}, %{cur}, %{cur}\n    %{s} = udiv i32 %{v}, %3\n",
            c = next,
            b = next + 1,
            v = next + 2,
            s = next + 3,
        ));
        cur = next + 2;
        next += 4;
    }
    text.push_str(&format!("    ret %{cur}\n}}\n"));
    text
}

#[test]
fn extraction_proofs_are_linear_in_a_select_chain() {
    let registry = Registry::parse(INTEGER_IDENTITIES).unwrap();
    let mut rows = Vec::new();
    for n in [64usize, 256] {
        let module = module(&select_chain(n));
        let input = function(&module, "f");
        let result = optimize_function(&module, input, &rules(), &EngineConfig::default())
            .unwrap_or_else(|d| panic!("declined: {d}"));
        assert!(result.rewritten);
        let verdict = check(
            &module,
            input,
            &result.function,
            &result.derivation,
            &registry,
        )
        .unwrap_or_else(|r| panic!("checker refused: {r:?}"));
        rows.push((result.derivation.len(), verdict.proof_steps));
    }
    let ((bytes_64, steps_64), (bytes_256, steps_256)) = (rows[0], rows[1]);
    // Four times the links: a linear derivation is about four times larger,
    // a quadratic one sixteen times.
    assert!(bytes_256 < 6 * bytes_64, "{rows:?}");
    assert!(steps_256 < 6 * steps_64, "{rows:?}");
}

/// `%k = add %k-1, %k-1` doublings: `double_to_mul` then `mul_mul_const`
/// fire on every link, the densest graph the default rules build.
fn doubling_chain(n: usize) -> String {
    let mut text = String::from(
        "; TrustIr text format v1\nmodule \"m\"\n\nfuncty.0 = (i32) -> (i32)\n\n\
         fn @f(functy.0) {\nbb0(%0: i32):\n    %1 = const i32 0\n    %2 = xor i32 %0, %1\n",
    );
    for k in 0..n {
        text.push_str(&format!(
            "    %{} = add i32 %{}, %{}\n",
            k + 3,
            k + 2,
            k + 2
        ));
    }
    text.push_str(&format!("    ret %{}\n}}\n", n + 2));
    text
}

#[test]
fn the_arena_bound_caps_ids_per_instruction() {
    let registry = Registry::parse(INTEGER_IDENTITIES).unwrap();
    let module = module(&doubling_chain(190));
    let input = function(&module, "f");
    let count = instructions(input);
    for per_instruction in [0u32, 1, 4, 16, 256] {
        let config = EngineConfig {
            max_ids_per_instruction: per_instruction,
            ..EngineConfig::default()
        };
        let result = optimize_function(&module, input, &rules(), &config)
            .unwrap_or_else(|d| panic!("declined at {per_instruction}: {d}"));
        let limit = per_instruction as usize * (count + 1);
        // Past the bound only the input's own nodes and leaves (at most two
        // per instruction) and the rhs instantiation in progress (a few
        // entries) are added.
        assert!(
            result.stats.ids <= limit + 2 * count + 32,
            "{per_instruction}: {} ids for {count} instructions",
            result.stats.ids
        );
        if per_instruction < 16 {
            assert!(result.stats.budget_hits > 0, "{:?}", result.stats);
        }
        if per_instruction == 0 {
            assert!(result.stats.rule_matches.is_empty(), "{:?}", result.stats);
        }
        assert!(result.stats.cost_after <= result.stats.cost_before);
        if result.rewritten {
            substitute(&module, &result.function);
            assert_same_behaviour(&module, input, &result.function, 64);
        } else {
            assert_eq!(&result.function, input);
            assert_eq!(result.derivation, header_only(&input.name));
        }
        check(
            &module,
            input,
            &result.function,
            &result.derivation,
            &registry,
        )
        .unwrap_or_else(|r| panic!("checker refused at {per_instruction}: {r:?}"));
        let again = optimize_function(&module, input, &rules(), &config).unwrap();
        assert_eq!(again.derivation, result.derivation);
        assert_eq!(again.stats, result.stats);
    }
}

#[test]
fn the_default_arena_bound_does_not_bind_on_the_densest_chains() {
    // Section 6 / `EngineConfig::default`: the default bound is above what
    // the default rules reach on a doubling chain, so it changes no output
    // there.
    let module = module(&doubling_chain(190));
    let input = function(&module, "f");
    let default = optimize_function(&module, input, &rules(), &EngineConfig::default()).unwrap();
    let unbounded = EngineConfig {
        max_ids_per_instruction: u32::MAX,
        ..EngineConfig::default()
    };
    let wide = optimize_function(&module, input, &rules(), &unbounded).unwrap();
    assert_eq!(default.stats, wide.stats);
    assert_eq!(default.derivation, wide.derivation);
    let bound = EngineConfig::default().max_ids_per_instruction as usize;
    assert!(
        default.stats.ids < bound * (instructions(input) + 1),
        "{:?}",
        default.stats
    );
}

// ---- literal-sensitive operands (sections 2.5 and 6) ------------------------------

/// The instruction that defines `value` in `function`.
fn def_of(function: &Function, value: trust_ir::ValueId) -> &Inst {
    function
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .find(|n| n.results.contains(&value))
        .map(|n| &n.inst)
        .unwrap_or_else(|| panic!("no definition of %{}", value.0))
}

/// The literal-sensitive operands of `function`, in body order.
fn literal_sensitive_operands(function: &Function) -> Vec<trust_ir::ValueId> {
    let mut out = Vec::new();
    for node in function.blocks.iter().flat_map(|b| &b.body) {
        match &node.inst {
            Inst::ExtractElement { index, .. } | Inst::InsertElement { index, .. } => {
                out.push(*index);
            }
            Inst::PtrFromParts { data, metadata, .. } => out.extend([*data, *metadata]),
            Inst::Resume { exn } => out.push(*exn),
            _ => {}
        }
    }
    out
}

/// `output` with every see-through copy in front of a literal-sensitive
/// operand bypassed: the form the engine must not return.
fn unguarded(output: &Function) -> Function {
    let mut out = output.clone();
    let copies: Vec<(trust_ir::ValueId, trust_ir::ValueId)> = out
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter_map(|n| match (&n.inst, n.results.as_slice()) {
            (Inst::Copy { operand, .. }, [result]) => Some((*result, *operand)),
            _ => None,
        })
        .collect();
    let bypass = |value: &mut trust_ir::ValueId| {
        if let Some((_, operand)) = copies.iter().find(|(result, _)| result == value) {
            *value = *operand;
        }
    };
    for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
        match &mut node.inst {
            Inst::ExtractElement { index, .. } | Inst::InsertElement { index, .. } => {
                bypass(index);
            }
            Inst::PtrFromParts { data, metadata, .. } => {
                bypass(data);
                bypass(metadata);
            }
            _ => {}
        }
    }
    out
}

/// Optimize `text`'s `@f` (the `optimize` contracts: the output validates,
/// the interpreter agrees, the derivation replays), check it with the
/// independent checker, and return, per literal-sensitive operand in body
/// order, whether a see-through copy defines it in the output.
fn literal_guards(text: &str) -> (Module, Function, Optimized, Vec<bool>) {
    let (module, input, result) = optimize(text, "f");
    assert!(result.rewritten, "{:?}", result.stats);
    let registry = Registry::parse(INTEGER_IDENTITIES).unwrap();
    check(
        &module,
        &input,
        &result.function,
        &result.derivation,
        &registry,
    )
    .unwrap_or_else(|r| panic!("checker refused the engine output: {r:?}"));
    let guarded = literal_sensitive_operands(&result.function)
        .into_iter()
        .map(|value| match def_of(&result.function, value) {
            Inst::Copy { operand, .. } => {
                assert!(
                    matches!(def_of(&result.function, *operand), Inst::Const { .. }),
                    "a guard copy of a non-constant"
                );
                true
            }
            _ => false,
        })
        .collect();
    (module, input, result, guarded)
}

// The verifier's case: `4 + 5` as a lane index is valid (the validator
// range-checks only a `Const` index), the folded `const u32 9` is not. Also
// an in-range computed index (folded, guarded), the same constant as an
// existing `Const` there (no guard) and a copy of a constant (guarded).
const EXTRACT_LANES: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little

functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const <4 x u32> vec[ 10, 20, 30, 40 ]
    %2 = const u32 4
    %3 = const u32 5
    %4 = add u32 %2, %3
    %5 = const u32 1
    %6 = const u32 2
    %7 = add u32 %5, %6
    %8 = extractelement u32 %1, %7
    %9 = const u32 0
    %10 = icmp eq u32 %0, %9
    condbr %10, bb1, bb2
bb1:
    %11 = extractelement u32 %1, %4
    ret %11
bb2:
    %12 = add u32 %0, %8
    %13 = const u32 2
    %14 = extractelement u32 %1, %13
    %15 = add u32 %12, %14
    %16 = const u32 0
    %17 = copy u32 %16
    %18 = extractelement u32 %1, %17
    %19 = add u32 %15, %18
    ret %19
}
"#;

#[test]
fn a_folded_lane_index_is_read_through_a_copy() {
    let (module, _, result, guarded) = literal_guards(EXTRACT_LANES);
    // %8 (folded 3), %11 (folded 9), %14 (the input's `const u32 2`), %18
    // (a copy of `const u32 0` in the input).
    assert_eq!(guarded, [true, true, false, true]);
    // Without the copies the out-of-range lane index is a `Const`, which
    // trust-ir's validator range-checks and refuses.
    let bare = unguarded(&result.function);
    let mut bare_module = module.clone();
    bare_module.functions[0] = bare;
    let errors = trust_ir_build::validate_module(&bare_module);
    assert!(
        errors
            .iter()
            .any(|e| format!("{e:?}").contains("constant lane index 9 is out of range")),
        "{errors:?}"
    );
}

const INSERT_LANES: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little

functy.0 = (i16) -> (i16)

fn @f(functy.0) {
bb0(%0: i16):
    %1 = const <4 x i16> vec[ -1, 2, -3, 4 ]
    %2 = const i16 3
    %3 = const i16 -1
    %4 = add i16 %2, %3
    %5 = insertelement <4 x i16> %1, %4, %0
    %6 = const i16 2
    %7 = extractelement i16 %5, %6
    %8 = const i16 0
    %9 = icmp eq i16 %0, %8
    condbr %9, bb1, bb2
bb1:
    %10 = const i16 7
    %11 = const i16 -1
    %12 = xor i16 %10, %11
    %13 = insertelement <4 x i16> %1, %12, %0
    %14 = extractelement i16 %13, %6
    ret %14
bb2:
    ret %7
}
"#;

#[test]
fn a_folded_insert_lane_index_is_read_through_a_copy() {
    let (module, _, result, guarded) = literal_guards(INSERT_LANES);
    // %5 (folded 2), %7 (the input's `const i16 2`), %13 (folded -8), %14
    // (the input's `const i16 2`).
    assert_eq!(guarded, [true, false, true, false]);
    let bare = unguarded(&result.function);
    let mut bare_module = module.clone();
    bare_module.functions[0] = bare;
    let errors = trust_ir_build::validate_module(&bare_module);
    assert!(
        errors
            .iter()
            .any(|e| format!("{e:?}").contains("constant lane index -8 is out of range")),
        "{errors:?}"
    );
}

const PTR_FROM_PARTS: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little

functy.0 = (u64) -> (u64)

type ty.0 = u64

fn @f(functy.0) {
bb0(%0: u64):
    %1 = alloca u64
    %2 = const u64 1
    %3 = const u64 2
    %4 = add u64 %2, %3
    %5 = ptr_from_parts fatptr<slice ty.0> ptr %1, u64 %4
    %6 = ptr_metadata fatptr<slice ty.0> %5 to u64
    %7 = add u64 %0, %6
    %8 = const u64 3
    %9 = ptr_from_parts fatptr<slice ty.0> ptr %1, u64 %8
    %10 = ptr_metadata fatptr<slice ty.0> %9 to u64
    %11 = add u64 %7, %10
    ret %11
}
"#;

#[test]
fn a_folded_ptr_from_parts_operand_is_read_through_a_copy() {
    let (_, _, _, guarded) = literal_guards(PTR_FROM_PARTS);
    // (data, metadata) of %5 (metadata folded to 3) and of %9 (the input's
    // `const u64 3`): a pointer data operand is never in the graph.
    assert_eq!(guarded, [false, true, false, false]);
}

// ---- exhaustive switch selectors (sections 2.5 and 6) -----------------------------

/// The selector trace of every flagged switch of `function` as the
/// validator's `selector_enum` and the checker read it: the non-copy
/// definitions from the selector through `zext`, `sext` and `bitcast` to the
/// first other definition, each as (result, instruction kind and every field
/// but the operands), copies skipped.
fn selector_traces(function: &Function) -> Vec<Vec<(trust_ir::ValueId, String)>> {
    let defs: std::collections::BTreeMap<trust_ir::ValueId, &Inst> = function
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .flat_map(|n| n.results.iter().map(move |r| (*r, &n.inst)))
        .collect();
    let mut traces = Vec::new();
    for node in function.blocks.iter().flat_map(|b| &b.body) {
        let Inst::Switch {
            value,
            exhaustive_enum_unreachable: true,
            ..
        } = &node.inst
        else {
            continue;
        };
        let mut trace = Vec::new();
        let mut current = *value;
        loop {
            match defs.get(&current).copied() {
                None => {
                    trace.push((current, "param".to_owned()));
                    break;
                }
                Some(Inst::Copy { operand, .. }) => current = *operand,
                Some(Inst::Cast {
                    op: trust_ir::CastOp::ZExt | trust_ir::CastOp::SExt | trust_ir::CastOp::Bitcast,
                    src_ty,
                    dst_ty,
                    operand,
                }) => {
                    trace.push((current, format!("cast {src_ty} -> {dst_ty}")));
                    current = *operand;
                }
                Some(inst) => {
                    let text = format!("{inst:?}");
                    let kind = text.split([' ', '{', '(']).next().unwrap_or("").to_owned();
                    trace.push((current, kind));
                    break;
                }
            }
        }
        traces.push(trace);
    }
    traces
}

/// Every argument vector of `(enum.0[, u32])`: each discriminant of the
/// three-variant `repr(u8)` enum 0, crossed with a few `u32` values.
fn enum_args(module: &Module, function: &Function) -> Vec<Vec<trust_ir::InterpretValue>> {
    let params = &module.func_types[function.ty.0 as usize].params;
    let tags: Vec<trust_ir::InterpretValue> = (0..3)
        .map(|d| trust_ir::InterpretValue {
            ty: params[0].clone(),
            kind: trust_ir::InterpretValueKind::Aggregate(vec![
                trust_ir::InterpretValue::int(trust_ir::Ty::U8, d).unwrap(),
            ]),
        })
        .collect();
    let mut out = Vec::new();
    for tag in tags {
        match params.len() {
            1 => out.push(vec![tag]),
            2 => {
                for r in [0u128, 1, 7, 0xffff_ffff] {
                    out.push(vec![tag.clone(), engine_common::value(&params[1], r)]);
                }
            }
            n => panic!("unexpected parameter count {n}"),
        }
    }
    out
}

/// Optimize `@f` of a module with an exhaustive switch and hold every
/// contract: the output validates, the independent checker accepts it with
/// its derivation, the interpreter agrees on every discriminant, the
/// derivation replays, and every selector trace is the input's.
fn optimize_switch(text: &str) -> (Module, Function, Optimized) {
    let module = module(text);
    let input = function(&module, "f").clone();
    let registry = rules();
    let result = optimize_function(&module, &input, &registry, &EngineConfig::default())
        .unwrap_or_else(|d| panic!("declined: {d}"));
    let output_module = substitute(&module, &result.function);
    check(
        &module,
        &input,
        &result.function,
        &result.derivation,
        &Registry::parse(INTEGER_IDENTITIES).unwrap(),
    )
    .unwrap_or_else(|r| panic!("checker refused the engine output: {r:?}"));
    let mut returned = 0;
    for args in enum_args(&module, &input) {
        let expected = engine_common::run(&module, input.id, &args);
        let actual = engine_common::run(&output_module, input.id, &args);
        assert_eq!(expected, actual, "args {args:?}");
        returned += usize::from(expected.is_ok());
    }
    assert!(returned > 0, "no input returned normally");
    if result.rewritten {
        assert!(result.stats.cost_after < result.stats.cost_before);
        check_derivation(&result.derivation, &registry);
    } else {
        assert_eq!(result.function, input);
        assert_eq!(result.derivation, header_only(&input.name));
    }
    assert_eq!(selector_traces(&result.function), selector_traces(&input));
    // The round trip keeps the traces too.
    let trip = round_trip(&module, &input).unwrap();
    substitute(&module, &trip);
    assert_eq!(selector_traces(&trip), selector_traces(&input));
    (module, input, result)
}

/// `%9 = OP u32 (zext tag), K; switch %9 [CASES] exhaustive`, with `ret %2`
/// on the cases: the reproducers of the selector trace rule. `add 0` / `mul 1`
/// make the trace end at a graph instruction the identities would remove.
fn tag_switch(op: &str, k: u32, cases: &str) -> String {
    format!(
        r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little
file 0 "m.rs"

enum @E repr(u8) {{ A, B, C }} id=0

functy.0 = (enum.0) -> (u32)

fn @f(functy.0) {{
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    %2 = zext u8 %1 to u32
    %8 = const u32 {k}
    %9 = {op} u32 %2, %8
    switch %9 [ {cases} default: bb2 ] exhaustive
bb1:
    ret %2
bb2:
    unreachable
}}
"#
    )
}

#[test]
fn an_add_zero_selector_of_an_incomplete_exhaustive_switch_is_kept() {
    let text = tag_switch("add", 0, "0: bb1 1: bb1");
    let (_, input, result) = optimize_switch(&text);
    // Nothing else is cheaper: the input comes back unchanged, and the
    // selector still ends at the `add` (the validator does not hold the
    // two-case set to the three-variant enum).
    assert!(!result.rewritten, "{:?}", result.stats);
    assert_eq!(
        selector_traces(&input),
        [[(trust_ir::ValueId(9), "BinOp".to_owned())]]
    );
}

#[test]
fn a_mul_one_selector_of_an_incomplete_exhaustive_switch_is_kept() {
    let (_, _, result) = optimize_switch(&tag_switch("mul", 1, "0: bb1 1: bb1"));
    assert!(!result.rewritten, "{:?}", result.stats);
}

#[test]
fn an_add_zero_selector_of_a_complete_exhaustive_switch_is_kept() {
    let (_, _, result) = optimize_switch(&tag_switch("add", 0, "0: bb1 1: bb1 2: bb1"));
    assert!(!result.rewritten, "{:?}", result.stats);
}

/// The trace `copy (zext u32->u64 (copy (add (mul (zext tag), 1), 0)))`: the
/// cast and the `add` that ends it are kept and the copies go; the `add`'s
/// own operand `mul %3, 1` folds to `%3` (a claim on the selector), and the
/// unrelated `add %12, 0` folds to `%12` (`%12` is a frontier `xor` of the
/// parameter, a defined value).
const TAG_TRACE_REWRITTEN: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little
file 0 "m.rs"

enum @E repr(u8) { A, B, C } id=0

functy.0 = (enum.0, u32) -> (u32)

fn @f(functy.0) {
bb0(%0: enum.0, %1: u32):
    %2 = extractfield u8 %0, 0
    %3 = zext u8 %2 to u32
    %4 = const u32 1
    %5 = mul u32 %3, %4
    %6 = const u32 0
    %7 = add u32 %5, %6
    %8 = copy u32 %7
    %9 = zext u32 %8 to u64
    %10 = copy u64 %9
    %12 = xor u32 %1, %6
    %11 = add u32 %12, %6
    switch %10 [ 0: bb1 1: bb1 default: bb2 ] exhaustive
bb1:
    ret %11
bb2:
    unreachable
}
"#;

#[test]
fn the_rest_of_a_function_with_an_exhaustive_switch_is_still_optimized() {
    let (_, input, result) = optimize_switch(TAG_TRACE_REWRITTEN);
    assert!(result.rewritten, "{:?}", result.stats);
    assert_eq!(
        selector_traces(&input),
        [[
            (trust_ir::ValueId(9), "cast u32 -> u64".to_owned()),
            (trust_ir::ValueId(7), "BinOp".to_owned())
        ]]
    );
    let out = &result.function;
    // The switch reads the kept cast directly (copies removed).
    let Some(Inst::Switch { value, .. }) = out.blocks[0].body.last().map(|n| &n.inst) else {
        panic!("bb0 does not end in the switch")
    };
    assert_eq!(*value, trust_ir::ValueId(9));
    // The kept `add` now reads the tag's zext directly.
    let Inst::BinOp { op, lhs, rhs, .. } = def_of(out, trust_ir::ValueId(7)) else {
        panic!("%7 is not a binop")
    };
    assert_eq!(*op, trust_ir::BinOp::Add);
    assert_eq!(*lhs, trust_ir::ValueId(3));
    assert!(matches!(def_of(out, *rhs), Inst::Const { .. }));
    // `ret %11` became `ret %12`; no copy, `mul` or second `add` is left.
    let Some(Inst::Return { values }) = out.blocks[1].body.last().map(|n| &n.inst) else {
        panic!("bb1 does not return")
    };
    assert_eq!(values.as_slice(), [trust_ir::ValueId(12)]);
    let insts: Vec<&Inst> = out.blocks[0].body.iter().map(|n| &n.inst).collect();
    assert!(
        !insts.iter().any(|i| matches!(i, Inst::Copy { .. })),
        "{out:?}"
    );
    let binops: Vec<trust_ir::BinOp> = insts
        .iter()
        .filter_map(|i| match i {
            Inst::BinOp { op, .. } => Some(*op),
            _ => None,
        })
        .collect();
    assert_eq!(
        binops,
        [trust_ir::BinOp::Add, trust_ir::BinOp::Xor],
        "{out:?}"
    );
    // Cost: 2 consts + mul (3) + add + 2 copies + zext + add = 10 before;
    // the kept add, its const 0 and the kept zext after.
    assert_eq!(result.stats.cost_before, 10);
    assert_eq!(result.stats.cost_after, 3);
    // Two claims: the selector's (through the kept add) and the return's.
    let decoded = check_derivation(&result.derivation, &rules());
    assert_eq!(decoded.claims.len(), 2);
}

/// The trace rule refuses what the engine produced before it kept the
/// trace: the switch reading `zext tag` directly does not validate with an
/// incomplete case set, and the checker refuses it.
#[test]
fn a_selector_exposed_to_the_tag_is_refused_by_the_validator_and_the_checker() {
    let input_module = module(&tag_switch("add", 0, "0: bb1 1: bb1"));
    let input = function(&input_module, "f").clone();
    let exposed_text = tag_switch("add", 0, "0: bb1 1: bb1")
        .replace("    %8 = const u32 0\n    %9 = add u32 %2, %8\n", "")
        .replace("switch %9", "switch %2");
    let exposed_module = trust_ir::parser::parse_module(&exposed_text).unwrap();
    assert!(!trust_ir_build::validate_module(&exposed_module).is_empty());
    let exposed = function(&exposed_module, "f").clone();
    let refused = check(
        &input_module,
        &input,
        &exposed,
        &header_only("f"),
        &Registry::parse(INTEGER_IDENTITIES).unwrap(),
    )
    .expect_err("the checker refuses an exposed tag");
    assert_eq!(refused.class(), "tag_provenance_changed", "{refused:?}");
}

#[test]
fn declines_refinement_predicates() {
    let (mut module, function) = base();
    module
        .intern_pred(trust_ir::Pred::Interval { lo: 0, hi: 9 })
        .unwrap()
        .unwrap();
    assert!(!module.predicates.is_empty());
    assert_eq!(declined(&module, &function), Decline::RefinementPredicates);
    assert_eq!(
        Decline::RefinementPredicates.class(),
        "refinement_predicates"
    );
}
