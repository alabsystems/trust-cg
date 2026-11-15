//! Finite regression contract for the *stored* AArch64 FCMP obligations.
//!
//! These checks do not call AY, obtain certificates, or establish formal
//! source-to-instruction correspondence. Expected IEEE comparisons use integer
//! bits, independently of both semantic encoders and the evaluator under test.

use std::collections::{HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};

use trust_cg_ir::WasmOpcode;
use trust_cg_lower::{Type, instructions::FloatCC};
use trust_cg_verify::aarch64_semantics::{FPSize, encode_fcmp};
use trust_cg_verify::ay_bridge::{AYConfig, generate_smt2_query_raw};
use trust_cg_verify::lowering_proof::{
    ProofObligation, VerificationConfig, all_fp_lowering_proofs, memoized_verify_by_evaluation,
    proof_fcmp_lt_f32, proof_fcmp_lt_f64, verify_by_evaluation_with_config,
    verify_fp_by_evaluation,
};
use trust_cg_verify::smt::{EvalResult, SmtExpr, SmtSort};
use trust_cg_verify::trust_ir_semantics::encode_trust_ir_fcmp;
use trust_cg_verify::verify::{VerificationResult, VerificationStrength};
use trust_cg_verify::wasm_function_verifier::{
    WasmISelInst, reconstruct_alu_obligation, representative_reconstructable_inst,
};
use trust_cg_verify::{wasm_lowering_proofs, x86_64_lowering_proofs};

const CONDITIONS: [(&str, FloatCC); 14] = [
    ("Eq", FloatCC::Equal),
    ("NE", FloatCC::NotEqual),
    ("LT", FloatCC::LessThan),
    ("LE", FloatCC::LessThanOrEqual),
    ("GT", FloatCC::GreaterThan),
    ("GE", FloatCC::GreaterThanOrEqual),
    ("Ord", FloatCC::Ordered),
    ("Uno", FloatCC::Unordered),
    ("UEQ", FloatCC::UnorderedEqual),
    ("UNE", FloatCC::UnorderedNotEqual),
    ("ULT", FloatCC::UnorderedLessThan),
    ("ULE", FloatCC::UnorderedLessThanOrEqual),
    ("UGT", FloatCC::UnorderedGreaterThan),
    ("UGE", FloatCC::UnorderedGreaterThanOrEqual),
];

const BITS32: [u64; 16] = [
    0,
    0x8000_0000,
    0x3f80_0000,
    0xbf80_0000,
    1,
    0x8000_0001,
    0x007f_ffff,
    0x0080_0000,
    0x7f7f_ffff,
    0xff7f_ffff,
    0x7f80_0000,
    0xff80_0000,
    0x7fc1_2345,
    0xffc2_3456,
    0x7f81_2345,
    0xff81_2346,
];
const BITS64: [u64; 16] = [
    0,
    0x8000_0000_0000_0000,
    0x3ff0_0000_0000_0000,
    0xbff0_0000_0000_0000,
    1,
    0x8000_0000_0000_0001,
    0x000f_ffff_ffff_ffff,
    0x0010_0000_0000_0000,
    0x7fef_ffff_ffff_ffff,
    0xffef_ffff_ffff_ffff,
    0x7ff0_0000_0000_0000,
    0xfff0_0000_0000_0000,
    0x7ff8_1234_5678_9abc,
    0xfff8_2345_6789_abcd,
    0x7ff0_1234_5678_9abc,
    0xfff0_1234_5678_9abd,
];

fn format(width: u32) -> (u32, u32) {
    match width {
        32 => (8, 24),
        64 => (11, 53),
        _ => panic!("unsupported test width"),
    }
}

fn ty(width: u32) -> Type {
    if width == 32 { Type::F32 } else { Type::F64 }
}

fn size(width: u32) -> FPSize {
    if width == 32 {
        FPSize::Single
    } else {
        FPSize::Double
    }
}

fn bits(width: u32) -> &'static [u64; 16] {
    if width == 32 { &BITS32 } else { &BITS64 }
}

fn raw_inputs(width: u32) -> Vec<(String, u32)> {
    vec![("a_bits".into(), width), ("b_bits".into(), width)]
}

fn operands(width: u32) -> (SmtExpr, SmtExpr) {
    let (eb, sb) = format(width);
    (
        SmtExpr::bv_bits_to_fp(SmtExpr::var("a_bits", width), eb, sb),
        SmtExpr::bv_bits_to_fp(SmtExpr::var("b_bits", width), eb, sb),
    )
}

fn environment(a: u64, b: u64) -> HashMap<String, u64> {
    HashMap::from([("a_bits".into(), a), ("b_bits".into(), b)])
}

fn bound_proof(width: u32, condition: FloatCC) -> ProofObligation {
    // A separate deliberately mutable positive for evaluator tests. The
    // registry tests below always inspect the actual builder output instead.
    let mut proof = if width == 32 {
        proof_fcmp_lt_f32()
    } else {
        proof_fcmp_lt_f64()
    };
    let (a, b) = operands(width);
    proof.inputs = raw_inputs(width);
    proof.fp_inputs.clear();
    proof.trust_ir_expr = encode_trust_ir_fcmp(&condition, ty(width), a.clone(), b.clone());
    proof.aarch64_expr = encode_fcmp(size(width), a, b, &condition);
    proof
}

fn legacy_zero_proof(width: u32) -> ProofObligation {
    let mut proof = bound_proof(width, FloatCC::LessThan);
    let (eb, sb) = format(width);
    let zero = SmtExpr::FPConst { bits: 0, eb, sb };
    proof.inputs.clear();
    proof.fp_inputs = vec![("a".into(), eb, sb), ("b".into(), eb, sb)];
    proof.trust_ir_expr =
        encode_trust_ir_fcmp(&FloatCC::LessThan, ty(width), zero.clone(), zero.clone());
    proof.aarch64_expr = encode_fcmp(size(width), zero.clone(), zero, &FloatCC::LessThan);
    proof
}

fn registry_rows() -> Vec<ProofObligation> {
    let rows: Vec<_> = all_fp_lowering_proofs()
        .into_iter()
        .filter(|proof| proof.name.starts_with("Fcmp_"))
        .collect();
    assert_eq!(rows.len(), 28);
    assert_eq!(
        rows.iter().map(|p| &p.name).collect::<HashSet<_>>().len(),
        28
    );
    rows
}

fn registry_row(rows: &[ProofObligation], width: u32, name: &str) -> ProofObligation {
    let expected = format!("Fcmp_{name}_F{width} -> FCMP+CSET");
    rows.iter()
        .find(|p| p.name == expected)
        .expect("required FCMP row")
        .clone()
}

// IEEE ordering by sign and unsigned magnitude. NaNs are removed before
// ordering, and signed zeros compare equal. No host FP operation is an oracle.
fn ieee_predicate(condition: usize, width: u32, a: u64, b: u64) -> bool {
    let sign = 1_u64 << (width - 1);
    let exponent = if width == 32 {
        0x7f80_0000
    } else {
        0x7ff0_0000_0000_0000
    };
    let fraction = if width == 32 {
        0x007f_ffff
    } else {
        0x000f_ffff_ffff_ffff
    };
    let nan = |x| x & exponent == exponent && x & fraction != 0;
    let unordered = nan(a) || nan(b);
    let zeros = a & !sign == 0 && b & !sign == 0;
    let equal = !unordered && (a == b || zeros);
    let less = !unordered
        && !equal
        && if (a ^ b) & sign != 0 {
            a & sign != 0
        } else if a & sign != 0 {
            a > b
        } else {
            a < b
        };
    let greater = !unordered && !equal && !less;
    match condition {
        0 => equal,
        1 => !unordered && !equal,
        2 => less,
        3 => less || equal,
        4 => greater,
        5 => greater || equal,
        6 => !unordered,
        7 => unordered,
        8 => unordered || equal,
        9 => unordered || !equal,
        10 => unordered || less,
        11 => unordered || less || equal,
        12 => unordered || greater,
        13 => unordered || greater || equal,
        _ => unreachable!(),
    }
}

fn query(proof: &ProofObligation) -> String {
    // Serialization only: no solver process is created.
    let raw = generate_smt2_query_raw(proof, &AYConfig::default());
    assert!(
        raw.lines().any(|line| line == "(set-logic QF_BVFP)"),
        "{} must retain combined FP/BV logic: {raw}",
        proof.name
    );
    raw
}

fn assertion(query: &str) -> &str {
    let assertions: Vec<_> = query
        .lines()
        .filter(|line| line.starts_with("(assert "))
        .collect();
    assert_eq!(assertions.len(), 1, "one raw assertion, not declarations");
    assertions[0]
}

fn has_token(text: &str, token: &str) -> bool {
    text.split(|c: char| c.is_whitespace() || matches!(c, '(' | ')'))
        .any(|s| s == token)
}

fn finite(proof: &ProofObligation) -> VerificationResult {
    verify_by_evaluation_with_config(proof, &VerificationConfig::with_sample_count(16))
}

fn assert_valid(result: VerificationResult, context: &str) {
    assert!(
        matches!(result, VerificationResult::Valid),
        "{context}: {result:?}"
    );
}

fn assert_invalid(result: VerificationResult, context: &str) {
    assert!(
        matches!(result, VerificationResult::Invalid { .. }),
        "{context}: {result:?}"
    );
}

fn assert_unknown(result: VerificationResult, context: &str) {
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "{context}: {result:?}"
    );
}

fn assert_rejected_without_panic(proof: &ProofObligation, context: &str) {
    let config = VerificationConfig::with_sample_count(16);
    for entry in ["primary", "memo", "direct-fp"] {
        let result = catch_unwind(AssertUnwindSafe(|| match entry {
            "primary" => verify_by_evaluation_with_config(proof, &config),
            "memo" => memoized_verify_by_evaluation(proof, &config),
            "direct-fp" => verify_fp_by_evaluation(proof),
            _ => unreachable!(),
        }));
        let result = result.unwrap_or_else(|_| panic!("{context}: {entry} panicked"));
        assert_unknown(result, &format!("{context}: {entry}"));
    }
}

#[test]
fn stored_registry_rows_bind_distinct_width_correct_raw_inputs_and_assertions() {
    let rows = registry_rows();
    let mut queries = HashSet::new();
    let mut degenerate = 0;
    for width in [32, 64] {
        let (eb, sb) = format(width);
        for (name, _) in CONDITIONS {
            let proof = registry_row(&rows, width, name);
            assert_eq!(proof.inputs, raw_inputs(width), "{}", proof.name);
            assert!(proof.fp_inputs.is_empty(), "{}", proof.name);
            assert!(proof.preconditions.is_empty());
            for expression in [&proof.trust_ir_expr, &proof.aarch64_expr] {
                assert_eq!(expression.sort(), SmtSort::BitVec(1));
                assert_eq!(expression.free_vars(), ["a_bits", "b_bits"]);
                let text = expression.to_smt2_expr();
                for input in ["a_bits", "b_bits"] {
                    assert!(
                        text.contains(&format!("((_ to_fp {eb} {sb}) {input})")),
                        "{text}"
                    );
                }
            }
            // Binding actual inputs does not create model independence. These
            // six existing identity trees still receive no static proof credit.
            assert_eq!(
                proof.is_degenerate(),
                matches!(name, "Eq" | "LT" | "Uno"),
                "{}",
                proof.name
            );
            degenerate += usize::from(proof.is_degenerate());
            let raw = query(&proof);
            let assertion = assertion(&raw);
            for input in ["a_bits", "b_bits"] {
                let declaration = format!("(declare-const {input} (_ BitVec {width}))");
                assert_eq!(raw.lines().filter(|line| *line == declaration).count(), 1);
                assert!(has_token(assertion, input), "{}: {assertion}", proof.name);
                assert!(assertion.contains(&format!("((_ to_fp {eb} {sb}) {input})")));
            }
            assert!(!has_token(assertion, "fp"), "no zero FP placeholders");
            assert!(
                queries.insert(raw),
                "each predicate/width has its own actual query"
            );
        }
    }
    assert_eq!(queries.len(), 28);
    assert_eq!((degenerate, rows.len() - degenerate), (6, 22));
}

#[test]
fn all_stored_source_and_machine_trees_match_independent_ieee_boundary_predicates() {
    let rows = registry_rows();
    let mut pairs = 0;
    let mut checks = 0;
    for width in [32, 64] {
        for (condition, (name, _)) in CONDITIONS.iter().enumerate() {
            let proof = registry_row(&rows, width, name);
            let mut choices = [0_usize; 2];
            for &a in bits(width) {
                for &b in bits(width) {
                    let expected = ieee_predicate(condition, width, a, b);
                    choices[usize::from(expected)] += 1;
                    let env = environment(a, b);
                    for (side, tree) in [
                        ("source", &proof.trust_ir_expr),
                        ("machine", &proof.aarch64_expr),
                    ] {
                        let actual = tree.try_eval(&env).unwrap_or_else(|error| {
                            panic!("{} {side} a={a:x} b={b:x}: {error}", proof.name)
                        });
                        assert_eq!(
                            actual,
                            EvalResult::Bv(u64::from(expected)),
                            "{} {side} a={a:x} b={b:x}",
                            proof.name
                        );
                        checks += 1;
                    }
                    pairs += 1;
                }
            }
            assert!(
                choices.iter().all(|n| *n > 0),
                "{} must exercise both choices",
                proof.name
            );
        }
    }
    assert_eq!(pairs, 14 * 2 * 16 * 16);
    assert_eq!(checks, 14_336);
}

#[test]
fn all_registered_fcmp_checks_remain_finite_even_with_large_exhaustive_threshold() {
    let mut config = VerificationConfig::with_sample_count(16);
    config.exhaustive_threshold = 128;
    for proof in registry_rows() {
        assert_eq!(
            VerificationStrength::for_obligation_with_config(&proof, &config),
            VerificationStrength::Statistical { sample_count: 16 }
        );
        assert_valid(
            verify_by_evaluation_with_config(&proof, &config),
            &proof.name,
        );
        assert_valid(memoized_verify_by_evaluation(&proof, &config), &proof.name);
    }
}

#[test]
fn same_name_asymmetric_swaps_collapse_and_wrong_predicates_refute_actual_trees() {
    let mut count = 0;
    for width in [32, 64] {
        let (a, b) = operands(width);
        let mut base = bound_proof(width, FloatCC::LessThan);
        // Only the seed changes: neither name contains the stored predicate.
        base.name = format!("renamed FCMP binding witness {width}");
        assert_valid(finite(&base), "renamed positive");
        for mutation in [
            "machine-swap",
            "machine-collapse",
            "machine-wrong-eq",
            "source-wrong-eq",
            "machine-wrong-gt",
            "constant-false",
        ] {
            let mut proof = base.clone();
            match mutation {
                "machine-swap" => {
                    proof.aarch64_expr =
                        encode_fcmp(size(width), b.clone(), a.clone(), &FloatCC::LessThan)
                }
                "machine-collapse" => {
                    proof.aarch64_expr =
                        encode_fcmp(size(width), a.clone(), a.clone(), &FloatCC::LessThan)
                }
                "machine-wrong-eq" => {
                    proof.aarch64_expr =
                        encode_fcmp(size(width), a.clone(), b.clone(), &FloatCC::Equal)
                }
                "source-wrong-eq" => {
                    proof.trust_ir_expr =
                        encode_trust_ir_fcmp(&FloatCC::Equal, ty(width), a.clone(), b.clone())
                }
                "machine-wrong-gt" => {
                    proof.aarch64_expr =
                        encode_fcmp(size(width), a.clone(), b.clone(), &FloatCC::GreaterThan)
                }
                "constant-false" => proof.aarch64_expr = SmtExpr::bv_const(0, 1),
                _ => unreachable!(),
            }
            assert_eq!(proof.name, base.name);
            assert_ne!(proof, base);
            let mut witnessed = false;
            for &left in bits(width) {
                for &right in bits(width) {
                    let env = environment(left, right);
                    witnessed |= proof.trust_ir_expr.try_eval(&env).unwrap()
                        != proof.aarch64_expr.try_eval(&env).unwrap();
                }
            }
            assert!(witnessed, "{width} {mutation} is not a real mutant");
            assert_invalid(finite(&proof), mutation);
            assert_invalid(
                memoized_verify_by_evaluation(&proof, &VerificationConfig::with_sample_count(16)),
                mutation,
            );
            assert_invalid(verify_fp_by_evaluation(&proof), mutation);
            count += 1;
        }
    }
    assert_eq!(count, 12);
}

#[test]
fn nan_plain_ne_mutants_refute_with_zero_random_samples() {
    let config = VerificationConfig::with_sample_count(0);
    for width in [32, 64] {
        let positive = bound_proof(width, FloatCC::NotEqual);
        assert_valid(
            verify_by_evaluation_with_config(&positive, &config),
            "ordered NE",
        );
        let (a, b) = operands(width);
        let plain_ne = SmtExpr::ite(
            a.fp_eq(b).not_expr(),
            SmtExpr::bv_const(1, 1),
            SmtExpr::bv_const(0, 1),
        );
        for source_side in [false, true] {
            let mut proof = positive.clone();
            if source_side {
                proof.trust_ir_expr = plain_ne.clone();
            } else {
                proof.aarch64_expr = plain_ne.clone();
            }
            let env = environment(bits(width)[12], 0);
            assert_ne!(
                proof.trust_ir_expr.try_eval(&env).unwrap(),
                proof.aarch64_expr.try_eval(&env).unwrap()
            );
            assert_invalid(
                verify_by_evaluation_with_config(&proof, &config),
                "NaN plain NE edge",
            );
            assert_invalid(
                memoized_verify_by_evaluation(&proof, &config),
                "NaN plain NE memo",
            );
            assert_invalid(verify_fp_by_evaluation(&proof), "NaN plain NE direct");
        }
    }
}

#[test]
fn malformed_bindings_and_identical_tree_shortcuts_fail_closed_without_panics() {
    let mut count = 0;
    for width in [32, 64] {
        let base = bound_proof(width, FloatCC::LessThan);
        let (a, b) = operands(width);
        let (eb, sb) = format(width);
        for mutation in [
            "missing",
            "duplicate",
            "wrong-declaration-width",
            "wrong-leaf-width",
            "wrong-bitcast-width",
            "wrong-bitcast-format",
            "unresolved",
            "evaluation-error",
            "output-sort",
            "extra-fp-input",
        ] {
            let mut proof = base.clone();
            match mutation {
                "missing" => {
                    proof.inputs.pop();
                }
                "duplicate" => {
                    proof.inputs[1] = proof.inputs[0].clone();
                }
                "wrong-declaration-width" => {
                    proof.inputs[1].1 = if width == 32 { 64 } else { 32 };
                }
                "wrong-leaf-width" => {
                    let bad = SmtExpr::bv_bits_to_fp(SmtExpr::var("a_bits", width - 1), eb, sb);
                    proof.aarch64_expr =
                        encode_fcmp(size(width), bad, b.clone(), &FloatCC::LessThan);
                }
                "wrong-bitcast-width" => {
                    let bad = SmtExpr::bv_bits_to_fp(SmtExpr::var("a_bits", width), 5, 11);
                    proof.aarch64_expr =
                        encode_fcmp(size(width), bad, b.clone(), &FloatCC::LessThan);
                }
                "wrong-bitcast-format" => {
                    let bad = SmtExpr::bv_bits_to_fp(SmtExpr::var("a_bits", width), eb + 1, sb - 1);
                    proof.aarch64_expr =
                        encode_fcmp(size(width), bad, b.clone(), &FloatCC::LessThan);
                }
                "unresolved" => {
                    let bad = SmtExpr::bv_bits_to_fp(SmtExpr::var("missing_bits", width), eb, sb);
                    proof.aarch64_expr =
                        encode_fcmp(size(width), bad, b.clone(), &FloatCC::LessThan);
                }
                "evaluation-error" => {
                    let bad = SmtExpr::uf(
                        "uninterpreted_bit",
                        vec![SmtExpr::var("a_bits", width)],
                        SmtSort::BitVec(1),
                    );
                    proof.aarch64_expr =
                        SmtExpr::ite(a.clone().fp_lt(b.clone()), bad, SmtExpr::bv_const(0, 1));
                }
                "output-sort" => {
                    proof.aarch64_expr = SmtExpr::ite(
                        a.clone().fp_lt(b.clone()),
                        SmtExpr::bv_const(1, 2),
                        SmtExpr::bv_const(0, 2),
                    );
                }
                "extra-fp-input" => proof.fp_inputs.push(("a_bits".into(), eb, sb)),
                _ => unreachable!(),
            }
            assert_rejected_without_panic(&proof, mutation);
            // Identical trees must not bypass declaration, recursive sort or
            // evaluation-error validation in either primary or memo entry.
            proof.trust_ir_expr = proof.aarch64_expr.clone();
            assert_rejected_without_panic(&proof, &format!("identical {mutation}"));
            count += 2;
        }
    }
    assert_eq!(count, 40);
}

#[test]
fn preconditions_constrain_actual_inputs_and_empty_domains_remain_unknown() {
    for width in [32, 64] {
        let mut proof = bound_proof(width, FloatCC::LessThan);
        let (a, b) = operands(width);
        proof.aarch64_expr = encode_fcmp(size(width), a, b, &FloatCC::GreaterThan);
        assert_invalid(finite(&proof), "unconstrained LT versus GT");
        proof
            .preconditions
            .push(SmtExpr::var("a_bits", width).eq_expr(SmtExpr::var("b_bits", width)));
        assert_valid(
            finite(&proof),
            "equal-bit domain makes both ordered predicates false",
        );
        proof.preconditions = vec![SmtExpr::bool_const(false)];
        assert_unknown(finite(&proof), "empty source domain");
        assert_unknown(
            memoized_verify_by_evaluation(&proof, &VerificationConfig::with_sample_count(16)),
            "empty memo domain",
        );
        assert_unknown(verify_fp_by_evaluation(&proof), "empty direct FP domain");
        proof.aarch64_expr = proof.trust_ir_expr.clone();
        assert_unknown(finite(&proof), "identical empty source domain");
        assert_unknown(
            memoized_verify_by_evaluation(&proof, &VerificationConfig::with_sample_count(16)),
            "identical empty memo domain",
        );
        for precondition in [
            SmtExpr::bv_const(1, 1),
            SmtExpr::var("unbound_precondition", width).eq_expr(SmtExpr::bv_const(0, width)),
        ] {
            proof.preconditions = vec![precondition];
            assert_rejected_without_panic(&proof, "malformed precondition");
        }
    }
}

#[test]
fn legacy_zero_and_current_bound_formulas_have_separate_queries_and_memo_verdicts() {
    let config = VerificationConfig::with_sample_count(16);
    for width in [32, 64] {
        let positive = bound_proof(width, FloatCC::LessThan);
        let legacy = legacy_zero_proof(width);
        let mut mutant = positive.clone();
        let (a, b) = operands(width);
        mutant.aarch64_expr = encode_fcmp(size(width), b, a, &FloatCC::LessThan);
        assert_eq!(legacy.name, positive.name);
        assert_eq!(mutant.name, positive.name);
        assert_ne!(legacy, positive);
        let legacy_query = query(&legacy);
        let positive_query = query(&positive);
        let mutant_query = query(&mutant);
        assert_ne!(legacy_query, positive_query);
        assert_ne!(positive_query, mutant_query);
        assert!(has_token(assertion(&legacy_query), "fp"));
        assert!(!has_token(assertion(&legacy_query), "a"));
        assert!(has_token(assertion(&positive_query), "a_bits"));
        assert!(has_token(assertion(&positive_query), "b_bits"));
        for _ in 0..2 {
            assert_valid(
                memoized_verify_by_evaluation(&positive, &config),
                "bound memo positive",
            );
            assert_unknown(
                memoized_verify_by_evaluation(&legacy, &config),
                "legacy placeholders cannot borrow bound credit",
            );
            assert_invalid(
                memoized_verify_by_evaluation(&mutant, &config),
                "same-name changed machine tree",
            );
            assert_valid(
                memoized_verify_by_evaluation(&positive, &config),
                "failed entry cannot contaminate positive",
            );
        }
        assert_rejected_without_panic(&legacy, "legacy placeholders");
        let mut identical = legacy;
        identical.aarch64_expr = identical.trust_ir_expr.clone();
        assert_rejected_without_panic(&identical, "identical legacy placeholders");
    }
}

fn audit_cross_arch_stored_row(proof: &ProofObligation, width: u32, condition: usize) -> usize {
    assert_eq!(proof.inputs, raw_inputs(width), "{}", proof.name);
    assert!(proof.fp_inputs.is_empty(), "{}", proof.name);
    let raw = query(proof);
    let (eb, sb) = format(width);
    for input in ["a_bits", "b_bits"] {
        assert!(raw.contains(&format!("(declare-const {input} (_ BitVec {width}))")));
        assert!(has_token(assertion(&raw), input));
        assert!(assertion(&raw).contains(&format!("((_ to_fp {eb} {sb}) {input})")));
    }
    assert!(!has_token(assertion(&raw), "fp"));
    for tree in [&proof.trust_ir_expr, &proof.aarch64_expr] {
        assert_eq!(tree.sort(), SmtSort::BitVec(1));
        assert_eq!(tree.free_vars(), ["a_bits", "b_bits"]);
    }
    let mut choices = [0_usize; 2];
    let mut checks = 0;
    for &a in bits(width) {
        for &b in bits(width) {
            let expected = ieee_predicate(condition, width, a, b);
            choices[usize::from(expected)] += 1;
            let env = environment(a, b);
            for (side, tree) in [
                ("source", &proof.trust_ir_expr),
                ("machine", &proof.aarch64_expr),
            ] {
                assert_eq!(
                    tree.try_eval(&env).unwrap(),
                    EvalResult::Bv(u64::from(expected)),
                    "{} {side} a={a:x} b={b:x}",
                    proof.name
                );
                checks += 1;
            }
        }
    }
    assert!(choices.iter().all(|n| *n > 0), "{}", proof.name);
    let mut config = VerificationConfig::with_sample_count(16);
    config.exhaustive_threshold = 128;
    assert_eq!(
        VerificationStrength::for_obligation_with_config(proof, &config),
        VerificationStrength::Statistical { sample_count: 16 }
    );
    assert_valid(
        verify_by_evaluation_with_config(proof, &config),
        &proof.name,
    );
    assert_valid(memoized_verify_by_evaluation(proof, &config), &proof.name);
    checks
}

#[test]
fn shared_evaluator_keeps_all_x86_fcmp_stored_queries_and_ieee_predicates_bound() {
    // These are stored x86 value models, not native x86 execution on this host.
    let rows: Vec<_> = x86_64_lowering_proofs::all_x86_64_proofs()
        .into_iter()
        .filter(|proof| proof.name.starts_with("Fcmp_"))
        .collect();
    assert_eq!(rows.len(), 28);
    let mut visited = HashSet::new();
    let mut checks = 0;
    for width in [32, 64] {
        let opcode = if width == 32 { "UCOMISS" } else { "UCOMISD" };
        for (condition, (tag, _)) in CONDITIONS.iter().enumerate() {
            let name = format!("Fcmp_{tag}_F{width} -> x86_64 {opcode}+SETcc");
            let proof = rows
                .iter()
                .find(|row| row.name == name)
                .expect("exact x86 FCMP row");
            assert!(visited.insert(proof.name.clone()));
            checks += audit_cross_arch_stored_row(proof, width, condition);
        }
    }
    assert_eq!(visited.len(), 28);
    assert_eq!(checks, 14_336);
}

#[test]
fn shared_evaluator_keeps_all_wasm_fcmp_stored_queries_and_wrong_control_bound() {
    // Wasm has twelve ordered/unordered predicates; no Ord/Uno row is invented.
    let predicates = [
        ("OEq", 0),
        ("ONe", 1),
        ("OLt", 2),
        ("OLe", 3),
        ("OGt", 4),
        ("OGe", 5),
        ("UEq", 8),
        ("UNe", 9),
        ("ULt", 10),
        ("ULe", 11),
        ("UGt", 12),
        ("UGe", 13),
    ];
    let rows = wasm_lowering_proofs::fcmp_proofs();
    assert_eq!(rows.len(), 24);
    let mut visited = HashSet::new();
    let mut checks = 0;
    for width in [32, 64] {
        for (tag, condition) in predicates {
            let name = format!("FCmp_{tag}_f{width} -> wasm");
            let proof = rows
                .iter()
                .find(|row| row.name == name)
                .expect("exact Wasm FCMP row");
            assert!(visited.insert(proof.name.clone()));
            checks += audit_cross_arch_stored_row(proof, width, condition);
        }
    }
    assert_eq!(visited.len(), 24);
    assert_eq!(checks, 12_288);
    let wrong = wasm_lowering_proofs::proof_wrong_oeq_is_olt();
    assert_eq!(wrong.inputs, raw_inputs(32));
    assert!(wrong.fp_inputs.is_empty());
    let raw = query(&wrong);
    for input in ["a_bits", "b_bits"] {
        assert!(has_token(assertion(&raw), input));
        assert!(assertion(&raw).contains(&format!("((_ to_fp 8 24) {input})")));
    }
    let env = environment(0, 0);
    assert_eq!(
        wrong.trust_ir_expr.try_eval(&env).unwrap(),
        EvalResult::Bv(1)
    );
    assert_eq!(
        wrong.aarch64_expr.try_eval(&env).unwrap(),
        EvalResult::Bv(0)
    );
    assert_invalid(finite(&wrong), "stored Wasm wrong-predicate control");
    assert_invalid(
        memoized_verify_by_evaluation(&wrong, &VerificationConfig::with_sample_count(16)),
        "stored Wasm wrong memo",
    );
    assert_invalid(verify_fp_by_evaluation(&wrong), "stored Wasm wrong direct");
}

#[test]
fn renamed_noncanonical_inputs_cannot_bypass_scalar_compare_sort_validation() {
    for width in [32, 64] {
        let mut proof = bound_proof(width, FloatCC::LessThan);
        proof.name = "independently named numerical relation".into();
        proof.inputs = vec![("left_raw".into(), width), ("right_raw".into(), width)];
        let (eb, sb) = format(width);
        let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("left_raw", width), eb, sb);
        let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("right_raw", width), eb, sb);
        proof.trust_ir_expr =
            encode_trust_ir_fcmp(&FloatCC::LessThan, ty(width), a.clone(), b.clone());
        proof.aarch64_expr = encode_fcmp(size(width), a.clone(), b.clone(), &FloatCC::LessThan);
        assert_valid(finite(&proof), "typed noncanonical input names");
        assert_valid(
            memoized_verify_by_evaluation(&proof, &VerificationConfig::with_sample_count(16)),
            "typed renamed memo",
        );
        for tree in [
            a.clone().fp_lt(b.clone()),
            SmtExpr::ite(
                a.clone().fp_lt(b.clone()),
                SmtExpr::bv_const(1, 2),
                SmtExpr::bv_const(0, 2),
            ),
        ] {
            let mut malformed = proof.clone();
            malformed.trust_ir_expr = tree.clone();
            malformed.aarch64_expr = tree;
            assert_rejected_without_panic(&malformed, "renamed identical invalid output sort");
        }
        let mut malformed = proof;
        malformed.inputs.pop();
        assert_rejected_without_panic(&malformed, "renamed missing declaration");
    }
}

#[test]
fn contradictory_and_nan_only_preconditions_measure_applicable_points() {
    let config = VerificationConfig::with_sample_count(0);
    for width in [32, 64] {
        let mut proof = bound_proof(width, FloatCC::NotEqual);
        let input = SmtExpr::var("a_bits", width);
        proof.preconditions = vec![
            input.clone().eq_expr(SmtExpr::bv_const(0, width)),
            input.eq_expr(SmtExpr::bv_const(1, width)),
        ];
        assert_unknown(
            verify_by_evaluation_with_config(&proof, &config),
            "contradictory nonliteral domain",
        );
        assert_unknown(
            memoized_verify_by_evaluation(&proof, &config),
            "contradictory memo domain",
        );
        assert_unknown(
            verify_fp_by_evaluation(&proof),
            "contradictory direct domain",
        );

        let (a, b) = operands(width);
        proof.preconditions = vec![a.clone().fp_is_nan()];
        assert_valid(
            verify_by_evaluation_with_config(&proof, &config),
            "actual NaN points are applicable",
        );
        proof.aarch64_expr = SmtExpr::ite(
            a.fp_eq(b).not_expr(),
            SmtExpr::bv_const(1, 1),
            SmtExpr::bv_const(0, 1),
        );
        assert_invalid(
            verify_by_evaluation_with_config(&proof, &config),
            "NaN-only domain refutes plain NE",
        );
        assert_invalid(
            memoized_verify_by_evaluation(&proof, &config),
            "NaN-only memo domain",
        );
        assert_invalid(verify_fp_by_evaluation(&proof), "NaN-only direct domain");
    }
}

// Additive compatibility contract for the existing runtime reconstruction lane.
// Unlike the 24 static Wasm rows above, actual Wasm comparison instructions have
// six predicates, two operand widths, and an i32 0/1 result carrier. These are
// finite stored-model checks, not execution of a Wasm engine or source binding.
fn reconstructed_wasm_rows() -> Vec<(WasmOpcode, u32, usize, ProofObligation)> {
    let rows = [
        (WasmOpcode::F32Eq, 32, 0),
        (WasmOpcode::F32Ne, 32, 9),
        (WasmOpcode::F32Lt, 32, 2),
        (WasmOpcode::F32Gt, 32, 4),
        (WasmOpcode::F32Le, 32, 3),
        (WasmOpcode::F32Ge, 32, 5),
        (WasmOpcode::F64Eq, 64, 0),
        (WasmOpcode::F64Ne, 64, 9),
        (WasmOpcode::F64Lt, 64, 2),
        (WasmOpcode::F64Gt, 64, 4),
        (WasmOpcode::F64Le, 64, 3),
        (WasmOpcode::F64Ge, 64, 5),
    ];
    rows.into_iter()
        .map(|(opcode, width, condition)| {
            let inst = representative_reconstructable_inst(opcode)
                .expect("existing scalar Wasm comparison representative");
            assert_eq!(inst.opcode, opcode);
            assert_eq!(inst.operand_width_bits, width);
            let proof = reconstruct_alu_obligation(&inst)
                .expect("existing scalar Wasm comparison reconstruction");
            (opcode, width, condition, proof)
        })
        .collect()
}

fn reconstructed_operands(width: u32) -> (SmtExpr, SmtExpr) {
    let (eb, sb) = format(width);
    (
        SmtExpr::bv_bits_to_fp(SmtExpr::var("recon_a", width), eb, sb),
        SmtExpr::bv_bits_to_fp(SmtExpr::var("recon_b", width), eb, sb),
    )
}

fn reconstructed_environment(a: u64, b: u64) -> HashMap<String, u64> {
    HashMap::from([("recon_a".into(), a), ("recon_b".into(), b)])
}

fn assert_reconstructed_mutant_refutes(proof: &ProofObligation, width: u32, context: &str) {
    let mut witnessed = false;
    for &a in bits(width) {
        for &b in bits(width) {
            let env = reconstructed_environment(a, b);
            witnessed |= proof.trust_ir_expr.try_eval(&env).unwrap()
                != proof.aarch64_expr.try_eval(&env).unwrap();
        }
    }
    assert!(witnessed, "{context}: no concrete asymmetric/NaN witness");
    assert_invalid(finite(proof), context);
    assert_invalid(
        memoized_verify_by_evaluation(proof, &VerificationConfig::with_sample_count(16)),
        context,
    );
    assert_invalid(verify_fp_by_evaluation(proof), context);
}

#[test]
fn reconstructed_wasm_comparisons_bind_all_twelve_actual_i32_models() {
    let rows = reconstructed_wasm_rows();
    assert_eq!(rows.len(), 12);
    let mut names = HashSet::new();
    let mut checks = 0;
    for (opcode, width, condition, mut proof) in rows {
        assert!(names.insert(proof.name.clone()));
        assert_eq!(
            proof.inputs,
            vec![("recon_a".into(), width), ("recon_b".into(), width)]
        );
        assert!(proof.fp_inputs.is_empty());
        assert_eq!(proof.trust_ir_expr.sort(), SmtSort::BitVec(32));
        assert_eq!(proof.aarch64_expr.sort(), SmtSort::BitVec(32));
        assert!(matches!(
            &proof.machine_side_provenance,
            trust_cg_verify::lowering_proof::MachineSideProvenance::Reconstructed {
                from_opcode,
                arity: 2,
            } if from_opcode == &format!("{opcode:?}")
        ));
        let (eb, sb) = format(width);
        let raw = query(&proof);
        for name in ["recon_a", "recon_b"] {
            assert!(raw.contains(&format!("(declare-const {name} (_ BitVec {width}))")));
            assert!(assertion(&raw).contains(&format!("((_ to_fp {eb} {sb}) {name})")));
        }
        let mut outcomes = [0, 0];
        for &a in bits(width) {
            for &b in bits(width) {
                let expected = ieee_predicate(condition, width, a, b) as u64;
                outcomes[expected as usize] += 1;
                let env = reconstructed_environment(a, b);
                for (side, tree) in [
                    ("source", &proof.trust_ir_expr),
                    ("decoded machine", &proof.aarch64_expr),
                ] {
                    assert_eq!(
                        tree.try_eval(&env).unwrap(),
                        EvalResult::Bv(expected),
                        "{opcode:?} {side}, a={a:#x}, b={b:#x}"
                    );
                    checks += 1;
                }
            }
        }
        assert!(outcomes.into_iter().all(|count| count > 0));
        assert_valid(finite(&proof), "actual Wasm i32 carrier");
        assert_valid(
            memoized_verify_by_evaluation(&proof, &VerificationConfig::with_sample_count(16)),
            "actual Wasm i32 carrier memo",
        );
        assert_valid(
            verify_fp_by_evaluation(&proof),
            "actual Wasm i32 carrier direct",
        );
        let mut config = VerificationConfig::with_sample_count(16);
        config.exhaustive_threshold = 128;
        assert_eq!(
            VerificationStrength::for_obligation_with_config(&proof, &config),
            VerificationStrength::Statistical { sample_count: 16 }
        );
        proof.name = format!("renamed actual i32 comparison {opcode:?}");
        assert_valid(
            finite(&proof),
            "renaming cannot discard a typed i32 carrier",
        );
    }
    assert_eq!(names.len(), 12);
    assert_eq!(checks, 6_144); // 12 actual rows × 16² pairs × source/machine.
}

#[test]
fn reconstructed_wasm_wrong_decoded_byte_source_predicate_and_stack_order_refute() {
    let rows = reconstructed_wasm_rows();
    let mut mutants = 0;
    for (opcode, width, condition, proof) in &rows {
        // Reconstruct another REAL opcode of the same width, retaining the
        // original source. The public path decodes its real opcode byte; this
        // test does not fabricate a second hand-written machine predicate.
        let (wrong_opcode, _, _, decoded_wrong) = rows
            .iter()
            .find(|(_, candidate_width, candidate_condition, _)| {
                candidate_width == width && candidate_condition != condition
            })
            .unwrap();
        assert_ne!(opcode.opcode_byte(), wrong_opcode.opcode_byte());
        let mut wrong = proof.clone();
        wrong.aarch64_expr = decoded_wrong.aarch64_expr.clone();
        assert_reconstructed_mutant_refutes(&wrong, *width, "actual wrong decoded compare byte");
        mutants += 1;

        let (a, b) = reconstructed_operands(*width);
        // Specifically preserve ordered-NE versus Wasm unordered-NE as a NaN
        // discriminator. Other rows receive an independently different source.
        let wrong_cc = if *condition == 9 {
            FloatCC::NotEqual
        } else if *condition == 0 {
            FloatCC::LessThan
        } else {
            FloatCC::Equal
        };
        let mut wrong = proof.clone();
        wrong.trust_ir_expr =
            encode_trust_ir_fcmp(&wrong_cc, ty(*width), a.clone(), b.clone()).zero_ext(31);
        assert_reconstructed_mutant_refutes(&wrong, *width, "actual decoded/source-cc mismatch");
        mutants += 1;

        // Eq and unordered Ne are symmetric: a swap cannot refute those rows.
        if matches!(condition, 2..=5) {
            let predicate = match condition {
                2 => b.fp_lt(a),
                3 => b.fp_le(a),
                4 => b.fp_gt(a),
                5 => b.fp_ge(a),
                _ => unreachable!(),
            };
            let mut wrong = proof.clone();
            wrong.aarch64_expr = SmtExpr::ite(
                predicate,
                SmtExpr::bv_const(1, 32),
                SmtExpr::bv_const(0, 32),
            );
            assert_reconstructed_mutant_refutes(&wrong, *width, "asymmetric stack operand swap");
            mutants += 1;
        }
    }
    assert_eq!(mutants, 32); // 12 wrong bytes + 12 source cc + 8 asymmetric swaps.
}

#[test]
fn reconstructed_wasm_i32_carriers_refuse_malformed_and_legacy_bindings() {
    let rows = reconstructed_wasm_rows();
    let mut malformed_cases = 0;
    for width in [32, 64] {
        let (_, _, _, proof) = rows
            .iter()
            .find(|(_, w, condition, _)| *w == width && *condition == 2)
            .unwrap();
        let (eb, sb) = format(width);
        let (a, b) = reconstructed_operands(width);
        let predicate = a.clone().fp_lt(b.clone());
        let mut variants = Vec::new();

        let mut bad = proof.clone();
        bad.inputs.pop();
        variants.push(("missing input", bad));
        let mut bad = proof.clone();
        bad.inputs[1] = bad.inputs[0].clone();
        variants.push(("duplicate input", bad));
        let mut bad = proof.clone();
        bad.inputs[1].1 = if width == 32 { 64 } else { 32 };
        variants.push(("wrong declaration width", bad));

        let mut bad = proof.clone();
        let other_width = if width == 32 { 64 } else { 32 };
        let wrong_a = SmtExpr::bv_bits_to_fp(SmtExpr::var("recon_a", other_width), eb, sb);
        bad.aarch64_expr = SmtExpr::ite(
            wrong_a.fp_lt(b.clone()),
            SmtExpr::bv_const(1, 32),
            SmtExpr::bv_const(0, 32),
        );
        variants.push(("wrong raw leaf/bitcast width", bad));

        let mut bad = proof.clone();
        bad.aarch64_expr = SmtExpr::ite(
            predicate.clone(),
            SmtExpr::bv_const(2, 32),
            SmtExpr::bv_const(0, 32),
        );
        variants.push(("non-Boolean i32 machine arm", bad));
        let mut bad = proof.clone();
        bad.trust_ir_expr = SmtExpr::ite(
            predicate.clone(),
            SmtExpr::bv_const(1, 2),
            SmtExpr::bv_const(0, 2),
        )
        .zero_ext(30);
        variants.push(("BV2 is not the BV1 carrier", bad));

        let mut bad = proof.clone();
        bad.trust_ir_expr = bad.aarch64_expr.clone();
        variants.push((
            "identical arbitrary BV32 cannot bypass pair validation",
            bad,
        ));
        let mut bad = proof.clone();
        bad.aarch64_expr = bad.trust_ir_expr.clone();
        variants.push(("identical extended BV32 cannot bypass pair validation", bad));
        let mut bad = proof.clone();
        bad.trust_ir_expr = predicate.clone();
        bad.aarch64_expr = predicate;
        variants.push(("identical Bool is not a comparison carrier", bad));

        // Reproduce the former reconstruction's actual malformed shape: raw
        // BV Vars used directly as FP operands, with only FP metadata binding.
        let mut bad = proof.clone();
        let old_a = SmtExpr::var("recon_a", width);
        let old_b = SmtExpr::var("recon_b", width);
        bad.inputs.clear();
        bad.fp_inputs = vec![("recon_a".into(), eb, sb), ("recon_b".into(), eb, sb)];
        bad.trust_ir_expr =
            encode_trust_ir_fcmp(&FloatCC::LessThan, ty(width), old_a.clone(), old_b.clone())
                .zero_ext(31);
        bad.aarch64_expr = SmtExpr::ite(
            old_a.fp_lt(old_b),
            SmtExpr::bv_const(1, 32),
            SmtExpr::bv_const(0, 32),
        );
        variants.push(("legacy unbound reconstruction", bad));

        let mut bad = proof.clone();
        bad.preconditions = vec![SmtExpr::BoolConst(false)];
        variants.push(("empty actual i32 domain", bad));
        let mut bad = proof.clone();
        bad.preconditions =
            vec![SmtExpr::var("unresolved", width).eq_expr(SmtExpr::bv_const(0, width))];
        variants.push(("unresolved actual i32 precondition", bad));

        assert_eq!(variants.len(), 12);
        for (context, mut bad) in variants {
            bad.name = format!("renamed i32 rejection {width}: {context}");
            assert_rejected_without_panic(&bad, context);
            malformed_cases += 1;
        }
    }
    assert_eq!(malformed_cases, 24); // Three entry points: 72 Unknown checks.

    for (opcode, width, _, _) in rows {
        for invalid_width in [0, 16, 128, if width == 32 { 64 } else { 32 }] {
            assert!(
                reconstruct_alu_obligation(&WasmISelInst::new(opcode, invalid_width)).is_none(),
                "{opcode:?} must reject mismatched operand width {invalid_width}"
            );
        }
    }
}
