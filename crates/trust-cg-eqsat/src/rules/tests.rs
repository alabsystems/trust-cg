// crates/trust-cg-eqsat/src/rules/tests.rs - rule parser, well-formedness, canonical text and digest tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! One test per well-formedness clause of section 5.1, the canonical text of
//! section 5.2, and the statement digest's exact construction.

use super::*;

fn rule_text(direction: &str, domain: &str, lhs: &str, rhs: &str, conds: &str) -> String {
    format!(
        "(rule r\n  (direction {direction})\n  (domain {domain})\n  (lhs {lhs})\n  (rhs {rhs})\n  (where {conds}))\n"
    )
}

fn refused(text: &str) -> RuleErrorKind {
    match RuleSet::parse(text) {
        Ok(_) => panic!("accepted:\n{text}"),
        Err(error) => {
            // Display carries the kind name.
            assert!(error.to_string().contains(error.kind.as_str()));
            error.kind
        }
    }
}

fn refused_rule(direction: &str, domain: &str, lhs: &str, rhs: &str, conds: &str) -> RuleErrorKind {
    refused(&rule_text(direction, domain, lhs, rhs, conds))
}

#[test]
fn every_integer_identity_parses() {
    let set = RuleSet::parse(INTEGER_IDENTITIES).expect("integer identities parse");
    let names: Vec<&str> = set.rules().iter().map(Rule::name).collect();
    assert!(names.len() >= 60, "{} rules", names.len());
    assert_eq!(names.first(), Some(&"add_const_right"));
    let texts = canonical_texts(INTEGER_IDENTITIES).expect("syntax");
    assert_eq!(texts.len(), names.len());
    for (rule, (name, text)) in set.rules().iter().zip(&texts) {
        assert_eq!(rule.name(), name);
        assert_eq!(rule.canonical_text(), text);
        assert_eq!(rule.statement_digest(), statement_digest(text));
    }
    let mul_zero = set
        .rules()
        .iter()
        .find(|r| r.name() == "mul_zero")
        .expect("mul_zero");
    assert!(!mul_zero.is_equiv());
    let rotl_full = set
        .rules()
        .iter()
        .find(|r| r.name() == "rotl_full")
        .expect("rotl_full");
    assert_eq!(rotl_full.side_condition_count(), 1);
    assert!(rotl_full.is_equiv());
}

#[test]
fn mutant_files_parse_or_refuse_by_clause() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/wrong_rules");
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .expect("wrong_rules dir")
        .map(|e| e.expect("entry").path())
        .collect();
    entries.sort();
    assert!(!entries.is_empty());
    for path in entries {
        let text = std::fs::read_to_string(&path).expect("read");
        // Syntax-only canonicalization always works.
        let texts = canonical_texts(&text).expect("syntax");
        assert_eq!(texts.len(), 1, "{}", path.display());
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        match RuleSet::parse(&text) {
            Ok(set) => {
                assert!(!name.starts_with("panic_only"), "{name} accepted");
                assert_eq!(set.rules().len(), 1);
            }
            Err(error) => {
                assert!(name.starts_with("panic_only"), "{name}: {error}");
                assert_eq!(error.kind, RuleErrorKind::NonTotalOperator);
            }
        }
    }
}

#[test]
fn canonical_text_examples() {
    let source = "; comment\n(rule  add_zero ; trailing\n (direction equiv)\n\t(domain i8\n u8)\n (lhs (add ?x (const 000)))\n (rhs ?x)\n (where))";
    let texts = canonical_texts(source).expect("syntax");
    assert_eq!(
        texts,
        vec![(
            "add_zero".to_owned(),
            "(rule add_zero (direction equiv) (domain i8 u8) (lhs (add ?x (const 0))) (rhs ?x) (where))"
                .to_owned()
        )]
    );
    let negative = canonical_texts(
        "(rule m (direction equiv) (domain i8) (lhs (mul ?x (const -0001))) (rhs (neg ?x)) (where (ne ?x -0)))",
    )
    .expect("syntax");
    assert_eq!(
        negative[0].1,
        "(rule m (direction equiv) (domain i8) (lhs (mul ?x (const -1))) (rhs (neg ?x)) (where (ne ?x 0)))"
    );
    // A refused rule still has a canonical text and a digest.
    let refused = canonical_texts(
        "(rule u (direction equiv) (domain u8) (lhs (udiv ?x ?x)) (rhs (const 1)) (where))",
    )
    .expect("syntax only");
    assert_eq!(refused[0].0, "u");
    assert_eq!(statement_digest(&refused[0].1).len(), 32);
    // Not a rule form.
    assert_eq!(
        canonical_texts("(rules x)").map_err(|e| e.kind),
        Err(RuleErrorKind::Structure)
    );
    assert_eq!(
        canonical_texts("(rule x").map_err(|e| e.kind),
        Err(RuleErrorKind::Syntax)
    );
    assert_eq!(
        canonical_texts("(rule x))").map_err(|e| e.kind),
        Err(RuleErrorKind::Syntax)
    );
}

#[test]
fn statement_digest_is_the_domain_separated_sha256() {
    let text =
        "(rule add_zero (direction equiv) (domain i8) (lhs (add ?x (const 0))) (rhs ?x) (where))";
    let expected =
        trust_ir::ProofDigest::sha256_domain("trust-cg-eqsat.rule-statement.v1", text.as_bytes())
            .bytes;
    assert_eq!(statement_digest(text), expected);
    assert_ne!(
        statement_digest(text),
        trust_ir::ProofDigest::sha256_domain("other", text.as_bytes()).bytes
    );
    let set = RuleSet::parse(text).expect("parse");
    assert_eq!(set.rules()[0].statement_digest(), expected);
}

#[test]
fn refuses_lexical_and_structure_errors() {
    assert_eq!(refused("(rule r é)"), RuleErrorKind::Syntax);
    assert_eq!(refused("(rule r (direction equiv)"), RuleErrorKind::Syntax);
    assert_eq!(refused("rule"), RuleErrorKind::Structure);
    assert_eq!(
        refused("(rule r (direction equiv) (domain i8) (lhs (add ?x ?x)) (rhs ?x))"),
        RuleErrorKind::Structure
    );
    assert_eq!(
        refused("(rule r (domain i8) (direction equiv) (lhs (add ?x ?x)) (rhs ?x) (where))"),
        RuleErrorKind::Structure
    );
    assert_eq!(
        refused("(rule r (direction equiv) (domain i8) (lhs (add ?x ?x) ?x) (rhs ?x) (where))"),
        RuleErrorKind::Structure
    );
}

#[test]
fn refuses_bad_and_duplicate_names() {
    assert_eq!(
        refused("(rule Bad (direction equiv) (domain i8) (lhs (and ?x ?x)) (rhs ?x) (where))"),
        RuleErrorKind::BadName
    );
    assert_eq!(
        refused("(rule 1r (direction equiv) (domain i8) (lhs (and ?x ?x)) (rhs ?x) (where))"),
        RuleErrorKind::BadName
    );
    let one = rule_text("equiv", "i8", "(and ?x ?x)", "?x", "");
    assert_eq!(
        refused(&format!("{one}{one}")),
        RuleErrorKind::DuplicateName
    );
}

#[test]
fn refuses_bad_direction() {
    assert_eq!(
        refused_rule("both", "i8", "(and ?x ?x)", "?x", ""),
        RuleErrorKind::BadDirection
    );
}

#[test]
fn refuses_bad_domains() {
    assert_eq!(
        refused_rule("equiv", "", "(and ?x ?x)", "?x", ""),
        RuleErrorKind::EmptyDomain
    );
    assert_eq!(
        refused_rule("equiv", "i8 char", "(and ?x ?x)", "?x", ""),
        RuleErrorKind::BadType
    );
    assert_eq!(
        refused_rule("equiv", "i8 u8 i8", "(and ?x ?x)", "?x", ""),
        RuleErrorKind::RepeatedType
    );
}

#[test]
fn refuses_bad_patterns() {
    assert_eq!(
        refused_rule("equiv", "i8", "(and ?x x)", "?x", ""),
        RuleErrorKind::BadPattern
    );
    assert_eq!(
        refused_rule("equiv", "i8", "(and ?x ?X)", "?x", ""),
        RuleErrorKind::BadPattern
    );
    assert_eq!(
        refused_rule("equiv", "i8", "(and ?x 5)", "?x", ""),
        RuleErrorKind::BadPattern
    );
    assert_eq!(
        refused_rule("equiv", "i8", "(and ?x (const))", "?x", ""),
        RuleErrorKind::BadPattern
    );
    assert_eq!(
        refused_rule("equiv", "i8", "(and ?x ())", "?x", ""),
        RuleErrorKind::BadPattern
    );
}

#[test]
fn refuses_unknown_and_non_total_operators() {
    assert_eq!(
        refused_rule("equiv", "i8", "(frob ?x ?x)", "?x", ""),
        RuleErrorKind::UnknownOperator
    );
    for op in ["udiv", "sdiv", "urem", "srem", "shl", "lshr", "ashr"] {
        assert_eq!(
            refused_rule("equiv", "u32", &format!("({op} ?x ?y)"), "?x", ""),
            RuleErrorKind::NonTotalOperator,
            "{op}"
        );
        // Also refused nested, in the rhs and under eval.
        assert_eq!(
            refused_rule("equiv", "u32", "(add ?x ?y)", &format!("({op} ?x ?y)"), ""),
            RuleErrorKind::NonTotalOperator,
            "{op} in rhs"
        );
        assert_eq!(
            refused_rule(
                "equiv",
                "u32",
                "(add (const ?a) (const ?b))",
                &format!("(eval {op} ?a ?b)"),
                ""
            ),
            RuleErrorKind::NonTotalOperator,
            "{op} in eval"
        );
    }
}

#[test]
fn refuses_wrong_arity() {
    assert_eq!(
        refused_rule("equiv", "i8", "(add ?x)", "?x", ""),
        RuleErrorKind::Arity
    );
    assert_eq!(
        refused_rule("equiv", "i8", "(neg ?x ?x)", "?x", ""),
        RuleErrorKind::Arity
    );
    assert_eq!(
        refused_rule(
            "equiv",
            "i8",
            "(add (const ?a) (const ?b))",
            "(eval add ?a)",
            ""
        ),
        RuleErrorKind::Arity
    );
}

#[test]
fn refuses_lhs_root_that_is_not_an_operator() {
    assert_eq!(
        refused_rule("equiv", "i8", "?x", "?x", ""),
        RuleErrorKind::LhsRootNotOperator
    );
    assert_eq!(
        refused_rule("equiv", "i8", "(const 1)", "(const 1)", ""),
        RuleErrorKind::LhsRootNotOperator
    );
    assert_eq!(
        refused_rule("equiv", "bool", "true", "true", ""),
        RuleErrorKind::LhsRootNotOperator
    );
}

#[test]
fn refuses_eval_in_lhs() {
    assert_eq!(
        refused_rule("equiv", "i8", "(add (eval neg ?c) ?x)", "?x", ""),
        RuleErrorKind::EvalInLhs
    );
}

#[test]
fn refuses_integers_out_of_range() {
    let max = "340282366920938463463374607431768211455";
    let min = "-170141183460469231731687303715884105728";
    assert!(
        RuleSet::parse(&rule_text(
            "equiv",
            "u128",
            &format!("(and ?x (const {max}))"),
            "?x",
            ""
        ))
        .is_ok()
    );
    assert!(
        RuleSet::parse(&rule_text(
            "equiv",
            "i128",
            &format!("(and ?x (const {min}))"),
            "?x",
            ""
        ))
        .is_ok()
    );
    assert_eq!(
        refused_rule(
            "equiv",
            "u128",
            "(and ?x (const 340282366920938463463374607431768211456))",
            "?x",
            ""
        ),
        RuleErrorKind::IntOutOfRange
    );
    assert_eq!(
        refused_rule(
            "equiv",
            "i128",
            "(and ?x (const -170141183460469231731687303715884105729))",
            "?x",
            ""
        ),
        RuleErrorKind::IntOutOfRange
    );
}

#[test]
fn refuses_sort_conflicts() {
    // A variable at two sorts.
    assert_eq!(
        refused_rule("equiv", "i8", "(select ?c ?c ?x)", "?x", ""),
        RuleErrorKind::SortConflict
    );
    // lhs and rhs of different sorts.
    assert_eq!(
        refused_rule("equiv", "i8", "(icmp.eq ?x ?y)", "?x", ""),
        RuleErrorKind::SortConflict
    );
    // A boolean literal at sort T.
    assert_eq!(
        refused_rule("equiv", "i8", "(and ?x ?y)", "true", ""),
        RuleErrorKind::SortConflict
    );
}

#[test]
fn refuses_mixed_variables() {
    // Constant and term variable in the lhs.
    assert_eq!(
        refused_rule("equiv", "i8", "(add (const ?c) ?c)", "?c", ""),
        RuleErrorKind::MixedVariable
    );
    // `(const ?x)` in the rhs of a term variable.
    assert_eq!(
        refused_rule("equiv", "i8", "(add ?x ?x)", "(const ?x)", ""),
        RuleErrorKind::MixedVariable
    );
}

#[test]
fn refuses_rhs_variable_not_in_lhs() {
    assert_eq!(
        refused_rule("equiv", "i8", "(add ?x ?x)", "?y", ""),
        RuleErrorKind::RhsVariableNotInLhs
    );
}

#[test]
fn refuses_bad_eval_arguments() {
    // A term variable under eval.
    assert_eq!(
        refused_rule("equiv", "i8", "(add ?x ?y)", "(eval add ?x ?y)", ""),
        RuleErrorKind::EvalArgument
    );
    // eval select has no single operand sort.
    assert_eq!(
        refused_rule(
            "equiv",
            "i8",
            "(select (const ?c) (const ?a) (const ?b))",
            "(eval select ?c ?a ?b)",
            ""
        ),
        RuleErrorKind::EvalArgument
    );
    // An eval argument at the wrong sort.
    assert_eq!(
        refused_rule(
            "equiv",
            "i8",
            "(select (const ?c) (const ?a) (const ?b))",
            "(eval add ?c ?a)",
            ""
        ),
        RuleErrorKind::SortConflict
    );
}

#[test]
fn refuses_bad_condition_variables() {
    // A term variable in `where`.
    assert_eq!(
        refused_rule("equiv", "i8", "(add ?x ?y)", "?x", "(eq ?y 0)"),
        RuleErrorKind::ConditionVariable
    );
    // A constant variable of sort bool.
    assert_eq!(
        refused_rule(
            "equiv",
            "i8",
            "(select (const ?c) ?x ?y)",
            "?x",
            "(eq ?c 1)"
        ),
        RuleErrorKind::ConditionVariable
    );
    // A condition in a rule whose domain contains bool.
    assert_eq!(
        refused_rule("equiv", "i8 bool", "(and ?x (const ?c))", "?x", "(pow2 ?c)"),
        RuleErrorKind::ConditionVariable
    );
    // A variable that is not in the lhs.
    assert_eq!(
        refused_rule("equiv", "i8", "(and ?x (const ?c))", "?x", "(pow2 ?d)"),
        RuleErrorKind::ConditionVariable
    );
    // A malformed condition.
    assert_eq!(
        refused_rule("equiv", "i8", "(and ?x (const ?c))", "?x", "(odd ?c)"),
        RuleErrorKind::BadPattern
    );
}

#[test]
fn refuses_const_int_at_bool() {
    assert_eq!(
        refused_rule("equiv", "bool", "(and ?x (const 1))", "?x", ""),
        RuleErrorKind::ConstAtBool
    );
    assert_eq!(
        refused_rule("equiv", "i8", "(select (const 1) ?x ?y)", "?x", ""),
        RuleErrorKind::ConstAtBool
    );
}

#[test]
fn refuses_operators_not_admitted_at_a_domain_type() {
    assert_eq!(
        refused_rule("equiv", "i8 bool", "(add ?x (const ?c))", "?x", ""),
        RuleErrorKind::OperatorNotAdmitted
    );
    assert_eq!(
        refused_rule("equiv", "bool", "(icmp.ult ?x ?x)", "false", ""),
        RuleErrorKind::OperatorNotAdmitted
    );
    assert_eq!(
        refused_rule("equiv", "bool", "(neg (neg ?x))", "?x", ""),
        RuleErrorKind::OperatorNotAdmitted
    );
}

#[test]
fn accepts_the_spec_forms() {
    // `(const ?c)` at bool, eval at bool, true/false, a refines rule.
    let text = "(rule a (direction equiv) (domain bool) (lhs (band (const ?a) (const ?b))) (rhs (eval band ?a ?b)) (where))\n\
                (rule b (direction refines) (domain i8 u8) (lhs (mul ?x (const 0))) (rhs (const 0)) (where))\n\
                (rule c (direction equiv) (domain u16) (lhs (sub ?x (const ?c))) (rhs (add ?x (eval neg ?c))) (where (ne ?c 0) (pow2 ?c) (zero_mod_width ?c) (eq ?c 16)))\n\
                (rule d (direction equiv) (domain i32) (lhs (select false ?x ?y)) (rhs ?y) (where))";
    let set = RuleSet::parse(text).expect("parse");
    assert_eq!(set.rules().len(), 4);
    assert!(!set.rules()[1].is_equiv());
    assert_eq!(set.rules()[2].side_condition_count(), 4);
}
