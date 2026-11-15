// trust-cg-eqsat-check/tests/registry.rs - rule-file parsing, well-formedness refusals, canonical text and digest
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! docs/eqsat-tier-e.md section 5: a realistic rule file is accepted; each
//! well-formedness clause, broken alone, is refused; canonical text and the
//! statement digest follow section 5.2.

use trust_cg_eqsat_check::Registry;

const REALISTIC: &str = "\
; a rule file in the style of the engine's data file, written for this test

(rule add_const_right
  (direction equiv)
  (domain i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize)
  (lhs (add (const ?c) ?x))   ; constants to the right
  (rhs (add ?x (const ?c)))
  (where))

(rule mul_zero
  (direction refines)
  (domain i8 u8 i64)
  (lhs (mul ?x (const 0)))
  (rhs (const 0))
  (where))

(rule sub_const_to_add
  (direction equiv)
  (domain i32 u32)
  (lhs (sub ?x (const ?c)))
  (rhs (add ?x (eval neg ?c)))
  (where (ne ?c 0)))

(rule rotl_full
  (direction equiv)
  (domain u8 u16 u32 u64)
  (lhs (rotl ?x (const ?c)))
  (rhs ?x)
  (where (zero_mod_width ?c)))

(rule mul_pow2_marker
  (direction equiv)
  (domain u32)
  (lhs (mul ?x (const ?c)))
  (rhs (mul ?x ?c))
  (where (pow2 ?c) (eq ?c 4)))

(rule select_same
  (direction equiv)
  (domain i8 u64 bool)
  (lhs (select ?c ?x ?x))
  (rhs ?x)
  (where))

(rule select_true
  (direction equiv)
  (domain u32 bool)
  (lhs (select true ?x ?y))
  (rhs ?x)
  (where))

(rule icmp_eq_self
  (direction equiv)
  (domain u32 bool)
  (lhs (icmp.eq ?x ?x))
  (rhs true)
  (where))

(rule band_true
  (direction equiv)
  (domain bool)
  (lhs (band ?b true))
  (rhs ?b)
  (where))

(rule fold_and
  (direction equiv)
  (domain u16 bool)
  (lhs (and (const ?a) (const ?b)))
  (rhs (eval and ?a ?b))
  (where))

(rule fold_cmp
  (direction equiv)
  (domain i32)
  (lhs (icmp.slt (const ?a) (const ?b)))
  (rhs (eval icmp.slt ?a ?b))
  (where))

(rule neg_neg
  (direction equiv)
  (domain i8 i16 i32 i64 i128)
  (lhs (neg (neg ?x)))
  (rhs ?x)
  (where))

(rule wide_constants
  (direction equiv)
  (domain u128)
  (lhs (and ?x (const 340282366920938463463374607431768211455)))
  (rhs (and ?x (const -170141183460469231731687303715884105728)))
  (where))
";

#[test]
fn realistic_rule_file_is_accepted() {
    let reg = Registry::parse(REALISTIC).expect("accepted");
    assert_eq!(reg.len(), 13);
    assert!(!reg.is_empty());
    assert_eq!(reg.names()[0], "add_const_right");
    assert_eq!(reg.names()[12], "wide_constants");
    assert!(reg.statement_digest("rotl_full").is_some());
    assert!(reg.statement_digest("nope").is_none());
    assert!(reg.canonical_text("nope").is_none());
}

#[test]
fn empty_file_is_an_empty_registry() {
    let reg = Registry::parse("; nothing here\n").expect("accepted");
    assert_eq!(reg.len(), 0);
    assert!(reg.is_empty());
}

#[test]
fn canonical_text_and_digest() {
    let text = "(rule   mul_one ; a comment ( ) here\n\
                \t(direction equiv)\n\
                (domain u32 i32)\n\
                ( lhs ( mul ?x (const 0001) ) )\n\
                (rhs ?x)\n\
                (where ) )";
    let reg = Registry::parse(text).expect("accepted");
    let canonical = reg.canonical_text("mul_one").expect("present");
    assert_eq!(
        canonical,
        "(rule mul_one (direction equiv) (domain u32 i32) (lhs (mul ?x (const 1))) (rhs ?x) (where))"
    );
    let expected = trust_ir::ProofDigest::sha256_domain(
        "trust-cg-eqsat.rule-statement.v1",
        canonical.as_bytes(),
    )
    .bytes;
    assert_eq!(reg.statement_digest("mul_one"), Some(expected));

    // Same statement, different layout: same digest.
    let tidy = Registry::parse(&canonical).expect("accepted");
    assert_eq!(tidy.statement_digest("mul_one"), Some(expected));

    // A different statement: a different digest.
    let other = Registry::parse(&canonical.replace("(const 1)", "(const 2)")).expect("accepted");
    assert_ne!(other.statement_digest("mul_one"), Some(expected));
}

#[test]
fn canonical_integers() {
    let reg = Registry::parse(
        "(rule r (direction equiv) (domain i32) (lhs (add ?x (const -0))) (rhs (add ?x (const 000))) (where))\n\
         (rule s (direction equiv) (domain i32) (lhs (sub ?x (const ?c))) (rhs ?x) (where (eq ?c -0012)))",
    )
    .expect("accepted");
    assert_eq!(
        reg.canonical_text("r").as_deref(),
        Some(
            "(rule r (direction equiv) (domain i32) (lhs (add ?x (const 0))) (rhs (add ?x (const 0))) (where))"
        )
    );
    assert_eq!(
        reg.canonical_text("s").as_deref(),
        Some(
            "(rule s (direction equiv) (domain i32) (lhs (sub ?x (const ?c))) (rhs ?x) (where (eq ?c -12)))"
        )
    );
}

fn refused(rule_text: &str) -> String {
    match Registry::parse(rule_text) {
        Ok(r) => panic!("accepted a malformed rule ({} rules): {rule_text}", r.len()),
        Err(e) => e.to_string(),
    }
}

/// A rule with the given clauses.
fn mk(name: &str, dir: &str, domain: &str, lhs: &str, rhs: &str, wh: &str) -> String {
    format!("(rule {name} (direction {dir}) (domain {domain}) (lhs {lhs}) (rhs {rhs}) (where{wh}))")
}

fn good() -> String {
    mk("ok", "equiv", "u32", "(add ?x (const 0))", "?x", "")
}

#[test]
fn baseline_is_accepted() {
    assert!(Registry::parse(&good()).is_ok());
}

#[test]
fn refuses_syntax_faults() {
    refused("(rule");
    refused("(rule ok (direction equiv) (domain u32) (lhs (add ?x (const 0))) (rhs ?x) (where)))");
    refused("rule");
    refused("(notrule ok)");
    refused(&format!("{} {}", good(), good())); // duplicate name
    refused(
        "(rule ok (direction equiv) (domain u32) (lhs (add ?x (const 0))) (rhs ?x) (where) (extra))",
    );
    refused("(rule ok (direction equiv) (domain u32) (lhs (add ?x (const 0))) (rhs ?x))");
    refused("(rule ok (domain u32) (direction equiv) (lhs (add ?x (const 0))) (rhs ?x) (where))");
    refused("(rule ok (direction equiv) (domain u32) (rhs ?x) (lhs (add ?x (const 0))) (where))");
    refused(
        "(rule ok (direction equiv) (domain u32) (lhs (add ?x (const 0))) (rhs ?x) (where) ) \u{00e9}",
    );
    let deep = format!("{}{}", "(".repeat(200), ")".repeat(200));
    refused(&deep);
}

#[test]
fn refuses_bad_names() {
    refused(&mk("Bad", "equiv", "u32", "(add ?x (const 0))", "?x", ""));
    refused(&mk("1bad", "equiv", "u32", "(add ?x (const 0))", "?x", ""));
    refused(&mk("ok", "equiv", "u32", "(add ?X (const 0))", "?X", ""));
    refused(&mk("ok", "equiv", "u32", "(add ? (const 0))", "?x", ""));
}

#[test]
fn refuses_bad_direction() {
    refused(&mk("ok", "both", "u32", "(add ?x (const 0))", "?x", ""));
    refused(
        "(rule ok (direction equiv refines) (domain u32) (lhs (add ?x (const 0))) (rhs ?x) (where))",
    );
}

#[test]
fn refuses_bad_domains() {
    refused(&mk("ok", "equiv", "", "(add ?x (const 0))", "?x", ""));
    refused(&mk(
        "ok",
        "equiv",
        "u32 u32",
        "(add ?x (const 0))",
        "?x",
        "",
    ));
    refused(&mk("ok", "equiv", "u33", "(add ?x (const 0))", "?x", ""));
    refused(&mk("ok", "equiv", "char", "(add ?x (const 0))", "?x", ""));
    refused(&mk("ok", "equiv", "f32", "(add ?x (const 0))", "?x", ""));
}

#[test]
fn refuses_non_total_operators() {
    for op in ["udiv", "sdiv", "urem", "srem", "shl", "lshr", "ashr"] {
        let msg = refused(&mk(
            "ok",
            "equiv",
            "u32",
            &format!("({op} ?x (const 1))"),
            "?x",
            "",
        ));
        assert!(msg.contains("not total"), "{op}: {msg}");
        // Also refused on the rhs and inside eval.
        refused(&mk(
            "ok",
            "equiv",
            "u32",
            "(add ?x ?y)",
            &format!("({op} ?x ?y)"),
            "",
        ));
        refused(&mk(
            "ok",
            "equiv",
            "u32",
            "(add (const ?a) (const ?b))",
            &format!("(eval {op} ?a ?b)"),
            "",
        ));
    }
    refused(&mk("ok", "equiv", "u32", "(frob ?x)", "?x", ""));
}

#[test]
fn refuses_lhs_root_that_is_not_an_operator() {
    refused(&mk("ok", "equiv", "u32", "?x", "?x", ""));
    refused(&mk("ok", "equiv", "u32", "(const 1)", "(const 1)", ""));
    refused(&mk("ok", "equiv", "bool", "true", "true", ""));
}

#[test]
fn refuses_eval_outside_the_rhs() {
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add (eval add ?a ?b) ?x)",
        "?x",
        "",
    ));
}

#[test]
fn refuses_bad_arity() {
    refused(&mk("ok", "equiv", "u32", "(add ?x)", "?x", ""));
    refused(&mk("ok", "equiv", "u32", "(neg ?x ?y)", "?x", ""));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add (const ?a) (const ?b))",
        "(eval add ?a)",
        "",
    ));
    refused(&mk("ok", "equiv", "u32", "(add ?x (const 1 2))", "?x", ""));
}

#[test]
fn refuses_variable_with_two_sorts() {
    // ?x is T (add) and bool (select condition).
    refused(&mk("ok", "equiv", "u32", "(select ?x ?x ?x)", "?x", ""));
}

#[test]
fn refuses_sort_mismatches() {
    // true at a T position; (const INT) at a bool position; lhs/rhs sorts.
    refused(&mk("ok", "equiv", "u32", "(add ?x true)", "?x", ""));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(select (const 1) ?x ?x)",
        "?x",
        "",
    ));
    refused(&mk("ok", "equiv", "u32", "(icmp.eq ?x ?x)", "?x", ""));
    refused(&mk("ok", "equiv", "u32", "(add ?x ?x)", "true", ""));
}

#[test]
fn refuses_constant_and_term_variable_mix() {
    refused(&mk("ok", "equiv", "u32", "(add ?c (const ?c))", "?c", ""));
    // (const ?x) in the rhs for a term variable.
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add ?x ?y)",
        "(add (const ?x) ?y)",
        "",
    ));
}

#[test]
fn refuses_rhs_variable_not_in_lhs() {
    refused(&mk("ok", "equiv", "u32", "(add ?x ?x)", "?y", ""));
    refused(&mk("ok", "equiv", "u32", "(add ?x ?x)", "(const ?c)", ""));
}

#[test]
fn refuses_bad_eval_arguments() {
    // A term variable, and a variable of the wrong sort.
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add ?x ?y)",
        "(eval add ?x ?y)",
        "",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(select (const ?b) (const ?a) (const ?a))",
        "(eval add ?b ?a)",
        "",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add (const ?a) (const ?b))",
        "(eval add ?a (const 1))",
        "",
    ));
}

#[test]
fn refuses_bad_where_clauses() {
    // Not a constant variable; not in the lhs; bool sort; bool domain.
    refused(&mk("ok", "equiv", "u32", "(add ?x ?y)", "?x", " (eq ?y 0)"));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add ?x (const ?c))",
        "?x",
        " (eq ?d 0)",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(select (const ?b) ?x ?x)",
        "?x",
        " (pow2 ?b)",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "u32 bool",
        "(and ?x (const ?c))",
        "?x",
        " (eq ?c 0)",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add ?x (const ?c))",
        "?x",
        " (lt ?c 0)",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add ?x (const ?c))",
        "?x",
        " (eq ?c x)",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add ?x (const ?c))",
        "?x",
        " (pow2 ?c 1)",
    ));
}

#[test]
fn refuses_operator_not_admitted_at_a_domain_type() {
    refused(&mk(
        "ok",
        "equiv",
        "u32 bool",
        "(add ?x ?x)",
        "(add ?x ?x)",
        "",
    ));
    refused(&mk("ok", "equiv", "bool", "(neg ?x)", "(neg ?x)", ""));
    refused(&mk("ok", "equiv", "bool", "(icmp.ult ?x ?x)", "false", ""));
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(and ?x ?x)",
        "(eval neg ?x)",
        "",
    ));
}

#[test]
fn refuses_const_int_at_bool() {
    refused(&mk("ok", "equiv", "bool", "(and ?x (const 1))", "?x", ""));
}

#[test]
fn refuses_int_out_of_range() {
    refused(&mk(
        "ok",
        "equiv",
        "u128",
        "(and ?x (const 340282366920938463463374607431768211456))",
        "?x",
        "",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "i128",
        "(and ?x (const -170141183460469231731687303715884105729))",
        "?x",
        "",
    ));
    refused(&mk("ok", "equiv", "u32", "(and ?x (const +1))", "?x", ""));
    refused(&mk("ok", "equiv", "u32", "(and ?x (const 1x))", "?x", ""));
}

#[test]
fn refuses_eval_select() {
    // Section 5.1: eval's OP is not select (it has no single operand sort).
    let msg = refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(select (const ?c) (const ?a) (const ?b))",
        "(eval select ?c ?a ?b)",
        "",
    ));
    assert!(msg.contains("eval select"), "{msg}");
    // The same fold without eval is admitted.
    assert!(
        Registry::parse(&mk(
            "ok",
            "equiv",
            "u32",
            "(select (const ?c) (const ?a) (const ?b))",
            "(select ?c ?a ?b)",
            "",
        ))
        .is_ok()
    );
}

/// `(rule r ... (lhs (not (not ... ?x))) ...)` with `nots` nested `not`s: the
/// deepest list is at depth `nots + 2`.
fn nested(nots: usize) -> String {
    let lhs = format!("{}?x{}", "(not ".repeat(nots), ")".repeat(nots));
    mk("r", "equiv", "u32", &lhs, "?x", "")
}

#[test]
fn nesting_bound_is_64_lists() {
    let reg = Registry::parse(&nested(62)).expect("depth 64 accepted");
    assert_eq!(reg.len(), 1);
    let msg = refused(&nested(63));
    assert!(msg.contains("nesting deeper than 64"), "{msg}");
}

#[test]
fn whitespace_and_characters() {
    // Space, tab, LF, CR and FF separate tokens.
    let spaced = good().replace(' ', "\t\r\n\x0c ");
    let reg = Registry::parse(&spaced).expect("accepted");
    assert_eq!(
        reg.canonical_text("ok").as_deref(),
        Some("(rule ok (direction equiv) (domain u32) (lhs (add ?x (const 0))) (rhs ?x) (where))")
    );
    // Any other control character, DEL or a non-ASCII character outside a
    // comment is refused.
    for bad in ["\x0b", "\x00", "\x7f", "\u{00a0}", "\u{2003}"] {
        let msg = refused(&format!("{}{bad}", good()));
        assert!(msg.contains("outside a comment"), "{bad:?}: {msg}");
        refused(&good().replacen(' ', bad, 1));
    }
    // Inside a comment they are allowed.
    let commented = format!("; r\u{00e9}gle \x0b\x7f\n{}", good());
    assert!(Registry::parse(&commented).is_ok());
}

#[test]
fn empty_files_are_empty_registries() {
    for text in ["", " \t\r\n\x0c", ";;\n; only comments"] {
        let reg = Registry::parse(text).expect("accepted");
        assert!(reg.is_empty(), "{text:?}");
    }
}

#[test]
fn sorts_are_symbolic_even_when_bool_is_in_the_domain() {
    // At T = Bool `(and ?x true)` would be well typed; symbolically `true`
    // stands at a T position.
    refused(&mk("ok", "equiv", "bool", "(and ?x true)", "?x", ""));
    refused(&mk("ok", "equiv", "bool u32", "(xor ?x ?x)", "false", ""));
    // `(const ?c)` takes the sort of its position, bool included.
    assert!(
        Registry::parse(&mk(
            "ok",
            "equiv",
            "bool",
            "(band ?x (const ?c))",
            "(band ?c ?x)",
            "",
        ))
        .is_ok()
    );
    // band/bor/bxor are bool-sorted whatever the domain: (const INT) under
    // one stands at a bool position.
    refused(&mk("ok", "equiv", "u32", "(band ?x (const 1))", "?x", ""));
}

#[test]
fn bool_domains_have_no_const_int_and_no_where() {
    // (const INT) anywhere, at a T position, is refused when bool is in the
    // domain: in the lhs and in the rhs.
    refused(&mk(
        "ok",
        "equiv",
        "u32 bool",
        "(and ?x (const 0))",
        "(const 0)",
        "",
    ));
    refused(&mk(
        "ok",
        "equiv",
        "bool u32",
        "(xor ?x ?x)",
        "(const 0)",
        "",
    ));
    // A where condition is refused when bool is in the domain, even over a
    // constant variable of sort T.
    refused(&mk(
        "ok",
        "equiv",
        "bool u32",
        "(and ?x (const ?c))",
        "?x",
        " (pow2 ?c)",
    ));
}

#[test]
fn constant_and_term_variables_never_mix_anywhere_in_the_rule() {
    // Term variable in the lhs, `(const ?x)` in the rhs.
    refused(&mk("ok", "equiv", "u32", "(add ?x ?x)", "(const ?x)", ""));
    // Term variable used as a where variable.
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add ?x ?y)",
        "?y",
        " (zero_mod_width ?x)",
    ));
    // Term variable used as an eval argument.
    refused(&mk(
        "ok",
        "equiv",
        "u32",
        "(add ?x (const ?c))",
        "(eval add ?x ?c)",
        "",
    ));
    // A constant variable may stand bare or as (const ?c) in the rhs.
    for rhs in ["(add ?c ?x)", "(add (const ?c) ?x)"] {
        assert!(
            Registry::parse(&mk("ok", "equiv", "u32", "(add ?x (const ?c))", rhs, "")).is_ok(),
            "{rhs}"
        );
    }
}
