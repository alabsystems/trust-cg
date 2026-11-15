// crates/trust-cg-eqsat/tests/cross_conformance.rs - the engine and the checker read the contract alike
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Agreement between the two independent readers of docs/eqsat-tier-e.md:
//! the engine (`trust-cg-eqsat`) and the checker (`trust-cg-eqsat-check`),
//! and, where trust-ir has a verdict, its validator and reference
//! interpreter at the pinned revision. Each case puts one input through
//! both crates and asserts the same verdict:
//! * availability of invoke results (section 4): every shape is accepted by
//!   the validator, the engine and the checker together or refused by all
//!   three, and an accepted shape's engine output passes the checker;
//! * `Const` classification (section 2.2) for every spelling family at every
//!   graph type and both pointer widths: the engine's and the checker's
//!   graph/skeleton reading agree with the contract's rule and with the
//!   validator, and a graph constant evaluates to the residue of section 3;
//! * rule files (section 5): both parsers accept or refuse the same files,
//!   `(eval select ...)` included, with equal canonical texts and statement
//!   digests for every accepted rule;
//! * every section 2.5 class: the engine's decline class is the checker's
//!   `Ineligible` class (for `refinement_predicates`, the class of its
//!   module-wide refusal), and a validating module with predicates is
//!   declined and refused for every function;
//! * malformed bodies (section 2.5, and trust-ir's `Resume` rule (c)) are
//!   refused by both, a `LandingPad` not first in its block included; a
//!   `Resume` reached through a copy is rewritten only into a body the
//!   checker and the validator accept.
//!
//! What it does NOT establish: agreement on inputs outside these tables, or
//! the soundness of either reader (the exit test and the checker's own
//! tests cover acceptance and refusal).

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod engine_common;

use engine_common::residue;
use trust_cg_eqsat::derivation::header_only;
use trust_cg_eqsat::rules::{INTEGER_IDENTITIES, RuleSet};
use trust_cg_eqsat::{Decline, EngineConfig, Optimized, optimize_function, round_trip};
use trust_cg_eqsat_check::{Body, Registry, Rejection, Verdict, check};
use trust_ir::{BlockId, Constant, Function, Inst, InstrNode, Interpreter, Module, Ty, ValueId};

fn parse(text: &str) -> Module {
    trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

fn validates(module: &Module) -> bool {
    trust_ir_build::validate_module(module).is_empty()
}

fn index_of(module: &Module, name: &str) -> usize {
    module
        .functions
        .iter()
        .position(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"))
}

fn engine_rules() -> RuleSet {
    RuleSet::parse(INTEGER_IDENTITIES).expect("engine rules")
}

fn registry() -> Registry {
    Registry::parse(INTEGER_IDENTITIES).expect("checker registry")
}

fn engine(module: &Module, function: &Function) -> Result<Optimized, Decline> {
    optimize_function(module, function, &engine_rules(), &EngineConfig::default())
}

/// The checker on the unchanged function with the header-only derivation.
fn identity(module: &Module, function: &Function) -> Result<Verdict, Rejection> {
    check(
        module,
        function,
        function,
        &header_only(&function.name),
        &registry(),
    )
}

fn substituted(module: &Module, output: &Function) -> Module {
    let mut out = module.clone();
    let index = out
        .functions
        .iter()
        .position(|f| f.id == output.id)
        .expect("function in module");
    out.functions[index] = output.clone();
    out
}

/// For an input the engine took: the checker accepts the engine's output and
/// the no-rule round trip, and both validate.
fn assert_engine_output_accepted(module: &Module, input: &Function, out: &Optimized, what: &str) {
    check(module, input, &out.function, &out.derivation, &registry())
        .unwrap_or_else(|r| panic!("{what}: checker refused the engine output: {r:?}"));
    let errors = trust_ir_build::validate_module(&substituted(module, &out.function));
    assert!(
        errors.is_empty(),
        "{what}: engine output does not validate: {errors:?}"
    );
    let trip = round_trip(module, input).unwrap_or_else(|d| panic!("{what}: round trip: {d}"));
    check(module, input, &trip, &header_only(&input.name), &registry())
        .unwrap_or_else(|r| panic!("{what}: checker refused the round trip: {r:?}"));
    let errors = trust_ir_build::validate_module(&substituted(module, &trip));
    assert!(
        errors.is_empty(),
        "{what}: round trip does not validate: {errors:?}"
    );
}

// ---------------------------------------------------------------------------
// Section 4: availability of invoke results.

const INVOKE_HEAD: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little

functy.0 = (i64) -> (i64)

fn @callee(functy.0) {
}

"#;

/// `(shape, function text, valid under trust-ir)`. Every valid shape holds a
/// foldable `add` of two constants, so the engine has something to rewrite.
const INVOKE_SHAPES: [(&str, &str, bool); 7] = [
    (
        "own normal-edge arguments",
        "fn @f(functy.0) {
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
",
        true,
    ),
    (
        "loop-header normal successor",
        "fn @f(functy.0) {
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
",
        true,
    ),
    (
        "block dominated by the normal successor",
        "fn @f(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    br bb3
bb2:
    %2, %3 = landingpad cleanup
    resume %2
bb3:
    %4 = const i64 3
    %5 = const i64 4
    %6 = add i64 %4, %5
    %7 = copy i64 %1
    ret %7
}
",
        true,
    ),
    (
        "unwind successor",
        "fn @f(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad cleanup
    %4 = copy i64 %1
    ret %4
}
",
        false,
    ),
    (
        "normal successor the landing pad also enters",
        "fn @f(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad cleanup
    br bb1
}
",
        false,
    ),
    (
        "own call argument",
        "fn @f(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%1) to bb1(%1) unwind bb2
bb1(%4: i64):
    ret %4
bb2:
    %2, %3 = landingpad cleanup
    resume %2
}
",
        false,
    ),
    (
        "join of the normal path and another path",
        "fn @f(functy.0) {
bb0(%0: i64):
    %8 = const i64 0
    %9 = icmp eq i64 %0, %8
    condbr %9, bb1, bb3
bb1:
    %1 = invoke @func.0(%0) to bb4() unwind bb2
bb2:
    %2, %3 = landingpad cleanup
    resume %2
bb3:
    br bb5
bb4:
    br bb5
bb5:
    ret %1
}
",
        false,
    ),
];

#[test]
fn invoke_result_availability_agrees() {
    for (shape, body, valid) in INVOKE_SHAPES {
        let module = parse(&format!("{INVOKE_HEAD}{body}"));
        let input = &module.functions[index_of(&module, "f")];
        let validator = validates(&module);
        let engine = engine(&module, input);
        let checker = identity(&module, input);
        assert_eq!(
            validator,
            valid,
            "{shape}: validator {:?}",
            trust_ir_build::validate_module(&module)
        );
        assert_eq!(engine.is_ok(), valid, "{shape}: engine {engine:?}");
        assert_eq!(checker.is_ok(), valid, "{shape}: checker {checker:?}");
        match (engine, checker) {
            (Ok(out), Ok(_)) => {
                assert!(out.rewritten, "{shape}: {:?}", out.stats);
                assert_engine_output_accepted(&module, input, &out, shape);
            }
            (Err(decline), Err(rejection)) => {
                assert_eq!(decline.class(), "unsupported", "{shape}: {decline}");
                assert!(
                    decline.to_string().contains("section 4"),
                    "{shape}: {decline}"
                );
                assert!(
                    matches!(
                        rejection,
                        Rejection::NotDominated {
                            body: Body::Input,
                            ..
                        }
                    ),
                    "{shape}: {rejection:?}"
                );
            }
            (engine, checker) => panic!("{shape}: engine {engine:?}, checker {checker:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Section 2.2 `Const` row and section 3.

/// `(spelling, width, signed)` of every graph type at a pointer width.
fn graph_types(pointer_bits: u32) -> Vec<(&'static str, Ty, u32, bool)> {
    vec![
        ("bool", Ty::Bool, 1, false),
        ("i8", Ty::I8, 8, true),
        ("i16", Ty::I16, 16, true),
        ("i32", Ty::I32, 32, true),
        ("i64", Ty::I64, 64, true),
        ("i128", Ty::I128, 128, true),
        ("isize", Ty::Isize, pointer_bits, true),
        ("u8", Ty::U8, 8, false),
        ("u16", Ty::U16, 16, false),
        ("u32", Ty::U32, 32, false),
        ("u64", Ty::U64, 64, false),
        ("u128", Ty::U128, 128, false),
        ("usize", Ty::Usize, pointer_bits, false),
    ]
}

/// Every spelling family at a type: the range ends and one past them in
/// `Int`, zero and minus one, the `U128` spellings below and above
/// `i128::MAX`, and both `Bool`s.
fn spellings(width: u32, signed: bool) -> Vec<Constant> {
    let (min, max): (i128, i128) = if width == 1 {
        (0, 1)
    } else if signed && width == 128 {
        (i128::MIN, i128::MAX)
    } else if signed {
        (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
    } else if width == 128 {
        (0, i128::MAX)
    } else {
        (0, (1i128 << width) - 1)
    };
    let mut out = vec![
        Constant::Int(0),
        Constant::Int(-1),
        Constant::Int(1),
        Constant::Int(min),
        Constant::Int(max),
        Constant::U128(0),
        Constant::U128(5),
        Constant::U128(i128::MAX as u128),
        Constant::U128(1u128 << 127),
        Constant::U128(u128::MAX),
        Constant::Bool(false),
        Constant::Bool(true),
    ];
    if let Some(below) = min.checked_sub(1) {
        out.push(Constant::Int(below));
    }
    if let Some(above) = max.checked_add(1) {
        out.push(Constant::Int(above));
    }
    out
}

/// The contract's rule (section 2.2 `Const` row): `Some(residue)` when the
/// constant is a graph constant, with the residue section 3 assigns it.
fn contract_reading(constant: &Constant, ty: &Ty, width: u32, signed: bool) -> Option<u128> {
    let mask = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    match (constant, ty) {
        (Constant::Bool(b), Ty::Bool) => Some(u128::from(*b)),
        (Constant::U128(v), Ty::U128) => (*v > i128::MAX as u128).then_some(*v),
        (Constant::Int(v), ty) if *ty != Ty::Bool => {
            let in_range = if signed {
                width == 128 || (-(1i128 << (width - 1))..(1i128 << (width - 1))).contains(v)
            } else {
                *v >= 0 && (width == 128 || *v < (1i128 << width))
            };
            in_range.then_some((*v as u128) & mask)
        }
        _ => None,
    }
}

/// `f: () -> (T)` with `%0 = <constant>` in `bb0` and `ret %0` in `bb1`, and
/// the same body with the constant moved into `bb1` (a graph instruction
/// may move; a skeleton one may not).
fn constant_bodies(ty: &str, target: &str, constant: &Constant) -> (Module, Function, Function) {
    let zero = if ty == "bool" { "false" } else { "0" };
    let text = format!(
        "; TrustIr text format v1\nmodule \"m\"\n{target}\nfuncty.0 = () -> ({ty})\n\n\
         fn @f(functy.0) {{\nbb0:\n    %0 = const {ty} {zero}\n    br bb1\nbb1:\n    ret %0\n}}\n"
    );
    let mut module = parse(&text);
    let index = index_of(&module, "f");
    let Inst::Const { ty, .. } = module.functions[index].blocks[0].body[0].inst.clone() else {
        panic!("not a const")
    };
    module.functions[index].blocks[0].body[0].inst = Inst::Const {
        ty,
        value: constant.clone(),
    };
    let input = module.functions[index].clone();
    let mut moved = input.clone();
    let node = moved.blocks[0].body.remove(0);
    moved.blocks[1].body.insert(0, node);
    (module, input, moved)
}

#[test]
fn constant_spellings_are_classified_alike() {
    let targets = [
        ("target \"aarch64-apple-darwin\" 8 little\n", 64u32),
        ("target \"wasm32-unknown-unknown\" 4 little\n", 32u32),
    ];
    let mut graph = 0usize;
    let mut skeleton = 0usize;
    for (target, pointer_bits) in targets {
        for (name, ty, width, signed) in graph_types(pointer_bits) {
            for constant in spellings(width, signed) {
                let what = format!("const {name} {constant:?} at {pointer_bits} bits");
                let (module, input, moved) = constant_bodies(name, target, &constant);
                assert_eq!(module.pointer_bits(), pointer_bits, "{what}");
                let expected = contract_reading(&constant, &ty, width, signed);
                let out =
                    optimize_function(&module, &input, &RuleSet::empty(), &EngineConfig::default())
                        .unwrap_or_else(|d| panic!("{what}: engine declined {d}"));
                let engine_graph = out.stats.graph_instructions == 1;
                assert_eq!(
                    out.stats.graph_instructions + out.stats.skeleton_instructions,
                    3,
                    "{what}: {:?}",
                    out.stats
                );
                identity(&module, &input)
                    .unwrap_or_else(|r| panic!("{what}: checker refused the identity: {r:?}"));
                let checker_graph =
                    match check(&module, &input, &moved, &header_only("f"), &registry()) {
                        Ok(_) => true,
                        Err(Rejection::SkeletonCountMismatch { .. }) => false,
                        Err(other) => panic!("{what}: checker: {other:?}"),
                    };
                assert_eq!(engine_graph, expected.is_some(), "{what}: engine");
                assert_eq!(checker_graph, expected.is_some(), "{what}: checker");
                assert_eq!(
                    validates(&module),
                    expected.is_some(),
                    "{what}: validator {:?}",
                    trust_ir_build::validate_module(&module)
                );
                if let Some(r) = expected {
                    graph += 1;
                    let ran = Interpreter::with_module(&module)
                        .execute_func(input.id, [])
                        .unwrap_or_else(|e| panic!("{what}: interpreter {e:?}"));
                    assert_eq!(ran.returns.len(), 1, "{what}");
                    assert_eq!(residue(&ran.returns[0]), r, "{what}: section 3 residue");
                } else {
                    skeleton += 1;
                }
            }
        }
    }
    eprintln!("constant spellings: {graph} graph constants, {skeleton} skeleton constants");
    assert!(graph > 0 && skeleton > 0);
}

// ---------------------------------------------------------------------------
// Section 5: rule files.

/// Files both parsers accept.
const GOOD_RULE_FILES: [&str; 4] = [
    "; c\n(rule   odd ;x\n (direction\tequiv)(domain u8 i32)\r\n (lhs (add ?x (const -0)))\x0c(rhs ?x)\n (where))\n\
     (rule odd2 (direction refines) (domain u16) (lhs (mul ?x (const ?c))) (rhs (const 000)) (where (eq ?c 0000)))\n",
    "(rule fold_add (direction equiv) (domain u8 isize) (lhs (add (const ?a) (const ?b))) (rhs (eval add ?a ?b)) (where))",
    "(rule fold_cmp (direction equiv) (domain i64) (lhs (icmp.slt (const ?a) (const ?b))) (rhs (eval icmp.slt ?a ?b)) (where))",
    "",
];

/// Files both parsers refuse, each breaking one clause of section 5.1.
const BAD_RULE_FILES: [(&str, &str); 16] = [
    (
        "eval select",
        "(rule fold_select (direction equiv) (domain u8) (lhs (select (const ?c) (const ?a) (const ?b))) (rhs (eval select ?c ?a ?b)) (where))",
    ),
    (
        "eval in the lhs",
        "(rule r (direction equiv) (domain u8) (lhs (add (eval add ?a ?b) ?x)) (rhs ?x) (where))",
    ),
    (
        "eval of a term variable",
        "(rule r (direction equiv) (domain u8) (lhs (add ?a ?b)) (rhs (eval add ?a ?b)) (where))",
    ),
    (
        "duplicate name",
        "(rule r (direction equiv) (domain u8) (lhs (add ?x (const 0))) (rhs ?x) (where))\n(rule r (direction equiv) (domain u8) (lhs (or ?x (const 0))) (rhs ?x) (where))",
    ),
    (
        "repeated domain type",
        "(rule r (direction equiv) (domain u8 u8) (lhs (add ?x (const 0))) (rhs ?x) (where))",
    ),
    (
        "non-total operator",
        "(rule r (direction equiv) (domain u8) (lhs (udiv ?x (const 1))) (rhs ?x) (where))",
    ),
    (
        "const at bool",
        "(rule r (direction equiv) (domain bool) (lhs (and ?x (const 1))) (rhs ?x) (where))",
    ),
    (
        "true at a T position",
        "(rule r (direction equiv) (domain u8) (lhs (add ?x true)) (rhs ?x) (where))",
    ),
    (
        "rhs variable not in the lhs",
        "(rule r (direction equiv) (domain u8) (lhs (add ?x (const 0))) (rhs ?y) (where))",
    ),
    (
        "constant and term variable mixed",
        "(rule r (direction equiv) (domain u8) (lhs (add ?x (const ?x))) (rhs ?x) (where))",
    ),
    (
        "where on a term variable",
        "(rule r (direction equiv) (domain u8) (lhs (add ?x (const 0))) (rhs ?x) (where (eq ?x 0)))",
    ),
    (
        "missing clause",
        "(rule r (direction equiv) (domain u8) (lhs (add ?x (const 0))) (rhs ?x))",
    ),
    (
        "integer out of range",
        "(rule r (direction equiv) (domain u8) (lhs (add ?x (const 340282366920938463463374607431768211456))) (rhs ?x) (where))",
    ),
    (
        "ordered compare at bool",
        "(rule r (direction equiv) (domain bool) (lhs (icmp.ult ?x ?x)) (rhs false) (where))",
    ),
    (
        "non-ASCII outside a comment",
        "(rule r (direction equiv) (domain u8) (lhs (add ?x (const 0))) (rhs ?x) (where))\u{a0}",
    ),
    (
        "lhs root not an operator",
        "(rule r (direction equiv) (domain u8) (lhs ?x) (rhs ?x) (where))",
    ),
];

/// Every committed rule-file text: the honest identities and the mutants.
fn committed_rule_files() -> Vec<(String, String)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/wrong_rules");
    let mut out = vec![(
        "integer_identities".to_owned(),
        INTEGER_IDENTITIES.to_owned(),
    )];
    let mut names: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    names.sort();
    for path in names {
        out.push((
            path.display().to_string(),
            std::fs::read_to_string(&path).unwrap(),
        ));
    }
    out
}

#[test]
fn rule_files_are_read_alike() {
    let mut texts: Vec<(String, String)> = GOOD_RULE_FILES
        .iter()
        .enumerate()
        .map(|(i, t)| (format!("good {i}"), (*t).to_owned()))
        .collect();
    texts.extend(committed_rule_files());
    let nested_64 = format!(
        "(rule r (direction equiv) (domain u8) (lhs {}?x{}) (rhs ?x) (where))",
        "(not ".repeat(62),
        ")".repeat(62)
    );
    texts.push(("nesting 64".to_owned(), nested_64));
    let mut accepted = 0usize;
    let mut refused = 0usize;
    for (what, text) in &texts {
        let engine = RuleSet::parse(text);
        let checker = Registry::parse(text);
        assert_eq!(
            engine.is_ok(),
            checker.is_ok(),
            "{what}: engine {:?}, checker {:?}",
            engine.as_ref().err(),
            checker.as_ref().err()
        );
        let (Ok(engine), Ok(checker)) = (engine, checker) else {
            refused += 1;
            continue;
        };
        accepted += 1;
        let names: Vec<String> = engine.rules().iter().map(|r| r.name().to_owned()).collect();
        assert_eq!(names, checker.names(), "{what}");
        let texts = trust_cg_eqsat::rules::canonical_texts(text).unwrap();
        for (rule, (name, canonical)) in engine.rules().iter().zip(&texts) {
            assert_eq!(rule.name(), name, "{what}");
            assert_eq!(rule.canonical_text(), canonical, "{what}");
            assert_eq!(
                checker.canonical_text(name).as_deref(),
                Some(rule.canonical_text()),
                "{what}: {name}"
            );
            assert_eq!(
                checker.statement_digest(name),
                Some(rule.statement_digest()),
                "{what}: {name}"
            );
        }
    }
    let nested_65 = format!(
        "(rule r (direction equiv) (domain u8) (lhs {}?x{}) (rhs ?x) (where))",
        "(not ".repeat(63),
        ")".repeat(63)
    );
    let mut bad: Vec<(&str, String)> = BAD_RULE_FILES
        .iter()
        .map(|(w, t)| (*w, (*t).to_owned()))
        .collect();
    bad.push(("nesting 65", nested_65));
    for (what, text) in &bad {
        let engine = RuleSet::parse(text);
        let checker = Registry::parse(text);
        assert!(engine.is_err(), "{what}: the engine accepts it");
        assert!(checker.is_err(), "{what}: the checker accepts it");
        refused += 1;
    }
    eprintln!("rule files: {accepted} accepted by both, {refused} refused by both");
    // The two panic-only mutants are the committed files refused by both.
    assert_eq!(refused, bad.len() + 2);
}

// ---------------------------------------------------------------------------
// Section 2.5: the refusal classes.

const BASE: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (i64) -> (i64)

fn @f(functy.0) {
bb0(%0: i64):
    %1 = const i64 3
    %2 = const i64 4
    %3 = add i64 %1, %2
    ret %3
}
"#;

fn obligation() -> trust_ir::ProofObligation {
    trust_ir::ProofObligation::new(
        trust_ir::ProofId::new(0),
        trust_ir::ObligationKind::Postcondition,
        trust_ir::ProofStatus::Pending,
        "an obligation",
    )
}

/// The section 2.5 class names, read from the contract.
fn contract_classes() -> Vec<String> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/eqsat-tier-e.md");
    let spec = std::fs::read_to_string(path).unwrap();
    let start = spec.find("### 2.5 ").expect("section 2.5");
    let end = start + spec[start..].find("\n## 3.").expect("section 3");
    spec[start..end]
        .lines()
        .filter_map(|line| line.strip_prefix("* `"))
        .filter_map(|rest| rest.split_once("`:").map(|(name, _)| name.to_owned()))
        .collect()
}

#[test]
fn refusal_classes_agree() {
    type Mutation = fn(&mut Module, usize);
    let cases: [(&str, Mutation); 12] = [
        ("no_body", |m, i| m.functions[i].blocks.clear()),
        ("function_proofs", |m, i| {
            m.functions[i].proofs.push(trust_ir::ProofAnnotation::Pure);
        }),
        ("summary", |m, i| {
            m.functions[i].summary = Some(trust_ir::FunctionSummary::default());
        }),
        ("body_gate", |m, i| {
            m.functions[i].body_gate = Some(trust_ir::BodyGate::Ungated);
        }),
        ("source_provenance", |m, i| {
            let digest = trust_ir::ProofDigest::sha256_domain("test", b"");
            m.functions[i].source_provenance =
                Some(trust_ir::SourceProvenance::new(digest, digest, Vec::new()));
        }),
        ("instruction_proofs", |m, i| {
            m.functions[i].blocks[0].body[0]
                .proofs
                .push(trust_ir::ProofAnnotation::Pure);
        }),
        ("module_obligation", |m, i| {
            let id = m.functions[i].id;
            m.proof_obligations.push(obligation().with_function(id));
        }),
        ("module_obligation", |m, i| {
            let (id, entry) = (m.functions[i].id, m.functions[i].entry);
            m.proof_obligations
                .push(obligation().with_site(trust_ir::ObligationSite::new(id, entry, 0)));
        }),
        ("unscoped_obligation", |m, _| {
            m.proof_obligations.push(obligation());
        }),
        ("spec_modules", |m, _| {
            m.spec_modules.push(trust_ir::SpecModule::new("spec"));
        }),
        ("refinement_predicates", |m, _| {
            m.intern_pred(trust_ir::Pred::Interval { lo: 0, hi: 9 })
                .expect("pred id")
                .expect("a canonical predicate");
        }),
        ("unreachable_block", |m, i| {
            let mut dead = m.functions[i].blocks[0].clone();
            dead.id = BlockId(9);
            m.functions[i].blocks.push(dead);
        }),
    ];
    let mut seen: Vec<String> = Vec::new();
    for (class, mutate) in cases {
        let mut module = parse(BASE);
        let index = index_of(&module, "f");
        mutate(&mut module, index);
        let function = &module.functions[index];
        let decline = engine(&module, function).expect_err(class);
        assert_eq!(decline.class(), class, "engine: {decline}");
        match identity(&module, function) {
            Err(Rejection::Ineligible {
                body: Body::Input,
                class: checker,
                ..
            }) => assert_eq!(checker, class, "checker"),
            // A module-wide refusal of its own (section 8 item 2).
            Err(refused @ Rejection::RefinementPredicates { .. }) => {
                assert_eq!(refused.class(), class, "checker");
            }
            other => panic!("{class}: checker {other:?}"),
        }
        // On the output side alone the checker refuses too (a module-level
        // class has no output side: the module is shared).
        let clean = parse(BASE);
        let clean_fn = &clean.functions[index];
        if module.proof_obligations.is_empty()
            && module.spec_modules.is_empty()
            && module.predicates.is_empty()
        {
            let refused =
                check(&clean, clean_fn, function, &header_only("f"), &registry()).expect_err(class);
            assert!(
                matches!(
                    &refused,
                    Rejection::Ineligible {
                        body: Body::Output,
                        ..
                    } | Rejection::FunctionFieldMismatch { .. }
                ),
                "{class}: output-side {refused:?}"
            );
        }
        seen.push(class.to_owned());
    }
    seen.sort();
    seen.dedup();
    let mut contract = contract_classes();
    contract.sort();
    assert_eq!(seen, contract, "every section 2.5 class is exercised");
}

/// A module with refinement predicates that the validator accepts: the
/// engine declines every function of it and the checker refuses it, both
/// with the class `refinement_predicates`, whatever the bodies (the identity
/// with the header-only derivation, and a rewrite the engine would make
/// without the predicate).
#[test]
fn refinement_predicates_are_refused_alike() {
    let text = r#"; TrustIr text format v1
module "m"

functy.0 = (i64) -> (i64)

fn @f(functy.0) {
bb0(%0: i64):
    %1 = const i64 0
    %2 = xor i64 %0, %1
    %3 = add i64 %2, %1
    ret %3
}

fn @g(functy.0) {
bb0(%0: i64):
    ret %0
}
"#;
    let plain = parse(text);
    let mut module = plain.clone();
    module
        .intern_pred(trust_ir::Pred::Interval { lo: 0, hi: 9 })
        .expect("pred id")
        .expect("a canonical predicate");
    assert!(validates(&module), "the predicate module validates");
    // Without the predicate the engine rewrites `@f`.
    let f = &plain.functions[index_of(&plain, "f")];
    let rewritten = engine(&plain, f).expect("plain f");
    assert!(rewritten.rewritten);
    assert_engine_output_accepted(&plain, f, &rewritten, "plain f");
    for function in &module.functions {
        let decline = engine(&module, function).expect_err("declined");
        assert_eq!(decline, Decline::RefinementPredicates);
        assert_eq!(decline.class(), "refinement_predicates");
        assert_eq!(round_trip(&module, function).err(), Some(decline.clone()));
        let refused = identity(&module, function).expect_err("checker");
        assert_eq!(refused.class(), decline.class(), "{refused}");
    }
    // The rewrite the engine makes without the predicate is refused under it.
    let f = &module.functions[index_of(&module, "f")];
    let refused = check(
        &module,
        f,
        &rewritten.function,
        &rewritten.derivation,
        &registry(),
    )
    .expect_err("checker");
    assert_eq!(refused.class(), "refinement_predicates", "{refused}");
}

// ---------------------------------------------------------------------------
// Section 2.5 malformed bodies and section 4 landing pads.

const PAD: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little

functy.0 = (i64) -> (i64)

fn @callee(functy.0) {
}

fn @f(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad cleanup
    %4 = const i64 3
    %5 = const i64 4
    %6 = add i64 %4, %5
    ret %6
}
"#;

fn const_node(value: u32, v: i128) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(v),
    })
    .with_result(ValueId(value))
}

#[test]
fn landing_pad_position_is_refused_by_both() {
    let module = parse(PAD);
    assert!(validates(&module));
    let index = index_of(&module, "f");
    let input = &module.functions[index];
    // The engine keeps the pad first and the checker accepts its output.
    let out = engine(&module, input).expect("engine");
    assert!(out.rewritten, "{:?}", out.stats);
    assert!(matches!(
        out.function.blocks[2].body[0].inst,
        Inst::LandingPad { .. }
    ));
    assert_engine_output_accepted(&module, input, &out, "pad");

    // An input with an instruction before its pad: refused by all three.
    let mut bad = module.clone();
    bad.functions[index].blocks[2]
        .body
        .insert(0, const_node(40, 1));
    assert!(!validates(&bad));
    let bad_fn = &bad.functions[index];
    let decline = engine(&bad, bad_fn).expect_err("engine");
    assert_eq!(decline.class(), "unsupported", "{decline}");
    assert!(
        matches!(
            identity(&bad, bad_fn),
            Err(Rejection::MalformedBody {
                body: Body::Input,
                ..
            })
        ),
        "{:?}",
        identity(&bad, bad_fn)
    );

    // An output with a graph instruction moved above the pad.
    let mut moved = input.clone();
    let node = moved.blocks[2].body.remove(1);
    moved.blocks[2].body.insert(0, node);
    let refused = check(&module, input, &moved, &header_only("f"), &registry());
    assert!(
        matches!(
            refused,
            Err(Rejection::MalformedBody {
                body: Body::Output,
                ..
            })
        ),
        "{refused:?}"
    );
}

#[test]
fn malformed_bodies_are_refused_by_both() {
    type Mutation = fn(&mut Function);
    let cases: [(&str, Mutation); 8] = [
        ("duplicate block id", |f| {
            let copy = f.blocks[1].clone();
            f.blocks.push(copy);
        }),
        ("duplicate value definition", |f| {
            let results = f.blocks[2].body[1].results.clone();
            f.blocks[2].body[2].results = results;
        }),
        ("missing entry block", |f| f.entry = BlockId(7)),
        ("terminator before the end", |f| {
            let ret = InstrNode::new(Inst::Return {
                values: vec![ValueId(0)],
            });
            f.blocks[2].body.insert(1, ret);
        }),
        ("no terminator", |f| {
            f.blocks[2].body.pop();
        }),
        ("edge to a missing block", |f| {
            f.blocks[1].body[0].inst = Inst::Br {
                target: BlockId(8),
                args: Vec::new(),
            };
        }),
        ("result count", |f| {
            f.blocks[2].body[1].results.push(ValueId(41));
        }),
        ("use before definition", |f| {
            f.blocks[2].body.swap(1, 3);
        }),
    ];
    let module = parse(PAD);
    let index = index_of(&module, "f");
    for (what, mutate) in cases {
        let mut bad = module.clone();
        mutate(&mut bad.functions[index]);
        assert!(!validates(&bad), "{what}: the validator accepts it");
        let function = &bad.functions[index];
        let engine = engine(&bad, function);
        let checker = identity(&bad, function);
        assert!(
            engine.is_err(),
            "{what}: engine {:?}",
            engine.map(|o| o.stats)
        );
        assert!(checker.is_err(), "{what}: checker accepts it");
    }
}

// ---------------------------------------------------------------------------
// trust-ir's `Resume` rule (c): a `Resume` re-raises only what a pad produced.

const RESUME_HEAD: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little

functy.0 = (i64) -> (i64)

fn @callee(functy.0) {
}

fn @f(functy.0) {
bb0(%0: i64):
    %1 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad cleanup
"#;

#[test]
fn resume_operands_are_read_alike() {
    // `(what, pad block tail, valid under trust-ir, rewritten)`. Removing the
    // copy before a selector or a constant would break rule (c), so the
    // engine keeps a copy there; only the folded sum is cheaper then.
    let cases = [
        ("exception object", "    resume %2\n}\n", true, false),
        (
            "copy of the selector",
            "    %4 = copy i32 %3\n    resume %4\n}\n",
            true,
            false,
        ),
        (
            "copy of a constant",
            "    %4 = const i32 7\n    %5 = copy i32 %4\n    resume %5\n}\n",
            true,
            false,
        ),
        (
            "copy of a folded sum",
            "    %4 = const i32 3\n    %5 = const i32 4\n    %6 = add i32 %4, %5\n    %7 = copy i32 %6\n    resume %7\n}\n",
            true,
            true,
        ),
        ("the selector", "    resume %3\n}\n", false, false),
        (
            "a constant",
            "    %4 = const i32 7\n    resume %4\n}\n",
            false,
            false,
        ),
    ];
    for (what, tail, valid, rewritten) in cases {
        let module = parse(&format!("{RESUME_HEAD}{tail}"));
        let input = &module.functions[index_of(&module, "f")];
        assert_eq!(
            validates(&module),
            valid,
            "{what}: validator {:?}",
            trust_ir_build::validate_module(&module)
        );
        let engine = engine(&module, input);
        let checker = identity(&module, input);
        assert_eq!(checker.is_ok(), valid, "{what}: checker {checker:?}");
        assert_eq!(
            engine.is_ok(),
            valid,
            "{what}: engine {:?}",
            engine.as_ref().map(|o| &o.stats)
        );
        let Ok(out) = engine else {
            continue;
        };
        assert_eq!(out.rewritten, rewritten, "{what}: {:?}", out.stats);
        assert_engine_output_accepted(&module, input, &out, what);
        if rewritten {
            // The folded constant reaches the Resume through a copy.
            let pad = &out.function.blocks[2].body;
            let Some(Inst::Resume { exn }) = pad.last().map(|n| &n.inst) else {
                panic!("{what}: no resume")
            };
            let def = pad.iter().find(|n| n.results.contains(exn)).unwrap();
            assert!(
                matches!(def.inst, Inst::Copy { .. }),
                "{what}: {:?}",
                def.inst
            );
        }
    }
    // No landing pad at all.
    let module = parse(
        r#"; TrustIr text format v1
module "m"

functy.0 = (i64) -> (i64)

fn @f(functy.0) {
bb0(%0: i64):
    resume %0
}
"#,
    );
    assert!(!validates(&module));
    let input = &module.functions[0];
    assert!(
        engine(&module, input).is_err(),
        "engine: resume with no pad"
    );
    assert!(
        identity(&module, input).is_err(),
        "checker: resume with no pad"
    );
}
