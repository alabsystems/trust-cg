// crates/trust-cg-eqsat/tests/eqsat_saturation_differential.rs - PKG-U4 exit test for Tier S
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The exit test of PKG-U4 (`docs/eqsat-tier-s.md`).
//!
//! * Saturation agrees with an exhaustive naive rewriter on seeded random
//!   terms: every form the rewriter reaches is a form the graph holds in
//!   the root's class (no missing form), and the independent checker
//!   accepts the derivation of every one (no rejected derivation). Where
//!   the rules are closed under inverse, the two sets are equal.
//! * Two runs that exhaust a match budget give identical results, on one
//!   fixture and on every term of four seeded corpora.
//! * Extraction never returns a form costlier than its input, on a fixture
//!   with a shared subterm where the tree-cost choice is costlier too; where
//!   its search ends within the budget, no form is cheaper.
//! * Regions thousands of levels deep are saturated, extracted, justified
//!   and checked on a test thread's stack.
//! * A derivation that rewrites a pinned reduction through an order-free
//!   node over the same operand is rejected, and so is an order-free node
//!   elaborated at two sites.
//!
//! Two cases are the exits of Trust's Luminal ledger rows
//! `egglog-rules-bounded-saturation-tests` and
//! `egglog-rules-staged-schedule` (trust
//! `tests/luminal-domination/capabilities.json`): each prints its
//! `LUMINAL-ROW <id> PASS` line after every check of the row has passed.
//!
//! The naive rewriter below is written for this test: its own term type,
//! its own reader for the rule file, syntactic matching, breadth-first
//! closure. It shares nothing with the engine but the rule file's text.
//! The generator is a fixed-seed SplitMix64; no time and no OS randomness
//! is read. What agreement shows is that the engine finds what plain
//! rewriting finds and can justify it to the checker; the rules themselves
//! are statements (sampled below, proved nowhere until PKG-U2).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use trust_cg_eqsat::derivation::{self, BinOpCode, DerivationBuilder, OpDesc, ScalarTy};
use trust_cg_eqsat::rules::{INTEGER_IDENTITIES, RuleErrorKind, RuleSet};
use trust_cg_eqsat::saturate::{
    LeafName, NodeId, Region, RegionNode, SaturateError, Schedule, Stage, Stop, saturate,
};
use trust_cg_eqsat_check::{RegionRejection, Registry, Rejection, check_region};

/// The Tier S rule set (statements; no proof authority until PKG-U2).
const RULES: &str = include_str!("../rules/tier_s_integer.rules");

/// The committed seed of every random choice in this file.
const SEED: u64 = 0x5eed_0004_7c9e_55a7;

/// The committed sizes: terms per pass and operator nodes per term.
const TERMS_PER_PASS: usize = 80;
const MAX_OPS_IDENTITY: usize = 4;
const MAX_OPS_DISTRIBUTION: usize = 3;

/// A naive closure larger than this fails the test (the generator's sizes
/// keep every closure below it).
const NAIVE_LIMIT: usize = 20_000;

/// The committed budgets every corpus term reaches its fixpoint within:
/// matches a stage may count, and concrete terms the graph may hold.
const FIXPOINT_MATCHES: u64 = 5_000_000;
const FIXPOINT_TERMS: usize = 500_000;

const LEAVES: u32 = 3;
const TYPES: [ScalarTy; 3] = [ScalarTy::U8, ScalarTy::I32, ScalarTy::U64];

// ---------------------------------------------------------------------------
// The naive side: terms, the rule-file reader, rewriting, costs, evaluation.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Op {
    Add,
    Mul,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Term {
    Leaf(u32),
    Const(u128),
    Bin(Op, Box<Term>, Box<Term>),
}

fn bin(op: Op, a: Term, b: Term) -> Term {
    Term::Bin(op, Box::new(a), Box::new(b))
}

fn render(term: &Term) -> String {
    match term {
        Term::Leaf(i) => format!("x{i}"),
        Term::Const(c) => c.to_string(),
        Term::Bin(op, a, b) => format!(
            "({} {} {})",
            if *op == Op::Add { "add" } else { "mul" },
            render(a),
            render(b)
        ),
    }
}

#[derive(Clone, Debug)]
enum Pattern {
    Var(String),
    Const(u128),
    Bin(Op, Box<Pattern>, Box<Pattern>),
}

#[derive(Clone, Debug)]
struct NaiveRule {
    name: String,
    lhs: Pattern,
    rhs: Pattern,
}

#[derive(Clone, Debug)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn read_sexps(text: &str) -> Vec<Sexp> {
    let mut stack: Vec<Vec<Sexp>> = vec![Vec::new()];
    let mut atom = String::new();
    let flush = |atom: &mut String, stack: &mut Vec<Vec<Sexp>>| {
        if !atom.is_empty() {
            stack
                .last_mut()
                .unwrap()
                .push(Sexp::Atom(std::mem::take(atom)));
        }
    };
    for line in text.lines() {
        let code = line.split(';').next().unwrap();
        for c in code.chars() {
            match c {
                '(' => {
                    flush(&mut atom, &mut stack);
                    stack.push(Vec::new());
                }
                ')' => {
                    flush(&mut atom, &mut stack);
                    let done = stack.pop().unwrap();
                    stack.last_mut().expect("balanced").push(Sexp::List(done));
                }
                c if c.is_whitespace() => flush(&mut atom, &mut stack),
                c => atom.push(c),
            }
        }
        flush(&mut atom, &mut stack);
    }
    assert_eq!(stack.len(), 1, "unbalanced rule file");
    stack.pop().unwrap()
}

fn pattern(sexp: &Sexp) -> Pattern {
    match sexp {
        Sexp::Atom(a) => Pattern::Var(a.strip_prefix('?').expect("a variable").to_owned()),
        Sexp::List(items) => {
            let Sexp::Atom(head) = &items[0] else {
                panic!("pattern head");
            };
            match (head.as_str(), &items[1..]) {
                ("const", [Sexp::Atom(n)]) => Pattern::Const(n.parse().expect("a literal")),
                ("add", [a, b]) => {
                    Pattern::Bin(Op::Add, Box::new(pattern(a)), Box::new(pattern(b)))
                }
                ("mul", [a, b]) => {
                    Pattern::Bin(Op::Mul, Box::new(pattern(a)), Box::new(pattern(b)))
                }
                other => panic!("the naive rewriter does not model {other:?}"),
            }
        }
    }
}

/// Reads the rule file with this test's own reader. Every rule must be an
/// unconditional `equiv` rule over `add`, `mul`, variables and literals.
fn naive_rules(text: &str) -> Vec<NaiveRule> {
    read_sexps(text)
        .iter()
        .map(|form| {
            let Sexp::List(items) = form else {
                panic!("a top-level atom");
            };
            let clause = |index: usize, name: &str| -> Vec<Sexp> {
                let Sexp::List(clause) = &items[index] else {
                    panic!("clause {name}");
                };
                assert!(
                    matches!(&clause[0], Sexp::Atom(a) if a == name),
                    "clause {name}"
                );
                clause[1..].to_vec()
            };
            assert!(matches!(&items[0], Sexp::Atom(a) if a == "rule"));
            let Sexp::Atom(name) = &items[1] else {
                panic!("rule name");
            };
            assert!(matches!(&clause(2, "direction")[..], [Sexp::Atom(d)] if d == "equiv"));
            assert!(clause(6, "where").is_empty(), "{name} has a side condition");
            NaiveRule {
                name: name.clone(),
                lhs: pattern(&clause(4, "lhs")[0]),
                rhs: pattern(&clause(5, "rhs")[0]),
            }
        })
        .collect()
}

fn matches(pattern: &Pattern, term: &Term, env: &mut BTreeMap<String, Term>) -> bool {
    match (pattern, term) {
        (Pattern::Var(v), _) => match env.get(v) {
            Some(bound) => bound == term,
            None => {
                env.insert(v.clone(), term.clone());
                true
            }
        },
        (Pattern::Const(c), Term::Const(d)) => c == d,
        (Pattern::Bin(op, a, b), Term::Bin(found, x, y)) => {
            op == found && matches(a, x, env) && matches(b, y, env)
        }
        _ => false,
    }
}

fn instance(pattern: &Pattern, env: &BTreeMap<String, Term>) -> Term {
    match pattern {
        Pattern::Var(v) => env[v].clone(),
        Pattern::Const(c) => Term::Const(*c),
        Pattern::Bin(op, a, b) => bin(*op, instance(a, env), instance(b, env)),
    }
}

/// Every term one rule application away from `term`, at any position.
fn rewrites(term: &Term, rules: &[NaiveRule]) -> Vec<Term> {
    let mut out = Vec::new();
    for rule in rules {
        let mut env = BTreeMap::new();
        if matches(&rule.lhs, term, &mut env) {
            out.push(instance(&rule.rhs, &env));
        }
    }
    if let Term::Bin(op, a, b) = term {
        for left in rewrites(a, rules) {
            out.push(bin(*op, left, (**b).clone()));
        }
        for right in rewrites(b, rules) {
            out.push(bin(*op, (**a).clone(), right));
        }
    }
    out
}

/// Every term reachable from `term` by any number of rule applications.
fn closure(term: &Term, rules: &[NaiveRule]) -> BTreeSet<Term> {
    let mut seen = BTreeSet::from([term.clone()]);
    let mut frontier = vec![term.clone()];
    while let Some(next) = frontier.pop() {
        for found in rewrites(&next, rules) {
            if seen.insert(found.clone()) {
                frontier.push(found);
            }
        }
        assert!(
            seen.len() <= NAIVE_LIMIT,
            "the naive closure of {} exceeds {NAIVE_LIMIT} forms",
            render(term)
        );
    }
    seen
}

fn width(ty: ScalarTy) -> u32 {
    match ty {
        ScalarTy::U8 => 8,
        ScalarTy::I32 | ScalarTy::U32 => 32,
        ScalarTy::U64 => 64,
        other => panic!("the test does not use {other:?}"),
    }
}

fn evaluate(term: &Term, leaves: &[u128], ty: ScalarTy) -> u128 {
    let mask = (1u128 << width(ty)) - 1;
    match term {
        Term::Leaf(i) => leaves[*i as usize] & mask,
        Term::Const(c) => c & mask,
        Term::Bin(Op::Add, a, b) => {
            evaluate(a, leaves, ty).wrapping_add(evaluate(b, leaves, ty)) & mask
        }
        Term::Bin(Op::Mul, a, b) => {
            evaluate(a, leaves, ty).wrapping_mul(evaluate(b, leaves, ty)) & mask
        }
    }
}

/// The exhaustive box of one leaf: the four lowest values of the type and
/// its two highest (where wrapping shows).
fn box_values(ty: ScalarTy) -> [u128; 6] {
    let max = (1u128 << width(ty)) - 1;
    [0, 1, 2, 3, max - 1, max]
}

/// Every assignment of the box's values to the `LEAVES` leaves.
fn exhaustive_box(ty: ScalarTy) -> Vec<Vec<u128>> {
    let values = box_values(ty);
    let mut points = vec![Vec::new()];
    for _ in 0..LEAVES {
        points = points
            .into_iter()
            .flat_map(|point: Vec<u128>| {
                values.iter().map(move |value| {
                    let mut next = point.clone();
                    next.push(*value);
                    next
                })
            })
            .collect();
    }
    points
}

fn node_cost(term: &Term) -> u64 {
    match term {
        Term::Leaf(_) => 0,
        Term::Const(_) | Term::Bin(Op::Add, ..) => 1,
        Term::Bin(Op::Mul, ..) => 3,
    }
}

/// The cost that prices every occurrence (a shared subterm once per use).
fn tree_cost(term: &Term) -> u64 {
    node_cost(term)
        + match term {
            Term::Bin(_, a, b) => tree_cost(a) + tree_cost(b),
            _ => 0,
        }
}

fn subterms<'a>(term: &'a Term, out: &mut BTreeSet<&'a Term>) {
    if out.insert(term)
        && let Term::Bin(_, a, b) = term
    {
        subterms(a, out);
        subterms(b, out);
    }
}

/// The cost that prices every distinct subterm once.
fn dag_cost(term: &Term) -> u64 {
    let mut all = BTreeSet::new();
    subterms(term, &mut all);
    all.into_iter().map(node_cost).sum()
}

// ---------------------------------------------------------------------------
// The seeded generator.

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// A term with exactly `ops` operator nodes over `LEAVES` leaves and the
/// literals `consts`.
fn random_term(rng: &mut Rng, ops: usize, consts: &[u128]) -> Term {
    if ops == 0 {
        return if rng.below(4) == 0 {
            Term::Const(consts[rng.below(consts.len())])
        } else {
            Term::Leaf(rng.below(LEAVES as usize) as u32)
        };
    }
    let op = if rng.below(2) == 0 { Op::Add } else { Op::Mul };
    let left = rng.below(ops);
    bin(
        op,
        random_term(rng, left, consts),
        random_term(rng, ops - 1 - left, consts),
    )
}

/// The committed corpus of one pass: `(type, term)`.
fn corpus(pass: u64, max_ops: usize, consts: &[u128]) -> Vec<(ScalarTy, Term)> {
    let mut rng = Rng(SEED ^ pass);
    (0..TERMS_PER_PASS)
        .map(|index| {
            let ops = 1 + rng.below(max_ops);
            (
                TYPES[index % TYPES.len()],
                random_term(&mut rng, ops, consts),
            )
        })
        .collect()
}

/// FNV-1a over the rendering of a corpus, to pin the generator.
fn corpus_digest(corpus: &[(ScalarTy, Term)]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for (ty, term) in corpus {
        for byte in format!("{}:{};", ty.name(), render(term)).bytes() {
            hash = (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    hash
}

// ---------------------------------------------------------------------------
// The engine side: regions from terms and back.

fn leaf_name(index: u32) -> LeafName {
    LeafName::Result {
        block: 0,
        ordinal: index,
        index: 0,
    }
}

/// A region named `name` with every leaf declared (so two regions over the
/// same leaves agree on them).
fn new_region(name: &str, ty: ScalarTy, leaves: u32) -> Region {
    let mut region = Region::new(name, 64);
    for index in 0..leaves {
        region.leaf(leaf_name(index), ty).unwrap();
    }
    region
}

fn add_term(region: &mut Region, ty: ScalarTy, term: &Term) -> NodeId {
    match term {
        Term::Leaf(index) => region.leaf(leaf_name(*index), ty).unwrap(),
        Term::Const(c) => region.constant(ty, *c).unwrap(),
        Term::Bin(op, a, b) => {
            let (a, b) = (add_term(region, ty, a), add_term(region, ty, b));
            let code = if *op == Op::Add {
                BinOpCode::Add
            } else {
                BinOpCode::Mul
            };
            region.op(OpDesc::Bin(code, ty), &[a, b]).unwrap()
        }
    }
}

fn region_of(name: &str, ty: ScalarTy, roots: &[Term]) -> Region {
    let mut region = new_region(name, ty, LEAVES);
    for root in roots {
        let node = add_term(&mut region, ty, root);
        region.root(node).unwrap();
    }
    region
}

fn term_of(region: &Region, node: NodeId) -> Term {
    match region.node(node).unwrap() {
        RegionNode::Leaf(LeafName::Result { ordinal, .. }) => Term::Leaf(*ordinal),
        RegionNode::Const(_, residue) => Term::Const(*residue),
        RegionNode::Op(OpDesc::Bin(BinOpCode::Add, _), args) => {
            bin(Op::Add, term_of(region, args[0]), term_of(region, args[1]))
        }
        RegionNode::Op(OpDesc::Bin(BinOpCode::Mul, _), args) => {
            bin(Op::Mul, term_of(region, args[0]), term_of(region, args[1]))
        }
        other => panic!("the test does not model {other:?}"),
    }
}

fn stage(rules: &[NaiveRule], max_matches: u64) -> Stage {
    Stage {
        rules: rules.iter().map(|rule| rule.name.clone()).collect(),
        max_matches,
    }
}

fn schedule(rules: &[NaiveRule], max_matches: u64, max_terms: usize) -> Schedule {
    Schedule {
        stages: vec![stage(rules, max_matches)],
        max_terms,
        max_extraction_trials: Schedule::DEFAULT_EXTRACTION_TRIALS,
    }
}

/// What one differential pass counted.
#[derive(Default)]
struct Tally {
    terms: usize,
    forms: usize,
    proof_steps: usize,
    rewritten: usize,
    /// Terms whose extraction search ended within its budget.
    searched: usize,
    /// Evaluations of a naive form against its term.
    points: usize,
}

/// One term: naive closure, saturation, a derivation for every naive form,
/// the checker on all of them, the count of forms, and extraction.
fn differential(
    index: usize,
    ty: ScalarTy,
    term: &Term,
    rules: &[NaiveRule],
    exact: bool,
    rng: &mut Rng,
    tally: &mut Tally,
) {
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let registry = Registry::parse(RULES).unwrap();
    let what = format!("term {index} {} at {}", render(term), ty.name());

    // The naive side. Every form evaluates like the term, in wrapping
    // arithmetic of the type, on every point of the exhaustive box and on
    // sampled leaves (a sample of the rule statements, not a proof of them).
    let naive: Vec<Term> = closure(term, rules).into_iter().collect();
    let mut points = exhaustive_box(ty);
    assert_eq!(points.len(), 216);
    for _ in 0..4 {
        points.push((0..LEAVES).map(|_| u128::from(rng.next())).collect());
    }
    for leaves in &points {
        let expected = evaluate(term, leaves, ty);
        for form in &naive {
            assert_eq!(
                evaluate(form, leaves, ty),
                expected,
                "{what}: {}",
                render(form)
            );
        }
    }
    tally.points += points.len() * naive.len();

    // One root per naive form, every root the term itself: the graph is the
    // graph of the term, and one derivation can justify every form.
    let name = format!("differential_{index}");
    let input = region_of(&name, ty, &vec![term.clone(); naive.len()]);
    let mut saturation = saturate(
        &input,
        &engine_rules,
        &schedule(rules, FIXPOINT_MATCHES, FIXPOINT_TERMS),
    )
    .unwrap_or_else(|error| panic!("{what}: {error}"));
    assert!(
        saturation.stats().saturated(),
        "{what}: no fixpoint: {:?}",
        saturation.stats().stages
    );

    // No missing form, no rejected derivation.
    let target = region_of(&name, ty, &naive);
    let derivation = saturation
        .justify(&target)
        .unwrap_or_else(|error| panic!("{what}: {error}"))
        .unwrap_or_else(|| {
            let missing: Vec<String> = naive
                .iter()
                .filter(|form| {
                    let one = region_of(&name, ty, &vec![(*form).clone(); naive.len()]);
                    saturation.justify(&one).unwrap().is_none()
                })
                .map(render)
                .collect();
            panic!("{what}: the graph misses the naive forms {missing:?}")
        });
    let verdict = check_region(&input.encode(), &target.encode(), &derivation, &registry)
        .unwrap_or_else(|rejection| panic!("{what}: the checker rejects: {rejection}"));
    assert_eq!(verdict.roots, naive.len(), "{what}");
    assert_eq!(verdict.changed_roots, naive.len() - 1, "{what}");
    assert_eq!(verdict.claims, naive.len() - 1, "{what}");

    // The graph holds no other form when the rules are closed under
    // inverse; with the one-way identities it may hold more, never fewer.
    let forms = saturation.forms(0);
    if exact {
        assert_eq!(forms, Some(naive.len() as u128), "{what}");
    } else {
        assert!(
            forms.is_none_or(|count| count >= naive.len() as u128),
            "{what}: {forms:?}"
        );
    }

    // Extraction: never costlier than the input, justified, and a form the
    // naive rewriter also has when the two sets are equal.
    let extracted = saturation.extract().unwrap();
    assert_eq!(extracted.cost_before, dag_cost(term), "{what}");
    assert!(extracted.cost_after <= extracted.cost_before, "{what}");
    assert_eq!(extracted.cost_after, extracted.region.cost(), "{what}");
    assert_eq!(
        extracted.rewritten,
        extracted.cost_after < extracted.cost_before,
        "{what}"
    );
    let chosen = term_of(&extracted.region, extracted.region.roots()[0]);
    assert_eq!(dag_cost(&chosen), extracted.cost_after, "{what}");
    let best = naive.iter().map(dag_cost).min().unwrap();
    if exact {
        assert!(
            naive.contains(&chosen),
            "{what}: extracted {}",
            render(&chosen)
        );
        assert!(extracted.cost_after >= best, "{what}");
    }
    // A search that ended within its budget missed no cheaper form: every
    // naive form is in the graph, so the result is no costlier than the
    // cheapest of them (and is exactly that when the two sets are equal).
    if extracted.search_complete {
        assert!(extracted.cost_after <= best, "{what}: {best}");
        tally.searched += 1;
    }
    for leaves in &points {
        assert_eq!(
            evaluate(&chosen, leaves, ty),
            evaluate(term, leaves, ty),
            "{what}: extracted {}",
            render(&chosen)
        );
    }
    let checked = check_region(
        &input.encode(),
        &extracted.region.encode(),
        &extracted.derivation,
        &registry,
    )
    .unwrap_or_else(|rejection| panic!("{what}: the checker rejects the extraction: {rejection}"));
    assert_eq!(checked.changed_roots > 0, extracted.rewritten, "{what}");

    tally.terms += 1;
    tally.forms += naive.len();
    tally.proof_steps += verdict.proof_steps;
    tally.rewritten += usize::from(extracted.rewritten);
}

fn rules_named(all: &[NaiveRule], names: &[&str]) -> Vec<NaiveRule> {
    let found: Vec<NaiveRule> = all
        .iter()
        .filter(|rule| names.contains(&rule.name.as_str()))
        .cloned()
        .collect();
    assert_eq!(
        found.len(),
        names.len(),
        "a rule of {names:?} is not in the file"
    );
    found
}

const AC: [&str; 6] = [
    "add_comm",
    "mul_comm",
    "add_assoc_right",
    "add_assoc_left",
    "mul_assoc_right",
    "mul_assoc_left",
];

// ---------------------------------------------------------------------------
// The cases.

/// The naive reader and the engine read the same rules from the same file.
#[test]
fn both_sides_read_the_same_rule_file() {
    let naive = naive_rules(RULES);
    let engine = RuleSet::parse(RULES).unwrap();
    let registry = Registry::parse(RULES).unwrap();
    let names: Vec<&str> = naive.iter().map(|rule| rule.name.as_str()).collect();
    assert_eq!(
        names,
        engine
            .rules()
            .iter()
            .map(|rule| rule.name())
            .collect::<Vec<_>>()
    );
    // All three readers keep file order.
    assert_eq!(names, registry.names());
    for rule in engine.rules() {
        assert!(rule.is_equiv(), "{}", rule.name());
        assert_eq!(
            Some(rule.statement_digest()),
            registry.statement_digest(rule.name()),
            "{}",
            rule.name()
        );
    }
    assert_eq!(names.len(), 10);
}

/// The generator is a pure function of the committed seed.
#[test]
fn the_generator_is_seeded_and_committed() {
    let identity = corpus(1, MAX_OPS_IDENTITY, &[0, 1, 2]);
    let distribution = corpus(2, MAX_OPS_DISTRIBUTION, &[2, 3]);
    assert_eq!(identity, corpus(1, MAX_OPS_IDENTITY, &[0, 1, 2]));
    assert_eq!(identity.len(), TERMS_PER_PASS);
    assert_eq!(distribution.len(), TERMS_PER_PASS);
    assert_eq!(
        (corpus_digest(&identity), corpus_digest(&distribution)),
        (IDENTITY_CORPUS_DIGEST, DISTRIBUTION_CORPUS_DIGEST),
        "the committed corpus changed"
    );
}

const IDENTITY_CORPUS_DIGEST: u64 = 10_208_409_498_839_644_707;
const DISTRIBUTION_CORPUS_DIGEST: u64 = 2_700_801_057_717_804_927;

/// Associativity and commutativity with the identities, on terms that hold
/// the literals 0 and 1: every naive form is in the graph and justified.
#[test]
fn saturation_agrees_with_naive_rewriting_under_identities() {
    identities_pass();
}

fn identities_pass() -> Tally {
    let all = naive_rules(RULES);
    let mut names = AC.to_vec();
    names.extend(["add_zero", "mul_one"]);
    let rules = rules_named(&all, &names);
    let mut rng = Rng(SEED ^ 0x1d);
    let mut tally = Tally::default();
    for (index, (ty, term)) in corpus(1, MAX_OPS_IDENTITY, &[0, 1, 2]).iter().enumerate() {
        differential(index, *ty, term, &rules, false, &mut rng, &mut tally);
    }
    eprintln!(
        "identities: {} terms, {} naive forms all justified, {} proof steps, {} extractions cheaper, {} searched to the end",
        tally.terms, tally.forms, tally.proof_steps, tally.rewritten, tally.searched
    );
    assert_eq!(tally.terms, TERMS_PER_PASS);
    assert!(tally.rewritten > 0, "no term of the corpus was improved");
    assert_eq!(
        tally.searched, tally.terms,
        "the extraction search did not end within its budget on every term"
    );
    tally
}

/// The whole rule set on terms without the literals 0 and 1 (the identities
/// are in the stage and cannot fire): the rules that fire are closed under
/// inverse, so the graph holds exactly the naive forms.
#[test]
fn saturation_agrees_with_naive_rewriting_under_distribution() {
    distribution_pass();
}

fn distribution_pass() -> Tally {
    let rules = naive_rules(RULES);
    let mut rng = Rng(SEED ^ 0x2d);
    let mut tally = Tally::default();
    for (index, (ty, term)) in corpus(2, MAX_OPS_DISTRIBUTION, &[2, 3]).iter().enumerate() {
        differential(index, *ty, term, &rules, true, &mut rng, &mut tally);
    }
    eprintln!(
        "distribution: {} terms, {} naive forms all justified, {} proof steps, {} extractions cheaper, {} searched to the end",
        tally.terms, tally.forms, tally.proof_steps, tally.rewritten, tally.searched
    );
    assert_eq!(tally.terms, TERMS_PER_PASS);
    assert_eq!(
        tally.searched, tally.terms,
        "the extraction search did not end within its budget on every term"
    );
    tally
}

/// The exit of Trust's Luminal ledger row
/// `egglog-rules-bounded-saturation-tests` (Luminal: tests that its integer
/// normalizer reaches a fixpoint within fixed budgets and agrees with
/// concrete arithmetic on small exhaustive boxes). Here: every term of both
/// committed corpora reaches the fixpoint of its stage within the committed
/// match and term budgets, the graph then holds every form an independent
/// exhaustive rewriter reaches, the checker accepts the derivation of every
/// one, and every form equals its term in wrapping arithmetic on every
/// point of the exhaustive box of its type. Tier S has no division or
/// remainder (total operators only), so there is no truncating case.
#[test]
fn luminal_row_bounded_saturation_tests() {
    let (identities, distribution) = (identities_pass(), distribution_pass());
    assert_eq!(identities.terms + distribution.terms, 2 * TERMS_PER_PASS);
    assert_eq!(identities.forms + distribution.forms, 3_041 + 5_286);
    assert_eq!(
        identities.points + distribution.points,
        (3_041 + 5_286) * 220
    );
    // The first character keeps the line apart from the harness's own
    // output when the harness names a test before it runs it.
    println!("\nLUMINAL-ROW egglog-rules-bounded-saturation-tests PASS");
}

/// Each associativity rule alone, against the naive rewriter restricted to
/// the same rule. Each direction follows from the other with commutativity,
/// so the passes above cannot tell whether the engine fires all four; a
/// stage of one rule can.
#[test]
fn each_associativity_rule_fires_alone() {
    let all = naive_rules(RULES);
    for (pass, name) in [
        "add_assoc_right",
        "add_assoc_left",
        "mul_assoc_right",
        "mul_assoc_left",
    ]
    .into_iter()
    .enumerate()
    {
        let rules = rules_named(&all, &[name]);
        let mut rng = Rng(SEED ^ 0x3d ^ pass as u64);
        let mut tally = Tally::default();
        for (index, (ty, term)) in corpus(3, MAX_OPS_IDENTITY, &[2, 3]).iter().enumerate() {
            differential(index, *ty, term, &rules, false, &mut rng, &mut tally);
        }
        eprintln!(
            "{name} alone: {} terms, {} naive forms all justified",
            tally.terms, tally.forms
        );
        assert_eq!(tally.terms, TERMS_PER_PASS);
        assert!(
            tally.forms >= tally.terms + 10,
            "{name} rewrites fewer than 10 terms of the corpus"
        );
    }
}

/// A term that does not saturate under the whole rule set (a product with a
/// zero factor): two runs that exhaust the match budget give the same
/// statistics, region bytes and derivation bytes, and so do two runs that
/// exhaust the term budget.
#[test]
fn two_runs_that_exhaust_a_budget_give_identical_results() {
    let rules = naive_rules(RULES);
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let registry = Registry::parse(RULES).unwrap();
    // ((x0 + 0) * x1 + x2 * 1) + (x1 + x0) * (x2 + x0)
    let term = bin(
        Op::Add,
        bin(
            Op::Add,
            bin(
                Op::Mul,
                bin(Op::Add, Term::Leaf(0), Term::Const(0)),
                Term::Leaf(1),
            ),
            bin(Op::Mul, Term::Leaf(2), Term::Const(1)),
        ),
        bin(
            Op::Mul,
            bin(Op::Add, Term::Leaf(1), Term::Leaf(0)),
            bin(Op::Add, Term::Leaf(2), Term::Leaf(0)),
        ),
    );
    let input = region_of("budget", ScalarTy::U32, std::slice::from_ref(&term));
    let run = |max_matches: u64, max_terms: usize| {
        let mut saturation = saturate(
            &input,
            &engine_rules,
            &schedule(&rules, max_matches, max_terms),
        )
        .unwrap();
        let stats = saturation.stats().clone();
        let extracted = saturation.extract().unwrap();
        (
            stats,
            extracted.region.encode(),
            extracted.derivation,
            extracted.cost_after,
        )
    };

    // Forms up to three rewrites away from the term, in a fixed order. The
    // extraction above is one small form whatever the budget; a derivation
    // of each of these depends on the whole budget-cut graph.
    let mut distant = BTreeSet::from([term.clone()]);
    let mut frontier = vec![term.clone()];
    for _ in 0..3 {
        let mut next = Vec::new();
        for form in &frontier {
            for found in rewrites(form, &rules) {
                if distant.len() < 400 && distant.insert(found.clone()) {
                    next.push(found);
                }
            }
        }
        frontier = next;
    }
    let justify_all = |max_matches: u64, max_terms: usize| {
        let mut saturation = saturate(
            &input,
            &engine_rules,
            &schedule(&rules, max_matches, max_terms),
        )
        .unwrap();
        distant
            .iter()
            .map(|form| {
                let target = region_of("budget", ScalarTy::U32, std::slice::from_ref(form));
                let derivation = saturation.justify(&target).unwrap();
                if let Some(derivation) = &derivation {
                    check_region(&input.encode(), &target.encode(), derivation, &registry)
                        .unwrap_or_else(|rejection| panic!("{}: {rejection}", render(form)));
                }
                derivation
            })
            .collect::<Vec<Option<Vec<u8>>>>()
    };

    for (max_matches, max_terms, stop) in [
        (400, usize::MAX, Stop::MatchBudget),
        (4_000, usize::MAX, Stop::MatchBudget),
        (u64::MAX, 600, Stop::TermBudget),
    ] {
        let (justified, again) = (
            justify_all(max_matches, max_terms),
            justify_all(max_matches, max_terms),
        );
        assert_eq!(
            justified, again,
            "derivations of distant forms differ between two runs"
        );
        let held = justified.iter().flatten().count();
        let longest = justified.iter().flatten().map(Vec::len).max().unwrap_or(0);
        eprintln!(
            "budget {max_matches}/{max_terms}: {held} of {} distant forms held, longest derivation {longest} bytes",
            justified.len()
        );
        assert!(held >= 20, "{held} distant forms held");
        let first = run(max_matches, max_terms);
        let second = run(max_matches, max_terms);
        assert!(longest > first.2.len(), "{longest}");
        assert_eq!(first.0.stages[0].stop, stop, "{max_matches} {max_terms}");
        assert_eq!(first.0, second.0, "statistics differ between two runs");
        assert_eq!(first.1, second.1, "region bytes differ between two runs");
        assert_eq!(
            first.2, second.2,
            "derivation bytes differ between two runs"
        );
        if stop == Stop::MatchBudget {
            assert_eq!(first.0.stages[0].matches, max_matches);
        }
        // A budget-stopped result is still justified and never costlier.
        assert!(first.3 <= dag_cost(&term));
        check_region(&input.encode(), &first.1, &first.2, &registry)
            .unwrap_or_else(|rejection| panic!("budget {max_matches}/{max_terms}: {rejection}"));
        eprintln!(
            "budget {max_matches}/{max_terms}: {:?}, cost {} -> {}, {} derivation bytes",
            first.0.stages[0],
            dag_cost(&term),
            first.3,
            first.2.len()
        );
    }
}

/// `add(S, S)` with `S = (x0 * x1) * x2` and the rule `add(x, x) = mul(x,
/// 2)`. The per-class tree-cost choice takes `mul(S, 2)` (10 against 13)
/// and that form costs 10, more than the input's 7, because the input
/// shares `S`. The extractor returns the input.
#[test]
fn shared_subterm_tree_choice_is_costlier_and_the_input_is_returned() {
    const DOUBLE: &str = "(rule add_self (direction equiv) (domain u32) \
                          (lhs (add ?x ?x)) (rhs (mul ?x (const 2))) (where))";
    let naive = naive_rules(DOUBLE);
    let engine_rules = RuleSet::parse(DOUBLE).unwrap();
    let registry = Registry::parse(DOUBLE).unwrap();
    let shared = bin(
        Op::Mul,
        bin(Op::Mul, Term::Leaf(0), Term::Leaf(1)),
        Term::Leaf(2),
    );
    let term = bin(Op::Add, shared.clone(), shared.clone());
    let doubled = bin(Op::Mul, shared, Term::Const(2));

    // The fixture's premise, by this test's own cost functions.
    let forms = closure(&term, &naive);
    assert_eq!(forms, BTreeSet::from([term.clone(), doubled.clone()]));
    let tree_choice = forms.iter().min_by_key(|form| tree_cost(form)).unwrap();
    assert_eq!(tree_choice, &doubled);
    assert_eq!((tree_cost(&term), tree_cost(&doubled)), (13, 10));
    assert_eq!((dag_cost(&term), dag_cost(&doubled)), (7, 10));
    assert!(dag_cost(tree_choice) > dag_cost(&term));

    let input = region_of("shared", ScalarTy::U32, std::slice::from_ref(&term));
    let mut saturation = saturate(&input, &engine_rules, &schedule(&naive, 1_000, 10_000)).unwrap();
    assert!(saturation.stats().saturated());
    assert_eq!(saturation.forms(0), Some(2));
    let extracted = saturation.extract().unwrap();
    assert_eq!(extracted.cost_before, 7);
    assert_eq!(
        extracted.tree_choice_cost, 10,
        "the tree-cost choice is mul(S, 2)"
    );
    assert!(extracted.tree_choice_cost > extracted.cost_before);
    assert_eq!(extracted.cost_after, 7);
    assert!(!extracted.rewritten);
    assert_eq!(extracted.region.encode(), input.encode());
    assert_eq!(
        extracted.derivation,
        derivation::region_header_only("shared")
    );
    let verdict = check_region(
        &input.encode(),
        &extracted.region.encode(),
        &extracted.derivation,
        &registry,
    )
    .unwrap();
    assert_eq!((verdict.claims, verdict.changed_roots), (0, 0));

    // The graph does hold the costlier form, and can justify it.
    let target = region_of("shared", ScalarTy::U32, std::slice::from_ref(&doubled));
    let derivation = saturation
        .justify(&target)
        .unwrap()
        .expect("mul(S, 2) is in the class");
    check_region(&input.encode(), &target.encode(), &derivation, &registry).unwrap();
}

/// Sharing also wins: two roots that are one class become one node, which
/// the tree cost cannot see (it prices both roots either way).
#[test]
fn extraction_shares_one_node_between_two_roots() {
    let all = naive_rules(RULES);
    let rules = rules_named(&all, &["add_comm"]);
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let registry = Registry::parse(RULES).unwrap();
    let roots = [
        bin(Op::Add, Term::Leaf(0), Term::Leaf(1)),
        bin(Op::Add, Term::Leaf(1), Term::Leaf(0)),
    ];
    let input = region_of("two_roots", ScalarTy::U64, &roots);
    let mut saturation = saturate(&input, &engine_rules, &schedule(&rules, 1_000, 10_000)).unwrap();
    let extracted = saturation.extract().unwrap();
    assert_eq!((extracted.cost_before, extracted.cost_after), (2, 1));
    assert!(extracted.rewritten);
    assert_eq!(extracted.region.roots()[0], extracted.region.roots()[1]);
    let verdict = check_region(
        &input.encode(),
        &extracted.region.encode(),
        &extracted.derivation,
        &registry,
    )
    .unwrap();
    assert_eq!((verdict.claims, verdict.changed_roots), (1, 1));
    assert_eq!(verdict.rules_used, ["add_comm"]);
}

/// A declared schedule: the identities to their fixpoint, then
/// associativity and commutativity with the identities still on. Stages run
/// in order, each reports why it stopped, and a stage that names an unknown
/// or a one-way rule is refused.
///
/// The second stage keeps the identities because the first stage makes
/// classes cyclic (`x`, `x + 0` and `x * 1` are one class): associativity
/// alone then builds `x + (0 + 0)`, `x + ((0 + 0) + 0)` and so on without
/// end, and only `add_zero` and `mul_one` fold those back. The same test
/// pins that an associativity-and-commutativity stage alone stops on its
/// match budget instead of running on.
#[test]
fn a_declared_schedule_runs_its_stages_in_order() {
    staged_schedule_case();
}

/// The exit of Trust's Luminal ledger row `egglog-rules-staged-schedule`
/// (Luminal: a fixed stratified schedule that every fixture carries and
/// runs). Here a schedule is declared data: stages run once each in the
/// declared order, each to its fixpoint or its match budget, each firing
/// only the rules it names, each reporting why it stopped. Tier S has none
/// of Luminal's strata beyond that (no propagation rules, backend matchers,
/// copy-mint, metadata or cleanup passes).
#[test]
fn luminal_row_staged_schedule() {
    staged_schedule_case();
    println!("\nLUMINAL-ROW egglog-rules-staged-schedule PASS");
}

fn staged_schedule_case() {
    let all = naive_rules(RULES);
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let registry = Registry::parse(RULES).unwrap();
    // (x0 * 1 + 0) + (x1 + 0) * 1
    let term = bin(
        Op::Add,
        bin(
            Op::Add,
            bin(Op::Mul, Term::Leaf(0), Term::Const(1)),
            Term::Const(0),
        ),
        bin(
            Op::Mul,
            bin(Op::Add, Term::Leaf(1), Term::Const(0)),
            Term::Const(1),
        ),
    );
    let input = region_of("staged", ScalarTy::I32, std::slice::from_ref(&term));
    let staged = Schedule {
        stages: vec![
            stage(&rules_named(&all, &["add_zero", "mul_one"]), 1_000),
            stage(
                &rules_named(
                    &all,
                    &[
                        "add_comm",
                        "mul_comm",
                        "add_assoc_right",
                        "add_assoc_left",
                        "mul_assoc_right",
                        "mul_assoc_left",
                        "add_zero",
                        "mul_one",
                    ],
                ),
                100_000,
            ),
        ],
        max_terms: 100_000,
        max_extraction_trials: Schedule::DEFAULT_EXTRACTION_TRIALS,
    };
    // Associativity and commutativity alone never saturate a cyclic class:
    // the stage ends on its budget, and says so.
    let unbounded = Schedule {
        stages: vec![
            staged.stages[0].clone(),
            stage(&rules_named(&all, &AC), 2_000),
        ],
        ..staged.clone()
    };
    let cut = saturate(&input, &engine_rules, &unbounded).unwrap();
    assert!(!cut.stats().saturated(), "{:?}", cut.stats().stages);
    assert_eq!(cut.stats().stages[0].applied, 4);
    assert_eq!(cut.stats().stages[0].stop, Stop::Fixpoint);
    assert_eq!(cut.stats().stages[1].stop, Stop::MatchBudget);
    assert_eq!(cut.stats().stages[1].matches, 2_000);
    let mut saturation = saturate(&input, &engine_rules, &staged).unwrap();
    let stats = saturation.stats().clone();
    assert_eq!(stats.stages.len(), 2);
    assert!(stats.saturated(), "{:?}", stats.stages);
    assert_eq!(
        stats.stages[0].applied, 4,
        "four identities fire in the first stage"
    );
    assert!(stats.rule_applications.contains_key("add_zero"));
    assert!(stats.rule_applications.contains_key("add_comm"));
    let extracted = saturation.extract().unwrap();
    assert_eq!((extracted.cost_before, extracted.cost_after), (11, 1));
    let chosen = term_of(&extracted.region, extracted.region.roots()[0]);
    assert!(
        chosen == bin(Op::Add, Term::Leaf(0), Term::Leaf(1))
            || chosen == bin(Op::Add, Term::Leaf(1), Term::Leaf(0)),
        "{}",
        render(&chosen)
    );
    check_region(
        &input.encode(),
        &extracted.region.encode(),
        &extracted.derivation,
        &registry,
    )
    .unwrap();

    // The first stage alone leaves the commuted form out of the class.
    let only_identities = Schedule {
        stages: vec![staged.stages[0].clone()],
        ..staged.clone()
    };
    let mut first = saturate(&input, &engine_rules, &only_identities).unwrap();
    let commuted = region_of(
        "staged",
        ScalarTy::I32,
        &[bin(Op::Add, Term::Leaf(1), Term::Leaf(0))],
    );
    assert!(first.justify(&commuted).unwrap().is_none());
    assert!(saturation.justify(&commuted).unwrap().is_some());

    let unknown = Schedule {
        stages: vec![Stage {
            rules: vec!["no_such_rule".to_owned()],
            max_matches: 1,
        }],
        ..staged.clone()
    };
    assert_eq!(
        saturate(&input, &engine_rules, &unknown).err(),
        Some(SaturateError::UnknownRule("no_such_rule".to_owned()))
    );
    // A stage that names a one-way rule is refused; the one-stage schedule
    // of a rule set leaves such a rule out, so it names nothing here.
    const ONE_WAY: &str = "(rule drop_zero (direction refines) (domain i32) \
                           (lhs (add ?x (const 0))) (rhs ?x) (where))";
    let one_way = RuleSet::parse(ONE_WAY).unwrap();
    let names_it = Schedule {
        stages: vec![Stage {
            rules: vec!["drop_zero".to_owned()],
            max_matches: 10,
        }],
        ..staged.clone()
    };
    assert_eq!(
        saturate(&input, &one_way, &names_it).err(),
        Some(SaturateError::RefinesRule("drop_zero".to_owned()))
    );
    let single = Schedule::single(&one_way, 10, 100);
    assert!(single.stages[0].rules.is_empty());
    let mut untouched = saturate(&input, &one_way, &single).unwrap();
    assert!(untouched.stats().saturated());
    assert!(!untouched.extract().unwrap().rewritten);
}

/// Two runs of every term of four seeded corpora under a match budget that
/// cuts some of them short: statistics, region bytes and derivation bytes
/// are equal. One fixture is not enough: an extractor that walked its
/// classes in a per-instance hash order differed on about one term in
/// twenty.
#[test]
fn two_runs_of_every_corpus_term_give_identical_bytes() {
    let all = naive_rules(RULES);
    let mut names = AC.to_vec();
    names.extend(["add_zero", "mul_one"]);
    let rules = rules_named(&all, &names);
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let registry = Registry::parse(RULES).unwrap();
    let (mut terms, mut cut, mut rewritten) = (0usize, 0usize, 0usize);
    for pass in [1, 11, 12, 13] {
        for (index, (ty, term)) in corpus(pass, MAX_OPS_IDENTITY, &[0, 1, 2])
            .iter()
            .enumerate()
        {
            let input = region_of("twice", *ty, std::slice::from_ref(term));
            let run = || {
                let mut saturation =
                    saturate(&input, &engine_rules, &schedule(&rules, 300, usize::MAX)).unwrap();
                let stats = saturation.stats().clone();
                let extracted = saturation.extract().unwrap();
                (
                    stats,
                    extracted.region.encode(),
                    extracted.derivation,
                    extracted.rewritten,
                    extracted.trials,
                )
            };
            let (first, second) = (run(), run());
            let what = format!("pass {pass} term {index} {}", render(term));
            assert_eq!(first.0, second.0, "{what}: statistics differ");
            assert_eq!(first.1, second.1, "{what}: region bytes differ");
            assert_eq!(first.2, second.2, "{what}: derivation bytes differ");
            assert_eq!(first.4, second.4, "{what}: extraction trials differ");
            check_region(&input.encode(), &first.1, &first.2, &registry)
                .unwrap_or_else(|rejection| panic!("{what}: {rejection}"));
            terms += 1;
            cut += usize::from(first.0.stages[0].stop == Stop::MatchBudget);
            rewritten += usize::from(first.3);
        }
    }
    eprintln!("two runs: {terms} terms, {cut} cut by the match budget, {rewritten} rewritten");
    assert_eq!(terms, 4 * TERMS_PER_PASS);
    assert!(cut >= 20, "{cut} terms exhausted the budget");
    assert!(rewritten >= 40, "{rewritten} terms were rewritten");
}

/// The dual of the fixture above: the input is `mul(S, 2)` with `S = (x0 *
/// x1) * x2`, and the rule is `mul(x, 2) = add(x, x)`. The per-class
/// tree-cost choice is the input (10 against 13); priced with `S` once,
/// `add(S, S)` costs 7. An extractor that priced by tree cost, or counted a
/// shared class once per use, would return the input.
#[test]
fn a_shared_subterm_makes_the_cheaper_form_and_extraction_finds_it() {
    const HALVE: &str = "(rule mul_two (direction equiv) (domain u32) \
                         (lhs (mul ?x (const 2))) (rhs (add ?x ?x)) (where))";
    let naive = naive_rules(HALVE);
    let engine_rules = RuleSet::parse(HALVE).unwrap();
    let registry = Registry::parse(HALVE).unwrap();
    let shared = bin(
        Op::Mul,
        bin(Op::Mul, Term::Leaf(0), Term::Leaf(1)),
        Term::Leaf(2),
    );
    let term = bin(Op::Mul, shared.clone(), Term::Const(2));
    let doubled = bin(Op::Add, shared.clone(), shared);
    assert_eq!((tree_cost(&term), tree_cost(&doubled)), (10, 13));
    assert_eq!((dag_cost(&term), dag_cost(&doubled)), (10, 7));

    let input = region_of("shares", ScalarTy::U32, std::slice::from_ref(&term));
    let mut saturation = saturate(&input, &engine_rules, &schedule(&naive, 1_000, 10_000)).unwrap();
    assert!(saturation.stats().saturated());
    let extracted = saturation.extract().unwrap();
    assert_eq!(
        extracted.tree_choice_cost, 10,
        "the tree-cost choice is the input"
    );
    assert!(extracted.rewritten);
    assert_eq!((extracted.cost_before, extracted.cost_after), (10, 7));
    assert!(extracted.search_complete);
    assert_eq!(
        term_of(&extracted.region, extracted.region.roots()[0]),
        doubled
    );
    check_region(
        &input.encode(),
        &extracted.region.encode(),
        &extracted.derivation,
        &registry,
    )
    .unwrap();
}

/// Two roots, `(x0 + x2) + x1` and `(x0 + x3) + x1`, cost four additions.
/// `(x0 + x1) + x2` and `(x0 + x1) + x3` cost three, because they share
/// `x0 + x1`, a node neither input root has. Changing either root alone to
/// its shared form still costs four, so a search that changes one class at a
/// time stops at the input; the branch-and-bound search finds the form.
#[test]
fn extraction_finds_a_shared_form_that_needs_two_classes_to_change() {
    let all = naive_rules(RULES);
    let rules = rules_named(&all, &["add_comm", "add_assoc_right", "add_assoc_left"]);
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let registry = Registry::parse(RULES).unwrap();
    let ty = ScalarTy::U32;
    let sum = |a: Term, b: Term| bin(Op::Add, a, b);
    let leaf = Term::Leaf;
    let region = |roots: &[Term]| {
        let mut region = new_region("two_classes", ty, 4);
        for root in roots {
            let node = add_term(&mut region, ty, root);
            region.root(node).unwrap();
        }
        region
    };
    let input = region(&[
        sum(sum(leaf(0), leaf(2)), leaf(1)),
        sum(sum(leaf(0), leaf(3)), leaf(1)),
    ]);
    let wanted = region(&[
        sum(sum(leaf(0), leaf(1)), leaf(2)),
        sum(sum(leaf(0), leaf(1)), leaf(3)),
    ]);
    assert_eq!((input.cost(), wanted.cost()), (4, 3));

    let run = |max_extraction_trials: u64| {
        let schedule = Schedule {
            max_extraction_trials,
            ..schedule(&rules, 1_000_000, 1_000_000)
        };
        let mut saturation = saturate(&input, &engine_rules, &schedule).unwrap();
        assert!(saturation.stats().saturated());
        let extracted = saturation.extract().unwrap();
        check_region(
            &input.encode(),
            &extracted.region.encode(),
            &extracted.derivation,
            &registry,
        )
        .unwrap();
        extracted
    };
    let extracted = run(Schedule::DEFAULT_EXTRACTION_TRIALS);
    assert!(extracted.search_complete, "{} trials", extracted.trials);
    assert_eq!(extracted.tree_choice_cost, 4);
    assert_eq!((extracted.cost_before, extracted.cost_after), (4, 3));
    // Three additions, one of them under both roots.
    let roots = extracted.region.roots();
    let shared = |root: NodeId| match extracted.region.node(root) {
        Some(RegionNode::Op(_, args)) => args
            .iter()
            .copied()
            .find(|arg| matches!(extracted.region.node(*arg), Some(RegionNode::Op(..)))),
        _ => None,
    };
    assert!(shared(roots[0]).is_some());
    assert_eq!(shared(roots[0]), shared(roots[1]));

    // Without trials the search does not run: the input comes back, and
    // the result says the search did not end.
    let cut = run(0);
    assert!(!cut.search_complete);
    assert!(!cut.rewritten);
    assert_eq!(cut.cost_after, 4);
}

/// Congruence closure needs more than one pass over the terms. Three
/// matches are applied in one round, in this order: `a = add(p, p)` joins
/// the new term `mul(p, 2)`; `b = mul(2, r)` joins the new term `mul(r,
/// 2)`; `p = add(r, 0)` joins `r`. The rebuild's first pass meets `xor(a,
/// y)` and `xor(b, y)` before the two new terms, which only then become one
/// e-node and make `a` and `b` one class; the two older parents become one
/// e-node in the second pass. The fourth match is over the budget, so the
/// stage ends after this one round and no later rebuild can help.
#[test]
fn a_late_congruence_merges_two_older_parents_within_one_round() {
    const LATE: &str = "\
        (rule add_self (direction equiv) (domain u32) \
          (lhs (add ?x ?x)) (rhs (mul ?x (const 2))) (where))\n\
        (rule mul_comm (direction equiv) (domain u32) \
          (lhs (mul ?x ?y)) (rhs (mul ?y ?x)) (where))\n\
        (rule add_zero (direction equiv) (domain u32) \
          (lhs (add ?x (const 0))) (rhs ?x) (where))";
    let engine_rules = RuleSet::parse(LATE).unwrap();
    let registry = Registry::parse(LATE).unwrap();
    let ty = ScalarTy::U32;
    let (add, mul, xor) = (
        OpDesc::Bin(BinOpCode::Add, ty),
        OpDesc::Bin(BinOpCode::Mul, ty),
        OpDesc::Bin(BinOpCode::Xor, ty),
    );
    // `second` chooses what the second root is: `xor(b, y)` or `xor(a, y)`.
    let build = |second_is_first: bool| {
        let mut region = new_region("late", ty, 3);
        let r = region.leaf(leaf_name(0), ty).unwrap();
        let y = region.leaf(leaf_name(1), ty).unwrap();
        let z = region.leaf(leaf_name(2), ty).unwrap();
        let zero = region.constant(ty, 0).unwrap();
        let p = region.op(add, &[r, zero]).unwrap();
        let a = region.op(add, &[p, p]).unwrap();
        let two = region.constant(ty, 2).unwrap();
        let b = region.op(mul, &[two, r]).unwrap();
        let first = region.op(xor, &[a, y]).unwrap();
        let second = region.op(xor, &[b, y]).unwrap();
        let extra = region.op(add, &[z, zero]).unwrap();
        for root in [first, if second_is_first { first } else { second }, extra] {
            region.root(root).unwrap();
        }
        region
    };
    let input = build(false);
    let schedule = Schedule {
        stages: vec![Stage {
            rules: vec![
                "add_self".to_owned(),
                "mul_comm".to_owned(),
                "add_zero".to_owned(),
            ],
            max_matches: 3,
        }],
        max_terms: 1_000,
        max_extraction_trials: Schedule::DEFAULT_EXTRACTION_TRIALS,
    };
    let mut saturation = saturate(&input, &engine_rules, &schedule).unwrap();
    let stage = &saturation.stats().stages[0];
    assert_eq!(
        (stage.rounds, stage.matches, stage.applied, stage.stop),
        (1, 3, 3, Stop::MatchBudget)
    );
    // `xor(a, y)` is a form of the second root: the two parents are one
    // class after the one round.
    let target = build(true);
    let derivation = saturation
        .justify(&target)
        .unwrap()
        .expect("xor(a, y) and xor(b, y) are one class");
    let verdict = check_region(&input.encode(), &target.encode(), &derivation, &registry).unwrap();
    assert_eq!(verdict.changed_roots, 1);
    assert_eq!(verdict.rules_used, ["add_self", "add_zero", "mul_comm"]);
}

/// A chain `n_0 = bottom`, `n_i = xor(n_(i-1), x1)`, root `n_levels`.
fn chain(name: &str, levels: usize, bottom_plus_zero: bool) -> Region {
    let ty = ScalarTy::U32;
    let mut region = new_region(name, ty, 2);
    let x0 = region.leaf(leaf_name(0), ty).unwrap();
    let x1 = region.leaf(leaf_name(1), ty).unwrap();
    let mut node = if bottom_plus_zero {
        let zero = region.constant(ty, 0).unwrap();
        region
            .op(OpDesc::Bin(BinOpCode::Add, ty), &[x0, zero])
            .unwrap()
    } else {
        x0
    };
    for _ in 0..levels {
        node = region
            .op(OpDesc::Bin(BinOpCode::Xor, ty), &[node, x1])
            .unwrap();
    }
    region.root(node).unwrap();
    region
}

/// Regions far deeper than a thread's stack would allow a recursive walk
/// (a test thread has 2 MiB; the recursive walks this replaces overflowed
/// an 8 MiB stack between 3,000 and 15,000 levels): loading, extraction,
/// justification, the count of forms and the checker all finish. 1,500 is
/// the depth Tier E pins.
#[test]
fn deep_regions_do_not_recurse() {
    let empty = RuleSet::empty();
    let registry = Registry::parse(RULES).unwrap();
    for levels in [1_500usize, 20_000] {
        let input = chain("deep", levels, false);
        let schedule = Schedule {
            stages: Vec::new(),
            max_terms: usize::MAX,
            max_extraction_trials: Schedule::DEFAULT_EXTRACTION_TRIALS,
        };
        let mut saturation = saturate(&input, &empty, &schedule).unwrap();
        assert_eq!(saturation.forms(0), Some(1), "{levels}");
        let extracted = saturation.extract().unwrap();
        assert!(!extracted.rewritten, "{levels}");
        assert_eq!(extracted.cost_after, levels as u64, "{levels}");
        let same = saturation.justify(&input).unwrap().expect("the input");
        assert_eq!(same, derivation::region_header_only("deep"));
        let verdict = check_region(&input.encode(), &input.encode(), &same, &registry).unwrap();
        assert_eq!((verdict.roots, verdict.changed_roots), (1, 0));
    }
}

/// The same depth with a rewrite at the bottom: `add(x0, 0)` under 20,000
/// `xor` levels becomes `x0`, so the extracted root's proof is a congruence
/// 20,000 levels deep, and justifying the collapsed chain explains 20,000
/// congruence edges, each through the one below it.
#[test]
fn a_deep_congruence_cascade_is_explained_without_recursion() {
    let all = naive_rules(RULES);
    let rules = rules_named(&all, &["add_zero"]);
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let registry = Registry::parse(RULES).unwrap();
    for levels in [1_500usize, 20_000] {
        let input = chain("cascade", levels, true);
        let collapsed = chain("cascade", levels, false);
        let schedule = schedule(&rules, 1_000_000, usize::MAX);

        let mut saturation = saturate(&input, &engine_rules, &schedule).unwrap();
        assert!(saturation.stats().saturated());
        let extracted = saturation.extract().unwrap();
        assert!(extracted.rewritten, "{levels}");
        assert_eq!(
            (extracted.cost_before, extracted.cost_after),
            (levels as u64 + 2, levels as u64),
            "{levels}"
        );
        assert_eq!(extracted.region.encode(), collapsed.encode(), "{levels}");
        let verdict = check_region(
            &input.encode(),
            &extracted.region.encode(),
            &extracted.derivation,
            &registry,
        )
        .unwrap_or_else(|rejection| panic!("{levels}: {rejection}"));
        assert!(verdict.proof_steps > levels, "{}", verdict.proof_steps);

        // A graph that has not extracted: every collapsed level is a new
        // term joined to its class by a congruence edge.
        let mut saturation = saturate(&input, &engine_rules, &schedule).unwrap();
        let derivation = saturation
            .justify(&collapsed)
            .unwrap()
            .expect("the collapsed chain is a form of the root");
        let verdict = check_region(&input.encode(), &collapsed.encode(), &derivation, &registry)
            .unwrap_or_else(|rejection| panic!("{levels}: {rejection}"));
        assert_eq!(verdict.changed_roots, 1);
        assert!(verdict.proof_steps > levels, "{}", verdict.proof_steps);
    }
}

/// Derivations are paths of the proof forest and are not minimized: the
/// first justification that makes two terms one class is the one every
/// later proof uses. `add(x0, 0)` reaches `x0` through `add_comm` and
/// `zero_add` when a stage fires those first, and a later `add_zero` match
/// on the same pair is dropped; one stage with all three takes `add_zero`
/// directly. Same graph, same extracted form, three proof steps or one.
#[test]
fn proof_length_depends_on_the_order_of_stages() {
    const THREE: &str = "\
        (rule add_comm (direction equiv) (domain u32) \
          (lhs (add ?x ?y)) (rhs (add ?y ?x)) (where))\n\
        (rule zero_add (direction equiv) (domain u32) \
          (lhs (add (const 0) ?x)) (rhs ?x) (where))\n\
        (rule add_zero (direction equiv) (domain u32) \
          (lhs (add ?x (const 0))) (rhs ?x) (where))";
    let engine_rules = RuleSet::parse(THREE).unwrap();
    let registry = Registry::parse(THREE).unwrap();
    let term = bin(Op::Add, Term::Leaf(0), Term::Const(0));
    let input = region_of("length", ScalarTy::U32, std::slice::from_ref(&term));
    let stage = |names: &[&str]| Stage {
        rules: names.iter().map(|name| (*name).to_owned()).collect(),
        max_matches: 1_000,
    };
    let run = |stages: Vec<Stage>| {
        let schedule = Schedule {
            stages,
            max_terms: 1_000,
            max_extraction_trials: Schedule::DEFAULT_EXTRACTION_TRIALS,
        };
        let mut saturation = saturate(&input, &engine_rules, &schedule).unwrap();
        assert!(saturation.stats().saturated());
        let stats = saturation.stats().clone();
        let extracted = saturation.extract().unwrap();
        assert_eq!((extracted.cost_before, extracted.cost_after), (2, 0));
        let verdict = check_region(
            &input.encode(),
            &extracted.region.encode(),
            &extracted.derivation,
            &registry,
        )
        .unwrap();
        (
            stats.classes,
            verdict.proof_steps,
            verdict.rules_used,
            extracted.derivation.len(),
        )
    };
    let staged = run(vec![stage(&["add_comm", "zero_add"]), stage(&["add_zero"])]);
    let single = run(vec![stage(&["add_comm", "zero_add", "add_zero"])]);
    eprintln!("proof length: staged {staged:?}, single {single:?}");
    assert_eq!(staged.0, single.0, "the two graphs have the same classes");
    assert_eq!((staged.1, single.1), (3, 1));
    assert_eq!(staged.2, ["add_comm", "zero_add"]);
    assert_eq!(single.2, ["add_zero"]);
    assert!(staged.3 > single.3);
}

/// What the two saturation budgets count. `max_matches` counts every match
/// a round finds, also those an earlier round applied: on a sum of five
/// leaves under associativity and commutativity fewer than one match in ten
/// merges two classes. `max_terms` counts concrete terms, more than twice
/// the e-nodes here. A budget copied from an engine that counts otherwise
/// buys less than its number says.
#[test]
fn the_budgets_count_examined_matches_and_concrete_terms() {
    let all = naive_rules(RULES);
    let rules = rules_named(&all, &["add_comm", "add_assoc_right", "add_assoc_left"]);
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let ty = ScalarTy::U64;
    let mut input = new_region("units", ty, 5);
    let mut term = Term::Leaf(0);
    for index in 1..5 {
        term = bin(Op::Add, term, Term::Leaf(index));
    }
    let root = add_term(&mut input, ty, &term);
    input.root(root).unwrap();
    let saturation = saturate(
        &input,
        &engine_rules,
        &schedule(&rules, u64::MAX, usize::MAX),
    )
    .unwrap();
    let stats = saturation.stats();
    assert!(stats.saturated());
    let stage = &stats.stages[0];
    eprintln!(
        "units: {} matches, {} applied, {} terms, {} e-nodes, {} classes",
        stage.matches, stage.applied, stats.terms, stats.enodes, stats.classes
    );
    assert_eq!(
        (stage.matches, stage.applied, stats.terms, stats.enodes),
        (2_701, 247, 425, 185)
    );
    assert!(stage.matches > 10 * stage.applied);
    assert!(stats.terms > 2 * stats.enodes);

    // The same sum under a budget below the matches a fixpoint examines.
    let cut = saturate(&input, &engine_rules, &schedule(&rules, 1_000, usize::MAX)).unwrap();
    let stage = &cut.stats().stages[0];
    assert_eq!((stage.stop, stage.matches), (Stop::MatchBudget, 1_000));
    let cut = saturate(&input, &engine_rules, &schedule(&rules, u64::MAX, 200)).unwrap();
    assert_eq!(cut.stats().stages[0].stop, Stop::TermBudget);
    assert!(cut.stats().terms >= 200 && cut.stats().enodes < 200);
}

/// Two rule files that state `add_zero` and `mul_one` in the same words
/// compose into one set, on both sides; a name given to two statements is
/// refused; the one-stage schedule of a set with one-way rules fires its
/// equivalences; a restricted registry refuses a rule left out.
#[test]
fn rule_sets_compose_and_restrict() {
    let (identities, tier_s) = (
        RuleSet::parse(INTEGER_IDENTITIES).unwrap(),
        RuleSet::parse(RULES).unwrap(),
    );
    let both = identities.merged(&tier_s).unwrap();
    assert_eq!(
        both.rules().len(),
        identities.rules().len() + tier_s.rules().len() - 2
    );
    let registry = Registry::parse(INTEGER_IDENTITIES)
        .unwrap()
        .merged(&Registry::parse(RULES).unwrap())
        .unwrap();
    assert_eq!(
        registry.names(),
        both.rules()
            .iter()
            .map(|rule| rule.name())
            .collect::<Vec<_>>()
    );
    for rule in both.rules() {
        assert_eq!(
            Some(rule.statement_digest()),
            registry.statement_digest(rule.name())
        );
    }

    let other_text = RULES.replace("(lhs (add ?x (const 0)))", "(lhs (add ?x (const 1)))");
    let refused = tier_s
        .merged(&RuleSet::parse(&other_text).unwrap())
        .unwrap_err();
    assert_eq!(refused.kind, RuleErrorKind::DuplicateName);
    assert_eq!(refused.rule.as_deref(), Some("add_zero"));
    let refused = Registry::parse(RULES)
        .unwrap()
        .merged(&Registry::parse(&other_text).unwrap())
        .unwrap_err();
    assert_eq!(refused.rule.as_deref(), Some("add_zero"));

    // The Tier E file has one-way rules; the one-stage schedule leaves
    // them out and the whole set saturates a small term.
    let one_way: Vec<&str> = both
        .rules()
        .iter()
        .filter(|rule| !rule.is_equiv())
        .map(|rule| rule.name())
        .collect();
    assert!(!one_way.is_empty());
    let single = Schedule::single(&both, 2_000, 10_000);
    assert_eq!(
        single.stages[0].rules.len(),
        both.rules().len() - one_way.len()
    );
    assert!(
        single.stages[0]
            .rules
            .iter()
            .all(|name| !one_way.contains(&name.as_str()))
    );
    // (x0 + 0) * 1
    let term = bin(
        Op::Mul,
        bin(Op::Add, Term::Leaf(0), Term::Const(0)),
        Term::Const(1),
    );
    let input = region_of("composed", ScalarTy::U8, std::slice::from_ref(&term));
    let mut saturation = saturate(&input, &both, &single).unwrap();
    let extracted = saturation.extract().unwrap();
    assert_eq!((extracted.cost_before, extracted.cost_after), (6, 0));
    let verdict = check_region(
        &input.encode(),
        &extracted.region.encode(),
        &extracted.derivation,
        &registry,
    )
    .unwrap();
    assert!(!verdict.rules_used.is_empty());

    // Restriction: the engine fires only what is admitted, and a registry
    // without a rule refuses a derivation that names it.
    let used = verdict.rules_used.clone();
    let admitted = both.restricted(|rule| used.iter().any(|name| name == rule.name()));
    assert_eq!(admitted.rules().len(), used.len());
    let mut again = saturate(
        &input,
        &admitted,
        &Schedule::single(&admitted, 2_000, 10_000),
    )
    .unwrap();
    assert_eq!(again.extract().unwrap().cost_after, 0);
    let without = registry.restricted(|name, _| name != used[0]);
    assert_eq!(without.len(), registry.len() - 1);
    let rejection = check_region(
        &input.encode(),
        &extracted.region.encode(),
        &extracted.derivation,
        &without,
    )
    .unwrap_err();
    assert!(
        matches!(
            rejection,
            RegionRejection::Derivation(Rejection::UnknownRule { .. })
        ),
        "{rejection}"
    );
}

// ---------------------------------------------------------------------------
// Order-free nodes and pinned reductions.

const T: ScalarTy = ScalarTy::U32;

/// The leaves of the order-free fixtures: `x` (the operand), `y`, and `f`,
/// the result of an order-free node over `x` whose family is the orders 1
/// and 2.
struct Fixture {
    region: Region,
    x: NodeId,
    y: NodeId,
    f: NodeId,
}

fn fixture(name: &str, order_free: bool) -> Fixture {
    let mut region = new_region(name, T, 3);
    let x = region.leaf(leaf_name(0), T).unwrap();
    let y = region.leaf(leaf_name(1), T).unwrap();
    let f = region.leaf(leaf_name(2), T).unwrap();
    if order_free {
        region.make_order_free(f, x, &[1, 2]).unwrap();
    }
    Fixture { region, x, y, f }
}

fn pinned(region: &mut Region, order: u32, operand: NodeId) -> NodeId {
    region.op(OpDesc::Pinned(order, T), &[operand]).unwrap()
}

/// The proof pieces of the order-free fixtures in a forged derivation.
struct Forge {
    builder: DerivationBuilder,
    f: derivation::TermRef,
    y: derivation::TermRef,
}

fn forge(name: &str) -> Forge {
    let mut builder = DerivationBuilder::new_region(name);
    let f = builder.result(0, 2, 0);
    let y = builder.result(0, 1, 0);
    Forge { builder, f, y }
}

fn registry() -> Registry {
    Registry::parse(RULES).unwrap()
}

/// The input computes the reduction pinned at order 1 over `x`, and an
/// order-free node over the same `x` exists. A derivation that takes the
/// pinned reduction back to the order-free node, and from there to the
/// reduction pinned at order 2, is rejected: an implementation is read one
/// way only.
#[test]
fn a_pinned_reduction_rewritten_through_an_order_free_node_is_rejected() {
    let mut input = fixture("pinned", true);
    let root = pinned(&mut input.region, 1, input.x);
    input.region.root(root).unwrap();

    // To the other order.
    let mut output = fixture("pinned", true);
    let other = pinned(&mut output.region, 2, output.x);
    output.region.root(other).unwrap();
    let mut forged = forge("pinned");
    let (to_first, to_second) = (
        forged.builder.implement(forged.f, 1),
        forged.builder.implement(forged.f, 2),
    );
    let back = forged.builder.sym(to_first);
    let through = forged.builder.trans(back, to_second);
    forged.builder.claim(through);
    let rejection = check_region(
        &input.region.encode(),
        &output.region.encode(),
        &forged.builder.finish(),
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(&rejection, RegionRejection::PinnedThroughOrderFree { leaf, .. } if leaf == "Result(bb0, 2, 0)"),
        "{rejection}"
    );
    assert_eq!(rejection.class(), "pinned_through_order_free");

    // To the order-free node itself.
    let mut output = fixture("pinned", true);
    output.region.root(output.f).unwrap();
    let mut forged = forge("pinned");
    let to_first = forged.builder.implement(forged.f, 1);
    let back = forged.builder.sym(to_first);
    forged.builder.claim(back);
    let rejection = check_region(
        &input.region.encode(),
        &output.region.encode(),
        &forged.builder.finish(),
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(rejection, RegionRejection::PinnedThroughOrderFree { .. }),
        "{rejection}"
    );

    // Without the reversed step nothing concludes the pair.
    let mut output = fixture("pinned", true);
    let other = pinned(&mut output.region, 2, output.x);
    output.region.root(other).unwrap();
    let mut forged = forge("pinned");
    let to_second = forged.builder.implement(forged.f, 2);
    forged.builder.claim(to_second);
    let rejection = check_region(
        &input.region.encode(),
        &output.region.encode(),
        &forged.builder.finish(),
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(rejection, RegionRejection::RootUnjustified { root: 0, .. }),
        "{rejection}"
    );

    // The engine never does it: the pinned root stays, and the other order
    // is not a form of its class.
    let rules = RuleSet::parse(RULES).unwrap();
    let mut saturation = saturate(
        &input.region,
        &rules,
        &Schedule::single(&rules, 10_000, 10_000),
    )
    .unwrap();
    let extracted = saturation.extract().unwrap();
    assert!(!extracted.rewritten);
    assert_eq!(extracted.region.encode(), input.region.encode());
    assert!(saturation.justify(&output.region).unwrap().is_none());
}

/// The input reads one order-free node twice. An output that implements it
/// by two different pinned reductions, or implements one use and keeps the
/// node for the other, is rejected; implementing both uses by the same
/// reduction is accepted.
#[test]
fn an_order_free_node_elaborated_at_two_sites_is_rejected() {
    let add = OpDesc::Bin(BinOpCode::Add, T);
    let mul = OpDesc::Bin(BinOpCode::Mul, T);
    let mut input = fixture("sites", true);
    let sum = input.region.op(add, &[input.f, input.y]).unwrap();
    let product = input.region.op(mul, &[input.f, input.y]).unwrap();
    input.region.root(sum).unwrap();
    input.region.root(product).unwrap();

    // `left` and `right`: the order each use is implemented at, or `None`
    // to keep the order-free node for that use.
    let attempt = |left: Option<u32>, right: Option<u32>| {
        let kept = left.is_none() || right.is_none();
        let mut output = fixture("sites", kept);
        let mut forged = forge("sites");
        let mut side = |order: Option<u32>, desc: OpDesc| {
            let operand = match order {
                Some(order) => pinned(&mut output.region, order, output.x),
                None => output.f,
            };
            let node = output.region.op(desc, &[operand, output.y]).unwrap();
            output.region.root(node).unwrap();
            if let Some(order) = order {
                let implement = forged.builder.implement(forged.f, order);
                let same = forged.builder.refl(forged.y);
                let step = forged.builder.congr(desc, &[implement, same]);
                forged.builder.claim(step);
            }
        };
        side(left, add);
        side(right, mul);
        check_region(
            &input.region.encode(),
            &output.region.encode(),
            &forged.builder.finish(),
            &registry(),
        )
    };

    let two_orders = attempt(Some(1), Some(2)).unwrap_err();
    assert!(
        matches!(&two_orders, RegionRejection::OrderFreeAtTwoSites { leaf, .. } if leaf == "Result(bb0, 2, 0)"),
        "{two_orders}"
    );
    assert_eq!(two_orders.class(), "order_free_at_two_sites");
    for (left, right) in [(Some(1), None), (None, Some(2))] {
        let kept_too = attempt(left, right).unwrap_err();
        assert!(
            matches!(kept_too, RegionRejection::OrderFreeAtTwoSites { .. }),
            "{kept_too}"
        );
    }

    let one_site = attempt(Some(2), Some(2)).unwrap();
    assert_eq!(
        (one_site.order_free_implemented, one_site.order_free_kept),
        (1, 0)
    );
    let untouched = attempt(None, None).unwrap();
    assert_eq!(
        (untouched.order_free_implemented, untouched.order_free_kept),
        (0, 1)
    );

    // An order outside the family, and an output that reads the node's
    // result without having the node.
    let mut output = fixture("sites", false);
    let operand = pinned(&mut output.region, 3, output.x);
    for desc in [add, mul] {
        let node = output.region.op(desc, &[operand, output.y]).unwrap();
        output.region.root(node).unwrap();
    }
    let mut forged = forge("sites");
    let implement = forged.builder.implement(forged.f, 3);
    let same = forged.builder.refl(forged.y);
    for desc in [add, mul] {
        let step = forged.builder.congr(desc, &[implement, same]);
        forged.builder.claim(step);
    }
    let outside = check_region(
        &input.region.encode(),
        &output.region.encode(),
        &forged.builder.finish(),
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(
            outside,
            RegionRejection::Derivation(Rejection::ImplementMismatch { .. })
        ),
        "{outside}"
    );

    let mut output = fixture("sites", false);
    for desc in [add, mul] {
        let node = output.region.op(desc, &[output.f, output.y]).unwrap();
        output.region.root(node).unwrap();
    }
    let dropped = check_region(
        &input.region.encode(),
        &output.region.encode(),
        &derivation::region_header_only("sites"),
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(dropped, RegionRejection::OrderFreeDropped { .. }),
        "{dropped}"
    );
}

/// The engine's own elaboration: the region already computes the reduction
/// pinned at order 1 over `x`, so the order-free node over `x` is
/// implemented by that one node, once, for both of its uses.
#[test]
fn the_engine_elaborates_an_order_free_node_once() {
    let add = OpDesc::Bin(BinOpCode::Add, T);
    let mul = OpDesc::Bin(BinOpCode::Mul, T);
    let rules = RuleSet::parse(RULES).unwrap();
    for pinned_first in [true, false] {
        let mut input = fixture("elaborate", true);
        let exact = pinned(&mut input.region, 1, input.x);
        let sum = input.region.op(add, &[input.f, input.y]).unwrap();
        let product = input.region.op(mul, &[input.f, input.y]).unwrap();
        let roots = if pinned_first {
            [exact, sum, product]
        } else {
            [sum, product, exact]
        };
        for root in roots {
            input.region.root(root).unwrap();
        }
        // pinned 4 + order-free 4 + add 1 + mul 3
        assert_eq!(input.region.cost(), 12);

        let mut saturation = saturate(
            &input.region,
            &rules,
            &Schedule::single(&rules, 10_000, 10_000),
        )
        .unwrap();
        let extracted = saturation.extract().unwrap();
        assert!(extracted.rewritten, "pinned first: {pinned_first}");
        assert_eq!((extracted.cost_before, extracted.cost_after), (12, 8));
        assert!(extracted.region.order_free().is_empty());
        let verdict = check_region(
            &input.region.encode(),
            &extracted.region.encode(),
            &extracted.derivation,
            &registry(),
        )
        .unwrap_or_else(|rejection| panic!("pinned first {pinned_first}: {rejection}"));
        assert_eq!(
            (verdict.order_free_implemented, verdict.order_free_kept),
            (1, 0)
        );
        assert_eq!(verdict.changed_roots, 2);
        // One implementation, by the reduction the region already had.
        assert_eq!(extracted.implemented, [(leaf_name(2), 1)]);
        assert_eq!(verdict.pinned_added, 0);

        // Alone, the node is kept: an implementation costs the same.
        let mut alone = fixture("elaborate", true);
        let sum = alone.region.op(add, &[alone.f, alone.y]).unwrap();
        alone.region.root(sum).unwrap();
        let mut saturation = saturate(
            &alone.region,
            &rules,
            &Schedule::single(&rules, 10_000, 10_000),
        )
        .unwrap();
        let extracted = saturation.extract().unwrap();
        assert!(!extracted.rewritten);
        assert_eq!(extracted.region.order_free().len(), 1);
        assert!(extracted.implemented.is_empty());
    }
}

/// What "one order" means. The input reads one order-free node twice; the
/// output implements both uses at order 1, but under one of them the
/// operand is rewritten to `x + 0` after the `Impl` step. The two
/// reductions are one value (same order, operands a proof relates), so the
/// region is accepted, and the verdict says the output adds two pinned
/// reductions for the one implemented node. The engine's extractor never
/// produces this (one option per class).
#[test]
fn one_order_over_two_related_operands_is_accepted_and_counted() {
    let add = OpDesc::Bin(BinOpCode::Add, T);
    let mul = OpDesc::Bin(BinOpCode::Mul, T);
    let mut input = fixture("related", true);
    let sum = input.region.op(add, &[input.f, input.y]).unwrap();
    let product = input.region.op(mul, &[input.f, input.y]).unwrap();
    input.region.root(sum).unwrap();
    input.region.root(product).unwrap();

    let mut output = fixture("related", false);
    let plain = pinned(&mut output.region, 1, output.x);
    let zero = output.region.constant(T, 0).unwrap();
    let padded = output.region.op(add, &[output.x, zero]).unwrap();
    let rewritten = pinned(&mut output.region, 1, padded);
    let sum = output.region.op(add, &[plain, output.y]).unwrap();
    let product = output.region.op(mul, &[rewritten, output.y]).unwrap();
    output.region.root(sum).unwrap();
    output.region.root(product).unwrap();

    let registry = registry();
    let mut forged = forge("related");
    let x = forged.builder.result(0, 0, 0);
    let implement = forged.builder.implement(forged.f, 1);
    let same = forged.builder.refl(forged.y);
    let first = forged.builder.congr(add, &[implement, same]);
    let add_zero = forged
        .builder
        .rule("add_zero", registry.statement_digest("add_zero").unwrap());
    let fold = forged.builder.rule_step(add_zero, T, &[("x", x)], 0);
    let unfold = forged.builder.sym(fold);
    let under = forged.builder.congr(OpDesc::Pinned(1, T), &[unfold]);
    let moved = forged.builder.trans(implement, under);
    let second = forged.builder.congr(mul, &[moved, same]);
    forged.builder.claim(first);
    forged.builder.claim(second);
    let verdict = check_region(
        &input.region.encode(),
        &output.region.encode(),
        &forged.builder.finish(),
        &registry,
    )
    .unwrap();
    assert_eq!(
        (verdict.order_free_implemented, verdict.pinned_added),
        (1, 2)
    );
}

/// A pinned reduction at an order the input does not name is refused,
/// wherever it appears. `sub(x, x) = 0` leaves `x` free on one side, so
/// read backwards it can introduce any term, a reduction pinned at order 99
/// among them; nothing says such a reduction is defined.
#[test]
fn a_pinned_order_the_input_does_not_name_is_rejected() {
    const SUB_SELF: &str = "(rule sub_self (direction equiv) (domain u32) \
                            (lhs (sub ?x ?x)) (rhs (const 0)) (where))";
    let registry = Registry::parse(SUB_SELF).unwrap();
    let digest = registry.statement_digest("sub_self").unwrap();
    let sub = OpDesc::Bin(BinOpCode::Sub, T);

    // `order_free`: whether the input has the order-free node (family 1, 2).
    // The input root is 0; the output root is the difference of the
    // reduction pinned at `order` over `x` with itself.
    let attempt = |order_free: bool, order: u32| {
        let mut input = fixture("unnamed", order_free);
        let zero = input.region.constant(T, 0).unwrap();
        input.region.root(zero).unwrap();
        let mut output = fixture("unnamed", order_free);
        let reduction = pinned(&mut output.region, order, output.x);
        let difference = output.region.op(sub, &[reduction, reduction]).unwrap();
        output.region.root(difference).unwrap();

        let mut builder = DerivationBuilder::new_region("unnamed");
        let x = builder.result(0, 0, 0);
        let reduction = builder.op(OpDesc::Pinned(order, T), &[x]);
        let rule = builder.rule("sub_self", digest);
        let fold = builder.rule_step(rule, T, &[("x", reduction)], 0);
        let unfold = builder.sym(fold);
        builder.claim(unfold);
        check_region(
            &input.region.encode(),
            &output.region.encode(),
            &builder.finish(),
            &registry,
        )
    };
    let rejection = attempt(false, 99).unwrap_err();
    assert!(
        matches!(
            &rejection,
            RegionRejection::PinnedOrderIntroduced {
                order: 99,
                ty: "u32",
                ..
            }
        ),
        "{rejection}"
    );
    assert_eq!(rejection.class(), "pinned_order_introduced");
    // An order outside the family is as unnamed as any other.
    assert!(matches!(
        attempt(true, 3),
        Err(RegionRejection::PinnedOrderIntroduced { order: 3, .. })
    ));
    // An order of the family is named: the premise covers it.
    let verdict = attempt(true, 2).unwrap();
    assert_eq!((verdict.order_free_kept, verdict.pinned_added), (1, 1));

    // In the derivation only: `sub(x, x)` goes to 0, out to the unnamed
    // reduction and back. Both regions are free of it and it is refused.
    let mut input = fixture("unnamed", false);
    let difference = input.region.op(sub, &[input.x, input.x]).unwrap();
    input.region.root(difference).unwrap();
    let mut output = fixture("unnamed", false);
    let zero = output.region.constant(T, 0).unwrap();
    output.region.root(zero).unwrap();
    let mut builder = DerivationBuilder::new_region("unnamed");
    let x = builder.result(0, 0, 0);
    let reduction = builder.op(OpDesc::Pinned(99, T), &[x]);
    let rule = builder.rule("sub_self", digest);
    let direct = builder.rule_step(rule, T, &[("x", x)], 0);
    let fold = builder.rule_step(rule, T, &[("x", reduction)], 0);
    let unfold = builder.sym(fold);
    let detour = builder.trans(unfold, fold);
    let through = builder.trans(direct, detour);
    builder.claim(through);
    let rejection = check_region(
        &input.region.encode(),
        &output.region.encode(),
        &builder.finish(),
        &registry,
    )
    .unwrap_err();
    assert!(
        matches!(
            rejection,
            RegionRejection::PinnedOrderIntroduced { order: 99, .. }
        ),
        "{rejection}"
    );
    // The direct step alone is accepted.
    let mut builder = DerivationBuilder::new_region("unnamed");
    let x = builder.result(0, 0, 0);
    let rule = builder.rule("sub_self", digest);
    let direct = builder.rule_step(rule, T, &[("x", x)], 0);
    builder.claim(direct);
    check_region(
        &input.region.encode(),
        &output.region.encode(),
        &builder.finish(),
        &registry,
    )
    .unwrap();
}

// ---------------------------------------------------------------------------
// Wrong derivations and wrong regions.

/// A correct result stops being accepted when any part of the triple is
/// changed: another registry, another output, a function derivation, a
/// truncated region.
#[test]
fn the_checker_rejects_what_the_engine_did_not_derive() {
    let all = naive_rules(RULES);
    let rules = rules_named(&all, &["add_zero", "add_comm"]);
    let engine_rules = RuleSet::parse(RULES).unwrap();
    let term = bin(
        Op::Add,
        bin(Op::Add, Term::Leaf(0), Term::Const(0)),
        Term::Leaf(1),
    );
    let input = region_of("wrong", ScalarTy::U8, std::slice::from_ref(&term));
    let mut saturation = saturate(&input, &engine_rules, &schedule(&rules, 1_000, 10_000)).unwrap();
    let extracted = saturation.extract().unwrap();
    assert!(extracted.rewritten);
    let (input_bytes, output_bytes) = (input.encode(), extracted.region.encode());
    check_region(
        &input_bytes,
        &output_bytes,
        &extracted.derivation,
        &registry(),
    )
    .unwrap();

    // A registry whose `add_zero` states something else.
    let other =
        Registry::parse(&RULES.replace("(lhs (add ?x (const 0)))", "(lhs (add ?x (const 1)))"))
            .unwrap();
    let rejection =
        check_region(&input_bytes, &output_bytes, &extracted.derivation, &other).unwrap_err();
    assert!(
        matches!(
            rejection,
            RegionRejection::Derivation(Rejection::DigestMismatch { .. })
        ),
        "{rejection}"
    );

    // Another output: `x0 * x1` is not what the derivation concludes.
    let product = region_of(
        "wrong",
        ScalarTy::U8,
        &[bin(Op::Mul, Term::Leaf(0), Term::Leaf(1))],
    );
    let rejection = check_region(
        &input_bytes,
        &product.encode(),
        &extracted.derivation,
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(rejection, RegionRejection::RootUnjustified { root: 0, .. }),
        "{rejection}"
    );

    // The right output with no derivation, and with a function derivation.
    let rejection = check_region(
        &input_bytes,
        &output_bytes,
        &derivation::region_header_only("wrong"),
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(rejection, RegionRejection::RootUnjustified { .. }),
        "{rejection}"
    );
    let rejection = check_region(
        &input_bytes,
        &output_bytes,
        &derivation::header_only("wrong"),
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(
            rejection,
            RegionRejection::Derivation(Rejection::Decode { .. })
        ),
        "{rejection}"
    );

    // Another region name, a truncated region, an unchanged region with a
    // claim that justifies nothing.
    let renamed = region_of("other", ScalarTy::U8, std::slice::from_ref(&term));
    let rejection = check_region(
        &renamed.encode(),
        &output_bytes,
        &extracted.derivation,
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(rejection, RegionRejection::RegionMismatch { .. }),
        "{rejection}"
    );
    let rejection = check_region(
        &input_bytes,
        &output_bytes[..output_bytes.len() - 1],
        &extracted.derivation,
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(rejection, RegionRejection::MalformedRegion { .. }),
        "{rejection}"
    );
    let rejection = check_region(
        &input_bytes,
        &input_bytes,
        &extracted.derivation,
        &registry(),
    )
    .unwrap_err();
    assert!(
        matches!(rejection, RegionRejection::ClaimMismatch { .. }),
        "{rejection}"
    );
}

// ---------------------------------------------------------------------------
// No budget is a clock.

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            out.push(path);
        }
    }
}

/// The engine's sources name neither clock type (the same substring search
/// as the package's exit command, so comments count too), and neither
/// crate's sources name what would make two runs differ: a hashed map or
/// set (iteration order per instance), the hasher's random state, the
/// environment or a thread.
#[test]
fn the_engine_reads_no_clock() {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    rust_files(&crate_dir.join("src"), &mut files);
    assert!(
        files
            .iter()
            .any(|path| path.ends_with("saturate/egraph.rs"))
    );
    let engine_files = files.len();
    rust_files(&crate_dir.join("../trust-cg-eqsat-check/src"), &mut files);
    assert!(files.iter().any(|path| path.ends_with("src/region.rs")));
    let clocks = [["Ins", "tant"].concat(), ["System", "Time"].concat()];
    let unordered = [
        ["Hash", "Map"].concat(),
        ["Hash", "Set"].concat(),
        ["Random", "State"].concat(),
        ["std::", "env"].concat(),
        ["std::", "thread"].concat(),
    ];
    for (index, path) in files.iter().enumerate() {
        let text = std::fs::read_to_string(path).unwrap();
        // The clock words are the exit command's, over the engine crate.
        let words = clocks
            .iter()
            .filter(|_| index < engine_files)
            .chain(&unordered);
        for word in words {
            assert!(
                !text.contains(word.as_str()),
                "{} names {word}",
                path.display()
            );
        }
    }
}
