// trust-cg-eqsat-check/src/registry.rs - rule-file parser, well-formedness, canonical text and digest
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker's own reader of rule files (docs/eqsat-tier-e.md section 5).
//!
//! [`Registry::parse`] accepts a file only if every rule satisfies every
//! well-formedness clause of section 5.1; any other text is a
//! [`RegistryError`]. The registry is the authority on which rules exist, on
//! their direction and on their statement digest (section 5.2). It holds
//! statements only: no rule here is proved (PKG-U2 attaches discharge records).
//!
//! Section 5.1 clauses that are easy to read loosely, as this parser reads
//! them:
//! * sorts are symbols: `T` and `bool` are distinct sorts even for a domain
//!   that contains `bool`, so a pattern is well sorted at every instance type
//!   at once;
//! * outside comments only printable ASCII and space, tab, LF, CR and FF may
//!   appear; lists nest at most 64 deep; a file with no rules is an empty
//!   registry;
//! * a constant variable in the rhs may be written `?c` or `(const ?c)`, a
//!   term variable only `?x`, and no variable is both anywhere in the rule;
//! * `(eval select ...)` is refused: eval's `OP` is not `select`.

use std::collections::BTreeMap;
use std::fmt;

use crate::types::{ALL_BIN, ALL_PRED, ALL_UN, BinK, OpDesc, Pred, Sty, UnK, mask};

/// The digest domain of a rule statement (section 5.2).
pub(crate) const STATEMENT_DOMAIN: &str = "trust-cg-eqsat.rule-statement.v1";

/// Why a rule text was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegistryError {
    /// 1-based line of the offending token.
    pub line: usize,
    /// The rule being read, when its name was already read.
    pub rule: Option<String>,
    /// What is wrong.
    pub message: String,
}

impl fmt::Display for RegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.rule {
            Some(rule) => write!(
                f,
                "rule file line {}: rule {}: {}",
                self.line, rule, self.message
            ),
            None => write!(f, "rule file line {}: {}", self.line, self.message),
        }
    }
}

impl std::error::Error for RegistryError {}

/// A rule's direction (section 5.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Direction {
    Equiv,
    Refines,
}

/// A sort: the instance type `T`, or `bool`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Sort {
    T,
    Bool,
}

impl Sort {
    pub(crate) fn at(self, t: Sty) -> Sty {
        match self {
            Sort::T => t,
            Sort::Bool => Sty::Bool,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Sort::T => "T",
            Sort::Bool => "bool",
        }
    }
}

/// An `OP` of a rule (section 5.1 table).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ROp {
    Bin(BinK),
    Un(UnK),
    Cmp(Pred),
    Select,
}

impl ROp {
    fn from_name(name: &str) -> Option<ROp> {
        if name == "select" {
            return Some(ROp::Select);
        }
        if let Some(pred) = name.strip_prefix("icmp.") {
            return ALL_PRED
                .iter()
                .copied()
                .find(|p| p.name() == pred)
                .map(ROp::Cmp);
        }
        if let Some(k) = ALL_BIN.iter().copied().find(|k| k.name() == name) {
            return Some(ROp::Bin(k));
        }
        ALL_UN
            .iter()
            .copied()
            .find(|k| k.name() == name)
            .map(ROp::Un)
    }

    /// Operand sorts and result sort.
    pub(crate) fn sorts(self) -> (Vec<Sort>, Sort) {
        match self {
            ROp::Bin(k) if k.is_bool_only() => (vec![Sort::Bool, Sort::Bool], Sort::Bool),
            ROp::Bin(_) => (vec![Sort::T, Sort::T], Sort::T),
            ROp::Un(_) => (vec![Sort::T], Sort::T),
            ROp::Cmp(_) => (vec![Sort::T, Sort::T], Sort::Bool),
            ROp::Select => (vec![Sort::Bool, Sort::T, Sort::T], Sort::T),
        }
    }

    /// The term operator this `OP` denotes at instance type `t`.
    pub(crate) fn at(self, t: Sty) -> OpDesc {
        match self {
            ROp::Bin(k) if k.is_bool_only() => OpDesc::Bin(k, Sty::Bool),
            ROp::Bin(k) => OpDesc::Bin(k, t),
            ROp::Un(k) => OpDesc::Un(k, t),
            ROp::Cmp(p) => OpDesc::Cmp(p, t),
            ROp::Select => OpDesc::Select(t),
        }
    }

    fn name(self) -> String {
        match self {
            ROp::Bin(k) => k.name().to_owned(),
            ROp::Un(k) => k.name().to_owned(),
            ROp::Cmp(p) => format!("icmp.{}", p.name()),
            ROp::Select => "select".to_owned(),
        }
    }
}

/// An `INT` literal in `[-2^127, 2^128 - 1]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Int {
    neg: bool,
    mag: u128,
}

impl Int {
    /// Parses `-?[0-9]+` within the section 5.1 range.
    fn parse(text: &str) -> Option<Int> {
        let (neg, digits) = match text.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, text),
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let mut mag: u128 = 0;
        for b in digits.bytes() {
            mag = mag.checked_mul(10)?.checked_add(u128::from(b - b'0'))?;
        }
        if neg && mag > (1u128 << 127) {
            return None;
        }
        Some(Int {
            neg: neg && mag != 0,
            mag,
        })
    }

    /// `INT mod 2^w`.
    pub(crate) fn residue(self, w: u32) -> u128 {
        if self.neg {
            self.mag.wrapping_neg() & mask(w)
        } else {
            self.mag & mask(w)
        }
    }

    fn canonical(self) -> String {
        if self.neg {
            format!("-{}", self.mag)
        } else {
            self.mag.to_string()
        }
    }
}

/// A side condition (section 5.1 `COND`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Cond {
    Eq(String, Int),
    Ne(String, Int),
    Pow2(String),
    ZeroModWidth(String),
}

/// A pattern (section 5.1 `PAT`). Variable names exclude the `?`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Pat {
    Var(String),
    ConstInt(Int),
    ConstVar(String),
    Bool(bool),
    Op(ROp, Vec<Pat>),
    Eval(ROp, Vec<String>),
}

/// What the rule says about one of its variables.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct VarInfo {
    pub(crate) sort: Sort,
    /// Every lhs occurrence is `(const ?v)`: it matches only constants.
    pub(crate) constant: bool,
}

/// One registered rule statement.
#[derive(Clone, Debug)]
pub(crate) struct Rule {
    pub(crate) name: String,
    pub(crate) direction: Direction,
    pub(crate) domain: Vec<Sty>,
    pub(crate) lhs: Pat,
    pub(crate) rhs: Pat,
    pub(crate) conds: Vec<Cond>,
    pub(crate) vars: BTreeMap<String, VarInfo>,
    pub(crate) canonical: String,
    pub(crate) digest: [u8; 32],
}

/// The rule registry: the statements the checker accepts derivations over.
#[derive(Clone, Debug)]
pub struct Registry {
    rules: Vec<Rule>,
    by_name: BTreeMap<String, usize>,
}

impl Registry {
    /// Parses a rule file, refusing everything section 5.1 refuses.
    pub fn parse(text: &str) -> Result<Registry, RegistryError> {
        let tokens = tokenize(text)?;
        let forms = parse_sexprs(&tokens)?;
        let mut rules = Vec::new();
        let mut by_name = BTreeMap::new();
        for form in &forms {
            let rule = read_rule(form)?;
            if by_name.contains_key(&rule.name) {
                return Err(RegistryError {
                    line: form.line(),
                    rule: Some(rule.name.clone()),
                    message: "duplicate rule name".to_owned(),
                });
            }
            by_name.insert(rule.name.clone(), rules.len());
            rules.push(rule);
        }
        Ok(Registry { rules, by_name })
    }

    /// The number of rules.
    pub fn len(&self) -> usize {
        self.rules.len()
    }

    /// Whether the registry holds no rule.
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// The rule names, in file order.
    pub fn names(&self) -> Vec<String> {
        self.rules.iter().map(|r| r.name.clone()).collect()
    }

    /// The statement digest of rule `name` (section 5.2).
    pub fn statement_digest(&self, name: &str) -> Option<[u8; 32]> {
        self.rule(name).map(|r| r.digest)
    }

    /// The canonical text of rule `name` (section 5.2).
    pub fn canonical_text(&self, name: &str) -> Option<String> {
        self.rule(name).map(|r| r.canonical.clone())
    }

    pub(crate) fn rule(&self, name: &str) -> Option<&Rule> {
        self.by_name.get(name).and_then(|&i| self.rules.get(i))
    }
}

// ---------------------------------------------------------------- tokens

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Open,
    Close,
    Atom(String),
}

fn tokenize(text: &str) -> Result<Vec<(Tok, usize)>, RegistryError> {
    let mut out = Vec::new();
    let mut line = 1usize;
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\n' => line += 1,
            ' ' | '\t' | '\r' | '\x0c' => {}
            ';' => {
                for c in chars.by_ref() {
                    if c == '\n' {
                        line += 1;
                        break;
                    }
                }
            }
            '(' => out.push((Tok::Open, line)),
            ')' => out.push((Tok::Close, line)),
            c if c.is_ascii_graphic() => {
                let mut atom = String::from(c);
                while let Some(&n) = chars.peek() {
                    if n.is_ascii_graphic() && n != '(' && n != ')' && n != ';' {
                        atom.push(n);
                        chars.next();
                    } else {
                        break;
                    }
                }
                out.push((Tok::Atom(atom), line));
            }
            other => {
                return Err(RegistryError {
                    line,
                    rule: None,
                    message: format!(
                        "character U+{:04X} outside a comment is not admitted",
                        u32::from(other)
                    ),
                });
            }
        }
    }
    Ok(out)
}

/// The deepest list nesting a rule file may use. The readers below recurse
/// over patterns, so the bound keeps them off unbounded stack depth.
const MAX_DEPTH: usize = 64;

#[derive(Clone, Debug)]
enum SExpr {
    Atom(String, usize),
    List(Vec<SExpr>, usize),
}

impl SExpr {
    fn line(&self) -> usize {
        match self {
            SExpr::Atom(_, l) | SExpr::List(_, l) => *l,
        }
    }
}

fn parse_sexprs(tokens: &[(Tok, usize)]) -> Result<Vec<SExpr>, RegistryError> {
    // Iterative to keep deep nesting off the call stack.
    let mut stack: Vec<(Vec<SExpr>, usize)> = vec![(Vec::new(), 1)];
    for (tok, line) in tokens {
        match tok {
            Tok::Open => {
                if stack.len() > MAX_DEPTH {
                    return Err(RegistryError {
                        line: *line,
                        rule: None,
                        message: format!("nesting deeper than {MAX_DEPTH} lists is refused"),
                    });
                }
                stack.push((Vec::new(), *line));
            }
            Tok::Close => {
                if stack.len() < 2 {
                    return Err(RegistryError {
                        line: *line,
                        rule: None,
                        message: "unbalanced ')'".to_owned(),
                    });
                }
                let (items, open_line) = stack.pop().unwrap_or_default();
                if let Some((parent, _)) = stack.last_mut() {
                    parent.push(SExpr::List(items, open_line));
                }
            }
            Tok::Atom(a) => {
                if let Some((top, _)) = stack.last_mut() {
                    top.push(SExpr::Atom(a.clone(), *line));
                }
            }
        }
    }
    if stack.len() != 1 {
        let line = stack.last().map(|(_, l)| *l).unwrap_or(1);
        return Err(RegistryError {
            line,
            rule: None,
            message: "unbalanced '(' (missing ')')".to_owned(),
        });
    }
    Ok(stack.pop().map(|(items, _)| items).unwrap_or_default())
}

// ---------------------------------------------------------------- rules

struct RuleReader {
    name: Option<String>,
}

impl RuleReader {
    fn err(&self, line: usize, message: impl Into<String>) -> RegistryError {
        RegistryError {
            line,
            rule: self.name.clone(),
            message: message.into(),
        }
    }

    /// A list `(KEYWORD items...)`, returning the items after the keyword.
    fn clause<'a>(&self, form: &'a SExpr, keyword: &str) -> Result<&'a [SExpr], RegistryError> {
        match form {
            SExpr::List(items, line) => match items.first() {
                Some(SExpr::Atom(k, _)) if k == keyword => Ok(&items[1..]),
                _ => Err(self.err(*line, format!("expected the ({keyword} ...) clause"))),
            },
            SExpr::Atom(a, line) => Err(self.err(
                *line,
                format!("expected the ({keyword} ...) clause, found atom {a}"),
            )),
        }
    }
}

fn is_name(s: &str) -> bool {
    let mut bytes = s.bytes();
    matches!(bytes.next(), Some(b'a'..=b'z'))
        && bytes.all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
}

fn var_name(s: &str) -> Option<&str> {
    s.strip_prefix('?').filter(|n| is_name(n))
}

fn is_int_token(s: &str) -> bool {
    let digits = s.strip_prefix('-').unwrap_or(s);
    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}

const REFUSED_OPS: [&str; 7] = ["udiv", "sdiv", "urem", "srem", "shl", "lshr", "ashr"];

fn read_rule(form: &SExpr) -> Result<Rule, RegistryError> {
    let mut rd = RuleReader { name: None };
    let (items, line) = match form {
        SExpr::List(items, line) => (items, *line),
        SExpr::Atom(a, line) => {
            return Err(rd.err(*line, format!("expected (rule ...), found atom {a}")));
        }
    };
    match items.first() {
        Some(SExpr::Atom(k, _)) if k == "rule" => {}
        _ => return Err(rd.err(line, "expected (rule ...)")),
    }
    let name = match items.get(1) {
        Some(SExpr::Atom(n, l)) => {
            if !is_name(n) {
                return Err(rd.err(*l, format!("rule name {n:?} is not [a-z][a-z0-9_]*")));
            }
            n.clone()
        }
        _ => return Err(rd.err(line, "missing rule NAME")),
    };
    rd.name = Some(name.clone());
    if items.len() != 7 {
        return Err(rd.err(
            line,
            format!(
                "a rule has exactly the five clauses direction, domain, lhs, rhs, where (found {} items after the name)",
                items.len().saturating_sub(2)
            ),
        ));
    }

    // (direction equiv|refines)
    let dir_items = rd.clause(&items[2], "direction")?;
    let direction = match dir_items {
        [SExpr::Atom(d, _)] if d == "equiv" => Direction::Equiv,
        [SExpr::Atom(d, _)] if d == "refines" => Direction::Refines,
        _ => return Err(rd.err(items[2].line(), "direction must be equiv or refines")),
    };

    // (domain TYPE+)
    let dom_items = rd.clause(&items[3], "domain")?;
    if dom_items.is_empty() {
        return Err(rd.err(items[3].line(), "the domain names no type"));
    }
    let mut domain = Vec::new();
    for item in dom_items {
        let SExpr::Atom(t, l) = item else {
            return Err(rd.err(item.line(), "a domain TYPE must be an atom"));
        };
        let Some(sty) = Sty::from_name(t) else {
            return Err(rd.err(*l, format!("unknown domain type {t}")));
        };
        if domain.contains(&sty) {
            return Err(rd.err(*l, format!("domain type {t} repeated")));
        }
        domain.push(sty);
    }
    let bool_in_domain = domain.contains(&Sty::Bool);

    // (lhs PAT) (rhs PAT)
    let lhs_items = rd.clause(&items[4], "lhs")?;
    let [lhs_form] = lhs_items else {
        return Err(rd.err(items[4].line(), "lhs takes exactly one pattern"));
    };
    let rhs_items = rd.clause(&items[5], "rhs")?;
    let [rhs_form] = rhs_items else {
        return Err(rd.err(items[5].line(), "rhs takes exactly one pattern"));
    };
    let lhs = read_pat(&rd, lhs_form, false)?;
    let rhs = read_pat(&rd, rhs_form, true)?;

    // (where COND*)
    let where_items = rd.clause(&items[6], "where")?;
    let mut conds = Vec::new();
    for item in where_items {
        conds.push(read_cond(&rd, item)?);
    }

    // ---- well-formedness
    let Pat::Op(root, _) = &lhs else {
        return Err(rd.err(lhs_form.line(), "the lhs root must be an OP node"));
    };
    let (_, lhs_sort) = root.sorts();

    let mut sorts: BTreeMap<String, Sort> = BTreeMap::new();
    let mut lhs_kinds: BTreeMap<String, (bool, bool)> = BTreeMap::new();
    let mut uses_const_int = false;
    check_sorts(
        &rd,
        lhs_form.line(),
        &lhs,
        lhs_sort,
        &mut sorts,
        Some(&mut lhs_kinds),
        &mut uses_const_int,
    )?;
    let mut vars = BTreeMap::new();
    for (v, (has_const, has_term)) in &lhs_kinds {
        if *has_const && *has_term {
            return Err(rd.err(
                lhs_form.line(),
                format!("?{v} is both a constant variable and a term variable in the lhs"),
            ));
        }
        let sort = sorts.get(v).copied().unwrap_or(Sort::T);
        vars.insert(
            v.clone(),
            VarInfo {
                sort,
                constant: *has_const,
            },
        );
    }
    check_sorts(
        &rd,
        rhs_form.line(),
        &rhs,
        lhs_sort,
        &mut sorts,
        None,
        &mut uses_const_int,
    )?;
    check_rhs_vars(&rd, rhs_form.line(), &rhs, &vars)?;
    for cond in &conds {
        let v = match cond {
            Cond::Eq(v, _) | Cond::Ne(v, _) | Cond::Pow2(v) | Cond::ZeroModWidth(v) => v,
        };
        match vars.get(v) {
            Some(info) if info.constant && info.sort == Sort::T => {}
            _ => {
                return Err(rd.err(
                    items[6].line(),
                    format!("where variable ?{v} must be a constant variable of sort T"),
                ));
            }
        }
    }
    if !conds.is_empty() && bool_in_domain {
        return Err(rd.err(
            items[6].line(),
            "a rule with side conditions cannot have bool in its domain (where variables need T not Bool)",
        ));
    }
    if uses_const_int && bool_in_domain {
        return Err(rd.err(
            items[3].line(),
            "(const INT) is refused at T = Bool, and bool is in the domain",
        ));
    }
    for &t in &domain {
        for op in ops_of(&lhs).into_iter().chain(ops_of(&rhs)) {
            if !op.at(t).admitted_category() {
                return Err(rd.err(
                    items[3].line(),
                    format!(
                        "operator {} is not admitted at domain type {}",
                        op.name(),
                        t.name()
                    ),
                ));
            }
        }
    }

    let mut canonical = String::new();
    render(form, &mut canonical);
    let digest = trust_ir::ProofDigest::sha256_domain(STATEMENT_DOMAIN, canonical.as_bytes()).bytes;
    Ok(Rule {
        name,
        direction,
        domain,
        lhs,
        rhs,
        conds,
        vars,
        canonical,
        digest,
    })
}

fn read_cond(rd: &RuleReader, form: &SExpr) -> Result<Cond, RegistryError> {
    let SExpr::List(items, line) = form else {
        return Err(rd.err(form.line(), "a COND must be a list"));
    };
    let atom = |i: usize| match items.get(i) {
        Some(SExpr::Atom(a, _)) => Some(a.as_str()),
        _ => None,
    };
    let var = |i: usize| atom(i).and_then(var_name).map(str::to_owned);
    let int = |i: usize| atom(i).and_then(Int::parse);
    let bad = || {
        rd.err(
            *line,
            "malformed COND: expected (eq ?c INT), (ne ?c INT), (pow2 ?c) or (zero_mod_width ?c)",
        )
    };
    match (atom(0), items.len()) {
        (Some("eq"), 3) => Ok(Cond::Eq(var(1).ok_or_else(bad)?, int(2).ok_or_else(bad)?)),
        (Some("ne"), 3) => Ok(Cond::Ne(var(1).ok_or_else(bad)?, int(2).ok_or_else(bad)?)),
        (Some("pow2"), 2) => Ok(Cond::Pow2(var(1).ok_or_else(bad)?)),
        (Some("zero_mod_width"), 2) => Ok(Cond::ZeroModWidth(var(1).ok_or_else(bad)?)),
        _ => Err(bad()),
    }
}

fn read_pat(rd: &RuleReader, form: &SExpr, rhs: bool) -> Result<Pat, RegistryError> {
    match form {
        SExpr::Atom(a, line) => {
            if a == "true" {
                return Ok(Pat::Bool(true));
            }
            if a == "false" {
                return Ok(Pat::Bool(false));
            }
            if let Some(v) = var_name(a) {
                return Ok(Pat::Var(v.to_owned()));
            }
            Err(rd.err(
                *line,
                format!("{a} is not a pattern (expected ?var, true, false or a list)"),
            ))
        }
        SExpr::List(items, line) => {
            let Some(SExpr::Atom(head, _)) = items.first() else {
                return Err(rd.err(*line, "a pattern list must start with an operator atom"));
            };
            let args = &items[1..];
            if head == "const" {
                let [SExpr::Atom(arg, l)] = args else {
                    return Err(rd.err(*line, "(const ...) takes exactly one INT or ?var"));
                };
                if let Some(v) = var_name(arg) {
                    return Ok(Pat::ConstVar(v.to_owned()));
                }
                if is_int_token(arg) {
                    return Int::parse(arg).map(Pat::ConstInt).ok_or_else(|| {
                        rd.err(*l, format!("INT {arg} outside [-2^127, 2^128 - 1]"))
                    });
                }
                return Err(rd.err(*l, format!("(const {arg}) is neither INT nor ?var")));
            }
            if head == "eval" {
                if !rhs {
                    return Err(rd.err(*line, "eval appears only in the rhs"));
                }
                let Some(SExpr::Atom(op_name, l)) = args.first() else {
                    return Err(rd.err(*line, "(eval OP ?var...) needs an OP"));
                };
                let op = op_by_name(rd, op_name, *l)?;
                if op == ROp::Select {
                    return Err(rd.err(
                        *l,
                        "(eval select ...) is refused: eval's OP is not select (section 5.1)",
                    ));
                }
                let (operand_sorts, _) = op.sorts();
                let rest = &args[1..];
                if rest.len() != operand_sorts.len() {
                    return Err(rd.err(
                        *line,
                        format!(
                            "(eval {op_name} ...) takes {} constant variables, found {}",
                            operand_sorts.len(),
                            rest.len()
                        ),
                    ));
                }
                let mut vs = Vec::new();
                for item in rest {
                    match item {
                        SExpr::Atom(a, _) if var_name(a).is_some() => {
                            vs.push(var_name(a).unwrap_or_default().to_owned());
                        }
                        _ => {
                            return Err(rd.err(
                                item.line(),
                                "eval arguments must be ?var constant variables",
                            ));
                        }
                    }
                }
                return Ok(Pat::Eval(op, vs));
            }
            let op = op_by_name(rd, head, *line)?;
            let (operand_sorts, _) = op.sorts();
            if args.len() != operand_sorts.len() {
                return Err(rd.err(
                    *line,
                    format!(
                        "{head} takes {} operands, found {}",
                        operand_sorts.len(),
                        args.len()
                    ),
                ));
            }
            let mut pats = Vec::new();
            for a in args {
                pats.push(read_pat(rd, a, rhs)?);
            }
            Ok(Pat::Op(op, pats))
        }
    }
}

fn op_by_name(rd: &RuleReader, name: &str, line: usize) -> Result<ROp, RegistryError> {
    if REFUSED_OPS.contains(&name) {
        return Err(rd.err(
            line,
            format!("operator {name} is not total (section 5.1) and is refused"),
        ));
    }
    ROp::from_name(name).ok_or_else(|| rd.err(line, format!("unknown operator {name}")))
}

fn assign_sort(
    rd: &RuleReader,
    line: usize,
    sorts: &mut BTreeMap<String, Sort>,
    v: &str,
    sort: Sort,
) -> Result<(), RegistryError> {
    match sorts.get(v) {
        Some(&s) if s != sort => Err(rd.err(
            line,
            format!("?{v} has two sorts ({} and {})", s.name(), sort.name()),
        )),
        Some(_) => Ok(()),
        None => {
            sorts.insert(v.to_owned(), sort);
            Ok(())
        }
    }
}

/// Checks that `pat` has sort `expected`, assigning variable sorts. For the
/// lhs, `lhs_kinds` records per variable whether it occurs as `(const ?v)`
/// and whether it occurs bare.
fn check_sorts(
    rd: &RuleReader,
    line: usize,
    pat: &Pat,
    expected: Sort,
    sorts: &mut BTreeMap<String, Sort>,
    mut lhs_kinds: Option<&mut BTreeMap<String, (bool, bool)>>,
    uses_const_int: &mut bool,
) -> Result<(), RegistryError> {
    match pat {
        Pat::Var(v) => {
            assign_sort(rd, line, sorts, v, expected)?;
            if let Some(k) = lhs_kinds {
                k.entry(v.clone()).or_insert((false, false)).1 = true;
            }
            Ok(())
        }
        Pat::ConstVar(v) => {
            assign_sort(rd, line, sorts, v, expected)?;
            if let Some(k) = lhs_kinds {
                k.entry(v.clone()).or_insert((false, false)).0 = true;
            }
            Ok(())
        }
        Pat::ConstInt(_) => {
            *uses_const_int = true;
            if expected != Sort::T {
                return Err(rd.err(line, "(const INT) has sort T but stands at a bool position"));
            }
            Ok(())
        }
        Pat::Bool(_) => {
            if expected != Sort::Bool {
                return Err(rd.err(line, "true/false have sort bool but stand at a T position"));
            }
            Ok(())
        }
        Pat::Op(op, args) => {
            let (operand_sorts, result) = op.sorts();
            if result != expected {
                return Err(rd.err(
                    line,
                    format!(
                        "{} has sort {} but stands at a {} position",
                        op.name(),
                        result.name(),
                        expected.name()
                    ),
                ));
            }
            for (a, s) in args.iter().zip(operand_sorts) {
                check_sorts(
                    rd,
                    line,
                    a,
                    s,
                    sorts,
                    lhs_kinds.as_deref_mut(),
                    uses_const_int,
                )?;
            }
            Ok(())
        }
        Pat::Eval(op, vs) => {
            let (operand_sorts, result) = op.sorts();
            if result != expected {
                return Err(rd.err(
                    line,
                    format!(
                        "(eval {} ...) has sort {} but stands at a {} position",
                        op.name(),
                        result.name(),
                        expected.name()
                    ),
                ));
            }
            for (v, s) in vs.iter().zip(operand_sorts) {
                assign_sort(rd, line, sorts, v, s)?;
            }
            Ok(())
        }
    }
}

fn check_rhs_vars(
    rd: &RuleReader,
    line: usize,
    pat: &Pat,
    vars: &BTreeMap<String, VarInfo>,
) -> Result<(), RegistryError> {
    match pat {
        Pat::Var(v) => {
            if !vars.contains_key(v) {
                return Err(rd.err(line, format!("rhs variable ?{v} does not occur in the lhs")));
            }
            Ok(())
        }
        Pat::ConstVar(v) => match vars.get(v) {
            Some(info) if info.constant => Ok(()),
            Some(_) => Err(rd.err(
                line,
                format!("(const ?{v}) in the rhs names a term variable"),
            )),
            None => Err(rd.err(line, format!("rhs variable ?{v} does not occur in the lhs"))),
        },
        Pat::ConstInt(_) | Pat::Bool(_) => Ok(()),
        Pat::Op(_, args) => {
            for a in args {
                check_rhs_vars(rd, line, a, vars)?;
            }
            Ok(())
        }
        Pat::Eval(op, vs) => {
            for v in vs {
                match vars.get(v) {
                    Some(info) if info.constant => {}
                    _ => {
                        return Err(rd.err(
                            line,
                            format!(
                                "(eval {} ...) argument ?{v} is not a constant variable of the lhs",
                                op.name()
                            ),
                        ));
                    }
                }
            }
            Ok(())
        }
    }
}

fn ops_of(pat: &Pat) -> Vec<ROp> {
    let mut out = Vec::new();
    let mut stack = vec![pat];
    while let Some(p) = stack.pop() {
        match p {
            Pat::Op(op, args) => {
                out.push(*op);
                stack.extend(args.iter());
            }
            Pat::Eval(op, _) => out.push(*op),
            Pat::Var(_) | Pat::ConstInt(_) | Pat::ConstVar(_) | Pat::Bool(_) => {}
        }
    }
    out
}

/// Section 5.2 canonical text: tokens joined by one space, none after `(`
/// and none before `)`, every `INT` token in canonical decimal. In a rule
/// that passed well-formedness, the only atoms of the form `-?[0-9]+` are
/// `INT` tokens (names, types, operators and variables cannot have it).
fn render(form: &SExpr, out: &mut String) {
    match form {
        SExpr::Atom(a, _) => {
            if is_int_token(a) {
                match Int::parse(a) {
                    Some(i) => out.push_str(&i.canonical()),
                    None => out.push_str(a),
                }
            } else {
                out.push_str(a);
            }
        }
        SExpr::List(items, _) => {
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                render(item, out);
            }
            out.push(')');
        }
    }
}
