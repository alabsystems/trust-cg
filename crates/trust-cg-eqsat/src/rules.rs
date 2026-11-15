// crates/trust-cg-eqsat/src/rules.rs - rule-file parser, well-formedness, canonical text and statement digest
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Rule files (`docs/eqsat-tier-e.md` section 5).
//!
//! A [`RuleSet`] is the parsed, well-formed content of one rule file; every
//! clause of section 5.1 that a file breaks is a typed [`RuleError`], and a
//! rule naming a non-total operator (`udiv sdiv urem srem shl lshr ashr`) is
//! refused. A rule is a *statement*: nothing here proves it (PKG-U2 binds a
//! discharge record to [`Rule::statement_digest`]).
//!
//! [`canonical_texts`] is the syntax-only half: it tokenizes and canonicalizes
//! each `(rule NAME ...)` form (section 5.2) without any operator, sort or
//! domain check, so a refused rule can still be named and digested.
//!
//! Lexical reading (fail-closed, recorded as a spec reading): a rule file is
//! ASCII; whitespace is space, tab, line feed, carriage return and form feed;
//! any other control character or any non-ASCII character outside a comment
//! is a syntax error, so two readers cannot disagree on token boundaries.

use std::fmt;

use crate::eval;
use crate::vocab::{BinOpCode, CmpPred, GraphWidths, OpDesc, ScalarTy, UnOpCode};

/// The PKG-U1 integer identity rule set (used by the tests).
pub const INTEGER_IDENTITIES: &str = include_str!("../rules/integer_identities.rules");

/// The digest domain of a rule statement (section 5.2).
pub const STATEMENT_DIGEST_DOMAIN: &str = "trust-cg-eqsat.rule-statement.v1";

/// Maximum list nesting accepted in a rule file (deeper input is a syntax
/// error rather than unbounded recursion).
const MAX_NESTING: usize = 64;

/// The statement digest of a canonical text (section 5.2).
#[must_use]
pub fn statement_digest(canonical_text: &str) -> [u8; 32] {
    trust_ir::ProofDigest::sha256_domain(STATEMENT_DIGEST_DOMAIN, canonical_text.as_bytes()).bytes
}

/// Which well-formedness clause a rule file breaks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RuleErrorKind {
    /// A character outside the lexical alphabet, unbalanced parentheses, or
    /// nesting deeper than the reader accepts.
    Syntax,
    /// A top-level form that is not `(rule NAME (direction ..) (domain ..)
    /// (lhs ..) (rhs ..) (where ..))` with all five clauses in order.
    Structure,
    /// `NAME` is not `[a-z][a-z0-9_]*`.
    BadName,
    /// Two rules share a `NAME`.
    DuplicateName,
    /// The direction is neither `equiv` nor `refines`.
    BadDirection,
    /// The domain is empty.
    EmptyDomain,
    /// A domain entry is not a section 5.1 `TYPE`.
    BadType,
    /// A domain type is repeated.
    RepeatedType,
    /// A pattern, variable or condition that is not in the section 5.1 grammar.
    BadPattern,
    /// An operator name the table of section 5.1 does not know.
    UnknownOperator,
    /// `udiv sdiv urem srem shl lshr ashr`: not total, refused.
    NonTotalOperator,
    /// An operator applied to the wrong number of patterns.
    Arity,
    /// The lhs root is not an `OP` node.
    LhsRootNotOperator,
    /// `eval` in the lhs.
    EvalInLhs,
    /// An `INT` outside `[-2^127, 2^128 - 1]`.
    IntOutOfRange,
    /// A variable used at two sorts, a pattern at the wrong sort, or lhs and
    /// rhs of different sorts.
    SortConflict,
    /// A variable that is both a constant variable and a term variable.
    MixedVariable,
    /// An rhs variable that does not occur in the lhs.
    RhsVariableNotInLhs,
    /// An `eval` argument that is not a constant variable of the operator's
    /// operand sort (or an `eval` of an operator without a single operand sort).
    EvalArgument,
    /// A `where` variable that is not a constant variable of sort `T`, or a
    /// side condition in a rule whose domain contains `bool`.
    ConditionVariable,
    /// `(const INT)` at sort `bool` or in a rule whose domain contains `bool`.
    ConstAtBool,
    /// An operator not admitted at some domain type.
    OperatorNotAdmitted,
}

impl RuleErrorKind {
    /// A stable snake-case name.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            RuleErrorKind::Syntax => "syntax",
            RuleErrorKind::Structure => "structure",
            RuleErrorKind::BadName => "bad_name",
            RuleErrorKind::DuplicateName => "duplicate_name",
            RuleErrorKind::BadDirection => "bad_direction",
            RuleErrorKind::EmptyDomain => "empty_domain",
            RuleErrorKind::BadType => "bad_type",
            RuleErrorKind::RepeatedType => "repeated_type",
            RuleErrorKind::BadPattern => "bad_pattern",
            RuleErrorKind::UnknownOperator => "unknown_operator",
            RuleErrorKind::NonTotalOperator => "non_total_operator",
            RuleErrorKind::Arity => "arity",
            RuleErrorKind::LhsRootNotOperator => "lhs_root_not_operator",
            RuleErrorKind::EvalInLhs => "eval_in_lhs",
            RuleErrorKind::IntOutOfRange => "int_out_of_range",
            RuleErrorKind::SortConflict => "sort_conflict",
            RuleErrorKind::MixedVariable => "mixed_variable",
            RuleErrorKind::RhsVariableNotInLhs => "rhs_variable_not_in_lhs",
            RuleErrorKind::EvalArgument => "eval_argument",
            RuleErrorKind::ConditionVariable => "condition_variable",
            RuleErrorKind::ConstAtBool => "const_at_bool",
            RuleErrorKind::OperatorNotAdmitted => "operator_not_admitted",
        }
    }
}

/// A refused rule file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleError {
    /// The clause broken.
    pub kind: RuleErrorKind,
    /// The rule's name, when the form got that far.
    pub rule: Option<String>,
    /// The 1-based line of the offending token or form.
    pub line: usize,
    /// What exactly was refused.
    pub detail: String,
}

impl fmt::Display for RuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "rule file line {}: ", self.line)?;
        if let Some(rule) = &self.rule {
            write!(f, "rule `{rule}`: ")?;
        }
        write!(f, "{}: {}", self.kind.as_str(), self.detail)
    }
}

impl std::error::Error for RuleError {}

fn err(
    kind: RuleErrorKind,
    rule: Option<&str>,
    line: usize,
    detail: impl Into<String>,
) -> RuleError {
    RuleError {
        kind,
        rule: rule.map(str::to_owned),
        line,
        detail: detail.into(),
    }
}

// ---------------------------------------------------------------------------
// Tokens and s-expressions (syntax only).

#[derive(Debug, Clone)]
enum SExpr {
    Atom(String, usize),
    List(Vec<SExpr>, usize),
}

impl SExpr {
    fn line(&self) -> usize {
        match self {
            SExpr::Atom(_, line) | SExpr::List(_, line) => *line,
        }
    }

    fn atom(&self) -> Option<&str> {
        match self {
            SExpr::Atom(text, _) => Some(text),
            SExpr::List(..) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Open,
    Close,
    Atom(String),
}

fn is_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0c')
}

fn tokenize(source: &str) -> Result<Vec<(Token, usize)>, RuleError> {
    let mut tokens = Vec::new();
    let mut line = 1usize;
    let mut chars = source.chars().peekable();
    let mut atom = String::new();
    let mut atom_line = 1usize;
    let flush = |atom: &mut String, tokens: &mut Vec<(Token, usize)>, at: usize| {
        if !atom.is_empty() {
            tokens.push((Token::Atom(std::mem::take(atom)), at));
        }
    };
    while let Some(c) = chars.next() {
        if c == ';' {
            flush(&mut atom, &mut tokens, atom_line);
            // A comment runs to the end of the line; its content is free text.
            for d in chars.by_ref() {
                if d == '\n' {
                    line += 1;
                    break;
                }
            }
            continue;
        }
        if is_space(c) {
            flush(&mut atom, &mut tokens, atom_line);
            if c == '\n' {
                line += 1;
            }
            continue;
        }
        if c == '(' || c == ')' {
            flush(&mut atom, &mut tokens, atom_line);
            tokens.push((if c == '(' { Token::Open } else { Token::Close }, line));
            continue;
        }
        if !c.is_ascii() || c.is_ascii_control() {
            return Err(err(
                RuleErrorKind::Syntax,
                None,
                line,
                format!("character U+{:04X} outside a comment", u32::from(c)),
            ));
        }
        if atom.is_empty() {
            atom_line = line;
        }
        atom.push(c);
    }
    flush(&mut atom, &mut tokens, atom_line);
    Ok(tokens)
}

fn parse_sexprs(source: &str) -> Result<Vec<SExpr>, RuleError> {
    let tokens = tokenize(source)?;
    // Iterative reader: a stack of open lists.
    let mut stack: Vec<(Vec<SExpr>, usize)> = Vec::new();
    let mut top: Vec<SExpr> = Vec::new();
    for (token, line) in tokens {
        match token {
            Token::Open => {
                if stack.len() >= MAX_NESTING {
                    return Err(err(
                        RuleErrorKind::Syntax,
                        None,
                        line,
                        "lists nested too deeply",
                    ));
                }
                stack.push((Vec::new(), line));
            }
            Token::Close => {
                let Some((items, open_line)) = stack.pop() else {
                    return Err(err(RuleErrorKind::Syntax, None, line, "unmatched `)`"));
                };
                let list = SExpr::List(items, open_line);
                match stack.last_mut() {
                    Some((parent, _)) => parent.push(list),
                    None => top.push(list),
                }
            }
            Token::Atom(text) => {
                let atom = SExpr::Atom(text, line);
                match stack.last_mut() {
                    Some((parent, _)) => parent.push(atom),
                    None => top.push(atom),
                }
            }
        }
    }
    if let Some((_, line)) = stack.last() {
        return Err(err(RuleErrorKind::Syntax, None, *line, "unclosed `(`"));
    }
    Ok(top)
}

/// Whether `text` is an `INT` token: `-?[0-9]+`.
fn is_int_token(text: &str) -> bool {
    let digits = text.strip_prefix('-').unwrap_or(text);
    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}

/// The canonical decimal spelling of an `INT` token (no leading zeros, `-0`
/// as `0`); other tokens are returned unchanged.
fn canonical_atom(text: &str) -> String {
    if !is_int_token(text) {
        return text.to_owned();
    }
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let trimmed = digits.trim_start_matches('0');
    if trimmed.is_empty() {
        "0".to_owned()
    } else if negative {
        format!("-{trimmed}")
    } else {
        trimmed.to_owned()
    }
}

fn render(expr: &SExpr, out: &mut String) {
    match expr {
        SExpr::Atom(text, _) => out.push_str(&canonical_atom(text)),
        SExpr::List(items, _) => {
            out.push('(');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(' ');
                }
                render(item, out);
            }
            out.push(')');
        }
    }
}

fn rule_form(expr: &SExpr) -> Result<(&[SExpr], &str), RuleError> {
    let SExpr::List(items, line) = expr else {
        return Err(err(
            RuleErrorKind::Structure,
            None,
            expr.line(),
            "a top-level form must be a `(rule NAME ...)` list",
        ));
    };
    match (
        items.first().and_then(SExpr::atom),
        items.get(1).and_then(SExpr::atom),
    ) {
        (Some("rule"), Some(name)) => Ok((items, name)),
        _ => Err(err(
            RuleErrorKind::Structure,
            None,
            *line,
            "a top-level form must start with `rule NAME`",
        )),
    }
}

/// The `(NAME, canonical text)` of every `(rule NAME ...)` form of `source`,
/// in file order. Syntax only: no operator, sort, domain or name check.
///
/// # Errors
/// A lexical error, unbalanced parentheses, or a top-level form that is not a
/// list starting with the atom `rule` followed by an atom.
pub fn canonical_texts(source: &str) -> Result<Vec<(String, String)>, RuleError> {
    let forms = parse_sexprs(source)?;
    let mut out = Vec::with_capacity(forms.len());
    for form in &forms {
        let (_, name) = rule_form(form)?;
        let mut text = String::new();
        render(form, &mut text);
        out.push((name.to_owned(), text));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Rule objects.

/// The direction of a rule (section 5.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Direction {
    /// Both sides are equal on every assignment in the domain.
    Equiv,
    /// Every outcome of the rhs is an outcome of the lhs; usable forward only.
    Refines,
}

/// The sort of a pattern position at instance type `T`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Sort {
    /// The instance type.
    T,
    /// `bool`.
    Bool,
}

impl Sort {
    pub(crate) const fn at(self, ty: ScalarTy) -> ScalarTy {
        match self {
            Sort::T => ty,
            Sort::Bool => ScalarTy::Bool,
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Sort::T => "T",
            Sort::Bool => "bool",
        }
    }
}

/// A rule operator (section 5.1 `OP`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RuleOp {
    Bin(BinOpCode),
    Un(UnOpCode),
    Cmp(CmpPred),
    Select,
}

impl RuleOp {
    fn from_name(name: &str) -> Option<RuleOp> {
        if name == "select" {
            return Some(RuleOp::Select);
        }
        if let Some(op) = BinOpCode::ALL.into_iter().find(|op| op.name() == name) {
            return Some(RuleOp::Bin(op));
        }
        if let Some(op) = UnOpCode::ALL.into_iter().find(|op| op.name() == name) {
            return Some(RuleOp::Un(op));
        }
        CmpPred::ALL
            .into_iter()
            .find(|pred| pred.name() == name)
            .map(RuleOp::Cmp)
    }

    fn name(self) -> &'static str {
        match self {
            RuleOp::Bin(op) => op.name(),
            RuleOp::Un(op) => op.name(),
            RuleOp::Cmp(pred) => pred.name(),
            RuleOp::Select => "select",
        }
    }

    const fn arity(self) -> usize {
        match self {
            RuleOp::Bin(_) | RuleOp::Cmp(_) => 2,
            RuleOp::Un(_) => 1,
            RuleOp::Select => 3,
        }
    }

    const fn is_bool_only(self) -> bool {
        matches!(
            self,
            RuleOp::Bin(BinOpCode::BAnd | BinOpCode::BOr | BinOpCode::BXor)
        )
    }

    /// The sort of operand `index`.
    pub(crate) const fn operand_sort(self, index: usize) -> Sort {
        match self {
            RuleOp::Select if index == 0 => Sort::Bool,
            _ if self.is_bool_only() => Sort::Bool,
            _ => Sort::T,
        }
    }

    /// The sort of the result.
    pub(crate) const fn result_sort(self) -> Sort {
        match self {
            RuleOp::Cmp(_) => Sort::Bool,
            _ if self.is_bool_only() => Sort::Bool,
            _ => Sort::T,
        }
    }

    /// The term operator this rule operator denotes at instance type `ty`.
    pub(crate) const fn desc(self, ty: ScalarTy) -> OpDesc {
        match self {
            RuleOp::Bin(op) if self.is_bool_only() => OpDesc::Bin(op, ScalarTy::Bool),
            RuleOp::Bin(op) => OpDesc::Bin(op, ty),
            RuleOp::Un(op) => OpDesc::Un(op, ty),
            RuleOp::Cmp(pred) => OpDesc::Cmp(pred, ty),
            RuleOp::Select => OpDesc::Select(ty),
        }
    }

    const fn admitted_at(self, ty: ScalarTy) -> bool {
        self.desc(ty).admitted()
    }
}

/// An integer literal of a rule file, range checked: `INT` is
/// `if negative { -magnitude } else { magnitude }`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RuleInt {
    pub(crate) negative: bool,
    pub(crate) magnitude: u128,
}

impl RuleInt {
    pub(crate) fn residue(self, width: u32) -> u128 {
        eval::int_residue(self.negative, self.magnitude, width)
    }
}

/// A pattern (section 5.1 `PAT`), variables by index into [`Rule::vars`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Pat {
    /// `?var` (a term variable, or a constant variable in the rhs).
    Var(usize),
    /// `(const ?var)`.
    ConstVar(usize),
    /// `(const INT)`.
    Int(RuleInt),
    /// `true` / `false`.
    Bool(bool),
    /// `(OP PAT...)`.
    Op(RuleOp, Vec<Pat>),
    /// `(eval OP ?var...)` (rhs only).
    Eval(RuleOp, Vec<usize>),
}

/// A variable of a rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Var {
    /// The name without `?`.
    pub(crate) name: String,
    /// Its sort.
    pub(crate) sort: Sort,
    /// Whether it is a constant variable (every lhs occurrence is `(const ?v)`).
    pub(crate) constant: bool,
}

/// A side condition (section 5.1 `COND`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Cond {
    /// `(eq ?c INT)`.
    Eq(usize, RuleInt),
    /// `(ne ?c INT)`.
    Ne(usize, RuleInt),
    /// `(pow2 ?c)`.
    Pow2(usize),
    /// `(zero_mod_width ?c)`.
    ZeroModWidth(usize),
}

impl Cond {
    /// Whether the condition holds when its variable's residue is `r` at
    /// width `width`.
    pub(crate) fn holds(self, r: u128, width: u32) -> bool {
        match self {
            Cond::Eq(_, int) => r == int.residue(width),
            Cond::Ne(_, int) => r != int.residue(width),
            Cond::Pow2(_) => r.count_ones() == 1,
            Cond::ZeroModWidth(_) => r.is_multiple_of(u128::from(width)),
        }
    }

    pub(crate) const fn var(self) -> usize {
        match self {
            Cond::Eq(var, _) | Cond::Ne(var, _) | Cond::Pow2(var) | Cond::ZeroModWidth(var) => var,
        }
    }
}

/// One well-formed rule: its statement, identity and digest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    name: String,
    direction: Direction,
    domain: Vec<ScalarTy>,
    vars: Vec<Var>,
    lhs: Pat,
    rhs: Pat,
    conds: Vec<Cond>,
    canonical: String,
    digest: [u8; 32],
}

impl Rule {
    /// The rule's `NAME`.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The canonical text of section 5.2.
    #[must_use]
    pub fn canonical_text(&self) -> &str {
        &self.canonical
    }

    /// The statement digest of section 5.2.
    #[must_use]
    pub fn statement_digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Whether the rule is `equiv` (else `refines`).
    #[must_use]
    pub fn is_equiv(&self) -> bool {
        self.direction == Direction::Equiv
    }

    /// The rule's direction.
    #[must_use]
    pub fn direction(&self) -> Direction {
        self.direction
    }

    /// The domain types, in file order.
    #[must_use]
    pub fn domain(&self) -> &[ScalarTy] {
        &self.domain
    }

    /// The number of side conditions.
    #[must_use]
    pub fn side_condition_count(&self) -> usize {
        self.conds.len()
    }

    pub(crate) fn vars(&self) -> &[Var] {
        &self.vars
    }

    pub(crate) fn lhs(&self) -> &Pat {
        &self.lhs
    }

    pub(crate) fn rhs(&self) -> &Pat {
        &self.rhs
    }

    pub(crate) fn conds(&self) -> &[Cond] {
        &self.conds
    }

    /// The instance types at which the lhs root can match a node whose
    /// operator is `desc`, in domain order, restricted to graph types of the
    /// module.
    pub(crate) fn instance_types(&self, desc: OpDesc, widths: GraphWidths) -> Vec<ScalarTy> {
        let Pat::Op(root, _) = &self.lhs else {
            return Vec::new();
        };
        self.domain
            .iter()
            .copied()
            .filter(|&ty| widths.admits(ty) && root.desc(ty) == desc)
            .collect()
    }
}

/// A parsed, well-formed rule file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleSet {
    rules: Vec<Rule>,
}

impl RuleSet {
    /// An empty rule set (no rule fires).
    #[must_use]
    pub fn empty() -> Self {
        Self { rules: Vec::new() }
    }

    /// Parse and check a rule file (section 5.1).
    ///
    /// # Errors
    /// The first clause of section 5.1 the file breaks, as a typed
    /// [`RuleError`].
    pub fn parse(text: &str) -> Result<RuleSet, RuleError> {
        let forms = parse_sexprs(text)?;
        let mut rules: Vec<Rule> = Vec::with_capacity(forms.len());
        for form in &forms {
            let rule = parse_rule(form)?;
            if rules.iter().any(|other| other.name == rule.name) {
                return Err(err(
                    RuleErrorKind::DuplicateName,
                    Some(&rule.name),
                    form.line(),
                    "the name is already used in this file",
                ));
            }
            rules.push(rule);
        }
        Ok(RuleSet { rules })
    }

    /// The rules, in file order (the order they fire in).
    #[must_use]
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }
}

fn valid_name(name: &str) -> bool {
    let mut bytes = name.bytes();
    matches!(bytes.next(), Some(b'a'..=b'z'))
        && bytes.all(|b| matches!(b, b'a'..=b'z' | b'0'..=b'9' | b'_'))
}

const NON_TOTAL: [&str; 7] = ["udiv", "sdiv", "urem", "srem", "shl", "lshr", "ashr"];

fn clause<'a>(
    items: &'a [SExpr],
    index: usize,
    keyword: &str,
    name: &str,
    line: usize,
) -> Result<&'a [SExpr], RuleError> {
    match items.get(index) {
        Some(SExpr::List(inner, _)) if inner.first().and_then(SExpr::atom) == Some(keyword) => {
            Ok(inner.get(1..).unwrap_or(&[]))
        }
        _ => Err(err(
            RuleErrorKind::Structure,
            Some(name),
            items.get(index).map_or(line, SExpr::line),
            format!("clause {index} must be `({keyword} ...)`"),
        )),
    }
}

fn parse_int(text: &str, name: &str, line: usize) -> Result<RuleInt, RuleError> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let mut magnitude: u128 = 0;
    for b in digits.bytes() {
        let digit = u128::from(b - b'0');
        magnitude = magnitude
            .checked_mul(10)
            .and_then(|m| m.checked_add(digit))
            .ok_or_else(|| {
                err(
                    RuleErrorKind::IntOutOfRange,
                    Some(name),
                    line,
                    format!("`{text}` is outside [-2^127, 2^128 - 1]"),
                )
            })?;
    }
    if negative && magnitude > 1u128 << 127 {
        return Err(err(
            RuleErrorKind::IntOutOfRange,
            Some(name),
            line,
            format!("`{text}` is outside [-2^127, 2^128 - 1]"),
        ));
    }
    Ok(RuleInt {
        negative: negative && magnitude != 0,
        magnitude,
    })
}

/// Per-variable facts gathered while reading the two sides.
#[derive(Debug, Default, Clone)]
struct VarFacts {
    sort: Option<Sort>,
    lhs_term: bool,
    lhs_const: bool,
    in_lhs: bool,
}

struct RuleReader<'a> {
    name: &'a str,
    names: Vec<String>,
    facts: Vec<VarFacts>,
    domain: &'a [ScalarTy],
    ops: Vec<(RuleOp, usize)>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    Lhs,
    Rhs,
}

impl RuleReader<'_> {
    fn error(&self, kind: RuleErrorKind, line: usize, detail: impl Into<String>) -> RuleError {
        err(kind, Some(self.name), line, detail)
    }

    fn var(&mut self, text: &str, line: usize, side: Side) -> Result<usize, RuleError> {
        let Some(name) = text.strip_prefix('?') else {
            return Err(self.error(
                RuleErrorKind::BadPattern,
                line,
                format!("`{text}` is not a variable"),
            ));
        };
        if !valid_name(name) {
            return Err(self.error(
                RuleErrorKind::BadPattern,
                line,
                format!("`{text}` is not `?[a-z][a-z0-9_]*`"),
            ));
        }
        let index = match self.names.iter().position(|known| known == name) {
            Some(index) => index,
            None => {
                self.names.push(name.to_owned());
                self.facts.push(VarFacts::default());
                self.names.len() - 1
            }
        };
        if side == Side::Rhs && !self.facts.get(index).is_some_and(|f| f.in_lhs) {
            return Err(self.error(
                RuleErrorKind::RhsVariableNotInLhs,
                line,
                format!("`{text}` does not occur in the lhs"),
            ));
        }
        Ok(index)
    }

    fn op(&mut self, text: &str, line: usize) -> Result<RuleOp, RuleError> {
        if NON_TOTAL.contains(&text) {
            return Err(self.error(
                RuleErrorKind::NonTotalOperator,
                line,
                format!("`{text}` is not total (section 2.4)"),
            ));
        }
        let op = RuleOp::from_name(text).ok_or_else(|| {
            self.error(
                RuleErrorKind::UnknownOperator,
                line,
                format!("`{text}` is not a rule operator"),
            )
        })?;
        self.ops.push((op, line));
        Ok(op)
    }

    fn pat(&mut self, expr: &SExpr, side: Side, depth: usize) -> Result<Pat, RuleError> {
        let line = expr.line();
        if depth > MAX_NESTING {
            return Err(self.error(RuleErrorKind::Syntax, line, "pattern nested too deeply"));
        }
        match expr {
            SExpr::Atom(text, _) => match text.as_str() {
                "true" => Ok(Pat::Bool(true)),
                "false" => Ok(Pat::Bool(false)),
                _ => {
                    let var = self.var(text, line, side)?;
                    if side == Side::Lhs
                        && let Some(facts) = self.facts.get_mut(var)
                    {
                        facts.lhs_term = true;
                    }
                    Ok(Pat::Var(var))
                }
            },
            SExpr::List(items, _) => {
                let Some(head) = items.first().and_then(SExpr::atom) else {
                    return Err(self.error(
                        RuleErrorKind::BadPattern,
                        line,
                        "a pattern list must start with an operator",
                    ));
                };
                let args = items.get(1..).unwrap_or(&[]);
                match head {
                    "const" => {
                        let [arg] = args else {
                            return Err(self.error(
                                RuleErrorKind::BadPattern,
                                line,
                                "`const` takes one INT or one variable",
                            ));
                        };
                        match arg.atom() {
                            Some(text) if is_int_token(text) => {
                                Ok(Pat::Int(parse_int(text, self.name, line)?))
                            }
                            Some(text) => {
                                let var = self.var(text, line, side)?;
                                if side == Side::Lhs
                                    && let Some(facts) = self.facts.get_mut(var)
                                {
                                    facts.lhs_const = true;
                                }
                                Ok(Pat::ConstVar(var))
                            }
                            None => Err(self.error(
                                RuleErrorKind::BadPattern,
                                line,
                                "`const` takes one INT or one variable",
                            )),
                        }
                    }
                    "eval" => {
                        if side == Side::Lhs {
                            return Err(self.error(
                                RuleErrorKind::EvalInLhs,
                                line,
                                "`eval` may appear only in the rhs",
                            ));
                        }
                        let Some(op_text) = args.first().and_then(SExpr::atom) else {
                            return Err(self.error(
                                RuleErrorKind::BadPattern,
                                line,
                                "`eval` takes an operator name",
                            ));
                        };
                        let op = self.op(op_text, line)?;
                        let operands = args.get(1..).unwrap_or(&[]);
                        if operands.len() != op.arity() {
                            return Err(self.error(
                                RuleErrorKind::Arity,
                                line,
                                format!("`{}` takes {} operands", op.name(), op.arity()),
                            ));
                        }
                        let mut vars = Vec::with_capacity(operands.len());
                        for operand in operands {
                            let Some(text) = operand.atom() else {
                                return Err(self.error(
                                    RuleErrorKind::EvalArgument,
                                    line,
                                    "`eval` arguments are constant variables",
                                ));
                            };
                            vars.push(self.var(text, line, side)?);
                        }
                        Ok(Pat::Eval(op, vars))
                    }
                    _ => {
                        let op = self.op(head, line)?;
                        if args.len() != op.arity() {
                            return Err(self.error(
                                RuleErrorKind::Arity,
                                line,
                                format!("`{}` takes {} operands", op.name(), op.arity()),
                            ));
                        }
                        let mut pats = Vec::with_capacity(args.len());
                        for arg in args {
                            pats.push(self.pat(arg, side, depth + 1)?);
                        }
                        Ok(Pat::Op(op, pats))
                    }
                }
            }
        }
    }

    fn assign(&mut self, var: usize, sort: Sort, line: usize) -> Result<(), RuleError> {
        let name = self.names.get(var).cloned().unwrap_or_default();
        let Some(facts) = self.facts.get_mut(var) else {
            return Err(err(
                RuleErrorKind::BadPattern,
                Some(self.name),
                line,
                "unknown variable",
            ));
        };
        match facts.sort {
            None => {
                facts.sort = Some(sort);
                Ok(())
            }
            Some(previous) if previous == sort => Ok(()),
            Some(previous) => Err(err(
                RuleErrorKind::SortConflict,
                Some(self.name),
                line,
                format!(
                    "`?{name}` is used at sort {} and at sort {}",
                    previous.name(),
                    sort.name()
                ),
            )),
        }
    }

    /// Check `pat` has sort `expected`, fixing variable sorts.
    fn sorts(&mut self, pat: &Pat, expected: Sort, line: usize) -> Result<(), RuleError> {
        match pat {
            Pat::Var(var) | Pat::ConstVar(var) => self.assign(*var, expected, line),
            Pat::Int(_) => {
                if expected == Sort::Bool || self.domain.contains(&ScalarTy::Bool) {
                    return Err(self.error(
                        RuleErrorKind::ConstAtBool,
                        line,
                        "`(const INT)` is refused at sort bool",
                    ));
                }
                Ok(())
            }
            Pat::Bool(_) => {
                if expected == Sort::Bool {
                    Ok(())
                } else {
                    Err(self.error(
                        RuleErrorKind::SortConflict,
                        line,
                        format!("`true`/`false` at a position of sort {}", expected.name()),
                    ))
                }
            }
            Pat::Op(op, args) => {
                if op.result_sort() != expected {
                    return Err(self.error(
                        RuleErrorKind::SortConflict,
                        line,
                        format!(
                            "`{}` has sort {}, the position has sort {}",
                            op.name(),
                            op.result_sort().name(),
                            expected.name()
                        ),
                    ));
                }
                for (index, arg) in args.iter().enumerate() {
                    self.sorts(arg, op.operand_sort(index), line)?;
                }
                Ok(())
            }
            Pat::Eval(op, vars) => {
                if op.result_sort() != expected {
                    return Err(self.error(
                        RuleErrorKind::SortConflict,
                        line,
                        format!(
                            "`(eval {} ..)` has sort {}, the position has sort {}",
                            op.name(),
                            op.result_sort().name(),
                            expected.name()
                        ),
                    ));
                }
                if *op == RuleOp::Select {
                    // `select` has no single operand sort (bool T T): refused,
                    // fail-closed.
                    return Err(self.error(
                        RuleErrorKind::EvalArgument,
                        line,
                        "`eval select` is refused: select has no single operand sort",
                    ));
                }
                for (index, var) in vars.iter().enumerate() {
                    self.assign(*var, op.operand_sort(index), line)?;
                }
                Ok(())
            }
        }
    }
}

fn collect_rhs_checks(
    pat: &Pat,
    constant: &[bool],
    name: &str,
    line: usize,
) -> Result<(), RuleError> {
    match pat {
        Pat::Var(_) | Pat::Int(_) | Pat::Bool(_) => Ok(()),
        Pat::ConstVar(var) => {
            if constant.get(*var).copied().unwrap_or(false) {
                Ok(())
            } else {
                Err(err(
                    RuleErrorKind::MixedVariable,
                    Some(name),
                    line,
                    "`(const ?v)` in the rhs names a term variable",
                ))
            }
        }
        Pat::Op(_, args) => {
            for arg in args {
                collect_rhs_checks(arg, constant, name, line)?;
            }
            Ok(())
        }
        Pat::Eval(_, vars) => {
            if vars
                .iter()
                .all(|var| constant.get(*var).copied().unwrap_or(false))
            {
                Ok(())
            } else {
                Err(err(
                    RuleErrorKind::EvalArgument,
                    Some(name),
                    line,
                    "`eval` arguments must be constant variables",
                ))
            }
        }
    }
}

fn parse_rule(form: &SExpr) -> Result<Rule, RuleError> {
    let (items, name) = rule_form(form)?;
    let line = form.line();
    if !valid_name(name) {
        return Err(err(
            RuleErrorKind::BadName,
            Some(name),
            line,
            "a rule name is `[a-z][a-z0-9_]*`",
        ));
    }
    if items.len() != 7 {
        return Err(err(
            RuleErrorKind::Structure,
            Some(name),
            line,
            "a rule has exactly the clauses direction, domain, lhs, rhs, where, in this order",
        ));
    }
    // direction
    let direction = clause(items, 2, "direction", name, line)?;
    let direction = match direction {
        [SExpr::Atom(text, _)] if text == "equiv" => Direction::Equiv,
        [SExpr::Atom(text, _)] if text == "refines" => Direction::Refines,
        _ => {
            return Err(err(
                RuleErrorKind::BadDirection,
                Some(name),
                line,
                "the direction is `equiv` or `refines`",
            ));
        }
    };
    // domain
    let domain_items = clause(items, 3, "domain", name, line)?;
    if domain_items.is_empty() {
        return Err(err(
            RuleErrorKind::EmptyDomain,
            Some(name),
            line,
            "the domain names at least one type",
        ));
    }
    let mut domain = Vec::with_capacity(domain_items.len());
    for item in domain_items {
        let ty = item.atom().and_then(ScalarTy::from_name).ok_or_else(|| {
            err(
                RuleErrorKind::BadType,
                Some(name),
                item.line(),
                "a domain type is one of i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize bool",
            )
        })?;
        if domain.contains(&ty) {
            return Err(err(
                RuleErrorKind::RepeatedType,
                Some(name),
                item.line(),
                format!("`{}` is repeated", ty.name()),
            ));
        }
        domain.push(ty);
    }
    let lhs_items = clause(items, 4, "lhs", name, line)?;
    let rhs_items = clause(items, 5, "rhs", name, line)?;
    let where_items = clause(items, 6, "where", name, line)?;
    let ([lhs_expr], [rhs_expr]) = (lhs_items, rhs_items) else {
        return Err(err(
            RuleErrorKind::Structure,
            Some(name),
            line,
            "`lhs` and `rhs` each hold exactly one pattern",
        ));
    };

    let mut reader = RuleReader {
        name,
        names: Vec::new(),
        facts: Vec::new(),
        domain: &domain,
        ops: Vec::new(),
    };
    let lhs = reader.pat(lhs_expr, Side::Lhs, 0)?;
    let Pat::Op(root, _) = &lhs else {
        return Err(err(
            RuleErrorKind::LhsRootNotOperator,
            Some(name),
            lhs_expr.line(),
            "the lhs root must be an operator node",
        ));
    };
    let lhs_sort = root.result_sort();
    for facts in &mut reader.facts {
        facts.in_lhs = true;
    }
    reader.sorts(&lhs, lhs_sort, lhs_expr.line())?;
    let rhs = reader.pat(rhs_expr, Side::Rhs, 0)?;
    reader.sorts(&rhs, lhs_sort, rhs_expr.line())?;

    // Constant variables: every lhs occurrence is `(const ?c)`.
    let mut constant = Vec::with_capacity(reader.facts.len());
    for (index, facts) in reader.facts.iter().enumerate() {
        if facts.lhs_term && facts.lhs_const {
            return Err(err(
                RuleErrorKind::MixedVariable,
                Some(name),
                line,
                format!(
                    "`?{}` is both a constant variable and a term variable",
                    reader.names.get(index).map_or("", String::as_str)
                ),
            ));
        }
        constant.push(facts.lhs_const);
    }
    collect_rhs_checks(&rhs, &constant, name, rhs_expr.line())?;

    // Side conditions.
    let mut conds = Vec::with_capacity(where_items.len());
    for item in where_items {
        let cond_line = item.line();
        let SExpr::List(parts, _) = item else {
            return Err(err(
                RuleErrorKind::BadPattern,
                Some(name),
                cond_line,
                "a side condition is a list",
            ));
        };
        let keyword = parts.first().and_then(SExpr::atom).unwrap_or("");
        let var_text = parts.get(1).and_then(SExpr::atom).unwrap_or("");
        let var = match reader
            .names
            .iter()
            .position(|known| var_text.strip_prefix('?') == Some(known.as_str()))
        {
            Some(var) => var,
            None if var_text.starts_with('?') => {
                return Err(err(
                    RuleErrorKind::ConditionVariable,
                    Some(name),
                    cond_line,
                    format!("`{var_text}` does not occur in the lhs"),
                ));
            }
            None => {
                return Err(err(
                    RuleErrorKind::BadPattern,
                    Some(name),
                    cond_line,
                    "a side condition names a variable",
                ));
            }
        };
        let cond = match (keyword, parts.len()) {
            ("eq" | "ne", 3) => {
                let int_text = parts.get(2).and_then(SExpr::atom).unwrap_or("");
                if !is_int_token(int_text) {
                    return Err(err(
                        RuleErrorKind::BadPattern,
                        Some(name),
                        cond_line,
                        "`eq`/`ne` compare with an INT",
                    ));
                }
                let int = parse_int(int_text, name, cond_line)?;
                if keyword == "eq" {
                    Cond::Eq(var, int)
                } else {
                    Cond::Ne(var, int)
                }
            }
            ("pow2", 2) => Cond::Pow2(var),
            ("zero_mod_width", 2) => Cond::ZeroModWidth(var),
            _ => {
                return Err(err(
                    RuleErrorKind::BadPattern,
                    Some(name),
                    cond_line,
                    "a side condition is (eq ?c INT), (ne ?c INT), (pow2 ?c) or (zero_mod_width ?c)",
                ));
            }
        };
        let facts = reader.facts.get(var);
        let is_constant = constant.get(var).copied().unwrap_or(false);
        if !is_constant
            || facts.and_then(|f| f.sort) != Some(Sort::T)
            || domain.contains(&ScalarTy::Bool)
        {
            return Err(err(
                RuleErrorKind::ConditionVariable,
                Some(name),
                cond_line,
                "a `where` variable is a constant variable of sort T, with T not bool",
            ));
        }
        conds.push(cond);
    }

    // Operator admission at every domain type.
    for &(op, op_line) in &reader.ops {
        for &ty in &domain {
            if !op.admitted_at(ty) {
                return Err(err(
                    RuleErrorKind::OperatorNotAdmitted,
                    Some(name),
                    op_line,
                    format!("`{}` is not admitted at `{}`", op.name(), ty.name()),
                ));
            }
        }
    }

    let mut vars = Vec::with_capacity(reader.names.len());
    for (index, var_name) in reader.names.iter().enumerate() {
        let sort = reader
            .facts
            .get(index)
            .and_then(|f| f.sort)
            .ok_or_else(|| {
                err(
                    RuleErrorKind::SortConflict,
                    Some(name),
                    line,
                    format!("`?{var_name}` has no sort"),
                )
            })?;
        vars.push(Var {
            name: var_name.clone(),
            sort,
            constant: constant.get(index).copied().unwrap_or(false),
        });
    }

    let mut canonical = String::new();
    render(form, &mut canonical);
    let digest = statement_digest(&canonical);
    Ok(Rule {
        name: name.to_owned(),
        direction,
        domain,
        vars,
        lhs,
        rhs,
        conds,
        canonical,
        digest,
    })
}

#[cfg(test)]
mod tests;
