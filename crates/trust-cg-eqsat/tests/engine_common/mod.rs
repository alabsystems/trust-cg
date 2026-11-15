// crates/trust-cg-eqsat/tests/engine_common/mod.rs - shared support for the engine's own integration tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Support for the `engine_*` tests: parsing and validating modules,
//! substituting an output body, comparing two bodies on the reference
//! interpreter, and a test-only decoder for section 7.2 derivations.
//!
//! The decoder is the engine testing its own encoding, NOT the checker: it
//! re-reads the bytes, checks the canonical-encoding properties of section
//! 7.2, replays every proof step's conclusion (rule steps by instantiating
//! the registry rule's canonical text), and then evaluates both sides of
//! every claim on many leaf assignments (section 3 semantics, the crate's
//! own `eval`). It shares the engine's `eval` and vocabulary, so it is a
//! sanity check, not independent evidence; `trust-cg-eqsat-check` is the
//! independent reader.

#![allow(dead_code, clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use std::collections::BTreeMap;

use trust_cg_eqsat::derivation::{BinOpCode, CastOpCode, CmpPred, OpDesc, ScalarTy, UnOpCode};
use trust_cg_eqsat::eval;
use trust_cg_eqsat::rules::RuleSet;
use trust_cg_eqsat::vocab::{GraphWidths, mask};
use trust_ir::{
    FuncId, Function, InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter, Module,
    Ty,
};

/// Parse and validate a module from trust-ir text.
pub fn module(text: &str) -> Module {
    let module = trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "input does not validate: {errors:?}\n{text}"
    );
    module
}

/// The function named `name`.
pub fn function<'m>(module: &'m Module, name: &str) -> &'m Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"))
}

/// `module` with `output` in place of the function of the same id; asserts
/// that the result validates.
pub fn substitute(module: &Module, output: &Function) -> Module {
    let mut out = module.clone();
    let slot = out
        .functions
        .iter_mut()
        .find(|f| f.id == output.id)
        .expect("function in module");
    *slot = output.clone();
    let errors = trust_ir_build::validate_module(&out);
    assert!(
        errors.is_empty(),
        "output does not validate: {errors:?}\n{}",
        trust_ir::format::text_checked(&out).unwrap_or_default()
    );
    out
}

/// Boundary residues of a width.
pub fn boundaries(width: u32) -> Vec<u128> {
    let m = mask(width);
    if width == 1 {
        return vec![0, 1];
    }
    let half = 1u128 << (width - 1);
    let mut out = vec![
        0,
        1,
        2,
        3,
        7,
        m,
        m - 1,
        half,
        half - 1,
        half + 1,
        0x5555_5555_5555_5555_5555_5555_5555_5555 & m,
        0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa & m,
        u128::from(width),
        u128::from(width) + 1,
    ];
    for value in &mut out {
        *value &= m;
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// The interpreter value of residue `r` at `ty` (64-bit pointers).
pub fn value(ty: &Ty, r: u128) -> InterpretValue {
    if *ty == Ty::Bool {
        InterpretValue::bool(r == 1)
    } else {
        InterpretValue::int_at(ty.clone(), r as i128, 64).expect("integer value")
    }
}

/// The residue of an interpreter value.
pub fn residue(value: &InterpretValue) -> u128 {
    match &value.kind {
        InterpretValueKind::Bool(b) => u128::from(*b),
        InterpretValueKind::Int(int) => int.raw,
        other => panic!("not a scalar: {other:?}"),
    }
}

/// The outcome of one run: the returned residues, or the error code.
pub fn run(
    module: &Module,
    id: FuncId,
    args: &[InterpretValue],
) -> Result<Vec<u128>, InterpretErrorCode> {
    Interpreter::with_module(module)
        .execute_func(id, args.iter().cloned())
        .map(|outcome| outcome.returns.iter().map(residue).collect())
        .map_err(|error| error.code)
}

/// Argument vectors for a function of scalar parameters: every combination
/// of a few boundary values per parameter (at most `limit` vectors).
pub fn inputs(params: &[Ty], limit: usize) -> Vec<Vec<InterpretValue>> {
    let widths = GraphWidths::new(64);
    let per: Vec<Vec<u128>> = params
        .iter()
        .map(|ty| {
            let scalar = widths.scalar(ty).expect("scalar parameter");
            let width = widths.width(scalar).expect("width");
            boundaries(width)
        })
        .collect();
    let mut out: Vec<Vec<InterpretValue>> = vec![Vec::new()];
    for (ty, values) in params.iter().zip(&per) {
        let mut next = Vec::new();
        for prefix in &out {
            for r in values {
                let mut v = prefix.clone();
                v.push(value(ty, *r));
                next.push(v);
                if next.len() >= limit {
                    break;
                }
            }
            if next.len() >= limit {
                break;
            }
        }
        out = next;
    }
    out
}

/// Assert that `after` (substituted into `module`) behaves like the input
/// function on every argument vector.
pub fn assert_same_behaviour(module: &Module, before: &Function, after: &Function, limit: usize) {
    let output_module = substitute(module, after);
    let params = module.func_types[before.ty.0 as usize].params.clone();
    let mut returned = 0;
    for args in inputs(&params, limit) {
        let expected = run(module, before.id, &args);
        let actual = run(&output_module, before.id, &args);
        assert_eq!(expected, actual, "args {args:?}");
        returned += usize::from(expected.is_ok());
    }
    // Not vacuous: the input returned normally on some inputs.
    assert!(returned > 0, "no input returned normally");
}

// ---------------------------------------------------------------------------
// Test-only derivation decoder.

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Param(u32, u32),
    Result(u32, u32, u32),
    Const(ScalarTy, u128),
    Op(OpDesc, Vec<u32>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Proof {
    Refl(u32),
    Sym(u32),
    Trans(u32, u32),
    Congr(OpDesc, Vec<u32>),
    Rule {
        rule: u32,
        ty: ScalarTy,
        bindings: Vec<(String, u32)>,
        premises: Vec<u32>,
    },
}

#[derive(Debug, Clone)]
pub struct Decoded {
    pub function: String,
    pub rules: Vec<(String, [u8; 32])>,
    pub terms: Vec<Term>,
    pub proofs: Vec<Proof>,
    pub claims: Vec<u32>,
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn take(&mut self, n: usize) -> Result<&[u8], String> {
        let end = self.at.checked_add(n).ok_or("overflow")?;
        let slice = self.bytes.get(self.at..end).ok_or("truncated")?;
        self.at = end;
        Ok(slice)
    }
    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn str(&mut self) -> Result<String, String> {
        let n = self.u32()? as usize;
        String::from_utf8(self.take(n)?.to_vec()).map_err(|e| e.to_string())
    }
    fn ty(&mut self) -> Result<ScalarTy, String> {
        let code = self.u8()?;
        ScalarTy::from_code(code).ok_or_else(|| format!("bad type code {code:#x}"))
    }
    fn opdesc(&mut self) -> Result<OpDesc, String> {
        let kind = self.u8()?;
        Ok(match kind {
            1 => {
                let code = self.u8()?;
                let op = BinOpCode::ALL
                    .into_iter()
                    .find(|o| o.code() == code)
                    .ok_or("bad bin op")?;
                OpDesc::Bin(op, self.ty()?)
            }
            2 => {
                let code = self.u8()?;
                let op = UnOpCode::ALL
                    .into_iter()
                    .find(|o| o.code() == code)
                    .ok_or("bad un op")?;
                OpDesc::Un(op, self.ty()?)
            }
            3 => {
                let code = self.u8()?;
                let pred = CmpPred::ALL
                    .into_iter()
                    .find(|o| o.code() == code)
                    .ok_or("bad pred")?;
                OpDesc::Cmp(pred, self.ty()?)
            }
            4 => {
                let code = self.u8()?;
                let op = CastOpCode::ALL
                    .into_iter()
                    .find(|o| o.code() == code)
                    .ok_or("bad cast")?;
                OpDesc::Cast(op, self.ty()?, self.ty()?)
            }
            5 => OpDesc::Select(self.ty()?),
            other => return Err(format!("bad opdesc kind {other}")),
        })
    }
}

/// Decode and check the canonical-encoding properties of section 7.2.
pub fn decode(bytes: &[u8]) -> Result<Decoded, String> {
    let mut r = Reader { bytes, at: 0 };
    if r.take(8)? != b"TCGEQSAT" {
        return Err("magic".into());
    }
    if r.u32()? != 1 {
        return Err("version".into());
    }
    let function = r.str()?;
    let nrules = r.u32()?;
    let mut rules: Vec<(String, [u8; 32])> = Vec::new();
    for _ in 0..nrules {
        let name = r.str()?;
        let digest: [u8; 32] = r.take(32)?.try_into().unwrap();
        if let Some((prev, _)) = rules.last()
            && prev.as_bytes() >= name.as_bytes()
        {
            return Err("rule table not strictly sorted".into());
        }
        rules.push((name, digest));
    }
    let nterms = r.u32()?;
    let mut terms: Vec<Term> = Vec::new();
    for index in 0..nterms {
        let term = match r.u8()? {
            1 => Term::Param(r.u32()?, r.u32()?),
            2 => Term::Result(r.u32()?, r.u32()?, r.u32()?),
            3 => {
                let ty = r.ty()?;
                let residue = u128::from_le_bytes(r.take(16)?.try_into().unwrap());
                let width = GraphWidths::new(64).width(ty).unwrap();
                if residue > mask(width) {
                    return Err("const residue too wide".into());
                }
                Term::Const(ty, residue)
            }
            4 => {
                let desc = r.opdesc()?;
                let mut args = Vec::new();
                for _ in 0..desc.arity() {
                    let arg = r.u32()?;
                    if arg >= index {
                        return Err("term not topological".into());
                    }
                    args.push(arg);
                }
                Term::Op(desc, args)
            }
            tag => return Err(format!("bad term tag {tag}")),
        };
        if terms.contains(&term) {
            return Err("duplicate term".into());
        }
        terms.push(term);
    }
    let nproofs = r.u32()?;
    let mut proofs: Vec<Proof> = Vec::new();
    for index in 0..nproofs {
        let check_proof = |p: u32| {
            if p < index {
                Ok(p)
            } else {
                Err("proof not topological".to_owned())
            }
        };
        let check_term = |t: u32| {
            if t < nterms {
                Ok(t)
            } else {
                Err("term index out of range".to_owned())
            }
        };
        let proof = match r.u8()? {
            1 => Proof::Refl(check_term(r.u32()?)?),
            2 => Proof::Sym(check_proof(r.u32()?)?),
            3 => Proof::Trans(check_proof(r.u32()?)?, check_proof(r.u32()?)?),
            4 => {
                let desc = r.opdesc()?;
                let mut ps = Vec::new();
                for _ in 0..desc.arity() {
                    ps.push(check_proof(r.u32()?)?);
                }
                Proof::Congr(desc, ps)
            }
            5 => {
                let rule = r.u32()?;
                if rule >= nrules {
                    return Err("rule index out of range".into());
                }
                let ty = r.ty()?;
                let n = r.u32()?;
                let mut bindings: Vec<(String, u32)> = Vec::new();
                for _ in 0..n {
                    let name = r.str()?;
                    let term = check_term(r.u32()?)?;
                    if let Some((prev, _)) = bindings.last()
                        && prev.as_bytes() >= name.as_bytes()
                    {
                        return Err("bindings not strictly sorted".into());
                    }
                    bindings.push((name, term));
                }
                let m = r.u32()?;
                let mut premises = Vec::new();
                for k in 0..m {
                    let p = r.u32()?;
                    if p != k {
                        return Err("premises not 0..k-1".into());
                    }
                    premises.push(p);
                }
                Proof::Rule {
                    rule,
                    ty,
                    bindings,
                    premises,
                }
            }
            tag => return Err(format!("bad proof tag {tag}")),
        };
        if proofs.contains(&proof) {
            return Err("duplicate proof".into());
        }
        proofs.push(proof);
    }
    let nclaims = r.u32()?;
    let mut claims = Vec::new();
    for _ in 0..nclaims {
        let c = r.u32()?;
        if c >= nproofs {
            return Err("claim out of range".into());
        }
        if claims.last().is_some_and(|prev| *prev >= c) {
            return Err("claims not strictly increasing".into());
        }
        claims.push(c);
    }
    if r.at != bytes.len() {
        return Err("trailing bytes".into());
    }
    let decoded = Decoded {
        function,
        rules,
        terms,
        proofs,
        claims,
    };
    check_reachability(&decoded)?;
    Ok(decoded)
}

fn check_reachability(d: &Decoded) -> Result<(), String> {
    let mut proof_seen = vec![false; d.proofs.len()];
    let mut term_seen = vec![false; d.terms.len()];
    let mut rule_seen = vec![false; d.rules.len()];
    let mut stack: Vec<u32> = d.claims.clone();
    let mut terms: Vec<u32> = Vec::new();
    while let Some(p) = stack.pop() {
        if std::mem::replace(&mut proof_seen[p as usize], true) {
            continue;
        }
        match &d.proofs[p as usize] {
            Proof::Refl(t) => terms.push(*t),
            Proof::Sym(q) => stack.push(*q),
            Proof::Trans(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            Proof::Congr(_, ps) => stack.extend(ps),
            Proof::Rule { rule, bindings, .. } => {
                rule_seen[*rule as usize] = true;
                terms.extend(bindings.iter().map(|(_, t)| *t));
            }
        }
    }
    while let Some(t) = terms.pop() {
        if std::mem::replace(&mut term_seen[t as usize], true) {
            continue;
        }
        if let Term::Op(_, args) = &d.terms[t as usize] {
            terms.extend(args);
        }
    }
    if proof_seen.iter().any(|s| !s) {
        return Err("unreachable proof".into());
    }
    if term_seen.iter().any(|s| !s) {
        return Err("unreachable term".into());
    }
    if rule_seen.iter().any(|s| !s) {
        return Err("unreachable rule".into());
    }
    Ok(())
}

// ---- replay of conclusions -------------------------------------------------

#[derive(Debug, Clone)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

fn sexpr(text: &str) -> SExpr {
    let spaced = text.replace('(', " ( ").replace(')', " ) ");
    let mut stack: Vec<Vec<SExpr>> = vec![Vec::new()];
    for token in spaced.split_whitespace() {
        match token {
            "(" => stack.push(Vec::new()),
            ")" => {
                let list = stack.pop().unwrap();
                stack.last_mut().unwrap().push(SExpr::List(list));
            }
            atom => stack.last_mut().unwrap().push(SExpr::Atom(atom.to_owned())),
        }
    }
    stack.pop().unwrap().into_iter().next().unwrap()
}

fn list(e: &SExpr) -> &[SExpr] {
    match e {
        SExpr::List(items) => items,
        SExpr::Atom(a) => panic!("expected a list, got {a}"),
    }
}

fn atom(e: &SExpr) -> &str {
    match e {
        SExpr::Atom(a) => a,
        SExpr::List(_) => panic!("expected an atom"),
    }
}

fn int_residue(text: &str, width: u32) -> u128 {
    let (neg, digits) = match text.strip_prefix('-') {
        Some(d) => (true, d),
        None => (false, text),
    };
    let magnitude: u128 = digits.parse().unwrap();
    eval::int_residue(neg, magnitude, width)
}

fn rule_desc(name: &str, ty: ScalarTy) -> OpDesc {
    if name == "select" {
        return OpDesc::Select(ty);
    }
    if let Some(op) = BinOpCode::ALL.into_iter().find(|o| o.name() == name) {
        return match op {
            BinOpCode::BAnd | BinOpCode::BOr | BinOpCode::BXor => OpDesc::Bin(op, ScalarTy::Bool),
            _ => OpDesc::Bin(op, ty),
        };
    }
    if let Some(op) = UnOpCode::ALL.into_iter().find(|o| o.name() == name) {
        return OpDesc::Un(op, ty);
    }
    let pred = CmpPred::ALL
        .into_iter()
        .find(|p| p.name() == name)
        .unwrap_or_else(|| panic!("unknown rule operator {name}"));
    OpDesc::Cmp(pred, ty)
}

/// A term table that grows (decoded terms first).
pub struct Table {
    pub terms: Vec<Term>,
    index: BTreeMap<Term, u32>,
}

impl Table {
    fn new(terms: &[Term]) -> Self {
        let mut table = Table {
            terms: Vec::new(),
            index: BTreeMap::new(),
        };
        for t in terms {
            table.intern(t.clone());
        }
        table
    }
    fn intern(&mut self, term: Term) -> u32 {
        if let Some(i) = self.index.get(&term) {
            return *i;
        }
        let i = self.terms.len() as u32;
        self.terms.push(term.clone());
        self.index.insert(term, i);
        i
    }
}

fn instantiate(
    pat: &SExpr,
    ty: ScalarTy,
    bindings: &BTreeMap<String, u32>,
    table: &mut Table,
) -> u32 {
    let width = GraphWidths::new(64).width(ty).unwrap();
    match pat {
        SExpr::Atom(a) if a == "true" => table.intern(Term::Const(ScalarTy::Bool, 1)),
        SExpr::Atom(a) if a == "false" => table.intern(Term::Const(ScalarTy::Bool, 0)),
        SExpr::Atom(a) => *bindings
            .get(a.strip_prefix('?').unwrap())
            .unwrap_or_else(|| panic!("unbound {a}")),
        SExpr::List(items) => {
            let head = atom(&items[0]);
            match head {
                "const" => {
                    let arg = atom(&items[1]);
                    if let Some(var) = arg.strip_prefix('?') {
                        bindings[var]
                    } else {
                        table.intern(Term::Const(ty, int_residue(arg, width)))
                    }
                }
                "eval" => {
                    let desc = rule_desc(atom(&items[1]), ty);
                    let residues: Vec<u128> = items[2..]
                        .iter()
                        .map(|v| {
                            let t = bindings[atom(v).strip_prefix('?').unwrap()];
                            match &table.terms[t as usize] {
                                Term::Const(_, r) => *r,
                                other => panic!("eval of a non-constant {other:?}"),
                            }
                        })
                        .collect();
                    let value = eval::op(GraphWidths::new(64), desc, &residues).unwrap();
                    table.intern(Term::Const(desc.result_ty(), value))
                }
                name => {
                    let desc = rule_desc(name, ty);
                    let args: Vec<u32> = items[1..]
                        .iter()
                        .map(|p| instantiate(p, ty, bindings, table))
                        .collect();
                    table.intern(Term::Op(desc, args))
                }
            }
        }
    }
}

fn conditions_hold(
    conds: &[SExpr],
    ty: ScalarTy,
    bindings: &BTreeMap<String, u32>,
    table: &Table,
) -> bool {
    let width = GraphWidths::new(64).width(ty).unwrap();
    conds.iter().all(|c| {
        let items = list(c);
        let var = atom(&items[1]).strip_prefix('?').unwrap();
        let Term::Const(_, r) = table.terms[bindings[var] as usize] else {
            return false;
        };
        match atom(&items[0]) {
            "eq" => r == int_residue(atom(&items[2]), width),
            "ne" => r != int_residue(atom(&items[2]), width),
            "pow2" => r.count_ones() == 1,
            "zero_mod_width" => r % u128::from(width) == 0,
            other => panic!("unknown condition {other}"),
        }
    })
}

/// A replayed conclusion `(lhs, rhs, equiv)` over the grown term table.
pub type Conclusion = (u32, u32, bool);

/// Replay every proof against `registry`: returns each claim's conclusion
/// over the grown term table.
pub fn replay(d: &Decoded, registry: &RuleSet) -> Result<(Table, Vec<Conclusion>), String> {
    let mut table = Table::new(&d.terms);
    let mut concl: Vec<(u32, u32, bool)> = Vec::new();
    for proof in &d.proofs {
        let c = match proof {
            Proof::Refl(t) => (*t, *t, true),
            Proof::Sym(p) => {
                let (l, r, e) = concl[*p as usize];
                if !e {
                    return Err("Sym of refines".into());
                }
                (r, l, true)
            }
            Proof::Trans(p, q) => {
                let (a, b1, e1) = concl[*p as usize];
                let (b2, c, e2) = concl[*q as usize];
                if b1 != b2 {
                    return Err("Trans middle terms differ".into());
                }
                (a, c, e1 && e2)
            }
            Proof::Congr(desc, ps) => {
                let ls: Vec<u32> = ps.iter().map(|p| concl[*p as usize].0).collect();
                let rs: Vec<u32> = ps.iter().map(|p| concl[*p as usize].1).collect();
                let e = ps.iter().all(|p| concl[*p as usize].2);
                (
                    table.intern(Term::Op(*desc, ls)),
                    table.intern(Term::Op(*desc, rs)),
                    e,
                )
            }
            Proof::Rule {
                rule,
                ty,
                bindings,
                premises,
            } => {
                let (name, digest) = &d.rules[*rule as usize];
                let registered = registry
                    .rules()
                    .iter()
                    .find(|r| r.name() == name)
                    .ok_or_else(|| format!("rule {name} not in the registry"))?;
                if registered.statement_digest() != *digest {
                    return Err(format!("rule {name}: digest differs"));
                }
                if !registered.domain().contains(ty) {
                    return Err(format!("rule {name}: type outside the domain"));
                }
                if premises.len() != registered.side_condition_count() {
                    return Err(format!("rule {name}: premise count"));
                }
                let form = sexpr(registered.canonical_text());
                let items = list(&form);
                let map: BTreeMap<String, u32> = bindings.iter().cloned().collect();
                if !conditions_hold(&list(&items[6])[1..], *ty, &map, &table) {
                    return Err(format!("rule {name}: side condition fails"));
                }
                let lhs = instantiate(&list(&items[4])[1], *ty, &map, &mut table);
                let rhs = instantiate(&list(&items[5])[1], *ty, &map, &mut table);
                (lhs, rhs, registered.is_equiv())
            }
        };
        concl.push(c);
    }
    let claims = d.claims.iter().map(|c| concl[*c as usize]).collect();
    Ok((table, claims))
}

fn splitmix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

/// Evaluate both sides of every claim on `trials` leaf assignments and
/// assert they agree (graph operators are total and deterministic, so both
/// `equiv` and `refines` claims must agree on defined leaves).
pub fn assert_claims_hold(table: &Table, claims: &[(u32, u32, bool)], trials: u64) {
    let widths = GraphWidths::new(64);
    // Leaf widths from the operator positions they occupy.
    let mut leaf_width: BTreeMap<u32, u32> = BTreeMap::new();
    for term in &table.terms {
        if let Term::Op(desc, args) = term {
            for (i, a) in args.iter().enumerate() {
                if matches!(table.terms[*a as usize], Term::Param(..) | Term::Result(..)) {
                    let w = widths.width(desc.operand_ty(i).unwrap()).unwrap();
                    leaf_width.insert(*a, w);
                }
            }
        }
    }
    for trial in 0..trials {
        let mut values: Vec<Option<u128>> = Vec::with_capacity(table.terms.len());
        for (index, term) in table.terms.iter().enumerate() {
            let v = match term {
                Term::Param(..) | Term::Result(..) => {
                    let h = (u128::from(splitmix(index as u64 * 1000 + trial)) << 64)
                        | u128::from(splitmix(index as u64 * 7777 + trial));
                    let raw = match trial {
                        0 => 0,
                        1 => u128::MAX,
                        2 => 1,
                        _ => h,
                    };
                    Some(raw & mask(*leaf_width.get(&(index as u32)).unwrap_or(&128)))
                }
                Term::Const(_, r) => Some(*r),
                Term::Op(desc, args) => {
                    let a: Option<Vec<u128>> = args.iter().map(|x| values[*x as usize]).collect();
                    a.and_then(|a| eval::op(widths, *desc, &a))
                }
            };
            values.push(v);
        }
        for (l, r, _) in claims {
            let (lv, rv) = (values[*l as usize], values[*r as usize]);
            assert!(lv.is_some(), "claim lhs does not evaluate");
            assert_eq!(
                lv, rv,
                "claim {:?} -> {:?} differs on trial {trial}",
                table.terms[*l as usize], table.terms[*r as usize]
            );
        }
    }
}

/// Decode, replay and semantically check a derivation; returns it.
pub fn check_derivation(bytes: &[u8], registry: &RuleSet) -> Decoded {
    let decoded = decode(bytes).unwrap_or_else(|e| panic!("derivation does not decode: {e}"));
    let (table, claims) = replay(&decoded, registry).unwrap_or_else(|e| panic!("replay: {e}"));
    assert_claims_hold(&table, &claims, 48);
    decoded
}
