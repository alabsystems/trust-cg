// Copyright 2026 Andrew Yates | Apache-2.0
//! Bounded fixture DATA intake only; it changes no query or proof authority.
use super::*;
use crate::lowering_proof::MachineSideProvenance;
#[derive(Debug)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}
impl Sexp {
    fn atom(&self) -> &str {
        let Self::Atom(atom) = self else {
            panic!("fixture atom: {self:?}")
        };
        atom
    }
    fn list(&self) -> &[Self] {
        let Self::List(list) = self else {
            panic!("fixture list: {self:?}")
        };
        list
    }
    fn number(&self) -> u32 {
        self.atom().parse().unwrap()
    }
}

fn parse(text: &str) -> Vec<Sexp> {
    assert!(text.len() < 65_536 && text.is_ascii());
    let mut stack = vec![Vec::new()];
    let mut atom = String::new();
    let flush = |atom: &mut String, stack: &mut Vec<Vec<Sexp>>| {
        if !atom.is_empty() {
            stack
                .last_mut()
                .unwrap()
                .push(Sexp::Atom(std::mem::take(atom)));
        }
    };
    for c in text.chars() {
        match c {
            '(' => {
                flush(&mut atom, &mut stack);
                assert!(stack.len() < 128);
                stack.push(Vec::new());
            }
            ')' => {
                flush(&mut atom, &mut stack);
                let list = stack.pop().unwrap();
                stack.last_mut().unwrap().push(Sexp::List(list));
            }
            c if c.is_ascii_whitespace() => flush(&mut atom, &mut stack),
            c => atom.push(c),
        }
    }
    flush(&mut atom, &mut stack);
    assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

fn sort(term: &Sexp) -> SmtSort {
    let fields = term.list();
    match fields[0].atom() {
        "_" => {
            assert_eq!(fields[1].atom(), "BitVec");
            SmtSort::BitVec(fields[2].number())
        }
        "Array" => SmtSort::Array(Box::new(sort(&fields[1])), Box::new(sort(&fields[2]))),
        other => panic!("fixture sort {other}"),
    }
}

fn expression(term: &Sexp, symbols: &HashMap<String, E>) -> E {
    if let Sexp::Atom(atom) = term {
        return match atom.as_str() {
            "true" => E::BoolConst(true),
            "false" => E::BoolConst(false),
            _ => symbols.get(atom).unwrap().clone(),
        };
    }
    let fields = term.list();
    if let Sexp::List(indexed) = &fields[0] {
        assert_eq!(indexed[0].atom(), "_");
        let value = expression(&fields[1], symbols);
        return match indexed[1].atom() {
            "extract" => value.extract(indexed[2].number(), indexed[3].number()),
            "zero_extend" => value.zero_ext(indexed[2].number()),
            other => panic!("fixture indexed operator {other}"),
        };
    }
    let op = fields[0].atom();
    if op == "_" {
        return E::bv_const(
            fields[1]
                .atom()
                .strip_prefix("bv")
                .unwrap()
                .parse()
                .unwrap(),
            fields[2].number(),
        );
    }
    let a = expression(&fields[1], symbols);
    if op == "not" {
        return a.not_expr();
    }
    let b = expression(&fields[2], symbols);
    match op {
        "=" => a.eq_expr(b),
        "and" => a.and_expr(b),
        "or" => a.or_expr(b),
        "bvadd" => a.bvadd(b),
        "bvsub" => a.bvsub(b),
        "bvmul" => a.bvmul(b),
        "bvand" => a.bvand(b),
        "bvor" => a.bvor(b),
        "bvshl" => a.bvshl(b),
        "bvule" => a.bvule(b),
        "bvuge" => a.bvuge(b),
        "bvult" => a.bvult(b),
        "select" => E::select(a, b),
        "store" => E::store(a, b, expression(&fields[3], symbols)),
        "ite" => E::ite(a, b, expression(&fields[3], symbols)),
        other => panic!("fixture operator {other}"),
    }
}

pub(super) fn captured(raw: &str, name: &str) -> ProofObligation {
    let mut symbols = HashMap::new();
    let mut inputs = Vec::new();
    let mut assertion = None;
    for command in parse(raw) {
        let fields = command.list();
        match fields[0].atom() {
            "declare-const" => {
                let name = fields[1].atom().to_owned();
                let SmtSort::BitVec(width) = sort(&fields[2]) else {
                    panic!("fixture input")
                };
                symbols.insert(name.clone(), E::var(name.clone(), width));
                inputs.push((name, width));
            }
            "declare-fun" => {
                assert!(fields[2].list().is_empty());
                let name = fields[1].atom().to_owned();
                symbols.insert(name.clone(), E::uf(name, vec![], sort(&fields[3])));
            }
            "assert" => {
                assert!(assertion.is_none());
                assertion = Some(expression(&fields[1], &symbols));
            }
            "set-option" | "set-logic" | "check-sat" | "exit" => {}
            other => panic!("fixture command {other}"),
        }
    }
    fn leaves(term: E, output: &mut Vec<E>) {
        if let E::And { lhs, rhs } = term {
            leaves((*lhs).clone(), output);
            leaves((*rhs).clone(), output);
        } else {
            output.push(term);
        }
    }
    let original = assertion.unwrap();
    let mut parts = Vec::new();
    leaves(original.clone(), &mut parts);
    let E::Not { operand } = parts.pop().unwrap() else {
        panic!("original terminal")
    };
    let E::Eq { lhs, rhs } = operand.as_ref() else {
        panic!("original equivalence")
    };
    let query = ProofObligation {
        name: name.into(),
        trust_ir_expr: lhs.as_ref().clone(),
        aarch64_expr: rhs.as_ref().clone(),
        inputs,
        preconditions: parts.into_iter().rev().collect(),
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    assert_eq!(query.negated_equivalence(), original);
    query
}
