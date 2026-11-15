// trust-cg-eqsat-check/tests/common/mod.rs - test-only derivation encoder, rule texts and body parsing
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared by the integration tests: a hand-written encoder of the
//! docs/eqsat-tier-e.md section 7.2 byte format (written from the spec, not
//! from the engine) that writes entries exactly as given, so a test can build
//! a canonical derivation and then break one canonicity rule at a time; the
//! rule texts the tests register; and trust-ir text parsing.
//!
//! Not every test binary uses every helper.
#![allow(dead_code)]

use trust_cg_eqsat_check::{Registry, Rejection, Verdict, check};
use trust_ir::{Function, Module};

pub const BOOL: u8 = 0x01;
pub const U8: u8 = 0x20;
pub const U32: u8 = 0x22;
pub const U64: u8 = 0x23;

pub const ADD: u8 = 1;
pub const MUL: u8 = 3;

/// An operator descriptor, as raw codes.
#[derive(Clone, Debug)]
pub enum OpD {
    Bin(u8, u8),
    Un(u8, u8),
    Cmp(u8, u8),
    Cast(u8, u8, u8),
    Select(u8),
}

#[derive(Clone, Debug)]
pub enum T {
    Param(u32, u32),
    Result(u32, u32, u32),
    Const(u8, u128),
    Op(OpD, Vec<u32>),
}

#[derive(Clone, Debug)]
pub enum P {
    Refl(u32),
    Sym(u32),
    Trans(u32, u32),
    Congr(OpD, Vec<u32>),
    Rule {
        rule: u32,
        ty: u8,
        bindings: Vec<(String, u32)>,
        premises: Vec<u32>,
    },
}

pub fn rule(rule: u32, ty: u8, bindings: &[(&str, u32)], premises: &[u32]) -> P {
    P::Rule {
        rule,
        ty,
        bindings: bindings
            .iter()
            .map(|(n, t)| ((*n).to_owned(), *t))
            .collect(),
        premises: premises.to_vec(),
    }
}

#[derive(Clone, Debug)]
pub struct Deriv {
    pub function: String,
    pub rules: Vec<(String, [u8; 32])>,
    pub terms: Vec<T>,
    pub proofs: Vec<P>,
    pub claims: Vec<u32>,
}

fn put_u32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn put_str(out: &mut Vec<u8>, s: &str) {
    put_u32(out, s.len() as u32);
    out.extend_from_slice(s.as_bytes());
}

fn put_op(out: &mut Vec<u8>, op: &OpD) {
    match op {
        OpD::Bin(o, t) => out.extend_from_slice(&[0x01, *o, *t]),
        OpD::Un(o, t) => out.extend_from_slice(&[0x02, *o, *t]),
        OpD::Cmp(p, t) => out.extend_from_slice(&[0x03, *p, *t]),
        OpD::Cast(o, s, d) => out.extend_from_slice(&[0x04, *o, *s, *d]),
        OpD::Select(t) => out.extend_from_slice(&[0x05, *t]),
    }
}

impl Deriv {
    /// A derivation with no entries for `function`.
    pub fn header(function: &str) -> Deriv {
        Deriv {
            function: function.to_owned(),
            rules: Vec::new(),
            terms: Vec::new(),
            proofs: Vec::new(),
            claims: Vec::new(),
        }
    }

    /// Adds a rule-table entry with the registry's digest.
    pub fn with_rule(mut self, registry: &Registry, name: &str) -> Deriv {
        let digest = registry.statement_digest(name).expect("rule registered");
        self.rules.push((name.to_owned(), digest));
        self
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(b"TCGEQSAT");
        put_u32(&mut out, 1);
        put_str(&mut out, &self.function);
        put_u32(&mut out, self.rules.len() as u32);
        for (name, digest) in &self.rules {
            put_str(&mut out, name);
            out.extend_from_slice(digest);
        }
        put_u32(&mut out, self.terms.len() as u32);
        for t in &self.terms {
            match t {
                T::Param(b, i) => {
                    out.push(0x01);
                    put_u32(&mut out, *b);
                    put_u32(&mut out, *i);
                }
                T::Result(b, k, j) => {
                    out.push(0x02);
                    put_u32(&mut out, *b);
                    put_u32(&mut out, *k);
                    put_u32(&mut out, *j);
                }
                T::Const(ty, r) => {
                    out.push(0x03);
                    out.push(*ty);
                    out.extend_from_slice(&r.to_le_bytes());
                }
                T::Op(op, args) => {
                    out.push(0x04);
                    put_op(&mut out, op);
                    for a in args {
                        put_u32(&mut out, *a);
                    }
                }
            }
        }
        put_u32(&mut out, self.proofs.len() as u32);
        for p in &self.proofs {
            match p {
                P::Refl(t) => {
                    out.push(0x01);
                    put_u32(&mut out, *t);
                }
                P::Sym(q) => {
                    out.push(0x02);
                    put_u32(&mut out, *q);
                }
                P::Trans(a, b) => {
                    out.push(0x03);
                    put_u32(&mut out, *a);
                    put_u32(&mut out, *b);
                }
                P::Congr(op, ps) => {
                    out.push(0x04);
                    put_op(&mut out, op);
                    for q in ps {
                        put_u32(&mut out, *q);
                    }
                }
                P::Rule {
                    rule,
                    ty,
                    bindings,
                    premises,
                } => {
                    out.push(0x05);
                    put_u32(&mut out, *rule);
                    out.push(*ty);
                    put_u32(&mut out, bindings.len() as u32);
                    for (n, t) in bindings {
                        put_str(&mut out, n);
                        put_u32(&mut out, *t);
                    }
                    put_u32(&mut out, premises.len() as u32);
                    for k in premises {
                        put_u32(&mut out, *k);
                    }
                }
            }
        }
        put_u32(&mut out, self.claims.len() as u32);
        for c in &self.claims {
            put_u32(&mut out, *c);
        }
        out
    }
}

/// The rules the tests register.
pub const RULES: &str = "\
; test rules (written for these tests, in the style of a rule file)
(rule add_comm
  (direction equiv)
  (domain u32)
  (lhs (add ?x ?y))
  (rhs (add ?y ?x))
  (where))

(rule add_zero
  (direction equiv)
  (domain u32)
  (lhs (add ?x (const 0)))
  (rhs ?x)
  (where))

(rule fold_add
  (direction equiv)
  (domain u32)
  (lhs (add (const ?a) (const ?b)))
  (rhs (eval add ?a ?b))
  (where))

(rule mul_one
  (direction equiv)
  (domain u32 i32)
  (lhs (mul ?x (const 1)))
  (rhs ?x)
  (where))

(rule mul_zero
  (direction refines)
  (domain u32)
  (lhs (mul ?x (const 0)))
  (rhs (const 0))
  (where))

(rule rotl_full
  (direction equiv)
  (domain u32)
  (lhs (rotl ?x (const ?c)))
  (rhs ?x)
  (where (zero_mod_width ?c)))
";

pub fn registry() -> Registry {
    Registry::parse(RULES).expect("test rules parse")
}

pub const HEADER: &str = "; TrustIr text format v1\nmodule \"m\"\nfile 0 \"m.rs\"\n\n";

/// Parses a module from `HEADER` + `body` and returns it with its function
/// named `f`.
pub fn parse(body: &str) -> (Module, Function) {
    let text = format!("{HEADER}{body}");
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("parse failed: {e}\n{text}"));
    let f = module.function_by_name("f").expect("function f").clone();
    (module, f)
}

/// Checks `output_body` against `input_body` (each a full module text body
/// with function `f`), in the input's module.
pub fn run(
    input_body: &str,
    output_body: &str,
    d: &Deriv,
    reg: &Registry,
) -> Result<Verdict, Rejection> {
    let (module, input) = parse(input_body);
    let (_, output) = parse(output_body);
    check(&module, &input, &output, &d.encode(), reg)
}

pub fn run_bytes(
    input_body: &str,
    output_body: &str,
    bytes: &[u8],
    reg: &Registry,
) -> Result<Verdict, Rejection> {
    let (module, input) = parse(input_body);
    let (_, output) = parse(output_body);
    check(&module, &input, &output, bytes, reg)
}

/// The class of a rejection, or "accepted".
pub fn class(r: &Result<Verdict, Rejection>) -> &'static str {
    match r {
        Ok(_) => "accepted",
        Err(e) => e.class(),
    }
}

// ---------------------------------------------------------------- scenarios

/// Scenario A: `(mul R (const 1))` returned, rewritten to `R` by mul_one.
/// R = Result(bb0, 0, 0) is the xor frontier instruction (defined).
pub const A_IN: &str = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = const u32 1
    %4 = mul u32 %2, %3
    ret %4
}
";

pub const A_OUT: &str = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    ret %2
}
";

pub fn a_deriv(reg: &Registry) -> Deriv {
    let mut d = Deriv::header("f").with_rule(reg, "mul_one");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[])];
    d.claims = vec![0];
    d
}

/// Scenario B: `(mul (add R (const 0)) (const 1))` to `R` by Trans(mul_one,
/// add_zero).
pub const B_IN: &str = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = add u32 %2, %1
    %4 = const u32 1
    %5 = mul u32 %3, %4
    ret %5
}
";

pub const B_OUT: &str = A_OUT;

pub fn b_deriv(reg: &Registry) -> Deriv {
    let mut d = Deriv::header("f")
        .with_rule(reg, "add_zero")
        .with_rule(reg, "mul_one");
    d.terms = vec![
        T::Result(0, 0, 0),
        T::Const(U32, 0),
        T::Op(OpD::Bin(ADD, U32), vec![0, 1]),
    ];
    d.proofs = vec![
        rule(1, U32, &[("x", 2)], &[]),
        rule(0, U32, &[("x", 0)], &[]),
        P::Trans(0, 1),
    ];
    d.claims = vec![2];
    d
}

/// Scenario C: `(add A B)` to `(add B A)` by add_comm (two bindings).
pub const C_IN: &str = "\
functy.0 = (u32, u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: u32):
    %2 = const u32 0
    %3 = xor u32 %0, %2
    %4 = xor u32 %1, %2
    %5 = add u32 %3, %4
    ret %5
}
";

pub const C_OUT: &str = "\
functy.0 = (u32, u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: u32):
    %2 = const u32 0
    %3 = xor u32 %0, %2
    %4 = xor u32 %1, %2
    %5 = add u32 %4, %3
    ret %5
}
";

pub fn c_deriv(reg: &Registry) -> Deriv {
    let mut d = Deriv::header("f").with_rule(reg, "add_comm");
    d.terms = vec![T::Result(0, 0, 0), T::Result(0, 1, 0)];
    d.proofs = vec![rule(0, U32, &[("x", 0), ("y", 1)], &[])];
    d.claims = vec![0];
    d
}
