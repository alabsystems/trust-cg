// trust-cg-eqsat-check/src/replay.rs - typing of the term table and replay of every proof step
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Replays a decoded derivation (docs/eqsat-tier-e.md sections 7.1 and 8
//! item 5) against the registry and the input body's leaves.
//!
//! Every conclusion is computed here, never read from the derivation: a
//! `Rule` step concludes this crate's own instantiation of the registered
//! lhs and rhs at the instance type, with `(eval ...)` folded by section 3 as
//! implemented in `semantics`. What a replayed conclusion establishes is
//! exactly what the registry states (unproved until PKG-U2) composed by
//! symmetry, transitivity and congruence; `refines` is never reversed.

use std::collections::BTreeMap;

use crate::decode::{Derivation, RawProof, RawTerm};
use crate::reader::term_rejection;
use crate::registry::{Cond, Direction, Pat, Registry, Rule};
use crate::rejection::{Rejection, TermSite};
use crate::semantics::eval;
use crate::terms::{Interner, Leaf, Node, TermError, TermId};
use crate::types::Sty;

/// A replayed conclusion `(lhs, rhs, direction)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Conclusion {
    pub(crate) lhs: TermId,
    pub(crate) rhs: TermId,
    pub(crate) dir: Direction,
}

fn combine(a: Direction, b: Direction) -> Direction {
    if a == Direction::Equiv && b == Direction::Equiv {
        Direction::Equiv
    } else {
        Direction::Refines
    }
}

/// Checks the rule table against the registry, interns the term table and
/// replays every proof. Returns each proof's conclusion, by proof index.
pub(crate) fn replay(
    d: &Derivation,
    registry: &Registry,
    interner: &mut Interner,
) -> Result<Vec<Conclusion>, Rejection> {
    // Rule table: same name and same statement digest.
    let mut table: Vec<&Rule> = Vec::with_capacity(d.rules.len());
    for (i, (name, digest)) in d.rules.iter().enumerate() {
        let Some(rule) = registry.rule(name) else {
            return Err(Rejection::UnknownRule {
                index: i,
                name: name.clone(),
            });
        };
        if &rule.digest != digest {
            return Err(Rejection::DigestMismatch {
                index: i,
                name: name.clone(),
            });
        }
        table.push(rule);
    }

    // Term table.
    let mut ids: Vec<TermId> = Vec::with_capacity(d.terms.len());
    for (i, raw) in d.terms.iter().enumerate() {
        let site = TermSite::TermTable(i);
        let id = match raw {
            RawTerm::Param { block, index } => interner.leaf(Leaf::Param {
                block: *block,
                index: *index,
            }),
            RawTerm::Result {
                block,
                ordinal,
                index,
            } => interner.leaf(Leaf::Result {
                block: *block,
                ordinal: *ordinal,
                index: *index,
            }),
            RawTerm::Const { ty, residue } => interner.constant(*ty, *residue),
            RawTerm::Op { desc, args } => {
                let mapped: Vec<TermId> = args.iter().map(|a| ids[*a as usize]).collect();
                interner.op(*desc, &mapped)
            }
        }
        .map_err(|e| term_rejection(e, site))?;
        ids.push(id);
    }

    // Proofs.
    let mut out: Vec<Conclusion> = Vec::with_capacity(d.proofs.len());
    for (i, proof) in d.proofs.iter().enumerate() {
        let c = match proof {
            RawProof::Refl(t) => {
                let t = ids[*t as usize];
                Conclusion {
                    lhs: t,
                    rhs: t,
                    dir: Direction::Equiv,
                }
            }
            RawProof::Sym(p) => {
                let p = out[*p as usize];
                if p.dir != Direction::Equiv {
                    return Err(Rejection::SymOfRefines { proof: i });
                }
                Conclusion {
                    lhs: p.rhs,
                    rhs: p.lhs,
                    dir: Direction::Equiv,
                }
            }
            RawProof::Trans(p, q) => {
                let (p, q) = (out[*p as usize], out[*q as usize]);
                if p.rhs != q.lhs {
                    return Err(Rejection::TransMiddleMismatch {
                        proof: i,
                        left_rhs: interner.render(p.rhs),
                        right_lhs: interner.render(q.lhs),
                    });
                }
                Conclusion {
                    lhs: p.lhs,
                    rhs: q.rhs,
                    dir: combine(p.dir, q.dir),
                }
            }
            RawProof::Congr(desc, ps) => {
                if ps.len() != desc.arity() {
                    return Err(Rejection::CongrMismatch {
                        proof: i,
                        detail: format!("{} takes {} children", desc.describe(), desc.arity()),
                    });
                }
                let children: Vec<Conclusion> = ps.iter().map(|p| out[*p as usize]).collect();
                for (k, (child, want)) in children.iter().zip(desc.operand_tys()).enumerate() {
                    let lt = interner.ty(child.lhs);
                    let rt = interner.ty(child.rhs);
                    if lt != Some(want) || rt != Some(want) {
                        return Err(Rejection::CongrMismatch {
                            proof: i,
                            detail: format!(
                                "child {k} concludes terms of type {:?}/{:?}, {} needs {}",
                                lt.map(Sty::name),
                                rt.map(Sty::name),
                                desc.describe(),
                                want.name()
                            ),
                        });
                    }
                }
                let lhs_args: Vec<TermId> = children.iter().map(|c| c.lhs).collect();
                let rhs_args: Vec<TermId> = children.iter().map(|c| c.rhs).collect();
                let site = TermSite::Proof(i);
                let lhs = interner
                    .op(*desc, &lhs_args)
                    .map_err(|e| term_rejection(e, site.clone()))?;
                let rhs = interner
                    .op(*desc, &rhs_args)
                    .map_err(|e| term_rejection(e, site))?;
                let dir = children
                    .iter()
                    .fold(Direction::Equiv, |acc, c| combine(acc, c.dir));
                Conclusion { lhs, rhs, dir }
            }
            RawProof::Rule {
                rule,
                ty,
                bindings,
                premises,
            } => {
                let r = table[*rule as usize];
                let sigma: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(n, t)| (n.clone(), ids[*t as usize]))
                    .collect();
                rule_step(i, r, *ty, &sigma, premises, interner)?
            }
        };
        out.push(c);
    }
    Ok(out)
}

fn binding_mismatch(proof: usize, rule: &Rule, detail: String) -> Rejection {
    Rejection::BindingMismatch {
        proof,
        rule: rule.name.clone(),
        detail,
    }
}

/// One `Rule(rule, T, sigma, premises)` step.
fn rule_step(
    proof: usize,
    rule: &Rule,
    t: Sty,
    sigma: &[(String, TermId)],
    premises: &[u32],
    interner: &mut Interner,
) -> Result<Conclusion, Rejection> {
    let ctx = interner.ctx();
    let Some(w) = ctx.width(t).filter(|_| rule.domain.contains(&t)) else {
        return Err(Rejection::TypeNotInDomain {
            proof,
            rule: rule.name.clone(),
            ty: t.name(),
        });
    };

    // The substitution binds exactly the rule's variables (both sorted).
    let bound: Vec<&str> = sigma.iter().map(|(n, _)| n.as_str()).collect();
    let wanted: Vec<&str> = rule.vars.keys().map(String::as_str).collect();
    if bound != wanted {
        return Err(binding_mismatch(
            proof,
            rule,
            format!("binds {bound:?}, the rule's variables are {wanted:?}"),
        ));
    }
    let mut env: BTreeMap<&str, TermId> = BTreeMap::new();
    for (name, term) in sigma {
        let Some(info) = rule.vars.get(name) else {
            return Err(binding_mismatch(
                proof,
                rule,
                format!("?{name} is not a variable"),
            ));
        };
        let want = info.sort.at(t);
        let have = interner.ty(*term);
        if have != Some(want) {
            return Err(binding_mismatch(
                proof,
                rule,
                format!(
                    "?{name} has sort {} but is bound to a term of type {:?}",
                    want.name(),
                    have.map(Sty::name)
                ),
            ));
        }
        match interner.node(*term) {
            Some(Node::Const(..)) => {}
            Some(Node::Leaf(leaf)) => {
                if info.constant {
                    return Err(binding_mismatch(
                        proof,
                        rule,
                        format!("constant variable ?{name} is bound to the leaf {leaf}"),
                    ));
                }
                let defined = interner.leaf_info(*leaf).is_some_and(|i| i.defined);
                if !defined {
                    return Err(Rejection::MaybePoisonLeaf {
                        site: TermSite::Proof(proof),
                        leaf: leaf.to_string(),
                    });
                }
            }
            Some(Node::Op(..)) => {
                if info.constant {
                    return Err(binding_mismatch(
                        proof,
                        rule,
                        format!("constant variable ?{name} is bound to an operator term"),
                    ));
                }
            }
            None => {
                return Err(binding_mismatch(
                    proof,
                    rule,
                    format!("?{name} names no term"),
                ));
            }
        }
        env.insert(name.as_str(), *term);
    }

    // Premises: exactly the indices of the rule's side conditions.
    let expected: Vec<u32> = (0..rule.conds.len())
        .map(|k| u32::try_from(k).unwrap_or(u32::MAX))
        .collect();
    if premises != expected.as_slice() {
        return Err(Rejection::PremiseMismatch {
            proof,
            rule: rule.name.clone(),
            expected: rule.conds.len(),
            found: premises.to_vec(),
        });
    }
    for (k, cond) in rule.conds.iter().enumerate() {
        let v = match cond {
            Cond::Eq(v, _) | Cond::Ne(v, _) | Cond::Pow2(v) | Cond::ZeroModWidth(v) => v,
        };
        let residue = env
            .get(v.as_str())
            .and_then(|id| interner.const_value(*id))
            .map(|(_, r)| r);
        let Some(r) = residue else {
            return Err(binding_mismatch(
                proof,
                rule,
                format!("side-condition variable ?{v} is not bound to a constant"),
            ));
        };
        let holds = match cond {
            Cond::Eq(_, lit) => r == lit.residue(w),
            Cond::Ne(_, lit) => r != lit.residue(w),
            Cond::Pow2(_) => r.count_ones() == 1,
            Cond::ZeroModWidth(_) => r % u128::from(w) == 0,
        };
        if !holds {
            return Err(Rejection::SideConditionFailed {
                proof,
                rule: rule.name.clone(),
                condition: k,
            });
        }
    }

    let site = TermSite::Proof(proof);
    let lhs = instantiate(&rule.lhs, t, w, &env, interner)
        .map_err(|e| term_rejection(e, site.clone()))?;
    let rhs = instantiate(&rule.rhs, t, w, &env, interner).map_err(|e| term_rejection(e, site))?;
    Ok(Conclusion {
        lhs,
        rhs,
        dir: rule.direction,
    })
}

/// `pat[sigma]` at instance type `t` (width `w`).
fn instantiate(
    pat: &Pat,
    t: Sty,
    w: u32,
    env: &BTreeMap<&str, TermId>,
    interner: &mut Interner,
) -> Result<TermId, TermError> {
    match pat {
        Pat::Var(v) | Pat::ConstVar(v) => env
            .get(v.as_str())
            .copied()
            .ok_or_else(|| TermError::IllTyped(format!("?{v} is unbound"))),
        Pat::ConstInt(lit) => {
            if t.is_bool() {
                return Err(TermError::IllTyped("(const INT) at Bool".to_owned()));
            }
            interner.constant(t, lit.residue(w))
        }
        Pat::Bool(b) => interner.constant(Sty::Bool, u128::from(*b)),
        Pat::Op(op, args) => {
            let mut ids = Vec::with_capacity(args.len());
            for a in args {
                ids.push(instantiate(a, t, w, env, interner)?);
            }
            interner.op(op.at(t), &ids)
        }
        Pat::Eval(op, vs) => {
            let desc = op.at(t);
            let mut residues = Vec::with_capacity(vs.len());
            for v in vs {
                let id = env
                    .get(v.as_str())
                    .copied()
                    .ok_or_else(|| TermError::IllTyped(format!("?{v} is unbound")))?;
                let Some((_, r)) = interner.const_value(id) else {
                    return Err(TermError::IllTyped(format!(
                        "eval argument ?{v} is not bound to a constant"
                    )));
                };
                residues.push(r);
            }
            let Some(r) = eval(desc, &residues, interner.ctx()) else {
                return Err(TermError::IllTyped(format!(
                    "eval of {} is undefined on its arguments",
                    desc.describe()
                )));
            };
            interner.constant(desc.result_ty(), r)
        }
    }
}
