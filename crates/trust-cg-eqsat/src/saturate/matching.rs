// crates/trust-cg-eqsat/src/saturate/matching.rs - e-matching of rule patterns and rule application
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! E-matching and rule application for Tier S (`docs/eqsat-tier-s.md`
//! section 4.2).
//!
//! A round first collects every match of the stage's rules against a
//! snapshot of the classes (no term is made and no class changes while
//! matching), then applies the matches in the order they were found. The
//! order is fixed: rules in file order, a rule's domain types in file
//! order, classes oldest first, a class's e-nodes oldest first, argument
//! patterns left to right.
//!
//! Applying a match makes the two concrete terms `lhs[sigma]` and
//! `rhs[sigma]` (a term variable stands for the representative of its
//! class, a constant variable for the constant term it matched) and merges
//! their classes under one `Rule` step. `lhs[sigma]` is the e-node that
//! matched, so it joins that e-node's class by congruence. A match whose
//! `rhs[sigma]` is already in the class of its `lhs[sigma]` makes no term.

use std::collections::BTreeMap;

use crate::derivation::TermRef;
use crate::proof::{EngineResult, invariant};
use crate::rules::{Pat, Rule};
use crate::saturate::egraph::{ClassView, Graph, TNode, Tid};
use crate::vocab::{GraphWidths, OpDesc, ScalarTy};

/// What a rule variable is bound to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bind {
    /// A term variable: the representative of the class it matched.
    Class(Tid),
    /// A constant variable: the constant term it matched.
    Const {
        term: Tid,
        ty: ScalarTy,
        residue: u128,
    },
}

type Binds = Vec<Option<Bind>>;

/// One complete match of a rule's lhs whose side conditions hold.
#[derive(Debug, Clone)]
pub(crate) struct Match {
    /// The rule, by index into the stage's rules.
    pub(crate) rule: usize,
    ty: ScalarTy,
    binds: Binds,
}

/// A read-only view of the classes for one round of matching.
pub(crate) struct Snapshot {
    classes: Vec<ClassView>,
    /// Each class's position in `classes`, by representative.
    position: BTreeMap<Tid, usize>,
    /// Every term's representative at the time of the snapshot.
    root: Vec<Tid>,
    nodes: Vec<TNode>,
}

impl Snapshot {
    pub(crate) fn take(graph: &mut Graph) -> EngineResult<Self> {
        let classes = graph.classes()?;
        let position = classes
            .iter()
            .enumerate()
            .map(|(index, class)| (class.root, index))
            .collect();
        let mut root = Vec::with_capacity(graph.len());
        let mut nodes = Vec::with_capacity(graph.len());
        for raw in 0..graph.len() {
            let term = graph_term(raw)?;
            root.push(graph.find(term));
            nodes.push(graph.node(term)?.clone());
        }
        Ok(Self {
            classes,
            position,
            root,
            nodes,
        })
    }

    fn enodes(&self, class: Tid) -> &[Tid] {
        match self
            .position
            .get(&class)
            .and_then(|index| self.classes.get(*index))
        {
            Some(view) => &view.enodes,
            None => &[],
        }
    }

    fn root_of(&self, term: Tid) -> EngineResult<Tid> {
        match self.root.get(term.index()) {
            Some(root) => Ok(*root),
            None => invariant("a term newer than the snapshot"),
        }
    }

    fn node(&self, term: Tid) -> EngineResult<&TNode> {
        match self.nodes.get(term.index()) {
            Some(node) => Ok(node),
            None => invariant("a term newer than the snapshot"),
        }
    }

    /// Every match of `rules`, in the fixed order, stopping once `cap`
    /// complete matches are found. Partial matches are never cut short, so
    /// fewer than `cap` results means every match was found.
    pub(crate) fn matches(
        &self,
        rules: &[&Rule],
        widths: GraphWidths,
        cap: usize,
    ) -> EngineResult<Vec<Match>> {
        let mut out = Vec::new();
        for (index, rule) in rules.iter().enumerate() {
            let Pat::Op(root_op, pats) = rule.lhs() else {
                continue;
            };
            for ty in rule.domain().iter().copied() {
                let Some(width) = widths.width(ty) else {
                    continue;
                };
                let desc = root_op.desc(ty);
                for class in &self.classes {
                    for enode in &class.enodes {
                        let TNode::Op(found, args) = self.node(*enode)? else {
                            continue;
                        };
                        if *found != desc || args.len() != pats.len() {
                            continue;
                        }
                        let empty: Binds = vec![None; rule.vars().len()];
                        for binds in self.match_args(rule, ty, width, pats, args, empty)? {
                            if rule.side_conditions_hold(width, |var| constant_of(&binds, var)) {
                                out.push(Match {
                                    rule: index,
                                    ty,
                                    binds,
                                });
                                if out.len() >= cap {
                                    return Ok(out);
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(out)
    }

    fn match_args(
        &self,
        rule: &Rule,
        ty: ScalarTy,
        width: u32,
        pats: &[Pat],
        args: &[Tid],
        binds: Binds,
    ) -> EngineResult<Vec<Binds>> {
        let mut partial = vec![binds];
        for (pat, arg) in pats.iter().zip(args) {
            let class = self.root_of(*arg)?;
            let mut next = Vec::new();
            for binds in &partial {
                next.extend(self.match_pat(rule, ty, width, pat, class, binds)?);
            }
            partial = next;
            if partial.is_empty() {
                break;
            }
        }
        Ok(partial)
    }

    fn match_pat(
        &self,
        rule: &Rule,
        ty: ScalarTy,
        width: u32,
        pat: &Pat,
        class: Tid,
        binds: &Binds,
    ) -> EngineResult<Vec<Binds>> {
        let mut out = Vec::new();
        match pat {
            Pat::Var(var) => match binds.get(*var).copied().flatten() {
                None => {
                    let mut next = binds.clone();
                    if let Some(slot) = next.get_mut(*var) {
                        *slot = Some(Bind::Class(class));
                    }
                    out.push(next);
                }
                Some(Bind::Class(bound)) if bound == class => out.push(binds.clone()),
                Some(_) => {}
            },
            Pat::ConstVar(var) => {
                let Some(info) = rule.vars().get(*var) else {
                    return invariant("a pattern names an unknown variable");
                };
                let position_ty = info.sort.at(ty);
                for enode in self.enodes(class) {
                    let TNode::Const(const_ty, residue) = *self.node(*enode)? else {
                        continue;
                    };
                    if const_ty != position_ty {
                        continue;
                    }
                    match binds.get(*var).copied().flatten() {
                        None => {
                            let mut next = binds.clone();
                            if let Some(slot) = next.get_mut(*var) {
                                *slot = Some(Bind::Const {
                                    term: *enode,
                                    ty: const_ty,
                                    residue,
                                });
                            }
                            out.push(next);
                        }
                        Some(Bind::Const {
                            ty: bound_ty,
                            residue: bound,
                            ..
                        }) if bound_ty == const_ty && bound == residue => {
                            out.push(binds.clone());
                        }
                        Some(_) => {}
                    }
                }
            }
            Pat::Int(int) => {
                if self.has_constant(class, ty, int.residue(width))? {
                    out.push(binds.clone());
                }
            }
            Pat::Bool(value) => {
                if self.has_constant(class, ScalarTy::Bool, u128::from(*value))? {
                    out.push(binds.clone());
                }
            }
            Pat::Op(op, pats) => {
                let desc = op.desc(ty);
                for enode in self.enodes(class) {
                    let TNode::Op(found, args) = self.node(*enode)? else {
                        continue;
                    };
                    if *found != desc || args.len() != pats.len() {
                        continue;
                    }
                    out.extend(self.match_args(rule, ty, width, pats, args, binds.clone())?);
                }
            }
            // `eval` never occurs in an lhs (the rule parser refuses it).
            Pat::Eval(..) => {}
        }
        Ok(out)
    }

    fn has_constant(&self, class: Tid, ty: ScalarTy, residue: u128) -> EngineResult<bool> {
        for enode in self.enodes(class) {
            if *self.node(*enode)? == TNode::Const(ty, residue) {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

fn graph_term(raw: usize) -> EngineResult<Tid> {
    match u32::try_from(raw) {
        Ok(raw) => Ok(crate::saturate::egraph::tid_from_raw(raw)),
        Err(_) => invariant("too many terms"),
    }
}

/// The residue a variable is bound to, when it is bound to a constant.
fn constant_of(binds: &Binds, var: usize) -> Option<u128> {
    match binds.get(var).copied().flatten() {
        Some(Bind::Const { residue, .. }) => Some(residue),
        _ => None,
    }
}

/// The class `pat[binds]` is in, when the graph already represents it.
fn class_of(
    graph: &mut Graph,
    widths: GraphWidths,
    ty: ScalarTy,
    pat: &Pat,
    binds: &Binds,
) -> EngineResult<Option<Tid>> {
    let width = match widths.width(ty) {
        Some(width) => width,
        None => return invariant("a match at a type that is not a graph type"),
    };
    Ok(match pat {
        Pat::Var(var) | Pat::ConstVar(var) => match binds.get(*var).copied().flatten() {
            Some(Bind::Class(class)) => Some(graph.find(class)),
            Some(Bind::Const { term, .. }) => Some(graph.find(term)),
            None => return invariant("a complete match left a variable unbound"),
        },
        Pat::Int(int) => graph
            .lookup(&TNode::Const(ty, int.residue(width)))
            .map(|term| graph.find(term)),
        Pat::Bool(value) => graph
            .lookup(&TNode::Const(ScalarTy::Bool, u128::from(*value)))
            .map(|term| graph.find(term)),
        Pat::Op(op, pats) => {
            let mut classes = Vec::with_capacity(pats.len());
            for sub in pats {
                match class_of(graph, widths, ty, sub, binds)? {
                    Some(class) => classes.push(class),
                    None => return Ok(None),
                }
            }
            graph
                .lookup_enode(op.desc(ty), &classes)
                .map(|term| graph.find(term))
        }
        Pat::Eval(op, vars) => {
            let (desc, value) = evaluate(widths, ty, *op, vars, binds)?;
            graph
                .lookup(&TNode::Const(desc.result_ty(), value))
                .map(|term| graph.find(term))
        }
    })
}

fn evaluate(
    widths: GraphWidths,
    ty: ScalarTy,
    op: crate::rules::RuleOp,
    vars: &[usize],
    binds: &Binds,
) -> EngineResult<(OpDesc, u128)> {
    crate::rules::eval_instance(widths, ty, op, vars, |var| constant_of(binds, var))
}

/// The concrete term `pat[binds]`, made when the graph does not hold it.
fn build(
    graph: &mut Graph,
    widths: GraphWidths,
    ty: ScalarTy,
    pat: &Pat,
    binds: &Binds,
) -> EngineResult<Tid> {
    let width = match widths.width(ty) {
        Some(width) => width,
        None => return invariant("a match at a type that is not a graph type"),
    };
    match pat {
        Pat::Var(var) | Pat::ConstVar(var) => match binds.get(*var).copied().flatten() {
            Some(Bind::Class(class)) => Ok(class),
            Some(Bind::Const { term, .. }) => Ok(term),
            None => invariant("a complete match left a variable unbound"),
        },
        Pat::Int(int) => graph.add(TNode::Const(ty, int.residue(width))),
        Pat::Bool(value) => graph.add(TNode::Const(ScalarTy::Bool, u128::from(*value))),
        Pat::Op(op, pats) => {
            let mut args = Vec::with_capacity(pats.len());
            for sub in pats {
                args.push(build(graph, widths, ty, sub, binds)?);
            }
            graph.add(TNode::Op(op.desc(ty), args))
        }
        Pat::Eval(op, vars) => {
            let (desc, value) = evaluate(widths, ty, *op, vars, binds)?;
            graph.add(TNode::Const(desc.result_ty(), value))
        }
    }
}

/// Apply one match: `true` when it merged two classes.
pub(crate) fn apply(
    graph: &mut Graph,
    widths: GraphWidths,
    rule: &Rule,
    found: &Match,
) -> EngineResult<bool> {
    let ty = found.ty;
    let lhs_class = class_of(graph, widths, ty, rule.lhs(), &found.binds)?;
    let rhs_class = class_of(graph, widths, ty, rule.rhs(), &found.binds)?;
    if lhs_class.is_some() && lhs_class == rhs_class {
        return Ok(false);
    }
    let lhs = build(graph, widths, ty, rule.lhs(), &found.binds)?;
    let rhs = build(graph, widths, ty, rule.rhs(), &found.binds)?;
    if graph.find(lhs) == graph.find(rhs) {
        return Ok(false);
    }
    let mut bindings: Vec<(&str, TermRef)> = Vec::with_capacity(rule.vars().len());
    for (index, var) in rule.vars().iter().enumerate() {
        let term = match found.binds.get(index).copied().flatten() {
            Some(Bind::Class(class)) => class,
            Some(Bind::Const { term, .. }) => term,
            None => return invariant("a complete match left a variable unbound"),
        };
        bindings.push((var.name.as_str(), graph.term_ref(term)?));
    }
    let Ok(side_conditions) = u32::try_from(rule.conds().len()) else {
        return invariant("too many side conditions");
    };
    let (lhs_ref, rhs_ref) = (graph.term_ref(lhs)?, graph.term_ref(rhs)?);
    let rule_ref = graph.prover.rule(rule.name(), rule.statement_digest());
    let step = graph.prover.rule_step(
        rule_ref,
        ty,
        &bindings,
        side_conditions,
        lhs_ref,
        rhs_ref,
        true,
    )?;
    graph.union_by_rule(lhs, rhs, step)
}
