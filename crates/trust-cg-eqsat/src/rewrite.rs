// crates/trust-cg-eqsat/src/rewrite.rs - node creation, hash-consing and eager rule firing
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The eager half of section 6: a node is hash-consed when it is created and
//! the rules fire on it then, never later.
//!
//! * A rule fires on a new operator node when its lhs root has the node's
//!   operator at a type of its domain (that is a graph type of the module).
//!   Rules fire in file order; matching descends into the argument Ids'
//!   trees (through `Union` and `Directed`), never into the whole class.
//! * Each match whose side conditions hold instantiates the rhs (creating
//!   nodes, which may fire rules up to `max_rewrite_depth`) and records a new
//!   `Union` (an `equiv` rule matched along `equiv` edges only) or a new
//!   `Directed` (a `refines` rule, or any match that passed a `Directed`
//!   edge: the relation established is then only a refinement). A match whose
//!   rhs is already in the node's tree records nothing.
//! * Every recorded edge carries its proof (section 7.1): congruence over the
//!   argument proofs, then the rule step, then the hash-cons explanation of
//!   the rhs. A match the engine cannot explain is an [`EngineError`], never
//!   a silent union.
//!
//! Budgets: `max_matches_per_node` complete lhs matches per node,
//! `max_rewrite_depth` levels of rhs-created nodes, and the arena bound
//! `max_ids_per_instruction * (input instructions + 1)`: once the arena
//! holds that many entries no rule fires (no new firing starts and a firing
//! in progress stops before its next match), while hash-consing continues.
//! All count events, never time. Each exhausted budget is counted in
//! `budget_hits`.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::ValueId;

use crate::EngineConfig;
use crate::derivation::{ProofRef, TermRef};
use crate::eval;
use crate::graph::{Entry, Graph, Hit, Id, Key, LeafPos, Node};
use crate::proof::{EngineResult, Prover, invariant};
use crate::rules::{Pat, Rule};
use crate::vocab::{GraphWidths, OpDesc, ScalarTy};

/// The value a rule variable is bound to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Binding {
    /// A term variable: an argument Id and its canonical term.
    Term { id: Id, term: TermRef },
    /// A constant variable: a constant member's value and term.
    Const {
        ty: ScalarTy,
        residue: u128,
        term: TermRef,
    },
}

impl Binding {
    const fn term(self) -> TermRef {
        match self {
            Binding::Term { term, .. } | Binding::Const { term, .. } => term,
        }
    }
}

type Binds = Vec<Option<Binding>>;

/// One way a pattern matched an Id: the bindings so far, the instantiated
/// pattern term and a proof `canon(id) -> term`.
#[derive(Debug, Clone)]
struct Matched {
    binds: Binds,
    term: TermRef,
    proof: ProofRef,
}

/// The result of creating (or finding) a node.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Made {
    /// The Id the value takes.
    pub(crate) id: Id,
    /// `requested term -> canon(id)`, where the requested term is the
    /// operator over the given arguments' canonical terms.
    pub(crate) proof: ProofRef,
    /// The node, when it was created now (not found by hash-consing).
    pub(crate) fresh: Option<Id>,
}

/// The e-graph with its rules, budgets and proof table.
pub(crate) struct Engine<'r> {
    pub(crate) graph: Graph,
    pub(crate) prover: Prover,
    rules: &'r [Rule],
    config: EngineConfig,
    /// Rules fire only while the arena holds fewer entries than this.
    id_limit: usize,
    pub(crate) widths: GraphWidths,
    pub(crate) rule_matches: BTreeMap<String, u64>,
    pub(crate) budget_hits: u64,
}

impl<'r> Engine<'r> {
    /// An engine for a function of `instructions` input instructions (the
    /// arena bound scales with it).
    pub(crate) fn new(
        function_name: &str,
        rules: &'r [Rule],
        config: EngineConfig,
        widths: GraphWidths,
        instructions: usize,
    ) -> Self {
        let per_instruction = usize::try_from(config.max_ids_per_instruction).unwrap_or(usize::MAX);
        Self {
            graph: Graph::default(),
            prover: Prover::new(function_name),
            rules,
            config,
            id_limit: per_instruction.saturating_mul(instructions.saturating_add(1)),
            widths,
            rule_matches: BTreeMap::new(),
            budget_hits: 0,
        }
    }

    fn width(&self, ty: ScalarTy) -> EngineResult<u32> {
        match self.widths.width(ty) {
            Some(width) => Ok(width),
            None => invariant("a type that is not a graph type in this module"),
        }
    }

    // ---- node creation -----------------------------------------------------

    /// The Id of a defined leaf (created once per position).
    pub(crate) fn leaf(&mut self, pos: LeafPos, ty: ScalarTy, value: ValueId) -> EngineResult<Id> {
        if let Some(id) = self.graph.leaf(pos) {
            return Ok(id);
        }
        let term = match pos {
            LeafPos::Result {
                block,
                ordinal,
                index,
            } => self.prover.result(block, ordinal, index),
        };
        let id = self
            .graph
            .push(Entry::Node(Node::Leaf { pos, ty, value }), term)?;
        self.graph.set_leaf(pos, id);
        Ok(id)
    }

    /// The Id of `Const(ty, residue)` (hash-consed in the current scope).
    pub(crate) fn constant(&mut self, ty: ScalarTy, residue: u128) -> EngineResult<Made> {
        let term = self.prover.constant(ty, residue);
        let proof = self.prover.refl(term)?;
        let key = Key::Const(ty, residue);
        if let Some(hit) = self.graph.lookup(&key) {
            return Ok(Made {
                id: hit.current,
                proof,
                fresh: None,
            });
        }
        let id = self
            .graph
            .push(Entry::Node(Node::Const { ty, residue }), term)?;
        self.graph.insert(
            key,
            Hit {
                node: id,
                current: id,
            },
        );
        Ok(Made {
            id,
            proof,
            fresh: Some(id),
        })
    }

    /// The Id of `desc(args)`: a hash-cons hit (with the proof that the
    /// requested term equals the hit's canonical term), or a new node on
    /// which the rules fire when `depth` is within the budget.
    pub(crate) fn operator(&mut self, desc: OpDesc, args: &[Id], depth: u32) -> EngineResult<Made> {
        if args.len() != desc.arity() || !desc.admitted() {
            return invariant("an operator node with the wrong arity or types");
        }
        let mut canon_args = Vec::with_capacity(args.len());
        let mut reps = Vec::with_capacity(args.len());
        for arg in args {
            canon_args.push(self.graph.canon(*arg)?);
            reps.push(self.graph.find(*arg));
        }
        let requested = self.prover.op(desc, &canon_args);
        let key = Key::Op(desc, reps);
        if let Some(hit) = self.graph.lookup(&key) {
            let Entry::Node(Node::Op {
                args: hit_args,
                desc: hit_desc,
            }) = self.graph.entry(hit.node)?.clone()
            else {
                return invariant("a hash-cons entry that is not an operator node");
            };
            if hit_desc != desc || hit_args.len() != args.len() {
                return invariant("a hash-cons entry with another operator");
            }
            let mut proofs = Vec::with_capacity(args.len());
            for (mine, theirs) in args.iter().zip(&hit_args) {
                proofs.push(self.graph.explain(&mut self.prover, *mine, *theirs)?);
            }
            let proof = self.prover.congr(desc, &proofs)?;
            return Ok(Made {
                id: hit.current,
                proof,
                fresh: None,
            });
        }
        let node = self.graph.push(
            Entry::Node(Node::Op {
                desc,
                args: args.to_vec(),
            }),
            requested,
        )?;
        self.graph.insert(
            key.clone(),
            Hit {
                node,
                current: node,
            },
        );
        let current = if depth <= self.config.max_rewrite_depth && self.has_room() {
            self.fire(node, desc, args, depth)?
        } else {
            if self.has_rule_for(desc) {
                self.budget_hits += 1;
            }
            node
        };
        if current != node {
            self.graph.insert(key, Hit { node, current });
        }
        let proof = self.prover.refl(requested)?;
        Ok(Made {
            id: current,
            proof,
            fresh: Some(node),
        })
    }

    /// Whether the arena is below its bound (rules may fire).
    fn has_room(&self) -> bool {
        self.graph.len() < self.id_limit
    }

    fn has_rule_for(&self, desc: OpDesc) -> bool {
        self.rules
            .iter()
            .any(|rule| !rule.instance_types(desc, self.widths).is_empty())
    }

    // ---- rule firing -------------------------------------------------------

    /// Fire every rule on the new node `node` (`desc(args)`), returning the Id
    /// that holds every form found.
    fn fire(&mut self, node: Id, desc: OpDesc, args: &[Id], depth: u32) -> EngineResult<Id> {
        let rules = self.rules;
        let mut current = node;
        let mut in_tree: BTreeSet<Id> = BTreeSet::new();
        in_tree.insert(node);
        let mut budget = self.config.max_matches_per_node;
        'rules: for rule in rules {
            for ty in rule.instance_types(desc, self.widths) {
                let cap = usize::try_from(budget)
                    .unwrap_or(usize::MAX)
                    .saturating_add(1);
                let matches = self.match_root(rule, ty, desc, args, cap)?;
                for found in matches {
                    if budget == 0 || !self.has_room() {
                        self.budget_hits += 1;
                        break 'rules;
                    }
                    budget -= 1;
                    if !self.side_conditions_hold(rule, ty, &found.binds)? {
                        continue;
                    }
                    let Some(next) = self.apply(rule, ty, &found, current, &in_tree, depth)? else {
                        continue;
                    };
                    for id in self.graph.tree_ids(next)? {
                        in_tree.insert(id);
                    }
                    current = next;
                    *self.rule_matches.entry(rule.name().to_owned()).or_insert(0) += 1;
                }
            }
        }
        Ok(current)
    }

    fn side_conditions_hold(&self, rule: &Rule, ty: ScalarTy, binds: &Binds) -> EngineResult<bool> {
        let width = self.width(ty)?;
        for cond in rule.conds() {
            match binds.get(cond.var()).copied().flatten() {
                Some(Binding::Const { residue, .. }) => {
                    if !cond.holds(residue, width) {
                        return Ok(false);
                    }
                }
                // A condition on an unbound or non-constant variable never
                // holds (fail-closed; the rule parser already refuses it).
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Build the rhs of one match and record the edge from `current`.
    /// `None` when the rhs is already in `current`'s tree.
    fn apply(
        &mut self,
        rule: &Rule,
        ty: ScalarTy,
        found: &Matched,
        current: Id,
        in_tree: &BTreeSet<Id>,
        depth: u32,
    ) -> EngineResult<Option<Id>> {
        let mut bindings: Vec<(&str, TermRef)> = Vec::with_capacity(rule.vars().len());
        for (index, var) in rule.vars().iter().enumerate() {
            match found.binds.get(index).copied().flatten() {
                Some(binding) => bindings.push((var.name.as_str(), binding.term())),
                None => return invariant("a complete match left a variable unbound"),
            }
        }
        let (rhs_id, rhs_term, rhs_proof) =
            self.instantiate(ty, rule.rhs(), &found.binds, depth)?;
        if in_tree.contains(&rhs_id) {
            return Ok(None);
        }
        let Ok(side_conditions) = u32::try_from(rule.conds().len()) else {
            return invariant("too many side conditions");
        };
        let rule_ref = self.prover.rule(rule.name(), rule.statement_digest());
        let step = self.prover.rule_step(
            rule_ref,
            ty,
            &bindings,
            side_conditions,
            found.term,
            rhs_term,
            rule.is_equiv(),
        )?;
        let lhs_to_rule = self.prover.trans(found.proof, step)?;
        let just = self.prover.trans(lhs_to_rule, rhs_proof)?;
        let conclusion = self.prover.conclusion(just)?;
        if conclusion.lhs != self.graph.canon(current)?
            || conclusion.rhs != self.graph.canon(rhs_id)?
        {
            return invariant("a union justification that does not relate its endpoints");
        }
        let canon = self.graph.canon(current)?;
        let next = if conclusion.equiv {
            let next = self.graph.push(
                Entry::Union {
                    a: current,
                    b: rhs_id,
                    just,
                },
                canon,
            )?;
            let same = self.prover.refl(canon)?;
            self.graph.merge(next, current, same)?;
            self.graph.merge(current, rhs_id, just)?;
            next
        } else {
            let next = self.graph.push(
                Entry::Directed {
                    a: current,
                    b: rhs_id,
                    just,
                },
                canon,
            )?;
            let same = self.prover.refl(canon)?;
            self.graph.merge(next, current, same)?;
            next
        };
        Ok(Some(next))
    }

    // ---- matching ----------------------------------------------------------

    fn match_root(
        &mut self,
        rule: &Rule,
        ty: ScalarTy,
        desc: OpDesc,
        args: &[Id],
        cap: usize,
    ) -> EngineResult<Vec<Matched>> {
        let Pat::Op(root, pats) = rule.lhs() else {
            return Ok(Vec::new());
        };
        if root.desc(ty) != desc || pats.len() != args.len() {
            return Ok(Vec::new());
        }
        let empty: Binds = vec![None; rule.vars().len()];
        let mut out = Vec::new();
        for (binds, terms, proofs) in self.match_args(rule, ty, pats, args, &empty, cap)? {
            let term = self.prover.op(desc, &terms);
            let proof = self.prover.congr(desc, &proofs)?;
            out.push(Matched { binds, term, proof });
        }
        Ok(out)
    }

    #[allow(clippy::type_complexity)]
    fn match_args(
        &mut self,
        rule: &Rule,
        ty: ScalarTy,
        pats: &[Pat],
        ids: &[Id],
        binds: &Binds,
        cap: usize,
    ) -> EngineResult<Vec<(Binds, Vec<TermRef>, Vec<ProofRef>)>> {
        let mut acc: Vec<(Binds, Vec<TermRef>, Vec<ProofRef>)> =
            vec![(binds.clone(), Vec::new(), Vec::new())];
        for (pat, id) in pats.iter().zip(ids) {
            let mut next = Vec::new();
            'partial: for (partial, terms, proofs) in &acc {
                for found in self.match_pat(rule, ty, pat, *id, partial, cap)? {
                    let mut terms = terms.clone();
                    terms.push(found.term);
                    let mut proofs = proofs.clone();
                    proofs.push(found.proof);
                    next.push((found.binds, terms, proofs));
                    if next.len() >= cap {
                        break 'partial;
                    }
                }
            }
            acc = next;
            if acc.is_empty() {
                break;
            }
        }
        Ok(acc)
    }

    fn match_pat(
        &mut self,
        rule: &Rule,
        ty: ScalarTy,
        pat: &Pat,
        id: Id,
        binds: &Binds,
        cap: usize,
    ) -> EngineResult<Vec<Matched>> {
        let mut out = Vec::new();
        match pat {
            Pat::Var(var) => match binds.get(*var).copied().flatten() {
                None => {
                    let term = self.graph.canon(id)?;
                    let proof = self.prover.refl(term)?;
                    let mut binds = binds.clone();
                    if let Some(slot) = binds.get_mut(*var) {
                        *slot = Some(Binding::Term { id, term });
                    }
                    out.push(Matched { binds, term, proof });
                }
                Some(Binding::Term { id: bound, term }) => {
                    if bound == id || self.graph.find(bound) == self.graph.find(id) {
                        let proof = self.graph.explain(&mut self.prover, id, bound)?;
                        out.push(Matched {
                            binds: binds.clone(),
                            term,
                            proof,
                        });
                    }
                }
                Some(Binding::Const { .. }) => {}
            },
            Pat::ConstVar(var) => {
                let Some(info) = rule.vars().get(*var) else {
                    return invariant("a pattern names an unknown variable");
                };
                let position_ty = info.sort.at(ty);
                let mut residues = BTreeSet::new();
                let walk = self.graph.members(id)?;
                for k in 0..walk.len() {
                    let member = walk.member(k)?;
                    let Entry::Node(Node::Const {
                        ty: member_ty,
                        residue,
                    }) = *self.graph.entry(member)?
                    else {
                        continue;
                    };
                    if member_ty != position_ty || !residues.insert(residue) {
                        continue;
                    }
                    let term = self.graph.canon(member)?;
                    let next = match binds.get(*var).copied().flatten() {
                        None => {
                            let mut next = binds.clone();
                            if let Some(slot) = next.get_mut(*var) {
                                *slot = Some(Binding::Const {
                                    ty: member_ty,
                                    residue,
                                    term,
                                });
                            }
                            next
                        }
                        Some(Binding::Const {
                            ty: bound_ty,
                            residue: bound,
                            ..
                        }) if bound_ty == member_ty && bound == residue => binds.clone(),
                        Some(_) => continue,
                    };
                    let proof = walk.proof(k, &self.graph, &mut self.prover)?;
                    out.push(Matched {
                        binds: next,
                        term,
                        proof,
                    });
                    if out.len() >= cap {
                        break;
                    }
                }
            }
            Pat::Int(int) => {
                let residue = int.residue(self.width(ty)?);
                if let Some(found) = self.match_constant(id, ty, residue, binds)? {
                    out.push(found);
                }
            }
            Pat::Bool(value) => {
                if let Some(found) =
                    self.match_constant(id, ScalarTy::Bool, u128::from(*value), binds)?
                {
                    out.push(found);
                }
            }
            Pat::Op(op, pats) => {
                let desc = op.desc(ty);
                let walk = self.graph.members(id)?;
                for k in 0..walk.len() {
                    let member = walk.member(k)?;
                    let Entry::Node(Node::Op {
                        desc: member_desc,
                        args,
                    }) = self.graph.entry(member)?.clone()
                    else {
                        continue;
                    };
                    if member_desc != desc || args.len() != pats.len() {
                        continue;
                    }
                    let found = self.match_args(rule, ty, pats, &args, binds, cap)?;
                    if found.is_empty() {
                        continue;
                    }
                    let to_member = walk.proof(k, &self.graph, &mut self.prover)?;
                    for (next, terms, proofs) in found {
                        let term = self.prover.op(desc, &terms);
                        let inner = self.prover.congr(desc, &proofs)?;
                        let proof = self.prover.trans(to_member, inner)?;
                        out.push(Matched {
                            binds: next,
                            term,
                            proof,
                        });
                        if out.len() >= cap {
                            break;
                        }
                    }
                    if out.len() >= cap {
                        break;
                    }
                }
            }
            // `eval` never occurs in an lhs (the parser refuses it).
            Pat::Eval(..) => {}
        }
        Ok(out)
    }

    /// The first constant member `Const(ty, residue)` of `id`'s tree.
    fn match_constant(
        &mut self,
        id: Id,
        ty: ScalarTy,
        residue: u128,
        binds: &Binds,
    ) -> EngineResult<Option<Matched>> {
        let walk = self.graph.members(id)?;
        for k in 0..walk.len() {
            let member = walk.member(k)?;
            if let Entry::Node(Node::Const {
                ty: member_ty,
                residue: member_residue,
            }) = *self.graph.entry(member)?
                && member_ty == ty
                && member_residue == residue
            {
                let term = self.graph.canon(member)?;
                let proof = walk.proof(k, &self.graph, &mut self.prover)?;
                return Ok(Some(Matched {
                    binds: binds.clone(),
                    term,
                    proof,
                }));
            }
        }
        Ok(None)
    }

    // ---- rhs instantiation -------------------------------------------------

    /// Substitute `binds` into `pat` at `ty`: the Id, the instantiated term
    /// (`rhs[sigma]` piece) and a proof `term -> canon(id)`.
    fn instantiate(
        &mut self,
        ty: ScalarTy,
        pat: &Pat,
        binds: &Binds,
        depth: u32,
    ) -> EngineResult<(Id, TermRef, ProofRef)> {
        match pat {
            Pat::Var(var) | Pat::ConstVar(var) => match binds.get(*var).copied().flatten() {
                Some(Binding::Term { id, term }) if matches!(pat, Pat::Var(_)) => {
                    let proof = self.prover.refl(term)?;
                    Ok((id, term, proof))
                }
                Some(Binding::Const { ty, residue, term }) => {
                    let made = self.constant(ty, residue)?;
                    Ok((made.id, term, made.proof))
                }
                _ => invariant("an rhs variable without a fitting binding"),
            },
            Pat::Int(int) => {
                let residue = int.residue(self.width(ty)?);
                let made = self.constant(ty, residue)?;
                let term = self.graph.canon(made.id)?;
                Ok((made.id, term, made.proof))
            }
            Pat::Bool(value) => {
                let made = self.constant(ScalarTy::Bool, u128::from(*value))?;
                let term = self.graph.canon(made.id)?;
                Ok((made.id, term, made.proof))
            }
            Pat::Op(op, pats) => {
                let desc = op.desc(ty);
                let mut ids = Vec::with_capacity(pats.len());
                let mut terms = Vec::with_capacity(pats.len());
                let mut proofs = Vec::with_capacity(pats.len());
                for sub in pats {
                    let (id, term, proof) = self.instantiate(ty, sub, binds, depth)?;
                    ids.push(id);
                    terms.push(term);
                    proofs.push(proof);
                }
                let term = self.prover.op(desc, &terms);
                let to_canon_args = self.prover.congr(desc, &proofs)?;
                let made = self.operator(desc, &ids, depth.saturating_add(1))?;
                let proof = self.prover.trans(to_canon_args, made.proof)?;
                Ok((made.id, term, proof))
            }
            Pat::Eval(op, vars) => {
                let desc = op.desc(ty);
                let mut residues = Vec::with_capacity(vars.len());
                for var in vars {
                    match binds.get(*var).copied().flatten() {
                        Some(Binding::Const { residue, .. }) => residues.push(residue),
                        _ => return invariant("an eval argument without a constant binding"),
                    }
                }
                let Some(value) = eval::op(self.widths, desc, &residues) else {
                    return invariant("eval of an operator outside its domain");
                };
                let made = self.constant(desc.result_ty(), value)?;
                let term = self.graph.canon(made.id)?;
                Ok((made.id, term, made.proof))
            }
        }
    }
}
