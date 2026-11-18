// crates/trust-cg-eqsat/src/saturate/extract.rs - sharing-aware extraction for Tier S regions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Extraction (`docs/eqsat-tier-s.md` section 5).
//!
//! Every class has **options**: one per e-node, and for the result of an
//! order-free node "keep it" plus one option per order of its family
//! ("implement it by the reduction pinned at that order"). A **choice** is
//! one option per class; the form it denotes takes, for every class the
//! roots reach, that class's option.
//!
//! A form's cost is the sum of its options' costs with every class counted
//! **once**, however many uses it has. The per-class tree-cost dynamic
//! program (each class takes the option whose own cost plus its children's
//! tree costs is least) ignores that sharing, so it is only the starting
//! point. [`Table::choose`] improves it in two steps under one budget of
//! trials:
//!
//! 1. it changes one class's option at a time while that lowers the cost of
//!    the whole form;
//! 2. it searches every choice by branch and bound, classes taken in the
//!    order the roots demand them, a branch cut when the cost of what is
//!    chosen plus the least own cost of every class still demanded is not
//!    below the best form found. A form that needs several classes to
//!    change together (two roots that can share a subterm neither has) is
//!    found here.
//!
//! When the second step ends before the budget does, no choice is cheaper
//! than the one returned. This is not the tree-decomposition extractor the
//! design names; it is exact on small regions and budget-cut on large ones.
//! The caller compares the result with the input region and keeps the input
//! unless the result is strictly cheaper.
//!
//! No walk here recurses on the depth of a region: each keeps its own stack.

use std::collections::{BTreeMap, BTreeSet};

use crate::derivation::{ProofRef, TermRef};
use crate::proof::{EngineResult, invariant};
use crate::saturate::FreeNode;
use crate::saturate::egraph::{Graph, TNode, Tid};
use crate::saturate::region::{NodeId, Region};
use crate::vocab::{CONST_COST, REDUCTION_COST};

/// One way to compute a class.
#[derive(Debug, Clone)]
pub(crate) enum Kind {
    /// The e-node of this term: a plain leaf, a constant or an operator.
    Term(Tid),
    /// The result of order-free node `entry`, kept.
    Keep { entry: usize },
    /// The result of order-free node `entry`, implemented by the reduction
    /// pinned at `order`, whose term is `pinned`.
    Implement {
        entry: usize,
        order: u32,
        pinned: Tid,
    },
}

#[derive(Debug, Clone)]
pub(crate) struct Choice {
    pub(crate) kind: Kind,
    cost: u64,
    /// The classes this option reads.
    children: Vec<Tid>,
}

/// Every class's options, by class representative.
pub(crate) struct Table {
    options: BTreeMap<Tid, Vec<Choice>>,
}

/// The result of [`Table::choose`].
pub(crate) struct Chosen {
    /// The option index of every class.
    pub(crate) choice: BTreeMap<Tid, usize>,
    pub(crate) tree_choice_cost: u64,
    pub(crate) trials: u64,
    /// Whether the branch-and-bound search ended before its budget did.
    pub(crate) search_complete: bool,
}

/// One class of the branch-and-bound search with the option it has taken.
struct Frame {
    class: Tid,
    /// The class's options that can be completed, cheapest tree cost first.
    order: Vec<usize>,
    /// The next entry of `order` to try.
    next: usize,
    /// The own cost of the option taken and the classes it newly demanded.
    applied: Option<(u64, usize)>,
}

impl Table {
    pub(crate) fn build(graph: &mut Graph, free: &[FreeNode]) -> EngineResult<Self> {
        let mut options: BTreeMap<Tid, Vec<Choice>> = BTreeMap::new();
        for class in graph.classes()? {
            let mut list = Vec::with_capacity(class.enodes.len());
            for enode in class.enodes {
                match graph.node(enode)?.clone() {
                    TNode::Leaf(_) => {
                        let entry = free.iter().position(|node| node.leaf == enode);
                        match entry.and_then(|index| free.get(index).map(|node| (index, node))) {
                            None => list.push(Choice {
                                kind: Kind::Term(enode),
                                cost: 0,
                                children: Vec::new(),
                            }),
                            Some((index, node)) => {
                                list.push(Choice {
                                    kind: Kind::Keep { entry: index },
                                    cost: REDUCTION_COST,
                                    children: vec![graph.find(node.operand)],
                                });
                                for (order, pinned) in &node.pinned {
                                    list.push(Choice {
                                        kind: Kind::Implement {
                                            entry: index,
                                            order: *order,
                                            pinned: *pinned,
                                        },
                                        cost: 0,
                                        children: vec![graph.find(*pinned)],
                                    });
                                }
                            }
                        }
                    }
                    TNode::Const(..) => list.push(Choice {
                        kind: Kind::Term(enode),
                        cost: CONST_COST,
                        children: Vec::new(),
                    }),
                    TNode::Op(desc, args) => list.push(Choice {
                        kind: Kind::Term(enode),
                        cost: desc.cost(),
                        children: args.iter().map(|arg| graph.find(*arg)).collect(),
                    }),
                }
            }
            options.insert(class.root, list);
        }
        Ok(Self { options })
    }

    pub(crate) fn option(&self, class: Tid, index: usize) -> EngineResult<&Choice> {
        match self.options.get(&class).and_then(|list| list.get(index)) {
            Some(choice) => Ok(choice),
            None => invariant("a class without the chosen option"),
        }
    }

    /// The number of distinct terms `class` represents (an order-free
    /// result counts as itself), or `None` when the class reaches itself or
    /// the count does not fit.
    pub(crate) fn forms(&self, class: Tid) -> Option<u128> {
        let mut done: BTreeMap<Tid, u128> = BTreeMap::new();
        let mut open: BTreeSet<Tid> = BTreeSet::new();
        let mut stack: Vec<(Tid, bool)> = vec![(class, false)];
        while let Some((class, leaving)) = stack.pop() {
            if done.contains_key(&class) {
                continue;
            }
            let list = self.options.get(&class)?;
            if leaving {
                let mut total = 0u128;
                for choice in list {
                    let product = match choice.kind {
                        Kind::Term(_) => {
                            let mut product = 1u128;
                            for child in &choice.children {
                                product = product.checked_mul(*done.get(child)?)?;
                            }
                            product
                        }
                        Kind::Keep { .. } => 1,
                        // An implementation is not a term of this class.
                        Kind::Implement { .. } => 0,
                    };
                    total = total.checked_add(product)?;
                }
                open.remove(&class);
                done.insert(class, total);
                continue;
            }
            if !open.insert(class) {
                return None;
            }
            stack.push((class, true));
            for choice in list {
                if matches!(choice.kind, Kind::Term(_)) {
                    for child in &choice.children {
                        if open.contains(child) {
                            return None;
                        }
                        if !done.contains_key(child) {
                            stack.push((*child, false));
                        }
                    }
                }
            }
        }
        done.get(&class).copied()
    }

    /// The per-class tree cost and the option that gives it: the least
    /// fixpoint of "own cost plus the children's tree costs", ties to the
    /// first option. A class without an entry has no finite form.
    fn tree_costs(&self) -> BTreeMap<Tid, (u64, usize)> {
        let mut best: BTreeMap<Tid, (u64, usize)> = BTreeMap::new();
        loop {
            let mut changed = false;
            for (class, list) in &self.options {
                for (index, choice) in list.iter().enumerate() {
                    let Some(cost) = Self::tree_cost_of(choice, &best) else {
                        continue;
                    };
                    if best.get(class).is_none_or(|(current, _)| cost < *current) {
                        best.insert(*class, (cost, index));
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        best
    }

    /// The tree cost of one option, when every class it reads has one.
    fn tree_cost_of(choice: &Choice, tree: &BTreeMap<Tid, (u64, usize)>) -> Option<u64> {
        let mut cost = choice.cost;
        for child in &choice.children {
            cost = cost.saturating_add(tree.get(child)?.0);
        }
        Some(cost)
    }

    /// The cost of the form `choice` gives the roots, every reached class
    /// counted once, with the classes reached; `None` when a reached class
    /// has no option or reaches itself.
    fn price(&self, choice: &BTreeMap<Tid, usize>, roots: &[Tid]) -> Option<(u64, BTreeSet<Tid>)> {
        let mut done: BTreeSet<Tid> = BTreeSet::new();
        let mut open: BTreeSet<Tid> = BTreeSet::new();
        let mut total = 0u64;
        let mut stack: Vec<(Tid, bool)> = roots.iter().rev().map(|root| (*root, false)).collect();
        while let Some((class, leaving)) = stack.pop() {
            if leaving {
                open.remove(&class);
                done.insert(class);
                continue;
            }
            if done.contains(&class) {
                continue;
            }
            if !open.insert(class) {
                return None;
            }
            let picked = self.options.get(&class)?.get(*choice.get(&class)?)?;
            total = total.saturating_add(picked.cost);
            stack.push((class, true));
            for child in picked.children.iter().rev() {
                if open.contains(child) {
                    return None;
                }
                stack.push((*child, false));
            }
        }
        Some((total, done))
    }

    /// Whether giving `class` an option that reads `children` closes a
    /// cycle through the classes already `assigned`.
    fn closes_cycle(&self, assigned: &BTreeMap<Tid, usize>, class: Tid, children: &[Tid]) -> bool {
        let mut seen: BTreeSet<Tid> = BTreeSet::new();
        let mut stack: Vec<Tid> = children.to_vec();
        while let Some(next) = stack.pop() {
            if next == class {
                return true;
            }
            if !seen.insert(next) {
                continue;
            }
            let read = assigned
                .get(&next)
                .and_then(|index| self.options.get(&next)?.get(*index));
            if let Some(option) = read {
                stack.extend(option.children.iter().copied());
            }
        }
        false
    }

    /// The least own cost of a class's options (what any form that demands
    /// the class pays for it at least).
    fn least_own_cost(&self, class: Tid) -> u64 {
        self.options
            .get(&class)
            .and_then(|list| list.iter().map(|choice| choice.cost).min())
            .unwrap_or(0)
    }

    /// Branch and bound over one option per demanded class (module docs,
    /// step 2). Returns the cheapest choice whose cost is below `incumbent`
    /// when there is one, the trials spent, and whether every choice was
    /// examined or cut by its bound before `max_trials` were spent.
    fn search(
        &self,
        roots: &[Tid],
        tree: &BTreeMap<Tid, (u64, usize)>,
        incumbent: u64,
        max_trials: u64,
    ) -> (Option<BTreeMap<Tid, usize>>, u64, bool) {
        let mut best = incumbent;
        let mut found: Option<BTreeMap<Tid, usize>> = None;
        let mut trials = 0u64;
        // `demanded` holds every class in `assigned`, in `pending` or in a
        // frame; `pending` holds the demanded classes without a frame.
        let mut assigned: BTreeMap<Tid, usize> = BTreeMap::new();
        let mut demanded: BTreeSet<Tid> = BTreeSet::new();
        let mut pending: Vec<Tid> = Vec::new();
        let mut pending_bound = 0u64;
        let mut cost = 0u64;
        for root in roots.iter().rev() {
            if demanded.insert(*root) {
                pending.push(*root);
                pending_bound = pending_bound.saturating_add(self.least_own_cost(*root));
            }
        }
        let mut frames: Vec<Frame> = Vec::new();
        loop {
            match pending.pop() {
                // Every demanded class has an option: a whole form.
                None => {
                    if cost < best {
                        best = cost;
                        found = Some(assigned.clone());
                    }
                }
                Some(class) => {
                    pending_bound = pending_bound.saturating_sub(self.least_own_cost(class));
                    let list = self.options.get(&class).map_or(&[][..], Vec::as_slice);
                    let mut order: Vec<(u64, usize)> = list
                        .iter()
                        .enumerate()
                        .filter_map(|(index, choice)| {
                            Self::tree_cost_of(choice, tree).map(|cost| (cost, index))
                        })
                        .collect();
                    order.sort_unstable();
                    frames.push(Frame {
                        class,
                        order: order.into_iter().map(|(_, index)| index).collect(),
                        next: 0,
                        applied: None,
                    });
                }
            }
            // Give the newest frame its next option; a frame without one
            // hands its class back and the frame below it moves on.
            loop {
                let Some(frame) = frames.last_mut() else {
                    return (found, trials, true);
                };
                if let Some((own, pushed)) = frame.applied.take() {
                    assigned.remove(&frame.class);
                    cost = cost.saturating_sub(own);
                    for _ in 0..pushed {
                        if let Some(child) = pending.pop() {
                            demanded.remove(&child);
                            pending_bound =
                                pending_bound.saturating_sub(self.least_own_cost(child));
                        }
                    }
                }
                let mut taken = false;
                while let Some(index) = frame.order.get(frame.next).copied() {
                    if trials >= max_trials {
                        return (found, trials, false);
                    }
                    trials += 1;
                    frame.next += 1;
                    let Some(option) = self
                        .options
                        .get(&frame.class)
                        .and_then(|list| list.get(index))
                    else {
                        continue;
                    };
                    let mut fresh: Vec<Tid> = Vec::new();
                    for child in &option.children {
                        if !demanded.contains(child) && !fresh.contains(child) {
                            fresh.push(*child);
                        }
                    }
                    let fresh_bound = fresh.iter().fold(0u64, |sum, child| {
                        sum.saturating_add(self.least_own_cost(*child))
                    });
                    let bound = cost
                        .saturating_add(option.cost)
                        .saturating_add(pending_bound)
                        .saturating_add(fresh_bound);
                    if bound >= best || self.closes_cycle(&assigned, frame.class, &option.children)
                    {
                        continue;
                    }
                    assigned.insert(frame.class, index);
                    cost = cost.saturating_add(option.cost);
                    pending_bound = pending_bound.saturating_add(fresh_bound);
                    for child in fresh.iter().rev() {
                        demanded.insert(*child);
                        pending.push(*child);
                    }
                    frame.applied = Some((option.cost, fresh.len()));
                    taken = true;
                    break;
                }
                if taken {
                    break;
                }
                let class = frame.class;
                frames.pop();
                pending.push(class);
                pending_bound = pending_bound.saturating_add(self.least_own_cost(class));
            }
        }
    }

    /// The tree-cost choice improved by single-class changes and then by
    /// the branch-and-bound search (module docs). `None` when the tree-cost
    /// choice gives the roots no form.
    pub(crate) fn choose(&self, roots: &[Tid], max_trials: u64) -> Option<Chosen> {
        let tree = self.tree_costs();
        let mut choice: BTreeMap<Tid, usize> = tree
            .iter()
            .map(|(class, (_, index))| (*class, *index))
            .collect();
        let (tree_choice_cost, _) = self.price(&choice, roots)?;
        let mut best = tree_choice_cost;
        let mut trials = 0u64;
        'climb: loop {
            let mut improved = false;
            let (_, reached) = self.price(&choice, roots)?;
            for class in reached {
                let Some(current) = choice.get(&class).copied() else {
                    continue;
                };
                let count = self.options.get(&class).map_or(0, Vec::len);
                let mut kept = current;
                for alternative in 0..count {
                    if alternative == kept {
                        continue;
                    }
                    if trials >= max_trials {
                        choice.insert(class, kept);
                        break 'climb;
                    }
                    trials += 1;
                    choice.insert(class, alternative);
                    match self.price(&choice, roots) {
                        Some((cost, _)) if cost < best => {
                            best = cost;
                            kept = alternative;
                            improved = true;
                        }
                        _ => {}
                    }
                    choice.insert(class, kept);
                }
            }
            if !improved {
                break;
            }
        }
        let (found, spent, search_complete) =
            self.search(roots, &tree, best, max_trials.saturating_sub(trials));
        if let Some(better) = found {
            choice.extend(better);
        }
        Some(Chosen {
            choice,
            tree_choice_cost,
            trials: trials.saturating_add(spent),
            search_complete,
        })
    }
}

/// What a class is emitted as: the output node, its term, the term the
/// proof starts at (the chosen e-node's own term, or the order-free leaf)
/// and a proof `start -> term`.
#[derive(Debug, Clone, Copy)]
struct Out {
    node: NodeId,
    term: TermRef,
    start: Tid,
    proof: ProofRef,
}

/// The output region of a choice with the claims that justify it.
pub(crate) struct Emitted {
    pub(crate) region: Region,
    pub(crate) claims: Vec<ProofRef>,
    /// The order-free entries the form implements, each with its order.
    pub(crate) implemented: BTreeMap<usize, u32>,
}

struct Emitter<'a> {
    graph: &'a mut Graph,
    free: &'a [FreeNode],
    table: &'a Table,
    choice: &'a BTreeMap<Tid, usize>,
    region: Region,
    done: BTreeMap<Tid, Out>,
    /// Order-free entries whose result the output keeps.
    kept: BTreeSet<usize>,
    /// Order-free entries the output implements, with the order.
    implemented: BTreeMap<usize, u32>,
}

impl Emitter<'_> {
    fn chosen(&self, class: Tid) -> EngineResult<Kind> {
        let Some(index) = self.choice.get(&class).copied() else {
            return invariant("a reached class without a choice");
        };
        Ok(self.table.option(class, index)?.kind.clone())
    }

    /// The classes whose emission the chosen option of `class` reads.
    fn reads(&mut self, class: Tid) -> EngineResult<Vec<Tid>> {
        Ok(match self.chosen(class)? {
            Kind::Term(term) => match self.graph.node(term)?.clone() {
                TNode::Op(_, args) => args.iter().map(|arg| self.graph.find(*arg)).collect(),
                TNode::Leaf(_) | TNode::Const(..) => Vec::new(),
            },
            // A kept node's operand is emitted by `emit`, after the roots.
            Kind::Keep { .. } => Vec::new(),
            Kind::Implement { pinned, .. } => vec![self.graph.find(pinned)],
        })
    }

    /// Emit `class` and every class its form reads, children first, on a
    /// stack of this walk's own.
    fn ensure(&mut self, class: Tid) -> EngineResult<()> {
        let mut open: BTreeSet<Tid> = BTreeSet::new();
        let mut stack: Vec<(Tid, bool)> = vec![(class, false)];
        while let Some((class, leaving)) = stack.pop() {
            if self.done.contains_key(&class) {
                continue;
            }
            if leaving {
                open.remove(&class);
                let out = self.class(class)?;
                self.done.insert(class, out);
                continue;
            }
            if !open.insert(class) {
                return invariant("a chosen form that reads itself");
            }
            stack.push((class, true));
            for read in self.reads(class)?.into_iter().rev() {
                if open.contains(&read) {
                    return invariant("a chosen form that reads itself");
                }
                if !self.done.contains_key(&read) {
                    stack.push((read, false));
                }
            }
        }
        Ok(())
    }

    /// A proof `term -> (what term's class is emitted as)`.
    fn step_into(&mut self, term: Tid) -> EngineResult<(Out, ProofRef)> {
        let class = self.graph.find(term);
        self.ensure(class)?;
        self.step(term)
    }

    /// [`Emitter::step_into`] for a term whose class is already emitted.
    fn step(&mut self, term: Tid) -> EngineResult<(Out, ProofRef)> {
        let class = self.graph.find(term);
        let Some(out) = self.done.get(&class).copied() else {
            return invariant("a class read before it is emitted");
        };
        let to_start = self.graph.explain(term, out.start)?;
        let proof = self.graph.prover.trans(to_start, out.proof)?;
        Ok((out, proof))
    }

    /// What `class` is emitted as. Every class its option reads is emitted.
    fn class(&mut self, class: Tid) -> EngineResult<Out> {
        Ok(match self.chosen(class)? {
            Kind::Term(term) => self.term(term)?,
            Kind::Keep { entry } => {
                let Some(leaf) = self.free.get(entry).map(|node| node.leaf) else {
                    return invariant("an option of an order-free node that does not exist");
                };
                self.kept.insert(entry);
                self.term(leaf)?
            }
            Kind::Implement {
                entry,
                order,
                pinned,
            } => {
                let Some(leaf) = self.free.get(entry).map(|node| node.leaf) else {
                    return invariant("an option of an order-free node that does not exist");
                };
                let (leaf_ref, pinned_ref) =
                    (self.graph.term_ref(leaf)?, self.graph.term_ref(pinned)?);
                let implement = self.graph.prover.implement(leaf_ref, order, pinned_ref)?;
                let (out, rest) = self.step(pinned)?;
                self.implemented.insert(entry, order);
                Out {
                    node: out.node,
                    term: out.term,
                    start: leaf,
                    proof: self.graph.prover.trans(implement, rest)?,
                }
            }
        })
    }

    /// The e-node of `term`, over what its argument classes are emitted as.
    fn term(&mut self, term: Tid) -> EngineResult<Out> {
        let reference = self.graph.term_ref(term)?;
        let refused = |error: crate::saturate::region::RegionError| {
            crate::proof::EngineError(format!("the chosen form is not a region: {error}"))
        };
        match self.graph.node(term)?.clone() {
            TNode::Leaf(leaf) => {
                let ty = self.graph.ty(term)?;
                Ok(Out {
                    node: self.region.leaf(leaf, ty).map_err(refused)?,
                    term: reference,
                    start: term,
                    proof: self.graph.prover.refl(reference)?,
                })
            }
            TNode::Const(ty, residue) => Ok(Out {
                node: self.region.constant(ty, residue).map_err(refused)?,
                term: reference,
                start: term,
                proof: self.graph.prover.refl(reference)?,
            }),
            TNode::Op(desc, args) => {
                let mut nodes = Vec::with_capacity(args.len());
                let mut proofs = Vec::with_capacity(args.len());
                for arg in &args {
                    let (out, proof) = self.step(*arg)?;
                    nodes.push(out.node);
                    proofs.push(proof);
                }
                let proof = self.graph.prover.congr(desc, &proofs)?;
                Ok(Out {
                    node: self.region.op(desc, &nodes).map_err(refused)?,
                    term: self.graph.prover.conclusion(proof)?.rhs,
                    start: term,
                    proof,
                })
            }
        }
    }
}

/// Write the form `choice` gives as a region, with one claim per root and
/// per kept order-free operand whose term changed. `None` when the form
/// cannot be written as a well-formed region (a kept order-free node whose
/// new operand would read a later node's result).
pub(crate) fn emit(
    graph: &mut Graph,
    input: &Region,
    free: &[FreeNode],
    roots: &[Tid],
    table: &Table,
    choice: &BTreeMap<Tid, usize>,
) -> EngineResult<Option<Emitted>> {
    let mut region = Region::new(input.name(), input.pointer_bits());
    for (leaf, ty) in input.leaves() {
        if region.leaf(leaf, ty).is_err() {
            return invariant("an input leaf the output region refuses");
        }
    }
    let mut emitter = Emitter {
        graph,
        free,
        table,
        choice,
        region,
        done: BTreeMap::new(),
        kept: BTreeSet::new(),
        implemented: BTreeMap::new(),
    };
    let mut claims = Vec::new();
    let mut claim = |emitter: &mut Emitter<'_>, proof: ProofRef| -> EngineResult<()> {
        let conclusion = emitter.graph.prover.conclusion(proof)?;
        if conclusion.lhs != conclusion.rhs {
            claims.push(proof);
        }
        Ok(())
    };
    let mut root_nodes = Vec::with_capacity(roots.len());
    for root in roots {
        let (out, proof) = emitter.step_into(*root)?;
        claim(&mut emitter, proof)?;
        root_nodes.push(out.node);
    }
    // Operands of kept order-free nodes, which may keep further nodes.
    let mut operands: BTreeMap<usize, NodeId> = BTreeMap::new();
    while let Some(entry) = emitter
        .kept
        .iter()
        .copied()
        .find(|entry| !operands.contains_key(entry))
    {
        let Some(operand) = free.get(entry).map(|node| node.operand) else {
            return invariant("a kept order-free node that does not exist");
        };
        let (out, proof) = emitter.step_into(operand)?;
        claim(&mut emitter, proof)?;
        operands.insert(entry, out.node);
    }
    for (entry, operand) in &operands {
        let Some(node) = free.get(*entry) else {
            return invariant("a kept order-free node that does not exist");
        };
        let Some(leaf) = emitter.done.get(&emitter.graph.find(node.leaf)) else {
            return invariant("a kept order-free result that was not emitted");
        };
        let orders: Vec<u32> = node.pinned.iter().map(|(order, _)| *order).collect();
        if emitter
            .region
            .make_order_free(leaf.node, *operand, &orders)
            .is_err()
        {
            return Ok(None);
        }
    }
    for root in root_nodes {
        if emitter.region.root(root).is_err() {
            return invariant("an emitted root the output region refuses");
        }
    }
    Ok(Some(Emitted {
        region: emitter.region,
        claims,
        implemented: emitter.implemented,
    }))
}
