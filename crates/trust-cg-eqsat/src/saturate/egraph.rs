// crates/trust-cg-eqsat/src/saturate/egraph.rs - Tier S e-graph: terms, congruence closure, explanations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The Tier S e-graph (`docs/eqsat-tier-s.md` section 4.1).
//!
//! * Every entry is a **concrete term** ([`Tid`]): a leaf, a constant or an
//!   operator over older terms, hash-consed by structure. A term never
//!   changes, so every proof this module writes is about fixed terms.
//! * A union-find over the terms (representative: the oldest term of the
//!   class) holds the classes. Two operator terms with the same operator
//!   and class-equal arguments are one **e-node**; [`Graph::rebuild`] merges
//!   the classes of such terms until none is left (congruence closure).
//! * Every merge is one edge of a **proof forest** over the terms, labelled
//!   with what justifies it: a rule step, or congruence. The forest is a
//!   tree per class, so two terms of one class are joined by exactly one
//!   path, and that path never changes once it exists (a later merge only
//!   joins two trees). [`Graph::explain`] turns the path into a proof of
//!   `docs/eqsat-tier-e.md` section 7.1; a congruence edge is explained
//!   through its arguments, whose paths are older than the edge.
//!
//! Evidence boundary: the graph records which rule step justifies which
//! edge and composes them; it proves nothing. The checker replays every
//! step against the registry.

use std::collections::{BTreeMap, BTreeSet};

use crate::derivation::{ProofRef, TermRef};
use crate::proof::{EngineResult, Prover, invariant};
use crate::saturate::region::LeafName;
use crate::vocab::{OpDesc, ScalarTy};

/// A concrete term of the graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Tid(u32);

impl Tid {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

pub(crate) const fn tid_from_raw(raw: u32) -> Tid {
    Tid(raw)
}

/// What a [`Tid`] denotes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum TNode {
    Leaf(LeafName),
    Const(ScalarTy, u128),
    Op(OpDesc, Vec<Tid>),
}

/// What justifies a proof-forest edge from one term to another.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Just {
    /// Same operator, class-equal arguments.
    Congruence,
    /// A rule step. `forward` says the step concludes `(edge source, edge
    /// target)`; otherwise it concludes the reverse.
    Rule { proof: ProofRef, forward: bool },
}

impl Just {
    const fn flipped(self) -> Just {
        match self {
            Just::Congruence => Just::Congruence,
            Just::Rule { proof, forward } => Just::Rule {
                proof,
                forward: !forward,
            },
        }
    }
}

/// One class as the matcher and the extractor see it: its representative
/// and one term per e-node (the oldest), oldest first.
#[derive(Debug, Clone)]
pub(crate) struct ClassView {
    pub(crate) root: Tid,
    pub(crate) enodes: Vec<Tid>,
}

/// The e-graph with its proof table.
pub(crate) struct Graph {
    pub(crate) prover: Prover,
    nodes: Vec<TNode>,
    types: Vec<ScalarTy>,
    refs: Vec<TermRef>,
    syntactic: BTreeMap<TNode, Tid>,
    parent: Vec<Tid>,
    forest: Vec<Option<(Tid, Just)>>,
    members: Vec<Vec<Tid>>,
    canon: BTreeMap<(OpDesc, Vec<Tid>), Tid>,
    explained: BTreeMap<(Tid, Tid), ProofRef>,
    merges: u64,
}

impl Graph {
    pub(crate) fn new(region_name: &str) -> Self {
        Self {
            prover: Prover::new_region(region_name),
            nodes: Vec::new(),
            types: Vec::new(),
            refs: Vec::new(),
            syntactic: BTreeMap::new(),
            parent: Vec::new(),
            forest: Vec::new(),
            members: Vec::new(),
            canon: BTreeMap::new(),
            explained: BTreeMap::new(),
            merges: 0,
        }
    }

    /// The number of concrete terms.
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    pub(crate) fn node(&self, term: Tid) -> EngineResult<&TNode> {
        match self.nodes.get(term.index()) {
            Some(node) => Ok(node),
            None => invariant("a term outside the graph"),
        }
    }

    pub(crate) fn ty(&self, term: Tid) -> EngineResult<ScalarTy> {
        match self.types.get(term.index()) {
            Some(ty) => Ok(*ty),
            None => invariant("a term outside the graph"),
        }
    }

    pub(crate) fn term_ref(&self, term: Tid) -> EngineResult<TermRef> {
        match self.refs.get(term.index()) {
            Some(reference) => Ok(*reference),
            None => invariant("a term outside the graph"),
        }
    }

    /// The representative of `term`'s class (the oldest term of the class).
    pub(crate) fn find(&mut self, term: Tid) -> Tid {
        let mut root = term;
        while let Some(next) = self.parent.get(root.index()).copied() {
            if next == root {
                break;
            }
            root = next;
        }
        let mut walk = term;
        while walk != root {
            let Some(slot) = self.parent.get_mut(walk.index()) else {
                break;
            };
            let next = *slot;
            *slot = root;
            walk = next;
        }
        root
    }

    /// The term with this exact structure, if the graph holds it.
    pub(crate) fn lookup(&self, node: &TNode) -> Option<Tid> {
        self.syntactic.get(node).copied()
    }

    /// A term of the e-node `desc` over the classes of `args`, if one exists.
    pub(crate) fn lookup_enode(&mut self, desc: OpDesc, args: &[Tid]) -> Option<Tid> {
        let key: Vec<Tid> = args.iter().map(|arg| self.find(*arg)).collect();
        self.canon.get(&(desc, key)).copied()
    }

    /// The term `node` (created when the graph does not hold it). A new
    /// operator term whose e-node exists joins that e-node's class by
    /// congruence at once.
    pub(crate) fn add(&mut self, node: TNode) -> EngineResult<Tid> {
        if let Some(found) = self.syntactic.get(&node) {
            return Ok(*found);
        }
        let (ty, reference) = match &node {
            TNode::Leaf(_) => {
                return invariant("a leaf that was not declared before use");
            }
            TNode::Const(ty, residue) => (*ty, self.prover.constant(*ty, *residue)),
            TNode::Op(desc, args) => {
                if args.len() != desc.arity() {
                    return invariant("an operator term with the wrong arity");
                }
                let mut refs = Vec::with_capacity(args.len());
                for (position, arg) in args.iter().enumerate() {
                    if desc.operand_ty(position) != Some(self.ty(*arg)?) {
                        return invariant("an operator term with an operand of the wrong type");
                    }
                    refs.push(self.term_ref(*arg)?);
                }
                (desc.result_ty(), self.prover.op(*desc, &refs))
            }
        };
        self.push(node, ty, reference)
    }

    /// Declare a leaf of the region (the only way a leaf term is made).
    pub(crate) fn declare_leaf(&mut self, leaf: LeafName, ty: ScalarTy) -> EngineResult<Tid> {
        let node = TNode::Leaf(leaf);
        if let Some(found) = self.syntactic.get(&node) {
            return Ok(*found);
        }
        let reference = match leaf {
            LeafName::Param { block, index } => self.prover.param(block, index),
            LeafName::Result {
                block,
                ordinal,
                index,
            } => self.prover.result(block, ordinal, index),
        };
        self.push(node, ty, reference)
    }

    fn push(&mut self, node: TNode, ty: ScalarTy, reference: TermRef) -> EngineResult<Tid> {
        let Ok(raw) = u32::try_from(self.nodes.len()) else {
            return invariant("too many terms");
        };
        let term = Tid(raw);
        self.nodes.push(node.clone());
        self.types.push(ty);
        self.refs.push(reference);
        self.parent.push(term);
        self.forest.push(None);
        self.members.push(vec![term]);
        self.syntactic.insert(node.clone(), term);
        if let TNode::Op(desc, args) = node {
            let key: Vec<Tid> = args.iter().map(|arg| self.find(*arg)).collect();
            match self.canon.get(&(desc, key.clone())).copied() {
                Some(existing) => {
                    self.merge(term, existing, Just::Congruence)?;
                }
                None => {
                    self.canon.insert((desc, key), term);
                }
            }
        }
        Ok(term)
    }

    /// Merge the classes of `lhs` and `rhs`, justified by the rule step
    /// `proof`, which concludes `(lhs, rhs, equiv)`. `false` when they
    /// already were one class.
    pub(crate) fn union_by_rule(
        &mut self,
        lhs: Tid,
        rhs: Tid,
        proof: ProofRef,
    ) -> EngineResult<bool> {
        let conclusion = self.prover.conclusion(proof)?;
        if !conclusion.equiv
            || conclusion.lhs != self.term_ref(lhs)?
            || conclusion.rhs != self.term_ref(rhs)?
        {
            return invariant("a merge whose rule step does not relate its two terms");
        }
        self.merge(
            lhs,
            rhs,
            Just::Rule {
                proof,
                forward: true,
            },
        )
    }

    fn merge(&mut self, a: Tid, b: Tid, just: Just) -> EngineResult<bool> {
        let (root_a, root_b) = (self.find(a), self.find(b));
        if root_a == root_b {
            return Ok(false);
        }
        // Make `a` the root of its tree, then hang it under `b`.
        let mut previous: Option<(Tid, Just)> = None;
        let mut current = a;
        loop {
            let Some(slot) = self.forest.get_mut(current.index()) else {
                return invariant("a proof-forest edge to a term outside the graph");
            };
            let next = slot.take();
            *slot = previous;
            match next {
                None => break,
                Some((up, edge)) => {
                    previous = Some((current, edge.flipped()));
                    current = up;
                }
            }
        }
        if let Some(slot) = self.forest.get_mut(a.index()) {
            *slot = Some((b, just));
        }
        let (keep, drop) = if root_a < root_b {
            (root_a, root_b)
        } else {
            (root_b, root_a)
        };
        if let Some(slot) = self.parent.get_mut(drop.index()) {
            *slot = keep;
        }
        let moved = match self.members.get_mut(drop.index()) {
            Some(list) => std::mem::take(list),
            None => Vec::new(),
        };
        if let Some(list) = self.members.get_mut(keep.index()) {
            let mut merged = Vec::with_capacity(list.len() + moved.len());
            let (mut i, mut j) = (0, 0);
            while i < list.len() || j < moved.len() {
                let take_left = match (list.get(i), moved.get(j)) {
                    (Some(left), Some(right)) => left < right,
                    (Some(_), None) => true,
                    _ => false,
                };
                if take_left {
                    merged.extend(list.get(i).copied());
                    i += 1;
                } else {
                    merged.extend(moved.get(j).copied());
                    j += 1;
                }
            }
            *list = merged;
        }
        self.merges += 1;
        Ok(true)
    }

    /// Congruence closure: merge the classes of operator terms that are one
    /// e-node until none is left, and rebuild the e-node index.
    pub(crate) fn rebuild(&mut self) -> EngineResult<()> {
        loop {
            let before = self.merges;
            let mut fresh: BTreeMap<(OpDesc, Vec<Tid>), Tid> = BTreeMap::new();
            for raw in 0..self.nodes.len() {
                let Ok(raw) = u32::try_from(raw) else {
                    return invariant("too many terms");
                };
                let term = Tid(raw);
                let TNode::Op(desc, args) = self.node(term)?.clone() else {
                    continue;
                };
                let key: Vec<Tid> = args.iter().map(|arg| self.find(*arg)).collect();
                match fresh.get(&(desc, key.clone())).copied() {
                    Some(first) => {
                        self.merge(term, first, Just::Congruence)?;
                    }
                    None => {
                        fresh.insert((desc, key), term);
                    }
                }
            }
            self.canon = fresh;
            if self.merges == before {
                return Ok(());
            }
        }
    }

    /// The classes, oldest representative first, each with one term per
    /// e-node. Call after [`Graph::rebuild`].
    pub(crate) fn classes(&mut self) -> EngineResult<Vec<ClassView>> {
        let mut out = Vec::new();
        for raw in 0..self.nodes.len() {
            let Ok(raw) = u32::try_from(raw) else {
                return invariant("too many terms");
            };
            let root = Tid(raw);
            if self.find(root) != root {
                continue;
            }
            let members = match self.members.get(root.index()) {
                Some(list) => list.clone(),
                None => Vec::new(),
            };
            let mut seen: BTreeMap<(OpDesc, Vec<Tid>), ()> = BTreeMap::new();
            let mut enodes = Vec::new();
            for member in members {
                match self.node(member)?.clone() {
                    TNode::Leaf(_) | TNode::Const(..) => enodes.push(member),
                    TNode::Op(desc, args) => {
                        let key: Vec<Tid> = args.iter().map(|arg| self.find(*arg)).collect();
                        if seen.insert((desc, key), ()).is_none() {
                            enodes.push(member);
                        }
                    }
                }
            }
            out.push(ClassView { root, enodes });
        }
        Ok(out)
    }

    fn path_up(&self, term: Tid) -> EngineResult<Vec<Tid>> {
        let mut path = vec![term];
        let mut current = term;
        while let Some(Some((up, _))) = self.forest.get(current.index()) {
            if path.len() > self.nodes.len() {
                return invariant("a cycle in the proof forest");
            }
            path.push(*up);
            current = *up;
        }
        Ok(path)
    }

    /// The forest path from `a` to `b`: each step is the term whose stored
    /// edge is walked and whether it is walked from the parent down.
    fn path(&self, a: Tid, b: Tid) -> EngineResult<Vec<(Tid, bool)>> {
        let up_a = self.path_up(a)?;
        let up_b = self.path_up(b)?;
        let position: BTreeMap<Tid, usize> = up_a
            .iter()
            .enumerate()
            .map(|(index, term)| (*term, index))
            .collect();
        let Some((meet_b, meet_a)) = up_b
            .iter()
            .enumerate()
            .find_map(|(index, term)| position.get(term).map(|found| (index, *found)))
        else {
            return invariant("an explanation between terms of two classes");
        };
        let mut steps = Vec::with_capacity(meet_a + meet_b);
        steps.extend(up_a.iter().take(meet_a).map(|term| (*term, false)));
        steps.extend(up_b.iter().take(meet_b).rev().map(|term| (*term, true)));
        Ok(steps)
    }

    /// The argument pairs the congruence edge stored at `from` is explained
    /// through, in the direction the edge is read (none for a rule edge).
    fn edge_arguments(&self, from: Tid, reversed: bool) -> EngineResult<(OpDesc, Vec<(Tid, Tid)>)> {
        let Some(Some((to, _))) = self.forest.get(from.index()).copied() else {
            return invariant("a missing proof-forest edge");
        };
        let (TNode::Op(desc, from_args), TNode::Op(to_desc, to_args)) =
            (self.node(from)?, self.node(to)?)
        else {
            return invariant("a congruence edge between terms that are not operators");
        };
        if desc != to_desc || from_args.len() != to_args.len() {
            return invariant("a congruence edge between two operators");
        }
        let pairs = from_args
            .iter()
            .zip(to_args)
            .map(|(x, y)| if reversed { (*y, *x) } else { (*x, *y) })
            .collect();
        Ok((*desc, pairs))
    }

    /// The explanation of `(a, b)` when it needs no walk: equal terms, or a
    /// pair already explained.
    fn explained_now(&mut self, a: Tid, b: Tid) -> EngineResult<Option<ProofRef>> {
        if a == b {
            let start = self.term_ref(a)?;
            return self.prover.refl(start).map(Some);
        }
        Ok(self.explained.get(&(a, b)).copied())
    }

    /// A proof of `(a, b, equiv)` for two terms of one class.
    ///
    /// A congruence edge is explained through its arguments, and those
    /// through theirs. The walk keeps its own stack of pairs, so a region
    /// as deep as memory allows is explained without deep recursion.
    pub(crate) fn explain(&mut self, a: Tid, b: Tid) -> EngineResult<ProofRef> {
        // Pairs still to explain; a pair in `open` waits for the argument
        // pairs of its congruence edges, which are above it on the stack.
        let mut stack: Vec<(Tid, Tid)> = vec![(a, b)];
        let mut open: BTreeSet<(Tid, Tid)> = BTreeSet::new();
        while let Some((x, y)) = stack.last().copied() {
            if self.explained_now(x, y)?.is_some() {
                stack.pop();
                continue;
            }
            let path = self.path(x, y)?;
            let mut needed: Vec<(Tid, Tid)> = Vec::new();
            for (from, reversed) in &path {
                let Some(Some((_, Just::Congruence))) = self.forest.get(from.index()).copied()
                else {
                    continue;
                };
                for (p, q) in self.edge_arguments(*from, *reversed)?.1 {
                    if self.explained_now(p, q)?.is_none() {
                        needed.push((p, q));
                    }
                }
            }
            if !needed.is_empty() {
                // The arguments of a congruence edge were one class before
                // the edge existed, so their paths never lead back here.
                if !open.insert((x, y)) || needed.iter().any(|pair| open.contains(pair)) {
                    return invariant("an explanation that needs itself");
                }
                stack.extend(needed);
                continue;
            }
            let start = self.term_ref(x)?;
            let mut steps = Vec::with_capacity(path.len());
            for (from, reversed) in path {
                steps.push(self.edge(from, reversed)?);
            }
            let proof = self.prover.chain(start, &steps)?;
            let conclusion = self.prover.conclusion(proof)?;
            if conclusion.lhs != start || conclusion.rhs != self.term_ref(y)? || !conclusion.equiv {
                return invariant("an explanation that does not relate its two terms");
            }
            self.explained.insert((x, y), proof);
            open.remove(&(x, y));
            stack.pop();
        }
        match self.explained_now(a, b)? {
            Some(proof) => Ok(proof),
            None => invariant("an explanation that was not written"),
        }
    }

    /// The proof of the forest edge stored at `from`, read from `from` to
    /// its parent, or from the parent to `from` when `reversed`. The
    /// argument pairs of a congruence edge are already explained.
    fn edge(&mut self, from: Tid, reversed: bool) -> EngineResult<ProofRef> {
        let Some(Some((_, just))) = self.forest.get(from.index()).copied() else {
            return invariant("a missing proof-forest edge");
        };
        match just {
            Just::Rule { proof, forward } => {
                if forward == reversed {
                    self.prover.sym(proof)
                } else {
                    Ok(proof)
                }
            }
            Just::Congruence => {
                let (desc, pairs) = self.edge_arguments(from, reversed)?;
                let mut proofs = Vec::with_capacity(pairs.len());
                for (x, y) in pairs {
                    match self.explained_now(x, y)? {
                        Some(proof) => proofs.push(proof),
                        None => {
                            return invariant(
                                "a congruence edge whose arguments are not explained",
                            );
                        }
                    }
                }
                self.prover.congr(desc, &proofs)
            }
        }
    }
}
