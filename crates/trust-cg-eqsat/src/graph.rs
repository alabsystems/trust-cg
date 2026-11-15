// crates/trust-cg-eqsat/src/graph.rs - Id arena, union-find, explanation edges and the scoped GVN map
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The acyclic e-graph of section 6.
//!
//! * Every entry is an [`Id`] in an append-only arena: a concrete [`Node`], a
//!   `Union(a, b)` or a `Directed(a, b)`. Arguments and union operands are
//!   always older Ids, so the arena is acyclic and an Id's tree is immutable.
//! * Every Id has a **canonical term**: a node's own term over its arguments'
//!   canonical terms, and for `Union(a, b)`/`Directed(a, b)` the canonical
//!   term of `a`. A union records a proof `canon(a) -> canon(b)`.
//! * The union-find (representative: the oldest Id of the class) keys
//!   hash-consing. Every union-find merge is backed by an `equiv` edge whose
//!   proof relates the two endpoints' canonical terms, so any two Ids of one
//!   class can be explained by a path of edges ([`Graph::explain`]).
//! * The hash-cons map is scoped by the dominator tree: an entry made in a
//!   block is removed when the traversal leaves that block's subtree.
//!
//! Evidence boundary: the graph records which proof justifies which edge; it
//! does not check the proofs (the [`crate::proof::Prover`] checks only that
//! composed steps fit, the checker checks everything).

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use trust_ir::ValueId;

use crate::derivation::{ProofRef, TermRef};
use crate::proof::{EngineResult, Prover, invariant};
use crate::vocab::{OpDesc, ScalarTy};

/// An entry of the arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Id(u32);

impl Id {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// The Id at arena position `raw` (the caller iterates the arena).
pub(crate) const fn id_from_raw(raw: u32) -> Id {
    Id(raw)
}

/// The position of a graph leaf (section 4), never a `ValueId`. Only defined
/// leaves become graph nodes, and a block parameter is never defined
/// (section 2.3), so a graph leaf is always a skeleton result
/// `Result(block, k, j)`; parameter leaves appear only as terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum LeafPos {
    Result {
        block: u32,
        ordinal: u32,
        index: u32,
    },
}

/// A concrete node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Node {
    /// A defined leaf of a scalar graph type, with the value that carries it
    /// (the same `ValueId` in the input and the output body).
    Leaf {
        pos: LeafPos,
        ty: ScalarTy,
        value: ValueId,
    },
    /// `Const(ty, residue)`.
    Const { ty: ScalarTy, residue: u128 },
    /// An operator over older Ids.
    Op { desc: OpDesc, args: Vec<Id> },
}

/// An arena entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Entry {
    Node(Node),
    /// `Union(a, b)`; `just` proves `canon(a) -> canon(b)` (`equiv`).
    Union {
        a: Id,
        b: Id,
        just: ProofRef,
    },
    /// `Directed(a, b)`; `just` proves `canon(a) -> canon(b)` (`refines`, or
    /// an `equiv` rule matched through a refinement).
    Directed {
        a: Id,
        b: Id,
        just: ProofRef,
    },
}

/// A hash-cons key: the operator and the union-find representatives of the
/// arguments (constants by value).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Key {
    Const(ScalarTy, u128),
    Op(OpDesc, Vec<Id>),
}

/// A hash-cons entry: the node first created for the key and the Id the
/// node's creation ended with (after its rules fired).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Hit {
    pub(crate) node: Id,
    pub(crate) current: Id,
}

/// One explanation edge, stored at both endpoints.
#[derive(Debug, Clone, Copy)]
struct Edge {
    other: Id,
    proof: ProofRef,
    /// `true`: `proof` concludes `canon(self) -> canon(other)`; `false`: the
    /// reverse.
    forward: bool,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Graph {
    entries: Vec<Entry>,
    canon: Vec<TermRef>,
    parent: Vec<Id>,
    edges: Vec<Vec<Edge>>,
    map: BTreeMap<Key, Hit>,
    undo: Vec<(Key, Option<Hit>)>,
    scopes: Vec<usize>,
    leaves: BTreeMap<LeafPos, Id>,
}

impl Graph {
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn entry(&self, id: Id) -> EngineResult<&Entry> {
        match self.entries.get(id.index()) {
            Some(entry) => Ok(entry),
            None => invariant("an Id outside the arena"),
        }
    }

    pub(crate) fn entries(&self) -> &[Entry] {
        &self.entries
    }

    pub(crate) fn canon(&self, id: Id) -> EngineResult<TermRef> {
        match self.canon.get(id.index()) {
            Some(term) => Ok(*term),
            None => invariant("an Id without a canonical term"),
        }
    }

    /// Append an entry with its canonical term; it starts as its own class.
    pub(crate) fn push(&mut self, entry: Entry, canon: TermRef) -> EngineResult<Id> {
        let Ok(raw) = u32::try_from(self.entries.len()) else {
            return invariant("the arena outgrew u32 Ids");
        };
        let id = Id(raw);
        // Acyclicity: every referenced Id is older.
        let older = |other: &Id| other.0 < raw;
        let ok = match &entry {
            Entry::Node(Node::Op { args, .. }) => args.iter().all(older),
            Entry::Node(_) => true,
            Entry::Union { a, b, .. } | Entry::Directed { a, b, .. } => older(a) && older(b),
        };
        if !ok {
            return invariant("an entry refers to a newer Id");
        }
        self.entries.push(entry);
        self.canon.push(canon);
        self.parent.push(id);
        self.edges.push(Vec::new());
        Ok(id)
    }

    // ---- union-find --------------------------------------------------------

    pub(crate) fn find(&mut self, id: Id) -> Id {
        let mut root = id;
        while let Some(&up) = self.parent.get(root.index()) {
            if up == root {
                break;
            }
            root = up;
        }
        // Path compression.
        let mut cur = id;
        while cur != root {
            let Some(slot) = self.parent.get_mut(cur.index()) else {
                break;
            };
            let next = *slot;
            *slot = root;
            cur = next;
        }
        root
    }

    /// Merge the classes of `a` and `b`, recording the explanation edge
    /// `proof: canon(a) -> canon(b)` (which must be `equiv`). The older root
    /// stays the representative.
    pub(crate) fn merge(&mut self, a: Id, b: Id, proof: ProofRef) -> EngineResult<()> {
        let (ra, rb) = (self.find(a), self.find(b));
        if let Some(list) = self.edges.get_mut(a.index()) {
            list.push(Edge {
                other: b,
                proof,
                forward: true,
            });
        } else {
            return invariant("merge of an Id outside the arena");
        }
        if let Some(list) = self.edges.get_mut(b.index()) {
            list.push(Edge {
                other: a,
                proof,
                forward: false,
            });
        } else {
            return invariant("merge of an Id outside the arena");
        }
        if ra != rb {
            let (keep, absorb) = if ra < rb { (ra, rb) } else { (rb, ra) };
            if let Some(slot) = self.parent.get_mut(absorb.index()) {
                *slot = keep;
            }
        }
        Ok(())
    }

    /// A proof `canon(a) -> canon(b)` (`equiv`) for two Ids of one class: the
    /// shortest path of explanation edges, found breadth-first in edge
    /// insertion order (deterministic).
    pub(crate) fn explain(&mut self, prover: &mut Prover, a: Id, b: Id) -> EngineResult<ProofRef> {
        let start = self.canon(a)?;
        if a == b {
            return prover.refl(start);
        }
        if self.find(a) != self.find(b) {
            return invariant("explain across two classes");
        }
        let mut previous: BTreeMap<Id, (Id, Edge)> = BTreeMap::new();
        let mut seen: BTreeSet<Id> = BTreeSet::new();
        let mut queue = VecDeque::new();
        seen.insert(a);
        queue.push_back(a);
        'search: while let Some(cur) = queue.pop_front() {
            let Some(list) = self.edges.get(cur.index()) else {
                return invariant("explain reached an Id outside the arena");
            };
            for edge in list {
                if seen.insert(edge.other) {
                    previous.insert(edge.other, (cur, *edge));
                    if edge.other == b {
                        break 'search;
                    }
                    queue.push_back(edge.other);
                }
            }
        }
        let mut path = Vec::new();
        let mut cur = b;
        while cur != a {
            let Some((from, edge)) = previous.get(&cur) else {
                return invariant("no explanation path inside one class");
            };
            path.push(*edge);
            cur = *from;
        }
        path.reverse();
        let mut steps = Vec::with_capacity(path.len());
        for edge in path {
            steps.push(if edge.forward {
                edge.proof
            } else {
                prover.sym(edge.proof)?
            });
        }
        prover.chain(start, &steps)
    }

    // ---- scoped hash-consing -----------------------------------------------

    pub(crate) fn lookup(&self, key: &Key) -> Option<Hit> {
        self.map.get(key).copied()
    }

    /// Insert or replace `key` in the current scope.
    pub(crate) fn insert(&mut self, key: Key, hit: Hit) {
        let previous = self.map.insert(key.clone(), hit);
        if !self.scopes.is_empty() {
            self.undo.push((key, previous));
        }
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(self.undo.len());
    }

    pub(crate) fn pop_scope(&mut self) {
        let Some(mark) = self.scopes.pop() else {
            return;
        };
        while self.undo.len() > mark {
            let Some((key, previous)) = self.undo.pop() else {
                break;
            };
            match previous {
                Some(hit) => {
                    self.map.insert(key, hit);
                }
                None => {
                    self.map.remove(&key);
                }
            }
        }
    }

    pub(crate) fn leaf(&self, pos: LeafPos) -> Option<Id> {
        self.leaves.get(&pos).copied()
    }

    pub(crate) fn set_leaf(&mut self, pos: LeafPos, id: Id) {
        self.leaves.insert(pos, id);
    }

    /// The distinct Ids of `id`'s tree (itself, inner unions, members), in
    /// depth-first order.
    pub(crate) fn tree_ids(&self, id: Id) -> EngineResult<Vec<Id>> {
        let mut out = Vec::new();
        let mut seen = BTreeSet::new();
        let mut stack = vec![id];
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            out.push(cur);
            match self.entry(cur)? {
                Entry::Node(_) => {}
                Entry::Union { a, b, .. } | Entry::Directed { a, b, .. } => {
                    stack.push(*b);
                    stack.push(*a);
                }
            }
        }
        Ok(out)
    }

    /// The concrete members of `id`'s tree (depth-first, `a` before `b`,
    /// each member once). The walk keeps one parent link per visited Id, so
    /// it is linear in the tree; [`Members::proof`] builds a member's path
    /// proof only when it is asked for.
    pub(crate) fn members(&self, id: Id) -> EngineResult<Members> {
        let mut walk = Members {
            visited: Vec::new(),
            members: Vec::new(),
        };
        let mut seen = BTreeSet::new();
        let mut stack = vec![Visited { id, link: None }];
        while let Some(Visited { id: cur, link }) = stack.pop() {
            // Every Id (member or inner union) is expanded once, along the
            // first path that reaches it, so a shared sub-tree is not walked
            // again.
            if !seen.insert(cur) {
                continue;
            }
            let index = walk.visited.len();
            walk.visited.push(Visited { id: cur, link });
            match self.entry(cur)? {
                Entry::Node(_) => walk.members.push(index),
                Entry::Union { a, b, just } | Entry::Directed { a, b, just } => {
                    stack.push(Visited {
                        id: *b,
                        link: Some(Link {
                            parent: index,
                            step: Some(*just),
                        }),
                    });
                    stack.push(Visited {
                        id: *a,
                        link: Some(Link {
                            parent: index,
                            step: None,
                        }),
                    });
                }
            }
        }
        Ok(walk)
    }
}

/// One Id reached by [`Graph::members`], with the link from its parent
/// (none for the root).
#[derive(Debug, Clone, Copy)]
struct Visited {
    id: Id,
    link: Option<Link>,
}

/// The parent's index in the walk and, for a `b` side, the parent's
/// justification `canon(a) -> canon(b)` (an `a` side has the parent's
/// canonical term, so it needs no step).
#[derive(Debug, Clone, Copy)]
struct Link {
    parent: usize,
    step: Option<ProofRef>,
}

/// The result of [`Graph::members`].
#[derive(Debug, Clone)]
pub(crate) struct Members {
    visited: Vec<Visited>,
    members: Vec<usize>,
}

impl Members {
    /// The number of concrete members.
    pub(crate) fn len(&self) -> usize {
        self.members.len()
    }

    /// The `k`-th concrete member.
    pub(crate) fn member(&self, k: usize) -> EngineResult<Id> {
        match self
            .members
            .get(k)
            .and_then(|index| self.visited.get(*index))
        {
            Some(visited) => Ok(visited.id),
            None => invariant("a member index outside the walk"),
        }
    }

    /// A proof `canon(root) -> canon(member k)`, composed right-recursively
    /// (`Trans(step, rest)`), so two paths that end alike share their
    /// suffix in the interned proof table.
    pub(crate) fn proof(
        &self,
        k: usize,
        graph: &Graph,
        prover: &mut Prover,
    ) -> EngineResult<ProofRef> {
        let Some(&index) = self.members.get(k) else {
            return invariant("a member index outside the walk");
        };
        let Some(member) = self.visited.get(index) else {
            return invariant("a member index outside the walk");
        };
        let mut proof = prover.refl(graph.canon(member.id)?)?;
        let mut link = member.link;
        while let Some(Link { parent, step }) = link {
            if let Some(step) = step {
                proof = prover.trans(step, proof)?;
            }
            link = match self.visited.get(parent) {
                Some(visited) => visited.link,
                None => return invariant("a parent index outside the walk"),
            };
        }
        Ok(proof)
    }
}
