// crates/trust-cg-eqsat/src/extract.rs - cost-based extraction over Id trees
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Extraction (section 6): each Id's cheapest member, bottom-up over the
//! arena. An Id's candidates are only the members of its own tree (through
//! `Union` and `Directed`), never its union-find class, so a chosen node's
//! leaves are always available where the Id is used. Costs are the static
//! costs of section 6 summed over the member's argument Ids' choices (leaves
//! 0, constants 1); ties keep the older member (smaller Id), and on a tie
//! between the two sides of a union the left (older) side.
//!
//! Every member of a tree has a proof from the tree's canonical term
//! ([`crate::graph`]), so whatever is chosen can be justified; the proof is
//! assembled by the elaborator along the side choices recorded here.

use crate::graph::{Entry, Graph, Id, Node};
use crate::proof::{EngineResult, invariant};
use crate::vocab::CONST_COST;

/// The choice for one Id.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Choice {
    /// Tree cost of the chosen member.
    pub(crate) cost: u64,
    /// The chosen concrete member.
    pub(crate) member: Id,
    /// For a union or directed Id: the member is reached through `a` (true)
    /// or `b` (false).
    pub(crate) left: bool,
}

/// The choice for every Id of the arena, indexed by Id.
pub(crate) fn choose(graph: &Graph) -> EngineResult<Vec<Choice>> {
    let mut out: Vec<Choice> = Vec::with_capacity(graph.len());
    for (index, entry) in graph.entries().iter().enumerate() {
        let Ok(raw) = u32::try_from(index) else {
            return invariant("the arena outgrew u32 Ids");
        };
        let this = id_of(raw);
        let get = |id: &Id| -> EngineResult<Choice> {
            match out.get(id.index()) {
                Some(choice) => Ok(*choice),
                None => invariant("extraction reached a newer Id"),
            }
        };
        let choice = match entry {
            Entry::Node(Node::Leaf { .. }) => Choice {
                cost: 0,
                member: this,
                left: true,
            },
            Entry::Node(Node::Const { .. }) => Choice {
                cost: CONST_COST,
                member: this,
                left: true,
            },
            Entry::Node(Node::Op { desc, args }) => {
                let mut cost = desc.cost();
                for arg in args {
                    cost = cost.saturating_add(get(arg)?.cost);
                }
                Choice {
                    cost,
                    member: this,
                    left: true,
                }
            }
            Entry::Union { a, b, .. } | Entry::Directed { a, b, .. } => {
                let (ca, cb) = (get(a)?, get(b)?);
                if (cb.cost, cb.member) < (ca.cost, ca.member) {
                    Choice {
                        cost: cb.cost,
                        member: cb.member,
                        left: false,
                    }
                } else {
                    Choice {
                        cost: ca.cost,
                        member: ca.member,
                        left: true,
                    }
                }
            }
        };
        out.push(choice);
    }
    Ok(out)
}

fn id_of(raw: u32) -> Id {
    crate::graph::id_from_raw(raw)
}
