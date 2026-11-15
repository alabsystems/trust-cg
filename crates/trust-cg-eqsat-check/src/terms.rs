// trust-cg-eqsat-check/src/terms.rs - positional leaves and the hash-consed, typed term table
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Terms (docs/eqsat-tier-e.md section 4) in one structural interner shared by
//! both bodies, the derivation's term table and every conclusion replay
//! builds, so that two terms are equal exactly when their ids are equal.
//!
//! Every term the interner holds is well typed and well formed:
//! * a leaf exists in the input body's leaf table and has a scalar graph type;
//! * a constant's residue is below `2^w` of its graph type;
//! * an operator is admitted at its types, its children have its operand
//!   types, and every child that is a leaf is **defined** (section 2.3),
//!   because graph operators are total only on defined operands.
//!
//! A leaf standing alone (not under an operator) may be maybe-poison: it is
//! the term of a skeleton operand that reads a parameter or a load.

use std::collections::BTreeMap;
use std::fmt;

use trust_ir::Ty;

use crate::types::{Ctx, OpDesc, Sty, mask};

/// A leaf, named by position (section 4).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Leaf {
    /// Parameter `index` of block `block` (raw `BlockId`).
    Param { block: u32, index: u32 },
    /// Result `index` of the `ordinal`-th skeleton instruction of `block`.
    Result {
        block: u32,
        ordinal: u32,
        index: u32,
    },
}

impl fmt::Display for Leaf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Leaf::Param { block, index } => write!(f, "Param(bb{block}, {index})"),
            Leaf::Result {
                block,
                ordinal,
                index,
            } => write!(f, "Result(bb{block}, {ordinal}, {index})"),
        }
    }
}

/// What the input body says about a leaf.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct LeafInfo {
    /// The declared parameter type, or `InstrNode::result_tys(&Module)[j]`.
    pub(crate) ty: Ty,
    /// That type as a scalar graph type, when it is one.
    pub(crate) sty: Option<Sty>,
    /// Defined (never poison), per section 2.3.
    pub(crate) defined: bool,
}

pub(crate) type TermId = usize;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Node {
    Leaf(Leaf),
    Const(Sty, u128),
    Op(OpDesc, Vec<TermId>),
}

/// Why a term cannot be formed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TermError {
    IllTyped(String),
    UnknownLeaf(Leaf),
    MaybePoison(Leaf),
}

pub(crate) struct Interner {
    ctx: Ctx,
    leaves: BTreeMap<Leaf, LeafInfo>,
    nodes: Vec<(Node, Sty)>,
    index: BTreeMap<Node, TermId>,
}

impl Interner {
    /// An interner over the input body's leaf table.
    pub(crate) fn new(ctx: Ctx, leaves: BTreeMap<Leaf, LeafInfo>) -> Self {
        Interner {
            ctx,
            leaves,
            nodes: Vec::new(),
            index: BTreeMap::new(),
        }
    }

    pub(crate) fn ctx(&self) -> Ctx {
        self.ctx
    }

    fn intern(&mut self, node: Node, ty: Sty) -> TermId {
        if let Some(&id) = self.index.get(&node) {
            return id;
        }
        let id = self.nodes.len();
        self.nodes.push((node.clone(), ty));
        self.index.insert(node, id);
        id
    }

    pub(crate) fn node(&self, id: TermId) -> Option<&Node> {
        self.nodes.get(id).map(|(n, _)| n)
    }

    pub(crate) fn ty(&self, id: TermId) -> Option<Sty> {
        self.nodes.get(id).map(|(_, t)| *t)
    }

    /// The residue of `id` when it is a constant.
    pub(crate) fn const_value(&self, id: TermId) -> Option<(Sty, u128)> {
        match self.node(id) {
            Some(Node::Const(t, r)) => Some((*t, *r)),
            _ => None,
        }
    }

    pub(crate) fn leaf_info(&self, leaf: Leaf) -> Option<&LeafInfo> {
        self.leaves.get(&leaf)
    }

    /// A leaf of the input body with a scalar graph type.
    pub(crate) fn leaf(&mut self, leaf: Leaf) -> Result<TermId, TermError> {
        let Some(info) = self.leaves.get(&leaf) else {
            return Err(TermError::UnknownLeaf(leaf));
        };
        let Some(sty) = info.sty else {
            return Err(TermError::IllTyped(format!(
                "leaf {leaf} has type {:?}, which is not a graph type",
                info.ty
            )));
        };
        Ok(self.intern(Node::Leaf(leaf), sty))
    }

    /// `Const(t, r)` with `r < 2^w(t)`.
    pub(crate) fn constant(&mut self, t: Sty, r: u128) -> Result<TermId, TermError> {
        let Some(w) = self.ctx.width(t) else {
            return Err(TermError::IllTyped(format!(
                "constant type {} has no established width in this module",
                t.name()
            )));
        };
        if r > mask(w) {
            return Err(TermError::IllTyped(format!(
                "constant residue {r} is not below 2^{w} ({})",
                t.name()
            )));
        }
        Ok(self.intern(Node::Const(t, r), t))
    }

    /// An operator over existing terms.
    pub(crate) fn op(&mut self, desc: OpDesc, args: &[TermId]) -> Result<TermId, TermError> {
        if !desc.admitted(self.ctx) {
            return Err(TermError::IllTyped(format!(
                "operator {} is not admitted at its types",
                desc.describe()
            )));
        }
        if args.len() != desc.arity() {
            return Err(TermError::IllTyped(format!(
                "operator {} takes {} operands, given {}",
                desc.describe(),
                desc.arity(),
                args.len()
            )));
        }
        for (i, (&arg, want)) in args.iter().zip(desc.operand_tys()).enumerate() {
            let Some(have) = self.ty(arg) else {
                return Err(TermError::IllTyped(format!("operand {i} names no term")));
            };
            if have != want {
                return Err(TermError::IllTyped(format!(
                    "operand {i} of {} has type {}, expected {}",
                    desc.describe(),
                    have.name(),
                    want.name()
                )));
            }
            if let Some(Node::Leaf(leaf)) = self.node(arg) {
                let defined = self.leaves.get(leaf).is_some_and(|i| i.defined);
                if !defined {
                    return Err(TermError::MaybePoison(*leaf));
                }
            }
        }
        Ok(self.intern(Node::Op(desc, args.to_vec()), desc.result_ty()))
    }

    /// A bounded rendering for diagnostics.
    pub(crate) fn render(&self, id: TermId) -> String {
        let mut out = String::new();
        self.render_into(id, 6, &mut out);
        out
    }

    fn render_into(&self, id: TermId, depth: usize, out: &mut String) {
        match self.node(id) {
            None => out.push_str("<none>"),
            Some(Node::Leaf(l)) => out.push_str(&l.to_string()),
            Some(Node::Const(t, r)) => out.push_str(&format!("(const.{} {r})", t.name())),
            Some(Node::Op(desc, args)) => {
                if depth == 0 {
                    out.push_str("(..)");
                    return;
                }
                out.push('(');
                out.push_str(&desc.describe());
                for &a in args {
                    out.push(' ');
                    self.render_into(a, depth - 1, out);
                }
                out.push(')');
            }
        }
    }
}
