// crates/trust-cg-eqsat/src/saturate/region.rs - Tier S regions and their byte format
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A Tier S region (`docs/eqsat-tier-s.md` sections 2 and 3): typed leaves, a
//! hash-consed DAG of total operators over them, order-free nodes and roots.
//!
//! [`Region`] is a builder that refuses an ill-typed node, and
//! [`Region::encode`] writes the section 3 bytes the checker reads with its
//! own decoder. The checks here keep the engine from building a region it
//! already knows is malformed; they are not evidence. Only the checker
//! decides what a region and a derivation establish.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::vocab::{CONST_COST, GraphWidths, OpDesc, REDUCTION_COST, ScalarTy, mask};

/// The magic bytes that open every region.
pub const REGION_MAGIC: [u8; 8] = *b"TCGEQREG";

/// The region format version this crate writes.
pub const REGION_FORMAT_VERSION: u32 = 1;

/// A leaf, named by position as in Tier E (`docs/eqsat-tier-e.md` section 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LeafName {
    /// Parameter `index` of block `block`.
    Param {
        /// The raw block id.
        block: u32,
        /// The parameter index.
        index: u32,
    },
    /// Result `index` of the `ordinal`-th skeleton instruction of `block`.
    Result {
        /// The raw block id.
        block: u32,
        /// The skeleton ordinal.
        ordinal: u32,
        /// The result index.
        index: u32,
    },
}

/// A node of a [`Region`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(u32);

impl NodeId {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// What a [`NodeId`] denotes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RegionNode {
    /// A declared leaf.
    Leaf(LeafName),
    /// `Const(ty, residue)`.
    Const(ScalarTy, u128),
    /// An operator over earlier nodes.
    Op(OpDesc, Vec<NodeId>),
}

/// An order-free node (section 2.3): the leaf that is its result, its
/// operand, and the orders of its family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderFree {
    /// The leaf node that is the result.
    pub leaf: NodeId,
    /// The operand.
    pub operand: NodeId,
    /// The orders of the family, strictly increasing.
    pub orders: Vec<u32>,
}

/// Why a [`Region`] builder call is refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionError(pub String);

impl fmt::Display for RegionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "region: {}", self.0)
    }
}

impl std::error::Error for RegionError {}

fn refuse<T>(message: impl Into<String>) -> Result<T, RegionError> {
    Err(RegionError(message.into()))
}

/// A bounded region of total operators (section 2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Region {
    name: String,
    pointer_bits: u32,
    leaves: BTreeMap<LeafName, ScalarTy>,
    nodes: Vec<RegionNode>,
    types: Vec<ScalarTy>,
    index: BTreeMap<RegionNode, NodeId>,
    order_free: Vec<OrderFree>,
    roots: Vec<NodeId>,
}

impl Region {
    /// An empty region named `name` in a module whose pointer width is
    /// `pointer_bits`.
    #[must_use]
    pub fn new(name: &str, pointer_bits: u32) -> Self {
        Self {
            name: name.to_owned(),
            pointer_bits,
            leaves: BTreeMap::new(),
            nodes: Vec::new(),
            types: Vec::new(),
            index: BTreeMap::new(),
            order_free: Vec::new(),
            roots: Vec::new(),
        }
    }

    /// The region's name (the derivation names it).
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The pointer width the region's `isize`/`usize` resolve against.
    #[must_use]
    pub fn pointer_bits(&self) -> u32 {
        self.pointer_bits
    }

    pub(crate) fn widths(&self) -> GraphWidths {
        GraphWidths::new(self.pointer_bits)
    }

    /// The declared leaves with their types, in leaf order.
    pub fn leaves(&self) -> impl Iterator<Item = (LeafName, ScalarTy)> + '_ {
        self.leaves.iter().map(|(leaf, ty)| (*leaf, *ty))
    }

    /// The roots, in order.
    #[must_use]
    pub fn roots(&self) -> &[NodeId] {
        &self.roots
    }

    /// The order-free nodes, in table order.
    #[must_use]
    pub fn order_free(&self) -> &[OrderFree] {
        &self.order_free
    }

    /// What `id` denotes.
    #[must_use]
    pub fn node(&self, id: NodeId) -> Option<&RegionNode> {
        self.nodes.get(id.index())
    }

    /// The type of `id`.
    #[must_use]
    pub fn ty(&self, id: NodeId) -> Option<ScalarTy> {
        self.types.get(id.index()).copied()
    }

    fn intern(&mut self, node: RegionNode, ty: ScalarTy) -> Result<NodeId, RegionError> {
        if let Some(found) = self.index.get(&node) {
            return Ok(*found);
        }
        let Ok(raw) = u32::try_from(self.nodes.len()) else {
            return refuse("too many nodes");
        };
        let id = NodeId(raw);
        self.nodes.push(node.clone());
        self.types.push(ty);
        self.index.insert(node, id);
        Ok(id)
    }

    /// Declare the leaf `leaf` of type `ty` and return its node. Declaring a
    /// leaf again with the same type returns the same node.
    ///
    /// # Errors
    /// A type that is not a graph type at this pointer width, or a leaf
    /// already declared with another type.
    pub fn leaf(&mut self, leaf: LeafName, ty: ScalarTy) -> Result<NodeId, RegionError> {
        if !self.widths().admits(ty) {
            return refuse(format!("{} is not a graph type here", ty.name()));
        }
        match self.leaves.get(&leaf) {
            Some(declared) if *declared != ty => {
                return refuse("a leaf declared with two types");
            }
            Some(_) => {}
            None => {
                self.leaves.insert(leaf, ty);
            }
        }
        self.intern(RegionNode::Leaf(leaf), ty)
    }

    /// `Const(ty, residue)`.
    ///
    /// # Errors
    /// A type that is not a graph type here, or a residue of `2^w` or more.
    pub fn constant(&mut self, ty: ScalarTy, residue: u128) -> Result<NodeId, RegionError> {
        let Some(width) = self.widths().width(ty) else {
            return refuse(format!("{} is not a graph type here", ty.name()));
        };
        if residue > mask(width) {
            return refuse("a constant residue that is not below 2^w");
        }
        self.intern(RegionNode::Const(ty, residue), ty)
    }

    /// The operator `desc` over `args`.
    ///
    /// # Errors
    /// An operator that is not admitted, the wrong arity, an unknown node or
    /// an operand of the wrong type.
    pub fn op(&mut self, desc: OpDesc, args: &[NodeId]) -> Result<NodeId, RegionError> {
        if !desc.admitted() || !self.widths().admits(desc.result_ty()) {
            return refuse(format!(
                "{} is not admitted at its types",
                desc.class_name()
            ));
        }
        if args.len() != desc.arity() {
            return refuse(format!("{} with the wrong arity", desc.class_name()));
        }
        for (position, arg) in args.iter().enumerate() {
            let Some(have) = self.ty(*arg) else {
                return refuse("an operand that names no node");
            };
            if desc.operand_ty(position) != Some(have) || !self.widths().admits(have) {
                return refuse(format!(
                    "operand {position} of {} has type {}",
                    desc.class_name(),
                    have.name()
                ));
            }
        }
        self.intern(RegionNode::Op(desc, args.to_vec()), desc.result_ty())
    }

    /// Whether `target` is `node` or one of its sub-terms.
    fn reaches(&self, node: NodeId, target: NodeId) -> bool {
        let mut seen = BTreeSet::new();
        let mut stack = vec![node];
        while let Some(next) = stack.pop() {
            if next == target {
                return true;
            }
            if !seen.insert(next) {
                continue;
            }
            if let Some(RegionNode::Op(_, args)) = self.node(next) {
                stack.extend(args.iter().copied());
            }
        }
        false
    }

    /// Make the declared leaf `leaf` the result of an order-free node over
    /// `operand` whose family is `orders` (section 2.3).
    ///
    /// # Errors
    /// `leaf` is not a leaf of an integer type or already is such a result;
    /// `operand` has another type or reaches `leaf`; `orders` is empty or
    /// not strictly increasing.
    pub fn make_order_free(
        &mut self,
        leaf: NodeId,
        operand: NodeId,
        orders: &[u32],
    ) -> Result<(), RegionError> {
        let Some(RegionNode::Leaf(_)) = self.node(leaf) else {
            return refuse("an order-free result that is not a leaf");
        };
        let Some(ty) = self.ty(leaf) else {
            return refuse("an order-free result that names no node");
        };
        if ty.is_bool() || self.ty(operand) != Some(ty) {
            return refuse("an order-free node needs one integer type for operand and result");
        }
        if self.order_free.iter().any(|entry| entry.leaf == leaf) {
            return refuse("a leaf that is the result of two order-free nodes");
        }
        if orders.is_empty() || orders.windows(2).any(|pair| pair[0] >= pair[1]) {
            return refuse("an order-free family that is empty or not strictly increasing");
        }
        // The operand of an entry reads only the results of earlier entries,
        // so the table is in dependency order and no node feeds itself.
        if self.reaches(operand, leaf) {
            return refuse("an order-free node that feeds itself");
        }
        if self
            .order_free
            .iter()
            .any(|entry| self.reaches(entry.operand, leaf))
        {
            return refuse("an order-free result that an earlier entry's operand reads");
        }
        self.order_free.push(OrderFree {
            leaf,
            operand,
            orders: orders.to_vec(),
        });
        Ok(())
    }

    /// Append a root.
    ///
    /// # Errors
    /// `node` names no node.
    pub fn root(&mut self, node: NodeId) -> Result<(), RegionError> {
        if self.node(node).is_none() {
            return refuse("a root that names no node");
        }
        self.roots.push(node);
        Ok(())
    }

    /// The order-free entry whose result is `leaf`, with its table index.
    pub(crate) fn order_free_of(&self, leaf: NodeId) -> Option<(usize, &OrderFree)> {
        self.order_free
            .iter()
            .enumerate()
            .find(|(_, entry)| entry.leaf == leaf)
    }

    /// The nodes the roots and the order-free table reach, oldest first
    /// (so children come before their parents).
    pub(crate) fn reachable(&self) -> Vec<NodeId> {
        let mut seen = BTreeSet::new();
        let mut stack: Vec<NodeId> = self.roots.clone();
        for entry in &self.order_free {
            stack.push(entry.leaf);
            stack.push(entry.operand);
        }
        while let Some(next) = stack.pop() {
            if !seen.insert(next) {
                continue;
            }
            if let Some(RegionNode::Op(_, args)) = self.node(next) {
                stack.extend(args.iter().copied());
            }
        }
        seen.into_iter().collect()
    }

    /// The nodes the roots reach, where an order-free result reaches its
    /// operand (it is computed from it).
    pub(crate) fn live(&self) -> BTreeSet<NodeId> {
        let mut seen = BTreeSet::new();
        let mut stack: Vec<NodeId> = self.roots.clone();
        while let Some(next) = stack.pop() {
            if !seen.insert(next) {
                continue;
            }
            match self.node(next) {
                Some(RegionNode::Op(_, args)) => stack.extend(args.iter().copied()),
                Some(RegionNode::Leaf(_)) => {
                    if let Some((_, entry)) = self.order_free_of(next) {
                        stack.push(entry.operand);
                    }
                }
                Some(RegionNode::Const(..)) | None => {}
            }
        }
        seen
    }

    /// The static cost of the region (section 5): every node the roots reach
    /// is priced once, whatever the number of its uses.
    #[must_use]
    pub fn cost(&self) -> u64 {
        let mut total = 0u64;
        for id in self.live() {
            let cost = match self.node(id) {
                Some(RegionNode::Op(desc, _)) => desc.cost(),
                Some(RegionNode::Const(..)) => CONST_COST,
                Some(RegionNode::Leaf(_)) if self.order_free_of(id).is_some() => REDUCTION_COST,
                Some(RegionNode::Leaf(_)) | None => 0,
            };
            total = total.saturating_add(cost);
        }
        total
    }

    /// The section 3 bytes: the declared leaves, the nodes the roots and the
    /// order-free table reach (children first, numbered by one depth-first
    /// traversal), the order-free table and the roots.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut number: BTreeMap<NodeId, u32> = BTreeMap::new();
        let mut order: Vec<NodeId> = Vec::new();
        let mut starts: Vec<NodeId> = Vec::new();
        for entry in &self.order_free {
            starts.push(entry.leaf);
            starts.push(entry.operand);
        }
        starts.extend(self.roots.iter().copied());
        for start in starts {
            let mut stack: Vec<(NodeId, bool)> = vec![(start, false)];
            while let Some((node, expanded)) = stack.pop() {
                if number.contains_key(&node) {
                    continue;
                }
                if expanded {
                    number.insert(node, u32::try_from(order.len()).unwrap_or(u32::MAX));
                    order.push(node);
                    continue;
                }
                stack.push((node, true));
                if let Some(RegionNode::Op(_, args)) = self.node(node) {
                    for arg in args.iter().rev() {
                        stack.push((*arg, false));
                    }
                }
            }
        }
        let numbered = |node: &NodeId| number.get(node).copied().unwrap_or(u32::MAX);

        let mut out = Vec::new();
        out.extend_from_slice(&REGION_MAGIC);
        put_u32(&mut out, REGION_FORMAT_VERSION);
        put_u32(&mut out, u32::try_from(self.name.len()).unwrap_or(u32::MAX));
        out.extend_from_slice(self.name.as_bytes());
        put_u32(&mut out, self.pointer_bits);
        put_u32(
            &mut out,
            u32::try_from(self.leaves.len()).unwrap_or(u32::MAX),
        );
        for (leaf, ty) in &self.leaves {
            put_leaf(&mut out, *leaf);
            out.push(ty.code());
        }
        put_u32(&mut out, u32::try_from(order.len()).unwrap_or(u32::MAX));
        for node in &order {
            match self.node(*node) {
                Some(RegionNode::Leaf(leaf)) => put_leaf(&mut out, *leaf),
                Some(RegionNode::Const(ty, residue)) => {
                    out.push(0x03);
                    out.push(ty.code());
                    out.extend_from_slice(&residue.to_le_bytes());
                }
                Some(RegionNode::Op(desc, args)) => {
                    out.push(0x04);
                    desc.encode(&mut out);
                    for arg in args {
                        put_u32(&mut out, numbered(arg));
                    }
                }
                None => {}
            }
        }
        put_u32(
            &mut out,
            u32::try_from(self.order_free.len()).unwrap_or(u32::MAX),
        );
        for entry in &self.order_free {
            put_u32(&mut out, numbered(&entry.leaf));
            put_u32(&mut out, numbered(&entry.operand));
            put_u32(
                &mut out,
                u32::try_from(entry.orders.len()).unwrap_or(u32::MAX),
            );
            for order in &entry.orders {
                put_u32(&mut out, *order);
            }
        }
        put_u32(
            &mut out,
            u32::try_from(self.roots.len()).unwrap_or(u32::MAX),
        );
        for root in &self.roots {
            put_u32(&mut out, numbered(root));
        }
        out
    }
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_leaf(out: &mut Vec<u8>, leaf: LeafName) {
    match leaf {
        LeafName::Param { block, index } => {
            out.push(0x01);
            put_u32(out, block);
            put_u32(out, index);
        }
        LeafName::Result {
            block,
            ordinal,
            index,
        } => {
            out.push(0x02);
            put_u32(out, block);
            put_u32(out, ordinal);
            put_u32(out, index);
        }
    }
}
