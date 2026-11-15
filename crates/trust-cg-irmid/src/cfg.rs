// trust-cg-irmid/cfg.rs - a trust-ir function as trust-cg-opt's MachIrView
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`TrustIrCfg`] presents a `trust_ir::Function` through
//! `trust_cg_opt::mach_view::MachIrView`, so the mid-end's CFG questions
//! (reachability, reverse postorder, dominators, natural loops) are answered
//! by the one generic `CfgAnalysis` the native optimizers already share. The
//! trait and the function type live in other crates, hence the newtype.
//!
//! Successors are the terminator's `successor_edges` (normal and unwind
//! edges), each target once, in edge order. A trust-ir value is not a virtual
//! register, so `defined_vreg` answers `None`: the view is for CFG analyses,
//! not for register-level queries.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::VReg;
use trust_cg_opt::mach_view::{
    CfgAnalysis, MachIrView, compute_idom, compute_rpo, predecessor_map,
};
use trust_ir::{BlockId, Function, Inst, InstrNode};

/// A trust-ir function viewed as a machine-IR CFG.
pub struct TrustIrCfg<'f> {
    func: &'f Function,
    index: HashMap<BlockId, usize>,
    /// Each block's successors, deduplicated once: the generic walks ask for
    /// a block's successors once per edge they follow, and a `switch` may
    /// have tens of thousands.
    succs: Vec<Vec<BlockId>>,
}

impl<'f> TrustIrCfg<'f> {
    pub fn new(func: &'f Function) -> Self {
        let index = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let succs = func
            .blocks
            .iter()
            .map(|b| {
                let mut seen = HashSet::new();
                b.body
                    .last()
                    .map(|n| n.inst.successor_edges())
                    .unwrap_or_default()
                    .into_iter()
                    .map(|edge| edge.target)
                    .filter(|target| seen.insert(*target))
                    .collect()
            })
            .collect();
        Self { func, index, succs }
    }

    /// The generic CFG analysis of this function.
    pub fn analysis(&self) -> CfgAnalysis<BlockId> {
        CfgAnalysis::compute(self)
    }

    /// The reachable blocks in reverse postorder.
    pub(crate) fn rpo(&self) -> Vec<BlockId> {
        compute_rpo(self)
    }

    /// The reachable blocks in reverse postorder and their immediate
    /// dominators (the entry its own), as [`TrustIrCfg::analysis`] computes
    /// them, without its natural-loop discovery.
    pub(crate) fn rpo_and_idom(&self) -> (Vec<BlockId>, HashMap<BlockId, BlockId>) {
        let preds = predecessor_map(self);
        let rpo = compute_rpo(self);
        let idom = compute_idom(self, &preds, &rpo);
        (rpo, idom.into_iter().collect())
    }

    fn node(&self, block: BlockId, idx: usize) -> Option<&'f InstrNode> {
        let func: &'f Function = self.func;
        self.index
            .get(&block)
            .and_then(|&i| func.blocks[i].body.get(idx))
    }

    fn inst(&self, block: BlockId, idx: usize) -> Option<&'f Inst> {
        self.node(block, idx).map(|n| &n.inst)
    }
}

impl MachIrView for TrustIrCfg<'_> {
    type Block = BlockId;

    fn ir_name(&self) -> &'static str {
        "trust-ir/Function"
    }

    fn entry_block(&self) -> Self::Block {
        self.func.entry
    }

    fn layout_order(&self) -> Vec<Self::Block> {
        self.func.blocks.iter().map(|b| b.id).collect()
    }

    fn block_index(&self, block: Self::Block) -> u32 {
        block.index()
    }

    fn successors(&self, block: Self::Block) -> Vec<Self::Block> {
        self.index
            .get(&block)
            .map(|&i| self.succs[i].clone())
            .unwrap_or_default()
    }

    fn inst_count(&self, block: Self::Block) -> usize {
        self.index
            .get(&block)
            .map_or(0, |&i| self.func.blocks[i].body.len())
    }

    fn is_branch(&self, block: Self::Block, idx: usize) -> bool {
        self.inst(block, idx)
            .is_some_and(|inst| !inst.successor_edges().is_empty())
    }

    fn is_terminator(&self, block: Self::Block, idx: usize) -> bool {
        self.inst(block, idx).is_some_and(Inst::is_terminator)
    }

    fn is_conditional_branch(&self, block: Self::Block, idx: usize) -> bool {
        matches!(
            self.inst(block, idx),
            Some(Inst::CondBr { .. } | Inst::Switch { .. })
        )
    }

    fn is_unconditional_branch(&self, block: Self::Block, idx: usize) -> bool {
        matches!(self.inst(block, idx), Some(Inst::Br { .. }))
    }

    fn is_return(&self, block: Self::Block, idx: usize) -> bool {
        matches!(self.inst(block, idx), Some(Inst::Return { .. }))
    }

    fn has_side_effects(&self, block: Self::Block, idx: usize) -> bool {
        self.inst(block, idx).is_none_or(Inst::has_side_effects)
    }

    fn defined_vreg(&self, _block: Self::Block, _idx: usize) -> Option<VReg> {
        None
    }

    fn branch_targets(&self, block: Self::Block, idx: usize) -> Vec<Self::Block> {
        let mut seen = HashSet::new();
        self.inst(block, idx)
            .map(Inst::successor_edges)
            .unwrap_or_default()
            .into_iter()
            .map(|edge| edge.target)
            .filter(|target| seen.insert(*target))
            .collect()
    }
}
