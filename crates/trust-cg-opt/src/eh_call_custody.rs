//! Calls whose exceptional continuation an instruction-changing pass must retain.
//!
//! This is a read-only snapshot, not an EH validator or an identity repair. Exact
//! selectors stay exact even when malformed; legacy rows conservatively protect
//! every live call in the named handler block. A callee name cannot mint custody.

use crate::fast_hash::FxHashSet;
use trust_cg_ir::function::EhCallSiteBindings;
use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction};

pub(crate) struct ProtectedCalls(FxHashSet<InstId>);

impl ProtectedCalls {
    pub(crate) fn collect(func: &MachFunction) -> Self {
        let mut calls = FxHashSet::default();
        match &func.eh_metadata.call_site_bindings {
            EhCallSiteBindings::ExactInstructions(bindings) => {
                calls.extend(bindings.iter().map(|binding| binding.call_inst));
            }
            EhCallSiteBindings::LegacyBlocks => {
                let mut blocks = FxHashSet::default();
                for site in &func.eh_metadata.call_sites {
                    if site.landing_pad_block.is_none() || !blocks.insert(site.call_block) {
                        continue;
                    }
                    if let Some(block) = func.blocks.get(site.call_block.0 as usize) {
                        for &id in &block.insts {
                            if func.insts.get(id.0 as usize).is_some_and(|inst| {
                                inst.is_call()
                                    || matches!(
                                        inst.opcode,
                                        AArch64Opcode::Bl
                                            | AArch64Opcode::Blr
                                            | AArch64Opcode::BL
                                            | AArch64Opcode::BLR
                                    )
                            }) {
                                calls.insert(id);
                            }
                        }
                    }
                }
            }
        }
        Self(calls)
    }

    pub(crate) fn contains(&self, id: InstId) -> bool {
        self.0.contains(&id)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Calls that leave their block in the middle: an exception the callee raises
/// leaves at the call for a landing pad of this function, so nothing the block
/// computes after the call runs on that path.
///
/// Facts that credit a whole block to its successors are false on that edge.
/// A def placed after such a call dominates the landing pad by block, yet the
/// pad never sees it; a pass that reuses it there reads whatever the register
/// held when the callee threw. Passes treat each of these calls as a mid-block
/// exit, as they treat a conditional branch in a switch cascade.
///
/// The set is a fail-closed superset of [`ProtectedCalls`]: it also takes
/// every call (by flag or by call opcode) in a block that an EH row names as
/// an invoke block, or whose successors include a landing pad, so a custody
/// record that drifted from its call cannot hide an exception edge.
pub(crate) struct UnwindExits {
    calls: FxHashSet<InstId>,
    blocks: FxHashSet<BlockId>,
}

impl UnwindExits {
    pub(crate) fn collect(func: &MachFunction) -> Self {
        let mut calls = FxHashSet::default();
        let mut blocks = FxHashSet::default();
        let eh = &func.eh_metadata;
        if !eh.has_eh_info() {
            return Self { calls, blocks };
        }
        let protected = ProtectedCalls::collect(func);
        let mut pads: FxHashSet<BlockId> = eh.landing_pads.iter().map(|pad| pad.block).collect();
        let mut invoke_blocks: FxHashSet<BlockId> = FxHashSet::default();
        for site in &eh.call_sites {
            if let Some(pad) = site.landing_pad_block {
                pads.insert(pad);
                invoke_blocks.insert(site.call_block);
            }
        }
        if let EhCallSiteBindings::ExactInstructions(bindings) = &eh.call_site_bindings {
            for binding in bindings {
                pads.insert(binding.landing_pad_block);
                invoke_blocks.insert(binding.call_block);
            }
        }
        for (index, block) in func.blocks.iter().enumerate() {
            let block_id = BlockId(index as u32);
            let exceptional = invoke_blocks.contains(&block_id)
                || block.succs.iter().any(|succ| pads.contains(succ));
            for &id in &block.insts {
                let is_call = func
                    .insts
                    .get(id.0 as usize)
                    .is_some_and(|inst| inst.is_call() || inst.opcode.default_flags().is_call());
                if protected.contains(id) || (exceptional && is_call) {
                    calls.insert(id);
                    blocks.insert(block_id);
                }
            }
        }
        Self { calls, blocks }
    }

    /// Whether `id` is a call an exception can leave its block through.
    pub(crate) fn contains(&self, id: InstId) -> bool {
        self.calls.contains(&id)
    }

    /// Whether `block` holds such a call: code placed after it does not run on
    /// every path out of the block.
    pub(crate) fn leaves_mid_block(&self, block: BlockId) -> bool {
        self.blocks.contains(&block)
    }
}

#[cfg(test)]
pub(crate) mod tests;
