//! Remove valid unreachable Invoke custody with its semantic handler only.

use super::*;
use trust_cg_ir::function::{EhCallSiteBindings, EhEdgeCensus, EhInvokeBinding};

pub(super) fn prunable_bindings(
    func: &MachFunction,
    reachable: &HashSet<BlockId>,
) -> Option<HashSet<EhInvokeBinding>> {
    let EhCallSiteBindings::ExactInstructions(bindings) = &func.eh_metadata.call_site_bindings
    else {
        return Some(HashSet::default());
    };
    // Conservative deletion planning, not an EH acceptance verdict. If custody
    // is incomplete, retain ALL metadata for the actual pipeline validator.
    let mut sites: HashMap<BlockId, BlockId> = HashMap::default();
    for site in &func.eh_metadata.call_sites {
        if let Some(pad) = site.landing_pad_block
            && sites.insert(site.call_block, pad).is_some()
        {
            return None;
        }
    }
    if sites.len() != bindings.len() {
        return None;
    }
    if bindings.is_empty() {
        return Some(HashSet::default());
    }
    let mut wanted = HashMap::default();
    let mut call_blocks = HashSet::default();
    for binding in bindings {
        if sites.get(&binding.call_block) != Some(&binding.landing_pad_block)
            || !call_blocks.insert(binding.call_block)
            || wanted
                .insert(binding.call_inst, binding.call_block)
                .is_some()
        {
            return None;
        }
    }
    // Scan the old layout once, retaining aliases across two dead blocks as
    // refusal evidence. No repeated handler/body scans or second persistent IR.
    let mut seen = HashSet::default();
    let mut laid_out = HashSet::default();
    let mut edges = EhEdgeCensus::for_handlers(&func.eh_metadata.call_sites);
    for &block_id in &func.block_order {
        if !laid_out.insert(block_id) {
            return None;
        }
        let block = func.blocks.get(block_id.0 as usize)?;
        edges.observe_block(block_id, block);
        for &id in &block.insts {
            if let Some(&owner) = wanted.get(&id)
                && (owner != block_id || !seen.insert(id))
            {
                return None;
            }
        }
    }
    if seen.len() != wanted.len() {
        return None;
    }
    let mut pads: HashMap<BlockId, usize> = HashMap::default();
    for pad in &func.eh_metadata.landing_pads {
        *pads.entry(pad.block).or_default() += 1;
    }
    for binding in bindings {
        let inst = func.insts.get(binding.call_inst.0 as usize)?;
        if inst.is_pseudo()
            || !matches!(
                inst.opcode,
                AArch64Opcode::Bl | AArch64Opcode::BL | AArch64Opcode::Blr | AArch64Opcode::BLR
            )
            || !laid_out.contains(&binding.landing_pad_block)
            || pads.get(&binding.landing_pad_block) != Some(&1)
            || edges.counts(binding.call_block, binding.landing_pad_block) != (1, 1)
        {
            return None;
        }
    }
    Some(
        bindings
            .iter()
            .copied()
            .filter(|binding| !reachable.contains(&binding.call_block))
            .collect(),
    )
}

#[cfg(test)]
mod tests;
