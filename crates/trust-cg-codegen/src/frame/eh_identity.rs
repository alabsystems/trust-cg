//! Preserve the exact Invoke and its exceptional edge across a frame split.
//! Planning is read-only; its owner publishes both sidecars with the CFG.

use super::*;

#[derive(Default)]
pub(super) struct Partition {
    pub(super) head_pads: Vec<BlockId>,
    pub(super) tail_pads: Vec<BlockId>,
    moved_sites: Vec<usize>,
    moved_bindings: Vec<usize>,
}

impl Partition {
    pub(super) fn retarget(
        self,
        sites: &mut [EhCallSiteEntry],
        bindings: &mut EhCallSiteBindings,
        tail: BlockId,
    ) {
        for index in self.moved_sites {
            sites[index].call_block = tail;
        }
        if let EhCallSiteBindings::ExactInstructions(bindings) = bindings {
            for index in self.moved_bindings {
                bindings[index].call_block = tail;
            }
        }
    }
}

pub(super) fn partition<I: Index<usize, Output = MachInst>>(
    insts: &I,
    sites: &[EhCallSiteEntry],
    bindings: &EhCallSiteBindings,
    block: BlockId,
    head: &[InstId],
    tail: &[InstId],
) -> Result<Partition, crate::lower::LowerError> {
    let fail = |detail: &str| {
        frame_insertion_error(format!(
            "stack probing cannot split EH-protected block {block:?}: {detail}"
        ))
    };
    let mut result = Partition::default();
    match bindings {
        EhCallSiteBindings::LegacyBlocks => {
            for (index, site) in sites
                .iter()
                .enumerate()
                .filter(|(_, site)| site.call_block == block)
            {
                let is_call = |id: &InstId| insts[id.0 as usize].flags.is_call();
                if !tail.iter().any(is_call) || head.iter().any(is_call) {
                    return Err(fail(
                        "its call would be separated from its landing-pad edge",
                    ));
                }
                result.moved_sites.push(index);
                if let Some(pad) = site.landing_pad_block {
                    result.tail_pads.push(pad);
                }
            }
        }
        EhCallSiteBindings::ExactInstructions(bindings) => {
            let mut matching_sites = sites
                .iter()
                .enumerate()
                .filter(|(_, site)| site.call_block == block && site.landing_pad_block.is_some());
            let site = matching_sites.next();
            let mut matching_bindings = bindings
                .iter()
                .enumerate()
                .filter(|(_, binding)| binding.call_block == block);
            let binding = matching_bindings.next();
            if matching_sites.next().is_some() || matching_bindings.next().is_some() {
                return Err(fail("duplicate handler or exact-call binding"));
            }
            match (site, binding) {
                (None, None) => return Ok(result),
                (Some(_), None) => return Err(fail("missing exact-call binding")),
                (None, Some(_)) => return Err(fail("orphan exact-call binding")),
                (Some((site_index, site)), Some((binding_index, binding))) => {
                    if site.landing_pad_block != Some(binding.landing_pad_block) {
                        return Err(fail("binding targets a different landing pad"));
                    }
                    let in_head = head.iter().filter(|&&id| id == binding.call_inst).count();
                    let in_tail = tail.iter().filter(|&&id| id == binding.call_inst).count();
                    if in_head + in_tail != 1 {
                        return Err(fail(
                            "protected instruction is not uniquely owned by this block",
                        ));
                    }
                    // Ownership proves the index is from the checked plan's
                    // instruction lists, not an unchecked sidecar reference.
                    if !matches!(
                        insts[binding.call_inst.0 as usize].opcode,
                        AArch64Opcode::Bl
                            | AArch64Opcode::BL
                            | AArch64Opcode::Blr
                            | AArch64Opcode::BLR
                    ) {
                        return Err(fail("protected instruction is not BL/BLR"));
                    }
                    if in_head == 1 {
                        result.head_pads.push(binding.landing_pad_block);
                    } else {
                        result.tail_pads.push(binding.landing_pad_block);
                        result.moved_sites.push(site_index);
                        result.moved_bindings.push(binding_index);
                    }
                }
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests;
