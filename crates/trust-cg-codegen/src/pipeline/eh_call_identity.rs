// Author: Andrew Yates | Copyright 2026 | License: Apache-2.0

//! Actual machine-owner checks for modern selected-invoke identities.

use super::*;
use trust_cg_ir::function::{EhCallSiteBindings, EhInvokeBinding, MachBlock};

/// Prepare the exact lookup once. Handler rows, not synthesized filler rows,
/// own the required key set. Legacy mode retains its strict block-only rule.
pub(super) fn exact_calls(
    func: &IrMachFunction,
) -> Result<Option<HashMap<BlockId, InstId>>, String> {
    let EhCallSiteBindings::ExactInstructions(bindings) = &func.eh_metadata.call_site_bindings
    else {
        return Ok(None);
    };
    let mut required = HashMap::new();
    for site in &func.eh_metadata.call_sites {
        if let Some(pad) = site.landing_pad_block
            && required.insert(site.call_block, pad).is_some()
        {
            return Err(format!(
                "EH call block {:?} has duplicate semantic handler rows",
                site.call_block
            ));
        }
    }
    let mut exact = HashMap::with_capacity(bindings.len());
    let mut wanted = HashMap::with_capacity(bindings.len());
    for binding in bindings {
        if exact
            .insert(binding.call_block, binding.call_inst)
            .is_some()
            || wanted
                .insert(binding.call_inst, binding.call_block)
                .is_some()
        {
            return Err(format!("duplicate exact Invoke binding {binding:?}"));
        }
        if required.get(&binding.call_block) != Some(&binding.landing_pad_block) {
            return Err(format!(
                "orphan or mismatched exact Invoke binding {binding:?}"
            ));
        }
        if func
            .blocks
            .get(binding.landing_pad_block.0 as usize)
            .is_none()
        {
            return Err(format!(
                "exact Invoke binding names missing landing pad {binding:?}"
            ));
        }
        let inst = func
            .insts
            .get(binding.call_inst.0 as usize)
            .ok_or_else(|| format!("exact Invoke binding names missing instruction {binding:?}"))?;
        if inst.is_pseudo()
            || !matches!(
                inst.opcode,
                IrOpcode::Bl | IrOpcode::BL | IrOpcode::Blr | IrOpcode::BLR
            )
        {
            return Err(format!(
                "exact Invoke binding does not identify an encoded BL/BLR call: {binding:?}"
            ));
        }
    }
    if exact.len() != required.len() {
        return Err("semantic handler row is missing its exact selected Invoke binding".to_owned());
    }
    if bindings.is_empty() {
        return Ok(Some(exact));
    }
    // One scan of the actual layout establishes unique ownership. Only the
    // selected IDs occupy this map, rather than duplicating the whole arena.
    let mut seen = BTreeSet::new();
    let mut laid_out = BTreeSet::new();
    for &block_id in &func.block_order {
        if !laid_out.insert(block_id) {
            return Err(format!(
                "block_order duplicates exact Invoke owner {block_id:?}"
            ));
        }
        let block = func
            .blocks
            .get(block_id.0 as usize)
            .ok_or_else(|| format!("block_order names missing exact Invoke owner {block_id:?}"))?;
        for &inst_id in &block.insts {
            if let Some(&owner) = wanted.get(&inst_id)
                && (owner != block_id || !seen.insert(inst_id))
            {
                return Err(format!(
                    "exact Invoke instruction {inst_id:?} is not uniquely owned by {owner:?}"
                ));
            }
        }
    }
    if seen.len() != wanted.len() {
        return Err(
            "exact Invoke instruction is detached or its owner is absent from block_order"
                .to_owned(),
        );
    }
    for binding in bindings {
        if !laid_out.contains(&binding.landing_pad_block) {
            return Err(format!(
                "exact Invoke landing pad is absent from block_order: {binding:?}"
            ));
        }
    }
    Ok(Some(exact))
}

/// The machine-to-allocator adapter emits the original arena one-for-one in
/// index order. Allocator insertions append and deletions tombstone; this set
/// selects those exact original slots, not a matching opcode or callee.
pub(super) fn original_call_indices(bindings: &EhCallSiteBindings) -> Option<BTreeSet<usize>> {
    match bindings {
        EhCallSiteBindings::LegacyBlocks => None,
        EhCallSiteBindings::ExactInstructions(bindings) => Some(
            bindings
                .iter()
                .map(|binding| binding.call_inst.0 as usize)
                .collect(),
        ),
    }
}

pub(super) fn protected_regalloc_original<'a>(
    originals: &'a [IrMachInst],
    original_index: usize,
    opcode: IrOpcode,
    operands: &[IrOperand],
) -> Result<&'a IrMachInst, String> {
    let original = originals
        .get(original_index)
        .ok_or_else(|| format!("protected Invoke original slot {original_index} is absent"))?;
    if original.opcode != opcode
        || !matches!(
            opcode,
            IrOpcode::Bl | IrOpcode::BL | IrOpcode::Blr | IrOpcode::BLR
        )
    {
        return Err(format!(
            "protected Invoke original slot {original_index} changed call opcode during register allocation"
        ));
    }
    // Identity is already fixed by the adapter-issued slot. Use the existing
    // operand transport contract only to validate allocation/split registers
    // and Imm(0) opaque placeholders, never to search for an original call.
    if !regalloc_rebuilt_operands_match_original(operands, original)
        && !regalloc_rebuilt_operands_match_original_loose(operands, original)
    {
        return Err(format!(
            "protected Invoke original slot {original_index} changed call target/operand transport during register allocation"
        ));
    }
    Ok(original)
}

/// Remap only the authoritative original-slot -> allocator-slot -> rebuilt-ID
/// chain, before publishing the new arena. No loose/scan matching participates
/// in protected-call custody. Unrelated instructions keep their existing
/// opaque-operand reconstruction policy.
pub(super) fn remap_regalloc_bindings(
    bindings: &EhCallSiteBindings,
    originals: &[IrMachInst],
    ra: &trust_cg_regalloc::RegAllocFunction,
    map: &[Option<InstId>],
    rebuilt: &[IrMachInst],
    blocks: &[MachBlock],
) -> Result<EhCallSiteBindings, String> {
    let EhCallSiteBindings::ExactInstructions(bindings) = bindings else {
        return Ok(EhCallSiteBindings::LegacyBlocks);
    };
    if bindings.is_empty() {
        return Ok(EhCallSiteBindings::ExactInstructions(Vec::new()));
    }
    let mut remapped = Vec::with_capacity(bindings.len());
    let mut wanted = HashMap::with_capacity(bindings.len());
    for binding in bindings {
        let original_index = binding.call_inst.0 as usize;
        let original = originals
            .get(original_index)
            .ok_or_else(|| format!("protected Invoke original slot {original_index} is absent"))?;
        let allocated = ra
            .insts
            .get(original_index)
            .ok_or_else(|| format!("protected Invoke allocator slot {original_index} is absent"))?;
        if allocated.opcode != original.opcode as u16 {
            return Err(format!(
                "protected Invoke allocator slot {original_index} was deleted or substituted"
            ));
        }
        let call_inst = map.get(original_index).copied().flatten().ok_or_else(|| {
            format!("protected Invoke allocator slot {original_index} has no rebuilt ID")
        })?;
        let call = rebuilt
            .get(call_inst.0 as usize)
            .ok_or_else(|| format!("protected Invoke rebuilt ID {call_inst:?} is absent"))?;
        if call.opcode != original.opcode || call.is_pseudo() {
            return Err(format!(
                "protected Invoke rebuilt ID {call_inst:?} changed call shape"
            ));
        }
        if wanted.insert(call_inst, binding.call_block).is_some() {
            return Err(format!(
                "protected Invoke rebuilt ID {call_inst:?} is duplicated"
            ));
        }
        remapped.push(EhInvokeBinding {
            call_inst,
            ..*binding
        });
    }
    let mut seen = BTreeSet::new();
    let mut laid_out = BTreeSet::new();
    for &block_id in &ra.block_order {
        if !laid_out.insert(block_id) {
            return Err(format!(
                "allocator layout duplicates Invoke owner {block_id:?}"
            ));
        }
        let block = blocks
            .get(block_id.0 as usize)
            .ok_or_else(|| format!("allocator layout names missing Invoke owner {block_id:?}"))?;
        for &inst_id in &block.insts {
            if let Some(&owner) = wanted.get(&inst_id)
                && (owner != block_id || !seen.insert(inst_id))
            {
                return Err(format!(
                    "rebuilt Invoke {inst_id:?} lost unique owner {owner:?}"
                ));
            }
        }
    }
    if seen.len() != wanted.len() {
        return Err("a rebuilt Invoke is detached or its owner is unlaid-out".to_owned());
    }
    if remapped
        .iter()
        .any(|binding| !laid_out.contains(&binding.landing_pad_block))
    {
        return Err("a rebuilt Invoke landing pad is unlaid-out".to_owned());
    }
    Ok(EhCallSiteBindings::ExactInstructions(remapped))
}
