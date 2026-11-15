// Author: Andrew Yates | Copyright 2026 | License: Apache-2.0

//! Sparse selected-invoke custody; no LIR/source identity-format change.

use super::*;
use trust_cg_ir::function::{EhCallSiteBindings, EhInvokeBinding};
use trust_cg_ir::{BlockId, InstId};

/// The exact append coordinate returned by the canonical call emitter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ISelEhInvokeBinding {
    /// The source invoke's selected block.
    pub call_block: Block,
    /// The exact append index returned by direct-call emission.
    pub call_index: usize,
    /// The source invoke's exceptional destination.
    pub landing_pad_block: Block,
}

impl ISelFunction {
    pub(super) fn validate_eh_invoke_bindings(&self) -> Result<(), ISelError> {
        if self.eh_info.call_sites.is_empty() && self.eh_invoke_bindings.is_empty() {
            return Ok(());
        }
        let refuse = |reason: String| ISelError::InvalidEhMetadata(reason);
        let laid_out: HashSet<Block> = self.block_order.iter().copied().collect();
        let mut required = HashMap::default();
        for site in &self.eh_info.call_sites {
            if required
                .insert(site.call_block, site.landing_pad_block)
                .is_some()
            {
                return Err(refuse(format!(
                    "duplicate Invoke handler row for {:?}",
                    site.call_block
                )));
            }
        }
        let mut coordinates = HashSet::default();
        for binding in &self.eh_invoke_bindings {
            if !coordinates.insert((binding.call_block, binding.call_index)) {
                return Err(refuse(format!(
                    "duplicate selected Invoke binding {binding:?}"
                )));
            }
            if required.remove(&binding.call_block) != Some(binding.landing_pad_block) {
                return Err(refuse(format!(
                    "orphan or mismatched selected Invoke binding {binding:?}"
                )));
            }
            if !laid_out.contains(&binding.call_block)
                || !laid_out.contains(&binding.landing_pad_block)
            {
                return Err(refuse(format!(
                    "selected Invoke binding escapes block_order: {binding:?}"
                )));
            }
            let selected = self
                .blocks
                .get(&binding.call_block)
                .and_then(|block| block.insts.get(binding.call_index));
            if !selected.is_some_and(|inst| inst.opcode == AArch64Opcode::Bl) {
                return Err(refuse(format!(
                    "selected Invoke binding does not identify its emitted BL: {binding:?}"
                )));
            }
        }
        if !required.is_empty() {
            return Err(refuse(
                "Invoke handler row is missing its selected call binding".to_owned(),
            ));
        }
        Ok(())
    }

    pub(super) fn machine_eh_call_bindings(
        &self,
        converted: &HashMap<(Block, usize), Option<InstId>>,
    ) -> EhCallSiteBindings {
        if self.eh_info.is_empty() && self.eh_invoke_bindings.is_empty() {
            return EhCallSiteBindings::LegacyBlocks;
        }
        let mut bindings = Vec::with_capacity(self.eh_invoke_bindings.len());
        for source in &self.eh_invoke_bindings {
            let mapped = converted
                .get(&(source.call_block, source.call_index))
                .copied()
                .flatten();
            let binding = EhInvokeBinding {
                call_inst: mapped.unwrap_or(InstId(u32::MAX)),
                call_block: BlockId(source.call_block.0),
                landing_pad_block: BlockId(source.landing_pad_block.0),
            };
            bindings.push(binding);
            if mapped.is_none() {
                // `to_ir_func` is an existing infallible public projection.
                // Keep malformed coordinates as refusal evidence, not dropped
                // data or a legacy-mode request. The duplicate guarantees
                // rejection even for a hypothetical full-u32 arena where the
                // sentinel ID itself could be in range. Checked finalizers
                // refuse the original coordinate before this projection.
                bindings.push(binding);
            }
        }
        EhCallSiteBindings::ExactInstructions(bindings)
    }
}
