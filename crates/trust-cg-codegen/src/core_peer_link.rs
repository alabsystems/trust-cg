// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Checked final-link custody for the bounded ordinary defined-peer entry.
//! Original symbolic inventory remains retained. The final caller certificate
//! is produced from the actual patched words and complete conditional proof;
//! no pre-patch certificate is rebound to changed bytes.

use super::*;
use sha2::{Digest, Sha256};
use trust_cg_verify::aarch64_affine_lowering::{
    CheckedDefinedPeerCall, ConditionalPeerEntryRequirement, ConditionallyReplayedDefinedPeer,
};
use trust_cg_verify::aarch64_static_frame::{SavedFrameRegister, StaticFrameLayoutClaim};

pub(super) struct CoreCheckedPeerLink {
    replay: ConditionallyReplayedDefinedPeer,
    original_fixup: CoreAddressFreeFixup,
    inventory_digest: Option<trust_ir::proof::ProofDigest>,
    original_caller: trust_cg_verify::CapturedFunctionVerificationReport,
    original_caller_bytes: Vec<u8>,
    ranges: Vec<(trust_ir::FuncId, String, std::ops::Range<usize>)>,
}

fn digest(bytes: &[u8]) -> trust_ir::proof::ProofDigest {
    trust_ir::proof::ProofDigest::sha256(Sha256::digest(bytes).into())
}

fn append_function(
    image: &mut Vec<u8>,
    name: &str,
    bytes: &[u8],
    alignment: u8,
) -> Result<std::ops::Range<usize>, String> {
    if alignment > 12 || bytes.is_empty() || bytes.len() % 4 != 0 {
        return Err("unsupported final peer function extent/alignment".into());
    }
    let align = 1usize << alignment.max(2);
    let padding = (align - image.len() % align) % align;
    image
        .try_reserve(
            padding
                .checked_add(bytes.len())
                .ok_or("final peer extent overflow")?,
        )
        .map_err(|e| e.to_string())?;
    for _ in 0..padding / 4 {
        image.extend_from_slice(&0xd503201fu32.to_le_bytes());
    }
    let start = image.len();
    image.extend_from_slice(bytes);
    if name.is_empty() {
        return Err("empty final peer symbol".into());
    }
    Ok(start..image.len())
}

/// Stream only the actual final caller beside the already checked compact
/// callee. No second compiler, function-graph collection, request or budget.
pub(super) fn prepare(
    verification: &CoreSourceVerification<'_>,
    caller: trust_ir::FuncId,
    lir: &trust_cg_lower::Function,
    machine: &trust_cg_ir::MachFunction,
    original_code: &[u8],
    layout: Option<&crate::frame::FrameLayout>,
    previous: &[CoreAddressFreeMachineFunction],
    fixups: &[CoreAddressFreeFixup],
    original: &trust_cg_verify::CapturedFunctionVerificationReport,
    retained_lir: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
) -> Result<(Vec<u8>, CoreCheckedPeerLink), String> {
    let module = verification.source.original();
    if module.functions.len() != 2
        || previous.len() != 1
        || original_code.len() != 20
        || fixups.len() != 1
    {
        return Err("conditional peer requires exactly one actual earlier callee and one final caller/fixup".into());
    }
    let previous = &previous[0];
    let fixup = fixups[0];
    if fixup.caller != caller
        || fixup.function_ordinal != 1
        || fixup.offset != 8
        || fixup.target
            != (CoreAddressFreeFixupTarget::ExactModuleFunction {
                function: previous.source_function,
            })
        || original_code[8..12] != 0x94000000u32.to_le_bytes()
        || original.report().emitted_opcode_inventory().is_promotable()
    {
        return Err("original caller/fixup/refusal identity differs".into());
    }
    let layout = layout.ok_or("missing actual producer frame layout")?;
    if layout.total_frame_size != 16
        || layout.callee_saved_area_size != 16
        || layout.spill_area_size != 0
        || layout.local_area_size != 0
        || layout.outgoing_arg_area_size != 0
        || !layout.uses_frame_pointer
        || layout.is_leaf
        || layout.uses_red_zone
        || layout.has_dynamic_alloc
        || layout.callee_saved_pairs.len() != 1
        || layout
            .callee_saved_pairs
            .iter()
            .any(|p| p.is_fpr || p.reg1.encoding() > 31 || p.reg2.encoding() > 31)
    {
        return Err("actual producer frame is outside the bounded peer domain".into());
    }
    let claim = StaticFrameLayoutClaim {
        saved_pairs: layout
            .callee_saved_pairs
            .iter()
            .map(|p| {
                [
                    SavedFrameRegister::X(p.reg1.encoding() as u8),
                    SavedFrameRegister::X(p.reg2.encoding() as u8),
                ]
            })
            .collect(),
        callee_saved_bytes: layout.callee_saved_area_size,
        stack_slot_bytes: layout.spill_area_size,
        outgoing_argument_bytes: layout.outgoing_arg_area_size,
        total_bytes: layout.total_frame_size,
        uses_frame_pointer: layout.uses_frame_pointer,
        dynamic_allocation: layout.has_dynamic_alloc,
        red_zone: layout.uses_red_zone,
        slot_fp_offsets: vec![],
    };
    let mut image = Vec::new();
    let callee_range = append_function(
        &mut image,
        &previous.name,
        &previous.code,
        previous.text_align_log2,
    )?;
    let caller_range = append_function(
        &mut image,
        &machine.name,
        original_code,
        machine.text_align_log2,
    )?;
    let site = caller_range
        .start
        .checked_add(fixup.offset as usize)
        .ok_or("final peer site overflow")?;
    let displacement = i64::try_from(callee_range.start)
        .ok()
        .and_then(|target| {
            i64::try_from(site)
                .ok()
                .and_then(|pc| target.checked_sub(pc))
        })
        .ok_or("final peer displacement overflow")?;
    // Existing checked signed Branch26 arithmetic; no new encoder or veneer.
    let selected: &mut [u8; 4] = image
        .get_mut(site..site + 4)
        .ok_or("final peer site extent")?
        .try_into()
        .map_err(|_| "final peer site width")?;
    crate::macho::fixup::apply_branch26(selected, displacement).map_err(|e| e.to_string())?;
    let summary = previous
        .defined_callee
        .as_ref()
        .map_err(|e| e.to_string())?
        .as_ref()
        .ok_or("genuine callee summary missing")?;
    let mut matches = retained_lir.iter().filter(|(f, _)| f.name == previous.name);
    let callee_lir = &matches.next().ok_or("retained callee LIR missing")?.0;
    if matches.next().is_some() {
        return Err("ambiguous retained callee LIR".into());
    }
    let attached = summary
        .attach(
            &verification.source,
            &verification.request,
            previous.source_function,
            callee_lir,
            &image[callee_range.clone()],
        )
        .map_err(|e| e.to_string())?;
    let peer = CheckedDefinedPeerCall::bind(
        &verification.source,
        &verification.request,
        original,
        caller,
        lir,
        machine,
        &image,
        caller_range.start,
        callee_range.start,
        &attached,
        &claim,
    )
    .map_err(|e| e.to_string())?;
    let replay = crate::jit_cert::run_on_proof_verifier_stack(
        "trust-cg-core-defined-peer-proof-verifier",
        || {
            shared_aarch64_function_verifier().verify_checked_defined_peer(
                machine,
                lir,
                &verification.source,
                &verification.request,
                peer,
            )
        },
    )
    .map_err(|e| e.to_string())?;
    let code = image[caller_range.clone()].to_vec();
    let link = CoreCheckedPeerLink {
        replay,
        original_fixup: fixup,
        inventory_digest: None,
        original_caller: original.clone(),
        original_caller_bytes: original_code.to_vec(),
        ranges: vec![
            (
                previous.source_function,
                previous.name.clone(),
                callee_range,
            ),
            (caller, machine.name.clone(), caller_range),
        ],
    };
    Ok((code, link))
}

impl CoreCheckedPeerLink {
    pub(super) fn bind_inventory(
        &mut self,
        inventory: &CoreAddressFreeFixupInventory,
    ) -> Result<(), String> {
        if inventory.entries.as_slice() != [self.original_fixup] {
            return Err("complete original peer fixup inventory differs".into());
        }
        self.inventory_digest = Some(inventory.digest);
        Ok(())
    }
    pub(super) fn replay(&self) -> &ConditionallyReplayedDefinedPeer {
        &self.replay
    }
    pub(super) fn requirement(&self) -> &ConditionalPeerEntryRequirement {
        self.replay.requirement()
    }
    pub(super) fn check_prepared(
        &self,
        module: &trust_ir::Module,
        previous: &[CoreAddressFreeMachineFunction],
        caller: trust_ir::FuncId,
        name: &str,
        alignment: u8,
        code: &[u8],
        inventory: &CoreAddressFreeFixupInventory,
    ) -> Result<(), String> {
        if self.inventory_digest != Some(inventory.digest)
            || inventory.entries.as_slice() != [self.original_fixup]
            || previous.len() != 1
            || caller != self.requirement().function()
        {
            return Err("conditional original inventory/caller changed".into());
        }
        let mut image = Vec::new();
        let mut ranges = Vec::new();
        for function in previous {
            ranges.push((
                function.source_function,
                function.name.clone(),
                append_function(
                    &mut image,
                    &function.name,
                    &function.code,
                    function.text_align_log2,
                )?,
            ));
        }
        ranges.push((
            caller,
            name.into(),
            append_function(&mut image, name, code, alignment)?,
        ));
        if ranges != self.ranges {
            return Err("conditional final layout changed".into());
        }
        self.requirement()
            .check_entry_binding(module, caller, code, &image)
            .map_err(|e| e.to_string())
    }
    pub(super) fn check(
        &self,
        artifact: &CoreAddressFreeMachineArtifact,
        source: &CoreCompilationSource,
    ) -> Result<(), String> {
        if self.inventory_digest != Some(artifact.fixup_inventory.digest)
            || artifact.fixup_inventory.entries.as_slice() != [self.original_fixup]
            || self
                .original_caller
                .report()
                .emitted_opcode_inventory()
                .is_promotable()
            || self.original_caller_bytes.get(8..12) != Some(0x94000000u32.to_le_bytes().as_slice())
        {
            return Err("original peer inventory/refusal custody differs".into());
        }
        let mut image = Vec::new();
        let mut ranges = Vec::new();
        for function in &artifact.functions {
            let range = append_function(
                &mut image,
                &function.name,
                &function.code,
                function.text_align_log2,
            )?;
            ranges.push((function.source_function, function.name.clone(), range));
        }
        if ranges != self.ranges {
            return Err("final peer placements differ".into());
        }
        let caller = artifact
            .functions
            .iter()
            .find(|f| f.source_function == self.replay.requirement().function())
            .ok_or("final peer caller missing")?;
        self.replay
            .requirement()
            .check_entry_binding(&source.module, caller.source_function, &caller.code, &image)
            .map_err(|e| e.to_string())
    }
    pub(super) fn check_running_image(&self, image: &[u8]) -> Result<(), String> {
        if digest(image) != self.replay.requirement().final_image_digest() {
            return Err("installed peer image differs from exact final proof".into());
        }
        Ok(())
    }
    pub(super) fn caller(&self) -> trust_ir::FuncId {
        self.replay.requirement().function()
    }
    pub(super) fn branch(&self) -> (&str, usize, usize) {
        let name = self
            .ranges
            .iter()
            .find(|(id, _, _)| *id == self.replay.requirement().callee())
            .map(|(_, name, _)| name.as_str())
            .unwrap_or("");
        (
            name,
            self.replay.requirement().call_site(),
            self.replay.requirement().callee_offset(),
        )
    }
}
