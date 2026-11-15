// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Borrow the complete input of one refused Core machine compilation for the
//! existing conditional frame checkers. No proof request is captured here.

use super::*;
use trust_cg_verify::aarch64_static_frame::{
    CheckedStaticFrameEnvelopes, FrameImagePatch, SavedFrameRegister,
    StaticFrameEnvelopeCandidates, StaticFrameGeometryError, StaticFrameLayoutClaim,
    check_static_frame_envelopes,
};

/// A failed connection to the retained original function. None of these
/// diagnostics changes the compilation failure or grants machine authority.
#[derive(Debug, Error)]
pub enum CoreRejectedFrameError {
    #[error("Core refusal has no retained machine input")]
    NoMachineInput,
    #[error("Core refusal has no unique retained source/LIR function")]
    SourceFunction,
    #[error("Core refusal differs from its original request or complete input")]
    InputMismatch,
    #[error("Core refusal has no supported static frame: {0}")]
    Layout(&'static str),
    #[error(transparent)]
    SourceModules(#[from] trust_cg_verify::SourceModuleHasNoWireImage),
}

/// Immutable connection from one refused compilation to the shared frame
/// checkers. The complete original module, LIR, machine, byte image, all exits
/// and pending calls remain borrowed from the same failure. Only nomination
/// vectors are allocated; no machine graph or proof report is cloned.
///
/// Construction rehashes the retained module once and checks the original
/// request capture and complete verifier input. This is custody, not a source
/// refinement or body proof. Checked envelopes remain conditional on body,
/// call, storage and final-image obligations; this cannot become a certificate
/// or an executable artifact.
#[derive(Debug)]
pub struct CoreRejectedFrameContext<'a> {
    modules: trust_cg_verify::FunctionSourceModules<'a>,
    source_function: trust_ir::FuncId,
    source_ordinal: usize,
    lir: &'a trust_cg_lower::Function,
    rejected: &'a CoreMachineProofRejection,
    claim: StaticFrameLayoutClaim,
    candidates: StaticFrameEnvelopeCandidates,
    patches: Vec<FrameImagePatch>,
}

impl<'a> CoreRejectedFrameContext<'a> {
    pub fn source_modules(&self) -> &trust_cg_verify::FunctionSourceModules<'a> {
        &self.modules
    }
    pub fn source_function(&self) -> trust_ir::FuncId {
        self.source_function
    }
    pub fn source_ordinal(&self) -> usize {
        self.source_ordinal
    }
    pub fn lir(&self) -> &'a trust_cg_lower::Function {
        self.lir
    }
    pub fn rejected(&self) -> &'a CoreMachineProofRejection {
        self.rejected
    }
    pub fn request(&self) -> &'a trust_cg_verify::FunctionVerificationRequest {
        &self.rejected.request
    }
    pub fn layout_claim(&self) -> &StaticFrameLayoutClaim {
        &self.claim
    }
    pub fn envelope_candidates(&self) -> &StaticFrameEnvelopeCandidates {
        &self.candidates
    }
    /// Exact recorded call patch extents. These are pending relocations, not
    /// resolved targets, checked callees or a complete final linked image.
    pub fn pending_patches(&self) -> &[FrameImagePatch] {
        &self.patches
    }

    /// Independently check every nominated envelope word while retaining all
    /// unresolved body intervals. Producer emission is used only to nominate
    /// instruction counts; it supplies no proof credit.
    pub fn check_static_envelopes(
        &self,
    ) -> Result<CheckedStaticFrameEnvelopes<'_>, StaticFrameGeometryError> {
        check_static_frame_envelopes(
            self.lir,
            &self.rejected.machine,
            &self.rejected.bytes,
            &self.claim,
            &self.candidates,
            &self.patches,
        )
    }
}

impl CoreAddressFreeMachineCompilationFailure {
    /// Connect the retained whole refused input to the existing conditional
    /// frame API. Early refusals return `NoMachineInput`. This neither retries
    /// compilation nor recaptures a request, changes a budget or promotes the
    /// failed report. Native/provider effects remain unproved.
    pub fn rejected_frame_context(
        &self,
    ) -> Result<CoreRejectedFrameContext<'_>, CoreRejectedFrameError> {
        use CoreRejectedFrameError as E;
        let rejected = self.machine_rejection.as_ref().ok_or(E::NoMachineInput)?;
        let module = &self.plan.plan.parts.module;
        let mut sources = module
            .functions
            .iter()
            .enumerate()
            .filter(|(_, f)| f.id == rejected.source_function);
        let (source_ordinal, source) = sources.next().ok_or(E::SourceFunction)?;
        if sources.next().is_some() {
            return Err(E::SourceFunction);
        }
        let mut lowered = self
            .plan
            .plan
            .parts
            .lir_functions
            .iter()
            .filter(|(f, _)| f.name == source.name);
        let (lir, _) = lowered.next().ok_or(E::SourceFunction)?;
        if lowered.next().is_some() || rejected.machine.name != source.name {
            return Err(E::SourceFunction);
        }
        let modules = trust_cg_verify::FunctionSourceModules::capture(module, module)?;
        if !rejected.captured.matches_request_capture(&rejected.request)
            || !rejected.captured.matches_aarch64_input_with_modules(
                &rejected.machine,
                Some(lir),
                &modules,
            )
        {
            return Err(E::InputMismatch);
        }
        let layout = rejected.frame_layout.as_ref().ok_or(E::Layout("missing"))?;
        let (prologue_len, epilogue_len) = nomination_lengths(layout)?;
        let register = |reg: trust_cg_ir::PReg, fpr: bool| {
            let raw = reg.encoding();
            if fpr {
                match raw {
                    64..=95 => Ok(SavedFrameRegister::D((raw - 64) as u8)),
                    96..=127 => Ok(SavedFrameRegister::D((raw - 96) as u8)),
                    _ => Err(E::Layout("unsupported saved floating register")),
                }
            } else if raw <= 30 {
                Ok(SavedFrameRegister::X(raw as u8))
            } else {
                Err(E::Layout("unsupported saved integer register"))
            }
        };
        let saved_pairs = layout
            .callee_saved_pairs
            .iter()
            .map(|p| Ok([register(p.reg1, p.is_fpr)?, register(p.reg2, p.is_fpr)?]))
            .collect::<Result<Vec<_>, E>>()?;
        let claim = StaticFrameLayoutClaim {
            saved_pairs,
            callee_saved_bytes: layout.callee_saved_area_size,
            // The producer's spill area already contains addressable locals.
            stack_slot_bytes: layout.spill_area_size,
            outgoing_argument_bytes: layout.outgoing_arg_area_size,
            total_bytes: layout.total_frame_size,
            uses_frame_pointer: layout.uses_frame_pointer,
            dynamic_allocation: layout.has_dynamic_alloc,
            red_zone: layout.uses_red_zone,
            slot_fp_offsets: crate::frame::stack_slot_frame_offsets(&rejected.machine, layout),
        };
        let real = |block: trust_cg_ir::BlockId| -> Result<Vec<trust_cg_ir::InstId>, E> {
            rejected
                .machine
                .blocks
                .get(block.0 as usize)
                .ok_or(E::Layout("missing block"))?
                .insts
                .iter()
                .copied()
                .filter_map(|id| match rejected.machine.insts.get(id.0 as usize) {
                    Some(inst) if inst.is_pseudo() => None,
                    Some(_) => Some(Ok(id)),
                    None => Some(Err(E::Layout("missing instruction"))),
                })
                .collect()
        };
        let entry = real(rejected.machine.entry)?;
        let prologue = entry
            .get(..prologue_len)
            .ok_or(E::Layout("short entry envelope"))?
            .to_vec();
        let mut epilogues = Vec::new();
        for &block in &rejected.machine.block_order {
            let row = real(block)?;
            if row.last().is_some_and(|id| {
                rejected.machine.insts[id.0 as usize].opcode == trust_cg_ir::AArch64Opcode::Ret
            }) {
                let start = row
                    .len()
                    .checked_sub(epilogue_len)
                    .ok_or(E::Layout("short return envelope"))?;
                epilogues.push(row[start..].to_vec());
            }
        }
        let candidates = StaticFrameEnvelopeCandidates {
            prologue,
            epilogues,
        };
        let mut patches = Vec::with_capacity(rejected.fixup_sites.len());
        for site in &rejected.fixup_sites {
            let start = site.offset as usize;
            let end = start
                .checked_add(4)
                .ok_or(E::Layout("call extent overflow"))?;
            if rejected.bytes.get(start..end)
                != Some(site.placeholder_word.to_le_bytes().as_slice())
            {
                return Err(E::Layout("call placeholder differs"));
            }
            patches.push(FrameImagePatch {
                offset: site.offset,
                bytes: 4,
            });
        }
        Ok(CoreRejectedFrameContext {
            modules,
            source_function: rejected.source_function,
            source_ordinal,
            lir,
            rejected,
            claim,
            candidates,
            patches,
        })
    }
}

// Keep this check before either emitter: emit_prologue unrolls counted loops.
fn nomination_lengths(
    layout: &crate::frame::FrameLayout,
) -> Result<(usize, usize), CoreRejectedFrameError> {
    use CoreRejectedFrameError as E;
    if layout.total_frame_size < layout.callee_saved_area_size {
        return Err(E::Layout("saved area exceeds complete frame"));
    }
    if layout.has_dynamic_alloc || layout.uses_red_zone {
        return Err(E::Layout("dynamic or red-zone frame"));
    }
    // emit_prologue deliberately unrolls a looped probe plan. Do not
    // allocate a synthetic instruction stream proportional to frame size
    // merely to nominate a straight-line envelope.
    if crate::frame::StaticStackProbePlan::for_layout(layout).looped {
        return Err(E::Layout("looped stack probe is not a static envelope"));
    }

    Ok((
        crate::frame::emit_prologue(layout).len(),
        crate::frame::emit_epilogue(layout).len(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn layout(total: u32, saved: u32) -> crate::frame::FrameLayout {
        crate::frame::FrameLayout {
            callee_saved_pairs: vec![],
            callee_saved_area_size: saved,
            spill_area_size: 0,
            local_area_size: 0,
            outgoing_arg_area_size: 0,
            total_frame_size: total,
            uses_frame_pointer: false,
            is_leaf: false,
            uses_red_zone: false,
            fp_to_spill_offset: 0,
            has_dynamic_alloc: false,
        }
    }

    #[test]
    fn looped_nomination_is_refused_without_unrolling_the_frame() {
        assert!(matches!(
            nomination_lengths(&layout(u32::MAX - 15, 0)),
            Err(CoreRejectedFrameError::Layout(
                "looped stack probe is not a static envelope"
            ))
        ));
    }

    #[test]
    fn invalid_or_dynamic_nomination_is_fallible_before_emission() {
        assert!(matches!(
            nomination_lengths(&layout(0, 16)),
            Err(CoreRejectedFrameError::Layout(
                "saved area exceeds complete frame"
            ))
        ));
        let mut dynamic = layout(0, 0);
        dynamic.has_dynamic_alloc = true;
        assert!(nomination_lengths(&dynamic).is_err());
        dynamic.has_dynamic_alloc = false;
        dynamic.uses_red_zone = true;
        assert!(nomination_lengths(&dynamic).is_err());
    }
}
