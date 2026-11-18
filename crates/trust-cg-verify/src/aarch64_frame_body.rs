// Copyright 2026 Andrew Yates | Apache-2.0

//! Frame preservation only. This is not a source-result refinement, a proof
//! verdict, installation authority, or permission to access the stack.

use std::collections::BTreeSet;
use std::sync::Arc;

use trust_cg_ir::InstId;
use trust_cg_lower::instructions::{DirectCallBinding, Opcode};

use super::{Result, inconsistent};
use crate::aarch64_affine_lowering::{
    AttachedDefinedAffineCallee, CheckedAarch64TrustIrAffineBytes,
};
use crate::aarch64_control_decode::{A64ControlWord, decode_a64_control_word};
use crate::aarch64_instruction_word_proofs::check_emitted_instruction_word;
use crate::aarch64_static_frame::CheckedStaticFrameEnvelopes;
use crate::aarch64_value_decode_proofs::{
    A64Dest, FieldOverrides, decode_a64_value_word, denote_a64_value_word,
};
use crate::function_request::FunctionVerificationRequest;
use crate::smt::SmtExpr;

/// A call occurrence and its independently checked original callee/LIR/bytes.
/// Offsets refer to one immutable linked image, not separately copied bytes.
#[derive(Debug)]
pub struct FrameBodyCall<'c, 'a> {
    pub instruction: InstId,
    pub lir_instruction: usize,
    pub callee_offset: usize,
    pub callee: &'c CheckedAarch64TrustIrAffineBytes<'a>,
}

impl<'c, 'a> FrameBodyCall<'c, 'a> {
    /// Join the existing source-bearing, captured callee without a new request.
    /// The frame checker must still bind the original call, lowering, BL target
    /// and linked bytes. This does not establish entry storage permissions.
    pub fn from_defined_callee(
        instruction: InstId,
        lir_instruction: usize,
        callee_offset: usize,
        callee: &'c AttachedDefinedAffineCallee<'a>,
        request: &FunctionVerificationRequest,
    ) -> Result<Self> {
        if !callee.matches_request_capture(request) {
            return Err(inconsistent(
                "defined frame call differs from original request capture",
            ));
        }
        Ok(Self {
            instruction,
            lir_instruction,
            callee_offset,
            callee: callee.checked_bytes(),
        })
    }
}

/// A call footprint backed by complete independent readonly relation replay.
/// This retains the original module, lowering, machine and final-byte borrows.
/// It grants no pointee readability, initialization, physical lifetime, source
/// license, native installation or call-result instantiation permission.
pub struct ReadonlyFrameBodyCall<'c, 'a> {
    instruction: InstId,
    lir_instruction: usize,
    callee_offset: usize,
    certificate: &'c crate::read_only_replay::ReadOnlyReplayCertificate<'c, 'a>,
}
impl<'c, 'a> ReadonlyFrameBodyCall<'c, 'a> {
    pub fn from_replayed_callee(
        instruction: InstId,
        lir_instruction: usize,
        callee_offset: usize,
        certificate: &'c crate::read_only_replay::ReadOnlyReplayCertificate<'c, 'a>,
        request: &FunctionVerificationRequest,
    ) -> Result<Self> {
        if !certificate.request().same_capture(request) {
            return Err(inconsistent(
                "readonly frame call differs from original request capture",
            ));
        }
        Ok(Self {
            instruction,
            lir_instruction,
            callee_offset,
            certificate,
        })
    }
}

#[derive(Clone, Copy)]
pub(super) enum BodyCallee<'c, 'a> {
    Affine(&'c CheckedAarch64TrustIrAffineBytes<'a>),
    Readonly(&'c crate::read_only_replay::ReadOnlyReplayCertificate<'c, 'a>),
}
impl std::fmt::Debug for BodyCallee<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BodyCallee")
            .field("function", &self.source().name)
            .finish_non_exhaustive()
    }
}
impl<'a> BodyCallee<'_, 'a> {
    pub(super) fn normal_return_memory_effect(
        &self,
    ) -> crate::aarch64_affine_lowering::NormalReturnMemoryEffect {
        match self {
            Self::Affine(c) => c.normal_return_memory_effect(),
            // This complete byte profile refuses all stores, SP/FP/LR writes
            // and nested calls; its retained reads still demand real access.
            Self::Readonly(_) => {
                crate::aarch64_affine_lowering::NormalReturnMemoryEffect::Unchanged
            }
        }
    }
    fn module(&self) -> &'a trust_ir::Module {
        match self {
            Self::Affine(c) => c.module(),
            Self::Readonly(c) => c.relations().source().module(),
        }
    }
    fn source(&self) -> &'a trust_ir::Function {
        match self {
            Self::Affine(c) => c.source(),
            Self::Readonly(c) => c.relations().source().source(),
        }
    }
    fn lir(&self) -> &'a trust_cg_lower::Function {
        match self {
            Self::Affine(c) => c.lir(),
            Self::Readonly(c) => c.relations().source().lir(),
        }
    }
    fn code(&self) -> &'a [u8] {
        match self {
            Self::Affine(c) => c.code(),
            Self::Readonly(c) => c.relations().final_bytes(),
        }
    }
    pub(super) fn private_stack_bytes(&self) -> usize {
        match self {
            Self::Affine(c) => c.statistics().private_stack_bytes,
            // The readonly machine AND byte observers reject any SP/FP/LR
            // write/access except canonical RET, stores, nested calls and non-scratch writes. They retain
            // every load demand; satisfying it is a separate caller premise.
            Self::Readonly(_) => 0,
        }
    }
}
#[derive(Debug)]
pub(super) struct BodyCall<'c, 'a> {
    pub(super) instruction: InstId,
    lir_instruction: usize,
    callee_offset: usize,
    pub(super) callee: BodyCallee<'c, 'a>,
}

/// Borrowed, checked body footprint. Its claim is preservation on normal
/// arrival at a selected epilogue, not termination or source functionality.
#[derive(Debug)]
pub struct CheckedFrameBody<'g, 'c, 'a> {
    pub(super) geometry: &'g CheckedStaticFrameEnvelopes<'a>,
    pub(super) calls: Vec<BodyCall<'c, 'a>>,
    pub(super) required_entry_bytes: u32,
    linked_image: &'a [u8],
    pub(super) caller_offset: usize,
}

impl CheckedFrameBody<'_, '_, '_> {
    /// Numeric stack extent only; writable, live, private storage is still an
    /// explicit caller ABI obligation, not established by this footprint.
    pub fn required_entry_stack_bytes(&self) -> u32 {
        self.required_entry_bytes
    }
    pub fn linked_image(&self) -> &[u8] {
        self.linked_image
    }

    /// Carry the actual replayed readonly memory-result expression across this
    /// exact original/LIR/linked BL occurrence. Candidate caller expressions
    /// do not establish actual argument registers, readable storage, normal
    /// return or caller source refinement; those remain composition premises.
    pub fn instantiate_readonly_call_result(
        &self,
        instruction: InstId,
        certificate: &crate::read_only_replay::ReadOnlyReplayCertificate<'_, '_>,
        request: &FunctionVerificationRequest,
        arguments: &[Arc<SmtExpr>],
        entry_memory: &Arc<SmtExpr>,
    ) -> Result<Arc<SmtExpr>> {
        if !certificate.request().same_capture(request) || !self.calls.iter().any(|call| {
            call.instruction == instruction
                && matches!(call.callee, BodyCallee::Readonly(c) if std::ptr::eq(c, certificate))
        }) {
            return Err(inconsistent(
                "readonly result lacks this checked frame call and request",
            ));
        }
        certificate
            .instantiate_result(arguments, entry_memory)
            .map_err(|_| inconsistent("readonly frame call argument/memory relation refused"))
    }

    /// Instantiate a checked scalar return only after this exact callee was
    /// accepted at the body's original/LIR/linked BL site. Arguments remain
    /// caller expressions: their source/register correspondence is still owed.
    /// This grants no caller source refinement, instruction or ABI credit.
    pub fn instantiate_defined_call_result(
        &self,
        instruction: InstId,
        callee: &AttachedDefinedAffineCallee<'_>,
        request: &FunctionVerificationRequest,
        arguments: &[Arc<SmtExpr>],
    ) -> Result<Option<Arc<SmtExpr>>> {
        if !callee.matches_request_capture(request)
            || !self.calls.iter().any(|call| {
                call.instruction == instruction
                    && matches!(call.callee, BodyCallee::Affine(c) if std::ptr::eq(c, callee.checked_bytes()))
            })
        {
            return Err(inconsistent(
                "defined result lacks this checked frame call and request",
            ));
        }
        callee
            .instantiate_result(arguments)
            .map_err(|_| inconsistent("defined frame call argument relation refused"))
    }
}

fn same_slice(whole: &[u8], offset: usize, part: &[u8]) -> bool {
    whole
        .get(offset..)
        .and_then(|tail| tail.get(..part.len()))
        .is_some_and(|selected| std::ptr::eq(selected, part))
}

/// Check every body word and every call. No imported/provider call is assigned
/// a footprint from its signature, name, hash, or declared memory attributes.
pub fn check_frame_body<'g, 'c, 'a>(
    geometry: &'g CheckedStaticFrameEnvelopes<'a>,
    module: &'a trust_ir::Module,
    caller_ordinal: usize,
    linked_image: &'a [u8],
    caller_offset: usize,
    calls: &'c [FrameBodyCall<'c, 'a>],
) -> Result<CheckedFrameBody<'g, 'c, 'a>> {
    check_frame_body_calls(
        geometry,
        module,
        caller_ordinal,
        linked_image,
        caller_offset,
        calls
            .iter()
            .map(|c| BodyCall {
                instruction: c.instruction,
                lir_instruction: c.lir_instruction,
                callee_offset: c.callee_offset,
                callee: BodyCallee::Affine(c.callee),
            })
            .collect(),
    )
}

/// Compose readonly leaf footprints with the SAME original-call/LIR/BL/image
/// traversal used for affine leaves. This is frame preservation on normal
/// return only. Every actual load's live initialized stable-memory premise,
/// argument/result correspondence and termination remain separate obligations.
pub fn check_readonly_frame_body<'g, 'c, 'a>(
    geometry: &'g CheckedStaticFrameEnvelopes<'a>,
    module: &'a trust_ir::Module,
    caller_ordinal: usize,
    linked_image: &'a [u8],
    caller_offset: usize,
    calls: &[ReadonlyFrameBodyCall<'c, 'a>],
) -> Result<CheckedFrameBody<'g, 'c, 'a>> {
    check_frame_body_calls(
        geometry,
        module,
        caller_ordinal,
        linked_image,
        caller_offset,
        calls
            .iter()
            .map(|c| BodyCall {
                instruction: c.instruction,
                lir_instruction: c.lir_instruction,
                callee_offset: c.callee_offset,
                callee: BodyCallee::Readonly(c.certificate),
            })
            .collect(),
    )
}

fn check_frame_body_calls<'g, 'c, 'a>(
    geometry: &'g CheckedStaticFrameEnvelopes<'a>,
    module: &'a trust_ir::Module,
    caller_ordinal: usize,
    linked_image: &'a [u8],
    caller_offset: usize,
    calls: Vec<BodyCall<'c, 'a>>,
) -> Result<CheckedFrameBody<'g, 'c, 'a>> {
    let source = module
        .functions
        .get(caller_ordinal)
        .ok_or_else(|| inconsistent("body caller is outside original module"))?;
    let lir = geometry.source();
    // Diagnose missing native/provider effects before selecting the bounded
    // ordinary-source profile. This is the actual original E1 frontier.
    if lir.blocks.values().flat_map(|b| &b.instructions).any(|i| {
        matches!(
            i.opcode,
            Opcode::Call {
                binding: DirectCallBinding::NativeDependency { .. }
                    | DirectCallBinding::DeclaredExternalFunction { .. },
                ..
            }
        )
    }) {
        return Err(inconsistent(
            "original provider source/LIR/native footprint witness is missing",
        ));
    }
    if !same_slice(linked_image, caller_offset, geometry.image()) || !geometry.patches().is_empty()
    {
        return Err(inconsistent(
            "body requires exact immutable linked caller bytes without pending patches",
        ));
    }
    if source.name != lir.name || source.blocks.len() != 1 || lir.blocks.len() != 1 {
        return Err(inconsistent(
            "body source-call binding requires one original and lowering block",
        ));
    }
    let block = lir
        .blocks
        .get(&lir.entry_block)
        .ok_or_else(|| inconsistent("missing body lowering entry"))?;
    let mut used_lir = BTreeSet::new();
    let mut used_machine = BTreeSet::new();
    let mut used_original = BTreeSet::new();
    let mut deepest = 0usize;
    for binding in &calls {
        if !used_lir.insert(binding.lir_instruction) || !used_machine.insert(binding.instruction.0)
        {
            return Err(inconsistent("duplicate body call occurrence"));
        }
        let node = block
            .instructions
            .get(binding.lir_instruction)
            .ok_or_else(|| inconsistent("foreign lowering call occurrence"))?;
        let Opcode::Call {
            name,
            binding: DirectCallBinding::ExactModuleFunction { function },
        } = &node.opcode
        else {
            return Err(inconsistent("body call lacks exact module-defined binding"));
        };
        let selected = module
            .functions
            .iter()
            .find(|f| f.id.index() == *function)
            .ok_or_else(|| inconsistent("foreign callee"))?;
        if !std::ptr::eq(module, binding.callee.module())
            || !std::ptr::eq(selected, binding.callee.source())
            || name != &selected.name
            || !same_slice(linked_image, binding.callee_offset, binding.callee.code())
            || node.args.len() != binding.callee.lir().signature.params.len()
            || node.results.len() != binding.callee.lir().signature.returns.len()
        {
            return Err(inconsistent(
                "callee original/lowering/linked-byte endpoint mismatch",
            ));
        }
        let origin = lir
            .trust_ir_origins
            .get(&lir.entry_block)
            .and_then(|v| v.get(binding.lir_instruction))
            .and_then(|v| *v)
            .ok_or_else(|| inconsistent("missing original call origin"))?;
        if !used_original.insert(origin.0) {
            return Err(inconsistent("duplicate original call origin"));
        }
        if !source.blocks[0]
            .body
            .get(origin.0 as usize)
            .is_some_and(|n| {
                matches!(
                    &n.inst, trust_ir::Inst::Call { callee, args }
                        if callee.index() == *function && args.len() == node.args.len()
                            && n.results.len() == node.results.len()
                )
            })
        {
            return Err(inconsistent("stale original call identity"));
        }
        deepest = deepest.max(binding.callee.private_stack_bytes());
    }
    if source.blocks[0]
        .body
        .iter()
        .enumerate()
        .any(|(index, node)| {
            matches!(node.inst, trust_ir::Inst::Call { .. })
                && !u32::try_from(index)
                    .ok()
                    .is_some_and(|i| used_original.contains(&i))
        })
    {
        return Err(inconsistent(
            "original call has no paired lowering/machine footprint",
        ));
    }
    if block
        .instructions
        .iter()
        .enumerate()
        .filter(|(_, n)| matches!(n.opcode, Opcode::Call { .. }))
        .any(|(i, _)| !used_lir.contains(&i))
    {
        return Err(inconsistent("lowering call has no checked body footprint"));
    }
    let mut body_offsets = BTreeSet::new();
    for interval in geometry.unresolved_body() {
        for &id in &interval.instructions {
            if let Some(offset) = geometry.byte_offset(id) {
                body_offsets.insert(offset);
            }
        }
    }
    let epilogue_offsets: BTreeSet<_> = geometry
        .candidates()
        .epilogues
        .iter()
        .filter_map(|ep| ep.first().and_then(|id| geometry.byte_offset(*id)))
        .collect();
    let mut seen_calls = BTreeSet::new();
    for interval in geometry.unresolved_body() {
        for &id in &interval.instructions {
            let Some(offset) = geometry.byte_offset(id) else {
                return Err(inconsistent("body instruction has no byte coordinate"));
            };
            let word = u32::from_le_bytes(
                geometry
                    .image()
                    .get(offset..offset + 4)
                    .ok_or_else(|| inconsistent("truncated body word"))?
                    .try_into()
                    .unwrap(),
            );
            let inst = geometry
                .machine()
                .insts
                .get(id.0 as usize)
                .ok_or_else(|| inconsistent("foreign body instruction"))?;
            // The existing select model has an independent strict word binder.
            // Its result establishes the architectural write footprint, not a
            // source predicate or value relation, and does not credit a row.
            let select = if matches!(
                inst.opcode,
                trust_cg_ir::AArch64Opcode::CSet
                    | trust_cg_ir::AArch64Opcode::Csel
                    | trust_cg_ir::AArch64Opcode::Csinc
                    | trust_cg_ir::AArch64Opcode::Csinv
                    | trust_cg_ir::AArch64Opcode::Csneg
            ) {
                Some(
                    crate::aarch64_csel_semantics::bind_conditional_select_word(inst, word)
                        .map_err(|_| {
                            inconsistent("select body word differs from its machine operands")
                        })?,
                )
            } else {
                None
            };
            if select.is_none() {
                match check_emitted_instruction_word(inst, word) {
                    Some(Ok(())) => (),
                    _ => {
                        return Err(inconsistent(
                            "body word is not bound to its machine instruction",
                        ));
                    }
                }
            }
            // A normal fallthrough (including return from a checked BL) must
            // stay inside this checked region. In particular an unselected
            // suffix cannot execute and later re-enter an epilogue.
            let control = decode_a64_control_word(word);
            if !matches!(control, Some(A64ControlWord::Branch { .. })) {
                let next = offset
                    .checked_add(4)
                    .ok_or_else(|| inconsistent("body fallthrough overflow"))?;
                if !body_offsets.contains(&next) && !epilogue_offsets.contains(&next) {
                    return Err(inconsistent(
                        "body fallthrough escapes checked body/epilogue",
                    ));
                }
            }
            if word & 0xfc00_0000 == 0x9400_0000 {
                let call = calls
                    .iter()
                    .find(|c| c.instruction == id)
                    .ok_or_else(|| inconsistent("machine call has no checked callee"))?;
                let mut symbols = inst
                    .operands
                    .iter()
                    .filter_map(|operand| operand.as_symbol());
                if !inst
                    .flags
                    .contains(trust_cg_ir::InstFlags::EXACT_MODULE_CALL)
                    || symbols.next() != Some(call.callee.source().name.as_str())
                    || symbols.next().is_some()
                {
                    return Err(inconsistent(
                        "machine call lacks exact module callee symbol",
                    ));
                }
                let displacement = (i64::from(word & 0x03ff_ffff) << 38) >> 36;
                let pc = caller_offset
                    .checked_add(offset)
                    .and_then(|v| i64::try_from(v).ok())
                    .ok_or_else(|| inconsistent("call coordinate overflow"))?;
                if pc.checked_add(displacement) != i64::try_from(call.callee_offset).ok() {
                    return Err(inconsistent("actual BL target differs from checked callee"));
                }
                seen_calls.insert(id.0);
                continue;
            }
            if let Some(control) = control {
                let displacement = match control {
                    A64ControlWord::Branch { displacement }
                    | A64ControlWord::ConditionalBranch { displacement, .. }
                    | A64ControlWord::CompareBranch { displacement, .. } => displacement,
                    A64ControlWord::Return { .. } => {
                        return Err(inconsistent("body return bypasses checked epilogue"));
                    }
                };
                let target = i64::try_from(offset)
                    .ok()
                    .and_then(|v| displacement.checked_mul(4).and_then(|d| v.checked_add(d)))
                    .and_then(|v| usize::try_from(v).ok())
                    .ok_or_else(|| inconsistent("body branch overflow"))?;
                if !body_offsets.contains(&target) && !epilogue_offsets.contains(&target) {
                    return Err(inconsistent("body branch escapes checked body/epilogue"));
                }
                // The existing word checker leaves block displacements as
                // holes. Bind those holes to the retained machine CFG too.
                for operand in &inst.operands {
                    if let trust_cg_ir::MachOperand::Block(block) = operand {
                        let expected = geometry
                            .machine()
                            .blocks
                            .get(block.0 as usize)
                            .and_then(|b| b.insts.iter().find_map(|id| geometry.byte_offset(*id)));
                        if expected != Some(target) {
                            return Err(inconsistent(
                                "actual body branch differs from retained machine CFG",
                            ));
                        }
                    }
                    if matches!(
                        operand,
                        trust_cg_ir::MachOperand::Symbol(_)
                            | trust_cg_ir::MachOperand::ExactModuleSymbol(_)
                    ) {
                        return Err(inconsistent("body branch has unresolved symbolic target"));
                    }
                }
                continue;
            }
            if word == 0xd503201f {
                continue;
            }
            let destination = if let Some(select) = select {
                // All variants read before writing only Rd. Register 31 is
                // discarded, never SP; W writes still replace the full X slot.
                match select.registers().0 {
                    31 => A64Dest::Discarded,
                    n => A64Dest::Gpr(n),
                }
            } else {
                let decoded = decode_a64_value_word(word)
                    .map_err(|_| inconsistent("body memory/system/unknown effect"))?;
                denote_a64_value_word(&decoded, &FieldOverrides::default())
                    .map_err(|_| inconsistent("body effect is not modeled"))?
                    .dest
            };
            if !matches!(destination, A64Dest::Gpr(n) if n < 18 ||
                (n != 29 && n != 30 && geometry.saved_slots().iter().any(|s|
                    s.register == crate::aarch64_static_frame::SavedFrameRegister::X(n))))
                && !matches!(destination, A64Dest::Discarded)
            {
                return Err(inconsistent(
                    "body writes SP/FP/LR/platform or system state",
                ));
            }
        }
    }
    if seen_calls != used_machine {
        return Err(inconsistent("unused checked callee occurrence"));
    }
    let required_entry_bytes = geometry
        .layout_claim()
        .total_bytes
        .checked_add(
            u32::try_from(deepest).map_err(|_| inconsistent("callee stack extent overflow"))?,
        )
        .ok_or_else(|| inconsistent("combined caller/callee stack extent overflow"))?;
    Ok(CheckedFrameBody {
        geometry,
        calls,
        required_entry_bytes,
        linked_image,
        caller_offset,
    })
}

#[cfg(test)]
#[path = "aarch64_frame_body_tests.rs"]
mod tests;
