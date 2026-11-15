// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Conditional whole-call ownership for an actual zero- or one-word defined peer.
//!
//! This owner checks the original call/result, strict LIR occurrence, actual
//! allocated words, complete frame/body/callee and final BL target. Its raw
//! theorem composes source result, normal continuation, FP/LR/SP restoration
//! and outside-private-memory agreement. Replay stays under the original
//! request. Construction alone grants no instruction or storage permission.
//! The resulting sealed entry requirement must stay attached to its final
//! bytes and can be discharged only by the consuming real runtime-stack owner.

use sha2::{Digest, Sha256};
use trust_cg_ir::{AArch64Opcode as Op, InstId, MachFunction};
use trust_cg_lower::{
    Function,
    instructions::{DirectCallBinding, Opcode},
};
use trust_ir::proof::ProofDigest;
use trust_ir::{FuncId, Inst, Module, Ty};

use super::{AttachedDefinedAffineCallee, defined_callee::scalar_expression, trust_ir_contract};
use crate::FunctionSourceModules;
use crate::aarch64_conditional_frame::{
    FrameBodyCall, check_frame_body, conditional_static_frame_with_body,
};
use crate::aarch64_static_frame::{
    StaticFrameEnvelopeCandidates, StaticFrameLayoutClaim, check_static_frame_envelopes,
};
use crate::function_request::{CapturedFunctionVerificationReport, FunctionVerificationRequest};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::{encode_load_le, memory_sort};
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::smt::SmtExpr as E;

#[derive(Debug, thiserror::Error)]
pub enum DefinedPeerCallError {
    #[error("defined peer source/call/result domain refused: {0}")]
    Source(&'static str),
    #[error("defined peer original request/input custody differs")]
    Request,
    #[error("defined peer actual machine/final-image binding refused: {0}")]
    Machine(String),
    #[error("defined peer callee relation refused: {0}")]
    Callee(String),
    #[error("defined peer complete conditional theorem was not formally replayed: {0}")]
    Replay(String),
    #[error("defined peer final entry requirement differs from retained source/bytes")]
    EntryBinding,
}
type Result<T> = std::result::Result<T, DefinedPeerCallError>;

/// Borrowed complete endpoints. This is deliberately not Clone/serializable.
#[derive(Debug)]
pub struct CheckedDefinedPeerCall<'a> {
    module: &'a Module,
    source: FuncId,
    machine: &'a MachFunction,
    lir: &'a Function,
    image: &'a [u8],
    caller_offset: usize,
    caller_len: usize,
    callee: FuncId,
    callee_offset: usize,
    call_site: usize,
    required_bytes: usize,
    argument_count: u8,
    covered: Vec<InstId>,
    original_request: FunctionVerificationRequest,
    original_caller: CapturedFunctionVerificationReport,
    obligation: ProofObligation,
}

/// An undischarged physical storage requirement, sealed only after formal
/// replay and exact input/final-byte binding. Numbers exposed here are
/// diagnostics, never a public permission constructor or mapped-memory fact.
#[derive(Debug)]
pub struct ConditionalPeerEntryRequirement {
    module: ProofDigest,
    function: FuncId,
    body: ProofDigest,
    machine_input: [u8; 32],
    final_code: ProofDigest,
    final_image: ProofDigest,
    private_bytes: usize,
    argument_count: u8,
    caller_offset: usize,
    callee: FuncId,
    callee_offset: usize,
    call_site: usize,
    captured: CapturedFunctionVerificationReport,
    original_request: FunctionVerificationRequest,
}

// Select the caller's actual source-call certificate AND its one inherited
// callee edge. The affine-leaf selector intentionally permits one certificate;
// source-call families carry a distinct second row. This is an exact prerequisite
// selection, not a replacement for the existing bounded IR/Clean family replay.
fn check_caller_source_family(
    module: &Module,
    function: &trust_ir::Function,
    callee: &AttachedDefinedAffineCallee<'_>,
) -> Result<()> {
    use trust_ir::{BodyGate, proof::ProofEvidence};
    let refuse = || DefinedPeerCallError::Source("actual source-call family binding differs");
    let Some(BodyGate::Gated {
        authority,
        evidence: Some(gate),
    }) = &function.body_gate
    else {
        return Err(refuse());
    };
    let Some(BodyGate::Gated {
        evidence: Some(callee_gate),
        ..
    }) = &callee.checked_bytes().source().body_gate
    else {
        return Err(refuse());
    };
    if authority != trust_cg_lower::CLEAN_KERNEL_TV_AUTHORITY
        || module.function_body_digest(function.id) != Ok(gate.body_digest)
    {
        return Err(refuse());
    }
    let mut obligations = module
        .proof_obligations
        .iter()
        .filter(|row| row.id == gate.obligation);
    if obligations
        .next()
        .is_none_or(|row| row.function != Some(function.id))
        || obligations.next().is_some()
    {
        return Err(refuse());
    }
    let mut source = None;
    let mut inherited = false;
    for certificate in module
        .proof_certificates
        .iter()
        .filter(|row| row.obligation == gate.obligation)
    {
        match &certificate.evidence {
            ProofEvidence::CleanCic {
                kernel_recheck: Some(recheck),
                ..
            } if source.is_none() => {
                if recheck.module != "CleanCompiler.SourceCallsV1"
                    || recheck.anchor
                        != trust_ir::proof::KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1
                    || !recheck.allowed_axioms.is_empty()
                {
                    return Err(refuse());
                }
                let binding = recheck.binding.as_ref().ok_or_else(refuse)?;
                if binding.environment.is_none()
                    || binding.callees.as_slice() != [callee.checked_bytes().source().name.clone()]
                {
                    return Err(refuse());
                }
                source = Some(binding.source.as_ref().ok_or_else(refuse)?);
            }
            ProofEvidence::InheritedFromCallee {
                callee: selected,
                obligation,
                external: None,
            } if !inherited
                && *selected == callee.checked_bytes().source().id
                && *obligation == callee_gate.obligation =>
            {
                inherited = true;
            }
            _ => return Err(refuse()),
        }
    }
    if !inherited
        || source.is_none_or(|source| {
            source.closure_digest != callee.summary().source_definition().closure_digest
        })
    {
        return Err(refuse());
    }
    Ok(())
}

impl<'a> CheckedDefinedPeerCall<'a> {
    /// The initial bounded profile is one actual Call followed by its Return,
    /// in a standard sixteen-byte caller frame. Neither signature metadata nor
    /// a module-wide callee census substitutes for this exact occurrence.
    #[allow(clippy::too_many_arguments)]
    pub fn bind(
        modules: &FunctionSourceModules<'a>,
        request: &FunctionVerificationRequest,
        original: &CapturedFunctionVerificationReport,
        caller: FuncId,
        lir: &'a Function,
        machine: &'a MachFunction,
        image: &'a [u8],
        caller_offset: usize,
        callee_offset: usize,
        callee: &AttachedDefinedAffineCallee<'a>,
        layout: &StaticFrameLayoutClaim,
    ) -> Result<Self> {
        if !std::ptr::eq(modules.original(), modules.lowered())
            || request.mode() != ProvenanceXCheckMode::Enforce
            || !original.matches_request_capture(request)
            || !original.matches_aarch64_input_with_modules(machine, Some(lir), modules)
            || !callee.matches_request_capture(request)
        {
            return Err(DefinedPeerCallError::Request);
        }
        let module = modules.original();
        let function = module
            .function_by_id(caller)
            .ok_or(DefinedPeerCallError::Source("missing caller"))?;
        let argument_count = function
            .blocks
            .first()
            .map_or(usize::MAX, |block| block.params.len());
        if argument_count > 1
            || module.functions.len() != 2
            || function.name != lir.name
            || machine.name != lir.name
            || function.blocks.len() != 1
            || lir.blocks.len() != 1
            || function.blocks[0].body.len() != 2
            || function.entry != function.blocks[0].id
            || (!lir.block_order.is_empty() && lir.block_order != [lir.entry_block])
            || lir.signature.params.len() != argument_count
            || lir
                .signature
                .params
                .iter()
                .any(|ty| *ty != trust_cg_lower::Type::I64)
            || machine.signature.params.len() != argument_count
            || machine
                .signature
                .params
                .iter()
                .any(|ty| *ty != trust_cg_ir::function::Type::I64)
            || machine.signature.returns.as_slice() != [trust_cg_ir::function::Type::I64]
            || lir.signature.returns.as_slice() != [trust_cg_lower::Type::I64]
        {
            return Err(DefinedPeerCallError::Source(
                "requires one zero- or one-word forwarding 64-bit call/return",
            ));
        }
        let ordinal = module
            .functions
            .iter()
            .position(|f| f.id == caller)
            .ok_or(DefinedPeerCallError::Source("missing caller ordinal"))?;
        super::defined_callee::scalar_abi(module, ordinal, lir)
            .map_err(|e| DefinedPeerCallError::Machine(e.to_string()))?;
        let signature = module
            .func_type(function.ty)
            .ok_or(DefinedPeerCallError::Source("missing signature"))?;
        if (argument_count == 0 && !signature.params.is_empty())
            || (argument_count == 1
                && (signature.params != [Ty::U64]
                    || signature.returns != [Ty::U64]
                    || function.blocks[0].params[0].1 != Ty::U64))
            || !matches!(signature.returns.as_slice(), [Ty::I64 | Ty::U64])
        {
            return Err(DefinedPeerCallError::Source("source ABI differs"));
        }
        if signature.is_vararg
            || !function.attrs.params.is_empty()
            || !function.attrs.ret.is_empty()
            || !lir.stack_slots.is_empty()
            || lir.stack_protector != trust_cg_ir::StackProtectorMode::None
        {
            return Err(DefinedPeerCallError::Source(
                "explicit ABI/stack sidecar outside peer profile",
            ));
        }
        let callee_signature = module
            .func_type(callee.checked_bytes().source().ty)
            .ok_or(DefinedPeerCallError::Source("missing callee signature"))?;
        if callee_signature.params != signature.params
            || callee_signature.returns != signature.returns
            || callee.summary().result_type() != Some(super::DefinedCalleeScalarType::BitVec(64))
        {
            return Err(DefinedPeerCallError::Source(
                "callee lacks the exact 64-bit result route",
            ));
        }
        let source_call = &function.blocks[0].body[0];
        let Inst::Call {
            callee: source_callee,
            args,
        } = &source_call.inst
        else {
            return Err(DefinedPeerCallError::Source(
                "original operation is not a call",
            ));
        };
        let Inst::Return { values } = &function.blocks[0].body[1].inst else {
            return Err(DefinedPeerCallError::Source(
                "original continuation is not return",
            ));
        };
        if args.len() != argument_count
            || args
                .iter()
                .zip(&function.blocks[0].params)
                .any(|(arg, param)| *arg != param.0)
            || source_call.results.len() != 1
            || values.as_slice() != [source_call.results[0]]
            || *source_callee != callee.checked_bytes().source().id
            || caller == *source_callee
            || !std::ptr::eq(module, callee.checked_bytes().module())
            || callee.checked_bytes().statistics().parameter_count != argument_count
        {
            return Err(DefinedPeerCallError::Source(
                "actual call/result/callee identity differs",
            ));
        }
        let block = lir
            .blocks
            .get(&lir.entry_block)
            .ok_or(DefinedPeerCallError::Source("missing LIR entry"))?;
        if block.instructions.len() != 2
            || block.params.len() != argument_count
            || block
                .params
                .iter()
                .any(|(_, ty)| *ty != trust_cg_lower::Type::I64)
        {
            return Err(DefinedPeerCallError::Source("LIR has unpaired operations"));
        }
        let call = &block.instructions[0];
        let ret = &block.instructions[1];
        if !matches!(&call.opcode,Opcode::Call {name,binding:DirectCallBinding::ExactModuleFunction {function}} if name==&callee.checked_bytes().source().name && *function==source_callee.index())
            || call.args.len() != argument_count
            || call
                .args
                .iter()
                .zip(&block.params)
                .any(|(arg, param)| *arg != param.0)
            || call.results.len() != 1
            || !matches!(ret.opcode, Opcode::Return)
            || ret.args.as_slice() != call.results.as_slice()
            || !ret.results.is_empty()
        {
            return Err(DefinedPeerCallError::Source(
                "LIR argument/result route differs",
            ));
        }
        // Block-parameter types come from the actual signature and block above.
        // The adapter records a sidecar for the call result, but need not repeat
        // parameter types there. Any optional parameter hint must still agree.
        if block.params.iter().any(|(value, _)| {
            *value == call.results[0]
                || lir
                    .value_types
                    .get(value)
                    .is_some_and(|ty| *ty != trust_cg_lower::Type::I64)
        }) || lir.value_types.get(&call.results[0]) != Some(&trust_cg_lower::Type::I64)
            || lir.value_types.iter().any(|(value, ty)| {
                (*value != call.results[0] && !block.params.iter().any(|(param, _)| param == value))
                    || *ty != trust_cg_lower::Type::I64
            })
        {
            return Err(DefinedPeerCallError::Source(
                "LIR call-result sidecar differs from its exact I64 route",
            ));
        }
        check_caller_source_family(module, function, callee)?;
        let raw_ids = &machine
            .blocks
            .get(machine.entry.0 as usize)
            .ok_or_else(|| DefinedPeerCallError::Machine("missing machine entry".into()))?
            .insts;
        // The one-word route retains exactly one zero-byte argument self-copy
        // before BL. Authenticate its operands and effect flags before omitting
        // it from the five emitted rows; arbitrary pseudos are not admitted.
        if machine.block_order.as_slice() != [machine.entry]
            || machine.blocks.len() != 1
            || raw_ids.len() != 5 + argument_count
        {
            return Err(DefinedPeerCallError::Machine(
                "requires exact framed call rows and argument setup count".into(),
            ));
        }
        let mut ids = Vec::with_capacity(5);
        for (position, id) in raw_ids.iter().copied().enumerate() {
            let row = machine
                .insts
                .get(id.0 as usize)
                .ok_or_else(|| DefinedPeerCallError::Machine("missing actual call row".into()))?;
            if argument_count == 1 && position == 2 {
                if !is_x0_argument_self_copy(row) {
                    return Err(DefinedPeerCallError::Machine(
                        "one-word call requires exact zero-byte X0 argument self-copy".into(),
                    ));
                }
            } else if row.is_pseudo() {
                return Err(DefinedPeerCallError::Machine(
                    "unexpected pseudo in framed peer".into(),
                ));
            } else {
                ids.push(id);
            }
        }
        // The append-only arena can retain detached pass history. The original
        // capture binds it all; the frame owner validates the unique emitted
        // IDs and exact twenty-byte extent below.
        if ids.len() != 5
            || ids.iter().enumerate().any(|(i, id)| {
                machine.insts[id.0 as usize].opcode
                    != [
                        Op::StpPreIndex,
                        Op::AddRI,
                        Op::Bl,
                        Op::LdpPostIndex,
                        Op::Ret,
                    ][i]
            })
        {
            return Err(DefinedPeerCallError::Machine(
                "requires complete actual framed BL stream".into(),
            ));
        }
        let caller_len = 20;
        let caller_code = image
            .get(
                caller_offset
                    ..caller_offset
                        .checked_add(caller_len)
                        .ok_or(DefinedPeerCallError::EntryBinding)?,
            )
            .ok_or(DefinedPeerCallError::EntryBinding)?;
        if caller_code[..8] != [0xfd, 0x7b, 0xbf, 0xa9, 0xfd, 0x03, 0x00, 0x91]
            || caller_code[12..] != [0xfd, 0x7b, 0xc1, 0xa8, 0xc0, 0x03, 0x5f, 0xd6]
            || u32::from_le_bytes(caller_code[8..12].try_into().unwrap()) & 0xfc00_0000
                != 0x9400_0000
        {
            return Err(DefinedPeerCallError::Machine(
                "actual standard envelope/BL/RET words differ".into(),
            ));
        }
        let callee_code = callee.checked_bytes().code();
        let selected = image
            .get(
                callee_offset
                    ..callee_offset
                        .checked_add(callee_code.len())
                        .ok_or(DefinedPeerCallError::EntryBinding)?,
            )
            .ok_or(DefinedPeerCallError::EntryBinding)?;
        if !std::ptr::eq(selected, callee_code)
            || caller_offset % 4 != 0
            || callee_offset % 4 != 0
            || !(callee_offset + callee_code.len() <= caller_offset
                || caller_offset + caller_len <= callee_offset)
        {
            return Err(DefinedPeerCallError::EntryBinding);
        }
        let candidates = StaticFrameEnvelopeCandidates {
            prologue: ids[..2].to_vec(),
            epilogues: vec![ids[3..].to_vec()],
        };
        let geometry =
            check_static_frame_envelopes(lir, machine, caller_code, layout, &candidates, &[])
                .map_err(|e| DefinedPeerCallError::Machine(e.to_string()))?;
        if geometry.layout_claim().total_bytes != 16 {
            return Err(DefinedPeerCallError::Machine("caller frame differs".into()));
        }
        let calls = [
            FrameBodyCall::from_defined_callee(ids[2], 0, callee_offset, callee, request)
                .map_err(|e| DefinedPeerCallError::Machine(e.to_string()))?,
        ];
        let ordinal = module
            .functions
            .iter()
            .position(|f| f.id == caller)
            .ok_or(DefinedPeerCallError::Source("caller ordinal"))?;
        let body = check_frame_body(&geometry, module, ordinal, image, caller_offset, &calls)
            .map_err(|e| DefinedPeerCallError::Machine(e.to_string()))?;
        let composed = conditional_static_frame_with_body(&body)
            .map_err(|e| DefinedPeerCallError::Machine(e.to_string()))?;
        if composed.exits().len() != 1 {
            return Err(DefinedPeerCallError::Machine(
                "ambiguous normal exit".into(),
            ));
        }
        let exit = &composed.exits()[0];
        let mut obligation = exit.obligation().clone();
        // Source result is reconstructed from the original callee body, while
        // the machine result comes from the exact attached final-word relation.
        let source_result = trust_ir_contract(module, callee.checked_bytes().source())
            .map_err(|e| DefinedPeerCallError::Callee(e.to_string()))?
            .result
            .ok_or(DefinedPeerCallError::Source("missing source result"))?;
        // Under the admitted scalar C ABI the one incoming word is X0. The
        // exact prologue only changes SP/FP, and the exact postlude only
        // restores SP/FP/LR: no caller instruction moves or overwrites X0.
        // Original and LIR argument lists above must forward that same first
        // parameter, so the checked callee relation receives this actual word.
        let arguments: Vec<_> = (argument_count == 1)
            .then(|| std::sync::Arc::new(E::var("peer_entry_x0", 64)))
            .into_iter()
            .collect();
        let source_result = scalar_expression(source_result, &arguments);
        let machine_result = body
            .instantiate_defined_call_result(ids[2], callee, request, &arguments)
            .map_err(|e| DefinedPeerCallError::Callee(e.to_string()))?
            .ok_or(DefinedPeerCallError::Source("missing callee result"))?;
        let entry_sp = E::var("frame_entry_sp", 64);
        let observation = E::var("peer_world_observation", 64);
        let source_memory = E::uf("peer_source_entry_memory", Vec::new(), memory_sort());
        let entry_memory = E::uf("frame_entry_memory", Vec::new(), memory_sort());
        let source_byte = encode_load_le(&source_memory, &observation, 1);
        let machine_entry_byte = encode_load_le(&entry_memory, &observation, 1);
        let final_byte = encode_load_le(exit.resume_memory(), &observation, 1);
        let required_bytes = body.required_entry_stack_bytes() as usize;
        if argument_count == 1 {
            obligation.inputs.push(("peer_entry_x0".into(), 64));
        }
        obligation.inputs.extend([
            ("peer_world_observation".into(), 64),
            ("peer_image_base".into(), 64),
        ]);
        obligation.preconditions.push(
            observation
                .clone()
                .bvult(
                    entry_sp
                        .clone()
                        .bvsub(E::bv_const(required_bytes as u64, 64)),
                )
                .or_expr(observation.clone().bvuge(entry_sp.clone())),
        );
        obligation
            .preconditions
            .push(source_byte.clone().eq_expr(machine_entry_byte));
        let base = E::var("peer_image_base", 64);
        obligation.preconditions.push(
            base.clone()
                .bvule(E::bv_const(u64::MAX - image.len() as u64, 64)),
        );
        obligation.preconditions.push(
            base.clone()
                .bvand(E::bv_const(3, 64))
                .eq_expr(E::bv_const(0, 64)),
        );
        let word = u32::from_le_bytes(caller_code[8..12].try_into().unwrap());
        let displacement = (i64::from(word & 0x03ff_ffff) << 38) >> 36;
        let pc = base
            .clone()
            .bvadd(E::bv_const((caller_offset + 8) as u64, 64));
        let linked_lr = pc.clone().bvadd(E::bv_const(4, 64));
        let target = pc.bvadd(E::bv_const(displacement as u64, 64));
        let continuation = base
            .clone()
            .bvadd(E::bv_const((caller_offset + 12) as u64, 64));
        let expected_target = base.bvadd(E::bv_const(callee_offset as u64, 64));
        obligation.aarch64_expr = obligation
            .aarch64_expr
            .and_expr(
                source_result
                    .as_ref()
                    .clone()
                    .eq_expr(machine_result.as_ref().clone()),
            )
            .and_expr(target.eq_expr(expected_target))
            .and_expr(linked_lr.eq_expr(continuation))
            .and_expr(source_byte.eq_expr(final_byte));
        obligation.name =
            "Source-bound defined peer: actual result/BL PC+4 continuation/frame/private-world"
                .into();
        obligation.category = Some(TransvalCheckKind::RegisterAllocation);
        obligation.machine_side_provenance = MachineSideProvenance::StaticDb;
        if obligation.is_degenerate() {
            return Err(DefinedPeerCallError::Machine(
                "degenerate complete query".into(),
            ));
        }
        let roots: Vec<_> = std::iter::once(&obligation.trust_ir_expr)
            .chain(std::iter::once(&obligation.aarch64_expr))
            .chain(obligation.preconditions.iter())
            .collect();
        crate::smt_raw_print::preflight_roots(&roots)
            .map_err(|e| DefinedPeerCallError::Machine(e.to_string()))?;
        Ok(Self {
            module,
            source: caller,
            machine,
            lir,
            image,
            caller_offset,
            caller_len,
            callee: *source_callee,
            callee_offset,
            call_site: caller_offset + 8,
            required_bytes,
            argument_count: argument_count as u8,
            covered: ids,
            original_request: request.clone(),
            original_caller: original.clone(),
            obligation,
        })
    }
    pub(crate) fn matches_inputs(
        &self,
        modules: &FunctionSourceModules<'_>,
        machine: &MachFunction,
        lir: &Function,
    ) -> bool {
        std::ptr::eq(modules.original(), self.module)
            && std::ptr::eq(modules.lowered(), self.module)
            && std::ptr::eq(machine, self.machine)
            && std::ptr::eq(lir, self.lir)
    }
    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
    pub(crate) fn matches_request(&self, request: &FunctionVerificationRequest) -> bool {
        // Exact invocation scope is checked by a captured report, not merely a
        // reusable policy digest or a separately recaptured equivalent request.
        self.original_request.same_capture(request)
    }
    pub(crate) fn replay_and_seal(
        &self,
        context: &crate::function_request::FunctionDischargeContext<'_>,
    ) -> Result<ConditionallyReplayedDefinedPeer> {
        if !self.matches_request(context.request)
            || context
                .source_modules
                .is_none_or(|modules| !self.matches_inputs(modules, self.machine, self.lir))
        {
            return Err(DefinedPeerCallError::Request);
        }
        let (verdict, why) = context.defined_peer(self);
        match verdict {
            Some(crate::verify::VerificationResult::Valid) => {
                DefinedPeerReplay { owner: self }.finish(context)
            }
            Some(other) => Err(DefinedPeerCallError::Replay(format!("{other:?}"))),
            None => Err(DefinedPeerCallError::Replay(
                why.unwrap_or_else(|| "no independently checked proof".into()),
            )),
        }
    }
}

/// Private move-only result of an actual successful replay, borrowing the
/// exact owner for the entire report/requirement construction. There is no
/// constructor from a report, numeric identity, checksum or caller descriptor.
struct DefinedPeerReplay<'owner, 'inputs> {
    owner: &'owner CheckedDefinedPeerCall<'inputs>,
}
impl DefinedPeerReplay<'_, '_> {
    fn finish(
        self,
        context: &crate::function_request::FunctionDischargeContext<'_>,
    ) -> Result<ConditionallyReplayedDefinedPeer> {
        let owner = self.owner;
        if !owner.matches_request(context.request)
            || context
                .source_modules
                .is_none_or(|modules| !owner.matches_inputs(modules, owner.machine, owner.lir))
        {
            return Err(DefinedPeerCallError::Request);
        }
        // No ordinary Formal row, captured successful report, A64Body export,
        // generic certificate or transferable storage authority is created.
        // The actual replay receipt remains paired with the conditional entry.
        let requirement = ConditionalPeerEntryRequirement {
            module: owner.module.stable_digest(),
            function: owner.source,
            body: owner
                .module
                .function_body_digest(owner.source)
                .map_err(|_| DefinedPeerCallError::EntryBinding)?,
            machine_input: *owner
                .original_caller
                .aarch64_input_digest()
                .ok_or(DefinedPeerCallError::EntryBinding)?,
            final_code: ProofDigest::sha256(
                Sha256::digest(
                    &owner.image[owner.caller_offset..owner.caller_offset + owner.caller_len],
                )
                .into(),
            ),
            final_image: ProofDigest::sha256(Sha256::digest(owner.image).into()),
            private_bytes: owner.required_bytes,
            argument_count: owner.argument_count,
            caller_offset: owner.caller_offset,
            callee: owner.callee,
            callee_offset: owner.callee_offset,
            call_site: owner.call_site,
            captured: owner.original_caller.clone(),
            original_request: owner.original_request.clone(),
        };
        Ok(ConditionallyReplayedDefinedPeer {
            requirement,
            statement: owner.obligation.clone(),
            covered: owner.covered.clone(),
        })
    }
}

/// A successful raw replay whose physical entry premise is still pending.
/// This move-only owner has no conversion to ordinary Formal rows, captured
/// reports, SourceBoundArithmeticObligation or a generic certificate. Its
/// generic diagnostic view remains non-promotable until a separate real
/// runtime storage owner performs the consuming physical binding.
#[derive(Debug)]
pub struct ConditionallyReplayedDefinedPeer {
    requirement: ConditionalPeerEntryRequirement,
    statement: ProofObligation,
    covered: Vec<InstId>,
}
impl ConditionallyReplayedDefinedPeer {
    pub fn requirement(&self) -> &ConditionalPeerEntryRequirement {
        &self.requirement
    }
    pub fn statement(&self) -> &ProofObligation {
        &self.statement
    }
    pub fn covered_instructions(&self) -> &[InstId] {
        &self.covered
    }
    pub fn original_caller(&self) -> &CapturedFunctionVerificationReport {
        &self.requirement.captured
    }
    pub fn diagnostic_report(&self) -> crate::function_verifier::FunctionVerificationReport {
        use crate::function_verifier::{
            FunctionVerificationReport, InstructionReport, InstructionVerificationResult,
        };
        let original = self.original_caller().report();
        FunctionVerificationReport {
            function_name:original.function_name.clone(),precondition_failure:original.precondition_failure.clone(),
            instructions:original.instructions.iter().map(|row|InstructionReport {
                inst_index:row.inst_index,opcode:row.opcode,
                result:InstructionVerificationResult::Unverified {reason:"complete peer replay is conditional: real entry storage is still pending".into()},
            }).collect(),
        }
    }
}

impl ConditionalPeerEntryRequirement {
    pub fn module_digest(&self) -> ProofDigest {
        self.module
    }
    pub fn function(&self) -> FuncId {
        self.function
    }
    pub fn required_private_stack_bytes(&self) -> usize {
        self.private_bytes
    }
    /// Number of scalar input words established by the original-source check.
    /// This diagnostic cannot manufacture a physical invocation permission.
    pub fn argument_count(&self) -> usize {
        usize::from(self.argument_count)
    }
    pub fn final_code_digest(&self) -> ProofDigest {
        self.final_code
    }
    pub fn final_image_digest(&self) -> ProofDigest {
        self.final_image
    }
    pub fn caller_offset(&self) -> usize {
        self.caller_offset
    }
    pub fn callee(&self) -> FuncId {
        self.callee
    }
    pub fn callee_offset(&self) -> usize {
        self.callee_offset
    }
    pub fn call_site(&self) -> usize {
        self.call_site
    }
    pub fn check_entry_binding(
        &self,
        module: &Module,
        function: FuncId,
        code: &[u8],
        image: &[u8],
    ) -> Result<()> {
        if self.module != module.stable_digest()
            || self.function != function
            || module.function_body_digest(function) != Ok(self.body)
            || module
                .function_by_id(function)
                .and_then(|f| module.func_type(f.ty))
                .is_none_or(|signature| signature.params.len() != self.argument_count())
            || self.final_code != ProofDigest::sha256(Sha256::digest(code).into())
            || self.final_image != ProofDigest::sha256(Sha256::digest(image).into())
            || !self
                .captured
                .matches_request_capture(&self.original_request)
            || self.captured.aarch64_input_digest() != Some(&self.machine_input)
        {
            return Err(DefinedPeerCallError::EntryBinding);
        }
        Ok(())
    }
}

// No machine effect is inferred from an arbitrary pseudo flag. This is the
// canonical post-allocation no-op for forwarding the incoming C-ABI X0.
fn is_x0_argument_self_copy(row: &trust_cg_ir::MachInst) -> bool {
    use trust_cg_ir::{InstFlags, MachOperand, regs::X0};
    row.opcode == Op::Nop
        && row.flags == (InstFlags::IS_PSEUDO | InstFlags::IS_CALL_ARG_SETUP)
        && row.operands == [MachOperand::PReg(X0), MachOperand::PReg(X0)]
        && row.implicit_defs.is_empty()
        && row.implicit_uses.is_empty()
        && row.proof.is_none()
}

#[cfg(test)]
mod argument_setup_tests {
    use super::*;
    use trust_cg_ir::{
        InstFlags, MachInst, MachOperand,
        regs::{W0, X0, X1},
    };

    #[test]
    fn only_effect_free_full_x0_argument_self_copy_is_admitted() {
        let row = MachInst::with_flags(
            Op::Nop,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X0)],
            InstFlags::IS_PSEUDO | InstFlags::IS_CALL_ARG_SETUP,
        );
        assert!(is_x0_argument_self_copy(&row));
        for register in [X1, W0] {
            let mut wrong = row.clone();
            wrong.operands[1] = MachOperand::PReg(register);
            assert!(!is_x0_argument_self_copy(&wrong));
            wrong.operands[0] = MachOperand::PReg(register);
            assert!(!is_x0_argument_self_copy(&wrong));
        }
        let mut wrong = row.clone();
        wrong.flags.remove(InstFlags::IS_PSEUDO);
        assert!(!is_x0_argument_self_copy(&wrong));
        wrong = row.clone();
        wrong.flags.insert(InstFlags::WRITES_MEMORY);
        assert!(!is_x0_argument_self_copy(&wrong));
        wrong = row.clone();
        wrong.implicit_defs = &[X1];
        assert!(!is_x0_argument_self_copy(&wrong));
        wrong = row.clone();
        wrong.implicit_uses = &[X1];
        assert!(!is_x0_argument_self_copy(&wrong));
        wrong = row;
        wrong.operands.push(MachOperand::PReg(X0));
        assert!(!is_x0_argument_self_copy(&wrong));
    }
}
