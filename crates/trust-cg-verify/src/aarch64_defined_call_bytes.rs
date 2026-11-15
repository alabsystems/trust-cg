// Copyright 2026 Andrew Yates | Apache-2.0

//! Complete bounded defined-call byte correspondence, using the existing
//! affine word evaluator. This is an executable semantic check, not a Formal
//! caller report, a SourceBoundReplay capability, or installation authority.
//! Module validity, original source/Core licensing and placement remain owed.
//!
//! Domain: attribute-free C () -> U64 CALL/RET to one same-module constant
//! leaf, with the exact standard sixteen-byte caller FP/LR envelope. The leaf
//! is attached to its original captured Formal request and independently checked
//! complete bytes. No external, recursive, indirect or additional call is
//! interpreted. No call-result or return premise is assumed: the finite caller
//! walk composes the checked leaf result/normal return, then checks X0 at RET.
//! Entry SP must be aligned, nonwrapping, and backed by the full live writable
//! private extent returned below. No owner here grants that storage permission.

use super::super::defined_callee::AttachedDefinedAffineCallee;
use super::{AffineByteError, ByteState, ScalarType, ScalarValue, invalid, linear_envelope, word};
use crate::aarch64_instruction_word_proofs::{DecodedWord, decode_word};
use crate::function_request::FunctionVerificationRequest;
use trust_cg_lower::instructions::{DirectCallBinding, Opcode};
use trust_cg_lower::{Function, Type};
use trust_ir::{CallingConv, Inst, Module, Ty};

/// Borrowed immutable endpoints of a complete executable byte check. The
/// caller's source and LIR retain their actual call and returned SSA value;
/// neither is replaced with a constant. This grants no proof or install grade.
#[derive(Debug)]
pub struct CheckedAarch64DefinedCallBytes<'c, 'a> {
    module: &'a Module,
    source: &'a trust_ir::Function,
    lir: &'a Function,
    image: &'a [u8],
    caller: &'a [u8],
    caller_offset: usize,
    callee_offset: usize,
    callee: &'c AttachedDefinedAffineCallee<'a>,
    private_stack_bytes: usize,
    result: u64,
}

impl<'c, 'a> CheckedAarch64DefinedCallBytes<'c, 'a> {
    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        self.source
    }
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    pub fn linked_image(&self) -> &'a [u8] {
        self.image
    }
    pub fn code(&self) -> &'a [u8] {
        self.caller
    }
    pub fn caller_offset(&self) -> usize {
        self.caller_offset
    }
    pub fn callee_offset(&self) -> usize {
        self.callee_offset
    }
    pub fn callee(&self) -> &'c AttachedDefinedAffineCallee<'a> {
        self.callee
    }
    pub fn required_private_stack_bytes(&self) -> usize {
        self.private_stack_bytes
    }
    pub fn required_entry_sp_alignment(&self) -> usize {
        16
    }
    pub fn result_u64(&self) -> u64 {
        self.result
    }
}

fn source_call<'a>(
    module: &'a Module,
    ordinal: usize,
    lir: &Function,
    callee: &trust_ir::Function,
) -> Result<&'a trust_ir::Function, AffineByteError> {
    let source = module
        .functions
        .get(ordinal)
        .ok_or_else(|| invalid(0, "foreign caller"))?;
    if !module.functions.iter().any(|f| std::ptr::eq(f, callee)) {
        return Err(invalid(0, "foreign callee source allocation"));
    }
    for function in [source, callee] {
        let signature = module
            .func_types
            .get(function.ty.index() as usize)
            .ok_or_else(|| invalid(0, "foreign signature"))?;
        if function.calling_conv != CallingConv::C
            || function.attrs != Default::default()
            || signature.is_vararg
            || !signature.params.is_empty()
            || signature.returns.as_slice() != [Ty::U64]
            || function.blocks.len() != 1
            || function.entry_block().is_none_or(|b| !b.params.is_empty())
            || module
                .functions
                .iter()
                .filter(|f| f.id == function.id || f.name == function.name)
                .count()
                != 1
        {
            return Err(invalid(
                0,
                "requires unambiguous attribute-free C () -> U64 endpoints",
            ));
        }
    }
    if source.id == callee.id || callee.linkage != trust_ir::Linkage::Internal {
        return Err(invalid(0, "requires a distinct internal defined leaf"));
    }
    let leaf = &callee.blocks[0].body;
    if leaf.len() != 2
        || leaf[0].results.len() != 1
        || !leaf[1].results.is_empty()
        || !matches!(&leaf[0].inst, Inst::Const { ty: Ty::U64, .. })
        || !matches!(&leaf[1].inst, Inst::Return { values } if values == &leaf[0].results)
    {
        return Err(invalid(0, "callee is not a constant/return leaf"));
    }
    let body = &source.blocks[0].body;
    if body.len() != 2
        || body[0].results.len() != 1
        || !body[1].results.is_empty()
        || !matches!(&body[0].inst, Inst::Call { callee: id, args } if *id == callee.id && args.is_empty())
        || !matches!(&body[1].inst, Inst::Return { values } if values == &body[0].results)
    {
        return Err(invalid(
            0,
            "caller is not the original defined CALL/RET pair",
        ));
    }
    let block = lir
        .blocks
        .get(&lir.entry_block)
        .ok_or_else(|| invalid(0, "missing LIR entry"))?;
    if lir.name != source.name
        || lir.blocks.len() != 1
        || !block.params.is_empty()
        || !lir.signature.params.is_empty()
        || lir.signature.returns.as_slice() != [Type::I64]
        || !lir.stack_slots.is_empty()
        || block.instructions.len() != 2
    {
        return Err(invalid(
            0,
            "caller LIR is outside the no-argument call/return profile",
        ));
    }
    let call = &block.instructions[0];
    let ret = &block.instructions[1];
    if !matches!(&call.opcode, Opcode::Call { name, binding: DirectCallBinding::ExactModuleFunction { function } }
        if name == &callee.name && *function == callee.id.index())
        || !call.args.is_empty()
        || call.results.len() != 1
        || !matches!(ret.opcode, Opcode::Return)
        || ret.args != call.results
        || !ret.results.is_empty()
        || lir
            .trust_ir_origins
            .get(&lir.entry_block)
            .is_none_or(|origins| {
                origins.len() != 2
                    || origins[0].is_none_or(|o| o.0 != 0)
                    || origins[1].is_none_or(|o| o.0 != 1)
            })
    {
        return Err(invalid(
            0,
            "original/LIR call or returned SSA identity differs",
        ));
    }
    Ok(source)
}

/// Walk finite actual caller words. Only the existing affine evaluator handles
/// scalar instructions. BL composes an already independently checked complete
/// callee, discards every ABI-volatile value/flag, and installs its checked X0.
/// The exact envelope saves entry LR before BL writes PC+4 and restores it
/// before the final RET X30. Body words cannot touch SP, FP, LR, saved GPRs,
/// SIMD, memory or system state. The callee's private window is strictly below
/// the caller's current SP, disjoint from its saved FP/LR.
fn call_result(
    code: &[u8],
    caller_offset: usize,
    callee_offset: usize,
    result: ScalarValue,
) -> Result<(), AffineByteError> {
    let (start, end, frame) = linear_envelope(code)?;
    if frame != 16 {
        return Err(invalid(
            0,
            "defined caller must save entry LR in the standard frame",
        ));
    }
    let mut state = ByteState::new(64, 0)?;
    let mut called = false;
    for index in start..end {
        let instruction = word(code, index);
        if let Some(DecodedWord::BranchImm { op: 1, imm26 }) = decode_word(instruction) {
            if called {
                return Err(invalid(index * 4, "multiple calls"));
            }
            let pc = caller_offset
                .checked_add(index * 4)
                .and_then(|v| i64::try_from(v).ok())
                .ok_or_else(|| invalid(index * 4, "call PC overflow"))?;
            let displacement = (i64::from(imm26) << 38) >> 36;
            if pc.checked_add(displacement) != i64::try_from(callee_offset).ok() {
                return Err(invalid(
                    index * 4,
                    "decoded BL target differs from attached callee",
                ));
            }
            // All previous volatile values/flags become unknown; do not
            // accidentally carry caller temporaries across the actual call.
            state = ByteState::new(64, 0)?;
            state.registers.write(0, result, index * 4)?;
            called = true;
        } else {
            state.step_word(index * 4, instruction)?;
        }
    }
    if !called {
        return Err(invalid(0, "missing defined call"));
    }
    if state.result(Some(ScalarType::Integer(64)), code.len() - 4)? != Some(result) {
        return Err(AffineByteError::ReturnMismatch);
    }
    Ok(())
}

/// Check original source/LIR and exact disjoint slices in ONE immutable linked
/// image. A copied callee byte vector is not an attachment to this image.
/// Pending relocations are not accepted: every supplied BL field is decoded.
#[allow(clippy::too_many_arguments)]
pub fn check_aarch64_defined_call_bytes<'c, 'a>(
    module: &'a Module,
    caller_ordinal: usize,
    lir: &'a Function,
    image: &'a [u8],
    caller_offset: usize,
    caller_len: usize,
    callee_offset: usize,
    callee: &'c AttachedDefinedAffineCallee<'a>,
    request: &FunctionVerificationRequest,
) -> Result<CheckedAarch64DefinedCallBytes<'c, 'a>, AffineByteError> {
    if !callee.matches_request_capture(request)
        || !std::ptr::eq(module, callee.checked_bytes().module())
    {
        return Err(invalid(0, "foreign module or original request capture"));
    }
    let source = source_call(module, caller_ordinal, lir, callee.checked_bytes().source())?;
    let caller_end = caller_offset
        .checked_add(caller_len)
        .ok_or_else(|| invalid(0, "caller extent overflow"))?;
    let callee_code = callee.checked_bytes().code();
    let callee_end = callee_offset
        .checked_add(callee_code.len())
        .ok_or_else(|| invalid(0, "callee extent overflow"))?;
    let caller = image
        .get(caller_offset..caller_end)
        .ok_or_else(|| invalid(0, "caller outside linked image"))?;
    let linked_callee = image
        .get(callee_offset..callee_end)
        .ok_or_else(|| invalid(0, "callee outside linked image"))?;
    if !caller_offset.is_multiple_of(4)
        || !callee_offset.is_multiple_of(4)
        || (caller_offset < callee_end && callee_offset < caller_end)
        || !std::ptr::eq(linked_callee, callee_code)
    {
        return Err(invalid(
            0,
            "overlapping, unaligned or detached linked endpoints",
        ));
    }
    let result = callee
        .checked_bytes()
        .scalar_result()
        .ok_or(AffineByteError::ReturnMismatch)?;
    let result_u64 = result
        .as_constant()
        .ok_or(AffineByteError::ReturnMismatch)?;
    call_result(caller, caller_offset, callee_offset, result)?;
    let private_stack_bytes = 16usize
        .checked_add(callee.summary().effects().required_private_stack_bytes())
        .ok_or_else(|| invalid(0, "composed private stack overflow"))?;
    Ok(CheckedAarch64DefinedCallBytes {
        module,
        source,
        lir,
        image,
        caller,
        caller_offset,
        callee_offset,
        callee,
        private_stack_bytes,
        result: result_u64,
    })
}

#[cfg(test)]
#[path = "aarch64_defined_call_bytes_tests.rs"]
mod tests;
