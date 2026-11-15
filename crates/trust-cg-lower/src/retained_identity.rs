// trust-cg-lower/retained_identity.rs - Retained strict-LIR authority identity
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Canonical identity of retained strict LIR and its proof context.
//!
//! This is an authority-boundary encoding, not a persistence format.  It is
//! deliberately explicit and versioned: all integers are big-endian, every
//! sequence/string/byte string has a `u64` length, options have a byte tag, and
//! enums have stable `u16` tags.  Map/set entries are sorted by their semantic
//! keys before emission.  No `Debug` or derived serialization participates.
//!
//! The payload is walked twice: once into a byte counter and once directly into
//! SHA-256 using TrustIR's standard domain framing.  Only short borrowed index
//! vectors used to order maps/sets are allocated; the module-sized payload is
//! never duplicated.

use trust_cg_ir::function::{
    DebugBaseType, DebugEnumType, DebugEnumerator, DebugLocalVariable, DebugStructMember,
    DebugStructType, DebugVariableStorage, EhTypeTableEntries, EnumTagWidth, FunctionDebugMeta,
    StackLimitOverflow, StackLimitRequest, StackLimitSource, StackProtectorMode,
    StackSlotAllocationKind, StackSlotSizeSource,
};
use trust_cg_ir::{SourceLoc, TlsModel};
use trust_ir::Constant;
use trust_ir::pred::{Pred, Space, Universe};
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ProofDigest, ProofDigestSha256DomainStream,
    ProofFormula,
};

use crate::adapter::{
    Proof, ProofContext, ProofContextIdentityView, ProofDivergence, ProofDropCode,
    ProofDropDiagnostic, ProofFact,
};
use crate::borrow_frame_undef::{
    BorrowFrameUndefReceipt, BorrowKind, BorrowRecord, FrameRecord, FrameSlotRecord,
    RetiredBorrowRecord, UndefRecord,
};
use crate::function::{
    AbiSretParam, BasicBlock, DebugValueBinding, EhCallSite, EhFunctionInfo, EhLandingPad,
    Function, ParamPointeeType, Signature, StackSlotInfo,
};
use crate::instructions::{
    AtomicOrdering, AtomicRmwOp, DirectCallBinding, FloatCC, Instruction, IntCC, Opcode,
};
use crate::lattice_guard::LatticeBoundsCapability;
use crate::types::Type;

const DOMAIN: &str = "trust-cg.retained-strict-lir-proof-context.v1";
// v2 added the indirect-return (`sret`) ABI facts (`abi_sret_param`,
// `sret_arg_callees`). They change emitted code, so a v1 payload must not be
// read as a v2 one.
// v3 authenticates `ProofFormula::bindings` (trust-ir v41): each clause free
// name's sort and IR place. The sort is soundness-bearing (a width-stripped
// clause can be "discharged" over a domain the program never had), so two
// formulas that differ only in their bindings must not share an identity.
// v4 added `sret_arg_indirect_callees`, the indirect-call half of the `sret`
// ABI facts: it moves an argument between X8 and X0, so it is emitted code.
// v5 added `eh_type_table`, the typeinfo symbols a function's typed catches
// bind to: two functions whose pads index different tables dispatch to
// different handlers. v6 spells it as a tagged enum (0 = the entry list,
// 1 = a trust-ir v50 splat: one symbol and a length), so a splat table is
// authenticated in constant size.
// v7 added the borrow / binding-frame / Undef legalization receipt
// (`ProofContext::borrow_frame_undef`): what that stage lowered is part of
// the retained identity of the LIR it produced.
// v8 added `target_features`, the function's stated target features: they
// decide which instructions its body selects, so they are emitted code.
// v9 added `FunctionDebugMeta::display_name`, the subprogram name the DWARF
// sections carry: two functions that differ only in it emit different bytes.
// v10 authenticates Invoke resolution binding as well as both EH successors.
// v11 authenticates adapter-produced aggregate call/field transport intent.
// v12 binds actual source Alloca identities, types/counts and emitted slots.
const PAYLOAD_SCHEMA_VERSION: u32 = 12;

/// A retained identity is unavailable unless its entire canonical payload fits
/// the framing and both immutable passes agree exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum RetainedIdentityError {
    #[error("retained LIR identity exceeds canonical u64 framing")]
    LengthOverflow,
    #[error("retained LIR identity payload differs from its counted length")]
    PayloadLengthMismatch,
}

trait Sink {
    fn write(&mut self, bytes: &[u8]);
    fn fail(&mut self, error: RetainedIdentityError);
}

struct CountSink(Result<u64, RetainedIdentityError>);

impl Default for CountSink {
    fn default() -> Self {
        Self(Ok(0))
    }
}

impl Sink for CountSink {
    fn write(&mut self, bytes: &[u8]) {
        self.0 = self.0.and_then(|count| {
            let len =
                u64::try_from(bytes.len()).map_err(|_| RetainedIdentityError::LengthOverflow)?;
            count
                .checked_add(len)
                .ok_or(RetainedIdentityError::LengthOverflow)
        });
    }

    fn fail(&mut self, error: RetainedIdentityError) {
        self.0 = self.0.and(Err(error));
    }
}

struct HashSink {
    stream: ProofDigestSha256DomainStream,
    status: Result<(), RetainedIdentityError>,
}

impl Sink for HashSink {
    fn write(&mut self, bytes: &[u8]) {
        if self.status.is_ok() {
            self.status = self
                .stream
                .update(bytes)
                .map_err(|_| RetainedIdentityError::PayloadLengthMismatch);
        }
    }

    fn fail(&mut self, error: RetainedIdentityError) {
        self.status = self.status.and(Err(error));
    }
}

impl HashSink {
    fn finish(self) -> Result<ProofDigest, RetainedIdentityError> {
        self.status?;
        self.stream
            .finish()
            .map_err(|_| RetainedIdentityError::PayloadLengthMismatch)
    }
}

struct Encoder<'a, S>(&'a mut S);

impl<S: Sink> Encoder<'_, S> {
    fn raw(&mut self, bytes: &[u8]) {
        self.0.write(bytes);
    }

    fn bool(&mut self, value: bool) {
        self.u8(u8::from(value));
    }

    fn u8(&mut self, value: u8) {
        self.raw(&[value]);
    }

    fn u16(&mut self, value: u16) {
        self.raw(&value.to_be_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.raw(&value.to_be_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.raw(&value.to_be_bytes());
    }

    fn u128(&mut self, value: u128) {
        self.raw(&value.to_be_bytes());
    }

    fn i64(&mut self, value: i64) {
        self.raw(&value.to_be_bytes());
    }

    fn i128(&mut self, value: i128) {
        self.raw(&value.to_be_bytes());
    }

    fn len(&mut self, value: usize) {
        match u64::try_from(value) {
            Ok(value) => self.u64(value),
            Err(_) => self.0.fail(RetainedIdentityError::LengthOverflow),
        }
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.len(bytes.len());
        self.raw(bytes);
    }

    fn str(&mut self, value: &str) {
        self.bytes(value.as_bytes());
    }

    fn option<T>(&mut self, value: Option<T>, write: impl FnOnce(&mut Self, T)) {
        match value {
            None => self.u8(0),
            Some(value) => {
                self.u8(1);
                write(self, value);
            }
        }
    }
}

/// Authenticate every retained strict-LIR byte-equivalent field and every
/// proof-context field without materializing a second module-sized buffer.
pub fn retained_lir_proof_context_digest(
    functions: &[(Function, ProofContext)],
) -> Result<ProofDigest, RetainedIdentityError> {
    let mut count = CountSink::default();
    encode_payload(&mut Encoder(&mut count), functions);

    let mut hash = HashSink {
        stream: ProofDigest::sha256_domain_stream(DOMAIN, count.0?),
        status: Ok(()),
    };
    encode_payload(&mut Encoder(&mut hash), functions);
    hash.finish()
}

fn encode_payload<S: Sink>(encoder: &mut Encoder<'_, S>, functions: &[(Function, ProofContext)]) {
    encoder.u32(PAYLOAD_SCHEMA_VERSION);
    encoder.len(functions.len());
    for (function, proofs) in functions {
        encode_function(encoder, function);
        encode_proof_context(encoder, proofs.retained_identity_view());
    }
}

fn encode_function<S: Sink>(encoder: &mut Encoder<'_, S>, function: &Function) {
    let Function {
        name,
        signature,
        blocks,
        block_order,
        trust_ir_origins,
        entry_block,
        stack_slots,
        value_types,
        pure_callees,
        libm_pure_callees,
        debug_meta,
        debug_value_bindings,
        stack_protector,
        stack_limit,
        param_pointee_types,
        abi_sret_param,
        sret_arg_callees,
        sret_arg_indirect_callees,
        eh_info,
        eh_type_table,
        target_features,
    } = function;

    encoder.str(name);
    encode_signature(encoder, signature);

    let mut blocks: Vec<_> = blocks.iter().collect();
    blocks.sort_unstable_by_key(|(block, _)| block.0);
    encoder.len(blocks.len());
    for (block, body) in blocks {
        encoder.u32(block.0);
        encode_basic_block(encoder, body);
    }

    encoder.len(block_order.len());
    for block in block_order {
        encoder.u32(block.0);
    }

    let mut origins: Vec<_> = trust_ir_origins.iter().collect();
    origins.sort_unstable_by_key(|(block, _)| block.0);
    encoder.len(origins.len());
    for (block, entries) in origins {
        encoder.u32(block.0);
        encoder.len(entries.len());
        for origin in entries {
            encoder.option(origin.as_ref(), |encoder, origin| encoder.u32(origin.0));
        }
    }

    encoder.u32(entry_block.0);
    encoder.len(stack_slots.len());
    for slot in stack_slots {
        encode_stack_slot(encoder, slot);
    }

    let mut value_types: Vec<_> = value_types.iter().collect();
    value_types.sort_unstable_by_key(|(value, _)| value.0);
    encoder.len(value_types.len());
    for (value, ty) in value_types {
        encoder.u32(value.0);
        encode_type(encoder, ty);
    }

    let mut pure_callees: Vec<_> = pure_callees.iter().map(String::as_str).collect();
    pure_callees.sort_unstable();
    encoder.len(pure_callees.len());
    for callee in pure_callees {
        encoder.str(callee);
    }

    let mut libm_pure_callees: Vec<_> = libm_pure_callees.iter().map(String::as_str).collect();
    libm_pure_callees.sort_unstable();
    encoder.len(libm_pure_callees.len());
    for callee in libm_pure_callees {
        encoder.str(callee);
    }

    encode_debug_meta(encoder, debug_meta);
    encoder.len(debug_value_bindings.len());
    for binding in debug_value_bindings {
        let DebugValueBinding { var_id, value } = binding;
        encoder.u32(var_id.0);
        encoder.u32(value.0);
    }
    encode_stack_protector(encoder, *stack_protector, stack_limit.as_ref());
    encoder.len(param_pointee_types.len());
    for pointee in param_pointee_types {
        let ParamPointeeType {
            param_index,
            pointee_ty,
        } = pointee;
        encoder.u32(*param_index);
        encode_type(encoder, pointee_ty);
    }
    // The indirect-return (`sret`) convention is an ABI FACT, not a hint: two
    // functions that disagree about it emit different machine code and must not
    // hash to the same retained identity.
    encoder.option(abi_sret_param.as_ref(), |encoder, sret| {
        let AbiSretParam { param_index } = sret;
        encoder.u32(*param_index);
    });
    let mut sret_arg_callees: Vec<_> = sret_arg_callees.iter().map(String::as_str).collect();
    sret_arg_callees.sort_unstable();
    encoder.len(sret_arg_callees.len());
    for callee in sret_arg_callees {
        encoder.str(callee);
    }
    let mut sret_arg_indirect_callees: Vec<u32> = sret_arg_indirect_callees
        .iter()
        .map(|value| value.0)
        .collect();
    sret_arg_indirect_callees.sort_unstable();
    encoder.len(sret_arg_indirect_callees.len());
    for callee in sret_arg_indirect_callees {
        encoder.u32(callee);
    }
    encode_eh_info(encoder, eh_info);
    // The EH type table binds typed catches to typeinfo symbols: two functions
    // whose pads index different tables dispatch to different handlers. Its
    // spelling is canonical (`EhTypeTable`), so the tagged spelling is the
    // table's identity, and a splat is encoded in constant size.
    match eh_type_table.entries() {
        EhTypeTableEntries::List(symbols) => {
            encoder.u16(0);
            encoder.len(symbols.len());
            for symbol in symbols {
                encoder.str(symbol);
            }
        }
        EhTypeTableEntries::Splat { symbol, len } => {
            encoder.u16(1);
            encoder.str(symbol);
            encoder.u64(len);
        }
    }
    // The function's stated target features select its instructions (LSE vs
    // LL/SC, CRC32 vs its baseline expansion), so they are emitted code. In
    // stated order: the adapter admits the producer's list as given.
    encoder.len(target_features.len());
    for feature in target_features {
        encoder.str(feature);
    }
}

fn encode_signature<S: Sink>(encoder: &mut Encoder<'_, S>, signature: &Signature) {
    let Signature { params, returns } = signature;
    encoder.len(params.len());
    for ty in params {
        encode_type(encoder, ty);
    }
    encoder.len(returns.len());
    for ty in returns {
        encode_type(encoder, ty);
    }
}

fn encode_basic_block<S: Sink>(encoder: &mut Encoder<'_, S>, block: &BasicBlock) {
    let BasicBlock {
        params,
        instructions,
        source_locs,
    } = block;
    encoder.len(params.len());
    for (value, ty) in params {
        encoder.u32(value.0);
        encode_type(encoder, ty);
    }
    encoder.len(instructions.len());
    for instruction in instructions {
        encode_instruction(encoder, instruction);
    }
    encoder.len(source_locs.len());
    for loc in source_locs {
        encoder.option(loc.as_ref(), encode_source_loc);
    }
}

fn encode_source_loc<S: Sink>(encoder: &mut Encoder<'_, S>, loc: &SourceLoc) {
    let SourceLoc { file, line, col } = loc;
    encoder.u32(*file);
    encoder.u32(*line);
    encoder.u32(*col);
}

fn encode_stack_slot<S: Sink>(encoder: &mut Encoder<'_, S>, slot: &StackSlotInfo) {
    let StackSlotInfo {
        size,
        align,
        allocation,
    } = slot;
    encoder.u32(*size);
    encoder.u32(*align);
    match allocation {
        StackSlotAllocationKind::Fixed => encoder.u16(0),
        StackSlotAllocationKind::RuntimeSized { size_source } => {
            encoder.u16(1);
            match size_source {
                StackSlotSizeSource::Value(value) => {
                    encoder.u16(0);
                    encoder.u32(*value);
                }
                StackSlotSizeSource::Unknown => encoder.u16(1),
            }
        }
    }
}

fn encode_type<S: Sink>(encoder: &mut Encoder<'_, S>, ty: &Type) {
    match ty {
        Type::I8 => encoder.u16(0),
        Type::I16 => encoder.u16(1),
        Type::I32 => encoder.u16(2),
        Type::I64 => encoder.u16(3),
        Type::I128 => encoder.u16(4),
        Type::F16 => encoder.u16(5),
        Type::F32 => encoder.u16(6),
        Type::F64 => encoder.u16(7),
        Type::B1 => encoder.u16(8),
        Type::V128 => encoder.u16(9),
        Type::V64 => encoder.u16(10),
        Type::Struct(fields) => {
            encoder.u16(11);
            encoder.len(fields.len());
            for field in fields {
                encode_type(encoder, field);
            }
        }
        Type::Array(element, count) => {
            encoder.u16(12);
            encode_type(encoder, element);
            encoder.u32(*count);
        }
        Type::Enum {
            tag_width,
            variants,
        } => {
            encoder.u16(13);
            encode_enum_tag_width(encoder, *tag_width);
            encoder.len(variants.len());
            for variant in variants {
                encoder.len(variant.len());
                for field in variant {
                    encode_type(encoder, field);
                }
            }
        }
    }
}

fn encode_enum_tag_width<S: Sink>(encoder: &mut Encoder<'_, S>, width: EnumTagWidth) {
    encoder.u16(match width {
        EnumTagWidth::U8 => 0,
        EnumTagWidth::U16 => 1,
        EnumTagWidth::U32 => 2,
        EnumTagWidth::U64 => 3,
    });
}

fn encode_debug_meta<S: Sink>(encoder: &mut Encoder<'_, S>, meta: &FunctionDebugMeta) {
    let FunctionDebugMeta {
        source_file,
        display_name,
        decl_line,
        param_names,
        local_variables,
        struct_types,
        enum_types,
    } = meta;
    encoder.option(source_file.as_deref(), Encoder::str);
    encoder.option(display_name.as_deref(), Encoder::str);
    encoder.u32(*decl_line);
    encoder.len(param_names.len());
    for name in param_names {
        encoder.str(name);
    }
    encoder.len(local_variables.len());
    for local in local_variables {
        let DebugLocalVariable {
            name,
            ty,
            storage,
            decl_line,
        } = local;
        encoder.str(name);
        encode_debug_base_type(encoder, *ty);
        match storage {
            DebugVariableStorage::StackSlot(slot) => {
                encoder.u16(0);
                encoder.u32(*slot);
            }
            DebugVariableStorage::ConstantInt(value) => {
                encoder.u16(1);
                encoder.u64(*value);
            }
            DebugVariableStorage::ProvenanceVar(var) => {
                encoder.u16(2);
                encoder.u32(var.0);
            }
        }
        encoder.u32(*decl_line);
    }
    encoder.len(struct_types.len());
    for structure in struct_types {
        let DebugStructType {
            name,
            byte_size,
            members,
        } = structure;
        encoder.str(name);
        encoder.u32(*byte_size);
        encoder.len(members.len());
        for member in members {
            let DebugStructMember { name, offset, ty } = member;
            encoder.str(name);
            encoder.u32(*offset);
            encode_debug_base_type(encoder, *ty);
        }
    }
    encoder.len(enum_types.len());
    for enumeration in enum_types {
        let DebugEnumType {
            name,
            byte_size,
            underlying_type,
            enumerators,
        } = enumeration;
        encoder.str(name);
        encoder.u32(*byte_size);
        encode_debug_base_type(encoder, *underlying_type);
        encoder.len(enumerators.len());
        for enumerator in enumerators {
            let DebugEnumerator { name, value } = enumerator;
            encoder.str(name);
            encoder.i64(*value);
        }
    }
}

fn encode_debug_base_type<S: Sink>(encoder: &mut Encoder<'_, S>, ty: DebugBaseType) {
    encoder.u16(match ty {
        DebugBaseType::I8 => 0,
        DebugBaseType::I16 => 1,
        DebugBaseType::I32 => 2,
        DebugBaseType::I64 => 3,
        DebugBaseType::I128 => 4,
        DebugBaseType::F32 => 5,
        DebugBaseType::F64 => 6,
        DebugBaseType::Bool => 7,
        DebugBaseType::U8 => 8,
        DebugBaseType::U16 => 9,
        DebugBaseType::U32 => 10,
        DebugBaseType::U64 => 11,
        DebugBaseType::U128 => 12,
        DebugBaseType::Ptr => 13,
    });
}

/// The stack-protector mode, then the U10 stack-limit request when present.
///
/// The mode word was 0 or 1 before U10. A request sets bit 15 of that word
/// and its fields follow, so a non-requesting function keeps its identity
/// bytes (no cache key moves) and the encoding stays injective: no earlier
/// word had bit 15 set, and the fields follow only when it is.
fn encode_stack_protector<S: Sink>(
    encoder: &mut Encoder<'_, S>,
    mode: StackProtectorMode,
    stack_limit: Option<&StackLimitRequest>,
) {
    const STACK_LIMIT_PRESENT: u16 = 0x8000;
    let mode_word = match mode {
        StackProtectorMode::None => 0,
        StackProtectorMode::StackGuard => 1,
    };
    let Some(request) = stack_limit else {
        encoder.u16(mode_word);
        return;
    };
    encoder.u16(mode_word | STACK_LIMIT_PRESENT);
    let StackLimitRequest {
        param,
        source,
        overflow,
    } = request;
    encoder.u16(u16::from(*param));
    match source {
        StackLimitSource::Value => encoder.u16(0),
        StackLimitSource::Pointee { offset } => {
            encoder.u16(1);
            encoder.u16(*offset);
        }
    }
    match overflow {
        StackLimitOverflow::Handler { symbol } => {
            encoder.u16(0);
            encoder.str(symbol);
        }
        StackLimitOverflow::Trap => encoder.u16(1),
    }
}

fn encode_eh_info<S: Sink>(encoder: &mut Encoder<'_, S>, info: &EhFunctionInfo) {
    let EhFunctionInfo {
        personality,
        landing_pads,
        call_sites,
    } = info;
    encoder.option(personality.as_deref(), Encoder::str);
    encoder.len(landing_pads.len());
    for pad in landing_pads {
        let EhLandingPad {
            block,
            catch_type_indices,
            is_cleanup,
        } = pad;
        encoder.u32(block.0);
        encoder.len(catch_type_indices.len());
        for index in catch_type_indices {
            encoder.u32(*index);
        }
        encoder.bool(*is_cleanup);
    }
    encoder.len(call_sites.len());
    for site in call_sites {
        let EhCallSite {
            call_block,
            landing_pad_block,
        } = site;
        encoder.u32(call_block.0);
        encoder.u32(landing_pad_block.0);
    }
}

fn encode_instruction<S: Sink>(encoder: &mut Encoder<'_, S>, instruction: &Instruction) {
    let Instruction {
        opcode,
        args,
        results,
    } = instruction;
    encode_opcode(encoder, opcode);
    encoder.len(args.len());
    for value in args {
        encoder.u32(value.0);
    }
    encoder.len(results.len());
    for value in results {
        encoder.u32(value.0);
    }
}

#[allow(clippy::too_many_lines)]
fn encode_opcode<S: Sink>(encoder: &mut Encoder<'_, S>, opcode: &Opcode) {
    match opcode {
        Opcode::Iconst { ty, imm } => {
            encoder.u16(0);
            encode_type(encoder, ty);
            encoder.i64(*imm);
        }
        Opcode::Iconst128 { lo, hi } => {
            encoder.u16(1);
            encoder.i64(*lo);
            encoder.i64(*hi);
        }
        Opcode::Fconst { ty, imm } => {
            encoder.u16(2);
            encode_type(encoder, ty);
            encoder.u64(imm.to_bits());
        }
        Opcode::Copy => encoder.u16(3),
        Opcode::Iadd => encoder.u16(4),
        Opcode::Isub => encoder.u16(5),
        Opcode::Imul => encoder.u16(6),
        Opcode::Udiv => encoder.u16(7),
        Opcode::Sdiv => encoder.u16(8),
        Opcode::Urem => encoder.u16(9),
        Opcode::Srem => encoder.u16(10),
        Opcode::GuardDivZero { obligation } => {
            encoder.u16(11);
            encoder.option(*obligation, Encoder::u64);
        }
        Opcode::GuardNull { obligation } => {
            encoder.u16(12);
            encoder.option(*obligation, Encoder::u64);
        }
        Opcode::GuardShiftRange {
            bitwidth,
            obligation,
        } => {
            encoder.u16(13);
            encoder.u16(*bitwidth);
            encoder.option(*obligation, Encoder::u64);
        }
        Opcode::GuardOverflow { op_tag, obligation } => {
            encoder.u16(14);
            encoder.i64(*op_tag);
            encoder.option(*obligation, Encoder::u64);
        }
        Opcode::GuardBoundsCheckDyn { obligation } => {
            encoder.u16(15);
            encoder.option(*obligation, Encoder::u64);
        }
        Opcode::GuardBoundsCheck { bound, obligation } => {
            encoder.u16(16);
            encoder.u64(*bound);
            encoder.option(*obligation, Encoder::u64);
        }
        Opcode::Assert => encoder.u16(17),
        Opcode::Ineg => encoder.u16(18),
        Opcode::Bnot => encoder.u16(19),
        Opcode::CtPop => encoder.u16(20),
        Opcode::Fneg => encoder.u16(21),
        Opcode::Fabs => encoder.u16(22),
        Opcode::Fsqrt => encoder.u16(23),
        Opcode::Ffloor => encoder.u16(24),
        Opcode::Fceil => encoder.u16(25),
        Opcode::Ftrunc => encoder.u16(26),
        Opcode::Ishl => encoder.u16(27),
        Opcode::Ushr => encoder.u16(28),
        Opcode::Sshr => encoder.u16(29),
        Opcode::Band => encoder.u16(30),
        Opcode::Bor => encoder.u16(31),
        Opcode::Bxor => encoder.u16(32),
        Opcode::BandNot => encoder.u16(33),
        Opcode::BorNot => encoder.u16(34),
        Opcode::Sextend { from_ty, to_ty } => {
            encoder.u16(35);
            encode_type(encoder, from_ty);
            encode_type(encoder, to_ty);
        }
        Opcode::Uextend { from_ty, to_ty } => {
            encoder.u16(36);
            encode_type(encoder, from_ty);
            encode_type(encoder, to_ty);
        }
        Opcode::ExtractBits { lsb, width } => {
            encoder.u16(37);
            encoder.u8(*lsb);
            encoder.u8(*width);
        }
        Opcode::SextractBits { lsb, width } => {
            encoder.u16(38);
            encoder.u8(*lsb);
            encoder.u8(*width);
        }
        Opcode::InsertBits { lsb, width } => {
            encoder.u16(39);
            encoder.u8(*lsb);
            encoder.u8(*width);
        }
        Opcode::V4I32MaskExtract => encoder.u16(40),
        Opcode::V16I8MaskExtract => encoder.u16(41),
        Opcode::V8I16MaskExtract => encoder.u16(42),
        Opcode::V2I64MaskExtract { result_ty } => {
            encoder.u16(43);
            encode_type(encoder, result_ty);
        }
        Opcode::V4I32Zero => encoder.u16(44),
        Opcode::V2I64Zero => encoder.u16(45),
        Opcode::V4I32PackLanes => encoder.u16(46),
        Opcode::V2I64PackLanes => encoder.u16(47),
        Opcode::V16I8PackLanes => encoder.u16(48),
        Opcode::V8I16PackLanes => encoder.u16(49),
        Opcode::V8I8PackLanes => encoder.u16(50),
        Opcode::V2I64Add => encoder.u16(51),
        Opcode::V2I64Sub => encoder.u16(52),
        Opcode::V2I64Mul => encoder.u16(53),
        Opcode::V4I32Add => encoder.u16(54),
        Opcode::V4I32Sub => encoder.u16(55),
        Opcode::V4I32Mul => encoder.u16(56),
        Opcode::V16I8Add => encoder.u16(57),
        Opcode::V16I8Sub => encoder.u16(58),
        Opcode::V16I8Mul => encoder.u16(59),
        Opcode::V8I16Add => encoder.u16(60),
        Opcode::V8I16Sub => encoder.u16(61),
        Opcode::V8I16Mul => encoder.u16(62),
        Opcode::V16I8Icmp { cond } => {
            encoder.u16(63);
            encode_int_cc(encoder, *cond);
        }
        Opcode::V8I16Icmp { cond } => {
            encoder.u16(64);
            encode_int_cc(encoder, *cond);
        }
        Opcode::V4I32Icmp { cond } => {
            encoder.u16(65);
            encode_int_cc(encoder, *cond);
        }
        Opcode::V2I64Icmp { cond } => {
            encoder.u16(66);
            encode_int_cc(encoder, *cond);
        }
        Opcode::V8I8Icmp { cond } => {
            encoder.u16(67);
            encode_int_cc(encoder, *cond);
        }
        Opcode::V4I32ExtractLane { lane } => {
            encoder.u16(68);
            encoder.u8(*lane);
        }
        Opcode::V4I32InsertLane { lane } => {
            encoder.u16(69);
            encoder.u8(*lane);
        }
        Opcode::V2I64ExtractLane { lane } => {
            encoder.u16(70);
            encoder.u8(*lane);
        }
        Opcode::V2I64InsertLane { lane } => {
            encoder.u16(71);
            encoder.u8(*lane);
        }
        Opcode::V16I8ExtractLane { lane } => {
            encoder.u16(72);
            encoder.u8(*lane);
        }
        Opcode::V16I8InsertLane { lane } => {
            encoder.u16(73);
            encoder.u8(*lane);
        }
        Opcode::V8I16ExtractLane { lane } => {
            encoder.u16(74);
            encoder.u8(*lane);
        }
        Opcode::V8I16InsertLane { lane } => {
            encoder.u16(75);
            encoder.u8(*lane);
        }
        Opcode::V4F32Fadd => encoder.u16(76),
        Opcode::V4F32Fsub => encoder.u16(77),
        Opcode::V4F32Fmul => encoder.u16(78),
        Opcode::V4F32Fdiv => encoder.u16(79),
        Opcode::V2F64Fadd => encoder.u16(80),
        Opcode::V2F64Fsub => encoder.u16(81),
        Opcode::V2F64Fmul => encoder.u16(82),
        Opcode::V2F64Fdiv => encoder.u16(83),
        Opcode::V4F32Fmuladd => encoder.u16(84),
        Opcode::V2F64Fmuladd => encoder.u16(85),
        Opcode::V2F64ExtractLane { lane } => {
            encoder.u16(86);
            encoder.u8(*lane);
        }
        Opcode::Select { cond } => {
            encoder.u16(87);
            encode_int_cc(encoder, *cond);
        }
        Opcode::Icmp { cond } => {
            encoder.u16(88);
            encode_int_cc(encoder, *cond);
        }
        Opcode::CheckedSadd => encoder.u16(89),
        Opcode::CheckedSsub => encoder.u16(90),
        Opcode::CheckedSmul => encoder.u16(91),
        Opcode::CheckedUadd => encoder.u16(92),
        Opcode::CheckedUsub => encoder.u16(93),
        Opcode::CheckedUmul => encoder.u16(94),
        Opcode::Fadd => encoder.u16(95),
        Opcode::Fsub => encoder.u16(96),
        Opcode::Fmul => encoder.u16(97),
        Opcode::Fdiv => encoder.u16(98),
        Opcode::Fma => encoder.u16(99),
        Opcode::Fmuladd => encoder.u16(100),
        Opcode::Fmin => encoder.u16(101),
        Opcode::Fmax => encoder.u16(102),
        Opcode::Fcmp { cond } => {
            encoder.u16(103);
            encode_float_cc(encoder, *cond);
        }
        Opcode::FcvtToInt { dst_ty } => {
            encoder.u16(104);
            encode_type(encoder, dst_ty);
        }
        Opcode::FcvtToUint { dst_ty } => {
            encoder.u16(105);
            encode_type(encoder, dst_ty);
        }
        Opcode::FcvtFromInt { src_ty } => {
            encoder.u16(106);
            encode_type(encoder, src_ty);
        }
        Opcode::FcvtFromUint { src_ty } => {
            encoder.u16(107);
            encode_type(encoder, src_ty);
        }
        Opcode::FPExt => encoder.u16(108),
        Opcode::FPTrunc => encoder.u16(109),
        Opcode::Trunc { to_ty } => {
            encoder.u16(110);
            encode_type(encoder, to_ty);
        }
        Opcode::Bitcast { to_ty } => {
            encoder.u16(111);
            encode_type(encoder, to_ty);
        }
        Opcode::GlobalRef { name } => {
            encoder.u16(112);
            encoder.str(name);
        }
        Opcode::FunctionAddr { name, function } => {
            encoder.u16(141);
            encoder.str(name);
            encoder.u32(*function);
        }
        Opcode::ExternRef { name } => {
            encoder.u16(113);
            encoder.str(name);
        }
        Opcode::TlsRef {
            name,
            model,
            local_exec_offset,
        } => {
            encoder.u16(114);
            encoder.str(name);
            encode_tls_model(encoder, *model);
            encoder.option(*local_exec_offset, Encoder::u32);
        }
        Opcode::StackAddr { slot } => {
            encoder.u16(115);
            encoder.u32(*slot);
        }
        Opcode::Jump { dest } => {
            encoder.u16(116);
            encoder.u32(dest.0);
        }
        Opcode::Brif {
            cond,
            then_dest,
            else_dest,
        } => {
            encoder.u16(117);
            encoder.u32(cond.0);
            encoder.u32(then_dest.0);
            encoder.u32(else_dest.0);
        }
        Opcode::Trap => encoder.u16(118),
        Opcode::Return => encoder.u16(119),
        Opcode::Call { name, binding } => {
            encoder.u16(120);
            encoder.str(name);
            encode_direct_call_binding(encoder, *binding);
        }
        Opcode::CallIndirect => encoder.u16(121),
        Opcode::CallVariadic { name, fixed_args } => {
            encoder.u16(122);
            encoder.str(name);
            encoder.u32(*fixed_args);
        }
        Opcode::Invoke {
            binding,
            name,
            normal_dest,
            unwind_dest,
        } => {
            encoder.u16(123);
            encoder.str(name);
            encode_direct_call_binding(encoder, *binding);
            encoder.u32(normal_dest.0);
            encoder.u32(unwind_dest.0);
        }
        Opcode::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            encoder.u16(124);
            encoder.bool(*is_cleanup);
            encoder.len(catch_type_indices.len());
            for index in catch_type_indices {
                encoder.u32(*index);
            }
        }
        Opcode::Resume => encoder.u16(125),
        Opcode::Switch { cases, default } => {
            encoder.u16(126);
            encoder.len(cases.len());
            for (value, block) in cases {
                encoder.i64(*value);
                encoder.u32(block.0);
            }
            encoder.u32(default.0);
        }
        Opcode::Load { ty, align } => {
            encoder.u16(127);
            encode_type(encoder, ty);
            encoder.option(*align, Encoder::u32);
        }
        Opcode::Store { ty, align } => {
            encoder.u16(128);
            encode_type(encoder, ty);
            encoder.option(*align, Encoder::u32);
        }
        Opcode::VolatileLoad { ty, align } => {
            encoder.u16(129);
            encode_type(encoder, ty);
            encoder.option(*align, Encoder::u32);
        }
        Opcode::VolatileStore { ty, align } => {
            encoder.u16(130);
            encode_type(encoder, ty);
            encoder.option(*align, Encoder::u32);
        }
        Opcode::AtomicLoad { ty, ordering } => {
            encoder.u16(131);
            encode_type(encoder, ty);
            encode_atomic_ordering(encoder, *ordering);
        }
        Opcode::AtomicStore { ty, ordering } => {
            encoder.u16(132);
            encode_type(encoder, ty);
            encode_atomic_ordering(encoder, *ordering);
        }
        Opcode::AtomicRmw { op, ty, ordering } => {
            encoder.u16(133);
            encode_atomic_rmw_op(encoder, *op);
            encode_type(encoder, ty);
            encode_atomic_ordering(encoder, *ordering);
        }
        Opcode::CmpXchg {
            ty,
            success,
            failure,
        } => {
            encoder.u16(134);
            encode_type(encoder, ty);
            encode_atomic_ordering(encoder, *success);
            encode_atomic_ordering(encoder, *failure);
        }
        Opcode::Fence { ordering } => {
            encoder.u16(135);
            encode_atomic_ordering(encoder, *ordering);
        }
        Opcode::StructGep {
            struct_ty,
            field_index,
        } => {
            encoder.u16(136);
            encode_type(encoder, struct_ty);
            encoder.u32(*field_index);
        }
        Opcode::ArrayGep { elem_ty } => {
            encoder.u16(137);
            encode_type(encoder, elem_ty);
        }
        Opcode::Memcpy => encoder.u16(138),
        Opcode::Memmove => encoder.u16(139),
        Opcode::Memset => encoder.u16(140),
        Opcode::Aarch64FmaddAsm => encoder.u16(142),
        Opcode::Aarch64FsqrtAsm => encoder.u16(143),
        Opcode::Aarch64FrintnAsm => encoder.u16(144),
        Opcode::Crc32 { bytes, castagnoli } => {
            encoder.u16(145);
            encoder.u8(*bytes);
            encoder.bool(*castagnoli);
        }
    }
}

fn encode_direct_call_binding<S: Sink>(encoder: &mut Encoder<'_, S>, binding: DirectCallBinding) {
    match binding {
        DirectCallBinding::Interposable => encoder.u16(0),
        DirectCallBinding::ExactModuleFunction { function } => {
            encoder.u16(1);
            encoder.u32(function);
        }
        DirectCallBinding::DeclaredExternalFunction { function } => {
            encoder.u16(2);
            encoder.u32(function);
        }
        DirectCallBinding::NativeDependency {
            function,
            dependency,
        } => {
            encoder.u16(3);
            encoder.u32(function);
            encoder.u32(dependency.index());
        }
    }
}

fn encode_tls_model<S: Sink>(encoder: &mut Encoder<'_, S>, model: TlsModel) {
    encoder.u16(match model {
        TlsModel::LocalExec => 0,
        TlsModel::InitialExec => 1,
        TlsModel::GeneralDynamic => 2,
        TlsModel::LocalDynamic => 3,
        TlsModel::Tlv => 4,
    });
}

fn encode_int_cc<S: Sink>(encoder: &mut Encoder<'_, S>, cond: IntCC) {
    encoder.u16(match cond {
        IntCC::Equal => 0,
        IntCC::NotEqual => 1,
        IntCC::SignedLessThan => 2,
        IntCC::SignedGreaterThanOrEqual => 3,
        IntCC::SignedGreaterThan => 4,
        IntCC::SignedLessThanOrEqual => 5,
        IntCC::UnsignedLessThan => 6,
        IntCC::UnsignedGreaterThanOrEqual => 7,
        IntCC::UnsignedGreaterThan => 8,
        IntCC::UnsignedLessThanOrEqual => 9,
    });
}

fn encode_float_cc<S: Sink>(encoder: &mut Encoder<'_, S>, cond: FloatCC) {
    encoder.u16(match cond {
        FloatCC::Equal => 0,
        FloatCC::NotEqual => 1,
        FloatCC::LessThan => 2,
        FloatCC::LessThanOrEqual => 3,
        FloatCC::GreaterThan => 4,
        FloatCC::GreaterThanOrEqual => 5,
        FloatCC::Ordered => 6,
        FloatCC::Unordered => 7,
        FloatCC::UnorderedEqual => 8,
        FloatCC::UnorderedNotEqual => 9,
        FloatCC::UnorderedLessThan => 10,
        FloatCC::UnorderedLessThanOrEqual => 11,
        FloatCC::UnorderedGreaterThan => 12,
        FloatCC::UnorderedGreaterThanOrEqual => 13,
    });
}

fn encode_atomic_ordering<S: Sink>(encoder: &mut Encoder<'_, S>, ordering: AtomicOrdering) {
    encoder.u16(match ordering {
        AtomicOrdering::Relaxed => 0,
        AtomicOrdering::Acquire => 1,
        AtomicOrdering::Release => 2,
        AtomicOrdering::AcqRel => 3,
        AtomicOrdering::SeqCst => 4,
    });
}

fn encode_atomic_rmw_op<S: Sink>(encoder: &mut Encoder<'_, S>, op: AtomicRmwOp) {
    encoder.u16(match op {
        AtomicRmwOp::Add => 0,
        AtomicRmwOp::Sub => 1,
        AtomicRmwOp::And => 2,
        AtomicRmwOp::Or => 3,
        AtomicRmwOp::Xor => 4,
        AtomicRmwOp::Xchg => 5,
        AtomicRmwOp::Max => 6,
        AtomicRmwOp::Min => 7,
        AtomicRmwOp::UMax => 8,
        AtomicRmwOp::UMin => 9,
    });
}

fn encode_proof_context<S: Sink>(
    encoder: &mut Encoder<'_, S>,
    context: ProofContextIdentityView<'_>,
) {
    let ProofContextIdentityView {
        value_proofs,
        function_proofs,
        value_facts,
        function_facts,
        noalias_param_indices,
        diagnostics,
        synthesized_discharged,
        synthesized_obligation_formulas,
        next_synthesized_obligation,
        refinement_env,
        lattice_bounds_capabilities,
        borrow_frame_undef,
        aggregate_call_intents,
        source_stack_allocations,
    } = context;

    let mut value_proofs: Vec<_> = value_proofs.iter().collect();
    value_proofs.sort_unstable_by_key(|(value, _)| value.0);
    encoder.len(value_proofs.len());
    for (value, proofs) in value_proofs {
        encoder.u32(value.0);
        encoder.len(proofs.len());
        for proof in proofs {
            encode_proof(encoder, proof);
        }
    }

    encoder.len(function_proofs.len());
    for proof in function_proofs {
        encode_proof(encoder, proof);
    }

    let mut value_facts: Vec<_> = value_facts.iter().collect();
    value_facts.sort_unstable_by_key(|(value, _)| value.0);
    encoder.len(value_facts.len());
    for (value, facts) in value_facts {
        encoder.u32(value.0);
        encoder.len(facts.len());
        for fact in facts {
            encode_proof_fact(encoder, *fact);
        }
    }

    encoder.len(function_facts.len());
    for fact in function_facts {
        encode_proof_fact(encoder, *fact);
    }

    encoder.len(noalias_param_indices.len());
    for index in noalias_param_indices {
        encoder.len(*index);
    }

    encoder.len(diagnostics.len());
    for diagnostic in diagnostics {
        encode_proof_drop_diagnostic(encoder, diagnostic);
    }

    encoder.len(synthesized_discharged.len());
    for id in synthesized_discharged {
        encoder.u64(*id);
    }

    encoder.len(synthesized_obligation_formulas.len());
    for (id, formula) in synthesized_obligation_formulas {
        encoder.u64(*id);
        encode_proof_formula(encoder, formula);
    }
    encoder.u64(next_synthesized_obligation);

    let refinement_env = refinement_env.retained_identity_view();
    let crate::lattice_guard::RefinementEnvIdentityView {
        predicates,
        universes,
    } = refinement_env;
    encoder.len(predicates.len());
    for predicate in predicates {
        encode_predicate(encoder, predicate);
    }
    encoder.len(universes.len());
    for universe in universes {
        encode_universe(encoder, universe);
    }

    encoder.len(lattice_bounds_capabilities.len());
    for capability in lattice_bounds_capabilities {
        encode_lattice_capability(encoder, capability);
    }

    encode_borrow_frame_undef_receipt(encoder, borrow_frame_undef);
    encoder.option(source_stack_allocations.source_function(), |e, id| {
        e.u32(id.index())
    });
    encoder.str(source_stack_allocations.symbol());
    encoder.len(source_stack_allocations.records().len());
    for allocation in source_stack_allocations.records() {
        use crate::source_stack_allocations::{AllocationExtent, AllocationGeometryBasis};
        encoder.u32(allocation.source_block().index());
        encoder.u32(allocation.source_instruction());
        encoder.u32(allocation.source_origin().0);
        encoder.u32(allocation.source_result().index());
        let type_identity = allocation.type_identity();
        encoder.u16(match type_identity.algorithm {
            trust_ir::proof::ProofDigestAlgorithm::Sha256 => 0,
            trust_ir::proof::ProofDigestAlgorithm::TrustIrStableV1 => 1,
        });
        encoder.raw(&type_identity.bytes);
        encoder.option(allocation.source_count(), |e, id| e.u32(id.index()));
        encoder.option(allocation.explicit_align(), |e, align| e.u64(align));
        encoder.u32(allocation.lir_result().0);
        encoder.u32(allocation.stack_slot());
        encoder.u32(allocation.element_bytes());
        encoder.u32(allocation.element_align());
        match allocation.extent() {
            AllocationExtent::One => encoder.u16(0),
            AllocationExtent::Constant(n) => {
                encoder.u16(1);
                encoder.i128(n);
            }
            AllocationExtent::BoundedUses => encoder.u16(2),
            AllocationExtent::Runtime => encoder.u16(3),
        }
        encoder.u16(match allocation.geometry_basis() {
            AllocationGeometryBasis::StorageLayout => 0,
            AllocationGeometryBasis::ValueCarrier => 1,
        });
        encode_stack_slot(encoder, &allocation.geometry());
    }
    encoder.bool(aggregate_call_intents.truncated());
    encoder.bool(aggregate_call_intents.caller().is_some());
    if let Some(caller) = aggregate_call_intents.caller() {
        encoder.u32(caller.index());
    }
    encoder.str(aggregate_call_intents.caller_name());
    encoder.len(aggregate_call_intents.calls().len());
    for call in aggregate_call_intents.calls() {
        encoder.u32(call.caller().index());
        encoder.u32(call.source_block());
        encoder.len(call.source_instruction());
        encoder.u32(call.source_origin().0);
        encoder.u32(call.callee().index());
        encoder.str(call.callee_name());
        encoder.len(call.source_arguments().len());
        for value in call.source_arguments() {
            encoder.u32(value.index());
        }
        encoder.len(call.argument_codecs().len());
        for codec in call.argument_codecs() {
            encode_aggregate_field_codec(encoder, *codec);
        }
        encoder.u32(call.source_result().index());
        encoder.u32(call.layout().source_type().index());
        for codec in call.layout().fields() {
            encode_aggregate_field_codec(encoder, *codec);
        }
        for offset in call.layout().offsets() {
            encoder.u64(*offset);
        }
        encoder.u64(call.layout().bytes());
        encoder.u64(call.layout().align());
        encoder.u32(call.lir_block().0);
        encoder.len(call.lir_instruction());
        encoder.len(call.lir_arguments().len());
        for value in call.lir_arguments() {
            encoder.u32(value.0);
        }
        encoder.u32(call.lir_result().0);
    }
    encoder.len(aggregate_call_intents.fields().len());
    for field in aggregate_call_intents.fields() {
        encoder.len(field.call());
        encoder.u32(field.source_block());
        encoder.len(field.source_instruction());
        encoder.u32(field.source_origin().0);
        encoder.u32(field.source_result().index());
        encoder.u32(field.field());
        encoder.u32(field.lir_block().0);
        encoder.len(field.lir_instruction());
        encoder.u32(field.pointer().0);
        encoder.u32(field.result().0);
    }
}

fn encode_aggregate_field_codec<S: Sink>(
    encoder: &mut Encoder<'_, S>,
    codec: crate::aggregate_call_transport::AggregateFieldCodec,
) {
    use crate::aggregate_call_transport::AggregateFieldCodec::*;
    encoder.u8(match codec {
        Signed64 => 0,
        Unsigned64 => 1,
        Pointer => 2,
    });
}

fn encode_borrow_frame_undef_receipt<S: Sink>(
    encoder: &mut Encoder<'_, S>,
    receipt: &BorrowFrameUndefReceipt,
) {
    let BorrowFrameUndefReceipt {
        borrows,
        retired_borrows,
        frames,
        undefs,
    } = receipt;
    encoder.str(crate::borrow_frame_undef::STAGE);
    encoder.str(crate::borrow_frame_undef::NO_UNDEF_MODEL);
    encoder.len(borrows.len());
    for BorrowRecord {
        source,
        root,
        kind,
        result,
        operand,
    } in borrows
    {
        encoder.u32(source.index());
        encoder.u32(root.index());
        encoder.u16(match kind {
            BorrowKind::Shared => 0,
            BorrowKind::Unique => 1,
        });
        encoder.u32(result.0);
        encoder.u32(operand.0);
    }
    encoder.len(retired_borrows.len());
    for RetiredBorrowRecord { source, borrow } in retired_borrows {
        encoder.u32(source.index());
        encoder.u32(borrow.0);
    }
    encoder.len(frames.len());
    for FrameRecord {
        source,
        frame_id,
        handle,
        stack_slot,
        bytes,
        align,
        slots,
    } in frames
    {
        encoder.u32(source.index());
        encoder.u32(*frame_id);
        encoder.u32(handle.0);
        encoder.u32(*stack_slot);
        encoder.u32(*bytes);
        encoder.u32(*align);
        encoder.len(slots.len());
        for FrameSlotRecord { offset, carrier } in slots {
            encoder.u32(*offset);
            encode_type(encoder, carrier);
        }
    }
    encoder.len(undefs.len());
    for UndefRecord {
        source,
        result,
        carrier,
    } in undefs
    {
        encoder.u32(source.index());
        encoder.u32(result.0);
        encode_type(encoder, carrier);
    }
}

fn encode_proof<S: Sink>(encoder: &mut Encoder<'_, S>, proof: &Proof) {
    match proof {
        Proof::NoOverflow { signed } => {
            encoder.u16(0);
            encoder.bool(*signed);
        }
        Proof::CarrierNoOverflow { signed } => {
            encoder.u16(1);
            encoder.bool(*signed);
        }
        Proof::InBounds { base, index } => {
            encoder.u16(2);
            encoder.u32(base.index());
            encoder.u32(index.index());
        }
        Proof::ExactInBounds { base, index, bound } => {
            encoder.u16(3);
            encoder.u32(base.0);
            encoder.u32(index.0);
            encoder.u64(*bound);
        }
        Proof::NotNull { ptr } => {
            encoder.u16(4);
            encoder.u32(ptr.index());
        }
        Proof::ValidBorrow { borrow } => {
            encoder.u16(5);
            encoder.u32(borrow.index());
        }
        Proof::InRange { lo, hi } => {
            encoder.u16(6);
            encoder.i128(*lo);
            encoder.i128(*hi);
        }
        Proof::NonZeroDivisor { divisor } => {
            encoder.u16(7);
            encoder.u32(divisor.index());
        }
        Proof::ValidShift { amount, bitwidth } => {
            encoder.u16(8);
            encoder.u32(amount.index());
            encoder.u16(*bitwidth);
        }
        Proof::Pure => encoder.u16(9),
        Proof::Associative => encoder.u16(10),
        Proof::Commutative => encoder.u16(11),
        Proof::Idempotent => encoder.u16(12),
        Proof::Refinement { pred } => {
            encoder.u16(13);
            encoder.u32(pred.index());
        }
    }
}

fn encode_proof_fact<S: Sink>(encoder: &mut Encoder<'_, S>, fact: ProofFact) {
    match fact {
        ProofFact::InBounds => encoder.u16(0),
        ProofFact::NoAlias => encoder.u16(1),
        ProofFact::Aligned(bytes) => {
            encoder.u16(2);
            encoder.u64(bytes);
        }
        ProofFact::Monotonic => encoder.u16(3),
        ProofFact::NoPanic => encoder.u16(4),
        ProofFact::NoUndef => encoder.u16(5),
        ProofFact::Deterministic => encoder.u16(6),
        ProofFact::Terminates => encoder.u16(7),
        ProofFact::DataRaceFree => encoder.u16(8),
        ProofFact::ValidDealloc => encoder.u16(9),
        ProofFact::ReadonlyTable => encoder.u16(10),
        ProofFact::AppendOnlyBuffer => encoder.u16(11),
        ProofFact::AtomicSetInsert => encoder.u16(12),
        ProofFact::ParallelMap => encoder.u16(13),
        ProofFact::BoundedLoop(bound) => {
            encoder.u16(14);
            encoder.u64(bound);
        }
        ProofFact::DivergenceClass(divergence) => {
            encoder.u16(15);
            encoder.u16(match divergence {
                ProofDivergence::Uniform => 0,
                ProofDivergence::Low => 1,
                ProofDivergence::High => 2,
            });
        }
    }
}

fn encode_proof_drop_diagnostic<S: Sink>(
    encoder: &mut Encoder<'_, S>,
    diagnostic: &ProofDropDiagnostic,
) {
    let ProofDropDiagnostic {
        fact,
        payload,
        code,
        reason,
    } = diagnostic;
    encoder.str(fact);
    encoder.option(payload.as_deref(), Encoder::str);
    encoder.u16(match code {
        ProofDropCode::Unrepresentable => 0,
        ProofDropCode::NoConsumer => 1,
        ProofDropCode::Custom => 2,
    });
    encoder.str(reason);
}

fn encode_proof_formula<S: Sink>(encoder: &mut Encoder<'_, S>, formula: &ProofFormula) {
    let ProofFormula {
        schema,
        payload,
        smtlib,
        sort,
        bindings,
    } = formula;
    encoder.str(schema);
    encoder.str(payload);
    encoder.option(smtlib.as_deref(), Encoder::str);
    encoder.option(sort.as_deref(), Encoder::str);
    // Producer order is part of the formula's content (an empty map reads as
    // UNBINDABLE, never as a wildcard), so it is emitted as given, not re-sorted.
    encoder.len(bindings.len());
    for (name, ClauseBinding { sort, place }) in bindings {
        encoder.str(name);
        encode_clause_sort(encoder, sort);
        encode_clause_place(encoder, place);
    }
}

fn encode_clause_sort<S: Sink>(encoder: &mut Encoder<'_, S>, sort: &ClauseSort) {
    match sort {
        ClauseSort::Bool => encoder.u16(0),
        ClauseSort::Int => encoder.u16(1),
        ClauseSort::BitVec(width) => {
            encoder.u16(2);
            encoder.u32(*width);
        }
        ClauseSort::Array(index, element) => {
            encoder.u16(3);
            encode_clause_sort(encoder, index);
            encode_clause_sort(encoder, element);
        }
        ClauseSort::Float { eb, sb } => {
            encoder.u16(4);
            encoder.u32(*eb);
            encoder.u32(*sb);
        }
        ClauseSort::RoundingMode => encoder.u16(5),
        ClauseSort::Datatype { name, constructors } => {
            encoder.u16(6);
            encoder.str(name);
            encoder.len(constructors.len());
            for (constructor, fields) in constructors {
                encoder.str(constructor);
                encoder.len(fields.len());
                for (field, field_sort) in fields {
                    encoder.str(field);
                    encode_clause_sort(encoder, field_sort);
                }
            }
        }
    }
}

fn encode_clause_place<S: Sink>(encoder: &mut Encoder<'_, S>, place: &ClausePlace) {
    match place {
        ClausePlace::Param { index } => {
            encoder.u16(0);
            encoder.u32(*index);
        }
        ClausePlace::ResultSlot { index } => {
            encoder.u16(1);
            encoder.u32(*index);
        }
        ClausePlace::MutParamExit { index } => {
            encoder.u16(2);
            encoder.u32(*index);
        }
        ClausePlace::World => encoder.u16(3),
        ClausePlace::Unwind => encoder.u16(4),
        ClausePlace::Value(value) => {
            encoder.u16(5);
            encoder.u32(value.index());
        }
        // trust-ir v46 spec-variable places. New tags, so no payload that
        // could be spelled before them changes its bytes.
        ClausePlace::SpecVar { index } => {
            encoder.u16(6);
            encoder.u32(*index);
        }
        ClausePlace::SpecVarNext { index } => {
            encoder.u16(7);
            encoder.u32(*index);
        }
        // v59 names entry and exit epochs separately. Append distinct tags:
        // every earlier spelling retains its exact bytes/schema, and neither
        // epoch aliases the legacy unbindable World place.
        ClausePlace::WorldPre => encoder.u16(8),
        ClausePlace::WorldPost => encoder.u16(9),
        // trust-ir v62 (DG-63): the entry-state pointee of reference parameter
        // `index`. Its own appended tag, so it never aliases `Param { index }`
        // (the reference itself) or `MutParamExit { index }` (the exit value),
        // and every earlier spelling keeps its bytes.
        ClausePlace::ParamPointeeEntry { index } => {
            encoder.u16(10);
            encoder.u32(*index);
        }
    }
}

fn encode_lattice_capability<S: Sink>(
    encoder: &mut Encoder<'_, S>,
    capability: &LatticeBoundsCapability,
) {
    let view = capability.retained_identity_view();
    encoder.u64(view.obligation_id);
    encoder.u128(view.lineage_digest);
    encoder.u32(view.discharging_pred.index());
    encoder.str(view.discharging_pred_text);
    encoder.i128(view.required_hi);
    encoder.u64(view.bound);
    encoder.option(view.source_carrier, |encoder, carrier| {
        encoder.str(carrier.function);
        encoder.u32(carrier.base.0);
        encoder.u32(carrier.index.0);
    });
}

fn encode_predicate<S: Sink>(encoder: &mut Encoder<'_, S>, predicate: &Pred) {
    match predicate {
        Pred::Interval { lo, hi } => {
            encoder.u16(0);
            encoder.i128(*lo);
            encoder.i128(*hi);
        }
        Pred::FiniteSet(constants) => {
            encoder.u16(1);
            encode_constants(encoder, constants);
        }
        Pred::InUniverse(universe, space) => {
            encoder.u16(2);
            encoder.u32(universe.index());
            encoder.u16(match space {
                Space::Index => 0,
                Space::Member => 1,
            });
        }
        Pred::NonZero => encoder.u16(3),
        Pred::NonNull => encoder.u16(4),
        Pred::Conj(children) => {
            encoder.u16(5);
            encoder.len(children.len());
            for child in children {
                encoder.u32(child.index());
            }
        }
        Pred::Disj(children) => {
            encoder.u16(6);
            encoder.len(children.len());
            for child in children {
                encoder.u32(child.index());
            }
        }
        Pred::Top => encoder.u16(7),
        Pred::Bottom => encoder.u16(8),
    }
}

fn encode_universe<S: Sink>(encoder: &mut Encoder<'_, S>, universe: &Universe) {
    match universe {
        Universe::IntRange { lo, hi } => {
            encoder.u16(0);
            encoder.i128(*lo);
            encoder.i128(*hi);
        }
        Universe::Members(constants) => {
            encoder.u16(1);
            encode_constants(encoder, constants);
        }
    }
}

fn encode_constants<S: Sink>(encoder: &mut Encoder<'_, S>, constants: &[Constant]) {
    encoder.len(constants.len());
    for constant in constants {
        encode_constant(encoder, constant);
    }
}

fn encode_constant<S: Sink>(encoder: &mut Encoder<'_, S>, constant: &Constant) {
    match constant {
        Constant::Ext(e) => e.unreachable(),
        Constant::Int(value) => {
            encoder.u16(0);
            encoder.i128(*value);
        }
        Constant::U128(value) => {
            encoder.u16(1);
            encoder.u128(*value);
        }
        Constant::Bytes { data, utf8 } => {
            encoder.u16(2);
            encoder.bytes(data);
            encoder.bool(*utf8);
        }
        Constant::Float(value) => {
            encoder.u16(3);
            encoder.u64(value.to_bits());
        }
        Constant::Bool(value) => {
            encoder.u16(4);
            encoder.bool(*value);
        }
        Constant::Aggregate(values) => {
            encoder.u16(5);
            encode_constants(encoder, values);
        }
        Constant::Array(values) => {
            encoder.u16(6);
            encode_constants(encoder, values);
        }
        Constant::Vector(values) => {
            encoder.u16(7);
            encode_constants(encoder, values);
        }
        Constant::Sequence(values) => {
            encoder.u16(8);
            encode_constants(encoder, values);
        }
        Constant::Set(values) => {
            encoder.u16(9);
            encode_constants(encoder, values);
        }
        Constant::Record(fields) => {
            encoder.u16(10);
            encoder.len(fields.len());
            for (name, value) in fields {
                encoder.str(name);
                encode_constant(encoder, value);
            }
        }
        Constant::Closure { func, captures } => {
            encoder.u16(11);
            encoder.u32(func.index());
            encode_constants(encoder, captures);
        }
        Constant::FnDef(func) => {
            encoder.u16(12);
            encoder.u32(func.index());
        }
        Constant::SymbolAddr { symbol, addend } => {
            encoder.u16(13);
            encoder.str(symbol);
            encoder.i64(*addend);
        }
        Constant::PhantomData => encoder.u16(14),
        // trust-ir v49's unwritten aggregate lane: a fresh tag, so no earlier
        // payload changes and the encoding stays injective.
        Constant::Uninit => encoder.u16(15),
        // trust-ir v50's uniform array: a fresh tag, then the length and the
        // ONE element — constant size in `len`, and injective because the
        // tag separates it from the list spellings.
        Constant::Splat { elem, len } => {
            encoder.u16(16);
            encoder.u64(*len);
            encode_constant(encoder, elem);
        }
        // trust-ir v70's content-addressed weight blob, identity only (the
        // adapter refuses weight execution): a fresh tag, then the digest and
        // the complete extents, read without the external bytes, so no earlier
        // payload changes and the encoding stays injective.
        Constant::TensorBlob { digest, dims } => {
            encoder.u16(17);
            encoder.bytes(&digest.0);
            encoder.len(dims.len());
            for dim in dims {
                encoder.u64(*dim);
            }
        }
    }
}

#[cfg(test)]
#[path = "retained_identity_world_epoch_tests.rs"]
mod world_epoch_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instructions::{Block, Value};
    use crate::lattice_guard::{
        RefinementEnv, certify_bounds_guard, certify_bounds_guard_for_test_source_carrier,
    };
    use trust_cg_ir::function::{DebugLocalVariable, DebugVariableStorage, EhTypeTable};
    use trust_cg_ir::provenance::{TrustIrInstId, TrustIrVarId};
    use trust_ir::value::ValueId;

    #[test]
    fn tensor_blob_identity_binds_content_address_and_ordered_shape() {
        #[derive(Default)]
        struct Bytes(Vec<u8>);
        impl Sink for Bytes {
            fn write(&mut self, bytes: &[u8]) {
                self.0.extend_from_slice(bytes);
            }
            fn fail(&mut self, reason: RetainedIdentityError) {
                panic!("{reason:?}");
            }
        }
        let encode = |value| {
            let mut bytes = Bytes::default();
            encode_constant(&mut Encoder(&mut bytes), &value);
            bytes.0
        };
        let digest = trust_ir::blob::BlobDigest::of(&[1, 2, 3, 4]);
        let base = encode(Constant::TensorBlob {
            digest,
            dims: vec![2, 3],
        });
        for other in [
            Constant::TensorBlob {
                digest: trust_ir::blob::BlobDigest::of(&[4, 3, 2, 1]),
                dims: vec![2, 3],
            },
            Constant::TensorBlob {
                digest,
                dims: vec![3, 2],
            },
            Constant::TensorBlob {
                digest,
                dims: vec![2, 3, 1],
            },
            Constant::TensorBlob {
                digest,
                dims: vec![6],
            },
            Constant::Bytes {
                data: vec![1, 2, 3, 4],
                utf8: false,
            },
            Constant::Splat {
                elem: Box::new(Constant::Int(6)),
                len: 2,
            },
        ] {
            assert_ne!(base, encode(other));
        }
        assert_eq!(
            base,
            encode(Constant::TensorBlob {
                digest,
                dims: vec![2, 3]
            })
        );
    }

    fn digest(function: Function, proofs: ProofContext) -> ProofDigest {
        digest_pairs(&[(function, proofs)])
    }

    fn digest_pairs(functions: &[(Function, ProofContext)]) -> ProofDigest {
        retained_lir_proof_context_digest(functions).expect("fixture identity is representable")
    }

    fn instruction(opcode: Opcode) -> Instruction {
        Instruction {
            opcode,
            args: vec![Value(3), Value(4)],
            results: vec![Value(5)],
        }
    }

    fn rich_pair(reverse_maps: bool) -> (Function, ProofContext) {
        let mut function = Function::new(
            "sealed",
            Signature {
                params: vec![Type::I64, Type::Array(Box::new(Type::I8), 4)],
                returns: vec![Type::Enum {
                    tag_width: EnumTagWidth::U16,
                    variants: vec![vec![Type::I32], vec![Type::F64]],
                }],
            },
        );
        function.entry_block = Block(7);
        function.block_order = vec![Block(7), Block(9)];
        let block_entries = [
            (
                Block(7),
                BasicBlock {
                    params: vec![(Value(1), Type::I64)],
                    instructions: vec![
                        instruction(Opcode::Fconst {
                            ty: Type::F64,
                            imm: f64::from_bits(0x7ff8_0000_0000_0042),
                        }),
                        instruction(Opcode::Call {
                            name: "native".to_string(),
                            binding: DirectCallBinding::NativeDependency {
                                function: 19,
                                dependency: trust_cg_ir::NativeDependencyId::new(23),
                            },
                        }),
                    ],
                    source_locs: vec![
                        Some(SourceLoc {
                            file: 2,
                            line: 3,
                            col: 4,
                        }),
                        None,
                    ],
                },
            ),
            (
                Block(9),
                BasicBlock {
                    params: vec![(Value(2), Type::V128)],
                    instructions: vec![instruction(Opcode::Return)],
                    source_locs: vec![],
                },
            ),
        ];
        for (block, body) in if reverse_maps {
            [block_entries[1].clone(), block_entries[0].clone()]
        } else {
            block_entries
        } {
            function.blocks.insert(block, body);
        }

        let origin_entries = [
            (Block(7), vec![Some(TrustIrInstId(31)), None]),
            (Block(9), vec![Some(TrustIrInstId(32))]),
        ];
        for (block, origins) in if reverse_maps {
            [origin_entries[1].clone(), origin_entries[0].clone()]
        } else {
            origin_entries
        } {
            function.trust_ir_origins.insert(block, origins);
        }
        let value_types = [(Value(5), Type::F64), (Value(2), Type::V128)];
        for (value, ty) in if reverse_maps {
            [value_types[1].clone(), value_types[0].clone()]
        } else {
            value_types
        } {
            function.value_types.insert(value, ty);
        }
        function.stack_slots = vec![
            StackSlotInfo::new(8, 8),
            StackSlotInfo::new_dynamic(StackSlotSizeSource::Value(17), 16),
        ];
        for callee in if reverse_maps { ["z", "a"] } else { ["a", "z"] } {
            function.pure_callees.insert(callee.to_string());
        }
        for callee in if reverse_maps {
            ["sin", "cos"]
        } else {
            ["cos", "sin"]
        } {
            function.libm_pure_callees.insert(callee.to_string());
        }
        function.abi_sret_param = Some(AbiSretParam { param_index: 0 });
        for callee in if reverse_maps {
            ["result_b", "result_a"]
        } else {
            ["result_a", "result_b"]
        } {
            function.sret_arg_callees.insert(callee.to_string());
        }
        for callee in if reverse_maps { [31, 17] } else { [17, 31] } {
            function.sret_arg_indirect_callees.insert(Value(callee));
        }
        function.debug_meta = FunctionDebugMeta {
            source_file: Some("source.ty".to_string()),
            display_name: Some("source::item".to_string()),
            decl_line: 44,
            param_names: vec!["x".to_string(), "y".to_string()],
            local_variables: vec![DebugLocalVariable {
                name: "local".to_string(),
                ty: DebugBaseType::U64,
                storage: DebugVariableStorage::ProvenanceVar(TrustIrVarId(77)),
                decl_line: 45,
            }],
            struct_types: vec![DebugStructType {
                name: "Pair".to_string(),
                byte_size: 16,
                members: vec![DebugStructMember {
                    name: "first".to_string(),
                    offset: 0,
                    ty: DebugBaseType::I64,
                }],
            }],
            enum_types: vec![DebugEnumType {
                name: "Choice".to_string(),
                byte_size: 4,
                underlying_type: DebugBaseType::U32,
                enumerators: vec![DebugEnumerator {
                    name: "One".to_string(),
                    value: -1,
                }],
            }],
        };
        function.debug_value_bindings = vec![DebugValueBinding {
            var_id: TrustIrVarId(78),
            value: Value(5),
        }];
        function.stack_protector = StackProtectorMode::StackGuard;
        function.param_pointee_types = vec![ParamPointeeType {
            param_index: 1,
            pointee_ty: Type::Struct(vec![Type::I8, Type::I64]),
        }];
        function.eh_info = EhFunctionInfo {
            personality: Some("personality".to_string()),
            landing_pads: vec![EhLandingPad {
                block: Block(9),
                catch_type_indices: vec![0, 3],
                is_cleanup: true,
            }],
            call_sites: vec![EhCallSite {
                call_block: Block(7),
                landing_pad_block: Block(9),
            }],
        };

        let mut module = trust_ir::Module::new("seal-test");
        let pred = module
            .intern_pred(Pred::interval(0, 7).expect("valid interval"))
            .expect("Module::intern_pred: test fixture")
            .expect("predicate interns");
        let env = RefinementEnv::from_module(&module);
        let cap = certify_bounds_guard_for_test_source_carrier(
            &env,
            pred,
            8,
            "sealed",
            Value(3),
            Value(4),
        )
        .expect("interval certifies bound");

        let mut proofs = ProofContext::default();
        let proof_entries = [
            (
                Value(5),
                vec![
                    Proof::NoOverflow { signed: true },
                    Proof::InBounds {
                        base: ValueId::new(1),
                        index: ValueId::new(2),
                    },
                ],
            ),
            (
                Value(2),
                vec![Proof::ExactInBounds {
                    base: Value(3),
                    index: Value(4),
                    bound: 8,
                }],
            ),
        ];
        for (value, entries) in if reverse_maps {
            [proof_entries[1].clone(), proof_entries[0].clone()]
        } else {
            proof_entries
        } {
            proofs.value_proofs.insert(value, entries);
        }
        proofs.function_proofs = vec![Proof::Pure, Proof::Refinement { pred }];
        let fact_entries = [
            (Value(5), vec![ProofFact::Aligned(16), ProofFact::NoAlias]),
            (
                Value(2),
                vec![ProofFact::DivergenceClass(ProofDivergence::Low)],
            ),
        ];
        for (value, entries) in if reverse_maps {
            [fact_entries[1].clone(), fact_entries[0].clone()]
        } else {
            fact_entries
        } {
            proofs.value_facts.insert(value, entries);
        }
        proofs.function_facts = vec![ProofFact::BoundedLoop(99), ProofFact::Deterministic];
        proofs.noalias_param_indices = vec![0, 2];
        proofs.diagnostics = vec![ProofDropDiagnostic {
            fact: "Custom",
            payload: Some("payload".to_string()),
            code: ProofDropCode::Custom,
            reason: "unsupported custom proof",
        }];
        let synthesized = proofs
            .synthesize_discharged_obligation()
            .expect("synthesized id available");
        proofs.synthesized_obligation_formulas.push((
            synthesized,
            ProofFormula {
                schema: "schema".to_string(),
                payload: "payload".to_string(),
                smtlib: Some("(assert false)".to_string()),
                sort: Some("Bool".to_string()),
                bindings: vec![(
                    "x".to_string(),
                    ClauseBinding {
                        sort: ClauseSort::BitVec(64),
                        place: ClausePlace::Param { index: 0 },
                    },
                )],
            },
        ));
        proofs.refinement_env = env;
        proofs.lattice_bounds_capabilities.push(cap);
        (function, proofs)
    }

    #[test]
    fn identity_is_independent_of_hash_map_and_hash_set_insertion_order() {
        let forward = rich_pair(false);
        let reverse = rich_pair(true);
        assert_eq!(digest_pairs(&[forward]), digest_pairs(&[reverse]));
    }

    #[test]
    fn float_constants_are_authenticated_by_raw_bits() {
        let mut function = Function::new("float", Signature::default());
        function.blocks.insert(
            Block(0),
            BasicBlock {
                instructions: vec![instruction(Opcode::Fconst {
                    ty: Type::F64,
                    imm: f64::from_bits(0x7ff8_0000_0000_0001),
                })],
                ..BasicBlock::default()
            },
        );
        let mut other_nan = function.clone();
        if let Opcode::Fconst { imm, .. } =
            &mut other_nan.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode
        {
            *imm = f64::from_bits(0x7ff8_0000_0000_0002);
        }
        assert_ne!(
            digest(function.clone(), ProofContext::default()),
            digest(other_nan, ProofContext::default())
        );
        let mut negative_zero = function.clone();
        if let Opcode::Fconst { imm, .. } = &mut negative_zero
            .blocks
            .get_mut(&Block(0))
            .unwrap()
            .instructions[0]
            .opcode
        {
            *imm = -0.0;
        }
        let mut positive_zero = function;
        if let Opcode::Fconst { imm, .. } = &mut positive_zero
            .blocks
            .get_mut(&Block(0))
            .unwrap()
            .instructions[0]
            .opcode
        {
            *imm = 0.0;
        }
        assert_ne!(
            digest(negative_zero, ProofContext::default()),
            digest(positive_zero, ProofContext::default())
        );
    }

    #[test]
    fn every_function_top_level_field_changes_identity() {
        let (base, proofs) = rich_pair(false);
        let baseline = digest(base.clone(), proofs.clone());
        let assert_changed = |candidate: Function| {
            assert_ne!(baseline, digest(candidate, proofs.clone()));
        };

        let mut changed = base.clone();
        changed.name.push('x');
        assert_changed(changed);
        let mut changed = base.clone();
        changed.signature.params.push(Type::B1);
        assert_changed(changed);
        let mut changed = base.clone();
        changed.blocks.get_mut(&Block(9)).unwrap().instructions[0].opcode = Opcode::Trap;
        assert_changed(changed);
        let mut changed = base.clone();
        changed.block_order.reverse();
        assert_changed(changed);
        let mut changed = base.clone();
        changed.trust_ir_origins.get_mut(&Block(7)).unwrap()[0] = Some(TrustIrInstId(999));
        assert_changed(changed);
        let mut changed = base.clone();
        changed.entry_block = Block(9);
        assert_changed(changed);
        let mut changed = base.clone();
        changed.stack_slots[0].size += 1;
        assert_changed(changed);
        let mut changed = base.clone();
        changed.value_types.insert(Value(5), Type::I64);
        assert_changed(changed);
        let mut changed = base.clone();
        changed.pure_callees.insert("new".to_string());
        assert_changed(changed);
        let mut changed = base.clone();
        changed.libm_pure_callees.insert("tan".to_string());
        assert_changed(changed);
        let mut changed = base.clone();
        changed.abi_sret_param = None;
        assert_changed(changed);
        let mut changed = base.clone();
        changed.abi_sret_param = Some(AbiSretParam { param_index: 1 });
        assert_changed(changed);
        let mut changed = base.clone();
        changed.sret_arg_callees.insert("result_c".to_string());
        assert_changed(changed);
        let mut changed = base.clone();
        changed.sret_arg_callees.clear();
        assert_changed(changed);
        let mut changed = base.clone();
        changed.sret_arg_indirect_callees.insert(Value(5));
        assert_changed(changed);
        let mut changed = base.clone();
        changed.sret_arg_indirect_callees.clear();
        assert_changed(changed);
        let mut changed = base.clone();
        changed.debug_meta.decl_line += 1;
        assert_changed(changed);
        let mut changed = base.clone();
        changed.debug_meta.display_name = None;
        assert_changed(changed);
        let mut changed = base.clone();
        changed.debug_meta.display_name = Some("source::other".to_string());
        assert_changed(changed);
        let mut changed = base.clone();
        changed.debug_value_bindings[0].value = Value(99);
        assert_changed(changed);
        let mut changed = base.clone();
        changed.stack_protector = StackProtectorMode::None;
        assert_changed(changed);
        // A U10 stack-limit request, and each of its fields, is identity.
        let request = StackLimitRequest {
            param: 1,
            source: StackLimitSource::Pointee { offset: 8 },
            overflow: StackLimitOverflow::Handler {
                symbol: "on_overflow".to_string(),
            },
        };
        let mut requesting = base.clone();
        requesting.stack_limit = Some(request.clone());
        let requesting_digest = digest(requesting.clone(), proofs.clone());
        assert_ne!(baseline, requesting_digest);
        for edit in [
            StackLimitRequest {
                param: 2,
                ..request.clone()
            },
            StackLimitRequest {
                source: StackLimitSource::Pointee { offset: 16 },
                ..request.clone()
            },
            StackLimitRequest {
                source: StackLimitSource::Value,
                ..request.clone()
            },
            StackLimitRequest {
                overflow: StackLimitOverflow::Handler {
                    symbol: "on_overflow2".to_string(),
                },
                ..request.clone()
            },
            StackLimitRequest {
                overflow: StackLimitOverflow::Trap,
                ..request.clone()
            },
        ] {
            let mut changed = base.clone();
            changed.stack_limit = Some(edit);
            let changed_digest = digest(changed, proofs.clone());
            assert_ne!(baseline, changed_digest);
            assert_ne!(requesting_digest, changed_digest);
        }
        let mut changed = base.clone();
        changed.param_pointee_types[0].param_index += 1;
        assert_changed(changed);
        let mut changed = base.clone();
        changed.eh_info.personality.as_mut().unwrap().push('x');
        assert_changed(changed);
        let mut changed = base.clone();
        changed.eh_type_table = EhTypeTable::from_symbols(vec!["_ZTId".to_string()]);
        assert_changed(changed);
        let mut changed = base.clone();
        changed.target_features.push("crc".to_string());
        assert_changed(changed.clone());
        let mut other = base.clone();
        other.target_features.push("lse".to_string());
        assert_ne!(
            digest(changed, proofs.clone()),
            digest(other, proofs.clone()),
            "two stated feature lists are two identities"
        );
        // A splat and the list of the same one entry are different tables.
        let mut splat = base.clone();
        splat.eh_type_table = EhTypeTable::splat("_ZTId".to_string(), 2);
        assert_changed(splat.clone());
        let mut longer = base;
        longer.eh_type_table = EhTypeTable::splat("_ZTId".to_string(), 3);
        assert_ne!(
            digest(splat, ProofContext::default()),
            digest(longer, ProofContext::default())
        );
    }

    #[test]
    fn every_proof_context_top_level_field_changes_identity() {
        let function = Function::new("proofs", Signature::default());
        let baseline = digest(function.clone(), ProofContext::default());
        let assert_changed = |proofs: ProofContext| {
            assert_ne!(baseline, digest(function.clone(), proofs));
        };

        let mut changed = ProofContext::default();
        changed.value_proofs.insert(Value(1), vec![Proof::Pure]);
        assert_changed(changed);
        let mut changed = ProofContext::default();
        changed.function_proofs.push(Proof::Associative);
        assert_changed(changed);
        let mut changed = ProofContext::default();
        changed
            .value_facts
            .insert(Value(1), vec![ProofFact::NoPanic]);
        assert_changed(changed);
        let mut changed = ProofContext::default();
        changed.function_facts.push(ProofFact::Terminates);
        assert_changed(changed);
        let mut changed = ProofContext::default();
        changed.noalias_param_indices.push(3);
        assert_changed(changed);
        let mut changed = ProofContext::default();
        changed.diagnostics.push(ProofDropDiagnostic {
            fact: "fact",
            payload: None,
            code: ProofDropCode::NoConsumer,
            reason: "reason",
        });
        assert_changed(changed);
        let mut changed = ProofContext::default();
        changed.synthesized_discharged.push(1u64 << 32);
        assert_changed(changed);
        let mut changed = ProofContext::default();
        changed
            .synthesized_obligation_formulas
            .push((1u64 << 32, ProofFormula::new("schema", "payload")));
        assert_changed(changed);
        // A formula's typed bindings (v41) are authenticated too: the same
        // schema/payload bound at a different sort or place is a different
        // formula, and a bound one differs from an unbound one.
        let bound = |sort: ClauseSort, place: ClausePlace| {
            let mut formula = ProofFormula::new("schema", "payload");
            formula.bindings = vec![("x".to_string(), ClauseBinding { sort, place })];
            let mut proofs = ProofContext::default();
            proofs
                .synthesized_obligation_formulas
                .push((1u64 << 32, formula));
            digest(function.clone(), proofs)
        };
        let mut unbound = ProofContext::default();
        unbound
            .synthesized_obligation_formulas
            .push((1u64 << 32, ProofFormula::new("schema", "payload")));
        let unbound = digest(function.clone(), unbound);
        let bv64_param0 = bound(ClauseSort::BitVec(64), ClausePlace::Param { index: 0 });
        assert_ne!(unbound, bv64_param0);
        assert_ne!(
            bv64_param0,
            bound(ClauseSort::BitVec(32), ClausePlace::Param { index: 0 })
        );
        assert_ne!(
            bv64_param0,
            bound(ClauseSort::BitVec(64), ClausePlace::Param { index: 1 })
        );
        assert_ne!(
            bv64_param0,
            bound(ClauseSort::BitVec(64), ClausePlace::ResultSlot { index: 0 })
        );

        // Keep the public vector at its default while changing only the private
        // allocator counter: the counter must still be sealed.
        let mut changed = ProofContext::default();
        changed
            .synthesize_discharged_obligation()
            .expect("synthesized id available");
        changed.synthesized_discharged.clear();
        assert_changed(changed);

        let mut module = trust_ir::Module::new("refinement");
        let pred = module
            .intern_pred(Pred::interval(0, 7).expect("valid interval"))
            .expect("Module::intern_pred: test fixture")
            .expect("predicate interns");
        let env = RefinementEnv::from_module(&module);
        let mut changed = ProofContext::default();
        changed.refinement_env = env.clone();
        assert_changed(changed.clone());
        changed
            .lattice_bounds_capabilities
            .push(certify_bounds_guard(&env, pred, 8).expect("interval certifies exact bound"));
        assert_changed(changed);

        // The borrow / binding-frame / Undef receipt: every record list, and
        // each record's fields, are sealed.
        use crate::borrow_frame_undef::{
            BorrowKind, BorrowRecord, FrameRecord, FrameSlotRecord, RetiredBorrowRecord,
            UndefRecord,
        };
        let borrow = BorrowRecord {
            source: trust_ir::ValueId::new(1),
            root: trust_ir::ValueId::new(0),
            kind: BorrowKind::Shared,
            result: Value(1),
            operand: Value(0),
        };
        let mut changed = ProofContext::default();
        changed.borrow_frame_undef.borrows.push(borrow.clone());
        assert_changed(changed.clone());
        let shared = digest(function.clone(), changed);
        let mut unique = ProofContext::default();
        unique.borrow_frame_undef.borrows.push(BorrowRecord {
            kind: BorrowKind::Unique,
            ..borrow.clone()
        });
        assert_ne!(shared, digest(function.clone(), unique));
        let mut rerooted = ProofContext::default();
        rerooted.borrow_frame_undef.borrows.push(BorrowRecord {
            root: trust_ir::ValueId::new(7),
            ..borrow
        });
        assert_ne!(shared, digest(function.clone(), rerooted));
        let mut changed = ProofContext::default();
        changed
            .borrow_frame_undef
            .retired_borrows
            .push(RetiredBorrowRecord {
                source: trust_ir::ValueId::new(1),
                borrow: Value(1),
            });
        assert_changed(changed);
        let frame = FrameRecord {
            source: trust_ir::ValueId::new(0),
            frame_id: 0,
            handle: Value(0),
            stack_slot: 0,
            bytes: 16,
            align: 8,
            slots: vec![FrameSlotRecord {
                offset: 8,
                carrier: Type::I64,
            }],
        };
        let mut changed = ProofContext::default();
        changed.borrow_frame_undef.frames.push(frame.clone());
        assert_changed(changed.clone());
        let framed = digest(function.clone(), changed);
        let mut moved = ProofContext::default();
        moved.borrow_frame_undef.frames.push(FrameRecord {
            slots: vec![FrameSlotRecord {
                offset: 0,
                carrier: Type::I64,
            }],
            ..frame
        });
        assert_ne!(framed, digest(function.clone(), moved));
        let mut changed = ProofContext::default();
        changed.borrow_frame_undef.undefs.push(UndefRecord {
            source: trust_ir::ValueId::new(2),
            result: Value(2),
            carrier: Type::I32,
        });
        assert_changed(changed);
    }

    #[test]
    fn pair_order_and_function_proof_pairing_are_authenticated() {
        let first = rich_pair(false);
        let mut second = rich_pair(false);
        second.0.name = "other".to_string();
        second.1.function_proofs.push(Proof::Commutative);
        let forward = digest_pairs(&[first.clone(), second.clone()]);
        let reverse = digest_pairs(&[second.clone(), first.clone()]);
        assert_ne!(forward, reverse);
        let crossed = digest_pairs(&[(first.0, second.1), (second.0, first.1)]);
        assert_ne!(forward, crossed);
    }

    #[test]
    fn digest_is_repeatable_and_sha256_domain_framed() {
        let pair = rich_pair(false);
        let first = digest_pairs(std::slice::from_ref(&pair));
        let second = digest_pairs(std::slice::from_ref(&pair));
        assert_eq!(first, second);
        assert_eq!(
            first.algorithm,
            trust_ir::proof::ProofDigestAlgorithm::Sha256
        );
        assert!(!first.is_zero());
    }

    /// The empty payload's digest is a WIRE CONTRACT: it pins
    /// `PAYLOAD_SCHEMA_VERSION` and the framing, so a payload-format change
    /// cannot slip through unnoticed. It therefore MOVES, deliberately, every
    /// time the payload schema does — and the version bump it pins is exactly
    /// what stops an old payload being read as a new one.
    ///
    /// v2 (2026-09-11) added the indirect-return (`sret`) ABI facts
    /// `abi_sret_param` / `sret_arg_callees` to `encode_function`. They change
    /// the emitted machine code (which register carries the return-buffer
    /// address), so two functions that disagree about them are not the same
    /// function and must not share a retained identity.
    ///
    /// v3 (2026-09-14) added `ProofFormula::bindings` to `encode_proof_formula`
    /// (trust-ir v41). The sort a binding names is soundness-bearing — a
    /// width-stripped clause can be discharged over a domain the program never
    /// has — so two formulas that differ only in bindings are not the same
    /// formula and must not share a retained identity. Re-minted from the
    /// failing assertion's computed bytes after the version bump.
    ///
    /// v4 (2026-09-21) added `sret_arg_indirect_callees` to `encode_function`:
    /// the `CallIndirect` half of the `sret` facts, which moves the hidden
    /// return-buffer address between X8 and X0 for a `BLR` edge. Re-minted the
    /// same way.
    ///
    /// v5 (2026-09-22) added `eh_type_table` to `encode_function`: the
    /// typeinfo symbols a function's typed catches bind to. Two functions whose
    /// pads index different tables dispatch to different handlers, so they are
    /// not the same function. Re-minted the same way.
    ///
    /// v6 (2026-09-27) spells `eh_type_table` as a tagged enum: the entry list,
    /// or a trust-ir v50 splat's one symbol and length, so a splat table is
    /// authenticated in constant size. Re-minted the same way.
    ///
    /// v7 (2026-09-27) added the borrow / binding-frame / Undef legalization
    /// receipt (`ProofContext::borrow_frame_undef`) to `encode_proof_context`:
    /// what that stage lowered is part of the LIR's identity. Re-minted the
    /// same way.
    ///
    /// v8 (2026-09-29) added `target_features` to `encode_function`: a
    /// function's stated target features select its instructions. Re-minted
    /// the same way.
    ///
    /// v9 (2026-10-01) added `display_name` to `encode_debug_meta`: the DWARF
    /// subprogram name of a `-g` object. Re-minted the same way.
    ///
    /// v10 (2026-10-14) adds the exact direct-call binding of `Invoke`,
    /// alongside its normal and unwind destinations (the invoke-binding lane
    /// minted it as its own v9, concurrently with `display_name`; the merge
    /// carries both). The v8 and both v9 goldens below remain incompatible
    /// historical identities.
    /// v12 retains source allocations. The empty golden is independently
    /// computed from canonical domain framing, u32be(12), u64be(0).
    #[test]
    fn empty_payload_digest_is_a_fixed_wire_contract_golden() {
        assert_eq!(
            digest_pairs(&[]).bytes,
            [
                0xcc, 0x07, 0x34, 0x24, 0x7e, 0x25, 0x26, 0x1c, 0xa8, 0x1a, 0xd1, 0x7c, 0xd8, 0x2b,
                0xd1, 0x8f, 0xa4, 0xc5, 0x9f, 0x61, 0xdb, 0x97, 0x44, 0x1c, 0x42, 0x6f, 0xf7, 0x48,
                0x52, 0xab, 0xa8, 0xd4,
            ]
        );
    }

    #[test]
    fn schema11_empty_identity_cannot_be_reused_as_current_schema12() {
        let mut old = Vec::new();
        old.extend_from_slice(&11u32.to_be_bytes());
        old.extend_from_slice(&0u64.to_be_bytes());
        assert_ne!(digest_pairs(&[]), ProofDigest::sha256_domain(DOMAIN, &old));
    }

    #[test]
    fn schema10_empty_identity_cannot_be_reused_as_current_schema12() {
        let mut old_payload = Vec::new();
        old_payload.extend_from_slice(&10u32.to_be_bytes());
        old_payload.extend_from_slice(&0u64.to_be_bytes());
        let old = ProofDigest::sha256_domain(DOMAIN, &old_payload);
        assert_eq!(
            old.bytes,
            [
                0x80, 0x5c, 0x96, 0x1f, 0x2d, 0xcc, 0xbe, 0x1f, 0x22, 0xb3, 0x49, 0xf2, 0xe1, 0x50,
                0xcb, 0xed, 0xa6, 0x51, 0xd5, 0x55, 0xc8, 0xbc, 0xb7, 0xc2, 0xcd, 0xf9, 0x30, 0x26,
                0x4f, 0xc0, 0x6b, 0xd0,
            ]
        );
        assert_ne!(digest_pairs(&[]), old);
    }

    #[test]
    fn schema8_empty_identity_cannot_be_reused_as_current_schema10() {
        // Exact old framing is retained as a negative, never relabeled v10.
        let mut old_payload = Vec::new();
        old_payload.extend_from_slice(&8u32.to_be_bytes());
        old_payload.extend_from_slice(&0u64.to_be_bytes());
        let old = ProofDigest::sha256_domain(DOMAIN, &old_payload);
        assert_eq!(
            old.bytes,
            [
                0x1c, 0xb6, 0x5c, 0x77, 0x9a, 0x93, 0xce, 0xe5, 0xa4, 0x2b, 0x82, 0xb2, 0x3d, 0x3a,
                0x65, 0x51, 0xe9, 0x4d, 0x5e, 0x97, 0x2e, 0x7f, 0x39, 0x43, 0x7a, 0xcd, 0xea, 0xfa,
                0xa2, 0xd9, 0xc4, 0x1c,
            ]
        );
        assert_ne!(digest_pairs(&[]), old);
    }

    #[test]
    fn schema9_empty_identity_cannot_be_reused_as_current_schema10() {
        // Both v9 spellings (display_name; Invoke binding) were each minted
        // alone; neither framing may be relabeled as the merged v10.
        let mut old_payload = Vec::new();
        old_payload.extend_from_slice(&9u32.to_be_bytes());
        old_payload.extend_from_slice(&0u64.to_be_bytes());
        let old = ProofDigest::sha256_domain(DOMAIN, &old_payload);
        assert_eq!(
            old.bytes,
            [
                0x01, 0xd0, 0xc8, 0xb7, 0xf5, 0xe6, 0x55, 0x3e, 0xdc, 0xf5, 0xa3, 0x82, 0x55, 0x4f,
                0xf4, 0xf6, 0x08, 0xa3, 0x4d, 0xda, 0x4a, 0x39, 0xc0, 0xa3, 0x55, 0xa3, 0x0b, 0x35,
                0x5d, 0xee, 0x2b, 0xe2,
            ]
        );
        assert_ne!(digest_pairs(&[]), old);
    }

    #[test]
    fn invoke_binding_and_both_eh_destinations_change_retained_proof_identity() {
        let (mut base, proofs) = rich_pair(false);
        base.blocks.get_mut(&Block(7)).unwrap().instructions[1].opcode = Opcode::Invoke {
            name: "native".into(),
            binding: DirectCallBinding::ExactModuleFunction { function: 19 },
            normal_dest: Block(9),
            unwind_dest: Block(7),
        };
        let identity = digest(base.clone(), proofs.clone());
        for mutation in 0..4 {
            let mut changed = base.clone();
            let Opcode::Invoke {
                binding,
                normal_dest,
                unwind_dest,
                ..
            } = &mut changed.blocks.get_mut(&Block(7)).unwrap().instructions[1].opcode
            else {
                panic!();
            };
            match mutation {
                0 => *binding = DirectCallBinding::Interposable,
                1 => *binding = DirectCallBinding::ExactModuleFunction { function: 20 },
                2 => *normal_dest = Block(7),
                _ => *unwind_dest = Block(9),
            }
            // EH-rich functions intentionally refuse textual canonical identity.
            // Their complete retained proof digest authenticates this carrier.
            assert_ne!(digest(changed, proofs.clone()), identity);
        }
    }

    #[test]
    fn canonical_count_overflow_is_sticky() {
        let mut count = CountSink(Ok(u64::MAX));
        count.write(&[0]);
        count.write(&[]);
        assert_eq!(count.0, Err(RetainedIdentityError::LengthOverflow));
    }

    #[test]
    fn canonical_hash_never_returns_a_partial_digest() {
        for (expected_len, payload) in [(2, &[1][..]), (0, &[1][..])] {
            let mut hash = HashSink {
                stream: ProofDigest::sha256_domain_stream(DOMAIN, expected_len),
                status: Ok(()),
            };
            hash.write(payload);
            hash.write(&[]);
            assert_eq!(
                hash.finish(),
                Err(RetainedIdentityError::PayloadLengthMismatch)
            );
        }
        let mut hash = HashSink {
            stream: ProofDigest::sha256_domain_stream(DOMAIN, 0),
            status: Ok(()),
        };
        hash.fail(RetainedIdentityError::LengthOverflow);
        hash.write(&[]);
        assert_eq!(hash.finish(), Err(RetainedIdentityError::LengthOverflow));
    }
}
