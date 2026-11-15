// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Retain and independently interpret the original typed output writer.
//!
//! A mutable-reference signature declares a caller obligation; neither that
//! declaration nor its LIR pointee sidecar proves live writable ownership.
//! This checker binds the declared extent and complete ordered stores to LIR
//! and final instruction bytes. It grants no production frame authority.

use super::{
    Aarch64OutputFrame, Store, Word, final_bytes, obligation_for_trace_in_frame, source_store_trace,
};
use crate::lowering_proof::ProofObligation;
use std::collections::{HashMap, HashSet};
use trust_cg_lower::{Function, Type, function::ParamPointeeType};
use trust_ir::{
    ArgExt, BinOp, CallingConv, CastOp, Constant, ICmpOp, Inst, Module, ProofAnnotation, Ty,
    ValueId,
};

#[path = "source_bound_output_bounds.rs"]
mod literal_bounds;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TrustIrOutputError {
    #[error("invalid or unsupported typed output TrustIR: {0}")]
    Source(&'static str),
    #[error(
        "original TrustIR and LIR output signature, pointee metadata or ordered stores disagree"
    )]
    LoweringMismatch,
    #[error("output instruction bytes: {0}")]
    Bytes(#[from] final_bytes::OutputByteError),
}

/// Required caller storage, derived from the original signature, not evidence
/// that any particular call supplies it. The whole interval must be live,
/// writable; framed code additionally requires separation from its private frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OutputMemoryRequirements {
    pub parameter_index: usize,
    pub byte_extent: u64,
    pub alignment: u64,
}

/// Immutable source and target endpoints. The conditional memory query still
/// needs independent replay, and caller ownership remains undischargeable by
/// this object alone. This is not a `SourceBoundFrame` or publication receipt.
pub struct CheckedAarch64TrustIrOutputBytes<'a> {
    module: &'a Module,
    source: &'a trust_ir::Function,
    lir: &'a Function,
    code: &'a [u8],
    frame: Aarch64OutputFrame,
    requirements: OutputMemoryRequirements,
    obligation: ProofObligation,
}

impl<'a> CheckedAarch64TrustIrOutputBytes<'a> {
    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        self.source
    }
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    pub fn code(&self) -> &'a [u8] {
        self.code
    }
    pub fn frame(&self) -> Aarch64OutputFrame {
        self.frame
    }
    pub fn requirements(&self) -> OutputMemoryRequirements {
        self.requirements
    }
    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
}

type Result<T> = std::result::Result<T, TrustIrOutputError>;
fn source_error(message: &'static str) -> TrustIrOutputError {
    TrustIrOutputError::Source(message)
}
fn integer(ty: &Ty) -> bool {
    matches!(ty, Ty::I64 | Ty::U64)
}

fn pointee(module: &Module, ty: &Ty) -> Result<(Type, u64)> {
    let (carrier, count) = match ty {
        Ty::Tuple(fields) if (1..=64).contains(&fields.len()) && fields.iter().all(integer) => (
            Type::Struct(vec![Type::I64; fields.len()]),
            fields.len() as u64,
        ),
        Ty::Array(element, count)
            if module
                .types
                .get(element.index() as usize)
                .is_some_and(integer)
                && *count <= 64 =>
        {
            (Type::Array(Box::new(Type::I64), *count as u32), *count)
        }
        _ => {
            return Err(source_error(
                "requires a flat tuple or array of 64-bit integer lanes",
            ));
        }
    };
    if !(1..=64).contains(&count) {
        return Err(source_error("output extent requires one through 64 lanes"));
    }
    Ok((carrier, count * 8))
}

struct Contract {
    requirements: OutputMemoryRequirements,
    pointee: Type,
    stores: Vec<Store>,
    arity: usize,
}

fn contract(module: &Module, source: &trust_ir::Function) -> Result<Contract> {
    let signature = module
        .func_types
        .get(source.ty.index() as usize)
        .ok_or_else(|| source_error("signature index outside module"))?;
    if source.calling_conv != CallingConv::C
        || signature.is_vararg
        || !(1..=8).contains(&signature.params.len())
        || !(signature.returns.is_empty() || signature.returns == [Ty::Unit])
        || source.attrs.params.len() > signature.params.len()
        // This byte relation uses one X register per source parameter. An
        // explicit pass or extension needs its own ABI refinement; it cannot
        // inherit the ordinary carrier relation from unchanged LIR metadata.
        || source.attrs.params.iter().any(|a| {
            a.byval || a.sret || a.readonly || a.ext != ArgExt::None || a.pass.is_some()
        })
        || !source.attrs.ret.is_empty()
        || source.attrs.readonly
        || source.attrs.readnone
        || source.attrs.naked
        || !source.attrs.target_features.is_empty()
        || source.body_gate.is_some()
    {
        return Err(source_error(
            "requires ordinary C ABI and a void writable body",
        ));
    }
    if source.blocks.is_empty() || source.blocks.len() > 16 {
        return Err(source_error("requires a bounded nonempty source body"));
    }
    let mut output = None;
    for (index, ty) in signature.params.iter().enumerate() {
        if let Ty::RefMut(inner) = ty {
            let (carrier, byte_extent) = pointee(module, inner)?;
            if output
                .replace((
                    OutputMemoryRequirements {
                        parameter_index: index,
                        byte_extent,
                        alignment: 8,
                    },
                    carrier,
                ))
                .is_some()
            {
                return Err(source_error("multiple output references"));
            }
        } else if !integer(ty) {
            return Err(source_error(
                "parameters require integers and one mutable reference",
            ));
        }
    }
    let (requirements, pointee) =
        output.ok_or_else(|| source_error("missing mutable output reference"))?;
    let blocks: HashMap<_, _> = source.blocks.iter().map(|b| (b.id, b)).collect();
    if blocks.len() != source.blocks.len() {
        return Err(source_error("duplicate block identity"));
    }
    let entry = blocks
        .get(&source.entry)
        .ok_or_else(|| source_error("missing entry"))?;
    if entry.params.len() != signature.params.len() {
        return Err(source_error("entry arity differs from signature"));
    }
    let mut values = HashMap::new();
    for (index, ((id, ty), declared)) in entry.params.iter().zip(&signature.params).enumerate() {
        if ty != declared
            || values
                .insert(*id, (ty.clone(), Word::parameter(index)))
                .is_some()
        {
            return Err(source_error("entry types or identities disagree"));
        }
    }
    let mut visited = HashSet::new();
    let mut current = source.entry;
    let mut count = 0;
    let mut stores = Vec::new();
    loop {
        let block = blocks
            .get(&current)
            .ok_or_else(|| source_error("unknown branch target"))?;
        if !visited.insert(current) || (current != source.entry && !block.params.is_empty()) {
            return Err(source_error(
                "loops and block arguments are outside the output domain",
            ));
        }
        count += block.body.len();
        if count > 256 || block.body.is_empty() {
            return Err(source_error("empty block or instruction limit"));
        }
        let mut next = None;
        let mut returned = false;
        for (index, node) in block.body.iter().enumerate() {
            if next.is_some() || returned || node.proof_context.is_some() {
                return Err(source_error(
                    "instruction follows terminator or has call-only context",
                ));
            }
            let read = |id: ValueId| {
                values
                    .get(&id)
                    .cloned()
                    .ok_or_else(|| source_error("undefined source value"))
            };
            let result = match &node.inst {
                Inst::Const {
                    ty,
                    value: Constant::Int(value),
                } if integer(ty) => {
                    let valid = if *ty == Ty::I64 {
                        i64::try_from(*value).is_ok()
                    } else {
                        u64::try_from(*value).is_ok()
                    };
                    if !valid {
                        return Err(source_error("integer literal outside declared width"));
                    }
                    Some((ty.clone(), Word::constant(*value as u64)))
                }
                Inst::Copy { ty, operand } => {
                    let (actual, value) = read(*operand)?;
                    // The bridge erases a thin reference to the address carrier
                    // with Copy Ptr. Keep the original signature and value;
                    // this erasure cannot create a new output pointer.
                    if *ty != actual && !(*ty == Ty::Ptr && matches!(actual, Ty::RefMut(_))) {
                        return Err(source_error("copy type mismatch"));
                    }
                    Some((ty.clone(), value))
                }
                Inst::ICmp { op, ty, lhs, rhs } if integer(ty) => {
                    let (left_ty, left) = read(*lhs)?;
                    let (right_ty, right) = read(*rhs)?;
                    if left_ty != *ty || right_ty != *ty {
                        return Err(source_error("comparison operand type mismatch"));
                    }
                    let value = literal_bounds::compare(
                        *op,
                        left.integer()
                            .ok_or_else(|| source_error("nonliteral comparison"))?,
                        right
                            .integer()
                            .ok_or_else(|| source_error("nonliteral comparison"))?,
                    );
                    // The frontend replaced a trapping bounds assertion with
                    // this annotated probe. Evaluate its actual operands; a
                    // ProofRef supplies no authority to erase a false guard.
                    if node.proofs.contains(&ProofAnnotation::InBounds)
                        && (*op != ICmpOp::Ult || !value)
                    {
                        return Err(source_error(
                            "bounds probe is not a true unsigned comparison",
                        ));
                    }
                    Some((Ty::Bool, Word::constant(u64::from(value))))
                }
                Inst::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand,
                } => {
                    let (actual, value) = read(*operand)?;
                    if actual != *src_ty {
                        return Err(source_error("cast source type mismatch"));
                    }
                    let allowed = match op {
                        CastOp::Bitcast => integer(src_ty) && integer(dst_ty),
                        CastOp::PtrToPtr => {
                            matches!(src_ty, Ty::RefMut(_))
                                && *dst_ty == Ty::Ptr
                                && src_ty.default_pointer_layout_shape()
                                    == dst_ty.default_pointer_layout_shape()
                        }
                        CastOp::PtrToInt => {
                            matches!(src_ty, Ty::Ptr | Ty::RefMut(_)) && integer(dst_ty)
                        }
                        CastOp::IntToPtr => {
                            integer(src_ty)
                                && *dst_ty == Ty::Ptr
                                && value.address().is_some_and(|(parameter, offset)| {
                                    parameter == requirements.parameter_index
                                        && offset <= requirements.byte_extent
                                })
                        }
                        _ => false,
                    };
                    if !allowed {
                        return Err(source_error("unsupported cast or fabricated pointer"));
                    }
                    Some((dst_ty.clone(), value))
                }
                Inst::BinOp {
                    op: BinOp::Add | BinOp::Mul,
                    ty,
                    lhs,
                    rhs,
                } if integer(ty) => {
                    let (left_ty, left) = read(*lhs)?;
                    let (right_ty, right) = read(*rhs)?;
                    if left_ty != *ty || right_ty != *ty {
                        return Err(source_error("arithmetic operand type mismatch"));
                    }
                    let value =
                        if matches!(node.inst, Inst::BinOp { op: BinOp::Mul, .. }) {
                            Word::constant(
                                left.integer()
                                    .and_then(|a| right.integer().map(|b| a.wrapping_mul(b)))
                                    .ok_or_else(|| {
                                        source_error("only literal multiplication is supported")
                                    })?,
                            )
                        } else if let Some(offset) = right.integer() {
                            left.add(offset)
                                .ok_or_else(|| source_error("bounded address addition"))?
                        } else {
                            right
                                .add(left.integer().ok_or_else(|| {
                                    source_error("addition needs a literal offset")
                                })?)
                                .ok_or_else(|| source_error("bounded address addition"))?
                        };
                    Some((ty.clone(), value))
                }
                Inst::GEP {
                    pointee_ty,
                    base,
                    indices,
                    ..
                } if indices.len() == 1 => {
                    let (ty, address) = read(*base)?;
                    if !matches!(ty, Ty::Ptr | Ty::RefMut(_)) {
                        return Err(source_error("GEP base is not an output-derived pointer"));
                    }
                    let stride = match pointee_ty {
                        Ty::I8 | Ty::U8 => 1,
                        Ty::I64 | Ty::U64 => 8,
                        _ => return Err(source_error("unsupported GEP scale")),
                    };
                    let (index_ty, index) = read(indices[0])?;
                    if !integer(&index_ty) {
                        return Err(source_error("noninteger index"));
                    }
                    let offset = index
                        .integer()
                        .and_then(|n| n.checked_mul(stride))
                        .ok_or_else(|| {
                            source_error("index must be a bounded nonnegative literal")
                        })?;
                    let value = address
                        .add(offset)
                        .ok_or_else(|| source_error("address overflow"))?;
                    let (parameter, offset) = value
                        .address()
                        .ok_or_else(|| source_error("lost output address"))?;
                    if parameter != requirements.parameter_index
                        || offset > requirements.byte_extent
                    {
                        return Err(source_error("GEP escapes declared output extent"));
                    }
                    Some((Ty::Ptr, value))
                }
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    align,
                } if integer(ty) => {
                    let (pointer_ty, address) = read(*ptr)?;
                    let (value_ty, value) = read(*value)?;
                    if !matches!(pointer_ty, Ty::Ptr | Ty::RefMut(_))
                        || value_ty != *ty
                        || align.is_some_and(|a| a == 0 || a > 8 || !a.is_power_of_two())
                    {
                        return Err(source_error(
                            "store pointer, value type or alignment mismatch",
                        ));
                    }
                    let store = super::store(address, value)
                        .ok_or_else(|| source_error("unsupported store"))?;
                    if store.parameter != requirements.parameter_index
                        || store
                            .offset
                            .checked_add(8)
                            .is_none_or(|end| end > requirements.byte_extent)
                    {
                        return Err(source_error("store escapes declared output extent"));
                    }
                    stores.push(store);
                    if stores.len() > 64 {
                        return Err(source_error("store limit"));
                    }
                    None
                }
                Inst::Br { target, args } if args.is_empty() => {
                    next = Some(*target);
                    None
                }
                Inst::Return { values } if values.is_empty() => {
                    returned = true;
                    None
                }
                _ => return Err(source_error("unsupported instruction in output writer")),
            };
            if node.results.len() != usize::from(result.is_some()) {
                return Err(source_error("instruction result arity"));
            }
            if let Some(result) = result {
                if values.insert(node.results[0], result).is_some() {
                    return Err(source_error("redefined source value"));
                }
            } else if (next.is_some() || returned) && index + 1 != block.body.len() {
                return Err(source_error("nonfinal terminator"));
            }
        }
        if let Some(target) = next {
            current = target;
        } else if returned {
            break;
        } else {
            return Err(source_error("missing terminator"));
        }
    }
    if visited.len() != source.blocks.len() || stores.is_empty() {
        return Err(source_error("unvisited blocks or empty output trace"));
    }
    Ok(Contract {
        requirements,
        pointee,
        stores,
        arity: signature.params.len(),
    })
}

/// Compare the original module-owned writer, actual LIR and exact A64 words.
/// Pointee metadata is retained and must match the original signature exactly.
/// Caller storage validity, lifetime, permission and frame separation remain
/// explicit requirements; no type, hint or source annotation discharges them.
pub fn check_aarch64_trust_ir_output_bytes<'a>(
    module: &'a Module,
    function_ordinal: usize,
    lir: &'a Function,
    code: &'a [u8],
) -> Result<CheckedAarch64TrustIrOutputBytes<'a>> {
    let source = module
        .functions
        .get(function_ordinal)
        .ok_or_else(|| source_error("function ordinal outside module"))?;
    if source.name != lir.name {
        return Err(TrustIrOutputError::LoweringMismatch);
    }
    let contract = contract(module, source)?;
    let expected_metadata = [ParamPointeeType {
        param_index: contract.requirements.parameter_index as u32,
        pointee_ty: contract.pointee,
    }];
    if lir.signature.params != vec![Type::I64; contract.arity]
        || !lir.signature.returns.is_empty()
        || lir.param_pointee_types != expected_metadata
    {
        return Err(TrustIrOutputError::LoweringMismatch);
    }
    let view =
        super::super::linear::source_view(lir).ok_or(TrustIrOutputError::LoweringMismatch)?;
    let view = literal_bounds::view(&view).ok_or(TrustIrOutputError::LoweringMismatch)?;
    let stores = source_store_trace(&view).ok_or(TrustIrOutputError::LoweringMismatch)?;
    if stores != contract.stores {
        return Err(TrustIrOutputError::LoweringMismatch);
    }
    let (machine, frame) = final_bytes::decoded_body(&view, code)?;
    let obligation = obligation_for_trace_in_frame(&view, &machine, &stores, frame)
        .ok_or(final_bytes::OutputByteError::StoreMismatch)?;
    Ok(CheckedAarch64TrustIrOutputBytes {
        module,
        source,
        lir,
        code,
        frame,
        requirements: contract.requirements,
        obligation,
    })
}

#[cfg(test)]
#[path = "source_bound_output_trust_ir_tests.rs"]
mod tests;
