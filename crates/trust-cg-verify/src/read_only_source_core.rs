// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact original-Core admission before the shared bounded graph driver.
//! The public read-only route keeps its original type/opcode inventory; only
//! the private scalar-memory profile admits narrow values and writes.
//! Pointer types declare carriers, not readable storage or lifetime authority.
//! The parent retains the original module, including source/debug metadata.

use super::*;
use std::collections::HashMap;
use trust_ir::{BinOp, CallingConv, CastOp, Constant, ICmpOp, Inst, Ty, ValueId};

type Result<T> = std::result::Result<T, ReadOnlySourceError>;

fn refuse(reason: &'static str) -> ReadOnlySourceError {
    ReadOnlySourceError::Source(reason)
}

fn kind(ty: &Ty, profile: Profile) -> Result<Kind> {
    match ty {
        Ty::I64 | Ty::U64 => Ok(Kind::Word),
        Ty::I32 | Ty::U32 if profile.writable() => Ok(Kind::Word32),
        Ty::Bool => Ok(Kind::Boolean),
        Ty::Ptr => Ok(Kind::Pointer),
        _ => Err(refuse("requires exact I64, U64, Bool or Ptr types")),
    }
}

fn word(ty: &Ty) -> Result<()> {
    matches!(ty, Ty::I64 | Ty::U64)
        .then_some(())
        .ok_or_else(|| refuse("requires an exact I64 or U64 word type"))
}

fn numeric(ty: &Ty, profile: Profile) -> Result<()> {
    if profile.writable() && matches!(ty, Ty::I32 | Ty::U32) {
        Ok(())
    } else {
        word(ty)
    }
}

fn binary(op: BinOp, profile: Profile) -> Result<Opcode> {
    Ok(match op {
        BinOp::Add => Opcode::Iadd,
        BinOp::Sub => Opcode::Isub,
        BinOp::Mul if profile.writable() => Opcode::Imul,
        BinOp::And => Opcode::Band,
        BinOp::Or => Opcode::Bor,
        BinOp::Xor => Opcode::Bxor,
        BinOp::Shl => Opcode::Ishl,
        BinOp::LShr => Opcode::Ushr,
        BinOp::AShr => Opcode::Sshr,
        _ => return Err(refuse("unsupported original Core binary operation")),
    })
}

fn stride(ty: &Ty, profile: Profile) -> Result<u64> {
    match ty {
        Ty::U8 => Ok(1),
        Ty::I8 if profile.void_memory() => Ok(1),
        Ty::I32 | Ty::U32 if profile.writable() => Ok(4),
        Ty::I64 | Ty::U64 if profile.writable() => Ok(8),
        _ => Err(refuse("requires an admitted scalar GEP stride")),
    }
}

fn memory_width(ty: &Ty, profile: Profile) -> Result<u32> {
    match ty {
        Ty::Ptr | Ty::I64 | Ty::U64 => Ok(8),
        Ty::I32 | Ty::U32 if profile.writable() => Ok(4),
        _ => Err(refuse("unsupported scalar memory type")),
    }
}

fn comparison(op: ICmpOp) -> IntCC {
    trust_cg_lower::instructions::intcc_of_icmp(op)
}

/// Validate the complete opcode/type/arity inventory without cloning operands
/// or building maps. Dynamic operand vectors are bounded at their constructors.
fn result_type(inst: &Inst, profile: Profile) -> Result<Option<Ty>> {
    let ty = match inst {
        Inst::Const { ty, value } => {
            match (ty, value) {
                (Ty::I64, Constant::Int(value)) if i64::try_from(*value).is_ok() => {}
                (Ty::U64, Constant::Int(value)) if u64::try_from(*value).is_ok() => {}
                (Ty::I32, Constant::Int(value))
                    if profile.writable() && i32::try_from(*value).is_ok() => {}
                (Ty::U32, Constant::Int(value))
                    if profile.writable() && u32::try_from(*value).is_ok() => {}
                (Ty::Bool, Constant::Bool(_)) => {}
                _ => return Err(refuse("constant spelling or range disagrees with its type")),
            }
            ty
        }
        Inst::Copy { ty, .. } => {
            kind(ty, profile)?;
            ty
        }
        Inst::BinOp { op, ty, .. } => {
            numeric(ty, profile)?;
            binary(*op, profile)?;
            ty
        }
        Inst::ICmp { ty, .. } => {
            numeric(ty, profile)?;
            return Ok(Some(Ty::Bool));
        }
        Inst::Select { ty, .. } => {
            if !matches!(
                kind(ty, profile)?,
                Kind::Word | Kind::Word32 | Kind::Boolean
            ) {
                return Err(refuse(
                    "pointer Select is outside the read-only source domain",
                ));
            }
            ty
        }
        Inst::GEP {
            pointee_ty,
            indices,
            inbounds,
            ..
        } => {
            if *inbounds || indices.len() != 1 || !profile.writable() && *pointee_ty != Ty::U8 {
                return Err(refuse("requires one non-inbounds byte GEP index"));
            }
            stride(pointee_ty, profile)?;
            return Ok(Some(Ty::Ptr));
        }
        Inst::Load {
            ty,
            volatile,
            align,
            ..
        } => {
            if memory_width(ty, profile).is_err()
                || *volatile
                || align.is_some_and(|a| a == 0 || a > 8 || !a.is_power_of_two())
            {
                return Err(refuse(if profile.writable() {
                    "requires nonvolatile four/eight-byte loads with valid alignment"
                } else {
                    "requires nonvolatile eight-byte loads with valid alignment"
                }));
            }
            ty
        }
        Inst::Store {
            ty,
            volatile,
            align,
            ..
        } if profile.writable() => {
            if !(profile.void_memory() && *ty == Ty::Ptr) {
                numeric(ty, profile)?;
            }
            if *volatile || align.is_some_and(|a| a == 0 || a > 8 || !a.is_power_of_two()) {
                return Err(refuse(
                    "requires nonvolatile scalar stores with valid alignment",
                ));
            }
            return Ok(None);
        }
        Inst::Cast {
            op: CastOp::PtrToPtr,
            src_ty: Ty::Ptr,
            dst_ty: Ty::Ptr,
            ..
        } => return Ok(Some(Ty::Ptr)),
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I32 | Ty::U32,
            dst_ty: ty @ (Ty::I64 | Ty::U64),
            ..
        } if profile.writable() => return Ok(Some(ty.clone())),
        Inst::Br { args, .. } if args.len() <= 8 => return Ok(None),
        Inst::CondBr {
            then_args,
            else_args,
            ..
        } if then_args.len() <= 8 && else_args.len() <= 8 => return Ok(None),
        Inst::Return { values }
            if values.len() == 1
                || profile.vector_returns() && (1..=8).contains(&values.len())
                || (profile.native_events() || profile.void_memory()) && values.is_empty() =>
        {
            return Ok(None);
        }
        Inst::Call { .. } if profile.vector_returns() => {
            return Err(refuse(
                "scalar-return calls require a checked callee/aggregate ABI owner",
            ));
        }
        _ => {
            return Err(refuse(
                "unsupported original Core instruction or operand arity",
            ));
        }
    };
    Ok(Some(ty.clone()))
}

fn require_type(values: &HashMap<ValueId, Ty>, value: ValueId, expected: &Ty) -> Result<u32> {
    if values.get(&value) != Some(expected) {
        return Err(refuse("original Core operand type or definition disagrees"));
    }
    Ok(value.index())
}

fn edge_args(
    blocks: &HashMap<u32, &trust_ir::Block>,
    values: &HashMap<ValueId, Ty>,
    target: u32,
    args: &[ValueId],
) -> Result<Vec<u32>> {
    let block = blocks
        .get(&target)
        .ok_or_else(|| refuse("original Core branch target does not exist"))?;
    if args.len() != block.params.len() {
        return Err(refuse("original Core branch argument arity disagrees"));
    }
    args.iter()
        .zip(&block.params)
        .map(|(value, (_, ty))| require_type(values, *value, ty))
        .collect()
}

pub(super) fn graph(module: &Module, ordinal: usize) -> Result<Graph> {
    graph_profile(module, ordinal, Profile::ReadOnly)
}

pub(super) fn graph_profile(module: &Module, ordinal: usize, profile: Profile) -> Result<Graph> {
    graph_impl(module, ordinal, profile, None, Metadata::Ordinary)
}

pub(super) fn graph_native(
    module: &Module,
    ordinal: usize,
    bindings: &native_aggregates::Bindings<'_>,
) -> Result<Graph> {
    graph_impl(
        module,
        ordinal,
        Profile::NativeAggregates(scalar_memory::Endpoint::Core),
        Some(bindings),
        Metadata::Ordinary,
    )
}

// The diagnostic constructors above always retain their metadata refusal.
// This private alternative is reachable only from the actual checked family.
#[derive(Clone, Copy)]
enum Metadata {
    Ordinary,
    #[cfg(feature = "source-defined-call")]
    LicensedReadonly,
    #[cfg(feature = "source-defined-call")]
    LicensedByteEntry,
    #[cfg(feature = "source-defined-call")]
    LicensedWordStatusEntry,
}

#[cfg(feature = "source-defined-call")]
pub(super) fn graph_licensed_byte_entry(
    family: &trust_ir_build::source_byte_entry::CheckedByteEntrySource<'_>,
) -> Result<(usize, Graph)> {
    let module = family.module();
    let function = family
        .function_in(module)
        .map_err(|_| refuse("foreign byte-entry source"))?;
    let ordinal = module
        .functions
        .iter()
        .position(|f| f.id == function)
        .ok_or_else(|| refuse("checked byte-entry function is absent"))?;
    let graph = graph_impl(
        module,
        ordinal,
        Profile::VoidMemory(scalar_memory::Endpoint::Core),
        None,
        Metadata::LicensedByteEntry,
    )?;
    Ok((ordinal, graph))
}
#[cfg(feature = "source-defined-call")]
pub(super) fn graph_licensed_word_status_entry(
    family: &trust_ir_build::source_word_status_entry::CheckedWordStatusEntrySource<'_>,
) -> Result<(usize, Graph)> {
    let module = family.module();
    let id = family
        .function_in(module)
        .map_err(|_| refuse("foreign word/status source"))?;
    let ordinal = module
        .functions
        .iter()
        .position(|f| f.id == id)
        .ok_or_else(|| refuse("checked word/status function absent"))?;
    let graph = graph_impl(
        module,
        ordinal,
        Profile::ScalarMemory(scalar_memory::Endpoint::Core),
        None,
        Metadata::LicensedWordStatusEntry,
    )?;
    Ok((ordinal, graph))
}
#[cfg(feature = "source-defined-call")]
pub(super) fn graph_licensed_readonly(
    module: &Module,
    ordinal: usize,
    family: &trust_ir_build::source_readonly_calls::CheckedReadonlySourceFamily<'_>,
) -> Result<Graph> {
    let (_, callee) = family
        .functions_in(module)
        .map_err(|_| refuse("licensed readonly family belongs to another original module"))?;
    if module.functions.get(ordinal).map(|f| f.id) != Some(callee) {
        return Err(refuse(
            "licensed readonly query must select the actual checked load leaf",
        ));
    }
    graph_impl(
        module,
        ordinal,
        Profile::ReadOnly,
        None,
        Metadata::LicensedReadonly,
    )
}

fn graph_impl(
    module: &Module,
    ordinal: usize,
    profile: Profile,
    native: Option<&native_aggregates::Bindings<'_>>,
    metadata: Metadata,
) -> Result<Graph> {
    let source = module
        .functions
        .get(ordinal)
        .ok_or_else(|| refuse("original Core function ordinal does not exist"))?;
    if !(1..=16).contains(&source.blocks.len()) {
        return Err(refuse("requires one through sixteen original Core blocks"));
    }
    let signature = module
        .func_types
        .get(source.ty.index() as usize)
        .ok_or_else(|| refuse("original Core function signature does not exist"))?;
    if !(source.calling_conv == CallingConv::C
        || profile.vector_returns() && source.calling_conv == CallingConv::Fast)
        || signature.is_vararg
        || profile.void_memory() && signature.abi.is_some()
        || !(1..=8).contains(&signature.params.len())
        || if profile.void_memory() {
            signature.params != [Ty::Ptr, Ty::Ptr] || !signature.returns.is_empty()
        } else if profile.vector_returns() {
            !(1..=8).contains(&signature.returns.len())
                && !(profile.native_events() && signature.returns.is_empty())
        } else {
            signature.returns.len() != 1
        }
        || source.attrs.params.len() > signature.params.len()
        || !source.attrs.is_empty()
        || !source.proofs.is_empty()
        || source.summary.is_some()
        || (source.body_gate.is_some() && matches!(metadata, Metadata::Ordinary))
        || signature
            .params
            .iter()
            .any(|ty| !matches!(ty, Ty::Ptr | Ty::I64 | Ty::U64))
    {
        return Err(refuse(
            "requires an ordinary unannotated C read-only source signature",
        ));
    }
    let returned_ty = signature.returns.first().unwrap_or(&Ty::I64);
    if profile.vector_returns() {
        for ty in &signature.returns {
            kind(ty, profile)?;
        }
    } else if !profile.void_memory() {
        word(returned_ty)?;
    }
    let mut count = 0usize;
    let mut parameter_count = 0usize;
    // Bound every collection before maps, graph storage or operand clones.
    for block in &source.blocks {
        count = count
            .checked_add(block.body.len())
            .ok_or_else(|| refuse("original Core instruction count overflow"))?;
        if count > 256 || block.params.len() > 8 {
            return Err(refuse(
                "original Core graph exceeds bounded source resources",
            ));
        }
        parameter_count += block.params.len();
    }
    for block in &source.blocks {
        for (_, ty) in &block.params {
            kind(ty, profile)?;
        }
        for (instruction, node) in block.body.iter().enumerate() {
            if node.results.len() > 1 || !node.proofs.is_empty() || node.proof_context.is_some() {
                return Err(refuse(
                    "original Core node has unsupported result or proof metadata",
                ));
            }
            if node.results.len()
                != usize::from(
                    node_type(node, block.id.index(), instruction, profile, native)?.is_some(),
                )
            {
                return Err(refuse(
                    "original Core result arity disagrees with its operation",
                ));
            }
        }
    }
    let mut blocks = HashMap::with_capacity(source.blocks.len());
    let mut values = HashMap::with_capacity(count + parameter_count);
    for block in &source.blocks {
        if blocks.insert(block.id.index(), block).is_some() {
            return Err(refuse("duplicate original Core block identity"));
        }
        for (id, ty) in &block.params {
            if values.insert(*id, ty.clone()).is_some() {
                return Err(refuse("duplicate original Core SSA definition"));
            }
        }
        for (instruction, node) in block.body.iter().enumerate() {
            if let Some(ty) = node_type(node, block.id.index(), instruction, profile, native)?
                && values.insert(node.results[0], ty).is_some()
            {
                return Err(refuse("duplicate original Core SSA definition"));
            }
        }
    }
    let entry = blocks
        .get(&source.entry.index())
        .ok_or_else(|| refuse("original Core entry block does not exist"))?;
    if entry.params.len() != signature.params.len()
        || entry
            .params
            .iter()
            .zip(&signature.params)
            .any(|((_, actual), expected)| actual != expected)
    {
        return Err(refuse(
            "original Core entry parameters disagree with its signature",
        ));
    }
    let parameters = entry
        .params
        .iter()
        .map(|(id, ty)| Ok((id.index(), kind(ty, profile)?)))
        .collect::<Result<_>>()?;
    let mut output = Vec::with_capacity(source.blocks.len());
    for block in &source.blocks {
        let mut nodes = Vec::with_capacity(block.body.len());
        for (instruction, node) in block.body.iter().enumerate() {
            let get = |value, ty: &Ty| require_type(&values, value, ty);
            let operation = match &node.inst {
                Inst::Call { .. } | Inst::ExtractField { .. } if native.is_some() => native
                    .and_then(|bindings| {
                        bindings.operation(block.id.index(), instruction, node, &values)
                    })
                    .ok_or_else(|| refuse("missing native aggregate operation binding"))??,
                Inst::Const {
                    value: Constant::Int(value),
                    ty,
                } => Operation::Constant(if matches!(ty, Ty::I32 | Ty::U32) {
                    u64::from(*value as u32)
                } else {
                    *value as u64
                }),
                Inst::Const {
                    value: Constant::Bool(value),
                    ..
                } => Operation::Constant(u64::from(*value)),
                Inst::Copy { ty, operand } => Operation::Copy(get(*operand, ty)?),
                Inst::BinOp { op, ty, lhs, rhs } => Operation::Binary {
                    opcode: binary(*op, profile)?,
                    left: get(*lhs, ty)?,
                    right: get(*rhs, ty)?,
                },
                Inst::ICmp { op, ty, lhs, rhs } => Operation::Compare {
                    condition: comparison(*op),
                    left: get(*lhs, ty)?,
                    right: get(*rhs, ty)?,
                },
                Inst::Select {
                    ty,
                    cond,
                    then_val,
                    else_val,
                } => Operation::Select {
                    condition: get(*cond, &Ty::Bool)?,
                    then_value: get(*then_val, ty)?,
                    else_value: get(*else_val, ty)?,
                    invert: false,
                },
                Inst::GEP {
                    base,
                    indices,
                    pointee_ty,
                    ..
                } => {
                    let index = indices[0];
                    let index_ty = values
                        .get(&index)
                        .ok_or_else(|| refuse("undefined byte GEP index"))?;
                    word(index_ty)?;
                    let base = get(*base, &Ty::Ptr)?;
                    if profile.writable() {
                        Operation::ScaledOffset {
                            base,
                            index: index.index(),
                            scale: stride(pointee_ty, profile)?,
                            signed: *index_ty == Ty::I64,
                        }
                    } else {
                        Operation::Offset {
                            base,
                            index: index.index(),
                            scale: 1,
                        }
                    }
                }
                Inst::Load { ty, ptr, align, .. } if profile.writable() => {
                    let byte_width = memory_width(ty, profile)?;
                    Operation::MemoryLoad {
                        address: get(*ptr, &Ty::Ptr)?,
                        alignment: align.unwrap_or(u64::from(byte_width)),
                        byte_width,
                    }
                }
                Inst::Load { ptr, align, .. } => Operation::Load {
                    address: get(*ptr, &Ty::Ptr)?,
                    alignment: align.unwrap_or(8),
                },
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    align,
                    ..
                } if profile.writable() => {
                    let byte_width = memory_width(ty, profile)?;
                    Operation::Store {
                        address: get(*ptr, &Ty::Ptr)?,
                        value: get(*value, ty)?,
                        alignment: align.unwrap_or(u64::from(byte_width)),
                        byte_width,
                    }
                }
                Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty,
                    operand,
                    ..
                } if profile.writable() => Operation::ZeroExtend(get(*operand, src_ty)?),
                Inst::Cast { operand, .. } => Operation::Copy(get(*operand, &Ty::Ptr)?),
                Inst::Br { target, args } => Operation::Jump {
                    target: target.index(),
                    args: edge_args(&blocks, &values, target.index(), args)?,
                },
                Inst::CondBr {
                    cond,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => Operation::Branch {
                    condition: get(*cond, &Ty::Bool)?,
                    then_target: then_target.index(),
                    then_args: edge_args(&blocks, &values, then_target.index(), then_args)?,
                    else_target: else_target.index(),
                    else_args: edge_args(&blocks, &values, else_target.index(), else_args)?,
                },
                Inst::Return { values }
                    if (profile.native_events() || profile.void_memory())
                        && signature.returns.is_empty()
                        && values.is_empty() =>
                {
                    Operation::VoidReturn
                }
                Inst::Return { values } if profile.vector_returns() => {
                    if values.len() != signature.returns.len() {
                        return Err(refuse(
                            "scalar return arity differs from original signature",
                        ));
                    }
                    Operation::VectorReturn(
                        values
                            .iter()
                            .zip(&signature.returns)
                            .map(|(value, ty)| Ok((get(*value, ty)?, kind(ty, profile)?)))
                            .collect::<Result<_>>()?,
                    )
                }
                Inst::Return { values } => Operation::Return(get(values[0], returned_ty)?),
                _ => return Err(refuse("unsupported original Core instruction")),
            };
            let result = if matches!(operation, Operation::NativeAggregateCall { .. }) {
                None
            } else {
                node_type(node, block.id.index(), instruction, profile, native)?
                    .map(|ty| -> Result<_> { Ok((node.results[0].index(), kind(&ty, profile)?)) })
                    .transpose()?
            };
            nodes.push(Node {
                site: ReadOnlySite {
                    block: block.id.index(),
                    instruction,
                },
                result,
                operation,
            });
        }
        output.push(Block {
            id: block.id.index(),
            parameters: block
                .params
                .iter()
                .map(|(id, ty)| Ok((id.index(), kind(ty, profile)?)))
                .collect::<Result<_>>()?,
            nodes,
        });
    }
    Ok(Graph {
        entry: source.entry.index(),
        parameters,
        blocks: output,
    })
}

fn node_type(
    node: &trust_ir::InstrNode,
    block: u32,
    instruction: usize,
    profile: Profile,
    native: Option<&native_aggregates::Bindings<'_>>,
) -> Result<Option<Ty>> {
    if let Some(result) =
        native.and_then(|bindings| bindings.result_type(block, instruction, &node.inst))
    {
        return result.map(Some);
    }
    result_type(&node.inst, profile)
}
