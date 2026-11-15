// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independently bind an original scalar C caller to its retained LIR.
//!
//! A typed mutable pointer declares the cell's extent; it does not restrict an
//! opaque callee to that cell. Calls may also affect public memory. This source
//! check does not establish ABI compliance, private-frame noninterference,
//! machine or encoded-byte correctness, or a discharged frame obligation.

use std::collections::{HashMap, HashSet};
use trust_cg_lower::Function;
use trust_ir::{CallingConv, CastOp, Constant, Endianness, Inst, Linkage, Module, Ty, ValueId};

#[path = "source_bound_cell_values.rs"]
pub(super) mod values;
use values::{Byte, Call, Contract, bytes};

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ScalarCellSourceError {
    #[error("invalid or unsupported scalar-cell TrustIR: {0}")]
    Source(&'static str),
    #[error("unsupported scalar-cell LIR")]
    Lowering,
    #[error("original TrustIR and LIR scalar-cell observations disagree")]
    LoweringMismatch,
}

/// Immutable original and lowered endpoints with matching scalar-cell events.
/// Construction supplies source binding only, never instruction proof credit.
pub struct CheckedAarch64ScalarCellSource<'a> {
    module: &'a Module,
    source: &'a trust_ir::Function,
    lir: &'a Function,
    contract: Contract,
}

impl<'a> CheckedAarch64ScalarCellSource<'a> {
    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        self.source
    }
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    pub fn cell_width(&self) -> usize {
        self.contract.width
    }
    pub fn call_count(&self) -> usize {
        self.contract.calls.len()
    }
}

type Result<T> = std::result::Result<T, ScalarCellSourceError>;
fn invalid(reason: &'static str) -> ScalarCellSourceError {
    ScalarCellSourceError::Source(reason)
}

#[derive(Clone, PartialEq, Eq)]
enum Value {
    Cell(Ty),
    Bits(Vec<Byte>),
}

fn ordinary(function: &trust_ir::Function, arity: usize) -> bool {
    function.calling_conv == CallingConv::C
        && function.linkage == Linkage::External
        && function.attrs.is_empty()
        && function.attrs.params.len() <= arity
        && function.proofs.is_empty()
        && function.summary.is_none()
        && function.body_gate.is_none()
        && function.source_provenance.is_none()
}

fn valid_align(align: Option<u64>, width: usize) -> bool {
    align.is_none_or(|a| a.is_power_of_two() && a <= width as u64)
}

fn contract(module: &Module, source: &trust_ir::Function) -> Result<Contract> {
    let signature = module
        .func_types
        .get(source.ty.index() as usize)
        .ok_or_else(|| invalid("missing caller signature"))?;
    let [ty] = signature.returns.as_slice() else {
        return Err(invalid("requires one scalar return"));
    };
    let width = match ty {
        Ty::F32 => 4,
        Ty::F64 => 8,
        _ => return Err(invalid("requires F32 or F64")),
    };
    if !ordinary(source, signature.params.len())
        || signature.is_vararg
        || !(1..=8).contains(&signature.params.len())
        || signature.params.iter().any(|param| param != ty)
        || !(1..=16).contains(&source.blocks.len())
    {
        return Err(invalid("requires a bounded ordinary C scalar caller"));
    }
    let blocks: HashMap<_, _> = source
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect();
    if blocks.len() != source.blocks.len() {
        return Err(invalid("duplicate block identity"));
    }
    let entry = blocks
        .get(&source.entry)
        .ok_or_else(|| invalid("missing entry"))?;
    if entry.params.len() != signature.params.len() {
        return Err(invalid("entry arity mismatch"));
    }
    let mut values = HashMap::new();
    for (index, (id, actual)) in entry.params.iter().enumerate() {
        if actual != ty
            || values
                .insert(
                    *id,
                    Value::Bits(bytes(width, |b| Byte::Parameter(index, b))),
                )
                .is_some()
        {
            return Err(invalid("entry type or identity mismatch"));
        }
    }
    let mut visited = HashSet::new();
    let mut current = source.entry;
    let mut allocated = false;
    let mut cell = None;
    let mut calls = Vec::new();
    let mut count = 0;
    loop {
        let block = blocks
            .get(&current)
            .ok_or_else(|| invalid("unknown branch target"))?;
        if !visited.insert(current) || (current != source.entry && !block.params.is_empty()) {
            return Err(invalid("loops or block arguments"));
        }
        count += block.body.len();
        if block.body.is_empty() || count > 256 {
            return Err(invalid("empty block or instruction limit"));
        }
        let mut next = None;
        for (index, node) in block.body.iter().enumerate() {
            if next.is_some() || !node.proofs.is_empty() || node.proof_context.is_some() {
                return Err(invalid(
                    "instruction after branch or unsupported proof metadata",
                ));
            }
            let read = |id: ValueId| {
                values
                    .get(&id)
                    .cloned()
                    .ok_or_else(|| invalid("undefined value"))
            };
            let bits = |id| match read(id)? {
                Value::Bits(value) => Ok(value),
                Value::Cell(_) => Err(invalid("cell address used as float")),
            };
            let produced = match &node.inst {
                Inst::Alloca {
                    ty: actual,
                    count: None,
                    align,
                } if actual == ty && align.is_none_or(|a| a == width as u64) && !allocated => {
                    allocated = true;
                    Some(Value::Cell(Ty::Ptr))
                }
                Inst::Copy {
                    ty: actual,
                    operand,
                } => {
                    let value = read(*operand)?;
                    let valid = match &value {
                        Value::Cell(source_ty) => actual == source_ty,
                        Value::Bits(_) => actual == ty,
                    };
                    if !valid {
                        return Err(invalid("copy changes scalar or cell type"));
                    }
                    Some(value)
                }
                Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty,
                    dst_ty,
                    operand,
                } if *dst_ty == Ty::Ptr || *dst_ty == Ty::PtrMut(Box::new(ty.clone())) => {
                    if read(*operand)? != Value::Cell(src_ty.clone()) {
                        return Err(invalid("pointer cast source type mismatch"));
                    }
                    Some(Value::Cell(dst_ty.clone()))
                }
                Inst::Const {
                    ty: actual,
                    value: Constant::Float(value),
                } if actual == ty => {
                    // Restrict literals to finite, exactly representable values.
                    // Parameters and opaque-call results remain arbitrary bytes.
                    if !value.is_finite()
                        || (width == 4 && ((*value as f32) as f64).to_bits() != value.to_bits())
                    {
                        return Err(invalid("unsupported floating literal"));
                    }
                    let raw = if width == 4 {
                        (*value as f32).to_bits() as u64
                    } else {
                        value.to_bits()
                    };
                    Some(Value::Bits(bytes(width, |b| {
                        Byte::Constant((raw >> (8 * b)) as u8)
                    })))
                }
                Inst::Store {
                    ty: actual,
                    ptr,
                    value,
                    volatile: false,
                    align,
                } if actual == ty && valid_align(*align, width) => {
                    if !matches!(read(*ptr)?, Value::Cell(_)) {
                        return Err(invalid("store outside local cell"));
                    }
                    cell = Some(bits(*value)?);
                    None
                }
                Inst::Load {
                    ty: actual,
                    ptr,
                    volatile: false,
                    align,
                } if actual == ty && valid_align(*align, width) => {
                    if !matches!(read(*ptr)?, Value::Cell(_)) {
                        return Err(invalid("load outside local cell"));
                    }
                    Some(Value::Bits(
                        cell.clone().ok_or_else(|| invalid("uninitialized cell"))?,
                    ))
                }
                Inst::Call { callee, args } if args.len() == 2 && calls.len() < 16 => {
                    let declaration = module
                        .functions
                        .iter()
                        .find(|f| f.id == *callee)
                        .ok_or_else(|| invalid("unknown callee"))?;
                    let callee_ty = module
                        .func_types
                        .get(declaration.ty.index() as usize)
                        .ok_or_else(|| invalid("missing callee signature"))?;
                    if !ordinary(declaration, 2)
                        || !declaration.blocks.is_empty()
                        || callee_ty.is_vararg
                        || !callee_ty.returns.is_empty()
                        || callee_ty.params != [Ty::PtrMut(Box::new(ty.clone())), ty.clone()]
                        || read(args[0])? != Value::Cell(Ty::PtrMut(Box::new(ty.clone())))
                    {
                        return Err(invalid(
                            "requires declared C (mutable scalar pointer, scalar) -> void",
                        ));
                    }
                    calls.push(Call {
                        name: declaration.name.clone(),
                        cell_before: cell
                            .clone()
                            .ok_or_else(|| invalid("uninitialized call cell"))?,
                        argument: bits(args[1])?,
                    });
                    cell = Some(bytes(width, |b| Byte::Call(calls.len() - 1, b)));
                    None
                }
                Inst::Br { target, args } if args.is_empty() => {
                    next = Some(*target);
                    None
                }
                Inst::Return { values: returned } if returned.len() == 1 => {
                    if index + 1 != block.body.len()
                        || !node.results.is_empty()
                        || visited.len() != blocks.len()
                        || calls.is_empty()
                    {
                        return Err(invalid("incomplete body or missing calls"));
                    }
                    return Ok(Contract {
                        width,
                        parameters: signature.params.len(),
                        calls,
                        cell_after: cell.ok_or_else(|| invalid("missing cell"))?,
                        result: bits(returned[0])?,
                    });
                }
                _ => return Err(invalid("instruction outside scalar-cell domain")),
            };
            match (produced, node.results.as_slice()) {
                (Some(value), [id]) if !values.contains_key(id) => {
                    values.insert(*id, value);
                }
                (None, []) => {}
                _ => return Err(invalid("result arity or duplicate identity")),
            }
        }
        current = next.ok_or_else(|| invalid("missing terminator"))?;
    }
}

/// Match original declared ABI and ordered cell/call/return bytes to LIR without
/// invoking the lowering adapter. This API supplies no callee footprint theorem:
/// arbitrary public-memory effects and private-frame separation remain to prove.
pub fn check_aarch64_scalar_cell_source<'a>(
    module: &'a Module,
    lir: &'a Function,
) -> Result<CheckedAarch64ScalarCellSource<'a>> {
    let target = module
        .target_info
        .as_ref()
        .ok_or_else(|| invalid("missing target"))?;
    if target.triple != "aarch64-unknown-linux-gnu"
        || target.pointer_size != 8
        || target.endianness != Endianness::Little
        || target.abi.is_some()
        || !module.globals.is_empty()
        || !module.global_asm.is_empty()
        || !module.imports.is_empty()
    {
        return Err(invalid("unsupported target or module symbol context"));
    }
    let mut ids = HashSet::new();
    let mut names = HashSet::new();
    for function in &module.functions {
        if !ids.insert(function.id)
            || !names.insert(&function.name)
            || function.name.is_empty()
            || function.name.as_bytes().contains(&0)
        {
            return Err(invalid("ambiguous function identity"));
        }
    }
    let source = module
        .functions
        .iter()
        .find(|f| f.name == lir.name)
        .ok_or_else(|| invalid("missing caller"))?;
    let expected = contract(module, source)?;
    let view = super::linear::source_view(lir).ok_or(ScalarCellSourceError::Lowering)?;
    let actual = values::contract(&view).ok_or(ScalarCellSourceError::Lowering)?;
    if expected != actual {
        return Err(ScalarCellSourceError::LoweringMismatch);
    }
    Ok(CheckedAarch64ScalarCellSource {
        module,
        source,
        lir,
        contract: expected,
    })
}

#[cfg(test)]
#[path = "source_bound_cell_source_tests.rs"]
mod tests;
