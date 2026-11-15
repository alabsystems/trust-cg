// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Byte identities for a bounded scalar stack object and opaque ABI calls.
//! There is no floating-point arithmetic: NaNs and signed zero retain their bits.

use std::collections::HashMap;
use trust_cg_lower::instructions::{DirectCallBinding, Opcode as L, Value};
use trust_cg_lower::{Function, Type};

pub(super) use super::super::output_memory::{Byte, bytes};

#[derive(Debug, Clone, PartialEq, Eq)]
enum ValueKind {
    Cell,
    Bits(Vec<Byte>),
}

#[derive(Debug, PartialEq, Eq)]
pub(in crate::source_bound_frame) struct Call {
    pub name: String,
    pub cell_before: Vec<Byte>,
    pub argument: Vec<Byte>,
}

#[derive(Debug, PartialEq, Eq)]
pub(in crate::source_bound_frame) struct Contract {
    pub width: usize,
    pub parameters: usize,
    pub calls: Vec<Call>,
    pub cell_after: Vec<Byte>,
    pub result: Vec<Byte>,
}

pub(in crate::source_bound_frame) fn contract(source: &Function) -> Option<Contract> {
    use trust_cg_ir::function::{StackProtectorMode, StackSlotAllocationKind};
    if source.blocks.len() != 1
        || source.stack_slots.len() != 1
        || !source.eh_info.is_empty()
        || source.stack_protector != StackProtectorMode::None
        || !source.param_pointee_types.is_empty()
        || source.abi_sret_param.is_some()
        || !source.sret_arg_callees.is_empty()
        || !source.pure_callees.is_empty()
        || !source.libm_pure_callees.is_empty()
        || source.signature.returns.len() != 1
        || source.signature.params.is_empty()
        || source.signature.params.len() > 8
    {
        return None;
    }
    let ty = source.signature.returns.first()?;
    let width = match ty {
        Type::F32 => 4,
        Type::F64 => 8,
        _ => return None,
    };
    let slot = &source.stack_slots[0];
    if source.signature.params.iter().any(|param| param != ty)
        || slot.size != width as u32
        || slot.align != width as u32
        || slot.allocation != StackSlotAllocationKind::Fixed
        || (!source.block_order.is_empty() && source.block_order != [source.entry_block])
    {
        return None;
    }
    let block = source.blocks.get(&source.entry_block)?;
    if block.instructions.len() > 256
        || (!block.params.is_empty()
            && (block.params.len() != source.signature.params.len()
                || block
                    .params
                    .iter()
                    .enumerate()
                    .any(|(i, (value, actual))| value.0 as usize != i || actual != ty)))
    {
        return None;
    }
    let mut values: HashMap<Value, ValueKind> = (0..source.signature.params.len())
        .map(|i| {
            (
                Value(i as u32),
                ValueKind::Bits(bytes(width, |b| Byte::Parameter(i, b))),
            )
        })
        .collect();
    if (0..source.signature.params.len()).any(|i| {
        source
            .value_types
            .get(&Value(i as u32))
            .is_some_and(|actual| actual != ty)
    }) {
        return None;
    }
    let mut cell = None;
    let mut calls = Vec::new();
    let mut result = None;
    for inst in &block.instructions {
        if result.is_some() {
            return None;
        }
        let value = |index: usize| values.get(inst.args.get(index)?).cloned();
        let bits = |index| match value(index)? {
            ValueKind::Bits(bits) => Some(bits),
            ValueKind::Cell => None,
        };
        let (args, results, produced) = match &inst.opcode {
            L::StackAddr { slot: 0 } => (0, 1, Some(ValueKind::Cell)),
            L::Copy => (1, 1, Some(value(0)?)),
            L::Fconst { ty: actual, imm } if actual == ty => {
                let raw = if width == 4 {
                    (*imm as f32).to_bits() as u64
                } else {
                    imm.to_bits()
                };
                (
                    0,
                    1,
                    Some(ValueKind::Bits(bytes(width, |b| {
                        Byte::Constant((raw >> (8 * b)) as u8)
                    }))),
                )
            }
            L::Store { ty: actual, align } if actual == ty => {
                if value(1)? != ValueKind::Cell || !valid_align(*align, width) {
                    return None;
                }
                cell = Some(bits(0)?);
                (2, 0, None)
            }
            L::Load { ty: actual, align } if actual == ty => {
                if value(0)? != ValueKind::Cell || !valid_align(*align, width) {
                    return None;
                }
                (1, 1, Some(ValueKind::Bits(cell.clone()?)))
            }
            L::Call {
                name,
                binding: DirectCallBinding::Interposable,
            } => {
                if name.is_empty() || value(0)? != ValueKind::Cell || calls.len() >= 16 {
                    return None;
                }
                let argument = bits(1)?;
                let cell_before = cell.clone()?;
                cell = Some(bytes(width, |b| Byte::Call(calls.len(), b)));
                calls.push(Call {
                    name: name.clone(),
                    cell_before,
                    argument,
                });
                (2, 0, None)
            }
            L::Return => {
                result = Some(bits(0)?);
                (1, 0, None)
            }
            _ => return None,
        };
        if inst.args.len() != args || inst.results.len() != results {
            return None;
        }
        if let Some(produced) = produced {
            let id = *inst.results.first()?;
            let expected = if produced == ValueKind::Cell {
                &Type::I64
            } else {
                ty
            };
            if source
                .value_types
                .get(&id)
                .is_some_and(|actual| actual != expected)
                || values.insert(id, produced).is_some()
            {
                return None;
            }
        }
    }
    if calls.is_empty() {
        return None;
    }
    Some(Contract {
        width,
        parameters: source.signature.params.len(),
        calls,
        cell_after: cell?,
        result: result?,
    })
}

fn valid_align(align: Option<u32>, width: usize) -> bool {
    align.is_none_or(|align| align.is_power_of_two() && align <= width as u32)
}
