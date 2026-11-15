// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independent, bounded output-byte transport. Queries are diagnostic only:
//! source validity supplies writable output storage, and a caller-memory/ABI
//! contract must establish that storage is disjoint from the private frame.
//! Neither obligation construction nor a solver result supplies that contract.
//! Calls, loads, volatile accesses, spills and control-dependent stores refuse.

use std::collections::HashMap;

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
use crate::smt::SmtExpr as E;
use trust_cg_ir::function::{StackProtectorMode, Type as MachineType};
use trust_cg_ir::regs::X30;
use trust_cg_ir::{AArch64Opcode as M, MachFunction, MachInst, MachOperand as O};
use trust_cg_lower::instructions::{Opcode as L, Value};
use trust_cg_lower::{Function, Type};

#[path = "source_bound_output_bytes.rs"]
pub(super) mod final_bytes;

#[path = "source_bound_output_trust_ir.rs"]
pub(super) mod trust_ir_source;

/// Stack effects independently recognized from the complete A64 stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Aarch64OutputFrame {
    /// No SP, FP or LR writes, and no private stack bytes.
    Frameless,
    /// Exact sixteen-byte FP/LR save, FP establishment and restore envelope.
    FpLr16,
}

// Shared with the scalar-cell source interpreter and its diagnostic machine
// checker. Call identities supply no production call authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Byte {
    Parameter(usize, usize),
    Constant(u8),
    Call(usize, usize),
    Register(u8, usize),
    Clobber(usize, u8, usize),
}

pub(super) fn bytes(width: usize, value: impl FnMut(usize) -> Byte) -> Vec<Byte> {
    (0..width).map(value).collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Word {
    Bits(Vec<Byte>),
    Address { parameter: usize, offset: u64 },
}

impl Word {
    fn parameter(index: usize) -> Self {
        Self::Bits(bytes(8, |b| Byte::Parameter(index, b)))
    }

    fn constant(value: u64) -> Self {
        Self::Bits(bytes(8, |b| Byte::Constant((value >> (b * 8)) as u8)))
    }

    fn integer(&self) -> Option<u64> {
        let Self::Bits(bits) = self else { return None };
        let mut value = 0;
        for (i, byte) in bits.iter().enumerate() {
            let Byte::Constant(byte) = byte else {
                return None;
            };
            value |= u64::from(*byte) << (i * 8);
        }
        Some(value)
    }

    fn address(&self) -> Option<(usize, u64)> {
        match self {
            Self::Address { parameter, offset } => Some((*parameter, *offset)),
            Self::Bits(bits) => {
                let Byte::Parameter(parameter, 0) = bits.first()? else {
                    return None;
                };
                (*self == Self::parameter(*parameter)).then_some((*parameter, 0))
            }
        }
    }

    fn add(&self, offset: u64) -> Option<Self> {
        if offset == 0 {
            return Some(self.clone());
        }
        if let Some(value) = self.integer() {
            return Some(Self::constant(value.wrapping_add(offset)));
        }
        let (parameter, before) = self.address()?;
        let offset = before.checked_add(offset)?;
        (offset <= 4095).then_some(Self::Address { parameter, offset })
    }

    fn expression(&self) -> Option<E> {
        if let Some((parameter, offset)) = self.address() {
            return Some(E::var(format!("arg_{parameter}"), 64).bvadd(E::bv_const(offset, 64)));
        }
        // Only complete parameter words and literal bytes are constructed.
        Some(E::bv_const(self.integer()?, 64))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Store {
    parameter: usize,
    offset: u64,
    value: Word,
}

fn store(address: Word, value: Word) -> Option<Store> {
    let (parameter, offset) = address.address()?;
    (offset <= 4095 && offset % 8 == 0).then_some(Store {
        parameter,
        offset,
        value,
    })
}

fn source_stores(source: &Function) -> Option<Vec<Store>> {
    source.param_pointee_types.is_empty().then_some(())?;
    source_store_trace(source)
}

// Shape/effect interpretation only. Typed callers must independently check
// the complete pointee sidecar against the retained original TrustIR.
fn source_store_trace(source: &Function) -> Option<Vec<Store>> {
    if source.blocks.len() != 1
        || !source.stack_slots.is_empty()
        || !source.eh_info.is_empty()
        || source.stack_protector != StackProtectorMode::None
        || source.abi_sret_param.is_some()
        || !source.sret_arg_callees.is_empty()
        || !source.pure_callees.is_empty()
        || !source.libm_pure_callees.is_empty()
        || !source.signature.returns.is_empty()
        || !(1..=8).contains(&source.signature.params.len())
        || source.signature.params.iter().any(|ty| *ty != Type::I64)
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
                    .any(|(i, (value, ty))| value.0 as usize != i || *ty != Type::I64)))
    {
        return None;
    }
    let mut values: HashMap<Value, Word> = (0..source.signature.params.len())
        .map(|i| (Value(i as u32), Word::parameter(i)))
        .collect();
    let mut stores = Vec::new();
    let mut returned = false;
    for inst in &block.instructions {
        if returned {
            return None;
        }
        let value = |i: usize| values.get(inst.args.get(i)?).cloned();
        let (args, results, output) = match &inst.opcode {
            L::Copy | L::Bitcast { to_ty: Type::I64 } => (1, 1, Some(value(0)?)),
            L::Iconst { ty: Type::I64, imm } => (0, 1, Some(Word::constant(*imm as u64))),
            L::Imul => (
                2,
                1,
                Some(Word::constant(
                    value(0)?.integer()?.wrapping_mul(value(1)?.integer()?),
                )),
            ),
            L::Iadd => {
                let a = value(0)?;
                let b = value(1)?;
                let sum = if let Some(offset) = b.integer() {
                    a.add(offset)?
                } else {
                    b.add(a.integer()?)?
                };
                (2, 1, Some(sum))
            }
            L::ArrayGep { elem_ty } => {
                let stride = match elem_ty {
                    Type::I8 => 1,
                    Type::I16 => 2,
                    Type::I32 => 4,
                    Type::I64 => 8,
                    _ => return None,
                };
                let offset = value(1)?.integer()?.checked_mul(stride)?;
                (2, 1, Some(value(0)?.add(offset)?))
            }
            L::Store {
                ty: Type::I64,
                align,
            } => {
                if align.is_some_and(|a| a == 0 || a > 8 || !a.is_power_of_two()) {
                    return None;
                }
                stores.push(store(value(1)?, value(0)?)?);
                (2, 0, None)
            }
            L::Return => {
                returned = true;
                (0, 0, None)
            }
            _ => return None,
        };
        if inst.args.len() != args || inst.results.len() != results || stores.len() > 64 {
            return None;
        }
        if let Some(output) = output
            && values.insert(*inst.results.first()?, output).is_some()
        {
            return None;
        }
    }
    if !returned
        || stores.is_empty()
        || stores.iter().any(|s| s.parameter != stores[0].parameter)
        || source
            .value_types
            .iter()
            .any(|(id, ty)| !values.contains_key(id) || *ty != Type::I64)
    {
        return None;
    }
    Some(stores)
}

fn register(operand: &O) -> Option<usize> {
    match operand {
        O::PReg(reg) if reg.encoding() <= 17 => Some(usize::from(reg.encoding())),
        _ => None,
    }
}

fn machine_stores(source: &Function, machine: &MachFunction) -> Option<Vec<Store>> {
    if source.name != machine.name
        || machine.signature.params != vec![MachineType::I64; source.signature.params.len()]
        || !machine.signature.returns.is_empty()
        || !machine.stack_slots.is_empty()
        || machine.eh_metadata.has_eh_info()
        || machine.stack_protector != StackProtectorMode::None
        || machine.stack_protector_slot.is_some()
        || !machine.jump_tables.is_empty()
        || machine.insts.len() > 256
    {
        return None;
    }
    let mut registers: Vec<Option<Word>> = (0..18)
        .map(|i| (i < source.signature.params.len()).then(|| Word::parameter(i)))
        .collect();
    let mut stores = Vec::new();
    let mut returned = false;
    for inst in &machine.insts {
        if returned {
            return None;
        }
        if super::inert_allocated_nop(inst, machine.next_vreg) {
            continue;
        }
        if !inst.implicit_defs.is_empty()
            || !inst.implicit_uses.is_empty()
            || inst.flags != MachInst::new(inst.opcode, Vec::new()).flags
        {
            return None;
        }
        let value = |operand: &O| registers.get(register(operand)?)?.clone();
        let immediate = |operand: &O| match operand {
            O::Imm(n) => Some(*n),
            _ => None,
        };
        let operands = inst.operands.as_slice();
        let output = match (inst.opcode, operands) {
            (M::MOVXrr | M::MovR, [dst, src]) => Some((register(dst)?, value(src)?)),
            (M::AddRI, [dst, src, imm]) => {
                let offset = immediate(imm)?;
                if !(0..=4095).contains(&offset) {
                    return None;
                }
                Some((register(dst)?, value(src)?.add(offset as u64)?))
            }
            (M::AddRR, [dst, left, right]) => {
                let a = value(left)?;
                let b = value(right)?;
                let sum = if let Some(offset) = b.integer() {
                    a.add(offset)?
                } else {
                    b.add(a.integer()?)?
                };
                Some((register(dst)?, sum))
            }
            (M::Madd, [dst, left, right, addend]) => {
                // Read every input before writing dst: the emitted writer
                // reuses an argument register after its value has been stored.
                // Only constant products are in this address-transport domain.
                let product = value(left)?
                    .integer()?
                    .wrapping_mul(value(right)?.integer()?);
                Some((register(dst)?, value(addend)?.add(product)?))
            }
            (M::Movz | M::Movn | M::Movk, [dst, imm])
            | (M::Movz | M::Movn | M::Movk, [dst, imm, _]) => {
                let word = immediate(imm)?;
                let shift = if operands.len() == 3 {
                    immediate(&operands[2])?
                } else {
                    0
                };
                if !(0..=65535).contains(&word) || ![0, 16, 32, 48].contains(&shift) {
                    return None;
                }
                let bits = (word as u64) << shift;
                let result = match inst.opcode {
                    M::Movz => bits,
                    M::Movn => !bits,
                    _ => (value(dst)?.integer()? & !(0xffff_u64 << shift)) | bits,
                };
                Some((register(dst)?, Word::constant(result)))
            }
            (M::StrRI | M::STRXui, [data, base, imm]) => {
                let offset = immediate(imm)?;
                if !(0..=32760).contains(&offset) || offset % 8 != 0 {
                    return None;
                }
                stores.push(store(value(base)?.add(offset as u64)?, value(data)?)?);
                None
            }
            (M::StpRI, [a, b, base]) | (M::StpRI, [a, b, base, _]) => {
                let offset = if operands.len() == 4 {
                    immediate(&operands[3])?
                } else {
                    0
                };
                if !(0..=504).contains(&offset) || offset % 8 != 0 {
                    return None;
                }
                let address = value(base)?.add(offset as u64)?;
                stores.push(store(address.clone(), value(a)?)?);
                stores.push(store(address.add(8)?, value(b)?)?);
                None
            }
            (M::Ret, [O::PReg(reg)]) if *reg == X30 => {
                returned = true;
                None
            }
            _ => return None,
        };
        if let Some((register, value)) = output {
            registers[register] = Some(value);
        }
        if stores.len() > 64 {
            return None;
        }
    }
    returned.then_some(stores)
}

pub(super) fn obligation(source: &Function, machine: &MachFunction) -> Option<ProofObligation> {
    let source_stores = source_stores(source)?;
    obligation_for_trace(source, machine, &source_stores)
}

fn obligation_for_trace(
    source: &Function,
    machine: &MachFunction,
    source_stores: &[Store],
) -> Option<ProofObligation> {
    obligation_for_trace_in_frame(source, machine, source_stores, Aarch64OutputFrame::FpLr16)
}

fn obligation_for_trace_in_frame(
    source: &Function,
    machine: &MachFunction,
    source_stores: &[Store],
    frame: Aarch64OutputFrame,
) -> Option<ProofObligation> {
    let actual_stores = machine_stores(source, machine)?;
    // Compare the whole ordered trace before introducing ANY memory premise.
    // A changed store never becomes valid by selecting a convenient guard.
    if source_stores != actual_stores {
        return None;
    }
    if frame == Aarch64OutputFrame::Frameless {
        return frameless_obligation(source, source_stores, &actual_stores);
    }
    let sp = E::var("entry_sp", 64);
    let frame = sp.clone().bvsub(E::bv_const(16, 64));
    let fp = E::var("entry_fp", 64);
    let lr = E::var("entry_lr", 64);
    let original = E::uf("entry_memory", Vec::new(), memory_sort());
    let mut expected = original.clone();
    let mut actual = encode_store_le(&original, &frame, &fp, 8);
    actual = encode_store_le(&actual, &frame.clone().bvadd(E::bv_const(8, 64)), &lr, 8);
    let address =
        |s: &Store| E::var(format!("arg_{}", s.parameter), 64).bvadd(E::bv_const(s.offset, 64));
    for s in source_stores {
        expected = encode_store_le(&expected, &address(s), &s.value.expression()?, 8);
    }
    for s in &actual_stores {
        actual = encode_store_le(&actual, &address(s), &s.value.expression()?, 8);
    }
    let observe = E::var("observe", 64);
    let outside = observe
        .clone()
        .bvult(frame.clone())
        .or_expr(observe.clone().bvuge(sp.clone()));
    // A single arbitrary observation covers every output byte and all untouched
    // public memory. Repeating a load theorem for each store would redundantly
    // expand the complete store chain, making query size quadratic.
    let complete = encode_load_le(&actual, &frame, 8)
        .eq_expr(fp)
        .and_expr(encode_load_le(&actual, &frame.clone().bvadd(E::bv_const(8, 64)), 8).eq_expr(lr))
        .and_expr(frame.clone().bvadd(E::bv_const(16, 64)).eq_expr(sp.clone()))
        .and_expr(
            outside.not_expr().or_expr(
                E::select(actual.clone(), observe.clone())
                    .eq_expr(E::select(expected.clone(), observe)),
            ),
        );
    let output = E::var(format!("arg_{}", source_stores[0].parameter), 64);
    let extent = source_stores.iter().map(|s| s.offset + 8).max()?;
    let end = output.clone().bvadd(E::bv_const(extent, 64));
    // The last byte may be UINT64_MAX. In that case the exclusive end wraps
    // to zero and cannot witness "before the frame"; only the opposite range
    // ordering can establish separation. No accessed byte itself may wrap.
    let end_fits = output.clone().bvule(E::bv_const(u64::MAX - extent, 64));
    let mut inputs: Vec<_> = (0..source.signature.params.len())
        .map(|i| (format!("arg_{i}"), 64))
        .collect();
    inputs.extend(["entry_sp", "entry_fp", "entry_lr", "observe"].map(|s| (s.into(), 64)));
    Some(ProofObligation {
        name: "Diagnostic source-bound AArch64 output bytes; caller memory premise pending".into(),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: complete,
        inputs,
        preconditions: vec![
            sp.clone().bvuge(E::bv_const(16, 64)),
            sp.clone()
                .bvand(E::bv_const(15, 64))
                .eq_expr(E::bv_const(0, 64)),
            output
                .clone()
                .bvand(E::bv_const(7, 64))
                .eq_expr(E::bv_const(0, 64)),
            output
                .clone()
                .bvule(E::bv_const(u64::MAX - (extent - 1), 64)),
            end_fits
                .and_expr(end.bvule(frame))
                .or_expr(output.bvuge(sp)),
        ],
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::RegisterAllocation),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    })
}

// Caller validity is still an external requirement. This theorem relates
// complete observable byte maps; a frameless body has no hidden stack interval.
fn frameless_obligation(
    source: &Function,
    source_stores: &[Store],
    actual_stores: &[Store],
) -> Option<ProofObligation> {
    let original = E::uf("entry_memory", Vec::new(), memory_sort());
    let apply = |stores: &[Store]| -> Option<E> {
        let mut memory = original.clone();
        for store in stores {
            let address =
                E::var(format!("arg_{}", store.parameter), 64).bvadd(E::bv_const(store.offset, 64));
            memory = encode_store_le(&memory, &address, &store.value.expression()?, 8);
        }
        Some(memory)
    };
    let expected = apply(source_stores)?;
    let actual = apply(actual_stores)?;
    let observe = E::var("observe", 64);
    let output = E::var(format!("arg_{}", source_stores.first()?.parameter), 64);
    let extent = source_stores.iter().map(|store| store.offset + 8).max()?;
    let mut inputs: Vec<_> = (0..source.signature.params.len())
        .map(|index| (format!("arg_{index}"), 64))
        .collect();
    inputs.push(("observe".into(), 64));
    Some(ProofObligation {
        name:
            "Diagnostic source-bound AArch64 frameless output bytes; caller memory premise pending"
                .into(),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: E::select(actual, observe.clone()).eq_expr(E::select(expected, observe)),
        inputs,
        preconditions: vec![
            output
                .clone()
                .bvand(E::bv_const(7, 64))
                .eq_expr(E::bv_const(0, 64)),
            output.bvule(E::bv_const(u64::MAX - (extent - 1), 64)),
        ],
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::RegisterAllocation),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    })
}

#[cfg(test)]
#[path = "source_bound_output_memory_tests.rs"]
mod tests;
