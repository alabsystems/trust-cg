// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded, independent byte transport across one scalar stack object and calls.
//! This checker grants no proof credit. It compares caller-side cell and
//! argument observations, conditional on callee-save preservation and private
//! frame noninterference. Calls may affect other public memory. These premises
//! and the complete public-memory relation need separate proof authority.
//! The scalar-cell caller owner ([`super::source_bound_scalar_cell_caller`])
//! uses `checked` as its admission filter only: acceptance decides that a
//! whole-call theorem is built, never that a row is credited.

use trust_cg_ir::regs::{PReg, RegClass, SpecialReg, X19, X20, X29, X30};
use trust_cg_ir::{
    AArch64Opcode as M, InstFlags, InstId, MachFunction, MachInst, MachOperand as O,
};
use trust_cg_lower::Function;

use super::cell_source::values;
use super::output_memory::{Byte, bytes};

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ScalarCellFrameError {
    #[error(transparent)]
    Source(#[from] super::ScalarCellSourceError),
    #[error("unsupported scalar-cell machine layout or instruction ownership")]
    Layout,
    #[error("scalar-cell machine observations do not match the source")]
    Observations,
}

/// Immutable source and machine endpoints with matching scalar-cell events.
/// This is a diagnostic correspondence, not an instruction proof, emitted-byte
/// check, callback contract, or authority for compiler admission.
pub struct CheckedAarch64ScalarCellFrame<'a> {
    source: super::CheckedAarch64ScalarCellSource<'a>,
    machine: &'a MachFunction,
    frame: CheckedCellFrame,
}

impl<'a> CheckedAarch64ScalarCellFrame<'a> {
    pub fn source(&self) -> &super::CheckedAarch64ScalarCellSource<'a> {
        &self.source
    }
    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }
    pub fn frame_instructions(&self) -> &[InstId] {
        &self.frame.envelope
    }
    pub fn cell_width(&self) -> usize {
        self.frame.cell_width
    }
    pub fn call_count(&self) -> usize {
        self.frame.calls
    }

    /// Complete conditional memory model for these checked source/machine
    /// endpoints. Includes every call input, arbitrary public effects, final
    /// cell and return bits, saved registers and SP. Each callback observes
    /// only public memory and its arguments; private save bytes are preserved.
    /// Callbacks must also preserve C ABI callee-saved registers and SP.
    /// These environment premises and the writable, private 48-byte frame must
    /// be justified separately. Neither a typed declaration nor this query
    /// establishes them. No proof receipt or instruction credit is returned.
    /// Encoded bytes and relocations also require their separate checker.
    pub fn diagnostic_memory_obligation(&self) -> crate::lowering_proof::ProofObligation {
        super::cell_memory::obligation(self.source.contract())
    }
}

/// Bind original TrustIR, LIR and allocated machine cell/argument observations.
/// Opaque call results are distinct symbolic bytes. ABI preservation, private
/// memory noninterference, full public effects, and final bytes/relocations
/// remain separate obligations; this function cannot construct a proof receipt.
pub fn check_aarch64_scalar_cell_frame<'a>(
    module: &'a trust_ir::Module,
    lir: &'a Function,
    machine: &'a MachFunction,
) -> Result<CheckedAarch64ScalarCellFrame<'a>, ScalarCellFrameError> {
    let source = super::check_aarch64_scalar_cell_source(module, lir)?;
    let frame = checked(lir, machine)?;
    Ok(CheckedAarch64ScalarCellFrame {
        source,
        machine,
        frame,
    })
}

pub(super) fn checked(
    source: &Function,
    machine: &MachFunction,
) -> Result<CheckedCellFrame, ScalarCellFrameError> {
    let view = super::linear::source_view(source).ok_or(ScalarCellFrameError::Layout)?;
    let chain = super::linear::machine_chain(machine).map_err(|_| ScalarCellFrameError::Layout)?;
    super::check_owned_instructions_with(machine, &chain.live, false, |inst| {
        inert(inst, machine.next_vreg)
    })
    .ok_or(ScalarCellFrameError::Layout)?;
    check(&view, machine, &chain.instructions).ok_or(ScalarCellFrameError::Observations)
}

pub(super) struct CheckedCellFrame {
    pub envelope: Vec<InstId>,
    pub cell_width: usize,
    pub calls: usize,
}

#[derive(Clone)]
enum GeneralValue {
    Unknown,
    Address(i64),
    Constant(u64),
}

fn register(operand: &O) -> Option<PReg> {
    match operand {
        O::PReg(reg) => Some(*reg),
        _ => None,
    }
}

fn fp(reg: PReg) -> Option<(usize, usize)> {
    match reg.encoding() {
        96..=127 => Some((usize::from(reg.encoding() - 96), 8)),
        128..=159 => Some((usize::from(reg.encoding() - 128), 4)),
        _ => None,
    }
}

fn body_gpr(reg: PReg) -> Option<usize> {
    matches!(reg.encoding(), 0..=17 | 19..=20).then_some(usize::from(reg.encoding()))
}

fn scalar_gpr(reg: PReg) -> Option<(usize, usize)> {
    match reg.encoding() {
        0..=17 | 19..=20 => Some((usize::from(reg.encoding()), 8)),
        32..=49 | 51..=52 => Some((usize::from(reg.encoding() - 32), 4)),
        _ => None,
    }
}

fn caller(reg: PReg) -> bool {
    match reg.encoding() {
        0..=18 | 30 | 32..=50 | 62 => true,
        64..=95 => matches!(reg.encoding()-64, 0..=7 | 16..=31),
        96..=127 => matches!(reg.encoding()-96, 0..=7 | 16..=31),
        128..=159 => matches!(reg.encoding()-128, 0..=7 | 16..=31),
        165..=196 => matches!(reg.encoding()-165, 0..=7 | 16..=31),
        _ => false,
    }
}

fn ordinary(inst: &MachInst) -> bool {
    inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
        && (inst.flags == MachInst::new(inst.opcode, Vec::new()).flags
            || inst.flags
                == (MachInst::new(inst.opcode, Vec::new()).flags | InstFlags::IS_CALL_ARG_SETUP))
}

pub(super) fn inert(inst: &MachInst, next_vreg: u32) -> bool {
    let inert_register =
        |reg| body_gpr(reg).is_some() || fp(reg).is_some_and(|(i, _)| !(8..16).contains(&i));
    inst.opcode == M::Nop
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.iter().copied().all(inert_register)
        && (matches!(inst.flags, InstFlags::EMPTY | InstFlags::IS_PSEUDO)
            || inst.flags == (InstFlags::IS_PSEUDO | InstFlags::IS_CALL_ARG_SETUP))
        && match inst.operands.as_slice() {
            [] => true,
            [O::PReg(a), O::PReg(b)] => a == b && inert_register(*a),
            // A removed scalar copy may retain its virtual destination.
            // NOP defines no value: later real uses still need known bytes.
            [O::VReg(a), O::PReg(b)] => {
                a.id < next_vreg
                    && inert_register(*b)
                    && match a.class {
                        RegClass::Gpr64 => body_gpr(*b).is_some(),
                        RegClass::Fpr32 => fp(*b).is_some_and(|(_, width)| width == 4),
                        RegClass::Fpr64 => fp(*b).is_some_and(|(_, width)| width == 8),
                        _ => false,
                    }
            }
            _ => false,
        }
}

fn envelope(machine: &MachFunction, ids: &[InstId]) -> Option<Vec<InstId>> {
    if ids.len() < 9 {
        return None;
    }
    let pair = |a, b, offset| {
        vec![
            O::PReg(a),
            O::PReg(b),
            O::Special(SpecialReg::SP),
            O::Imm(offset),
        ]
    };
    let sp = |offset| {
        vec![
            O::Special(SpecialReg::SP),
            O::Special(SpecialReg::SP),
            O::Imm(offset),
        ]
    };
    let positions = [0, 1, 2, 3, ids.len() - 4, ids.len() - 3, ids.len() - 2];
    let expected = [
        (M::StpPreIndex, pair(X20, X19, -32)),
        (M::StpRI, pair(X29, X30, 16)),
        (
            M::AddRI,
            vec![O::PReg(X29), O::Special(SpecialReg::SP), O::Imm(16)],
        ),
        (M::SubRI, sp(16)),
        (M::AddRI, sp(16)),
        (M::LdpRI, pair(X29, X30, 16)),
        (M::LdpPostIndex, pair(X20, X19, 32)),
    ];
    for (position, (opcode, operands)) in positions.iter().zip(expected) {
        if !super::exact_instruction(
            machine.insts.get(ids[*position].0 as usize)?,
            opcode,
            &operands,
        ) {
            return None;
        }
    }
    Some(positions.map(|p| ids[p]).to_vec())
}

pub(super) fn check(
    source: &Function,
    machine: &MachFunction,
    ids: &[InstId],
) -> Option<CheckedCellFrame> {
    use trust_cg_ir::function::{StackProtectorMode, StackSlotAllocationKind, Type};
    let contract = values::contract(source)?;
    let ty = if contract.width == 4 {
        Type::F32
    } else {
        Type::F64
    };
    if source.name != machine.name
        || machine.signature.params != vec![ty.clone(); contract.parameters]
        || machine.signature.returns != [ty]
        || machine.stack_slots.len() != 1
        || machine.stack_slots[0].size != contract.width as u32
        || machine.stack_slots[0].align != contract.width as u32
        || machine.stack_slots[0].allocation != StackSlotAllocationKind::Fixed
        || machine.eh_metadata.has_eh_info()
        || machine.stack_protector != StackProtectorMode::None
        || machine.stack_protector_slot.is_some()
        || !machine.jump_tables.is_empty()
    {
        return None;
    }
    let envelope = envelope(machine, ids)?;
    let mut gpr = vec![GeneralValue::Unknown; 31];
    gpr[29] = GeneralValue::Address(-16);
    let mut fpr: Vec<Vec<Byte>> = (0..32)
        .map(|i| bytes(8, |b| Byte::Register(96 + i, b)))
        .collect();
    for (i, reg) in fpr.iter_mut().enumerate().take(contract.parameters) {
        reg[..contract.width].clone_from_slice(&bytes(contract.width, |b| Byte::Parameter(i, b)));
    }
    let cell_address = -32 - contract.width as i64;
    let mut cell = None;
    let mut calls = 0;
    for id in &ids[4..ids.len() - 4] {
        let inst = machine.insts.get(id.0 as usize)?;
        if inert(inst, machine.next_vreg) {
            continue;
        }
        if inst.opcode == M::Bl {
            let [O::Symbol(symbol)] = inst.operands.as_slice() else {
                return None;
            };
            let expected = contract.calls.get(calls)?;
            if inst.flags != MachInst::new(M::Bl, Vec::new()).flags
                || !inst.implicit_defs.iter().copied().all(caller)
                || inst.implicit_uses
                    != [
                        PReg::new(0),
                        PReg::new(if contract.width == 4 { 128 } else { 96 }),
                    ]
                || *symbol != expected.name
                || !matches!(gpr[0],GeneralValue::Address(a) if a==cell_address)
                || cell.as_ref()? != &expected.cell_before
                || fpr[0][..contract.width] != expected.argument
            {
                return None;
            }
            cell = Some(bytes(contract.width, |b| Byte::Call(calls, b)));
            for reg in &mut gpr[..19] {
                *reg = GeneralValue::Unknown;
            }
            gpr[30] = GeneralValue::Unknown;
            for (i, reg) in fpr.iter_mut().enumerate() {
                if !(8..16).contains(&i) {
                    *reg = bytes(8, |b| Byte::Clobber(calls, 96 + i as u8, b));
                }
            }
            calls += 1;
            continue;
        }
        if !ordinary(inst) {
            return None;
        }
        match (inst.opcode, inst.operands.as_slice()) {
            (M::Movz | M::Movn | M::Movk, [O::PReg(dst), O::Imm(imm)])
            | (M::Movz | M::Movn | M::Movk, [O::PReg(dst), O::Imm(imm), O::Imm(_)]) => {
                let (index, width) = scalar_gpr(*dst)?;
                let shift = match inst.operands.get(2) {
                    Some(O::Imm(shift)) => *shift,
                    None => 0,
                    _ => return None,
                };
                if !(0..=65535).contains(imm)
                    || shift < 0
                    || shift % 16 != 0
                    || shift >= (width * 8) as i64
                {
                    return None;
                }
                let bits = (*imm as u64) << shift;
                let value = match inst.opcode {
                    M::Movz => bits,
                    M::Movn => !bits,
                    M::Movk => {
                        let GeneralValue::Constant(previous) = gpr[index] else {
                            return None;
                        };
                        (previous & !(0xffff_u64 << shift)) | bits
                    }
                    _ => unreachable!(),
                };
                // Every W-register write also clears the upper X bits.
                gpr[index] = GeneralValue::Constant(if width == 4 {
                    value & u64::from(u32::MAX)
                } else {
                    value
                });
            }
            (M::FmovGprFpr, [O::PReg(dst), O::PReg(src)]) => {
                let (d, width) = fp(*dst)?;
                let (s, source_width) = scalar_gpr(*src)?;
                if width != source_width || (8..16).contains(&d) {
                    return None;
                }
                let GeneralValue::Constant(value) = gpr[s] else {
                    return None;
                };
                fpr[d] = bytes(8, |b| {
                    Byte::Constant(if b < width {
                        (value >> (8 * b)) as u8
                    } else {
                        0
                    })
                });
            }
            (M::MOVXrr, [O::PReg(dst), O::PReg(src)]) => {
                gpr[body_gpr(*dst)?] = gpr.get(usize::from(src.encoding()))?.clone();
            }
            (M::AddRI | M::SubRI, [O::PReg(dst), O::PReg(src), O::Imm(offset)])
                if (0..4096).contains(offset) =>
            {
                let GeneralValue::Address(base) = gpr.get(usize::from(src.encoding()))? else {
                    return None;
                };
                let address = if inst.opcode == M::AddRI {
                    base.checked_add(*offset)?
                } else {
                    base.checked_sub(*offset)?
                };
                gpr[body_gpr(*dst)?] = GeneralValue::Address(address);
            }
            (M::NeonOrrV, [O::PReg(dst), O::PReg(left), O::PReg(right), O::Imm(1)])
                if left == right =>
            {
                let (d, w) = fp(*dst)?;
                let (s, sw) = fp(*left)?;
                if w != sw || (8..16).contains(&d) {
                    return None;
                }
                fpr[d] = fpr[s].clone();
            }
            (M::StrRI | M::LdrRI, [data, O::PReg(base), O::Imm(0)]) => {
                let (index, width) = fp(register(data)?)?;
                if width != contract.width
                    || (8..16).contains(&index)
                    || !matches!(gpr.get(usize::from(base.encoding()))?,GeneralValue::Address(a) if *a==cell_address)
                {
                    return None;
                }
                if inst.opcode == M::StrRI {
                    cell = Some(fpr[index][..width].to_vec());
                } else {
                    fpr[index] = bytes(8, |_| Byte::Constant(0));
                    fpr[index][..width].clone_from_slice(cell.as_ref()?);
                }
            }
            _ => return None,
        }
    }
    let ret = machine.insts.get(ids.last()?.0 as usize)?;
    if ret.opcode != M::Ret
        || ret.operands != [O::PReg(X30)]
        || ret.flags != MachInst::new(M::Ret, Vec::new()).flags
        || !ret.implicit_defs.is_empty()
        || ret.implicit_uses != [PReg::new(if contract.width == 4 { 128 } else { 96 })]
        || calls != contract.calls.len()
        || cell? != contract.cell_after
        || fpr[0][..contract.width] != contract.result
    {
        return None;
    }
    Some(CheckedCellFrame {
        envelope,
        cell_width: contract.width,
        calls,
    })
}

/// The stack-local algebra after framing a conforming external call's public
/// effects. The byte interpreter must separately establish that private saves
/// do not escape and that source/machine call observations coincide. This
/// formula alone grants no permission to assume a callback preserves memory.
#[cfg(test)]
pub(super) fn obligation(width: usize) -> crate::lowering_proof::ProofObligation {
    use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
    use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
    use crate::smt::SmtExpr as E;
    assert!(matches!(width, 4 | 8));
    let sp = E::var("entry_sp", 64);
    let address = |below| sp.clone().bvsub(E::bv_const(below, 64));
    let original = E::uf("entry_memory", Vec::new(), memory_sort());
    let saved = [
        ("entry_x20", 32),
        ("entry_x19", 24),
        ("entry_fp", 16),
        ("entry_lr", 8),
    ];
    let mut memory = original.clone();
    for (name, below) in saved {
        memory = encode_store_le(&memory, &address(below), &E::var(name, 64), 8);
    }
    let cell = address(32 + width as u64);
    let before = E::var("cell_before", (width * 8) as u32);
    let after = E::var("cell_after", (width * 8) as u32);
    memory = encode_store_le(&memory, &cell, &before, width as u32);
    memory = encode_store_le(&memory, &cell, &after, width as u32);
    let restored_sp = sp
        .clone()
        .bvsub(E::bv_const(32, 64))
        .bvsub(E::bv_const(16, 64))
        .bvadd(E::bv_const(16, 64))
        .bvadd(E::bv_const(32, 64));
    let mut complete = restored_sp.eq_expr(sp.clone());
    for (name, below) in saved {
        complete = complete
            .and_expr(encode_load_le(&memory, &address(below), 8).eq_expr(E::var(name, 64)));
    }
    complete = complete.and_expr(encode_load_le(&memory, &cell, width as u32).eq_expr(after));
    let observe = E::var("observe", 64);
    let outside = observe
        .clone()
        .bvult(address(48))
        .or_expr(observe.clone().bvuge(sp.clone()));
    complete = complete.and_expr(
        outside
            .not_expr()
            .or_expr(E::select(memory, observe.clone()).eq_expr(E::select(original, observe))),
    );
    let mut inputs = vec![("entry_sp".into(), 64), ("observe".into(), 64)];
    inputs.extend(saved.map(|(name, _)| (name.into(), 64)));
    inputs.extend([
        ("cell_before".into(), (width * 8) as u32),
        ("cell_after".into(), (width * 8) as u32),
    ]);
    ProofObligation {
        name: format!(
            "Source-bound AArch64 scalar cell: private saves and {}-bit payload",
            width * 8
        ),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: complete,
        inputs,
        preconditions: vec![
            sp.clone().bvuge(E::bv_const(48, 64)),
            sp.bvand(E::bv_const(15, 64)).eq_expr(E::bv_const(0, 64)),
        ],
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::RegisterAllocation),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

#[cfg(test)]
#[path = "source_bound_cell_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "source_bound_cell_pipeline_tests.rs"]
mod pipeline_tests;
