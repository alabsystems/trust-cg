// trust-cg-codegen/debug_provenance.rs - Verified debug variable range adapter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Codegen-side filtering for provenance-backed debug variable ranges.
//!
//! The DWARF writer consumes byte-addressed location-list entries. This module
//! is the narrow adapter between post-RA provenance ranges and those entries:
//! only ranges that still describe a declared debug local and a bounded,
//! non-overlapping final machine-code span are converted.

use std::collections::BTreeMap;

use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::{AArch64Opcode, InstFlags, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::provenance::{
    LocationExpr, ProvenanceMap, TrustIrInstId, TrustIrVarId, TrustIrVarNamespace, VarLocation,
};
use trust_cg_ir::regs::{
    PReg, RegClass, SP, WSP, WZR, XZR, gpr32_to_gpr64, preg_class, reg_number, regs_overlap,
};
use trust_cg_ir::types::{InstId, StackSlotId};
use trust_cg_opt::effects::{aarch64_def_operand_positions, is_lse_cas, is_lse_rmw};

use crate::dwarf_info::{LocationListEntry, VariableLocation};

const LEGACY_VALUE_DEBUG_PROVENANCE_VAR_TAG: u32 = 0x2000_0000;
const LEGACY_DEBUG_PROVENANCE_VAR_INDEX_MASK: u32 = 0x1fff_ffff;

/// Declared debug-local metadata needed to validate provenance ranges.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DebugProvenanceLocal {
    /// Source-visible variable ID used by the provenance map.
    pub var_id: TrustIrVarId,
    /// Declared source type width. Ranges narrower than their storage are fine;
    /// ranges wider than their storage are rejected.
    pub bit_width: u16,
    /// Stack slot that is live for the whole function as source storage.
    ///
    /// This is used for fixed alloca-backed locals. Spill-backed stack ranges
    /// must instead start immediately after a concrete store to the slot.
    pub entry_stack_slot: Option<StackSlotId>,
}

impl DebugProvenanceLocal {
    /// Create declaration metadata for one provenance-backed debug local.
    pub fn new(
        var_id: TrustIrVarId,
        bit_width: u16,
        entry_stack_slot: Option<StackSlotId>,
    ) -> Self {
        Self {
            var_id,
            bit_width,
            entry_stack_slot,
        }
    }
}

/// Filters post-RA provenance ranges into DWARF location-list entries.
pub struct DebugProvenanceAdapter<'a> {
    ir_func: &'a MachFunction,
    provenance: &'a ProvenanceMap,
    stack_slot_offsets: &'a [Option<i32>],
    code_size: u32,
    locals: BTreeMap<TrustIrVarId, DebugProvenanceLocal>,
    layout: InstructionLayout,
}

impl<'a> DebugProvenanceAdapter<'a> {
    /// Build an adapter for the final post-RA function.
    pub fn new<I>(
        ir_func: &'a MachFunction,
        provenance: &'a ProvenanceMap,
        stack_slot_offsets: &'a [Option<i32>],
        code_size: u32,
        locals: I,
    ) -> Self
    where
        I: IntoIterator<Item = DebugProvenanceLocal>,
    {
        Self {
            ir_func,
            provenance,
            stack_slot_offsets,
            code_size,
            locals: locals
                .into_iter()
                .map(|local| (local.var_id, local))
                .collect(),
            layout: InstructionLayout::new(ir_func, code_size),
        }
    }

    /// Return verifier-accepted DWARF location-list entries for `var_id`.
    ///
    /// Undeclared variables, dead ranges, malformed ranges, and ranges whose
    /// final location cannot be proven are omitted.
    pub fn location_list_entries(&self, var_id: TrustIrVarId) -> Vec<LocationListEntry> {
        let Some(local) = self.locals.get(&var_id).copied() else {
            return Vec::new();
        };

        self.location_list_entries_from_ranges(
            var_id,
            local,
            self.provenance.var_live_ranges(var_id),
        )
    }

    fn location_list_entries_from_ranges(
        &self,
        var_id: TrustIrVarId,
        local: DebugProvenanceLocal,
        raw_ranges: &[VarLocation],
    ) -> Vec<LocationListEntry> {
        let mut ranges: Vec<&VarLocation> = raw_ranges
            .iter()
            .filter(|loc| !matches!(loc.value, LocationExpr::Dead { .. }))
            .collect();
        ranges.sort_by_key(|loc| (loc.start, loc.end));

        let mut previous_live: Option<&VarLocation> = None;
        let mut entries = Vec::new();
        for loc in ranges {
            if loc.var != var_id {
                return Vec::new();
            }
            if loc.start >= loc.end {
                continue;
            }
            if let Some(previous) = previous_live
                && loc.start < previous.end
            {
                return Vec::new();
            }
            previous_live = Some(loc);

            if let Some(entry) = self.location_list_entry(local, loc) {
                entries.push(entry);
            }
        }

        entries.sort_by_key(|entry| (entry.low_pc, entry.size, entry.expression.clone()));
        entries
    }

    fn location_list_entry(
        &self,
        local: DebugProvenanceLocal,
        loc: &VarLocation,
    ) -> Option<LocationListEntry> {
        let (low_pc, size) = self.range_byte_bounds(loc)?;
        let dwarf_location = match loc.value {
            LocationExpr::Reg(preg) => {
                self.validate_register_range(local, loc, preg)?;
                VariableLocation::Register(dwarf_register_number(preg)?)
            }
            LocationExpr::Stack(slot) => {
                let frame_offset = self.validate_stack_range(local, loc, slot)?;
                VariableLocation::FrameOffset(i64::from(frame_offset))
            }
            LocationExpr::Const { value, bit_width } => {
                self.validate_constant_range(local, value, bit_width)?;
                VariableLocation::ConstantInt(u64::try_from(value).ok()?)
            }
            LocationExpr::Dead { .. } => return None,
        };

        Some(LocationListEntry::from_location(
            low_pc,
            size,
            &dwarf_location,
        ))
    }

    fn range_byte_bounds(&self, loc: &VarLocation) -> Option<(u64, u32)> {
        if self.code_size == 0 || loc.end.0 as usize > self.ir_func.insts.len() {
            return None;
        }

        let start_inst = self.ir_func.insts.get(loc.start.0 as usize)?;
        if start_inst.is_pseudo() {
            return None;
        }

        let start_position = self.layout.position(loc.start)?;
        let end_position = self.layout.end_position(loc.end, self.ir_func)?;
        if start_position >= end_position {
            return None;
        }

        let low_pc = self.layout.byte_boundary(loc.start)?;
        let high_pc = if loc.end == function_end_inst(self.ir_func) {
            self.code_size
        } else {
            self.layout.byte_boundary(loc.end)?
        };
        if low_pc >= high_pc || high_pc > self.code_size {
            return None;
        }

        Some((u64::from(low_pc), high_pc - low_pc))
    }

    fn validate_register_range(
        &self,
        local: DebugProvenanceLocal,
        loc: &VarLocation,
        preg: PReg,
    ) -> Option<()> {
        let class = valid_dwarf_register_class(preg)?;
        if u32::from(local.bit_width) > class.size_bits() {
            return None;
        }

        let start_inst = self.ir_func.insts.get(loc.start.0 as usize)?;
        if !inst_defines_preg(start_inst, preg) {
            return None;
        }
        validate_register_source_origin(self.provenance, local.var_id, loc.start, start_inst)?;

        for inst_id in self
            .layout
            .insts_after_start_before_end(loc.start, loc.end, self.ir_func)
        {
            let inst = self.ir_func.insts.get(inst_id.0 as usize)?;
            if inst.is_pseudo() {
                continue;
            }
            if inst_clobbers_preg(inst, preg) {
                return None;
            }
        }

        Some(())
    }

    fn validate_stack_range(
        &self,
        local: DebugProvenanceLocal,
        loc: &VarLocation,
        slot: StackSlotId,
    ) -> Option<i32> {
        let stack_slot = self.ir_func.stack_slots.get(slot.0 as usize)?;
        let slot_size = stack_slot.fixed_size()?;
        if slot_size == 0 || u32::from(local.bit_width) > slot_size.saturating_mul(8) {
            return None;
        }

        let frame_offset = self
            .stack_slot_offsets
            .get(slot.0 as usize)
            .copied()
            .flatten()?;
        if local.entry_stack_slot == Some(slot) {
            return Some(frame_offset);
        }

        let materializing_store = self
            .layout
            .previous_non_pseudo_before(loc.start, self.ir_func)
            .filter(|&inst_id| {
                self.ir_func
                    .insts
                    .get(inst_id.0 as usize)
                    .is_some_and(|inst| {
                        inst_writes_stack_location(inst, slot, frame_offset)
                            || inst.flags.contains(InstFlags::WRITES_MEMORY)
                    })
            })?;

        validate_stack_store_source_origin(self.provenance, local.var_id, materializing_store)?;

        if self.stack_slot_has_conflicting_live_owner(local.var_id, loc, slot) {
            return None;
        }

        let start_inst = self.ir_func.insts.get(loc.start.0 as usize)?;
        if inst_writes_stack_location(start_inst, slot, frame_offset) {
            return None;
        }
        for inst_id in self
            .layout
            .insts_after_start_before_end(loc.start, loc.end, self.ir_func)
        {
            let inst = self.ir_func.insts.get(inst_id.0 as usize)?;
            if inst.is_pseudo() {
                continue;
            }
            if inst_writes_stack_location(inst, slot, frame_offset) {
                return None;
            }
        }

        Some(frame_offset)
    }

    fn stack_slot_has_conflicting_live_owner(
        &self,
        var_id: TrustIrVarId,
        loc: &VarLocation,
        slot: StackSlotId,
    ) -> bool {
        self.provenance.declared_vars().iter().any(|&other_var| {
            other_var != var_id
                && self
                    .provenance
                    .var_live_ranges(other_var)
                    .iter()
                    .filter(|other| !matches!(other.value, LocationExpr::Dead { .. }))
                    .any(|other| {
                        matches!(other.value, LocationExpr::Stack(other_slot) if other_slot == slot)
                            && ranges_overlap(loc.start, loc.end, other.start, other.end)
                    })
        })
    }

    fn validate_constant_range(
        &self,
        local: DebugProvenanceLocal,
        value: u128,
        bit_width: u16,
    ) -> Option<()> {
        if bit_width == 0 || bit_width > 64 || bit_width != local.bit_width {
            return None;
        }
        let mask = if bit_width == 64 {
            u128::from(u64::MAX)
        } else {
            (1u128 << bit_width) - 1
        };
        (value & !mask == 0).then_some(())
    }
}

#[derive(Debug, Clone)]
struct InstructionLayout {
    ordered: Vec<InstId>,
    positions: BTreeMap<InstId, usize>,
    byte_boundaries: BTreeMap<InstId, u32>,
}

impl InstructionLayout {
    fn new(ir_func: &MachFunction, code_size: u32) -> Self {
        let mut ordered = Vec::new();
        let mut positions = BTreeMap::new();
        let mut byte_boundaries = BTreeMap::new();
        let mut offset = 0u32;

        for block_id in &ir_func.block_order {
            let Some(block) = ir_func.blocks.get(block_id.0 as usize) else {
                continue;
            };
            for &inst_id in &block.insts {
                let Some(inst) = ir_func.insts.get(inst_id.0 as usize) else {
                    continue;
                };
                positions.entry(inst_id).or_insert_with(|| ordered.len());
                byte_boundaries
                    .entry(inst_id)
                    .or_insert(offset.min(code_size));
                ordered.push(inst_id);
                if !inst.is_pseudo() {
                    offset = offset.saturating_add(4).min(code_size);
                }
            }
        }

        Self {
            ordered,
            positions,
            byte_boundaries,
        }
    }

    fn position(&self, inst: InstId) -> Option<usize> {
        self.positions.get(&inst).copied()
    }

    fn byte_boundary(&self, inst: InstId) -> Option<u32> {
        self.byte_boundaries.get(&inst).copied()
    }

    fn end_position(&self, end: InstId, ir_func: &MachFunction) -> Option<usize> {
        if end == function_end_inst(ir_func) {
            Some(self.ordered.len())
        } else {
            self.position(end)
        }
    }

    fn previous_non_pseudo_before(&self, inst: InstId, ir_func: &MachFunction) -> Option<InstId> {
        let position = self.position(inst)?;
        self.ordered[..position]
            .iter()
            .rev()
            .copied()
            .find(|candidate| {
                ir_func
                    .insts
                    .get(candidate.0 as usize)
                    .is_some_and(|inst| !inst.is_pseudo())
            })
    }

    fn insts_after_start_before_end(
        &self,
        start: InstId,
        end: InstId,
        ir_func: &MachFunction,
    ) -> Vec<InstId> {
        let Some(start_position) = self.position(start) else {
            return Vec::new();
        };
        let Some(end_position) = self.end_position(end, ir_func) else {
            return Vec::new();
        };
        if start_position >= end_position {
            return Vec::new();
        }
        self.ordered[start_position + 1..end_position].to_vec()
    }
}

fn function_end_inst(ir_func: &MachFunction) -> InstId {
    InstId(u32::try_from(ir_func.insts.len()).unwrap_or(u32::MAX))
}

fn dwarf_register_number(preg: PReg) -> Option<u64> {
    valid_dwarf_register_class(preg)?;
    let preg = match preg_class(preg) {
        RegClass::Gpr32 => gpr32_to_gpr64(preg).unwrap_or(preg),
        _ => preg,
    };
    Some(u64::from(preg.encoding()))
}

fn valid_dwarf_register_class(preg: PReg) -> Option<RegClass> {
    if matches!(preg, SP | WSP | XZR | WZR) || reg_number(preg).is_none() {
        return None;
    }
    let class = preg_class(preg);
    (!matches!(class, RegClass::System)).then_some(class)
}

fn debug_value_origin_from_var(var_id: TrustIrVarId) -> Option<TrustIrInstId> {
    if matches!(
        var_id.namespace(),
        Some(TrustIrVarNamespace::O3RegisterLocal | TrustIrVarNamespace::O3SpillLocal)
    ) {
        return Some(TrustIrInstId(var_id.namespace_index()));
    }
    if var_id.0 & !LEGACY_DEBUG_PROVENANCE_VAR_INDEX_MASK == LEGACY_VALUE_DEBUG_PROVENANCE_VAR_TAG {
        return Some(TrustIrInstId(
            var_id.0 & LEGACY_DEBUG_PROVENANCE_VAR_INDEX_MASK,
        ));
    }

    None
}

fn register_debug_origin_from_var(var_id: TrustIrVarId) -> Option<TrustIrInstId> {
    debug_value_origin_from_var(var_id)
}

fn validate_register_source_origin(
    provenance: &ProvenanceMap,
    var_id: TrustIrVarId,
    start: InstId,
    start_inst: &MachInst,
) -> Option<()> {
    let expected_origin = register_debug_origin_from_var(var_id)?;
    let entry = provenance.get_entry(start)?;
    if !entry.is_active() {
        return None;
    }
    let [actual_origin] = entry.trust_ir_origins.as_slice() else {
        return None;
    };
    if *actual_origin != expected_origin {
        return None;
    }
    if !provenance
        .get_mach_insts(expected_origin)
        .is_some_and(|insts| insts.contains(&start))
    {
        return None;
    }
    if register_start_is_ambiguous_transfer(start_inst) {
        return None;
    }

    Some(())
}

fn validate_stack_store_source_origin(
    provenance: &ProvenanceMap,
    var_id: TrustIrVarId,
    store: InstId,
) -> Option<()> {
    let expected_origin = debug_value_origin_from_var(var_id)?;
    let entry = provenance.get_entry(store)?;
    if !entry.is_active() {
        return None;
    }
    let [actual_origin] = entry.trust_ir_origins.as_slice() else {
        return None;
    };
    if *actual_origin != expected_origin {
        return None;
    }
    if !provenance
        .get_mach_insts(expected_origin)
        .is_some_and(|insts| insts.contains(&store))
    {
        return None;
    }

    Some(())
}

fn ranges_overlap(a_start: InstId, a_end: InstId, b_start: InstId, b_end: InstId) -> bool {
    a_start < b_end && b_start < a_end
}

fn register_start_is_ambiguous_transfer(inst: &MachInst) -> bool {
    inst.opcode.is_move() || inst.flags.contains(InstFlags::READS_MEMORY)
}

fn inst_writes_stack_location(inst: &MachInst, slot: StackSlotId, frame_offset: i32) -> bool {
    inst.flags.contains(InstFlags::WRITES_MEMORY)
        && inst.operands.iter().any(|operand| match operand {
            MachOperand::StackSlot(candidate) => *candidate == slot,
            MachOperand::MemOp { offset, .. } => *offset == i64::from(frame_offset),
            _ => false,
        })
}

fn inst_clobbers_preg(inst: &MachInst, preg: PReg) -> bool {
    if inst.flags.contains(InstFlags::IS_CALL)
        && trust_cg_regalloc::aarch64_caller_saved_regs()
            .into_iter()
            .any(|caller_saved| regs_overlap(caller_saved, preg))
    {
        return true;
    }

    inst_defines_preg(inst, preg)
}

fn inst_defines_preg(inst: &MachInst, preg: PReg) -> bool {
    def_operand_positions(inst).iter().any(|&pos| {
        matches!(
            inst.operands.get(pos),
            Some(MachOperand::PReg(def)) if regs_overlap(*def, preg)
        )
    }) || inst
        .implicit_defs
        .iter()
        .any(|&def| regs_overlap(def, preg))
}

fn def_operand_positions(inst: &MachInst) -> Vec<usize> {
    if opcode_has_lse_atomic_operand_roles(inst.opcode)
        || opcode_has_explicit_writeback_operand_roles(inst.opcode)
    {
        return aarch64_def_operand_positions(inst.opcode, inst.operands.len());
    }
    if opcode_uses_all_operands_for_regalloc(inst.opcode, inst.flags) || inst.operands.is_empty() {
        Vec::new()
    } else {
        aarch64_def_operand_positions(inst.opcode, inst.operands.len())
    }
}

fn opcode_has_lse_atomic_operand_roles(opcode: AArch64Opcode) -> bool {
    is_lse_rmw(opcode) || is_lse_cas(opcode)
}

fn opcode_has_explicit_writeback_operand_roles(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::LdrPreIndex
            | AArch64Opcode::StrPreIndex
            | AArch64Opcode::LdrPostIndex
            | AArch64Opcode::StrPostIndex
            | AArch64Opcode::LdpPostIndex
            | AArch64Opcode::StpPreIndex
            | AArch64Opcode::NeonLd1Post
            | AArch64Opcode::NeonLdpQPost
            | AArch64Opcode::NeonSt1Post
            | AArch64Opcode::NeonStpQPost
    )
}

fn opcode_uses_all_operands_for_regalloc(opcode: AArch64Opcode, flags: InstFlags) -> bool {
    if opcode_has_lse_atomic_operand_roles(opcode) {
        return false;
    }

    let is_store = flags.contains(InstFlags::WRITES_MEMORY);
    let is_branch = flags.contains(InstFlags::IS_BRANCH);
    let is_return = flags.contains(InstFlags::IS_RETURN);
    let is_call = flags.contains(InstFlags::IS_CALL);
    let is_cmp = matches!(
        opcode,
        AArch64Opcode::CmpRR | AArch64Opcode::CmpRI | AArch64Opcode::Fcmp
    );

    is_store || is_branch || is_return || is_call || is_cmp
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::{
        DebugBaseType, DebugLocalVariable, DebugVariableStorage, Signature, StackSlot,
    };
    use trust_cg_ir::inst::AArch64Opcode;
    use trust_cg_ir::regs::{PReg, SP, X0, X1, X2};

    fn bit_width(ty: DebugBaseType) -> u16 {
        match ty {
            DebugBaseType::Bool => 1,
            DebugBaseType::I8 | DebugBaseType::U8 => 8,
            DebugBaseType::I16 | DebugBaseType::U16 => 16,
            DebugBaseType::I32 | DebugBaseType::U32 | DebugBaseType::F32 => 32,
            DebugBaseType::I64 | DebugBaseType::U64 | DebugBaseType::F64 | DebugBaseType::Ptr => 64,
            DebugBaseType::I128 | DebugBaseType::U128 => 128,
        }
    }

    fn test_func() -> (MachFunction, InstId, InstId, InstId) {
        let mut func = MachFunction::new(
            "debug_provenance_adapter".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let first = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::PReg(X0), MachOperand::Imm(1)],
        ));
        let second = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X0),
                MachOperand::PReg(X2),
            ],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(entry, first);
        func.append_inst(entry, second);
        func.append_inst(entry, ret);
        (func, first, second, ret)
    }

    fn local(var_id: TrustIrVarId) -> DebugProvenanceLocal {
        DebugProvenanceLocal::new(var_id, bit_width(DebugBaseType::U64), None)
    }

    fn value_var(origin: TrustIrInstId) -> TrustIrVarId {
        TrustIrVarId(LEGACY_VALUE_DEBUG_PROVENANCE_VAR_TAG | origin.0)
    }

    fn record_origin(provenance: &mut ProvenanceMap, origin: TrustIrInstId, inst: InstId) {
        provenance.record_lowering(origin, &[inst], trust_cg_ir::PassId::new("test-isel"));
    }

    fn stack_spill_func() -> (MachFunction, StackSlotId, InstId, InstId, InstId, InstId) {
        let mut func = MachFunction::new(
            "debug_provenance_stack_spill".to_string(),
            Signature::new(vec![], vec![]),
        );
        let slot = func.alloc_stack_slot(StackSlot::new(8, 8));
        let entry = func.entry;
        let value = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::PReg(X0), MachOperand::Imm(1)],
        ));
        let store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![MachOperand::PReg(X0), MachOperand::StackSlot(slot)],
        ));
        let live = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(entry, value);
        func.append_inst(entry, store);
        func.append_inst(entry, live);
        func.append_inst(entry, ret);
        (func, slot, value, store, live, ret)
    }

    #[test]
    fn debug_provenance_accepts_declared_register_range() {
        let (func, first, _second, ret) = test_func();
        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, origin, first);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, first, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);
        let entries = adapter.location_list_entries(var_id);

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].low_pc, 0);
        assert_eq!(entries[0].size, 8);
    }

    #[test]
    fn debug_provenance_rejects_register_range_starting_at_use_only_inst() {
        let (func, _first, second, ret) = test_func();
        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, origin, second);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, second, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_register_range_without_source_origin() {
        let (func, first, _second, ret) = test_func();
        let var_id = TrustIrVarId(7);
        let mut provenance = ProvenanceMap::new();
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, first, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_register_range_with_wrong_origin() {
        let (func, first, _second, ret) = test_func();
        let expected_origin = TrustIrInstId(7);
        let actual_origin = TrustIrInstId(8);
        let var_id = value_var(expected_origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, actual_origin, first);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, first, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_register_range_with_multi_origin_def() {
        let (func, first, second, ret) = test_func();
        let expected_origin = TrustIrInstId(7);
        let merged_origin = TrustIrInstId(8);
        let var_id = value_var(expected_origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, expected_origin, first);
        record_origin(&mut provenance, merged_origin, second);
        provenance.record_merge(
            &[first, second],
            first,
            trust_cg_ir::PassId::new("test-merge"),
        );
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, first, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_register_range_starting_at_copy() {
        let mut func = MachFunction::new(
            "debug_provenance_copy_start".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let copy = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(entry, copy);
        func.append_inst(entry, ret);

        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, origin, copy);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, copy, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 8, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_register_range_starting_at_reload() {
        let mut func = MachFunction::new(
            "debug_provenance_reload_start".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let reload = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(SP),
                MachOperand::Imm(0),
            ],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(entry, reload);
        func.append_inst(entry, ret);

        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, origin, reload);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, reload, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 8, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_accepts_stack_range_after_provenance_backed_store() {
        let (func, slot, _value, store, live, ret) = stack_spill_func();
        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, origin, store);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, live, ret, LocationExpr::Stack(slot)),
            )
            .unwrap();

        let adapter =
            DebugProvenanceAdapter::new(&func, &provenance, &[Some(-8)], 16, [local(var_id)]);
        let entries = adapter.location_list_entries(var_id);

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].low_pc, 8);
        assert_eq!(entries[0].size, 4);
        assert_eq!(
            entries[0].expression,
            crate::dwarf_info::encode_location_expr(&VariableLocation::FrameOffset(-8))
        );
    }

    #[test]
    fn debug_provenance_rejects_stack_range_without_store_provenance() {
        let (func, slot, _value, _store, live, ret) = stack_spill_func();
        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let mut provenance = ProvenanceMap::new();
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, live, ret, LocationExpr::Stack(slot)),
            )
            .unwrap();

        let adapter =
            DebugProvenanceAdapter::new(&func, &provenance, &[Some(-8)], 16, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_stack_range_with_wrong_store_origin() {
        let (func, slot, _value, store, live, ret) = stack_spill_func();
        let expected_origin = TrustIrInstId(7);
        let actual_origin = TrustIrInstId(8);
        let var_id = value_var(expected_origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, actual_origin, store);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, live, ret, LocationExpr::Stack(slot)),
            )
            .unwrap();

        let adapter =
            DebugProvenanceAdapter::new(&func, &provenance, &[Some(-8)], 16, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_stack_range_starting_at_materializing_store() {
        let (func, slot, _value, store, _live, ret) = stack_spill_func();
        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, origin, store);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, store, ret, LocationExpr::Stack(slot)),
            )
            .unwrap();

        let adapter =
            DebugProvenanceAdapter::new(&func, &provenance, &[Some(-8)], 16, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_stack_range_with_conflicting_live_owner() {
        let (func, slot, _value, store, live, ret) = stack_spill_func();
        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let other_var_id = value_var(TrustIrInstId(8));
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, origin, store);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, live, ret, LocationExpr::Stack(slot)),
            )
            .unwrap();
        provenance
            .declare_var(
                other_var_id,
                VarLocation::new(other_var_id, live, ret, LocationExpr::Stack(slot)),
            )
            .unwrap();

        let adapter =
            DebugProvenanceAdapter::new(&func, &provenance, &[Some(-8)], 16, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_undeclared_variable() {
        let (func, first, _second, ret) = test_func();
        let origin = TrustIrInstId(7);
        let var_id = value_var(origin);
        let mut provenance = ProvenanceMap::new();
        record_origin(&mut provenance, origin, first);
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, first, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, []);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_skips_dead_ranges() {
        let (func, first, _second, ret) = test_func();
        let var_id = TrustIrVarId(7);
        let mut provenance = ProvenanceMap::new();
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, first, ret, LocationExpr::Reg(X0)),
            )
            .unwrap();
        provenance
            .kill_var(
                var_id,
                first,
                trust_cg_ir::PassId::new("test"),
                trust_cg_ir::provenance::DeadReason::SourceLifetimeEnded,
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_drops_empty_and_out_of_bounds_ranges() {
        let (func, first, _second, _ret) = test_func();
        let var_id = TrustIrVarId(7);
        let empty = VarLocation::new(var_id, first, first, LocationExpr::Reg(X0));
        let out_of_bounds = VarLocation::new(var_id, first, InstId(99), LocationExpr::Reg(X0));
        let provenance = ProvenanceMap::new();

        let ranges = [empty, out_of_bounds];
        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);
        let entries = adapter.location_list_entries_from_ranges(var_id, local(var_id), &ranges);

        assert!(entries.is_empty());
    }

    #[test]
    fn debug_provenance_rejects_unknown_register() {
        let (func, first, _second, ret) = test_func();
        let var_id = TrustIrVarId(7);
        let mut provenance = ProvenanceMap::new();
        provenance
            .declare_var(
                var_id,
                VarLocation::new(var_id, first, ret, LocationExpr::Reg(PReg::new(999))),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_constant_width_mismatch() {
        let (func, first, _second, ret) = test_func();
        let var_id = TrustIrVarId(7);
        let mut provenance = ProvenanceMap::new();
        provenance
            .declare_var(
                var_id,
                VarLocation::new(
                    var_id,
                    first,
                    ret,
                    LocationExpr::Const {
                        value: 42,
                        bit_width: 32,
                    },
                ),
            )
            .unwrap();

        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);

        assert!(adapter.location_list_entries(var_id).is_empty());
    }

    #[test]
    fn debug_provenance_rejects_overlapping_live_ranges() {
        let (func, first, second, ret) = test_func();
        let var_id = TrustIrVarId(7);
        let ranges = [
            VarLocation::new(var_id, first, ret, LocationExpr::Reg(X0)),
            VarLocation::new(var_id, second, ret, LocationExpr::Reg(X1)),
        ];
        let provenance = ProvenanceMap::new();
        let adapter = DebugProvenanceAdapter::new(&func, &provenance, &[], 12, [local(var_id)]);

        assert!(
            adapter
                .location_list_entries_from_ranges(var_id, local(var_id), &ranges)
                .is_empty()
        );
    }

    #[test]
    fn debug_provenance_local_shape_matches_debug_storage() {
        let var_id = TrustIrVarId(3);
        let debug_local = DebugLocalVariable {
            name: "tracked".to_string(),
            ty: DebugBaseType::U64,
            storage: DebugVariableStorage::ProvenanceVar(var_id),
            decl_line: 1,
        };
        let storage_var = match debug_local.storage {
            DebugVariableStorage::ProvenanceVar(var) => var,
            _ => panic!("test local should be provenance-backed"),
        };

        assert_eq!(local(storage_var).var_id, var_id);
    }
}
