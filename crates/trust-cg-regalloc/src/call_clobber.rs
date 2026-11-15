// trust-cg-regalloc/call_clobber.rs - Call-clobber handling for register allocation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Call-clobber handling for the register allocator.
//!
//! When a live interval spans a call instruction, the value must be preserved
//! across the call. There are two strategies:
//!
//! 1. **Assign to a callee-saved register.** The callee will save/restore it.
//!    This is free in terms of our codegen (the callee handles it), but uses
//!    a callee-saved register that may be scarce.
//!
//! 2. **Save/restore around the call.** Insert a store before the call and
//!    a load after it. This is like a targeted spill just for the call site.
//!
//! This module analyzes which intervals cross calls and adjusts their
//! allocation preferences accordingly.
//!
//! Reference: LLVM `RegAllocGreedy.cpp` — call-crossing interval handling.

use crate::AllocError;
use crate::liveness::LiveInterval;
use crate::machine_types::{
    InstFlags, InstId, MachFunction, MachInst, MachOperand, PReg, RegClass, VReg,
};
use crate::spill::{PSEUDO_SPILL_LOAD, PSEUDO_SPILL_STORE};
use std::collections::{BTreeMap, BTreeSet};

/// Information about a call instruction and the live values crossing it.
#[derive(Debug, Clone)]
pub struct CallCrossing {
    /// The instruction index (global numbering) of the call.
    pub call_inst_idx: u32,
    /// The InstId of the call instruction.
    pub call_inst_id: InstId,
    /// VRegs that are live across this call.
    pub live_across: Vec<VReg>,
}

/// AArch64 registers clobbered by a call.
///
/// `PReg` encodes register width, so include GPR/FPR aliases for every
/// volatile register class. This intentionally includes non-allocatable IP/LR
/// registers because the pipeline also uses this set as call implicit defs.
pub fn aarch64_caller_saved_regs() -> BTreeSet<PReg> {
    aarch64_saved_regs(false)
}

/// AArch64 callee-saved registers that regalloc may allocate.
///
/// The local model classifies V8-V15 by their preserved low 64 bits; Fpr128
/// allocation independently excludes those registers because their upper bits
/// are volatile. Include each scalar alias encoded by this allocator.
pub fn aarch64_callee_saved_regs() -> BTreeSet<PReg> {
    aarch64_saved_regs(true)
}

fn aarch64_saved_regs(callee: bool) -> BTreeSet<PReg> {
    let mut regs = BTreeSet::new();
    for index in 0u8..=30 {
        // FP is reserved in this allocator; the architectural model still
        // classifies it, but neither allocatable set includes its aliases.
        if index == 29 {
            continue;
        }
        let upper = crate::trust_cg_aarch64_gpr_before30(index, 1, 0);
        let flag = crate::trust_cg_aarch64_gpr_before19(index, 0, upper);
        if (flag == 1) == callee {
            for base in [0u16, 32] {
                regs.insert(PReg::new(base + u16::from(index)));
            }
        }
    }
    for index in 0u8..32 {
        let upper = crate::trust_cg_aarch64_fpr_before16(index, 1, 0);
        let flag = crate::trust_cg_aarch64_fpr_before8(index, 0, upper);
        if (flag == 1) == callee {
            // V/D/S/H encodings of the same architectural register.
            for base in [64u16, 96, 128, 165] {
                regs.insert(PReg::new(base + u16::from(index)));
            }
        }
    }
    regs
}

/// Find all call instructions and the VRegs live across them.
///
/// Returns a list of CallCrossing records, one per call instruction.
pub fn find_call_crossings(
    func: &MachFunction,
    intervals: &BTreeMap<u32, LiveInterval>,
    inst_numbering: &BTreeMap<InstId, u32>,
) -> Vec<CallCrossing> {
    find_call_crossings_in(func, intervals.values(), inst_numbering)
}

/// [`find_call_crossings`] over any interval sequence; the crossings' `live_across`
/// lists follow the sequence's order (the map version iterates ascending id).
pub fn find_call_crossings_in<'a>(
    func: &MachFunction,
    intervals: impl IntoIterator<Item = &'a LiveInterval> + Clone,
    inst_numbering: &BTreeMap<InstId, u32>,
) -> Vec<CallCrossing> {
    // Every numbered call, in block and instruction order: the order the
    // crossings are reported in.
    let mut calls: Vec<(u32, InstId)> = Vec::new();
    for block in &func.blocks {
        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];
            if !inst.flags.is_call() {
                continue;
            }
            if let Some(&call_idx) = inst_numbering.get(&inst_id) {
                calls.push((call_idx, inst_id));
            }
        }
    }
    if calls.is_empty() {
        return Vec::new();
    }

    // Call positions in ascending order, each with its report ordinal. Asking
    // every interval about every call is quadratic in a function's call count
    // (a straight-line block of `c` calls has `O(c)` intervals); walking each
    // interval's ranges over the sorted positions visits only the calls it is
    // live across. Pushing in interval order keeps each `live_across` list in
    // the sequence's order, exactly as the per-call scan built it.
    let mut positions: Vec<(u32, usize)> = calls
        .iter()
        .enumerate()
        .map(|(ordinal, &(call_idx, _))| (call_idx, ordinal))
        .collect();
    positions.sort_unstable();
    let call_points: Vec<u32> = positions.iter().map(|&(call_idx, _)| call_idx).collect();

    let mut live_across: Vec<Vec<VReg>> = vec![Vec::new(); calls.len()];
    for interval in intervals {
        if interval.has_ordered_ranges() {
            for range in &interval.ranges {
                let first = call_points.partition_point(|&pos| pos < range.start);
                crate::scan_work::charge(1);
                for &(call_idx, ordinal) in &positions[first..] {
                    crate::scan_work::charge(1);
                    if call_idx >= range.end {
                        break;
                    }
                    live_across[ordinal].push(interval.vreg);
                }
            }
        } else {
            // Outside the ranges invariant, keep the literal per-call question.
            for (ordinal, &(call_idx, _)) in calls.iter().enumerate() {
                if interval.is_live_at(call_idx) {
                    live_across[ordinal].push(interval.vreg);
                }
            }
        }
    }

    calls
        .into_iter()
        .zip(live_across)
        .filter(|(_, live_across)| !live_across.is_empty())
        .map(
            |((call_inst_idx, call_inst_id), live_across)| CallCrossing {
                call_inst_idx,
                call_inst_id,
                live_across,
            },
        )
        .collect()
}

/// Insert save/restore code around calls for VRegs assigned to caller-saved
/// registers.
///
/// For each call crossing:
/// 1. Check which live-across VRegs are assigned to caller-saved registers.
/// 2. For those VRegs, insert a store before the call and a load after.
///
/// Returns the number of save/restore pairs inserted. Slot-ID exhaustion
/// returns an error without changing instructions, counters, or slot metadata.
/// This public helper is not called by the current allocation pipeline, which
/// enforces call-clobber constraints through reservations and spill allocation.
pub fn insert_call_save_restore(
    func: &mut MachFunction,
    crossings: &[CallCrossing],
    allocation: &BTreeMap<VReg, PReg>,
    caller_saved: &BTreeSet<PReg>,
) -> Result<u32, AllocError> {
    let mut pairs_inserted = 0u32;
    let mut slots = func.stack_slot_allocation_plan();

    // Build a plan first, then apply (to avoid mutating while iterating).
    // Plan entry: (block_idx, inst_pos_in_block, saves_before, restores_after).
    let mut plans: Vec<(usize, usize, Vec<MachInst>, Vec<MachInst>)> = Vec::new();

    for crossing in crossings {
        // Find which block and position this call is in.
        for (block_idx, block) in func.blocks.iter().enumerate() {
            if let Some(pos) = block
                .insts
                .iter()
                .position(|&id| id == crossing.call_inst_id)
            {
                let mut saves = Vec::new();
                let mut restores = Vec::new();
                let mut seen_live_across = BTreeSet::new();

                for &vreg in &crossing.live_across {
                    if !seen_live_across.insert(vreg) {
                        continue;
                    }
                    if let Some(&preg) = allocation.get(&vreg)
                        && caller_saved.contains(&preg)
                    {
                        // Need to save before and restore after.
                        let size = vreg.class.size_bytes();
                        let slot = slots
                            .allocate(size, size)
                            .ok_or(AllocError::StackSlotExhausted)?;

                        // Store before call.
                        saves.push(MachInst {
                            opcode: PSEUDO_SPILL_STORE,
                            defs: vec![],
                            uses: vec![MachOperand::VReg(vreg), MachOperand::StackSlot(slot)],
                            implicit_defs: Vec::new(),
                            implicit_uses: Vec::new(),
                            flags: InstFlags::WRITES_MEMORY,
                            tied_operands: vec![],
                        });

                        // Load after call.
                        restores.push(MachInst {
                            opcode: PSEUDO_SPILL_LOAD,
                            defs: vec![MachOperand::VReg(vreg)],
                            uses: vec![MachOperand::StackSlot(slot)],
                            implicit_defs: Vec::new(),
                            implicit_uses: Vec::new(),
                            flags: InstFlags::READS_MEMORY,
                            tied_operands: vec![],
                        });

                        // Every pair consumes a distinct checked slot ID; the
                        // total cannot exceed the u32::MAX allocatable IDs.
                        pairs_inserted += 1;
                    }
                }

                if !saves.is_empty() || !restores.is_empty() {
                    plans.push((block_idx, pos, saves, restores));
                }
                break;
            }
        }
    }

    // Apply plans in reverse order to maintain position validity.
    plans.sort_by(|a, b| b.0.cmp(&a.0).then(b.1.cmp(&a.1)));

    slots.commit(func);
    for (block_idx, pos, saves, restores) in plans {
        let block = &mut func.blocks[block_idx];

        // Insert restores after the call.
        for (i, restore) in restores.into_iter().enumerate() {
            let restore_id = InstId(func.insts.len() as u32);
            func.insts.push(restore);
            block.insts.insert(pos + 1 + i, restore_id);
        }

        // Insert saves before the call.
        for save in saves.into_iter().rev() {
            let save_id = InstId(func.insts.len() as u32);
            func.insts.push(save);
            block.insts.insert(pos, save_id);
        }
    }

    Ok(pairs_inserted)
}

/// Compute register allocation hints for call-crossing intervals.
///
/// Returns a map from VReg to a preferred PReg. Call-crossing intervals
/// should prefer callee-saved registers to avoid save/restore overhead.
pub fn compute_call_crossing_hints(
    crossings: &[CallCrossing],
    callee_saved: &BTreeSet<PReg>,
    allocatable: &BTreeMap<RegClass, Vec<PReg>>,
) -> BTreeMap<VReg, Vec<PReg>> {
    let mut hints: BTreeMap<VReg, Vec<PReg>> = BTreeMap::new();

    // Collect all VRegs that cross at least one call.
    let mut call_crossing_vregs: BTreeSet<VReg> = BTreeSet::new();
    for crossing in crossings {
        for &vreg in &crossing.live_across {
            call_crossing_vregs.insert(vreg);
        }
    }

    // For each call-crossing VReg, prefer callee-saved registers.
    for vreg in call_crossing_vregs {
        if let Some(regs) = allocatable.get(&vreg.class) {
            let preferred: Vec<PReg> = regs
                .iter()
                .filter(|r| callee_saved.contains(r))
                .copied()
                .collect();
            if !preferred.is_empty() {
                hints.insert(vreg, preferred);
            }
        }
    }

    hints
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liveness::{LiveInterval, LiveRange};
    use crate::machine_types::{
        BlockId, InstFlags, InstId, MachBlock, MachFunction, MachInst, MachOperand, PReg, RegClass,
        StackSlotId, VReg,
    };
    use std::collections::BTreeMap;

    fn slot_boundary_call_function(next_stack_slot: u32) -> MachFunction {
        MachFunction {
            name: "slot_boundary_call".into(),
            insts: vec![MachInst {
                opcode: 0xCA,
                defs: vec![],
                uses: vec![],
                implicit_defs: vec![],
                implicit_uses: vec![],
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            }],
            blocks: vec![MachBlock {
                insts: vec![InstId(0)],
                preds: vec![],
                succs: vec![],
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot,
            stack_slots: BTreeMap::new(),
        }
    }

    #[test]
    fn slot_boundary_call_save_exhaustion_preserves_function() {
        let mut func = slot_boundary_call_function(u32::MAX - 1);
        let before = format!("{func:?}");
        let crossings = [CallCrossing {
            call_inst_idx: 0,
            call_inst_id: InstId(0),
            live_across: vec![vreg(0), vreg(1)],
        }];
        let allocation = BTreeMap::from([(vreg(0), PReg::new(0)), (vreg(1), PReg::new(1))]);
        assert!(matches!(
            insert_call_save_restore(
                &mut func,
                &crossings,
                &allocation,
                &aarch64_caller_saved_regs()
            ),
            Err(AllocError::StackSlotExhausted)
        ));
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn slot_boundary_call_save_does_not_overwrite_existing_slot() {
        let mut func = slot_boundary_call_function(0);
        func.stack_slots.insert(
            StackSlotId(0),
            crate::machine_types::RegAllocStackSlot::new(32, 32),
        );
        let original_slot = format!("{:?}", func.stack_slots[&StackSlotId(0)]);
        let crossings = [CallCrossing {
            call_inst_idx: 0,
            call_inst_id: InstId(0),
            live_across: vec![vreg(0)],
        }];
        let allocation = BTreeMap::from([(vreg(0), PReg::new(0))]);
        insert_call_save_restore(
            &mut func,
            &crossings,
            &allocation,
            &aarch64_caller_saved_regs(),
        )
        .unwrap();
        assert_eq!(
            format!("{:?}", func.stack_slots[&StackSlotId(0)]),
            original_slot
        );
        assert_eq!(func.stack_slots.len(), 2);
    }

    #[test]
    fn slot_boundary_call_save_last_slot_emits_matching_pair() {
        let mut func = slot_boundary_call_function(u32::MAX - 1);
        let crossings = [CallCrossing {
            call_inst_idx: 0,
            call_inst_id: InstId(0),
            live_across: vec![vreg(0), vreg(0)],
        }];
        let allocation = BTreeMap::from([(vreg(0), PReg::new(0))]);
        assert_eq!(
            insert_call_save_restore(
                &mut func,
                &crossings,
                &allocation,
                &aarch64_caller_saved_regs()
            )
            .unwrap(),
            1
        );
        assert_eq!(func.next_stack_slot, u32::MAX);
        let slot = StackSlotId(u32::MAX - 1);
        let insts: Vec<_> = func.blocks[0]
            .insts
            .iter()
            .map(|id| &func.insts[id.0 as usize])
            .collect();
        assert_eq!(
            insts.iter().map(|inst| inst.opcode).collect::<Vec<_>>(),
            [PSEUDO_SPILL_STORE, 0xCA, PSEUDO_SPILL_LOAD]
        );
        assert_eq!(
            insts[0].uses,
            [MachOperand::VReg(vreg(0)), MachOperand::StackSlot(slot)]
        );
        assert_eq!(insts[2].defs, [MachOperand::VReg(vreg(0))]);
        assert_eq!(insts[2].uses, [MachOperand::StackSlot(slot)]);
        assert_eq!(func.stack_slots[&slot].size, 8);
    }

    #[test]
    fn slot_boundary_later_call_exhaustion_discards_earlier_plan() {
        let mut func = slot_boundary_call_function(u32::MAX - 1);
        func.insts.push(func.insts[0].clone());
        func.blocks[0].insts.push(InstId(1));
        let before = format!("{func:?}");
        let crossings = [
            CallCrossing {
                call_inst_idx: 0,
                call_inst_id: InstId(0),
                live_across: vec![vreg(0)],
            },
            CallCrossing {
                call_inst_idx: 1,
                call_inst_id: InstId(1),
                live_across: vec![vreg(0)],
            },
        ];
        let allocation = BTreeMap::from([(vreg(0), PReg::new(0))]);
        assert!(matches!(
            insert_call_save_restore(
                &mut func,
                &crossings,
                &allocation,
                &aarch64_caller_saved_regs()
            ),
            Err(AllocError::StackSlotExhausted)
        ));
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn slot_boundary_no_call_saves_succeeds_at_capacity() {
        let mut func = slot_boundary_call_function(u32::MAX);
        let before = format!("{func:?}");
        let crossings = [CallCrossing {
            call_inst_idx: 0,
            call_inst_id: InstId(0),
            live_across: vec![vreg(0), vreg(1)],
        }];
        // v0 is callee-saved; v1 has no physical assignment (spilled).
        let allocation = BTreeMap::from([(vreg(0), PReg::new(19))]);
        assert_eq!(
            insert_call_save_restore(
                &mut func,
                &crossings,
                &allocation,
                &aarch64_caller_saved_regs()
            )
            .unwrap(),
            0
        );
        assert_eq!(
            insert_call_save_restore(&mut func, &[], &allocation, &aarch64_caller_saved_regs())
                .unwrap(),
            0
        );
        assert_eq!(format!("{func:?}"), before);
    }

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    fn fpr16_vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Fpr16,
        }
    }

    fn interval_at(id: u32, start: u32, end: u32) -> LiveInterval {
        let mut iv = LiveInterval::new(vreg(id));
        iv.add_range(start, end);
        iv
    }

    #[test]
    fn test_aarch64_caller_saved() {
        let cs = aarch64_caller_saved_regs();
        assert!(cs.contains(&PReg::new(0))); // X0
        assert!(cs.contains(&PReg::new(15))); // X15
        assert!(!cs.contains(&PReg::new(19))); // X19 is callee-saved
        assert!(cs.contains(&PReg::new(32))); // W0
        assert!(cs.contains(&PReg::new(47))); // W15
        assert!(!cs.contains(&PReg::new(51))); // W19 is callee-saved
        assert!(cs.contains(&PReg::new(64))); // V0
        assert!(cs.contains(&PReg::new(71))); // V7
        assert!(cs.contains(&PReg::new(80))); // V16
        assert!(!cs.contains(&PReg::new(72))); // V8 is callee-saved
        assert!(cs.contains(&PReg::new(96))); // D0
        assert!(cs.contains(&PReg::new(112))); // D16
        assert!(!cs.contains(&PReg::new(104))); // D8 is callee-saved
        assert!(cs.contains(&PReg::new(128))); // S0
        assert!(cs.contains(&PReg::new(144))); // S16
        assert!(!cs.contains(&PReg::new(136))); // S8 is callee-saved
        assert!(cs.contains(&PReg::new(165))); // H0
        assert!(cs.contains(&PReg::new(172))); // H7
        assert!(cs.contains(&PReg::new(181))); // H16
        assert!(cs.contains(&PReg::new(196))); // H31
        assert!(!cs.contains(&PReg::new(173))); // H8 is callee-saved
    }

    #[test]
    fn test_aarch64_callee_saved() {
        let cs = aarch64_callee_saved_regs();
        assert!(!cs.contains(&PReg::new(0))); // X0 is caller-saved
        assert!(cs.contains(&PReg::new(19))); // X19
        assert!(cs.contains(&PReg::new(28))); // X28
        assert!(!cs.contains(&PReg::new(32))); // W0 is caller-saved
        assert!(cs.contains(&PReg::new(51))); // W19
        assert!(cs.contains(&PReg::new(60))); // W28
        assert!(cs.contains(&PReg::new(72))); // V8
        assert!(cs.contains(&PReg::new(79))); // V15
        assert!(cs.contains(&PReg::new(104))); // D8
        assert!(cs.contains(&PReg::new(111))); // D15
        assert!(cs.contains(&PReg::new(136))); // S8
        assert!(cs.contains(&PReg::new(143))); // S15
        assert!(cs.contains(&PReg::new(173))); // H8
        assert!(cs.contains(&PReg::new(180))); // H15
        assert!(!cs.contains(&PReg::new(165))); // H0 is caller-saved
        assert!(!cs.contains(&PReg::new(181))); // H16 is caller-saved
    }

    #[test]
    fn test_find_call_crossings() {
        // Build a simple function: define v0, call, use v0.
        let insts = vec![
            // inst 0: def v0
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // inst 1: CALL
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            },
            // inst 2: use v0
            MachInst {
                opcode: 3,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];

        let inst_ids: Vec<InstId> = (0..3).map(InstId).collect();
        let func = MachFunction {
            name: "test".into(),
            insts,
            blocks: vec![MachBlock {
                insts: inst_ids.clone(),
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let numbering: BTreeMap<InstId, u32> = inst_ids
            .iter()
            .enumerate()
            .map(|(i, &id)| (id, i as u32))
            .collect();

        // v0 is live [0, 3) — spans the call at index 1.
        let intervals = BTreeMap::from([(0u32, interval_at(0, 0, 3))]);

        let crossings = find_call_crossings(&func, &intervals, &numbering);
        assert_eq!(crossings.len(), 1);
        assert_eq!(crossings[0].live_across.len(), 1);
        assert_eq!(crossings[0].live_across[0], vreg(0));
    }

    #[test]
    fn test_compute_call_crossing_hints() {
        let crossings = vec![CallCrossing {
            call_inst_idx: 5,
            call_inst_id: InstId(5),
            live_across: vec![vreg(0)],
        }];

        let callee_saved = aarch64_callee_saved_regs();
        let mut allocatable = BTreeMap::new();
        let gpr: Vec<PReg> = (0u16..=15).chain(19u16..=28).map(PReg::new).collect();
        allocatable.insert(RegClass::Gpr64, gpr);

        let hints = compute_call_crossing_hints(&crossings, &callee_saved, &allocatable);
        assert!(hints.contains_key(&vreg(0)));
        let prefs = &hints[&vreg(0)];
        // All preferred registers should be callee-saved (X19-X28).
        for &preg in prefs {
            assert!(
                callee_saved.contains(&preg),
                "{:?} is not callee-saved",
                preg
            );
        }
    }

    /// SOUNDNESS (Finding #2, AArch64 v8-v15 partial-preserve gap): AAPCS64
    /// preserves only the LOWER 64 bits of V8-V15; the upper 64 are
    /// caller-clobbered and the frame save stores only the lower 64 (D8..D15).
    /// So a 128-bit value placed in V8-V15 and live across a call loses its
    /// upper 64 bits. After dropping V8-V15 from the Fpr128 allocatable pool,
    /// the call-crossing-hint path must yield NO callee-saved Fpr128 candidate
    /// (V8-V15 are gone) — so a call-crossing Fpr128 vreg is never steered into
    /// a partially-preserved register and instead falls to the full-width
    /// (16-byte) save/restore path on a caller-saved V0-V7/V16-V31 register.
    #[test]
    fn fpr128_call_crossing_never_hinted_to_v8_v15() {
        use crate::linear_scan::aarch64_allocatable_regs;

        let v128 = VReg {
            id: 0,
            class: RegClass::Fpr128,
        };
        let crossings = vec![CallCrossing {
            call_inst_idx: 5,
            call_inst_id: InstId(5),
            live_across: vec![v128],
        }];

        let callee_saved = aarch64_callee_saved_regs();
        let allocatable = aarch64_allocatable_regs();

        // The Fpr128 pool must contain none of V8-V15 (enc 72-79).
        for enc in 72u16..=79 {
            assert!(
                !allocatable[&RegClass::Fpr128].contains(&PReg::new(enc)),
                "V{} (enc {enc}) must not be Fpr128-allocatable",
                enc - 64
            );
        }

        let hints = compute_call_crossing_hints(&crossings, &callee_saved, &allocatable);
        // No Fpr128 candidate is both allocatable AND callee-saved, so there is
        // NO hint for the call-crossing Fpr128 vreg. It cannot be steered into
        // V8-V15.
        assert!(
            !hints.contains_key(&v128),
            "call-crossing Fpr128 must get no callee-saved hint (V8-V15 are excluded)"
        );

        // And the full 128-bit value is preserved by the around-call save path:
        // an Fpr128 spill/save slot is 16 bytes (the full Q register).
        assert_eq!(
            RegClass::Fpr128.size_bytes(),
            16,
            "Fpr128 around-call save must cover the full 128 bits"
        );
    }

    // -----------------------------------------------------------------------
    // Additional edge-case and correctness tests (issue #139)
    // -----------------------------------------------------------------------

    #[test]
    fn test_caller_callee_sets_disjoint() {
        let caller = aarch64_caller_saved_regs();
        let callee = aarch64_callee_saved_regs();
        // Caller-saved and callee-saved should be completely disjoint.
        for reg in &caller {
            assert!(
                !callee.contains(reg),
                "{:?} is in both caller-saved and callee-saved sets",
                reg
            );
        }
    }

    #[test]
    fn test_caller_saved_count() {
        let cs = aarch64_caller_saved_regs();
        // X/W0-X/W18 plus X/W30 = 40 GPR aliases.
        // V/D/S/H 0-7 and 16-31 = 96 FPR aliases. Total: 136.
        assert_eq!(
            cs.len(),
            136,
            "expected 136 caller-saved regs, got {}",
            cs.len()
        );
    }

    #[test]
    fn test_callee_saved_count() {
        let cs = aarch64_callee_saved_regs();
        // X/W19-X/W28 = 20 GPR aliases; V/D/S/H8-V/D/S/H15 = 32 FPR aliases.
        assert_eq!(
            cs.len(),
            52,
            "expected 52 callee-saved regs, got {}",
            cs.len()
        );
    }

    #[test]
    fn test_find_call_crossings_no_calls() {
        // Function with no call instructions should produce no crossings.
        let insts = vec![MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }];
        let func = MachFunction {
            name: "no_call".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let numbering = BTreeMap::from([(InstId(0), 0u32)]);
        let intervals = BTreeMap::from([(0u32, interval_at(0, 0, 1))]);
        let crossings = find_call_crossings(&func, &intervals, &numbering);
        assert!(crossings.is_empty());
    }

    #[test]
    fn test_find_call_crossings_no_live_across() {
        // A call with no live values across it should produce no crossings.
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // use v0 (v0 dies before call)
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // call (v0 is dead here)
            MachInst {
                opcode: 3,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            },
        ];
        let func = MachFunction {
            name: "dead_before_call".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let numbering: BTreeMap<InstId, u32> = (0..3).map(|i| (InstId(i), i)).collect();
        // v0 live [0, 2) — dies before call at index 2.
        let intervals = BTreeMap::from([(0u32, interval_at(0, 0, 2))]);
        let crossings = find_call_crossings(&func, &intervals, &numbering);
        assert!(crossings.is_empty(), "no values live across the call");
    }

    #[test]
    fn test_find_call_crossings_multiple_vregs() {
        // Two VRegs live across a call.
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(1))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 0xCA,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0)), MachOperand::VReg(vreg(1))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];
        let func = MachFunction {
            name: "multi_live".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2), InstId(3)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let numbering: BTreeMap<InstId, u32> = (0..4).map(|i| (InstId(i), i)).collect();
        let intervals =
            BTreeMap::from([(0u32, interval_at(0, 0, 4)), (1u32, interval_at(1, 1, 4))]);
        let crossings = find_call_crossings(&func, &intervals, &numbering);
        assert_eq!(crossings.len(), 1);
        assert_eq!(crossings[0].live_across.len(), 2);
    }

    #[test]
    fn test_insert_call_save_restore_callee_saved_skipped() {
        // A VReg assigned to a callee-saved register should NOT get save/restore.
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 0xCA,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];

        let mut func = MachFunction {
            name: "callee_saved_alloc".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let crossings = vec![CallCrossing {
            call_inst_idx: 1,
            call_inst_id: InstId(1),
            live_across: vec![vreg(0)],
        }];

        // v0 is allocated to X19 (callee-saved).
        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(0), PReg::new(19));

        let caller_saved = aarch64_caller_saved_regs();
        let pairs =
            insert_call_save_restore(&mut func, &crossings, &allocation, &caller_saved).unwrap();

        assert_eq!(
            pairs, 0,
            "callee-saved register should not need save/restore"
        );
    }

    #[test]
    fn test_insert_call_save_restore_caller_saved_needs_save() {
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 0xCA,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];

        let mut func = MachFunction {
            name: "caller_saved_alloc".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let crossings = vec![CallCrossing {
            call_inst_idx: 1,
            call_inst_id: InstId(1),
            live_across: vec![vreg(0)],
        }];

        // v0 is allocated to X0 (caller-saved).
        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(0), PReg::new(0));

        let caller_saved = aarch64_caller_saved_regs();
        let pairs =
            insert_call_save_restore(&mut func, &crossings, &allocation, &caller_saved).unwrap();

        assert_eq!(pairs, 1, "caller-saved register needs save/restore");

        // Verify a store and load were inserted.
        let block = &func.blocks[0];
        let has_store = block
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == crate::spill::PSEUDO_SPILL_STORE);
        let has_load = block
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == crate::spill::PSEUDO_SPILL_LOAD);
        assert!(has_store, "should insert store before call");
        assert!(has_load, "should insert load after call");
    }

    #[test]
    fn test_insert_call_save_restore_deduplicates_live_across_vregs() {
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 0xCA,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];

        let mut func = MachFunction {
            name: "duplicate_live_across".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let crossings = vec![CallCrossing {
            call_inst_idx: 1,
            call_inst_id: InstId(1),
            live_across: vec![vreg(0), vreg(0), vreg(0)],
        }];

        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(0), PReg::new(0));

        let caller_saved = aarch64_caller_saved_regs();
        let pairs =
            insert_call_save_restore(&mut func, &crossings, &allocation, &caller_saved).unwrap();

        assert_eq!(pairs, 1, "duplicate live-across entries share one pair");
        assert_eq!(func.stack_slots.len(), 1, "one temporary stack slot");

        let block = &func.blocks[0];
        let stores = block
            .insts
            .iter()
            .filter(|&&id| func.insts[id.0 as usize].opcode == crate::spill::PSEUDO_SPILL_STORE)
            .count();
        let loads = block
            .insts
            .iter()
            .filter(|&&id| func.insts[id.0 as usize].opcode == crate::spill::PSEUDO_SPILL_LOAD)
            .count();

        assert_eq!(stores, 1, "one store before the call");
        assert_eq!(loads, 1, "one load after the call");
    }

    #[test]
    fn test_insert_call_save_restore_fpr16_caller_saved_h_reg() {
        let v0 = fpr16_vreg(0);
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(v0)],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 0xCA,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(v0)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];

        let mut func = MachFunction {
            name: "fpr16_caller_saved_alloc".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let crossings = vec![CallCrossing {
            call_inst_idx: 1,
            call_inst_id: InstId(1),
            live_across: vec![v0],
        }];

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(165)); // H0 is caller-saved.

        let caller_saved = aarch64_caller_saved_regs();
        let pairs =
            insert_call_save_restore(&mut func, &crossings, &allocation, &caller_saved).unwrap();

        assert_eq!(pairs, 1, "caller-saved H register needs save/restore");
        let slot = func
            .stack_slots
            .values()
            .next()
            .expect("Fpr16 save/restore should allocate one stack slot");
        assert_eq!(slot.size, 2);
        assert_eq!(slot.align, 2);

        let block = &func.blocks[0];
        let store = block
            .insts
            .iter()
            .map(|&id| &func.insts[id.0 as usize])
            .find(|inst| inst.opcode == crate::spill::PSEUDO_SPILL_STORE)
            .expect("should insert store before call");
        let load = block
            .insts
            .iter()
            .map(|&id| &func.insts[id.0 as usize])
            .find(|inst| inst.opcode == crate::spill::PSEUDO_SPILL_LOAD)
            .expect("should insert load after call");
        assert_eq!(store.uses[0], MachOperand::VReg(v0));
        assert_eq!(load.defs[0], MachOperand::VReg(v0));
    }

    #[test]
    fn test_compute_call_crossing_hints_prefers_fpr16_callee_saved_h_regs() {
        let v0 = fpr16_vreg(0);
        let crossings = vec![CallCrossing {
            call_inst_idx: 5,
            call_inst_id: InstId(5),
            live_across: vec![v0],
        }];

        let callee_saved = aarch64_callee_saved_regs();
        let mut allocatable = BTreeMap::new();
        let hregs: Vec<PReg> = (165u16..=180).map(PReg::new).collect();
        allocatable.insert(RegClass::Fpr16, hregs);

        let hints = compute_call_crossing_hints(&crossings, &callee_saved, &allocatable);
        let prefs = hints
            .get(&v0)
            .expect("Fpr16 live-across-call value should get callee-saved hints");
        let expected: Vec<PReg> = (173u16..=180).map(PReg::new).collect();
        assert_eq!(prefs, &expected);
    }

    #[test]
    fn test_compute_hints_no_crossings() {
        let crossings: Vec<CallCrossing> = Vec::new();
        let callee_saved = aarch64_callee_saved_regs();
        let allocatable = BTreeMap::new();
        let hints = compute_call_crossing_hints(&crossings, &callee_saved, &allocatable);
        assert!(hints.is_empty());
    }

    #[test]
    fn test_compute_hints_deduplicates_vregs() {
        // Same vreg crossing multiple calls should only get one hint entry.
        let crossings = vec![
            CallCrossing {
                call_inst_idx: 5,
                call_inst_id: InstId(5),
                live_across: vec![vreg(0)],
            },
            CallCrossing {
                call_inst_idx: 10,
                call_inst_id: InstId(10),
                live_across: vec![vreg(0)],
            },
        ];

        let callee_saved = aarch64_callee_saved_regs();
        let mut allocatable = BTreeMap::new();
        let gpr: Vec<PReg> = (0u16..=15).chain(19u16..=28).map(PReg::new).collect();
        allocatable.insert(RegClass::Gpr64, gpr);

        let hints = compute_call_crossing_hints(&crossings, &callee_saved, &allocatable);
        assert_eq!(hints.len(), 1, "should have one hint entry for v0");
    }
    /// The per-call scan `find_call_crossings_in` used before it walked
    /// interval ranges over sorted call positions: the differential oracle.
    fn find_call_crossings_reference<'a>(
        func: &MachFunction,
        intervals: impl IntoIterator<Item = &'a LiveInterval> + Clone,
        inst_numbering: &BTreeMap<InstId, u32>,
    ) -> Vec<(u32, InstId, Vec<VReg>)> {
        let mut crossings = Vec::new();
        for block in &func.blocks {
            for &inst_id in &block.insts {
                let inst = &func.insts[inst_id.0 as usize];
                if !inst.flags.is_call() {
                    continue;
                }
                let Some(&call_idx) = inst_numbering.get(&inst_id) else {
                    continue;
                };
                let live_across: Vec<VReg> = intervals
                    .clone()
                    .into_iter()
                    .filter(|interval| interval.is_live_at(call_idx))
                    .map(|interval| interval.vreg)
                    .collect();
                if !live_across.is_empty() {
                    crossings.push((call_idx, inst_id, live_across));
                }
            }
        }
        crossings
    }

    #[test]
    fn find_call_crossings_matches_per_call_scan() {
        let mut state = 0x2b7e_1516_28ae_d2a6u64;
        let mut next = move |limit: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) % limit
        };
        let mut crossings_seen = 0usize;
        let mut discriminating = 0usize;
        for case in 0..300 {
            let inst_count = 1 + next(120) as usize;
            let insts: Vec<MachInst> = (0..inst_count)
                .map(|_| MachInst {
                    opcode: 1,
                    defs: vec![],
                    uses: vec![],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: if next(3) == 0 {
                        InstFlags::IS_CALL
                    } else {
                        InstFlags::default()
                    },
                    tied_operands: vec![],
                })
                .collect();
            // Two blocks, the second listed first in `blocks`, so report order
            // (block list order) differs from numbering order.
            let split = inst_count / 2;
            let first: Vec<InstId> = (0..split as u32).map(InstId).collect();
            let second: Vec<InstId> = (split as u32..inst_count as u32).map(InstId).collect();
            let block = |insts: Vec<InstId>| MachBlock {
                insts,
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            };
            let func = MachFunction {
                name: "crossings".into(),
                insts,
                blocks: vec![block(second), block(first)],
                block_order: vec![BlockId(1), BlockId(0)],
                entry_block: BlockId(1),
                next_vreg: 0,
                next_stack_slot: 0,
                stack_slots: BTreeMap::new(),
            };
            // Leave some instructions unnumbered.
            let numbering: BTreeMap<InstId, u32> = (0..inst_count as u32)
                .filter(|_| next(10) != 0)
                .map(|i| (InstId(i), i))
                .collect();

            let mut intervals: Vec<LiveInterval> = (0..next(40) as u32)
                .map(|id| {
                    let mut interval = LiveInterval::new(vreg(id));
                    for _ in 0..1 + next(4) {
                        let start = next(inst_count as u64 + 4) as u32;
                        interval.add_range(start, start + 1 + next(30) as u32);
                    }
                    interval
                })
                .collect();
            if case % 5 == 0 {
                // Ranges outside the invariant take the literal fallback.
                let mut unordered = LiveInterval::new(vreg(1000));
                unordered.ranges = vec![LiveRange::new(40, 60), LiveRange::new(2, 30)];
                intervals.push(unordered);
            }

            let (fast, units) = crate::scan_work::measure(|| {
                find_call_crossings_in(&func, &intervals, &numbering)
                    .into_iter()
                    .map(|c| (c.call_inst_idx, c.call_inst_id, c.live_across))
                    .collect::<Vec<(u32, InstId, Vec<VReg>)>>()
            });
            let reference = find_call_crossings_reference(&func, &intervals, &numbering);
            assert_eq!(fast, reference, "call crossings differ in case {case}");
            crossings_seen += fast.len();

            // Work accounting: an ordered interval costs one search per range,
            // one unit per call it is live across and at most one past each
            // range's end; an unordered one keeps the per-call `is_live_at`.
            // The per-call scan charges `intervals * calls`, so every case
            // where that exceeds the bound tells the two apart.
            let calls = numbering
                .keys()
                .filter(|id| func.insts[id.0 as usize].flags.is_call())
                .count() as u64;
            let pushes: u64 = fast.iter().map(|(_, _, live)| live.len() as u64).sum();
            let bound: u64 = pushes
                + intervals
                    .iter()
                    .map(|interval| {
                        if interval.has_ordered_ranges() {
                            2 * interval.ranges.len() as u64
                        } else {
                            calls
                        }
                    })
                    .sum::<u64>();
            assert!(
                units <= bound,
                "case {case}: {units} units charged, range walk bound {bound}"
            );
            if intervals.len() as u64 * calls > bound {
                discriminating += 1;
            }
        }
        assert!(
            crossings_seen > 1000,
            "crossings exercised: {crossings_seen}"
        );
        assert!(
            discriminating > 100,
            "cases where the per-call scan exceeds the bound: {discriminating}"
        );
    }

    /// One straight-line block of `c` calls, each value live across one call:
    /// the range walk visits `O(c)` (interval, call) pairs. The per-call scan
    /// asks every interval about every call, `O(c^2)`, and fails this bound
    /// (see `crate::scan_work`).
    #[test]
    fn find_call_crossings_cost_grows_linearly() {
        crate::scan_work::assert_near_linear("find_call_crossings_in", 128, |calls| {
            let insts: Vec<MachInst> = (0..2 * calls)
                .map(|idx| MachInst {
                    opcode: 1,
                    defs: vec![],
                    uses: vec![],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: if idx % 2 == 1 {
                        InstFlags::IS_CALL
                    } else {
                        InstFlags::default()
                    },
                    tied_operands: vec![],
                })
                .collect();
            let func = MachFunction {
                name: "call_block".into(),
                blocks: vec![MachBlock {
                    insts: (0..insts.len() as u32).map(InstId).collect(),
                    preds: Vec::new(),
                    succs: Vec::new(),
                    loop_depth: 0,
                }],
                insts,
                block_order: vec![BlockId(0)],
                entry_block: BlockId(0),
                next_vreg: 0,
                next_stack_slot: 0,
                stack_slots: BTreeMap::new(),
            };
            let numbering: BTreeMap<InstId, u32> =
                (0..2 * calls as u32).map(|i| (InstId(i), i)).collect();
            // Value `i` is defined before call `i` and dies before call `i + 1`.
            let intervals: Vec<LiveInterval> = (0..calls as u32)
                .map(|i| {
                    let mut interval = LiveInterval::new(vreg(i));
                    interval.add_range(2 * i, 2 * i + 3);
                    interval
                })
                .collect();
            let (crossings, units) =
                crate::scan_work::measure(|| find_call_crossings_in(&func, &intervals, &numbering));
            assert_eq!(crossings.len(), calls);
            units
        });
    }
}
