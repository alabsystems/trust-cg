// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent AArch64 physical-register liveness for the allocation validator.
//!
//! The allocator reserves every instruction point at which a physical value is
//! live between its reaching definition and a sink read
//! (`physical_liveness::reserve`, reached through
//! `implicit_def_reservations`). The allocation validator's phys-reg
//! interference gate consumes that same reservation map, so a defect in the
//! shared routine would both mis-allocate and pass validation. This module is
//! the second, separately written implementation the validator compares
//! against:
//!
//! * **Its own alias model.** A location is keyed by `(register file, register
//!   number)` derived here from the AArch64 encoding bands (X/W share a GPR key;
//!   V/D/S/H/B share an FPR key). It does not call the allocator's overlap
//!   predicate, `trust_cg_ir::regs::regs_overlap` or `aliasing_pregs`.
//! * **Its own call model.** A call kills the AAPCS64 caller-saved locations
//!   (X0-X18, X30, V0-V7, V16-V31) from this module's table as well as every
//!   operand/implicit definition the instruction carries; a stale or truncated
//!   `implicit_defs` list cannot extend a value across a call here.
//! * **Its own solver.** A round-robin backward fixpoint over one 64-bit mask
//!   per block, instead of the allocator's per-representative worklist.
//!
//! The comparison is one-directional. A point that is live here must be
//! reserved for that location in the allocator's map. Extra reservations cost
//! registers but cannot clobber a value, so they are not reported. Because this
//! model kills at least as much as the allocator's and generates from exactly
//! the same sink reads (explicit physical uses plus implicit uses, in the
//! post-allocation operand roles), a correct reservation map always covers it.
//!
//! Scope: allocatable AArch64 registers only. SP/WSP/XZR/WZR (register number
//! 31), NZCV/FPCR/FPSR and x86 registers have no key and are not checked here;
//! none of them can be assigned to a virtual register.

use std::collections::{BTreeMap, BTreeSet};

use crate::machine_types::{InstId, PReg, RegAllocFunction, RegAllocOperand};

/// Independent location key: `0..=30` for X0-X30/W0-W30 and `32..=63` for
/// V0-V31 and their D/S/H/B views.
fn location_key(preg: PReg) -> Option<u32> {
    let encoding = u32::from(preg.encoding());
    match encoding {
        // X0-X30 and W0-W30. Encoding 31 (SP) and 63 (WSP) are excluded.
        0..=30 => Some(encoding),
        32..=62 => Some(encoding - 32),
        // V0-V31, D0-D31, S0-S31.
        64..=95 => Some(32 + encoding - 64),
        96..=127 => Some(32 + encoding - 96),
        128..=159 => Some(32 + encoding - 128),
        // H0-H31, B0-B31.
        165..=196 => Some(32 + encoding - 165),
        197..=228 => Some(32 + encoding - 197),
        // XZR/WZR, NZCV/FPCR/FPSR, x86 bands and anything unassigned.
        _ => None,
    }
}

fn location_mask(preg: PReg) -> u64 {
    location_key(preg).map_or(0, |key| 1u64 << key)
}

/// A representative register for diagnostics: `Xn` or `Vn`.
fn key_register(key: u32) -> PReg {
    if key < 32 {
        PReg::new(key as u16)
    } else {
        PReg::new((64 + key - 32) as u16)
    }
}

/// AAPCS64 locations a call does not preserve: X0-X18, X30 (written by BL/BLR),
/// V0-V7 and V16-V31. The low halves of V8-V15 are callee-saved; their upper
/// halves are volatile but a 64-bit liveness key cannot split them, so V8-V15
/// are not killed here (killing less only enlarges the required set, which the
/// allocator's map must then still cover).
const fn aapcs64_call_kill_mask() -> u64 {
    let mut mask = 0u64;
    let mut n = 0;
    while n <= 18 {
        mask |= 1u64 << n;
        n += 1;
    }
    mask |= 1u64 << 30;
    let mut v = 0;
    while v <= 31 {
        if v <= 7 || v >= 16 {
            mask |= 1u64 << (32 + v);
        }
        v += 1;
    }
    mask
}

const CALL_KILL_MASK: u64 = aapcs64_call_kill_mask();

struct Transfer {
    uses: u64,
    kills: u64,
}

fn transfer(func: &RegAllocFunction, inst_id: InstId) -> Option<Transfer> {
    let inst = func.insts.get(inst_id.0 as usize)?;
    let mut uses = 0u64;
    for preg in inst.uses.iter().filter_map(RegAllocOperand::as_preg) {
        uses |= location_mask(preg);
    }
    for &preg in &inst.implicit_uses {
        uses |= location_mask(preg);
    }
    let mut kills = 0u64;
    for preg in inst.defs.iter().filter_map(RegAllocOperand::as_preg) {
        kills |= location_mask(preg);
    }
    for &preg in &inst.implicit_defs {
        kills |= location_mask(preg);
    }
    if inst.flags.is_call() {
        kills |= CALL_KILL_MASK;
    }
    Some(Transfer { uses, kills })
}

/// One required-but-unreserved point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct UnreservedLivePoint {
    /// Representative register (`Xn`/`Vn`) of the live location.
    pub preg: PReg,
    /// Instruction position (in `numbering`) where the value is live.
    pub point: u32,
    /// The instruction at that position.
    pub inst: InstId,
}

/// Recompute physical liveness over `func` and return every live point that
/// `reserved` does not cover for the same location, at most one per location
/// (the earliest position), in location order.
pub(crate) fn unreserved_live_points(
    func: &RegAllocFunction,
    numbering: &BTreeMap<InstId, u32>,
    reserved: &BTreeMap<PReg, Vec<u32>>,
) -> Vec<UnreservedLivePoint> {
    let block_count = func.blocks.len();
    // Each listed block once, in first-listed order. Unlisted blocks keep an
    // empty live-in, matching the allocator's documented block contract.
    let mut listed = vec![false; block_count];
    let mut order = Vec::new();
    for block in &func.block_order {
        let index = block.0 as usize;
        if index < block_count && !listed[index] {
            listed[index] = true;
            order.push(index);
        }
    }

    let mut live_in = vec![0u64; block_count];
    let live_out = |live_in: &[u64], index: usize| -> u64 {
        func.blocks[index]
            .succs
            .iter()
            .map(|succ| succ.0 as usize)
            .filter(|&succ| succ < block_count && listed[succ])
            .fold(0u64, |acc, succ| acc | live_in[succ])
    };

    // Round-robin backward fixpoint: masks only grow, so this terminates after
    // at most 64 changes per block.
    loop {
        let mut changed = false;
        for &index in order.iter().rev() {
            let mut live = live_out(&live_in, index);
            for &inst_id in func.blocks[index].insts.iter().rev() {
                if let Some(t) = transfer(func, inst_id) {
                    live = (live & !t.kills) | t.uses;
                }
            }
            if live != live_in[index] {
                live_in[index] = live;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Reserved positions per independent location key.
    let mut covered: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
    for (&preg, points) in reserved {
        if let Some(key) = location_key(preg) {
            covered
                .entry(key)
                .or_default()
                .extend(points.iter().copied());
        }
    }

    let mut first_miss: BTreeMap<u32, UnreservedLivePoint> = BTreeMap::new();
    for &index in &order {
        let mut live = live_out(&live_in, index);
        for &inst_id in func.blocks[index].insts.iter().rev() {
            let Some(t) = transfer(func, inst_id) else {
                continue;
            };
            let after = live;
            let before = (live & !t.kills) | t.uses;
            if let Some(&point) = numbering.get(&inst_id) {
                let mut required = before | after;
                while required != 0 {
                    let key = required.trailing_zeros();
                    required &= required - 1;
                    let is_covered = covered
                        .get(&key)
                        .is_some_and(|points| points.contains(&point));
                    if !is_covered {
                        let miss = UnreservedLivePoint {
                            preg: key_register(key),
                            point,
                            inst: inst_id,
                        };
                        first_miss
                            .entry(key)
                            .and_modify(|existing| {
                                if point < existing.point {
                                    *existing = miss;
                                }
                            })
                            .or_insert(miss);
                    }
                }
            }
            live = before;
        }
    }
    first_miss.into_values().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine_types::{BlockId, InstFlags, RegAllocBlock, RegAllocInst};

    #[test]
    fn keys_follow_register_files_not_widths() {
        assert_eq!(location_key(PReg::new(0)), Some(0)); // X0
        assert_eq!(location_key(PReg::new(32)), Some(0)); // W0
        assert_eq!(location_key(PReg::new(30)), Some(30)); // X30
        assert_eq!(location_key(PReg::new(31)), None); // SP
        assert_eq!(location_key(PReg::new(63)), None); // WSP
        assert_eq!(location_key(PReg::new(160)), None); // XZR
        assert_eq!(location_key(PReg::new(72)), Some(40)); // V8
        assert_eq!(location_key(PReg::new(104)), Some(40)); // D8
        assert_eq!(location_key(PReg::new(136)), Some(40)); // S8
        assert_eq!(location_key(PReg::new(173)), Some(40)); // H8
        assert_eq!(location_key(PReg::new(205)), Some(40)); // B8
        assert_eq!(location_key(PReg::new(512)), None); // x86 band
    }

    #[test]
    fn call_kill_mask_is_the_aapcs64_volatile_set() {
        for n in 0..=30u32 {
            let expected = n <= 18 || n == 30;
            assert_eq!(CALL_KILL_MASK & (1 << n) != 0, expected, "X{n}");
        }
        for v in 0..=31u32 {
            let expected = v <= 7 || v >= 16;
            assert_eq!(CALL_KILL_MASK & (1 << (32 + v)) != 0, expected, "V{v}");
        }
    }

    fn inst(defs: &[u16], uses: &[u16], implicit_uses: &[u16], call: bool) -> RegAllocInst {
        RegAllocInst {
            opcode: 7,
            defs: defs
                .iter()
                .map(|&r| RegAllocOperand::PReg(PReg::new(r)))
                .collect(),
            uses: uses
                .iter()
                .map(|&r| RegAllocOperand::PReg(PReg::new(r)))
                .collect(),
            implicit_defs: Vec::new(),
            implicit_uses: implicit_uses.iter().map(|&r| PReg::new(r)).collect(),
            flags: if call {
                InstFlags::IS_CALL
            } else {
                InstFlags::default()
            },
            tied_operands: Vec::new(),
        }
    }

    fn two_blocks(body0: Vec<RegAllocInst>, body1: Vec<RegAllocInst>) -> RegAllocFunction {
        let split = body0.len();
        let mut insts = body0;
        insts.extend(body1);
        let total = insts.len();
        RegAllocFunction {
            name: "independent_liveness".into(),
            insts,
            blocks: vec![
                RegAllocBlock {
                    insts: (0..split).map(|i| InstId(i as u32)).collect(),
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                RegAllocBlock {
                    insts: (split..total).map(|i| InstId(i as u32)).collect(),
                    preds: vec![BlockId(0)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1)],
            entry_block: BlockId(0),
            next_vreg: 0,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    fn numbering(func: &RegAllocFunction) -> BTreeMap<InstId, u32> {
        (0..func.insts.len())
            .map(|i| (InstId(i as u32), i as u32 * 2))
            .collect()
    }

    #[test]
    fn cross_block_return_lane_requires_every_interior_point() {
        // b0: def X0; unrelated; b1: RET (implicit use W0 alias).
        let func = two_blocks(
            vec![inst(&[0], &[], &[], false), inst(&[9], &[], &[], false)],
            vec![inst(&[], &[], &[32], false)],
        );
        let numbering = numbering(&func);
        let full = BTreeMap::from([(PReg::new(0), vec![0, 2, 4])]);
        assert!(unreserved_live_points(&func, &numbering, &full).is_empty());
        let hole = BTreeMap::from([(PReg::new(32), vec![0, 4])]);
        assert_eq!(
            unreserved_live_points(&func, &numbering, &hole),
            vec![UnreservedLivePoint {
                preg: PReg::new(0),
                point: 2,
                inst: InstId(1),
            }]
        );
    }

    #[test]
    fn a_call_ends_a_caller_saved_value_even_without_implicit_defs() {
        // X9 is read after a call that carries no implicit defs: the value
        // read is the call's clobber, so the pre-call def is not live across.
        let func = two_blocks(
            vec![
                inst(&[9], &[], &[], false),
                inst(&[], &[], &[], true),
                inst(&[], &[9], &[], false),
            ],
            Vec::new(),
        );
        let numbering = numbering(&func);
        let reserved = BTreeMap::from([(PReg::new(9), vec![2, 4])]);
        assert!(unreserved_live_points(&func, &numbering, &reserved).is_empty());
    }

    #[test]
    fn callee_saved_value_is_required_across_a_call() {
        let func = two_blocks(
            vec![
                inst(&[19], &[], &[], false),
                inst(&[], &[], &[], true),
                inst(&[], &[19], &[], false),
            ],
            Vec::new(),
        );
        let numbering = numbering(&func);
        let reserved = BTreeMap::from([(PReg::new(19), vec![0, 4])]);
        let misses = unreserved_live_points(&func, &numbering, &reserved);
        assert_eq!(misses.len(), 1);
        assert_eq!(misses[0].point, 2);
    }
}
