// trust-cg-verify/post_ra_spill_slots/legacy.rs - frameless SP-invariant slot rule
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The original SP-only reaching-store rule, retained unchanged for the
//! functions it could model: a stream with no call, no SP modification or
//! escape, no X29-based access and only plain scalar SP-relative accesses.
//! For every tracked scalar load of a constant SP offset that the body stores
//! somewhere, a store to that offset must reach the load on every path.
//!
//! It applies to every tracked load, flagged or not, so it keeps covering
//! unflagged SP-relative slots in the frameless shape it always modeled. When
//! the frame model in the parent module analyzed the same stream, loads stamped
//! [`InstFlags::SPILL_SLOT_ACCESS`](trust_cg_ir::InstFlags) are skipped here
//! because that model checks them with a stronger rule (any byte not
//! spill-stored on every path is a violation). When the frame model declined,
//! this rule still checks them, so a decline never removes the coverage this
//! rule had before the frame model existed.

use std::collections::HashMap;
use std::collections::VecDeque;

use trust_cg_ir::aarch64_regs::{SP, X29};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, SpecialReg};

/// One reload with no reaching store: `(block, instruction position, opcode, SP offset)`.
pub(super) type LegacyViolation = (u32, usize, AArch64Opcode, i64);

/// Maximum number of distinct tracked spill-slot offsets (bitset width). A
/// function with more distinct SP-store offsets than this DECLINES — fail-safe,
/// and mirrors the fixed 64-location bound of the reaching-def slice.
const MAX_TRACKED_SLOTS: usize = 64;

// ---------------------------------------------------------------------------
// Access model: classify each instruction's relationship to SP-relative memory
// ---------------------------------------------------------------------------

/// Opcodes that STORE a single scalar register at a constant `[base,#imm]`
/// offset — the only store forms whose SP-relative slot this slice tracks.
fn is_tracked_store_opcode(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        StrRI | StrbRI | StrhRI | STRWui | STRXui | STRSui | STRDui
    )
}

/// Opcodes that LOAD a single scalar register from a constant `[base,#imm]`
/// offset — the only reload forms this slice read-checks.
fn is_tracked_load_opcode(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(op, LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI)
}

/// How one instruction relates to tracked SP-relative memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SlotAccess {
    /// No SP-relative memory access we care about.
    None,
    /// A tracked store to `[SP,#offset]` (a gen).
    Store(i64),
    /// A tracked reload from `[SP,#offset]` (a read to check).
    Load(i64),
    /// Touches SP-relative (or FP-relative) memory in a form we cannot soundly
    /// model — the whole function must DECLINE.
    Decline,
}

/// Classify `inst`'s SP-relative memory access. Any FP/X29-relative access, or
/// any SP-relative access through a non-plain-scalar form (pair / register-offset
/// / writeback / atomic), yields [`SlotAccess::Decline`].
fn classify_slot_access(inst: &MachInst) -> SlotAccess {
    let mut sp_offset: Option<i64> = None;
    for operand in &inst.operands {
        if let MachOperand::MemOp { base, offset } = operand {
            if *base == X29 {
                // FP-relative addressing => this is a frame-pointer frame whose
                // spills are FP-relative; out of scope for the SP-only slice.
                return SlotAccess::Decline;
            }
            if *base == SP {
                // A single plain MemOp per access is expected; a second SP MemOp
                // on one instruction is an unmodeled shape.
                if sp_offset.is_some() {
                    return SlotAccess::Decline;
                }
                sp_offset = Some(*offset);
            }
        }
    }
    let Some(off) = sp_offset else {
        return SlotAccess::None;
    };
    let op = inst.opcode;
    // A tracked store writes memory and only writes it (excludes LSE atomics,
    // which both read and write the slot).
    if is_tracked_store_opcode(op) && inst.writes_memory() && !inst.reads_memory() {
        return SlotAccess::Store(off);
    }
    if is_tracked_load_opcode(op) && inst.reads_memory() && !inst.writes_memory() {
        return SlotAccess::Load(off);
    }
    // SP-relative memory access through a form we do not model (pair, register-
    // offset, writeback, atomic, ...): fail safe.
    SlotAccess::Decline
}

/// Whether SP is used in a way that makes SP-relative slot identity unsound:
/// SP modified, SP escaping into a GPR (frame-address materialization), a split
/// `Special(SP)` addressing/ALU form, SP in `implicit_defs`, or a call. The ONLY
/// sound appearance of SP is as the `base` of a plain `MemOp` (a distinct operand
/// variant, so it never trips this check).
fn sp_used_unsafely(inst: &MachInst) -> bool {
    if inst.is_call() {
        return true;
    }
    if inst.implicit_defs.contains(&SP) {
        return true;
    }
    inst.operands.iter().any(|operand| match operand {
        // Split addressing / ALU operand form of SP (e.g. `SUB SP,SP,#imm`,
        // `MOV X29,SP`, `ADD Xd,SP,#imm`, `[Rt, Special(SP), Imm]`).
        MachOperand::Special(SpecialReg::SP) => true,
        // SP as a bare register operand (never a plain load/store base, which is
        // the MemOp variant) — an ALU/move source or def touching SP.
        MachOperand::PReg(p) if *p == SP => true,
        _ => false,
    })
}

/// A stream is in the final, fully-lowered form this validator models only if no
/// operand is a pre-regalloc `VReg` or a pre-frame-lowering placeholder
/// (`StackSlot`/`FrameIndex`/`IncomingArg`). Any of these means the analysis
/// assumptions (all frame access is a resolved constant-offset `MemOp`) do not
/// hold, so we DECLINE.
fn stream_is_final(func: &MachFunction) -> bool {
    // Inspect the block table itself, not `block_order`: an omitted reachable
    // block must not be able to evade final-form validation.
    for block in &func.blocks {
        for &inst_id in &block.insts {
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                return false;
            };
            for operand in &inst.operands {
                if matches!(
                    operand,
                    MachOperand::VReg(_)
                        | MachOperand::StackSlot(_)
                        | MachOperand::FrameIndex(_)
                        | MachOperand::IncomingArg(_)
                ) {
                    return false;
                }
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Forward MUST reaching-store fixpoint
// ---------------------------------------------------------------------------

/// The stored-slot bitset on entry to block `b`: the entry block starts EMPTY (no
/// spill slot is stored before the body runs); every other block is the
/// INTERSECTION of its reachable predecessors' out-sets (a slot is stored only if
/// stored on ALL paths).
fn block_in(
    b: usize,
    entry_idx: usize,
    preds: &[Vec<usize>],
    stored_out: &[u64],
    reachable: &[bool],
) -> u64 {
    if b == entry_idx {
        return 0;
    }
    let mut acc = u64::MAX;
    let mut any = false;
    for &p in &preds[b] {
        if reachable[p] {
            acc &= stored_out[p];
            any = true;
        }
    }
    // A reachable non-entry block always has a reachable predecessor; the empty
    // fallback is defensive and can never over-approximate the stored set.
    if any { acc } else { 0 }
}

/// Run the analysis over `func`. Returns `Some(violations)` (possibly empty) for a
/// stream we could soundly model, or `None` to DECLINE (non-final stream, framed
/// / SP-escaping function, unmodeled SP form, malformed CFG, or non-convergence)
/// — declining reports nothing. `skip_flagged_reloads` skips loads stamped
/// `SPILL_SLOT_ACCESS`; the caller sets it only when the frame model analyzed
/// (did not decline) the same stream.
pub(super) fn analyze(
    func: &MachFunction,
    skip_flagged_reloads: bool,
) -> Option<Vec<LegacyViolation>> {
    if !stream_is_final(func) {
        return None;
    }
    let nblocks = func.blocks.len();
    if nblocks == 0 {
        return Some(Vec::new());
    }
    let entry_idx = func.entry.0 as usize;
    if entry_idx >= nblocks {
        return None;
    }

    // 1. Validate the successor graph and independently derive predecessors.
    // `MachBlock::preds` is auxiliary allocator metadata and can be stale; a
    // missing predecessor there must never turn a MUST intersection into a
    // false proof that a slot is initialized on every path.
    let mut preds = vec![Vec::new(); nblocks];
    for (b, block) in func.blocks.iter().enumerate() {
        for &succ in &block.succs {
            let s = succ.0 as usize;
            if s >= nblocks {
                return None;
            }
            preds[s].push(b);
        }
    }

    // 2. Reachability from entry over the validated successor graph.
    let mut reachable = vec![false; nblocks];
    let mut queue = VecDeque::new();
    reachable[entry_idx] = true;
    queue.push_back(func.entry);
    while let Some(bid) = queue.pop_front() {
        let block = func.blocks.get(bid.0 as usize)?;
        for &s in &block.succs {
            let si = s.0 as usize;
            if !reachable[si] {
                reachable[si] = true;
                queue.push_back(s);
            }
        }
    }

    // 3. Safety + slot-collection pre-pass. Any unsafe SP use or unmodeled SP
    //    access DECLINES; every distinct tracked STORE offset is assigned a bit.
    let mut offset_bit: HashMap<i64, u32> = HashMap::new();
    for (b, &is_reachable) in reachable.iter().enumerate() {
        if !is_reachable {
            continue;
        }
        for &inst_id in &func.blocks[b].insts {
            let inst = func.insts.get(inst_id.0 as usize)?;
            if sp_used_unsafely(inst) {
                return None;
            }
            match classify_slot_access(inst) {
                SlotAccess::Decline => return None,
                SlotAccess::Store(off) => {
                    if !offset_bit.contains_key(&off) {
                        let next = offset_bit.len();
                        if next >= MAX_TRACKED_SLOTS {
                            return None;
                        }
                        offset_bit.insert(off, next as u32);
                    }
                }
                SlotAccess::Load(_) | SlotAccess::None => {}
            }
        }
    }
    // Nothing body-managed to track: analyzed, trivially clean.
    if offset_bit.is_empty() {
        return Some(Vec::new());
    }

    // 4. Per-block gen_bits = union of tracked-store bits.
    let bit_of = |off: i64| -> Option<u64> { offset_bit.get(&off).map(|&b| 1u64 << b) };
    let mut gen_bits = vec![0u64; nblocks];
    for b in 0..nblocks {
        if !reachable[b] {
            continue;
        }
        let mut g = 0u64;
        for &inst_id in &func.blocks[b].insts {
            let inst = &func.insts[inst_id.0 as usize];
            if let SlotAccess::Store(off) = classify_slot_access(inst)
                && let Some(m) = bit_of(off)
            {
                g |= m;
            }
        }
        gen_bits[b] = g;
    }

    // 5. Forward MUST fixpoint. Non-entry out-sets start at TOP (all stored) so a
    //    not-yet-computed back-edge predecessor never spuriously narrows a loop
    //    header; intersection can only clear bits, so it converges.
    let mut stored_out = vec![u64::MAX; nblocks];
    stored_out[entry_idx] = gen_bits[entry_idx];
    let max_iters = nblocks.saturating_mul(MAX_TRACKED_SLOTS).saturating_add(8);
    let mut iters = 0usize;
    loop {
        let mut changed = false;
        // Iterate the authoritative block table, not `block_order`: an omitted
        // reachable block must still participate in the fixed point.
        for b in 0..nblocks {
            if !reachable[b] {
                continue;
            }
            let in_b = block_in(b, entry_idx, &preds, &stored_out, &reachable);
            let new_out = in_b | gen_bits[b];
            if new_out != stored_out[b] {
                stored_out[b] = new_out;
                changed = true;
            }
        }
        iters += 1;
        if !changed {
            break;
        }
        if iters > max_iters {
            // Non-convergence (should be unreachable): decline, never flag.
            return None;
        }
    }

    // 6. Per-instruction reload check. As above, walk every reachable block in
    // the authoritative block table rather than trusting `block_order`.
    let mut violations = Vec::new();
    for b in 0..nblocks {
        if !reachable[b] {
            continue;
        }
        let bid = trust_cg_ir::BlockId(b as u32);
        let mut cur = block_in(b, entry_idx, &preds, &stored_out, &reachable);
        for (inst_pos, &inst_id) in func.blocks[b].insts.iter().enumerate() {
            let inst = &func.insts[inst_id.0 as usize];
            match classify_slot_access(inst) {
                SlotAccess::Load(off) => {
                    // Only body-managed (ever-stored) slots are tracked; a reload
                    // of an untracked offset is not attributable and not flagged.
                    // Flagged spill reloads are checked by the frame model
                    // when it analyzed this stream.
                    if !(skip_flagged_reloads && inst.flags.is_spill_slot_access())
                        && let Some(m) = bit_of(off)
                        && (cur & m) == 0
                    {
                        violations.push((bid.0, inst_pos, inst.opcode, off));
                    }
                }
                SlotAccess::Store(off) => {
                    if let Some(m) = bit_of(off) {
                        cur |= m;
                    }
                }
                SlotAccess::None | SlotAccess::Decline => {}
            }
        }
    }
    Some(violations)
}
