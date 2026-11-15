// trust-cg-verify/post_ra_spill_slots.rs - TV-6 final-stream AArch64 frame dataflow net
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-6 frame dataflow net over the FINAL post-register-allocation,
//! post-frame-lowering AArch64 stream (`[TCG-A64-SPILL-SLOT]`).
//!
//! # What this checks
//!
//! The companion [`crate::post_ra_reaching_def`] net proves that every physical
//! register read has *some* reaching definition. It deliberately treats a call's
//! clobbers as definitions and never looks at memory, so it cannot see a spill
//! reload that reads the wrong or an unwritten stack slot, a value left in a
//! caller-saved register across a call, a callee-saved register that is not
//! restored, or a return lane overwritten while the frame is torn down. This
//! module is a forward abstract interpretation of the actual AArch64 frame that
//! checks exactly those properties on the emitted instruction stream:
//!
//! 1. **Spill store/reload pairing** (`reload-without-reaching-store`,
//!    `reload-from-non-spill-store`, `reload-of-call-clobbered-slot`,
//!    `reload-misaligned-with-spill-store`). Every reload stamped
//!    [`InstFlags::SPILL_SLOT_ACCESS`](trust_cg_ir::InstFlags) must read
//!    exactly the bytes one flagged spill store wrote on every path from entry,
//!    with no intervening non-spill store and no call that may have written
//!    them. A dropped spill store, a spill slot overlapping a callee-save,
//!    local, probe or outgoing-argument cell, and a store or reload offset
//!    shifted onto unwritten or non-spill bytes, inside a spill cell or across
//!    two spill cells, all fail. The final stream carries no spill-slot
//!    identity, so a reload shifted by whole slots onto ANOTHER spill cell that
//!    spill stores wrote with the same width on every path is not detected.
//! 2. **Call clobbers** (`call-clobbered-register-read`,
//!    `call-clobbered-upper-half-read`). A call ends every AAPCS64 volatile,
//!    non-result location (X8-X18, X30, V16-V31); reading one before
//!    redefining it reads garbage. This catches a reload hoisted above the
//!    call it must follow and a reload whose destination register was swapped
//!    away from the register its consumer reads. AAPCS64 preserves only the
//!    low 64 bits of V8-V15, so a 128-bit (Q-view) read of V8-V15 after a call
//!    with no redefinition of that register in between reads a clobbered upper
//!    half: a 128-bit value kept in V8-V15 across a call instead of being
//!    spilled.
//! 3. **Callee-saved preservation** (`callee-saved-not-restored`,
//!    `return-address-not-restored`, `stack-pointer-not-restored`). At every
//!    `RET` and tail call, X19-X28, X29, the low halves of V8-V15, the return
//!    address and SP must hold their values from function entry — restored by
//!    the epilogue from the cells the prologue saved them in.
//! 4. **Caller values** (`caller-callee-saved-value-read`). The caller's
//!    X19-X28/V8-V15 values may only be moved between registers or stored to
//!    the frame (the prologue save); computing with one, using it as an
//!    address or passing it consumes a value meaningless to this function.
//!    Register copies and spill stores propagate values and taints instead of
//!    being checked themselves; the eventual consumer is checked.
//! 5. **Return lanes** (`return-lane-clobbered`,
//!    `return-lane-holds-caller-value`). A `RET`'s implicit ABI sinks (and a tail
//!    call's argument lanes) must not be call-clobbered, hold a caller's
//!    callee-saved value, or be computed inside the epilogue (after the frame
//!    teardown began in the same block). A shrink-wrapped frame edge ends its
//!    epilogue with a branch to a return shared with a frameless path; code
//!    in that return block runs frameless by design and is not "epilogue".
//!
//! # Model
//!
//! Addresses are byte offsets from the CFA (SP at function entry). The state at
//! each program point holds, per register location (X0-X30, V0-V31 keyed by
//! number so W/X and B/H/S/D/Q views alias), an abstract value — an exact frame
//! address `CFA+c`, a known constant, the untouched entry value, or opaque —
//! with taints (call-clobbered, possible caller callee-saved value, written
//! after teardown); the SP height; and the frame cells written so far, each a
//! byte range with the set of possible writers (uninitialized, spill store,
//! other store, callee) and the stored abstract value. The model follows what
//! frame lowering actually emits: pre-index `STP ... [SP,#-n]!` saves, offset
//! `STP` saves, `ADD X29,SP,#k`, chunked `SUB SP`, unrolled `STR XZR,[SP]`
//! probes, the counted probe loop (`SUB SP; STR XZR,[SP]; SUBS Xc,Xc,#1; B.NE`
//! summarized from the loop counter's known entry value), FP- and SP-relative
//! slot addressing, large-offset scratch materialization (`MOVZ/MOVK` plus
//! `ADD/SUB` from a frame base), writeback pair/scalar forms, the dynamic-frame
//! `MOV SP,X29` epilogue and post-index `LDP` teardown. Joins take the meet;
//! predecessors are recomputed from the successor graph, and all reachable
//! blocks are analyzed independently of `block_order`. An edge into a landing
//! pad carries the merged state after the block's calls (unwinding leaves from
//! a call site with the frame intact), never the block's end state.
//!
//! # Assumptions and conservative choices
//!
//! * Spill and callee-save cells are private: a store or call through a pointer
//!   that is not a known frame address never writes them. Frame addresses that
//!   escape into memory or calls are not tracked further.
//! * A call may write only its outgoing stack-argument area, taken as
//!   `[SP, SP+n)` where `n` covers the non-save SP-relative stores the same
//!   block made since the previous call.
//! * Result lanes (X0-X7, V0-V7) are defined by every call: the final stream
//!   does not carry callee result arity, so a return lane overwritten by an
//!   intervening call's result register is not distinguishable here.
//! * Any write to V8-V15 (including a scalar B/H/S/D write, which zeroes the
//!   upper bits, and a lane insert) is taken to define its upper half, so a
//!   lane-by-lane rebuild after a call is not reported; only a Q-view read
//!   reads the upper half.
//! * Non-spill loads are not checked for initialization; locals may be read
//!   partially initialized (padding) or under dynamic guards.
//!
//! # Declines
//!
//! A stream the net cannot soundly model yields no report and increments a
//! per-reason counter ([`DeclineReason`], [`decline_counts`]): a non-final
//! stream, a malformed CFG, a flagged spill access that is not a plain scalar
//! constant-offset access, a flagged spill access whose base is not a known
//! frame address (for example SP after a runtime-sized allocation), more than
//! [`MAX_CELLS`] tracked cells or an oversize state, and fixpoint
//! non-convergence. SP-relative stores with an unknown SP (dynamic frames) are
//! modeled, not declined: they are outgoing-argument or object stores, which the
//! privacy assumption keeps away from spill and save cells.
//!
//! The original SP-only reaching-store rule is kept in [`legacy`] for the
//! frameless SP-invariant shape it could model and runs alongside.
//!
//! # Enforcement
//!
//! Ships **ENFORCE** ([`AARCH64_SPILL_SLOT_DEFAULT`], diagnostic override
//! `TCG_AARCH64_POST_RA_SPILL_SLOTS` = `off`|`warn`|`enforce`); proof-grade
//! pipeline transitions force Enforce. This is a validation net over the
//! emitted stream, not a proof of the frame lowering: a clean result means the
//! checked properties hold on this stream under the assumptions above.

mod legacy;

use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};

use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, PReg, SpecialReg};
use trust_cg_opt::effects::{is_lse_cas, is_lse_rmw};

pub use crate::post_regalloc_recheck::PostRegallocRecheckMode;

/// Maximum number of tracked frame cells per program point. More declines.
pub const MAX_CELLS: usize = 8192;

/// Upper bound on `blocks x tracked stores` before the net declines as
/// oversize (bounds the per-block state memory).
const MAX_STATE_WORK: usize = 40_000_000;

/// Maximum number of reported violations per function.
const MAX_REPORTS: usize = 64;

// ---------------------------------------------------------------------------
// Register locations
// ---------------------------------------------------------------------------

/// Register locations: `0..=30` for X0-X30/W0-W30, `32..=63` for V0-V31 and
/// their D/S/H/B views. Index 31 is unused (SP is tracked separately).
const LOCS: usize = 64;
const FP_LOC: usize = 29;
const LR_LOC: usize = 30;

fn reg_loc(reg: PReg) -> Option<usize> {
    let e = reg.encoding() as usize;
    match e {
        0..=30 => Some(e),
        32..=62 => Some(e - 32),
        64..=95 => Some(32 + e - 64),
        96..=127 => Some(32 + e - 96),
        128..=159 => Some(32 + e - 128),
        165..=196 => Some(32 + e - 165),
        197..=228 => Some(32 + e - 197),
        _ => None,
    }
}

/// SP and WSP as register operands (register 31 in an SP context).
fn is_sp_reg(reg: PReg) -> bool {
    matches!(reg.encoding(), 31 | 63)
}

/// XZR and WZR.
fn is_zero_reg(reg: PReg) -> bool {
    matches!(reg.encoding(), 160 | 161)
}

fn is_gpr64(reg: PReg) -> bool {
    reg.encoding() <= 30
}

fn is_gpr32(reg: PReg) -> bool {
    (32..=62).contains(&reg.encoding())
}

/// Transfer width in bytes of a data register.
fn reg_bytes(reg: PReg) -> Option<i64> {
    match reg.encoding() {
        0..=30 | 160 => Some(8),
        32..=62 | 161 => Some(4),
        64..=95 => Some(16),
        96..=127 => Some(8),
        128..=159 => Some(4),
        165..=196 => Some(2),
        197..=228 => Some(1),
        _ => None,
    }
}

/// AAPCS64 callee-saved locations: X19-X28 and (the low halves of) V8-V15.
fn is_callee_saved_loc(loc: usize) -> bool {
    (19..=28).contains(&loc) || (40..=47).contains(&loc)
}

/// Locations frame lowering saves and restores: callee-saved plus FP and LR.
fn is_frame_record_loc(loc: usize) -> bool {
    is_callee_saved_loc(loc) || loc == FP_LOC || loc == LR_LOC
}

/// Result-capable volatile locations (X0-X7, V0-V7): defined by every call.
fn is_call_result_loc(loc: usize) -> bool {
    loc <= 7 || (32..=39).contains(&loc)
}

/// Volatile non-result locations (X8-X18, X30, V16-V31): garbage after a call.
fn is_call_clobber_loc(loc: usize) -> bool {
    (8..=18).contains(&loc) || loc == LR_LOC || (48..=63).contains(&loc)
}

/// Bit of V8-V15 in [`State::upper_clobbered`] for a Q-view (128-bit)
/// register, or 0 for any other register or view.
fn q_view_upper_bit(reg: PReg) -> u8 {
    match reg.encoding() {
        e @ 72..=79 => 1u8 << (e - 72),
        _ => 0,
    }
}

/// Bit of V8-V15 in [`State::upper_clobbered`] for any view of the register.
fn fpr_upper_bit(reg: PReg) -> u8 {
    match reg_loc(reg) {
        Some(loc @ 40..=47) => 1u8 << (loc - 40),
        _ => 0,
    }
}

fn loc_name(loc: usize) -> String {
    if loc < 32 {
        format!("x{loc}")
    } else {
        format!("v{}", loc - 32)
    }
}

// ---------------------------------------------------------------------------
// Abstract values
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Val {
    /// The exact address `CFA + offset`.
    Frame(i64),
    /// A known 64-bit constant.
    Const(i64),
    /// The untouched value the location held at function entry.
    Entry(u8),
    /// Anything else.
    Opaque,
}

/// Garbage left by a call in a volatile non-result location.
const T_CALL_CLOBBERED: u8 = 1 << 0;
/// May be (on some path) a caller's callee-saved value.
const T_CALLER_SAVED: u8 = 1 << 1;
/// Computed (not copied) after the frame teardown began in the same block.
const T_EPILOGUE: u8 = 1 << 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AbsVal {
    val: Val,
    taint: u8,
}

impl AbsVal {
    const fn new(val: Val) -> Self {
        Self { val, taint: 0 }
    }

    const fn opaque(taint: u8) -> Self {
        Self {
            val: Val::Opaque,
            taint,
        }
    }

    fn frame(self) -> Option<i64> {
        match self.val {
            Val::Frame(c) => Some(c),
            _ => None,
        }
    }

    fn is_callers_callee_saved_entry(self) -> bool {
        matches!(self.val, Val::Entry(loc) if is_callee_saved_loc(loc as usize))
    }

    fn is_frame_record_entry(self) -> bool {
        matches!(self.val, Val::Entry(loc) if is_frame_record_loc(loc as usize))
    }

    fn may_hold_callers_callee_saved(self) -> bool {
        self.is_callers_callee_saved_entry() || self.taint & T_CALLER_SAVED != 0
    }

    /// Exactly the untouched entry value of `loc`, on every path.
    fn is_entry_of(self, loc: usize) -> bool {
        self.val == Val::Entry(loc as u8) && self.taint == 0
    }

    fn merge(self, other: Self) -> Self {
        if self == other {
            return self;
        }
        let mut taint = self.taint | other.taint;
        if self.is_callers_callee_saved_entry() || other.is_callers_callee_saved_entry() {
            taint |= T_CALLER_SAVED;
        }
        let val = if self.val == other.val {
            self.val
        } else {
            Val::Opaque
        };
        Self { val, taint }
    }
}

// ---------------------------------------------------------------------------
// Frame cells
// ---------------------------------------------------------------------------

/// Possible writers of a byte: not written in this activation (below the CFA).
const K_UNINIT: u8 = 1 << 0;
/// A flagged spill store.
const K_SPILL: u8 = 1 << 1;
/// Any other store (callee-save, local, probe, outgoing argument, caller data).
const K_OTHER: u8 = 1 << 2;
/// A call that may have written its incoming stack arguments.
const K_CALLEE: u8 = 1 << 3;

/// Writers of an untracked byte range `[lo, hi)`: bytes below the CFA are
/// uninitialized in this activation, bytes at or above it belong to the caller.
fn implicit_kinds(lo: i64, hi: i64) -> u8 {
    let mut kinds = 0;
    if lo < 0 {
        kinds |= K_UNINIT;
    }
    if hi > 0 {
        kinds |= K_OTHER;
    }
    kinds
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Cell {
    end: i64,
    kinds: u8,
    val: AbsVal,
}

/// The frame cells of a program point: disjoint, non-empty byte ranges
/// `[start, cell.end)`, ascending by start, in one sorted vector.
///
/// Every operation below maintains disjointness and non-emptiness (a store
/// replaces the cells it overlaps by their outside pieces plus the new cell;
/// marking splits each touched cell into pieces of its own range; a join
/// emits cells on disjoint elementary intervals), so the ends ascend with the
/// starts and each lookup is a binary search. The vector replaced an ordered
/// map with the same keys: the analysis clones a state per block visit and
/// joins states at every edge, and the map's per-node allocation and
/// rebuilding made the join the frame net's largest cost.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Cells(Vec<(i64, Cell)>);

impl Cells {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    #[cfg(test)]
    fn iter(&self) -> impl DoubleEndedIterator<Item = (&i64, &Cell)> + Clone {
        self.0.iter().map(|(start, cell)| (start, cell))
    }

    #[cfg(test)]
    fn keys(&self) -> impl Iterator<Item = &i64> {
        self.0.iter().map(|(start, _)| start)
    }

    /// Insert or replace the cell starting at `start` (map semantics).
    fn insert(&mut self, start: i64, cell: Cell) -> Option<Cell> {
        match self.0.binary_search_by_key(&start, |(s, _)| *s) {
            Ok(i) => Some(std::mem::replace(&mut self.0[i].1, cell)),
            Err(i) => {
                self.0.insert(i, (start, cell));
                None
            }
        }
    }

    #[cfg(test)]
    fn remove(&mut self, start: &i64) -> Option<Cell> {
        self.0
            .binary_search_by_key(start, |(s, _)| *s)
            .ok()
            .map(|i| self.0.remove(i).1)
    }

    #[cfg(test)]
    fn get(&self, start: &i64) -> Option<&Cell> {
        self.0
            .binary_search_by_key(start, |(s, _)| *s)
            .ok()
            .map(|i| &self.0[i].1)
    }

    #[cfg(test)]
    fn get_mut(&mut self, start: &i64) -> Option<&mut Cell> {
        self.0
            .binary_search_by_key(start, |(s, _)| *s)
            .ok()
            .map(|i| &mut self.0[i].1)
    }

    /// Index of the first cell whose start is at least `pos`.
    fn first_starting_at_or_after(&self, pos: i64) -> usize {
        self.0.partition_point(|(start, _)| *start < pos)
    }

    /// The cells overlapping `[lo, hi)`, as an index range: every cell that
    /// starts before `hi` and ends after `lo`. They are contiguous because the
    /// cells are disjoint and ascending.
    fn overlapping(&self, lo: i64, hi: i64) -> std::ops::Range<usize> {
        let first = self.0.partition_point(|(_, cell)| cell.end <= lo);
        let end = self.first_starting_at_or_after(hi).max(first);
        first..end
    }
}

impl<const N: usize> From<[(i64, Cell); N]> for Cells {
    fn from(cells: [(i64, Cell); N]) -> Self {
        cells.into_iter().collect()
    }
}

impl FromIterator<(i64, Cell)> for Cells {
    /// Map semantics: ascending by start, a later cell replacing an earlier
    /// one with the same start. An ascending, distinct input (what the join
    /// produces) is taken as it is.
    fn from_iter<I: IntoIterator<Item = (i64, Cell)>>(iter: I) -> Self {
        let cells: Vec<(i64, Cell)> = iter.into_iter().collect();
        if cells.windows(2).all(|pair| pair[0].0 < pair[1].0) {
            return Self(cells);
        }
        let mut out = Self::new();
        for (start, cell) in cells {
            out.insert(start, cell);
        }
        out
    }
}

fn cell_covering(cells: &Cells, pos: i64) -> Option<(i64, &Cell)> {
    // The last cell starting at or before `pos`, when it reaches past `pos`.
    let starts_at_or_before = cells.0.partition_point(|(start, _)| *start <= pos);
    starts_at_or_before
        .checked_sub(1)
        .map(|i| &cells.0[i])
        .filter(|(_, cell)| cell.end > pos)
        .map(|(start, cell)| (*start, cell))
}

/// Join of two frame-cell lists at a control-flow merge, over the elementary
/// intervals between consecutive bounds (every cell start and end of either
/// list, and the CFA). An interval covered by the same cell `[lo, end)` in both
/// lists keeps that cell with the union of its writers and the join of its
/// values; any other covered interval becomes an opaque cell with the union of
/// both sides' writers (the implicit writers of an untracked side) and taints;
/// an interval neither list tracks stays untracked.
///
/// Only the lists' differing middles are swept ([`merge_cell_slices`]): a
/// cell both lists hold at the same position from the front (or from the back)
/// joins to itself, and the elementary intervals around it are the same
/// whether or not the other side's bounds are present, because an interval
/// between a common cell and a differing one is covered by neither list and
/// emits nothing. So the join is the common prefix, the joined middles and the
/// common suffix. (The CFA bound only splits a covered interval, and a cell
/// covering the CFA lies in the part of the lists it belongs to.)
fn merge_cells(a: &Cells, b: &Cells) -> Cells {
    if a == b {
        return a.clone();
    }
    let (prefix, suffix) = common_prefix_suffix(&a.0, &b.0);
    let middle = merge_cell_slices(
        &a.0[prefix..a.0.len() - suffix],
        &b.0[prefix..b.0.len() - suffix],
    );
    let mut out = Vec::with_capacity(prefix + middle.len() + suffix);
    out.extend_from_slice(&a.0[..prefix]);
    out.extend(middle);
    out.extend_from_slice(&a.0[a.0.len() - suffix..]);
    Cells(out)
}

/// Lengths of the longest common prefix and, of what remains, the longest
/// common suffix of two cell lists.
fn common_prefix_suffix(a: &[(i64, Cell)], b: &[(i64, Cell)]) -> (usize, usize) {
    let prefix = a.iter().zip(b).take_while(|(x, y)| x == y).count();
    let suffix = a[prefix..]
        .iter()
        .rev()
        .zip(b[prefix..].iter().rev())
        .take_while(|(x, y)| x == y)
        .count();
    (prefix, suffix)
}

/// The elementary-interval join of two ascending, disjoint cell lists, in
/// one ordered sweep: the bounds are a merge of three ascending sequences
/// (each list's `start_0 < end_0 <= start_1 < ...`, and the CFA), and each
/// list's covering cell is found by a cursor that only moves forward (the
/// intervals are visited in ascending order, and among disjoint cells the
/// only one that can cover a point is the first that ends after it, when it
/// also starts at or before it).
fn merge_cell_slices(a: &[(i64, Cell)], b: &[(i64, Cell)]) -> Vec<(i64, Cell)> {
    let bound = |cells: &[(i64, Cell)], k: usize| {
        let (start, cell) = &cells[k / 2];
        if k.is_multiple_of(2) {
            *start
        } else {
            cell.end
        }
    };
    let mut bounds: Vec<i64> = Vec::with_capacity(2 * (a.len() + b.len()) + 1);
    let (mut ka, mut kb) = (0usize, 0usize);
    let mut cfa = true;
    loop {
        let na = (ka < 2 * a.len()).then(|| bound(a, ka));
        let nb = (kb < 2 * b.len()).then(|| bound(b, kb));
        let nc = cfa.then_some(0i64);
        let Some(next) = [na, nb, nc].into_iter().flatten().min() else {
            break;
        };
        if na == Some(next) {
            ka += 1;
        } else if nb == Some(next) {
            kb += 1;
        } else {
            cfa = false;
        }
        if bounds.last() != Some(&next) {
            bounds.push(next);
        }
    }
    let (mut ia, mut ib) = (0usize, 0usize);
    let mut out: Vec<(i64, Cell)> = Vec::with_capacity(bounds.len());
    let mut i = 0;
    while i + 1 < bounds.len() {
        let lo = bounds[i];
        let hi = bounds[i + 1];
        while ia < a.len() && a[ia].1.end <= lo {
            ia += 1;
        }
        while ib < b.len() && b[ib].1.end <= lo {
            ib += 1;
        }
        let ca = a.get(ia).filter(|(start, _)| *start <= lo);
        let cb = b.get(ib).filter(|(start, _)| *start <= lo);
        if ca.is_none() && cb.is_none() {
            i += 1;
            continue;
        }
        if let (Some((sa, xa)), Some((sb, xb))) = (ca, cb)
            && *sa == lo
            && *sb == lo
            && xa.end == xb.end
        {
            out.push((
                lo,
                Cell {
                    end: xa.end,
                    kinds: xa.kinds | xb.kinds,
                    val: xa.val.merge(xb.val),
                },
            ));
            while i < bounds.len() && bounds[i] < xa.end {
                i += 1;
            }
            continue;
        }
        let ka = ca.map_or_else(|| implicit_kinds(lo, hi), |(_, c)| c.kinds);
        let kb = cb.map_or_else(|| implicit_kinds(lo, hi), |(_, c)| c.kinds);
        let taint = ca.map_or(0, |(_, c)| c.val.taint) | cb.map_or(0, |(_, c)| c.val.taint);
        out.push((
            lo,
            Cell {
                end: hi,
                kinds: ka | kb,
                val: AbsVal::opaque(taint),
            },
        ));
        i += 1;
    }
    out
}

// ---------------------------------------------------------------------------
// Program-point state
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
struct State {
    regs: [AbsVal; LOCS],
    /// SP as `CFA + sp`, when known.
    sp: Option<i64>,
    /// The frame teardown began earlier in the current block.
    torn_down: bool,
    /// Bit `i`: a call may have clobbered the upper 64 bits of V(8+i) and no
    /// instruction has written V(8+i) since.
    upper_clobbered: u8,
    cells: Cells,
}

impl State {
    fn entry() -> Self {
        let mut regs = [AbsVal::opaque(0); LOCS];
        for (loc, reg) in regs.iter_mut().enumerate() {
            if loc != 31 {
                *reg = AbsVal::new(Val::Entry(loc as u8));
            }
        }
        Self {
            regs,
            sp: Some(0),
            torn_down: false,
            upper_clobbered: 0,
            cells: Cells::new(),
        }
    }

    /// `*self = self.merge(other)`, returning whether that changed `self`.
    /// Decided field by field as the join is formed, without building a
    /// second state or comparing whole states; the cells are joined only when
    /// the two sides differ (`merge_cells` of equal lists is the list).
    fn join_from(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (reg, theirs) in self.regs.iter_mut().zip(other.regs.iter()) {
            let joined = reg.merge(*theirs);
            if joined != *reg {
                *reg = joined;
                changed = true;
            }
        }
        if self.sp != other.sp && self.sp.is_some() {
            self.sp = None;
            changed = true;
        }
        if other.torn_down && !self.torn_down {
            self.torn_down = true;
            changed = true;
        }
        let upper = self.upper_clobbered | other.upper_clobbered;
        if upper != self.upper_clobbered {
            self.upper_clobbered = upper;
            changed = true;
        }
        if self.cells != other.cells {
            // As `merge_cells`: only the differing middles are joined, and
            // `self` changes exactly when their join differs from its middle.
            let (prefix, suffix) = common_prefix_suffix(&self.cells.0, &other.cells.0);
            let mine = prefix..self.cells.0.len() - suffix;
            let joined = merge_cell_slices(
                &self.cells.0[mine.clone()],
                &other.cells.0[prefix..other.cells.0.len() - suffix],
            );
            if joined[..] != self.cells.0[mine.clone()] {
                self.cells.0.splice(mine, joined);
                changed = true;
            }
        }
        changed
    }

    fn merge(&self, other: &Self) -> Self {
        let mut regs = self.regs;
        for (reg, theirs) in regs.iter_mut().zip(other.regs.iter()) {
            *reg = reg.merge(*theirs);
        }
        Self {
            regs,
            sp: if self.sp == other.sp { self.sp } else { None },
            torn_down: self.torn_down || other.torn_down,
            upper_clobbered: self.upper_clobbered | other.upper_clobbered,
            cells: merge_cells(&self.cells, &other.cells),
        }
    }

    fn sp_value(&self) -> AbsVal {
        match self.sp {
            Some(c) => AbsVal::new(Val::Frame(c)),
            None => AbsVal::opaque(0),
        }
    }

    /// Record a store of `val` to `[addr, addr+width)` by writers `kinds`.
    /// The caller guarantees `addr + width` does not overflow.
    ///
    /// The cells overlapping the range are replaced by their pieces outside
    /// it (only the first can start before `addr`, only the last can end
    /// after `addr + width`; both keep their writers and forget their values)
    /// and the new cell.
    fn store(&mut self, addr: i64, width: i64, kinds: u8, val: AbsVal) {
        let end = addr + width;
        let run = self.cells.overlapping(addr, end);
        let mut pieces: Vec<(i64, Cell)> = Vec::with_capacity(3);
        if !run.is_empty() {
            let (start, cell) = &self.cells.0[run.start];
            if *start < addr {
                pieces.push((
                    *start,
                    Cell {
                        end: addr,
                        kinds: cell.kinds,
                        val: AbsVal::opaque(cell.val.taint),
                    },
                ));
            }
        }
        pieces.push((addr, Cell { end, kinds, val }));
        if !run.is_empty() {
            let (_, cell) = &self.cells.0[run.end - 1];
            if cell.end > end {
                pieces.push((
                    end,
                    Cell {
                        end: cell.end,
                        kinds: cell.kinds,
                        val: AbsVal::opaque(cell.val.taint),
                    },
                ));
            }
        }
        self.cells.0.splice(run, pieces);
    }

    /// Possible writers of `[addr, addr+width)` and, when one cell covers the
    /// range exactly, its stored value. The caller guarantees `addr + width`
    /// does not overflow.
    fn load(&self, addr: i64, width: i64) -> (u8, Option<AbsVal>) {
        let end = addr + width;
        let mut kinds = 0u8;
        let mut cursor = addr;
        let mut exact = None;
        let first = cell_covering(&self.cells, addr).map(|(start, _)| start);
        let lower = first.unwrap_or(addr);
        let from = self.cells.first_starting_at_or_after(lower);
        let to = self.cells.first_starting_at_or_after(end).max(from);
        for (start, cell) in &self.cells.0[from..to] {
            let start = *start;
            if cell.end <= addr {
                continue;
            }
            if start > cursor {
                kinds |= implicit_kinds(cursor, start);
            }
            kinds |= cell.kinds;
            if start == addr && cell.end == end {
                exact = Some(cell.val);
            }
            cursor = cursor.max(cell.end);
        }
        if cursor < end {
            kinds |= implicit_kinds(cursor, end);
        }
        (kinds, exact)
    }

    /// Add `kinds` to every tracked byte in `[lo, hi)`, splitting cells at the
    /// boundaries, and forget their values.
    fn mark_written(&mut self, lo: i64, hi: i64, kinds: u8) {
        if lo >= hi {
            return;
        }
        let run = self.cells.overlapping(lo, hi);
        if run.is_empty() {
            return;
        }
        let mut pieces: Vec<(i64, Cell)> = Vec::with_capacity(run.len() + 2);
        for (start, cell) in &self.cells.0[run.clone()] {
            let start = *start;
            if start < lo {
                pieces.push((
                    start,
                    Cell {
                        end: lo,
                        kinds: cell.kinds,
                        val: AbsVal::opaque(cell.val.taint),
                    },
                ));
            }
            pieces.push((
                start.max(lo),
                Cell {
                    end: cell.end.min(hi),
                    kinds: cell.kinds | kinds,
                    val: AbsVal::opaque(cell.val.taint),
                },
            ));
            if cell.end > hi {
                pieces.push((
                    hi,
                    Cell {
                        end: cell.end,
                        kinds: cell.kinds,
                        val: AbsVal::opaque(cell.val.taint),
                    },
                ));
            }
        }
        self.cells.0.splice(run, pieces);
    }
}

// ---------------------------------------------------------------------------
// Instruction decoding (independent of the codegen encoder)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BaseOp {
    Sp,
    Reg(PReg),
}

/// One decoded load/store with a constant displacement.
#[derive(Debug, Clone)]
struct Access {
    base: BaseOp,
    /// Address of the first data register relative to the base value BEFORE
    /// any writeback.
    disp: i64,
    /// Base register update applied by a pre/post-index form.
    writeback: Option<i64>,
    /// Data registers in address order.
    data: Vec<PReg>,
    /// Bytes per data register.
    width: i64,
    is_load: bool,
}

enum MemShape {
    None,
    Access(Access),
    /// Touches memory in a form this net does not decode exactly.
    Unmodeled {
        writes: bool,
    },
}

fn base_op(op: &MachOperand) -> Option<BaseOp> {
    match op {
        MachOperand::Special(SpecialReg::SP) => Some(BaseOp::Sp),
        MachOperand::PReg(p) if is_sp_reg(*p) => Some(BaseOp::Sp),
        MachOperand::PReg(p) if !is_zero_reg(*p) => Some(BaseOp::Reg(*p)),
        _ => None,
    }
}

fn mem_base(base: PReg) -> BaseOp {
    if is_sp_reg(base) {
        BaseOp::Sp
    } else {
        BaseOp::Reg(base)
    }
}

/// `[MemOp]`, `[base, #imm]` or `[base]` after the data operands.
fn addressing(ops: &[MachOperand]) -> Option<(BaseOp, i64)> {
    match ops {
        [MachOperand::MemOp { base, offset }] => Some((mem_base(*base), *offset)),
        [base, MachOperand::Imm(offset)] => Some((base_op(base)?, *offset)),
        [base] => Some((base_op(base)?, 0)),
        _ => None,
    }
}

fn data_reg(op: &MachOperand) -> Option<PReg> {
    match op {
        MachOperand::PReg(p) if !is_sp_reg(*p) => Some(*p),
        MachOperand::Special(SpecialReg::XZR) => Some(trust_cg_ir::aarch64_regs::XZR),
        MachOperand::Special(SpecialReg::WZR) => Some(trust_cg_ir::aarch64_regs::WZR),
        _ => None,
    }
}

fn scalar_width(op: AArch64Opcode, data: PReg) -> Option<i64> {
    use AArch64Opcode::*;
    match op {
        LdrRI | StrRI | VolatileLdrRI | VolatileStrRI | LdrPreIndex | StrPreIndex
        | LdrPostIndex | StrPostIndex => reg_bytes(data),
        LdrbRI | StrbRI | LdrsbRI | VolatileLdrbRI | VolatileStrbRI => Some(1),
        LdrhRI | StrhRI | LdrshRI | VolatileLdrhRI | VolatileStrhRI => Some(2),
        STRWui | STRSui => Some(4),
        STRXui | STRDui => Some(8),
        _ => None,
    }
}

fn decode_memory(inst: &MachInst) -> MemShape {
    use AArch64Opcode::*;
    let ops = inst.operands.as_slice();
    let op = inst.opcode;
    let decoded = match op {
        LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | VolatileLdrRI | VolatileLdrbRI
        | VolatileLdrhRI | StrRI | StrbRI | StrhRI | VolatileStrRI | VolatileStrbRI
        | VolatileStrhRI | STRWui | STRXui | STRSui | STRDui => (|| {
            let data = data_reg(ops.first()?)?;
            let (base, disp) = addressing(&ops[1..])?;
            let width = scalar_width(op, data)?;
            let is_load = matches!(
                op,
                LdrRI
                    | LdrbRI
                    | LdrhRI
                    | LdrsbRI
                    | LdrshRI
                    | VolatileLdrRI
                    | VolatileLdrbRI
                    | VolatileLdrhRI
            );
            Some(Access {
                base,
                disp,
                writeback: None,
                data: vec![data],
                width,
                is_load,
            })
        })(),
        LdrPreIndex | StrPreIndex | LdrPostIndex | StrPostIndex => (|| {
            let [data, base, MachOperand::Imm(amount)] = ops else {
                return None;
            };
            let data = data_reg(data)?;
            let base = base_op(base)?;
            let width = scalar_width(op, data)?;
            let pre = matches!(op, LdrPreIndex | StrPreIndex);
            Some(Access {
                base,
                disp: if pre { *amount } else { 0 },
                writeback: Some(*amount),
                data: vec![data],
                width,
                is_load: matches!(op, LdrPreIndex | LdrPostIndex),
            })
        })(),
        StpRI | LdpRI => (|| {
            let first = data_reg(ops.first()?)?;
            let second = data_reg(ops.get(1)?)?;
            let (base, disp) = addressing(ops.get(2..)?)?;
            let width = reg_bytes(first)?;
            (reg_bytes(second)? == width).then_some(Access {
                base,
                disp,
                writeback: None,
                data: vec![first, second],
                width,
                is_load: op == LdpRI,
            })
        })(),
        StpPreIndex | LdpPostIndex | NeonStpQPost | NeonLdpQPost => (|| {
            let [first, second, base, MachOperand::Imm(amount)] = ops else {
                return None;
            };
            let first = data_reg(first)?;
            let second = data_reg(second)?;
            let base = base_op(base)?;
            let width = reg_bytes(first)?;
            if reg_bytes(second)? != width {
                return None;
            }
            let pre = op == StpPreIndex;
            Some(Access {
                base,
                disp: if pre { *amount } else { 0 },
                writeback: Some(*amount),
                data: vec![first, second],
                width,
                is_load: matches!(op, LdpPostIndex | NeonLdpQPost),
            })
        })(),
        _ => {
            let touches = inst.reads_memory()
                || inst.writes_memory()
                || is_lse_rmw(op)
                || is_lse_cas(op)
                || matches!(
                    op,
                    Ldaxr | Stlxr | Ldar | Ldarb | Ldarh | Stlr | Stlrb | Stlrh
                );
            return if touches {
                MemShape::Unmodeled {
                    writes: inst.writes_memory()
                        || is_lse_rmw(op)
                        || is_lse_cas(op)
                        || matches!(op, Stlxr | Stlr | Stlrb | Stlrh),
                }
            } else {
                MemShape::None
            };
        }
    };
    match decoded {
        Some(access) => MemShape::Access(access),
        None => MemShape::Unmodeled {
            writes: inst.writes_memory(),
        },
    }
}

fn is_call_inst(inst: &MachInst) -> bool {
    use AArch64Opcode::*;
    inst.is_call() || matches!(inst.opcode, Bl | BL | Blr | BLR | TlsDescCall | BlrTlsdesc)
}

fn is_function_exit(inst: &MachInst) -> bool {
    inst.is_return() || matches!(inst.opcode, AArch64Opcode::Ret | AArch64Opcode::TailCall)
}

/// The recognized static stack-probe loop: one or more `SUB SP,SP,#a`, one
/// `STR XZR,[SP]`, `SUBS Xc,Xc,#1`, and a conditional back-branch, with the
/// block itself among exactly two successors. Returns the SP bytes allocated
/// per iteration and the counter location.
fn probe_loop_shape(func: &MachFunction, block: usize) -> Option<(i64, usize)> {
    let b = func.blocks.get(block)?;
    if b.succs.len() != 2 || !b.succs.iter().any(|s| s.0 as usize == block) {
        return None;
    }
    let insts: Vec<&MachInst> = b
        .insts
        .iter()
        .map(|id| func.insts.get(id.0 as usize))
        .collect::<Option<Vec<_>>>()?
        .into_iter()
        .filter(|inst| !inst.is_pseudo())
        .collect();
    let is_sp = |op: &MachOperand| base_op(op) == Some(BaseOp::Sp);
    let mut step = 0i64;
    let mut i = 0;
    while let Some(inst) = insts.get(i) {
        match (inst.opcode, inst.operands.as_slice()) {
            (AArch64Opcode::SubRI, [dst, src, MachOperand::Imm(a)])
                if is_sp(dst) && is_sp(src) && *a > 0 =>
            {
                step = step.checked_add(*a)?;
                i += 1;
            }
            _ => break,
        }
    }
    if step == 0 {
        return None;
    }
    let probe = insts.get(i)?;
    let MemShape::Access(access) = decode_memory(probe) else {
        return None;
    };
    if probe.opcode != AArch64Opcode::StrRI
        || access.base != BaseOp::Sp
        || access.disp != 0
        || !access.data.iter().all(|d| is_zero_reg(*d))
    {
        return None;
    }
    let counter = insts.get(i + 1)?;
    let (
        AArch64Opcode::SubsRI,
        [
            MachOperand::PReg(d),
            MachOperand::PReg(s),
            MachOperand::Imm(1),
        ],
    ) = (counter.opcode, counter.operands.as_slice())
    else {
        return None;
    };
    if d != s || !is_gpr64(*d) {
        return None;
    }
    let branch = insts.get(i + 2)?;
    if branch.opcode != AArch64Opcode::BCond || insts.len() != i + 3 {
        return None;
    }
    Some((step, reg_loc(*d)?))
}

/// How a register read uses its value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReadContext {
    /// Computed with, used as an address, passed or returned: fully checked.
    Consume,
    /// Stored into a frame cell by a non-spill store (a save is allowed).
    FrameSave,
    /// Only moved (register copy or spill store): checked where consumed.
    Move,
}

/// `(dst, src, exact)` of a register-to-register copy. `exact` copies keep the
/// value identity (64-bit GPR moves); inexact ones (32-bit or FP moves) keep
/// only its taints.
fn copy_operands(inst: &MachInst) -> Option<(PReg, PReg, bool)> {
    use AArch64Opcode::*;
    let [MachOperand::PReg(dst), MachOperand::PReg(src)] = inst.operands.as_slice() else {
        return None;
    };
    if is_sp_reg(*dst) || is_sp_reg(*src) || is_zero_reg(*src) {
        return None;
    }
    match inst.opcode {
        MovR | MOVXrr if is_gpr64(*dst) && is_gpr64(*src) => Some((*dst, *src, true)),
        MovR | MOVWrr | MOVXrr => Some((*dst, *src, false)),
        FmovFprFpr => Some((*dst, *src, false)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Violations, declines, statistics
// ---------------------------------------------------------------------------

/// Which frame property broke.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpillSlotViolationKind {
    /// A reload reads bytes no spill store wrote on some path (a dropped or
    /// mismatched spill store; the value is uninitialized this activation).
    ReloadWithoutReachingStore,
    /// A reload reads bytes last written by a non-spill store on some path (a
    /// shifted spill offset landing on a callee-save, local, probe or argument
    /// cell).
    ReloadFromNonSpillStore,
    /// A reload reads bytes a call may have written (a spill cell inside the
    /// outgoing stack-argument area).
    ReloadOfCallClobberedSlot,
    /// A reload reads only spill-stored bytes, but not exactly the byte range
    /// one spill store wrote on every path: its offset is shifted inside or
    /// across spill cells, or its width differs from the store's.
    ReloadMisalignedWithSpillStore,
    /// A call-clobbered volatile register is read before being redefined.
    ClobberedRegisterRead,
    /// A 128-bit (Q-view) read of V8-V15 after a call, with no redefinition of
    /// the register in between: AAPCS64 preserves only its low 64 bits.
    UpperHalfClobberedRead,
    /// A caller's callee-saved register value is consumed (computed with,
    /// used as an address, passed or stored outside the frame) rather than
    /// only moved or saved.
    CallerSavedValueRead,
    /// A callee-saved register or X29 does not hold its entry value at exit.
    CalleeSavedNotRestored,
    /// The return address does not hold its entry value at exit.
    ReturnAddressNotRestored,
    /// SP is not back at the CFA at exit.
    StackPointerNotRestored,
    /// A return (or tail-call argument) lane is call-clobbered or written
    /// after the frame teardown began.
    ReturnLaneClobbered,
    /// A return lane holds a caller's callee-saved value.
    ReturnLaneHoldsCallerValue,
}

impl SpillSlotViolationKind {
    /// Greppable tag for the diagnostic line.
    pub fn tag(self) -> &'static str {
        match self {
            Self::ReloadWithoutReachingStore => "reload-without-reaching-store",
            Self::ReloadFromNonSpillStore => "reload-from-non-spill-store",
            Self::ReloadOfCallClobberedSlot => "reload-of-call-clobbered-slot",
            Self::ReloadMisalignedWithSpillStore => "reload-misaligned-with-spill-store",
            Self::ClobberedRegisterRead => "call-clobbered-register-read",
            Self::UpperHalfClobberedRead => "call-clobbered-upper-half-read",
            Self::CallerSavedValueRead => "caller-callee-saved-value-read",
            Self::CalleeSavedNotRestored => "callee-saved-not-restored",
            Self::ReturnAddressNotRestored => "return-address-not-restored",
            Self::StackPointerNotRestored => "stack-pointer-not-restored",
            Self::ReturnLaneClobbered => "return-lane-clobbered",
            Self::ReturnLaneHoldsCallerValue => "return-lane-holds-caller-value",
        }
    }
}

/// A single frame violation. In ENFORCE mode any one fails the compile.
#[derive(Debug, Clone)]
pub struct SpillSlotViolation {
    /// Which property broke.
    pub kind: SpillSlotViolationKind,
    /// Human-readable diagnostic (block / instruction / location).
    pub detail: String,
}

/// Why the net declined to model a stream. Declining reports nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclineReason {
    /// A surviving `VReg`, `StackSlot`, `FrameIndex` or `IncomingArg` operand.
    NonFinalStream,
    /// An out-of-range entry, successor or instruction id.
    MalformedCfg,
    /// A flagged spill access that is not a plain constant-offset scalar access.
    UnmodeledSpillAccess,
    /// A flagged spill access whose base is not a known frame address.
    UnresolvedSpillAddress,
    /// More than [`MAX_CELLS`] tracked cells at one program point.
    TooManyCells,
    /// `blocks x tracked stores` above the state-memory bound.
    TooLarge,
    /// The fixpoint exceeded its visit bound.
    NonConvergence,
}

impl DeclineReason {
    /// Every reason, in counter order.
    pub const ALL: [DeclineReason; 7] = [
        Self::NonFinalStream,
        Self::MalformedCfg,
        Self::UnmodeledSpillAccess,
        Self::UnresolvedSpillAddress,
        Self::TooManyCells,
        Self::TooLarge,
        Self::NonConvergence,
    ];

    /// Greppable tag.
    pub fn tag(self) -> &'static str {
        match self {
            Self::NonFinalStream => "non-final-stream",
            Self::MalformedCfg => "malformed-cfg",
            Self::UnmodeledSpillAccess => "unmodeled-spill-access",
            Self::UnresolvedSpillAddress => "unresolved-spill-address",
            Self::TooManyCells => "too-many-cells",
            Self::TooLarge => "too-large",
            Self::NonConvergence => "non-convergence",
        }
    }

    fn index(self) -> usize {
        Self::ALL.iter().position(|r| *r == self).unwrap_or(0)
    }
}

/// What the net examined in one analyzed stream.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FrameNetStats {
    /// Flagged spill stores modeled.
    pub spill_stores: u32,
    /// Flagged spill reloads checked.
    pub spill_reloads_checked: u32,
    /// Function exits (`RET`/tail call) checked.
    pub exits_checked: u32,
    /// Calls modeled as clobber points.
    pub calls: u32,
    /// Static probe loops summarized.
    pub probe_loops: u32,
    /// Frame-address writes in a form not decoded exactly (conservatively
    /// marked as written).
    pub unmodeled_frame_writes: u32,
    /// SP moved somewhere in the function (a framed function).
    pub framed: bool,
}

/// Result of [`analyze_frame`].
#[derive(Debug, Clone)]
pub enum FrameNetOutcome {
    /// The stream was modeled; `violations` may be empty.
    Analyzed {
        violations: Vec<SpillSlotViolation>,
        stats: FrameNetStats,
    },
    /// The stream could not be soundly modeled.
    Declined(DeclineReason),
}

// ---------------------------------------------------------------------------
// The analysis
// ---------------------------------------------------------------------------

struct Analyzer<'a> {
    func: &'a MachFunction,
    probe_loops: Vec<Option<(i64, usize)>>,
    /// Blocks entered by unwinding (landing pads).
    landing_pads: Vec<bool>,
    /// States right after each call of the block being executed, collected
    /// when the block has a landing-pad successor: unwinding enters the pad
    /// from a call site with the frame intact, not from the block's end.
    post_call_states: Vec<State>,
    collect_post_call: bool,
    /// Checking pass: record violations and statistics.
    checking: bool,
    violations: Vec<SpillSlotViolation>,
    stats: FrameNetStats,
}

type Flow<T> = Result<T, DeclineReason>;

/// The instruction a diagnostic names. Rendered (as `block B inst #P (Opcode)`)
/// only when a report is recorded, not once per executed instruction.
#[derive(Clone, Copy)]
struct Site {
    block: usize,
    pos: usize,
    opcode: AArch64Opcode,
}

impl std::fmt::Display for Site {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "block {} inst #{} ({:?})",
            self.block, self.pos, self.opcode
        )
    }
}

impl<'a> Analyzer<'a> {
    /// Record a violation in the checking pass. The detail is formatted only
    /// when it is recorded: the fixpoint pass runs the same transfer functions
    /// over unconverged states and discards every report.
    fn report(&mut self, kind: SpillSlotViolationKind, detail: std::fmt::Arguments<'_>) {
        if self.checking && self.violations.len() < MAX_REPORTS {
            self.violations.push(SpillSlotViolation {
                kind,
                detail: detail.to_string(),
            });
        }
    }

    fn operand_value(state: &State, op: &MachOperand) -> Option<AbsVal> {
        match op {
            MachOperand::Special(SpecialReg::SP) => Some(state.sp_value()),
            MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR) => {
                Some(AbsVal::new(Val::Const(0)))
            }
            MachOperand::PReg(p) if is_sp_reg(*p) => Some(state.sp_value()),
            MachOperand::PReg(p) if is_zero_reg(*p) => Some(AbsVal::new(Val::Const(0))),
            MachOperand::PReg(p) => reg_loc(*p).map(|loc| state.regs[loc]),
            MachOperand::Imm(v) => Some(AbsVal::new(Val::Const(*v))),
            _ => None,
        }
    }

    fn base_value(state: &State, base: BaseOp) -> Option<i64> {
        match base {
            BaseOp::Sp => state.sp,
            BaseOp::Reg(p) => reg_loc(p).and_then(|loc| state.regs[loc].frame()),
        }
    }

    /// Value of an ALU definition of operand 0, for the forms that carry
    /// frame addresses or constants.
    fn alu_value(state: &State, inst: &MachInst) -> Val {
        use AArch64Opcode::*;
        let ops = inst.operands.as_slice();
        let Some(dst) = ops.first() else {
            return Val::Opaque;
        };
        let dst_is_x = match dst {
            MachOperand::PReg(p) => is_gpr64(*p) || is_sp_reg(*p),
            MachOperand::Special(SpecialReg::SP) => true,
            _ => false,
        };
        let dst_is_w = matches!(dst, MachOperand::PReg(p) if is_gpr32(*p));
        let mask = |v: i64| -> i64 { if dst_is_w { v & 0xffff_ffff } else { v } };
        let value = |i: usize| ops.get(i).and_then(|op| Self::operand_value(state, op));
        match inst.opcode {
            AddRI | SubRI | AddRIShift12 if dst_is_x && ops.len() == 3 => {
                let (Some(src), Some(MachOperand::Imm(imm))) = (value(1), ops.get(2)) else {
                    return Val::Opaque;
                };
                let imm = if inst.opcode == AddRIShift12 {
                    imm.checked_shl(12).unwrap_or(i64::MAX)
                } else {
                    *imm
                };
                let delta = if inst.opcode == SubRI {
                    match imm.checked_neg() {
                        Some(negated) => negated,
                        None => return Val::Opaque,
                    }
                } else {
                    imm
                };
                match src.val {
                    Val::Frame(c) => c.checked_add(delta).map_or(Val::Opaque, Val::Frame),
                    Val::Const(k) => Val::Const(k.wrapping_add(delta)),
                    _ => Val::Opaque,
                }
            }
            AddRR | SubRR if dst_is_x && ops.len() == 3 => {
                let (Some(a), Some(b)) = (value(1), value(2)) else {
                    return Val::Opaque;
                };
                let sub = inst.opcode == SubRR;
                match (a.val, b.val, sub) {
                    (Val::Frame(c), Val::Const(k), false)
                    | (Val::Const(k), Val::Frame(c), false) => {
                        c.checked_add(k).map_or(Val::Opaque, Val::Frame)
                    }
                    (Val::Frame(c), Val::Const(k), true) => {
                        c.checked_sub(k).map_or(Val::Opaque, Val::Frame)
                    }
                    (Val::Const(x), Val::Const(y), false) => Val::Const(x.wrapping_add(y)),
                    (Val::Const(x), Val::Const(y), true) => Val::Const(x.wrapping_sub(y)),
                    (Val::Frame(x), Val::Frame(y), true) => Val::Const(x.wrapping_sub(y)),
                    _ => Val::Opaque,
                }
            }
            Movz | MovI | MOVZXi | MOVZWi if dst_is_x || dst_is_w => {
                let Some(MachOperand::Imm(imm)) = ops.get(1) else {
                    return Val::Opaque;
                };
                let shift = match ops.get(2) {
                    Some(MachOperand::Imm(s)) => *s,
                    None => 0,
                    _ => return Val::Opaque,
                };
                if !(0..64).contains(&shift) {
                    return Val::Opaque;
                }
                Val::Const(mask((*imm & 0xffff) << shift))
            }
            Movn if dst_is_x || dst_is_w => {
                let Some(MachOperand::Imm(imm)) = ops.get(1) else {
                    return Val::Opaque;
                };
                let shift = match ops.get(2) {
                    Some(MachOperand::Imm(s)) => *s,
                    None => 0,
                    _ => return Val::Opaque,
                };
                if !(0..64).contains(&shift) {
                    return Val::Opaque;
                }
                Val::Const(mask(!((*imm & 0xffff) << shift)))
            }
            Movk if dst_is_x || dst_is_w => {
                let (Some(prev), Some(MachOperand::Imm(imm))) = (value(0), ops.get(1)) else {
                    return Val::Opaque;
                };
                let shift = match ops.get(2) {
                    Some(MachOperand::Imm(s)) => *s,
                    None => 0,
                    _ => return Val::Opaque,
                };
                let Val::Const(prev) = prev.val else {
                    return Val::Opaque;
                };
                if !(0..64).contains(&shift) {
                    return Val::Opaque;
                }
                let field = 0xffffi64 << shift;
                Val::Const(mask((prev & !field) | ((*imm & 0xffff) << shift)))
            }
            MovR | MOVXrr if dst_is_x && ops.len() == 2 => match value(1).map(|v| v.val) {
                Some(v @ (Val::Frame(_) | Val::Const(_))) => v,
                _ => Val::Opaque,
            },
            _ => Val::Opaque,
        }
    }

    /// Register reads of `inst` that consume a value, with the checks each
    /// one is subject to. A register copy only moves its source (the copy's
    /// destination inherits the value and its taints, and is checked where it
    /// is consumed); the data register of a flagged spill store likewise only
    /// moves its value into the spill cell. The data register of any other
    /// store to a resolved frame address may be a caller's callee-saved value
    /// (the prologue save) but not a call-clobbered one.
    fn checked_reads(
        state: &State,
        inst: &MachInst,
        shape: &MemShape,
        exit: bool,
    ) -> Vec<(PReg, ReadContext)> {
        let roles = crate::post_ra_reaching_def::operand_roles(inst);
        let copy_source = copy_operands(inst).map(|(_, src, _)| src);
        let (spill_data, frame_data): (Vec<PReg>, Vec<PReg>) = match shape {
            MemShape::Access(access)
                if !access.is_load && Self::base_value(state, access.base).is_some() =>
            {
                if inst.flags.is_spill_slot_access() {
                    (access.data.clone(), Vec::new())
                } else {
                    (Vec::new(), access.data.clone())
                }
            }
            _ => (Vec::new(), Vec::new()),
        };
        let mut reads = Vec::new();
        for (pos, operand) in inst.operands.iter().enumerate() {
            let role = roles
                .get(pos)
                .copied()
                .unwrap_or(trust_cg_opt::effects::OperandRole::Use);
            match operand {
                MachOperand::PReg(p) if role.is_use() && !is_sp_reg(*p) && !is_zero_reg(*p) => {
                    if exit {
                        // The return target is checked as the return address.
                        continue;
                    }
                    let context = if (copy_source == Some(*p) && pos == 1) || spill_data.contains(p)
                    {
                        ReadContext::Move
                    } else if frame_data.contains(p) {
                        ReadContext::FrameSave
                    } else {
                        ReadContext::Consume
                    };
                    reads.push((*p, context));
                }
                MachOperand::MemOp { base, .. } if !is_sp_reg(*base) => {
                    reads.push((*base, ReadContext::Consume));
                }
                _ => {}
            }
        }
        if !exit {
            for &p in inst.implicit_uses {
                reads.push((p, ReadContext::Consume));
            }
        }
        reads
    }

    fn check_reads(&mut self, state: &State, reads: &[(PReg, ReadContext)], at: Site) {
        for &(reg, context) in reads {
            // Even a move of the full 128 bits carries the clobbered half.
            if state.upper_clobbered & q_view_upper_bit(reg) != 0 {
                self.report(
                    SpillSlotViolationKind::UpperHalfClobberedRead,
                    format_args!(
                        "{at}: reads all 128 bits of {reg}, whose upper 64 bits a call left \
                         clobbered on some path (AAPCS64 preserves only the low half of \
                         V8-V15; a 128-bit value live across a call must be spilled)"
                    ),
                );
            }
            if context == ReadContext::Move {
                continue;
            }
            let Some(loc) = reg_loc(reg) else {
                continue;
            };
            let value = state.regs[loc];
            if value.taint & T_CALL_CLOBBERED != 0 {
                self.report(
                    SpillSlotViolationKind::ClobberedRegisterRead,
                    format_args!(
                        "{at}: consumes {} ({reg}) which a call left clobbered on some path (a \
                         caller-saved value was not reloaded, or its reload targets another register)",
                        loc_name(loc)
                    ),
                );
            }
            if context == ReadContext::Consume && value.may_hold_callers_callee_saved() {
                self.report(
                    SpillSlotViolationKind::CallerSavedValueRead,
                    format_args!(
                        "{at}: consumes {} ({reg}) which may still hold the caller's callee-saved \
                         value (it may only be moved or saved, never computed with)",
                        loc_name(loc)
                    ),
                );
            }
        }
    }

    fn check_exit(&mut self, state: &State, inst: &MachInst, at: Site) {
        self.stats.exits_checked += 1;
        if let Some(sp) = state.sp
            && sp != 0
        {
            self.report(
                SpillSlotViolationKind::StackPointerNotRestored,
                format_args!("{at}: SP is CFA{sp:+} at function exit, not the CFA"),
            );
        }
        for loc in (19..=29).chain(40..=47) {
            if !state.regs[loc].is_entry_of(loc) {
                self.report(
                    SpillSlotViolationKind::CalleeSavedNotRestored,
                    format_args!(
                        "{at}: callee-saved {} does not hold its entry value on every path to \
                         the exit (missing, dropped or misdirected save/restore)",
                        loc_name(loc)
                    ),
                );
            }
        }
        let target_loc = inst
            .operands
            .iter()
            .find_map(|op| match op {
                MachOperand::PReg(p) if inst.opcode == AArch64Opcode::Ret => reg_loc(*p),
                _ => None,
            })
            .unwrap_or(LR_LOC);
        if !state.regs[target_loc].is_entry_of(LR_LOC) {
            self.report(
                SpillSlotViolationKind::ReturnAddressNotRestored,
                format_args!(
                    "{at}: the return address in {} is not the entry link register value",
                    loc_name(target_loc)
                ),
            );
        }
        for &lane in inst.implicit_uses {
            let Some(loc) = reg_loc(lane) else {
                continue;
            };
            let value = state.regs[loc];
            if value.taint & T_CALL_CLOBBERED != 0 {
                self.report(
                    SpillSlotViolationKind::ReturnLaneClobbered,
                    format_args!("{at}: return/argument lane {lane} is call-clobbered at the exit"),
                );
            }
            if value.taint & T_EPILOGUE != 0 {
                self.report(
                    SpillSlotViolationKind::ReturnLaneClobbered,
                    format_args!(
                        "{at}: return/argument lane {lane} is written after the frame \
                         teardown began"
                    ),
                );
            }
            if value.may_hold_callers_callee_saved() {
                self.report(
                    SpillSlotViolationKind::ReturnLaneHoldsCallerValue,
                    format_args!(
                        "{at}: return/argument lane {lane} may hold a caller's callee-saved value"
                    ),
                );
            }
        }
    }

    fn set_sp(state: &mut State, new_sp: Option<i64>) {
        if let Some(new) = new_sp
            && state.sp.is_none_or(|old| new > old)
        {
            state.torn_down = true;
        }
        state.sp = new_sp;
    }

    fn def_taint(state: &State) -> u8 {
        if state.torn_down { T_EPILOGUE } else { 0 }
    }

    fn exec_access(
        &mut self,
        state: &mut State,
        inst: &MachInst,
        access: &Access,
        pending_args: &mut Vec<(i64, i64)>,
        at: Site,
    ) -> Flow<()> {
        let spill = inst.flags.is_spill_slot_access();
        let base = Self::base_value(state, access.base);
        if spill && (access.data.len() != 1 || access.writeback.is_some()) {
            return Err(DeclineReason::UnmodeledSpillAccess);
        }
        let Some(base_addr) = base else {
            if spill {
                return Err(DeclineReason::UnresolvedSpillAddress);
            }
            // Not a known frame address: an object or outgoing-argument store,
            // private-cell assumption. Loads and writeback produce opaque values.
            let taint = Self::def_taint(state);
            if access.is_load {
                for data in &access.data {
                    if let Some(loc) = reg_loc(*data) {
                        state.regs[loc] = AbsVal::opaque(taint);
                    }
                }
            }
            if access.writeback.is_some() {
                match access.base {
                    BaseOp::Sp => Self::set_sp(state, None),
                    BaseOp::Reg(p) => {
                        if let Some(loc) = reg_loc(p) {
                            state.regs[loc] = AbsVal::opaque(taint);
                        }
                    }
                }
            }
            return Ok(());
        };
        let addr = base_addr
            .checked_add(access.disp)
            .ok_or(DeclineReason::TooLarge)?;
        for (i, data) in access.data.iter().enumerate() {
            // Checked so extreme (malformed) frame addresses decline instead of
            // overflowing; `a + width` is then representable for `load`/`store`.
            let a = (i as i64)
                .checked_mul(access.width)
                .and_then(|delta| addr.checked_add(delta))
                .filter(|a| a.checked_add(access.width).is_some())
                .ok_or(DeclineReason::TooLarge)?;
            if access.is_load {
                let (kinds, exact) = state.load(a, access.width);
                if spill {
                    self.stats.spill_reloads_checked += u32::from(self.checking);
                    if kinds & K_UNINIT != 0 {
                        self.report(
                            SpillSlotViolationKind::ReloadWithoutReachingStore,
                            format_args!(
                                "{at}: reload of spill cell CFA{a:+} ({} bytes) has no reaching \
                                 spill store on some path (dropped or mismatched spill store)",
                                access.width
                            ),
                        );
                    }
                    if kinds & K_OTHER != 0 {
                        self.report(
                            SpillSlotViolationKind::ReloadFromNonSpillStore,
                            format_args!(
                                "{at}: reload of spill cell CFA{a:+} ({} bytes) reads bytes \
                                 written by a non-spill store on some path (spill offset collides \
                                 with a save, local, probe or argument cell)",
                                access.width
                            ),
                        );
                    }
                    if kinds & K_CALLEE != 0 {
                        self.report(
                            SpillSlotViolationKind::ReloadOfCallClobberedSlot,
                            format_args!(
                                "{at}: reload of spill cell CFA{a:+} ({} bytes) reads bytes a call \
                                 may have written (spill cell inside the outgoing argument area)",
                                access.width
                            ),
                        );
                    }
                    if kinds == K_SPILL && exact.is_none() {
                        self.report(
                            SpillSlotViolationKind::ReloadMisalignedWithSpillStore,
                            format_args!(
                                "{at}: reload of CFA{a:+} ({} bytes) does not read exactly the \
                                 bytes one spill store wrote on every path (reload offset shifted \
                                 inside or across spill cells, or a store/reload width mismatch)",
                                access.width
                            ),
                        );
                    }
                }
                let restored = exact.filter(|v| v.is_frame_record_entry());
                if restored.is_some() {
                    state.torn_down = true;
                }
                let value = match (restored, exact) {
                    (Some(v), _) => v,
                    (None, Some(v)) if spill => AbsVal {
                        val: v.val,
                        taint: v.taint | Self::def_taint(state),
                    },
                    _ => AbsVal::opaque(Self::def_taint(state)),
                };
                if let Some(loc) = reg_loc(*data) {
                    state.regs[loc] = value;
                }
            } else {
                let value = if is_zero_reg(*data) {
                    AbsVal::new(Val::Const(0))
                } else {
                    reg_loc(*data).map_or(AbsVal::opaque(0), |loc| state.regs[loc])
                };
                let kinds = if spill { K_SPILL } else { K_OTHER };
                if spill {
                    self.stats.spill_stores += u32::from(self.checking);
                }
                state.store(a, access.width, kinds, value);
                if state.cells.len() > MAX_CELLS {
                    return Err(DeclineReason::TooManyCells);
                }
                if !spill
                    && access.base == BaseOp::Sp
                    && a >= base_addr
                    && !is_zero_reg(*data)
                    && !value.is_frame_record_entry()
                {
                    pending_args.push((a, a + access.width));
                }
            }
        }
        if let Some(amount) = access.writeback {
            let new_base = base_addr.checked_add(amount);
            match access.base {
                BaseOp::Sp => Self::set_sp(state, new_base),
                BaseOp::Reg(p) => {
                    if let Some(loc) = reg_loc(p) {
                        state.regs[loc] = match new_base {
                            Some(c) => AbsVal {
                                val: Val::Frame(c),
                                taint: Self::def_taint(state),
                            },
                            None => AbsVal::opaque(Self::def_taint(state)),
                        };
                    }
                }
            }
        }
        Ok(())
    }

    fn exec_call(
        &mut self,
        state: &mut State,
        inst: &MachInst,
        pending_args: &mut Vec<(i64, i64)>,
    ) {
        self.stats.calls += u32::from(self.checking);
        state.upper_clobbered = u8::MAX;
        let taint = Self::def_taint(state);
        for (loc, register) in state.regs[..LOCS].iter_mut().enumerate() {
            if is_call_result_loc(loc) {
                *register = AbsVal::opaque(taint);
            } else if is_call_clobber_loc(loc) {
                *register = AbsVal::opaque(T_CALL_CLOBBERED | taint);
            }
        }
        for &p in inst.implicit_defs {
            if let Some(loc) = reg_loc(p)
                && !is_call_result_loc(loc)
                && !is_call_clobber_loc(loc)
            {
                state.regs[loc] = AbsVal::opaque(taint);
            }
        }
        // The callee owns its incoming stack arguments and may overwrite them:
        // every SP-relative non-save store this block made since the previous
        // call is a possible stack argument.
        if let Some(sp) = state.sp {
            for &(lo, hi) in pending_args.iter().filter(|(lo, _)| *lo >= sp) {
                state.mark_written(lo, hi, K_CALLEE);
            }
        }
        pending_args.clear();
    }

    /// Execute one block from `state`; in the checking pass, record violations.
    fn exec_block(&mut self, block: usize, state: &mut State) -> Flow<()> {
        let func = self.func;
        let bid = block;
        if let Some((step, counter)) = self.probe_loops[block] {
            // Summarize the counted probe loop: SP drops by `n * step`.
            self.stats.probe_loops += u32::from(self.checking);
            let count = match state.regs[counter].val {
                Val::Const(n) if n >= 1 => Some(n),
                _ => None,
            };
            state.sp = match (state.sp, count) {
                (Some(sp), Some(n)) => n.checked_mul(step).and_then(|total| sp.checked_sub(total)),
                _ => None,
            };
            state.regs[counter] = AbsVal::new(Val::Const(0));
            return Ok(());
        }
        let mut pending_args: Vec<(i64, i64)> = Vec::new();
        // The epilogue frame lowering emits is contiguous and ends its block
        // (before `ret`, a tail call, or the branch of a shrink-wrapped frame
        // edge into a shared return). Code in a later block runs frameless by
        // design (shrink-wrapping), so teardown is tracked within a block.
        state.torn_down = false;
        for (pos, &inst_id) in func.blocks[block].insts.iter().enumerate() {
            let inst = func
                .insts
                .get(inst_id.0 as usize)
                .ok_or(DeclineReason::MalformedCfg)?;
            if inst.is_pseudo() {
                continue;
            }
            // Diagnostics are only rendered for a recorded report.
            let at = Site {
                block: bid,
                pos,
                opcode: inst.opcode,
            };
            let exit = is_function_exit(inst);
            let call = is_call_inst(inst);
            let shape = if exit || call || inst.is_branch() {
                MemShape::None
            } else {
                decode_memory(inst)
            };
            if inst.flags.is_spill_slot_access() && !matches!(shape, MemShape::Access(_)) {
                return Err(DeclineReason::UnmodeledSpillAccess);
            }
            if self.checking {
                let reads = Self::checked_reads(state, inst, &shape, exit);
                self.check_reads(state, &reads, at);
                if exit {
                    self.check_exit(state, inst, at);
                }
            }
            if call {
                self.exec_call(state, inst, &mut pending_args);
                if self.collect_post_call {
                    self.post_call_states.push(state.clone());
                }
                continue;
            }
            // Clearing bits of a zero mask is a no-op, and `written_upper_bits`
            // derives the operand roles only when a V8-V15 register appears.
            if state.upper_clobbered != 0 {
                state.upper_clobbered &= !Self::written_upper_bits(inst, &shape);
            }
            match &shape {
                MemShape::Access(access) => {
                    self.exec_access(state, inst, access, &mut pending_args, at)?;
                }
                MemShape::Unmodeled { writes } => {
                    if *writes {
                        for (lo, hi) in Self::unmodeled_write_ranges(state, inst) {
                            self.stats.unmodeled_frame_writes += u32::from(self.checking);
                            state.mark_written(lo, hi, K_OTHER);
                        }
                    }
                    self.exec_register_defs(state, inst);
                }
                MemShape::None => {
                    self.exec_register_defs(state, inst);
                }
            }
            for &p in inst.implicit_defs {
                if is_sp_reg(p) {
                    Self::set_sp(state, None);
                } else if let Some(loc) = reg_loc(p) {
                    state.regs[loc] = AbsVal::opaque(Self::def_taint(state));
                }
            }
            if self.checking && state.sp != Some(0) {
                self.stats.framed = true;
            }
        }
        Ok(())
    }

    /// V8-V15 bits of [`State::upper_clobbered`] a non-call instruction
    /// writes: explicit definitions, loaded data registers and implicit
    /// definitions, in any view.
    fn written_upper_bits(inst: &MachInst, shape: &MemShape) -> u8 {
        let mut bits = 0u8;
        // Only a V8-V15 operand can contribute a bit, so the operand roles
        // (an allocation per instruction) are derived only when one is present;
        // the result is the same either way.
        if inst
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::PReg(p) if fpr_upper_bit(*p) != 0))
        {
            let roles = crate::post_ra_reaching_def::operand_roles(inst);
            for (pos, operand) in inst.operands.iter().enumerate() {
                if let MachOperand::PReg(p) = operand
                    && roles.get(pos).is_some_and(|role| role.is_def())
                {
                    bits |= fpr_upper_bit(*p);
                }
            }
        }
        if let MemShape::Access(access) = shape
            && access.is_load
        {
            for &data in &access.data {
                bits |= fpr_upper_bit(data);
            }
        }
        for &p in inst.implicit_defs {
            bits |= fpr_upper_bit(p);
        }
        bits
    }

    /// Frame byte ranges an undecoded store may write, from its address
    /// operand. Register-offset stores through a frame base index into an
    /// object (a local array) and are covered by the private-cell assumption.
    fn unmodeled_write_ranges(state: &State, inst: &MachInst) -> Vec<(i64, i64)> {
        use AArch64Opcode::*;
        let ops = inst.operands.as_slice();
        let frame_at = |i: usize| -> Option<i64> {
            ops.get(i)
                .and_then(|op| Self::operand_value(state, op))
                .and_then(AbsVal::frame)
        };
        let width_of = |i: usize| -> i64 {
            match ops.get(i) {
                Some(MachOperand::PReg(p)) => reg_bytes(*p).unwrap_or(16),
                _ => 16,
            }
        };
        let exact = |addr: Option<i64>, width: i64| -> Vec<(i64, i64)> {
            addr.map(|a| vec![(a, a.saturating_add(width))])
                .unwrap_or_default()
        };
        match inst.opcode {
            StrRO | StrbRO | StrhRO => Vec::new(),
            Stlr => exact(frame_at(1), width_of(0)),
            Stlrb => exact(frame_at(1), 1),
            Stlrh => exact(frame_at(1), 2),
            Stlxr => exact(frame_at(2), width_of(1)),
            op if is_lse_rmw(op) || is_lse_cas(op) => exact(frame_at(2), width_of(0)),
            _ => {
                let roles = crate::post_ra_reaching_def::operand_roles(inst);
                let mut ranges = Vec::new();
                for (pos, op) in ops.iter().enumerate() {
                    let addr = match op {
                        MachOperand::MemOp { base, offset } => {
                            Self::base_value(state, mem_base(*base))
                                .and_then(|c| c.checked_add(*offset))
                        }
                        _ if roles
                            .get(pos)
                            .is_some_and(|r| *r == trust_cg_opt::effects::OperandRole::DefUse) =>
                        {
                            frame_at(pos)
                        }
                        _ => None,
                    };
                    if let Some(a) = addr {
                        ranges.push((a, a.saturating_add(16)));
                    }
                }
                ranges
            }
        }
    }

    /// Explicit register definitions of a non-call instruction that is not a
    /// decoded memory access.
    fn exec_register_defs(&mut self, state: &mut State, inst: &MachInst) {
        let taint = Self::def_taint(state);
        if let Some((dst, src, exact)) = copy_operands(inst)
            && let (Some(dst_loc), Some(src_loc)) = (reg_loc(dst), reg_loc(src))
        {
            // A copy preserves the value (and its taints); it is not a new
            // definition, even after the teardown began.
            let source = state.regs[src_loc];
            state.regs[dst_loc] = if exact {
                source
            } else {
                let caller = if source.may_hold_callers_callee_saved() {
                    T_CALLER_SAVED
                } else {
                    0
                };
                AbsVal::opaque(source.taint | caller)
            };
            return;
        }
        let roles = crate::post_ra_reaching_def::operand_roles(inst);
        let computed = Self::alu_value(state, inst);
        for (pos, operand) in inst.operands.iter().enumerate() {
            if !roles.get(pos).is_some_and(|role| role.is_def()) {
                continue;
            }
            let value = if pos == 0 { computed } else { Val::Opaque };
            match operand {
                MachOperand::Special(SpecialReg::SP) => {
                    let new_sp = match value {
                        Val::Frame(c) => Some(c),
                        _ => None,
                    };
                    Self::set_sp(state, new_sp);
                }
                MachOperand::PReg(p) if is_sp_reg(*p) => {
                    let new_sp = match value {
                        Val::Frame(c) => Some(c),
                        _ => None,
                    };
                    Self::set_sp(state, new_sp);
                }
                MachOperand::PReg(p) => {
                    if let Some(loc) = reg_loc(*p) {
                        state.regs[loc] = AbsVal { val: value, taint };
                    }
                }
                MachOperand::MemOp { base, .. } => {
                    // Writeback base of an undecoded form.
                    if is_sp_reg(*base) {
                        Self::set_sp(state, None);
                    } else if let Some(loc) = reg_loc(*base) {
                        state.regs[loc] = AbsVal::opaque(taint);
                    }
                }
                _ => {}
            }
        }
    }
}

/// A stream is in final form only if no operand is a pre-regalloc `VReg` or a
/// pre-frame-lowering placeholder.
fn stream_is_final(func: &MachFunction) -> Flow<()> {
    for block in &func.blocks {
        for &inst_id in &block.insts {
            let inst = func
                .insts
                .get(inst_id.0 as usize)
                .ok_or(DeclineReason::MalformedCfg)?;
            if inst.operands.iter().any(|operand| {
                matches!(
                    operand,
                    MachOperand::VReg(_)
                        | MachOperand::StackSlot(_)
                        | MachOperand::FrameIndex(_)
                        | MachOperand::IncomingArg(_)
                )
            }) {
                return Err(DeclineReason::NonFinalStream);
            }
        }
    }
    Ok(())
}

fn analyze_inner(func: &MachFunction) -> Flow<(Vec<SpillSlotViolation>, FrameNetStats)> {
    stream_is_final(func)?;
    let nblocks = func.blocks.len();
    if nblocks == 0 {
        return Ok((Vec::new(), FrameNetStats::default()));
    }
    let entry = func.entry.0 as usize;
    if entry >= nblocks {
        return Err(DeclineReason::MalformedCfg);
    }
    for block in &func.blocks {
        if block.succs.iter().any(|s| s.0 as usize >= nblocks) {
            return Err(DeclineReason::MalformedCfg);
        }
    }
    let stores = func
        .insts
        .iter()
        .filter(|inst| inst.writes_memory())
        .count()
        .max(1);
    if nblocks.saturating_mul(stores.saturating_mul(2) + LOCS) > MAX_STATE_WORK {
        return Err(DeclineReason::TooLarge);
    }
    let probe_loops: Vec<Option<(i64, usize)>> =
        (0..nblocks).map(|b| probe_loop_shape(func, b)).collect();
    let mut landing_pads = vec![false; nblocks];
    let eh = &func.eh_metadata;
    for block in eh.landing_pads.iter().map(|pad| pad.block).chain(
        eh.call_sites
            .iter()
            .filter_map(|site| site.landing_pad_block),
    ) {
        if let Some(flag) = landing_pads.get_mut(block.0 as usize) {
            *flag = true;
        }
    }
    let mut analyzer = Analyzer {
        func,
        probe_loops,
        landing_pads,
        post_call_states: Vec::new(),
        collect_post_call: false,
        checking: false,
        violations: Vec::new(),
        stats: FrameNetStats::default(),
    };

    // Forward fixpoint over the successor graph. A probe loop's self edge is
    // summarized by its block transfer and not propagated.
    let mut in_states: Vec<Option<State>> = vec![None; nblocks];
    in_states[entry] = Some(State::entry());
    let mut queued = vec![false; nblocks];
    let mut worklist = VecDeque::from([entry]);
    queued[entry] = true;
    let max_visits = nblocks.saturating_mul(256).saturating_add(1024);
    let mut visits = 0usize;
    while let Some(block) = worklist.pop_front() {
        queued[block] = false;
        visits += 1;
        if visits > max_visits {
            return Err(DeclineReason::NonConvergence);
        }
        let Some(mut state) = in_states[block].clone() else {
            continue;
        };
        analyzer.collect_post_call = func.blocks[block]
            .succs
            .iter()
            .any(|s| analyzer.landing_pads[s.0 as usize]);
        analyzer.post_call_states.clear();
        analyzer.exec_block(block, &mut state)?;
        // Unwinding enters a landing pad from a call site of this block.
        let unwind_state = analyzer
            .post_call_states
            .iter()
            .skip(1)
            .fold(analyzer.post_call_states.first().cloned(), |acc, next| {
                acc.map(|acc| acc.merge(next))
            });
        let is_probe = analyzer.probe_loops[block].is_some();
        for succ in &func.blocks[block].succs {
            let s = succ.0 as usize;
            if is_probe && s == block {
                continue;
            }
            let outgoing = if analyzer.landing_pads[s] {
                match &unwind_state {
                    Some(unwind) => unwind,
                    // No call in this block can unwind into the pad.
                    None => continue,
                }
            } else {
                &state
            };
            // The join is formed in place: `changed` is exactly whether the
            // joined state differs from the stored one (a first arrival always
            // does), and the cell bound is checked on the joined state as
            // before; exceeding it declines the whole stream.
            let (changed, cells) = match &mut in_states[s] {
                None => {
                    let first = outgoing.clone();
                    let cells = first.cells.len();
                    in_states[s] = Some(first);
                    (true, cells)
                }
                Some(old) => {
                    let changed = old.join_from(outgoing);
                    (changed, old.cells.len())
                }
            };
            if cells > MAX_CELLS {
                return Err(DeclineReason::TooManyCells);
            }
            if changed && !queued[s] {
                queued[s] = true;
                worklist.push_back(s);
            }
        }
    }

    // Checking pass over every reachable block from its converged entry state.
    analyzer.checking = true;
    analyzer.collect_post_call = false;
    for (block, in_state) in in_states.iter().enumerate() {
        let Some(in_state) = in_state else {
            continue;
        };
        let mut state = in_state.clone();
        if in_state.sp != Some(0) {
            analyzer.stats.framed = true;
        }
        analyzer.exec_block(block, &mut state)?;
    }
    Ok((analyzer.violations, analyzer.stats))
}

/// Model `func` and check it. Side-effect free (no telemetry).
pub fn analyze_frame(func: &MachFunction) -> FrameNetOutcome {
    match analyze_inner(func) {
        Ok((violations, stats)) => FrameNetOutcome::Analyzed { violations, stats },
        Err(reason) => FrameNetOutcome::Declined(reason),
    }
}

/// The frameless legacy rule. `frame_modeled` says whether the frame model
/// analyzed `func`; only then does the legacy rule leave flagged reloads to it.
fn legacy_violations(func: &MachFunction, frame_modeled: bool) -> Vec<SpillSlotViolation> {
    legacy::analyze(func, frame_modeled)
        .unwrap_or_default()
        .into_iter()
        .map(|(block, pos, opcode, off)| SpillSlotViolation {
            kind: SpillSlotViolationKind::ReloadWithoutReachingStore,
            detail: format!(
                "block {block} inst #{pos} ({opcode:?}): reload from spill slot [SP,#{off}] has no \
                 reaching store on every path from entry (dropped/mismatched spill store — the \
                 reloaded value is uninitialized this activation)"
            ),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Mode + telemetry
// ---------------------------------------------------------------------------

/// Default mode for the aarch64 frame net: ENFORCE.
pub const AARCH64_SPILL_SLOT_DEFAULT: PostRegallocRecheckMode = PostRegallocRecheckMode::Enforce;

/// Resolve the active mode from `TCG_AARCH64_POST_RA_SPILL_SLOTS`
/// (`off`|`warn`|`enforce`, or `0`|`1`|`2`), defaulting to
/// [`AARCH64_SPILL_SLOT_DEFAULT`]. The environment knob remains as an explicit
/// diagnostic downgrade/disable escape hatch; absent it, violations fail closed.
pub fn spill_slot_mode() -> PostRegallocRecheckMode {
    match trust_cg_process_env::var("TCG_AARCH64_POST_RA_SPILL_SLOTS").as_deref() {
        Ok("off") | Ok("0") => PostRegallocRecheckMode::Off,
        Ok("enforce") | Ok("2") => PostRegallocRecheckMode::Enforce,
        Ok("warn") | Ok("1") => PostRegallocRecheckMode::Warn,
        _ => AARCH64_SPILL_SLOT_DEFAULT,
    }
}

static VIOLATION_HITS: AtomicU64 = AtomicU64::new(0);
static STREAMS_ANALYZED: AtomicU64 = AtomicU64::new(0);
static STREAMS_DECLINED: AtomicU64 = AtomicU64::new(0);
static FRAMED_ANALYZED: AtomicU64 = AtomicU64::new(0);
static SPILL_RELOADS_CHECKED: AtomicU64 = AtomicU64::new(0);
static EXITS_CHECKED: AtomicU64 = AtomicU64::new(0);
static DECLINES: [AtomicU64; DeclineReason::ALL.len()] =
    [const { AtomicU64::new(0) }; DeclineReason::ALL.len()];

/// Total frame violations observed by this process (soak telemetry).
pub fn spill_slot_hit_count() -> u64 {
    VIOLATION_HITS.load(Ordering::Relaxed)
}

/// (analyzed, declined) stream counts.
pub fn coverage_counts() -> (u64, u64) {
    (
        STREAMS_ANALYZED.load(Ordering::Relaxed),
        STREAMS_DECLINED.load(Ordering::Relaxed),
    )
}

/// Process-wide coverage of [`evaluate`] calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrameNetCoverage {
    /// Streams modeled.
    pub analyzed: u64,
    /// Streams declined (see [`decline_counts`]).
    pub declined: u64,
    /// Modeled streams whose SP moved (framed functions).
    pub framed_analyzed: u64,
    /// Flagged spill reloads checked.
    pub spill_reloads_checked: u64,
    /// Function exits checked.
    pub exits_checked: u64,
}

/// Process-wide coverage of [`evaluate`] calls.
pub fn frame_coverage() -> FrameNetCoverage {
    FrameNetCoverage {
        analyzed: STREAMS_ANALYZED.load(Ordering::Relaxed),
        declined: STREAMS_DECLINED.load(Ordering::Relaxed),
        framed_analyzed: FRAMED_ANALYZED.load(Ordering::Relaxed),
        spill_reloads_checked: SPILL_RELOADS_CHECKED.load(Ordering::Relaxed),
        exits_checked: EXITS_CHECKED.load(Ordering::Relaxed),
    }
}

/// Per-reason decline counts of [`evaluate`] calls in this process.
pub fn decline_counts() -> Vec<(DeclineReason, u64)> {
    DeclineReason::ALL
        .iter()
        .map(|&reason| (reason, DECLINES[reason.index()].load(Ordering::Relaxed)))
        .collect()
}

fn record_violation(function_name: &str, detail: &str, mode: PostRegallocRecheckMode) {
    VIOLATION_HITS.fetch_add(1, Ordering::Relaxed);
    let tag = match mode {
        PostRegallocRecheckMode::Enforce => "[TCG-A64-SPILL-SLOT-FAIL]",
        _ => "[TCG-A64-SPILL-SLOT-WARN]",
    };
    eprintln!("{tag} arch=aarch64 fn={function_name}: {detail}");
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Pure entry point: the violations in `func`, or an EMPTY list for a clean
/// stream OR a stream the frame model declines (the frameless legacy rule
/// still applies). Side-effect free.
pub fn check(func: &MachFunction) -> Vec<SpillSlotViolation> {
    let (mut violations, frame_modeled) = match analyze_frame(func) {
        FrameNetOutcome::Analyzed { violations, .. } => (violations, true),
        FrameNetOutcome::Declined(_) => (Vec::new(), false),
    };
    violations.extend(legacy_violations(func, frame_modeled));
    violations
}

/// Driver: apply the resolved mode.
/// * `Off` -> `None` immediately.
/// * All violations are recorded (telemetry) regardless of mode.
/// * `Enforce` -> the FIRST violation is returned so the caller fails closed;
///   `Warn` -> `None` (telemetry only, no verdict change).
pub fn evaluate(func: &MachFunction, mode: PostRegallocRecheckMode) -> Option<SpillSlotViolation> {
    if mode == PostRegallocRecheckMode::Off {
        return None;
    }
    let outcome = analyze_frame(func);
    let frame_modeled = matches!(outcome, FrameNetOutcome::Analyzed { .. });
    let mut violations = match outcome {
        FrameNetOutcome::Analyzed { violations, stats } => {
            STREAMS_ANALYZED.fetch_add(1, Ordering::Relaxed);
            if stats.framed {
                FRAMED_ANALYZED.fetch_add(1, Ordering::Relaxed);
            }
            SPILL_RELOADS_CHECKED
                .fetch_add(u64::from(stats.spill_reloads_checked), Ordering::Relaxed);
            EXITS_CHECKED.fetch_add(u64::from(stats.exits_checked), Ordering::Relaxed);
            violations
        }
        FrameNetOutcome::Declined(reason) => {
            STREAMS_DECLINED.fetch_add(1, Ordering::Relaxed);
            DECLINES[reason.index()].fetch_add(1, Ordering::Relaxed);
            Vec::new()
        }
    };
    violations.extend(legacy_violations(func, frame_modeled));
    for v in &violations {
        record_violation(&func.name, &format!("{} {}", v.kind.tag(), v.detail), mode);
    }
    if mode == PostRegallocRecheckMode::Enforce {
        violations.into_iter().next()
    } else {
        None
    }
}

#[cfg(test)]
mod tests;
