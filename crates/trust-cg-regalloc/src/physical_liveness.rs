// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact physical-use reservations from one block-summary dataflow solve.
//!
//! Bits name the scalar pass's first-seen representatives, not raw encodings
//! or assumed equivalence classes. Every mask uses the allocator's actual
//! overlap predicate. In particular, this has no fixed register-number limit.

use std::collections::{BTreeMap, BTreeSet};

use crate::bitset::BitSet;
use crate::greedy::allocator_pregs_overlap;
use crate::machine_types::{InstId, PReg, RegAllocFunction, RegAllocOperand};

/// Deterministic test observations, not elapsed-time or allocator/RSS claims.
/// The production version is zero-sized and its observation methods are no-ops.
#[derive(Default, Debug)]
pub(super) struct WorkStats {
    #[cfg(test)]
    pub instruction_scans: usize,
    #[cfg(test)]
    pub block_visits: usize,
    #[cfg(test)]
    pub alias_queries: usize,
    /// Retained container element/backing-word capacities, excluding output,
    /// BTree node/allocator overhead, and stack temporaries.
    #[cfg(test)]
    pub scratch_payload_bytes: usize,
}

impl WorkStats {
    #[inline]
    pub(super) fn instruction(&mut self) {
        #[cfg(test)]
        {
            self.instruction_scans += 1;
        }
    }

    #[inline]
    pub(super) fn block(&mut self) {
        #[cfg(test)]
        {
            self.block_visits += 1;
        }
    }

    #[inline]
    pub(super) fn overlap(&mut self, a: PReg, b: PReg) -> bool {
        #[cfg(test)]
        {
            self.alias_queries += 1;
        }
        allocator_pregs_overlap(a, b)
    }
}

/// Physical sink reads of one instruction: explicit physical uses, then
/// implicit uses. Production builds forward to the shared definition verbatim.
#[cfg(not(test))]
#[inline]
fn physical_uses(inst: &crate::machine_types::RegAllocInst) -> impl Iterator<Item = PReg> + '_ {
    super::regalloc_inst_physical_uses(inst)
}

/// Test builds apply the injected [`fault::ReserveFault`] so the allocation
/// validator's independent physical-liveness recomputation can be shown to
/// catch a corrupted `reserve`.
#[cfg(test)]
fn physical_uses(inst: &crate::machine_types::RegAllocInst) -> impl Iterator<Item = PReg> + '_ {
    let keep_implicit = fault::active() != fault::ReserveFault::IgnoreImplicitUses;
    inst.uses.iter().filter_map(RegAllocOperand::as_preg).chain(
        inst.implicit_uses
            .iter()
            .copied()
            .filter(move |_| keep_implicit),
    )
}

/// Test-only mutation hooks for [`reserve`]. Each fault is a deliberate,
/// thread-local corruption of the shared reservation routine; the allocation
/// validator must reject every allocation it validates while one is active.
/// None of this is compiled into production builds.
#[cfg(test)]
pub(crate) mod fault {
    use std::cell::Cell;

    /// A deliberate corruption of [`super::reserve`].
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) enum ReserveFault {
        /// No corruption.
        None,
        /// Drop every successor's live-in when forming a block's live-out, so
        /// a physical value read in a later block is not reserved across the
        /// producing block's tail.
        DropSuccessorLiveIn,
        /// Ignore implicit physical reads (call arguments and return sinks).
        IgnoreImplicitUses,
    }

    thread_local! {
        static FAULT: Cell<ReserveFault> = const { Cell::new(ReserveFault::None) };
    }

    pub(crate) fn active() -> ReserveFault {
        FAULT.with(Cell::get)
    }

    /// Restores the previous fault when dropped.
    pub(crate) struct FaultGuard(ReserveFault);

    impl Drop for FaultGuard {
        fn drop(&mut self) {
            FAULT.with(|fault| fault.set(self.0));
        }
    }

    /// Activate `fault` on this thread until the returned guard is dropped.
    pub(crate) fn inject(fault: ReserveFault) -> FaultGuard {
        FaultGuard(FAULT.with(|current| current.replace(fault)))
    }
}

struct Masks {
    values: BTreeMap<PReg, BitSet>,
}

impl Masks {
    fn get_or_insert(&mut self, preg: PReg, reps: &[PReg], stats: &mut WorkStats) -> &BitSet {
        self.values.entry(preg).or_insert_with(|| {
            let mut mask = BitSet::new(reps.len());
            for (id, &rep) in reps.iter().enumerate() {
                // Keep the exact operand→representative orientation used by
                // the scalar transfers; do not assume overlap is transitive.
                if stats.overlap(preg, rep) {
                    mask.insert(id as u32);
                }
            }
            mask
        })
    }
}

struct Summary {
    generated: BitSet,
    killed: BitSet,
}

/// Preserve the scalar pass's tolerated missing entries and exact output keys.
/// This does not validate or grant new authority to malformed machine IR.
pub(super) fn reserve(
    func: &RegAllocFunction,
    numbering: &BTreeMap<InstId, u32>,
    reserved: &mut BTreeMap<PReg, Vec<u32>>,
) -> WorkStats {
    if let Some(block) = single_block_without_backedge(func) {
        reserve_single_block(func, block, numbering, reserved)
    } else {
        reserve_worklist(func, numbering, reserved)
    }
}

/// Exactly one *listed* valid block, with no edge back to itself. Other
/// successors are unlisted/invalid and therefore have empty IN under the
/// unchanged scalar contract. This proves OUT=empty without any CFG solve.
fn single_block_without_backedge(func: &RegAllocFunction) -> Option<usize> {
    let mut found = None;
    for block in &func.block_order {
        let id = block.0 as usize;
        if id >= func.blocks.len() {
            continue;
        }
        match found {
            Some(previous) if previous != id => return None,
            None => found = Some(id),
            _ => {}
        }
    }
    let id = found?;
    (!func.blocks[id]
        .succs
        .iter()
        .any(|next| next.0 as usize == id))
    .then_some(id)
}

/// Single-word storage is an algebraic representation choice, not a target or
/// source-size heuristic. Wider universes retain the same shared dense set.
enum LocalSet {
    Word(u64),
    Wide(BitSet),
}

impl LocalSet {
    fn new(bits: usize) -> Self {
        if bits <= 64 {
            Self::Word(0)
        } else {
            Self::Wide(BitSet::new(bits))
        }
    }

    /// Every analysis builds its sets from one universe size, so mixed
    /// Word/Wide operands do not arise; the element-wise path keeps the set
    /// operations total (and exact) if a caller ever mixes universes.
    fn elements(&self) -> Vec<u32> {
        let mut out = Vec::new();
        self.for_each(|id| out.push(id as u32));
        out
    }

    fn from_elements(elements: Vec<u32>) -> Self {
        let bits = elements.iter().max().map_or(0, |max| *max as usize + 1);
        let mut set = Self::new(bits);
        for id in elements {
            set.insert(id);
        }
        set
    }

    fn insert(&mut self, id: u32) {
        match self {
            Self::Word(word) => *word |= 1u64 << id,
            Self::Wide(bits) => bits.insert(id),
        }
    }

    fn copy_from(&mut self, other: &Self) {
        match (self, other) {
            (Self::Word(a), Self::Word(b)) => *a = *b,
            (Self::Wide(a), Self::Wide(b)) => a.copy_from(b),
            (this, other) => *this = Self::from_elements(other.elements()),
        }
    }

    fn union_from(&mut self, other: &Self) {
        match (self, other) {
            (Self::Word(a), Self::Word(b)) => *a |= *b,
            (Self::Wide(a), Self::Wide(b)) => a.union_from(b),
            (this, other) => {
                let mut all = this.elements();
                all.extend(other.elements());
                *this = Self::from_elements(all);
            }
        }
    }

    fn subtract(&mut self, other: &Self) {
        match (self, other) {
            (Self::Word(a), Self::Word(b)) => *a &= !*b,
            (Self::Wide(a), Self::Wide(b)) => a.subtract(b),
            (this, other) => {
                let removed = other.elements();
                let kept = this
                    .elements()
                    .into_iter()
                    .filter(|id| !removed.contains(id));
                *this = Self::from_elements(kept.collect());
            }
        }
    }

    fn for_each(&self, mut visit: impl FnMut(usize)) {
        match self {
            Self::Word(word) => {
                let mut bits = *word;
                while bits != 0 {
                    visit(bits.trailing_zeros() as usize);
                    bits &= bits - 1;
                }
            }
            Self::Wide(bits) => {
                for id in bits.iter() {
                    visit(id as usize);
                }
            }
        }
    }

    #[cfg(test)]
    fn storage_bytes(&self) -> usize {
        match self {
            Self::Word(_) => 0,
            Self::Wide(bits) => bits.storage_bytes(),
        }
    }
}

#[derive(Default)]
struct LocalMasks {
    // Sparse exact-operand cache. Up to eight entries use bounded linear
    // lookup; larger inventories gain an index, never an unbounded T² search.
    // Single-word masks themselves do not allocate.
    values: Vec<(PReg, LocalSet)>,
    index: Option<BTreeMap<PReg, usize>>,
}

impl LocalMasks {
    fn get_or_insert(&mut self, preg: PReg, reps: &[PReg], stats: &mut WorkStats) -> &LocalSet {
        let found = if let Some(index) = &self.index {
            index.get(&preg).copied()
        } else {
            self.values.iter().position(|(key, _)| *key == preg)
        };
        if let Some(index) = found {
            return &self.values[index].1;
        }
        let mut mask = LocalSet::new(reps.len());
        for (id, &rep) in reps.iter().enumerate() {
            if stats.overlap(preg, rep) {
                mask.insert(id as u32);
            }
        }
        if self.index.is_none() && self.values.len() == 8 {
            self.index = Some(
                self.values
                    .iter()
                    .enumerate()
                    .map(|(id, (preg, _))| (*preg, id))
                    .collect(),
            );
        }
        if let Some(index) = &mut self.index {
            index.insert(preg, self.values.len());
        }
        let slot = self.values.len();
        self.values.push((preg, mask));
        &self.values[slot].1
    }
}

fn reserve_single_block(
    func: &RegAllocFunction,
    id: usize,
    numbering: &BTreeMap<InstId, u32>,
    reserved: &mut BTreeMap<PReg, Vec<u32>>,
) -> WorkStats {
    let mut stats = WorkStats::default();
    let block = &func.blocks[id];
    let mut reps = Vec::new();
    // Repeating this same block cannot change its chosen representative keys.
    for inst_id in &block.insts {
        let Some(inst) = func.insts.get(inst_id.0 as usize) else {
            continue;
        };
        stats.instruction();
        for preg in physical_uses(inst) {
            if !reps.iter().any(|&rep| stats.overlap(rep, preg)) {
                reps.push(preg);
            }
        }
    }
    if reps.is_empty() {
        return stats;
    }
    if reps.len() == 1 {
        // A singleton universe is one Boolean, with one borrowed output list.
        // Direct exact alias queries cost less storage than building masks;
        // this still visits each instruction only once per listed occurrence.
        let rep = reps[0];
        let points = reserved.entry(rep).or_default();
        for block_id in &func.block_order {
            if block_id.0 as usize != id {
                continue;
            }
            stats.block();
            let mut live = false;
            for inst_id in block.insts.iter().rev() {
                let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                    continue;
                };
                stats.instruction();
                let after = live;
                if inst
                    .defs
                    .iter()
                    .filter_map(RegAllocOperand::as_preg)
                    .chain(inst.implicit_defs.iter().copied())
                    .any(|defined| stats.overlap(defined, rep))
                {
                    live = false;
                }
                if physical_uses(inst).any(|used| stats.overlap(used, rep)) {
                    live = true;
                }
                if (live || after)
                    && let Some(&position) = numbering.get(inst_id)
                {
                    points.push(position);
                }
            }
        }
        #[cfg(test)]
        {
            stats.scratch_payload_bytes = reps.capacity() * std::mem::size_of::<PReg>();
        }
        return stats;
    }
    // First-seen alias representatives have already been selected. Sorting
    // these exact keys only assigns private bit positions, enabling a merge
    // with the output map without another index tree or lookup per point.
    reps.sort_unstable();
    for &rep in &reps {
        reserved.entry(rep).or_default();
    }
    let mut next = 0;
    let mut points: Vec<_> = reserved
        .iter_mut()
        .filter_map(|(preg, points)| {
            if reps.get(next) == Some(preg) {
                next += 1;
                Some(points)
            } else {
                None
            }
        })
        .collect();
    debug_assert_eq!(points.len(), reps.len());
    let mut masks = LocalMasks::default();
    let empty = LocalSet::new(reps.len());
    let mut live = LocalSet::new(reps.len());
    let mut before = LocalSet::new(reps.len());
    for block_id in &func.block_order {
        if block_id.0 as usize != id {
            continue;
        }
        stats.block();
        live.copy_from(&empty);
        for inst_id in block.insts.iter().rev() {
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                continue;
            };
            stats.instruction();
            before.copy_from(&live);
            for preg in inst
                .defs
                .iter()
                .filter_map(RegAllocOperand::as_preg)
                .chain(inst.implicit_defs.iter().copied())
            {
                before.subtract(masks.get_or_insert(preg, &reps, &mut stats));
            }
            for preg in physical_uses(inst) {
                before.union_from(masks.get_or_insert(preg, &reps, &mut stats));
            }
            if let Some(&position) = numbering.get(inst_id) {
                live.union_from(&before);
                live.for_each(|rep| points[rep].push(position));
            }
            live.copy_from(&before);
        }
    }
    #[cfg(test)]
    {
        use std::mem::size_of;
        stats.scratch_payload_bytes = reps.capacity() * size_of::<PReg>()
            + points.capacity() * size_of::<&mut Vec<u32>>()
            + masks.values.capacity() * size_of::<(PReg, LocalSet)>()
            + masks
                .index
                .as_ref()
                .map_or(0, |index| index.len() * size_of::<(PReg, usize)>())
            + masks
                .values
                .iter()
                .map(|(_, bits)| bits.storage_bytes())
                .sum::<usize>()
            + empty.storage_bytes()
            + live.storage_bytes()
            + before.storage_bytes();
    }
    stats
}

/// General solver retained as an independently selectable measurement baseline.
pub(super) fn reserve_worklist(
    func: &RegAllocFunction,
    numbering: &BTreeMap<InstId, u32>,
    reserved: &mut BTreeMap<PReg, Vec<u32>>,
) -> WorkStats {
    let mut stats = WorkStats::default();
    let mut reps = Vec::new();
    let mut seen_uses = BTreeSet::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id.0 as usize) else {
            continue;
        };
        for inst_id in &block.insts {
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                continue;
            };
            stats.instruction();
            for preg in physical_uses(inst) {
                // Only exact duplicate operands are elided. Once a preg was
                // seen, its earlier representative remains present forever
                // (or it represented itself, and overlap is reflexive).
                // Discovery keeps the scalar rep→operand orientation; masks
                // below independently keep operand→rep. No symmetry shortcut.
                if seen_uses.insert(preg) && !reps.iter().any(|&rep| stats.overlap(rep, preg)) {
                    reps.push(preg);
                }
            }
        }
    }
    if reps.is_empty() {
        return stats;
    }

    let count = func.blocks.len();
    let mut active = vec![false; count];
    let mut worklist = Vec::with_capacity(count);
    for block_id in &func.block_order {
        let id = block_id.0 as usize;
        if let Some(flag) = active.get_mut(id)
            && !*flag
        {
            *flag = true;
            worklist.push(id);
        }
    }
    let mut queued = active.clone();
    let mut masks = Masks {
        values: BTreeMap::new(),
    };
    let mut summaries: Vec<_> = (0..count)
        .map(|_| Summary {
            generated: BitSet::new(reps.len()),
            killed: BitSet::new(reps.len()),
        })
        .collect();

    // F(S)=GEN ∪ (S\KILL). Uses are added before this instruction's
    // definitions: calls and read/modify/write instructions read their inputs
    // before clobbering their output lanes.
    for &id in &worklist {
        let summary = &mut summaries[id];
        for inst_id in &func.blocks[id].insts {
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                continue;
            };
            stats.instruction();
            for preg in physical_uses(inst) {
                summary.generated.union_difference(
                    masks.get_or_insert(preg, &reps, &mut stats),
                    &summary.killed,
                );
            }
            for preg in inst
                .defs
                .iter()
                .filter_map(RegAllocOperand::as_preg)
                .chain(inst.implicit_defs.iter().copied())
            {
                summary
                    .killed
                    .union_from(masks.get_or_insert(preg, &reps, &mut stats));
            }
        }
    }

    // Derive reverse edges from the *same successor inventory* as the scalar
    // solver. Stored preds may be stale. Unlisted successors have empty IN.
    // Flat adjacency avoids one allocation per block.
    let mut offsets = vec![0usize; count + 1];
    for &id in &worklist {
        for succ in &func.blocks[id].succs {
            let next = succ.0 as usize;
            if active.get(next).copied().unwrap_or(false) {
                offsets[next + 1] += 1;
            }
        }
    }
    for id in 0..count {
        offsets[id + 1] += offsets[id];
    }
    let mut cursors = offsets[..count].to_vec();
    let mut predecessors = vec![0usize; offsets[count]];
    for &id in &worklist {
        for succ in &func.blocks[id].succs {
            let next = succ.0 as usize;
            if active.get(next).copied().unwrap_or(false) {
                predecessors[cursors[next]] = id;
                cursors[next] += 1;
            }
        }
    }
    drop(cursors);

    let mut live_in = vec![BitSet::new(reps.len()); count];
    let mut live_out = vec![BitSet::new(reps.len()); count];
    let mut scratch = BitSet::new(reps.len());
    let mut before = BitSet::new(reps.len());
    // All listed blocks are seeded, including disconnected/irreducible loops.
    // Monotone finite sets converge without an iteration cap. Only IN changes
    // trigger predecessors, but OUT must be kept even when this block kills
    // every newly live successor bit: final instruction points still need it.
    while let Some(id) = worklist.pop() {
        queued[id] = false;
        stats.block();
        scratch.clear();
        #[cfg(test)]
        let drop_successors = fault::active() == fault::ReserveFault::DropSuccessorLiveIn;
        #[cfg(not(test))]
        let drop_successors = false;
        for succ in &func.blocks[id].succs {
            if drop_successors {
                break;
            }
            if let Some(input) = live_in.get(succ.0 as usize) {
                scratch.union_from(input);
            }
        }
        live_out[id].copy_from(&scratch);
        scratch.subtract(&summaries[id].killed);
        scratch.union_from(&summaries[id].generated);
        if scratch != live_in[id] {
            live_in[id].copy_from(&scratch);
            for &pred in &predecessors[offsets[id]..offsets[id + 1]] {
                if !queued[pred] {
                    queued[pred] = true;
                    worklist.push(pred);
                    debug_assert!(worklist.len() <= count);
                }
            }
        }
    }

    // Collect emitted points per representative index, avoiding a tree lookup
    // per point, then append them after every existing entry's earlier prefix
    // (emission order within each list is unchanged).
    for &preg in &reps {
        reserved.entry(preg).or_default();
    }
    let mut points: Vec<Vec<u32>> = vec![Vec::new(); reps.len()];
    for block_id in &func.block_order {
        let id = block_id.0 as usize;
        let Some(block) = func.blocks.get(id) else {
            continue;
        };
        scratch.copy_from(&live_out[id]);
        for inst_id in block.insts.iter().rev() {
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                continue;
            };
            stats.instruction();
            before.copy_from(&scratch);
            for preg in inst
                .defs
                .iter()
                .filter_map(RegAllocOperand::as_preg)
                .chain(inst.implicit_defs.iter().copied())
            {
                before.subtract(&masks.values[&preg]);
            }
            for preg in physical_uses(inst) {
                before.union_from(&masks.values[&preg]);
            }
            if let Some(&position) = numbering.get(inst_id) {
                scratch.union_from(&before);
                for rep in scratch.iter() {
                    points[rep as usize].push(position);
                }
            }
            scratch.copy_from(&before);
        }
    }
    #[cfg(test)]
    {
        use std::mem::size_of;
        // Container element/backing capacities only; excludes output vectors,
        // BTree node bookkeeping and allocator overhead. No peak RSS claim.
        stats.scratch_payload_bytes = reps.capacity() * size_of::<PReg>()
            + seen_uses.len() * size_of::<PReg>()
            + (active.capacity() + queued.capacity()) * size_of::<bool>()
            + (worklist.capacity() + offsets.capacity() + predecessors.capacity())
                * size_of::<usize>()
            + summaries.capacity() * size_of::<Summary>()
            + summaries
                .iter()
                .map(|s| s.generated.storage_bytes() + s.killed.storage_bytes())
                .sum::<usize>()
            + (live_in.capacity() + live_out.capacity()) * size_of::<BitSet>()
            + live_in
                .iter()
                .chain(&live_out)
                .map(BitSet::storage_bytes)
                .sum::<usize>()
            + scratch.storage_bytes()
            + before.storage_bytes()
            + masks.values.len() * size_of::<(PReg, BitSet)>()
            + masks
                .values
                .values()
                .map(BitSet::storage_bytes)
                .sum::<usize>()
            + points.capacity() * size_of::<Vec<u32>>();
    }
    for (&preg, emitted) in reps.iter().zip(points) {
        if !emitted.is_empty() {
            reserved.entry(preg).or_default().extend(emitted);
        }
    }
    stats
}

#[cfg(test)]
mod tests;
