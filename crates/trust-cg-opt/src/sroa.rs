// trust-cg-opt - Scalar Replacement of Aggregates
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Scalar Replacement of Aggregates (SROA) for machine-level IR.
//!
//! SROA identifies stack slots whose address never escapes the function and
//! whose uses are limited to simple load/store patterns, and rewrites those
//! loads/stores into pure vreg-to-vreg copies. The stack slot storage is left
//! in the function (regalloc / frame lowering may prune unused slots later),
//! but the scalar SSA replacement eliminates stack traffic for the slot.
//!
//! # Scope (Phase 2b — issue #391)
//!
//! The current implementation targets the "textbook" pattern that frontends
//! emit for struct/tuple locals that are never address-escaped:
//!
//! ```text
//!   root = AddPCRel SP, StackSlot(N)          ; address of slot
//!   ; optional per-field offset derivation:
//!   f0   = MovR root                          ; field 0 (offset 0)
//!   f1   = AddRI root, #K                     ; field 1 (offset K)
//!   STR  value, f0, #0                        ; store to field
//!   val  = LDR       f1, #0                   ; load from field
//! ```
//!
//! A slot is rewritten iff **every** reference to the root vreg flows into
//! exactly one of:
//!
//! 1. a `MovR` alias (offset +0) that is itself a "derived address",
//! 2. an `AddRI` immediate offset that is itself a "derived address",
//! 3. a `LdrRI`/`StrRI` where the root/derived vreg is the address base
//!    (and the inner immediate is a known constant).
//!
//! Any use outside that envelope (call operand, compare, arithmetic other
//! than AddRI, store of the address as a value, out-of-pass block argument,
//! etc.) marks the slot **escaped** and the pass leaves it alone.
//!
//! When a slot is accepted, each distinct `(slot_byte_offset, opcode)` load
//! or store is replaced by a vreg move against a dedicated scalar vreg.
//! Intermediate `AddPCRel` / `AddRI` / `MovR` root uses become dead and are
//! removed in the same pass; subsequent DCE and copy-prop clean up the moves.
//!
//! # Non-goals
//!
//! * SROA for stack slots accessed via register-indexed addressing
//!   (`LdrRO`/`StrRO`) — array locals stay on the stack for now.
//! * SROA across aliased stack slots (partial overlap or dynamic offset) —
//!   tracked separately for future work.
//! * SROA for uninitialized cross-block paths — a cross-block load is only
//!   rewritten when a store reaches it from every predecessor path.
//!
//! # Safety / correctness
//!
//! The pass is a straightforward local rewrite:
//!
//! * Only stores keep "observable" effects at the ISA level; we replace them
//!   with vreg moves (which are not observable from outside the function).
//!   Because we also eliminate every matching load from the same slot, the
//!   semantics of the function modulo the slot's memory contents are
//!   preserved.
//! * The escape analysis is conservative: any unrecognised instruction
//!   that mentions the root (or a derived address) triggers a bail-out.
//! * We never rewrite across a slot whose load/store widths disagree for
//!   the same byte offset, whose independently tracked byte ranges overlap,
//!   or whose access range falls outside the fixed-size slot. Narrow byte and
//!   halfword accesses are also declined because a plain `MovR` cannot model
//!   their truncation and extension semantics.
//! * Orphan instructions are removed in a single sweep after rewriting, so
//!   the block instruction vectors stay consistent with `func.insts`.
//!
//! # Provenance policy
//!
//! The tracing and finalisation phases only inspect the function and do not
//! update provenance. Commit merges removed root/derived address provenance
//! into surviving scalarized load/store replacements, records address-only
//! removals as optimized away when no scalar instruction remains, and records
//! partial-escape shadow mirrors as clones of the surviving store.
//! Partial-escape roots, derived address defs, and stores that remain unchanged
//! intentionally keep their existing provenance entries.
//!
//! Reference: `designs/2026-04-18-aggregate-lowering.md` Phase 2b.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PassId, ProofAnnotation,
    ProvenanceMap, RegClass, StackSlotId, VReg, regs,
};

use crate::pass_manager::MachinePass;

/// Kill switch for the small-constant-`memcpy`-into-slot expansion (the
/// "memcpy fill", #salsa20): set `TCG_NO_SROA_MEMCPY_FILL` (any value) to
/// treat such calls as full escapes again.
fn sroa_memcpy_fill_enabled() -> bool {
    std::env::var_os("TCG_NO_SROA_MEMCPY_FILL").is_none()
}

/// Kill switch for accepting stores to one offset from MULTIPLE (dominance-
/// ordered) blocks: set `TCG_NO_SROA_MULTIBLOCK_STORES` (any value) to
/// restore the historical one-store-block-per-offset requirement.
fn sroa_multiblock_stores_enabled() -> bool {
    std::env::var_os("TCG_NO_SROA_MULTIBLOCK_STORES").is_none()
}

/// Largest constant `memcpy` length (bytes) the fill expansion models.
const SROA_MEMCPY_FILL_MAX_BYTES: i64 = 64;

/// Scalar Replacement of Aggregates pass.
///
/// Runs at `O1+`; see [`OptimizationPipeline`](crate::pipeline::OptimizationPipeline)
/// for wiring.
#[derive(Debug, Default)]
pub struct ScalarReplacementOfAggregates;

impl MachinePass for ScalarReplacementOfAggregates {
    fn name(&self) -> &str {
        "sroa"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_impl(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_impl(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }
}

fn run_impl(func: &mut MachFunction, provenance: Option<&mut ProvenanceMap>) -> bool {
    // 1. Build VReg -> definer instruction map so we can recognise a
    //    load/store base that came from an AddPCRel or AddRI chain.
    let def_of = build_vreg_def_map(func);

    // 1b. VRegs with more than one definition. The address tracer assumes SSA;
    //     a multi-defined vreg (e.g. a lowered loop phi assigned the slot
    //     address on one edge and a non-slot pointer on another) must never be
    //     treated as a pure slot-address alias. See build_multidef_set.
    let multidef = build_multidef_set(func);

    // 2. Count every use of every VReg across the function. This lets us
    //    confirm that when we eliminate a root/derived vreg, the def is
    //    truly dead (no surprise reader).
    let use_count = collect_vreg_use_counts(func);

    // 3. Find every "root" AddPCRel that materialises a stack-slot address.
    let roots = collect_stack_slot_roots(func);

    if roots.is_empty() {
        return false;
    }

    let mut rewrites: Vec<SlotRewrite> = Vec::new();
    let mut next_scalar_vreg = func.next_vreg;

    // 4. For each slot, try to collect all accesses. Bail out (skip the
    //    slot) the moment we see a use we don't recognise.
    'slot_loop: for (slot, root_insts) in group_roots_by_slot(&roots) {
        let mut plan = SlotPlan::new(slot);

        for root_inst in &root_insts {
            let root_vreg = match def_vreg(func.inst(*root_inst)) {
                Some(v) => v,
                None => continue 'slot_loop,
            };
            if multidef.contains(&root_vreg) {
                // The root address vreg is itself re-defined elsewhere; the
                // AddPCRel is not its sole producer. Unsound to scalarize.
                continue 'slot_loop;
            }
            if !plan.add_root(root_vreg, *root_inst) {
                continue 'slot_loop;
            }
            if !trace_addr_uses(
                func,
                &def_of,
                &multidef,
                root_vreg,
                0,
                &[*root_inst],
                &mut plan,
            ) {
                continue 'slot_loop;
            }
        }

        // Every root def is covered, every derived vreg is used only by
        // recognised addresses. Now confirm we touched **every** use of
        // every root/derived vreg: if `use_count` disagrees with what we
        // walked, there's an unknown reader (e.g., a backward edge we
        // didn't revisit) and we must bail.
        if !plan.all_uses_covered(&use_count) {
            continue 'slot_loop;
        }

        // Collect the rewrite entries.
        if let Some(r) = plan.finalise(func, &mut next_scalar_vreg) {
            rewrites.push(r);
        }
    }

    if rewrites.is_empty() {
        return false;
    }

    apply_rewrites(func, &rewrites, provenance)
}

// ---------------------------------------------------------------------------
// Helpers: vreg bookkeeping
// ---------------------------------------------------------------------------

/// Return the defining vreg (operand[0]) if the instruction's first operand
/// is a VReg; otherwise `None`. SROA only considers instructions whose
/// convention is "first operand is the destination".
fn def_vreg(inst: &MachInst) -> Option<VReg> {
    inst.operands.first().and_then(|op| match op {
        MachOperand::VReg(v) => Some(*v),
        _ => None,
    })
}

/// Map every defined VReg to the instruction that defined it.
fn build_vreg_def_map(func: &MachFunction) -> HashMap<VReg, InstId> {
    let mut out = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if produces_value(inst)
                && let Some(v) = def_vreg(inst)
            {
                out.insert(v, inst_id);
            }
        }
    }
    out
}

/// VRegs that are DEFINED by more than one instruction.
///
/// The address-tracing model assumes SSA: each root/derived-address vreg is
/// produced by exactly one instruction (the AddPCRel root or the MovR/AddRI
/// alias we followed). A vreg with multiple defs breaks that assumption — most
/// importantly a lowered loop `phi` that is assigned the slot address on the
/// entry edge (`MovR %v, root`) and a DIFFERENT, non-slot value on the backedge
/// (`MovR %v, loaded_ptr`). Tracing into such a vreg would rewrite every
/// `Ldr [%v]` as a read of the slot even on iterations where `%v` holds the
/// loaded runtime pointer — a miscompile (an infinite pointer-chasing loop:
/// gcc-c-torture 20000801-2). Any derived vreg appearing here forces a bail-out.
fn build_multidef_set(func: &MachFunction) -> HashSet<VReg> {
    let mut seen: HashSet<VReg> = HashSet::new();
    let mut multi: HashSet<VReg> = HashSet::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if produces_value(inst)
                && let Some(v) = def_vreg(inst)
                && !seen.insert(v)
            {
                multi.insert(v);
            }
        }
    }
    multi
}

/// Count how many times each VReg appears as a *source* operand.
///
/// Uses the same convention as DCE: if the instruction produces a value,
/// operands[0] is the def; otherwise every operand is a use.
fn collect_vreg_use_counts(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            let start = if produces_value(inst) { 1 } else { 0 };
            for op in &inst.operands[start..] {
                if let MachOperand::VReg(v) = op {
                    *counts.entry(*v).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

/// An instruction produces a value iff its `InstFlags` predicate says so.
/// Mirrors `effects::inst_produces_value` but we duplicate locally to keep
/// dependencies minimal.
fn produces_value(inst: &MachInst) -> bool {
    crate::effects::inst_produces_value(inst)
}

// ---------------------------------------------------------------------------
// Root discovery
// ---------------------------------------------------------------------------

/// Collect every `AddPCRel` instruction whose third operand is a StackSlot.
/// These are the ISel-emitted roots for `Opcode::StackAddr { slot }`.
fn collect_stack_slot_roots(func: &MachFunction) -> Vec<(StackSlotId, InstId)> {
    let mut out = Vec::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::AddPCRel {
                continue;
            }
            // AddPCRel operands: [VReg(dst), PReg(SP), StackSlot(N)].
            if let Some(MachOperand::StackSlot(slot)) = inst.operands.get(2) {
                out.push((*slot, inst_id));
            }
        }
    }
    out
}

/// Group the flat list of roots by `StackSlotId`, preserving definition order.
fn group_roots_by_slot(roots: &[(StackSlotId, InstId)]) -> Vec<(StackSlotId, Vec<InstId>)> {
    let mut order: Vec<StackSlotId> = Vec::new();
    let mut by_slot: HashMap<StackSlotId, Vec<InstId>> = HashMap::new();
    for (slot, inst) in roots {
        if !by_slot.contains_key(slot) {
            order.push(*slot);
        }
        by_slot.entry(*slot).or_default().push(*inst);
    }
    order
        .into_iter()
        .map(|s| (s, by_slot.remove(&s).unwrap()))
        .collect()
}

// ---------------------------------------------------------------------------
// Address-use tracing
// ---------------------------------------------------------------------------

/// A single access instruction (load or store) against a slot.
#[derive(Debug, Clone)]
struct Access {
    inst_id: InstId,
    byte_offset: i64,
    is_load: bool,
    /// Address-materialization instructions that fed this access, ordered
    /// root-to-leaf. These are removed on full SROA and their provenance is
    /// transferred into a surviving scalar replacement.
    addr_sources: Vec<InstId>,
    /// For loads, the destination vreg (operand[0]). For stores, the source
    /// vreg holding the stored value (operand[0]).
    value_vreg: VReg,
    /// Opcode bucket for width-consistency checks.
    opcode: AArch64Opcode,
}

/// A matched `memcpy(dst = slot, src, #len)` libcall whose destination is the
/// (whole) slot: on full promotion the call is deleted and replaced by one
/// element-width load from `src + offset` directly into the shadow scalar of
/// each covered offset ("memcpy fill"). Exact by construction: `memcpy`
/// copies `src[o..o+w)` into `dst[o..o+w)`, and the inserted loads read the
/// same bytes at the same program point (the call site), so every rewritten
/// slot load observes the same value; the deleted call's other effects
/// (writing the promoted slot's bytes, reading src bytes not covered by any
/// live lane) are unobservable.
#[derive(Debug, Clone)]
struct MemcpyFill {
    /// The `Bl "memcpy"` instruction.
    bl_id: InstId,
    /// The ABI arg-marshalling copies (`Copy PReg(x0..x3), vreg`), removed
    /// together with the call.
    arg_copies: Vec<InstId>,
    /// The vreg holding the source pointer (the x1 argument).
    src_vreg: VReg,
    /// The constant copy length in bytes (the x2 argument).
    len: i64,
}

/// Per-slot rewrite plan accumulated during use tracing.
struct SlotPlan {
    slot: StackSlotId,
    /// All root AddPCRel instructions for this slot.
    roots: Vec<InstId>,
    /// Derived-address instructions (`AddRI` and `MovR`) to remove on commit.
    derived_defs: Vec<InstId>,
    /// Every vreg we took ownership of (root + derived). Used to confirm no
    /// outside reader exists.
    owned_vregs: HashMap<VReg, u32 /* observed use count */>,
    /// Loads and stores we will rewrite.
    accesses: Vec<Access>,
    /// Set to true if tracing has found a reason to abort.
    aborted: bool,
    /// True when the slot address is passed to a `Bl` callee tagged with
    /// `ProofAnnotation::Pure` (#456 partial-escape).
    ///
    /// In this mode the slot is *not* fully scalar-replaceable: the Bl reads
    /// the slot's spilled bytes, so the root/derived-address defs and the
    /// `StrRI` stores must remain live. What we *can* do is redirect each
    /// in-function `LdrRI` against the slot to read the shadow scalar vreg
    /// written by the preceding `StrRI` at the same offset, eliminating the
    /// load/store round-trip inside the caller.
    partial_escape: bool,
    /// A matched whole-slot `memcpy` initialization (see [`MemcpyFill`]).
    memcpy_fill: Option<MemcpyFill>,
}

impl SlotPlan {
    fn new(slot: StackSlotId) -> Self {
        Self {
            slot,
            roots: Vec::new(),
            derived_defs: Vec::new(),
            owned_vregs: HashMap::new(),
            accesses: Vec::new(),
            aborted: false,
            partial_escape: false,
            memcpy_fill: None,
        }
    }

    fn add_root(&mut self, vreg: VReg, inst: InstId) -> bool {
        if self.owned_vregs.contains_key(&vreg) {
            // Two AddPCRel instructions produced the same VReg — unexpected.
            return false;
        }
        self.owned_vregs.insert(vreg, 0);
        self.roots.push(inst);
        true
    }

    fn add_derived(&mut self, vreg: VReg, inst: InstId) -> bool {
        if self.owned_vregs.contains_key(&vreg) {
            return false;
        }
        self.owned_vregs.insert(vreg, 0);
        self.derived_defs.push(inst);
        true
    }

    fn note_use(&mut self, vreg: VReg) {
        if let Some(c) = self.owned_vregs.get_mut(&vreg) {
            *c = c.saturating_add(1);
        }
    }

    fn abort(&mut self) {
        self.aborted = true;
    }

    fn all_uses_covered(&self, global: &HashMap<VReg, u32>) -> bool {
        if self.aborted {
            return false;
        }
        for (vreg, walked) in &self.owned_vregs {
            let global_count = global.get(vreg).copied().unwrap_or(0);
            if global_count != *walked {
                return false;
            }
        }
        true
    }

    /// Finalise: return a rewrite, or `None` if we have nothing to do.
    fn finalise(&mut self, func: &MachFunction, next_scalar_vreg: &mut u32) -> Option<SlotRewrite> {
        if self.aborted {
            return None;
        }
        if self.accesses.is_empty() && self.derived_defs.is_empty() && self.roots.is_empty() {
            return None;
        }
        // A scalar shadow is a plain `MovR`, so it is sound only for full-width
        // GPR accesses with one exact register class per byte offset.  In
        // particular, `LdrRI`/`StrRI` do not encode the width in the opcode:
        // the VReg class does.  Treating a Gpr32 store and Gpr64 load as the
        // same shape loses the adjacent four bytes of a packed value.
        //
        // Byte/halfword forms are declined even when their opcodes match: a
        // store truncates and a load extends, neither of which a `MovR`
        // reproduces.  Distinct offsets must also describe disjoint ranges;
        // otherwise independent shadow vregs would erase memory overlap.
        let slot_size = i64::from(func.stack_slots.get(self.slot.0 as usize)?.fixed_size()?);
        let mut shape_at_offset: HashMap<i64, (RegClass, i64)> = HashMap::new();
        for a in &self.accesses {
            if !matches!(a.opcode, AArch64Opcode::LdrRI | AArch64Opcode::StrRI) {
                return None;
            }
            if !matches!(a.value_vreg.class, RegClass::Gpr32 | RegClass::Gpr64) {
                return None;
            }
            let width = i64::from(a.value_vreg.class.size_bytes());
            let end = a.byte_offset.checked_add(width)?;
            if a.byte_offset < 0 || end > slot_size {
                return None;
            }
            match shape_at_offset.get(&a.byte_offset) {
                Some((class, existing_width))
                    if *class != a.value_vreg.class || *existing_width != width =>
                {
                    return None;
                }
                Some(_) => {}
                None => {
                    shape_at_offset.insert(a.byte_offset, (a.value_vreg.class, width));
                }
            }
        }

        let mut ranges: Vec<(i64, i64)> = shape_at_offset
            .iter()
            .map(|(offset, (_, width))| (*offset, *offset + *width))
            .collect();
        ranges.sort_unstable();
        if ranges.windows(2).any(|pair| pair[1].0 < pair[0].1) {
            return None;
        }

        // Validate a matched memcpy fill against the (now known) access shape
        // and derive its lane offsets: one element-width load per accessed
        // offset the copy covers. Any mismatch fails the WHOLE slot closed —
        // the call cannot be deleted unless every covered load is modeled.
        let memcpy_fill: Option<(MemcpyFill, Vec<i64>)> = match self.memcpy_fill.take() {
            None => None,
            Some(fill) => {
                if self.partial_escape {
                    // Fill + partial escape is unsupported: the pure callee
                    // would need the (deleted) memcpy's bytes.
                    return None;
                }
                // The source must not be an address of this same slot.
                if self.owned_vregs.contains_key(&fill.src_vreg) {
                    return None;
                }
                // One uniform element width across every accessed offset.
                let mut shapes = shape_at_offset.values();
                let &(class0, w) = shapes.next()?;
                if shapes.any(|&(c, w2)| c != class0 || w2 != w) {
                    return None;
                }
                if fill.len <= 0 || fill.len % w != 0 || fill.len > slot_size {
                    return None;
                }
                let mut lanes: Vec<i64> = Vec::new();
                for &offset in shape_at_offset.keys() {
                    if offset < fill.len {
                        // A covered access must sit exactly on the lane grid.
                        if offset % w != 0 || offset + w > fill.len {
                            return None;
                        }
                        lanes.push(offset);
                    }
                }
                if lanes.is_empty() {
                    return None;
                }
                lanes.sort_unstable();
                Some((fill, lanes))
            }
        };

        // Every rewritten load must be backed by a store at the same offset
        // either earlier in the block or along every predecessor path. The
        // rewrite uses one shadow vreg per offset; multiple predecessor stores
        // intentionally become multiple defs of that vreg, which the machine
        // liveness/regalloc pipeline already models. A memcpy fill counts as
        // a store to each of its lanes at the call site.
        let flow_accesses: Vec<Access> = match &memcpy_fill {
            None => self.accesses.clone(),
            Some((fill, lanes)) => {
                let mut flow = self.accesses.clone();
                for &offset in lanes {
                    flow.push(Access {
                        inst_id: fill.bl_id,
                        byte_offset: offset,
                        is_load: false,
                        addr_sources: Vec::new(),
                        // Synthetic entry for the dataflow checks only; the
                        // value vreg is never read for stores.
                        value_vreg: VReg::new(u32::MAX, RegClass::Gpr64),
                        opcode: AArch64Opcode::StrRI,
                    });
                }
                flow
            }
        };
        if !accesses_have_reaching_stores(func, &flow_accesses) {
            return None;
        }
        if !stores_are_dominance_ordered_per_offset(func, &flow_accesses) {
            return None;
        }

        // Allocate one scalar "shadow" vreg per access offset, matching the
        // destination register class of the first load at that offset (or a
        // store's source class).
        let mut scalar_vreg: HashMap<i64, VReg> = HashMap::new();
        for a in &self.accesses {
            if scalar_vreg.contains_key(&a.byte_offset) {
                continue;
            }
            let cls = a.value_vreg.class;
            scalar_vreg.insert(a.byte_offset, VReg::new(*next_scalar_vreg, cls));
            *next_scalar_vreg += 1;
        }

        Some(SlotRewrite {
            slot: self.slot,
            roots: std::mem::take(&mut self.roots),
            derived_defs: std::mem::take(&mut self.derived_defs),
            accesses: std::mem::take(&mut self.accesses),
            scalar_vreg,
            next_vreg: *next_scalar_vreg,
            partial_escape: self.partial_escape,
            memcpy_fill,
        })
    }
}

fn accesses_have_reaching_stores(func: &MachFunction, accesses: &[Access]) -> bool {
    if accesses.is_empty() {
        return true;
    }

    let mut access_positions = Vec::with_capacity(accesses.len());
    for access in accesses {
        let Some((block_id, index)) = containing_block_position(func, access.inst_id) else {
            return false;
        };
        access_positions.push((access, block_id, index));
    }

    let dominators = compute_dominators(func);

    for (access, block_id, index) in &access_positions {
        if !access.is_load {
            continue;
        }
        if block_has_store_before(&access_positions, *block_id, *index, access.byte_offset) {
            continue;
        }
        if has_dominating_store(
            &access_positions,
            &dominators,
            *block_id,
            access.byte_offset,
        ) {
            continue;
        }

        let preds = &func.block(*block_id).preds;
        if preds.is_empty() {
            return false;
        }

        for pred in preds {
            let mut seen = HashSet::new();
            if !predecessor_path_has_store(
                func,
                &access_positions,
                *pred,
                access.byte_offset,
                &mut seen,
            ) {
                return false;
            }
        }
    }

    true
}

fn compute_dominators(
    func: &MachFunction,
) -> HashMap<trust_cg_ir::BlockId, HashSet<trust_cg_ir::BlockId>> {
    let all_blocks: HashSet<trust_cg_ir::BlockId> = func.block_order.iter().copied().collect();
    let entry = func.entry;
    let mut dominators: HashMap<trust_cg_ir::BlockId, HashSet<trust_cg_ir::BlockId>> =
        HashMap::new();

    for block_id in &func.block_order {
        if *block_id == entry {
            dominators.insert(*block_id, HashSet::from([entry]));
        } else {
            dominators.insert(*block_id, all_blocks.clone());
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block_id in &func.block_order {
            if *block_id == entry {
                continue;
            }

            let preds = &func.block(*block_id).preds;
            let mut next = if let Some((first, rest)) = preds.split_first() {
                let mut intersection = dominators.get(first).cloned().unwrap_or_else(HashSet::new);
                for pred in rest {
                    if let Some(pred_doms) = dominators.get(pred) {
                        intersection.retain(|candidate| pred_doms.contains(candidate));
                    } else {
                        intersection.clear();
                    }
                }
                intersection
            } else {
                HashSet::new()
            };
            next.insert(*block_id);

            if dominators.get(block_id) != Some(&next) {
                dominators.insert(*block_id, next);
                changed = true;
            }
        }
    }

    dominators
}

fn containing_block_position(
    func: &MachFunction,
    inst_id: InstId,
) -> Option<(trust_cg_ir::BlockId, usize)> {
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        if let Some(index) = block.insts.iter().position(|id| *id == inst_id) {
            return Some((*block_id, index));
        }
    }
    None
}

fn block_has_store_before(
    access_positions: &[(&Access, trust_cg_ir::BlockId, usize)],
    block_id: trust_cg_ir::BlockId,
    before_index: usize,
    byte_offset: i64,
) -> bool {
    access_positions
        .iter()
        .any(|(access, access_block, index)| {
            *access_block == block_id
                && *index < before_index
                && !access.is_load
                && access.byte_offset == byte_offset
        })
}

fn has_dominating_store(
    access_positions: &[(&Access, trust_cg_ir::BlockId, usize)],
    dominators: &HashMap<trust_cg_ir::BlockId, HashSet<trust_cg_ir::BlockId>>,
    load_block: trust_cg_ir::BlockId,
    byte_offset: i64,
) -> bool {
    let Some(load_dominators) = dominators.get(&load_block) else {
        return false;
    };

    access_positions.iter().any(|(access, access_block, _)| {
        !access.is_load
            && access.byte_offset == byte_offset
            && *access_block != load_block
            && load_dominators.contains(access_block)
    })
}

fn block_has_store(
    access_positions: &[(&Access, trust_cg_ir::BlockId, usize)],
    block_id: trust_cg_ir::BlockId,
    byte_offset: i64,
) -> bool {
    access_positions.iter().any(|(access, access_block, _)| {
        *access_block == block_id && !access.is_load && access.byte_offset == byte_offset
    })
}

fn predecessor_path_has_store(
    func: &MachFunction,
    access_positions: &[(&Access, trust_cg_ir::BlockId, usize)],
    block_id: trust_cg_ir::BlockId,
    byte_offset: i64,
    seen: &mut HashSet<trust_cg_ir::BlockId>,
) -> bool {
    if !seen.insert(block_id) {
        return false;
    }
    if block_has_store(access_positions, block_id, byte_offset) {
        return true;
    }
    let preds = &func.block(block_id).preds;
    !preds.is_empty()
        && preds.iter().all(|pred| {
            predecessor_path_has_store(func, access_positions, *pred, byte_offset, seen)
        })
}

/// Historically SROA required all stores to one offset to sit in a SINGLE
/// block. That is relaxed (kill switch `TCG_NO_SROA_MULTIBLOCK_STORES`) to
/// allow stores from multiple blocks when those blocks are totally ordered by
/// dominance: on any execution the shadow vreg then receives its defs in the
/// same order the memory cell would have, so every rewritten load still reads
/// the value of the latest store on its path (the general soundness invariant
/// — every store rewritten to a def, every load to a use, positions
/// unchanged — needs no block constraint at all, but the dominance chain
/// keeps the accepted shapes easy to audit).
fn stores_are_dominance_ordered_per_offset(func: &MachFunction, accesses: &[Access]) -> bool {
    let mut store_blocks_by_offset: HashMap<i64, Vec<trust_cg_ir::BlockId>> = HashMap::new();
    for access in accesses {
        if access.is_load {
            continue;
        }
        let Some((block_id, _)) = containing_block_position(func, access.inst_id) else {
            return false;
        };
        let blocks = store_blocks_by_offset
            .entry(access.byte_offset)
            .or_default();
        if !blocks.contains(&block_id) {
            blocks.push(block_id);
        }
    }

    if store_blocks_by_offset.values().all(|b| b.len() <= 1) {
        return true;
    }
    if !sroa_multiblock_stores_enabled() {
        // Kill switch: historical single-block-per-offset behavior.
        return false;
    }

    let dominators = compute_dominators(func);
    for blocks in store_blocks_by_offset.values() {
        for (i, a) in blocks.iter().enumerate() {
            for b in &blocks[i + 1..] {
                let a_dom_b = dominators.get(b).is_some_and(|d| d.contains(a));
                let b_dom_a = dominators.get(a).is_some_and(|d| d.contains(b));
                if !a_dom_b && !b_dom_a {
                    return false;
                }
            }
        }
    }
    true
}

/// The rewrite description produced once we have confirmed the slot is safe.
#[derive(Debug)]
struct SlotRewrite {
    #[allow(dead_code)]
    slot: StackSlotId,
    roots: Vec<InstId>,
    derived_defs: Vec<InstId>,
    accesses: Vec<Access>,
    scalar_vreg: HashMap<i64, VReg>,
    /// Partial-escape mode (#456): the slot's address is passed to a pure
    /// Bl. In this mode commit keeps all roots, derived defs, and STRs alive
    /// (the Bl still needs the spilled bytes) and only rewrites LDRs.
    partial_escape: bool,
    /// Whole-slot memcpy initialization to expand into per-lane shadow loads
    /// (with the validated lane offsets), deleting the call (`memcpy fill`).
    memcpy_fill: Option<(MemcpyFill, Vec<i64>)>,
    next_vreg: u32,
}

/// Walk every use of `vreg` and classify it as:
///
/// * a `LdrRI` / `StrRI` against (root + `base_offset` + inner_imm) — add to
///   the plan,
/// * an `AddRI` with an immediate — recurse with offset += imm,
/// * a `MovR` / `Copy` — recurse with unchanged offset,
/// * anything else — abort.
///
/// Returns `false` and marks the plan aborted when it sees a use it doesn't
/// recognise or a use it already visited (cycle).
fn trace_addr_uses(
    func: &MachFunction,
    def_of: &HashMap<VReg, InstId>,
    multidef: &HashSet<VReg>,
    vreg: VReg,
    base_offset: i64,
    addr_sources: &[InstId],
    plan: &mut SlotPlan,
) -> bool {
    // Find every instruction using `vreg` as a source.
    let users = collect_users_of(func, vreg);
    for user_id in users {
        let inst = func.inst(user_id);
        plan.note_use(vreg);

        // Ignore the definer itself — it uses its own def only in the
        // degenerate case of `a = a`, which we treat as "too weird".
        if let Some(defining) = def_of.get(&vreg)
            && *defining == user_id
        {
            // Unreachable in well-formed IR; treat as abort.
            plan.abort();
            return false;
        }

        match inst.opcode {
            AArch64Opcode::AddRI => {
                // Must be: AddRI dst, base_vreg, imm. Base must be our vreg,
                // imm must be an immediate.
                if !is_addr_user_addri(inst, vreg) {
                    plan.abort();
                    return false;
                }
                let imm = match inst.operands.get(2) {
                    Some(MachOperand::Imm(v)) => *v,
                    _ => {
                        plan.abort();
                        return false;
                    }
                };
                let dst = match def_vreg(inst) {
                    Some(v) => v,
                    None => {
                        plan.abort();
                        return false;
                    }
                };
                if multidef.contains(&dst) {
                    // dst is assigned elsewhere too (e.g. a loop phi); it is not
                    // a pure alias of the slot address. Bail.
                    plan.abort();
                    return false;
                }
                if !plan.add_derived(dst, user_id) {
                    plan.abort();
                    return false;
                }
                let Some(next_offset) = base_offset.checked_add(imm) else {
                    plan.abort();
                    return false;
                };
                let mut nested_sources = addr_sources.to_vec();
                nested_sources.push(user_id);
                if !trace_addr_uses(
                    func,
                    def_of,
                    multidef,
                    dst,
                    next_offset,
                    &nested_sources,
                    plan,
                ) {
                    return false;
                }
            }
            AArch64Opcode::MovR | AArch64Opcode::Copy => {
                // MovR/Copy dst, src: alias. Our vreg must be the source.
                if !is_mov_from_source(inst, vreg) {
                    plan.abort();
                    return false;
                }
                match inst.operands.first() {
                    Some(MachOperand::VReg(dst)) => {
                        // Internal alias — recurse into the derived vreg.
                        let dst = *dst;
                        if multidef.contains(&dst) {
                            // dst is assigned elsewhere too (e.g. a loop phi
                            // that also carries a non-slot pointer); tracing it
                            // as a pure slot alias would miscompile. Bail.
                            plan.abort();
                            return false;
                        }
                        if !plan.add_derived(dst, user_id) {
                            plan.abort();
                            return false;
                        }
                        let mut nested_sources = addr_sources.to_vec();
                        nested_sources.push(user_id);
                        if !trace_addr_uses(
                            func,
                            def_of,
                            multidef,
                            dst,
                            base_offset,
                            &nested_sources,
                            plan,
                        ) {
                            return false;
                        }
                    }
                    Some(MachOperand::PReg(_)) => {
                        // Copy-to-PReg is ABI arg marshalling for a following
                        // call.
                        //
                        // Special case (memcpy fill): the WHOLE slot address
                        // (offset 0) passed as the DESTINATION of a small
                        // constant-length `memcpy` — record the fill; on full
                        // promotion the call is replaced by per-lane loads
                        // from the source (`TCG_NO_SROA_MEMCPY_FILL`).
                        //
                        // Otherwise: if the same block has a subsequent `Bl`
                        // tagged `ProofAnnotation::Pure`, the slot address is
                        // used only as a call argument that does not escape
                        // the callee — we can rewrite in-function LDRs against
                        // the slot but must leave the root/derived defs and
                        // STRs alone (partial-escape, #456). Otherwise, this
                        // is a normal escape and we bail.
                        if sroa_memcpy_fill_enabled()
                            && base_offset == 0
                            && plan.memcpy_fill.is_none()
                            && let Some(fill) = match_memcpy_fill(func, def_of, multidef, user_id)
                        {
                            plan.memcpy_fill = Some(fill);
                        } else if copy_preg_reaches_pure_bl(func, user_id) {
                            plan.partial_escape = true;
                        } else {
                            plan.abort();
                            return false;
                        }
                        // The Copy itself is a legitimate use of our vreg —
                        // record it so the use-count check passes without
                        // adding any derived vreg.
                    }
                    _ => {
                        plan.abort();
                        return false;
                    }
                }
            }
            AArch64Opcode::LdrRI
            | AArch64Opcode::LdrbRI
            | AArch64Opcode::LdrhRI
            | AArch64Opcode::LdrsbRI
            | AArch64Opcode::LdrshRI => {
                // Load format: [dst, base, imm]. Base must be our vreg.
                if !is_mem_base(inst, 1, vreg) {
                    plan.abort();
                    return false;
                }
                let imm = match inst.operands.get(2) {
                    Some(MachOperand::Imm(v)) => *v,
                    _ => {
                        plan.abort();
                        return false;
                    }
                };
                let dst = match def_vreg(inst) {
                    Some(v) => v,
                    None => {
                        plan.abort();
                        return false;
                    }
                };
                let Some(byte_offset) = base_offset.checked_add(imm) else {
                    plan.abort();
                    return false;
                };
                plan.accesses.push(Access {
                    inst_id: user_id,
                    byte_offset,
                    is_load: true,
                    addr_sources: addr_sources.to_vec(),
                    value_vreg: dst,
                    opcode: inst.opcode,
                });
            }
            AArch64Opcode::StrRI | AArch64Opcode::StrbRI | AArch64Opcode::StrhRI => {
                // Store format: [value, base, imm]. Base must be our vreg
                // (operand[1]); crucially, operand[0] (the value) must NOT
                // be our vreg — storing the address itself is an escape.
                if !is_mem_base(inst, 1, vreg) {
                    plan.abort();
                    return false;
                }
                if matches!(inst.operands.first(), Some(MachOperand::VReg(value)) if *value == vreg)
                {
                    plan.abort();
                    return false;
                }
                let imm = match inst.operands.get(2) {
                    Some(MachOperand::Imm(v)) => *v,
                    _ => {
                        plan.abort();
                        return false;
                    }
                };
                let value = match inst.operands.first() {
                    Some(MachOperand::VReg(v)) => *v,
                    _ => {
                        plan.abort();
                        return false;
                    }
                };
                let Some(byte_offset) = base_offset.checked_add(imm) else {
                    plan.abort();
                    return false;
                };
                plan.accesses.push(Access {
                    inst_id: user_id,
                    byte_offset,
                    is_load: false,
                    addr_sources: addr_sources.to_vec(),
                    value_vreg: value,
                    opcode: inst.opcode,
                });
            }
            _ => {
                // Any other opcode touching the slot address means escape.
                plan.abort();
                return false;
            }
        }
    }
    true
}

/// Collect InstIds that use `vreg` as a *source* operand.
fn collect_users_of(func: &MachFunction, vreg: VReg) -> Vec<InstId> {
    let mut out = Vec::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            let start = if produces_value(inst) { 1 } else { 0 };
            for op in &inst.operands[start..] {
                if let MachOperand::VReg(v) = op
                    && *v == vreg
                {
                    out.push(inst_id);
                    break;
                }
            }
        }
    }
    out
}

/// Is this `AddRI dst, base, imm` with `base == vreg`?
fn is_addr_user_addri(inst: &MachInst, vreg: VReg) -> bool {
    if inst.operands.len() != 3 {
        return false;
    }
    let base_ok = matches!(inst.operands.get(1), Some(MachOperand::VReg(v)) if *v == vreg);
    let imm_ok = matches!(inst.operands.get(2), Some(MachOperand::Imm(_)));
    let dst_ok = matches!(inst.operands.first(), Some(MachOperand::VReg(_)));
    base_ok && imm_ok && dst_ok
}

/// Is this `MovR dst, src` / `Copy dst, src` whose *source* is `vreg`,
/// irrespective of whether the destination is a VReg (internal alias) or a
/// PReg (ABI arg marshalling, partial-escape #456)?
fn is_mov_from_source(inst: &MachInst, vreg: VReg) -> bool {
    if inst.operands.len() != 2 {
        return false;
    }
    let src_ok = matches!(inst.operands.get(1), Some(MachOperand::VReg(v)) if *v == vreg);
    let dst_ok = matches!(
        inst.operands.first(),
        Some(MachOperand::VReg(_)) | Some(MachOperand::PReg(_))
    );
    src_ok && dst_ok
}

/// Walk the block containing `copy_id` forward; return `true` iff the next
/// `Bl` ISA instruction in that block carries `proof == Some(Pure)`.
///
/// This is the partial-escape predicate for SROA (#456): a Copy from a slot
/// address into a PReg is non-escaping *only* when it feeds a pure call in
/// the same basic block. We conservatively require no intervening Bl/Blr with
/// non-pure proof before the pure Bl.
fn copy_preg_reaches_pure_bl(func: &MachFunction, copy_id: InstId) -> bool {
    if !trust_cg_lower::guard_evidence::validator_guard_replay_authority_available() && !cfg!(test)
    {
        return false;
    }

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        let Some(pos) = block.insts.iter().position(|id| *id == copy_id) else {
            continue;
        };
        for &next_id in &block.insts[pos + 1..] {
            let next = func.inst(next_id);
            match next.opcode {
                AArch64Opcode::Bl => {
                    return next.proof == Some(ProofAnnotation::Pure);
                }
                AArch64Opcode::Blr => {
                    // Indirect call in the way — can't prove purity of the
                    // target, so we must conservatively treat the slot as
                    // escaped.
                    return false;
                }
                _ => {}
            }
        }
        // Copy was in this block but no Bl follows — treat as escape.
        return false;
    }
    false
}

/// Match the marshalling of a `memcpy(dst = slot, src, #len[, #0])` libcall
/// around `copy_id` (the `Copy PReg(x0) <- slot_root`). Fails closed on every
/// shape deviation:
///
/// * `copy_id` must be the x0 (destination) argument copy;
/// * a `Bl "memcpy"` must follow in the same block, with only other
///   Copy-to-PReg marshalling instructions in between;
/// * the contiguous Copy-to-PReg run immediately before the `Bl` must cover
///   exactly x0..x2 (plain `memcpy` call) or x0..x3 (the `llvm.memcpy`
///   intrinsic, whose 4th argument — the volatile flag — must be constant 0),
///   each from a vreg, each preg exactly once, and must contain `copy_id`;
/// * the length (x2) must be a single-def `Movz`/`MovI` constant in
///   `1..=SROA_MEMCPY_FILL_MAX_BYTES`;
/// * the call's return value (x0) must be unused: the instruction after the
///   `Bl` must not copy PReg x0 out.
fn match_memcpy_fill(
    func: &MachFunction,
    def_of: &HashMap<VReg, InstId>,
    multidef: &HashSet<VReg>,
    copy_id: InstId,
) -> Option<MemcpyFill> {
    // The traced use must be the x0 (destination) argument.
    if func.inst(copy_id).operands.first() != Some(&MachOperand::PReg(regs::X0)) {
        return None;
    }

    let (block_id, pos) = containing_block_position(func, copy_id)?;
    let insts = &func.block(block_id).insts;

    // Find the following Bl; only other Copy-to-PReg marshalling may
    // intervene.
    let mut bl_pos = None;
    for (i, &id) in insts.iter().enumerate().skip(pos + 1) {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::Bl => {
                bl_pos = Some(i);
                break;
            }
            AArch64Opcode::Copy | AArch64Opcode::MovR
                if matches!(inst.operands.first(), Some(MachOperand::PReg(_))) => {}
            _ => return None,
        }
    }
    let bl_pos = bl_pos?;
    let bl_id = insts[bl_pos];
    if func
        .inst(bl_id)
        .operands
        .first()
        .and_then(|op| op.as_symbol())
        != Some("memcpy")
    {
        return None;
    }

    // The contiguous Copy-to-PReg run immediately before the Bl.
    let mut run_start = bl_pos;
    while run_start > 0 {
        let inst = func.inst(insts[run_start - 1]);
        let is_arg_copy = matches!(inst.opcode, AArch64Opcode::Copy | AArch64Opcode::MovR)
            && matches!(inst.operands.first(), Some(MachOperand::PReg(_)))
            && matches!(inst.operands.get(1), Some(MachOperand::VReg(_)));
        if !is_arg_copy {
            break;
        }
        run_start -= 1;
    }
    if !insts[run_start..bl_pos].contains(&copy_id) {
        return None;
    }

    // Parse the run: preg index -> source vreg, each preg exactly once.
    let mut args: HashMap<trust_cg_ir::PReg, VReg> = HashMap::new();
    let mut arg_copies: Vec<InstId> = Vec::new();
    for &id in &insts[run_start..bl_pos] {
        let inst = func.inst(id);
        let (Some(MachOperand::PReg(preg)), Some(MachOperand::VReg(src))) =
            (inst.operands.first(), inst.operands.get(1))
        else {
            return None;
        };
        if args.insert(*preg, *src).is_some() {
            return None;
        }
        arg_copies.push(id);
    }
    let expected: &[trust_cg_ir::PReg] = if args.len() == 3 {
        &[regs::X0, regs::X1, regs::X2]
    } else if args.len() == 4 {
        &[regs::X0, regs::X1, regs::X2, regs::X3]
    } else {
        return None;
    };
    if !expected.iter().all(|p| args.contains_key(p)) {
        return None;
    }

    let src_vreg = args[&regs::X1];
    let len = const_movz_value(func, def_of, multidef, args[&regs::X2])?;
    if !(1..=SROA_MEMCPY_FILL_MAX_BYTES).contains(&len) {
        return None;
    }
    // llvm.memcpy's 4th arg is the volatile flag: must be constant 0.
    if args.len() == 4 && const_movz_value(func, def_of, multidef, args[&regs::X3]) != Some(0) {
        return None;
    }

    // The call's return value (dst in x0) must be unused.
    if let Some(&after_id) = insts.get(bl_pos + 1) {
        let after = func.inst(after_id);
        if matches!(after.opcode, AArch64Opcode::Copy | AArch64Opcode::MovR)
            && after.operands.get(1) == Some(&MachOperand::PReg(regs::X0))
        {
            return None;
        }
    }

    Some(MemcpyFill {
        bl_id,
        arg_copies,
        src_vreg,
        len,
    })
}

/// `v`'s single-def constant value from a canonical `Movz`/`MovI`, if any.
fn const_movz_value(
    func: &MachFunction,
    def_of: &HashMap<VReg, InstId>,
    multidef: &HashSet<VReg>,
    v: VReg,
) -> Option<i64> {
    if multidef.contains(&v) {
        return None;
    }
    let inst = func.inst(*def_of.get(&v)?);
    match inst.opcode {
        AArch64Opcode::Movz => {
            let (dst, value) = crate::reaching_const::movz_value(inst)?;
            if dst != v {
                return None;
            }
            i64::try_from(value).ok()
        }
        AArch64Opcode::MovI if inst.operands.len() == 2 => {
            inst.operands.get(1).and_then(|op| op.as_imm())
        }
        _ => None,
    }
}

/// For a load `[dst, base, imm]` or store `[val, base, imm]`: operand at
/// `base_idx` must be `VReg(vreg)`.
fn is_mem_base(inst: &MachInst, base_idx: usize, vreg: VReg) -> bool {
    if inst.operands.len() != 3 {
        return false;
    }
    matches!(inst.operands.get(base_idx), Some(MachOperand::VReg(base)) if *base == vreg)
}

// ---------------------------------------------------------------------------
// Rewrite application
// ---------------------------------------------------------------------------

/// Apply the accumulated rewrites to the function in place.
///
/// Returns `true` iff any instruction was modified or removed.
fn apply_rewrites(
    func: &mut MachFunction,
    rewrites: &[SlotRewrite],
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut changed = false;
    let pass = PassId::new("sroa");

    // Flatten "dead" instruction ids (roots + derived) into a single set so
    // one block pass can remove them all.
    let mut dead: HashSet<InstId> = HashSet::new();
    // Bump the function's vreg counter once, using the max of all rewrites.
    let mut max_next = func.next_vreg;

    // For partial-escape slots (#456), each STR must be preceded by a new
    // `MovR scalar_vreg, value` that mirrors the stored bytes into the shadow
    // vreg; a memcpy fill inserts its per-lane loads before the (deleted) Bl.
    // We collect these insertions here and splice them in afterwards, so we
    // only pay the block rebuild cost once.
    //
    // Keyed by `original InstId` -> newly-allocated InstIds inserted before it.
    let mut insert_before: HashMap<InstId, Vec<InstId>> = HashMap::new();
    let mut transferred_dead: HashSet<InstId> = HashSet::new();

    // Rewrite loads/stores first — this modifies `func.insts` in place.
    for rw in rewrites {
        max_next = max_next.max(rw.next_vreg);

        for acc in &rw.accesses {
            let target_vreg = rw.scalar_vreg[&acc.byte_offset];
            let source_loc = sroa_access_source_loc(func, acc);
            if rw.partial_escape {
                if acc.is_load {
                    // LdrRI dst, base, imm -> MovR dst, scalar_vreg
                    // (LDR is eliminated; STR still runs so the callee sees
                    // the spilled bytes.)
                    let inst = func.inst_mut(acc.inst_id);
                    inst.opcode = AArch64Opcode::MovR;
                    // The instruction was a LdrRI (READS_MEMORY|HAS_SIDE_EFFECTS).
                    // Rewriting it to a register move must also drop those memory
                    // flags; otherwise downstream def/use classification treats the
                    // MovR like a memory op (all operands as uses) and never spills
                    // its destination def, corrupting the value. Reset to MovR's
                    // canonical flags rather than mutating opcode alone.
                    inst.flags = AArch64Opcode::MovR.default_flags();
                    inst.operands = vec![
                        MachOperand::VReg(acc.value_vreg),
                        MachOperand::VReg(target_vreg),
                    ];
                    inst.source_loc = source_loc;
                    if let Some(provenance) = provenance.as_deref_mut() {
                        provenance.record_in_place_transform(acc.inst_id, pass.clone());
                    }
                    changed = true;
                } else {
                    // Insert a new `MovR scalar_vreg, value` *before* the
                    // original StrRI. The STR itself is left intact — the
                    // pure callee reads the spilled bytes. Provenance treats
                    // this as a clone/split of the STR: the original STR
                    // remains active, and the shadow mirror inherits its
                    // source mapping.
                    let mut mov = MachInst::new(
                        AArch64Opcode::MovR,
                        vec![
                            MachOperand::VReg(target_vreg),
                            MachOperand::VReg(acc.value_vreg),
                        ],
                    );
                    mov.source_loc = source_loc;
                    let new_id = func.push_inst(mov);
                    if let Some(provenance) = provenance.as_deref_mut() {
                        provenance.record_clone(acc.inst_id, new_id, pass.clone());
                    }
                    insert_before.entry(acc.inst_id).or_default().push(new_id);
                    changed = true;
                }
            } else {
                let inst = func.inst_mut(acc.inst_id);
                if acc.is_load {
                    // LdrRI dst, base, imm -> MovR dst, scalar_vreg
                    inst.opcode = AArch64Opcode::MovR;
                    inst.operands = vec![
                        MachOperand::VReg(acc.value_vreg),
                        MachOperand::VReg(target_vreg),
                    ];
                } else {
                    // StrRI value, base, imm -> MovR scalar_vreg, value
                    inst.opcode = AArch64Opcode::MovR;
                    inst.operands = vec![
                        MachOperand::VReg(target_vreg),
                        MachOperand::VReg(acc.value_vreg),
                    ];
                }
                // Promoting a load/store to a register move must also clear the
                // stale memory flags (READS_MEMORY/WRITES_MEMORY|HAS_SIDE_EFFECTS)
                // inherited from the original LdrRI/StrRI. A MovR that still
                // advertises WRITES_MEMORY is classified as a memory instruction
                // by the regalloc adapter, which marks *all* operands as uses and
                // therefore never inserts a spill store for the move's
                // destination def — yielding reads of uninitialized stack slots.
                inst.flags = AArch64Opcode::MovR.default_flags();
                inst.source_loc = source_loc;
                if let Some(provenance) = provenance.as_deref_mut() {
                    let mut sources = vec![acc.inst_id];
                    for source in &acc.addr_sources {
                        if !transferred_dead.contains(source)
                            && provenance.get_entry(*source).is_some()
                        {
                            transferred_dead.insert(*source);
                            sources.push(*source);
                        }
                    }
                    if sources.len() > 1 {
                        provenance.record_merge(&sources, acc.inst_id, pass.clone());
                    } else {
                        provenance.record_in_place_transform(acc.inst_id, pass.clone());
                    }
                }
                changed = true;
            }
        }

        // Memcpy fill (full promotion only): insert one element-width load
        // from `src + lane` directly into each lane's shadow vreg at the call
        // site, then delete the call and its argument marshalling.
        if let Some((fill, lanes)) = &rw.memcpy_fill {
            let bl_loc = func.inst(fill.bl_id).source_loc;
            for &offset in lanes {
                let shadow = rw.scalar_vreg[&offset];
                let mut load = MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::VReg(shadow),
                        MachOperand::VReg(fill.src_vreg),
                        MachOperand::Imm(offset),
                    ],
                );
                load.source_loc = bl_loc;
                let new_id = func.push_inst(load);
                if let Some(provenance) = provenance.as_deref_mut() {
                    provenance.record_clone(fill.bl_id, new_id, pass.clone());
                }
                insert_before.entry(fill.bl_id).or_default().push(new_id);
            }
            dead.insert(fill.bl_id);
            if let Some(provenance) = provenance.as_deref_mut() {
                provenance.record_deletion(
                    fill.bl_id,
                    pass.clone(),
                    "SROA expanded whole-slot memcpy into per-lane shadow loads",
                );
            }
            for id in &fill.arg_copies {
                dead.insert(*id);
                if let Some(provenance) = provenance.as_deref_mut() {
                    provenance.record_deletion(
                        *id,
                        pass.clone(),
                        "SROA removed memcpy argument marshalling with the expanded call",
                    );
                }
            }
            changed = true;
        }

        if !rw.partial_escape {
            for id in &rw.roots {
                dead.insert(*id);
                if !transferred_dead.contains(id)
                    && let Some(provenance) = provenance.as_deref_mut()
                {
                    provenance.record_deletion(
                        *id,
                        pass.clone(),
                        "SROA removed fully scalarized stack-slot address root",
                    );
                }
            }
            for id in &rw.derived_defs {
                dead.insert(*id);
                if !transferred_dead.contains(id)
                    && let Some(provenance) = provenance.as_deref_mut()
                {
                    provenance.record_deletion(
                        *id,
                        pass.clone(),
                        "SROA removed fully scalarized derived stack-slot address",
                    );
                }
            }
        }
        // Partial-escape: roots/derived defs stay alive (the Bl needs the
        // slot address in the ABI register), and the STRs stay alive too.
        // Those unchanged instructions need no provenance update; only the
        // rewritten LDRs and inserted shadow mirrors above change the map.
    }

    if !dead.is_empty() || !insert_before.is_empty() {
        for block_id in func.block_order.clone() {
            let block = func.block_mut(block_id);
            let before = block.insts.len();
            let mut new_insts: Vec<InstId> = Vec::with_capacity(block.insts.len());
            for &id in &block.insts {
                if let Some(inserted) = insert_before.get(&id) {
                    new_insts.extend(inserted.iter().copied());
                }
                if !dead.contains(&id) {
                    new_insts.push(id);
                }
            }
            if new_insts.len() != before {
                changed = true;
            }
            block.insts = new_insts;
        }
    }

    if max_next > func.next_vreg {
        func.next_vreg = max_next;
    }

    changed
}

fn sroa_access_source_loc(func: &MachFunction, acc: &Access) -> Option<trust_cg_ir::SourceLoc> {
    func.inst(acc.inst_id).source_loc.or_else(|| {
        acc.addr_sources
            .iter()
            .rev()
            .find_map(|source| func.inst(*source).source_loc)
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
        ProvenanceStatus, RegClass, Signature, SourceLoc, StackSlot, StackSlotId, TransformKind,
        TrustIrInstId, VReg,
    };

    fn vreg(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }
    fn g64(id: u32) -> MachOperand {
        vreg(id, RegClass::Gpr64)
    }
    fn g32(id: u32) -> MachOperand {
        vreg(id, RegClass::Gpr32)
    }
    fn imm(v: i64) -> MachOperand {
        MachOperand::Imm(v)
    }
    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 0,
            line,
            col: 1,
        }
    }

    fn new_func() -> MachFunction {
        MachFunction::new("sroa_test".to_string(), Signature::new(vec![], vec![]))
    }

    /// Build a minimal entry block with SP + StackSlot(0) already allocated.
    fn with_slot(func: &mut MachFunction, size: u32, align: u32) -> StackSlotId {
        func.alloc_stack_slot(StackSlot::new(size, align))
    }

    fn push(func: &mut MachFunction, block: BlockId, inst: MachInst) -> InstId {
        let id = func.push_inst(inst);
        func.append_inst(block, id);
        id
    }

    fn assert_sroa_survived(provenance: &ProvenanceMap, trust_ir: TrustIrInstId, inst_id: InstId) {
        let entry = provenance
            .get_entry(inst_id)
            .expect("rewritten instruction should retain provenance");
        assert!(entry.is_active());
        let transform = entry.transforms.last().expect("transform record");
        assert_eq!(transform.pass, PassId::new("sroa"));
        assert_eq!(transform.kind, TransformKind::Survived);
        assert_eq!(provenance.get_mach_insts(trust_ir), Some(&[inst_id][..]));
    }

    fn assert_sroa_merged(
        provenance: &ProvenanceMap,
        inst_id: InstId,
        expected_origins: &[TrustIrInstId],
        expected_sources: &[InstId],
    ) {
        let entry = provenance
            .get_entry(inst_id)
            .expect("merged instruction should retain provenance");
        assert!(entry.is_active());

        let mut origins = entry.trust_ir_origins.clone();
        origins.sort_unstable();
        let mut expected_origins = expected_origins.to_vec();
        expected_origins.sort_unstable();
        assert_eq!(origins, expected_origins);

        let transform = entry.transforms.last().expect("transform record");
        assert_eq!(transform.pass, PassId::new("sroa"));
        match &transform.kind {
            TransformKind::Merged { sources } => {
                let mut sources = sources.clone();
                sources.sort_unstable();
                let mut expected_sources = expected_sources.to_vec();
                expected_sources.sort_unstable();
                assert_eq!(sources, expected_sources);
            }
            other => panic!("expected merged provenance, got {other:?}"),
        }

        for origin in expected_origins {
            assert_eq!(provenance.get_mach_insts(origin), Some(&[inst_id][..]));
        }
    }

    fn assert_sroa_optimized_away(provenance: &ProvenanceMap, inst_id: InstId) {
        let entry = provenance
            .get_entry(inst_id)
            .expect("deleted instruction should retain optimized-away provenance");
        match &entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass, &PassId::new("sroa"));
                assert!(justification.contains("SROA removed"));
            }
            other => panic!("expected optimized-away provenance, got {other:?}"),
        }
    }

    /// Scenario: single stack slot of a struct `(i64, i64)`, store at +0,
    /// store at +8, load from +0. SROA should remove all memory instructions
    /// and replace them with register moves.
    #[test]
    fn struct_local_store_store_load_is_sroa_eliminated() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 16, 8);
        func.next_vreg = 20; // reserve space for materialised values.

        // v10 = AddPCRel SP, StackSlot(0)    ; root
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        // v11 = AddRI v10, #8                ; field 1 offset
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::AddRI, vec![g64(11), g64(10), imm(8)]),
        );
        // STR v0, v10, #0                    ; store field 0
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        // STR v1, v11, #0                    ; store field 1
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(1), g64(11), imm(0)]),
        );
        // v2 = LDR v10, #0                   ; load field 0
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(2), g64(10), imm(0)]),
        );
        // RET
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(
            changed,
            "SROA should fire on single-slot, no-escape pattern"
        );

        // Count memory ops / address ops remaining.
        let block = func.block(entry);
        let kinds: Vec<AArch64Opcode> =
            block.insts.iter().map(|id| func.inst(*id).opcode).collect();

        assert!(
            !kinds.contains(&AArch64Opcode::AddPCRel),
            "root AddPCRel removed"
        );
        assert!(
            !kinds.contains(&AArch64Opcode::AddRI),
            "derived AddRI removed"
        );
        assert!(
            !kinds.contains(&AArch64Opcode::LdrRI),
            "LDR replaced by MovR"
        );
        assert!(
            !kinds.contains(&AArch64Opcode::StrRI),
            "STR replaced by MovR"
        );
        // At least one MovR (store->move, load->move) remains.
        assert!(kinds.contains(&AArch64Opcode::MovR));
        // Ret still present.
        assert!(kinds.contains(&AArch64Opcode::Ret));
    }

    /// Regression: when SROA promotes a LdrRI/StrRI to a register `MovR`, the
    /// rewritten instruction must carry MovR's own flags — *not* the stale
    /// READS_MEMORY / WRITES_MEMORY | HAS_SIDE_EFFECTS flags inherited from the
    /// original load/store.
    ///
    /// A `MovR` that still advertises `WRITES_MEMORY` is treated by the regalloc
    /// adapter as a memory instruction whose operands are *all uses*. That
    /// misclassifies the move's destination (operand 0) as a use rather than a
    /// def, so the allocator inserts a reload before it but never a spill store
    /// after the (spilled) def. Downstream reads then observe uninitialized
    /// stack-slot bytes. This previously caused a compiled-invariant SIGBUS in
    /// the function-space quantifier path (reading a garbage upper bound into a
    /// dynamic range allocation).
    #[test]
    fn sroa_promoted_moves_carry_movr_flags_not_memory_flags() {
        use trust_cg_ir::inst::InstFlags;
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        // v10 = AddPCRel SP, StackSlot(0)   ; root address of the local slot
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        // STR v0, [v10]                     ; store value into the slot
        let str_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        // v1 = LDR [v10]                    ; load it back
        let ldr_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        // Sanity: the originals advertise the memory flags we must not leak.
        assert!(func.inst(str_id).flags.contains(InstFlags::WRITES_MEMORY));
        assert!(func.inst(ldr_id).flags.contains(InstFlags::READS_MEMORY));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            sroa.run(&mut func),
            "SROA should fire on single-slot pattern"
        );

        // Every instruction the slot was scalarized into must be a clean MovR.
        let memory_flags = InstFlags::READS_MEMORY
            .union(InstFlags::WRITES_MEMORY)
            .union(InstFlags::HAS_SIDE_EFFECTS);
        let mut saw_move = false;
        for &id in &func.block(entry).insts {
            let inst = func.inst(id);
            if inst.opcode == AArch64Opcode::MovR {
                saw_move = true;
                assert_eq!(
                    inst.flags,
                    AArch64Opcode::MovR.default_flags(),
                    "SROA-promoted MovR must use MovR's default flags, got {:#x}",
                    inst.flags.bits()
                );
                assert!(
                    inst.flags.intersection(memory_flags).is_empty(),
                    "SROA-promoted MovR must not retain stale memory flags, got {:#x}",
                    inst.flags.bits()
                );
            }
        }
        assert!(saw_move, "expected at least one promoted MovR");
    }

    #[test]
    fn same_id_different_class_addr_def_use_does_not_block_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        let decoy_def = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::AddRI, vec![g32(10), g32(6), imm(1)]),
        );
        let decoy_use = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::AddRI, vec![g32(12), g32(10), imm(4)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(2), g64(10), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            sroa.run(&mut func),
            "same numeric id in another class must not block scalarization"
        );

        let block = func.block(entry);
        assert!(block.insts.contains(&decoy_def));
        assert!(block.insts.contains(&decoy_use));
        assert_eq!(func.inst(decoy_def).opcode, AArch64Opcode::AddRI);
        assert_eq!(func.inst(decoy_use).opcode, AArch64Opcode::AddRI);
        assert!(
            block
                .insts
                .iter()
                .any(|id| func.inst(*id).opcode == AArch64Opcode::MovR),
            "the real Gpr64 stack access should still scalarize"
        );
    }

    #[test]
    fn same_id_different_class_memory_base_is_not_stack_addr_use() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        let unrelated_store = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(4), g32(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(2), g64(10), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            sroa.run(&mut func),
            "same numeric id in another class must not count as a stack-address base"
        );

        let block = func.block(entry);
        assert!(block.insts.contains(&unrelated_store));
        let unrelated = func.inst(unrelated_store);
        assert_eq!(unrelated.opcode, AArch64Opcode::StrRI);
        assert_eq!(unrelated.operands, vec![g64(4), g32(10), imm(0)]);
        assert!(
            block
                .insts
                .iter()
                .any(|id| func.inst(*id).opcode == AArch64Opcode::MovR),
            "the real Gpr64 stack access should still scalarize"
        );
    }

    #[test]
    fn preheader_store_reaches_loop_load_through_storeless_latch() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );

        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)]),
        );
        push(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("use_v1".to_string()), g64(1)],
            ),
        );
        push(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Block(exit), MachOperand::Block(latch)],
            ),
        );

        push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        push(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, header);
        func.add_edge(header, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(
            changed,
            "preheader store dominates the loop header load even though the latch has no store"
        );

        let kinds: Vec<AArch64Opcode> = func
            .block_order
            .iter()
            .flat_map(|block_id| func.block(*block_id).insts.iter())
            .map(|id| func.inst(*id).opcode)
            .collect();
        assert!(
            !kinds.contains(&AArch64Opcode::AddPCRel),
            "dominating preheader root should be removed"
        );
        assert!(
            !kinds.contains(&AArch64Opcode::StrRI),
            "dominating preheader store should become a scalar move"
        );
        assert!(
            !kinds.contains(&AArch64Opcode::LdrRI),
            "loop header load should read the scalar replacement"
        );
    }

    #[test]
    fn branch_store_on_one_path_does_not_reach_merge_load() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let store_path = func.create_block();
        let empty_path = func.create_block();
        let merge = func.create_block();
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Block(store_path),
                    MachOperand::Block(empty_path),
                ],
            ),
        );

        push(
            &mut func,
            store_path,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            store_path,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(merge)]),
        );

        push(
            &mut func,
            empty_path,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(merge)]),
        );

        push(
            &mut func,
            merge,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)]),
        );
        push(&mut func, merge, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, store_path);
        func.add_edge(entry, empty_path);
        func.add_edge(store_path, merge);
        func.add_edge(empty_path, merge);

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "SROA must not rewrite a merge load when one incoming branch has no store"
        );
    }

    #[test]
    fn different_offset_store_does_not_reach_loop_load() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();
        let slot = with_slot(&mut func, 16, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(8)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );

        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)]),
        );
        push(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Block(exit), MachOperand::Block(latch)],
            ),
        );

        push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        push(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, header);
        func.add_edge(header, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "a dominating store to offset 8 must not initialize a load from offset 0"
        );
    }

    #[test]
    fn same_offset_multi_store_keeps_latest_value_ordering() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(2), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(3), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("use_v3".to_string()), g64(3)],
            ),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(sroa.run(&mut func), "same-offset stores should scalarize");

        let movs: Vec<&MachInst> = func
            .block(entry)
            .insts
            .iter()
            .map(|id| func.inst(*id))
            .filter(|inst| inst.opcode == AArch64Opcode::MovR)
            .collect();
        assert_eq!(movs.len(), 3);
        assert_eq!(movs[0].operands[1], g64(0));
        assert_eq!(movs[1].operands[1], g64(2));
        assert_eq!(movs[2].operands[0], g64(3));
        assert_eq!(
            movs[2].operands[1], movs[1].operands[0],
            "load must read the scalar vreg most recently written by the second store"
        );
    }

    #[test]
    fn sroa_provenance_preserves_rewritten_split_accesses() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 16, 8);
        func.next_vreg = 20;

        let addpc = push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        let addri = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::AddRI, vec![g64(11), g64(10), imm(8)]),
        );
        let str0 = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        let str1 = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(1), g64(11), imm(0)]),
        );
        let ldr0 = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(2), g64(10), imm(0)]),
        );
        let ret = push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut provenance = ProvenanceMap::new();
        for (trust_ir, inst_id) in [
            (TrustIrInstId(100), addpc),
            (TrustIrInstId(101), addri),
            (TrustIrInstId(102), str0),
            (TrustIrInstId(103), str1),
            (TrustIrInstId(104), ldr0),
            (TrustIrInstId(105), ret),
        ] {
            provenance.record_lowering(trust_ir, &[inst_id], PassId::new("isel"));
        }

        let mut sroa = ScalarReplacementOfAggregates;
        let mut analyses = crate::pass_manager::AnalysisCache::new();
        assert!(sroa.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        assert!(!func.block(entry).insts.contains(&addpc));
        assert!(!func.block(entry).insts.contains(&addri));
        assert_eq!(func.inst(str0).opcode, AArch64Opcode::MovR);
        assert_eq!(func.inst(str1).opcode, AArch64Opcode::MovR);
        assert_eq!(func.inst(ldr0).opcode, AArch64Opcode::MovR);

        assert_sroa_merged(
            &provenance,
            str1,
            &[TrustIrInstId(100), TrustIrInstId(101), TrustIrInstId(103)],
            &[addpc, addri, str1],
        );
        assert_sroa_survived(&provenance, TrustIrInstId(102), str0);
        assert_sroa_survived(&provenance, TrustIrInstId(104), ldr0);
        assert!(
            provenance.get_entry(addpc).is_none(),
            "root provenance should transfer into a surviving scalar replacement"
        );
        assert!(
            provenance.get_entry(addri).is_none(),
            "derived-address provenance should transfer into a surviving scalar replacement"
        );
    }

    #[test]
    fn sroa_provenance_records_dead_address_root_deletion_rationale() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        let addpc = push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        let ret = push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(300), &[addpc], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(301), &[ret], PassId::new("isel"));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(sroa.run_with_provenance(&mut func, &mut provenance));

        assert!(
            !func.block(entry).insts.contains(&addpc),
            "dead aggregate address root should be removed"
        );
        assert_sroa_optimized_away(&provenance, addpc);
        assert!(provenance.get_entry(ret).unwrap().is_active());
    }

    #[test]
    fn sroa_source_loc_falls_back_to_folded_address_source() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 16, 8);
        func.next_vreg = 20;

        let root_loc = source_loc(31);
        let derived_loc = source_loc(37);
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            )
            .with_source_loc(root_loc),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::AddRI, vec![g64(11), g64(10), imm(8)])
                .with_source_loc(derived_loc),
        );
        let str_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(11), imm(0)]),
        );
        let ldr_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(11), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(sroa.run(&mut func));

        assert_eq!(func.inst(str_id).opcode, AArch64Opcode::MovR);
        assert_eq!(func.inst(str_id).source_loc, Some(derived_loc));
        assert_eq!(func.inst(ldr_id).opcode, AArch64Opcode::MovR);
        assert_eq!(func.inst(ldr_id).source_loc, Some(derived_loc));
    }

    #[test]
    fn sroa_source_loc_keeps_access_loc_over_address_fallback() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        let root_loc = source_loc(43);
        let load_loc = source_loc(47);
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            )
            .with_source_loc(root_loc),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        let ldr_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)])
                .with_source_loc(load_loc),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(sroa.run(&mut func));

        assert_eq!(func.inst(ldr_id).opcode, AArch64Opcode::MovR);
        assert_eq!(func.inst(ldr_id).source_loc, Some(load_loc));
    }

    #[test]
    fn sroa_provenance_records_partial_escape_shadow_split() {
        use trust_cg_ir::regs::{SP, X0};

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        let addpc = push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        let str_loc = SourceLoc {
            file: 0,
            line: 42,
            col: 7,
        };
        let str_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)])
                .with_source_loc(str_loc),
        );
        let ldr_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(2), g64(10), imm(0)]),
        );
        let copy_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), g64(10)]),
        );
        let bl_id = push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("pure_callee".to_string())],
            )
            .with_proof(ProofAnnotation::Pure),
        );
        let ret_id = push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut provenance = ProvenanceMap::new();
        for (trust_ir, inst_id) in [
            (TrustIrInstId(200), addpc),
            (TrustIrInstId(201), str_id),
            (TrustIrInstId(202), ldr_id),
            (TrustIrInstId(203), copy_id),
            (TrustIrInstId(204), bl_id),
            (TrustIrInstId(205), ret_id),
        ] {
            provenance.record_lowering(trust_ir, &[inst_id], PassId::new("isel"));
        }

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(sroa.run_with_provenance(&mut func, &mut provenance));

        let block = func.block(entry);
        let str_pos = block
            .insts
            .iter()
            .position(|id| *id == str_id)
            .expect("partial-escape STR should remain in block");
        let mirror_id = block.insts[str_pos - 1];
        assert_ne!(mirror_id, ldr_id);
        assert_eq!(func.inst(mirror_id).opcode, AArch64Opcode::MovR);
        assert_eq!(func.inst(mirror_id).source_loc, Some(str_loc));
        assert_eq!(func.inst(str_id).opcode, AArch64Opcode::StrRI);
        assert_eq!(func.inst(ldr_id).opcode, AArch64Opcode::MovR);

        assert_sroa_survived(&provenance, TrustIrInstId(202), ldr_id);

        let mirror_entry = provenance
            .get_entry(mirror_id)
            .expect("inserted shadow mirror should inherit STR provenance");
        assert_eq!(mirror_entry.trust_ir_origins, vec![TrustIrInstId(201)]);
        let mirror_transform = mirror_entry.transforms.last().unwrap();
        assert_eq!(mirror_transform.pass, PassId::new("sroa"));
        assert_eq!(
            mirror_transform.kind,
            TransformKind::Cloned { source: str_id }
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(201)),
            Some(&[str_id, mirror_id][..])
        );

        let str_entry = provenance.get_entry(str_id).unwrap();
        assert!(
            !str_entry
                .transforms
                .iter()
                .any(|record| record.pass == PassId::new("sroa")),
            "partial-escape STR is intentionally unchanged"
        );
        assert!(provenance.get_entry(addpc).unwrap().is_active());
    }

    /// Scenario: slot address escapes through a store (pointer stored into
    /// another memory location). SROA must bail out; IR unchanged.
    #[test]
    fn escaping_address_store_disables_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        // v10 = AddPCRel SP, StackSlot(0)
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        // STR v10, v1, #0      ; store the address v10 as a value! (escape)
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(10), g64(1), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let kinds_before: Vec<AArch64Opcode> = func
            .block(entry)
            .insts
            .iter()
            .map(|id| func.inst(*id).opcode)
            .collect();

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(!changed, "SROA must decline when address escapes via store");
        let kinds_after: Vec<AArch64Opcode> = func
            .block(entry)
            .insts
            .iter()
            .map(|id| func.inst(*id).opcode)
            .collect();
        assert_eq!(kinds_before, kinds_after, "IR unchanged on escape");
    }

    /// Scenario: slot address is passed to a call (escape via argument).
    #[test]
    fn escaping_address_to_call_disables_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        // v10 = AddPCRel SP, StackSlot(0)
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        // BL callee, v10      (pretend `Bl` consumes v10 as an argument)
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("callee".to_string()), g64(10)],
            ),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(!changed, "SROA must bail when address escapes to a call");
    }

    /// Scenario: two distinct slots, both SROA-eligible, independent rewrite.
    #[test]
    fn multiple_independent_slots_are_both_sroa_eliminated() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot0 = with_slot(&mut func, 8, 8);
        let slot1 = with_slot(&mut func, 8, 8);
        func.next_vreg = 30;

        // slot0
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    g64(10),
                    MachOperand::PReg(SP),
                    MachOperand::StackSlot(slot0),
                ],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(20), g64(10), imm(0)]),
        );
        // slot1
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    g64(11),
                    MachOperand::PReg(SP),
                    MachOperand::StackSlot(slot1),
                ],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(1), g64(11), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(21), g64(11), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(changed);

        let kinds: Vec<AArch64Opcode> = func
            .block(entry)
            .insts
            .iter()
            .map(|id| func.inst(*id).opcode)
            .collect();
        assert!(!kinds.contains(&AArch64Opcode::AddPCRel));
        assert!(!kinds.contains(&AArch64Opcode::LdrRI));
        assert!(!kinds.contains(&AArch64Opcode::StrRI));
    }

    /// Regression: each rewritten stack slot must receive its own shadow
    /// vreg range. Reusing the same shadow vreg for every independent slot
    /// aliases unrelated locals and can fabricate stale state after DCE and
    /// copy propagation.
    #[test]
    fn independent_slots_get_distinct_shadow_vregs() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot0 = with_slot(&mut func, 8, 8);
        let slot1 = with_slot(&mut func, 8, 8);
        func.next_vreg = 30;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    g64(10),
                    MachOperand::PReg(SP),
                    MachOperand::StackSlot(slot0),
                ],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(20), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    g64(11),
                    MachOperand::PReg(SP),
                    MachOperand::StackSlot(slot1),
                ],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(1), g64(11), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(21), g64(11), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(sroa.run(&mut func));

        let mut scalar_ids: HashSet<u32> = HashSet::new();
        for &inst_id in &func.block(entry).insts {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::MovR
                && let Some(MachOperand::VReg(dst)) = inst.operands.first()
                && dst.id >= 30
            {
                scalar_ids.insert(dst.id);
            }
        }
        assert_eq!(
            scalar_ids.len(),
            2,
            "two independent slots must not alias the same SROA shadow vreg"
        );
        assert!(
            func.next_vreg >= 32,
            "SROA must advance the function vreg cursor past both shadows"
        );
    }

    /// Scenario: a stack slot is written in one block and read in another.
    /// The machine liveness/regalloc pipeline supports a vreg defined in a
    /// predecessor and used in a dominated successor, so SROA can remove the
    /// stack round-trip once it proves the load is initialized.
    #[test]
    fn cross_block_slot_access_promotes_reaching_store() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let load_block = func.create_block();
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 30;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(load_block)]),
        );
        func.add_edge(entry, load_block);

        push(
            &mut func,
            load_block,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)]),
        );
        push(
            &mut func,
            load_block,
            MachInst::new(AArch64Opcode::Ret, vec![]),
        );

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(
            changed,
            "SROA should promote a cross-block slot load with a reaching store"
        );

        let entry_kinds: Vec<AArch64Opcode> = func
            .block(entry)
            .insts
            .iter()
            .map(|id| func.inst(*id).opcode)
            .collect();
        let load_kinds: Vec<AArch64Opcode> = func
            .block(load_block)
            .insts
            .iter()
            .map(|id| func.inst(*id).opcode)
            .collect();
        assert!(!entry_kinds.contains(&AArch64Opcode::AddPCRel));
        assert!(!entry_kinds.contains(&AArch64Opcode::StrRI));
        assert!(!load_kinds.contains(&AArch64Opcode::LdrRI));
        assert!(entry_kinds.contains(&AArch64Opcode::MovR));
        assert!(load_kinds.contains(&AArch64Opcode::MovR));
    }

    /// Scenario: a bytecode-register slot is initialized in one block, then
    /// overwritten and read in a successor. The store blocks form a dominance
    /// chain (entry dominates the overwrite block), so the shadow vreg
    /// receives its (multiple, cross-block) defs in exactly the order the
    /// memory cell would: SROA now promotes this shape
    /// (`TCG_NO_SROA_MULTIBLOCK_STORES` restores the historical decline).
    #[test]
    fn cross_block_multi_store_dominance_chain_promotes() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let overwrite_block = func.create_block();
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 30;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(overwrite_block)]),
        );
        func.add_edge(entry, overwrite_block);

        let overwrite_store = push(
            &mut func,
            overwrite_block,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(2), g64(10), imm(0)]),
        );
        let load = push(
            &mut func,
            overwrite_block,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(3), g64(10), imm(0)]),
        );
        push(
            &mut func,
            overwrite_block,
            MachInst::new(AArch64Opcode::Ret, vec![]),
        );

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            sroa.run(&mut func),
            "dominance-chain multi-block stores should promote"
        );

        // Both stores and the load are register moves now; the load reads the
        // same shadow vreg the LATEST store (program order) wrote.
        let store_inst = func.inst(overwrite_store);
        assert_eq!(store_inst.opcode, AArch64Opcode::MovR);
        let shadow = store_inst.operands[0].clone();
        let load_inst = func.inst(load);
        assert_eq!(load_inst.opcode, AArch64Opcode::MovR);
        assert_eq!(load_inst.operands[0], g64(3));
        assert_eq!(load_inst.operands[1], shadow);
    }

    /// Scenario: two stores to the same offset in PARALLEL (diamond) branches.
    /// Neither store block dominates the other — the dominance-chain
    /// relaxation must decline (the historical conservatism for shapes whose
    /// def order is control-dependent).
    #[test]
    fn cross_block_multi_store_diamond_declines_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let left = func.create_block();
        let right = func.create_block();
        let join = func.create_block();
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 30;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(left)]),
        );
        func.add_edge(entry, left);
        func.add_edge(entry, right);

        for (b, val) in [(left, 0), (right, 2)] {
            push(
                &mut func,
                b,
                MachInst::new(AArch64Opcode::StrRI, vec![g64(val), g64(10), imm(0)]),
            );
            push(
                &mut func,
                b,
                MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
            );
            func.add_edge(b, join);
        }

        push(
            &mut func,
            join,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(3), g64(10), imm(0)]),
        );
        push(&mut func, join, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "parallel (non-dominance-ordered) store blocks must decline"
        );
    }

    /// The memcpy fill: `memcpy(slot, src, #16)` followed by element loads of
    /// the slot promotes to per-lane loads from `src` directly into the
    /// shadow vregs, deleting the call and its marshalling.
    #[test]
    fn memcpy_fill_expands_call_into_lane_loads() {
        use trust_cg_ir::regs::{SP, X0, X1, X2, X3};

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 16, 4);
        func.next_vreg = 40;

        // src pointer (ABI copy-in) and length/volatile constants.
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![g64(1), MachOperand::PReg(X1)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(16)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Movz, vec![g64(3), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), g64(10)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X1), g64(1)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X2), g64(2)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X3), g64(3)]),
        );
        let bl = push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("memcpy".to_string())],
            ),
        );
        // Element accesses: loads at offsets 0 and 4 (Gpr32 lanes).
        let addr4 = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::AddRI, vec![g64(11), g64(10), imm(4)]),
        );
        let load0 = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g32(20), g64(10), imm(0)]),
        );
        let load4 = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g32(21), g64(11), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(sroa.run(&mut func), "memcpy fill should promote the slot");

        let kinds: Vec<AArch64Opcode> = func
            .block(entry)
            .insts
            .iter()
            .map(|id| func.inst(*id).opcode)
            .collect();
        assert!(
            !kinds.contains(&AArch64Opcode::Bl),
            "the memcpy call must be deleted"
        );
        assert!(
            !func.block(entry).insts.contains(&addr4),
            "derived slot addresses must be deleted"
        );
        // Two lane loads from src (v1) at offsets 0 and 4 replace the call.
        let lane_loads: Vec<&MachInst> = func
            .block(entry)
            .insts
            .iter()
            .map(|id| func.inst(*id))
            .filter(|inst| {
                inst.opcode == AArch64Opcode::LdrRI && inst.operands.get(1) == Some(&g64(1))
            })
            .collect();
        assert_eq!(lane_loads.len(), 2, "one lane load per accessed offset");
        let mut offsets: Vec<i64> = lane_loads
            .iter()
            .map(|inst| inst.operands[2].as_imm().unwrap())
            .collect();
        offsets.sort_unstable();
        assert_eq!(offsets, vec![0, 4]);
        // The original slot loads became register moves off the lane shadows.
        for (id, dst) in [(load0, g32(20)), (load4, g32(21))] {
            let inst = func.inst(id);
            assert_eq!(inst.opcode, AArch64Opcode::MovR);
            assert_eq!(inst.operands[0], dst);
        }
        // The lane loads' shadow dsts feed exactly those moves.
        let shadow0 = lane_loads
            .iter()
            .find(|inst| inst.operands[2].as_imm() == Some(0))
            .unwrap()
            .operands[0]
            .clone();
        assert_eq!(func.inst(load0).operands[1], shadow0);
        let _ = bl;
    }

    /// A memcpy whose length is NOT a lane multiple of the accessed widths
    /// (len 6 vs 4-byte accesses) must fail the whole slot closed.
    #[test]
    fn memcpy_fill_misaligned_length_declines() {
        use trust_cg_ir::regs::{SP, X0, X1, X2, X3};

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 16, 4);
        func.next_vreg = 40;

        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![g64(1), MachOperand::PReg(X1)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(6)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Movz, vec![g64(3), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), g64(10)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X1), g64(1)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X2), g64(2)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X3), g64(3)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("memcpy".to_string())],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g32(20), g64(10), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "len 6 cannot be decomposed into 4-byte lanes: fail closed"
        );
    }

    /// Scenario: one predecessor reaches a load without storing to the slot.
    /// SROA must keep memory traffic rather than introduce a possibly
    /// undefined shadow vreg on that edge.
    #[test]
    fn cross_block_slot_access_declines_uninitialized_predecessor() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let store_block = func.create_block();
        let load_block = func.create_block();
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 30;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(store_block)]),
        );
        func.add_edge(entry, store_block);
        func.add_edge(entry, load_block);

        push(
            &mut func,
            store_block,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            store_block,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(load_block)]),
        );
        func.add_edge(store_block, load_block);

        push(
            &mut func,
            load_block,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)]),
        );
        push(
            &mut func,
            load_block,
            MachInst::new(AArch64Opcode::Ret, vec![]),
        );

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "SROA must decline when any predecessor path reaches a load without a store"
        );
    }

    /// Scenario: mixed widths at the same offset. A byte store then a word
    /// load from offset 0 would require a truncation we don't synthesise —
    /// SROA must bail out cleanly.
    #[test]
    fn mixed_widths_at_same_offset_disables_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        // v10 = AddPCRel SP, StackSlot(0)
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        // STRB v0, v10, #0   ; byte write at offset 0
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrbRI, vec![g32(0), g64(10), imm(0)]),
        );
        // v1 = LDR v10, #0   ; word read at offset 0 — INCONSISTENT!
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(
            !changed,
            "SROA must decline when loads/stores at the same offset have mismatched widths"
        );
    }

    /// `LdrRI` and `StrRI` carry their width in the value register class, not
    /// in the opcode. A packed pair of u32 fields may therefore be stored with
    /// two Gpr32 stores and reloaded as one Gpr64 value. Replacing the reload
    /// with the first field's scalar shadow loses the adjacent field.
    #[test]
    fn packed_gpr32_fields_reloaded_as_gpr64_disable_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 72, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g32(0), g64(10), imm(64)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g32(1), g64(10), imm(68)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(2), g64(10), imm(64)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "SROA must preserve a packed 64-bit reload assembled from adjacent u32 fields"
        );
    }

    /// Even when each offset has a self-consistent register class, separate
    /// scalar shadows cannot represent partially overlapping memory ranges.
    #[test]
    fn overlapping_distinct_access_ranges_disable_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 16, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g32(2), g64(10), imm(4)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g32(3), g64(10), imm(4)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "SROA must preserve aliasing between overlapping byte ranges"
        );
    }

    /// A matching byte store/load still needs truncation and zero extension;
    /// a plain `MovR` is not an equivalent replacement.
    #[test]
    fn narrow_roundtrip_without_explicit_conversion_disables_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrbRI, vec![g32(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrbRI, vec![g32(1), g64(10), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "SROA must not erase byte truncation/extension semantics"
        );
    }

    /// Address arithmetic is untrusted input to this pass. Overflow must make
    /// the slot ineligible instead of wrapping into an apparently valid range.
    #[test]
    fn derived_address_overflow_disables_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::AddRI, vec![g64(11), g64(10), imm(i64::MAX)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(11), imm(1)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "SROA address tracing must fail closed on offset overflow"
        );
    }

    /// Logical stack-slot bounds are part of SROA's non-aliasing proof. An
    /// access extending past the slot could overlap another frame object.
    #[test]
    fn out_of_bounds_access_range_disables_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(4)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(1), g64(10), imm(4)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        assert!(
            !sroa.run(&mut func),
            "SROA must decline an access that extends beyond its fixed slot"
        );
    }

    /// Scenario: unknown use of the address (e.g., compare with zero).
    #[test]
    fn unknown_use_disables_sroa() {
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        // v10 = AddPCRel SP, StackSlot(0)
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        // CMP v10, #0       ; unknown pattern — must bail
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::CmpRI, vec![g64(10), imm(0)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(!changed);
    }

    #[test]
    fn multidef_derived_address_disables_sroa() {
        // Regression: gcc-c-torture 20000801-2. A lowered loop `phi` vreg is
        // assigned the slot address on one edge (`MovR v11, root`) and a
        // NON-slot pointer on another (`MovR v11, loaded`). SROA must not treat
        // `v11` as a pure slot alias — doing so rewrites `Ldr [v11]` as a slot
        // read even when `v11` holds the loaded runtime pointer, producing an
        // infinite pointer-chasing loop. The multi-def guard must decline.
        use trust_cg_ir::regs::SP;

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        // v10 = AddPCRel SP, StackSlot(0)   ; root slot address
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        // MovR v11, v10                     ; v11 = slot addr (phi entry edge) — DEF 1 of v11
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::MovR, vec![g64(11), g64(10)]),
        );
        // v13 = LdrRI v11, #0               ; load through v11 (node->next)
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(13), g64(11), imm(0)]),
        );
        // MovR v11, v13                     ; v11 = loaded ptr (phi backedge) — DEF 2 of v11
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::MovR, vec![g64(11), g64(13)]),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(
            !changed,
            "SROA must decline: v11 is multi-defined (loop phi), not a pure slot alias",
        );
    }

    /// Scenario (#456 partial-escape): slot address is copied into `X0` and
    /// passed to a `Bl` tagged with `ProofAnnotation::Pure`. The in-function
    /// LDR must be rewritten to a MovR against the shadow scalar, while the
    /// STR (spill) and the root `AddPCRel` must stay live because the pure
    /// callee reads the spilled bytes.
    #[test]
    fn pure_call_enables_partial_escape_sroa() {
        use trust_cg_ir::regs::{SP, X0};

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        // v10 = AddPCRel SP, StackSlot(0)    ; root
        let addpc = push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        // STR v0, v10, #0                    ; spill arg into slot
        let str_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        // v2 = LDR v10, #0                   ; in-function read of the slot
        let ldr_id = push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(2), g64(10), imm(0)]),
        );
        // Copy X0, v10                       ; ABI arg marshalling
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), g64(10)]),
        );
        // Bl pure_callee                     ; proof = Pure
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("pure_callee".to_string())],
            )
            .with_proof(ProofAnnotation::Pure),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(changed, "pure-call partial-escape must fire");

        // Root AddPCRel must still be present (Bl needs the address).
        let block = func.block(entry);
        let opcodes_and_ids: Vec<(InstId, AArch64Opcode)> = block
            .insts
            .iter()
            .map(|id| (*id, func.inst(*id).opcode))
            .collect();
        assert!(
            opcodes_and_ids.iter().any(|(id, _)| *id == addpc),
            "AddPCRel root must survive partial-escape"
        );
        // Original StrRI must still be present (the pure callee reads the
        // spilled bytes).
        assert!(
            opcodes_and_ids.iter().any(|(id, _)| *id == str_id),
            "StrRI must survive partial-escape"
        );
        // LDR must have been rewritten to MovR.
        let ldr_inst = func.inst(ldr_id);
        assert_eq!(
            ldr_inst.opcode,
            AArch64Opcode::MovR,
            "LdrRI must become MovR from shadow scalar"
        );
        // A `MovR scalar, v0` must precede the StrRI — it is a newly-inserted
        // shadow mirror that makes the rewritten LDR read a defined vreg.
        let str_pos = opcodes_and_ids
            .iter()
            .position(|(id, _)| *id == str_id)
            .expect("str pos");
        assert!(
            str_pos >= 1,
            "a MovR scalar mirror must be spliced before the StrRI"
        );
        let mirror = &opcodes_and_ids[str_pos - 1];
        assert_eq!(mirror.1, AArch64Opcode::MovR);
    }

    /// Scenario (#456): a partial-escape slot load before the first store at
    /// the same offset must not be rewritten to read an undefined shadow vreg.
    #[test]
    fn pure_call_partial_escape_declines_load_before_store() {
        use trust_cg_ir::regs::{SP, X0};

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![g64(2), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), g64(10)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("pure_callee".to_string())],
            )
            .with_proof(ProofAnnotation::Pure),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(
            !changed,
            "partial-escape SROA must decline when a load precedes the first store at the same offset"
        );
    }

    /// Scenario (#456): slot address copied to X0 but the following call is
    /// NOT tagged Pure. SROA must fall back to the conservative escape path
    /// and decline.
    #[test]
    fn non_pure_call_still_escapes_sroa() {
        use trust_cg_ir::regs::{SP, X0};

        let mut func = new_func();
        let entry = func.entry;
        let slot = with_slot(&mut func, 8, 8);
        func.next_vreg = 20;

        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            ),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::StrRI, vec![g64(0), g64(10), imm(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), g64(10)]),
        );
        // Plain Bl, no proof — classic escape.
        push(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("impure_callee".to_string())],
            ),
        );
        push(&mut func, entry, MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut sroa = ScalarReplacementOfAggregates;
        let changed = sroa.run(&mut func);
        assert!(
            !changed,
            "non-pure call must still escape — no partial-escape rewrite"
        );
    }
}
