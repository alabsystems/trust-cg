// trust-cg-opt - x86-64 Scalar Replacement of Aggregates
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Scalar Replacement of Aggregates (SROA) for x86-64 ISel-output functions.
//!
//! This is the x86 counterpart of [`crate::sroa::ScalarReplacementOfAggregates`],
//! which operates on the AArch64-shaped `trust_cg_ir::MachFunction`. The x86
//! pass-manager surface ([`crate::x86_pass_manager`]) consumes the distinct
//! [`X86ISelFunction`] IR (blocks carry their instructions inline, there is no
//! shared `InstId` arena, and there is no predecessor list or dominator tree on
//! the function). The escape-envelope analysis and every safety precondition
//! below are ported from the verified AArch64 SROA; only the IR plumbing and the
//! opcode vocabulary differ.
//!
//! # What it does
//!
//! Identifies stack slots whose address never escapes the function and whose
//! uses are limited to simple load/store patterns, and rewrites those
//! loads/stores into pure vreg-to-vreg copies. The canonical win is a slice
//! fat-pointer `(base, len)` that the frontend unconditionally memory-backs into
//! an address-taken slot and reloads every loop iteration
//! (`leaq -K(%rbp),%r; movq (%r),%rax`) instead of holding it in a register.
//! Because the slot's address is proven non-escaping, promoting it to SSA vregs
//! pre-regalloc is sound *independently of any heap store in the loop* (a
//! non-escaped slot cannot be aliased) — which is exactly what LICM's load tier
//! cannot establish when a heap `y[i]` store sits in the body.
//!
//! # Recognised pattern (x86 opcode mapping)
//!
//! ```text
//!   root  = lea  dst, [StackSlot(N) + 0]        ; address of slot  (== AArch64 AddPCRel)
//!   ; optional per-field offset derivation:
//!   f1    = lea  dst, [root + K]                 ; field 1 (offset K) (== AArch64 AddRI)
//!   a     = mov  dst, root                       ; alias (offset +0)  (== AArch64 MovR)
//!   mov   [root + disp], value                   ; store to field     (== AArch64 StrRI)
//!   val   = mov  dst, [root + disp]              ; load from field    (== AArch64 LdrRI)
//! ```
//!
//! A slot is rewritten iff **every** reference to the root vreg (and every
//! derived-address vreg) flows into exactly one of:
//!
//! 1. a full-width `MovRR` alias (offset +0),
//! 2. a `Lea dst, [root + K]` immediate offset derivation,
//! 3. a `MovRM{,32}` / `MovMR{,32}` where the root/derived vreg is the `[base +
//!    CONST-disp]` memory base (and, for a store, is NOT the stored value).
//!
//! Any use outside that envelope — the root as a **stored value**
//! (`mov [x], root`), a call/branch operand, a **SIB index**, a compare, a
//! `MovRR32` truncation, a bare `StackSlot` direct access, a multi-def carrier,
//! an unknown opcode — marks the slot **escaped** and the pass leaves it alone.
//! This allowlist is strictly more precise than LICM's `compute_escaped_slots`
//! and is exactly what excludes the ref-escape store-drop miscompile family.
//!
//! # Soundness / correctness
//!
//! * **Escape envelope** (`trace_addr_uses`): every use of a root/derived vreg
//!   is one of the recognised forms; anything else bails the slot. Because the
//!   address never escapes, no other pointer can alias the slot, so forwarding a
//!   dominating same-offset store's value to a load is exact.
//! * **Direct-slot guard** (`slot_has_foreign_reference`): if the slot is
//!   *also* touched by a bare `StackSlot(s)` operand that is not one of the
//!   recognised root `Lea`s (a direct `[StackSlot]`-addressed load/store, a SIB
//!   base/index, an indexed `LeaSib`), the slot bails. Otherwise an invisible
//!   direct store could interleave between the recorded store and the promoted
//!   load, and forwarding the stale value would miscompile.
//! * **Reaching stores** (`accesses_have_reaching_stores`): a load is
//!   rewritten only when a same-offset store dominates it on every path;
//!   uninitialized cross-block paths bail.
//! * **Single writer block per offset** (`stores_are_single_block_per_offset`):
//!   all stores to an offset live in one block, so the shadow vreg has a single
//!   defining block (the x86 liveness/regalloc pipeline models a def dominating a
//!   cross-block use, but not merge-of-two-defs phi semantics).
//! * **Width discipline**: only 64-bit (`MovRM`/`MovMR` → `MovRR`) and 32-bit
//!   (`MovRM32`/`MovMR32` → `MovRR32`) GPR accesses are admitted, and every
//!   access at a given offset must share one canonical width bucket. Narrow
//!   (8/16-bit), FP/vector, atomic/volatile (`proof_origin`), and SIB-indexed
//!   accesses bail — correctness over code quality.
//!
//! Reference: `crates/trust-cg-opt/src/sroa.rs` (AArch64 SROA).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::x86_produces_value;
use crate::mach_view::predecessor_map;
use crate::x86_pass_manager::X86MachinePass;

/// A concrete instruction location: `(block, index-within-block)`. Positions are
/// stable through tracing (the pass never mutates until the final commit) and
/// are resolved to edits in a single splice at the end.
type Site = (Block, usize);

/// Scalar Replacement of Aggregates for x86-64 ISel-output machine functions.
#[derive(Debug, Default)]
pub struct X86ScalarReplacementOfAggregates;

impl X86ScalarReplacementOfAggregates {
    pub fn new() -> Self {
        Self
    }

    /// Run x86 SROA directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86ScalarReplacementOfAggregates {
    fn name(&self) -> &str {
        "x86-sroa"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

// ===========================================================================
// Driver
// ===========================================================================

fn run_impl(func: &mut X86ISelFunction) -> bool {
    // Whole-function def counts: a vreg defined more than once is a
    // path-sensitive carrier (e.g. a lowered loop phi), never a pure SSA slot
    // alias — tracing into it would rewrite reads of an unrelated value.
    let def_counts = build_def_counts(func);

    // Per-operand-appearance use counts, used to confirm we walked EVERY use of
    // every root/derived vreg (a use we did not classify is an escape).
    let use_counts = collect_vreg_use_counts(func);

    // Every `lea dst, [StackSlot(s) + disp]` root, grouped by slot.
    let roots = collect_stack_slot_roots(func);
    if roots.is_empty() {
        return false;
    }

    let mut rewrites: Vec<SlotRewrite> = Vec::new();
    let mut next_scalar_vreg = func.next_vreg;

    'slot_loop: for (slot, root_sites) in group_roots_by_slot(&roots) {
        // Direct-slot guard: the slot must be reachable ONLY through its
        // recognised root `Lea`s. Any other `StackSlot(s)` mention (direct
        // `[StackSlot]` load/store, SIB base/index, indexed `LeaSib`) means an
        // access we cannot forward through — bail.
        let root_set: HashSet<Site> = root_sites.iter().copied().collect();
        if slot_has_foreign_reference(func, slot, &root_set) {
            continue 'slot_loop;
        }

        let mut plan = SlotPlan::new();

        for &root_site in &root_sites {
            let root_inst = &func.blocks[&root_site.0].insts[root_site.1];
            // Root `Lea` must carry no atomic/volatile marker and define a
            // single-def vreg.
            if root_inst.proof_origin.is_some() {
                continue 'slot_loop;
            }
            let (root_vreg, base_offset) = match root_lea_vreg_and_offset(root_inst) {
                Some(v) => v,
                None => continue 'slot_loop,
            };
            if def_counts.get(&root_vreg).copied().unwrap_or(0) != 1 {
                continue 'slot_loop;
            }
            if !plan.add_root(root_vreg, root_site) {
                continue 'slot_loop;
            }
            if !trace_addr_uses(func, &def_counts, root_vreg, base_offset, &mut plan) {
                continue 'slot_loop;
            }
        }

        // Confirm we touched EVERY use of every owned vreg: a use we did not
        // walk is an unknown reader → bail.
        if !plan.all_uses_covered(&use_counts) {
            continue 'slot_loop;
        }

        if let Some(r) = plan.finalise(func, &mut next_scalar_vreg) {
            rewrites.push(r);
        }
    }

    if rewrites.is_empty() {
        return false;
    }

    apply_rewrites(func, &rewrites, next_scalar_vreg)
}

// ===========================================================================
// Opcode classification (explicit allowlists — default-deny, no wildcard that
// treats an unknown opcode as safe)
// ===========================================================================

/// Full-width (64-bit) register-register move: the only alias form that
/// faithfully preserves a pointer. `MovRR32` is EXCLUDED — it truncates to 32
/// bits, so aliasing a slot address through it is an escape (the low-32 alias is
/// not the address).
fn is_alias_move_opcode(opcode: X86Opcode) -> bool {
    matches!(opcode, X86Opcode::MovRR)
}

/// GPR loads the pass can scalar-replace, mapped to their canonical width
/// bucket. Only 64-bit (`MovRM`) and 32-bit (`MovRM32`) plain loads are
/// admitted; narrow (8/16), FP/vector, and SIB-indexed loads bail.
fn promotable_load_bucket(opcode: X86Opcode) -> Option<X86Opcode> {
    match opcode {
        X86Opcode::MovRM => Some(X86Opcode::MovRM),
        X86Opcode::MovRM32 => Some(X86Opcode::MovRM32),
        _ => None,
    }
}

/// GPR stores the pass can scalar-replace, mapped to the SAME canonical width
/// bucket used by [`promotable_load_bucket`] so a store and a load at the same
/// offset compare equal.
fn promotable_store_bucket(opcode: X86Opcode) -> Option<X86Opcode> {
    match opcode {
        X86Opcode::MovMR => Some(X86Opcode::MovRM),
        X86Opcode::MovMR32 => Some(X86Opcode::MovRM32),
        _ => None,
    }
}

/// The register-register move opcode a canonical bucket promotes to, and the
/// register class the value operand must carry. `MovRM` (64-bit) → `MovRR`
/// (Gpr64); `MovRM32` (32-bit) → `MovRR32` (Gpr32).
fn bucket_move_and_class(bucket: X86Opcode) -> Option<(X86Opcode, RegClass)> {
    match bucket {
        X86Opcode::MovRM => Some((X86Opcode::MovRR, RegClass::Gpr64)),
        X86Opcode::MovRM32 => Some((X86Opcode::MovRR32, RegClass::Gpr32)),
        _ => None,
    }
}

// ===========================================================================
// vreg bookkeeping
// ===========================================================================

/// The single defined vreg (operand 0) of a value-producing instruction.
fn x86_defined_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

fn build_def_counts(func: &X86ISelFunction) -> HashMap<VReg, usize> {
    let mut counts: HashMap<VReg, usize> = HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if let Some(def) = x86_defined_vreg(inst) {
                *counts.entry(def).or_insert(0) += 1;
            }
        }
    }
    counts
}

/// Count how many times each vreg appears as a *source* operand, counting each
/// top-level source operand that mentions the vreg once. Mirrors the AArch64
/// pass: this is compared against the per-user-instruction walk to prove no
/// unclassified reader exists (a vreg mentioned by two operands of one
/// instruction makes the counts disagree → conservative bail).
fn collect_vreg_use_counts(func: &X86ISelFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            let start = usize::from(x86_produces_value(inst.opcode));
            for op in &inst.operands[start..] {
                let mut mentioned: HashSet<VReg> = HashSet::new();
                collect_operand_vregs(op, &mut mentioned);
                for v in mentioned {
                    *counts.entry(v).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

/// Collect every vreg mentioned (possibly nested inside a memory operand) by a
/// single operand.
fn collect_operand_vregs(op: &X86ISelOperand, out: &mut HashSet<VReg>) {
    match op {
        X86ISelOperand::VReg(v) => {
            out.insert(*v);
        }
        X86ISelOperand::MemAddr { base, .. } => collect_operand_vregs(base, out),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_vregs(base, out);
            collect_operand_vregs(index, out);
        }
        _ => {}
    }
}

/// True iff `op` mentions `vreg` anywhere (top-level or nested in a memory
/// operand).
fn operand_mentions_vreg(op: &X86ISelOperand, vreg: VReg) -> bool {
    match op {
        X86ISelOperand::VReg(v) => *v == vreg,
        X86ISelOperand::MemAddr { base, .. } => operand_mentions_vreg(base, vreg),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_mentions_vreg(base, vreg) || operand_mentions_vreg(index, vreg)
        }
        _ => false,
    }
}

/// Collect InstId-equivalent sites where `vreg` appears as a *source* operand.
/// Each user instruction appears at most once.
fn collect_user_sites(func: &X86ISelFunction, vreg: VReg) -> Vec<Site> {
    let mut out = Vec::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            let start = usize::from(x86_produces_value(inst.opcode));
            if inst.operands[start..]
                .iter()
                .any(|op| operand_mentions_vreg(op, vreg))
            {
                out.push((*block_id, idx));
            }
        }
    }
    out
}

// ===========================================================================
// Root discovery
// ===========================================================================

/// If `inst` is `lea dst, [StackSlot(s) + disp]`, return `(slot, dst, disp)`.
fn root_lea_slot(inst: &X86ISelInst) -> Option<(u32, VReg, i64)> {
    if inst.opcode != X86Opcode::Lea {
        return None;
    }
    if inst.operands.len() != 2 {
        return None;
    }
    let dst = match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => *v,
        _ => return None,
    };
    match inst.operands.get(1) {
        Some(X86ISelOperand::MemAddr { base, disp }) => match base.as_ref() {
            X86ISelOperand::StackSlot(s) => Some((*s, dst, i64::from(*disp))),
            _ => None,
        },
        _ => None,
    }
}

/// The `(dst vreg, base byte offset)` of a root `Lea` already known to be one.
fn root_lea_vreg_and_offset(inst: &X86ISelInst) -> Option<(VReg, i64)> {
    root_lea_slot(inst).map(|(_, v, off)| (v, off))
}

/// Collect every `lea dst, [StackSlot(s) + disp]` root site with its slot.
fn collect_stack_slot_roots(func: &X86ISelFunction) -> Vec<(u32, Site)> {
    let mut out = Vec::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            if let Some((slot, _dst, _off)) = root_lea_slot(inst) {
                out.push((slot, (*block_id, idx)));
            }
        }
    }
    out
}

fn group_roots_by_slot(roots: &[(u32, Site)]) -> Vec<(u32, Vec<Site>)> {
    let mut order: Vec<u32> = Vec::new();
    let mut by_slot: HashMap<u32, Vec<Site>> = HashMap::new();
    for (slot, site) in roots {
        if !by_slot.contains_key(slot) {
            order.push(*slot);
        }
        by_slot.entry(*slot).or_default().push(*site);
    }
    order
        .into_iter()
        .map(|s| (s, by_slot.remove(&s).unwrap()))
        .collect()
}

/// True iff `slot` is referenced by any operand that is NOT one of its
/// recognised root `Lea`s. A recognised root mentions `StackSlot(slot)` inside
/// its `MemAddr` base at its own site; anything else (a direct `[StackSlot]`
/// load/store, a SIB base/index, an indexed `LeaSib`, a bare operand) is a
/// foreign reference the pass cannot forward through, so the slot bails.
fn slot_has_foreign_reference(
    func: &X86ISelFunction,
    slot: u32,
    root_sites: &HashSet<Site>,
) -> bool {
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            let mentions = inst
                .operands
                .iter()
                .any(|op| operand_mentions_slot(op, slot));
            if mentions && !root_sites.contains(&(*block_id, idx)) {
                return true;
            }
        }
    }
    false
}

fn operand_mentions_slot(op: &X86ISelOperand, slot: u32) -> bool {
    match op {
        X86ISelOperand::StackSlot(s) => *s == slot,
        X86ISelOperand::MemAddr { base, .. } => operand_mentions_slot(base, slot),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_mentions_slot(base, slot) || operand_mentions_slot(index, slot)
        }
        _ => false,
    }
}

// ===========================================================================
// Address-use tracing
// ===========================================================================

/// A single load or store against a slot, in canonical-bucket form.
#[derive(Debug, Clone)]
struct Access {
    site: Site,
    byte_offset: i64,
    is_load: bool,
    /// Load dst (for loads) or stored-value source (for stores).
    value_vreg: VReg,
    /// Canonical width bucket (`MovRM` = 64-bit, `MovRM32` = 32-bit).
    bucket: X86Opcode,
}

/// Per-slot plan accumulated during tracing.
struct SlotPlan {
    roots: Vec<Site>,
    derived_defs: Vec<Site>,
    /// Every vreg we took ownership of (root + derived) → observed walk count.
    owned_vregs: HashMap<VReg, u32>,
    accesses: Vec<Access>,
    aborted: bool,
}

impl SlotPlan {
    fn new() -> Self {
        Self {
            roots: Vec::new(),
            derived_defs: Vec::new(),
            owned_vregs: HashMap::new(),
            accesses: Vec::new(),
            aborted: false,
        }
    }

    fn add_root(&mut self, vreg: VReg, site: Site) -> bool {
        if self.owned_vregs.contains_key(&vreg) {
            return false;
        }
        self.owned_vregs.insert(vreg, 0);
        self.roots.push(site);
        true
    }

    fn add_derived(&mut self, vreg: VReg, site: Site) -> bool {
        if self.owned_vregs.contains_key(&vreg) {
            return false;
        }
        self.owned_vregs.insert(vreg, 0);
        self.derived_defs.push(site);
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

    fn finalise(
        &mut self,
        func: &X86ISelFunction,
        next_scalar_vreg: &mut u32,
    ) -> Option<SlotRewrite> {
        if self.aborted {
            return None;
        }
        if self.accesses.is_empty() && self.derived_defs.is_empty() && self.roots.is_empty() {
            return None;
        }

        // Width consistency: every (offset) must stay a single canonical bucket,
        // and every access's value class must match the bucket's width.
        let mut bucket_at_offset: HashMap<i64, X86Opcode> = HashMap::new();
        for a in &self.accesses {
            let (_mov, class) = bucket_move_and_class(a.bucket)?;
            if a.value_vreg.class != class {
                return None;
            }
            match bucket_at_offset.get(&a.byte_offset) {
                Some(existing) if *existing != a.bucket => return None,
                Some(_) => {}
                None => {
                    bucket_at_offset.insert(a.byte_offset, a.bucket);
                }
            }
        }

        // Reaching-store + single-writer-block preconditions.
        let preds = predecessor_map(func);
        if !accesses_have_reaching_stores(func, &preds, &self.accesses) {
            return None;
        }
        if !stores_are_single_block_per_offset(&self.accesses) {
            return None;
        }

        // One shadow vreg per offset, matching the value register class.
        let mut scalar_vreg: HashMap<i64, VReg> = HashMap::new();
        for a in &self.accesses {
            if scalar_vreg.contains_key(&a.byte_offset) {
                continue;
            }
            scalar_vreg.insert(
                a.byte_offset,
                VReg::new(*next_scalar_vreg, a.value_vreg.class),
            );
            *next_scalar_vreg += 1;
        }

        Some(SlotRewrite {
            roots: std::mem::take(&mut self.roots),
            derived_defs: std::mem::take(&mut self.derived_defs),
            accesses: std::mem::take(&mut self.accesses),
            scalar_vreg,
        })
    }
}

/// The rewrite description produced once a slot is confirmed safe.
#[derive(Debug)]
struct SlotRewrite {
    roots: Vec<Site>,
    derived_defs: Vec<Site>,
    accesses: Vec<Access>,
    scalar_vreg: HashMap<i64, VReg>,
}

/// Walk every use of `vreg` (a root or derived slot-address vreg) and classify
/// it. Returns `false` (and marks the plan aborted) on the first use outside the
/// recognised envelope. Dispatch is via explicit opcode-classifier helpers so no
/// wildcard `match` arm can ever treat an unknown opcode as safe: the final
/// `else` bails.
fn trace_addr_uses(
    func: &X86ISelFunction,
    def_counts: &HashMap<VReg, usize>,
    vreg: VReg,
    base_offset: i64,
    plan: &mut SlotPlan,
) -> bool {
    let users = collect_user_sites(func, vreg);
    for site in users {
        let inst = &func.blocks[&site.0].insts[site.1];
        plan.note_use(vreg);

        // Never trace through an atomic/volatile carrier.
        if inst.proof_origin.is_some() {
            plan.abort();
            return false;
        }

        let opcode = inst.opcode;

        if is_alias_move_opcode(opcode) {
            // `MovRR dst, vreg`: full-width alias. dst must be a single-def vreg;
            // vreg must be the sole source. Recurse with the same offset.
            let ok_shape = inst.operands.len() == 2
                && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(_)))
                && matches!(inst.operands.get(1), Some(X86ISelOperand::VReg(v)) if *v == vreg);
            if !ok_shape {
                plan.abort();
                return false;
            }
            let dst = match inst.operands.first() {
                Some(X86ISelOperand::VReg(v)) => *v,
                _ => {
                    plan.abort();
                    return false;
                }
            };
            if def_counts.get(&dst).copied().unwrap_or(0) != 1 {
                plan.abort();
                return false;
            }
            if !plan.add_derived(dst, site) {
                plan.abort();
                return false;
            }
            if !trace_addr_uses(func, def_counts, dst, base_offset, plan) {
                return false;
            }
        } else if opcode == X86Opcode::Lea {
            // `Lea dst, [vreg + K]`: immediate offset derivation. SIB (indexed)
            // forms and any base other than `vreg` bail.
            let (dst, disp) = match (inst.operands.first(), inst.operands.get(1)) {
                (Some(X86ISelOperand::VReg(dst)), Some(X86ISelOperand::MemAddr { base, disp })) => {
                    match base.as_ref() {
                        X86ISelOperand::VReg(b) if *b == vreg => (*dst, i64::from(*disp)),
                        _ => {
                            plan.abort();
                            return false;
                        }
                    }
                }
                _ => {
                    plan.abort();
                    return false;
                }
            };
            if inst.operands.len() != 2 {
                plan.abort();
                return false;
            }
            if def_counts.get(&dst).copied().unwrap_or(0) != 1 {
                plan.abort();
                return false;
            }
            if !plan.add_derived(dst, site) {
                plan.abort();
                return false;
            }
            if !trace_addr_uses(func, def_counts, dst, base_offset + disp, plan) {
                return false;
            }
        } else if let Some(bucket) = promotable_load_bucket(opcode) {
            // `MovRM{,32} dst, [vreg + disp]`: load. Base must be `vreg`; no SIB.
            if inst.operands.len() != 2 {
                plan.abort();
                return false;
            }
            let dst = match inst.operands.first() {
                Some(X86ISelOperand::VReg(v)) => *v,
                _ => {
                    plan.abort();
                    return false;
                }
            };
            let Some(disp) = mem_base_disp(inst.operands.get(1), vreg) else {
                plan.abort();
                return false;
            };
            plan.accesses.push(Access {
                site,
                byte_offset: base_offset + disp,
                is_load: true,
                value_vreg: dst,
                bucket,
            });
        } else if let Some(bucket) = promotable_store_bucket(opcode) {
            // `MovMR{,32} [vreg + disp], value`: store. Memory base (operand 0)
            // must be `vreg`; the stored value (operand 1) must NOT be `vreg`
            // (storing the address itself is an escape); no SIB.
            if inst.operands.len() != 2 {
                plan.abort();
                return false;
            }
            let Some(disp) = mem_base_disp(inst.operands.first(), vreg) else {
                plan.abort();
                return false;
            };
            let value = match inst.operands.get(1) {
                Some(X86ISelOperand::VReg(v)) => *v,
                _ => {
                    plan.abort();
                    return false;
                }
            };
            if value == vreg {
                plan.abort();
                return false;
            }
            plan.accesses.push(Access {
                site,
                byte_offset: base_offset + disp,
                is_load: false,
                value_vreg: value,
                bucket,
            });
        } else {
            // Any other opcode touching the slot address means escape.
            plan.abort();
            return false;
        }
    }
    true
}

/// If `op` is `MemAddr { base: VReg(vreg), disp }` (a plain, non-SIB memory
/// operand based exactly on `vreg`), return `disp`. SIB-indexed operands and any
/// other base bail.
fn mem_base_disp(op: Option<&X86ISelOperand>, vreg: VReg) -> Option<i64> {
    match op {
        Some(X86ISelOperand::MemAddr { base, disp }) => match base.as_ref() {
            X86ISelOperand::VReg(b) if *b == vreg => Some(i64::from(*disp)),
            _ => None,
        },
        _ => None,
    }
}

// ===========================================================================
// Reaching-store analysis (ported from sroa.rs dominators)
// ===========================================================================
//
// The predecessor map comes from the shared arch-neutral CFG analysis
// [`crate::mach_view::predecessor_map`], which is behavior-identical to the
// private copy this pass used to carry: it iterates `block_order`, pushes one
// predecessor entry per CFG edge in successor order, and blocks absent from
// `func.blocks` contribute no edges. The set-based `compute_dominators` below
// stays private: mach_view exposes an idom TREE (`compute_idom`/`dominates`),
// not the full dominator SETS that `has_dominating_store` consumes.

fn accesses_have_reaching_stores(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    accesses: &[Access],
) -> bool {
    if accesses.is_empty() {
        return true;
    }
    let dominators = compute_dominators(func, preds);

    for access in accesses {
        if !access.is_load {
            continue;
        }
        let (block_id, index) = access.site;
        if block_has_store_before(accesses, block_id, index, access.byte_offset) {
            continue;
        }
        if has_dominating_store(accesses, &dominators, block_id, access.byte_offset) {
            continue;
        }
        let empty: Vec<Block> = Vec::new();
        let block_preds = preds.get(&block_id).unwrap_or(&empty);
        if block_preds.is_empty() {
            return false;
        }
        for pred in block_preds {
            let mut seen = HashSet::new();
            if !predecessor_path_has_store(preds, accesses, *pred, access.byte_offset, &mut seen) {
                return false;
            }
        }
    }
    true
}

fn compute_dominators(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
) -> HashMap<Block, HashSet<Block>> {
    let all_blocks: HashSet<Block> = func.block_order.iter().copied().collect();
    let Some(entry) = func.block_order.first().copied() else {
        return HashMap::new();
    };
    let mut dominators: HashMap<Block, HashSet<Block>> = HashMap::new();
    for block_id in &func.block_order {
        if *block_id == entry {
            dominators.insert(*block_id, HashSet::from([entry]));
        } else {
            dominators.insert(*block_id, all_blocks.clone());
        }
    }

    let empty: Vec<Block> = Vec::new();
    let mut changed = true;
    while changed {
        changed = false;
        for block_id in &func.block_order {
            if *block_id == entry {
                continue;
            }
            let block_preds = preds.get(block_id).unwrap_or(&empty);
            let mut next = if let Some((first, rest)) = block_preds.split_first() {
                let mut intersection = dominators.get(first).cloned().unwrap_or_default();
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

fn block_has_store_before(
    accesses: &[Access],
    block_id: Block,
    before_index: usize,
    byte_offset: i64,
) -> bool {
    accesses.iter().any(|access| {
        access.site.0 == block_id
            && access.site.1 < before_index
            && !access.is_load
            && access.byte_offset == byte_offset
    })
}

fn has_dominating_store(
    accesses: &[Access],
    dominators: &HashMap<Block, HashSet<Block>>,
    load_block: Block,
    byte_offset: i64,
) -> bool {
    let Some(load_dominators) = dominators.get(&load_block) else {
        return false;
    };
    accesses.iter().any(|access| {
        !access.is_load
            && access.byte_offset == byte_offset
            && access.site.0 != load_block
            && load_dominators.contains(&access.site.0)
    })
}

fn block_has_store(accesses: &[Access], block_id: Block, byte_offset: i64) -> bool {
    accesses.iter().any(|access| {
        access.site.0 == block_id && !access.is_load && access.byte_offset == byte_offset
    })
}

fn predecessor_path_has_store(
    preds: &HashMap<Block, Vec<Block>>,
    accesses: &[Access],
    block_id: Block,
    byte_offset: i64,
    seen: &mut HashSet<Block>,
) -> bool {
    if !seen.insert(block_id) {
        return false;
    }
    if block_has_store(accesses, block_id, byte_offset) {
        return true;
    }
    let empty: Vec<Block> = Vec::new();
    let block_preds = preds.get(&block_id).unwrap_or(&empty);
    !block_preds.is_empty()
        && block_preds
            .iter()
            .all(|pred| predecessor_path_has_store(preds, accesses, *pred, byte_offset, seen))
}

fn stores_are_single_block_per_offset(accesses: &[Access]) -> bool {
    let mut store_block_by_offset: HashMap<i64, Block> = HashMap::new();
    for access in accesses {
        if access.is_load {
            continue;
        }
        match store_block_by_offset.get(&access.byte_offset) {
            Some(existing) if *existing != access.site.0 => return false,
            Some(_) => {}
            None => {
                store_block_by_offset.insert(access.byte_offset, access.site.0);
            }
        }
    }
    true
}

// ===========================================================================
// Rewrite application
// ===========================================================================

fn apply_rewrites(
    func: &mut X86ISelFunction,
    rewrites: &[SlotRewrite],
    next_scalar_vreg: u32,
) -> bool {
    // Build the in-place access replacements and the dead-address removal set,
    // keyed by their (stable) original sites.
    let mut replacements: HashMap<Site, X86ISelInst> = HashMap::new();
    let mut dead: HashSet<Site> = HashSet::new();

    for rw in rewrites {
        for acc in &rw.accesses {
            let scalar = rw.scalar_vreg[&acc.byte_offset];
            let Some((move_op, _class)) = bucket_move_and_class(acc.bucket) else {
                // Unreachable: finalise already validated the bucket.
                continue;
            };
            let new_inst = if acc.is_load {
                // `MovRM{,32} dst, [mem]` → `MovRR{,32} dst, scalar`
                X86ISelInst::new(
                    move_op,
                    vec![
                        X86ISelOperand::VReg(acc.value_vreg),
                        X86ISelOperand::VReg(scalar),
                    ],
                )
            } else {
                // `MovMR{,32} [mem], value` → `MovRR{,32} scalar, value`
                X86ISelInst::new(
                    move_op,
                    vec![
                        X86ISelOperand::VReg(scalar),
                        X86ISelOperand::VReg(acc.value_vreg),
                    ],
                )
            };
            replacements.insert(acc.site, new_inst);
        }
        for site in &rw.roots {
            dead.insert(*site);
        }
        for site in &rw.derived_defs {
            dead.insert(*site);
        }
    }

    if replacements.is_empty() && dead.is_empty() {
        return false;
    }

    // Apply per block: first mutate the access replacements in place (index-
    // stable), then remove the dead address instructions by descending index.
    for block_id in func.block_order.clone() {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        for (idx, slot) in block.insts.iter_mut().enumerate() {
            if let Some(new_inst) = replacements.get(&(block_id, idx)) {
                *slot = new_inst.clone();
            }
        }

        let mut dead_idxs: Vec<usize> = (0..block.insts.len())
            .filter(|idx| dead.contains(&(block_id, *idx)))
            .collect();
        dead_idxs.sort_unstable_by(|a, b| b.cmp(a));
        for idx in dead_idxs {
            block.insts.remove(idx);
        }
    }

    if next_scalar_vreg > func.next_vreg {
        func.next_vreg = next_scalar_vreg;
    }

    true
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    use trust_cg_ir::x86_64_regs::RAX;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::types::Type;

    fn g64(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }
    fn imm(v: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(v)
    }
    fn mem_slot(slot: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(X86ISelOperand::StackSlot(slot)),
            disp,
        }
    }
    fn mem_vreg(id: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(g64(id)),
            disp,
        }
    }
    fn root_lea(dst: u32, slot: u32) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Lea, vec![g64(dst), mem_slot(slot, 0)])
    }
    fn load(dst: u32, base: u32, disp: i32) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::MovRM, vec![g64(dst), mem_vreg(base, disp)])
    }
    fn store(base: u32, disp: i32, src: u32) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::MovMR, vec![mem_vreg(base, disp), g64(src)])
    }

    fn new_func() -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_sroa_test".to_string(), sig);
        func.ensure_block(Block(0));
        func.next_vreg = 64;
        func
    }

    fn count_opcode(insts: &[X86ISelInst], opcode: X86Opcode) -> usize {
        insts.iter().filter(|i| i.opcode == opcode).count()
    }

    fn entry_insts(func: &X86ISelFunction) -> &[X86ISelInst] {
        &func.blocks.get(&Block(0)).unwrap().insts
    }

    /// A struct `(i64,i64)`: store at +0, derived-lea +8, store at +8, load +0.
    /// Every address use is in the envelope → fully scalar-replaced.
    #[test]
    fn x86_sroa_promotes_struct_store_store_load() {
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0), // v100 = lea [slot0]
            X86ISelInst::new(X86Opcode::Lea, vec![g64(101), mem_vreg(100, 8)]), // v101 = lea [v100+8]
            store(100, 0, 10),                                                  // [v100+0] = v10
            store(101, 0, 11),                                                  // [v101+0] = v11
            load(12, 100, 0),                                                   // v12 = [v100+0]
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(16, 8)];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(pass.run_on_function(&mut func), "SROA should fire");

        let insts = entry_insts(&func);
        assert_eq!(
            count_opcode(insts, X86Opcode::Lea),
            0,
            "roots/derived removed"
        );
        assert_eq!(count_opcode(insts, X86Opcode::MovRM), 0, "load promoted");
        assert_eq!(count_opcode(insts, X86Opcode::MovMR), 0, "stores promoted");
        assert!(count_opcode(insts, X86Opcode::MovRR) >= 3, "moves present");
        assert_eq!(count_opcode(insts, X86Opcode::Ret), 1);
    }

    /// The fat-pointer slice shape: base+len stored once, reloaded in a loop.
    /// Both reloads must be promoted out of the memory world.
    #[test]
    fn x86_sroa_promotes_fatptr_reload_in_loop() {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("saxpy_like".to_string(), sig);
        let bb0 = Block(0);
        let bb1 = Block(1);
        let bb2 = Block(2);
        for b in [bb0, bb1, bb2] {
            func.ensure_block(b);
        }
        func.next_vreg = 64;
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(16, 8)];

        // bb0: root, spill base(+0) and len(+8), jmp bb1
        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1];
        for inst in [
            root_lea(100, 0),
            store(100, 0, 10), // base
            store(100, 8, 11), // len
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        ] {
            func.push_inst(bb0, inst);
        }

        // bb1: reload base and len every iteration; jcc bb1 / bb2
        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb1, bb2];
        for inst in [
            load(20, 100, 0),
            load(21, 100, 8),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::B),
                    X86ISelOperand::Block(bb1),
                ],
            ),
        ] {
            func.push_inst(bb1, inst);
        }
        func.push_inst(bb2, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(
            pass.run_on_function(&mut func),
            "fat-ptr slot should promote"
        );

        let loop_insts = &func.blocks.get(&bb1).unwrap().insts;
        assert_eq!(
            count_opcode(loop_insts, X86Opcode::MovRM),
            0,
            "the fat-ptr reloads must be gone from the loop body"
        );
        assert_eq!(
            count_opcode(loop_insts, X86Opcode::MovRR),
            2,
            "reloads → reg moves"
        );
    }

    /// REFUSAL: the slot address is stored as a VALUE (escape). Must NOT promote.
    #[test]
    fn x86_sroa_refuses_address_stored_as_value() {
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0),
            // [v50] = v100  — store the address itself: escape.
            store(50, 0, 100),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];

        let before = entry_insts(&func).to_vec();
        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(
            !pass.run_on_function(&mut func),
            "escape via stored address"
        );
        let after = entry_insts(&func);
        assert_eq!(after.len(), before.len(), "IR unchanged on escape");
        assert_eq!(count_opcode(after, X86Opcode::Lea), 1);
    }

    /// REFUSAL: the slot address is passed to a call (moved into RAX/an arg reg).
    #[test]
    fn x86_sroa_refuses_address_to_call() {
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0),
            store(100, 0, 10),
            // mov RAX, v100 — marshal the address into a physical reg (escape).
            X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RAX), g64(100)]),
            X86ISelInst::new(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(!pass.run_on_function(&mut func), "escape via call arg");
        assert_eq!(count_opcode(entry_insts(&func), X86Opcode::Lea), 1);
    }

    /// REFUSAL: the slot address is used as a SIB index (address arithmetic we
    /// cannot scalar-replace). Must NOT promote.
    #[test]
    fn x86_sroa_refuses_address_as_sib_index() {
        let mut func = new_func();
        let b = Block(0);
        let sib_load = X86ISelInst::new(
            X86Opcode::MovRMSib,
            vec![
                g64(20),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(g64(30)),
                    index: Box::new(g64(100)), // the slot address as an index!
                    scale: 8,
                    disp: 0,
                },
            ],
        );
        for inst in [
            root_lea(100, 0),
            store(100, 0, 10),
            sib_load,
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(!pass.run_on_function(&mut func), "escape via SIB index");
        assert_eq!(count_opcode(entry_insts(&func), X86Opcode::Lea), 1);
    }

    /// REFUSAL: a load with no reaching store must not read an undefined shadow.
    #[test]
    fn x86_sroa_refuses_load_without_reaching_store() {
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0),
            load(20, 100, 0), // load before any store
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(!pass.run_on_function(&mut func), "no reaching store");
        assert_eq!(count_opcode(entry_insts(&func), X86Opcode::MovRM), 1);
    }

    /// REFUSAL: a direct `[StackSlot]`-addressed store to the same slot (not
    /// through the root vreg) is an invisible writer — the slot must bail.
    #[test]
    fn x86_sroa_refuses_direct_slot_access() {
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0),
            // direct [slot0] store, bypassing the root vreg
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_slot(0, 0), g64(10)]),
            load(20, 100, 0),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(
            !pass.run_on_function(&mut func),
            "direct slot access must bail"
        );
        assert_eq!(count_opcode(entry_insts(&func), X86Opcode::MovRM), 1);
    }

    /// REFUSAL: a multi-def derived-address vreg (loop-phi carrier) must bail.
    #[test]
    fn x86_sroa_refuses_multidef_alias() {
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0),
            X86ISelInst::new(X86Opcode::MovRR, vec![g64(101), g64(100)]), // v101 = v100 (def 1)
            load(20, 101, 0),
            X86ISelInst::new(X86Opcode::MovRR, vec![g64(101), g64(20)]), // v101 redefined (def 2)
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(
            !pass.run_on_function(&mut func),
            "multi-def alias must bail"
        );
    }

    /// REFUSAL: mixed widths at the same offset (32-bit store, 64-bit load).
    #[test]
    fn x86_sroa_refuses_mixed_width_at_offset() {
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0),
            // 32-bit store at +0
            X86ISelInst::new(
                X86Opcode::MovMR32,
                vec![
                    mem_vreg(100, 0),
                    X86ISelOperand::VReg(VReg::new(10, RegClass::Gpr32)),
                ],
            ),
            // 64-bit load at +0 — inconsistent bucket
            load(20, 100, 0),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(!pass.run_on_function(&mut func), "mixed width must bail");
    }

    /// REFUSAL: an atomic/volatile load (proof_origin marker) must never promote.
    #[test]
    fn x86_sroa_refuses_atomic_marked_access() {
        use trust_cg_lower::x86_64_isel::X86ProofOrigin;
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0),
            store(100, 0, 10),
            load(20, 100, 0).with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(!pass.run_on_function(&mut func), "atomic access must bail");
    }

    /// Two independent slots both promote and get distinct shadow vregs.
    #[test]
    fn x86_sroa_promotes_two_independent_slots() {
        let mut func = new_func();
        let b = Block(0);
        for inst in [
            root_lea(100, 0),
            store(100, 0, 10),
            load(20, 100, 0),
            root_lea(101, 1),
            store(101, 0, 11),
            load(21, 101, 0),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(b, inst);
        }
        func.stack_slots = vec![
            trust_cg_lower::function::StackSlotInfo::new(8, 8),
            trust_cg_lower::function::StackSlotInfo::new(8, 8),
        ];

        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(pass.run_on_function(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(count_opcode(insts, X86Opcode::Lea), 0);
        assert_eq!(count_opcode(insts, X86Opcode::MovRM), 0);
        assert_eq!(count_opcode(insts, X86Opcode::MovMR), 0);
        // distinct shadow vregs (>= 64)
        let mut shadows: HashSet<u32> = HashSet::new();
        for inst in insts {
            if inst.opcode == X86Opcode::MovRR
                && let Some(X86ISelOperand::VReg(d)) = inst.operands.first()
                && d.id >= 64
            {
                shadows.insert(d.id);
            }
        }
        assert_eq!(shadows.len(), 2, "two slots must not alias one shadow vreg");
    }

    /// A straight-line function with no slot roots is a no-op.
    #[test]
    fn x86_sroa_noop_without_roots() {
        let mut func = new_func();
        let b = Block(0);
        func.push_inst(b, X86ISelInst::new(X86Opcode::MovRI, vec![g64(10), imm(1)]));
        func.push_inst(b, X86ISelInst::new(X86Opcode::Ret, vec![]));
        let mut pass = X86ScalarReplacementOfAggregates::new();
        assert!(!pass.run_on_function(&mut func));
    }
}
