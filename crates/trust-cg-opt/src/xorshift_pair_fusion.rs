// trust-cg-opt - Latency fusion of a left-then-right xorshift step pair
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shorten a loop-carried xorshift recurrence by one cycle per step pair.
//!
//! The xorshift step `t = x ^ (x << a)` selects to one `EOR Xt, Xx, Xx, LSL
//! #a`. On the Apple M4 an ALU operation reads its SHIFTED operand two cycles
//! after that operand is produced and its plain operand one cycle after
//! (measured: a chain of 4 dependent `eor` through the shifted operand runs at
//! 2.01 cycles each, through the plain operand at 1.06, and `ubfiz` at 1.00;
//! `reports/perf/2026-10-01-darwin-runtime-per-program`). Each step therefore
//! costs 2 cycles of latency, and `xorshift64` (`<< 13, >> 7, << 17`) costs 6.
//! A loop whose next state is that function of its current state (the
//! corpus's `p1_xorshift`; the RNG in front of the unpredictable branches of
//! `b1_mispredict` and `p6_branch_match`) runs no faster than its recurrence.
//!
//! # The rewrite
//!
//! A left step followed by a right step,
//!
//! ```text
//!   t = EorRRLsl t, x, x, #a        ; t = x ^ (x << a)
//!   y = EorRRLsr y, t, t, #b        ; y = t ^ (t >> b)
//! ```
//!
//! becomes
//!
//! ```text
//!   t = EorRRLsl t, x, x, #a        ; unchanged
//!   w = Ubfm     w, x, #(b-a)&63, #63-a   ; w = (x << a) >> b
//!   u = EorRRLsr u, w, x, #b        ; u = (x >> b) ^ ((x << a) >> b)
//!   y = EorRR    y, t, u            ; y = t ^ u
//! ```
//!
//! `y` is ready 3 cycles after `x` instead of 4: `t` and `u` are both ready at
//! 2 (`u` reads `x` through its shifted operand and `w`, ready at 1, through
//! its plain one), and the plain `EorRR` adds 1. Two instructions are added.
//!
//! # Why it is the same value
//!
//! A logical right shift distributes over XOR, so
//! `t >> b = (x >> b) ^ ((x << a) >> b)` and `y = t ^ (t >> b) = t ^ u`. For
//! `1 <= a, b <= 63`, `(x << a) >> b` is one unsigned bitfield move: with
//! `imms = 63 - a` and `immr = (b - a) mod 64`, `UBFM` is `UBFIZ x, #(a-b),
//! #(64-a)` when `a > b` (`imms < immr`), `UBFX x, #0, #(64-a)` when `a == b`,
//! and `UBFX x, #(b-a), #(64-b)` when `a < b`. The unit tests check the whole
//! rewrite against an interpreter of the four opcodes that follows the ARM
//! pseudocode, for every `(a, b)` in `1..=63` squared on random values.
//!
//! # When it fires (fail-closed)
//!
//! * both instructions in one block, `x`, `t`, `y` full-width `Gpr64`
//!   virtual registers, `x != t`, both shift operands the same register as
//!   the other source (genuinely `x ^ (x << a)` and `t ^ (t >> b)`);
//! * `t`'s definition is the last one before `y`'s, and `x` is not redefined
//!   between them, so `u` reads the `x` that `t` read. Redefinition is by
//!   numeric register ID: a 32-bit write of `x`'s ID clobbers `x` too;
//! * both steps carry ordinary metadata (default flags, no implicit
//!   definitions or uses, no proof annotation), and the right step's
//!   instruction is referenced by exactly one block, counting blocks outside
//!   the layout, because it is rewritten in place (OD-109). A refused pair
//!   allocates nothing;
//! * the block is in a loop that defines `x` (the back-edge writeback of a
//!   rolled recurrence, or the previous lane's result in an unrolled one), so
//!   the step pair is on the loop's dependence chain. Outside loops, or on a
//!   value the loop only reads, the two extra instructions buy no latency
//!   that matters.
//!
//! The mirrored pair (right then left) has no single-instruction
//! `(x >> a) << b` and is left alone. Runs late (after every pass that
//! recognizes the xorshift shape, before the scheduler) and is idempotent: the
//! rewritten `y` is a plain `EorRR`. Kill switch:
//! `TRUST_CG_DISABLE_PASSES=xorshiftfuse`.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    RegClass, VReg,
};

use crate::candidate::alloc;
use crate::dom::DomTree;
use crate::effects::inst_clobbers_vreg_id;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// The xorshift step-pair latency fusion pass.
pub struct XorshiftPairFusion;

impl MachinePass for XorshiftPairFusion {
    fn name(&self) -> &str {
        "xorshift-pair-fusion"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !has_right_step(func) {
            return false;
        }
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        let pairs = find_pairs(func, &loops);
        apply(func, pairs, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        if !has_right_step(func) {
            return false;
        }
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        let pairs = find_pairs(func, &loops);
        apply(func, pairs, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        if !has_right_step(func) {
            return false;
        }
        let pairs = {
            let (_, loops) = analyses.domtree_and_loops(func);
            find_pairs(func, loops)
        };
        // Instructions are added inside existing blocks; no edge changes.
        apply(func, pairs, Some(provenance))
    }
}

/// Prefilter: a right step `EorRRLsr` exists at all.
fn has_right_step(func: &MachFunction) -> bool {
    func.block_order
        .iter()
        .flat_map(|b| func.block(*b).insts.iter())
        .any(|&i| func.inst(i).opcode == AArch64Opcode::EorRRLsr)
}

fn pass_id() -> PassId {
    PassId::new("xorshift-pair-fusion")
}

/// Default flags, no implicit definitions or uses and no proof annotation: an
/// instruction whose meaning is its opcode and operands alone. Anything else
/// keeps the original (OD-109: no proof transfer is established here).
fn ordinary_metadata(inst: &MachInst) -> bool {
    inst.flags == inst.opcode.default_flags()
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
        && inst.proof.is_none()
}

/// `op [d, s, s2, #k]` with `d`, `s` full-width virtual registers, `s2` the
/// same value as `s` at this point (`s` itself, or a live in-block copy
/// `s2 = MovR s`, see `copies`) and `1 <= k <= 63`: `(d, s, k)`.
fn self_shift_step(
    inst: &MachInst,
    op: AArch64Opcode,
    copies: &HashMap<VReg, VReg>,
) -> Option<(VReg, VReg, i64)> {
    if inst.opcode != op || !ordinary_metadata(inst) {
        return None;
    }
    match inst.operands.as_slice() {
        [
            MachOperand::VReg(d),
            MachOperand::VReg(s),
            MachOperand::VReg(s2),
            MachOperand::Imm(k),
        ] if (s == s2 || copies.get(s2) == Some(s) || copies.get(s) == Some(s2))
            && d.class == RegClass::Gpr64
            && s.class == RegClass::Gpr64
            && s2.class == RegClass::Gpr64
            && (1..=63).contains(k) =>
        {
            // Name the value by the copy's source when `s` is the copy, so the
            // carried-register test sees the loop's own register.
            let base = if copies.get(s) == Some(s2) { *s2 } else { *s };
            Some((*d, base, *k))
        }
        _ => None,
    }
}

/// One recognized pair: the right step at `y_pos` of `block` reads `t`, the
/// left step of `x` by `a`; the right shift is `b`.
struct Pair {
    block: BlockId,
    y_inst: InstId,
    y: VReg,
    t: VReg,
    x: VReg,
    a: i64,
    b: i64,
}

fn find_pairs(func: &MachFunction, loops: &LoopAnalysis) -> Vec<Pair> {
    let mut out = Vec::new();
    // Blocks defining each numeric register ID (a W write defines the X
    // view's ID too).
    let mut def_blocks: HashMap<u32, HashSet<BlockId>> = HashMap::default();
    for &b in &func.block_order {
        for &id in &func.block(b).insts {
            crate::effects::for_each_inst_def(func.inst(id), |v| {
                def_blocks.entry(v.id).or_default().insert(b);
            });
        }
    }
    // Per loop: its blocks and the registers it defines. The state register
    // of a recurrence is defined in the loop: the back-edge writeback of a
    // rolled loop, or the previous lane's result in an unrolled body
    // (`scalar-unroll`'s verbatim lanes), where every lane's `x` is the last
    // lane's output and only the first is carried.
    let mut loop_defs: Vec<(HashSet<BlockId>, HashSet<u32>)> = Vec::new();
    for lp in loops.all_loops() {
        let blocks: HashSet<BlockId> = lp.body.iter().copied().collect();
        let defined: HashSet<u32> = def_blocks
            .iter()
            .filter(|(_, bs)| bs.iter().any(|b| blocks.contains(b)))
            .map(|(v, _)| *v)
            .collect();
        loop_defs.push((blocks, defined));
    }
    if loop_defs.is_empty() {
        return out;
    }
    for &block in &func.block_order {
        let carried_here: Vec<&HashSet<u32>> = loop_defs
            .iter()
            .filter(|(blocks, _)| blocks.contains(&block))
            .map(|(_, defs)| defs)
            .collect();
        if carried_here.is_empty() {
            continue;
        }
        let insts = &func.block(block).insts;
        // Last left step defining each vreg so far in this block, by position.
        let mut left: HashMap<VReg, (usize, VReg, i64)> = HashMap::default();
        // Live in-block copies `dst = MovR src`: both still hold the value
        // the copy gave them (neither redefined since).
        let mut copies: HashMap<VReg, VReg> = HashMap::default();
        for (pos, &id) in insts.iter().enumerate() {
            let inst = func.inst(id);
            // Operands are read before this instruction's own definitions.
            let left_step = self_shift_step(inst, AArch64Opcode::EorRRLsl, &copies);
            if let Some((y, t, b)) = self_shift_step(inst, AArch64Opcode::EorRRLsr, &copies)
                && let Some(&(t_pos, x, a)) = left.get(&t)
                && x != t
                && carried_here.iter().any(|defs| defs.contains(&x.id))
                && !insts[t_pos + 1..pos].iter().any(|&mid| {
                    let m = func.inst(mid);
                    inst_clobbers_vreg_id(m, x.id) || inst_clobbers_vreg_id(m, t.id)
                })
            {
                out.push(Pair {
                    block,
                    y_inst: id,
                    y,
                    t,
                    x,
                    a,
                    b,
                });
            }
            // Any definition retires an older left step or copy it overwrites
            // (its result or its source) before this one is recorded.
            left.retain(|&t, &mut (_, x, _)| {
                !inst_clobbers_vreg_id(inst, t.id) && !inst_clobbers_vreg_id(inst, x.id)
            });
            copies.retain(|&d, &mut src| {
                !inst_clobbers_vreg_id(inst, d.id) && !inst_clobbers_vreg_id(inst, src.id)
            });
            if let Some((t, x, a)) = left_step
                && t != x
            {
                left.insert(t, (pos, x, a));
            }
            if inst.opcode == AArch64Opcode::MovR
                && ordinary_metadata(inst)
                && let [MachOperand::VReg(d), MachOperand::VReg(src)] = inst.operands.as_slice()
                && d != src
                && d.class == src.class
            {
                copies.insert(*d, *src);
            }
        }
    }
    // The right step is rewritten in place: it must be referenced by exactly
    // one block, counting blocks outside the layout (a shared arena entry
    // would change in every block that links it). Counts saturate at two.
    if !out.is_empty() {
        let mut owners: HashMap<InstId, u8> = out.iter().map(|p| (p.y_inst, 0)).collect();
        for block in &func.blocks {
            for id in &block.insts {
                if let Some(n) = owners.get_mut(id) {
                    *n = n.saturating_add(1).min(2);
                }
            }
        }
        out.retain(|p| owners.get(&p.y_inst) == Some(&1));
    }
    out
}

fn apply(
    func: &mut MachFunction,
    pairs: Vec<Pair>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    // L10-P5: admit the function before synchronizing its counter, so a
    // counter left stale before this pass is refused (sticky on `func`,
    // reported by the pass manager) instead of being repaired here. After the
    // admission the synchronization changes nothing: this pass writes no
    // register it did not allocate.
    if pairs.is_empty()
        || func.admit_ids_before_allocation().is_err()
        || func.try_sync_vreg_counter().is_none()
    {
        return false;
    }
    let mut changed = false;
    for pair in pairs {
        let (Some(w), Some(u)) = (alloc(func, RegClass::Gpr64), alloc(func, RegClass::Gpr64))
        else {
            break;
        };
        let original = func.inst(pair.y_inst).clone();
        let mut ubfm = MachInst::new(
            AArch64Opcode::Ubfm,
            vec![
                MachOperand::VReg(w),
                MachOperand::VReg(pair.x),
                MachOperand::Imm((pair.b - pair.a).rem_euclid(64)),
                MachOperand::Imm(63 - pair.a),
            ],
        );
        ubfm.source_loc = original.source_loc;
        let mut eor_u = MachInst::new(
            AArch64Opcode::EorRRLsr,
            vec![
                MachOperand::VReg(u),
                MachOperand::VReg(w),
                MachOperand::VReg(pair.x),
                MachOperand::Imm(pair.b),
            ],
        );
        eor_u.source_loc = original.source_loc;
        let Some(w_id) = func.try_push_inst(ubfm) else {
            break;
        };
        let Some(u_id) = func.try_push_inst(eor_u) else {
            break;
        };
        let Some(pos) = func
            .block(pair.block)
            .insts
            .iter()
            .position(|&id| id == pair.y_inst)
        else {
            continue;
        };
        func.block_mut(pair.block)
            .insts
            .splice(pos..pos, [w_id, u_id]);
        let y_inst = func.inst_mut(pair.y_inst);
        y_inst.opcode = AArch64Opcode::EorRR;
        y_inst.operands = vec![
            MachOperand::VReg(pair.y),
            MachOperand::VReg(pair.t),
            MachOperand::VReg(u),
        ];
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_clone(pair.y_inst, w_id, pass_id());
            provenance.record_clone(pair.y_inst, u_id, pass_id());
            provenance.record_in_place_transform(pair.y_inst, pass_id());
        }
        changed = true;
    }
    changed
}

#[cfg(test)]
mod tests;
