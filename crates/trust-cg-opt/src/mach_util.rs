// trust-cg-opt/mach_util.rs - shared MachFunction query helpers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Small AArch64 `MachFunction` queries shared by the loop-idiom and NEON
//! recognizers. Each one replaces private copies that were textually identical
//! in every module that now imports it; recognizers whose legality depends on a
//! different definition (for example a `copy_like` that also accepts
//! `FmovFprFpr`) keep their own.

use crate::effects::for_each_inst_def;
use crate::fast_hash::FxHashMap as HashMap;
use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, VReg};

/// `MovR(d, s)` / `Copy(d, s)` / `AddRI(d, s, 0)` copy idioms => `(d, s)`.
pub(crate) fn copy_like(inst: &MachInst) -> Option<(VReg, VReg)> {
    match inst.opcode {
        AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
            Some((inst.operands[0].as_vreg()?, inst.operands[1].as_vreg()?))
        }
        AArch64Opcode::AddRI
            if inst.operands.len() == 3 && inst.operands[2].as_imm() == Some(0) =>
        {
            Some((inst.operands[0].as_vreg()?, inst.operands[1].as_vreg()?))
        }
        _ => None,
    }
}

/// Every `Block` operand of `inst`, in operand order.
pub(crate) fn branch_targets(inst: &MachInst) -> Vec<BlockId> {
    inst.operands
        .iter()
        .filter_map(|op| match op {
            MachOperand::Block(b) => Some(*b),
            _ => None,
        })
        .collect()
}

/// Whether a copy of `block` built by rewriting its instructions' `Block`
/// operands has `block`'s own out-edges: the block's successor set equals the
/// set of its `Block` operands, and no instruction reads a jump table.
///
/// A pass that copies a block together with its control flow copies each
/// instruction with its `Block` operands mapped to the copies, then gives the
/// copy the successors those operands name (or the original's successor list,
/// mapped the same way). `loop-unswitch`, `alias-hoist`, the bounded-early-exit
/// and diamond full unrolls of `loop-unroll` and the machine inliner require
/// this predicate of every block they copy. An edge carried any other way is
/// shared with, or lost by, the copy:
///
/// * a jump-table dispatch (`Adr t, JumpTableIndex(k); LdrswRO; AddRR; Br`)
///   indexes `MachFunction::jump_tables[k]`, whose entries name the ORIGINAL
///   case blocks, so the copy dispatches into the original body while its own
///   case blocks become unreachable;
/// * a fall-through edge follows the block layout, which the copy does not
///   share.
///
/// The successor-set comparison catches both, including a dispatch whose `Adr`
/// was hoisted out of the block; the operand scan names the jump-table case
/// directly. A `Block` operand that is not an out-edge (a `Phi` predecessor)
/// also fails it, since a copy wired from its operands would gain that edge.
pub(crate) fn clone_reproduces_out_edges(func: &MachFunction, block: BlockId) -> bool {
    let mut named: Vec<BlockId> = Vec::new();
    for &iid in &func.block(block).insts {
        let inst = func.inst(iid);
        if inst
            .operands
            .iter()
            .any(|op| op.as_jump_table_index().is_some())
        {
            return false;
        }
        for target in branch_targets(inst) {
            if !named.contains(&target) {
                named.push(target);
            }
        }
    }
    let succs = &func.block(block).succs;
    succs.iter().all(|s| named.contains(s)) && named.iter().all(|n| succs.contains(n))
}

/// [`clone_reproduces_out_edges`] for every block of a body that one
/// transform copies.
pub(crate) fn body_clone_reproduces_out_edges<'a>(
    func: &MachFunction,
    body: impl IntoIterator<Item = &'a BlockId>,
) -> bool {
    body.into_iter()
        .all(|&block| clone_reproduces_out_edges(func, block))
}

/// The block (by index in `func.blocks`) that contains `target`.
pub(crate) fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, block) in func.blocks.iter().enumerate() {
        if block.insts.contains(&target) {
            return Some(BlockId(u32::try_from(idx).ok()?));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Every-path value resolution over a last-wins def map
// ---------------------------------------------------------------------------
//
// The machine IR is NOT SSA. `effects::build_reaching_def_map` keeps, per vreg
// id, only the def LAST in the emitted layout, so a register written on several
// paths (one `Movz` per exit edge of a fully unrolled early-exit search, one
// copy per incoming edge of a phi, a preheader copy plus a back-edge copy)
// resolves to whichever of those writes happens to be laid out last. Reading a
// constant, or walking a copy, through that def is wrong code on every other
// path.
//
// The resolvers below therefore never TRUST the map's def. They use it only as
// a cheap first filter (the last def must already have the right shape), then
// decide from EVERY instruction in the layout that writes the id:
//
// * a copy is walked only when it is the id's ONLY def ([`sole_copy_source`]);
// * a constant is returned only when every def of the id materializes that
//   same constant ([`const_value`], [`materialized_value`]).
//
// Defs are matched by vreg ID through the audited operand-role model
// (`effects::for_each_inst_def`), class-blind: a W-view write clobbers the X
// view, so matching by id only ever adds defs (fail closed). Instructions
// outside `func.block_order` never execute and are not defs, as in the map.
//
// No use point is involved, so "the same value on every path" is the only claim
// these make. A caller that has a use point and needs a value that differs per
// path reads it with `crate::reaching_const` instead.

/// A def map the every-path resolvers can read: the LAST def of each vreg id in
/// the emitted layout (`effects::build_reaching_def_map` semantics), plus,
/// optionally, an index of how many instructions in the layout write each id.
///
/// The index is a cost knob, not a correctness one: without it the resolvers
/// count defs by scanning the function, which finds what an index built from
/// the same function state holds.
pub(crate) trait DefLookup {
    /// The last def of `id` in the emitted layout.
    fn last_def(&self, id: u32) -> Option<InstId>;

    /// `effects::live_def_count(func, id)` when this lookup indexes it for the
    /// current state of `func`; `None` makes the resolvers scan.
    fn indexed_def_count(&self, _func: &MachFunction, _id: u32) -> Option<usize> {
        None
    }
}

impl DefLookup for HashMap<u32, InstId> {
    fn last_def(&self, id: u32) -> Option<InstId> {
        self.get(&id).copied()
    }
}

/// A reference reads through, index included, so a caller holding `&map` or
/// `&&map` reaches the same lookup.
impl<T: DefLookup + ?Sized> DefLookup for &T {
    fn last_def(&self, id: u32) -> Option<InstId> {
        (**self).last_def(id)
    }

    fn indexed_def_count(&self, func: &MachFunction, id: u32) -> Option<usize> {
        (**self).indexed_def_count(func, id)
    }
}

/// Whether `inst` writes a vreg with `id` (any register class) at a modeled
/// def position. Defs are always explicit vreg operands, so an instruction that
/// does not name `id` at all is rejected before the role table is consulted.
pub(crate) fn writes_id(inst: &MachInst, id: u32) -> bool {
    if !inst
        .operands
        .iter()
        .any(|op| matches!(op, MachOperand::VReg(v) if v.id == id))
    {
        return false;
    }
    let mut hit = false;
    for_each_inst_def(inst, |d| hit |= d.id == id);
    hit
}

/// One instruction in the emitted layout that writes a queried id.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DefSite {
    pub(crate) block: BlockId,
    /// Index of the instruction in `block`'s instruction list.
    pub(crate) pos: usize,
    pub(crate) inst: InstId,
}

/// Every instruction in the emitted layout that writes `id`, in layout order.
pub(crate) fn live_def_sites(func: &MachFunction, id: u32) -> Vec<DefSite> {
    let mut sites = Vec::new();
    for &block in &func.block_order {
        for (pos, &inst) in func.block(block).insts.iter().enumerate() {
            if writes_id(func.inst(inst), id) {
                sites.push(DefSite { block, pos, inst });
            }
        }
    }
    sites
}

/// The ONE instruction in the emitted layout that writes `id`, or `None` when
/// there is none or more than one. With an index, the map's last def is that
/// instruction exactly when the index counts one def; without one, the scan
/// must find the instruction the map names (a map from another function state
/// is not trusted).
pub(crate) fn sole_def<D: DefLookup + ?Sized>(
    func: &MachFunction,
    def: &D,
    id: u32,
) -> Option<InstId> {
    let last = def.last_def(id)?;
    if let Some(n) = def.indexed_def_count(func, id) {
        return (n == 1).then_some(last);
    }
    let mut found = None;
    for &block in &func.block_order {
        for &inst in &func.block(block).insts {
            if writes_id(func.inst(inst), id) && found.replace(inst).is_some() {
                return None;
            }
        }
    }
    found.filter(|&only| only == last)
}

/// `v`'s copy source when the only instruction writing `v`'s id is a
/// value-preserving copy ([`copy_like`]) into exactly `v`; `None` otherwise.
///
/// A copy into a register written anywhere else (a phi copy into a block
/// parameter, an outer latch copying the inner induction into a register the
/// entry also writes) holds the copied value on SOME paths only, so it is not
/// walked.
pub(crate) fn sole_copy_source<D: DefLookup + ?Sized>(
    func: &MachFunction,
    def: &D,
    v: VReg,
) -> Option<VReg> {
    let last = def.last_def(v.id)?;
    let (dst, src) = copy_like(func.inst(last))?;
    if dst != v {
        return None;
    }
    (sole_def(func, def, v.id)? == last).then_some(src)
}

/// Follow value-preserving copies (bounded) from `v` to the register they
/// copy, stepping only through [`sole_copy_source`], so the result holds the
/// same value as `v` on every path. A multi-def register ends the walk.
pub(crate) fn strip_copies<D: DefLookup + ?Sized>(func: &MachFunction, def: &D, v: VReg) -> VReg {
    let mut v = v;
    for _ in 0..16 {
        match sole_copy_source(func, def, v) {
            Some(src) => v = src,
            None => return v,
        }
    }
    v
}

/// True iff `v` IS `target`, or reaches it through [`sole_copy_source`] steps.
/// The walk never steps PAST `target` (its defs are not read), so the target
/// can be a multi-def induction variable.
pub(crate) fn copies_reg<D: DefLookup + ?Sized>(
    func: &MachFunction,
    def: &D,
    v: VReg,
    target: VReg,
) -> bool {
    let mut v = v;
    for _ in 0..16 {
        if v == target {
            return true;
        }
        match sole_copy_source(func, def, v) {
            Some(src) => v = src,
            None => return false,
        }
    }
    false
}

/// The 16-bit immediate of a canonical shift-zero `Movz` (2-operand, or an
/// explicit `lsl #0`), the one form [`const_value`] folds.
fn narrow_movz(inst: &MachInst) -> Option<i64> {
    let (_, value) = crate::reaching_const::movz_value(inst)?;
    i64::try_from(value).ok()
}

/// The constant `val` holds wherever it is read: every instruction in the
/// emitted layout that writes `val`'s id is a shift-zero `Movz` of the SAME
/// 16-bit immediate. A register written with different constants on different
/// paths (a phi of constants, the per-exit-edge writes of an unrolled search),
/// or written by anything else, is `None`.
///
/// `def` is a last-wins map; its def is only the cheap first filter.
pub(crate) fn const_value<D: DefLookup + ?Sized>(
    func: &MachFunction,
    def: &D,
    val: VReg,
) -> Option<i64> {
    let k = narrow_movz(func.inst(def.last_def(val.id)?))?;
    if def.indexed_def_count(func, val.id) == Some(1) {
        return Some(k);
    }
    let mut seen = false;
    for &block in &func.block_order {
        for &inst in &func.block(block).insts {
            let inst = func.inst(inst);
            if writes_id(inst, val.id) {
                if narrow_movz(inst) != Some(k) {
                    return None;
                }
                seen = true;
            }
        }
    }
    seen.then_some(k)
}

/// The constant `v` holds wherever it is read, for a register materialized by
/// a shift-zero `Movz` plus the `Movk`s that patch it, which covers every value
/// a 64-bit register can hold.
///
/// Every instruction in the emitted layout that writes `v`'s id must belong to
/// a RUN: a `Movz` into exactly `v`, then `Movk`s into exactly `v` at the
/// immediately following positions of the same block. No other instruction
/// sits inside a run, so a read outside one sees a complete run's value, and
/// every run must produce the same value. Anything else (a `Movk` patching a
/// value from another block, a run interrupted by another instruction, a copy,
/// two runs of different constants) is `None`.
pub(crate) fn materialized_value<D: DefLookup + ?Sized>(
    func: &MachFunction,
    def: &D,
    v: VReg,
) -> Option<u64> {
    let last = func.inst(def.last_def(v.id)?);
    match last.opcode {
        AArch64Opcode::Movz if def.indexed_def_count(func, v.id) == Some(1) => {
            let (dst, value) = crate::reaching_const::movz_value(last)?;
            return (dst == v).then_some(value);
        }
        AArch64Opcode::Movz | AArch64Opcode::Movk => {}
        _ => return None,
    }
    materialized_runs_value(func, v, &live_def_sites(func, v.id))
}

/// The value every run in `sites` (all the defs of `v`'s id, in layout order,
/// as [`live_def_sites`] lists them) produces, by the rule of
/// [`materialized_value`]; `None` for no sites.
pub(crate) fn materialized_runs_value(
    func: &MachFunction,
    v: VReg,
    sites: &[DefSite],
) -> Option<u64> {
    use crate::reaching_const::{apply_movk, movz_value};
    // The value every completed run produced, and the run being read.
    let mut agreed: Option<u64> = None;
    let mut run: Option<(DefSite, u64)> = None;
    let agrees = |run: Option<(DefSite, u64)>, agreed: &mut Option<u64>| match (run, *agreed) {
        (None, _) => true,
        (Some((_, value)), None) => {
            *agreed = Some(value);
            true
        }
        (Some((_, value)), Some(seen)) => value == seen,
    };
    for &site in sites {
        let inst = func.inst(site.inst);
        match inst.opcode {
            AArch64Opcode::Movz => {
                if !agrees(run.take(), &mut agreed) {
                    return None;
                }
                let (dst, value) = movz_value(inst)?;
                if dst != v {
                    return None;
                }
                run = Some((site, value));
            }
            AArch64Opcode::Movk => {
                let (prev, value) = run?;
                if prev.block != site.block || prev.pos + 1 != site.pos {
                    return None;
                }
                run = Some((site, apply_movk(inst, v, value)?));
            }
            _ => return None,
        }
    }
    if !agrees(run, &mut agreed) {
        return None;
    }
    agreed
}

/// [`materialized_value`] of the register `val` copies ([`strip_copies`]), as
/// a non-negative `i64` (a value with bit 63 set is `None`).
pub(crate) fn copied_const<D: DefLookup + ?Sized>(
    func: &MachFunction,
    def: &D,
    val: VReg,
) -> Option<i64> {
    let v = strip_copies(func, def, val);
    i64::try_from(materialized_value(func, def, v)?).ok()
}

#[cfg(test)]
#[path = "mach_util_tests.rs"]
mod tests;
