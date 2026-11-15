// trust-cg-opt - Copy Propagation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Copy propagation pass for machine-level IR.
//!
//! When a same-class `MovR dst, src` instruction is the only definition of
//! `dst`, all uses of `dst` are replaced with `src`, and the MOV becomes dead
//! (subsequently removed by DCE).
//!
//! # Algorithm
//!
//! 1. Scan all instructions to find `MovR` instructions where:
//!    - The destination is a VReg.
//!    - The source is a VReg in the same register class as the destination.
//!    - The destination VReg has exactly one definition (this MOV).
//! 2. Build a replacement map: `dst → src`.
//! 3. Chase chains: if `src` itself maps to another register, follow
//!    the chain to the root source (avoiding cycles). Each chain edge is
//!    checked against source redefinitions so non-SSA registers still denote
//!    the same reaching value at the rewritten use.
//! 4. Replace all occurrences of `dst` with the resolved source in all
//!    instruction operands.
//!
//! The MOV instructions themselves are NOT removed by this pass — that's
//! left to DCE, which will see that `dst` is no longer used.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use trust_cg_ir::{BlockId, InstId, MachFunction, MachOperand, PassId, ProvenanceMap, VReg};

use crate::dom::DomTree;
use crate::effects::aarch64_def_operand_positions;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Copy propagation pass.
pub struct CopyPropagation;

impl MachinePass for CopyPropagation {
    fn name(&self) -> &str {
        "copy-prop"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        run_copy_prop(func, Some(&dom), None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let dom = analyses.domtree(func);
        run_copy_prop(func, Some(dom), None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = DomTree::compute(func);
        run_copy_prop(func, Some(&dom), Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = analyses.domtree(func);
        run_copy_prop(func, Some(dom), Some(provenance))
    }
}

#[derive(Debug, Clone, Copy)]
struct CopyInfo {
    src: VReg,
    block: BlockId,
    inst_index: usize,
}

#[derive(Debug, Clone, Copy)]
struct DefSite {
    block: BlockId,
    inst_index: usize,
}

fn run_copy_prop(
    func: &mut MachFunction,
    dom: Option<&DomTree>,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    // Step 1: Count definitions per VReg.
    let def_sites = collect_defs(func);
    let def_counts: HashMap<VReg, u32> = def_sites
        .iter()
        .map(|(vreg, sites)| (*vreg, sites.len() as u32))
        .collect();

    // Step 2: Find copy instructions (MovR dst, src) where dst has
    // exactly one definition.
    let mut copy_map: HashMap<VReg, CopyInfo> = HashMap::default();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (inst_index, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if !inst.is_move() {
                continue;
            }
            if inst.operands.len() < 2 {
                continue;
            }

            let dst = match &inst.operands[0] {
                MachOperand::VReg(v) => *v,
                _ => continue,
            };
            let src = match &inst.operands[1] {
                MachOperand::VReg(v) => *v,
                _ => continue,
            };

            // Only propagate transparent same-class copies. Mixed-class MovR
            // can carry width semantics such as Gpr32 -> Gpr64 zero-extension.
            if dst.class == src.class && def_counts.get(&dst).copied().unwrap_or(0) == 1 {
                copy_map.insert(
                    dst,
                    CopyInfo {
                        src,
                        block: *block_id,
                        inst_index,
                    },
                );
            }
        }
    }

    if copy_map.is_empty() {
        return false;
    }

    // Step 3: Replace operands throughout the function, but only where
    // the copy definition dominates the use. The previous global rewrite
    // was unsound for loop/block-arg paths because it ignored whether a
    // `MovR dst, src` had actually executed on the path reaching the use.
    let mut changed = false;
    let mut changed_insts: Vec<InstId> = Vec::new();
    for block_id in func.block_order.clone() {
        let block = func.block(block_id);
        for (inst_index, &inst_id) in block.insts.clone().iter().enumerate() {
            let inst = func.inst(inst_id);

            // Def positions as a bitmask over operand slots and the uses through
            // the visitor: no per-instruction HashSet, position Vecs or operand
            // clone. A use that is also a def (a tied operand) is skipped
            // exactly as before.
            let n = inst.operands.len();
            let def_mask = crate::effects::def_position_mask(inst.opcode, n);
            let mut replacements = Vec::new();
            crate::effects::aarch64_for_each_use_position(inst.opcode, n, |i| {
                if i < 64 && def_mask & (1u64 << i) != 0 {
                    return;
                }
                if let MachOperand::VReg(vreg) = &inst.operands[i]
                    && let Some(replacement) = resolve_use_replacement(
                        *vreg, block_id, inst_index, &copy_map, &def_sites, func, dom,
                    )
                {
                    replacements.push((i, replacement));
                }
            });

            if !replacements.is_empty() {
                let inst = func.inst_mut(inst_id);
                for (i, replacement) in replacements {
                    inst.operands[i] = MachOperand::VReg(replacement);
                }
                changed_insts.push(inst_id);
                changed = true;
            }
        }
    }

    if let Some(provenance) = provenance
        && !changed_insts.is_empty()
    {
        changed_insts.sort_unstable();
        changed_insts.dedup();
        for inst_id in changed_insts {
            provenance.record_in_place_transform(inst_id, PassId::new("copy-prop"));
        }
    }

    changed
}

/// Collect definition sites for each VReg across the function.
fn collect_defs(func: &MachFunction) -> HashMap<VReg, Vec<DefSite>> {
    let mut defs: HashMap<VReg, Vec<DefSite>> = HashMap::default();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (inst_index, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            for idx in aarch64_def_operand_positions(inst.opcode, inst.operands.len()) {
                let Some(MachOperand::VReg(vreg)) = inst.operands.get(idx) else {
                    continue;
                };
                defs.entry(*vreg).or_default().push(DefSite {
                    block: *block_id,
                    inst_index,
                });
            }
        }
    }

    defs
}

fn copy_reaches_use(
    copy: CopyInfo,
    use_block: BlockId,
    use_inst_index: usize,
    dom: Option<&DomTree>,
) -> bool {
    if copy.block == use_block {
        return copy.inst_index < use_inst_index;
    }

    dom.is_some_and(|domtree| domtree.dominates(copy.block, use_block))
}

fn def_known_before_copy(def: DefSite, copy: CopyInfo, dom: Option<&DomTree>) -> bool {
    if def.block == copy.block {
        return def.inst_index < copy.inst_index;
    }

    dom.is_some_and(|domtree| domtree.dominates(def.block, copy.block))
}

/// Whether a CFG path of at least one edge leads from `from` to `to`. With
/// `from == to`, whether `from` lies on a cycle.
fn block_reaches(func: &MachFunction, from: BlockId, to: BlockId) -> bool {
    let mut stack = vec![from];
    let mut seen = HashSet::default();

    while let Some(block_id) = stack.pop() {
        if !seen.insert(block_id) {
            continue;
        }

        for &succ in &func.block(block_id).succs {
            if succ == to {
                return true;
            }
            stack.push(succ);
        }
    }

    false
}

/// Whether `def` may reach the use at `use_inst_index` of `use_block` along a
/// CFG path that does not run `copy` after it. `false` is exact; `true` may be
/// conservative, and `def_known_before_copy` is checked separately.
///
/// In the use's own block, a def before the use reaches it directly. A def at
/// or after the use (an instruction reads its operands before it writes them)
/// reaches it only by leaving the block and re-entering it at its top, so it
/// counts only when some such re-entry avoids the copy
/// (`use_block_reentered_without_copy`). Across blocks, a def reaches the use
/// when its block can reach the use's block, whether or not that path runs the
/// copy. That is checked only with a dominator tree: without one,
/// `copy_reaches_use` admits only a copy above the use in the use's block,
/// which every path from another block re-runs before the use.
fn def_can_reach_use(
    def: DefSite,
    copy: CopyInfo,
    use_block: BlockId,
    use_inst_index: usize,
    func: &MachFunction,
    dom: Option<&DomTree>,
) -> bool {
    if def.block == use_block {
        return def.inst_index < use_inst_index
            || use_block_reentered_without_copy(func, copy, use_block, use_inst_index);
    }

    if dom.is_some_and(|domtree| domtree.dominates(def.block, use_block)) {
        return true;
    }

    dom.is_some() && block_reaches(func, def.block, use_block)
}

/// Whether some CFG path leaves `use_block` and re-enters it at its top
/// without running the copy before the use. Exact over CFG paths.
///
/// A re-entry runs the copy first when the copy sits above the use in
/// `use_block` itself. Otherwise a path runs the copy exactly when it passes
/// through the copy's block, which it enters at the top and, being bound for
/// another block, leaves at the bottom; the search does not continue through
/// that block. This keeps a loop whose copy sits in a block on every cycle
/// back to the use, such as the edge block that is the body's only
/// predecessor, and refuses one with a cycle that bypasses that block.
fn use_block_reentered_without_copy(
    func: &MachFunction,
    copy: CopyInfo,
    use_block: BlockId,
    use_inst_index: usize,
) -> bool {
    if copy.block == use_block && copy.inst_index < use_inst_index {
        return false;
    }

    let mut stack: Vec<BlockId> = func.block(use_block).succs.clone();
    let mut seen = HashSet::default();

    while let Some(block_id) = stack.pop() {
        if block_id == use_block {
            return true;
        }
        if block_id == copy.block || !seen.insert(block_id) {
            continue;
        }
        stack.extend(func.block(block_id).succs.iter().copied());
    }

    false
}

/// Whether `src` still holds, at the use, the value the copy read from it:
/// every definition of `src` either cannot reach the use or reaches it only
/// along paths on which the copy runs between that definition and the use. A
/// def known to run before the copy qualifies because the copy dominates the
/// use, so every path from that def to the use passes the copy.
fn source_is_stable_at_use(
    src: VReg,
    copy: CopyInfo,
    use_block: BlockId,
    use_inst_index: usize,
    def_sites: &HashMap<VReg, Vec<DefSite>>,
    func: &MachFunction,
    dom: Option<&DomTree>,
) -> bool {
    let Some(defs) = def_sites.get(&src) else {
        return true;
    };

    defs.iter().copied().all(|def| {
        def_known_before_copy(def, copy, dom)
            || !def_can_reach_use(def, copy, use_block, use_inst_index, func, dom)
    })
}

fn resolve_use_replacement(
    original: VReg,
    use_block: BlockId,
    use_inst_index: usize,
    copy_map: &HashMap<VReg, CopyInfo>,
    def_sites: &HashMap<VReg, Vec<DefSite>>,
    func: &MachFunction,
    dom: Option<&DomTree>,
) -> Option<VReg> {
    let mut current = original;
    let mut seen = HashSet::default();
    const MAX_CHAIN: usize = 64;

    for _ in 0..MAX_CHAIN {
        if !seen.insert(current) {
            break;
        }

        let Some(copy) = copy_map.get(&current).copied() else {
            break;
        };
        if !copy_reaches_use(copy, use_block, use_inst_index, dom) {
            break;
        }
        if !source_is_stable_at_use(
            copy.src,
            copy,
            use_block,
            use_inst_index,
            def_sites,
            func,
            dom,
        ) {
            break;
        }

        current = copy.src;
    }

    (current != original).then_some(current)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::MachinePass;
    use trust_cg_ir::{
        AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, RegClass, Signature,
        TransformKind, TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg_class(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new("test_cp".to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    #[test]
    fn test_simple_copy_prop() {
        // v1 = mov v0
        // v2 = add v1, #5  → v2 = add v0, #5
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, add, ret]);

        let mut cp = CopyPropagation;
        assert!(cp.run(&mut func));

        // add should now use v0 instead of v1
        let add_inst = func.inst(InstId(1));
        assert_eq!(add_inst.operands[1], vreg(0));
    }

    #[test]
    fn test_copy_prop_provenance_marks_rewritten_use_in_place() {
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, add, ret]);
        let mov_id = func.block(func.entry).insts[0];
        let add_id = func.block(func.entry).insts[1];
        let ret_id = func.block(func.entry).insts[2];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(20), &[mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(21), &[add_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(22), &[ret_id], PassId::new("isel"));

        let mut cp = CopyPropagation;
        let mut analyses = AnalysisCache::new();
        assert!(cp.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let add_inst = func.inst(add_id);
        assert_eq!(add_inst.operands[1], vreg(0));

        let add_entry = provenance.get_entry(add_id).unwrap();
        let transform = add_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("copy-prop"));
        assert_eq!(transform.kind, TransformKind::Survived);
        assert!(add_entry.is_active());

        assert_eq!(provenance.get_entry(mov_id).unwrap().transforms.len(), 1);
        assert_eq!(provenance.get_entry(ret_id).unwrap().transforms.len(), 1);
    }

    #[test]
    fn test_chain_copy_prop() {
        // v1 = mov v0
        // v2 = mov v1
        // v3 = add v2, #5  → v3 = add v0, #5
        let m1 = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let m2 = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(1)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m1, m2, add, ret]);

        let mut cp = CopyPropagation;
        assert!(cp.run(&mut func));

        let add_inst = func.inst(InstId(2));
        assert_eq!(add_inst.operands[1], vreg(0));
    }

    #[test]
    fn test_direct_run_propagates_to_dominated_cross_block_use() {
        // entry: v1 = mov v0; br body
        // body:  v2 = add v1, #1  → v2 = add v0, #1
        //
        // The direct MachinePass::run entrypoint computes the same dominator
        // context that pass-manager stats/fixpoint paths pass through the cache.
        let mut func = MachFunction::new(
            "cp_direct_cross_block".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let body = func.create_block();

        let mov = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]));
        let br = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(body)],
        ));
        func.append_inst(entry, mov);
        func.append_inst(entry, br);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg(1), imm(1)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(body, add);
        func.append_inst(body, ret);

        func.add_edge(entry, body);

        let mut cp = CopyPropagation;
        assert!(cp.run(&mut func));
        assert_eq!(func.inst(add).operands[1], vreg(0));
    }

    #[test]
    fn test_direct_provenance_propagates_to_dominated_cross_block_use() {
        let mut func = MachFunction::new(
            "cp_direct_provenance_cross_block".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let body = func.create_block();

        let mov = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]));
        let br = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(body)],
        ));
        func.append_inst(entry, mov);
        func.append_inst(entry, br);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg(1), imm(1)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(body, add);
        func.append_inst(body, ret);

        func.add_edge(entry, body);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(30), &[mov], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(31), &[br], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(32), &[add], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(33), &[ret], PassId::new("isel"));

        let mut cp = CopyPropagation;
        assert!(cp.run_with_provenance(&mut func, &mut provenance));

        assert_eq!(func.inst(add).operands[1], vreg(0));
        let add_entry = provenance.get_entry(add).unwrap();
        let transform = add_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("copy-prop"));
        assert_eq!(transform.kind, TransformKind::Survived);
    }

    #[test]
    fn test_no_prop_multiple_defs() {
        // v1 = mov v0
        // v1 = add v1, #1  (second def of v1 → don't propagate)
        // v2 = add v1, #5
        let m1 = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let a1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(1), imm(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m1, a1, a2, ret]);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));
    }

    #[test]
    fn test_no_prop_through_scalar_writeback_base_def() {
        // v1 = mov v0
        // str-post v5, v1, #8  (updates v1)
        // v2 = add v1, #1      (must observe post-writeback v1)
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let writeback = MachInst::new(AArch64Opcode::StrPostIndex, vec![vreg(5), vreg(1), imm(8)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, writeback, add, ret]);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));

        assert_eq!(func.inst(InstId(1)).operands[1], vreg(1));
        assert_eq!(func.inst(InstId(2)).operands[1], vreg(1));
    }

    #[test]
    fn test_copy_prop_does_not_rewrite_scalar_writeback_defuse_operand() {
        // Rewriting the DefUse base would retarget the architectural
        // writeback destination, so copy-prop leaves it alone.
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let writeback = MachInst::new(AArch64Opcode::StrPostIndex, vec![vreg(5), vreg(1), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, writeback, ret]);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));

        assert_eq!(func.inst(InstId(1)).operands[1], vreg(1));
    }

    #[test]
    fn test_no_prop_across_register_classes() {
        // A Gpr32 -> Gpr64 MovR is used by ISel to model zero-extension.
        // Propagating the Gpr32 source into a Gpr64 use changes the value.
        let mov = MachInst::new(
            AArch64Opcode::MovR,
            vec![
                vreg_class(1, RegClass::Gpr64),
                vreg_class(0, RegClass::Gpr32),
            ],
        );
        let store = MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg_class(1, RegClass::Gpr64), vreg(2), imm(0)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, store, ret]);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));

        let store_inst = func.inst(InstId(1));
        assert_eq!(store_inst.operands[0], vreg_class(1, RegClass::Gpr64));
    }

    #[test]
    fn test_no_prop_to_same_id_different_class_use() {
        // The copy itself is a transparent Gpr64 -> Gpr64 copy, but a later
        // same-id Gpr32 operand is a different virtual register identity.
        let mov = MachInst::new(
            AArch64Opcode::MovR,
            vec![
                vreg_class(1, RegClass::Gpr64),
                vreg_class(0, RegClass::Gpr64),
            ],
        );
        let store = MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg_class(1, RegClass::Gpr32), vreg(2), imm(0)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, store, ret]);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));

        let store_inst = func.inst(InstId(1));
        assert_eq!(store_inst.operands[0], vreg_class(1, RegClass::Gpr32));
    }

    #[test]
    fn test_same_id_different_class_def_does_not_block_copy() {
        // Def counts are keyed by full VReg identity. A same numeric id in a
        // different class must not make the Gpr64 copy look multiply defined.
        let unrelated_def = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                vreg_class(1, RegClass::Gpr32),
                vreg_class(3, RegClass::Gpr32),
                imm(1),
            ],
        );
        let mov = MachInst::new(
            AArch64Opcode::MovR,
            vec![
                vreg_class(1, RegClass::Gpr64),
                vreg_class(0, RegClass::Gpr64),
            ],
        );
        let add = MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg_class(1, RegClass::Gpr64), imm(5)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![unrelated_def, mov, add, ret]);

        let mut cp = CopyPropagation;
        assert!(cp.run(&mut func));

        let add_inst = func.inst(InstId(2));
        assert_eq!(add_inst.operands[1], vreg_class(0, RegClass::Gpr64));
    }

    #[test]
    fn test_same_id_different_class_source_redef_does_not_block_copy() {
        // Source stability is also class-exact: redefining v0:Gpr32 after a
        // v1:Gpr64 <- v0:Gpr64 copy cannot affect later uses of v1:Gpr64.
        let mov = MachInst::new(
            AArch64Opcode::MovR,
            vec![
                vreg_class(1, RegClass::Gpr64),
                vreg_class(0, RegClass::Gpr64),
            ],
        );
        let unrelated_redef = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                vreg_class(0, RegClass::Gpr32),
                vreg_class(3, RegClass::Gpr32),
                imm(1),
            ],
        );
        let add = MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg_class(1, RegClass::Gpr64), imm(5)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, unrelated_redef, add, ret]);

        let mut cp = CopyPropagation;
        assert!(cp.run(&mut func));

        let add_inst = func.inst(InstId(2));
        assert_eq!(add_inst.operands[1], vreg_class(0, RegClass::Gpr64));
    }

    #[test]
    fn test_no_prop_same_block_source_redefined_after_copy() {
        // v1 = mov v0
        // v0 = add v2, #1
        // v3 = add v1, #5
        //
        // The copy captured the old value of v0. Rewriting the v1 use to v0
        // would read the later same-block definition instead.
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let redef = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(2), imm(1)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(1), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, redef, add, ret]);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));
        let add_inst = func.inst(InstId(2));
        assert_eq!(add_inst.operands[1], vreg(1));
    }

    #[test]
    fn test_no_change_no_copies() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(1), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));
    }

    #[test]
    fn test_no_prop_to_non_dominated_use() {
        // entry -> left, right
        // left:  v1 = mov v0; br merge
        // right: br merge
        // merge: v2 = add v1, #1
        //
        // The copy in `left` does not dominate `merge`, so the add's use of
        // v1 must not be rewritten to v0. The previous implementation did a
        // blind function-wide replacement and was unsound on CFGs like this.
        let mut func =
            MachFunction::new("cp_dom_guard".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let left = func.create_block();
        let right = func.create_block();
        let merge = func.create_block();

        let br_entry = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(left), MachOperand::Block(right)],
        ));
        func.append_inst(entry, br_entry);

        let mov = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]));
        let br_left = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(merge)],
        ));
        func.append_inst(left, mov);
        func.append_inst(left, br_left);

        let br_right = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(merge)],
        ));
        func.append_inst(right, br_right);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg(1), imm(1)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(merge, add);
        func.append_inst(merge, ret);

        func.add_edge(entry, left);
        func.add_edge(entry, right);
        func.add_edge(left, merge);
        func.add_edge(right, merge);

        let mut cp = CopyPropagation;
        let mut analyses = crate::pass_manager::AnalysisCache::new();
        assert!(!cp.run_with_analyses(&mut func, &mut analyses));
        let add_inst = func.inst(add);
        assert_eq!(add_inst.operands[1], vreg(1));
    }

    #[test]
    fn test_no_prop_cross_block_source_redefined_after_copy() {
        // entry: v1 = mov v0; br left/right
        // left:  v0 = add v2, #1; br merge
        // right: br merge
        // merge: v3 = add v1, #5
        //
        // The copy dominates the merge use, but v0 is redefined on one path
        // between the copy and merge. The use of v1 must keep the captured
        // value instead of reading the path-dependent current value of v0.
        let mut func = MachFunction::new(
            "cp_src_redef_guard".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let left = func.create_block();
        let right = func.create_block();
        let merge = func.create_block();

        let mov = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]));
        let br_entry = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(left), MachOperand::Block(right)],
        ));
        func.append_inst(entry, mov);
        func.append_inst(entry, br_entry);

        let redef = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(2), imm(1)],
        ));
        let br_left = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(merge)],
        ));
        func.append_inst(left, redef);
        func.append_inst(left, br_left);

        let br_right = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(merge)],
        ));
        func.append_inst(right, br_right);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(3), vreg(1), imm(5)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(merge, add);
        func.append_inst(merge, ret);

        func.add_edge(entry, left);
        func.add_edge(entry, right);
        func.add_edge(left, merge);
        func.add_edge(right, merge);

        let mut cp = CopyPropagation;
        let mut analyses = crate::pass_manager::AnalysisCache::new();
        assert!(!cp.run_with_analyses(&mut func, &mut analyses));
        let add_inst = func.inst(add);
        assert_eq!(add_inst.operands[1], vreg(1));
    }

    /// `entry: <entry_insts>; b body`, then `body: <body_insts>` and `exit:
    /// ret`. With `loops`, `body` ends `b.cond body, exit` and has a self
    /// edge; without it, `body` ends `b exit` and nothing re-enters it.
    /// Returns the function and the ids of `body_insts`, in order.
    fn entry_body_exit(
        entry_insts: Vec<MachInst>,
        body_insts: Vec<MachInst>,
        loops: bool,
    ) -> (MachFunction, Vec<InstId>) {
        let mut func = MachFunction::new("cp_loop".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let body = func.create_block();
        let exit = func.create_block();

        for inst in entry_insts {
            let id = func.push_inst(inst);
            func.append_inst(entry, id);
        }
        let br_entry = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(body)],
        ));
        func.append_inst(entry, br_entry);

        let mut body_ids = Vec::new();
        for inst in body_insts {
            let id = func.push_inst(inst);
            func.append_inst(body, id);
            body_ids.push(id);
        }
        let br_body = if loops {
            MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Block(body), MachOperand::Block(exit)],
            )
        } else {
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit)])
        };
        let br_body = func.push_inst(br_body);
        func.append_inst(body, br_body);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(entry, body);
        if loops {
            func.add_edge(body, body);
        }
        func.add_edge(body, exit);
        (func, body_ids)
    }

    #[test]
    fn test_no_prop_when_source_redefined_after_use_in_self_loop() {
        // entry: v1 = mov v0; b body
        // body:  v2 = add v1, #1     use of the copy
        //        v0 = add v2, #1     source redefined after the use
        //        b.cond body, exit
        //
        // The copy runs once, before the loop. From the second iteration on,
        // v0 holds the value body's back edge carries while v1 still holds
        // v0's entry value, so the use of v1 must not be rewritten to v0.
        let (mut func, body) = entry_body_exit(
            vec![MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)])],
            vec![
                MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]),
                MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(2), imm(1)]),
            ],
            true,
        );

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));
        assert_eq!(func.inst(body[0]).operands[1], vreg(1));
    }

    #[test]
    fn test_no_prop_when_use_itself_redefines_source_in_self_loop() {
        // entry: v1 = mov v0; b body
        // body:  v0 = add v0, v1     reads v1, then writes v0
        //        b.cond body, exit
        //
        // The use reads its operands before it writes, so its own def of v0
        // reaches it only around the back edge, and it does. Rewriting v1 to
        // v0 would add the running v0 to itself instead of adding v0's entry
        // value on every iteration after the first.
        let (mut func, body) = entry_body_exit(
            vec![MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)])],
            vec![MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(0), vreg(0), vreg(1)],
            )],
            true,
        );

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));
        assert_eq!(func.inst(body[0]).operands[2], vreg(1));
    }

    #[test]
    fn test_no_prop_when_source_redefined_after_use_around_two_block_cycle() {
        // entry:  v1 = mov v0; b header
        // header: v2 = add v1, #1    use of the copy
        //         v0 = add v2, #1    source redefined after the use
        //         b latch
        // latch:  b.cond header, exit
        //
        // header reaches itself through latch, not through a self edge; the
        // redefinition still reaches the use without re-running the copy.
        let mut func = MachFunction::new(
            "cp_two_block_cycle".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        let mov = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]));
        let br_entry = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        func.append_inst(entry, mov);
        func.append_inst(entry, br_entry);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg(1), imm(1)],
        ));
        let redef = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(2), imm(1)],
        ));
        let br_header = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(latch)],
        ));
        func.append_inst(header, add);
        func.append_inst(header, redef);
        func.append_inst(header, br_header);

        let br_latch = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(header), MachOperand::Block(exit)],
        ));
        func.append_inst(latch, br_latch);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(entry, header);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));
        assert_eq!(func.inst(add).operands[1], vreg(1));
    }

    #[test]
    fn test_prop_when_source_redefined_after_use_in_block_without_cycle() {
        // entry: v1 = mov v0; b body
        // body:  v2 = add v1, #1  → v2 = add v0, #1
        //        v0 = add v2, #1
        //        b exit
        //
        // Nothing re-enters body, so the later redefinition of v0 cannot
        // reach the use and the rewrite stays legal.
        let (mut func, body) = entry_body_exit(
            vec![MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)])],
            vec![
                MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]),
                MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(2), imm(1)]),
            ],
            false,
        );

        let mut cp = CopyPropagation;
        assert!(cp.run(&mut func));
        assert_eq!(func.inst(body[0]).operands[1], vreg(0));
    }

    #[test]
    fn test_prop_when_copy_reruns_before_use_in_self_loop() {
        // entry: b body
        // body:  v1 = mov v0
        //        v2 = add v1, #1  → v2 = add v0, #1
        //        v0 = add v2, #1
        //        b.cond body, exit
        //
        // The redefinition reaches the use around the back edge, but every
        // such path re-enters body at its top and re-runs the copy first, so
        // v1 equals v0 at the use on every iteration.
        let (mut func, body) = entry_body_exit(
            vec![],
            vec![
                MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]),
                MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]),
                MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(2), imm(1)]),
            ],
            true,
        );

        let mut cp = CopyPropagation;
        assert!(cp.run(&mut func));
        assert_eq!(func.inst(body[1]).operands[1], vreg(0));
    }

    /// The importer's counted-loop shape, with the copy in the edge block that
    /// is `body`'s only predecessor:
    ///
    /// ```text
    /// entry:  v4 = movz #0; v5 = mov v4; b header
    /// header: cmp v5, v2; b.cond edge, exit
    /// edge:   v6 = mov v5; b body
    /// body:   v9 = add v6, #8      uses of the copy
    ///         v12 = add v6, #1
    ///         v5 = mov v12         source redefined after the uses
    ///         b header             (with `bypass`: b latch)
    /// latch:  b.cond body, header  (only with `bypass`)
    /// exit:   ret
    /// ```
    ///
    /// Returns the function and the ids of the two uses.
    fn edge_copy_loop(bypass: bool) -> (MachFunction, [InstId; 2]) {
        let mut func =
            MachFunction::new("cp_edge_copy".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let header = func.create_block();
        let edge = func.create_block();
        let body = func.create_block();
        let latch = bypass.then(|| func.create_block());
        let exit = func.create_block();
        let put = |func: &mut MachFunction, block: BlockId, inst: MachInst| {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
            id
        };

        put(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Movz, vec![vreg(4), imm(0)]),
        );
        put(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(5), vreg(4)]),
        );
        put(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );

        put(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(5), vreg(2)]),
        );
        put(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Block(edge), MachOperand::Block(exit)],
            ),
        );

        put(
            &mut func,
            edge,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(6), vreg(5)]),
        );
        put(
            &mut func,
            edge,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(body)]),
        );

        let use1 = put(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(9), vreg(6), imm(8)]),
        );
        let use2 = put(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(12), vreg(6), imm(1)]),
        );
        put(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(5), vreg(12)]),
        );
        let body_target = latch.unwrap_or(header);
        put(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(body_target)]),
        );

        if let Some(latch) = latch {
            put(
                &mut func,
                latch,
                MachInst::new(
                    AArch64Opcode::BCond,
                    vec![MachOperand::Block(body), MachOperand::Block(header)],
                ),
            );
        }

        put(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, header);
        func.add_edge(header, edge);
        func.add_edge(header, exit);
        func.add_edge(edge, body);
        func.add_edge(body, body_target);
        if let Some(latch) = latch {
            func.add_edge(latch, body);
            func.add_edge(latch, header);
        }
        (func, [use1, use2])
    }

    #[test]
    fn test_prop_when_every_cycle_back_to_use_runs_copy_in_edge_block() {
        // The redefinition `v5 = mov v12` follows both uses in body and
        // reaches them only around body -> header -> edge -> body, which runs
        // `v6 = mov v5` again. v6 equals v5 at both uses on every iteration,
        // so both are rewritten to v5.
        let (mut func, uses) = edge_copy_loop(false);

        let mut cp = CopyPropagation;
        assert!(cp.run(&mut func));
        for use_id in uses {
            assert_eq!(func.inst(use_id).operands[1], vreg(5));
        }
    }

    #[test]
    fn test_no_prop_when_a_cycle_back_to_use_bypasses_copy_block() {
        // The same loop with a latch that also branches straight back to
        // body. Around body -> latch -> body the copy does not run, so from
        // the second trip of that cycle on, v5 holds the redefined value
        // while v6 still holds the one edge copied. Neither use is rewritten.
        let (mut func, uses) = edge_copy_loop(true);

        let mut cp = CopyPropagation;
        assert!(!cp.run(&mut func));
        for use_id in uses {
            assert_eq!(func.inst(use_id).operands[1], vreg(6));
        }
    }
}
