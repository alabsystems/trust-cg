// trust-cg-opt - Rotate-idiom peephole pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Rotate-idiom recognition (former peephole pattern 53).
//!
//! `(x << k) | (x >> (W - k))` -> `ror x, #(W - k)`.
//!
//! Retained as a standalone pass after the hand-written peephole migration
//! because it depends on cross-instruction dominator information the
//! declarative rewrite engine does not thread: a shift amount may be a
//! materialized constant defined in a *dominating* block, not just the same
//! block.
//!
//! # Sub-width (u32-carried-in-Gpr64) constant-rotate arm
//!
//! The width-`W` arm above only fires when `lsl + lsr == REGISTER width`. A
//! `u32::rotate_left/right` whose value travels the 64-bit masked-I64 bitmanip
//! carrier is open-coded by isel as
//!
//! ```text
//!   xc  = AndRI(zext, 0xffffffff)     ; zext = Uxtw(w32)  (32-bit-clean)
//!   t1  = LslRI(xc, l)                ; l + r == 32, l, r in [1, 31]
//!   t2  = LsrRI(xc, r)
//!   or  = OrrRR(t1, t2)
//!   m   = AndRI(or, 0xffffffff)
//!   d32 = MovR(m)                     ; the Gpr64 -> Gpr32 retype (ANCHOR)
//! ```
//!
//! (`1 + 31 == 32 != 64`, so the width-64 arm correctly stays silent). This arm
//! anchors at the retype `MovR(d32: Gpr32, m: Gpr64)` and rewrites THAT
//! instruction in place to `RorRI(d32, w32, #r)`, leaving the (now-dead when
//! `m` was single-use, which is required) shift group for DCE. Anchoring at the
//! retype is load-bearing for performance: the rewrite puts ZERO copies on a
//! loop-carried ARX chain.
//!
//! Soundness (QF_BV, same identity class as the width-64 arm): for
//! `x = zext64(w)` with `w: u32` and `l + r == 32`, `l, r in [1, 31]`:
//! `x >> r  = zext(w >>u r)` (no bits above 31 survive in `x`, so nothing
//! foreign shifts into the low lanes), `(x << l) & 0xffffffff = zext(w << l)`,
//! hence `((x << l) | (x >> r)) & 0xffffffff = zext(rotl32(w, l))
//! = zext(ror32(w, r))`, and the truncating retype yields exactly
//! `ror32(w, r)` — the Gpr32 `RorRI`. The 32-bit-cleanliness of `xc` is the
//! linchpin: without the proven `zext` root, `x >> r` pulls garbage bits
//! `32..62` into masked result bits `(32-r)..31`, so this arm REQUIRES the
//! `Uxtw` root (directly, or through one `AndRI(_, 0xffffffff)`) and bails on
//! anything else (fail-closed).

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    VReg,
    regs::{RegClass, preg_class},
};

use crate::dom::DomTree;
use crate::effects::{
    aarch64_for_each_use_position, for_each_inst_def, inst_defines_vreg, single_inst_def,
};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Rotate-idiom recognition pass (former peephole pattern 53).
pub struct RotateIdiom;

impl MachinePass for RotateIdiom {
    fn name(&self) -> &str {
        "rotate-idiom"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_rotate_idiom(func, None, None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let dom = analyses.domtree(func);
        run_rotate_idiom(func, Some(dom), None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_rotate_idiom(func, None, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = analyses.domtree(func);
        run_rotate_idiom(func, Some(dom), Some(provenance))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ConstantDef {
    block: BlockId,
    value: i64,
}

type UniqueConstantDefs = HashMap<VReg, Option<ConstantDef>>;

fn rotate_idiom_pass_id() -> PassId {
    PassId::new("rotate-idiom")
}

fn run_rotate_idiom(
    func: &mut MachFunction,
    dom: Option<&DomTree>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut changed = false;
    let dominating_constants = dom.map(|_| collect_unique_materialized_constants(func));

    for block_id in func.block_order.clone() {
        let mut def_map: HashMap<VReg, InstId> = HashMap::new();
        let block = func.block(block_id);
        for &inst_id in block.insts.clone().iter() {
            let result = match func.inst(inst_id).opcode {
                AArch64Opcode::OrrRR => peephole_rotate_or(
                    func.inst(inst_id),
                    func,
                    &def_map,
                    block_id,
                    dom,
                    dominating_constants.as_ref(),
                ),
                AArch64Opcode::MovR => {
                    peephole_subwidth_rotate_retype(func.inst(inst_id), func, &def_map)
                }
                _ => None,
            };

            match result {
                None => {
                    record_value_def(&mut def_map, inst_id, func.inst(inst_id));
                }
                Some(mut new_inst) => {
                    let orig_inst = func.inst(inst_id);
                    let orig_proof = orig_inst.proof;
                    let orig_source_loc = orig_inst.source_loc;
                    new_inst.proof = orig_proof;
                    if new_inst.source_loc.is_none() {
                        new_inst.source_loc = orig_source_loc;
                    }
                    *func.inst_mut(inst_id) = new_inst;
                    if let Some(provenance) = provenance.as_deref_mut() {
                        provenance.record_in_place_transform(inst_id, rotate_idiom_pass_id());
                    }
                    changed = true;
                    record_value_def(&mut def_map, inst_id, func.inst(inst_id));
                }
            }
        }
    }

    changed
}

fn collect_unique_materialized_constants(func: &MachFunction) -> UniqueConstantDefs {
    let mut constants: UniqueConstantDefs = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            let sole_def = single_inst_def(inst);
            for_each_inst_def(inst, |dst| match constants.entry(dst) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(
                        (sole_def == Some(dst))
                            .then(|| simple_materialized_constant(inst))
                            .flatten()
                            .map(|value| ConstantDef {
                                block: block_id,
                                value,
                            }),
                    );
                }
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    entry.insert(None);
                }
            });
        }
    }
    constants
}

fn simple_materialized_constant(inst: &MachInst) -> Option<i64> {
    match inst.opcode {
        AArch64Opcode::MovI if inst.operands.len() == 2 => inst.operands.get(1)?.as_imm(),
        AArch64Opcode::Movz => {
            crate::reaching_const::movz_value(inst).map(|(_, value)| value as i64)
        }
        _ => None,
    }
}

fn record_value_def(def_map: &mut HashMap<VReg, InstId>, inst_id: InstId, inst: &MachInst) {
    for_each_inst_def(inst, |dst| {
        def_map.insert(dst, inst_id);
    });
}

fn lookup_def<'a>(
    vreg: VReg,
    func: &'a MachFunction,
    def_map: &HashMap<VReg, InstId>,
) -> Option<&'a MachInst> {
    def_map.get(&vreg).map(|&id| func.inst(id))
}

fn peephole_rotate_or(
    inst: &MachInst,
    func: &MachFunction,
    def_map: &HashMap<VReg, InstId>,
    current_block: BlockId,
    dom: Option<&DomTree>,
    dominating_constants: Option<&UniqueConstantDefs>,
) -> Option<MachInst> {
    if inst.operands.len() < 3 {
        return None;
    }
    let lhs_def = lookup_def_operand(&inst.operands[1], func, def_map);
    let rhs_def = lookup_def_operand(&inst.operands[2], func, def_map);
    if let (Some(lhs), Some(rhs)) = (lhs_def, rhs_def) {
        return try_rotate_shift_pair(
            inst,
            lhs,
            rhs,
            func,
            def_map,
            current_block,
            dom,
            dominating_constants,
        )
        .or_else(|| {
            try_rotate_shift_pair(
                inst,
                rhs,
                lhs,
                func,
                def_map,
                current_block,
                dom,
                dominating_constants,
            )
        });
    }
    None
}

fn lookup_def_operand<'a>(
    operand: &MachOperand,
    func: &'a MachFunction,
    def_map: &HashMap<VReg, InstId>,
) -> Option<&'a MachInst> {
    operand
        .as_vreg()
        .and_then(|vreg| lookup_def(vreg, func, def_map))
}

#[allow(clippy::too_many_arguments)]
fn try_rotate_shift_pair(
    outer: &MachInst,
    lsl: &MachInst,
    lsr: &MachInst,
    func: &MachFunction,
    def_map: &HashMap<VReg, InstId>,
    current_block: BlockId,
    dom: Option<&DomTree>,
    dominating_constants: Option<&UniqueConstantDefs>,
) -> Option<MachInst> {
    if !matches!(lsl.opcode, AArch64Opcode::LslRI | AArch64Opcode::LslRR)
        || !matches!(lsr.opcode, AArch64Opcode::LsrRI | AArch64Opcode::LsrRR)
    {
        return None;
    }
    if lsl.operands.len() < 3 || lsr.operands.len() < 3 {
        return None;
    }
    let src = &lsl.operands[1];
    if !same_register_operand(src, &lsr.operands[1]) {
        return None;
    }
    let width = register_width(src).or_else(|| register_width(&outer.operands[0]))?;
    let lsl_shift =
        constant_shift_amount(lsl, func, def_map, current_block, dom, dominating_constants)?;
    let lsr_shift =
        constant_shift_amount(lsr, func, def_map, current_block, dom, dominating_constants)?;
    if !(1..width).contains(&lsl_shift) || !(1..width).contains(&lsr_shift) {
        return None;
    }
    if lsl_shift + lsr_shift != width {
        return None;
    }
    Some(MachInst::new(
        AArch64Opcode::RorRI,
        vec![
            outer.operands[0].clone(),
            src.clone(),
            MachOperand::Imm(lsr_shift),
        ],
    ))
}

/// Sub-width (u32-in-Gpr64) constant-rotate arm — see the module docs.
///
/// Anchored at the Gpr64 -> Gpr32 retype `MovR(d32, m)`. Fires ONLY when ALL of
/// the following hold (each guards a soundness step; anything unproven bails):
///
/// * `m: Gpr64` is defined in THIS block (in-block `def_map` discipline) by
///   `AndRI(or_v, 0xffffffff)`;
/// * `or_v := OrrRR(a, b)` with `{a, b} = {LslRI(xc, l), LsrRI(xc, r)}` (either
///   operand order), both shifts of the SAME `xc`, both amounts IMMEDIATE, and
///   `l + r == 32` with `l, r in [1, 31]`;
/// * `xc` is provably 32-bit-clean: its def is `Uxtw(w32)` or
///   `AndRI(y, 0xffffffff)` with `y := Uxtw(w32)` (walk of at most 2), and
///   `w32` is `Gpr32`;
/// * every chain vreg (`m`, `or_v`, `a`, `b`, `xc`, `y`, and the rotate source
///   `w32`) has exactly ONE def in the whole function, so the values read here
///   are position-independent (the in-block `def_map` lookups cannot be
///   shadowed by another def between the chain and the anchor);
/// * `m` is SINGLE-USE (this `MovR`), so the rewrite leaves the whole shift
///   group dead for DCE rather than a half-live mixed state.
///
/// The anchor is rewritten in place to `RorRI(d32, w32, #r)`.
fn peephole_subwidth_rotate_retype(
    inst: &MachInst,
    func: &MachFunction,
    def_map: &HashMap<VReg, InstId>,
) -> Option<MachInst> {
    const MASK32: i64 = 0xffff_ffff;
    // Anchor: `MovR(d32: Gpr32, m: Gpr64)` — the truncating retype.
    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands[0].as_vreg()?;
    let m = inst.operands[1].as_vreg()?;
    if dst.class != RegClass::Gpr32 || m.class != RegClass::Gpr64 {
        return None;
    }
    // `m` single-use (this anchor) across all block-linked instructions.
    if count_linked_uses(func, m) != 1 {
        return None;
    }
    // m := AndRI(or_v, 0xffffffff)
    let m_def = lookup_def(m, func, def_map)?;
    let or_v = match_and_mask32(m_def, MASK32)?;
    // or_v := OrrRR(a, b)
    let or_def = lookup_def(or_v, func, def_map)?;
    if or_def.opcode != AArch64Opcode::OrrRR || or_def.operands.len() < 3 {
        return None;
    }
    let a = or_def.operands[1].as_vreg()?;
    let b = or_def.operands[2].as_vreg()?;
    let a_def = lookup_def(a, func, def_map)?;
    let b_def = lookup_def(b, func, def_map)?;
    // {a, b} = {LslRI(xc, l), LsrRI(xc, r)} in either order; IMMEDIATE amounts.
    let (lsl, lsr) = match (a_def.opcode, b_def.opcode) {
        (AArch64Opcode::LslRI, AArch64Opcode::LsrRI) => (a_def, b_def),
        (AArch64Opcode::LsrRI, AArch64Opcode::LslRI) => (b_def, a_def),
        _ => return None,
    };
    if lsl.operands.len() < 3 || lsr.operands.len() < 3 {
        return None;
    }
    let xc = lsl.operands[1].as_vreg()?;
    if lsr.operands[1].as_vreg()? != xc {
        return None;
    }
    let l = lsl.operands[2].as_imm()?;
    let r = lsr.operands[2].as_imm()?;
    if !(1..=31).contains(&l) || !(1..=31).contains(&r) || l + r != 32 {
        return None;
    }
    // `xc` 32-bit-clean, walk <= 2: Uxtw(w32) | AndRI(Uxtw(w32), 0xffffffff).
    let xc_def = lookup_def(xc, func, def_map)?;
    let (w32, chain_y) = match xc_def.opcode {
        AArch64Opcode::Uxtw if xc_def.operands.len() == 2 => (xc_def.operands[1].as_vreg()?, None),
        AArch64Opcode::AndRI => {
            let y = match_and_mask32(xc_def, MASK32)?;
            let y_def = lookup_def(y, func, def_map)?;
            if y_def.opcode != AArch64Opcode::Uxtw || y_def.operands.len() != 2 {
                return None;
            }
            (y_def.operands[1].as_vreg()?, Some(y))
        }
        _ => return None,
    };
    if w32.class != RegClass::Gpr32 {
        return None;
    }
    // Every chain vreg (and the surviving rotate source `w32`) must have exactly
    // one def in the whole function: the values the in-block lookups resolved
    // are then the only values those registers can ever hold, so no def between
    // a chain instruction and the anchor can shadow what we matched, and `w32`
    // still holds the Uxtw-rooted value at the anchor.
    for v in [m, or_v, a, b, xc, w32].into_iter().chain(chain_y) {
        if count_linked_defs(func, v) != 1 {
            return None;
        }
    }
    Some(MachInst::new(
        AArch64Opcode::RorRI,
        vec![
            inst.operands[0].clone(),
            MachOperand::VReg(w32),
            MachOperand::Imm(r),
        ],
    ))
}

/// `AndRI(dst, src, #mask)` with the exact required mask -> `src`.
fn match_and_mask32(inst: &MachInst, mask: i64) -> Option<VReg> {
    if inst.opcode != AArch64Opcode::AndRI || inst.operands.len() < 3 {
        return None;
    }
    if inst.operands[2].as_imm()? != mask {
        return None;
    }
    inst.operands[1].as_vreg()
}

/// Number of reads of `v` across all block-linked instructions.
fn count_linked_uses(func: &MachFunction, v: VReg) -> usize {
    let mut uses = 0;
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                if inst.operands.get(pos).and_then(MachOperand::as_vreg) == Some(v) {
                    uses += 1;
                }
            });
        }
    }
    uses
}

/// Number of DEFS of `v` across all block-linked instructions.
fn count_linked_defs(func: &MachFunction, v: VReg) -> usize {
    let mut defs = 0;
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            if inst_defines_vreg(func.inst(inst_id), v) {
                defs += 1;
            }
        }
    }
    defs
}

fn constant_shift_amount(
    shift_inst: &MachInst,
    func: &MachFunction,
    def_map: &HashMap<VReg, InstId>,
    current_block: BlockId,
    dom: Option<&DomTree>,
    dominating_constants: Option<&UniqueConstantDefs>,
) -> Option<i64> {
    if let Some(imm) = shift_inst.operands[2].as_imm() {
        return Some(imm);
    }
    let amount_vreg = shift_inst.operands[2].as_vreg()?;
    if let Some(def) = lookup_def(amount_vreg, func, def_map) {
        return simple_materialized_constant(def);
    }
    let dom = dom?;
    let constant_def = dominating_constants?
        .get(&amount_vreg)
        .and_then(|entry| *entry)?;
    if constant_def.block == current_block || !dom.dominates(constant_def.block, current_block) {
        return None;
    }
    Some(constant_def.value)
}

fn same_register_operand(a: &MachOperand, b: &MachOperand) -> bool {
    match (a, b) {
        (MachOperand::VReg(a), MachOperand::VReg(b)) => a == b,
        (MachOperand::PReg(a), MachOperand::PReg(b)) => a == b,
        (MachOperand::Special(a), MachOperand::Special(b)) => a == b,
        _ => false,
    }
}

fn register_width(operand: &MachOperand) -> Option<i64> {
    let class = match operand {
        MachOperand::VReg(vreg) => vreg.class,
        MachOperand::PReg(preg) => preg_class(*preg),
        MachOperand::Special(special) => {
            return Some(match special {
                trust_cg_ir::regs::SpecialReg::WZR => 32,
                trust_cg_ir::regs::SpecialReg::SP | trust_cg_ir::regs::SpecialReg::XZR => 64,
            });
        }
        _ => return None,
    };
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{RegClass, Signature, VReg};

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn single_block_func(insts: Vec<MachInst>) -> (MachFunction, BlockId) {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        for i in insts {
            let id = func.push_inst(i);
            func.append_inst(entry, id);
        }
        (func, entry)
    }

    #[test]
    fn rotate_64_recognized() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(1), vreg(0), MachOperand::Imm(20)],
            ),
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(2), vreg(0), MachOperand::Imm(44)],
            ),
            MachInst::new(AArch64Opcode::OrrRR, vec![vreg(3), vreg(1), vreg(2)]),
        ]);
        let mut pass = RotateIdiom;
        assert!(pass.run(&mut func));
        let after = func.inst(func.block(entry).insts[2]);
        assert_eq!(after.opcode, AArch64Opcode::RorRI);
        assert_eq!(after.operands[1], vreg(0));
        assert_eq!(after.operands[2], MachOperand::Imm(44));
    }

    #[test]
    fn rotate_commuted_operands_recognized() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(1), vreg(0), MachOperand::Imm(7)],
            ),
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(2), vreg(0), MachOperand::Imm(57)],
            ),
            MachInst::new(AArch64Opcode::OrrRR, vec![vreg(3), vreg(2), vreg(1)]),
        ]);
        let mut pass = RotateIdiom;
        assert!(pass.run(&mut func));
        let after = func.inst(func.block(entry).insts[2]);
        assert_eq!(after.opcode, AArch64Opcode::RorRI);
        assert_eq!(after.operands[2], MachOperand::Imm(57));
    }

    #[test]
    fn non_rotate_shift_sum_not_width_left_alone() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(1), vreg(0), MachOperand::Imm(20)],
            ),
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(2), vreg(0), MachOperand::Imm(30)],
            ),
            MachInst::new(AArch64Opcode::OrrRR, vec![vreg(3), vreg(1), vreg(2)]),
        ]);
        let mut pass = RotateIdiom;
        assert!(!pass.run(&mut func));
        assert_eq!(
            func.inst(func.block(entry).insts[2]).opcode,
            AArch64Opcode::OrrRR
        );
    }

    fn wreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    /// The d02 sub-width chain: `w48 -> Uxtw v49 -> AndRI v51 -> (Lsl #l | Lsr
    /// #r) -> OrrRR v56 -> AndRI v58 -> MovR d59:Gpr32` with `l + r == 32`.
    fn subwidth_chain(l: i64, r: i64, outer_mask: i64) -> Vec<MachInst> {
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![wreg(48), MachOperand::Imm(7)]),
            MachInst::new(AArch64Opcode::Uxtw, vec![vreg(49), wreg(48)]),
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![vreg(51), vreg(49), MachOperand::Imm(0xffff_ffff)],
            ),
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(54), vreg(51), MachOperand::Imm(l)],
            ),
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(55), vreg(51), MachOperand::Imm(r)],
            ),
            MachInst::new(AArch64Opcode::OrrRR, vec![vreg(56), vreg(54), vreg(55)]),
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![vreg(58), vreg(56), MachOperand::Imm(outer_mask)],
            ),
            MachInst::new(AArch64Opcode::MovR, vec![wreg(59), vreg(58)]),
        ]
    }

    #[test]
    fn subwidth_u32_rotate_retype_recognized() {
        let (mut func, entry) = single_block_func(subwidth_chain(1, 31, 0xffff_ffff));
        let mut pass = RotateIdiom;
        assert!(pass.run(&mut func));
        let after = func.inst(func.block(entry).insts[7]);
        assert_eq!(after.opcode, AArch64Opcode::RorRI);
        assert_eq!(after.operands[0], wreg(59));
        assert_eq!(after.operands[1], wreg(48));
        assert_eq!(after.operands[2], MachOperand::Imm(31));
    }

    #[test]
    fn subwidth_u32_rotate_other_amount_recognized() {
        // rotate_right(7): l = 25, r = 7.
        let (mut func, entry) = single_block_func(subwidth_chain(25, 7, 0xffff_ffff));
        let mut pass = RotateIdiom;
        assert!(pass.run(&mut func));
        let after = func.inst(func.block(entry).insts[7]);
        assert_eq!(after.opcode, AArch64Opcode::RorRI);
        assert_eq!(after.operands[2], MachOperand::Imm(7));
    }

    #[test]
    fn subwidth_without_uxtw_root_not_rewritten() {
        // xc := Movz (64-bit constant, NOT provably 32-bit-clean via Uxtw):
        // bits 32..62 of a general value would leak into the masked result.
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(51), MachOperand::Imm(7)]),
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(54), vreg(51), MachOperand::Imm(1)],
            ),
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(55), vreg(51), MachOperand::Imm(31)],
            ),
            MachInst::new(AArch64Opcode::OrrRR, vec![vreg(56), vreg(54), vreg(55)]),
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![vreg(58), vreg(56), MachOperand::Imm(0xffff_ffff)],
            ),
            MachInst::new(AArch64Opcode::MovR, vec![wreg(59), vreg(58)]),
        ]);
        let mut pass = RotateIdiom;
        assert!(!pass.run(&mut func));
        assert_eq!(
            func.inst(func.block(entry).insts[5]).opcode,
            AArch64Opcode::MovR
        );
    }

    #[test]
    fn subwidth_wrong_outer_mask_not_rewritten() {
        let (mut func, _) = single_block_func(subwidth_chain(1, 31, 0x7fff_ffff));
        let mut pass = RotateIdiom;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn subwidth_shift_sum_not_32_not_rewritten() {
        let (mut func, _) = single_block_func(subwidth_chain(2, 31, 0xffff_ffff));
        let mut pass = RotateIdiom;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn subwidth_root_redefined_before_anchor_not_rewritten() {
        // Redefine the Gpr32 root `w48` between the `Uxtw` and the retype
        // anchor. The rewrite reads the root directly (`RorRI(d, w48)`), so it
        // would observe the NEW value rather than the one the chain masked —
        // MUST bail.
        let mut insts = subwidth_chain(1, 31, 0xffff_ffff);
        insts.insert(
            7,
            MachInst::new(AArch64Opcode::Movz, vec![wreg(48), MachOperand::Imm(9)]),
        );
        let (mut func, _) = single_block_func(insts);
        let mut pass = RotateIdiom;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn subwidth_multi_use_mask_not_rewritten() {
        // A second consumer of the masked value `v58` keeps the group live.
        let mut insts = subwidth_chain(1, 31, 0xffff_ffff);
        insts.push(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(60), vreg(58), MachOperand::Imm(1)],
        ));
        let (mut func, _) = single_block_func(insts);
        let mut pass = RotateIdiom;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn subwidth_pair_in_genuine_64bit_context_not_rewritten() {
        // The same `l + r == 32` shift pair WITHOUT the Gpr32 retype anchor:
        // a genuine 64-bit consumer keeps the 64-bit value; neither arm fires
        // (the width-64 arm needs l + r == 64, the sub-width arm needs the
        // truncating MovR anchor).
        let mut insts = subwidth_chain(1, 31, 0xffff_ffff);
        insts.pop(); // drop the retype
        insts.push(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(60), vreg(58), MachOperand::Imm(1)],
        ));
        let (mut func, _) = single_block_func(insts);
        let mut pass = RotateIdiom;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn different_source_registers_not_a_rotate() {
        let (mut func, _entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(1), vreg(0), MachOperand::Imm(20)],
            ),
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(2), vreg(9), MachOperand::Imm(44)],
            ),
            MachInst::new(AArch64Opcode::OrrRR, vec![vreg(3), vreg(1), vreg(2)]),
        ]);
        let mut pass = RotateIdiom;
        assert!(!pass.run(&mut func));
    }
}
