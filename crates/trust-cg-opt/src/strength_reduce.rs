// trust-cg-opt - Strength reduction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Strength reduction pass for loop induction variables.
//!
//! Replaces expensive operations (multiply) in loop bodies with cheaper
//! operations (add) by recognizing induction variable patterns.
//!
//! # Key Transformation
//!
//! Replace:
//! ```text
//!   v_addr = MulRR v_iv, v_stride    ; address computation each iteration
//! ```
//! With:
//! ```text
//!   ; In preheader:
//!   v_addr_init = MulRR v_iv_init, v_stride
//!   ; In loop header:
//!   v_addr_cur = Phi [v_addr_init, preheader], [v_addr_next, latch]
//!   ; In loop body (replacing the MulRR):
//!   v_addr = Copy v_addr_cur
//!   ; On the latch edge:
//!   v_addr_next = AddRR v_addr_cur, v_stride
//! ```
//!
//! This is one of the most impactful classical loop optimizations. A multiply
//! per iteration becomes an add per iteration, saving cycles especially on
//! architectures where multiply has higher latency than add.
//!
//! # Algorithm
//!
//! 1. Compute dominator tree and loop analysis.
//! 2. For each loop, identify induction variables (linear IVs: `iv = iv + step`).
//! 3. Scan loop body for multiply instructions where one operand is the IV
//!    and the other is loop-invariant.
//! 4. Replace `MulRR iv, invariant` with the current derived value and
//!    advance the derived IV on the latch edge.
//!
//! # Safety
//!
//! This transformation preserves semantics because:
//! - `iv * stride` where `iv = iv_prev + step` is equivalent to
//!   `(iv_prev + step) * stride = iv_prev * stride + step * stride`
//! - So `result_new = result_prev + step * stride` (a constant increment).
//!
//! Reference: LLVM `LoopStrengthReduce.cpp`, Muchnick ch. 14.1

use std::collections::HashSet;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    VReg,
};

use crate::dom::DomTree;
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Strength reduction pass.
pub struct StrengthReduction;

impl MachinePass for StrengthReduction {
    fn name(&self) -> &str {
        "strength-reduce"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &loop_analysis, None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &loop_analysis, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis, Some(provenance))
    }
}

impl StrengthReduction {
    fn run_with_loop_analysis(
        func: &mut MachFunction,
        loop_analysis: &LoopAnalysis,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        if loop_analysis.is_empty() {
            return false;
        }

        let mut changed = false;

        // Process loops innermost-first.
        let mut loops: Vec<NaturalLoop> = loop_analysis.all_loops().cloned().collect();
        loops.sort_by_key(|lp| std::cmp::Reverse(lp.depth));

        for lp in &loops {
            if reduce_strength_in_loop(func, lp, provenance.as_deref_mut()) {
                changed = true;
            }
        }

        changed
    }
}

/// Information about an induction variable.
#[derive(Debug, Clone)]
struct InductionVar {
    /// The vreg of the IV (as defined by the Phi or the increment).
    vreg: VReg,
    /// The constant step added each iteration.
    step: i64,
}

/// Attempt strength reduction on multiply instructions in a loop.
fn reduce_strength_in_loop(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let preheader = match lp.preheader {
        Some(ph) => ph,
        None => return false,
    };

    // Step 1: Find induction variables.
    let ivs = find_induction_variables(func, lp);
    if ivs.is_empty() {
        return false;
    }

    // Step 2: Build a set of vregs defined outside the loop (loop-invariant vregs).
    let loop_defs = collect_loop_defined_vregs(func, lp);

    // Step 3: Scan for MulRR instructions where one operand is an IV
    //         and the other is loop-invariant.
    let mut reductions: Vec<MulReduction> = Vec::new();

    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        if block_id != lp.latch {
            continue;
        }
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::MulRR {
                continue;
            }
            // MulRR operands: [dst, src1, src2]
            if inst.operands.len() < 3 {
                continue;
            }
            let dst = match inst.operands[0].as_vreg() {
                Some(v) => v,
                None => continue,
            };
            let src1 = match inst.operands[1].as_vreg() {
                Some(v) => v,
                None => continue,
            };
            let src2 = match inst.operands[2].as_vreg() {
                Some(v) => v,
                None => continue,
            };

            // Check if one operand is an IV and the other is loop-invariant.
            for iv in &ivs {
                let (_iv_op, invariant_op) = if src1 == iv.vreg && !loop_defs.contains(&src2) {
                    (src1, src2)
                } else if src2 == iv.vreg && !loop_defs.contains(&src1) {
                    (src2, src1)
                } else {
                    continue;
                };

                reductions.push(MulReduction {
                    block_id,
                    inst_id,
                    dst,
                    iv: iv.clone(),
                    invariant_vreg: invariant_op,
                });
                break; // only one reduction per MulRR
            }
        }
    }

    if reductions.is_empty() {
        return false;
    }

    // Step 4: Apply each reduction.
    for reduction in &reductions {
        apply_reduction(func, lp, preheader, reduction, provenance.as_deref_mut());
    }

    true
}

/// A multiply instruction that can be strength-reduced.
#[derive(Debug)]
struct MulReduction {
    /// The block containing the original MulRR.
    block_id: BlockId,
    /// The original MulRR instruction ID.
    inst_id: InstId,
    /// Destination vreg of the original MulRR.
    dst: VReg,
    /// The induction variable operand.
    iv: InductionVar,
    /// The loop-invariant operand.
    invariant_vreg: VReg,
}

/// Find all induction variables in a loop.
///
/// An induction variable is defined by a Phi in the header where:
/// - One incoming value is from outside the loop (init value).
/// - The other incoming value is defined by `AddRI` or `SubRI` of the
///   Phi's own value and a constant step.
fn find_induction_variables(func: &MachFunction, lp: &NaturalLoop) -> Vec<InductionVar> {
    let mut ivs = Vec::new();
    let header_block = func.block(lp.header);

    for &inst_id in &header_block.insts {
        let inst = func.inst(inst_id);
        if inst.opcode != AArch64Opcode::Phi {
            continue;
        }

        // Phi operands: [def, val0, block0, val1, block1, ...]
        let def = match inst.operands.first().and_then(|op| op.as_vreg()) {
            Some(v) => v,
            None => continue,
        };

        // Find the incoming value from inside the loop (the latch or body).
        let mut loop_val: Option<VReg> = None;
        let mut i = 1;
        while i + 1 < inst.operands.len() {
            if let MachOperand::Block(bid) = &inst.operands[i + 1]
                && lp.body.contains(bid)
                && let Some(v) = inst.operands[i].as_vreg()
            {
                loop_val = Some(v);
            }
            i += 2;
        }

        let loop_val = match loop_val {
            Some(v) => v,
            None => continue,
        };

        // Check if loop_val is defined by AddRI or SubRI of the Phi's def.
        if let Some(step) = find_iv_step(func, lp, def, loop_val) {
            ivs.push(InductionVar { vreg: def, step });
        }
    }

    ivs
}

/// Check if `result_vreg` is defined by `AddRI phi_vreg, #step`
/// or `SubRI phi_vreg, #step` within the loop.
fn find_iv_step(
    func: &MachFunction,
    lp: &NaturalLoop,
    phi_vreg: VReg,
    result_vreg: VReg,
) -> Option<i64> {
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            match inst.opcode {
                AArch64Opcode::AddRI => {
                    // AddRI [dst, src, imm]
                    if inst.operands.len() >= 3
                        && let (Some(dst), Some(src), Some(step)) = (
                            inst.operands[0].as_vreg(),
                            inst.operands[1].as_vreg(),
                            inst.operands[2].as_imm(),
                        )
                        && dst == result_vreg
                        && src == phi_vreg
                    {
                        return Some(step);
                    }
                }
                AArch64Opcode::SubRI => {
                    if inst.operands.len() >= 3
                        && let (Some(dst), Some(src), Some(step)) = (
                            inst.operands[0].as_vreg(),
                            inst.operands[1].as_vreg(),
                            inst.operands[2].as_imm(),
                        )
                        && dst == result_vreg
                        && src == phi_vreg
                    {
                        return Some(-step);
                    }
                }
                _ => {}
            }
        }
    }
    None
}

/// Collect all vregs defined inside the loop body.
///
/// Uses the canonical operand-role classification (NOT "operand 0 of a
/// value-producer"): it also counts LDP's second def, pre/post-index writeback
/// bases, LSE RMW old-value defs in operand 1, and CAS/tied def-use operands,
/// so a vreg written by any of those inside the loop can never pass the
/// "loop-invariant" test. Strictly more conservative than the historical
/// operand-0 scan (it can only add defs, i.e. only REJECT more reductions).
fn collect_loop_defined_vregs(func: &MachFunction, lp: &NaturalLoop) -> HashSet<VReg> {
    let mut defs = HashSet::new();
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            crate::effects::aarch64_for_each_def_position(
                inst.opcode,
                inst.operands.len(),
                |pos| {
                    if let Some(vreg) = inst.operands.get(pos).and_then(|op| op.as_vreg()) {
                        defs.insert(vreg);
                    }
                },
            );
        }
    }
    defs
}

/// Apply a strength reduction by introducing a derived IV recurrence.
///
/// 1. In preheader: compute initial value `v_init = MulRR iv_init, stride`.
/// 2. Add a Phi in header for the running product.
/// 3. Replace MulRR in loop body with `Copy v_cur`.
/// 4. Advance the running product on the latch edge by `stride_step`.
fn apply_reduction(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    preheader: BlockId,
    reduction: &MulReduction,
    provenance: Option<&mut ProvenanceMap>,
) {
    if reduction.block_id != lp.latch {
        return;
    }

    let iv = &reduction.iv;
    let iv_init = match find_iv_init_vreg(func, lp, iv.vreg) {
        Some(v) => v,
        None => return,
    };

    let rc = reduction.dst.class;
    if iv.vreg.class != rc || iv_init.class != rc || reduction.invariant_vreg.class != rc {
        return;
    }
    let source_loc = func.inst(reduction.inst_id).source_loc;
    let with_reduction_source_loc = |mut inst: MachInst| {
        inst.source_loc = source_loc;
        inst
    };

    let init_vreg_id = func.alloc_vreg();
    let mul_init = func.push_inst(with_reduction_source_loc(MachInst::new(
        AArch64Opcode::MulRR,
        vec![
            MachOperand::VReg(VReg::new(init_vreg_id, rc)),
            MachOperand::VReg(iv_init),
            MachOperand::VReg(reduction.invariant_vreg),
        ],
    )));
    insert_before_terminator(func, preheader, mul_init);
    let mut created_insts = vec![mul_init];

    if iv.step == 0 {
        let inst = func.inst_mut(reduction.inst_id);
        inst.opcode = AArch64Opcode::Copy;
        inst.operands = vec![
            MachOperand::VReg(reduction.dst),
            MachOperand::VReg(VReg::new(init_vreg_id, rc)),
        ];
        inst.source_loc = source_loc;

        if let Some(provenance) = provenance {
            let pass = PassId::new("strength-reduce");
            provenance.record_in_place_transform(reduction.inst_id, pass.clone());
            provenance.record_clone(reduction.inst_id, mul_init, pass);
        }
        return;
    }

    // Allocate new vregs for the running derived-IV recurrence.
    let running_vreg = func.alloc_vreg(); // running product (Phi in header)
    let next_vreg = func.alloc_vreg(); // running product for the next iteration

    // The current iteration must see the current derived value, not the
    // incremented one. Advance to the next value on the latch edge instead.
    let inst = func.inst_mut(reduction.inst_id);
    inst.opcode = AArch64Opcode::Copy;
    inst.operands = vec![
        MachOperand::VReg(reduction.dst),
        MachOperand::VReg(VReg::new(running_vreg, rc)),
    ];

    let advance_inst = if iv.step == 1 {
        with_reduction_source_loc(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(VReg::new(next_vreg, rc)),
                MachOperand::VReg(VReg::new(running_vreg, rc)),
                MachOperand::VReg(reduction.invariant_vreg),
            ],
        ))
    } else if iv.step == -1 {
        with_reduction_source_loc(MachInst::new(
            AArch64Opcode::SubRR,
            vec![
                MachOperand::VReg(VReg::new(next_vreg, rc)),
                MachOperand::VReg(VReg::new(running_vreg, rc)),
                MachOperand::VReg(reduction.invariant_vreg),
            ],
        ))
    } else {
        let step_vreg_id = func.alloc_vreg();
        let stride_step_vreg = func.alloc_vreg();
        let step_mov = func.push_inst(with_reduction_source_loc(MachInst::new(
            AArch64Opcode::MovI,
            vec![
                MachOperand::VReg(VReg::new(step_vreg_id, rc)),
                MachOperand::Imm(iv.step),
            ],
        )));
        insert_before_terminator(func, preheader, step_mov);
        created_insts.push(step_mov);

        let stride_step_inst = func.push_inst(with_reduction_source_loc(MachInst::new(
            AArch64Opcode::MulRR,
            vec![
                MachOperand::VReg(VReg::new(stride_step_vreg, rc)),
                MachOperand::VReg(reduction.invariant_vreg),
                MachOperand::VReg(VReg::new(step_vreg_id, rc)),
            ],
        )));
        insert_before_terminator(func, preheader, stride_step_inst);
        created_insts.push(stride_step_inst);

        with_reduction_source_loc(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(VReg::new(next_vreg, rc)),
                MachOperand::VReg(VReg::new(running_vreg, rc)),
                MachOperand::VReg(VReg::new(stride_step_vreg, rc)),
            ],
        ))
    };
    let advance_inst_id = func.push_inst(advance_inst);
    insert_before_terminator(func, lp.latch, advance_inst_id);
    created_insts.push(advance_inst_id);

    let phi = func.push_inst(with_reduction_source_loc(MachInst::new(
        AArch64Opcode::Phi,
        vec![
            MachOperand::VReg(VReg::new(running_vreg, rc)),
            MachOperand::VReg(VReg::new(init_vreg_id, rc)),
            MachOperand::Block(preheader),
            MachOperand::VReg(VReg::new(next_vreg, rc)),
            MachOperand::Block(lp.latch),
        ],
    )));
    let header_insts = &mut func.block_mut(lp.header).insts;
    header_insts.insert(0, phi);
    created_insts.push(phi);

    if let Some(provenance) = provenance {
        let pass = PassId::new("strength-reduce");
        provenance.record_in_place_transform(reduction.inst_id, pass.clone());
        for inst_id in created_insts {
            provenance.record_clone(reduction.inst_id, inst_id, pass.clone());
        }
    }
}

/// Find the vreg of the IV's initial value from the preheader.
///
/// Looks at the Phi instruction in the header and finds the operand
/// that comes from outside the loop.
fn find_iv_init_vreg(func: &MachFunction, lp: &NaturalLoop, phi_vreg: VReg) -> Option<VReg> {
    let header_block = func.block(lp.header);
    for &inst_id in &header_block.insts {
        let inst = func.inst(inst_id);
        if inst.opcode != AArch64Opcode::Phi {
            continue;
        }
        let Some(def) = inst.operands.first().and_then(|op| op.as_vreg()) else {
            continue;
        };
        if def != phi_vreg {
            continue;
        }
        // Find the operand that comes from outside the loop.
        let mut i = 1;
        while i + 1 < inst.operands.len() {
            if let MachOperand::Block(bid) = &inst.operands[i + 1]
                && !lp.body.contains(bid)
                && let Some(v) = inst.operands[i].as_vreg()
            {
                return Some(v);
            }
            i += 2;
        }
    }
    None
}

/// Insert an instruction before the terminator of a block.
fn insert_before_terminator(func: &mut MachFunction, block: BlockId, inst_id: InstId) {
    let block_insts = &func.block(block).insts;
    if block_insts.is_empty() {
        func.block_mut(block).insts.push(inst_id);
    } else {
        // Check if last instruction is a terminator.
        // block_insts is non-empty (in else branch of is_empty() check).
        let last = block_insts[block_insts.len() - 1];
        let flags = func.inst(last).flags;
        let is_term = flags.is_terminator() || flags.is_branch();
        let block_data = func.block_mut(block);
        if is_term {
            let pos = block_data.insts.len() - 1;
            block_data.insts.insert(pos, inst_id);
        } else {
            block_data.insts.push(inst_id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use trust_cg_ir::{
        AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, RegClass, Signature,
        SourceLoc, TransformKind, TrustIrInstId, VReg,
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

    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 0,
            line,
            col: 7,
        }
    }

    /// Build a loop with a multiply that can be strength-reduced:
    ///
    /// ```text
    ///   bb0 (preheader):
    ///     v0 = MovI #0          ; IV init
    ///     B bb1
    ///
    ///   bb1 (header):
    ///     v1 = Phi [v0, bb0], [v4, bb3]  ; IV
    ///     CmpRI v1, #100
    ///     BCond bb2, bb3
    ///
    ///   bb3 (latch / body):
    ///     v2 = MulRR v1, v10    ; address = iv * stride (v10 is loop-invariant)
    ///     v3 = AddRI v2, v2, #0 ; use the multiply result
    ///     v4 = AddRI v1, v1, #1 ; IV increment
    ///     B bb1
    ///
    ///   bb2 (exit):
    ///     Ret
    /// ```
    fn make_mul_in_loop() -> MachFunction {
        let mut func = MachFunction::new("mul_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block(); // header
        let bb2 = func.create_block(); // exit
        let bb3 = func.create_block(); // latch/body

        // bb0: preheader
        let init = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(bb0, init);
        // v10 is loop-invariant (defined outside loop)
        let stride = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(10), imm(8)]));
        func.append_inst(bb0, stride);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // bb1: header with Phi for IV
        let phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![
                vreg(1),
                vreg(0),
                MachOperand::Block(bb0),
                vreg(4),
                MachOperand::Block(bb3),
            ],
        ));
        func.append_inst(bb1, phi);
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(100)]));
        func.append_inst(bb1, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        // bb3: body with multiply
        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(2), vreg(1), vreg(10)],
        ));
        func.append_inst(bb3, mul);
        let use_mul = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(3), vreg(2), imm(0)],
        ));
        func.append_inst(bb3, use_mul);
        let iv_inc = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(4), vreg(1), imm(1)],
        ));
        func.append_inst(bb3, iv_inc);
        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        // bb2: exit
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        // Set next_vreg past all used vregs.
        func.next_vreg = 20;

        func
    }

    fn set_latch_iv_step(func: &mut MachFunction, step: i64) {
        let increment_id = func
            .block(BlockId(3))
            .insts
            .iter()
            .copied()
            .find(|&iid| {
                let inst = func.inst(iid);
                inst.opcode == AArch64Opcode::AddRI
                    && inst
                        .operands
                        .first()
                        .and_then(|op| op.as_vreg())
                        .is_some_and(|vreg| vreg.id == 4 && vreg.class == RegClass::Gpr64)
            })
            .expect("expected original Gpr64 IV increment");
        func.inst_mut(increment_id).operands = vec![vreg(4), vreg(1), imm(step)];
    }

    #[test]
    fn test_strength_reduce_rewrites_mul_to_current_value_copy() {
        let mut func = make_mul_in_loop();

        // Verify the MulRR exists before.
        let has_mul_before = func
            .block(BlockId(3))
            .insts
            .iter()
            .any(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR);
        assert!(
            has_mul_before,
            "should have MulRR before strength reduction"
        );

        let mut pass = StrengthReduction;
        let changed = pass.run(&mut func);
        assert!(changed, "strength reduction should modify the function");

        // After reduction, the MulRR in the loop body (bb3) should be replaced
        // with a copy of the current derived value.
        let has_mul_after = func
            .block(BlockId(3))
            .insts
            .iter()
            .any(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR);
        assert!(
            !has_mul_after,
            "MulRR in loop body should be replaced with the current-value copy"
        );

        let has_copy = func
            .block(BlockId(3))
            .insts
            .iter()
            .any(|&iid| func.inst(iid).opcode == AArch64Opcode::Copy);
        assert!(has_copy, "should have Copy replacing the loop-body MulRR");
    }

    #[test]
    fn test_strength_reduce_adds_preheader_init() {
        let mut func = make_mul_in_loop();
        let mut pass = StrengthReduction;
        pass.run(&mut func);

        // Check that the preheader (bb0) has a MulRR for initialization.
        let has_init_mul = func
            .block(BlockId(0))
            .insts
            .iter()
            .any(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR);
        assert!(
            has_init_mul,
            "preheader should have a MulRR for initial value computation"
        );
    }

    #[test]
    fn test_strength_reduce_adds_phi() {
        let mut func = make_mul_in_loop();
        let mut pass = StrengthReduction;
        pass.run(&mut func);

        // Check that header (bb1) has an additional Phi for the running product.
        let phi_count = func
            .block(BlockId(1))
            .insts
            .iter()
            .filter(|&&iid| func.inst(iid).opcode == AArch64Opcode::Phi)
            .count();
        assert!(
            phi_count >= 2,
            "header should have at least 2 Phis (original IV + running product), got {}",
            phi_count
        );
    }

    #[test]
    fn test_strength_reduce_adds_latch_advance() {
        let mut func = make_mul_in_loop();
        let mut pass = StrengthReduction;
        pass.run(&mut func);

        let has_latch_advance = func
            .block(BlockId(3))
            .insts
            .iter()
            .any(|&iid| func.inst(iid).opcode == AArch64Opcode::AddRR);
        assert!(
            has_latch_advance,
            "latch should advance the derived IV for the next iteration"
        );
    }

    #[test]
    fn test_strength_reduce_preserves_source_loc_on_synthesized_insts() {
        let mut func = make_mul_in_loop();
        let loc = source_loc(73);

        let mul_id = func
            .block(BlockId(3))
            .insts
            .iter()
            .copied()
            .find(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR)
            .expect("expected loop-body multiply before strength reduction");
        func.inst_mut(mul_id).source_loc = Some(loc);

        let mut pass = StrengthReduction;
        assert!(pass.run(&mut func));

        let copy = func
            .block(BlockId(3))
            .insts
            .iter()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::Copy).then_some(inst)
            })
            .expect("expected Copy replacing the loop-body MulRR");
        assert_eq!(
            copy.source_loc,
            Some(loc),
            "strength-reduce must preserve source_loc on the rewritten loop-body value"
        );

        let init_mul = func
            .block(BlockId(0))
            .insts
            .iter()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::MulRR).then_some(inst)
            })
            .expect("expected preheader init multiply");
        assert_eq!(
            init_mul.source_loc,
            Some(loc),
            "strength-reduce must preserve source_loc on synthesized preheader init"
        );

        let advance = func
            .block(BlockId(3))
            .insts
            .iter()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::AddRR).then_some(inst)
            })
            .expect("expected synthesized latch advance");
        assert_eq!(
            advance.source_loc,
            Some(loc),
            "strength-reduce must preserve source_loc on synthesized latch advance"
        );

        let running_phi = func
            .block(BlockId(1))
            .insts
            .iter()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::Phi && inst.source_loc == Some(loc)).then_some(inst)
            })
            .expect("expected synthesized running-product Phi with source_loc");
        assert_eq!(running_phi.source_loc, Some(loc));
    }

    #[test]
    fn test_strength_reduce_provenance_marks_rewrite_and_synthesized_insts() {
        let mut func = make_mul_in_loop();
        let original_insts: HashSet<InstId> = func
            .block_order
            .iter()
            .flat_map(|&block_id| func.block(block_id).insts.iter().copied())
            .collect();

        let mul_id = func
            .block(BlockId(3))
            .insts
            .iter()
            .copied()
            .find(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR)
            .expect("expected loop-body multiply before strength reduction");

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(60), &[mul_id], PassId::new("isel"));

        let mut pass = StrengthReduction;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::Copy);
        let entry = provenance.get_entry(mul_id).unwrap();
        assert!(entry.is_active());
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(60)]);
        let transform = entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("strength-reduce"));
        assert_eq!(transform.kind, TransformKind::Survived);
        let synthesized: Vec<InstId> = func
            .block_order
            .iter()
            .flat_map(|&block_id| func.block(block_id).insts.iter().copied())
            .filter(|inst_id| !original_insts.contains(inst_id))
            .collect();
        assert_eq!(
            synthesized.len(),
            3,
            "step=1 reduction should synthesize init, advance, and Phi instructions"
        );

        let mapped = provenance
            .get_mach_insts(TrustIrInstId(60))
            .expect("reduction origin should map to original and derived recurrence");
        assert_eq!(
            mapped.len(),
            1 + synthesized.len(),
            "strength-reduce must preserve the original trust_ir origin on derived recurrence instructions"
        );
        assert!(mapped.contains(&mul_id));

        for inst_id in synthesized {
            assert!(
                mapped.contains(&inst_id),
                "derived recurrence instruction should remain mapped to the original trust_ir multiply"
            );
            let entry = provenance
                .get_entry(inst_id)
                .expect("synthesized instruction should have provenance");
            assert!(entry.is_active());
            assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(60)]);
            let transform = entry.transforms.last().unwrap();
            assert_eq!(transform.pass, PassId::new("strength-reduce"));
            assert_eq!(
                transform.kind,
                TransformKind::Cloned { source: mul_id },
                "derived recurrence should clone the source multiply provenance"
            );
        }
    }

    #[test]
    fn test_strength_reduce_zero_step_uses_preheader_product_without_recurrence() {
        let mut func = make_mul_in_loop();
        set_latch_iv_step(&mut func, 0);

        let mut pass = StrengthReduction;
        assert!(pass.run(&mut func));

        let header_phi_count = func
            .block(BlockId(1))
            .insts
            .iter()
            .filter(|&&iid| func.inst(iid).opcode == AArch64Opcode::Phi)
            .count();
        assert_eq!(
            header_phi_count, 1,
            "zero-step IV product is loop-invariant and must not add a running-product Phi"
        );

        let preheader_mov_count = func
            .block(BlockId(0))
            .insts
            .iter()
            .filter(|&&iid| func.inst(iid).opcode == AArch64Opcode::MovI)
            .count();
        assert_eq!(
            preheader_mov_count, 2,
            "zero-step reduction must not materialize an extra MovI #0"
        );

        let preheader_mul = func
            .block(BlockId(0))
            .insts
            .iter()
            .copied()
            .filter(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR)
            .collect::<Vec<_>>();
        assert_eq!(
            preheader_mul.len(),
            1,
            "zero-step reduction should synthesize only the invariant product"
        );
        let init_product = func.inst(preheader_mul[0]).operands[0]
            .as_vreg()
            .expect("preheader product should define a vreg");

        assert!(
            !func
                .block(BlockId(3))
                .insts
                .iter()
                .any(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR),
            "loop-body MulRR should be replaced"
        );
        assert!(
            !func
                .block(BlockId(3))
                .insts
                .iter()
                .any(|&iid| func.inst(iid).opcode == AArch64Opcode::AddRR),
            "zero-step reduction must not add a latch recurrence advance"
        );

        let copy = func
            .block(BlockId(3))
            .insts
            .iter()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::Copy).then_some(inst)
            })
            .expect("expected zero-step multiply replacement");
        assert_eq!(
            copy.operands,
            vec![vreg(2), MachOperand::VReg(init_product)],
            "zero-step multiply should copy the preheader product directly"
        );
    }

    #[test]
    fn test_strength_reduce_zero_step_preserves_source_loc() {
        let mut func = make_mul_in_loop();
        set_latch_iv_step(&mut func, 0);
        let loc = source_loc(88);

        let mul_id = func
            .block(BlockId(3))
            .insts
            .iter()
            .copied()
            .find(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR)
            .expect("expected loop-body multiply before strength reduction");
        func.inst_mut(mul_id).source_loc = Some(loc);

        let mut pass = StrengthReduction;
        assert!(pass.run(&mut func));

        let copy = func
            .block(BlockId(3))
            .insts
            .iter()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::Copy).then_some(inst)
            })
            .expect("expected zero-step multiply replacement");
        assert_eq!(
            copy.source_loc,
            Some(loc),
            "zero-step replacement must preserve source_loc on the rewritten instruction"
        );

        let init_mul = func
            .block(BlockId(0))
            .insts
            .iter()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::MulRR).then_some(inst)
            })
            .expect("expected zero-step preheader product");
        assert_eq!(
            init_mul.source_loc,
            Some(loc),
            "zero-step replacement must preserve source_loc on the preheader product"
        );
    }

    #[test]
    fn test_strength_reduce_zero_step_provenance_maps_only_preheader_product() {
        let mut func = make_mul_in_loop();
        set_latch_iv_step(&mut func, 0);
        let original_insts: HashSet<InstId> = func
            .block_order
            .iter()
            .flat_map(|&block_id| func.block(block_id).insts.iter().copied())
            .collect();

        let mul_id = func
            .block(BlockId(3))
            .insts
            .iter()
            .copied()
            .find(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR)
            .expect("expected loop-body multiply before strength reduction");

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(61), &[mul_id], PassId::new("isel"));

        let mut pass = StrengthReduction;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::Copy);
        let entry = provenance.get_entry(mul_id).unwrap();
        assert!(entry.is_active());
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(61)]);
        let transform = entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("strength-reduce"));
        assert_eq!(transform.kind, TransformKind::Survived);

        let synthesized: Vec<InstId> = func
            .block_order
            .iter()
            .flat_map(|&block_id| func.block(block_id).insts.iter().copied())
            .filter(|inst_id| !original_insts.contains(inst_id))
            .collect();
        assert_eq!(
            synthesized.len(),
            1,
            "zero-step reduction should synthesize only the preheader product"
        );

        let mapped = provenance
            .get_mach_insts(TrustIrInstId(61))
            .expect("zero-step product origin should map to original and preheader product");
        assert_eq!(
            mapped.len(),
            2,
            "zero-step reduction should map only the rewritten multiply and invariant product"
        );
        assert!(mapped.contains(&mul_id));
        assert!(mapped.contains(&synthesized[0]));

        let entry = provenance
            .get_entry(synthesized[0])
            .expect("preheader product should have provenance");
        assert!(entry.is_active());
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(61)]);
        let transform = entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("strength-reduce"));
        assert_eq!(
            transform.kind,
            TransformKind::Cloned { source: mul_id },
            "preheader product should clone the source multiply provenance"
        );
    }

    #[test]
    fn test_strength_reduce_uses_matching_iv_init() {
        let mut func = make_mul_in_loop();
        let bb1 = BlockId(1);
        let extra_phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![
                vreg(11),
                vreg(12),
                MachOperand::Block(BlockId(0)),
                vreg(13),
                MachOperand::Block(BlockId(3)),
            ],
        ));
        func.block_mut(bb1).insts.insert(0, extra_phi);

        let mut pass = StrengthReduction;
        pass.run(&mut func);

        let init_mul = func
            .block(BlockId(0))
            .insts
            .iter()
            .rev()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::MulRR).then_some(inst)
            })
            .expect("expected preheader init multiply");

        assert_eq!(
            init_mul.operands[1].as_vreg().map(|v| v.id),
            Some(0),
            "strength reduction should seed from the matched IV's init value"
        );
    }

    #[test]
    fn test_strength_reduce_same_numeric_different_class_increment_does_not_match_iv() {
        let mut func = make_mul_in_loop();
        let latch = BlockId(3);

        let increment_id = func
            .block(latch)
            .insts
            .iter()
            .copied()
            .find(|&iid| {
                let inst = func.inst(iid);
                inst.opcode == AArch64Opcode::AddRI
                    && inst
                        .operands
                        .first()
                        .and_then(|op| op.as_vreg())
                        .is_some_and(|vreg| vreg.id == 4 && vreg.class == RegClass::Gpr64)
            })
            .expect("expected original Gpr64 IV increment");
        func.inst_mut(increment_id).operands = vec![
            vreg_class(4, RegClass::Gpr32),
            vreg_class(1, RegClass::Gpr32),
            imm(1),
        ];

        let mut pass = StrengthReduction;
        assert!(
            !pass.run(&mut func),
            "different-class same-id increment must not create a false IV match"
        );
        assert!(
            func.block(latch)
                .insts
                .iter()
                .any(|&iid| func.inst(iid).opcode == AArch64Opcode::MulRR),
            "loop multiply must remain when the IV update is only a raw-id collision"
        );
    }

    #[test]
    fn test_strength_reduce_same_numeric_different_class_loop_def_keeps_invariant_reducible() {
        let mut func = make_mul_in_loop();
        let latch = BlockId(3);
        let local_same_id_other_class = func.push_inst(MachInst::new(
            AArch64Opcode::MovI,
            vec![vreg_class(10, RegClass::Gpr32), imm(99)],
        ));
        func.block_mut(latch)
            .insts
            .insert(0, local_same_id_other_class);

        let mut pass = StrengthReduction;
        assert!(
            pass.run(&mut func),
            "Gpr32 v10 loop def must not block reduction using invariant Gpr64 v10"
        );
        assert!(
            func.block(latch)
                .insts
                .iter()
                .any(|&iid| func.inst(iid).opcode == AArch64Opcode::Copy),
            "loop-body multiply should be replaced with the running-product copy"
        );
    }

    #[test]
    fn test_strength_reduce_uses_class_exact_iv_init() {
        let mut func = make_mul_in_loop();
        let bb1 = BlockId(1);
        let class_collision_phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![
                vreg_class(1, RegClass::Gpr32),
                vreg_class(12, RegClass::Gpr32),
                MachOperand::Block(BlockId(0)),
                vreg_class(13, RegClass::Gpr32),
                MachOperand::Block(BlockId(3)),
            ],
        ));
        func.block_mut(bb1).insts.insert(0, class_collision_phi);

        let mut pass = StrengthReduction;
        assert!(pass.run(&mut func));

        let init_mul = func
            .block(BlockId(0))
            .insts
            .iter()
            .rev()
            .find_map(|&iid| {
                let inst = func.inst(iid);
                (inst.opcode == AArch64Opcode::MulRR).then_some(inst)
            })
            .expect("expected preheader init multiply");

        assert_eq!(
            init_mul.operands[1],
            vreg(0),
            "same-id Gpr32 Phi must not supply the Gpr64 IV's initial value"
        );
    }

    #[test]
    fn test_no_strength_reduce_without_loop() {
        let mut func = MachFunction::new("no_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(0), vreg(1), vreg(2)],
        ));
        func.append_inst(bb0, mul);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb0, ret);

        let mut pass = StrengthReduction;
        assert!(!pass.run(&mut func), "no loops means no strength reduction");
    }

    #[test]
    fn test_no_strength_reduce_non_iv_mul() {
        // Loop with MulRR but neither operand is an IV.
        let mut func = MachFunction::new("non_iv_mul".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // No Phi -> no induction variable detected.
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(5), imm(10)]));
        func.append_inst(bb1, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        // bb3: body with mul (neither operand is an IV)
        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(6), vreg(7), vreg(8)],
        ));
        func.append_inst(bb3, mul);
        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        let mut pass = StrengthReduction;
        assert!(
            !pass.run(&mut func),
            "should not strength-reduce MulRR when neither operand is an IV"
        );
    }

    #[test]
    fn test_no_strength_reduce_non_latch_mul() {
        let mut func =
            MachFunction::new("non_latch_mul".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block(); // header
        let bb2 = func.create_block(); // exit
        let bb3 = func.create_block(); // body with mul
        let bb4 = func.create_block(); // latch

        let init = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(bb0, init);
        let stride = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(10), imm(8)]));
        func.append_inst(bb0, stride);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![
                vreg(1),
                vreg(0),
                MachOperand::Block(bb0),
                vreg(4),
                MachOperand::Block(bb4),
            ],
        ));
        func.append_inst(bb1, phi);
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(100)]));
        func.append_inst(bb1, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(2), vreg(1), vreg(10)],
        ));
        func.append_inst(bb3, mul);
        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb4)],
        ));
        func.append_inst(bb3, br3);

        let iv_inc = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(4), vreg(1), imm(1)],
        ));
        func.append_inst(bb4, iv_inc);
        let br4 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb4, br4);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb4);
        func.add_edge(bb4, bb1);

        let mut pass = StrengthReduction;
        assert!(
            !pass.run(&mut func),
            "should not strength-reduce MulRR outside the loop latch"
        );
    }

    #[test]
    fn test_strength_reduce_idempotent() {
        let mut func = make_mul_in_loop();
        let mut pass = StrengthReduction;

        // First run does the reduction.
        let changed1 = pass.run(&mut func);
        assert!(changed1);

        // Second run: MulRR is gone from loop body, so nothing to reduce.
        let changed2 = pass.run(&mut func);
        assert!(!changed2, "second pass should be idempotent");
    }
}
