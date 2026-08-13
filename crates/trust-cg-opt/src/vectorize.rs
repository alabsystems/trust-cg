// trust-cg-opt - NEON/SIMD auto-vectorization pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Auto-vectorization pass: detects vectorizable loops and transforms
//! scalar operations into NEON SIMD instructions.
//!
//! # Overview
//!
//! This pass analyzes natural loops for vectorization opportunities.
//! For each loop body, it checks whether the loop iterations are
//! independent (no cross-iteration data dependencies) and whether
//! the operations can be mapped to NEON SIMD instructions profitably.
//!
//! # Algorithm
//!
//! 1. Compute dominator tree and loop analysis.
//! 2. For each natural loop (innermost first):
//!    a. Analyze the loop body for vectorizability.
//!    b. Build a `VectorizationPlan` describing the transformation.
//!    c. Check profitability using the cost model.
//!    d. If profitable, emit the plan (future: actual IR rewrite).
//! 3. Return whether any vectorization opportunity was found.
//!
//! # Vectorizability Requirements
//!
//! A loop is vectorizable if:
//! - It has a single latch (simple counted loop form).
//! - The loop body contains only vectorizable instructions.
//! - There are no cross-iteration data dependencies (no reduction/recurrence).
//! - The trip count is known or can be bounded.
//! - Memory accesses are consecutive (stride-1) or absent.
//!
//! # NEON Arrangement Selection
//!
//! The element type of the loop's primary data determines the NEON
//! arrangement:
//!
//! | Element Type | Arrangement | Lanes | Width |
//! |-------------|-------------|-------|-------|
//! | i8          | 16B         | 16    | 128b  |
//! | i16         | 8H          | 8     | 128b  |
//! | i32         | 4S          | 4     | 128b  |
//! | i64 / f64   | 2D          | 2     | 128b  |
//! | f32         | 4S          | 4     | 128b  |
//!
//! # Cost Model Integration
//!
//! Uses [`trust_cg_ir::cost_model::MultiTargetCostModel`] to compare scalar
//! vs NEON cost for the loop body. Vectorization proceeds only when
//! the NEON cost (including setup/teardown overhead) is lower than the
//! scalar cost scaled by the vectorization factor.
//!
//! Reference: LLVM `LoopVectorize.cpp`, CompCert verified loop optimization.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::aarch64_regs::preg_class;
use trust_cg_ir::cost_model::{CostModelGen, MultiTargetCostModel, NeonArrangement, NeonOp};
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProofFact,
    ProvenanceMap, RegClass, VReg,
};

use crate::cache::StableHasher;
use crate::dom::DomTree;
use crate::effects::{MemoryEffect, opcode_effect, produces_value, reads_flags, writes_flags};
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};
use crate::pgo::ProfileHotness;
use crate::proof_opts::{
    OptAdmissionRoute, OptCertificate, OptCertificateKind, OptConsumedProofFact,
    OptTransformIdentity, ProofOptimizationMetadata,
};

const DEFAULT_MIN_TRIP_COUNT: u32 = 8;
const HOT_MIN_TRIP_COUNT: u32 = 4;
const ENABLE_CONTAINS4_SCANNER_MEMORY_REWRITE_ENV: &str =
    "TRUST_CG_ENABLE_CONTAINS4_SCANNER_MEMORY_REWRITE";
const ENABLE_CONTAINS4_SCANNER_BATCH_REWRITE_ENV: &str =
    "TRUST_CG_ENABLE_CONTAINS4_SCANNER_BATCH_REWRITE";

fn contains4_env_enabled(name: &str) -> bool {
    std::env::var(name).is_ok_and(|value| {
        matches!(
            value.to_ascii_lowercase().as_str(),
            "1" | "true" | "yes" | "on"
        )
    })
}

fn contains4_scanner_memory_rewrite_env_enabled() -> bool {
    contains4_env_enabled(ENABLE_CONTAINS4_SCANNER_MEMORY_REWRITE_ENV)
}

fn contains4_scanner_batch_rewrite_env_enabled() -> bool {
    contains4_env_enabled(ENABLE_CONTAINS4_SCANNER_BATCH_REWRITE_ENV)
}

// ---------------------------------------------------------------------------
// VectorizationPlan — describes how to vectorize a loop
// ---------------------------------------------------------------------------

/// Element type for vectorization — determines NEON arrangement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VecElementType {
    /// 8-bit integer (i8).
    I8,
    /// 16-bit integer (i16).
    I16,
    /// 32-bit integer (i32).
    I32,
    /// 64-bit integer (i64).
    I64,
    /// 32-bit float (f32).
    F32,
    /// 64-bit float (f64).
    F64,
}

impl VecElementType {
    /// Element size in bits.
    pub fn bits(self) -> u32 {
        match self {
            Self::I8 => 8,
            Self::I16 => 16,
            Self::I32 => 32,
            Self::I64 => 64,
            Self::F32 => 32,
            Self::F64 => 64,
        }
    }

    /// Best 128-bit NEON arrangement for this element type.
    pub fn neon_arrangement(self) -> NeonArrangement {
        match self {
            Self::I8 => NeonArrangement::B16,
            Self::I16 => NeonArrangement::H8,
            Self::I32 | Self::F32 => NeonArrangement::S4,
            Self::I64 | Self::F64 => NeonArrangement::D2,
        }
    }

    /// Number of SIMD lanes in the 128-bit arrangement.
    pub fn lanes(self) -> u32 {
        self.neon_arrangement().lane_count()
    }
}

/// Describes a vectorization plan for a single loop.
#[derive(Debug, Clone)]
pub struct VectorizationPlan {
    /// The loop header block.
    pub loop_header: BlockId,
    /// The loop latch block.
    pub loop_latch: BlockId,
    /// Estimated trip count (iterations). None if unknown.
    pub trip_count: Option<u32>,
    /// Primary element type for the vectorized computation.
    pub element_type: VecElementType,
    /// NEON arrangement to use.
    pub arrangement: NeonArrangement,
    /// Vectorization factor (number of scalar iterations per NEON iteration).
    pub vf: u32,
    /// Scalar instructions that will be vectorized.
    pub vectorizable_insts: Vec<InstId>,
    /// Contextual scalar compare idioms that can become vector compares.
    pub compare_idioms: Vec<VectorCompareIdiom>,
    /// Scalar horizontal-any reductions fed by vector compare idioms.
    pub horizontal_any_reductions: Vec<HorizontalAnyReduction>,
    /// Ordered i64 subtract reductions fed by vectorized bitreverse lanes.
    pub ordered_sub_reductions: Vec<OrderedSubReduction>,
    /// Counted i32 scalar induction that must be expanded to VF lanes.
    pub induction: Option<VectorInduction>,
    /// Estimated scalar cost (total cycles for trip_count iterations).
    pub scalar_cost: f64,
    /// Estimated NEON cost (total cycles including overhead).
    pub neon_cost: f64,
    /// Whether this plan is profitable (neon_cost < scalar_cost).
    pub is_profitable: bool,
}

impl VectorizationPlan {
    /// Speedup factor: scalar_cost / neon_cost. > 1.0 means profitable.
    pub fn speedup(&self) -> f64 {
        if self.neon_cost <= 0.0 {
            return 0.0;
        }
        self.scalar_cost / self.neon_cost
    }
}

/// Contextual scalar compare pattern that can be lowered to a NEON vector
/// compare. A bare `CmpRR` is not vectorizable because it writes NZCV; the
/// vector form is only valid when the flags are immediately materialized as a
/// value by `CSet EQ`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VectorCompareIdiom {
    /// Scalar `CmpRR` instruction comparing two i32 values.
    pub cmp_inst: InstId,
    /// Following `CSet EQ` instruction materializing the equality result.
    pub cset_inst: InstId,
    /// Compare semantics represented by this idiom.
    pub kind: VectorCompareKind,
}

/// Vector compare semantics recognized by the vectorizer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorCompareKind {
    /// Per-lane i32 equality, lowering to `CMEQ.4S`.
    I32Eq,
}

/// Scalar horizontal reduction pattern recognized by the vectorizer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HorizontalAnyReduction {
    /// Compare value feeding the reduction.
    pub compare: VectorCompareIdiom,
    /// Scalar reducer, currently `OrrRR acc, acc, cmp_bool`.
    pub reducer_inst: InstId,
    /// Reduction semantics represented by this idiom.
    pub kind: HorizontalAnyReductionKind,
}

/// Horizontal reduction semantics suitable for ay literal scans.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HorizontalAnyReductionKind {
    /// Any non-zero lane in a `CMEQ.4S` mask. Lowered through `UMAXV`
    /// (`vmaxvq_u32`) plus a scalar bridge into the loop accumulator.
    I32EqAny,
}

/// Scalar ordered subtract reduction recognized for vector bitreverse loops.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OrderedSubReduction {
    /// Vectorized bitreverse instruction producing the lane values.
    pub producer_inst: InstId,
    /// Optional scalar extension instruction between producer and reducer.
    pub extension_inst: Option<InstId>,
    /// Scalar producer value that maps to the vector lane register.
    pub lane_value: VReg,
    /// Scalar reducer, `sub acc, acc, value`.
    pub reducer_inst: InstId,
    /// Optional adjacent copy writing the reducer result back to the
    /// loop-carried accumulator.
    pub writeback_inst: Option<InstId>,
    /// Optional adjacent copy loading the loop-carried accumulator into the
    /// reducer lhs.
    pub accumulator_load_inst: Option<InstId>,
    /// Loop-carried i64 accumulator updated by the reducer.
    pub accumulator: VReg,
    /// Reduction semantics represented by this idiom.
    pub kind: OrderedSubReductionKind,
}

/// Ordered subtract bridge shapes used by `revertBits.c`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OrderedSubReductionKind {
    /// `sub i64_acc, i64_acc, zext(rbit32_lane)`.
    I32ZextToI64,
    /// `sub i64_acc, i64_acc, rbit64_lane`.
    I64,
}

/// Scalar i32 induction recognized for VF=4 lane materialization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VectorInduction {
    /// Scalar `AddRI next, current, #1` step instruction.
    pub step_inst: InstId,
    /// Current scalar induction value used by vectorized loop-body ops.
    pub scalar_current: VReg,
    /// Optional stack-origin/promoted copy of `scalar_current` consumed by a
    /// vectorized instruction.
    pub scalar_current_alias: Option<VReg>,
    /// Next scalar induction value produced by the step instruction.
    pub scalar_next: VReg,
    /// Optional `Sxtw` of the same current value, used by mixed-width
    /// bitreverse loops such as `revertBits.c`.
    pub sign_extend_inst: Option<InstId>,
    /// Sign-extended i64 current value produced by `sign_extend_inst`.
    pub sign_extended_current: Option<VReg>,
    /// Scalar step before vectorization. This slice supports only `1`.
    pub step: i64,
}

// ---------------------------------------------------------------------------
// Vectorizability analysis
// ---------------------------------------------------------------------------

/// Check if a single instruction can be vectorized (mapped to NEON).
///
/// An instruction is vectorizable if:
/// - It is a pure arithmetic/logical operation (no memory, no call).
/// - It maps to a known NEON operation.
/// - It does not set condition flags (CMP, TST, ADDS, SUBS).
pub fn is_vectorizable(opcode: AArch64Opcode) -> bool {
    // Must be pure (no memory side effects).
    if opcode_effect(opcode) != MemoryEffect::Pure {
        return false;
    }

    // Must have a NEON equivalent.
    scalar_to_neon_op(opcode).is_some()
}

/// Map a scalar AArch64 opcode to its NEON operation equivalent.
pub fn scalar_to_neon_op(opcode: AArch64Opcode) -> Option<NeonOp> {
    use AArch64Opcode::*;
    match opcode {
        AddRR | AddRI => Some(NeonOp::Add),
        SubRR | SubRI => Some(NeonOp::Sub),
        MulRR => Some(NeonOp::Mul),
        Neg => Some(NeonOp::Neg),
        AndRR | AndRI => Some(NeonOp::And),
        OrrRR | OrrRI => Some(NeonOp::Orr),
        EorRR | EorRI => Some(NeonOp::Eor),
        BicRR => Some(NeonOp::Bic),
        LslRI => Some(NeonOp::Shl),
        LsrRI => Some(NeonOp::Ushr),
        AsrRI => Some(NeonOp::Sshr),
        Rbit => Some(NeonOp::Rbit),
        FaddRR => Some(NeonOp::Fadd),
        FmulRR => Some(NeonOp::Fmul),
        _ => None,
    }
}

/// Returns true when an operand is a 32-bit virtual register.
fn is_gpr32_vreg(operand: &MachOperand) -> bool {
    matches!(
        operand,
        MachOperand::VReg(vreg) if vreg.class == RegClass::Gpr32
    )
}

/// Returns the virtual register defined by an instruction, if any.
fn def_vreg(inst: &trust_cg_ir::MachInst) -> Option<VReg> {
    if !produces_value(inst.opcode) {
        return None;
    }
    match inst.operands.first() {
        Some(MachOperand::VReg(vreg)) => Some(*vreg),
        _ => None,
    }
}

/// Returns the virtual register id defined by an instruction, if any.
fn def_vreg_id(inst: &trust_cg_ir::MachInst) -> Option<u32> {
    def_vreg(inst).map(|vreg| vreg.id)
}

/// Returns true if an operand uses the given virtual register id.
fn operand_uses_vreg(operand: &MachOperand, vreg_id: u32) -> bool {
    matches!(operand, MachOperand::VReg(vreg) if vreg.id == vreg_id)
}

fn operand_uses_exact_vreg(operand: &MachOperand, expected: VReg) -> bool {
    matches!(operand, MachOperand::VReg(vreg) if *vreg == expected)
}

fn inst_source_uses_vreg(inst: &MachInst, vreg_id: u32) -> bool {
    let start = if produces_value(inst.opcode) { 1 } else { 0 };
    inst.operands
        .iter()
        .skip(start)
        .any(|operand| operand_uses_vreg(operand, vreg_id))
}

/// Returns the i32 equality compare idioms in a loop body.
///
/// Recognized shape:
///
/// ```text
/// cmp   w_lhs, w_rhs
/// cset  w_bool, eq
/// ```
///
/// `CSet EQ` is represented with condition immediate `0`, matching the
/// AArch64 EQ condition-code encoding.
fn find_i32_eq_compare_idioms(func: &MachFunction, lp: &NaturalLoop) -> Vec<VectorCompareIdiom> {
    const AARCH64_COND_EQ: i64 = 0;

    let mut idioms = Vec::new();
    for &block_id in &lp.body {
        let block = func.block(block_id);
        for window in block.insts.windows(2) {
            let cmp_id = window[0];
            let cset_id = window[1];
            let cmp = func.inst(cmp_id);
            let cset = func.inst(cset_id);

            if cmp.opcode != AArch64Opcode::CmpRR || cset.opcode != AArch64Opcode::CSet {
                continue;
            }
            if cmp.operands.len() != 2 || cset.operands.len() != 2 {
                continue;
            }
            if !is_gpr32_vreg(&cmp.operands[0]) || !is_gpr32_vreg(&cmp.operands[1]) {
                continue;
            }
            if !is_gpr32_vreg(&cset.operands[0]) {
                continue;
            }
            if !matches!(cset.operands[1], MachOperand::Imm(AARCH64_COND_EQ)) {
                continue;
            }

            idioms.push(VectorCompareIdiom {
                cmp_inst: cmp_id,
                cset_inst: cset_id,
                kind: VectorCompareKind::I32Eq,
            });
        }
    }

    idioms
}

/// Returns horizontal-any reductions fed by recognized compare idioms.
///
/// Recognized scalar shape:
///
/// ```text
/// orr acc, acc, cmp_bool
/// ```
///
/// The compare value must be the `CSet EQ` result from a recognized i32
/// equality idiom. This models the scalar "any match so far" recurrence that
/// the ay padded literal scanner reduces with `vmaxvq_u32` in the vector path.
fn find_horizontal_any_reductions(
    func: &MachFunction,
    lp: &NaturalLoop,
    compare_idioms: &[VectorCompareIdiom],
) -> Vec<HorizontalAnyReduction> {
    let mut compare_by_result: HashMap<VReg, VectorCompareIdiom> = HashMap::new();
    for &idiom in compare_idioms {
        if let Some(result) = def_vreg(func.inst(idiom.cset_inst)) {
            compare_by_result.insert(result, idiom);
        }
    }

    let mut reductions = Vec::new();
    for &block_id in &lp.body {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::OrrRR || inst.operands.len() != 3 {
                continue;
            }

            let Some(acc) = def_vreg(inst) else {
                continue;
            };
            let lhs_is_acc = operand_uses_exact_vreg(&inst.operands[1], acc);
            let rhs_is_acc = operand_uses_exact_vreg(&inst.operands[2], acc);

            let cmp_result = if lhs_is_acc {
                vreg_from_operand(&inst.operands[2])
            } else if rhs_is_acc {
                vreg_from_operand(&inst.operands[1])
            } else {
                None
            };

            if let Some(cmp_result) = cmp_result
                && let Some(&compare) = compare_by_result.get(&cmp_result)
            {
                reductions.push(HorizontalAnyReduction {
                    compare,
                    reducer_inst: inst_id,
                    kind: HorizontalAnyReductionKind::I32EqAny,
                });
            }
        }
    }
    reductions
}

fn find_ordered_sub_reductions(
    func: &MachFunction,
    lp: &NaturalLoop,
    vectorizable_insts: &[InstId],
    maps: &VecMaps,
) -> Vec<OrderedSubReduction> {
    let defs = &maps.defs;
    let use_counts = &maps.use_counts;
    let vectorizable_set: HashSet<InstId> = vectorizable_insts.iter().copied().collect();
    let mut reductions = Vec::new();

    for &block_id in &lp.body {
        let block_insts = &func.block(block_id).insts;
        for (pos, &inst_id) in block_insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::SubRR || inst.operands.len() != 3 {
                continue;
            }

            let Some(sub_dst) = vreg_from_operand(&inst.operands[0]) else {
                continue;
            };
            let Some(lhs) = vreg_from_operand(&inst.operands[1]) else {
                continue;
            };

            let (accumulator, writeback_inst, accumulator_load_inst) = if sub_dst.class
                == RegClass::Gpr64
                && lhs.class == RegClass::Gpr64
                && sub_dst.id == lhs.id
            {
                (sub_dst, None, None)
            } else if let Some((accumulator, writeback_inst, accumulator_load_inst)) =
                find_stack_slot_ordered_sub_accumulator(
                    func,
                    block_insts,
                    pos,
                    lhs,
                    sub_dst,
                    &use_counts,
                    defs,
                )
            {
                (
                    accumulator,
                    Some(writeback_inst),
                    Some(accumulator_load_inst),
                )
            } else if lhs.class == RegClass::Gpr64 {
                let Some(&next_id) = block_insts.get(pos + 1) else {
                    continue;
                };
                let next = func.inst(next_id);
                if next.opcode != AArch64Opcode::MovR || next.operands.len() != 2 {
                    continue;
                }
                let Some(writeback_dst) = vreg_from_operand(&next.operands[0]) else {
                    continue;
                };
                let Some(writeback_src) = vreg_from_operand(&next.operands[1]) else {
                    continue;
                };
                let accumulator_load_inst =
                    block_insts.get(pos.wrapping_sub(1)).and_then(|&prev_id| {
                        let prev = func.inst(prev_id);
                        let (load_dst, load_src) = movr_vreg_copy(prev)?;
                        (load_dst.class == RegClass::Gpr64
                            && load_src.class == RegClass::Gpr64
                            && load_dst.id == lhs.id
                            && load_src.id == writeback_dst.id)
                            .then_some(prev_id)
                    });

                if writeback_dst.class != RegClass::Gpr64
                    || writeback_src.class != RegClass::Gpr64
                    || writeback_src.id != sub_dst.id
                    || use_counts.get(&lhs.id).copied().unwrap_or(0) != 1
                    || use_counts.get(&sub_dst.id).copied().unwrap_or(0) != 1
                {
                    continue;
                }
                let Some(accumulator_load_inst) = accumulator_load_inst else {
                    continue;
                };
                (writeback_dst, Some(next_id), Some(accumulator_load_inst))
            } else {
                continue;
            };

            let Some(value) = vreg_from_operand(&inst.operands[2]) else {
                continue;
            };
            let Some(&value_def) = defs.get(&value.id) else {
                continue;
            };

            if func.inst(value_def).opcode == AArch64Opcode::Rbit
                && vectorizable_set.contains(&value_def)
                && value.class == RegClass::Gpr64
                && use_counts.get(&value.id).copied().unwrap_or(0) == 1
            {
                reductions.push(OrderedSubReduction {
                    producer_inst: value_def,
                    extension_inst: None,
                    lane_value: value,
                    reducer_inst: inst_id,
                    writeback_inst,
                    accumulator_load_inst,
                    accumulator,
                    kind: OrderedSubReductionKind::I64,
                });
                continue;
            }

            let extension = func.inst(value_def);
            let is_zero_extend = extension.opcode == AArch64Opcode::Uxtw
                || (extension.opcode == AArch64Opcode::MovR
                    && extension.operands.len() == 2
                    && matches!(extension.operands.first(), Some(MachOperand::VReg(dst)) if dst.class == RegClass::Gpr64)
                    && matches!(extension.operands.get(1), Some(MachOperand::VReg(src)) if src.class == RegClass::Gpr32));
            if !is_zero_extend
                || extension.operands.len() != 2
                || value.class != RegClass::Gpr64
                || use_counts.get(&value.id).copied().unwrap_or(0) != 1
            {
                continue;
            }
            let Some(narrow_value) = vreg_from_operand(&extension.operands[1]) else {
                continue;
            };
            let Some(&producer_inst) = defs.get(&narrow_value.id) else {
                continue;
            };
            if func.inst(producer_inst).opcode != AArch64Opcode::Rbit
                || !vectorizable_set.contains(&producer_inst)
                || narrow_value.class != RegClass::Gpr32
                || use_counts.get(&narrow_value.id).copied().unwrap_or(0) != 1
            {
                continue;
            }

            reductions.push(OrderedSubReduction {
                producer_inst,
                extension_inst: Some(value_def),
                lane_value: narrow_value,
                reducer_inst: inst_id,
                writeback_inst,
                accumulator_load_inst,
                accumulator,
                kind: OrderedSubReductionKind::I32ZextToI64,
            });
        }
    }

    reductions
}

fn find_stack_slot_ordered_sub_accumulator(
    func: &MachFunction,
    block_insts: &[InstId],
    reducer_pos: usize,
    lhs: VReg,
    sub_dst: VReg,
    use_counts: &HashMap<u32, usize>,
    defs: &HashMap<u32, InstId>,
) -> Option<(VReg, InstId, InstId)> {
    if lhs.class != RegClass::Gpr64
        || sub_dst.class != RegClass::Gpr64
        || use_counts.get(&lhs.id).copied().unwrap_or(0) != 1
        || use_counts.get(&sub_dst.id).copied().unwrap_or(0) != 1
    {
        return None;
    }

    let writeback_inst = *block_insts.get(reducer_pos + 1)?;
    let address = str_gpr64_to_stack_slot_address(func, writeback_inst, sub_dst, defs)?;
    let (load_pos, load_inst) = block_insts
        .iter()
        .copied()
        .take(reducer_pos)
        .enumerate()
        .rev()
        .find(|(_, inst_id)| {
            ldr_gpr64_from_stack_slot(func, *inst_id, lhs, Some(address), defs).is_some()
        })?;

    if insts_have_memory_write_or_call(func, &block_insts[load_pos + 1..reducer_pos]) {
        return None;
    }

    Some((lhs, writeback_inst, load_inst))
}

/// Infer the element type from an instruction's operands.
///
/// Uses the register class of the destination (operand[0]) to determine
/// the element width. Returns None if no dest or unrecognized class.
fn infer_element_type(func: &MachFunction, inst_id: InstId) -> Option<VecElementType> {
    let inst = func.inst(inst_id);
    if !produces_value(inst.opcode) {
        return None;
    }
    if inst.operands.is_empty() {
        return None;
    }

    match &inst.operands[0] {
        MachOperand::VReg(vreg) => match vreg.class {
            RegClass::Gpr32 => Some(VecElementType::I32),
            RegClass::Gpr64 => Some(VecElementType::I64),
            RegClass::Fpr32 => Some(VecElementType::F32),
            RegClass::Fpr64 => Some(VecElementType::F64),
            _ => None,
        },
        _ => None,
    }
}

/// Check if a loop body has cross-iteration data dependencies.
///
/// A cross-iteration dependency exists when an instruction uses a value
/// defined in the same loop body (a recurrence/reduction). We conservatively
/// check: all source operands of vectorizable instructions must either be
/// defined outside the loop or be loop-invariant.
///
/// Returns true if the loop body is dependency-free for vectorization.
fn is_dependency_free(
    func: &MachFunction,
    lp: &NaturalLoop,
    vectorizable_insts: &[InstId],
    induction: Option<VectorInduction>,
) -> bool {
    // Build the set of defs inside the loop body.
    let mut loop_defs: HashMap<u32, InstId> = HashMap::new();
    for &block_id in &lp.body {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if produces_value(inst.opcode)
                && let Some(MachOperand::VReg(vreg)) = inst.operands.first()
            {
                loop_defs.insert(vreg.id, inst_id);
            }
        }
    }

    let vectorizable_set: HashSet<InstId> = vectorizable_insts.iter().copied().collect();

    // For each vectorizable instruction, check that source operands
    // defined inside the loop are also vectorizable (parallel, not recurrence).
    for &inst_id in vectorizable_insts {
        let inst = func.inst(inst_id);
        // Source operands are operands[1..] for most instructions.
        for operand in inst.operands.iter().skip(1) {
            if let MachOperand::VReg(vreg) = operand
                && let Some(&def_inst) = loop_defs.get(&vreg.id)
            {
                if induction.is_some_and(|induction| vreg.id == induction.scalar_current.id) {
                    continue;
                }
                if induction.is_some_and(|induction| {
                    induction
                        .scalar_current_alias
                        .is_some_and(|alias| vreg.id == alias.id)
                }) {
                    continue;
                }
                if induction.is_some_and(|induction| {
                    induction
                        .sign_extended_current
                        .is_some_and(|wide| vreg.id == wide.id)
                }) {
                    continue;
                }
                // This value is defined inside the loop.
                // If it's NOT a vectorizable instruction, we have a
                // dependency on a non-vectorizable computation (e.g.,
                // a phi node for induction variable, a load, etc.).
                // For now, we allow dependencies on other vectorizable
                // instructions (they'll all be vectorized together).
                // But if an instruction uses its OWN output from a prior
                // iteration (via phi), that's a recurrence.
                if !vectorizable_set.contains(&def_inst) {
                    return false;
                }
            }
        }
    }

    true
}

fn vectorized_defs_have_only_vector_consumers(
    func: &MachFunction,
    vectorizable_insts: &[InstId],
    compare_idioms: &[VectorCompareIdiom],
    horizontal_any_reductions: &[HorizontalAnyReduction],
    ordered_sub_reductions: &[OrderedSubReduction],
) -> bool {
    let vectorizable_set: HashSet<InstId> = vectorizable_insts.iter().copied().collect();
    let mut bridge_insts: HashSet<InstId> = HashSet::new();

    for idiom in compare_idioms {
        bridge_insts.insert(idiom.cmp_inst);
        bridge_insts.insert(idiom.cset_inst);
    }
    for reduction in horizontal_any_reductions {
        bridge_insts.insert(reduction.reducer_inst);
    }
    for reduction in ordered_sub_reductions {
        bridge_insts.insert(reduction.reducer_inst);
        if let Some(inst) = reduction.extension_inst {
            bridge_insts.insert(inst);
        }
        if let Some(inst) = reduction.writeback_inst {
            bridge_insts.insert(inst);
        }
        if let Some(inst) = reduction.accumulator_load_inst {
            bridge_insts.insert(inst);
        }
    }

    for &producer_id in vectorizable_insts {
        let Some(def_id) = def_vreg_id(func.inst(producer_id)) else {
            continue;
        };

        for (idx, inst) in func.insts.iter().enumerate() {
            let consumer_id = InstId(idx as u32);
            if consumer_id == producer_id || vectorizable_set.contains(&consumer_id) {
                continue;
            }
            if bridge_insts.contains(&consumer_id) {
                continue;
            }

            if inst_source_uses_vreg(inst, def_id) {
                return false;
            }
        }
    }

    true
}

fn addri_i32_step(inst: &MachInst) -> Option<(VReg, VReg, i64)> {
    if inst.opcode != AArch64Opcode::AddRI || inst.operands.len() != 3 {
        return None;
    }
    let dst = gpr32_vreg_from_operand(&inst.operands[0])?;
    let src = gpr32_vreg_from_operand(&inst.operands[1])?;
    let MachOperand::Imm(step) = inst.operands[2] else {
        return None;
    };
    Some((dst, src, step))
}

fn movr_vreg_copy(inst: &MachInst) -> Option<(VReg, VReg)> {
    if inst.opcode != AArch64Opcode::MovR || inst.operands.len() != 2 {
        return None;
    }
    let dst = vreg_from_operand(&inst.operands[0])?;
    let src = vreg_from_operand(&inst.operands[1])?;
    Some((dst, src))
}

fn movz_i32_imm(inst: &MachInst) -> Option<(VReg, i64)> {
    let (dst, value) = crate::reaching_const::movz_value(inst)?;
    if dst.class != RegClass::Gpr32 {
        return None;
    }
    Some((dst, i64::try_from(value).ok()?))
}

fn vectorizable_sources_use_vreg(
    func: &MachFunction,
    vectorizable_insts: &[InstId],
    ignored_inst: InstId,
    vreg_id: u32,
) -> bool {
    vectorizable_insts
        .iter()
        .copied()
        .filter(|&inst_id| inst_id != ignored_inst)
        .any(|inst_id| inst_source_uses_vreg(func.inst(inst_id), vreg_id))
}

fn vectorizable_source_alias_from_movr(
    func: &MachFunction,
    lp: &NaturalLoop,
    vectorizable_insts: &[InstId],
    ignored_inst: InstId,
    source_id: u32,
    use_counts: &HashMap<u32, usize>,
) -> Option<VReg> {
    for &block_id in &lp.body {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            let Some((dst, src)) = movr_vreg_copy(inst) else {
                continue;
            };
            if src.id == source_id
                && dst.class == RegClass::Gpr32
                && use_counts.get(&dst.id).copied().unwrap_or(0) == 1
                && vectorizable_sources_use_vreg(func, vectorizable_insts, ignored_inst, dst.id)
            {
                return Some(dst);
            }
        }
    }
    None
}

fn vectorizable_source_from_stack_slot_load(
    func: &MachFunction,
    lp: &NaturalLoop,
    vectorizable_insts: &[InstId],
    ignored_inst: InstId,
    address: VReg,
    use_counts: &HashMap<u32, usize>,
    defs: &HashMap<u32, InstId>,
) -> Option<VReg> {
    for &block_id in &lp.body {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            let Some(dst) = inst.operands.first().and_then(gpr32_vreg_from_operand) else {
                continue;
            };
            if ldr_i32_from_stack_slot(func, inst_id, dst, Some(address), defs).is_some()
                && use_counts.get(&dst.id).copied().unwrap_or(0) == 1
                && vectorizable_sources_use_vreg(func, vectorizable_insts, ignored_inst, dst.id)
            {
                return Some(dst);
            }
        }
    }
    None
}

fn has_i32_stack_slot_writeback(
    func: &MachFunction,
    lp: &NaturalLoop,
    address: VReg,
    value: VReg,
) -> bool {
    lp.body.iter().any(|&block_id| {
        func.block(block_id)
            .insts
            .iter()
            .copied()
            .any(|candidate| str_i32_to_stack_slot(func.inst(candidate), value, address))
    })
}

/// Find the narrow i32 induction shape this slice knows how to vectorize.
///
/// Supported:
///
/// ```text
/// scalar_use ... current
/// next = add current, #1
/// ```
///
/// The current value may come from a stack load/promoted scalar. The step is
/// not itself vectorized; rewrite materializes `current + {0,1,2,3}` and then
/// advances the scalar step by VF. If a vectorized instruction consumes an
/// AddRI induction candidate with any other step, analysis fails instead of
/// silently treating it as ordinary vector arithmetic.
fn find_i32_vector_induction(
    func: &MachFunction,
    lp: &NaturalLoop,
    vectorizable_insts: &[InstId],
    maps: &VecMaps,
) -> Result<Option<VectorInduction>, ()> {
    let mut found = None;
    let defs = &maps.defs;
    let use_counts = &maps.use_counts;

    for &block_id in &lp.body {
        let block_insts = &func.block(block_id).insts;
        for &inst_id in block_insts {
            if let Some((dst, src, step)) = addri_i32_step(func.inst(inst_id)) {
                if step != 1 {
                    return Err(());
                }
                let (scalar_current, scalar_current_alias) =
                    if vectorizable_sources_use_vreg(func, vectorizable_insts, inst_id, src.id) {
                        (src, None)
                    } else if let Some(&load_inst) = defs.get(&src.id)
                        && let Some((load_dst, loaded_from)) = movr_vreg_copy(func.inst(load_inst))
                        && load_dst.id == src.id
                        && loaded_from.class == RegClass::Gpr32
                        && use_counts.get(&src.id).copied().unwrap_or(0) == 1
                        && let Some(alias) = vectorizable_source_alias_from_movr(
                            func,
                            lp,
                            vectorizable_insts,
                            inst_id,
                            loaded_from.id,
                            &use_counts,
                        )
                    {
                        (loaded_from, Some(alias))
                    } else if let Some(&load_inst) = defs.get(&src.id)
                        && let Some(address) =
                            ldr_i32_from_stack_slot(func, load_inst, src, None, defs)
                        && use_counts.get(&src.id).copied().unwrap_or(0) == 1
                        && let Some(scalar_current) = vectorizable_source_from_stack_slot_load(
                            func,
                            lp,
                            vectorizable_insts,
                            inst_id,
                            address,
                            &use_counts,
                            defs,
                        )
                        && has_i32_stack_slot_writeback(func, lp, address, dst)
                    {
                        (scalar_current, None)
                    } else {
                        continue;
                    };
                let has_writeback = lp.body.iter().any(|&block_id| {
                    func.block(block_id).insts.iter().copied().any(|candidate| {
                        movr_vreg_copy(func.inst(candidate)).is_some_and(
                            |(writeback_dst, writeback_src)| {
                                writeback_dst.id == scalar_current.id && writeback_src.id == dst.id
                            },
                        )
                    })
                });
                if scalar_current_alias.is_some() && !has_writeback {
                    continue;
                }
                if found.is_some() {
                    return Err(());
                }
                found = Some(VectorInduction {
                    step_inst: inst_id,
                    scalar_current,
                    scalar_current_alias,
                    scalar_next: dst,
                    sign_extend_inst: None,
                    sign_extended_current: None,
                    step,
                });
                continue;
            }

            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::AddRR || inst.operands.len() != 3 {
                continue;
            }
            let Some(dst) = gpr32_vreg_from_operand(&inst.operands[0]) else {
                continue;
            };
            let Some(lhs) = gpr32_vreg_from_operand(&inst.operands[1]) else {
                continue;
            };
            let Some(rhs) = gpr32_vreg_from_operand(&inst.operands[2]) else {
                continue;
            };

            let lhs_is_one = defs
                .get(&lhs.id)
                .and_then(|&def| movz_i32_imm(func.inst(def)))
                .is_some_and(|(_, imm)| imm == 1);
            let rhs_is_one = defs
                .get(&rhs.id)
                .and_then(|&def| movz_i32_imm(func.inst(def)))
                .is_some_and(|(_, imm)| imm == 1);
            let loaded_current = if lhs_is_one {
                rhs
            } else if rhs_is_one {
                lhs
            } else {
                continue;
            };
            let Some(&load_inst) = defs.get(&loaded_current.id) else {
                continue;
            };
            let (scalar_current, scalar_current_alias) = if let Some((load_dst, scalar_current)) =
                movr_vreg_copy(func.inst(load_inst))
            {
                if load_dst.id != loaded_current.id || scalar_current.class != RegClass::Gpr32 {
                    continue;
                }
                if use_counts.get(&loaded_current.id).copied().unwrap_or(0) != 1 {
                    continue;
                }
                let Some(alias) = vectorizable_source_alias_from_movr(
                    func,
                    lp,
                    vectorizable_insts,
                    inst_id,
                    scalar_current.id,
                    &use_counts,
                ) else {
                    continue;
                };
                let has_writeback = lp.body.iter().any(|&block_id| {
                    func.block(block_id).insts.iter().copied().any(|candidate| {
                        movr_vreg_copy(func.inst(candidate)).is_some_and(
                            |(writeback_dst, writeback_src)| {
                                writeback_dst.id == scalar_current.id && writeback_src.id == dst.id
                            },
                        )
                    })
                });
                if !has_writeback {
                    continue;
                }
                (scalar_current, Some(alias))
            } else if let Some(address) =
                ldr_i32_from_stack_slot(func, load_inst, loaded_current, None, defs)
            {
                if use_counts.get(&loaded_current.id).copied().unwrap_or(0) != 1 {
                    continue;
                }
                let Some(scalar_current) = vectorizable_source_from_stack_slot_load(
                    func,
                    lp,
                    vectorizable_insts,
                    inst_id,
                    address,
                    &use_counts,
                    defs,
                ) else {
                    continue;
                };
                if !has_i32_stack_slot_writeback(func, lp, address, dst) {
                    continue;
                }
                (scalar_current, None)
            } else {
                continue;
            };
            if found.is_some() {
                return Err(());
            }
            found = Some(VectorInduction {
                step_inst: inst_id,
                scalar_current,
                scalar_current_alias,
                scalar_next: dst,
                sign_extend_inst: None,
                sign_extended_current: None,
                step: 1,
            });
        }
    }

    if let Some(induction) = found.as_mut() {
        let mut sign_extend = None;
        let induction_stack_address = defs.get(&induction.scalar_current.id).and_then(|&def| {
            ldr_i32_from_stack_slot(func, def, induction.scalar_current, None, defs)
        });
        for &block_id in &lp.body {
            for &inst_id in &func.block(block_id).insts {
                let inst = func.inst(inst_id);
                if inst.opcode != AArch64Opcode::Sxtw || inst.operands.len() != 2 {
                    continue;
                }
                let Some(dst) = vreg_from_operand(&inst.operands[0]) else {
                    continue;
                };
                let Some(src) = vreg_from_operand(&inst.operands[1]) else {
                    continue;
                };
                let source_matches = src.id == induction.scalar_current.id
                    || induction
                        .scalar_current_alias
                        .is_some_and(|alias| src.id == alias.id)
                    || movr_vreg_copy(
                        defs.get(&src.id)
                            .map(|&def| func.inst(def))
                            .unwrap_or(func.inst(inst_id)),
                    )
                    .is_some_and(|(copy_dst, copy_src)| {
                        copy_dst.id == src.id && copy_src.id == induction.scalar_current.id
                    })
                    || induction_stack_address.is_some_and(|address| {
                        defs.get(&src.id)
                            .and_then(|&def| {
                                ldr_i32_from_stack_slot(func, def, src, Some(address), defs)
                            })
                            .is_some()
                    });
                if dst.class != RegClass::Gpr64
                    || src.class != RegClass::Gpr32
                    || !source_matches
                    || use_counts.get(&src.id).copied().unwrap_or(0) != 1
                    || !vectorizable_sources_use_vreg(func, vectorizable_insts, inst_id, dst.id)
                {
                    continue;
                }
                if sign_extend.is_some() {
                    return Err(());
                }
                sign_extend = Some((inst_id, dst));
            }
        }

        if let Some((inst_id, dst)) = sign_extend {
            induction.sign_extend_inst = Some(inst_id);
            induction.sign_extended_current = Some(dst);
        }
    }

    Ok(found)
}

/// Estimate the trip count of a loop from its structure.
///
/// Looks for a simple counted loop pattern:
/// - Compare against immediate in the latch or header.
/// - The immediate is the trip count.
///
/// Returns None if the trip count cannot be determined statically.
fn estimate_trip_count(func: &MachFunction, lp: &NaturalLoop) -> Option<u32> {
    // Look in the latch block for a compare-immediate that controls the branch.
    estimate_trip_count_in_block(func, lp.latch)
        .or_else(|| estimate_trip_count_in_block(func, lp.header))
}

fn estimate_trip_count_in_block(func: &MachFunction, block_id: BlockId) -> Option<u32> {
    let block = func.block(block_id);
    let mut constants: HashMap<VReg, u64> = HashMap::new();
    for &inst_id in &block.insts {
        let inst = func.inst(inst_id);
        match inst.opcode {
            AArch64Opcode::Movz => {
                if let Some(dst) = inst.operands.first().and_then(vreg_from_operand) {
                    match crate::reaching_const::movz_value(inst) {
                        Some((parsed_dst, value)) if parsed_dst == dst => {
                            constants.insert(dst, value);
                        }
                        _ => {
                            // A malformed or non-proof-covered redefinition must
                            // invalidate any earlier fact for this register.
                            constants.remove(&dst);
                        }
                    }
                }
            }
            AArch64Opcode::Movk => {
                if let Some(dst) = inst.operands.first().and_then(vreg_from_operand) {
                    let next = constants.get(&dst).copied().and_then(|previous| {
                        crate::reaching_const::apply_movk(inst, dst, previous)
                    });
                    match next {
                        Some(value) => {
                            constants.insert(dst, value);
                        }
                        None => {
                            constants.remove(&dst);
                        }
                    }
                }
            }
            AArch64Opcode::CmpRR => {
                for operand in &inst.operands {
                    if let Some(vreg) = vreg_from_operand(operand)
                        && let Some(&val) = constants.get(&vreg)
                        && val > 0
                        && val <= 100_000_000
                    {
                        return Some(val as u32);
                    }
                }
            }
            AArch64Opcode::CmpRI | AArch64Opcode::CMPWri | AArch64Opcode::CMPXri => {
                // The immediate operand is typically the last operand.
                for operand in &inst.operands {
                    if let MachOperand::Imm(val) = operand
                        && *val > 0
                        && *val <= 100_000_000
                    {
                        return Some(*val as u32);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn loop_has_rbit_result_type(func: &MachFunction, insts: &[InstId], reg_class: RegClass) -> bool {
    insts.iter().copied().any(|inst_id| {
        let inst = func.inst(inst_id);
        inst.opcode == AArch64Opcode::Rbit
            && matches!(inst.operands.first(), Some(MachOperand::VReg(vreg)) if vreg.class == reg_class)
    })
}

/// Analyze a loop for vectorization potential.
///
/// Returns a `VectorizationPlan` describing whether and how to vectorize,
/// or None if the loop is fundamentally not vectorizable.
/// Whole-function vreg maps shared across an analysis sweep.
///
/// `build_def_map` and `build_vreg_use_counts` walk `func.insts` — the entire
/// instruction ARENA, which only ever grows because deleted instructions are
/// left inert in it. They were rebuilt TWICE per natural loop
/// (`find_ordered_sub_reductions` and `find_i32_vector_induction` each built
/// their own pair), so a function with many loops paid O(loops x arena). On the
/// `many_fns` shape, where every call site inlines a small loop into `main`,
/// vectorize was the largest pass at 284.6ms and scaled 3.94x for a 2x input.
pub struct VecMaps {
    defs: HashMap<u32, InstId>,
    use_counts: HashMap<u32, usize>,
}

impl VecMaps {
    pub fn build(func: &MachFunction) -> Self {
        Self {
            defs: build_def_map(func),
            use_counts: build_vreg_use_counts(func),
        }
    }
}

/// Analyze one loop, building the shared maps for this call.
///
/// Kept for callers that analyze a single loop against an unmutated function.
/// The pass driver uses [`analyze_loop_with`] so one map pair serves every loop.
pub fn analyze_loop(
    func: &MachFunction,
    lp: &NaturalLoop,
    cost_model: &MultiTargetCostModel,
) -> Option<VectorizationPlan> {
    analyze_loop_with(func, lp, cost_model, &VecMaps::build(func))
}

pub fn analyze_loop_with(
    func: &MachFunction,
    lp: &NaturalLoop,
    cost_model: &MultiTargetCostModel,
    maps: &VecMaps,
) -> Option<VectorizationPlan> {
    // Collect vectorizable instructions and their element types.
    let mut vectorizable_insts: Vec<InstId> = Vec::new();
    let mut element_types: HashMap<VecElementType, u32> = HashMap::new();

    for &block_id in &lp.body {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if is_vectorizable(inst.opcode) {
                vectorizable_insts.push(inst_id);
                if let Some(ety) = infer_element_type(func, inst_id) {
                    *element_types.entry(ety).or_insert(0) += 1;
                }
            }
        }
    }
    let compare_idioms = find_i32_eq_compare_idioms(func, lp);
    for _ in &compare_idioms {
        *element_types.entry(VecElementType::I32).or_insert(0) += 1;
    }

    let horizontal_any_reductions = find_horizontal_any_reductions(func, lp, &compare_idioms);
    if !horizontal_any_reductions.is_empty() {
        let reduction_insts: HashSet<InstId> = horizontal_any_reductions
            .iter()
            .map(|reduction| reduction.reducer_inst)
            .collect();
        vectorizable_insts.retain(|inst_id| !reduction_insts.contains(inst_id));
    }

    let ordered_sub_reductions = find_ordered_sub_reductions(func, lp, &vectorizable_insts, maps);
    if !ordered_sub_reductions.is_empty() {
        let reduction_insts: HashSet<InstId> = ordered_sub_reductions
            .iter()
            .map(|reduction| reduction.reducer_inst)
            .collect();
        for reduction in &ordered_sub_reductions {
            if let Some(ety) = infer_element_type(func, reduction.reducer_inst)
                && let Some(count) = element_types.get_mut(&ety)
            {
                *count = count.saturating_sub(1);
            }
        }
        element_types.retain(|_, count| *count > 0);
        vectorizable_insts.retain(|inst_id| !reduction_insts.contains(inst_id));
    }

    // Must have at least one vectorizable instruction or contextual compare
    // idiom. A bare CmpRR remains non-vectorizable.
    if vectorizable_insts.is_empty() && compare_idioms.is_empty() {
        return None;
    }

    let induction = match find_i32_vector_induction(func, lp, &vectorizable_insts, maps) {
        Ok(induction) => induction,
        Err(()) => return None,
    };
    if let Some(induction) = induction {
        vectorizable_insts.retain(|&inst_id| inst_id != induction.step_inst);
        if let Some(count) = element_types.get_mut(&VecElementType::I32) {
            *count = count.saturating_sub(1);
        }
        element_types.retain(|_, count| *count > 0);
    }

    // Check for cross-iteration dependencies.
    if !is_dependency_free(func, lp, &vectorizable_insts, induction) {
        return None;
    }
    if !vectorized_defs_have_only_vector_consumers(
        func,
        &vectorizable_insts,
        &compare_idioms,
        &horizontal_any_reductions,
        &ordered_sub_reductions,
    ) {
        return None;
    }

    // Determine the primary element type (most common).
    let mixed_width_bitreverse_induction = induction.is_some_and(|induction| {
        induction.sign_extended_current.is_some()
            && loop_has_rbit_result_type(func, &vectorizable_insts, RegClass::Gpr32)
            && loop_has_rbit_result_type(func, &vectorizable_insts, RegClass::Gpr64)
    });
    let element_type = if mixed_width_bitreverse_induction {
        VecElementType::I64
    } else {
        element_types
            .into_iter()
            .max_by_key(|&(_, count)| count)
            .map(|(ty, _)| ty)?
    };

    let arrangement = element_type.neon_arrangement();
    let vf = element_type.lanes();

    // Estimate trip count.
    let trip_count = estimate_trip_count(func, lp);

    // Cost analysis: compare scalar vs NEON.
    let tc = trip_count.unwrap_or(64); // assume 64 iterations if unknown
    let scalar_cost = compute_scalar_cost(
        func,
        &vectorizable_insts,
        &compare_idioms,
        &horizontal_any_reductions,
        &ordered_sub_reductions,
        cost_model,
        tc,
    );
    let neon_cost = compute_neon_cost(
        func,
        &vectorizable_insts,
        &compare_idioms,
        &horizontal_any_reductions,
        &ordered_sub_reductions,
        cost_model,
        element_type,
        arrangement,
        vf,
        tc,
    );

    // The exact mixed revertBits idiom needs a pair of ordered scalar bridges,
    // which the generic cost model overprices relative to eliminating two
    // scalar RBIT recurrences per unrolled step.
    let is_profitable = mixed_width_bitreverse_induction || neon_cost < scalar_cost;

    Some(VectorizationPlan {
        loop_header: lp.header,
        loop_latch: lp.latch,
        trip_count,
        element_type,
        arrangement,
        vf,
        vectorizable_insts,
        compare_idioms,
        horizontal_any_reductions,
        ordered_sub_reductions,
        induction,
        scalar_cost,
        neon_cost,
        is_profitable,
    })
}

/// Compute the scalar cost of executing the vectorizable instructions
/// for `trip_count` iterations.
fn compute_scalar_cost(
    func: &MachFunction,
    insts: &[InstId],
    compare_idioms: &[VectorCompareIdiom],
    horizontal_any_reductions: &[HorizontalAnyReduction],
    ordered_sub_reductions: &[OrderedSubReduction],
    cost_model: &MultiTargetCostModel,
    trip_count: u32,
) -> f64 {
    let scalar_model = cost_model.scalar_model();
    let mut per_iter: f64 = insts
        .iter()
        .map(|&inst_id| {
            let opcode = func.inst(inst_id).opcode;
            use trust_cg_ir::cost_model::CostModel;
            scalar_model.latency(opcode) as f64
        })
        .sum();

    for idiom in compare_idioms {
        use trust_cg_ir::cost_model::CostModel;
        per_iter += scalar_model.latency(func.inst(idiom.cmp_inst).opcode) as f64;
        per_iter += scalar_model.latency(func.inst(idiom.cset_inst).opcode) as f64;
    }
    for reduction in horizontal_any_reductions {
        use trust_cg_ir::cost_model::CostModel;
        per_iter += scalar_model.latency(func.inst(reduction.reducer_inst).opcode) as f64;
    }
    for reduction in ordered_sub_reductions {
        use trust_cg_ir::cost_model::CostModel;
        if let Some(extension_inst) = reduction.extension_inst {
            per_iter += scalar_model.latency(func.inst(extension_inst).opcode) as f64;
        }
        per_iter += scalar_model.latency(func.inst(reduction.reducer_inst).opcode) as f64;
    }

    per_iter * trip_count as f64
}

/// Compute the NEON cost of executing the vectorized loop.
///
/// Includes:
/// - NEON instruction cost per vector iteration (trip_count / vf iterations).
/// - Setup overhead: vector register initialization, domain entry/exit.
/// - Teardown: scalar epilogue for remaining elements.
///
/// # Cost model rationale
///
/// Data transfer between GPR and NEON domains is expensive (~12 cycles
/// per transfer on Apple Silicon), but for a vectorized loop the data
/// stays in NEON registers for the entire loop duration. Transfer cost
/// is therefore one-time at loop entry and exit, NOT per-iteration.
/// This matches real hardware behavior: the loop body operates entirely
/// in the NEON domain.
#[allow(clippy::too_many_arguments)]
fn compute_neon_cost(
    func: &MachFunction,
    insts: &[InstId],
    compare_idioms: &[VectorCompareIdiom],
    horizontal_any_reductions: &[HorizontalAnyReduction],
    ordered_sub_reductions: &[OrderedSubReduction],
    cost_model: &MultiTargetCostModel,
    element_type: VecElementType,
    arrangement: NeonArrangement,
    vf: u32,
    trip_count: u32,
) -> f64 {
    // NEON cost per vector iteration.
    let mut per_vector_iter: f64 = insts
        .iter()
        .map(|&inst_id| {
            let opcode = func.inst(inst_id).opcode;
            if opcode == AArch64Opcode::Rbit
                && let Some((_rev_opcode, rev_op, _byte_arrangement, byte_cost_arrangement)) =
                    vector_bitreverse_byte_arrangement(element_type)
            {
                let (rbit_lat, _rbit_tp) =
                    cost_model.neon_cost(NeonOp::Rbit, byte_cost_arrangement);
                let (rev_lat, _rev_tp) = cost_model.neon_cost(rev_op, byte_cost_arrangement);
                return (rbit_lat + rev_lat) as f64;
            }
            if let Some(neon_op) = scalar_to_neon_op(opcode) {
                let (lat, _tp) = cost_model.neon_cost(neon_op, arrangement);
                lat as f64
            } else {
                // Fallback: estimate same as scalar (shouldn't happen for
                // truly vectorizable insts, but be conservative).
                use trust_cg_ir::cost_model::CostModel;
                cost_model.scalar_model().latency(opcode) as f64
            }
        })
        .sum();

    for _idiom in compare_idioms {
        per_vector_iter += neon_compare_cost(cost_model, arrangement);
    }
    for _reduction in horizontal_any_reductions {
        per_vector_iter += horizontal_any_reduction_cost();
    }
    for reduction in ordered_sub_reductions {
        per_vector_iter += ordered_sub_reduction_cost(reduction.kind);
    }

    let vector_iters = (trip_count / vf) as f64;
    let remainder = trip_count % vf;

    // Scalar epilogue cost for remaining elements.
    let scalar_model = cost_model.scalar_model();
    let mut per_scalar_iter: f64 = insts
        .iter()
        .map(|&inst_id| {
            let opcode = func.inst(inst_id).opcode;
            use trust_cg_ir::cost_model::CostModel;
            scalar_model.latency(opcode) as f64
        })
        .sum();
    for idiom in compare_idioms {
        use trust_cg_ir::cost_model::CostModel;
        per_scalar_iter += scalar_model.latency(func.inst(idiom.cmp_inst).opcode) as f64;
        per_scalar_iter += scalar_model.latency(func.inst(idiom.cset_inst).opcode) as f64;
    }
    for reduction in horizontal_any_reductions {
        use trust_cg_ir::cost_model::CostModel;
        per_scalar_iter += scalar_model.latency(func.inst(reduction.reducer_inst).opcode) as f64;
    }
    for reduction in ordered_sub_reductions {
        use trust_cg_ir::cost_model::CostModel;
        if let Some(extension_inst) = reduction.extension_inst {
            per_scalar_iter += scalar_model.latency(func.inst(extension_inst).opcode) as f64;
        }
        per_scalar_iter += scalar_model.latency(func.inst(reduction.reducer_inst).opcode) as f64;
    }
    let epilogue_cost = per_scalar_iter * remainder as f64;

    // Setup overhead: domain transfer is one-time at loop entry/exit.
    // Includes: loop counter setup, NEON register initialization, and
    // one domain transfer each way for operands that start/end in GPR.
    let transfer = cost_model.transfer_costs();
    let setup_cost = 4.0 // loop counter + branch overhead
        + transfer.memory_to_neon_cycles  // one-time: load initial vectors
        + transfer.neon_to_memory_cycles; // one-time: store final results

    per_vector_iter * vector_iters + epilogue_cost + setup_cost
}

/// Estimated NEON vector-compare cost for a recognized scalar compare idiom.
fn neon_compare_cost(cost_model: &MultiTargetCostModel, _arrangement: NeonArrangement) -> f64 {
    use trust_cg_ir::cost_model::CostModel;
    cost_model.scalar_model().latency(AArch64Opcode::NeonCmeqV) as f64
}

/// Estimated cost for the ay horizontal-any reduction.
///
/// Models `UMAXV.4S`, `FMOV Wd, Sn`, then scalar `ORR` into the existing
/// loop-carried accumulator.
fn horizontal_any_reduction_cost() -> f64 {
    4.0
}

fn ordered_sub_reduction_cost(kind: OrderedSubReductionKind) -> f64 {
    match kind {
        OrderedSubReductionKind::I32ZextToI64 => 20.0,
        OrderedSubReductionKind::I64 => 8.0,
    }
}

fn vector_bitreverse_byte_arrangement(
    element_type: VecElementType,
) -> Option<(AArch64Opcode, NeonOp, i64, NeonArrangement)> {
    vector_bitreverse_byte_arrangement_for_lanes(element_type, element_type.lanes())
}

fn vector_bitreverse_byte_arrangement_for_lanes(
    element_type: VecElementType,
    lanes: u32,
) -> Option<(AArch64Opcode, NeonOp, i64, NeonArrangement)> {
    match element_type {
        VecElementType::I32 if lanes == 2 => Some((
            AArch64Opcode::NeonRev32V,
            NeonOp::Rev32,
            0,
            NeonArrangement::B8,
        )),
        VecElementType::I32 if lanes == 4 => Some((
            AArch64Opcode::NeonRev32V,
            NeonOp::Rev32,
            1,
            NeonArrangement::B16,
        )),
        VecElementType::I64 if lanes == 2 => Some((
            AArch64Opcode::NeonRev64V,
            NeonOp::Rev64,
            1,
            NeonArrangement::B16,
        )),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// IR Rewriting — apply vectorization plan to the MachFunction
// ---------------------------------------------------------------------------

/// Result of applying a vectorization plan to a function.
#[derive(Debug, Clone)]
pub struct VectorizationResult {
    /// Number of instructions rewritten from scalar to NEON.
    pub insts_rewritten: u32,
    /// Number of contextual compare idioms rewritten to vector compares.
    pub compare_idioms_rewritten: u32,
    /// Number of horizontal reductions recognized by analysis.
    pub horizontal_reductions_recognized: u32,
    /// Number of ordered subtract reductions recognized by analysis.
    pub ordered_sub_reductions_recognized: u32,
    /// Number of registers upgraded from GPR to SIMD.
    pub regs_upgraded: u32,
    /// Whether an epilogue block was created for remainder iterations.
    pub has_epilogue: bool,
    /// The new vector trip count (original / vf).
    pub vector_trip_count: Option<u32>,
    /// The remainder iterations handled by scalar epilogue.
    pub remainder: u32,
}

/// Reverse load/add/store accumulation candidate recognized for proof-gating.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReverseAccumulationProofReport {
    pub loop_header: BlockId,
    pub loop_body: BlockId,
    pub source_address_inst: InstId,
    pub dest_address_inst: InstId,
    pub source_load_inst: InstId,
    pub dest_load_inst: InstId,
    pub dest_store_inst: InstId,
    pub consumed_facts: Vec<ProofFact>,
    pub rejection: Option<ReverseAccumulationRejection>,
}

/// First missing or failed proof precondition for reverse accumulation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReverseAccumulationRejection {
    MissingSourceNoAlias,
    MissingDestNoAlias,
    MissingSourceInBounds,
    MissingDestInBounds,
    SameAllocationBase,
    MissingReverseTraversal,
}

impl ReverseAccumulationRejection {
    pub fn missing_fact(self) -> &'static str {
        match self {
            Self::MissingSourceNoAlias | Self::MissingDestNoAlias => "NoAlias",
            Self::MissingSourceInBounds | Self::MissingDestInBounds => "InBounds",
            Self::SameAllocationBase => "NoAlias",
            Self::MissingReverseTraversal => "Monotonic",
        }
    }

    pub fn detail(self) -> &'static str {
        match self {
            Self::MissingSourceNoAlias => "source array address is not proven noalias",
            Self::MissingDestNoAlias => "destination array address is not proven noalias",
            Self::MissingSourceInBounds => "source array address is not proven in-bounds",
            Self::MissingDestInBounds => "destination array address is not proven in-bounds",
            Self::SameAllocationBase => {
                "source and destination addresses derive from the same base"
            }
            Self::MissingReverseTraversal => {
                "loop latch is not the imported-O0 reverse i32 decrement shape"
            }
        }
    }
}

fn push_unique_proof_fact(facts: &mut Vec<ProofFact>, fact: ProofFact) {
    if !facts.contains(&fact) {
        facts.push(fact);
    }
}

fn reverse_vectorization_hash(
    func: &MachFunction,
    report: &ReverseAccumulationProofReport,
) -> u128 {
    let mut hasher = StableHasher::new();
    hasher.write_str("vectorize.reverse-accumulation-proof.v1");
    hasher.write_str(&func.name);
    hasher.write_u32(report.loop_header.0);
    hasher.write_u32(report.loop_body.0);
    hasher.write_u32(report.source_address_inst.0);
    hasher.write_u32(report.dest_address_inst.0);
    hasher.write_u32(report.source_load_inst.0);
    hasher.write_u32(report.dest_load_inst.0);
    hasher.write_u32(report.dest_store_inst.0);
    for fact in &report.consumed_facts {
        hasher.write_str(fact.stable_name());
        match fact {
            ProofFact::Aligned(bytes) | ProofFact::BoundedLoop(bytes) => {
                hasher.write_u64(*bytes);
            }
            _ => hasher.write_u64(0),
        }
    }
    hasher.finish128()
}

fn reverse_vectorization_proof_hash(consumed_facts: &[OptConsumedProofFact]) -> u128 {
    let mut hasher = StableHasher::new();
    hasher.write_str("vectorize.reverse-accumulation-proof-facts.v1");
    for fact in consumed_facts {
        hasher.write_str(fact.stable_name());
        if let Some(payload) = fact.payload() {
            hasher.write_str(&payload);
        } else {
            hasher.write_str("");
        }
    }
    hasher.finish128()
}

fn reverse_vectorization_validation_hash(
    transform: &OptTransformIdentity,
    route: &OptAdmissionRoute,
    source_region_hash: u128,
    target_region_hash: u128,
    proof_hash: u128,
) -> u128 {
    let mut hasher = StableHasher::new();
    hasher.write_str("vectorize.reverse-accumulation-validation.v1");
    hasher.write_str(&transform.name);
    hasher.write_u32(transform.version);
    hasher.write_str(&route.pass);
    hasher.write_str(&route.admission);
    hasher.write_str("flags-refined");
    hasher.write(&source_region_hash.to_le_bytes());
    hasher.write(&target_region_hash.to_le_bytes());
    hasher.write(&proof_hash.to_le_bytes());
    hasher.finish128()
}

fn reverse_vectorization_certificate_id(
    transform: &OptTransformIdentity,
    source_region_hash: u128,
    target_region_hash: u128,
    proof_hash: u128,
    validation_hash: u128,
) -> u128 {
    let mut hasher = StableHasher::new();
    hasher.write_str("vectorize.reverse-accumulation-certificate-id.v1");
    hasher.write_str(&transform.name);
    hasher.write_u32(transform.version);
    hasher.write(&source_region_hash.to_le_bytes());
    hasher.write(&target_region_hash.to_le_bytes());
    hasher.write(&proof_hash.to_le_bytes());
    hasher.write(&validation_hash.to_le_bytes());
    hasher.finish128()
}

fn reverse_vectorization_certificate(
    func: &MachFunction,
    report: &ReverseAccumulationProofReport,
) -> OptCertificate {
    let transform = OptTransformIdentity {
        name: "vectorize.proof-gated.i32-reverse-accumulation-loop".to_string(),
        version: 1,
    };
    let route = OptAdmissionRoute {
        pass: "vectorize".to_string(),
        admission: "proof-facts".to_string(),
    };
    let consumed_facts: Vec<_> = report
        .consumed_facts
        .iter()
        .copied()
        .map(OptConsumedProofFact::ProofFact)
        .collect();
    let source_region_hash = reverse_vectorization_hash(func, report);
    let target_region_hash = source_region_hash;
    let proof_hash = reverse_vectorization_proof_hash(&consumed_facts);
    let validation_hash = reverse_vectorization_validation_hash(
        &transform,
        &route,
        source_region_hash,
        target_region_hash,
        proof_hash,
    );
    let certificate_id = reverse_vectorization_certificate_id(
        &transform,
        source_region_hash,
        target_region_hash,
        proof_hash,
        validation_hash,
    );

    OptCertificate {
        certificate_id,
        transform,
        route,
        annotation: None,
        consumed_facts,
        description:
            "Vectorized i32 reverse accumulation loop under ay/trust_ir memory proof facts"
                .to_string(),
        primary_inst: report.dest_store_inst,
        affected_insts: vec![
            report.source_address_inst,
            report.dest_address_inst,
            report.source_load_inst,
            report.dest_load_inst,
        ],
        kind: OptCertificateKind::FlagsRefined,
        source_region_hash,
        target_region_hash,
        proof_hash,
        validation_hash,
        rejection: None,
    }
}

/// Map a `VecElementType` to the SIMD register class for NEON 128-bit vectors.
///
/// All NEON 128-bit operations use `Fpr128` (V registers / Q registers).
/// The element type determines the arrangement suffix (.4S, .2D, etc.)
/// but the physical register class is always the full 128-bit vector register.
fn simd_reg_class_for_element(_ety: VecElementType) -> RegClass {
    // All 128-bit NEON operations use the Fpr128 (V/Q) register file.
    RegClass::Fpr128
}

/// Integer/vector arrangement encoding expected by the AArch64 encoder:
/// 0=8B, 1=16B, 2=4H, 3=8H, 4=2S, 5=4S, 6=2D.
fn neon_int_arrangement_encoding(arrangement: NeonArrangement) -> i64 {
    match arrangement {
        NeonArrangement::B8 => 0,
        NeonArrangement::B16 => 1,
        NeonArrangement::H4 => 2,
        NeonArrangement::H8 => 3,
        NeonArrangement::S2 => 4,
        NeonArrangement::S4 => 5,
        NeonArrangement::D1 | NeonArrangement::D2 => 6,
    }
}

/// FP arrangement encoding expected by the AArch64 encoder:
/// 0=2S, 1=4S, 2=2D.
fn neon_fp_arrangement_encoding(arrangement: NeonArrangement) -> i64 {
    match arrangement {
        NeonArrangement::D1 | NeonArrangement::D2 => 2,
        NeonArrangement::S2 => 0,
        NeonArrangement::S4 => 1,
        _ => 1,
    }
}

fn arrangement_encoding_for_opcode(opcode: AArch64Opcode, arrangement: NeonArrangement) -> i64 {
    match opcode {
        AArch64Opcode::FaddRR
        | AArch64Opcode::FmulRR
        | AArch64Opcode::NeonFaddV
        | AArch64Opcode::NeonFsubV
        | AArch64Opcode::NeonFmulV
        | AArch64Opcode::NeonFdivV => neon_fp_arrangement_encoding(arrangement),
        _ => neon_int_arrangement_encoding(arrangement),
    }
}

/// Rewrite a scalar opcode to its NEON equivalent AArch64Opcode.
///
/// While `scalar_to_neon_op()` maps to the abstract `NeonOp`, this function
/// maps directly to the `AArch64Opcode` that should be emitted. In a real
/// encoder, NEON instructions would have separate opcode variants. For now,
/// we reuse the same opcode but change the register class to Fpr128 to
/// signal that this is a NEON operation. The NEON operation type is stored
/// as the arrangement encoding in an immediate operand appended to the
/// instruction.
///
/// Returns the NEON opcode and the `NeonOp` for cost model reference.
fn rewrite_opcode_for_neon(opcode: AArch64Opcode) -> Option<(AArch64Opcode, NeonOp)> {
    let neon_op = scalar_to_neon_op(opcode)?;
    // In the current IR, we keep the same opcode but upgrade register classes
    // to Fpr128. The NEON arrangement is encoded as an extra immediate operand.
    // A production backend would have distinct NEON opcodes (e.g., NeonAddV4S).
    Some((opcode, neon_op))
}

fn vectorize_pass_id() -> PassId {
    PassId::new("vectorize")
}

#[derive(Debug, Clone, Copy)]
struct Contains4MaskedBit {
    cmp_inst: InstId,
    cset_inst: InstId,
    lsl_inst: Option<InstId>,
    lane_value: VReg,
    literal: VReg,
}

#[derive(Debug, Clone)]
struct Contains4MaskedIdiom {
    and_inst: InstId,
    zero_inst: InstId,
    orr_insts: Vec<InstId>,
    bits: [Contains4MaskedBit; 4],
    memory_chunk: Option<Contains4MemoryChunk>,
    valid_mask: VReg,
    output: VReg,
}

#[derive(Debug, Clone)]
struct Contains4MemoryChunk {
    load_insts: [InstId; 4],
    base: MachOperand,
    can_use_base_directly: bool,
}

#[derive(Debug, Clone, Copy)]
struct I32InductionStoreLoop {
    preheader: BlockId,
    header: BlockId,
    branch_to_header: InstId,
    index: I32InductionStoreIndex,
    bound: VReg,
    array_base: VReg,
}

#[derive(Debug, Clone, Copy)]
enum I32InductionStoreIndex {
    Register(VReg),
    StackSlot { address: VReg },
}

#[derive(Debug, Clone)]
struct Contains4OrChain {
    zero_inst: InstId,
    orr_insts: Vec<InstId>,
    bit_values: Vec<u32>,
}

fn vreg_from_operand(operand: &MachOperand) -> Option<VReg> {
    match operand {
        MachOperand::VReg(vreg) => Some(*vreg),
        _ => None,
    }
}

fn gpr32_vreg_from_operand(operand: &MachOperand) -> Option<VReg> {
    let vreg = vreg_from_operand(operand)?;
    (vreg.class == RegClass::Gpr32).then_some(vreg)
}

fn gpr64_vreg_from_operand(operand: &MachOperand) -> Option<VReg> {
    let vreg = vreg_from_operand(operand)?;
    (vreg.class == RegClass::Gpr64).then_some(vreg)
}

fn is_gpr64_operand(operand: &MachOperand) -> bool {
    match operand {
        MachOperand::VReg(vreg) => vreg.class == RegClass::Gpr64,
        MachOperand::PReg(preg) => preg_class(*preg) == RegClass::Gpr64,
        _ => false,
    }
}

pub(crate) static VEC_BDM_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static VEC_BDM_CALLS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    if crate::neon_array::boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = build_def_map_inner(func);
        VEC_BDM_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        VEC_BDM_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    build_def_map_inner(func)
}

fn build_def_map_inner(func: &MachFunction) -> HashMap<u32, InstId> {
    let mut defs = HashMap::new();
    for (idx, inst) in func.insts.iter().enumerate() {
        if produces_value(inst.opcode)
            && let Some(MachOperand::VReg(vreg)) = inst.operands.first()
        {
            defs.insert(vreg.id, InstId(idx as u32));
        }
    }
    defs
}

fn build_vreg_use_counts(func: &MachFunction) -> HashMap<u32, usize> {
    let mut uses = HashMap::new();
    for inst in &func.insts {
        let start = if produces_value(inst.opcode) { 1 } else { 0 };
        for operand in inst.operands.iter().skip(start) {
            if let MachOperand::VReg(vreg) = operand {
                *uses.entry(vreg.id).or_insert(0) += 1;
            }
        }
    }
    uses
}

fn block_target_operand(inst: &MachInst, target: BlockId) -> bool {
    inst.operands
        .iter()
        .any(|operand| matches!(operand, MachOperand::Block(block) if *block == target))
}

fn rewrite_block_target(inst: &mut MachInst, old_target: BlockId, new_target: BlockId) -> bool {
    let mut changed = false;
    for operand in &mut inst.operands {
        if matches!(operand, MachOperand::Block(block) if *block == old_target) {
            *operand = MachOperand::Block(new_target);
            changed = true;
        }
    }
    changed
}

fn branch_target(inst: &MachInst) -> Option<BlockId> {
    inst.operands.iter().find_map(|operand| match operand {
        MachOperand::Block(block) => Some(*block),
        _ => None,
    })
}

fn push_unique_inst(ids: &mut Vec<InstId>, id: InstId) {
    if !ids.contains(&id) {
        ids.push(id);
    }
}

fn movr_source_for_dst_in_insts(
    func: &MachFunction,
    insts: &[InstId],
    dst: VReg,
) -> Option<(VReg, InstId)> {
    insts.iter().copied().find_map(|inst_id| {
        let (copy_dst, copy_src) = movr_vreg_copy(func.inst(inst_id))?;
        (copy_dst == dst && copy_src.class == dst.class).then_some((copy_src, inst_id))
    })
}

fn movr_source_for_dst_in_block(
    func: &MachFunction,
    block: BlockId,
    dst: VReg,
) -> Option<(VReg, InstId)> {
    movr_source_for_dst_in_insts(func, &func.block(block).insts, dst)
}

fn loop_index_view_in_block(
    func: &MachFunction,
    block: BlockId,
    candidate: VReg,
    loop_index: VReg,
) -> Option<Option<InstId>> {
    if candidate == loop_index {
        return Some(None);
    }
    let (source, inst_id) = movr_source_for_dst_in_block(func, block, candidate)?;
    (source == loop_index).then_some(Some(inst_id))
}

fn stack_slot_address_vreg(
    func: &MachFunction,
    address: VReg,
    defs: &HashMap<u32, InstId>,
) -> bool {
    let Some(&def_id) = defs.get(&address.id) else {
        return false;
    };
    let def = func.inst(def_id);
    def.opcode == AArch64Opcode::AddPCRel
        && def.operands.first() == Some(&MachOperand::VReg(address))
        && matches!(def.operands.get(2), Some(MachOperand::StackSlot(_)))
}

fn ldr_i32_from_stack_slot(
    func: &MachFunction,
    inst_id: InstId,
    expected_dst: VReg,
    expected_address: Option<VReg>,
    defs: &HashMap<u32, InstId>,
) -> Option<VReg> {
    let inst = func.inst(inst_id);
    if inst.opcode != AArch64Opcode::LdrRI
        || !(2..=3).contains(&inst.operands.len())
        || inst.operands[0] != MachOperand::VReg(expected_dst)
        || expected_dst.class != RegClass::Gpr32
    {
        return None;
    }
    let address = gpr64_vreg_from_operand(&inst.operands[1])?;
    if expected_address.is_some_and(|expected| expected != address) {
        return None;
    }
    if matches!(inst.operands.get(2), Some(operand) if operand != &MachOperand::Imm(0)) {
        return None;
    }
    stack_slot_address_vreg(func, address, defs).then_some(address)
}

fn ldr_gpr64_from_stack_slot(
    func: &MachFunction,
    inst_id: InstId,
    expected_dst: VReg,
    expected_address: Option<VReg>,
    defs: &HashMap<u32, InstId>,
) -> Option<VReg> {
    let inst = func.inst(inst_id);
    if inst.opcode != AArch64Opcode::LdrRI
        || !(2..=3).contains(&inst.operands.len())
        || inst.operands[0] != MachOperand::VReg(expected_dst)
        || expected_dst.class != RegClass::Gpr64
    {
        return None;
    }
    let address = gpr64_vreg_from_operand(&inst.operands[1])?;
    if expected_address.is_some_and(|expected| expected != address) {
        return None;
    }
    if matches!(inst.operands.get(2), Some(operand) if operand != &MachOperand::Imm(0)) {
        return None;
    }
    stack_slot_address_vreg(func, address, defs).then_some(address)
}

fn ldr_i32_from_stack_slot_in_insts(
    func: &MachFunction,
    insts: &[InstId],
    expected_dst: VReg,
    expected_address: Option<VReg>,
    defs: &HashMap<u32, InstId>,
) -> Option<(VReg, InstId)> {
    insts.iter().copied().find_map(|inst_id| {
        ldr_i32_from_stack_slot(func, inst_id, expected_dst, expected_address, defs)
            .map(|address| (address, inst_id))
    })
}

fn str_i32_to_stack_slot(inst: &MachInst, value: VReg, address: VReg) -> bool {
    inst.opcode == AArch64Opcode::StrRI
        && inst.operands
            == [
                MachOperand::VReg(value),
                MachOperand::VReg(address),
                MachOperand::Imm(0),
            ]
}

fn str_gpr64_to_stack_slot_address(
    func: &MachFunction,
    inst_id: InstId,
    value: VReg,
    defs: &HashMap<u32, InstId>,
) -> Option<VReg> {
    let inst = func.inst(inst_id);
    if inst.opcode != AArch64Opcode::StrRI
        || inst.operands.len() != 3
        || inst.operands[0] != MachOperand::VReg(value)
        || value.class != RegClass::Gpr64
        || inst.operands[2] != MachOperand::Imm(0)
    {
        return None;
    }
    let address = gpr64_vreg_from_operand(&inst.operands[1])?;
    stack_slot_address_vreg(func, address, defs).then_some(address)
}

fn insts_have_memory_write_or_call(func: &MachFunction, insts: &[InstId]) -> bool {
    insts.iter().copied().any(|inst_id| {
        let inst = func.inst(inst_id);
        opcode_effect(inst.opcode).writes_memory()
            || inst.flags.contains(trust_cg_ir::InstFlags::WRITES_MEMORY)
            || inst.flags.contains(trust_cg_ir::InstFlags::IS_CALL)
    })
}

fn loop_index_view_for_store_index(
    func: &MachFunction,
    block: BlockId,
    candidate: VReg,
    index: I32InductionStoreIndex,
    defs: &HashMap<u32, InstId>,
) -> Option<Option<InstId>> {
    match index {
        I32InductionStoreIndex::Register(loop_index) => {
            loop_index_view_in_block(func, block, candidate, loop_index)
        }
        I32InductionStoreIndex::StackSlot { address } => {
            let (_address, inst_id) = ldr_i32_from_stack_slot_in_insts(
                func,
                &func.block(block).insts,
                candidate,
                Some(address),
                defs,
            )?;
            Some(Some(inst_id))
        }
    }
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&succ| succ != to);
    func.block_mut(to).preds.retain(|&pred| pred != from);
}

fn insert_new_blocks_before(func: &mut MachFunction, before: BlockId, new_blocks: &[BlockId]) {
    let mut reordered = Vec::with_capacity(func.block_order.len());
    for &block in &func.block_order {
        if block == before {
            reordered.extend(new_blocks.iter().copied());
        }
        if !new_blocks.contains(&block) {
            reordered.push(block);
        }
    }
    func.block_order = reordered;
}

fn as_block_branch(inst: &MachInst, opcode: AArch64Opcode) -> Option<BlockId> {
    (inst.opcode == opcode)
        .then(|| branch_target(inst))
        .flatten()
}

fn match_i32_induction_store_header(
    func: &MachFunction,
    block: BlockId,
    defs: &HashMap<u32, InstId>,
) -> Option<(I32InductionStoreIndex, VReg, BlockId, BlockId)> {
    const AARCH64_COND_NE: i64 = 1;
    const AARCH64_COND_LT: i64 = 11;

    let insts: Vec<InstId> = func
        .block(block)
        .insts
        .iter()
        .copied()
        .filter(|&inst_id| func.inst(inst_id).opcode != AArch64Opcode::Nop)
        .collect();
    let cmp_pos = insts
        .iter()
        .position(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::CmpRR)?;
    let cmp_id = insts[cmp_pos];
    let cmp = func.inst(cmp_id);
    if cmp.operands.len() != 2 {
        return None;
    }
    let cmp_index = gpr32_vreg_from_operand(&cmp.operands[0])?;
    let cmp_bound = gpr32_vreg_from_operand(&cmp.operands[1])?;
    let stack_index =
        ldr_i32_from_stack_slot_in_insts(func, &insts[..cmp_pos], cmp_index, None, defs);
    if insts[..cmp_pos].iter().any(|&inst_id| {
        func.inst(inst_id).opcode != AArch64Opcode::MovR
            && stack_index.is_none_or(|(_, load_inst)| load_inst != inst_id)
    }) {
        return None;
    }
    let index = if let Some((address, _load_inst)) = stack_index {
        I32InductionStoreIndex::StackSlot { address }
    } else {
        I32InductionStoreIndex::Register(
            movr_source_for_dst_in_insts(func, &insts[..cmp_pos], cmp_index)
                .map(|(source, _)| source)
                .unwrap_or(cmp_index),
        )
    };
    let bound = movr_source_for_dst_in_insts(func, &insts[..cmp_pos], cmp_bound)
        .map(|(source, _)| source)
        .unwrap_or(cmp_bound);

    let tail = &insts[cmp_pos + 1..];
    if tail.len() == 2 {
        let bcond = func.inst(tail[0]);
        let branch = func.inst(tail[1]);
        if bcond.opcode != AArch64Opcode::BCond
            || bcond.operands.len() != 2
            || bcond.operands[0] != MachOperand::Imm(AARCH64_COND_LT)
            || branch.opcode != AArch64Opcode::B
        {
            return None;
        }
        let body = branch_target(bcond)?;
        let exit = branch_target(branch)?;
        return Some((index, bound, body, exit));
    }

    if tail.len() != 4 {
        return None;
    }
    let cset = func.inst(tail[0]);
    let test = func.inst(tail[1]);
    let bcond = func.inst(tail[2]);
    let branch = func.inst(tail[3]);
    if cset.opcode != AArch64Opcode::CSet
        || cset.operands.len() != 2
        || cset.operands[1] != MachOperand::Imm(AARCH64_COND_LT)
        || test.opcode != AArch64Opcode::CmpRI
        || test.operands.len() != 2
        || test.operands[1] != MachOperand::Imm(0)
        || bcond.opcode != AArch64Opcode::BCond
        || bcond.operands.len() != 2
        || bcond.operands[0] != MachOperand::Imm(AARCH64_COND_NE)
        || branch.opcode != AArch64Opcode::B
    {
        return None;
    }
    let bool_value = vreg_from_operand(&cset.operands[0])?;
    if test.operands[0] != MachOperand::VReg(bool_value) {
        return None;
    }
    let body = branch_target(bcond)?;
    let exit = branch_target(branch)?;
    Some((index, bound, body, exit))
}

fn find_branch_to_header(
    func: &MachFunction,
    preheader: BlockId,
    header: BlockId,
) -> Option<InstId> {
    func.block(preheader)
        .insts
        .iter()
        .copied()
        .rev()
        .find(|&inst_id| {
            let inst = func.inst(inst_id);
            matches!(inst.opcode, AArch64Opcode::B | AArch64Opcode::BCond)
                && block_target_operand(inst, header)
        })
}

type I32InductionStoreBody = (
    Option<VReg>,
    Option<InstId>,
    VReg,
    VReg,
    InstId,
    InstId,
    InstId,
    InstId,
    Vec<InstId>,
);

fn match_i32_induction_store_body(
    func: &MachFunction,
    body: BlockId,
    index: I32InductionStoreIndex,
    defs: &HashMap<u32, InstId>,
) -> Option<I32InductionStoreBody> {
    let insts = &func.block(body).insts;
    let mut extra_allowed = Vec::new();

    let mut store_value_inst = None;
    let mut store_value = None;
    let mut one: Option<Option<VReg>> = None;
    let mut body_index = None;
    for &inst_id in insts {
        let inst = func.inst(inst_id);
        let matched = if let Some((dst, src, 1)) = addri_i32_step(inst) {
            loop_index_view_for_store_index(func, body, src, index, defs)
                .map(|index_copy| (dst, src, index_copy, None))
        } else if inst.opcode == AArch64Opcode::AddRR && inst.operands.len() == 3 {
            let dst = gpr32_vreg_from_operand(&inst.operands[0])?;
            let lhs = gpr32_vreg_from_operand(&inst.operands[1])?;
            let rhs = gpr32_vreg_from_operand(&inst.operands[2])?;
            let rhs_is_one = defs
                .get(&rhs.id)
                .and_then(|&def| movz_i32_imm(func.inst(def)).map(|(_, imm)| (def, imm)))
                .is_some_and(|(_, imm)| imm == 1);
            let lhs_is_one = defs
                .get(&lhs.id)
                .and_then(|&def| movz_i32_imm(func.inst(def)).map(|(_, imm)| (def, imm)))
                .is_some_and(|(_, imm)| imm == 1);
            let lhs_index_copy = loop_index_view_for_store_index(func, body, lhs, index, defs);
            let rhs_index_copy = loop_index_view_for_store_index(func, body, rhs, index, defs);
            if let Some(index_copy) = lhs_index_copy
                && rhs_is_one
            {
                Some((dst, lhs, index_copy, Some(rhs)))
            } else if let Some(index_copy) = rhs_index_copy
                && lhs_is_one
            {
                Some((dst, rhs, index_copy, Some(lhs)))
            } else {
                None
            }
        } else {
            None
        };
        let Some((matched_value, matched_index, index_copy, matched_one)) = matched else {
            continue;
        };
        store_value_inst = Some(inst_id);
        store_value = Some(matched_value);
        body_index = Some(matched_index);
        one = Some(matched_one);
        if let Some(index_copy) = index_copy {
            push_unique_inst(&mut extra_allowed, index_copy);
        }
        break;
    }
    let store_value_inst = store_value_inst?;
    let store_value = store_value?;
    let one = one?;
    let body_index = body_index?;
    let one_inst =
        one.and_then(|one| defs.get(&one.id).copied().filter(|def| insts.contains(def)))
            .or_else(|| {
                insts.iter().copied().find(|&inst_id| {
                    movz_i32_imm(func.inst(inst_id)).is_some_and(|(_, imm)| imm == 1)
                })
            });

    let mut sign_extend_inst = None;
    let mut wide_index = None;
    for &inst_id in insts {
        let inst = func.inst(inst_id);
        if inst.opcode == AArch64Opcode::Sxtw
            && inst.operands.len() == 2
            && inst.operands[1] == MachOperand::VReg(body_index)
            && let Some(dst) = vreg_from_operand(&inst.operands[0])
            && dst.class == RegClass::Gpr64
        {
            sign_extend_inst = Some(inst_id);
            wide_index = Some(dst);
            break;
        }
    }
    let sign_extend_inst = sign_extend_inst?;
    let wide_index = wide_index?;

    let mut address_inst = None;
    let mut address = None;
    let mut element_size = None;
    let mut array_base = None;
    for &inst_id in insts {
        let inst = func.inst(inst_id);
        if inst.opcode != AArch64Opcode::Madd || inst.operands.len() != 4 {
            continue;
        }
        let dst = vreg_from_operand(&inst.operands[0])?;
        let lhs = vreg_from_operand(&inst.operands[1])?;
        let rhs = vreg_from_operand(&inst.operands[2])?;
        let addend = vreg_from_operand(&inst.operands[3])?;
        if dst.class != RegClass::Gpr64
            || lhs.class != RegClass::Gpr64
            || rhs.class != RegClass::Gpr64
            || addend.class != RegClass::Gpr64
            || lhs.id != wide_index.id
        {
            continue;
        }
        let stride_def = defs.get(&rhs.id).copied();
        let stride_is_i32 = stride_def.is_some_and(|def| {
            let def_inst = func.inst(def);
            crate::reaching_const::movz_value(def_inst)
                .is_some_and(|(dst, value)| dst == rhs && value == 4)
        });
        if !stride_is_i32 {
            continue;
        }
        if let Some(stride_def) = stride_def.filter(|def| insts.contains(def)) {
            push_unique_inst(&mut extra_allowed, stride_def);
        }
        let (canonical_base, base_copy) = movr_source_for_dst_in_block(func, body, addend)
            .filter(|(source, _)| source.class == RegClass::Gpr64)
            .unwrap_or((addend, inst_id));
        if base_copy != inst_id {
            push_unique_inst(&mut extra_allowed, base_copy);
        }
        address_inst = Some(inst_id);
        address = Some(dst);
        element_size = Some(rhs);
        array_base = Some(canonical_base);
        break;
    }
    let address_inst = address_inst?;
    let address = address?;
    let element_size = element_size?;
    let array_base = array_base?;

    let store_inst = insts.iter().copied().find(|&inst_id| {
        let inst = func.inst(inst_id);
        inst.opcode == AArch64Opcode::StrRI
            && inst.operands
                == [
                    MachOperand::VReg(store_value),
                    MachOperand::VReg(address),
                    MachOperand::Imm(0),
                ]
    })?;

    Some((
        one,
        one_inst,
        array_base,
        element_size,
        store_inst,
        store_value_inst,
        sign_extend_inst,
        address_inst,
        extra_allowed,
    ))
}

fn match_i32_induction_store_latch(
    func: &MachFunction,
    latch: BlockId,
    header: BlockId,
    index: I32InductionStoreIndex,
    one: Option<VReg>,
    defs: &HashMap<u32, InstId>,
) -> Option<(InstId, InstId)> {
    let insts: Vec<InstId> = func
        .block(latch)
        .insts
        .iter()
        .copied()
        .filter(|&inst_id| func.inst(inst_id).opcode != AArch64Opcode::Nop)
        .collect();
    let (step_index, step_id, writeback_id, branch_id) = match index {
        I32InductionStoreIndex::Register(index) => {
            if insts.len() != 3 && insts.len() != 4 {
                return None;
            }
            if insts.len() == 4 {
                let (copy_dst, copy_src) = movr_vreg_copy(func.inst(insts[0]))?;
                if copy_src != index || copy_dst.class != index.class {
                    return None;
                }
                (copy_dst, insts[1], insts[2], insts[3])
            } else {
                (index, insts[0], insts[1], insts[2])
            }
        }
        I32InductionStoreIndex::StackSlot { address } => {
            if insts.len() != 4 {
                return None;
            }
            let step_index = gpr32_vreg_from_operand(func.inst(insts[0]).operands.first()?)?;
            ldr_i32_from_stack_slot(func, insts[0], step_index, Some(address), defs)?;
            (step_index, insts[1], insts[2], insts[3])
        }
    };
    let step = func.inst(step_id);
    let writeback = func.inst(writeback_id);
    let branch = func.inst(branch_id);
    let next = if let Some((next, src, 1)) = addri_i32_step(step) {
        (src.id == step_index.id).then_some(next)?
    } else {
        let one = one?;
        if step.opcode != AArch64Opcode::AddRR || step.operands.len() != 3 {
            return None;
        }
        let next = gpr32_vreg_from_operand(&step.operands[0])?;
        let lhs = gpr32_vreg_from_operand(&step.operands[1])?;
        let rhs = gpr32_vreg_from_operand(&step.operands[2])?;
        if !((lhs.id == step_index.id && rhs.id == one.id)
            || (lhs.id == one.id && rhs.id == step_index.id))
        {
            return None;
        }
        next
    };
    match index {
        I32InductionStoreIndex::Register(index) => {
            let (dst, src) = movr_vreg_copy(writeback)?;
            if dst.id != index.id || src.id != next.id {
                return None;
            }
        }
        I32InductionStoreIndex::StackSlot { address } => {
            if !str_i32_to_stack_slot(writeback, next, address) {
                return None;
            }
        }
    }
    if as_block_branch(branch, AArch64Opcode::B) != Some(header) {
        return None;
    }
    Some((step_id, writeback_id))
}

fn body_contains_only_i32_induction_store_idiom(
    func: &MachFunction,
    body: BlockId,
    latch: BlockId,
    allowed: &[InstId],
) -> bool {
    func.block(body).insts.iter().copied().all(|inst_id| {
        let inst = func.inst(inst_id);
        inst.opcode == AArch64Opcode::Nop
            || allowed.contains(&inst_id)
            || (inst.opcode == AArch64Opcode::B && branch_target(inst) == Some(latch))
    })
}

fn match_i32_induction_store_loop(
    func: &MachFunction,
    lp: &NaturalLoop,
    defs: &HashMap<u32, InstId>,
) -> Option<I32InductionStoreLoop> {
    let header = lp.header;
    let latch = lp.latch;
    let preheader = func
        .block(header)
        .preds
        .iter()
        .copied()
        .find(|&pred| pred != latch)?;
    let branch_to_header = find_branch_to_header(func, preheader, header)?;

    let (index, bound, scalar_body, _exit) = match_i32_induction_store_header(func, header, defs)?;
    if !func.block(scalar_body).succs.contains(&latch) {
        return None;
    }

    let (
        one,
        one_inst,
        array_base,
        _element_size,
        store_inst,
        store_value_inst,
        sign_extend_inst,
        address_inst,
        extra_allowed,
    ) = match_i32_induction_store_body(func, scalar_body, index, defs)?;
    let (_latch_step_inst, _latch_writeback_inst) =
        match_i32_induction_store_latch(func, latch, header, index, one, defs)?;
    let mut allowed_body_insts = vec![store_inst, store_value_inst, sign_extend_inst, address_inst];
    allowed_body_insts.extend(extra_allowed);
    if let Some(one_inst) = one_inst {
        allowed_body_insts.push(one_inst);
    }
    if !body_contains_only_i32_induction_store_idiom(func, scalar_body, latch, &allowed_body_insts)
    {
        return None;
    }

    Some(I32InductionStoreLoop {
        preheader,
        header,
        branch_to_header,
        index,
        bound,
        array_base,
    })
}

fn push_inst_to_block(
    func: &mut MachFunction,
    block: BlockId,
    inst: MachInst,
    created: &mut Vec<InstId>,
) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
    created.push(id);
    id
}

fn rewrite_i32_induction_store_loop(
    func: &mut MachFunction,
    idiom: I32InductionStoreLoop,
    provenance: Option<&mut ProvenanceMap>,
) -> Option<VectorizationResult> {
    const ELEMENT_SIZE_S: i64 = 4;
    const S4_ARRANGEMENT: i64 = 5;
    const AARCH64_COND_LT: i64 = 11;

    let vector_header = func.create_block();
    let vector_body = func.create_block();
    let vector_latch = func.create_block();
    insert_new_blocks_before(
        func,
        idiom.header,
        &[vector_header, vector_body, vector_latch],
    );

    if !rewrite_block_target(
        func.inst_mut(idiom.branch_to_header),
        idiom.header,
        vector_header,
    ) {
        return None;
    }

    remove_cfg_edge(func, idiom.preheader, idiom.header);
    func.add_edge(idiom.preheader, vector_header);
    func.add_edge(vector_header, vector_body);
    func.add_edge(vector_header, idiom.header);
    func.add_edge(vector_body, vector_latch);
    func.add_edge(vector_latch, vector_header);

    let mut created = Vec::new();
    let vector_index = match idiom.index {
        I32InductionStoreIndex::Register(index) => index,
        I32InductionStoreIndex::StackSlot { address } => {
            let index = alloc_fresh_vreg(func, RegClass::Gpr32);
            push_inst_to_block(
                func,
                vector_header,
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::VReg(index),
                        MachOperand::VReg(address),
                        MachOperand::Imm(0),
                    ],
                ),
                &mut created,
            );
            index
        }
    };

    let vector_base = alloc_fresh_vreg(func, RegClass::Gpr64);
    let base_copy = func.push_inst(MachInst::new(
        AArch64Opcode::MovR,
        vec![
            MachOperand::VReg(vector_base),
            MachOperand::VReg(idiom.array_base),
        ],
    ));
    if !insert_before_inst(func, idiom.branch_to_header, &[base_copy]) {
        return None;
    }
    created.push(base_copy);

    let guard = alloc_fresh_vreg(func, RegClass::Gpr32);
    push_inst_to_block(
        func,
        vector_header,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(guard),
                MachOperand::VReg(vector_index),
                MachOperand::Imm(3),
            ],
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_header,
        MachInst::new(
            AArch64Opcode::CmpRR,
            vec![MachOperand::VReg(guard), MachOperand::VReg(idiom.bound)],
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_header,
        MachInst::new(
            AArch64Opcode::BCond,
            vec![
                MachOperand::Imm(AARCH64_COND_LT),
                MachOperand::Block(vector_body),
            ],
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_header,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(idiom.header)]),
        &mut created,
    );

    let lane0 = alloc_fresh_vreg(func, RegClass::Gpr32);
    let lanes = alloc_fresh_vreg(func, RegClass::Fpr128);
    push_inst_to_block(
        func,
        vector_body,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(lane0),
                MachOperand::VReg(vector_index),
                MachOperand::Imm(1),
            ],
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_body,
        MachInst::new(
            AArch64Opcode::NeonDupGen,
            vec![
                MachOperand::VReg(lanes),
                MachOperand::VReg(lane0),
                MachOperand::Imm(ELEMENT_SIZE_S),
            ],
        ),
        &mut created,
    );
    for lane in 1..4 {
        let scalar_lane = alloc_fresh_vreg(func, RegClass::Gpr32);
        push_inst_to_block(
            func,
            vector_body,
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::VReg(scalar_lane),
                    MachOperand::VReg(lane0),
                    MachOperand::Imm(lane as i64),
                ],
            ),
            &mut created,
        );
        push_inst_to_block(
            func,
            vector_body,
            MachInst::new(
                AArch64Opcode::NeonInsGen,
                vec![
                    MachOperand::VReg(lanes),
                    MachOperand::VReg(scalar_lane),
                    MachOperand::Imm(lane as i64),
                    MachOperand::Imm(ELEMENT_SIZE_S),
                ],
            ),
            &mut created,
        );
    }

    push_inst_to_block(
        func,
        vector_body,
        MachInst::new(
            AArch64Opcode::NeonSt1Post,
            vec![
                MachOperand::VReg(lanes),
                MachOperand::VReg(vector_base),
                MachOperand::Imm(S4_ARRANGEMENT),
            ],
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_body,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(vector_latch)]),
        &mut created,
    );

    let (advance_operands, stack_writeback) = match idiom.index {
        I32InductionStoreIndex::Register(index) => (
            vec![
                MachOperand::VReg(index),
                MachOperand::VReg(index),
                MachOperand::Imm(4),
            ],
            None,
        ),
        I32InductionStoreIndex::StackSlot { address } => {
            let next_index = alloc_fresh_vreg(func, RegClass::Gpr32);
            (
                vec![
                    MachOperand::VReg(next_index),
                    MachOperand::VReg(vector_index),
                    MachOperand::Imm(4),
                ],
                Some((next_index, address)),
            )
        }
    };
    push_inst_to_block(
        func,
        vector_latch,
        MachInst::new(AArch64Opcode::AddRI, advance_operands),
        &mut created,
    );
    if let Some((next_index, address)) = stack_writeback {
        push_inst_to_block(
            func,
            vector_latch,
            MachInst::new(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::VReg(next_index),
                    MachOperand::VReg(address),
                    MachOperand::Imm(0),
                ],
            ),
            &mut created,
        );
    }
    push_inst_to_block(
        func,
        vector_latch,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(vector_header)]),
        &mut created,
    );

    if let Some(provenance) = provenance {
        let pass = vectorize_pass_id();
        provenance.record_in_place_transform(idiom.branch_to_header, pass.clone());
        for inst_id in created {
            provenance.record_creation(inst_id, pass.clone(), "vectorize i32 induction store loop");
        }
    }

    Some(VectorizationResult {
        insts_rewritten: 1,
        compare_idioms_rewritten: 0,
        horizontal_reductions_recognized: 0,
        ordered_sub_reductions_recognized: 0,
        regs_upgraded: 1,
        has_epilogue: true,
        vector_trip_count: None,
        remainder: 0,
    })
}

fn rewrite_i32_induction_store_loops(
    func: &mut MachFunction,
    loop_analysis: &LoopAnalysis,
    mut provenance: Option<&mut ProvenanceMap>,
) -> Vec<VectorizationResult> {
    let mut results = Vec::new();
    let loops: Vec<_> = loop_analysis.all_loops().cloned().collect();
    // The scan is read-only, so one map serves every match attempt. A rewrite
    // can grow the arena even when it fails partway, so the map is rebuilt
    // after any rewrite call that does not return.
    let mut defs = build_def_map(func);
    for lp in loops {
        let Some(idiom) = match_i32_induction_store_loop(func, &lp, &defs) else {
            continue;
        };
        if let Some(result) =
            rewrite_i32_induction_store_loop(func, idiom, provenance.as_deref_mut())
        {
            results.push(result);
            return results;
        }
        defs = build_def_map(func);
    }
    results
}

#[derive(Debug, Clone, Copy)]
struct ReverseAccumulationCandidate {
    loop_header: BlockId,
    loop_body: BlockId,
    source_address_inst: InstId,
    dest_address_inst: InstId,
    source_load_inst: InstId,
    dest_load_inst: InstId,
    add_inst: InstId,
    dest_store_inst: InstId,
    sign_extend_inst: InstId,
    narrow_index: VReg,
    element_size: VReg,
    source_base: VReg,
    dest_base: VReg,
}

#[derive(Debug, Clone)]
struct ReverseAccumulationLoop {
    preheader: BlockId,
    branch_to_header: InstId,
    index: ReverseAccumulationIndex,
    candidate: ReverseAccumulationCandidate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReverseAccumulationIndex {
    Register(VReg),
    StackSlot { address: VReg },
}

fn proof_facts_contain(facts: &[ProofFact], needle: ProofFact) -> bool {
    facts.contains(&needle)
}

fn any_inst_has_proof_fact(
    proof_facts: &HashMap<InstId, Vec<ProofFact>>,
    insts: &[InstId],
    fact: ProofFact,
) -> bool {
    insts.iter().any(|inst_id| {
        proof_facts
            .get(inst_id)
            .is_some_and(|facts| proof_facts_contain(facts, fact))
    })
}

fn direct_calloc_call(inst: &MachInst) -> bool {
    matches!(inst.opcode, AArch64Opcode::Bl | AArch64Opcode::BL)
        && inst.operands.iter().any(|operand| {
            matches!(
                operand,
                MachOperand::Symbol(symbol) if matches!(symbol.as_str(), "calloc" | "_calloc")
            )
        })
}

fn block_inst_position(func: &MachFunction, target: InstId) -> Option<(BlockId, usize)> {
    for (idx, block) in func.blocks.iter().enumerate() {
        if let Some(pos) = block.insts.iter().position(|&inst_id| inst_id == target) {
            return Some((BlockId(idx as u32), pos));
        }
    }
    None
}

fn vreg_copy_source_for_dst(inst: &MachInst, expected_dst: VReg) -> Option<VReg> {
    if !matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy) || inst.operands.len() != 2
    {
        return None;
    }
    let dst = vreg_from_operand(&inst.operands[0])?;
    let src = vreg_from_operand(&inst.operands[1])?;
    (dst == expected_dst && src.class == expected_dst.class).then_some(src)
}

fn x0_call_result_copy(inst: &MachInst, expected_dst: VReg) -> bool {
    inst.opcode == AArch64Opcode::Copy
        && inst.operands
            == [
                MachOperand::VReg(expected_dst),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::X0),
            ]
}

fn nearest_calloc_before_result_copy(func: &MachFunction, copy_inst: InstId) -> Option<InstId> {
    let (block, pos) = block_inst_position(func, copy_inst)?;
    for &inst_id in func.block(block).insts[..pos].iter().rev() {
        let inst = func.inst(inst_id);
        if direct_calloc_call(inst) {
            return Some(inst_id);
        }
        if matches!(
            inst.opcode,
            AArch64Opcode::Bl | AArch64Opcode::BL | AArch64Opcode::Blr | AArch64Opcode::BLR
        ) {
            return None;
        }
    }
    None
}

fn calloc_return_origin_for_vreg(
    func: &MachFunction,
    base: VReg,
    defs: &HashMap<u32, InstId>,
) -> Option<InstId> {
    let mut current = base;
    let mut seen = HashSet::new();
    for _ in 0..16 {
        if !seen.insert(current.id) {
            return None;
        }
        let def = *defs.get(&current.id)?;
        let inst = func.inst(def);
        if x0_call_result_copy(inst, current) {
            return nearest_calloc_before_result_copy(func, def);
        }
        if let Some(source) = vreg_copy_source_for_dst(inst, current) {
            current = source;
            continue;
        }
        return None;
    }
    None
}

fn match_reverse_accumulation_madd_address(
    func: &MachFunction,
    address_inst: InstId,
) -> Option<(VReg, VReg, VReg)> {
    let inst = func.inst(address_inst);
    match inst.opcode {
        AArch64Opcode::Madd => Some((
            gpr64_vreg_from_operand(inst.operands.get(1)?)?,
            gpr64_vreg_from_operand(inst.operands.get(2)?)?,
            gpr64_vreg_from_operand(inst.operands.get(3)?)?,
        )),
        _ => None,
    }
}

fn movn_i32_minus_one(inst: &MachInst) -> Option<VReg> {
    let (dst, value) = crate::reaching_const::movn_value(inst)?;
    if dst.class != RegClass::Gpr32 || value != u32::MAX as u64 {
        return None;
    }
    Some(dst)
}

fn vreg_is_i32_zero(func: &MachFunction, defs: &HashMap<u32, InstId>, vreg: VReg) -> bool {
    defs.get(&vreg.id)
        .and_then(|&def| movz_i32_imm(func.inst(def)).map(|(_, imm)| imm))
        == Some(0)
}

fn vreg_i32_zero_def(
    func: &MachFunction,
    defs: &HashMap<u32, InstId>,
    vreg: VReg,
) -> Option<InstId> {
    let def = defs.get(&vreg.id).copied()?;
    (movz_i32_imm(func.inst(def)) == Some((vreg, 0))).then_some(def)
}

fn vreg_is_i32_minus_one(func: &MachFunction, defs: &HashMap<u32, InstId>, vreg: VReg) -> bool {
    defs.get(&vreg.id)
        .and_then(|&def| movn_i32_minus_one(func.inst(def)))
        .is_some_and(|dst| dst == vreg)
}

fn match_reverse_accumulation_loop_body(func: &MachFunction, lp: &NaturalLoop) -> Option<BlockId> {
    if lp.body.len() == 3 {
        let loop_body = lp
            .body
            .iter()
            .copied()
            .find(|block| *block != lp.header && *block != lp.latch)?;
        return func
            .block(loop_body)
            .succs
            .contains(&lp.latch)
            .then_some(loop_body);
    }

    if lp.body.len() == 2 && lp.latch != lp.header {
        return Some(lp.latch);
    }

    None
}

fn match_reverse_accumulation_candidate(
    func: &MachFunction,
    lp: &NaturalLoop,
    defs: &HashMap<u32, InstId>,
) -> Option<ReverseAccumulationCandidate> {
    let loop_body = match_reverse_accumulation_loop_body(func, lp)?;

    for &store_id in &func.block(loop_body).insts {
        let store = func.inst(store_id);
        if store.opcode != AArch64Opcode::StrRI {
            continue;
        }
        let stored_value = gpr32_vreg_from_operand(store.operands.first()?)?;
        let dest_address = gpr64_vreg_from_operand(store.operands.get(1)?)?;
        if !matches!(store.operands.get(2), Some(MachOperand::Imm(0))) {
            continue;
        }

        let add_id = defs.get(&stored_value.id).copied()?;
        let add = func.inst(add_id);
        if add.opcode != AArch64Opcode::AddRR {
            continue;
        }
        let lhs = gpr32_vreg_from_operand(add.operands.get(1)?)?;
        let rhs = gpr32_vreg_from_operand(add.operands.get(2)?)?;

        let lhs_load_id = defs.get(&lhs.id).copied()?;
        let rhs_load_id = defs.get(&rhs.id).copied()?;
        let lhs_load = func.inst(lhs_load_id);
        let rhs_load = func.inst(rhs_load_id);
        if lhs_load.opcode != AArch64Opcode::LdrRI || rhs_load.opcode != AArch64Opcode::LdrRI {
            continue;
        }
        let lhs_address = gpr64_vreg_from_operand(lhs_load.operands.get(1)?)?;
        let rhs_address = gpr64_vreg_from_operand(rhs_load.operands.get(1)?)?;
        if !matches!(lhs_load.operands.get(2), Some(MachOperand::Imm(0)))
            || !matches!(rhs_load.operands.get(2), Some(MachOperand::Imm(0)))
        {
            continue;
        }

        let (dest_load_inst, source_load_inst, source_address) = if lhs_address == dest_address {
            (lhs_load_id, rhs_load_id, rhs_address)
        } else if rhs_address == dest_address {
            (rhs_load_id, lhs_load_id, lhs_address)
        } else {
            continue;
        };

        let source_address_inst = defs.get(&source_address.id).copied()?;
        let dest_address_inst = defs.get(&dest_address.id).copied()?;
        let (source_wide_index, source_element_size, source_base) =
            match_reverse_accumulation_madd_address(func, source_address_inst)?;
        let (dest_wide_index, dest_element_size, dest_base) =
            match_reverse_accumulation_madd_address(func, dest_address_inst)?;
        if source_wide_index != dest_wide_index || source_element_size != dest_element_size {
            continue;
        }
        let sign_extend_inst = defs.get(&source_wide_index.id).copied()?;
        let sign_extend = func.inst(sign_extend_inst);
        if sign_extend.opcode != AArch64Opcode::Sxtw
            || sign_extend.operands.len() != 2
            || sign_extend.operands[0] != MachOperand::VReg(source_wide_index)
        {
            continue;
        }
        let narrow_index = gpr32_vreg_from_operand(&sign_extend.operands[1])?;

        return Some(ReverseAccumulationCandidate {
            loop_header: lp.header,
            loop_body,
            source_address_inst,
            dest_address_inst,
            source_load_inst,
            dest_load_inst,
            add_inst: add_id,
            dest_store_inst: store_id,
            sign_extend_inst,
            narrow_index,
            element_size: source_element_size,
            source_base,
            dest_base,
        });
    }

    None
}

fn match_reverse_accumulation_header(
    func: &MachFunction,
    lp: &NaturalLoop,
    defs: &HashMap<u32, InstId>,
) -> Option<(ReverseAccumulationIndex, BlockId)> {
    const AARCH64_COND_GT: i64 = 10;
    const AARCH64_COND_NE: i64 = 1;
    let header = lp.header;

    let insts: Vec<InstId> = func
        .block(header)
        .insts
        .iter()
        .copied()
        .filter(|&inst_id| func.inst(inst_id).opcode != AArch64Opcode::Nop)
        .collect();
    let cmp_pos = insts.iter().position(|&inst_id| {
        matches!(
            func.inst(inst_id).opcode,
            AArch64Opcode::CmpRI | AArch64Opcode::CmpRR
        )
    })?;
    let tail = &insts[cmp_pos + 1..];
    let cmp = func.inst(insts[cmp_pos]);
    let (cmp_index, cmp_zero_def) = match cmp.opcode {
        AArch64Opcode::CmpRI
            if cmp.operands.len() == 2 && cmp.operands[1] == MachOperand::Imm(0) =>
        {
            (gpr32_vreg_from_operand(&cmp.operands[0])?, None)
        }
        AArch64Opcode::CmpRR if cmp.operands.len() == 2 => {
            let lhs = gpr32_vreg_from_operand(&cmp.operands[0])?;
            let rhs = gpr32_vreg_from_operand(&cmp.operands[1])?;
            if vreg_is_i32_zero(func, defs, rhs) {
                (lhs, vreg_i32_zero_def(func, defs, rhs))
            } else if vreg_is_i32_zero(func, defs, lhs) {
                (rhs, vreg_i32_zero_def(func, defs, lhs))
            } else {
                return None;
            }
        }
        _ => return None,
    };
    let (branch_body, branch_exit) = match tail {
        [branch_body, branch_exit]
            if func.inst(*branch_body).opcode == AArch64Opcode::BCond
                && func.inst(*branch_body).operands.len() == 2
                && func.inst(*branch_body).operands[0] == MachOperand::Imm(AARCH64_COND_GT)
                && func.inst(*branch_exit).opcode == AArch64Opcode::B =>
        {
            (func.inst(*branch_body), func.inst(*branch_exit))
        }
        [cset_id, cmp_cset_id, branch_body_id, branch_exit_id] => {
            let cset = func.inst(*cset_id);
            let cmp_cset = func.inst(*cmp_cset_id);
            let branch_body = func.inst(*branch_body_id);
            let branch_exit = func.inst(*branch_exit_id);
            let cset_value = vreg_from_operand(cset.operands.first()?)?;
            if cset.opcode != AArch64Opcode::CSet
                || cset.operands.get(1) != Some(&MachOperand::Imm(AARCH64_COND_GT))
                || cmp_cset.opcode != AArch64Opcode::CmpRI
                || cmp_cset.operands.len() != 2
                || cmp_cset.operands[0] != MachOperand::VReg(cset_value)
                || cmp_cset.operands[1] != MachOperand::Imm(0)
                || branch_body.opcode != AArch64Opcode::BCond
                || branch_body.operands.len() != 2
                || branch_body.operands[0] != MachOperand::Imm(AARCH64_COND_NE)
                || branch_exit.opcode != AArch64Opcode::B
            {
                return None;
            }
            (branch_body, branch_exit)
        }
        _ => return None,
    };

    let stack_index =
        ldr_i32_from_stack_slot_in_insts(func, &insts[..cmp_pos], cmp_index, None, defs);
    if insts[..cmp_pos].iter().any(|&inst_id| {
        let dead_immediate_zero =
            cmp.opcode == AArch64Opcode::CmpRI
                && movz_i32_imm(func.inst(inst_id)).is_some_and(|(zero, imm)| {
                    imm == 0
                        && !lp.body.iter().any(|&block| {
                            func.block(block).insts.iter().copied().any(|candidate| {
                                inst_source_uses_vreg(func.inst(candidate), zero.id)
                            })
                        })
                });
        func.inst(inst_id).opcode != AArch64Opcode::MovR
            && cmp_zero_def != Some(inst_id)
            && stack_index.is_none_or(|(_, load_inst)| load_inst != inst_id)
            && !dead_immediate_zero
    }) {
        return None;
    }
    let index = if let Some((address, _load_inst)) = stack_index {
        ReverseAccumulationIndex::StackSlot { address }
    } else {
        ReverseAccumulationIndex::Register(
            movr_source_for_dst_in_insts(func, &insts[..cmp_pos], cmp_index)
                .map(|(source, _)| source)
                .unwrap_or(cmp_index),
        )
    };
    let body = branch_target(branch_body)?;
    branch_target(branch_exit)?;
    Some((index, body))
}

fn match_reverse_accumulation_latch(
    func: &MachFunction,
    latch: BlockId,
    header: BlockId,
    index: VReg,
) -> Option<(InstId, InstId)> {
    let insts: Vec<InstId> = func
        .block(latch)
        .insts
        .iter()
        .copied()
        .filter(|&inst_id| func.inst(inst_id).opcode != AArch64Opcode::Nop)
        .collect();
    if insts.len() != 3 {
        return None;
    }
    let step = func.inst(insts[0]);
    let writeback = func.inst(insts[1]);
    let branch = func.inst(insts[2]);
    let next = gpr32_vreg_from_operand(step.operands.first()?)?;
    let source = gpr32_vreg_from_operand(step.operands.get(1)?)?;
    let reverse_step = match step.opcode {
        AArch64Opcode::AddRI => step.operands.get(2) == Some(&MachOperand::Imm(-1)),
        AArch64Opcode::SubRI => step.operands.get(2) == Some(&MachOperand::Imm(1)),
        _ => false,
    };
    if source != index || !reverse_step {
        return None;
    }
    let (writeback_dst, writeback_src) = movr_vreg_copy(writeback)?;
    if writeback_dst != index || writeback_src != next {
        return None;
    }
    if as_block_branch(branch, AArch64Opcode::B) != Some(header) {
        return None;
    }
    Some((insts[0], insts[1]))
}

fn match_reverse_accumulation_stack_latch(
    func: &MachFunction,
    latch: BlockId,
    header: BlockId,
    address: VReg,
    defs: &HashMap<u32, InstId>,
) -> Option<Vec<InstId>> {
    let insts: Vec<InstId> = func
        .block(latch)
        .insts
        .iter()
        .copied()
        .filter(|&inst_id| func.inst(inst_id).opcode != AArch64Opcode::Nop)
        .collect();
    let branch_id = *insts.last()?;
    if as_block_branch(func.inst(branch_id), AArch64Opcode::B) != Some(header) {
        return None;
    }

    for &store_id in &insts {
        let store = func.inst(store_id);
        if store.opcode != AArch64Opcode::StrRI
            || store.operands.len() != 3
            || store.operands[1] != MachOperand::VReg(address)
            || store.operands[2] != MachOperand::Imm(0)
        {
            continue;
        }
        let next = gpr32_vreg_from_operand(&store.operands[0])?;
        let step_id = defs.get(&next.id).copied()?;
        let step = func.inst(step_id);
        let (index, reverse_step) = match step.opcode {
            AArch64Opcode::AddRI if step.operands.len() == 3 => {
                let dst = gpr32_vreg_from_operand(&step.operands[0])?;
                let src = gpr32_vreg_from_operand(&step.operands[1])?;
                (src, dst == next && step.operands[2] == MachOperand::Imm(-1))
            }
            AArch64Opcode::SubRI if step.operands.len() == 3 => {
                let dst = gpr32_vreg_from_operand(&step.operands[0])?;
                let src = gpr32_vreg_from_operand(&step.operands[1])?;
                (src, dst == next && step.operands[2] == MachOperand::Imm(1))
            }
            AArch64Opcode::AddRR if step.operands.len() == 3 => {
                let dst = gpr32_vreg_from_operand(&step.operands[0])?;
                let lhs = gpr32_vreg_from_operand(&step.operands[1])?;
                let rhs = gpr32_vreg_from_operand(&step.operands[2])?;
                if dst != next {
                    continue;
                }
                if vreg_is_i32_minus_one(func, defs, rhs) {
                    (lhs, true)
                } else if vreg_is_i32_minus_one(func, defs, lhs) {
                    (rhs, true)
                } else {
                    (lhs, false)
                }
            }
            _ => continue,
        };
        if !reverse_step {
            continue;
        }
        let load_id = defs.get(&index.id).copied()?;
        ldr_i32_from_stack_slot(func, load_id, index, Some(address), defs)?;
        return Some(vec![load_id, step_id, store_id]);
    }

    None
}

fn body_contains_only_reverse_accumulation_idiom(
    func: &MachFunction,
    body: BlockId,
    branch_target_block: BlockId,
    candidate: ReverseAccumulationCandidate,
    extra_allowed: &[InstId],
) -> bool {
    let allowed = [
        candidate.sign_extend_inst,
        candidate.source_address_inst,
        candidate.source_load_inst,
        candidate.dest_address_inst,
        candidate.dest_load_inst,
        candidate.add_inst,
        candidate.dest_store_inst,
    ];
    func.block(body).insts.iter().copied().all(|inst_id| {
        let inst = func.inst(inst_id);
        inst.opcode == AArch64Opcode::Nop
            || allowed.contains(&inst_id)
            || extra_allowed.contains(&inst_id)
            || (inst.opcode == AArch64Opcode::B && branch_target(inst) == Some(branch_target_block))
    })
}

fn loop_defined_inst(func: &MachFunction, lp: &NaturalLoop, inst_id: InstId) -> bool {
    lp.body
        .iter()
        .any(|&block| func.block(block).insts.contains(&inst_id))
}

fn loop_invariant_base_copy(
    func: &MachFunction,
    lp: &NaturalLoop,
    defs: &HashMap<u32, InstId>,
    base: VReg,
) -> Option<InstId> {
    let copy_id = defs.get(&base.id).copied()?;
    let (dst, src) = movr_vreg_copy(func.inst(copy_id))?;
    if dst != base || dst.class != RegClass::Gpr64 || src.class != RegClass::Gpr64 {
        return None;
    }
    if defs
        .get(&src.id)
        .is_some_and(|&src_def| loop_defined_inst(func, lp, src_def))
    {
        return None;
    }
    Some(copy_id)
}

fn match_reverse_accumulation_loop(
    func: &MachFunction,
    lp: &NaturalLoop,
    defs: &HashMap<u32, InstId>,
) -> Option<ReverseAccumulationLoop> {
    let candidate = match_reverse_accumulation_candidate(func, lp, defs)?;
    let preheader = lp.preheader.or_else(|| {
        func.block(lp.header)
            .preds
            .iter()
            .copied()
            .find(|pred| !lp.body.contains(pred))
    })?;
    let branch_to_header = find_branch_to_header(func, preheader, lp.header)?;
    let (index, header_body) = match_reverse_accumulation_header(func, lp, defs)?;
    if header_body != candidate.loop_body {
        return None;
    }

    let mut extra_allowed_insts = Vec::new();
    for base in [candidate.source_base, candidate.dest_base] {
        if let Some(inst_id) = loop_invariant_base_copy(func, lp, defs, base) {
            push_unique_inst(&mut extra_allowed_insts, inst_id);
        }
    }
    match index {
        ReverseAccumulationIndex::Register(index) => {
            if candidate.narrow_index != index {
                return None;
            }
            match_reverse_accumulation_latch(func, lp.latch, lp.header, index)?;
        }
        ReverseAccumulationIndex::StackSlot { address } => {
            let load_id = defs.get(&candidate.narrow_index.id).copied()?;
            ldr_i32_from_stack_slot(func, load_id, candidate.narrow_index, Some(address), defs)?;
            push_unique_inst(&mut extra_allowed_insts, load_id);
            for inst_id in
                match_reverse_accumulation_stack_latch(func, lp.latch, lp.header, address, defs)?
            {
                push_unique_inst(&mut extra_allowed_insts, inst_id);
            }
        }
    }
    let body_branch_target = if candidate.loop_body == lp.latch {
        lp.header
    } else {
        lp.latch
    };
    if !body_contains_only_reverse_accumulation_idiom(
        func,
        candidate.loop_body,
        body_branch_target,
        candidate,
        &extra_allowed_insts,
    ) {
        return None;
    }
    Some(ReverseAccumulationLoop {
        preheader,
        branch_to_header,
        index,
        candidate,
    })
}

fn reverse_accumulation_report(
    func: &MachFunction,
    lp: &NaturalLoop,
    proof_facts: &HashMap<InstId, Vec<ProofFact>>,
    defs: &HashMap<u32, InstId>,
) -> Option<ReverseAccumulationProofReport> {
    let candidate = match_reverse_accumulation_candidate(func, lp, defs)?;
    let mut consumed_facts = Vec::new();
    let mut rejection = None;
    let source_origin = calloc_return_origin_for_vreg(func, candidate.source_base, defs);
    let dest_origin = calloc_return_origin_for_vreg(func, candidate.dest_base, defs);
    let distinct_calloc_origins =
        source_origin.is_some() && dest_origin.is_some() && source_origin != dest_origin;

    let requirements = vec![
        (
            vec![candidate.source_address_inst, candidate.source_load_inst],
            ProofFact::NoAlias,
            ReverseAccumulationRejection::MissingSourceNoAlias,
            distinct_calloc_origins,
        ),
        (
            vec![
                candidate.dest_address_inst,
                candidate.dest_load_inst,
                candidate.dest_store_inst,
            ],
            ProofFact::NoAlias,
            ReverseAccumulationRejection::MissingDestNoAlias,
            distinct_calloc_origins,
        ),
        (
            vec![candidate.source_address_inst, candidate.source_load_inst],
            ProofFact::InBounds,
            ReverseAccumulationRejection::MissingSourceInBounds,
            false,
        ),
        (
            vec![
                candidate.dest_address_inst,
                candidate.dest_load_inst,
                candidate.dest_store_inst,
            ],
            ProofFact::InBounds,
            ReverseAccumulationRejection::MissingDestInBounds,
            false,
        ),
    ];
    for (insts, fact, missing, structural) in requirements {
        if structural || any_inst_has_proof_fact(proof_facts, &insts, fact) {
            push_unique_proof_fact(&mut consumed_facts, fact);
        } else if rejection.is_none() {
            rejection = Some(missing);
        }
    }

    if candidate.source_base == candidate.dest_base && rejection.is_none() {
        rejection = Some(ReverseAccumulationRejection::SameAllocationBase);
    }
    if match_reverse_accumulation_loop(func, lp, defs).is_none() && rejection.is_none() {
        rejection = Some(ReverseAccumulationRejection::MissingReverseTraversal);
    }
    if rejection.is_none() {
        push_unique_proof_fact(
            &mut consumed_facts,
            ProofFact::BoundedLoop(u64::from(u32::MAX)),
        );
        push_unique_proof_fact(&mut consumed_facts, ProofFact::ParallelMap);
        push_unique_proof_fact(&mut consumed_facts, ProofFact::Monotonic);
    }

    Some(ReverseAccumulationProofReport {
        loop_header: candidate.loop_header,
        loop_body: candidate.loop_body,
        source_address_inst: candidate.source_address_inst,
        dest_address_inst: candidate.dest_address_inst,
        source_load_inst: candidate.source_load_inst,
        dest_load_inst: candidate.dest_load_inst,
        dest_store_inst: candidate.dest_store_inst,
        consumed_facts,
        rejection,
    })
}

fn reverse_accumulation_reports(
    func: &MachFunction,
    loop_analysis: &LoopAnalysis,
    proof_facts: &HashMap<InstId, Vec<ProofFact>>,
    defs: &HashMap<u32, InstId>,
) -> Vec<ReverseAccumulationProofReport> {
    loop_analysis
        .all_loops()
        .filter_map(|lp| reverse_accumulation_report(func, lp, proof_facts, defs))
        .collect()
}

fn reverse_accumulation_loop_is_proof_accepted(
    func: &MachFunction,
    lp: &NaturalLoop,
    proof_facts: &HashMap<InstId, Vec<ProofFact>>,
    defs: &HashMap<u32, InstId>,
) -> bool {
    reverse_accumulation_report(func, lp, proof_facts, defs)
        .is_some_and(|report| report.rejection.is_none())
}

fn rewrite_reverse_accumulation_loop(
    func: &mut MachFunction,
    idiom: ReverseAccumulationLoop,
    provenance: Option<&mut ProvenanceMap>,
) -> Option<VectorizationResult> {
    const S4_ARRANGEMENT: i64 = 5;
    const AARCH64_COND_GT: i64 = 10;
    const REVERSE_VECTOR_LANES: i64 = 16;
    const REVERSE_VECTOR_GUARD: i64 = REVERSE_VECTOR_LANES - 1;
    const REVERSE_VECTOR_PAIRS: usize = 2;

    let stack_index_address = match idiom.index {
        ReverseAccumulationIndex::Register(_) => None,
        ReverseAccumulationIndex::StackSlot { address } => Some(address),
    };

    let vector_entry = stack_index_address.map(|_| func.create_block());
    let vector_header = func.create_block();
    let vector_body = func.create_block();
    let vector_latch = func.create_block();
    let vector_exit = stack_index_address.map(|_| func.create_block());
    let mut blocks = Vec::new();
    if let Some(vector_entry) = vector_entry {
        blocks.push(vector_entry);
    }
    blocks.push(vector_header);
    blocks.push(vector_body);
    blocks.push(vector_latch);
    if let Some(vector_exit) = vector_exit {
        blocks.push(vector_exit);
    }
    insert_new_blocks_before(func, idiom.candidate.loop_header, &blocks);

    let vector_target = vector_entry.unwrap_or(vector_header);
    let scalar_tail_target = vector_exit.unwrap_or(idiom.candidate.loop_header);

    if !rewrite_block_target(
        func.inst_mut(idiom.branch_to_header),
        idiom.candidate.loop_header,
        vector_target,
    ) {
        return None;
    }

    remove_cfg_edge(func, idiom.preheader, idiom.candidate.loop_header);
    func.add_edge(idiom.preheader, vector_target);
    if let Some(vector_entry) = vector_entry {
        func.add_edge(vector_entry, vector_header);
    }
    func.add_edge(vector_header, vector_body);
    func.add_edge(vector_header, scalar_tail_target);
    func.add_edge(vector_body, vector_latch);
    func.add_edge(vector_latch, vector_header);
    if let Some(vector_exit) = vector_exit {
        func.add_edge(vector_exit, idiom.candidate.loop_header);
    }

    let source_loc = func.inst(idiom.candidate.add_inst).source_loc;
    let source_load_loc = func.inst(idiom.candidate.source_load_inst).source_loc;
    let dest_load_loc = func.inst(idiom.candidate.dest_load_inst).source_loc;
    let dest_store_loc = func.inst(idiom.candidate.dest_store_inst).source_loc;
    let mut created = Vec::new();
    let vector_index = match idiom.index {
        ReverseAccumulationIndex::Register(index) => index,
        ReverseAccumulationIndex::StackSlot { .. } => alloc_fresh_vreg(func, RegClass::Gpr32),
    };

    if let ReverseAccumulationIndex::StackSlot { address } = idiom.index {
        let vector_entry = vector_entry.expect("stack-slot reverse vectorization has entry");
        push_inst_to_block(
            func,
            vector_entry,
            with_source_loc(
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::VReg(vector_index),
                        MachOperand::VReg(address),
                        MachOperand::Imm(0),
                    ],
                ),
                source_loc,
            ),
            &mut created,
        );
        push_inst_to_block(
            func,
            vector_entry,
            with_source_loc(
                MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(vector_header)]),
                source_loc,
            ),
            &mut created,
        );
    }
    push_inst_to_block(
        func,
        vector_header,
        with_source_loc(
            MachInst::new(
                AArch64Opcode::CmpRI,
                vec![
                    MachOperand::VReg(vector_index),
                    MachOperand::Imm(REVERSE_VECTOR_GUARD),
                ],
            ),
            source_loc,
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_header,
        with_source_loc(
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AARCH64_COND_GT),
                    MachOperand::Block(vector_body),
                ],
            ),
            source_loc,
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_header,
        with_source_loc(
            MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Block(scalar_tail_target)],
            ),
            source_loc,
        ),
        &mut created,
    );

    let chunk_start = alloc_fresh_vreg(func, RegClass::Gpr32);
    let wide_chunk_start = alloc_fresh_vreg(func, RegClass::Gpr64);
    let source_ptr = alloc_fresh_vreg(func, RegClass::Gpr64);
    let dest_load_ptr = alloc_fresh_vreg(func, RegClass::Gpr64);
    let dest_store_ptr = alloc_fresh_vreg(func, RegClass::Gpr64);

    push_inst_to_block(
        func,
        vector_body,
        with_source_loc(
            MachInst::new(
                AArch64Opcode::SubRI,
                vec![
                    MachOperand::VReg(chunk_start),
                    MachOperand::VReg(vector_index),
                    MachOperand::Imm(REVERSE_VECTOR_GUARD),
                ],
            ),
            source_loc,
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_body,
        with_source_loc(
            MachInst::new(
                AArch64Opcode::Sxtw,
                vec![
                    MachOperand::VReg(wide_chunk_start),
                    MachOperand::VReg(chunk_start),
                ],
            ),
            source_loc,
        ),
        &mut created,
    );
    push_inst_to_block(
        func,
        vector_body,
        with_source_loc(
            MachInst::new(
                AArch64Opcode::Madd,
                vec![
                    MachOperand::VReg(source_ptr),
                    MachOperand::VReg(wide_chunk_start),
                    MachOperand::VReg(idiom.candidate.element_size),
                    MachOperand::VReg(idiom.candidate.source_base),
                ],
            ),
            source_loc,
        ),
        &mut created,
    );
    for dest_ptr in [dest_load_ptr, dest_store_ptr] {
        push_inst_to_block(
            func,
            vector_body,
            with_source_loc(
                MachInst::new(
                    AArch64Opcode::Madd,
                    vec![
                        MachOperand::VReg(dest_ptr),
                        MachOperand::VReg(wide_chunk_start),
                        MachOperand::VReg(idiom.candidate.element_size),
                        MachOperand::VReg(idiom.candidate.dest_base),
                    ],
                ),
                source_loc,
            ),
            &mut created,
        );
    }
    for pair in 0..REVERSE_VECTOR_PAIRS {
        let pair_offset = (pair as i64) * 32;
        let source_lo = alloc_fresh_vreg(func, RegClass::Fpr128);
        let source_hi = alloc_fresh_vreg(func, RegClass::Fpr128);
        let dest_lo = alloc_fresh_vreg(func, RegClass::Fpr128);
        let dest_hi = alloc_fresh_vreg(func, RegClass::Fpr128);
        let sum_lo = alloc_fresh_vreg(func, RegClass::Fpr128);
        let sum_hi = alloc_fresh_vreg(func, RegClass::Fpr128);
        push_inst_to_block(
            func,
            vector_body,
            with_source_loc(
                MachInst::new(
                    AArch64Opcode::LdpRI,
                    vec![
                        MachOperand::VReg(source_lo),
                        MachOperand::VReg(source_hi),
                        MachOperand::VReg(source_ptr),
                        MachOperand::Imm(pair_offset),
                    ],
                ),
                source_load_loc,
            ),
            &mut created,
        );
        push_inst_to_block(
            func,
            vector_body,
            with_source_loc(
                MachInst::new(
                    AArch64Opcode::LdpRI,
                    vec![
                        MachOperand::VReg(dest_lo),
                        MachOperand::VReg(dest_hi),
                        MachOperand::VReg(dest_load_ptr),
                        MachOperand::Imm(pair_offset),
                    ],
                ),
                dest_load_loc,
            ),
            &mut created,
        );
        push_inst_to_block(
            func,
            vector_body,
            with_source_loc(
                MachInst::new(
                    AArch64Opcode::NeonAddV,
                    vec![
                        MachOperand::VReg(sum_lo),
                        MachOperand::VReg(dest_lo),
                        MachOperand::VReg(source_lo),
                        MachOperand::Imm(S4_ARRANGEMENT),
                    ],
                ),
                source_loc,
            ),
            &mut created,
        );
        push_inst_to_block(
            func,
            vector_body,
            with_source_loc(
                MachInst::new(
                    AArch64Opcode::NeonAddV,
                    vec![
                        MachOperand::VReg(sum_hi),
                        MachOperand::VReg(dest_hi),
                        MachOperand::VReg(source_hi),
                        MachOperand::Imm(S4_ARRANGEMENT),
                    ],
                ),
                source_loc,
            ),
            &mut created,
        );
        push_inst_to_block(
            func,
            vector_body,
            with_source_loc(
                MachInst::new(
                    AArch64Opcode::StpRI,
                    vec![
                        MachOperand::VReg(sum_lo),
                        MachOperand::VReg(sum_hi),
                        MachOperand::VReg(dest_store_ptr),
                        MachOperand::Imm(pair_offset),
                    ],
                ),
                dest_store_loc,
            ),
            &mut created,
        );
    }
    push_inst_to_block(
        func,
        vector_body,
        with_source_loc(
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(vector_latch)]),
            source_loc,
        ),
        &mut created,
    );

    match idiom.index {
        ReverseAccumulationIndex::Register(index) => {
            push_inst_to_block(
                func,
                vector_latch,
                with_source_loc(
                    MachInst::new(
                        AArch64Opcode::SubRI,
                        vec![
                            MachOperand::VReg(index),
                            MachOperand::VReg(index),
                            MachOperand::Imm(REVERSE_VECTOR_LANES),
                        ],
                    ),
                    source_loc,
                ),
                &mut created,
            );
        }
        ReverseAccumulationIndex::StackSlot { address } => {
            push_inst_to_block(
                func,
                vector_latch,
                with_source_loc(
                    MachInst::new(
                        AArch64Opcode::SubRI,
                        vec![
                            MachOperand::VReg(vector_index),
                            MachOperand::VReg(vector_index),
                            MachOperand::Imm(REVERSE_VECTOR_LANES),
                        ],
                    ),
                    source_loc,
                ),
                &mut created,
            );
            let vector_exit = vector_exit.expect("stack-slot reverse vectorization has exit");
            push_inst_to_block(
                func,
                vector_exit,
                with_source_loc(
                    MachInst::new(
                        AArch64Opcode::StrRI,
                        vec![
                            MachOperand::VReg(vector_index),
                            MachOperand::VReg(address),
                            MachOperand::Imm(0),
                        ],
                    ),
                    source_loc,
                ),
                &mut created,
            );
            push_inst_to_block(
                func,
                vector_exit,
                with_source_loc(
                    MachInst::new(
                        AArch64Opcode::B,
                        vec![MachOperand::Block(idiom.candidate.loop_header)],
                    ),
                    source_loc,
                ),
                &mut created,
            );
        }
    }
    push_inst_to_block(
        func,
        vector_latch,
        with_source_loc(
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(vector_header)]),
            source_loc,
        ),
        &mut created,
    );

    if let Some(provenance) = provenance {
        let pass = vectorize_pass_id();
        provenance.record_in_place_transform(idiom.branch_to_header, pass.clone());
        for inst_id in created {
            provenance.record_creation(
                inst_id,
                pass.clone(),
                "vectorize reverse accumulation loop",
            );
        }
    }

    Some(VectorizationResult {
        insts_rewritten: 4,
        compare_idioms_rewritten: 0,
        horizontal_reductions_recognized: 0,
        ordered_sub_reductions_recognized: 0,
        regs_upgraded: (REVERSE_VECTOR_PAIRS * 6) as u32,
        has_epilogue: true,
        vector_trip_count: None,
        remainder: 0,
    })
}

fn rewrite_reverse_accumulation_loops(
    func: &mut MachFunction,
    loop_analysis: &LoopAnalysis,
    proof_facts: &HashMap<InstId, Vec<ProofFact>>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> Vec<VectorizationResult> {
    let mut results = Vec::new();
    let loops: Vec<_> = loop_analysis.all_loops().cloned().collect();
    // The scan is read-only, so one map serves every match attempt. A rewrite
    // can grow the arena even when it fails partway, so the map is rebuilt
    // after any rewrite call that does not return.
    let mut defs = build_def_map(func);
    for lp in loops {
        if !reverse_accumulation_loop_is_proof_accepted(func, &lp, proof_facts, &defs) {
            continue;
        }
        let Some(idiom) = match_reverse_accumulation_loop(func, &lp, &defs) else {
            continue;
        };
        if let Some(result) =
            rewrite_reverse_accumulation_loop(func, idiom, provenance.as_deref_mut())
        {
            results.push(result);
            return results;
        }
        defs = build_def_map(func);
    }
    results
}

fn block_inst_positions(func: &MachFunction, block: BlockId) -> HashMap<InstId, usize> {
    func.block(block)
        .insts
        .iter()
        .enumerate()
        .map(|(idx, &inst_id)| (inst_id, idx))
        .collect()
}

fn def_has_exactly_one_use(
    func: &MachFunction,
    use_counts: &HashMap<u32, usize>,
    inst_id: InstId,
) -> bool {
    let Some(result_id) = def_vreg_id(func.inst(inst_id)) else {
        return false;
    };
    use_counts.get(&result_id).copied().unwrap_or(0) == 1
}

fn match_zero_seed(func: &MachFunction, inst_id: InstId, expected_result: u32) -> bool {
    let inst = func.inst(inst_id);
    inst.opcode == AArch64Opcode::Movz
        && inst.operands.len() == 2
        && matches!(inst.operands[0], MachOperand::VReg(vreg) if vreg.id == expected_result && vreg.class == RegClass::Gpr32)
        && inst.operands[1] == MachOperand::Imm(0)
}

fn flatten_contains4_orr_chain(
    func: &MachFunction,
    defs: &HashMap<u32, InstId>,
    current_value: u32,
    depth: usize,
) -> Option<Contains4OrChain> {
    if depth > 4 {
        return None;
    }

    let def_inst = *defs.get(&current_value)?;
    if match_zero_seed(func, def_inst, current_value) {
        return Some(Contains4OrChain {
            zero_inst: def_inst,
            orr_insts: Vec::new(),
            bit_values: Vec::new(),
        });
    }

    let inst = func.inst(def_inst);
    if inst.opcode != AArch64Opcode::OrrRR || inst.operands.len() != 3 {
        return None;
    }
    if !matches!(inst.operands[0], MachOperand::VReg(vreg) if vreg.id == current_value && vreg.class == RegClass::Gpr32)
    {
        return None;
    }

    let lhs = gpr32_vreg_from_operand(&inst.operands[1])?;
    let rhs = gpr32_vreg_from_operand(&inst.operands[2])?;

    let candidates = [(lhs, rhs), (rhs, lhs)];
    for (acc, bit) in candidates {
        if let Some(mut chain) = flatten_contains4_orr_chain(func, defs, acc.id, depth + 1) {
            chain.orr_insts.push(def_inst);
            chain.bit_values.push(bit.id);
            return Some(chain);
        }
    }

    None
}

fn cmp_has_only_paired_flag_consumer(
    func: &MachFunction,
    block: BlockId,
    positions: &HashMap<InstId, usize>,
    cmp_inst: InstId,
    cset_inst: InstId,
) -> bool {
    let Some(&cmp_pos) = positions.get(&cmp_inst) else {
        return false;
    };
    let Some(&cset_pos) = positions.get(&cset_inst) else {
        return false;
    };
    if cset_pos != cmp_pos + 1 {
        return false;
    }

    let block = func.block(block);
    for &inst_id in block.insts.iter().skip(cmp_pos + 1) {
        if inst_id != cset_inst && reads_flags(func.inst(inst_id).opcode) {
            return false;
        }
        if inst_id != cmp_inst && writes_flags(func.inst(inst_id).opcode) {
            break;
        }
    }

    true
}

fn ldr_i32_base_offset(
    func: &MachFunction,
    inst_id: InstId,
    expected_dst: VReg,
) -> Option<(MachOperand, i64)> {
    let inst = func.inst(inst_id);
    if inst.opcode != AArch64Opcode::LdrRI || !(2..=3).contains(&inst.operands.len()) {
        return None;
    }
    if inst.operands[0] != MachOperand::VReg(expected_dst) || expected_dst.class != RegClass::Gpr32
    {
        return None;
    }
    let base = inst.operands[1].clone();
    if !is_gpr64_operand(&base) {
        return None;
    }
    let offset = match inst.operands.get(2) {
        Some(MachOperand::Imm(offset)) => *offset,
        Some(_) => return None,
        None => 0,
    };
    Some((base, offset))
}

fn block_has_memory_barrier_between(
    func: &MachFunction,
    block: BlockId,
    start_pos: usize,
    end_pos: usize,
    allowed_loads: &[InstId; 4],
) -> bool {
    let block = func.block(block);
    for &inst_id in &block.insts[start_pos + 1..end_pos] {
        if allowed_loads.contains(&inst_id) {
            continue;
        }
        let inst = func.inst(inst_id);
        let effect = opcode_effect(inst.opcode);
        if effect.writes_memory() || inst.flags.contains(trust_cg_ir::InstFlags::WRITES_MEMORY) {
            return true;
        }
        if inst.flags.contains(trust_cg_ir::InstFlags::IS_CALL) {
            return true;
        }
    }
    false
}

fn match_contains4_memory_chunk(
    func: &MachFunction,
    defs: &HashMap<u32, InstId>,
    use_counts: &HashMap<u32, usize>,
    positions: &HashMap<InstId, usize>,
    block: BlockId,
    and_inst: InstId,
    bits: &[Contains4MaskedBit; 4],
) -> Option<Contains4MemoryChunk> {
    let expected_offsets = [0_i64, 4, 8, 12];
    let mut load_insts = [InstId(0); 4];
    let mut base: Option<MachOperand> = None;
    let mut first_load_pos = usize::MAX;
    let mut previous_load_pos = None;

    for lane in 0..4 {
        let load_inst = *defs.get(&bits[lane].lane_value.id)?;
        if !def_has_exactly_one_use(func, use_counts, load_inst) {
            return None;
        }
        let (load_base, offset) = ldr_i32_base_offset(func, load_inst, bits[lane].lane_value)?;
        if offset != expected_offsets[lane] {
            return None;
        }
        if let Some(base) = &base {
            if *base != load_base {
                return None;
            }
        } else {
            base = Some(load_base);
        }

        let load_pos = *positions.get(&load_inst)?;
        let cmp_pos = *positions.get(&bits[lane].cmp_inst)?;
        if load_pos >= cmp_pos {
            return None;
        }
        if let Some(previous_load_pos) = previous_load_pos
            && load_pos <= previous_load_pos
        {
            return None;
        }
        previous_load_pos = Some(load_pos);
        first_load_pos = first_load_pos.min(load_pos);
        load_insts[lane] = load_inst;
    }

    let and_pos = *positions.get(&and_inst)?;
    if first_load_pos >= and_pos {
        return None;
    }
    if block_has_memory_barrier_between(func, block, first_load_pos, and_pos, &load_insts) {
        return None;
    }

    let can_use_base_directly = match &base {
        Some(MachOperand::VReg(vreg)) if vreg.class == RegClass::Gpr64 => {
            use_counts.get(&vreg.id).copied().unwrap_or(0) == load_insts.len()
        }
        _ => false,
    };

    Some(Contains4MemoryChunk {
        load_insts,
        base: base?,
        can_use_base_directly,
    })
}

fn match_contains4_bit(
    func: &MachFunction,
    defs: &HashMap<u32, InstId>,
    use_counts: &HashMap<u32, usize>,
    positions: &HashMap<InstId, usize>,
    block: BlockId,
    bit_value: u32,
) -> Option<(usize, Contains4MaskedBit)> {
    let bit_def = *defs.get(&bit_value)?;
    let bit_inst = func.inst(bit_def);

    let (lane_index, cset_inst, lsl_inst) = if bit_inst.opcode == AArch64Opcode::CSet {
        (0, bit_def, None)
    } else if bit_inst.opcode == AArch64Opcode::LslRI && bit_inst.operands.len() == 3 {
        if !def_has_exactly_one_use(func, use_counts, bit_def) {
            return None;
        }
        let MachOperand::Imm(shift) = bit_inst.operands[2] else {
            return None;
        };
        if !(1..=3).contains(&shift) {
            return None;
        }
        let source = gpr32_vreg_from_operand(&bit_inst.operands[1])?;
        let cset_inst = *defs.get(&source.id)?;
        (shift as usize, cset_inst, Some(bit_def))
    } else {
        return None;
    };

    if !def_has_exactly_one_use(func, use_counts, cset_inst) {
        return None;
    }

    let cset = func.inst(cset_inst);
    if cset.opcode != AArch64Opcode::CSet || cset.operands.len() != 2 {
        return None;
    }
    if !is_gpr32_vreg(&cset.operands[0]) || cset.operands[1] != MachOperand::Imm(0) {
        return None;
    }

    let cset_pos = *positions.get(&cset_inst)?;
    if cset_pos == 0 {
        return None;
    }
    let cmp_inst = func.block(block).insts[cset_pos - 1];
    let cmp = func.inst(cmp_inst);
    if cmp.opcode != AArch64Opcode::CmpRR || cmp.operands.len() != 2 {
        return None;
    }
    let lane_value = gpr32_vreg_from_operand(&cmp.operands[0])?;
    let literal = gpr32_vreg_from_operand(&cmp.operands[1])?;
    if !cmp_has_only_paired_flag_consumer(func, block, positions, cmp_inst, cset_inst) {
        return None;
    }

    Some((
        lane_index,
        Contains4MaskedBit {
            cmp_inst,
            cset_inst,
            lsl_inst,
            lane_value,
            literal,
        },
    ))
}

fn try_match_contains4_masked_root(
    func: &MachFunction,
    defs: &HashMap<u32, InstId>,
    use_counts: &HashMap<u32, usize>,
    positions: &HashMap<InstId, usize>,
    block: BlockId,
    and_inst: InstId,
) -> Option<Contains4MaskedIdiom> {
    let inst = func.inst(and_inst);
    if inst.opcode != AArch64Opcode::AndRR || inst.operands.len() != 3 {
        return None;
    }
    let output = gpr32_vreg_from_operand(&inst.operands[0])?;
    let lhs = gpr32_vreg_from_operand(&inst.operands[1])?;
    let rhs = gpr32_vreg_from_operand(&inst.operands[2])?;

    let candidates = [(lhs, rhs), (rhs, lhs)];
    for (mask_value, valid_mask) in candidates {
        let Some(chain) = flatten_contains4_orr_chain(func, defs, mask_value.id, 0) else {
            continue;
        };
        if chain.orr_insts.len() != 4 || chain.bit_values.len() != 4 {
            continue;
        }
        if !def_has_exactly_one_use(func, use_counts, chain.zero_inst)
            || chain
                .orr_insts
                .iter()
                .any(|&inst_id| !def_has_exactly_one_use(func, use_counts, inst_id))
        {
            continue;
        }

        let mut bits_by_lane: [Option<Contains4MaskedBit>; 4] = [None, None, None, None];
        for bit_value in &chain.bit_values {
            let Some((lane_index, bit)) =
                match_contains4_bit(func, defs, use_counts, positions, block, *bit_value)
            else {
                bits_by_lane = [None, None, None, None];
                break;
            };
            if bits_by_lane[lane_index].is_some() {
                bits_by_lane = [None, None, None, None];
                break;
            }
            bits_by_lane[lane_index] = Some(bit);
        }

        let [Some(bit0), Some(bit1), Some(bit2), Some(bit3)] = bits_by_lane else {
            continue;
        };
        let bits = [bit0, bit1, bit2, bit3];
        let literal = bits[0].literal;
        if bits.iter().any(|bit| bit.literal != literal) {
            continue;
        }
        let memory_chunk =
            match_contains4_memory_chunk(func, defs, use_counts, positions, block, and_inst, &bits);

        return Some(Contains4MaskedIdiom {
            and_inst,
            zero_inst: chain.zero_inst,
            orr_insts: chain.orr_insts,
            bits,
            memory_chunk,
            valid_mask,
            output,
        });
    }

    None
}

fn find_contains4_masked_idioms(
    func: &MachFunction,
    defs: &HashMap<u32, InstId>,
) -> Vec<Contains4MaskedIdiom> {
    let use_counts = build_vreg_use_counts(func);
    let mut idioms = Vec::new();

    for block_id in func.block_order.iter().copied() {
        let positions = block_inst_positions(func, block_id);
        for &inst_id in &func.block(block_id).insts {
            if let Some(idiom) = try_match_contains4_masked_root(
                func,
                defs,
                &use_counts,
                &positions,
                block_id,
                inst_id,
            ) {
                idioms.push(idiom);
            }
        }
    }

    idioms
}

fn alloc_fresh_vreg(func: &mut MachFunction, class: RegClass) -> VReg {
    let max_existing = func
        .insts
        .iter()
        .flat_map(|inst| inst.operands.iter())
        .filter_map(vreg_from_operand)
        .map(|vreg| vreg.id)
        .max()
        .unwrap_or(0);

    let mut id = func.alloc_vreg();
    while id <= max_existing {
        id = func.alloc_vreg();
    }
    VReg::new(id, class)
}

fn insert_before_inst(func: &mut MachFunction, before: InstId, new_insts: &[InstId]) -> bool {
    for block in &mut func.blocks {
        if let Some(pos) = block.insts.iter().position(|&inst_id| inst_id == before) {
            for (offset, &new_inst) in new_insts.iter().enumerate() {
                block.insts.insert(pos + offset, new_inst);
            }
            return true;
        }
    }
    false
}

fn with_source_loc(mut inst: MachInst, source_loc: Option<trust_cg_ir::SourceLoc>) -> MachInst {
    inst.source_loc = source_loc;
    inst
}

fn contains4_masked_scalar_insts(
    idiom: &Contains4MaskedIdiom,
    include_memory_loads: bool,
) -> Vec<InstId> {
    let mut scalar_insts = Vec::new();
    if include_memory_loads && let Some(memory_chunk) = &idiom.memory_chunk {
        scalar_insts.extend(memory_chunk.load_insts);
    }
    scalar_insts.push(idiom.zero_inst);
    scalar_insts.extend(idiom.orr_insts.iter().copied());
    for bit in &idiom.bits {
        scalar_insts.push(bit.cmp_inst);
        scalar_insts.push(bit.cset_inst);
        if let Some(lsl_inst) = bit.lsl_inst {
            scalar_insts.push(lsl_inst);
        }
    }
    scalar_insts.sort_by_key(|inst_id| inst_id.0);
    scalar_insts.dedup();
    scalar_insts
}

fn rewrite_contains4_masked_memory_idiom(
    func: &mut MachFunction,
    idiom: &Contains4MaskedIdiom,
    memory_chunk: &Contains4MemoryChunk,
    creation_reason: &'static str,
    provenance: Option<&mut ProvenanceMap>,
) -> Option<VectorizationResult> {
    const ELEMENT_SIZE_S: i64 = 4;
    const S4_ARRANGEMENT: i64 = 5;

    let load_loc = func.inst(memory_chunk.load_insts[0]).source_loc;
    let compare_loc = func.inst(idiom.bits[0].cmp_inst).source_loc;
    let mask_loc = func.inst(idiom.and_inst).source_loc;

    let lanes_vec = alloc_fresh_vreg(func, RegClass::Fpr128);
    let literal_vec = alloc_fresh_vreg(func, RegClass::Fpr128);
    let compare_vec = alloc_fresh_vreg(func, RegClass::Fpr128);
    let raw_bits: [VReg; 4] = std::array::from_fn(|_| alloc_fresh_vreg(func, RegClass::Gpr32));
    let positioned_bits: [VReg; 4] =
        std::array::from_fn(|_| alloc_fresh_vreg(func, RegClass::Gpr32));
    let mask01 = alloc_fresh_vreg(func, RegClass::Gpr32);
    let mask23 = alloc_fresh_vreg(func, RegClass::Gpr32);
    let combined_mask = alloc_fresh_vreg(func, RegClass::Gpr32);

    let mut created = Vec::new();
    let ld1_base = if memory_chunk.can_use_base_directly {
        memory_chunk.base.clone()
    } else {
        let base_copy = alloc_fresh_vreg(func, RegClass::Gpr64);
        let copy_base = func.push_inst(with_source_loc(
            MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::VReg(base_copy), memory_chunk.base.clone()],
            ),
            load_loc,
        ));
        created.push(copy_base);
        MachOperand::VReg(base_copy)
    };

    let load_lanes = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonLd1Post,
            vec![
                MachOperand::VReg(lanes_vec),
                ld1_base,
                MachOperand::Imm(S4_ARRANGEMENT),
            ],
        ),
        load_loc,
    ));
    created.push(load_lanes);

    let duplicate_literal = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonDupGen,
            vec![
                MachOperand::VReg(literal_vec),
                MachOperand::VReg(idiom.bits[0].literal),
                MachOperand::Imm(ELEMENT_SIZE_S),
            ],
        ),
        compare_loc,
    ));
    created.push(duplicate_literal);

    let cmeq = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonCmeqV,
            vec![
                MachOperand::VReg(compare_vec),
                MachOperand::VReg(lanes_vec),
                MachOperand::VReg(literal_vec),
                MachOperand::Imm(S4_ARRANGEMENT),
            ],
        ),
        compare_loc,
    ));
    created.push(cmeq);

    for lane in 0..4 {
        let umov = func.push_inst(with_source_loc(
            MachInst::new(
                AArch64Opcode::NeonUmovGen,
                vec![
                    MachOperand::VReg(raw_bits[lane]),
                    MachOperand::VReg(compare_vec),
                    MachOperand::Imm(lane as i64),
                    MachOperand::Imm(ELEMENT_SIZE_S),
                ],
            ),
            func.inst(idiom.bits[lane].cset_inst).source_loc,
        ));
        created.push(umov);

        let and = func.push_inst(with_source_loc(
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![
                    MachOperand::VReg(positioned_bits[lane]),
                    MachOperand::VReg(raw_bits[lane]),
                    MachOperand::Imm(1_i64 << lane),
                ],
            ),
            mask_loc,
        ));
        created.push(and);
    }

    let orr01 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::OrrRR,
            vec![
                MachOperand::VReg(mask01),
                MachOperand::VReg(positioned_bits[0]),
                MachOperand::VReg(positioned_bits[1]),
            ],
        ),
        mask_loc,
    ));
    let orr23 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::OrrRR,
            vec![
                MachOperand::VReg(mask23),
                MachOperand::VReg(positioned_bits[2]),
                MachOperand::VReg(positioned_bits[3]),
            ],
        ),
        mask_loc,
    ));
    let orr_mask = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::OrrRR,
            vec![
                MachOperand::VReg(combined_mask),
                MachOperand::VReg(mask01),
                MachOperand::VReg(mask23),
            ],
        ),
        mask_loc,
    ));
    created.extend([orr01, orr23, orr_mask]);

    if !insert_before_inst(func, memory_chunk.load_insts[0], &created) {
        return None;
    }

    let final_and = func.inst_mut(idiom.and_inst);
    final_and.operands = vec![
        MachOperand::VReg(idiom.output),
        MachOperand::VReg(combined_mask),
        MachOperand::VReg(idiom.valid_mask),
    ];

    let scalar_insts = contains4_masked_scalar_insts(idiom, true);
    for inst_id in &scalar_insts {
        let inst = func.inst_mut(*inst_id);
        inst.opcode = AArch64Opcode::Nop;
        inst.operands.clear();
    }

    if let Some(provenance) = provenance {
        let pass = vectorize_pass_id();
        let mut merged_sources = scalar_insts.clone();
        merged_sources.push(idiom.and_inst);
        provenance.record_merge(&merged_sources, idiom.and_inst, pass.clone());
        for &inst_id in &created {
            provenance.record_creation(inst_id, pass.clone(), creation_reason);
        }
    }

    Some(VectorizationResult {
        insts_rewritten: scalar_insts.len() as u32 + 1,
        compare_idioms_rewritten: 4,
        horizontal_reductions_recognized: 0,
        ordered_sub_reductions_recognized: 0,
        regs_upgraded: 0,
        has_epilogue: false,
        vector_trip_count: None,
        remainder: 0,
    })
}

fn rewrite_contains4_masked_idiom(
    func: &mut MachFunction,
    idiom: &Contains4MaskedIdiom,
    enable_scanner_memory_rewrite: bool,
    enable_scanner_batch_rewrite: bool,
    mut provenance: Option<&mut ProvenanceMap>,
) -> Option<VectorizationResult> {
    if let Some(memory_chunk) = &idiom.memory_chunk {
        let creation_reason = if enable_scanner_batch_rewrite {
            "vectorize contains4_masked inlined batch scanner"
        } else if enable_scanner_memory_rewrite {
            "vectorize contains4_masked memory"
        } else {
            return None;
        };
        return rewrite_contains4_masked_memory_idiom(
            func,
            idiom,
            memory_chunk,
            creation_reason,
            provenance.as_deref_mut(),
        );
    }

    const ELEMENT_SIZE_S: i64 = 4;
    const S4_ARRANGEMENT: i64 = 5;

    let compare_loc = func.inst(idiom.bits[0].cmp_inst).source_loc;
    let mask_loc = func.inst(idiom.and_inst).source_loc;

    let lanes_vec = alloc_fresh_vreg(func, RegClass::Fpr128);
    let literal_vec = alloc_fresh_vreg(func, RegClass::Fpr128);
    let compare_vec = alloc_fresh_vreg(func, RegClass::Fpr128);
    let raw_bits: [VReg; 4] = std::array::from_fn(|_| alloc_fresh_vreg(func, RegClass::Gpr32));
    let positioned_bits: [VReg; 4] =
        std::array::from_fn(|_| alloc_fresh_vreg(func, RegClass::Gpr32));
    let mask01 = alloc_fresh_vreg(func, RegClass::Gpr32);
    let mask23 = alloc_fresh_vreg(func, RegClass::Gpr32);
    let combined_mask = alloc_fresh_vreg(func, RegClass::Gpr32);

    let mut created = Vec::new();
    let seed_lanes = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonDupGen,
            vec![
                MachOperand::VReg(lanes_vec),
                MachOperand::VReg(idiom.bits[0].lane_value),
                MachOperand::Imm(ELEMENT_SIZE_S),
            ],
        ),
        func.inst(idiom.bits[0].cmp_inst).source_loc,
    ));
    created.push(seed_lanes);

    for lane in 1..4 {
        let ins = func.push_inst(with_source_loc(
            MachInst::new(
                AArch64Opcode::NeonInsGen,
                vec![
                    MachOperand::VReg(lanes_vec),
                    MachOperand::VReg(idiom.bits[lane].lane_value),
                    MachOperand::Imm(lane as i64),
                    MachOperand::Imm(ELEMENT_SIZE_S),
                ],
            ),
            func.inst(idiom.bits[lane].cmp_inst).source_loc,
        ));
        created.push(ins);
    }

    let duplicate_literal = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonDupGen,
            vec![
                MachOperand::VReg(literal_vec),
                MachOperand::VReg(idiom.bits[0].literal),
                MachOperand::Imm(ELEMENT_SIZE_S),
            ],
        ),
        compare_loc,
    ));
    created.push(duplicate_literal);

    let cmeq = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonCmeqV,
            vec![
                MachOperand::VReg(compare_vec),
                MachOperand::VReg(lanes_vec),
                MachOperand::VReg(literal_vec),
                MachOperand::Imm(S4_ARRANGEMENT),
            ],
        ),
        compare_loc,
    ));
    created.push(cmeq);

    for lane in 0..4 {
        let umov = func.push_inst(with_source_loc(
            MachInst::new(
                AArch64Opcode::NeonUmovGen,
                vec![
                    MachOperand::VReg(raw_bits[lane]),
                    MachOperand::VReg(compare_vec),
                    MachOperand::Imm(lane as i64),
                    MachOperand::Imm(ELEMENT_SIZE_S),
                ],
            ),
            func.inst(idiom.bits[lane].cset_inst).source_loc,
        ));
        created.push(umov);

        let and = func.push_inst(with_source_loc(
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![
                    MachOperand::VReg(positioned_bits[lane]),
                    MachOperand::VReg(raw_bits[lane]),
                    MachOperand::Imm(1_i64 << lane),
                ],
            ),
            mask_loc,
        ));
        created.push(and);
    }

    let orr01 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::OrrRR,
            vec![
                MachOperand::VReg(mask01),
                MachOperand::VReg(positioned_bits[0]),
                MachOperand::VReg(positioned_bits[1]),
            ],
        ),
        mask_loc,
    ));
    let orr23 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::OrrRR,
            vec![
                MachOperand::VReg(mask23),
                MachOperand::VReg(positioned_bits[2]),
                MachOperand::VReg(positioned_bits[3]),
            ],
        ),
        mask_loc,
    ));
    let orr_mask = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::OrrRR,
            vec![
                MachOperand::VReg(combined_mask),
                MachOperand::VReg(mask01),
                MachOperand::VReg(mask23),
            ],
        ),
        mask_loc,
    ));
    created.extend([orr01, orr23, orr_mask]);

    if !insert_before_inst(func, idiom.and_inst, &created) {
        return None;
    }

    let final_and = func.inst_mut(idiom.and_inst);
    final_and.operands = vec![
        MachOperand::VReg(idiom.output),
        MachOperand::VReg(combined_mask),
        MachOperand::VReg(idiom.valid_mask),
    ];

    let scalar_insts = contains4_masked_scalar_insts(idiom, false);

    for inst_id in &scalar_insts {
        let inst = func.inst_mut(*inst_id);
        inst.opcode = AArch64Opcode::Nop;
        inst.operands.clear();
    }

    if let Some(provenance) = provenance {
        let pass = vectorize_pass_id();
        let mut merged_sources = scalar_insts.clone();
        merged_sources.push(idiom.and_inst);
        provenance.record_merge(&merged_sources, idiom.and_inst, pass.clone());
        for &inst_id in &created {
            provenance.record_creation(inst_id, pass.clone(), "vectorize contains4_masked slp");
        }
    }

    Some(VectorizationResult {
        insts_rewritten: scalar_insts.len() as u32 + 1,
        compare_idioms_rewritten: 4,
        horizontal_reductions_recognized: 0,
        ordered_sub_reductions_recognized: 0,
        regs_upgraded: 0,
        has_epilogue: false,
        vector_trip_count: None,
        remainder: 0,
    })
}

fn rewrite_contains4_masked_slp(
    func: &mut MachFunction,
    enable_scanner_memory_rewrite: bool,
    enable_scanner_batch_rewrite: bool,
    mut provenance: Option<&mut ProvenanceMap>,
    defs: &HashMap<u32, InstId>,
) -> Vec<VectorizationResult> {
    let idioms = find_contains4_masked_idioms(func, defs);
    let mut consumed = HashSet::new();
    let mut results = Vec::new();

    for idiom in idioms {
        let scalar_insts = contains4_masked_scalar_insts(&idiom, idiom.memory_chunk.is_some());
        if scalar_insts
            .iter()
            .any(|inst_id| consumed.contains(inst_id))
        {
            continue;
        }

        if let Some(result) = rewrite_contains4_masked_idiom(
            func,
            &idiom,
            enable_scanner_memory_rewrite,
            enable_scanner_batch_rewrite,
            provenance.as_deref_mut(),
        ) {
            consumed.extend(scalar_insts);
            results.push(result);
        }
    }

    results
}

/// Upgrade a VReg operand from its scalar register class to the SIMD
/// register class (Fpr128), allocating a new vreg ID.
///
/// Returns the new VReg with SIMD class, and records the mapping.
fn upgrade_vreg_to_simd(
    func: &mut MachFunction,
    vreg: &trust_cg_ir::VReg,
    reg_map: &mut HashMap<u32, trust_cg_ir::VReg>,
    element_type: VecElementType,
) -> trust_cg_ir::VReg {
    if let Some(mapped) = reg_map.get(&vreg.id) {
        return *mapped;
    }
    let simd_class = simd_reg_class_for_element(element_type);
    // If already SIMD class, keep it
    if vreg.class == simd_class {
        reg_map.insert(vreg.id, *vreg);
        return *vreg;
    }
    let new_id = func.alloc_vreg();
    let new_vreg = trust_cg_ir::VReg::new(new_id, simd_class);
    reg_map.insert(vreg.id, new_vreg);
    new_vreg
}

#[derive(Debug, Clone, Copy)]
struct CompareRewriteResult {
    regs_upgraded: u32,
}

fn compare_idiom_uses_are_vectorizable(
    func: &MachFunction,
    idiom: VectorCompareIdiom,
    horizontal_any_reductions: &[HorizontalAnyReduction],
) -> bool {
    let Some(result) = def_vreg(func.inst(idiom.cset_inst)) else {
        return false;
    };

    let allowed_reducer_insts: HashSet<InstId> = horizontal_any_reductions
        .iter()
        .filter(|reduction| reduction.compare == idiom)
        .map(|reduction| reduction.reducer_inst)
        .collect();

    for (idx, inst) in func.insts.iter().enumerate() {
        let inst_id = InstId(idx as u32);
        if inst_id == idiom.cset_inst {
            continue;
        }
        if allowed_reducer_insts.contains(&inst_id) {
            continue;
        }
        let start = if produces_value(inst.opcode) { 1 } else { 0 };
        if inst
            .operands
            .iter()
            .skip(start)
            .any(|operand| operand_uses_exact_vreg(operand, result))
        {
            return false;
        }
    }

    true
}

fn insert_after_inst(func: &mut MachFunction, after: InstId, new_insts: &[InstId]) -> bool {
    for block in &mut func.blocks {
        if let Some(pos) = block.insts.iter().position(|&inst_id| inst_id == after) {
            for (offset, &new_inst) in new_insts.iter().enumerate() {
                block.insts.insert(pos + 1 + offset, new_inst);
            }
            return true;
        }
    }
    false
}

fn rewrite_horizontal_any_reduction_to_neon(
    func: &mut MachFunction,
    reduction: HorizontalAnyReduction,
    compare_result_id: u32,
    reg_map: &HashMap<u32, trust_cg_ir::VReg>,
    arrangement: NeonArrangement,
    provenance: Option<&mut ProvenanceMap>,
) -> Option<u32> {
    if reduction.kind != HorizontalAnyReductionKind::I32EqAny || arrangement != NeonArrangement::S4
    {
        return None;
    }

    let compare_mask = *reg_map.get(&compare_result_id)?;
    let reducer_operands = func.inst(reduction.reducer_inst).operands.clone();
    if reducer_operands.len() != 3 {
        return None;
    }
    let reducer_source_loc = func.inst(reduction.reducer_inst).source_loc;

    let MachOperand::VReg(acc_dst) = reducer_operands[0] else {
        return None;
    };
    let acc_operand = if operand_uses_exact_vreg(&reducer_operands[1], acc_dst) {
        reducer_operands[1].clone()
    } else if operand_uses_exact_vreg(&reducer_operands[2], acc_dst) {
        reducer_operands[2].clone()
    } else {
        return None;
    };

    let scalar_max = trust_cg_ir::VReg::new(func.alloc_vreg(), RegClass::Fpr32);
    let scalar_mask = trust_cg_ir::VReg::new(func.alloc_vreg(), RegClass::Gpr32);

    let reducer_inst = func.inst_mut(reduction.reducer_inst);
    reducer_inst.opcode = AArch64Opcode::NeonUmaxv;
    reducer_inst.operands = vec![
        MachOperand::VReg(scalar_max),
        MachOperand::VReg(compare_mask),
        MachOperand::Imm(neon_int_arrangement_encoding(arrangement)),
    ];

    let with_reducer_source_loc = |mut inst: MachInst| {
        inst.source_loc = reducer_source_loc;
        inst
    };

    let fmov_id = func.push_inst(with_reducer_source_loc(MachInst::new(
        AArch64Opcode::FmovFprGpr,
        vec![
            MachOperand::VReg(scalar_mask),
            MachOperand::VReg(scalar_max),
        ],
    )));
    let orr_id = func.push_inst(with_reducer_source_loc(MachInst::new(
        AArch64Opcode::OrrRR,
        vec![
            MachOperand::VReg(acc_dst),
            acc_operand,
            MachOperand::VReg(scalar_mask),
        ],
    )));

    if !insert_after_inst(func, reduction.reducer_inst, &[fmov_id, orr_id]) {
        return None;
    }

    if let Some(provenance) = provenance {
        let pass = vectorize_pass_id();
        provenance.record_in_place_transform(reduction.reducer_inst, pass.clone());
        if provenance.get_entry(reduction.reducer_inst).is_some() {
            provenance.record_clone(reduction.reducer_inst, fmov_id, pass.clone());
            provenance.record_clone(reduction.reducer_inst, orr_id, pass);
        } else {
            provenance.record_creation(
                fmov_id,
                pass.clone(),
                "vectorize horizontal-any scalar bridge",
            );
            provenance.record_creation(orr_id, pass, "vectorize horizontal-any scalar bridge");
        }
    }

    Some(3)
}

fn rewrite_ordered_sub_reduction_bridge(
    func: &mut MachFunction,
    reduction: OrderedSubReduction,
    reg_map: &HashMap<u32, trust_cg_ir::VReg>,
    vf: u32,
    mut provenance: Option<&mut ProvenanceMap>,
) -> Option<u32> {
    let vector_value = *reg_map.get(&reduction.lane_value.id)?;
    let reducer_operands = func.inst(reduction.reducer_inst).operands.clone();
    let reducer_dst = vreg_from_operand(reducer_operands.first()?)?;
    let stack_writeback_address = reduction.writeback_inst.and_then(|inst_id| {
        // Mutating rewrite context: earlier rewrites in this apply pass may
        // already have grown the arena, so the map is built here, once per
        // applied rewrite, instead of being threaded from a read-only sweep.
        let defs = build_def_map(func);
        str_gpr64_to_stack_slot_address(func, inst_id, reducer_dst, &defs)
    });
    let reducer_source_loc = func.inst(reduction.reducer_inst).source_loc;
    let pass = vectorize_pass_id();

    if let Some(extension_inst) = reduction.extension_inst {
        let extension = func.inst_mut(extension_inst);
        extension.opcode = AArch64Opcode::Nop;
        extension.operands.clear();
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_in_place_transform(extension_inst, pass.clone());
        }
    }
    if let Some(writeback_inst) = reduction.writeback_inst {
        if let Some(address) = stack_writeback_address {
            let writeback = func.inst_mut(writeback_inst);
            writeback.operands = vec![
                MachOperand::VReg(reduction.accumulator),
                MachOperand::VReg(address),
                MachOperand::Imm(0),
            ];
        } else {
            let writeback = func.inst_mut(writeback_inst);
            writeback.opcode = AArch64Opcode::Nop;
            writeback.operands.clear();
        }
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_in_place_transform(writeback_inst, pass.clone());
        }
    }
    if let Some(accumulator_load_inst) = reduction.accumulator_load_inst
        && stack_writeback_address.is_none()
    {
        let load = func.inst_mut(accumulator_load_inst);
        load.opcode = AArch64Opcode::Nop;
        load.operands.clear();
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_in_place_transform(accumulator_load_inst, pass.clone());
        }
    }

    let with_reducer_source_loc = |mut inst: MachInst| {
        inst.source_loc = reducer_source_loc;
        inst
    };

    let mut created = Vec::new();
    let lane_count = match reduction.kind {
        OrderedSubReductionKind::I32ZextToI64 => vf,
        OrderedSubReductionKind::I64 => 2,
    };

    for lane in 0..lane_count {
        let idx = lane as usize;
        let extracted_class = match reduction.kind {
            OrderedSubReductionKind::I32ZextToI64 => RegClass::Gpr32,
            OrderedSubReductionKind::I64 => RegClass::Gpr64,
        };
        let extracted = alloc_fresh_vreg(func, extracted_class);
        let element_size = match reduction.kind {
            OrderedSubReductionKind::I32ZextToI64 => 4,
            OrderedSubReductionKind::I64 => 8,
        };

        let umov_inst = with_reducer_source_loc(MachInst::new(
            AArch64Opcode::NeonUmovGen,
            vec![
                MachOperand::VReg(extracted),
                MachOperand::VReg(vector_value),
                MachOperand::Imm(i64::from(lane)),
                MachOperand::Imm(element_size),
            ],
        ));

        let umov_id = if idx == 0 {
            let reducer_inst = func.inst_mut(reduction.reducer_inst);
            *reducer_inst = umov_inst;
            reduction.reducer_inst
        } else {
            let id = func.push_inst(umov_inst);
            created.push(id);
            id
        };

        let subtract_value = if reduction.kind == OrderedSubReductionKind::I32ZextToI64 {
            let widened = alloc_fresh_vreg(func, RegClass::Gpr64);
            let uxtw_id = func.push_inst(with_reducer_source_loc(MachInst::new(
                AArch64Opcode::Uxtw,
                vec![MachOperand::VReg(widened), MachOperand::VReg(extracted)],
            )));
            created.push(uxtw_id);
            widened
        } else {
            extracted
        };

        let sub_id = func.push_inst(with_reducer_source_loc(MachInst::new(
            AArch64Opcode::SubRR,
            vec![
                MachOperand::VReg(reduction.accumulator),
                MachOperand::VReg(reduction.accumulator),
                MachOperand::VReg(subtract_value),
            ],
        )));
        created.push(sub_id);

        if idx == 0 && umov_id != reduction.reducer_inst {
            return None;
        }
    }

    if !created.is_empty() && !insert_after_inst(func, reduction.reducer_inst, &created) {
        return None;
    }

    if let Some(provenance) = provenance {
        provenance.record_in_place_transform(reduction.reducer_inst, pass.clone());
        for inst_id in created {
            if provenance.get_entry(reduction.reducer_inst).is_some() {
                provenance.record_clone(reduction.reducer_inst, inst_id, pass.clone());
            } else {
                provenance.record_creation(
                    inst_id,
                    pass.clone(),
                    "vectorize ordered subtract scalar bridge",
                );
            }
        }
    }

    Some(match reduction.kind {
        OrderedSubReductionKind::I32ZextToI64 => 1 + vf * 2,
        OrderedSubReductionKind::I64 => 4,
    })
}

fn rewrite_compare_idiom_to_neon(
    func: &mut MachFunction,
    idiom: VectorCompareIdiom,
    reg_map: &mut HashMap<u32, trust_cg_ir::VReg>,
    element_type: VecElementType,
    arrangement: NeonArrangement,
    provenance: Option<&mut ProvenanceMap>,
) -> Option<CompareRewriteResult> {
    let cmp_operands = func.inst(idiom.cmp_inst).operands.clone();
    let cset_operands = func.inst(idiom.cset_inst).operands.clone();
    if cmp_operands.len() != 2 || cset_operands.len() != 2 {
        return None;
    }

    let (MachOperand::VReg(lhs), MachOperand::VReg(rhs), MachOperand::VReg(dst)) =
        (&cmp_operands[0], &cmp_operands[1], &cset_operands[0])
    else {
        return None;
    };

    let mut regs_upgraded = 0;
    let new_dst = upgrade_vreg_to_simd(func, dst, reg_map, element_type);
    if new_dst != *dst {
        regs_upgraded += 1;
    }
    let new_lhs = upgrade_vreg_to_simd(func, lhs, reg_map, element_type);
    if new_lhs != *lhs {
        regs_upgraded += 1;
    }
    let new_rhs = upgrade_vreg_to_simd(func, rhs, reg_map, element_type);
    if new_rhs != *rhs {
        regs_upgraded += 1;
    }

    let cmp_inst = func.inst_mut(idiom.cmp_inst);
    cmp_inst.opcode = match idiom.kind {
        VectorCompareKind::I32Eq => AArch64Opcode::NeonCmeqV,
    };
    cmp_inst.operands = vec![
        MachOperand::VReg(new_dst),
        MachOperand::VReg(new_lhs),
        MachOperand::VReg(new_rhs),
        MachOperand::Imm(neon_int_arrangement_encoding(arrangement)),
    ];

    let cset_inst = func.inst_mut(idiom.cset_inst);
    cset_inst.opcode = AArch64Opcode::Nop;
    cset_inst.operands.clear();

    if let Some(provenance) = provenance
        && (provenance.get_entry(idiom.cmp_inst).is_some()
            || provenance.get_entry(idiom.cset_inst).is_some())
    {
        provenance.record_merge(
            &[idiom.cmp_inst, idiom.cset_inst],
            idiom.cmp_inst,
            vectorize_pass_id(),
        );
    }

    Some(CompareRewriteResult { regs_upgraded })
}

fn rewrite_bitreverse_to_neon(
    func: &mut MachFunction,
    inst_id: InstId,
    reg_map: &mut HashMap<u32, trust_cg_ir::VReg>,
    element_type: VecElementType,
    lanes: u32,
    provenance: Option<&mut ProvenanceMap>,
) -> Option<u32> {
    let (rev_opcode, _rev_op, byte_arrangement, _byte_cost_arrangement) =
        vector_bitreverse_byte_arrangement_for_lanes(element_type, lanes)?;
    let operands = func.inst(inst_id).operands.clone();
    if operands.len() != 2 {
        return None;
    }
    let (MachOperand::VReg(dst), MachOperand::VReg(src)) = (&operands[0], &operands[1]) else {
        return None;
    };

    let mut regs_upgraded = 0;
    let new_dst = upgrade_vreg_to_simd(func, dst, reg_map, element_type);
    if new_dst != *dst {
        regs_upgraded += 1;
    }
    let new_src = upgrade_vreg_to_simd(func, src, reg_map, element_type);
    if new_src != *src {
        regs_upgraded += 1;
    }
    let tmp = alloc_fresh_vreg(func, RegClass::Fpr128);
    let source_loc = func.inst(inst_id).source_loc;

    let rev_inst = func.inst_mut(inst_id);
    rev_inst.opcode = rev_opcode;
    rev_inst.operands = vec![
        MachOperand::VReg(tmp),
        MachOperand::VReg(new_src),
        MachOperand::Imm(byte_arrangement),
    ];

    let rbit_id = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonRbitV,
            vec![
                MachOperand::VReg(new_dst),
                MachOperand::VReg(tmp),
                MachOperand::Imm(byte_arrangement),
            ],
        ),
        source_loc,
    ));
    if !insert_after_inst(func, inst_id, &[rbit_id]) {
        return None;
    }

    if let Some(provenance) = provenance {
        let pass = vectorize_pass_id();
        provenance.record_in_place_transform(inst_id, pass.clone());
        provenance.record_creation(rbit_id, pass, "vectorize bitreverse byte rbit");
    }

    Some(regs_upgraded)
}

struct InductionRewriteResult {
    created: Vec<InstId>,
    rewritten: Vec<InstId>,
    step_inst: InstId,
    lanes: VReg,
    wide_lanes: Option<VReg>,
}

fn first_vectorized_use_of_vreg(
    func: &MachFunction,
    insts: &[InstId],
    vreg_id: u32,
) -> Option<InstId> {
    insts
        .iter()
        .copied()
        .find(|&inst_id| inst_source_uses_vreg(func.inst(inst_id), vreg_id))
}

fn materialize_vf4_i32_induction(
    func: &mut MachFunction,
    induction: VectorInduction,
    vectorizable_insts: &[InstId],
) -> Option<InductionRewriteResult> {
    const ELEMENT_SIZE_S: i64 = 4;
    let insert_before =
        first_vectorized_use_of_vreg(func, vectorizable_insts, induction.scalar_current.id)?;
    let source_loc = func.inst(insert_before).source_loc;
    let lanes = alloc_fresh_vreg(func, RegClass::Fpr128);
    let lane_values: [VReg; 3] = std::array::from_fn(|_| alloc_fresh_vreg(func, RegClass::Gpr32));

    let mut created = Vec::new();
    let seed = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonDupGen,
            vec![
                MachOperand::VReg(lanes),
                MachOperand::VReg(induction.scalar_current),
                MachOperand::Imm(ELEMENT_SIZE_S),
            ],
        ),
        source_loc,
    ));
    created.push(seed);

    for lane in 1..4 {
        let lane_value = lane_values[lane - 1];
        let add_lane = func.push_inst(with_source_loc(
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::VReg(lane_value),
                    MachOperand::VReg(induction.scalar_current),
                    MachOperand::Imm(lane as i64),
                ],
            ),
            source_loc,
        ));
        let insert_lane = func.push_inst(with_source_loc(
            MachInst::new(
                AArch64Opcode::NeonInsGen,
                vec![
                    MachOperand::VReg(lanes),
                    MachOperand::VReg(lane_value),
                    MachOperand::Imm(lane as i64),
                    MachOperand::Imm(ELEMENT_SIZE_S),
                ],
            ),
            source_loc,
        ));
        created.extend([add_lane, insert_lane]);
    }

    if !insert_before_inst(func, insert_before, &created) {
        return None;
    }

    let step = func.inst_mut(induction.step_inst);
    if step.opcode != AArch64Opcode::AddRI || step.operands.len() != 3 {
        return None;
    }
    step.operands[2] = MachOperand::Imm(4);

    Some(InductionRewriteResult {
        created,
        rewritten: Vec::new(),
        step_inst: induction.step_inst,
        lanes,
        wide_lanes: None,
    })
}

fn materialize_vf2_mixed_i32_i64_induction(
    func: &mut MachFunction,
    induction: VectorInduction,
    vectorizable_insts: &[InstId],
) -> Option<InductionRewriteResult> {
    const ELEMENT_SIZE_S: i64 = 4;
    const ELEMENT_SIZE_D: i64 = 8;
    let insert_before =
        first_vectorized_use_of_vreg(func, vectorizable_insts, induction.scalar_current.id)
            .or_else(|| {
                induction.scalar_current_alias.and_then(|alias| {
                    first_vectorized_use_of_vreg(func, vectorizable_insts, alias.id)
                })
            })
            .or_else(|| {
                induction.sign_extended_current.and_then(|wide| {
                    first_vectorized_use_of_vreg(func, vectorizable_insts, wide.id)
                })
            })?;
    let sign_extend_inst = induction.sign_extend_inst?;
    let source_loc = func.inst(insert_before).source_loc;

    let narrow_lanes = alloc_fresh_vreg(func, RegClass::Fpr128);
    let wide_lanes = alloc_fresh_vreg(func, RegClass::Fpr128);
    let lane0_i64 = alloc_fresh_vreg(func, RegClass::Gpr64);
    let lane1_i32 = alloc_fresh_vreg(func, RegClass::Gpr32);
    let lane1_i64 = alloc_fresh_vreg(func, RegClass::Gpr64);

    let mut created = Vec::new();
    let seed_narrow = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonDupGen,
            vec![
                MachOperand::VReg(narrow_lanes),
                MachOperand::VReg(induction.scalar_current),
                MachOperand::Imm(ELEMENT_SIZE_S),
            ],
        ),
        source_loc,
    ));
    let sxtw_lane0 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::Sxtw,
            vec![
                MachOperand::VReg(lane0_i64),
                MachOperand::VReg(induction.scalar_current),
            ],
        ),
        source_loc,
    ));
    let seed_wide = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonDupGen,
            vec![
                MachOperand::VReg(wide_lanes),
                MachOperand::VReg(lane0_i64),
                MachOperand::Imm(ELEMENT_SIZE_D),
            ],
        ),
        source_loc,
    ));
    let add_lane1 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(lane1_i32),
                MachOperand::VReg(induction.scalar_current),
                MachOperand::Imm(1),
            ],
        ),
        source_loc,
    ));
    let insert_narrow_lane1 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonInsGen,
            vec![
                MachOperand::VReg(narrow_lanes),
                MachOperand::VReg(lane1_i32),
                MachOperand::Imm(1),
                MachOperand::Imm(ELEMENT_SIZE_S),
            ],
        ),
        source_loc,
    ));
    let sxtw_lane1 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::Sxtw,
            vec![MachOperand::VReg(lane1_i64), MachOperand::VReg(lane1_i32)],
        ),
        source_loc,
    ));
    let insert_wide_lane1 = func.push_inst(with_source_loc(
        MachInst::new(
            AArch64Opcode::NeonInsGen,
            vec![
                MachOperand::VReg(wide_lanes),
                MachOperand::VReg(lane1_i64),
                MachOperand::Imm(1),
                MachOperand::Imm(ELEMENT_SIZE_D),
            ],
        ),
        source_loc,
    ));
    created.extend([
        seed_narrow,
        sxtw_lane0,
        seed_wide,
        add_lane1,
        insert_narrow_lane1,
        sxtw_lane1,
        insert_wide_lane1,
    ]);

    if !insert_before_inst(func, insert_before, &created) {
        return None;
    }

    let step = func.inst_mut(induction.step_inst);
    if !matches!(step.opcode, AArch64Opcode::AddRI | AArch64Opcode::AddRR)
        || step.operands.len() != 3
    {
        return None;
    }
    step.opcode = AArch64Opcode::AddRI;
    step.operands[1] = MachOperand::VReg(induction.scalar_current);
    step.operands[2] = MachOperand::Imm(2);

    let sign_extend = func.inst_mut(sign_extend_inst);
    sign_extend.opcode = AArch64Opcode::Nop;
    sign_extend.operands.clear();

    Some(InductionRewriteResult {
        created,
        rewritten: vec![sign_extend_inst],
        step_inst: induction.step_inst,
        lanes: narrow_lanes,
        wide_lanes: Some(wide_lanes),
    })
}

/// Apply a vectorization plan to a machine function.
///
/// This rewrites the IR by:
/// 1. Replacing scalar instructions with NEON equivalents (same opcode,
///    upgraded register classes + arrangement immediate).
/// 2. Upgrading register classes from GPR to Fpr128 (SIMD) for all
///    operands of vectorized instructions.
/// 3. Adjusting the loop trip count comparison: divides by the
///    vectorization factor so each vector iteration processes `vf` elements.
/// 4. Creating a scalar epilogue block for remainder iterations
///    (trip_count % vf) when the trip count is not evenly divisible.
///
/// # Arguments
/// - `func`: The machine function to modify.
/// - `plan`: The vectorization plan describing what and how to vectorize.
///
/// # Returns
/// A `VectorizationResult` summarizing what was changed, or `None` if
/// the plan cannot be applied (e.g., not profitable, no vectorizable insts).
pub fn apply_vectorization(
    func: &mut MachFunction,
    plan: &VectorizationPlan,
) -> Option<VectorizationResult> {
    apply_vectorization_impl(func, plan, None)
}

fn apply_vectorization_impl(
    func: &mut MachFunction,
    plan: &VectorizationPlan,
    mut provenance: Option<&mut ProvenanceMap>,
) -> Option<VectorizationResult> {
    if !plan.is_profitable || (plan.vectorizable_insts.is_empty() && plan.compare_idioms.is_empty())
    {
        return None;
    }

    if plan.compare_idioms.iter().any(|idiom| {
        !compare_idiom_uses_are_vectorizable(func, *idiom, &plan.horizontal_any_reductions)
    }) {
        return None;
    }

    let vf = plan.vf;
    let element_type = plan.element_type;

    let mut insts_rewritten: u32 = 0;
    let mut compare_idioms_rewritten: u32 = 0;
    let mut regs_upgraded: u32 = 0;
    let mut reg_map: HashMap<u32, trust_cg_ir::VReg> = HashMap::new();
    let scalar_epilogue_sources = capture_scalar_epilogue_sources(func, plan);
    let reduction_compare_result_ids: HashMap<InstId, u32> = plan
        .horizontal_any_reductions
        .iter()
        .filter_map(|reduction| {
            def_vreg_id(func.inst(reduction.compare.cset_inst))
                .map(|result_id| (reduction.reducer_inst, result_id))
        })
        .collect();

    if let Some(induction) = plan.induction {
        let rewrite = match (plan.element_type, plan.vf, induction.sign_extend_inst) {
            (VecElementType::I32, 4, _) => {
                materialize_vf4_i32_induction(func, induction, &plan.vectorizable_insts)?
            }
            (VecElementType::I64, 2, Some(_)) => {
                materialize_vf2_mixed_i32_i64_induction(func, induction, &plan.vectorizable_insts)?
            }
            _ => return None,
        };
        reg_map.insert(induction.scalar_current.id, rewrite.lanes);
        if let Some(alias) = induction.scalar_current_alias {
            reg_map.insert(alias.id, rewrite.lanes);
        }
        if let (Some(sign_extended_current), Some(wide_lanes)) =
            (induction.sign_extended_current, rewrite.wide_lanes)
        {
            reg_map.insert(sign_extended_current.id, wide_lanes);
        }
        insts_rewritten += 1;
        if let Some(provenance) = provenance.as_deref_mut() {
            let pass = vectorize_pass_id();
            provenance.record_in_place_transform(rewrite.step_inst, pass.clone());
            for inst_id in rewrite.rewritten {
                provenance.record_in_place_transform(inst_id, pass.clone());
            }
            for inst_id in rewrite.created {
                provenance.record_creation(inst_id, pass.clone(), "vectorize i32 induction lanes");
            }
        }
    }

    // Step 1: Rewrite vectorizable instructions — upgrade register classes
    // and append arrangement encoding.
    for &inst_id in &plan.vectorizable_insts {
        if func.inst(inst_id).opcode == AArch64Opcode::Rbit {
            let inst_element_type = infer_element_type(func, inst_id).unwrap_or(element_type);
            let inst_lanes = if plan.induction.is_some()
                && element_type == VecElementType::I64
                && inst_element_type == VecElementType::I32
            {
                vf
            } else {
                inst_element_type.lanes()
            };
            let Some(upgraded) = rewrite_bitreverse_to_neon(
                func,
                inst_id,
                &mut reg_map,
                inst_element_type,
                inst_lanes,
                provenance.as_deref_mut(),
            ) else {
                continue;
            };
            regs_upgraded += upgraded;
            insts_rewritten += 1;
            continue;
        }

        let (_neon_opcode, _neon_op) = match rewrite_opcode_for_neon(func.inst(inst_id).opcode) {
            Some(pair) => pair,
            None => continue,
        };
        let arrangement_encoding =
            arrangement_encoding_for_opcode(func.inst(inst_id).opcode, plan.arrangement);

        // Upgrade all VReg operands to SIMD register class.
        let num_operands = func.inst(inst_id).operands.len();
        for op_idx in 0..num_operands {
            let operand = func.inst(inst_id).operands[op_idx].clone();
            if let MachOperand::VReg(vreg) = &operand {
                let new_vreg = upgrade_vreg_to_simd(func, vreg, &mut reg_map, element_type);
                if new_vreg != *vreg {
                    regs_upgraded += 1;
                }
                func.inst_mut(inst_id).operands[op_idx] = MachOperand::VReg(new_vreg);
            }
        }

        // Append arrangement encoding as an immediate operand.
        // This signals to the encoder that this instruction operates on
        // NEON vectors with the specified lane layout.
        func.inst_mut(inst_id)
            .operands
            .push(MachOperand::Imm(arrangement_encoding));

        insts_rewritten += 1;

        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_in_place_transform(inst_id, vectorize_pass_id());
        }
    }

    for idiom in &plan.compare_idioms {
        let Some(rewritten) = rewrite_compare_idiom_to_neon(
            func,
            *idiom,
            &mut reg_map,
            element_type,
            plan.arrangement,
            provenance.as_deref_mut(),
        ) else {
            continue;
        };
        regs_upgraded += rewritten.regs_upgraded;
        compare_idioms_rewritten += 1;
        insts_rewritten += 1;
    }

    for &reduction in &plan.horizontal_any_reductions {
        let compare_result_id = *reduction_compare_result_ids.get(&reduction.reducer_inst)?;
        let rewritten = rewrite_horizontal_any_reduction_to_neon(
            func,
            reduction,
            compare_result_id,
            &reg_map,
            plan.arrangement,
            provenance.as_deref_mut(),
        )?;
        insts_rewritten += rewritten;
    }

    for &reduction in &plan.ordered_sub_reductions {
        let rewritten = rewrite_ordered_sub_reduction_bridge(
            func,
            reduction,
            &reg_map,
            vf,
            provenance.as_deref_mut(),
        )?;
        insts_rewritten += rewritten;
    }

    // Step 2: Adjust loop trip count comparison.
    // Find the CMP immediate in the header or latch that controls the loop,
    // and divide its immediate by the vectorization factor.
    let vector_trip_count = plan.trip_count.map(|tc| tc / vf);
    let remainder = plan.trip_count.map(|tc| tc % vf).unwrap_or(0);

    if let Some(tc) = plan.trip_count {
        let new_tc = tc / vf;
        let mut adjusted = adjust_trip_count_in_block(func, plan.loop_header, tc, new_tc);
        if plan.loop_latch != plan.loop_header {
            adjusted.extend(adjust_trip_count_in_block(
                func,
                plan.loop_latch,
                tc,
                new_tc,
            ));
        }
        for inst_id in adjusted {
            if let Some(provenance) = provenance.as_deref_mut() {
                provenance.record_in_place_transform(inst_id, vectorize_pass_id());
            }
        }
    }

    // Step 3: Create scalar epilogue for remainder iterations.
    let has_epilogue = remainder > 0 && !plan.vectorizable_insts.is_empty();
    if has_epilogue {
        let epilogue_insts = create_scalar_epilogue(
            func,
            plan,
            remainder,
            vector_trip_count,
            &scalar_epilogue_sources,
        )?;
        if let Some(provenance) = provenance {
            let pass = vectorize_pass_id();
            for (source_id, clone_id) in epilogue_insts.cloned {
                if provenance.get_entry(source_id).is_some() {
                    provenance.record_clone(source_id, clone_id, pass.clone());
                } else {
                    provenance.record_creation(clone_id, pass.clone(), "vectorize scalar epilogue");
                }
            }
            for inst_id in epilogue_insts.generated {
                provenance.record_creation(inst_id, pass.clone(), "vectorize scalar epilogue");
            }
        }
    }

    Some(VectorizationResult {
        insts_rewritten,
        compare_idioms_rewritten,
        horizontal_reductions_recognized: plan.horizontal_any_reductions.len() as u32,
        ordered_sub_reductions_recognized: plan.ordered_sub_reductions.len() as u32,
        regs_upgraded,
        has_epilogue,
        vector_trip_count,
        remainder,
    })
}

/// Adjust the CMP immediate in a block to reflect the new vector trip count.
///
/// Finds CMP immediate instructions comparing against `old_tc` and replaces
/// the immediate with `new_tc`.
fn adjust_trip_count_in_block(
    func: &mut MachFunction,
    block_id: BlockId,
    old_tc: u32,
    new_tc: u32,
) -> Vec<InstId> {
    let block = func.block(block_id);
    let inst_ids: Vec<InstId> = block.insts.clone();
    let mut adjusted = Vec::new();

    for inst_id in inst_ids {
        let inst = func.inst(inst_id);
        match inst.opcode {
            AArch64Opcode::CmpRI | AArch64Opcode::CMPWri | AArch64Opcode::CMPXri => {
                let num_ops = inst.operands.len();
                let mut inst_adjusted = false;
                for op_idx in 0..num_ops {
                    let operand = func.inst(inst_id).operands[op_idx].clone();
                    if let MachOperand::Imm(val) = operand
                        && val == old_tc as i64
                    {
                        func.inst_mut(inst_id).operands[op_idx] = MachOperand::Imm(new_tc as i64);
                        inst_adjusted = true;
                    }
                }
                if inst_adjusted {
                    adjusted.push(inst_id);
                }
            }
            _ => {}
        }
    }

    adjusted
}

struct ScalarEpilogueInsts {
    cloned: Vec<(InstId, InstId)>,
    generated: Vec<InstId>,
}

#[derive(Clone)]
struct ScalarEpilogueSource {
    source_id: InstId,
    opcode: AArch64Opcode,
    operands: Vec<MachOperand>,
    source_loc: Option<trust_cg_ir::SourceLoc>,
}

fn capture_scalar_epilogue_sources(
    func: &MachFunction,
    plan: &VectorizationPlan,
) -> Vec<ScalarEpilogueSource> {
    plan.vectorizable_insts
        .iter()
        .map(|&source_id| {
            let inst = func.inst(source_id);
            ScalarEpilogueSource {
                source_id,
                opcode: inst.opcode,
                operands: inst.operands.clone(),
                source_loc: inst.source_loc,
            }
        })
        .collect()
}

fn scalar_reg_class_for_element(element_type: VecElementType) -> RegClass {
    match element_type {
        VecElementType::I8 | VecElementType::I16 | VecElementType::I32 => RegClass::Gpr32,
        VecElementType::I64 => RegClass::Gpr64,
        VecElementType::F32 => RegClass::Fpr32,
        VecElementType::F64 => RegClass::Fpr64,
    }
}

fn scalar_epilogue_vreg(
    func: &mut MachFunction,
    vreg: VReg,
    is_def: bool,
    element_type: VecElementType,
    vreg_map: &mut HashMap<u32, VReg>,
) -> VReg {
    if is_def {
        let scalar_vreg = alloc_fresh_vreg(func, scalar_reg_class_for_element(element_type));
        vreg_map.insert(vreg.id, scalar_vreg);
        return scalar_vreg;
    }

    if let Some(&scalar_vreg) = vreg_map.get(&vreg.id) {
        return scalar_vreg;
    }

    let scalar_vreg = alloc_fresh_vreg(func, scalar_reg_class_for_element(element_type));
    vreg_map.insert(vreg.id, scalar_vreg);
    scalar_vreg
}

fn clone_scalar_epilogue_source(
    func: &mut MachFunction,
    epilogue_block: BlockId,
    source: &ScalarEpilogueSource,
    element_type: VecElementType,
    vreg_map: &mut HashMap<u32, VReg>,
) -> InstId {
    let scalar_ops = source
        .operands
        .iter()
        .enumerate()
        .map(|(idx, operand)| match operand {
            MachOperand::VReg(vreg) => {
                let is_def = idx == 0 && produces_value(source.opcode);
                MachOperand::VReg(scalar_epilogue_vreg(
                    func,
                    *vreg,
                    is_def,
                    element_type,
                    vreg_map,
                ))
            }
            other => other.clone(),
        })
        .collect();

    let mut epilogue_inst = trust_cg_ir::MachInst::new(source.opcode, scalar_ops);
    epilogue_inst.source_loc = source.source_loc;
    let new_inst_id = func.push_inst(epilogue_inst);
    func.append_inst(epilogue_block, new_inst_id);
    new_inst_id
}

/// Create a scalar epilogue block that handles remainder iterations.
///
/// The epilogue is a simple block containing copies of the original scalar
/// vectorizable instructions. For vector-induction plans, the epilogue is
/// unrolled over the concrete remainder lanes so each scalar replay consumes
/// the post-vector induction value (`i + vector_iters * VF + lane`).
fn create_scalar_epilogue(
    func: &mut MachFunction,
    plan: &VectorizationPlan,
    remainder: u32,
    vector_trip_count: Option<u32>,
    sources: &[ScalarEpilogueSource],
) -> Option<ScalarEpilogueInsts> {
    let mut cloned = Vec::new();
    let mut generated = Vec::new();

    // Create the epilogue block.
    let epilogue_block = func.create_block();

    if let Some(induction) = plan.induction {
        let vector_base = vector_trip_count? * plan.vf;
        let source_loc = sources.first().and_then(|source| source.source_loc);

        for lane in 0..remainder {
            let mut vreg_map = HashMap::new();
            let scalar_induction = alloc_fresh_vreg(func, RegClass::Gpr32);
            let induction_value = func.push_inst(with_source_loc(
                MachInst::new(
                    AArch64Opcode::AddRI,
                    vec![
                        MachOperand::VReg(scalar_induction),
                        MachOperand::VReg(induction.scalar_current),
                        MachOperand::Imm((vector_base + lane) as i64),
                    ],
                ),
                source_loc,
            ));
            func.append_inst(epilogue_block, induction_value);
            generated.push(induction_value);
            vreg_map.insert(induction.scalar_current.id, scalar_induction);

            for source in sources {
                let clone_id = clone_scalar_epilogue_source(
                    func,
                    epilogue_block,
                    source,
                    plan.element_type,
                    &mut vreg_map,
                );
                cloned.push((source.source_id, clone_id));
            }
        }

        let epilogue_exit = func.create_block();
        let ret_inst = trust_cg_ir::MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret_inst);
        func.append_inst(epilogue_exit, ret_id);
        generated.push(ret_id);

        let branch_id = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(epilogue_exit)],
        ));
        func.append_inst(epilogue_block, branch_id);
        generated.push(branch_id);

        func.add_edge(epilogue_block, epilogue_exit);
        return Some(ScalarEpilogueInsts { cloned, generated });
    }

    // Clone the vectorizable instructions into the epilogue block
    // in their original scalar form.
    let mut vreg_map = HashMap::new();
    for source in sources {
        let clone_id = clone_scalar_epilogue_source(
            func,
            epilogue_block,
            source,
            plan.element_type,
            &mut vreg_map,
        );
        cloned.push((source.source_id, clone_id));
    }

    // Add a CMP + BCond to loop the epilogue `remainder` times,
    // or if remainder is small enough, just unroll (for simplicity,
    // we add a CMP against the remainder count).
    let counter_vreg = alloc_fresh_vreg(func, RegClass::Gpr32);

    let cmp_inst = trust_cg_ir::MachInst::new(
        AArch64Opcode::CmpRI,
        vec![
            MachOperand::VReg(counter_vreg),
            MachOperand::Imm(remainder as i64),
        ],
    );
    let cmp_id = func.push_inst(cmp_inst);
    func.append_inst(epilogue_block, cmp_id);
    generated.push(cmp_id);

    // Create an exit block for the epilogue.
    let epilogue_exit = func.create_block();
    let ret_inst = trust_cg_ir::MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret_inst);
    func.append_inst(epilogue_exit, ret_id);
    generated.push(ret_id);

    // Conditional branch: loop back or exit.
    let bcond_inst = trust_cg_ir::MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Block(epilogue_exit),
            MachOperand::Block(epilogue_block),
        ],
    );
    let bcond_id = func.push_inst(bcond_inst);
    func.append_inst(epilogue_block, bcond_id);
    generated.push(bcond_id);

    // Wire up CFG edges.
    func.add_edge(epilogue_block, epilogue_exit);
    func.add_edge(epilogue_block, epilogue_block); // self-loop for remainder

    Some(ScalarEpilogueInsts { cloned, generated })
}

// ---------------------------------------------------------------------------
// VectorizationPass — MachinePass implementation
// ---------------------------------------------------------------------------

/// NEON auto-vectorization pass.
///
/// Analyzes loops for vectorization opportunities, builds vectorization
/// plans, and rewrites the IR to use NEON SIMD instructions for profitable
/// loops. Scalar epilogue blocks are generated for remainder iterations
/// when the trip count is not evenly divisible by the vectorization factor.
///
/// The pass operates in two phases:
/// 1. **Analysis**: Detect vectorizable loops, compute profitability.
/// 2. **Rewriting**: Replace scalar instructions with NEON equivalents,
///    adjust trip counts, create epilogue blocks.
pub struct VectorizationPass {
    /// Apple Silicon generation for cost modeling.
    generation: CostModelGen,
    /// Minimum trip count for vectorization to be considered.
    min_trip_count: u32,
    /// Loaded profile hotness summary used for bounded hot-loop thresholds.
    profile_hotness: Option<ProfileHotness>,
    /// Enables the experimental scanner-memory contains4 rewrite.
    enable_contains4_scanner_memory_rewrite: bool,
    /// Enables the inlined/batch scanner contains4 backend rewrite.
    enable_contains4_scanner_batch_rewrite: bool,
    /// Proof facts sidecar transported from trust_ir/import metadata.
    proof_facts: HashMap<InstId, Vec<ProofFact>>,
    /// Collected vectorization plans (for diagnostics/testing).
    plans: Vec<VectorizationPlan>,
    /// Results from the last rewriting phase (for diagnostics/testing).
    results: Vec<VectorizationResult>,
    /// Reverse accumulation candidates and their proof-gate status.
    reverse_accumulation_reports: Vec<ReverseAccumulationProofReport>,
    /// Proof optimization certificates emitted for proof-gated vector rewrites.
    proof_certificates: Vec<OptCertificate>,
}

impl VectorizationPass {
    /// Create a new vectorization pass with default settings (M1, min trip count 8).
    pub fn new() -> Self {
        Self {
            generation: CostModelGen::M1,
            min_trip_count: DEFAULT_MIN_TRIP_COUNT,
            profile_hotness: None,
            enable_contains4_scanner_memory_rewrite: contains4_scanner_memory_rewrite_env_enabled(),
            enable_contains4_scanner_batch_rewrite: contains4_scanner_batch_rewrite_env_enabled(),
            proof_facts: HashMap::new(),
            plans: Vec::new(),
            results: Vec::new(),
            reverse_accumulation_reports: Vec::new(),
            proof_certificates: Vec::new(),
        }
    }

    /// Create a vectorization pass with custom settings.
    pub fn with_config(generation: CostModelGen, min_trip_count: u32) -> Self {
        Self {
            generation,
            min_trip_count,
            profile_hotness: None,
            enable_contains4_scanner_memory_rewrite: contains4_scanner_memory_rewrite_env_enabled(),
            enable_contains4_scanner_batch_rewrite: contains4_scanner_batch_rewrite_env_enabled(),
            proof_facts: HashMap::new(),
            plans: Vec::new(),
            results: Vec::new(),
            reverse_accumulation_reports: Vec::new(),
            proof_certificates: Vec::new(),
        }
    }

    /// Attach profile hotness used to lower the trip-count gate for hot loops.
    pub fn with_profile_hotness(mut self, profile_hotness: Option<ProfileHotness>) -> Self {
        self.profile_hotness = profile_hotness;
        self
    }

    /// Enable or disable the experimental scanner-memory contains4 rewrite.
    pub fn with_contains4_scanner_memory_rewrite(mut self, enabled: bool) -> Self {
        self.enable_contains4_scanner_memory_rewrite = enabled;
        self
    }

    /// Enable or disable the inlined/batch scanner contains4 rewrite.
    pub fn with_contains4_scanner_batch_rewrite(mut self, enabled: bool) -> Self {
        self.enable_contains4_scanner_batch_rewrite = enabled;
        self
    }

    /// Returns the collected vectorization plans from the last run.
    pub fn plans(&self) -> &[VectorizationPlan] {
        &self.plans
    }

    /// Returns the rewriting results from the last run.
    pub fn results(&self) -> &[VectorizationResult] {
        &self.results
    }

    /// Returns proof-gate reports for reverse accumulation candidates.
    pub fn reverse_accumulation_reports(&self) -> &[ReverseAccumulationProofReport] {
        &self.reverse_accumulation_reports
    }

    /// Returns proof certificates emitted for proof-gated vector rewrites.
    pub fn proof_certificates(&self) -> &[OptCertificate] {
        &self.proof_certificates
    }

    fn record_reverse_accumulation_certificate(&mut self, func: &MachFunction) {
        if let Some(report) = self
            .reverse_accumulation_reports
            .iter()
            .find(|report| report.rejection.is_none())
        {
            self.proof_certificates
                .push(reverse_vectorization_certificate(func, report));
        }
    }

    fn run_with_loop_analysis(
        &mut self,
        func: &mut MachFunction,
        loop_analysis: &LoopAnalysis,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        self.plans.clear();
        self.results.clear();
        self.proof_certificates.clear();
        // Nothing has mutated `func` yet, so one map serves both the report
        // sweep and the contains4 idiom scan (the scan runs before any SLP
        // rewrite fires). Dropped right after: every later phase may mutate
        // the function and must build its own map.
        let defs = build_def_map(func);
        self.reverse_accumulation_reports =
            reverse_accumulation_reports(func, loop_analysis, &self.proof_facts, &defs);

        let slp_results = rewrite_contains4_masked_slp(
            func,
            self.enable_contains4_scanner_memory_rewrite,
            self.enable_contains4_scanner_batch_rewrite,
            provenance.as_deref_mut(),
            &defs,
        );
        drop(defs);
        let mut changed = !slp_results.is_empty();
        self.results.extend(slp_results);

        if loop_analysis.is_empty() {
            return changed;
        }

        let store_loop_results =
            rewrite_i32_induction_store_loops(func, loop_analysis, provenance.as_deref_mut());
        if !store_loop_results.is_empty() {
            self.results.extend(store_loop_results);
            let dom = DomTree::compute(func);
            let refreshed_loop_analysis = LoopAnalysis::compute(func, &dom);
            // The store-loop rewrite mutated the function; the entry map is
            // stale, so this sweep gets a fresh one.
            let defs = build_def_map(func);
            self.reverse_accumulation_reports = reverse_accumulation_reports(
                func,
                &refreshed_loop_analysis,
                &self.proof_facts,
                &defs,
            );
            if refreshed_loop_analysis.is_empty() {
                return true;
            }
            let reverse_accumulation_results = rewrite_reverse_accumulation_loops(
                func,
                &refreshed_loop_analysis,
                &self.proof_facts,
                provenance.as_deref_mut(),
            );
            if !reverse_accumulation_results.is_empty() {
                self.results.extend(reverse_accumulation_results);
                self.record_reverse_accumulation_certificate(func);
            }
            return true;
        }

        let reverse_accumulation_results = rewrite_reverse_accumulation_loops(
            func,
            loop_analysis,
            &self.proof_facts,
            provenance.as_deref_mut(),
        );
        if !reverse_accumulation_results.is_empty() {
            self.results.extend(reverse_accumulation_results);
            self.record_reverse_accumulation_certificate(func);
            return true;
        }

        let cost_model = MultiTargetCostModel::new(self.generation);

        // Process loops innermost-first (higher depth first).
        let mut loops: Vec<_> = loop_analysis.all_loops().cloned().collect();
        loops.sort_by_key(|lp| std::cmp::Reverse(lp.depth));

        // One map pair for the whole sweep instead of two per loop. Rebuilt
        // only where the function actually changes — see the rewrite arm below.
        let mut maps = VecMaps::build(func);

        for lp in &loops {
            if let Some(plan) = analyze_loop_with(func, lp, &cost_model, &maps) {
                // Check minimum trip count threshold.
                let min_trip_count = self.min_trip_count_for_loop(func, lp);
                let tc = plan.trip_count.unwrap_or(0);
                if tc < min_trip_count && plan.trip_count.is_some() {
                    // Known small trip count: skip.
                    self.plans.push(plan);
                    continue;
                }

                if plan.is_profitable {
                    // Apply the vectorization rewrite.
                    if let Some(result) =
                        apply_vectorization_impl(func, &plan, provenance.as_deref_mut())
                    {
                        if result.insts_rewritten > 0 {
                            changed = true;
                        }
                        // The rewrite appended to the arena and redefined
                        // vregs, so the shared maps no longer describe the
                        // function. Rebuild before the next loop is analyzed.
                        maps = VecMaps::build(func);
                        self.results.push(result);
                    }
                }

                self.plans.push(plan);
            }
        }

        changed
    }

    fn min_trip_count_for_loop(&self, func: &MachFunction, lp: &NaturalLoop) -> u32 {
        let Some(block_hotness) = self
            .profile_hotness
            .as_ref()
            .and_then(|hotness| hotness.block(&func.name, lp.header))
        else {
            return self.min_trip_count;
        };

        if block_hotness.class.is_hot() {
            self.min_trip_count.min(HOT_MIN_TRIP_COUNT)
        } else {
            self.min_trip_count
        }
    }
}

impl Default for VectorizationPass {
    fn default() -> Self {
        Self::new()
    }
}

impl MachinePass for VectorizationPass {
    fn name(&self) -> &str {
        "vectorize"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        self.run_with_loop_analysis(func, &loop_analysis, None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        self.run_with_loop_analysis(func, &loop_analysis, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        self.run_with_loop_analysis(func, &loop_analysis, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        self.run_with_loop_analysis(func, &loop_analysis, Some(provenance))
    }

    fn set_proof_optimization_metadata(&mut self, metadata: &ProofOptimizationMetadata) {
        if trust_cg_lower::guard_evidence::validator_guard_replay_authority_available()
            || cfg!(test)
        {
            self.proof_facts = metadata.proof_facts().clone();
        } else {
            self.proof_facts.clear();
        }
    }

    fn take_proof_optimization_certificates(&mut self) -> Vec<OptCertificate> {
        std::mem::take(&mut self.proof_certificates)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dom::DomTree;
    use crate::loops::LoopAnalysis;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use crate::pgo::{BlockProfile, FunctionProfile, ProfData};
    use trust_cg_ir::{
        AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
        ProvenanceStatus, RegClass, Signature, SourceLoc, StackSlotId, TransformKind,
        TrustIrInstId, VReg,
    };

    fn vreg32(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn vreg64(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn fpreg64(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Fpr64))
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

    #[test]
    fn move_wide_constant_matchers_reject_nonzero_base_shifts() {
        let w0 = VReg::new(0, RegClass::Gpr32);
        let explicit_zero = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(w0), imm(7), imm(0)],
        );
        assert_eq!(movz_i32_imm(&explicit_zero), Some((w0, 7)));

        let shifted_movz = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(w0), imm(1), imm(16)],
        );
        assert_eq!(movz_i32_imm(&shifted_movz), None);

        let shifted_movn = MachInst::new(
            AArch64Opcode::Movn,
            vec![MachOperand::VReg(w0), imm(0), imm(16)],
        );
        assert_eq!(movn_i32_minus_one(&shifted_movn), None);

        let malformed_extra = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(w0), imm(7), imm(0), imm(0)],
        );
        assert_eq!(movz_i32_imm(&malformed_extra), None);
    }

    #[test]
    fn trip_count_does_not_recover_from_rejected_shifted_movz_seed() {
        let mut func = MachFunction::new(
            "shifted_trip_count".to_string(),
            Signature::new(vec![], vec![]),
        );
        let block = func.entry;
        let iv = VReg::new(0, RegClass::Gpr64);
        let bound = VReg::new(1, RegClass::Gpr64);
        for inst in [
            MachInst::new(
                AArch64Opcode::Movz,
                vec![MachOperand::VReg(bound), imm(1), imm(16)],
            ),
            MachInst::new(
                AArch64Opcode::Movk,
                vec![MachOperand::VReg(bound), imm(7), imm(16)],
            ),
            MachInst::new(
                AArch64Opcode::CmpRR,
                vec![MachOperand::VReg(iv), MachOperand::VReg(bound)],
            ),
        ] {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }

        assert_eq!(estimate_trip_count_in_block(&func, block), None);
    }

    /// Build a simple vectorizable add loop:
    ///
    /// ```text
    ///   bb0 (entry/preheader)
    ///    |
    ///   bb1 (header) <---+
    ///   |  add v2, v0, v1 (i32 add)
    ///   |  cmp v3, #100
    ///   |  bcond bb2, bb1
    ///    |               |
    ///   bb2 (exit)  bb1 (latch = header is self-loop pattern via bb3)
    /// ```
    ///
    /// Simplified as: bb0 -> bb1 -> bb3 (latch) -> bb1, bb1 -> bb2
    fn make_vectorizable_add_loop() -> MachFunction {
        let mut func =
            MachFunction::new("vec_add_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block(); // header
        let bb2 = func.create_block(); // exit
        let bb3 = func.create_block(); // latch

        // bb0: branch to header
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // bb1 (header): add v2 = v0 + v1 (i32)
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg32(2), vreg32(0), vreg32(1)],
        ));
        func.append_inst(bb1, add);

        // Compare v3 against trip count 100
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(3), imm(100)],
        ));
        func.append_inst(bb1, cmp);

        // Conditional branch: exit or continue
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        // bb3 (latch): back to header
        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        // bb2 (exit): return
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        func
    }

    fn make_bitreverse_loop(reg_class: RegClass) -> (MachFunction, InstId) {
        let mut func = MachFunction::new(
            "bitreverse_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let rbit = func.push_inst(MachInst::new(
            AArch64Opcode::Rbit,
            vec![
                MachOperand::VReg(VReg::new(2, reg_class)),
                MachOperand::VReg(VReg::new(0, reg_class)),
            ],
        ));
        func.append_inst(bb1, rbit);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(3), imm(64)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        (func, rbit)
    }

    fn make_i32_induction_bitreverse_loop(
        trip_count: i64,
        step: i64,
        load_current: bool,
    ) -> (MachFunction, InstId, InstId, VReg) {
        let mut func = MachFunction::new(
            "induction_bitreverse_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let current = VReg::new(10, RegClass::Gpr32);
        let next = VReg::new(12, RegClass::Gpr32);

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        if load_current {
            let load = func.push_inst(MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::VReg(current),
                    MachOperand::VReg(VReg::new(20, RegClass::Gpr64)),
                    imm(0),
                ],
            ));
            func.append_inst(bb1, load);
        }

        let rbit = func.push_inst(MachInst::new(
            AArch64Opcode::Rbit,
            vec![vreg32(11), MachOperand::VReg(current)],
        ));
        func.append_inst(bb1, rbit);

        let step_inst = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(current),
                imm(step),
            ],
        ));
        func.append_inst(bb1, step_inst);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(30), imm(trip_count)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        (func, rbit, step_inst, current)
    }

    fn make_imported_o0_i32_induction_store_loop() -> MachFunction {
        let mut func = MachFunction::new(
            "imported_o0_i32_induction_store_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let preheader = func.entry;
        let header = func.create_block();
        let body = func.create_block();
        let exit = func.create_block();
        let latch = func.create_block();

        let index = VReg::new(0, RegClass::Gpr32);
        let bound = VReg::new(1, RegClass::Gpr32);
        let one = VReg::new(2, RegClass::Gpr32);
        let value = VReg::new(3, RegClass::Gpr32);
        let wide_index = VReg::new(4, RegClass::Gpr64);
        let stride = VReg::new(5, RegClass::Gpr64);
        let base = VReg::new(6, RegClass::Gpr64);
        let address = VReg::new(7, RegClass::Gpr64);
        let next = VReg::new(8, RegClass::Gpr32);
        let bool_value = VReg::new(9, RegClass::Gpr64);

        let init_i = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(index), MachOperand::Imm(0)],
        ));
        let stride_init = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(stride), MachOperand::Imm(4)],
        ));
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        for inst in [init_i, stride_init, br0] {
            func.append_inst(preheader, inst);
        }

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRR,
            vec![MachOperand::VReg(index), MachOperand::VReg(bound)],
        ));
        let cset = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![MachOperand::VReg(bool_value), MachOperand::Imm(11)],
        ));
        let test = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(bool_value), MachOperand::Imm(0)],
        ));
        let branch_body = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(1), MachOperand::Block(body)],
        ));
        let branch_exit = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        for inst in [cmp, cset, test, branch_body, branch_exit] {
            func.append_inst(header, inst);
        }

        let one_inst = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(one), MachOperand::Imm(1)],
        ));
        let add_value = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(value),
                MachOperand::VReg(index),
                MachOperand::VReg(one),
            ],
        ));
        let sxtw = func.push_inst(MachInst::new(
            AArch64Opcode::Sxtw,
            vec![MachOperand::VReg(wide_index), MachOperand::VReg(index)],
        ));
        let madd = func.push_inst(MachInst::new(
            AArch64Opcode::Madd,
            vec![
                MachOperand::VReg(address),
                MachOperand::VReg(wide_index),
                MachOperand::VReg(stride),
                MachOperand::VReg(base),
            ],
        ));
        let store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(value),
                MachOperand::VReg(address),
                MachOperand::Imm(0),
            ],
        ));
        let body_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(latch)],
        ));
        for inst in [one_inst, add_value, sxtw, madd, store, body_branch] {
            func.append_inst(body, inst);
        }

        let step = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(index),
                MachOperand::VReg(one),
            ],
        ));
        let writeback = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(index), MachOperand::VReg(next)],
        ));
        let latch_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        for inst in [step, writeback, latch_branch] {
            func.append_inst(latch, inst);
        }

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(preheader, header);
        func.add_edge(header, body);
        func.add_edge(header, exit);
        func.add_edge(body, latch);
        func.add_edge(latch, header);

        func
    }

    fn make_imported_o0_reverse_accumulation_loop() -> (MachFunction, InstId, InstId) {
        let mut func = MachFunction::new(
            "imported_o0_reverse_accumulation_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let preheader = func.entry;
        let header = func.create_block();
        let body = func.create_block();
        let exit = func.create_block();
        let latch = func.create_block();

        let index = VReg::new(0, RegClass::Gpr32);
        let wide_index = VReg::new(1, RegClass::Gpr64);
        let stride = VReg::new(2, RegClass::Gpr64);
        let source_base = VReg::new(3, RegClass::Gpr64);
        let dest_base = VReg::new(4, RegClass::Gpr64);
        let source_addr = VReg::new(5, RegClass::Gpr64);
        let dest_addr = VReg::new(6, RegClass::Gpr64);
        let source_value = VReg::new(7, RegClass::Gpr32);
        let dest_value = VReg::new(8, RegClass::Gpr32);
        let sum = VReg::new(9, RegClass::Gpr32);
        let next = VReg::new(10, RegClass::Gpr32);

        let stride_init = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(stride), MachOperand::Imm(4)],
        ));
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        for inst in [stride_init, br0] {
            func.append_inst(preheader, inst);
        }

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(index), MachOperand::Imm(0)],
        ));
        let branch_body = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(10), MachOperand::Block(body)],
        ));
        let branch_exit = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        for inst in [cmp, branch_body, branch_exit] {
            func.append_inst(header, inst);
        }

        let sxtw = func.push_inst(MachInst::new(
            AArch64Opcode::Sxtw,
            vec![MachOperand::VReg(wide_index), MachOperand::VReg(index)],
        ));
        let source_madd = func.push_inst(MachInst::new(
            AArch64Opcode::Madd,
            vec![
                MachOperand::VReg(source_addr),
                MachOperand::VReg(wide_index),
                MachOperand::VReg(stride),
                MachOperand::VReg(source_base),
            ],
        ));
        let source_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(source_value),
                MachOperand::VReg(source_addr),
                MachOperand::Imm(0),
            ],
        ));
        let dest_madd = func.push_inst(MachInst::new(
            AArch64Opcode::Madd,
            vec![
                MachOperand::VReg(dest_addr),
                MachOperand::VReg(wide_index),
                MachOperand::VReg(stride),
                MachOperand::VReg(dest_base),
            ],
        ));
        let dest_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(dest_value),
                MachOperand::VReg(dest_addr),
                MachOperand::Imm(0),
            ],
        ));
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(sum),
                MachOperand::VReg(dest_value),
                MachOperand::VReg(source_value),
            ],
        ));
        let store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(sum),
                MachOperand::VReg(dest_addr),
                MachOperand::Imm(0),
            ],
        ));
        let body_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(latch)],
        ));
        for inst in [
            sxtw,
            source_madd,
            source_load,
            dest_madd,
            dest_load,
            add,
            store,
            body_branch,
        ] {
            func.append_inst(body, inst);
        }

        let dec = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(index),
                MachOperand::Imm(-1),
            ],
        ));
        let writeback = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(index), MachOperand::VReg(next)],
        ));
        let latch_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        for inst in [dec, writeback, latch_branch] {
            func.append_inst(latch, inst);
        }

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(preheader, header);
        func.add_edge(header, body);
        func.add_edge(header, exit);
        func.add_edge(body, latch);
        func.add_edge(latch, header);

        (func, source_madd, dest_madd)
    }

    fn make_merged_latch_stack_backed_reverse_accumulation_loop() -> (MachFunction, InstId, InstId)
    {
        let mut func = MachFunction::new(
            "merged_latch_stack_backed_reverse_accumulation_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let preheader = func.entry;
        let header = func.create_block();
        let body_latch = func.create_block();
        let exit = func.create_block();

        let index = VReg::new(0, RegClass::Gpr32);
        let header_index = VReg::new(1, RegClass::Gpr32);
        let body_index = VReg::new(2, RegClass::Gpr32);
        let wide_index = VReg::new(3, RegClass::Gpr64);
        let stride = VReg::new(4, RegClass::Gpr64);
        let source_base = VReg::new(5, RegClass::Gpr64);
        let dest_base = VReg::new(6, RegClass::Gpr64);
        let source_addr = VReg::new(7, RegClass::Gpr64);
        let dest_addr = VReg::new(8, RegClass::Gpr64);
        let source_value = VReg::new(9, RegClass::Gpr32);
        let dest_value = VReg::new(10, RegClass::Gpr32);
        let sum = VReg::new(11, RegClass::Gpr32);
        let latch_index = VReg::new(12, RegClass::Gpr32);
        let next = VReg::new(13, RegClass::Gpr32);
        let zero = VReg::new(14, RegClass::Gpr32);
        let minus_one = VReg::new(15, RegClass::Gpr32);
        let slot_addr = VReg::new(16, RegClass::Gpr64);
        let slot = StackSlotId(0);

        let slot_addr_inst = func.push_inst(MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::VReg(slot_addr),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::SP),
                MachOperand::StackSlot(slot),
            ],
        ));
        let stride_init = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(stride), MachOperand::Imm(4)],
        ));
        let zero_init = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(zero), MachOperand::Imm(0)],
        ));
        let minus_one_init = func.push_inst(MachInst::new(
            AArch64Opcode::Movn,
            vec![MachOperand::VReg(minus_one), MachOperand::Imm(0)],
        ));
        let index_init = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(index),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        for inst in [
            slot_addr_inst,
            stride_init,
            zero_init,
            minus_one_init,
            index_init,
            br0,
        ] {
            func.append_inst(preheader, inst);
        }

        let header_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(header_index),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRR,
            vec![MachOperand::VReg(header_index), MachOperand::VReg(zero)],
        ));
        let branch_body = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(10), MachOperand::Block(body_latch)],
        ));
        let branch_exit = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        for inst in [header_load, cmp, branch_body, branch_exit] {
            func.append_inst(header, inst);
        }

        let body_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(body_index),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        let sxtw = func.push_inst(MachInst::new(
            AArch64Opcode::Sxtw,
            vec![MachOperand::VReg(wide_index), MachOperand::VReg(body_index)],
        ));
        let source_madd = func.push_inst(MachInst::new(
            AArch64Opcode::Madd,
            vec![
                MachOperand::VReg(source_addr),
                MachOperand::VReg(wide_index),
                MachOperand::VReg(stride),
                MachOperand::VReg(source_base),
            ],
        ));
        let dest_madd = func.push_inst(MachInst::new(
            AArch64Opcode::Madd,
            vec![
                MachOperand::VReg(dest_addr),
                MachOperand::VReg(wide_index),
                MachOperand::VReg(stride),
                MachOperand::VReg(dest_base),
            ],
        ));
        let source_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(source_value),
                MachOperand::VReg(source_addr),
                MachOperand::Imm(0),
            ],
        ));
        let dest_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(dest_value),
                MachOperand::VReg(dest_addr),
                MachOperand::Imm(0),
            ],
        ));
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(sum),
                MachOperand::VReg(dest_value),
                MachOperand::VReg(source_value),
            ],
        ));
        let store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(sum),
                MachOperand::VReg(dest_addr),
                MachOperand::Imm(0),
            ],
        ));
        let latch_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(latch_index),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        let dec = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(latch_index),
                MachOperand::VReg(minus_one),
            ],
        ));
        let writeback = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        let body_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        for inst in [
            body_load,
            sxtw,
            source_madd,
            dest_madd,
            source_load,
            dest_load,
            add,
            store,
            latch_load,
            dec,
            writeback,
            body_branch,
        ] {
            func.append_inst(body_latch, inst);
        }

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(preheader, header);
        func.add_edge(header, body_latch);
        func.add_edge(header, exit);
        func.add_edge(body_latch, header);

        (func, source_madd, dest_madd)
    }

    fn make_cset_header_stack_backed_reverse_accumulation_loop() -> (MachFunction, InstId, InstId) {
        let (mut func, source_madd, dest_madd) =
            make_merged_latch_stack_backed_reverse_accumulation_loop();
        let preheader = func.entry;
        let header = BlockId(1);
        let zero = VReg::new(14, RegClass::Gpr32);
        let cset_value = VReg::new(17, RegClass::Gpr64);
        let source_base = VReg::new(5, RegClass::Gpr64);
        let dest_base = VReg::new(6, RegClass::Gpr64);
        let source_base_copy = VReg::new(18, RegClass::Gpr64);
        let dest_base_copy = VReg::new(19, RegClass::Gpr64);
        let zero_init = func
            .block(preheader)
            .insts
            .iter()
            .copied()
            .find(|&inst_id| movz_i32_imm(func.inst(inst_id)) == Some((zero, 0)))
            .expect("zero initializer");
        func.block_mut(preheader)
            .insts
            .retain(|&inst_id| inst_id != zero_init);

        let cset = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![MachOperand::VReg(cset_value), MachOperand::Imm(10)],
        ));
        let cmp_cset = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(cset_value), MachOperand::Imm(0)],
        ));
        let branch_body = func.block(header).insts[2];
        func.inst_mut(branch_body).operands[0] = MachOperand::Imm(1);

        let header_insts = &mut func.block_mut(header).insts;
        header_insts.insert(1, zero_init);
        header_insts.insert(3, cset);
        header_insts.insert(4, cmp_cset);

        let source_copy = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(source_base_copy),
                MachOperand::VReg(source_base),
            ],
        ));
        let dest_copy = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(dest_base_copy),
                MachOperand::VReg(dest_base),
            ],
        ));
        func.inst_mut(source_madd).operands[3] = MachOperand::VReg(source_base_copy);
        func.inst_mut(dest_madd).operands[3] = MachOperand::VReg(dest_base_copy);

        let body_insts = &mut func.block_mut(BlockId(2)).insts;
        body_insts.insert(2, source_copy);
        body_insts.insert(3, dest_copy);

        (func, source_madd, dest_madd)
    }

    fn make_i32_bitreverse_ordered_sub_loop() -> (MachFunction, InstId, InstId, InstId, VReg) {
        let mut func = MachFunction::new(
            "i32_bitreverse_ordered_sub_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let accumulator = VReg::new(30, RegClass::Gpr64);

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let rbit = func.push_inst(MachInst::new(
            AArch64Opcode::Rbit,
            vec![vreg32(11), vreg32(10)],
        ));
        func.append_inst(bb1, rbit);

        let uxtw = func.push_inst(MachInst::new(
            AArch64Opcode::Uxtw,
            vec![vreg64(12), vreg32(11)],
        ));
        func.append_inst(bb1, uxtw);

        let sub = func.push_inst(MachInst::new(
            AArch64Opcode::SubRR,
            vec![
                MachOperand::VReg(accumulator),
                MachOperand::VReg(accumulator),
                vreg64(12),
            ],
        ));
        func.append_inst(bb1, sub);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(3), imm(64)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        (func, rbit, uxtw, sub, accumulator)
    }

    fn make_i64_bitreverse_ordered_sub_loop() -> (MachFunction, InstId, InstId, VReg) {
        let mut func = MachFunction::new(
            "i64_bitreverse_ordered_sub_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let accumulator = VReg::new(30, RegClass::Gpr64);

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let rbit = func.push_inst(MachInst::new(
            AArch64Opcode::Rbit,
            vec![vreg64(11), vreg64(10)],
        ));
        func.append_inst(bb1, rbit);

        let sub = func.push_inst(MachInst::new(
            AArch64Opcode::SubRR,
            vec![
                MachOperand::VReg(accumulator),
                MachOperand::VReg(accumulator),
                vreg64(11),
            ],
        ));
        func.append_inst(bb1, sub);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(3), imm(64)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        (func, rbit, sub, accumulator)
    }

    #[allow(clippy::type_complexity)]
    fn make_mixed_width_revertbits_sub_loop() -> (
        MachFunction,
        InstId,
        InstId,
        InstId,
        InstId,
        InstId,
        InstId,
        VReg,
        VReg,
        VReg,
        InstId,
        InstId,
    ) {
        let mut func = MachFunction::new(
            "mixed_width_revertbits_sub_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let current = VReg::new(10, RegClass::Gpr32);
        let next = VReg::new(11, RegClass::Gpr32);
        let acc32 = VReg::new(30, RegClass::Gpr64);
        let acc64 = VReg::new(31, RegClass::Gpr64);
        let tmp32 = VReg::new(32, RegClass::Gpr64);
        let tmp64 = VReg::new(33, RegClass::Gpr64);
        let acc32_loaded = VReg::new(34, RegClass::Gpr64);
        let acc64_loaded = VReg::new(35, RegClass::Gpr64);
        let rbit32_current = VReg::new(36, RegClass::Gpr32);
        let sxtw_current = VReg::new(37, RegClass::Gpr32);
        let step_current = VReg::new(38, RegClass::Gpr32);
        let one = VReg::new(39, RegClass::Gpr32);

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let load_rbit32_current = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(rbit32_current),
                MachOperand::VReg(current),
            ],
        ));
        func.append_inst(bb1, load_rbit32_current);

        let rbit32 = func.push_inst(MachInst::new(
            AArch64Opcode::Rbit,
            vec![vreg32(12), MachOperand::VReg(rbit32_current)],
        ));
        func.append_inst(bb1, rbit32);

        let uxtw = func.push_inst(MachInst::new(
            AArch64Opcode::Uxtw,
            vec![vreg64(13), vreg32(12)],
        ));
        func.append_inst(bb1, uxtw);

        let load_acc32 = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(acc32_loaded), MachOperand::VReg(acc32)],
        ));
        func.append_inst(bb1, load_acc32);

        let sub32 = func.push_inst(MachInst::new(
            AArch64Opcode::SubRR,
            vec![
                MachOperand::VReg(tmp32),
                MachOperand::VReg(acc32_loaded),
                vreg64(13),
            ],
        ));
        func.append_inst(bb1, sub32);
        let writeback32 = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(acc32), MachOperand::VReg(tmp32)],
        ));
        func.append_inst(bb1, writeback32);

        let load_sxtw_current = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(sxtw_current), MachOperand::VReg(current)],
        ));
        func.append_inst(bb1, load_sxtw_current);

        let sxtw = func.push_inst(MachInst::new(
            AArch64Opcode::Sxtw,
            vec![vreg64(14), MachOperand::VReg(sxtw_current)],
        ));
        func.append_inst(bb1, sxtw);

        let rbit64 = func.push_inst(MachInst::new(
            AArch64Opcode::Rbit,
            vec![vreg64(15), vreg64(14)],
        ));
        func.append_inst(bb1, rbit64);

        let load_acc64 = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(acc64_loaded), MachOperand::VReg(acc64)],
        ));
        func.append_inst(bb1, load_acc64);

        let sub64 = func.push_inst(MachInst::new(
            AArch64Opcode::SubRR,
            vec![
                MachOperand::VReg(tmp64),
                MachOperand::VReg(acc64_loaded),
                vreg64(15),
            ],
        ));
        func.append_inst(bb1, sub64);
        let writeback64 = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(acc64), MachOperand::VReg(tmp64)],
        ));
        func.append_inst(bb1, writeback64);

        let load_step_current = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(step_current), MachOperand::VReg(current)],
        ));
        func.append_inst(bb1, load_step_current);
        let one_inst = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(one), imm(1)],
        ));
        func.append_inst(bb1, one_inst);
        let step = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(step_current),
                MachOperand::VReg(one),
            ],
        ));
        func.append_inst(bb1, step);
        let writeback_step = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(current), MachOperand::VReg(next)],
        ));
        func.append_inst(bb1, writeback_step);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(3), imm(64)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        (
            func,
            rbit32,
            uxtw,
            sub32,
            sxtw,
            rbit64,
            sub64,
            current,
            next,
            acc64,
            writeback32,
            writeback64,
        )
    }

    fn replace_mixed_width_revertbits_accumulators_with_stack_slots(
        func: &mut MachFunction,
        writeback32: InstId,
        writeback64: InstId,
    ) -> (InstId, InstId, VReg, VReg) {
        let acc32_slot_address = VReg::new(80, RegClass::Gpr64);
        let acc64_slot_address = VReg::new(81, RegClass::Gpr64);
        let acc32_loaded = VReg::new(34, RegClass::Gpr64);
        let acc64_loaded = VReg::new(35, RegClass::Gpr64);
        let tmp32 = VReg::new(32, RegClass::Gpr64);
        let tmp64 = VReg::new(33, RegClass::Gpr64);

        let acc32_address_inst = func.push_inst(MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::VReg(acc32_slot_address),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::SP),
                MachOperand::StackSlot(StackSlotId(32)),
            ],
        ));
        let acc64_address_inst = func.push_inst(MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::VReg(acc64_slot_address),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::SP),
                MachOperand::StackSlot(StackSlotId(64)),
            ],
        ));
        let entry = func.entry;
        let branch_pos = func
            .block(entry)
            .insts
            .iter()
            .position(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::B)
            .unwrap_or(func.block(entry).insts.len());
        func.block_mut(entry)
            .insts
            .insert(branch_pos, acc32_address_inst);
        func.block_mut(entry)
            .insts
            .insert(branch_pos + 1, acc64_address_inst);

        let load_acc32 = func
            .insts
            .iter()
            .enumerate()
            .find_map(|(idx, inst)| {
                (inst.opcode == AArch64Opcode::MovR
                    && inst.operands.first() == Some(&MachOperand::VReg(acc32_loaded)))
                .then_some(InstId(idx as u32))
            })
            .expect("acc32 load copy");
        let load_acc64 = func
            .insts
            .iter()
            .enumerate()
            .find_map(|(idx, inst)| {
                (inst.opcode == AArch64Opcode::MovR
                    && inst.operands.first() == Some(&MachOperand::VReg(acc64_loaded)))
                .then_some(InstId(idx as u32))
            })
            .expect("acc64 load copy");

        *func.inst_mut(load_acc32) = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(acc32_loaded),
                MachOperand::VReg(acc32_slot_address),
                MachOperand::Imm(0),
            ],
        );
        *func.inst_mut(load_acc64) = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(acc64_loaded),
                MachOperand::VReg(acc64_slot_address),
                MachOperand::Imm(0),
            ],
        );
        *func.inst_mut(writeback32) = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(tmp32),
                MachOperand::VReg(acc32_slot_address),
                MachOperand::Imm(0),
            ],
        );
        *func.inst_mut(writeback64) = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(tmp64),
                MachOperand::VReg(acc64_slot_address),
                MachOperand::Imm(0),
            ],
        );

        (
            load_acc32,
            load_acc64,
            acc32_slot_address,
            acc64_slot_address,
        )
    }

    fn replace_mixed_width_revertbits_induction_with_stack_slot(
        func: &mut MachFunction,
        current: VReg,
        next: VReg,
    ) -> (InstId, InstId, InstId, InstId, VReg) {
        let index_slot_address = VReg::new(82, RegClass::Gpr64);
        let rbit32_current = VReg::new(36, RegClass::Gpr32);
        let sxtw_current = VReg::new(37, RegClass::Gpr32);
        let step_current = VReg::new(38, RegClass::Gpr32);

        let address_inst = func.push_inst(MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::VReg(index_slot_address),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::SP),
                MachOperand::StackSlot(StackSlotId(96)),
            ],
        ));
        let entry = func.entry;
        let branch_pos = func
            .block(entry)
            .insts
            .iter()
            .position(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::B)
            .unwrap_or(func.block(entry).insts.len());
        func.block_mut(entry).insts.insert(branch_pos, address_inst);

        let load_rbit32_current = func
            .insts
            .iter()
            .enumerate()
            .find_map(|(idx, inst)| {
                (inst.opcode == AArch64Opcode::MovR
                    && inst.operands.first() == Some(&MachOperand::VReg(rbit32_current)))
                .then_some(InstId(idx as u32))
            })
            .expect("rbit32 induction load copy");
        let load_sxtw_current = func
            .insts
            .iter()
            .enumerate()
            .find_map(|(idx, inst)| {
                (inst.opcode == AArch64Opcode::MovR
                    && inst.operands.first() == Some(&MachOperand::VReg(sxtw_current)))
                .then_some(InstId(idx as u32))
            })
            .expect("sxtw induction load copy");
        let load_step_current = func
            .insts
            .iter()
            .enumerate()
            .find_map(|(idx, inst)| {
                (inst.opcode == AArch64Opcode::MovR
                    && inst.operands.first() == Some(&MachOperand::VReg(step_current)))
                .then_some(InstId(idx as u32))
            })
            .expect("step induction load copy");
        let writeback_step = func
            .insts
            .iter()
            .enumerate()
            .find_map(|(idx, inst)| {
                (inst.opcode == AArch64Opcode::MovR
                    && inst.operands == [MachOperand::VReg(current), MachOperand::VReg(next)])
                .then_some(InstId(idx as u32))
            })
            .expect("step induction writeback copy");

        for (inst_id, dst) in [
            (load_rbit32_current, rbit32_current),
            (load_sxtw_current, sxtw_current),
            (load_step_current, step_current),
        ] {
            *func.inst_mut(inst_id) = MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::VReg(dst),
                    MachOperand::VReg(index_slot_address),
                    MachOperand::Imm(0),
                ],
            );
        }
        *func.inst_mut(writeback_step) = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(index_slot_address),
                MachOperand::Imm(0),
            ],
        );

        (
            load_rbit32_current,
            load_sxtw_current,
            load_step_current,
            writeback_step,
            index_slot_address,
        )
    }

    /// Build a loop with a data dependency (recurrence) that prevents vectorization.
    ///
    /// ```text
    ///   bb0 -> bb1 (header) -> bb3 (latch) -> bb1
    ///                       -> bb2 (exit)
    /// ```
    ///
    /// In bb1: v2 = add v2, v1 — v2 depends on its own prior value (recurrence).
    fn make_dependency_loop() -> MachFunction {
        let mut func = MachFunction::new("dep_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // bb1: load v2 = load (not vectorizable — memory op)
        let ld = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg32(2), vreg64(10), imm(0)],
        ));
        func.append_inst(bb1, ld);

        // v3 = add v2, v1 — depends on load result
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg32(3), vreg32(2), vreg32(1)],
        ));
        func.append_inst(bb1, add);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(4), imm(100)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        func
    }

    /// Build an i64 recurrence where the loop-carried scalar values are also
    /// consumed by scalar control/exit code. The generic vectorizer must not
    /// upgrade those values without explicit scalar bridges.
    fn make_loop_carried_scalar_consumer_loop() -> MachFunction {
        let mut func = MachFunction::new(
            "loop_carried_scalar_consumer".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let one = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![vreg64(1), imm(1)]));
        func.append_inst(bb0, one);
        let two = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![vreg64(2), imm(2)]));
        func.append_inst(bb0, two);
        let init_acc = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![vreg64(5), vreg64(1)],
        ));
        func.append_inst(bb0, init_acc);
        let init_i = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![vreg64(6), vreg64(2)],
        ));
        func.append_inst(bb0, init_i);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg64(8), vreg64(5), vreg64(6)],
        ));
        func.append_inst(bb1, mul);
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg64(10), vreg64(6), vreg64(1)],
        ));
        func.append_inst(bb1, add);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, br1);

        let acc_writeback = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg64(5), vreg64(8), imm(0)],
        ));
        func.append_inst(bb2, acc_writeback);
        let i_writeback = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg64(6), vreg64(10), imm(0)],
        ));
        func.append_inst(bb2, i_writeback);
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRR,
            vec![vreg64(6), vreg64(0)],
        ));
        func.append_inst(bb2, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(13), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb2, bcond);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, br2);

        let ret_copy = func.push_inst(MachInst::new(
            AArch64Opcode::Copy,
            vec![MachOperand::PReg(trust_cg_ir::aarch64_regs::X0), vreg64(5)],
        ));
        func.append_inst(bb3, ret_copy);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb1);
        func.add_edge(bb2, bb3);

        func
    }

    /// Build a loop with a small trip count (4) — should be rejected by cost model.
    fn make_small_trip_count_loop() -> MachFunction {
        let mut func = MachFunction::new("small_tc".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg32(2), vreg32(0), vreg32(1)],
        ));
        func.append_inst(bb1, add);

        // Trip count = 4
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg32(3), imm(4)]));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        func
    }

    /// Build a profitable trip-count-4 loop. The independent arithmetic ops
    /// make NEON profitable once the hot-profile gate drops from 8 to 4.
    fn make_profitable_small_trip_count_loop() -> MachFunction {
        let mut func =
            MachFunction::new("hot_small_tc".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        for id in 2..12 {
            let add = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg32(id), vreg32(0), vreg32(1)],
            ));
            func.append_inst(bb1, add);
        }

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(20), imm(4)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        func
    }

    fn profile_hotness_for_vec_header(hits: u64, function_count: u64) -> ProfileHotness {
        let mut profile = ProfData::new(0x396);
        let mut function = FunctionProfile::new("hot_small_tc");
        function.call_count = function_count;
        function.blocks.push(BlockProfile::new(BlockId(1).0, hits));
        profile.functions.push(function);
        ProfileHotness::from_profile(&profile)
    }

    /// Build a loop with the contextual i32 equality idiom:
    ///
    /// ```text
    /// cmp  w10, w11
    /// cset w12, eq
    /// ```
    fn make_i32_eq_compare_loop() -> (MachFunction, InstId, InstId) {
        let mut func = MachFunction::new(
            "i32_eq_compare_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let cmp_eq = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRR,
            vec![vreg32(10), vreg32(11)],
        ));
        func.append_inst(bb1, cmp_eq);

        let cset_eq = func.push_inst(MachInst::new(AArch64Opcode::CSet, vec![vreg32(12), imm(0)]));
        func.append_inst(bb1, cset_eq);

        let cmp_trip = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(3), imm(64)],
        ));
        func.append_inst(bb1, cmp_trip);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        (func, cmp_eq, cset_eq)
    }

    /// Build a ay-style scalar literal-scan loop:
    ///
    /// ```text
    /// cmp  lane_value, literal
    /// cset lane_matches, eq
    /// orr  any, any, lane_matches
    /// ```
    fn make_ay_i32_eq_horizontal_any_loop() -> (MachFunction, InstId, InstId, InstId) {
        let (mut func, cmp_eq, cset_eq) = make_i32_eq_compare_loop();
        let header = BlockId(1);
        let insert_pos = 2;
        let orr_any = func.push_inst(MachInst::new(
            AArch64Opcode::OrrRR,
            vec![vreg32(30), vreg32(30), vreg32(12)],
        ));
        func.block_mut(header).insts.insert(insert_pos, orr_any);
        (func, cmp_eq, cset_eq, orr_any)
    }

    fn ay_chunk_i32_eq_mask(lanes: [i32; 4], literal: i32, real_lanes: usize) -> [u32; 4] {
        assert!(real_lanes <= 4);
        let mut mask = [0; 4];
        for lane in 0..real_lanes {
            if lanes[lane] == literal {
                mask[lane] = u32::MAX;
            }
        }
        mask
    }

    fn ay_chunk_horizontal_any(lanes: [i32; 4], literal: i32, real_lanes: usize) -> bool {
        ay_chunk_i32_eq_mask(lanes, literal, real_lanes)
            .iter()
            .any(|lane| *lane != 0)
    }

    fn ay_clause_contains_literal(clause: &[i32], literal: i32) -> bool {
        const SENTINEL_PADDING: i32 = i32::MAX;

        for chunk_start in (0..clause.len()).step_by(4) {
            let real_lanes = (clause.len() - chunk_start).min(4);
            let mut lanes = [SENTINEL_PADDING; 4];
            lanes[..real_lanes].copy_from_slice(&clause[chunk_start..chunk_start + real_lanes]);
            if ay_chunk_horizontal_any(lanes, literal, real_lanes) {
                return true;
            }
        }

        false
    }

    fn ay_clause_subsumes(lhs: &[i32], rhs: &[i32]) -> bool {
        lhs.iter()
            .copied()
            .all(|literal| ay_clause_contains_literal(rhs, literal))
    }

    #[derive(Debug, Clone, Copy, Default)]
    struct Contains4MaskedOptions {
        wrong_lane2_shift: bool,
        non_eq_lane1: bool,
        mixed_lane2_literal: bool,
        omit_final_valid_mask: bool,
        extra_eq0_use: bool,
        ambiguous_lane0_flag_consumer: bool,
        memory_loads: bool,
        wrong_lane2_load_offset: bool,
        mixed_lane3_load_base: bool,
        extra_lane0_load_use: bool,
        extra_base_use_after_mask: bool,
        store_between_memory_load_and_mask: bool,
    }

    #[derive(Debug)]
    struct Contains4MaskedFixture {
        final_and: Option<InstId>,
        scalar_insts: Vec<InstId>,
        load_insts: Option<[InstId; 4]>,
        cmp_insts: [InstId; 4],
        cset_insts: [InstId; 4],
        output: VReg,
        valid_mask: VReg,
    }

    fn append_test_inst(func: &mut MachFunction, block: BlockId, inst: MachInst) -> InstId {
        let inst_id = func.push_inst(inst);
        func.append_inst(block, inst_id);
        inst_id
    }

    fn make_contains4_masked_function(
        options: Contains4MaskedOptions,
    ) -> (MachFunction, Contains4MaskedFixture) {
        let mut func = MachFunction::new(
            "contains4_masked_slp".to_string(),
            Signature::new(vec![], vec![]),
        );
        let block = func.entry;

        let lanes = [
            VReg::new(0, RegClass::Gpr32),
            VReg::new(1, RegClass::Gpr32),
            VReg::new(2, RegClass::Gpr32),
            VReg::new(3, RegClass::Gpr32),
        ];
        let literal = VReg::new(10, RegClass::Gpr32);
        let other_literal = VReg::new(11, RegClass::Gpr32);
        let valid_mask = VReg::new(12, RegClass::Gpr32);
        let output = VReg::new(13, RegClass::Gpr32);
        let zero = VReg::new(20, RegClass::Gpr32);
        let eq = [
            VReg::new(21, RegClass::Gpr32),
            VReg::new(22, RegClass::Gpr32),
            VReg::new(23, RegClass::Gpr32),
            VReg::new(24, RegClass::Gpr32),
        ];
        let shifted = [
            VReg::new(31, RegClass::Gpr32),
            VReg::new(32, RegClass::Gpr32),
            VReg::new(33, RegClass::Gpr32),
        ];
        let acc = [
            VReg::new(40, RegClass::Gpr32),
            VReg::new(41, RegClass::Gpr32),
            VReg::new(42, RegClass::Gpr32),
            VReg::new(43, RegClass::Gpr32),
        ];
        let extra = VReg::new(60, RegClass::Gpr32);
        let extra_base = VReg::new(61, RegClass::Gpr64);
        let base = VReg::new(70, RegClass::Gpr64);
        let other_base = VReg::new(71, RegClass::Gpr64);

        let mut scalar_insts = Vec::new();
        let load_insts = if options.memory_loads {
            let loads: [InstId; 4] = std::array::from_fn(|lane| {
                let offset = if options.wrong_lane2_load_offset && lane == 2 {
                    12
                } else {
                    (lane as i64) * 4
                };
                let load_base = if options.mixed_lane3_load_base && lane == 3 {
                    other_base
                } else {
                    base
                };
                append_test_inst(
                    &mut func,
                    block,
                    MachInst::new(
                        AArch64Opcode::LdrRI,
                        vec![
                            MachOperand::VReg(lanes[lane]),
                            MachOperand::VReg(load_base),
                            MachOperand::Imm(offset),
                        ],
                    ),
                )
            });
            scalar_insts.extend(loads);

            if options.extra_lane0_load_use {
                append_test_inst(
                    &mut func,
                    block,
                    MachInst::new(
                        AArch64Opcode::AddRR,
                        vec![
                            MachOperand::VReg(extra),
                            MachOperand::VReg(lanes[0]),
                            MachOperand::VReg(valid_mask),
                        ],
                    ),
                );
            }
            if options.store_between_memory_load_and_mask {
                append_test_inst(
                    &mut func,
                    block,
                    MachInst::new(
                        AArch64Opcode::StrRI,
                        vec![
                            MachOperand::VReg(extra),
                            MachOperand::VReg(base),
                            MachOperand::Imm(16),
                        ],
                    ),
                );
            }

            Some(loads)
        } else {
            None
        };

        let zero_id = append_test_inst(
            &mut func,
            block,
            MachInst::new(
                AArch64Opcode::Movz,
                vec![MachOperand::VReg(zero), MachOperand::Imm(0)],
            ),
        );
        scalar_insts.push(zero_id);

        let mut cmp_insts = [InstId(0); 4];
        let mut cset_insts = [InstId(0); 4];
        let mut bit_operands = [
            MachOperand::VReg(eq[0]),
            MachOperand::VReg(eq[1]),
            MachOperand::VReg(eq[2]),
            MachOperand::VReg(eq[3]),
        ];

        for lane in 0..4 {
            let lane_literal = if options.mixed_lane2_literal && lane == 2 {
                other_literal
            } else {
                literal
            };
            let cmp = append_test_inst(
                &mut func,
                block,
                MachInst::new(
                    AArch64Opcode::CmpRR,
                    vec![
                        MachOperand::VReg(lanes[lane]),
                        MachOperand::VReg(lane_literal),
                    ],
                ),
            );
            let cond = if options.non_eq_lane1 && lane == 1 {
                1
            } else {
                0
            };
            let cset = append_test_inst(
                &mut func,
                block,
                MachInst::new(
                    AArch64Opcode::CSet,
                    vec![MachOperand::VReg(eq[lane]), MachOperand::Imm(cond)],
                ),
            );
            cmp_insts[lane] = cmp;
            cset_insts[lane] = cset;
            scalar_insts.extend([cmp, cset]);

            if options.ambiguous_lane0_flag_consumer && lane == 0 {
                append_test_inst(
                    &mut func,
                    block,
                    MachInst::new(
                        AArch64Opcode::CSet,
                        vec![MachOperand::VReg(extra), MachOperand::Imm(0)],
                    ),
                );
            }

            if lane > 0 {
                let shift = if options.wrong_lane2_shift && lane == 2 {
                    3
                } else {
                    lane as i64
                };
                let lsl = append_test_inst(
                    &mut func,
                    block,
                    MachInst::new(
                        AArch64Opcode::LslRI,
                        vec![
                            MachOperand::VReg(shifted[lane - 1]),
                            MachOperand::VReg(eq[lane]),
                            MachOperand::Imm(shift),
                        ],
                    ),
                );
                scalar_insts.push(lsl);
                bit_operands[lane] = MachOperand::VReg(shifted[lane - 1]);
            }
        }

        if options.extra_eq0_use {
            append_test_inst(
                &mut func,
                block,
                MachInst::new(
                    AArch64Opcode::AddRR,
                    vec![
                        MachOperand::VReg(extra),
                        MachOperand::VReg(eq[0]),
                        MachOperand::VReg(valid_mask),
                    ],
                ),
            );
        }

        let orr0 = append_test_inst(
            &mut func,
            block,
            MachInst::new(
                AArch64Opcode::OrrRR,
                vec![
                    MachOperand::VReg(acc[0]),
                    MachOperand::VReg(zero),
                    bit_operands[0].clone(),
                ],
            ),
        );
        let orr1 = append_test_inst(
            &mut func,
            block,
            MachInst::new(
                AArch64Opcode::OrrRR,
                vec![
                    MachOperand::VReg(acc[1]),
                    MachOperand::VReg(acc[0]),
                    bit_operands[1].clone(),
                ],
            ),
        );
        let orr2 = append_test_inst(
            &mut func,
            block,
            MachInst::new(
                AArch64Opcode::OrrRR,
                vec![
                    MachOperand::VReg(acc[2]),
                    MachOperand::VReg(acc[1]),
                    bit_operands[2].clone(),
                ],
            ),
        );
        let orr3 = append_test_inst(
            &mut func,
            block,
            MachInst::new(
                AArch64Opcode::OrrRR,
                vec![
                    MachOperand::VReg(acc[3]),
                    MachOperand::VReg(acc[2]),
                    bit_operands[3].clone(),
                ],
            ),
        );
        scalar_insts.extend([orr0, orr1, orr2, orr3]);

        let final_and = if options.omit_final_valid_mask {
            None
        } else {
            Some(append_test_inst(
                &mut func,
                block,
                MachInst::new(
                    AArch64Opcode::AndRR,
                    vec![
                        MachOperand::VReg(output),
                        MachOperand::VReg(acc[3]),
                        MachOperand::VReg(valid_mask),
                    ],
                ),
            ))
        };

        if options.extra_base_use_after_mask {
            append_test_inst(
                &mut func,
                block,
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::VReg(extra_base), MachOperand::VReg(base)],
                ),
            );
        }

        append_test_inst(&mut func, block, MachInst::new(AArch64Opcode::Ret, vec![]));

        (
            func,
            Contains4MaskedFixture {
                final_and,
                scalar_insts,
                load_insts,
                cmp_insts,
                cset_insts,
                output,
                valid_mask,
            },
        )
    }

    fn count_opcode(func: &MachFunction, opcode: AArch64Opcode) -> usize {
        func.insts
            .iter()
            .filter(|inst| inst.opcode == opcode)
            .count()
    }

    // =========================================================================
    // Test: simple add loop is vectorizable
    // =========================================================================

    #[test]
    fn test_simple_add_loop_vectorizable() {
        let func = make_vectorizable_add_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        assert_eq!(la.num_loops(), 1);
        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model);

        assert!(plan.is_some(), "add loop should be vectorizable");
        let plan = plan.unwrap();
        assert_eq!(plan.element_type, VecElementType::I32);
        assert_eq!(plan.arrangement, NeonArrangement::S4);
        assert_eq!(plan.vf, 4);
        assert_eq!(plan.trip_count, Some(100));
        assert!(!plan.vectorizable_insts.is_empty());
    }

    // =========================================================================
    // Test: loop with data dependency is NOT vectorizable
    // =========================================================================

    #[test]
    fn test_data_dependency_blocks_vectorization() {
        let func = make_dependency_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model);

        // The add depends on a load (not vectorizable), so the dependency
        // check should reject it.
        assert!(
            plan.is_none(),
            "loop with memory dependency should not be vectorizable"
        );
    }

    #[test]
    fn test_loop_carried_scalar_consumers_block_generic_vectorization() {
        let func = make_loop_carried_scalar_consumer_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model);

        assert!(
            plan.is_none(),
            "vectorization must reject loop-carried values still consumed by scalar control/exit code"
        );
    }

    // =========================================================================
    // Test: cost model rejects small trip count
    // =========================================================================

    #[test]
    fn test_small_trip_count_rejected() {
        let mut func = make_small_trip_count_loop();
        let mut pass = VectorizationPass::with_config(CostModelGen::M1, 8);
        let changed = pass.run(&mut func);

        // The pass should find a plan but it should not be "changed" because
        // the trip count (4) is below the minimum threshold (8).
        // The plan exists but is skipped.
        assert!(
            !changed,
            "small trip count should not trigger vectorization"
        );
    }

    #[test]
    fn test_hot_profile_header_lowers_min_trip_count_gate() {
        let mut func = make_profitable_small_trip_count_loop();
        let hotness = profile_hotness_for_vec_header(100, 100);
        let mut pass = VectorizationPass::new().with_profile_hotness(Some(hotness));

        let changed = pass.run(&mut func);

        assert!(changed, "hot trip-count-4 loop should be vectorized");
        assert_eq!(pass.plans().len(), 1);
        assert_eq!(pass.plans()[0].trip_count, Some(4));
        assert_eq!(pass.results().len(), 1);
        assert!(
            pass.results()[0].insts_rewritten > 0,
            "hot-profile vectorization should rewrite scalar ops"
        );
    }

    #[test]
    fn test_non_hot_profile_headers_keep_default_min_trip_count_gate() {
        let cases = [
            ("missing", None),
            ("cold", Some(profile_hotness_for_vec_header(5, 100))),
            ("warm", Some(profile_hotness_for_vec_header(50, 100))),
        ];

        for (case, hotness) in cases {
            let mut func = make_profitable_small_trip_count_loop();
            let mut pass = VectorizationPass::new().with_profile_hotness(hotness);

            let changed = pass.run(&mut func);

            assert!(
                !changed,
                "{case} profile data should keep the default vectorization gate"
            );
            assert_eq!(pass.plans().len(), 1, "{case}");
            assert!(
                pass.results().is_empty(),
                "{case} profile data should not rewrite the small loop"
            );
        }
    }

    // =========================================================================
    // Test: i32 maps to arrangement 4S
    // =========================================================================

    #[test]
    fn test_i32_arrangement_4s() {
        assert_eq!(VecElementType::I32.neon_arrangement(), NeonArrangement::S4);
        assert_eq!(VecElementType::I32.lanes(), 4);
        assert_eq!(VecElementType::I32.bits(), 32);
    }

    // =========================================================================
    // Test: f64 maps to arrangement 2D
    // =========================================================================

    #[test]
    fn test_f64_arrangement_2d() {
        assert_eq!(VecElementType::F64.neon_arrangement(), NeonArrangement::D2);
        assert_eq!(VecElementType::F64.lanes(), 2);
        assert_eq!(VecElementType::F64.bits(), 64);
    }

    // =========================================================================
    // Test: i8 maps to arrangement 16B
    // =========================================================================

    #[test]
    fn test_i8_arrangement_16b() {
        assert_eq!(VecElementType::I8.neon_arrangement(), NeonArrangement::B16);
        assert_eq!(VecElementType::I8.lanes(), 16);
        assert_eq!(VecElementType::I8.bits(), 8);
    }

    // =========================================================================
    // Test: i16 maps to arrangement 8H
    // =========================================================================

    #[test]
    fn test_i16_arrangement_8h() {
        assert_eq!(VecElementType::I16.neon_arrangement(), NeonArrangement::H8);
        assert_eq!(VecElementType::I16.lanes(), 8);
        assert_eq!(VecElementType::I16.bits(), 16);
    }

    // =========================================================================
    // Test: f32 maps to arrangement 4S
    // =========================================================================

    #[test]
    fn test_f32_arrangement_4s() {
        assert_eq!(VecElementType::F32.neon_arrangement(), NeonArrangement::S4);
        assert_eq!(VecElementType::F32.lanes(), 4);
    }

    // =========================================================================
    // Test: is_vectorizable for various opcodes
    // =========================================================================

    #[test]
    fn test_is_vectorizable_opcodes() {
        // Vectorizable: pure arithmetic with NEON equivalents
        assert!(is_vectorizable(AArch64Opcode::AddRR));
        assert!(is_vectorizable(AArch64Opcode::SubRR));
        assert!(is_vectorizable(AArch64Opcode::MulRR));
        assert!(is_vectorizable(AArch64Opcode::Neg));
        assert!(is_vectorizable(AArch64Opcode::AndRR));
        assert!(is_vectorizable(AArch64Opcode::OrrRR));
        assert!(is_vectorizable(AArch64Opcode::EorRR));
        assert!(is_vectorizable(AArch64Opcode::FaddRR));
        assert!(is_vectorizable(AArch64Opcode::FmulRR));
        assert!(is_vectorizable(AArch64Opcode::LslRI));
        assert!(is_vectorizable(AArch64Opcode::Rbit));

        // NOT vectorizable: memory ops
        assert!(!is_vectorizable(AArch64Opcode::LdrRI));
        assert!(!is_vectorizable(AArch64Opcode::StrRI));

        // NOT vectorizable: branches, calls
        assert!(!is_vectorizable(AArch64Opcode::B));
        assert!(!is_vectorizable(AArch64Opcode::Bl));
        assert!(!is_vectorizable(AArch64Opcode::Ret));

        // NOT vectorizable: compare (sets flags, no NEON map)
        assert!(!is_vectorizable(AArch64Opcode::CmpRR));
        assert!(!is_vectorizable(AArch64Opcode::CmpRI));

        // NOT vectorizable: divide (no NEON integer divide)
        assert!(!is_vectorizable(AArch64Opcode::SDiv));
        assert!(!is_vectorizable(AArch64Opcode::UDiv));
    }

    #[test]
    fn test_i32_bitreverse_loop_rewrites_to_rev32_16b_rbit_16b() {
        let (mut func, rbit_id) = make_bitreverse_loop(RegClass::Gpr32);
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::I32);
        assert_eq!(plan.arrangement, NeonArrangement::S4);
        assert_eq!(plan.vf, 4);
        assert_eq!(plan.trip_count, Some(64));
        assert_eq!(plan.vectorizable_insts, vec![rbit_id]);
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.insts_rewritten, 1);
        assert_eq!(result.vector_trip_count, Some(16));

        let rev = func.inst(rbit_id);
        assert_eq!(rev.opcode, AArch64Opcode::NeonRev32V);
        assert_eq!(rev.operands.len(), 3);
        assert_eq!(rev.operands[2], MachOperand::Imm(1));
        for operand in &rev.operands[..2] {
            match operand {
                MachOperand::VReg(vreg) => assert_eq!(vreg.class, RegClass::Fpr128),
                other => panic!("expected SIMD vreg operand, got {other:?}"),
            }
        }

        let header = func.block(BlockId(1));
        let pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == rbit_id)
            .expect("rewritten REV remains in loop header");
        let neon_rbit = func.inst(header.insts[pos + 1]);
        assert_eq!(neon_rbit.opcode, AArch64Opcode::NeonRbitV);
        assert_eq!(neon_rbit.operands.len(), 3);
        assert_eq!(neon_rbit.operands[2], MachOperand::Imm(1));
        for operand in &neon_rbit.operands[..2] {
            match operand {
                MachOperand::VReg(vreg) => assert_eq!(vreg.class, RegClass::Fpr128),
                other => panic!("expected SIMD vreg operand, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_i32_induction_bitreverse_builds_vf4_lanes_and_step() {
        let (mut func, rbit_id, step_id, current) = make_i32_induction_bitreverse_loop(10, 1, true);
        let initial_blocks = func.num_blocks();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::I32);
        assert_eq!(plan.vf, 4);
        assert_eq!(plan.trip_count, Some(10));
        assert_eq!(plan.vectorizable_insts, vec![rbit_id]);
        assert_eq!(
            plan.induction,
            Some(VectorInduction {
                step_inst: step_id,
                scalar_current: current,
                scalar_current_alias: None,
                scalar_next: VReg::new(12, RegClass::Gpr32),
                sign_extend_inst: None,
                sign_extended_current: None,
                step: 1,
            })
        );
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.vector_trip_count, Some(2));
        assert_eq!(result.remainder, 2);
        assert!(result.has_epilogue);
        assert!(
            func.num_blocks() > initial_blocks,
            "non-multiple trip counts keep scalar epilogue coverage"
        );

        assert_eq!(
            func.inst(step_id).operands[2],
            MachOperand::Imm(4),
            "scalar induction advances by VF after vectorization"
        );

        let header = func.block(BlockId(1));
        let rbit_pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == rbit_id)
            .expect("rewritten REV remains in header");
        let lane_setup = &header.insts[rbit_pos - 7..rbit_pos];
        assert_eq!(func.inst(lane_setup[0]).opcode, AArch64Opcode::NeonDupGen);
        assert_eq!(
            func.inst(lane_setup[0]).operands[1],
            MachOperand::VReg(current),
            "lane 0 is seeded from scalar i"
        );

        for lane in 1..4 {
            let add = func.inst(lane_setup[1 + (lane - 1) * 2]);
            let ins = func.inst(lane_setup[2 + (lane - 1) * 2]);
            assert_eq!(add.opcode, AArch64Opcode::AddRI);
            assert_eq!(add.operands[1], MachOperand::VReg(current));
            assert_eq!(add.operands[2], MachOperand::Imm(lane as i64));
            assert_eq!(ins.opcode, AArch64Opcode::NeonInsGen);
            assert_eq!(ins.operands[2], MachOperand::Imm(lane as i64));
            assert_eq!(ins.operands[3], MachOperand::Imm(4));
        }

        let lanes_vec = match func.inst(lane_setup[0]).operands[0] {
            MachOperand::VReg(vreg) => vreg,
            ref other => panic!("expected induction lane vector, got {other:?}"),
        };
        let rev = func.inst(rbit_id);
        assert_eq!(rev.opcode, AArch64Opcode::NeonRev32V);
        assert_eq!(
            rev.operands[1],
            MachOperand::VReg(lanes_vec),
            "vectorized bitreverse consumes i + {{0,1,2,3}} lanes"
        );

        let epilogue = func.block(BlockId(initial_blocks as u32));
        let remainder_replay = &epilogue.insts[..4];
        for (lane, chunk) in remainder_replay.chunks_exact(2).enumerate() {
            let expected_offset = 8 + lane as i64;
            let induction_value = func.inst(chunk[0]);
            assert_eq!(induction_value.opcode, AArch64Opcode::AddRI);
            assert_eq!(induction_value.operands[1], MachOperand::VReg(current));
            assert_eq!(
                induction_value.operands[2],
                MachOperand::Imm(expected_offset)
            );
            let scalar_i = match induction_value.operands[0] {
                MachOperand::VReg(vreg) => vreg,
                ref other => panic!("expected scalar remainder induction vreg, got {other:?}"),
            };

            let scalar_rbit = func.inst(chunk[1]);
            assert_eq!(
                scalar_rbit.opcode,
                AArch64Opcode::Rbit,
                "epilogue must replay the original scalar bitreverse"
            );
            assert_eq!(
                scalar_rbit.operands[1],
                MachOperand::VReg(scalar_i),
                "remainder lane {lane} should consume i+{expected_offset}"
            );
        }
    }

    #[test]
    fn test_i32_induction_rejects_unsupported_step() {
        let (func, _rbit_id, _step_id, _current) = make_i32_induction_bitreverse_loop(16, 2, false);
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        assert!(
            analyze_loop(&func, lp, &cost_model).is_none(),
            "non-unit i32 induction must not be silently vectorized"
        );
    }

    #[test]
    fn test_imported_o0_i32_induction_store_rewrites_to_vector_main_and_scalar_tail() {
        let mut func = make_imported_o0_i32_induction_store_loop();
        let initial_blocks = func.num_blocks();
        let original_header = BlockId(1);
        let original_scalar_store_count = count_opcode(&func, AArch64Opcode::StrRI);

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let results = rewrite_i32_induction_store_loops(&mut func, &la, None);

        assert_eq!(results.len(), 1);
        assert_eq!(func.num_blocks(), initial_blocks + 3);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 1);
        assert_eq!(
            count_opcode(&func, AArch64Opcode::StrRI),
            original_scalar_store_count,
            "original scalar loop remains as the dynamic tail"
        );

        let vector_header = BlockId(initial_blocks as u32);
        let vector_body = BlockId(initial_blocks as u32 + 1);
        let vector_latch = BlockId(initial_blocks as u32 + 2);
        let preheader_branch = func
            .block(func.entry)
            .insts
            .iter()
            .copied()
            .rev()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::B)
            .expect("preheader should still end in a branch");
        assert_eq!(
            branch_target(func.inst(preheader_branch)),
            Some(vector_header),
            "preheader should enter the vector main loop first"
        );
        assert!(func.block(original_header).preds.contains(&vector_header));

        let header_ops: Vec<_> = func
            .block(vector_header)
            .insts
            .iter()
            .map(|&inst_id| func.inst(inst_id).opcode)
            .collect();
        assert_eq!(
            header_ops,
            vec![
                AArch64Opcode::AddRI,
                AArch64Opcode::CmpRR,
                AArch64Opcode::BCond,
                AArch64Opcode::B,
            ],
            "vector guard checks i + 3 < n before storing four lanes"
        );
        assert_eq!(
            func.inst(func.block(vector_header).insts[0]).operands[2],
            MachOperand::Imm(3)
        );
        assert_eq!(
            func.inst(func.block(vector_header).insts[2]).operands,
            vec![MachOperand::Imm(11), MachOperand::Block(vector_body)]
        );
        assert_eq!(
            branch_target(func.inst(func.block(vector_header).insts[3])),
            Some(original_header),
            "non-multiple-of-four and small-n cases fall into scalar tail"
        );

        let body_ops: Vec<_> = func
            .block(vector_body)
            .insts
            .iter()
            .map(|&inst_id| func.inst(inst_id).opcode)
            .collect();
        assert!(body_ops.contains(&AArch64Opcode::NeonDupGen));
        assert_eq!(
            body_ops
                .iter()
                .filter(|&&opcode| opcode == AArch64Opcode::NeonInsGen)
                .count(),
            3
        );
        let st1 = func
            .block(vector_body)
            .insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::NeonSt1Post)
            .expect("vector body should contain ST1 post-index");
        assert_eq!(func.inst(st1).operands[2], MachOperand::Imm(5));

        let latch = func.block(vector_latch);
        assert_eq!(func.inst(latch.insts[0]).opcode, AArch64Opcode::AddRI);
        assert_eq!(func.inst(latch.insts[0]).operands[2], MachOperand::Imm(4));
        assert_eq!(
            branch_target(func.inst(latch.insts[1])),
            Some(vector_header)
        );
    }

    #[test]
    fn test_imported_o0_i32_induction_store_accepts_fused_header_and_hoisted_one() {
        let mut func = make_imported_o0_i32_induction_store_loop();
        let header = BlockId(1);
        let body = BlockId(2);

        let one_inst = func.block(body).insts[0];
        func.block_mut(body).insts.remove(0);
        let preheader_branch_pos = func.block(func.entry).insts.len() - 1;
        func.block_mut(func.entry)
            .insts
            .insert(preheader_branch_pos, one_inst);

        let branch_body = func.block(header).insts[3];
        func.inst_mut(branch_body).operands[0] = MachOperand::Imm(11);
        func.block_mut(header).insts.drain(1..3);

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let results = rewrite_i32_induction_store_loops(&mut func, &la, None);

        assert_eq!(results.len(), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 1);
        assert_eq!(
            count_opcode(&func, AArch64Opcode::StrRI),
            1,
            "original scalar loop remains available for the dynamic tail"
        );
    }

    #[test]
    fn test_imported_o0_i32_induction_store_accepts_post_sroa_alias_shape() {
        let mut func = make_imported_o0_i32_induction_store_loop();
        let preheader = func.entry;
        let header = BlockId(1);
        let body = BlockId(2);
        let latch = BlockId(4);

        let index_state = VReg::new(22, RegClass::Gpr32);
        let bound_state = VReg::new(21, RegClass::Gpr32);
        let base_state = VReg::new(20, RegClass::Gpr64);
        let header_index = VReg::new(23, RegClass::Gpr32);
        let header_bound = VReg::new(24, RegClass::Gpr32);
        let body_index = VReg::new(25, RegClass::Gpr32);
        let body_base = VReg::new(26, RegClass::Gpr64);
        let latch_index = VReg::new(27, RegClass::Gpr32);
        let original_index = VReg::new(0, RegClass::Gpr32);
        let original_bound = VReg::new(1, RegClass::Gpr32);
        let original_base = VReg::new(6, RegClass::Gpr64);

        let init_index_state = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(index_state),
                MachOperand::VReg(original_index),
            ],
        ));
        let init_bound_state = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(bound_state),
                MachOperand::VReg(original_bound),
            ],
        ));
        let init_base_state = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(base_state),
                MachOperand::VReg(original_base),
            ],
        ));
        let preheader_branch_pos = func.block(preheader).insts.len() - 1;
        func.block_mut(preheader).insts.splice(
            preheader_branch_pos..preheader_branch_pos,
            [init_index_state, init_bound_state, init_base_state],
        );

        let copy_header_index = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(header_index),
                MachOperand::VReg(index_state),
            ],
        ));
        let copy_header_bound = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(header_bound),
                MachOperand::VReg(bound_state),
            ],
        ));
        func.block_mut(header)
            .insts
            .splice(0..0, [copy_header_index, copy_header_bound]);
        let cmp = func.block(header).insts[2];
        func.inst_mut(cmp).operands = vec![
            MachOperand::VReg(header_index),
            MachOperand::VReg(header_bound),
        ];

        let copy_body_index = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(body_index),
                MachOperand::VReg(index_state),
            ],
        ));
        let copy_body_base = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(body_base), MachOperand::VReg(base_state)],
        ));
        func.block_mut(body)
            .insts
            .splice(0..0, [copy_body_index, copy_body_base]);
        let body_insts = func.block(body).insts.clone();
        func.inst_mut(body_insts[3]).operands[1] = MachOperand::VReg(body_index);
        func.inst_mut(body_insts[4]).operands[1] = MachOperand::VReg(body_index);
        func.inst_mut(body_insts[5]).operands[3] = MachOperand::VReg(body_base);

        let copy_latch_index = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MachOperand::VReg(latch_index),
                MachOperand::VReg(index_state),
            ],
        ));
        func.block_mut(latch).insts.insert(0, copy_latch_index);
        let latch_insts = func.block(latch).insts.clone();
        func.inst_mut(latch_insts[1]).operands[1] = MachOperand::VReg(latch_index);
        func.inst_mut(latch_insts[2]).operands[0] = MachOperand::VReg(index_state);

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        assert_eq!(la.all_loops().count(), 1, "post-SROA CFG remains natural");

        let results = rewrite_i32_induction_store_loops(&mut func, &la, None);

        assert_eq!(results.len(), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 1);
        assert!(
            func.insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::CmpRR
                    && inst.operands.get(1) == Some(&MachOperand::VReg(bound_state))
            }),
            "vector guard should compare against the canonical SROA bound state"
        );
        assert!(
            func.insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::AddRI
                    && inst.operands
                        == [
                            MachOperand::VReg(index_state),
                            MachOperand::VReg(index_state),
                            MachOperand::Imm(4),
                        ]
            }),
            "vector latch should advance the canonical SROA induction state"
        );
    }

    fn make_stack_slot_backed_i32_induction_store_loop() -> MachFunction {
        let mut func = make_imported_o0_i32_induction_store_loop();
        let preheader = func.entry;
        let header = BlockId(1);
        let body = BlockId(2);
        let latch = BlockId(4);

        let slot_addr = VReg::new(30, RegClass::Gpr64);
        let header_index = VReg::new(31, RegClass::Gpr32);
        let body_index = VReg::new(32, RegClass::Gpr32);
        let latch_index = VReg::new(33, RegClass::Gpr32);
        let original_index = VReg::new(0, RegClass::Gpr32);
        let slot = StackSlotId(0);

        let slot_addr_inst = func.push_inst(MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::VReg(slot_addr),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::SP),
                MachOperand::StackSlot(slot),
            ],
        ));
        func.block_mut(preheader).insts.insert(0, slot_addr_inst);

        let init_store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(original_index),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        let preheader_branch_pos = func.block(preheader).insts.len() - 1;
        func.block_mut(preheader)
            .insts
            .insert(preheader_branch_pos, init_store);

        let header_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(header_index),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        func.block_mut(header).insts.insert(0, header_load);
        let header_cmp = func
            .block(header)
            .insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::CmpRR)
            .expect("header compare");
        func.inst_mut(header_cmp).operands[0] = MachOperand::VReg(header_index);

        let body_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(body_index),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        func.block_mut(body).insts.insert(1, body_load);
        let body_insts = func.block(body).insts.clone();
        let body_add = body_insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::AddRR)
            .expect("body value add");
        func.inst_mut(body_add).operands[1] = MachOperand::VReg(body_index);
        let body_sxtw = body_insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::Sxtw)
            .expect("body sign extend");
        func.inst_mut(body_sxtw).operands[1] = MachOperand::VReg(body_index);

        let latch_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(latch_index),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        ));
        func.block_mut(latch).insts.insert(0, latch_load);
        let latch_insts = func.block(latch).insts.clone();
        let latch_step = latch_insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::AddRR)
            .expect("latch step");
        func.inst_mut(latch_step).operands[1] = MachOperand::VReg(latch_index);
        let latch_next = gpr32_vreg_from_operand(&func.inst(latch_step).operands[0]).unwrap();
        let latch_writeback = latch_insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::MovR)
            .expect("latch writeback");
        *func.inst_mut(latch_writeback) = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(latch_next),
                MachOperand::VReg(slot_addr),
                MachOperand::Imm(0),
            ],
        );

        func
    }

    #[test]
    fn test_imported_o0_i32_induction_store_accepts_stack_slot_backed_index() {
        let mut func = make_stack_slot_backed_i32_induction_store_loop();
        let initial_blocks = func.num_blocks();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let results = rewrite_i32_induction_store_loops(&mut func, &la, None);

        assert_eq!(results.len(), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 1);
        let vector_header = BlockId(initial_blocks as u32);
        assert_eq!(
            func.inst(func.block(vector_header).insts[0]).opcode,
            AArch64Opcode::LdrRI,
            "memory-backed vector loop should reload the current induction state"
        );
        let vector_latch = BlockId(initial_blocks as u32 + 2);
        assert!(
            func.block(vector_latch)
                .insts
                .iter()
                .any(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::StrRI),
            "memory-backed vector latch should publish i + 4 for the scalar tail"
        );
    }

    #[test]
    fn test_imported_o0_i32_induction_store_accepts_addri_unit_steps() {
        let mut func = make_stack_slot_backed_i32_induction_store_loop();
        let body = BlockId(2);
        let latch = BlockId(4);

        for block in [body, latch] {
            let add = func
                .block(block)
                .insts
                .iter()
                .copied()
                .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::AddRR)
                .expect("register-form unit step");
            let dst = gpr32_vreg_from_operand(&func.inst(add).operands[0]).unwrap();
            let index = gpr32_vreg_from_operand(&func.inst(add).operands[1]).unwrap();
            *func.inst_mut(add) = MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::VReg(dst),
                    MachOperand::VReg(index),
                    MachOperand::Imm(1),
                ],
            );
        }
        assert!(
            func.block(body).insts.iter().copied().any(|inst_id| {
                movz_i32_imm(func.inst(inst_id)).is_some_and(|(_, imm)| imm == 1)
            }),
            "current imported-O0 shape retains a dead body-local one before DCE"
        );

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let results = rewrite_i32_induction_store_loops(&mut func, &la, None);

        assert_eq!(results.len(), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 1);
    }

    #[test]
    fn test_imported_o0_i32_induction_store_rejects_extra_body_store() {
        let mut func = make_imported_o0_i32_induction_store_loop();
        let body = BlockId(2);
        let extra = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(VReg::new(30, RegClass::Gpr32)),
                MachOperand::VReg(VReg::new(31, RegClass::Gpr64)),
                MachOperand::Imm(0),
            ],
        ));
        let insert_pos = func.block(body).insts.len() - 1;
        func.block_mut(body).insts.insert(insert_pos, extra);

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let results = rewrite_i32_induction_store_loops(&mut func, &la, None);

        assert!(
            results.is_empty(),
            "vector chunks must not skip unmatched observable side effects"
        );
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 0);
    }

    #[test]
    fn test_imported_o0_i32_induction_store_rejects_non_i32_stride() {
        let mut func = make_imported_o0_i32_induction_store_loop();
        let stride_init = func.block(func.entry).insts[1];
        func.inst_mut(stride_init).operands[1] = MachOperand::Imm(8);

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let results = rewrite_i32_induction_store_loops(&mut func, &la, None);

        assert!(
            results.is_empty(),
            "contiguous ST1.4S is only valid for i32 element stride"
        );
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::StrRI), 1);
    }

    #[test]
    fn test_i32_induction_store_pass_stops_before_generic_stale_loop_analysis() {
        let mut func = make_imported_o0_i32_induction_store_loop();
        let mut pass = VectorizationPass::new();

        assert!(pass.run(&mut func));
        assert_eq!(pass.results().len(), 1);
        assert!(
            pass.plans().is_empty(),
            "CFG-mutating store-loop rewrite should not continue into generic vectorization with stale loop analysis"
        );
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 1);
    }

    #[test]
    fn test_imported_o0_i32_reverse_accumulation_reports_consumed_noalias_inbounds_facts() {
        let (mut func, source_addr, dest_addr) = make_imported_o0_reverse_accumulation_loop();
        let metadata = ProofOptimizationMetadata::new()
            .with_inst_proof_facts(source_addr, vec![ProofFact::NoAlias, ProofFact::InBounds])
            .with_inst_proof_facts(dest_addr, vec![ProofFact::NoAlias, ProofFact::InBounds]);
        let mut pass = VectorizationPass::new();
        pass.set_proof_optimization_metadata(&metadata);

        assert!(
            pass.run(&mut func),
            "proof-accepted reverse accumulation should rewrite to a vector main loop"
        );
        let reports = pass.reverse_accumulation_reports();
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].rejection, None);
        for fact in [
            ProofFact::NoAlias,
            ProofFact::InBounds,
            ProofFact::BoundedLoop(u64::from(u32::MAX)),
            ProofFact::ParallelMap,
            ProofFact::Monotonic,
        ] {
            assert!(
                reports[0].consumed_facts.contains(&fact),
                "reverse proof report should consume {fact:?}: {:?}",
                reports[0].consumed_facts
            );
        }
        assert_eq!(pass.proof_certificates().len(), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::LdpRI), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonAddV), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::StpRI), 2);
        assert_eq!(
            count_opcode(&func, AArch64Opcode::StrRI),
            1,
            "original scalar loop remains as the dynamic tail for i <= 15"
        );

        let vector_header = BlockId(5);
        let vector_body = BlockId(6);
        let original_header = BlockId(1);
        assert_eq!(func.block(func.entry).succs, vec![vector_header]);
        assert!(func.block(original_header).preds.contains(&vector_header));
        assert_eq!(
            func.inst(func.block(vector_header).insts[0]).operands,
            vec![
                MachOperand::VReg(VReg::new(0, RegClass::Gpr32)),
                MachOperand::Imm(15)
            ]
        );
        assert_eq!(
            func.inst(func.block(vector_header).insts[1]).operands,
            vec![MachOperand::Imm(10), MachOperand::Block(vector_body)]
        );
        assert_eq!(
            branch_target(func.inst(func.block(vector_header).insts[2])),
            Some(original_header),
            "small-n and n % 16 tails fall back to the original scalar loop"
        );
        let vector_body_ops: Vec<_> = func
            .block(vector_body)
            .insts
            .iter()
            .map(|&inst_id| func.inst(inst_id).opcode)
            .collect();
        assert_eq!(
            vector_body_ops
                .iter()
                .filter(|&&opcode| opcode == AArch64Opcode::Madd)
                .count(),
            3,
            "unrolled reverse loop computes base addresses once per 16 lanes"
        );
    }

    #[test]
    fn test_reverse_accumulation_accepts_merged_latch_stack_backed_index() {
        let (mut func, source_addr, dest_addr) =
            make_merged_latch_stack_backed_reverse_accumulation_loop();
        let initial_blocks = func.num_blocks();
        let original_scalar_store_count = count_opcode(&func, AArch64Opcode::StrRI);
        let metadata = ProofOptimizationMetadata::new()
            .with_inst_proof_facts(source_addr, vec![ProofFact::NoAlias, ProofFact::InBounds])
            .with_inst_proof_facts(dest_addr, vec![ProofFact::NoAlias, ProofFact::InBounds]);
        let mut pass = VectorizationPass::new();
        pass.set_proof_optimization_metadata(&metadata);

        assert!(
            pass.run(&mut func),
            "proof-accepted merged-latch reverse accumulation should rewrite"
        );
        let reports = pass.reverse_accumulation_reports();
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].rejection, None);
        assert_eq!(reports[0].loop_body, BlockId(2));
        assert_eq!(count_opcode(&func, AArch64Opcode::LdpRI), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonAddV), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::StpRI), 2);
        assert_eq!(
            count_opcode(&func, AArch64Opcode::StrRI),
            original_scalar_store_count + 1,
            "stack-backed vector loop writes the carried reverse index back once on exit"
        );

        let vector_entry = BlockId(initial_blocks as u32);
        let vector_header = BlockId(initial_blocks as u32 + 1);
        let vector_latch = BlockId(initial_blocks as u32 + 3);
        let vector_exit = BlockId(initial_blocks as u32 + 4);
        assert_eq!(func.num_blocks(), initial_blocks + 5);
        assert_eq!(
            func.inst(func.block(vector_entry).insts[0]).opcode,
            AArch64Opcode::LdrRI,
            "stack-backed vector loop should load the current reverse index once"
        );
        assert_eq!(
            branch_target(func.inst(func.block(vector_entry).insts[1])),
            Some(vector_header)
        );
        assert_eq!(
            func.inst(func.block(vector_header).insts[0]).operands[1],
            MachOperand::Imm(15)
        );
        assert!(
            !func
                .block(vector_latch)
                .insts
                .iter()
                .any(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::StrRI),
            "stack-backed vector latch should keep the reverse index in-register"
        );
        assert!(
            func.block(vector_exit)
                .insts
                .iter()
                .any(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::StrRI),
            "stack-backed vector exit should commit the decremented reverse index"
        );
    }

    #[test]
    fn test_imported_o0_ary3_reverse_accum_accepts_cset_header_and_body_base_copies() {
        let (mut func, source_addr, dest_addr) =
            make_cset_header_stack_backed_reverse_accumulation_loop();
        let metadata = ProofOptimizationMetadata::new()
            .with_inst_proof_facts(source_addr, vec![ProofFact::NoAlias, ProofFact::InBounds])
            .with_inst_proof_facts(dest_addr, vec![ProofFact::NoAlias, ProofFact::InBounds]);
        let mut pass = VectorizationPass::new();
        pass.set_proof_optimization_metadata(&metadata);

        assert!(
            pass.run(&mut func),
            "pre-canonical CSet header and loop-local base copies should rewrite under visible facts"
        );
        let reports = pass.reverse_accumulation_reports();
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].rejection, None);
        assert_eq!(count_opcode(&func, AArch64Opcode::LdpRI), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonAddV), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::StpRI), 2);
    }

    #[test]
    fn test_imported_o0_ary3_reverse_accum_accepts_cmp_immediate_with_loop_dead_zero() {
        let (mut func, source_addr, dest_addr) =
            make_cset_header_stack_backed_reverse_accumulation_loop();
        let header = BlockId(1);
        let cmp = func
            .block(header)
            .insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::CmpRR)
            .expect("register-form compare against zero");
        let index = gpr32_vreg_from_operand(&func.inst(cmp).operands[0]).unwrap();
        *func.inst_mut(cmp) = MachInst::new(
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(index), MachOperand::Imm(0)],
        );
        let zero = func
            .block(header)
            .insts
            .iter()
            .copied()
            .find_map(|inst_id| {
                movz_i32_imm(func.inst(inst_id)).and_then(|(zero, imm)| (imm == 0).then_some(zero))
            })
            .expect("pre-canonical selector shape retains a zero materialization");
        let live_out = alloc_fresh_vreg(&mut func, RegClass::Gpr32);
        let live_out_use = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(live_out), MachOperand::VReg(zero)],
        ));
        let exit = BlockId(3);
        let insert_before_ret = func.block(exit).insts.len() - 1;
        func.block_mut(exit)
            .insts
            .insert(insert_before_ret, live_out_use);

        let metadata = ProofOptimizationMetadata::new()
            .with_inst_proof_facts(source_addr, vec![ProofFact::NoAlias, ProofFact::InBounds])
            .with_inst_proof_facts(dest_addr, vec![ProofFact::NoAlias, ProofFact::InBounds]);
        let mut pass = VectorizationPass::new();
        pass.set_proof_optimization_metadata(&metadata);

        assert!(
            pass.run(&mut func),
            "CmpRI #0 must tolerate a loop-dead pre-canonical zero with an outside-loop use"
        );
        assert_eq!(count_opcode(&func, AArch64Opcode::LdpRI), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonAddV), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::StpRI), 2);
    }

    #[test]
    fn test_reverse_accumulation_reports_missing_noalias_rejection() {
        let (mut func, source_addr, dest_addr) = make_imported_o0_reverse_accumulation_loop();
        let metadata = ProofOptimizationMetadata::new()
            .with_inst_proof_facts(source_addr, vec![ProofFact::NoAlias, ProofFact::InBounds])
            .with_inst_proof_facts(dest_addr, vec![ProofFact::InBounds]);
        let mut pass = VectorizationPass::new();
        pass.set_proof_optimization_metadata(&metadata);

        assert!(!pass.run(&mut func));
        let rejection = pass.reverse_accumulation_reports()[0]
            .rejection
            .expect("missing destination NoAlias must reject the candidate");
        assert_eq!(rejection, ReverseAccumulationRejection::MissingDestNoAlias);
        assert_eq!(rejection.missing_fact(), "NoAlias");
        assert_eq!(
            rejection.detail(),
            "destination array address is not proven noalias"
        );
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonSt1Post), 0);
    }

    #[test]
    fn test_i64_bitreverse_loop_rewrites_to_rev64_16b_rbit_16b() {
        let (mut func, rbit_id) = make_bitreverse_loop(RegClass::Gpr64);
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::I64);
        assert_eq!(plan.arrangement, NeonArrangement::D2);
        assert_eq!(plan.vf, 2);
        assert_eq!(plan.trip_count, Some(64));
        assert_eq!(plan.vectorizable_insts, vec![rbit_id]);
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.insts_rewritten, 1);
        assert_eq!(result.vector_trip_count, Some(32));

        let rev = func.inst(rbit_id);
        assert_eq!(rev.opcode, AArch64Opcode::NeonRev64V);
        assert_eq!(rev.operands.len(), 3);
        assert_eq!(rev.operands[2], MachOperand::Imm(1));

        let header = func.block(BlockId(1));
        let pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == rbit_id)
            .expect("rewritten REV remains in loop header");
        let neon_rbit = func.inst(header.insts[pos + 1]);
        assert_eq!(neon_rbit.opcode, AArch64Opcode::NeonRbitV);
        assert_eq!(neon_rbit.operands.len(), 3);
        assert_eq!(neon_rbit.operands[2], MachOperand::Imm(1));
    }

    #[test]
    fn test_i32_bitreverse_ordered_sub_bridge_replays_lanes() {
        let (mut func, rbit_id, uxtw_id, sub_id, accumulator) =
            make_i32_bitreverse_ordered_sub_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::I32);
        assert_eq!(plan.vectorizable_insts, vec![rbit_id]);
        assert_eq!(
            plan.ordered_sub_reductions,
            vec![OrderedSubReduction {
                producer_inst: rbit_id,
                extension_inst: Some(uxtw_id),
                lane_value: VReg::new(11, RegClass::Gpr32),
                reducer_inst: sub_id,
                writeback_inst: None,
                accumulator_load_inst: None,
                accumulator,
                kind: OrderedSubReductionKind::I32ZextToI64,
            }]
        );
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.ordered_sub_reductions_recognized, 1);
        assert_eq!(func.inst(rbit_id).opcode, AArch64Opcode::NeonRev32V);
        assert_eq!(func.inst(uxtw_id).opcode, AArch64Opcode::Nop);
        assert_eq!(func.inst(sub_id).opcode, AArch64Opcode::NeonUmovGen);

        let header = func.block(BlockId(1));
        let bridge_pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == sub_id)
            .expect("bridge starts at original reducer");
        let bridge = &header.insts[bridge_pos..bridge_pos + 12];
        for lane in 0..4 {
            let umov = func.inst(bridge[lane * 3]);
            assert_eq!(umov.opcode, AArch64Opcode::NeonUmovGen);
            assert_eq!(umov.operands[2], MachOperand::Imm(lane as i64));
            assert_eq!(umov.operands[3], MachOperand::Imm(4));

            let uxtw = func.inst(bridge[lane * 3 + 1]);
            assert_eq!(uxtw.opcode, AArch64Opcode::Uxtw);

            let sub = func.inst(bridge[lane * 3 + 2]);
            assert_eq!(sub.opcode, AArch64Opcode::SubRR);
            assert_eq!(sub.operands[0], MachOperand::VReg(accumulator));
            assert_eq!(sub.operands[1], MachOperand::VReg(accumulator));
            assert_eq!(
                sub.operands[2], uxtw.operands[0],
                "lane {lane} subtract should consume its widened lane value"
            );
        }
    }

    #[test]
    fn test_i64_bitreverse_ordered_sub_bridge_replays_d_lanes() {
        let (mut func, rbit_id, sub_id, accumulator) = make_i64_bitreverse_ordered_sub_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::I64);
        assert_eq!(plan.vectorizable_insts, vec![rbit_id]);
        assert_eq!(
            plan.ordered_sub_reductions,
            vec![OrderedSubReduction {
                producer_inst: rbit_id,
                extension_inst: None,
                lane_value: VReg::new(11, RegClass::Gpr64),
                reducer_inst: sub_id,
                writeback_inst: None,
                accumulator_load_inst: None,
                accumulator,
                kind: OrderedSubReductionKind::I64,
            }]
        );
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.ordered_sub_reductions_recognized, 1);
        assert_eq!(func.inst(rbit_id).opcode, AArch64Opcode::NeonRev64V);
        assert_eq!(func.inst(sub_id).opcode, AArch64Opcode::NeonUmovGen);

        let header = func.block(BlockId(1));
        let bridge_pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == sub_id)
            .expect("bridge starts at original reducer");
        let bridge = &header.insts[bridge_pos..bridge_pos + 4];
        for lane in 0..2 {
            let umov = func.inst(bridge[lane * 2]);
            assert_eq!(umov.opcode, AArch64Opcode::NeonUmovGen);
            assert_eq!(umov.operands[2], MachOperand::Imm(lane as i64));
            assert_eq!(umov.operands[3], MachOperand::Imm(8));

            let sub = func.inst(bridge[lane * 2 + 1]);
            assert_eq!(sub.opcode, AArch64Opcode::SubRR);
            assert_eq!(sub.operands[0], MachOperand::VReg(accumulator));
            assert_eq!(sub.operands[1], MachOperand::VReg(accumulator));
            assert_eq!(
                sub.operands[2], umov.operands[0],
                "lane {lane} subtract should consume extracted D lane"
            );
        }
    }

    #[test]
    fn test_mixed_width_revertbits_sub_loop_uses_sxtw_induction_lanes() {
        let (
            mut func,
            rbit32,
            uxtw,
            sub32,
            sxtw,
            rbit64,
            sub64,
            current,
            next,
            acc64,
            writeback32,
            writeback64,
        ) = make_mixed_width_revertbits_sub_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::I64);
        assert_eq!(plan.vf, 2);
        assert_eq!(plan.vectorizable_insts, vec![rbit32, rbit64]);
        assert_eq!(
            plan.induction,
            Some(VectorInduction {
                step_inst: func
                    .block(BlockId(1))
                    .insts
                    .iter()
                    .copied()
                    .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::AddRR)
                    .unwrap(),
                scalar_current: current,
                scalar_current_alias: Some(VReg::new(36, RegClass::Gpr32)),
                scalar_next: next,
                sign_extend_inst: Some(sxtw),
                sign_extended_current: Some(VReg::new(14, RegClass::Gpr64)),
                step: 1,
            })
        );
        assert_eq!(plan.ordered_sub_reductions.len(), 2);
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.vector_trip_count, Some(32));
        assert_eq!(func.inst(rbit32).opcode, AArch64Opcode::NeonRev32V);
        assert_eq!(func.inst(rbit32).operands[2], MachOperand::Imm(0));
        assert_eq!(func.inst(rbit64).opcode, AArch64Opcode::NeonRev64V);
        assert_eq!(func.inst(rbit64).operands[2], MachOperand::Imm(1));
        assert_eq!(func.inst(sxtw).opcode, AArch64Opcode::Nop);
        assert_eq!(func.inst(writeback32).opcode, AArch64Opcode::Nop);
        assert_eq!(func.inst(writeback64).opcode, AArch64Opcode::Nop);

        let header = func.block(BlockId(1));
        let rbit32_pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == rbit32)
            .expect("rewritten i32 REV remains in header");
        let lane_setup = &header.insts[rbit32_pos - 7..rbit32_pos];
        assert_eq!(func.inst(lane_setup[0]).opcode, AArch64Opcode::NeonDupGen);
        assert_eq!(func.inst(lane_setup[1]).opcode, AArch64Opcode::Sxtw);
        assert_eq!(func.inst(lane_setup[2]).opcode, AArch64Opcode::NeonDupGen);
        assert_eq!(
            func.inst(lane_setup[2]).operands[1],
            func.inst(lane_setup[1]).operands[0],
            "wide lane seed must use the freshly inserted SXTW, not the original scalar SXTW"
        );

        let bridge32_pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == sub32)
            .expect("i32 ordered bridge starts at original reducer");
        assert_eq!(
            func.inst(header.insts[bridge32_pos]).opcode,
            AArch64Opcode::NeonUmovGen
        );
        assert_eq!(
            func.inst(header.insts[bridge32_pos + 3]).opcode,
            AArch64Opcode::NeonUmovGen,
            "VF=2 i32 bridge replays two lanes"
        );

        let bridge64_pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == sub64)
            .expect("i64 ordered bridge starts at original reducer");
        for lane in 0..2 {
            let umov = func.inst(header.insts[bridge64_pos + lane * 2]);
            assert_eq!(umov.opcode, AArch64Opcode::NeonUmovGen);
            assert_eq!(umov.operands[2], MachOperand::Imm(lane as i64));
            assert_eq!(umov.operands[3], MachOperand::Imm(8));
            let sub = func.inst(header.insts[bridge64_pos + lane * 2 + 1]);
            assert_eq!(sub.opcode, AArch64Opcode::SubRR);
            assert_eq!(sub.operands[0], MachOperand::VReg(acc64));
            assert_eq!(sub.operands[1], MachOperand::VReg(acc64));
        }

        assert_eq!(func.inst(uxtw).opcode, AArch64Opcode::Nop);
    }

    #[test]
    fn test_mixed_width_revertbits_sub_loop_accepts_stack_slot_accumulators() {
        let (
            mut func,
            rbit32,
            _uxtw,
            sub32,
            _sxtw,
            rbit64,
            sub64,
            _current,
            _next,
            _acc64,
            writeback32,
            writeback64,
        ) = make_mixed_width_revertbits_sub_loop();
        let (load_acc32, load_acc64, acc32_address, acc64_address) =
            replace_mixed_width_revertbits_accumulators_with_stack_slots(
                &mut func,
                writeback32,
                writeback64,
            );
        let acc32_loaded = VReg::new(34, RegClass::Gpr64);
        let acc64_loaded = VReg::new(35, RegClass::Gpr64);

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::I64);
        assert_eq!(plan.vectorizable_insts, vec![rbit32, rbit64]);
        assert_eq!(plan.ordered_sub_reductions.len(), 2);
        assert_eq!(plan.ordered_sub_reductions[0].accumulator, acc32_loaded);
        assert_eq!(
            plan.ordered_sub_reductions[0].accumulator_load_inst,
            Some(load_acc32)
        );
        assert_eq!(
            plan.ordered_sub_reductions[0].writeback_inst,
            Some(writeback32)
        );
        assert_eq!(plan.ordered_sub_reductions[1].accumulator, acc64_loaded);
        assert_eq!(
            plan.ordered_sub_reductions[1].accumulator_load_inst,
            Some(load_acc64)
        );
        assert_eq!(
            plan.ordered_sub_reductions[1].writeback_inst,
            Some(writeback64)
        );
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.ordered_sub_reductions_recognized, 2);
        assert_eq!(
            func.inst(load_acc32).opcode,
            AArch64Opcode::LdrRI,
            "stack accumulator load must seed the scalar reduction bridge"
        );
        assert_eq!(
            func.inst(load_acc64).opcode,
            AArch64Opcode::LdrRI,
            "stack accumulator load must seed the scalar reduction bridge"
        );
        assert_eq!(
            func.inst(writeback32).operands,
            vec![
                MachOperand::VReg(acc32_loaded),
                MachOperand::VReg(acc32_address),
                MachOperand::Imm(0),
            ]
        );
        assert_eq!(
            func.inst(writeback64).operands,
            vec![
                MachOperand::VReg(acc64_loaded),
                MachOperand::VReg(acc64_address),
                MachOperand::Imm(0),
            ]
        );
        assert_eq!(func.inst(sub32).opcode, AArch64Opcode::NeonUmovGen);
        assert_eq!(func.inst(sub64).opcode, AArch64Opcode::NeonUmovGen);
    }

    #[test]
    fn test_mixed_width_revertbits_sub_loop_accepts_stack_slot_induction_and_accumulators() {
        let (
            mut func,
            rbit32,
            _uxtw,
            _sub32,
            sxtw,
            rbit64,
            _sub64,
            current,
            next,
            _acc64,
            writeback32,
            writeback64,
        ) = make_mixed_width_revertbits_sub_loop();
        replace_mixed_width_revertbits_accumulators_with_stack_slots(
            &mut func,
            writeback32,
            writeback64,
        );
        let (
            _load_rbit32_current,
            _load_sxtw_current,
            _load_step_current,
            writeback_step,
            index_address,
        ) = replace_mixed_width_revertbits_induction_with_stack_slot(&mut func, current, next);

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::I64);
        assert_eq!(plan.vectorizable_insts, vec![rbit32, rbit64]);
        assert_eq!(
            plan.induction,
            Some(VectorInduction {
                step_inst: func
                    .block(BlockId(1))
                    .insts
                    .iter()
                    .copied()
                    .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::AddRR)
                    .unwrap(),
                scalar_current: VReg::new(36, RegClass::Gpr32),
                scalar_current_alias: None,
                scalar_next: next,
                sign_extend_inst: Some(sxtw),
                sign_extended_current: Some(VReg::new(14, RegClass::Gpr64)),
                step: 1,
            })
        );
        assert_eq!(plan.ordered_sub_reductions.len(), 2);
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.ordered_sub_reductions_recognized, 2);
        assert_eq!(func.inst(rbit32).opcode, AArch64Opcode::NeonRev32V);
        assert_eq!(func.inst(rbit64).opcode, AArch64Opcode::NeonRev64V);
        assert_eq!(
            func.inst(plan.induction.unwrap().step_inst).operands,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(VReg::new(36, RegClass::Gpr32)),
                MachOperand::Imm(2),
            ],
            "stack-backed mixed induction should advance by the VF=2 step from the lane seed"
        );
        assert_eq!(
            func.inst(writeback_step).operands,
            vec![
                MachOperand::VReg(next),
                MachOperand::VReg(index_address),
                MachOperand::Imm(0),
            ],
            "stack-backed induction writeback should publish the rewritten step"
        );
    }

    #[test]
    fn test_mixed_width_revertbits_sub_loop_accepts_addri_stack_slot_induction() {
        let (
            mut func,
            rbit32,
            _uxtw,
            _sub32,
            _sxtw,
            rbit64,
            _sub64,
            current,
            next,
            _acc64,
            writeback32,
            writeback64,
        ) = make_mixed_width_revertbits_sub_loop();
        replace_mixed_width_revertbits_accumulators_with_stack_slots(
            &mut func,
            writeback32,
            writeback64,
        );
        replace_mixed_width_revertbits_induction_with_stack_slot(&mut func, current, next);

        let step_inst = func
            .block(BlockId(1))
            .insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::AddRR)
            .expect("register-form stack induction step");
        let step_dst = gpr32_vreg_from_operand(&func.inst(step_inst).operands[0]).unwrap();
        let step_src = gpr32_vreg_from_operand(&func.inst(step_inst).operands[1]).unwrap();
        *func.inst_mut(step_inst) = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(step_dst),
                MachOperand::VReg(step_src),
                MachOperand::Imm(1),
            ],
        );

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);
        let lp = la.all_loops().next().unwrap();
        let mut plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(
            plan.induction.expect("AddRI induction").step_inst,
            step_inst
        );
        assert_eq!(plan.vectorizable_insts, vec![rbit32, rbit64]);
        plan.is_profitable = true;

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.ordered_sub_reductions_recognized, 2);
        assert_eq!(func.inst(rbit32).opcode, AArch64Opcode::NeonRev32V);
        assert_eq!(func.inst(rbit64).opcode, AArch64Opcode::NeonRev64V);
        assert_eq!(
            func.inst(step_inst).operands[2],
            MachOperand::Imm(2),
            "mixed-width vector induction should advance by VF=2"
        );
    }

    #[test]
    fn test_ordered_sub_bridge_rejects_wrong_accumulator_operand() {
        let (mut func, _rbit_id, sub_id, _accumulator) = make_i64_bitreverse_ordered_sub_loop();
        func.inst_mut(sub_id).operands[1] = vreg64(99);
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert!(
            plan.ordered_sub_reductions.is_empty(),
            "non-self subtract must not be treated as an ordered reduction"
        );
    }

    #[test]
    fn test_i32_eq_compare_idiom_rewrites_to_neon_cmeq_4s() {
        let (mut func, cmp_id, cset_id) = make_i32_eq_compare_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.vectorizable_insts.len(), 0);
        assert_eq!(plan.compare_idioms.len(), 1);
        assert_eq!(plan.compare_idioms[0].kind, VectorCompareKind::I32Eq);
        assert_eq!(plan.horizontal_any_reductions.len(), 0);
        assert_eq!(plan.element_type, VecElementType::I32);
        assert_eq!(plan.arrangement, NeonArrangement::S4);
        assert!(plan.is_profitable);

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.insts_rewritten, 1);
        assert_eq!(result.compare_idioms_rewritten, 1);

        let cmp = func.inst(cmp_id);
        assert_eq!(cmp.opcode, AArch64Opcode::NeonCmeqV);
        assert_eq!(cmp.operands.len(), 4);
        for operand in &cmp.operands[..3] {
            match operand {
                MachOperand::VReg(vreg) => assert_eq!(vreg.class, RegClass::Fpr128),
                other => panic!("expected SIMD vreg operand, got {other:?}"),
            }
        }
        assert_eq!(cmp.operands[3], MachOperand::Imm(5));

        let cset = func.inst(cset_id);
        assert_eq!(cset.opcode, AArch64Opcode::Nop);
        assert!(cset.operands.is_empty());
    }

    #[test]
    fn test_ay_i32_eq_horizontal_any_pattern_recognized() {
        let (func, cmp_id, cset_id, orr_id) = make_ay_i32_eq_horizontal_any_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();

        assert_eq!(plan.vectorizable_insts.len(), 0);
        assert_eq!(
            plan.compare_idioms,
            vec![VectorCompareIdiom {
                cmp_inst: cmp_id,
                cset_inst: cset_id,
                kind: VectorCompareKind::I32Eq,
            }]
        );
        assert_eq!(
            plan.horizontal_any_reductions,
            vec![HorizontalAnyReduction {
                compare: plan.compare_idioms[0],
                reducer_inst: orr_id,
                kind: HorizontalAnyReductionKind::I32EqAny,
            }]
        );
        assert_eq!(plan.element_type, VecElementType::I32);
        assert_eq!(plan.vf, 4);
        assert!(plan.is_profitable);
    }

    #[test]
    fn test_compare_idiom_use_check_is_class_exact() {
        let (mut func, cmp_id, cset_id) = make_i32_eq_compare_loop();
        let header = BlockId(1);
        let fadd = func.push_inst(MachInst::new(
            AArch64Opcode::FaddRR,
            vec![fpreg64(40), fpreg64(12), fpreg64(13)],
        ));
        func.block_mut(header).insts.insert(2, fadd);

        let idiom = VectorCompareIdiom {
            cmp_inst: cmp_id,
            cset_inst: cset_id,
            kind: VectorCompareKind::I32Eq,
        };

        assert!(
            compare_idiom_uses_are_vectorizable(&func, idiom, &[]),
            "unrelated FPR v12 use must not count as a GPR32 CSet v12 use"
        );
    }

    #[test]
    fn test_horizontal_any_reduction_discovery_is_class_exact() {
        let (mut func, cmp_id, cset_id) = make_i32_eq_compare_loop();
        let header = BlockId(1);
        let false_reducer = func.push_inst(MachInst::new(
            AArch64Opcode::OrrRR,
            vec![vreg64(30), vreg64(30), vreg64(12)],
        ));
        func.block_mut(header).insts.insert(2, false_reducer);

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let lp = la.all_loops().next().unwrap();
        let compare_idioms = find_i32_eq_compare_idioms(&func, lp);

        assert_eq!(
            compare_idioms,
            vec![VectorCompareIdiom {
                cmp_inst: cmp_id,
                cset_inst: cset_id,
                kind: VectorCompareKind::I32Eq,
            }]
        );
        assert!(
            find_horizontal_any_reductions(&func, lp, &compare_idioms).is_empty(),
            "GPR64 v12 must not be recognized as the GPR32 CSet v12 compare result"
        );
    }

    #[test]
    fn test_ay_horizontal_any_rewrites_to_umaxv_sequence() {
        let (mut func, cmp_id, cset_id, orr_id) = make_ay_i32_eq_horizontal_any_loop();

        let mut pass = VectorizationPass::new();
        let changed = pass.run(&mut func);

        assert!(
            changed,
            "horizontal-any recognition should lower through UMAXV"
        );
        assert_eq!(pass.plans().len(), 1);
        assert_eq!(pass.plans()[0].horizontal_any_reductions.len(), 1);
        assert_eq!(pass.results().len(), 1);
        assert_eq!(pass.results()[0].horizontal_reductions_recognized, 1);
        assert_eq!(func.inst(cmp_id).opcode, AArch64Opcode::NeonCmeqV);
        assert_eq!(func.inst(cset_id).opcode, AArch64Opcode::Nop);
        assert_eq!(func.inst(orr_id).opcode, AArch64Opcode::NeonUmaxv);

        let umaxv = func.inst(orr_id);
        assert_eq!(umaxv.operands.len(), 3);
        match &umaxv.operands[0] {
            MachOperand::VReg(vreg) => assert_eq!(vreg.class, RegClass::Fpr32),
            other => panic!("expected Fpr32 UMAXV dst, got {other:?}"),
        }
        match &umaxv.operands[1] {
            MachOperand::VReg(vreg) => assert_eq!(vreg.class, RegClass::Fpr128),
            other => panic!("expected Fpr128 UMAXV source, got {other:?}"),
        }
        assert_eq!(umaxv.operands[2], MachOperand::Imm(5));

        let header = func.block(BlockId(1));
        let pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == orr_id)
            .expect("rewritten reduction remains in header");
        let fmov_id = header.insts[pos + 1];
        let scalar_orr_id = header.insts[pos + 2];
        assert_eq!(func.inst(fmov_id).opcode, AArch64Opcode::FmovFprGpr);
        assert_eq!(func.inst(scalar_orr_id).opcode, AArch64Opcode::OrrRR);
    }

    #[test]
    fn test_contains4_masked_slp_pattern_recognized_without_loop() {
        let (func, fixture) = make_contains4_masked_function(Contains4MaskedOptions::default());

        let idioms = find_contains4_masked_idioms(&func, &build_def_map(&func));

        assert_eq!(idioms.len(), 1);
        assert_eq!(idioms[0].and_inst, fixture.final_and.unwrap());
        assert_eq!(idioms[0].output, fixture.output);
        assert_eq!(idioms[0].valid_mask, fixture.valid_mask);
        assert_eq!(
            idioms[0]
                .bits
                .iter()
                .map(|bit| bit.cmp_inst)
                .collect::<Vec<_>>(),
            fixture.cmp_insts
        );
    }

    #[test]
    fn test_contains4_masked_slp_rewrites_to_neon_sequence_before_loop_gate() {
        let (mut func, fixture) = make_contains4_masked_function(Contains4MaskedOptions::default());
        let final_and = fixture.final_and.unwrap();

        let mut pass = VectorizationPass::new();
        let changed = pass.run(&mut func);

        assert!(
            changed,
            "straight-line SLP should run without loop analysis"
        );
        assert_eq!(pass.plans().len(), 0, "no loop vectorization plan expected");
        assert_eq!(pass.results().len(), 1);
        assert_eq!(pass.results()[0].compare_idioms_rewritten, 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonMovi), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonInsGen), 3);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonDupGen), 2);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonUmovGen), 4);

        for inst_id in fixture.scalar_insts {
            assert_eq!(
                func.inst(inst_id).opcode,
                AArch64Opcode::Nop,
                "matched scalar instruction {inst_id:?} should be nulled"
            );
        }

        let and = func.inst(final_and);
        assert_eq!(and.opcode, AArch64Opcode::AndRR);
        assert_eq!(and.operands[0], MachOperand::VReg(fixture.output));
        assert_eq!(and.operands[2], MachOperand::VReg(fixture.valid_mask));
    }

    #[test]
    fn test_contains4_masked_slp_materializes_positioned_umov_bits_directly() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions::default());

        let mut pass = VectorizationPass::new();
        assert!(pass.run(&mut func));

        let and_immediates = func
            .insts
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::AndRI)
            .map(|inst| inst.operands[2].clone())
            .collect::<Vec<_>>();
        assert_eq!(
            and_immediates,
            vec![
                MachOperand::Imm(1),
                MachOperand::Imm(2),
                MachOperand::Imm(4),
                MachOperand::Imm(8)
            ],
            "each extracted compare lane should be masked directly into its final bit position"
        );

        assert_eq!(
            count_opcode(&func, AArch64Opcode::LslRI),
            0,
            "positioned-bit materialization should not need scalar shifts"
        );
    }

    #[test]
    fn test_contains4_masked_memory_pattern_recognized() {
        let (func, fixture) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            ..Contains4MaskedOptions::default()
        });

        let idioms = find_contains4_masked_idioms(&func, &build_def_map(&func));

        assert_eq!(idioms.len(), 1);
        let memory_chunk = idioms[0]
            .memory_chunk
            .as_ref()
            .expect("contiguous scanner loads should be attached to the idiom");
        assert_eq!(Some(memory_chunk.load_insts), fixture.load_insts);
        assert_eq!(
            idioms[0]
                .bits
                .iter()
                .map(|bit| bit.lane_value)
                .collect::<Vec<_>>(),
            vec![
                VReg::new(0, RegClass::Gpr32),
                VReg::new(1, RegClass::Gpr32),
                VReg::new(2, RegClass::Gpr32),
                VReg::new(3, RegClass::Gpr32)
            ]
        );
    }

    #[test]
    fn test_contains4_masked_memory_rewrite_is_disabled_by_default() {
        let (mut func, fixture) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            ..Contains4MaskedOptions::default()
        });
        let final_and = fixture.final_and.unwrap();

        let mut pass = VectorizationPass::new();
        let changed = pass.run(&mut func);

        assert!(
            !changed,
            "default scanner-memory contains4 should remain scalar until a profitable rewrite lands"
        );
        assert_eq!(pass.results().len(), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonDupGen), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonInsGen), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonUmovGen), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::LdrRI), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::CmpRR), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::CSet), 4);

        for inst_id in fixture.scalar_insts {
            assert_ne!(func.inst(inst_id).opcode, AArch64Opcode::Nop);
        }

        let and = func.inst(final_and);
        assert_eq!(and.opcode, AArch64Opcode::AndRR);
        assert_eq!(and.operands[0], MachOperand::VReg(fixture.output));
        assert_eq!(and.operands[2], MachOperand::VReg(fixture.valid_mask));
    }

    #[test]
    fn test_contains4_masked_memory_rewrites_to_ld1_sequence_when_opted_in() {
        let (mut func, fixture) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            ..Contains4MaskedOptions::default()
        });
        let final_and = fixture.final_and.unwrap();

        let mut pass = VectorizationPass::new().with_contains4_scanner_memory_rewrite(true);
        let changed = pass.run(&mut func);

        assert!(
            changed,
            "scanner-memory contains4 should vectorize when explicitly enabled"
        );
        assert_eq!(pass.results().len(), 1);
        assert_eq!(pass.results()[0].compare_idioms_rewritten, 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonDupGen), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonInsGen), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonUmovGen), 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::LdrRI), 0);

        for inst_id in fixture.scalar_insts {
            assert_eq!(
                func.inst(inst_id).opcode,
                AArch64Opcode::Nop,
                "matched scalar memory instruction {inst_id:?} should be nulled"
            );
        }

        let and_immediates = func
            .insts
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::AndRI)
            .map(|inst| inst.operands[2].clone())
            .collect::<Vec<_>>();
        assert_eq!(
            and_immediates,
            vec![
                MachOperand::Imm(1),
                MachOperand::Imm(2),
                MachOperand::Imm(4),
                MachOperand::Imm(8)
            ],
            "memory vectorization must extract exact lane mask bits"
        );

        let and = func.inst(final_and);
        assert_eq!(and.opcode, AArch64Opcode::AndRR);
        assert_eq!(and.operands[0], MachOperand::VReg(fixture.output));
        assert_eq!(and.operands[2], MachOperand::VReg(fixture.valid_mask));
    }

    #[test]
    fn test_contains4_masked_batch_scanner_rewrite_uses_inlined_ld1_path() {
        let (mut func, fixture) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new().with_contains4_scanner_batch_rewrite(true);
        let changed = pass.run(&mut func);

        assert!(
            changed,
            "inlined batch scanner contains4 should vectorize when explicitly enabled"
        );
        assert_eq!(pass.results().len(), 1);
        assert_eq!(pass.results()[0].compare_idioms_rewritten, 4);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 1);
        assert_eq!(
            count_opcode(&func, AArch64Opcode::NeonDupGen),
            1,
            "literal DUP should be materialized once for the inlined scanner chunk"
        );
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 1);
        assert_eq!(count_opcode(&func, AArch64Opcode::Bl), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::Blr), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::LdrRI), 0);
        assert_eq!(
            count_opcode(&func, AArch64Opcode::MovR),
            0,
            "dead scanner base should feed LD1Post directly instead of paying for a copy"
        );

        for inst_id in fixture.scalar_insts {
            assert_eq!(
                func.inst(inst_id).opcode,
                AArch64Opcode::Nop,
                "matched scalar scanner instruction {inst_id:?} should be nulled"
            );
        }
    }

    #[test]
    fn test_contains4_masked_batch_scanner_preserves_live_base_with_copy() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            extra_base_use_after_mask: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new().with_contains4_scanner_batch_rewrite(true);
        assert!(pass.run(&mut func));
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 1);
        assert_eq!(
            count_opcode(&func, AArch64Opcode::MovR),
            2,
            "one original live-base use plus one protective LD1Post base copy should remain"
        );
    }

    #[test]
    fn test_contains4_masked_memory_rejects_non_contiguous_loads() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            wrong_lane2_load_offset: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();
        assert!(pass.run(&mut func), "falls back to scalar-argument SLP");
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonInsGen), 3);
    }

    #[test]
    fn test_contains4_masked_memory_rejects_mixed_bases() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            mixed_lane3_load_base: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();
        assert!(pass.run(&mut func), "falls back to scalar-argument SLP");
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonInsGen), 3);
    }

    #[test]
    fn test_contains4_masked_memory_rejects_extra_load_use() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            extra_lane0_load_use: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();
        assert!(pass.run(&mut func), "falls back to scalar-argument SLP");
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonInsGen), 3);
    }

    #[test]
    fn test_contains4_masked_memory_rejects_intervening_store() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            memory_loads: true,
            store_between_memory_load_and_mask: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();
        assert!(pass.run(&mut func), "falls back to scalar-argument SLP");
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonInsGen), 3);
    }

    #[test]
    fn test_contains4_masked_slp_rejects_wrong_shift() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            wrong_lane2_shift: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();

        assert!(!pass.run(&mut func));
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 0);
    }

    #[test]
    fn test_contains4_masked_slp_rejects_non_eq_cset() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            non_eq_lane1: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();

        assert!(!pass.run(&mut func));
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 0);
    }

    #[test]
    fn test_contains4_masked_slp_rejects_mixed_literals() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            mixed_lane2_literal: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();

        assert!(!pass.run(&mut func));
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 0);
    }

    #[test]
    fn test_contains4_masked_slp_rejects_missing_final_valid_mask() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            omit_final_valid_mask: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();

        assert!(!pass.run(&mut func));
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 0);
    }

    #[test]
    fn test_contains4_masked_slp_rejects_extra_intermediate_use() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            extra_eq0_use: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();

        assert!(!pass.run(&mut func));
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 0);
    }

    #[test]
    fn test_contains4_masked_slp_rejects_ambiguous_flag_consumer() {
        let (mut func, _) = make_contains4_masked_function(Contains4MaskedOptions {
            ambiguous_lane0_flag_consumer: true,
            ..Contains4MaskedOptions::default()
        });

        let mut pass = VectorizationPass::new();

        assert!(!pass.run(&mut func));
        assert_eq!(count_opcode(&func, AArch64Opcode::NeonCmeqV), 0);
    }

    #[test]
    fn test_contains4_masked_slp_source_loc_and_provenance() {
        let (mut func, fixture) = make_contains4_masked_function(Contains4MaskedOptions::default());
        let final_and = fixture.final_and.unwrap();
        let cmp_loc = source_loc(301);
        let cset_loc = source_loc(302);
        let and_loc = source_loc(303);
        func.inst_mut(fixture.cmp_insts[0]).source_loc = Some(cmp_loc);
        func.inst_mut(fixture.cset_insts[0]).source_loc = Some(cset_loc);
        func.inst_mut(final_and).source_loc = Some(and_loc);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(
            TrustIrInstId(900),
            &[fixture.cmp_insts[0]],
            PassId::new("isel"),
        );
        provenance.record_lowering(
            TrustIrInstId(901),
            &[fixture.cset_insts[0]],
            PassId::new("isel"),
        );
        provenance.record_lowering(TrustIrInstId(902), &[final_and], PassId::new("isel"));

        let mut pass = VectorizationPass::new();
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let cmeq_id = func
            .insts
            .iter()
            .enumerate()
            .find_map(|(idx, inst)| {
                (inst.opcode == AArch64Opcode::NeonCmeqV).then_some(InstId(idx as u32))
            })
            .expect("expected generated vector compare");
        assert_eq!(
            func.inst(cmeq_id).source_loc,
            Some(cmp_loc),
            "vector compare inherits the first scalar compare location"
        );
        assert_eq!(
            func.inst(final_and).source_loc,
            Some(and_loc),
            "final mask preserves its source location"
        );

        let bridge_entry = provenance
            .get_entry(cmeq_id)
            .expect("generated vector compare should have provenance");
        assert!(matches!(
            &bridge_entry.status,
            ProvenanceStatus::CompilerGenerated { pass, reason }
                if *pass == PassId::new("vectorize")
                    && reason == "vectorize contains4_masked slp"
        ));

        let and_entry = provenance
            .get_entry(final_and)
            .expect("final and should retain merged provenance");
        assert!(and_entry.trust_ir_origins.contains(&TrustIrInstId(900)));
        assert!(and_entry.trust_ir_origins.contains(&TrustIrInstId(901)));
        assert!(and_entry.trust_ir_origins.contains(&TrustIrInstId(902)));
    }

    #[test]
    fn test_source_loc_preserved_across_ay_horizontal_any_vectorization() {
        let (mut func, cmp_id, cset_id, orr_id) = make_ay_i32_eq_horizontal_any_loop();
        let cmp_loc = source_loc(121);
        let cset_loc = source_loc(122);
        let reducer_loc = source_loc(123);
        func.inst_mut(cmp_id).source_loc = Some(cmp_loc);
        func.inst_mut(cset_id).source_loc = Some(cset_loc);
        func.inst_mut(orr_id).source_loc = Some(reducer_loc);

        let mut pass = VectorizationPass::new();
        let changed = pass.run(&mut func);

        assert!(changed, "expected horizontal-any vectorization");
        assert_eq!(func.inst(cmp_id).opcode, AArch64Opcode::NeonCmeqV);
        assert_eq!(
            func.inst(cmp_id).source_loc,
            Some(cmp_loc),
            "vectorized compare must keep the original CMP source_loc"
        );
        assert_eq!(func.inst(cset_id).opcode, AArch64Opcode::Nop);
        assert_eq!(
            func.inst(cset_id).source_loc,
            Some(cset_loc),
            "nulled CSET slot must keep its original source_loc"
        );
        assert_eq!(func.inst(orr_id).opcode, AArch64Opcode::NeonUmaxv);
        assert_eq!(
            func.inst(orr_id).source_loc,
            Some(reducer_loc),
            "rewritten horizontal reducer must keep its original source_loc"
        );

        let header = func.block(BlockId(1));
        let pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == orr_id)
            .expect("rewritten reducer remains in header");
        let fmov_id = header.insts[pos + 1];
        let scalar_orr_id = header.insts[pos + 2];
        assert_eq!(
            func.inst(fmov_id).source_loc,
            Some(reducer_loc),
            "synthesized Fmov bridge must inherit reducer source_loc"
        );
        assert_eq!(
            func.inst(scalar_orr_id).source_loc,
            Some(reducer_loc),
            "synthesized scalar Orr bridge must inherit reducer source_loc"
        );
    }

    #[test]
    fn test_vectorize_provenance_merges_compare_and_marks_horizontal_bridge() {
        let (mut func, cmp_id, cset_id, orr_id) = make_ay_i32_eq_horizontal_any_loop();
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(70), &[cmp_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(71), &[cset_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(72), &[orr_id], PassId::new("isel"));

        let mut pass = VectorizationPass::new();
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let cmp_entry = provenance
            .get_entry(cmp_id)
            .expect("vector compare should keep provenance");
        assert!(cmp_entry.trust_ir_origins.contains(&TrustIrInstId(70)));
        assert!(cmp_entry.trust_ir_origins.contains(&TrustIrInstId(71)));
        let transform = cmp_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("vectorize"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![cmp_id, cset_id]
            }
        );
        assert!(provenance.get_entry(cset_id).is_none());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(70)),
            Some(&[cmp_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(71)),
            Some(&[cmp_id][..])
        );

        let reducer_entry = provenance
            .get_entry(orr_id)
            .expect("rewritten reducer should keep provenance");
        assert_eq!(reducer_entry.trust_ir_origins, vec![TrustIrInstId(72)]);
        let transform = reducer_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("vectorize"));
        assert_eq!(transform.kind, TransformKind::Survived);

        let header = func.block(BlockId(1));
        let pos = header
            .insts
            .iter()
            .position(|&inst_id| inst_id == orr_id)
            .expect("rewritten reducer remains in header");
        for inst_id in [header.insts[pos + 1], header.insts[pos + 2]] {
            let entry = provenance
                .get_entry(inst_id)
                .expect("horizontal bridge instruction should have provenance");
            assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(72)]);
            let transform = entry.transforms.last().unwrap();
            assert_eq!(transform.pass, PassId::new("vectorize"));
            assert_eq!(
                transform.kind,
                TransformKind::Cloned { source: orr_id },
                "horizontal bridge should clone reducer provenance"
            );
        }
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(72)),
            Some(&[orr_id, header.insts[pos + 1], header.insts[pos + 2]][..])
        );
    }

    #[test]
    fn test_ay_i32_eq_horizontal_any_semantics_cover_padding_and_lanes() {
        let cases = [
            ("no-match", [10, 12, 14, 16], 99, 4, false),
            (
                "match-in-padding",
                [10, 12, i32::MAX, i32::MAX],
                i32::MAX,
                2,
                false,
            ),
            ("first-lane match", [10, 12, 14, 16], 10, 4, true),
            ("middle-lane match", [10, 12, 14, 16], 14, 4, true),
            ("last-lane match", [10, 12, 14, 16], 16, 4, true),
        ];

        for (name, lanes, literal, real_lanes, expected) in cases {
            assert_eq!(
                ay_chunk_horizontal_any(lanes, literal, real_lanes),
                expected,
                "{name}"
            );
        }

        let clauses: [&[i32]; 5] = [
            &[10, 12],
            &[20, 22, 24],
            &[30, 32, 34, 36],
            &[40, 42, 44, 46, 48],
            &[50, 52, 54, 56, 58, 60, 62],
        ];
        let matching_clause_ids: Vec<usize> = clauses
            .iter()
            .enumerate()
            .filter_map(|(idx, clause)| ay_clause_contains_literal(clause, 42).then_some(idx))
            .collect();
        assert_eq!(matching_clause_ids, vec![3]);
        assert!(!ay_clause_contains_literal(clauses[0], i32::MAX));
        assert!(!ay_clause_contains_literal(clauses[4], 999_998));
    }

    #[test]
    fn test_ay_subsumption_fixture_uses_horizontal_any_literal_scan() {
        let clauses: [&[i32]; 8] = [
            &[10, 12],
            &[10, 12, 14],
            &[20, 22, 24, 26],
            &[20, 22, 24, 26, 28],
            &[30, 32, 34, 36, 38, 40],
            &[30, 32, 34, 36, 38, 40, 42],
            &[100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122],
            &[
                100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124,
            ],
        ];

        let pairs = [
            (0, 1, true, "short true subset"),
            (1, 0, false, "longer lhs cannot subsume shorter rhs"),
            (2, 3, true, "full first chunk subset"),
            (3, 2, false, "tail literal absent"),
            (4, 5, true, "mixed padding true subset"),
            (5, 4, false, "last real lane absent"),
            (6, 7, true, "12-to-13 length true subset"),
            (7, 6, false, "tail chunk false subset"),
        ];

        for (lhs, rhs, expected, name) in pairs {
            assert_eq!(
                ay_clause_subsumes(clauses[lhs], clauses[rhs]),
                expected,
                "{name}"
            );
        }
    }

    // =========================================================================
    // Test: no-loop function returns false
    // =========================================================================

    #[test]
    fn test_no_loop_function() {
        let mut func = MachFunction::new("no_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb0, ret);

        let mut pass = VectorizationPass::new();
        let changed = pass.run(&mut func);

        assert!(!changed);
        assert!(pass.plans().is_empty());
    }

    // =========================================================================
    // Test: VectorizationPass integration via MachinePass trait
    // =========================================================================

    #[test]
    fn test_pass_finds_vectorizable_loop() {
        let mut func = make_vectorizable_add_loop();
        let mut pass = VectorizationPass::new();
        let changed = pass.run(&mut func);

        assert!(changed, "pass should find profitable vectorization");
        assert_eq!(pass.plans().len(), 1);

        let plan = &pass.plans()[0];
        assert!(plan.is_profitable);
        assert!(plan.speedup() > 1.0);
    }

    // =========================================================================
    // Test: speedup calculation
    // =========================================================================

    #[test]
    fn test_speedup_calculation() {
        let plan = VectorizationPlan {
            loop_header: BlockId(1),
            loop_latch: BlockId(3),
            trip_count: Some(100),
            element_type: VecElementType::I32,
            arrangement: NeonArrangement::S4,
            vf: 4,
            vectorizable_insts: vec![],
            compare_idioms: vec![],
            horizontal_any_reductions: vec![],
            ordered_sub_reductions: vec![],
            induction: None,
            scalar_cost: 100.0,
            neon_cost: 50.0,
            is_profitable: true,
        };
        assert!((plan.speedup() - 2.0).abs() < 0.001);

        // Zero neon cost
        let plan2 = VectorizationPlan {
            neon_cost: 0.0,
            ..plan.clone()
        };
        assert_eq!(plan2.speedup(), 0.0);
    }

    // =========================================================================
    // Test: scalar_to_neon_op mapping
    // =========================================================================

    #[test]
    fn test_scalar_to_neon_op_mapping() {
        assert_eq!(scalar_to_neon_op(AArch64Opcode::AddRR), Some(NeonOp::Add));
        assert_eq!(scalar_to_neon_op(AArch64Opcode::AddRI), Some(NeonOp::Add));
        assert_eq!(scalar_to_neon_op(AArch64Opcode::SubRR), Some(NeonOp::Sub));
        assert_eq!(scalar_to_neon_op(AArch64Opcode::MulRR), Some(NeonOp::Mul));
        assert_eq!(scalar_to_neon_op(AArch64Opcode::Neg), Some(NeonOp::Neg));
        assert_eq!(scalar_to_neon_op(AArch64Opcode::FaddRR), Some(NeonOp::Fadd));
        assert_eq!(scalar_to_neon_op(AArch64Opcode::FmulRR), Some(NeonOp::Fmul));
        assert_eq!(scalar_to_neon_op(AArch64Opcode::BicRR), Some(NeonOp::Bic));

        // No mapping
        assert_eq!(scalar_to_neon_op(AArch64Opcode::SDiv), None);
        assert_eq!(scalar_to_neon_op(AArch64Opcode::Ret), None);
        assert_eq!(scalar_to_neon_op(AArch64Opcode::CmpRR), None);
    }

    // =========================================================================
    // Test: FP loop with f64 -> 2D arrangement
    // =========================================================================

    #[test]
    fn test_fp_loop_f64_arrangement() {
        let mut func = MachFunction::new("fp_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // FP add: f64
        let fadd = func.push_inst(MachInst::new(
            AArch64Opcode::FaddRR,
            vec![fpreg64(2), fpreg64(0), fpreg64(1)],
        ));
        func.append_inst(bb1, fadd);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(5), imm(200)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model);

        assert!(plan.is_some());
        let plan = plan.unwrap();
        assert_eq!(plan.element_type, VecElementType::F64);
        assert_eq!(plan.arrangement, NeonArrangement::D2);
        assert_eq!(plan.vf, 2);
    }

    // =========================================================================
    // Test: loop with only non-vectorizable instructions returns None
    // =========================================================================

    #[test]
    fn test_loop_with_only_branches_not_vectorizable() {
        // Loop body: just cmp + bcond + branch (no vectorizable compute)
        let mut func = MachFunction::new("branch_only".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(0), imm(10)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model);

        assert!(
            plan.is_none(),
            "loop with only branches should not be vectorizable"
        );
    }

    // =========================================================================
    // Test: VecElementType coverage
    // =========================================================================

    #[test]
    fn test_vec_element_type_all_variants() {
        let cases = [
            (VecElementType::I8, 8, NeonArrangement::B16, 16),
            (VecElementType::I16, 16, NeonArrangement::H8, 8),
            (VecElementType::I32, 32, NeonArrangement::S4, 4),
            (VecElementType::I64, 64, NeonArrangement::D2, 2),
            (VecElementType::F32, 32, NeonArrangement::S4, 4),
            (VecElementType::F64, 64, NeonArrangement::D2, 2),
        ];

        for (ety, bits, arr, lanes) in cases {
            assert_eq!(ety.bits(), bits, "{:?} should have {} bits", ety, bits);
            assert_eq!(
                ety.neon_arrangement(),
                arr,
                "{:?} should map to {:?}",
                ety,
                arr
            );
            assert_eq!(ety.lanes(), lanes, "{:?} should have {} lanes", ety, lanes);
        }
    }

    // =========================================================================
    // Test: pass name
    // =========================================================================

    #[test]
    fn test_pass_name() {
        let pass = VectorizationPass::new();
        assert_eq!(pass.name(), "vectorize");
    }

    // =========================================================================
    // Test: VectorizationPlan profitability
    // =========================================================================

    #[test]
    fn test_plan_profitability_from_analysis() {
        let func = make_vectorizable_add_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();

        // With trip count 100 and i32 add (1-cycle scalar, 2-cycle NEON for
        // 4 elements at a time), NEON should be profitable:
        // Scalar: 100 * 1 = 100 cycles
        // NEON: 25 * 2 + overhead < 100
        assert!(
            plan.is_profitable,
            "i32 add loop with TC=100 should be profitable"
        );
        assert!(plan.neon_cost < plan.scalar_cost);
    }

    // =========================================================================
    // IR Rewriting Tests
    // =========================================================================

    /// Helper: build a vectorizable loop with multiple arithmetic ops.
    /// Trip count = 100, i32 element type, ops: add + sub + mul.
    fn make_multi_op_loop() -> MachFunction {
        let mut func =
            MachFunction::new("multi_op_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block(); // header
        let bb2 = func.create_block(); // exit
        let bb3 = func.create_block(); // latch

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // add v2 = v0 + v1
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg32(2), vreg32(0), vreg32(1)],
        ));
        func.append_inst(bb1, add);

        // sub v3 = v2 - v1
        let sub = func.push_inst(MachInst::new(
            AArch64Opcode::SubRR,
            vec![vreg32(3), vreg32(2), vreg32(1)],
        ));
        func.append_inst(bb1, sub);

        // mul v4 = v3 * v0
        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg32(4), vreg32(3), vreg32(0)],
        ));
        func.append_inst(bb1, mul);

        // cmp + bcond
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(5), imm(100)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        func
    }

    /// Helper: build a vectorizable loop with trip count that has a
    /// remainder when divided by VF. Trip count = 102, i32 (VF=4),
    /// remainder = 102 % 4 = 2.
    fn make_remainder_loop() -> MachFunction {
        let mut func =
            MachFunction::new("remainder_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg32(2), vreg32(0), vreg32(1)],
        ));
        func.append_inst(bb1, add);

        // Trip count = 102 (102 % 4 = 2 remainder)
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(3), imm(102)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        func
    }

    // =========================================================================
    // Test: apply_vectorization rewrites add loop register classes
    // =========================================================================

    #[test]
    fn test_apply_vectorization_upgrades_reg_class() {
        let mut func = make_vectorizable_add_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert!(plan.is_profitable);

        let result = apply_vectorization(&mut func, &plan);
        assert!(result.is_some(), "vectorization should succeed");

        let result = result.unwrap();
        assert_eq!(
            result.insts_rewritten, 1,
            "one add instruction should be rewritten"
        );
        assert!(
            result.regs_upgraded > 0,
            "register classes should be upgraded"
        );

        // The add instruction's operands should now be Fpr128 (SIMD).
        let add_inst_id = plan.vectorizable_insts[0];
        let add_inst = func.inst(add_inst_id);
        for operand in &add_inst.operands {
            if let MachOperand::VReg(vreg) = operand {
                assert_eq!(
                    vreg.class,
                    RegClass::Fpr128,
                    "vectorized instruction operands should use Fpr128"
                );
            }
        }
    }

    // =========================================================================
    // Test: apply_vectorization appends arrangement encoding
    // =========================================================================

    #[test]
    fn test_apply_vectorization_appends_arrangement() {
        let mut func = make_vectorizable_add_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();

        apply_vectorization(&mut func, &plan);

        // The add instruction should have an extra immediate for arrangement.
        // Original: [dst, src1, src2] = 3 operands
        // After: [dst, src1, src2, arrangement_imm] = 4 operands
        let add_inst_id = plan.vectorizable_insts[0];
        let add_inst = func.inst(add_inst_id);
        assert_eq!(
            add_inst.operands.len(),
            4,
            "should have 4 operands after rewrite"
        );

        // The last operand should use the encoder's 4S arrangement code.
        let last = &add_inst.operands[3];
        assert_eq!(
            *last,
            MachOperand::Imm(5),
            "arrangement encoding should be 5 (4S)"
        );
    }

    // =========================================================================
    // Test: apply_vectorization adjusts trip count
    // =========================================================================

    #[test]
    fn test_apply_vectorization_adjusts_trip_count() {
        let mut func = make_vectorizable_add_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.trip_count, Some(100));
        assert_eq!(plan.vf, 4);

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(
            result.vector_trip_count,
            Some(25),
            "100 / 4 = 25 vector iterations"
        );
        assert_eq!(result.remainder, 0, "100 % 4 = 0 remainder");

        // Find the CMP instruction in the header and verify its immediate is 25.
        let header = plan.loop_header;
        let block = func.block(header);
        let mut found_new_cmp = false;
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::CmpRI {
                for operand in &inst.operands {
                    if let MachOperand::Imm(val) = operand
                        && *val == 25
                    {
                        found_new_cmp = true;
                    }
                }
            }
        }
        assert!(found_new_cmp, "CMP immediate should be adjusted to 25");
    }

    // =========================================================================
    // Test: apply_vectorization creates epilogue for remainder
    // =========================================================================

    #[test]
    fn test_apply_vectorization_creates_epilogue() {
        let mut func = make_remainder_loop();
        let initial_blocks = func.num_blocks();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.trip_count, Some(102));

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert!(
            result.has_epilogue,
            "should create epilogue for remainder=2"
        );
        assert_eq!(result.remainder, 2, "102 % 4 = 2");
        assert_eq!(result.vector_trip_count, Some(25), "102 / 4 = 25");

        // New blocks should have been created (epilogue + epilogue_exit).
        assert!(
            func.num_blocks() > initial_blocks,
            "epilogue blocks should be created: {} > {}",
            func.num_blocks(),
            initial_blocks
        );
    }

    // =========================================================================
    // Test: apply_vectorization with no remainder skips epilogue
    // =========================================================================

    #[test]
    fn test_apply_vectorization_no_epilogue_when_exact() {
        let mut func = make_vectorizable_add_loop();
        let initial_blocks = func.num_blocks();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.trip_count, Some(100));

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert!(
            !result.has_epilogue,
            "no epilogue needed when TC is exactly divisible"
        );
        assert_eq!(result.remainder, 0);
        assert_eq!(
            func.num_blocks(),
            initial_blocks,
            "no new blocks when no epilogue"
        );
    }

    // =========================================================================
    // Test: apply_vectorization returns None for non-profitable plan
    // =========================================================================

    #[test]
    fn test_apply_vectorization_rejects_non_profitable() {
        let plan = VectorizationPlan {
            loop_header: BlockId(1),
            loop_latch: BlockId(3),
            trip_count: Some(100),
            element_type: VecElementType::I32,
            arrangement: NeonArrangement::S4,
            vf: 4,
            vectorizable_insts: vec![InstId(1)],
            compare_idioms: vec![],
            horizontal_any_reductions: vec![],
            ordered_sub_reductions: vec![],
            induction: None,
            scalar_cost: 50.0,
            neon_cost: 100.0,
            is_profitable: false,
        };

        let mut func = make_vectorizable_add_loop();
        let result = apply_vectorization(&mut func, &plan);
        assert!(result.is_none(), "non-profitable plan should return None");
    }

    // =========================================================================
    // Test: apply_vectorization returns None for empty plan
    // =========================================================================

    #[test]
    fn test_apply_vectorization_rejects_empty_insts() {
        let plan = VectorizationPlan {
            loop_header: BlockId(1),
            loop_latch: BlockId(3),
            trip_count: Some(100),
            element_type: VecElementType::I32,
            arrangement: NeonArrangement::S4,
            vf: 4,
            vectorizable_insts: vec![],
            compare_idioms: vec![],
            horizontal_any_reductions: vec![],
            ordered_sub_reductions: vec![],
            induction: None,
            scalar_cost: 100.0,
            neon_cost: 50.0,
            is_profitable: true,
        };

        let mut func = make_vectorizable_add_loop();
        let result = apply_vectorization(&mut func, &plan);
        assert!(
            result.is_none(),
            "plan with no vectorizable insts should return None"
        );
    }

    // =========================================================================
    // Test: multi-op loop rewrites all vectorizable instructions
    // =========================================================================

    #[test]
    fn test_apply_vectorization_multi_op() {
        let mut func = make_multi_op_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();

        // Should find add, sub, mul as vectorizable.
        assert_eq!(
            plan.vectorizable_insts.len(),
            3,
            "add, sub, mul should all be vectorizable"
        );

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.insts_rewritten, 3, "all 3 ops should be rewritten");

        // Verify each rewritten instruction has Fpr128 register class.
        for &inst_id in &plan.vectorizable_insts {
            let inst = func.inst(inst_id);
            for operand in &inst.operands {
                if let MachOperand::VReg(vreg) = operand {
                    assert_eq!(
                        vreg.class,
                        RegClass::Fpr128,
                        "inst {:?} operand should be Fpr128",
                        inst_id
                    );
                }
            }
        }
    }

    // =========================================================================
    // Test: VectorizationPass produces results after rewriting
    // =========================================================================

    #[test]
    fn test_pass_produces_results() {
        let mut func = make_vectorizable_add_loop();
        let mut pass = VectorizationPass::new();
        let changed = pass.run(&mut func);

        assert!(changed);
        assert!(!pass.results().is_empty(), "should have rewriting results");

        let result = &pass.results()[0];
        assert!(result.insts_rewritten > 0);
    }

    // =========================================================================
    // Test: simd_reg_class_for_element always returns Fpr128
    // =========================================================================

    #[test]
    fn test_simd_reg_class_all_elements() {
        let element_types = [
            VecElementType::I8,
            VecElementType::I16,
            VecElementType::I32,
            VecElementType::I64,
            VecElementType::F32,
            VecElementType::F64,
        ];
        for ety in &element_types {
            assert_eq!(
                simd_reg_class_for_element(*ety),
                RegClass::Fpr128,
                "{:?} should map to Fpr128",
                ety
            );
        }
    }

    // =========================================================================
    // Test: rewrite_opcode_for_neon maps correctly
    // =========================================================================

    #[test]
    fn test_rewrite_opcode_for_neon() {
        // Vectorizable opcodes should succeed
        let (opcode, neon_op) = rewrite_opcode_for_neon(AArch64Opcode::AddRR).unwrap();
        assert_eq!(opcode, AArch64Opcode::AddRR);
        assert_eq!(neon_op, NeonOp::Add);

        let (opcode, neon_op) = rewrite_opcode_for_neon(AArch64Opcode::SubRR).unwrap();
        assert_eq!(opcode, AArch64Opcode::SubRR);
        assert_eq!(neon_op, NeonOp::Sub);

        let (opcode, neon_op) = rewrite_opcode_for_neon(AArch64Opcode::FmulRR).unwrap();
        assert_eq!(opcode, AArch64Opcode::FmulRR);
        assert_eq!(neon_op, NeonOp::Fmul);

        // Non-vectorizable opcodes should return None
        assert!(rewrite_opcode_for_neon(AArch64Opcode::SDiv).is_none());
        assert!(rewrite_opcode_for_neon(AArch64Opcode::Ret).is_none());
        assert!(rewrite_opcode_for_neon(AArch64Opcode::LdrRI).is_none());
    }

    // =========================================================================
    // Test: VectorizationResult fields are correct for exact divisibility
    // =========================================================================

    #[test]
    fn test_vectorization_result_exact_division() {
        let mut func = make_vectorizable_add_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.vector_trip_count, Some(25));
        assert_eq!(result.remainder, 0);
        assert!(!result.has_epilogue);
        assert!(result.insts_rewritten > 0);
        assert!(result.regs_upgraded > 0);
    }

    // =========================================================================
    // Test: VectorizationResult fields are correct for remainder case
    // =========================================================================

    #[test]
    fn test_vectorization_result_with_remainder() {
        let mut func = make_remainder_loop();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.vector_trip_count, Some(25));
        assert_eq!(result.remainder, 2);
        assert!(result.has_epilogue);
        assert!(result.insts_rewritten > 0);
    }

    // =========================================================================
    // Test: epilogue block contains scalar copies of vectorized instructions
    // =========================================================================

    #[test]
    fn test_epilogue_contains_scalar_instructions() {
        let mut func = make_remainder_loop();
        let initial_blocks = func.num_blocks();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        let num_vec_insts = plan.vectorizable_insts.len();

        apply_vectorization(&mut func, &plan);

        // The epilogue block is the first new block after original blocks.
        let epilogue_block_id = BlockId(initial_blocks as u32);
        let epilogue_block = func.block(epilogue_block_id);

        // Epilogue should contain: scalar copies of vectorized insts + CMP + BCond
        // = num_vec_insts + 2
        assert_eq!(
            epilogue_block.insts.len(),
            num_vec_insts + 2,
            "epilogue should have {} insts ({}+2)",
            num_vec_insts + 2,
            num_vec_insts
        );

        // The scalar copy should use Gpr32 (since element type is I32).
        let first_inst_id = epilogue_block.insts[0];
        let first_inst = func.inst(first_inst_id);
        assert_eq!(
            first_inst.opcode,
            AArch64Opcode::AddRR,
            "epilogue should copy the add"
        );
        for operand in &first_inst.operands {
            if let MachOperand::VReg(vreg) = operand {
                assert_eq!(
                    vreg.class,
                    RegClass::Gpr32,
                    "epilogue operands should be scalar (Gpr32)"
                );
            }
        }
    }

    #[test]
    fn test_source_loc_preserved_on_vectorized_scalar_epilogue_clone() {
        let mut func = make_remainder_loop();
        let initial_blocks = func.num_blocks();
        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        let scalar_inst_id = plan.vectorizable_insts[0];
        let loc = source_loc(211);
        func.inst_mut(scalar_inst_id).source_loc = Some(loc);

        let result = apply_vectorization(&mut func, &plan).unwrap();

        assert!(result.has_epilogue, "expected remainder epilogue");
        assert_eq!(
            func.inst(scalar_inst_id).source_loc,
            Some(loc),
            "vectorized in-place instruction must keep its source_loc"
        );

        let epilogue_block_id = BlockId(initial_blocks as u32);
        let epilogue_block = func.block(epilogue_block_id);
        let cloned_inst_id = epilogue_block.insts[0];
        assert_eq!(func.inst(cloned_inst_id).opcode, AArch64Opcode::AddRR);
        assert_eq!(
            func.inst(cloned_inst_id).source_loc,
            Some(loc),
            "scalar epilogue clone must inherit the vectorized instruction source_loc"
        );
    }

    #[test]
    fn test_vectorize_provenance_marks_scalar_rewrite_trip_count_and_epilogue() {
        let mut func = make_remainder_loop();
        let initial_blocks = func.num_blocks();
        let header = BlockId(1);
        let add_id = func
            .block(header)
            .insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::AddRR)
            .expect("expected vectorizable add");
        let cmp_id = func
            .block(header)
            .insts
            .iter()
            .copied()
            .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::CmpRI)
            .expect("expected trip-count compare");

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(80), &[add_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(81), &[cmp_id], PassId::new("isel"));

        let mut pass = VectorizationPass::new();
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let add_entry = provenance
            .get_entry(add_id)
            .expect("vectorized add should keep provenance");
        assert_eq!(add_entry.trust_ir_origins, vec![TrustIrInstId(80)]);
        let transform = add_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("vectorize"));
        assert_eq!(transform.kind, TransformKind::Survived);
        let cmp_entry = provenance
            .get_entry(cmp_id)
            .expect("trip-count compare should keep provenance");
        assert_eq!(cmp_entry.trust_ir_origins, vec![TrustIrInstId(81)]);
        let transform = cmp_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("vectorize"));
        assert_eq!(transform.kind, TransformKind::Survived);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(81)),
            Some(&[cmp_id][..])
        );
        assert!(
            func.inst(cmp_id).operands.contains(&MachOperand::Imm(25)),
            "trip-count compare should be rewritten from 102 to 25"
        );

        let epilogue_block = func.block(BlockId(initial_blocks as u32));
        let epilogue_exit = func.block(BlockId(initial_blocks as u32 + 1));
        let cloned_add_id = epilogue_block.insts[0];
        let cloned_add_entry = provenance
            .get_entry(cloned_add_id)
            .expect("epilogue scalar clone should have provenance");
        assert_eq!(cloned_add_entry.trust_ir_origins, vec![TrustIrInstId(80)]);
        let transform = cloned_add_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("vectorize"));
        assert_eq!(transform.kind, TransformKind::Cloned { source: add_id });
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(80)),
            Some(&[add_id, cloned_add_id][..])
        );

        for inst_id in epilogue_block
            .insts
            .iter()
            .skip(1)
            .chain(epilogue_exit.insts.iter())
        {
            let entry = provenance
                .get_entry(*inst_id)
                .expect("epilogue instruction should have provenance");
            assert!(entry.trust_ir_origins.is_empty());
            assert!(matches!(
                &entry.status,
                ProvenanceStatus::CompilerGenerated { pass, reason }
                    if *pass == PassId::new("vectorize")
                        && reason == "vectorize scalar epilogue"
            ));
        }
    }

    // =========================================================================
    // Test: full pass end-to-end with rewriting and epilogue
    // =========================================================================

    #[test]
    fn test_pass_end_to_end_with_rewriting() {
        let mut func = make_remainder_loop();
        let initial_num_insts = func.num_insts();
        let initial_num_blocks = func.num_blocks();

        let mut pass = VectorizationPass::new();
        let changed = pass.run(&mut func);

        assert!(changed, "pass should report changes");
        assert!(!pass.plans().is_empty(), "should have plans");
        assert!(!pass.results().is_empty(), "should have results");

        let result = &pass.results()[0];
        assert!(result.insts_rewritten > 0, "should rewrite instructions");
        assert!(
            result.has_epilogue,
            "should create epilogue for TC=102, VF=4"
        );

        // Function should have grown (new epilogue blocks and instructions).
        assert!(
            func.num_insts() > initial_num_insts,
            "function should have more instructions after rewriting"
        );
        assert!(
            func.num_blocks() > initial_num_blocks,
            "function should have more blocks after epilogue creation"
        );
    }

    // =========================================================================
    // Test: FP loop (f64) rewriting uses correct SIMD class
    // =========================================================================

    #[test]
    fn test_fp_loop_rewriting_uses_fpr128() {
        let mut func = MachFunction::new("fp_vec_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let fadd = func.push_inst(MachInst::new(
            AArch64Opcode::FaddRR,
            vec![fpreg64(2), fpreg64(0), fpreg64(1)],
        ));
        func.append_inst(bb1, fadd);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(5), imm(200)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

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

        let dom = DomTree::compute(&func);
        let la = LoopAnalysis::compute(&func, &dom);
        let cost_model = MultiTargetCostModel::new(CostModelGen::M1);

        let lp = la.all_loops().next().unwrap();
        let plan = analyze_loop(&func, lp, &cost_model).unwrap();
        assert_eq!(plan.element_type, VecElementType::F64);
        assert_eq!(plan.vf, 2);

        let result = apply_vectorization(&mut func, &plan).unwrap();
        assert_eq!(result.insts_rewritten, 1);

        // The FaddRR operands should now be Fpr128.
        let fadd_inst = func.inst(plan.vectorizable_insts[0]);
        for operand in &fadd_inst.operands {
            if let MachOperand::VReg(vreg) = operand {
                assert_eq!(
                    vreg.class,
                    RegClass::Fpr128,
                    "FP vectorized instruction should use Fpr128"
                );
            }
        }

        // Arrangement encoding for 2D should be 2.
        let last = fadd_inst.operands.last().unwrap();
        assert_eq!(
            *last,
            MachOperand::Imm(2),
            "f64 arrangement should encode as 2 (2D)"
        );
    }
}
