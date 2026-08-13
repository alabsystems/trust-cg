// trust-cg-opt - AArch64 If-Conversion Pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! General if-conversion pass for AArch64.
//!
//! Converts diamond and triangle CFG patterns into predicated conditional
//! select instructions (CSEL, CSINC, CSNEG), eliminating branches and
//! improving instruction-level parallelism on modern AArch64 cores.
//!
//! # Difference from CmpSelectCombine
//!
//! [`crate::cmp_select::CmpSelectCombine`] handles the narrow case where
//! both diamond arms contain exactly one MOV instruction. This pass is
//! more general:
//!
//! - **Diamond patterns**: Arms may contain up to 2 simple instructions
//!   (arithmetic, logical, moves) plus a branch — not just a single MOV.
//! - **Triangle patterns**: If-then (no else) where one arm has a single
//!   assignment that falls through to the merge block.
//! - **CSINC/CSNEG formation**: Recognizes `ADD dst, src, #1` and
//!   `NEG dst, src` patterns in diamond arms for more compact codegen.
//!
//! # Patterns
//!
//! | Pattern | Transformation |
//! |---------|---------------|
//! | Diamond: MOV + ADD #1 | `CSINC Xd, Xn, Xm, cond` |
//! | Diamond: MOV + NEG    | `CSNEG Xd, Xn, Xm, cond` |
//! | Diamond: MOV + MOV (general) | `CSEL Xd, Xn, Xm, cond` |
//! | Triangle: single assign + fallthrough | `CSEL Xd, Xn, Xd, cond` |
//!
//! # Diamond CFG Shape
//!
//! ```text
//!   header:
//!     ...
//!     CMP Xn, Xm
//!     B.cond true_block
//!   false_block:
//!     <1-2 simple insts>
//!     B join
//!   true_block:
//!     <1-2 simple insts>
//!     B join
//!   join:
//!     ...
//! ```
//!
//! # Triangle CFG Shape
//!
//! ```text
//!   header:
//!     ...
//!     CMP Xn, Xm
//!     B.cond then_block
//!     (fallthrough to join)
//!   then_block:
//!     MOV Xd, Xn (single value-producing inst)
//!     B join
//!   join:
//!     ...
//! ```
//!
//! # Profitability
//!
//! Only converts when:
//! - Each arm has at most 2 non-branch instructions
//! - No memory operations (loads/stores) in either arm
//! - No calls in either arm
//! - The branch condition is still available
//!
//! # Safety Constraints
//!
//! - Arm blocks must have exactly 1 predecessor (the header)
//! - Diamond arms must branch to the same merge block
//! - Triangle then-block must branch to the header's fallthrough successor
//! - No flag-setting instructions in arms (would clobber NZCV used by CSEL)

use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, PassId,
    ProvenanceMap, SourceLoc, SpecialReg, VReg,
};

use crate::effects::{
    aarch64_def_operand_positions, aarch64_use_operand_positions, opcode_effect, reads_flags,
    writes_flags,
};
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// AArch64 if-conversion pass.
///
/// Converts diamond and triangle CFG patterns into conditional select
/// instructions. Runs at O2+ after CmpSelectCombine (which handles the
/// simplest cases) and before DCE (which cleans up dead instructions).
pub struct IfConversion;

impl MachinePass for IfConversion {
    fn name(&self) -> &str {
        "if-convert"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_if_conversion(func, None, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_if_conversion(func, Some(provenance), None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        // The non-provenance analysis-driven driver: still supply loop analysis
        // so loop-diamond if-conversion fires (see
        // [`run_with_analyses_and_provenance`] for the borrow rationale).
        let loop_analysis = analyses.loop_analysis(func);
        run_if_conversion(func, None, Some(loop_analysis))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        // Loop analysis powers the loop-diamond profitability predicate
        // (see [`is_profitable_loop_diamond`]); the borrow of `func` inside
        // `loop_analysis` ends when it returns (the reference is tied to the
        // cache), so it is free to reborrow `func` mutably below.
        let loop_analysis = analyses.loop_analysis(func);
        run_if_conversion(func, Some(provenance), Some(loop_analysis))
    }
}

fn if_convert_pass_id() -> PassId {
    PassId::new("if-convert")
}

fn run_if_conversion(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
    loop_analysis: Option<&LoopAnalysis>,
) -> bool {
    let mut changed = false;

    // Collect diamond transforms first to avoid borrow issues.
    let diamond_xforms = collect_diamond_transforms(func, loop_analysis);
    for xform in &diamond_xforms {
        apply_diamond_transform(func, xform, provenance.as_deref_mut());
        changed = true;
    }

    // Collect triangle transforms (must re-scan after diamonds).
    let triangle_xforms = collect_triangle_transforms(func);
    for xform in &triangle_xforms {
        apply_triangle_transform(func, xform, provenance.as_deref_mut());
        changed = true;
    }

    changed
}

// ---------------------------------------------------------------------------
// Diamond if-conversion
// ---------------------------------------------------------------------------

/// A diamond transform: replaces a BCond + two arm blocks with a
/// conditional select instruction in the header.
struct DiamondTransform {
    header: BlockId,
    true_block: BlockId,
    false_block: BlockId,
    join_block: BlockId,
    /// The conditional select instruction(s) to insert before the BCond.
    new_insts: Vec<MachInst>,
    /// How each new instruction inherits provenance from removed arm insts.
    new_inst_provenance: Vec<NewInstProvenance>,
    condition_inst_id: Option<InstId>,
    bcond_inst_id: InstId,
    true_br_inst_id: InstId,
    false_br_inst_id: InstId,
    /// When the header ends in the explicit two-edge form `BCond T; B F`, this
    /// is the trailing unconditional `B F` — it is removed by
    /// [`apply_diamond_transform`] (the BCond itself is rewritten to `B join`).
    /// `None` for the fallthrough form (`BCond T` with implicit fall-through).
    header_fallthrough_br: Option<InstId>,
    /// A now-dead flag compare (the div-guard `CMP divisor, 0`) to delete along
    /// with the branch. Only set for the FULL COLLAPSE (bare div, no CSEL), and
    /// only when the compare is PROVABLY dead (its NZCV def is overwritten before
    /// any read on every path). `None` keeps the compare (always correct).
    dead_condition_inst: Option<InstId>,
}

enum NewInstProvenance {
    /// A single removed instruction is represented by the new instruction.
    Replaced(InstId),
    /// Multiple removed instructions are represented by the new instruction.
    Merged(Vec<InstId>),
}

/// Scan for diamond CFG patterns suitable for if-conversion.
fn collect_diamond_transforms(
    func: &MachFunction,
    loop_analysis: Option<&LoopAnalysis>,
) -> Vec<DiamondTransform> {
    let mut transforms = Vec::new();

    for &header_id in &func.block_order {
        let header = func.block(header_id);
        let insts_len = header.insts.len();
        let Some(&last_inst_id) = header.insts.last() else {
            continue;
        };

        // The header's branch is either the last instruction (`BCond T`, implicit
        // fall-through) or the second-to-last with an explicit trailing
        // `B F` (`BCond T; B F`). Real ISel output uses the explicit form; the
        // hand-written fall-through form appears in tests and some passes.
        let last_inst = func.inst(last_inst_id);
        let (bcond_inst_id, header_fallthrough_br) = if last_inst.opcode == AArch64Opcode::BCond {
            (last_inst_id, None)
        } else if last_inst.is_unconditional_branch() && insts_len >= 2 {
            let prev_id = header.insts[insts_len - 2];
            if func.inst(prev_id).opcode == AArch64Opcode::BCond {
                (prev_id, Some(last_inst_id))
            } else {
                continue;
            }
        } else {
            continue;
        };

        // BCond operands: [Imm(cond_code), Block(target)]
        let bcond = func.inst(bcond_inst_id);
        if bcond.operands.len() < 2 {
            continue;
        }
        let cond_encoding = match bcond.operands[0].as_imm() {
            Some(v) => v as u8,
            None => continue,
        };
        let true_block = match &bcond.operands[1] {
            MachOperand::Block(bid) => *bid,
            _ => continue,
        };
        let condition_inst_id = latest_flag_writer_before(func, header, bcond_inst_id);
        let source_loc_fallback =
            predicated_source_loc_fallback(func, bcond_inst_id, condition_inst_id);

        // Header must have exactly 2 successors.
        if header.succs.len() != 2 {
            continue;
        }

        // Determine false block: the successor that is NOT the BCond target.
        let false_block = if header.succs[0] == true_block {
            header.succs[1]
        } else if header.succs[1] == true_block {
            header.succs[0]
        } else {
            continue;
        };

        // Both arm blocks must have exactly 1 predecessor (the header).
        if func.block(true_block).preds.len() != 1 || func.block(false_block).preds.len() != 1 {
            continue;
        }

        // Both arm blocks must have exactly 1 successor (the join block).
        let true_blk = func.block(true_block);
        let false_blk = func.block(false_block);
        if true_blk.succs.len() != 1 || false_blk.succs.len() != 1 {
            continue;
        }

        // Both arms must branch to the same join block.
        let join_block = true_blk.succs[0];
        if false_blk.succs[0] != join_block {
            continue;
        }

        // Last instruction of each arm must be unconditional B.
        let (Some(&true_last_id), Some(&false_last_id)) =
            (true_blk.insts.last(), false_blk.insts.last())
        else {
            continue;
        };
        let true_last = func.inst(true_last_id);
        let false_last = func.inst(false_last_id);
        if !true_last.is_unconditional_branch() || !false_last.is_unconditional_branch() {
            continue;
        }

        // Non-branch instructions in each arm (excluding the trailing B).
        let true_body: Vec<InstId> = true_blk.insts[..true_blk.insts.len() - 1].to_vec();
        let false_body: Vec<InstId> = false_blk.insts[..false_blk.insts.len() - 1].to_vec();

        // Profitability check: at most 2 non-branch instructions per arm.
        if true_body.len() > 2 || false_body.len() > 2 {
            continue;
        }

        // Safety check: all non-branch instructions must be safe to speculate.
        if !all_safe_to_speculate(func, &true_body) || !all_safe_to_speculate(func, &false_body) {
            continue;
        }

        let cond = match decode_cond(cond_encoding) {
            Some(c) => c,
            None => continue,
        };

        // Blast-radius bound for the explicit two-edge header form (`BCond T; B F`,
        // which is what real ISel emits). Two admissions are carved out; every
        // other explicit-header diamond stays branchy (the general MOV-only
        // recognizers keep their prior fallthrough-form-only reach):
        //
        //   * DIV-GUARD collapse — a division arm, while `ifconv_div` is enabled.
        //   * LOOP DIAMOND — a loop-resident, non-div diamond whose branch is a
        //     hard-to-predict self-recurrence (its own merged value feeds, across
        //     the loop back-edge, the value its condition tests). This is the
        //     collatz `if c&1 {…}` shape: converting it to a branchless CSEL
        //     removes a per-iteration mispredict. The tight profitability
        //     predicate ([`is_profitable_loop_diamond`]) is deliberately narrow
        //     so it fires here and NOT on well-predicted structural diamonds
        //     (bounds checks, monotone-IV parity), which a CSEL would regress.
        //     Kill switch: `TRUST_CG_DISABLE_PASSES=ifconv_loop`.
        let involves_div = diamond_involves_div(func, &true_body, &false_body);
        if header_fallthrough_br.is_some() {
            let div_admitted = involves_div && div_collapse_enabled();
            let loop_admitted = !involves_div
                && loop_ifconv_enabled()
                && is_profitable_loop_diamond(
                    func,
                    loop_analysis,
                    header_id,
                    condition_inst_id,
                    &true_body,
                    &false_body,
                );
            if !div_admitted && !loop_admitted {
                continue;
            }
        }

        // DIV-GUARD collapse / CSEL. Tried first so a division arm is never
        // mishandled by the MOV-only recognizers, and handles both the 1-inst
        // (`DIV merge`) and 2-inst (`DIV vt; MOV merge, vt`) arm shapes.
        if let Some((insts, prov)) = try_div_diamond(
            func,
            true_block,
            false_block,
            &true_body,
            &false_body,
            cond,
            condition_inst_id,
        ) {
            let mut insts = insts;
            apply_predicated_source_loc_fallback(&mut insts, &prov, source_loc_fallback);

            // FULL COLLAPSE (a single bare div, no CSEL) leaves the div-guard
            // compare dead. Delete it when it is a pure flag-compare adjacent to
            // the branch AND provably dead (its NZCV def is killed before any
            // read on every path leaving the diamond — the arms are flag-neutral
            // by `all_safe_to_speculate`, so it suffices to check the join).
            let is_full_collapse = insts.len() == 1 && is_div_opcode(insts[0].opcode);
            let dead_condition_inst = if is_full_collapse {
                condition_inst_id.filter(|&cid| {
                    is_pure_flag_compare(func.inst(cid))
                        && condition_is_adjacent_before_branch(func, header_id, cid, bcond_inst_id)
                        && flags_dead_from_block(func, join_block)
                })
            } else {
                None
            };

            transforms.push(DiamondTransform {
                header: header_id,
                true_block,
                false_block,
                join_block,
                new_insts: insts,
                new_inst_provenance: prov,
                condition_inst_id,
                bcond_inst_id,
                true_br_inst_id: true_last_id,
                false_br_inst_id: false_last_id,
                header_fallthrough_br,
                dead_condition_inst,
            });
            continue;
        }

        // Try to form a single conditional select from the last value-producing
        // instruction in each arm. Both arms must write to the same destination.
        if true_body.len() == 1 && false_body.len() == 1 {
            let true_inst = func.inst(true_body[0]);
            let false_inst = func.inst(false_body[0]);

            // Both must have a destination operand and it must be the same.
            if true_inst.operands.is_empty() || false_inst.operands.is_empty() {
                continue;
            }
            if true_inst.operands[0] != false_inst.operands[0] {
                continue;
            }

            // Try CSINC: true arm is MOV, false arm is ADD src, #1.
            if let Some(mut inst) = try_csinc(true_inst, false_inst, cond) {
                apply_source_loc_fallback(&mut inst, source_loc_fallback);
                transforms.push(DiamondTransform {
                    header: header_id,
                    true_block,
                    false_block,
                    join_block,
                    new_insts: vec![inst],
                    new_inst_provenance: vec![NewInstProvenance::Merged(vec![
                        true_body[0],
                        false_body[0],
                    ])],
                    condition_inst_id,
                    bcond_inst_id,
                    true_br_inst_id: true_last_id,
                    false_br_inst_id: false_last_id,
                    header_fallthrough_br,
                    dead_condition_inst: None,
                });
                continue;
            }

            // Try CSNEG: true arm is MOV, false arm is NEG.
            if let Some(mut inst) = try_csneg(true_inst, false_inst, cond) {
                apply_source_loc_fallback(&mut inst, source_loc_fallback);
                transforms.push(DiamondTransform {
                    header: header_id,
                    true_block,
                    false_block,
                    join_block,
                    new_insts: vec![inst],
                    new_inst_provenance: vec![NewInstProvenance::Merged(vec![
                        true_body[0],
                        false_body[0],
                    ])],
                    condition_inst_id,
                    bcond_inst_id,
                    true_br_inst_id: true_last_id,
                    false_br_inst_id: false_last_id,
                    header_fallthrough_br,
                    dead_condition_inst: None,
                });
                continue;
            }

            // Try general CSEL: both arms produce a value into the same dest.
            if let Some(mut inst) = try_general_csel(true_inst, false_inst, cond) {
                apply_source_loc_fallback(&mut inst, source_loc_fallback);
                transforms.push(DiamondTransform {
                    header: header_id,
                    true_block,
                    false_block,
                    join_block,
                    new_insts: vec![inst],
                    new_inst_provenance: vec![NewInstProvenance::Merged(vec![
                        true_body[0],
                        false_body[0],
                    ])],
                    condition_inst_id,
                    bcond_inst_id,
                    true_br_inst_id: true_last_id,
                    false_br_inst_id: false_last_id,
                    header_fallthrough_br,
                    dead_condition_inst: None,
                });
                continue;
            }
        }

        // Multi-instruction diamond: hoist all body instructions and add a CSEL
        // for the final value-producing instruction in each arm.
        if (true_body.len() == 2 && false_body.len() <= 2
            || true_body.len() <= 2 && false_body.len() == 2)
            && let Some((mut insts, new_inst_provenance)) =
                try_multi_inst_diamond(func, true_block, false_block, &true_body, &false_body, cond)
        {
            apply_predicated_source_loc_fallback(
                &mut insts,
                &new_inst_provenance,
                source_loc_fallback,
            );
            transforms.push(DiamondTransform {
                header: header_id,
                true_block,
                false_block,
                join_block,
                new_insts: insts,
                new_inst_provenance,
                condition_inst_id,
                bcond_inst_id,
                true_br_inst_id: true_last_id,
                false_br_inst_id: false_last_id,
                header_fallthrough_br,
                dead_condition_inst: None,
            });
        }
    }

    transforms
}

/// Check if an instruction is safe to speculate (hoist past a branch).
/// Must be pure, must not touch flags, and must not be a branch/call.
fn is_safe_to_speculate(opcode: AArch64Opcode) -> bool {
    // Must have no memory effects.
    if !opcode_effect(opcode).is_pure() {
        return false;
    }
    // Must not read or set condition flags. Flag readers have implicit
    // dependencies on the latest CMP/TST/flag-setting arithmetic, and flag
    // writers can clobber the condition consumed by the CSEL this pass emits.
    if reads_flags(opcode) || writes_flags(opcode) {
        return false;
    }

    // Must not be control flow.
    use AArch64Opcode::*;
    !matches!(
        opcode,
        B | BCond
            | Cbz
            | Cbnz
            | Tbz
            | Tbnz
            | Br
            | Ret
            | Bl
            | Blr
            | BL
            | BLR
            | Brk
            | TrapOverflow
            | TrapBoundsCheck
            | TrapBoundsCheckExact
            | TrapNull
            | TrapNullIfZero
            | TrapDivZero
            | TrapDivZeroIfZero
            | TrapShiftRange
            | TrapShiftRangeIfOOB
            | TrapOverflowExact
    )
}

/// Check that all instructions in a list are safe to speculate.
fn all_safe_to_speculate(func: &MachFunction, insts: &[InstId]) -> bool {
    insts
        .iter()
        .all(|&id| is_safe_to_speculate(func.inst(id).opcode))
}

/// Try to form CSINC: true arm is MOV dst, src_n; false arm is ADD dst, src_m, #1
/// -> CSINC dst, src_n, src_m, cond
///
/// Also handles the swapped case: true is ADD #1, false is MOV.
fn try_csinc(true_inst: &MachInst, false_inst: &MachInst, cond: CondCode) -> Option<MachInst> {
    let dst = true_inst.operands[0].clone();

    // Case 1: true = MOV, false = ADD #1
    if true_inst.opcode == AArch64Opcode::MovR && is_add_imm1(false_inst) {
        let true_src = mov_register_source(true_inst)?;
        let false_src = add_register_base(false_inst)?;
        let mut inst = MachInst::new(
            AArch64Opcode::Csinc,
            vec![
                dst,
                true_src,
                false_src,
                MachOperand::Imm(cond.encoding() as i64),
            ],
        );
        inst.source_loc = true_inst.source_loc.or(false_inst.source_loc);
        return Some(inst);
    }

    // Case 2: true = ADD #1, false = MOV -> CSINC dst, false_src, true_base, inverted
    if is_add_imm1(true_inst) && false_inst.opcode == AArch64Opcode::MovR {
        let false_src = mov_register_source(false_inst)?;
        let true_base = add_register_base(true_inst)?;
        let inv = cond.invert();
        let mut inst = MachInst::new(
            AArch64Opcode::Csinc,
            vec![
                dst,
                false_src,
                true_base,
                MachOperand::Imm(inv.encoding() as i64),
            ],
        );
        inst.source_loc = true_inst.source_loc.or(false_inst.source_loc);
        return Some(inst);
    }

    None
}

/// Try to form CSNEG: true arm is MOV dst, src_n; false arm is NEG dst, src_m
/// -> CSNEG dst, src_n, src_m, cond
fn try_csneg(true_inst: &MachInst, false_inst: &MachInst, cond: CondCode) -> Option<MachInst> {
    let dst = true_inst.operands[0].clone();

    // Case 1: true = MOV, false = NEG
    if true_inst.opcode == AArch64Opcode::MovR && false_inst.opcode == AArch64Opcode::Neg {
        let true_src = mov_register_source(true_inst)?;
        let neg_src = register_operand_at(false_inst, 1)?;
        let mut inst = MachInst::new(
            AArch64Opcode::Csneg,
            vec![
                dst,
                true_src,
                neg_src,
                MachOperand::Imm(cond.encoding() as i64),
            ],
        );
        inst.source_loc = true_inst.source_loc.or(false_inst.source_loc);
        return Some(inst);
    }

    // Case 2: true = NEG, false = MOV -> CSNEG dst, false_src, true_neg_src, inverted
    if true_inst.opcode == AArch64Opcode::Neg && false_inst.opcode == AArch64Opcode::MovR {
        let false_src = mov_register_source(false_inst)?;
        let neg_src = register_operand_at(true_inst, 1)?;
        let inv = cond.invert();
        let mut inst = MachInst::new(
            AArch64Opcode::Csneg,
            vec![
                dst,
                false_src,
                neg_src,
                MachOperand::Imm(inv.encoding() as i64),
            ],
        );
        inst.source_loc = true_inst.source_loc.or(false_inst.source_loc);
        return Some(inst);
    }

    None
}

/// Try to form a general CSEL from two single-instruction arms.
/// Both arms must be register moves writing to the same destination.
fn try_general_csel(
    true_inst: &MachInst,
    false_inst: &MachInst,
    cond: CondCode,
) -> Option<MachInst> {
    if true_inst.opcode != AArch64Opcode::MovR || false_inst.opcode != AArch64Opcode::MovR {
        return None;
    }
    let dst = true_inst.operands[0].clone();
    let true_src = mov_register_source(true_inst)?;
    let false_src = mov_register_source(false_inst)?;

    let mut inst = MachInst::new(
        AArch64Opcode::Csel,
        vec![
            dst,
            true_src,
            false_src,
            MachOperand::Imm(cond.encoding() as i64),
        ],
    );
    inst.source_loc = true_inst.source_loc.or(false_inst.source_loc);
    Some(inst)
}

// ---------------------------------------------------------------------------
// Div-guard diamond if-conversion (HARDWARE-TOTAL div semantics)
// ---------------------------------------------------------------------------
//
// The source `r += b != 0 ? a/b : 0` lowers (soundly, to avoid trust_ir's
// div-by-zero UB) to a DIAMOND: the SDIV/UDIV sits behind a `b != 0` guard.
// clang -O3 / LLVM are STUCK with that branch — hoisting the IR `sdiv` above its
// guard would execute UB on the zero rows.
//
// trust-cg reasons at the MACHINE level, where AArch64 SDIV/UDIV are TOTAL
// (`x / 0 == 0`, ARM DDI 0487) and PURE (no trap) — so [`is_safe_to_speculate`]
// already admits them. This recognizer therefore SPECULATES the division out of
// its guard:
//
//   * FULL COLLAPSE — when the else value is 0 AND the branch is exactly
//     `divisor != 0`: emit the BARE total SDIV/UDIV, no CSEL. This is the
//     proven `select(b != 0, a/b, 0) == sdiv_hw(a, b)` collapse
//     (see `if_convert_proofs::proof_select_sdiv_collapse_*`).
//   * CSEL VARIANT — any other else value K: speculate the total div, then
//     `CSEL dst, div, K, cond`. Still branchless, still a win; sound because the
//     machine div is pure+total so speculating it past the guard cannot trap.
//
// Kill switch: `TRUST_CG_DISABLE_PASSES=ifconv_div` (default ON).

/// Pure predicate: does a `TRUST_CG_DISABLE_PASSES` value disable the div-guard
/// collapse? True iff the comma list contains the `ifconv_div` token.
fn div_collapse_disabled_by(list: &str) -> bool {
    list.split(',')
        .map(str::trim)
        .any(|tok| tok == "ifconv_div")
}

#[cfg(test)]
thread_local! {
    /// Test-only, per-thread kill-switch override. Set on the current test's own
    /// thread so the synchronously-run pass observes it WITHOUT mutating the
    /// process-global env (which would race parallel tests). Mirrors the
    /// `pipeline::TEST_DISABLE_PASSES` pattern.
    static TEST_DIV_COLLAPSE_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether the div-guard diamond collapse is enabled (default ON). Turned off by
/// listing `ifconv_div` in `TRUST_CG_DISABLE_PASSES`.
///
/// Under `cfg(test)` the decision comes SOLELY from the per-thread override (set
/// by the kill-switch test) — never the process-global env — so parallel tests
/// cannot race on it. The env parsing itself is covered by
/// `test_div_collapse_disable_token_parsing` over the pure
/// [`div_collapse_disabled_by`].
fn div_collapse_enabled() -> bool {
    #[cfg(test)]
    {
        !TEST_DIV_COLLAPSE_DISABLED.with(std::cell::Cell::get)
    }
    #[cfg(not(test))]
    match crate::env_lock::var("TRUST_CG_DISABLE_PASSES") {
        Ok(list) => !div_collapse_disabled_by(&list),
        Err(_) => true,
    }
}

// ---------------------------------------------------------------------------
// Loop-diamond if-conversion (branchless self-recurrent CSEL)
// ---------------------------------------------------------------------------
//
// A diamond WHOSE OWN merged output feeds, across the loop back-edge, the value
// its branch condition tests is a data-dependent recurrence: the next branch
// outcome depends on the accumulated result of the previous ones. That is
// exactly the hard-to-predict shape a branch predictor fails on, and exactly
// where replacing the branch with an unconditional CSEL (both arms computed,
// no misprediction) wins. The canonical case is collatz's inner
// `if c&1==0 { c>>=1 } else { c=3c+1 }`: `c` is loop-carried, `c`'s next value
// is the diamond's own merge, and `c&1` is the branch — a self-recurrence.
//
// The predicate is deliberately TIGHT. A well-predicted structural diamond —
// one gated on a loop-invariant, a monotone induction variable's parity, or a
// bounds/exit test — would be REGRESSED by forcing both arms + register
// pressure, so it must NOT fire there. The self-recurrence signature
// (`csel_dst` reachable, within the loop, from the condition) cannot hold for
// those: `csel_dst` is produced in the arms, strictly after the header
// condition within an iteration, so the only way the condition can depend on it
// is through the back-edge — which a monotone IV or an invariant never does.
//
// Kill switch: `TRUST_CG_DISABLE_PASSES=ifconv_loop` (default ON).

/// Pure predicate: does a `TRUST_CG_DISABLE_PASSES` value disable loop-diamond
/// if-conversion? True iff the comma list contains the `ifconv_loop` token.
fn loop_ifconv_disabled_by(list: &str) -> bool {
    list.split(',')
        .map(str::trim)
        .any(|tok| tok == "ifconv_loop")
}

#[cfg(test)]
thread_local! {
    /// Test-only, per-thread kill-switch override (mirrors
    /// `TEST_DIV_COLLAPSE_DISABLED`): set on the current test's own thread so the
    /// synchronously-run pass observes it without racing the process-global env.
    static TEST_LOOP_IFCONV_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether loop-diamond if-conversion is enabled (default ON). Turned off by
/// listing `ifconv_loop` in `TRUST_CG_DISABLE_PASSES`. Under `cfg(test)` the
/// decision comes solely from the per-thread override (never the process env),
/// matching [`div_collapse_enabled`].
fn loop_ifconv_enabled() -> bool {
    #[cfg(test)]
    {
        !TEST_LOOP_IFCONV_DISABLED.with(std::cell::Cell::get)
    }
    #[cfg(not(test))]
    match crate::env_lock::var("TRUST_CG_DISABLE_PASSES") {
        Ok(list) => !loop_ifconv_disabled_by(&list),
        Err(_) => true,
    }
}

// ---------------------------------------------------------------------------
// CSEL -> CSINC increment fold (absorb a `+1` select arm into the increment)
// ---------------------------------------------------------------------------
//
// A machine `CSINC Xd, Xn, Xm, cond` computes `cond ? Xn : Xm + 1` in ONE
// instruction. When an already-formed `CSEL` selects, on one side, a value that
// is exactly `t + 1` (a single-use `ADD t, #1` / `ADD t, one`), that add can be
// deleted and folded into a `CSINC`, removing an instruction from the value's
// dependency chain. This is the LLVM `csinc` collatz shape: the odd arm
// `c*3 + 1`, strength-reduced by `mul-shift-reduce` (with the addend deferred to
// the OUTERMOST `+1`) to `(c + c<<1) + 1`, feeds a `CSEL c>>1 : 3c+1`; this fold
// rewrites it to `CSINC c>>1, 3c, eq`, shortening the loop-carried recurrence to
// `AddRRShift(3c) -> Csinc` (2 ops) — matching LLVM's `add x,x,x,lsl#1; csinc`.
//
// Runs as a LATE peephole (after `mul-shift-reduce` + `shift-alu-fuse` have
// exposed the `+1` as the CSEL's direct operand), NOT at diamond-conversion
// time, because at O2 (single-pass) `if-convert` runs BEFORE `mul-shift-reduce`
// and would see the odd arm as a `Madd`, not a `+1`.
//
// SOUNDNESS (a wrong CSINC polarity is a silent miscompile, so this is exact):
//   * `Csel(dst, T, F, cc) = cc ? T : F`, `Csinc(dst, Xn, Xm, cc) = cc ? Xn :
//     (Xm + 1)` (wrapping, mod 2^W).
//   * FALSE-arm fold: `F == t + 1` (wrapping) ⇒ `Csel(dst, T, t+1, cc) ==
//     Csinc(dst, T, t, cc)` — same `cc`, `t` in the increment slot.
//   * TRUE-arm fold: `T == t + 1` ⇒ `Csel(dst, t+1, F, cc) == Csinc(dst, F, t,
//     invert(cc))` (`invert(cc) ? F : t+1` = `cc ? t+1 : F`).
//   * The `+1` producer must be SINGLE-USE (only this CSEL reads it) so deleting
//     it strands nothing, and the base `t` must NOT be redefined between the add
//     and the CSEL (both in the same block) so the value the CSINC recomputes
//     equals what the deleted add produced. Both are checked before firing;
//     any unmet precondition BAILS (the CSEL is left intact — always correct).
// `Csinc` is already emittable and gate-credited (no new opcode / proof).
//
// Kill switch: `TRUST_CG_DISABLE_PASSES=csincfold` (default ON).

/// CSEL->CSINC increment-fold peephole (see the section comment above).
pub struct CsincFold;

impl MachinePass for CsincFold {
    fn name(&self) -> &str {
        "csinc-fold"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_csinc_fold(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_csinc_fold(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_csinc_fold(func, Some(provenance))
    }
}

fn csinc_fold_pass_id() -> PassId {
    PassId::new("csinc-fold")
}

/// Pure predicate: does a `TRUST_CG_DISABLE_PASSES` value disable the CSEL->CSINC
/// fold? True iff the comma list contains the `csincfold` token.
fn csinc_fold_disabled_by(list: &str) -> bool {
    list.split(',').map(str::trim).any(|tok| tok == "csincfold")
}

#[cfg(test)]
thread_local! {
    /// Test-only, per-thread kill-switch override (mirrors the div/loop
    /// switches): set on the current test's thread so the synchronously-run pass
    /// observes it without racing the process-global env.
    static TEST_CSINC_FOLD_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether the CSEL->CSINC fold is enabled (default ON). Turned off by listing
/// `csincfold` in `TRUST_CG_DISABLE_PASSES`. Under `cfg(test)` the decision
/// comes solely from the per-thread override (never the process env).
fn csinc_fold_enabled() -> bool {
    #[cfg(test)]
    {
        !TEST_CSINC_FOLD_DISABLED.with(std::cell::Cell::get)
    }
    #[cfg(not(test))]
    match crate::env_lock::var("TRUST_CG_DISABLE_PASSES") {
        Ok(list) => !csinc_fold_disabled_by(&list),
        Err(_) => true,
    }
}

/// A validated CSEL->CSINC rewrite: replace `csel_id`'s instruction with `csinc`
/// (in place, keeping its InstId) and delete the folded `+1` producer `add_id`.
struct CsincRewrite {
    csel_id: InstId,
    add_id: InstId,
    add_block: BlockId,
    csinc: MachInst,
}

fn run_csinc_fold(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    if !csinc_fold_enabled() {
        return false;
    }
    let rewrites = collect_csinc_folds(func);
    if rewrites.is_empty() {
        return false;
    }
    for rw in &rewrites {
        *func.inst_mut(rw.csel_id) = rw.csinc.clone();
        func.block_mut(rw.add_block)
            .insts
            .retain(|&id| id != rw.add_id);
        if let Some(p) = provenance.as_deref_mut() {
            // The CSEL kept its InstId (opcode changed in place); the folded
            // `+1` producer is optimized away into it.
            p.record_deletion(
                rw.add_id,
                csinc_fold_pass_id(),
                "increment producer folded into CSINC (CSEL->CSINC increment fold)",
            );
        }
    }
    true
}

/// Scan every block for a `Csel` whose selected value is a single-use `t + 1`
/// and build the CSINC rewrite. Recognition reads the UNMUTATED function.
fn collect_csinc_folds(func: &MachFunction) -> Vec<CsincRewrite> {
    let use_count = build_vreg_use_counts(func);
    let mut out = Vec::new();
    for &bid in &func.block_order {
        let block_insts = func.block(bid).insts.clone();
        for &iid in &block_insts {
            let inst = func.inst(iid);
            if inst.opcode != AArch64Opcode::Csel || inst.operands.len() != 4 {
                continue;
            }
            let dst = inst.operands[0].clone();
            let tval = inst.operands[1].clone();
            let fval = inst.operands[2].clone();
            let Some(cond) = inst.operands[3].as_imm().and_then(|c| decode_cond(c as u8)) else {
                continue;
            };
            let src_loc = inst.source_loc;

            // FALSE-arm fold: `Csel dst, T, (t+1), cc` -> `Csinc dst, T, t, cc`.
            if let Some((base, add_id, add_block)) =
                add_of_one_base(func, &use_count, bid, iid, &fval)
            {
                out.push(CsincRewrite {
                    csel_id: iid,
                    add_id,
                    add_block,
                    csinc: make_csinc(dst, tval, base, cond, src_loc),
                });
                continue;
            }
            // TRUE-arm fold: `Csel dst, (t+1), F, cc` -> `Csinc dst, F, t, !cc`.
            if let Some((base, add_id, add_block)) =
                add_of_one_base(func, &use_count, bid, iid, &tval)
            {
                out.push(CsincRewrite {
                    csel_id: iid,
                    add_id,
                    add_block,
                    csinc: make_csinc(dst, fval, base, cond.invert(), src_loc),
                });
                continue;
            }
        }
    }
    out
}

/// Build a `Csinc [dst, Xn, Xm, Imm(cond)]` — `dst = cond ? Xn : Xm + 1`.
fn make_csinc(
    dst: MachOperand,
    xn: MachOperand,
    xm: MachOperand,
    cond: CondCode,
    source_loc: Option<SourceLoc>,
) -> MachInst {
    let mut inst = MachInst::new(
        AArch64Opcode::Csinc,
        vec![dst, xn, xm, MachOperand::Imm(cond.encoding() as i64)],
    );
    inst.source_loc = source_loc;
    inst
}

/// If `operand` is a single-use register defined (in the CSEL's own block, before
/// the CSEL) by an `ADD base, #1` / `ADD base, one` whose base is not redefined
/// between the add and the CSEL, return `(base, add_id, add_block)`. Otherwise
/// `None` (BAIL — leave the CSEL intact).
fn add_of_one_base(
    func: &MachFunction,
    use_count: &std::collections::HashMap<VReg, usize>,
    csel_block: BlockId,
    csel_id: InstId,
    operand: &MachOperand,
) -> Option<(MachOperand, InstId, BlockId)> {
    let v = operand.as_vreg()?;
    // SINGLE-USE: the only reader of the `+1` result is this CSEL, so deleting
    // the add strands nothing. (`build_vreg_use_counts` counts every read.)
    if use_count.get(&v).copied().unwrap_or(0) != 1 {
        return None;
    }

    // Locate the add in the CSEL's OWN block, strictly before the CSEL. Same
    // block bounds the "base unchanged between add and CSINC" reasoning to a
    // local scan; a producer elsewhere BAILS.
    let insts = &func.block(csel_block).insts;
    let csel_pos = insts.iter().position(|&id| id == csel_id)?;
    let add_id = *insts[..csel_pos]
        .iter()
        .find(|&&id| inst_defines_vreg(func.inst(id), v))?;
    let add = func.inst(add_id);

    // The producer must be `ADD base, #1` (immediate) or `ADD base, one` /
    // `ADD one, base` (register, `one` proven to materialize the constant 1).
    let base = match add.opcode {
        AArch64Opcode::AddRI => {
            if add.operands.len() < 3 || add.operands[2].as_imm() != Some(1) {
                return None;
            }
            register_operand_at(add, 1)?
        }
        AArch64Opcode::AddRR => {
            let a = register_operand_at(add, 1)?;
            let b = register_operand_at(add, 2)?;
            if reg_holds_one(func, &b) {
                a
            } else if reg_holds_one(func, &a) {
                b
            } else {
                return None;
            }
        }
        _ => return None,
    };

    // The base value must be UNCHANGED between the add and the CSEL (else the
    // CSINC, which recomputes `base + 1` at the CSEL site, would differ from the
    // deleted add's value). Scan the strictly-between instructions for a redef.
    let add_pos = insts.iter().position(|&id| id == add_id)?;
    for &mid in &insts[add_pos + 1..csel_pos] {
        if inst_def_registers(func.inst(mid))
            .iter()
            .any(|d| operands_equal(d, &base))
        {
            return None;
        }
    }

    Some((base, add_id, csel_block))
}

/// Does `inst` define the vreg `v`?
fn inst_defines_vreg(inst: &MachInst, v: VReg) -> bool {
    inst_def_registers(inst)
        .iter()
        .any(|d| d.as_vreg() == Some(v))
}

/// Whole-function count of how many instructions READ each vreg (implicit and
/// explicit uses). A vreg with count 1 is read by exactly one instruction.
fn build_vreg_use_counts(func: &MachFunction) -> std::collections::HashMap<VReg, usize> {
    let mut counts: std::collections::HashMap<VReg, usize> = std::collections::HashMap::new();
    for &bid in &func.block_order {
        for &iid in &func.block(bid).insts {
            for u in inst_use_registers(func.inst(iid)) {
                if let Some(v) = u.as_vreg() {
                    *counts.entry(v).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

/// Does `inst` materialize the integer constant 1 into its destination? Accepts
/// `MOVZ dst, #1` / `MOVI dst, #1` with NO nonzero shift (a shifted `#1` would
/// be `1<<s != 1`). Mirrors [`inst_materializes_zero`] for the value 1.
fn inst_materializes_one(inst: &MachInst) -> bool {
    match inst.opcode {
        AArch64Opcode::Movz => {
            crate::reaching_const::movz_value(inst).is_some_and(|(_, value)| value == 1)
        }
        AArch64Opcode::MovI => {
            inst.operands.len() == 2
                && inst.operands.get(1).and_then(MachOperand::as_imm) == Some(1)
        }
        _ => false,
    }
}

/// Is `operand` PROVABLY the constant 1 at every use? True for a register whose
/// EVERY defining instruction materializes 1 (sound whole-function def scan): a
/// def that does NOT materialize 1, or no def at all, conservatively returns
/// false (refuse the fold). Analogous to [`reg_holds_zero`].
fn reg_holds_one(func: &MachFunction, operand: &MachOperand) -> bool {
    if !is_register_operand(operand) {
        return false;
    }
    let mut saw_def = false;
    for &bid in &func.block_order {
        for &iid in &func.block(bid).insts {
            let inst = func.inst(iid);
            if inst_def_registers(inst)
                .iter()
                .any(|d| operands_equal(d, operand))
            {
                saw_def = true;
                if !inst_materializes_one(inst) {
                    return false;
                }
            }
        }
    }
    saw_def
}

/// TIGHT profitability gate for loop-resident, non-div diamonds (the widened
/// `:305` blast-radius admission). Returns `true` only for a diamond that is:
///
///   1. loop-resident — its header block is inside a natural loop, AND
///   2. value-merging — both arms end by writing the SAME merge register (the
///      shared final `MovR` destination; this is the CSEL's destination), AND
///   3. self-recurrent — that merge register is reachable, following defs that
///      stay INSIDE the loop body, backward from the branch condition's source
///      registers. Because the merge is produced in the arms (after the header
///      condition within one iteration), such a dependency can only close
///      through the loop back-edge: the branch tests a value derived from its
///      own previous output. That is the hard-to-predict recurrence CSEL wins
///      on; a monotone-IV or loop-invariant condition never reaches it.
///
/// Fail-safe: any missing analysis, non-value-merge shape, or absent condition
/// makes this return `false` (leave the diamond branchy — always correct).
fn is_profitable_loop_diamond(
    func: &MachFunction,
    loop_analysis: Option<&LoopAnalysis>,
    header: BlockId,
    condition_inst_id: Option<InstId>,
    true_body: &[InstId],
    false_body: &[InstId],
) -> bool {
    // (1) Loop-resident.
    let Some(la) = loop_analysis else {
        return false;
    };
    let Some(lp) = la.containing_loop(header) else {
        return false;
    };

    // (2) Value-merge shape: both arms' final instruction is `MovR merge, _`
    //     writing the SAME merge register, which becomes the CSEL destination.
    let (Some(&true_last), Some(&false_last)) = (true_body.last(), false_body.last()) else {
        return false;
    };
    let true_last = func.inst(true_last);
    let false_last = func.inst(false_last);
    if true_last.opcode != AArch64Opcode::MovR || false_last.opcode != AArch64Opcode::MovR {
        return false;
    }
    let (Some(true_dst), Some(false_dst)) =
        (true_last.operands.first(), false_last.operands.first())
    else {
        return false;
    };
    if !operands_equal(true_dst, false_dst) {
        return false;
    }
    let Some(merge_reg) = true_dst.as_vreg() else {
        return false;
    };

    // (3) Self-recurrence: `merge_reg` reachable, within the loop body, backward
    //     from the branch condition's source registers.
    let Some(cond_id) = condition_inst_id else {
        return false;
    };
    let cond_source_regs = inst_use_registers(func.inst(cond_id));
    let def_map = build_inloop_def_map(func, &lp.body);
    inloop_reaches(func, &def_map, &cond_source_regs, merge_reg)
}

/// Build a vreg -> defining-instruction map restricted to the blocks of a loop
/// body. Restricting to the body means every def followed by [`inloop_reaches`]
/// stays inside the loop, so the only way a backward walk reaches the diamond's
/// merge register is through the loop back-edge (the self-recurrence signal).
fn build_inloop_def_map(
    func: &MachFunction,
    body: &std::collections::HashSet<BlockId>,
) -> std::collections::HashMap<VReg, Vec<InstId>> {
    let mut map: std::collections::HashMap<VReg, Vec<InstId>> = std::collections::HashMap::new();
    for &bid in body {
        for &iid in &func.block(bid).insts {
            for d in inst_def_registers(func.inst(iid)) {
                if let Some(v) = d.as_vreg() {
                    map.entry(v).or_default().push(iid);
                }
            }
        }
    }
    map
}

/// Sound bounded backward reachability over in-loop defs: is `target` reachable
/// from any of the `seed` registers by repeatedly stepping from a register to
/// the use-registers of its in-loop defining instructions? A visited set bounds
/// the walk (loops terminate).
fn inloop_reaches(
    func: &MachFunction,
    def_map: &std::collections::HashMap<VReg, Vec<InstId>>,
    seeds: &[MachOperand],
    target: VReg,
) -> bool {
    let mut visited: std::collections::HashSet<VReg> = std::collections::HashSet::new();
    let mut work: Vec<VReg> = seeds.iter().filter_map(MachOperand::as_vreg).collect();
    while let Some(v) = work.pop() {
        if v == target {
            return true;
        }
        if !visited.insert(v) {
            continue;
        }
        if let Some(defs) = def_map.get(&v) {
            for &def_id in defs {
                for u in inst_use_registers(func.inst(def_id)) {
                    if let Some(uv) = u.as_vreg() {
                        work.push(uv);
                    }
                }
            }
        }
    }
    false
}

/// The two AArch64 total-division opcodes this recognizer speculates.
fn is_div_opcode(opcode: AArch64Opcode) -> bool {
    matches!(opcode, AArch64Opcode::SDiv | AArch64Opcode::UDiv)
}

/// Is `operand` a hardware zero register (WZR/XZR)?
fn is_zero_register(operand: &MachOperand) -> bool {
    matches!(
        operand,
        MachOperand::Special(SpecialReg::WZR) | MachOperand::Special(SpecialReg::XZR)
    )
}

/// Does `inst` materialize the integer constant 0 into its destination?
/// Recognizes `MOVZ dst, #0` (how ISel materializes small iconsts) and
/// `MOV dst, wzr/xzr`.
fn inst_materializes_zero(inst: &MachInst) -> bool {
    match inst.opcode {
        AArch64Opcode::Movz => {
            crate::reaching_const::movz_value(inst).is_some_and(|(_, value)| value == 0)
        }
        AArch64Opcode::MovI => {
            inst.operands.len() == 2
                && inst.operands.get(1).and_then(MachOperand::as_imm) == Some(0)
        }
        AArch64Opcode::MovR => inst.operands.get(1).is_some_and(is_zero_register),
        _ => false,
    }
}

/// Is `operand` PROVABLY zero at every use? True for WZR/XZR, or for a register
/// whose EVERY defining instruction in the function materializes 0. Uses a
/// sound whole-function def scan: if a def exists that does NOT materialize 0,
/// or no def is found, we conservatively return false (refuse the collapse).
fn reg_holds_zero(func: &MachFunction, operand: &MachOperand) -> bool {
    if is_zero_register(operand) {
        return true;
    }
    if !is_register_operand(operand) {
        return false;
    }
    let mut saw_def = false;
    for &bid in &func.block_order {
        for &iid in &func.block(bid).insts {
            let inst = func.inst(iid);
            if inst_def_registers(inst)
                .iter()
                .any(|d| operands_equal(d, operand))
            {
                saw_def = true;
                if !inst_materializes_zero(inst) {
                    return false;
                }
            }
        }
    }
    saw_def
}

/// Does the arm instruction produce the value 0 into its destination?
/// Either a direct zero materialization, or `MOV dst, zreg` where `zreg` is
/// provably zero.
fn arm_produces_zero(func: &MachFunction, inst: &MachInst) -> bool {
    if inst_materializes_zero(inst) {
        return true;
    }
    if inst.opcode == AArch64Opcode::MovR
        && let Some(src) = register_operand_at(inst, 1)
    {
        return reg_holds_zero(func, &src);
    }
    false
}

/// Does the diamond's flag-writer compare `reg` against zero — i.e. is the
/// guard exactly `reg <cc> 0`? Accepts `CMP reg, #0` (immediate) and
/// `CMP reg, zreg` (register form against a provably-zero register), which is
/// how ISel lowers `icmp ne/eq %divisor, 0`.
fn cmp_tests_reg_zero(
    func: &MachFunction,
    condition_inst_id: Option<InstId>,
    reg: &MachOperand,
) -> bool {
    let Some(cid) = condition_inst_id else {
        return false;
    };
    let cmp = func.inst(cid);
    // First compare operand must be exactly the register under test (the divisor).
    if cmp.operands.first().map(|o| operands_equal(o, reg)) != Some(true) {
        return false;
    }
    match cmp.opcode {
        AArch64Opcode::CmpRI => cmp.operands.get(1).and_then(MachOperand::as_imm) == Some(0),
        AArch64Opcode::CmpRR => cmp
            .operands
            .get(1)
            .is_some_and(|rhs| reg_holds_zero(func, rhs)),
        _ => false,
    }
}

/// A pure NZCV-only compare (`CMP`/`CMN`-style): writes flags, defines no
/// register. Removing it when its flags are dead cannot affect any value.
fn is_pure_flag_compare(inst: &MachInst) -> bool {
    matches!(inst.opcode, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI)
        && writes_flags(inst.opcode)
        && inst_def_registers(inst).is_empty()
}

/// Is `cond_id` the instruction immediately before `bcond_id` in `header`? This
/// guarantees no instruction between the compare and the branch reads the
/// compare's flags.
fn condition_is_adjacent_before_branch(
    func: &MachFunction,
    header: BlockId,
    cond_id: InstId,
    bcond_id: InstId,
) -> bool {
    let insts = &func.block(header).insts;
    match insts.iter().position(|&id| id == bcond_id) {
        Some(pos) if pos > 0 => insts[pos - 1] == cond_id,
        _ => false,
    }
}

/// May this opcode READ the NZCV flags? The complete set of AArch64 flag
/// consumers in this IR: the `reads_flags` arithmetic/select group plus the
/// conditional branch (`BCond`/`Bcc`), whose NZCV dependency is implicit in its
/// condition field rather than an explicit operand. Used by the flag-liveness
/// scan; erring toward "reads" only ever REFUSES to delete a compare.
fn may_read_flags(opcode: AArch64Opcode) -> bool {
    reads_flags(opcode) || matches!(opcode, AArch64Opcode::BCond | AArch64Opcode::Bcc)
}

/// Sound forward flag-liveness: are NZCV flags entering `start` DEAD — i.e. on
/// EVERY reachable path a flag WRITER is hit before any flag READER? Returns
/// `false` (conservatively: flags may be live) the moment a reader is seen
/// before a writer on some path. A block that writes flags kills them (its
/// successors are not explored); a block with neither propagates to successors.
/// Loops terminate via the visited set.
fn flags_dead_from_block(func: &MachFunction, start: BlockId) -> bool {
    let mut worklist = vec![start];
    let mut visited = std::collections::HashSet::new();
    while let Some(bid) = worklist.pop() {
        if !visited.insert(bid) {
            continue;
        }
        let block = func.block(bid);
        let mut killed = false;
        for &iid in &block.insts {
            let op = func.inst(iid).opcode;
            if may_read_flags(op) {
                return false; // a live read reached before any write
            }
            if writes_flags(op) {
                killed = true;
                break; // flags overwritten here; downstream reads are of new flags
            }
        }
        if !killed {
            for &succ in &block.succs {
                worklist.push(succ);
            }
        }
    }
    true
}

/// Given a `CMP divisor, 0` guard, does the DIV arm execute exactly when
/// `divisor != 0`? On such a compare, `NE` ⇔ `divisor != 0` and `EQ` ⇔
/// `divisor == 0`. When the div is the true arm it runs on the branch
/// condition; when it is the false arm it runs on the negation.
fn div_taken_when_divisor_nonzero(cond: CondCode, div_in_true: bool) -> bool {
    if div_in_true {
        cond == CondCode::NE
    } else {
        cond == CondCode::EQ
    }
}

/// Does either arm body contain a division? (Cheap scoping predicate.)
fn diamond_involves_div(func: &MachFunction, true_body: &[InstId], false_body: &[InstId]) -> bool {
    true_body
        .iter()
        .chain(false_body)
        .any(|&id| is_div_opcode(func.inst(id).opcode))
}

/// The InstId of the (first) division in an arm body, if any.
fn body_div_inst(func: &MachFunction, body: &[InstId]) -> Option<InstId> {
    body.iter()
        .copied()
        .find(|&id| is_div_opcode(func.inst(id).opcode))
}

/// A parsed div arm: the division, its dividend/divisor, the merge register the
/// arm ultimately writes, and (for the two-instruction form) the copy that moves
/// the div result into the merge register.
struct DivArm {
    div_id: InstId,
    dividend: MachOperand,
    divisor: MachOperand,
    div_dst: MachOperand,
    merge: MachOperand,
    copy_id: Option<InstId>,
}

/// Parse an arm body as a division producer. Accepts the two post-ISel shapes:
///   * `[DIV merge, a, b]`                  (div writes the merge register)
///   * `[DIV vt, a, b ; MOV merge, vt]`     (div writes a temp, copied to merge)
fn parse_div_arm(func: &MachFunction, body: &[InstId]) -> Option<DivArm> {
    let div_id = *body.first()?;
    let div = func.inst(div_id);
    if !is_div_opcode(div.opcode) || div.operands.len() < 3 {
        return None;
    }
    let div_dst = div.operands[0].clone();
    let dividend = register_operand_at(div, 1)?;
    let divisor = register_operand_at(div, 2)?;

    match body.len() {
        1 => Some(DivArm {
            div_id,
            dividend,
            divisor,
            div_dst: div_dst.clone(),
            merge: div_dst,
            copy_id: None,
        }),
        2 => {
            // The trailing inst must copy the div result into the merge register.
            let copy = func.inst(body[1]);
            if copy.opcode != AArch64Opcode::MovR {
                return None;
            }
            let copy_src = register_operand_at(copy, 1)?;
            if !operands_equal(&copy_src, &div_dst) {
                return None;
            }
            let merge = copy.operands.first()?.clone();
            Some(DivArm {
                div_id,
                dividend,
                divisor,
                div_dst,
                merge,
                copy_id: Some(body[1]),
            })
        }
        _ => None,
    }
}

/// Recognize a div-guard diamond over the arm BODIES and speculate the division
/// out of its branch. The division arm is `parse_div_arm`-shaped; the else arm is
/// a single `MOV merge, esrc`.
///
///   * FULL COLLAPSE — else value 0, guard is exactly `divisor != 0`: emit the
///     bare total DIV writing the merge register (no CSEL). The proven
///     `select(b != 0, a/b, 0) == sdiv_hw(a, b)` collapse.
///   * CSEL VARIANT — otherwise: speculate the DIV, then `CSEL merge, div, esrc`.
///     Sound because the machine DIV is pure + total (speculating it can't trap).
fn try_div_diamond(
    func: &MachFunction,
    true_block: BlockId,
    false_block: BlockId,
    true_body: &[InstId],
    false_body: &[InstId],
    cond: CondCode,
    condition_inst_id: Option<InstId>,
) -> Option<(Vec<MachInst>, Vec<NewInstProvenance>)> {
    if !div_collapse_enabled() {
        return None;
    }

    // Exactly one arm must be a division producer.
    let true_div = body_div_inst(func, true_body).is_some();
    let false_div = body_div_inst(func, false_body).is_some();
    let (div_body, else_body, div_block, div_in_true) = match (true_div, false_div) {
        (true, false) => (true_body, false_body, true_block, true),
        (false, true) => (false_body, true_body, false_block, false),
        _ => return None,
    };

    let arm = parse_div_arm(func, div_body)?;

    // Else arm: exactly `MOV merge, esrc`.
    if else_body.len() != 1 {
        return None;
    }
    let else_id = else_body[0];
    let else_inst = func.inst(else_id);
    if else_inst.opcode != AArch64Opcode::MovR
        || else_inst
            .operands
            .first()
            .map(|d| operands_equal(d, &arm.merge))
            != Some(true)
    {
        return None;
    }
    let else_src = register_operand_at(else_inst, 1)?;

    // The div's inputs must not alias the merge register (we retarget the div's
    // destination to `merge` on the collapse path, and the CSEL reads `merge`).
    if operands_equal(&arm.dividend, &arm.merge) || operands_equal(&arm.divisor, &arm.merge) {
        return None;
    }

    // --- FULL COLLAPSE ---
    if arm_produces_zero(func, else_inst)
        && cmp_tests_reg_zero(func, condition_inst_id, &arm.divisor)
        && div_taken_when_divisor_nonzero(cond, div_in_true)
    {
        let mut bare = func.inst(arm.div_id).clone();
        bare.operands[0] = arm.merge.clone(); // write the merge register directly
        let mut merged = vec![arm.div_id, else_id];
        if let Some(cid) = arm.copy_id {
            merged.push(cid);
        }
        return Some((vec![bare], vec![NewInstProvenance::Merged(merged)]));
    }

    // --- CSEL VARIANT ---
    // For the two-instruction arm the div writes a temp that now becomes live in
    // the header; guard that the temp is not observed outside the two arms with
    // its speculated value (sound conservative whole-function use scan).
    if arm.copy_id.is_some()
        && hoisted_defs_used_outside_arms(
            func,
            std::slice::from_ref(&arm.div_dst),
            true_block,
            false_block,
        )
    {
        return None;
    }
    let _ = div_block; // (kept for symmetry / future per-arm scoping)

    let hoisted_div = func.inst(arm.div_id).clone(); // writes arm.div_dst
    let (on_true, on_false) = if div_in_true {
        (arm.div_dst.clone(), else_src)
    } else {
        (else_src, arm.div_dst.clone())
    };
    let mut csel = MachInst::new(
        AArch64Opcode::Csel,
        vec![
            arm.merge.clone(),
            on_true,
            on_false,
            MachOperand::Imm(cond.encoding() as i64),
        ],
    );
    csel.source_loc = func.inst(arm.div_id).source_loc.or(else_inst.source_loc);

    let mut merged = vec![else_id];
    if let Some(cid) = arm.copy_id {
        merged.push(cid);
    }
    Some((
        vec![hoisted_div, csel],
        vec![
            NewInstProvenance::Replaced(arm.div_id),
            NewInstProvenance::Merged(merged),
        ],
    ))
}

/// Try to convert a multi-instruction diamond (2 insts in at least one arm).
/// Hoists the non-final instructions into the header and produces a CSEL
/// for the final value.
///
/// This only works when the final instructions in both arms write to the
/// same destination and are MOVs (the earlier instructions are hoisted
/// unconditionally since they are safe to speculate).
fn try_multi_inst_diamond(
    func: &MachFunction,
    true_block: BlockId,
    false_block: BlockId,
    true_body: &[InstId],
    false_body: &[InstId],
    cond: CondCode,
) -> Option<(Vec<MachInst>, Vec<NewInstProvenance>)> {
    let (Some(&true_last_id), Some(&false_last_id)) = (true_body.last(), false_body.last()) else {
        return None;
    };

    let true_last = func.inst(true_last_id);
    let false_last = func.inst(false_last_id);

    // Final instructions must both be register moves to the same destination.
    if true_last.opcode != AArch64Opcode::MovR || false_last.opcode != AArch64Opcode::MovR {
        return None;
    }
    if true_last.operands.is_empty() || false_last.operands.is_empty() {
        return None;
    }
    if true_last.operands[0] != false_last.operands[0] {
        return None;
    }

    // CROSS-ARM CLOBBER GUARD.
    //
    // The multi-instruction path hoists the non-final body instructions of
    // BOTH arms into the header, where they then execute *unconditionally* and
    // sequentially before the merged CSEL. That is sound only if speculating
    // both arms cannot corrupt a value the merge depends on. The per-arm
    // `all_safe_to_speculate` gate is opcode-only (purity / no flags / no
    // control flow) and never compares one arm's defs against the other arm's
    // uses or defs — so without this guard a hoisted def from one arm can
    // overwrite a register the other arm reads (including the final MOV's
    // source feeding the CSEL), or both arms can write the same intermediate
    // temp, yielding valid-but-wrong machine code (a live O2/O3 miscompile).
    //
    // We refuse (return None, leaving the branchy diamond intact) whenever
    // unconditional speculation of both arms could corrupt a value. The merged
    // CSEL destination is the single register both arms are *allowed* to
    // co-define (it is exactly what the CSEL recomputes); every other shared
    // def, or any cross-arm def/use overlap, is a clobber. Correctness
    // dominates: when in doubt, refuse.
    //
    // The merged CSEL destination (`true_last.operands[0]`, validated equal to
    // `false_last.operands[0]` above) is the single register both arms are
    // allowed to co-define and to be live-out — it is exactly what the CSEL
    // recomputes. It is excluded from the DEF sets *by construction* below
    // (`arm_hoisted_def_registers` skips each arm's final MOV), so no special-
    // casing by value is needed in the checks.

    // DEF sets are built over the HOISTED (non-final) instructions ONLY. The
    // final MOV of each arm is folded into the CSEL — it is never emitted as a
    // separate def — so its destination (`csel_dst`) is intentionally absent
    // from these sets. `csel_dst` is the single register both arms are *allowed*
    // to co-define and to be live past the diamond (the CSEL recomputes it);
    // including it here would falsely reject the common `x = cond ? f(...) : x`
    // idiom whose other-arm final MOV is `MOV dst, dst`.
    //
    // USE sets cover ALL instructions of the arm INCLUDING the final MOV's
    // source (the value feeding the CSEL): a hoisted def of one arm that
    // overwrites the other arm's CSEL source is a real clobber that must be
    // caught.
    let true_defs = arm_hoisted_def_registers(func, true_body);
    let false_defs = arm_hoisted_def_registers(func, false_body);
    let true_uses = arm_use_registers(func, true_body);
    let false_uses = arm_use_registers(func, false_body);

    // (1) true arm hoisted-defines a register the false arm reads.
    if registers_overlap(&true_defs, &false_uses) {
        return None;
    }
    // (2) false arm hoisted-defines a register the true arm reads.
    if registers_overlap(&false_defs, &true_uses) {
        return None;
    }
    // (3) both arms hoisted-define the same register. Since `csel_dst` is
    //     excluded from both DEF sets by construction, any overlap here is a
    //     co-defined shared temp (corruption), never the legitimate merge dst.
    if registers_overlap(&true_defs, &false_defs) {
        return None;
    }

    // (4) Live-out guard. The hoisted (non-final) defs now execute on BOTH paths
    //     unconditionally; if any such temp is read OUTSIDE the two arms (the
    //     join/merge block or any other block/successor) it becomes observable
    //     with the speculated value on the path that did not originally compute
    //     it -> miscompile. We use a sound conservative whole-function use-scan
    //     (over-approximates the live-out set, so it can only refuse more).
    let mut hoisted_defs = true_defs;
    for d in false_defs {
        push_register(&mut hoisted_defs, d);
    }
    if hoisted_defs_used_outside_arms(func, &hoisted_defs, true_block, false_block) {
        return None;
    }

    let mut hoisted = Vec::new();
    let mut new_inst_provenance = Vec::new();

    // Hoist all non-final instructions from both arms.
    for &inst_id in &true_body[..true_body.len() - 1] {
        hoisted.push(func.inst(inst_id).clone());
        new_inst_provenance.push(NewInstProvenance::Replaced(inst_id));
    }
    for &inst_id in &false_body[..false_body.len() - 1] {
        hoisted.push(func.inst(inst_id).clone());
        new_inst_provenance.push(NewInstProvenance::Replaced(inst_id));
    }

    // Add the CSEL for the final value.
    let dst = true_last.operands[0].clone();
    let true_src = mov_register_source(true_last)?;
    let false_src = mov_register_source(false_last)?;

    let mut csel = MachInst::new(
        AArch64Opcode::Csel,
        vec![
            dst,
            true_src,
            false_src,
            MachOperand::Imm(cond.encoding() as i64),
        ],
    );
    csel.source_loc = true_last.source_loc.or(false_last.source_loc);
    hoisted.push(csel);
    new_inst_provenance.push(NewInstProvenance::Merged(vec![true_last_id, false_last_id]));

    Some((hoisted, new_inst_provenance))
}

/// Apply a diamond transform to the function.
fn apply_diamond_transform(
    func: &mut MachFunction,
    xform: &DiamondTransform,
    provenance: Option<&mut ProvenanceMap>,
) {
    // 1. Insert new instructions in the header just before the BCond.
    let header = func.block(xform.header);
    let bcond_pos = header
        .insts
        .iter()
        .position(|&id| id == xform.bcond_inst_id);

    let mut new_inst_ids = Vec::new();
    for inst in &xform.new_insts {
        let id = func.push_inst(inst.clone());
        new_inst_ids.push(id);
    }

    if let Some(pos) = bcond_pos {
        let header_mut = func.block_mut(xform.header);
        for (i, &id) in new_inst_ids.iter().enumerate() {
            header_mut.insts.insert(pos + i, id);
        }
    }

    // 2. Replace BCond with B .join.
    let bcond_source_loc = func.inst(xform.bcond_inst_id).source_loc;
    let mut b_join = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(xform.join_block)]);
    b_join.source_loc = bcond_source_loc;
    *func.inst_mut(xform.bcond_inst_id) = b_join;

    // 2b. Explicit two-edge form: drop the trailing `B F`. The BCond (now
    // `B join`) is the header's sole terminator; leaving the old fallthrough
    // branch would make the header double-terminated.
    if let Some(fallthrough_br) = xform.header_fallthrough_br {
        let header_mut = func.block_mut(xform.header);
        header_mut.insts.retain(|&id| id != fallthrough_br);
    }

    // 2c. Full collapse: delete the now-dead div-guard compare (proved dead at
    // collect time). The bare div consumes no flags, so its guard compare is
    // pure dead code.
    if let Some(dead_cmp) = xform.dead_condition_inst {
        let header_mut = func.block_mut(xform.header);
        header_mut.insts.retain(|&id| id != dead_cmp);
    }

    // 3. Update CFG: header's successors become just [join_block].
    let header = func.block_mut(xform.header);
    header.succs.clear();
    header.succs.push(xform.join_block);

    // 4. Update join block predecessors.
    let join = func.block_mut(xform.join_block);
    join.preds
        .retain(|&bid| bid != xform.true_block && bid != xform.false_block);
    if !join.preds.contains(&xform.header) {
        join.preds.push(xform.header);
    }

    // 5. Remove arm blocks from block_order. Block removal has no separate
    // ProvenanceMap entry; every removed arm instruction is merged, replaced,
    // or marked optimized-away below.
    func.block_order
        .retain(|&bid| bid != xform.true_block && bid != xform.false_block);

    if let Some(provenance) = provenance {
        record_diamond_provenance(provenance, xform, &new_inst_ids);
    }
}

// ---------------------------------------------------------------------------
// Triangle if-conversion
// ---------------------------------------------------------------------------

/// A triangle transform: replaces a conditional branch over a single-
/// assignment block with a CSEL in the header.
struct TriangleTransform {
    header: BlockId,
    then_block: BlockId,
    join_block: BlockId,
    new_inst: MachInst,
    condition_inst_id: Option<InstId>,
    bcond_inst_id: InstId,
    then_inst_id: InstId,
    then_br_inst_id: InstId,
}

/// Scan for triangle CFG patterns.
///
/// ```text
///   header:
///     ...
///     B.cond then_block
///     (fallthrough to join)
///   then_block:
///     MOV Xd, Xn
///     B join
///   join:
///     ...
/// ```
fn collect_triangle_transforms(func: &MachFunction) -> Vec<TriangleTransform> {
    let mut transforms = Vec::new();

    for &header_id in &func.block_order {
        let header = func.block(header_id);
        let Some(&last_inst_id) = header.insts.last() else {
            continue;
        };

        // Last instruction must be BCond.
        let last_inst = func.inst(last_inst_id);
        if last_inst.opcode != AArch64Opcode::BCond {
            continue;
        }

        if last_inst.operands.len() < 2 {
            continue;
        }
        let cond_encoding = match last_inst.operands[0].as_imm() {
            Some(v) => v as u8,
            None => continue,
        };
        let then_block = match &last_inst.operands[1] {
            MachOperand::Block(bid) => *bid,
            _ => continue,
        };
        let condition_inst_id = latest_flag_writer_before(func, header, last_inst_id);
        let source_loc_fallback =
            predicated_source_loc_fallback(func, last_inst_id, condition_inst_id);

        // Header must have exactly 2 successors.
        if header.succs.len() != 2 {
            continue;
        }

        // Determine the fallthrough (join) block.
        let join_block = if header.succs[0] == then_block {
            header.succs[1]
        } else if header.succs[1] == then_block {
            header.succs[0]
        } else {
            continue;
        };

        // Triangle: then_block must jump to join_block.
        let then_blk = func.block(then_block);
        if then_blk.succs.len() != 1 || then_blk.succs[0] != join_block {
            continue;
        }

        // Then block must have exactly 1 predecessor (the header).
        if then_blk.preds.len() != 1 {
            continue;
        }

        // Then block must have exactly 2 instructions: one value-producing + B.
        if then_blk.insts.len() != 2 {
            continue;
        }

        let then_inst_id = then_blk.insts[0];
        let then_br_id = then_blk.insts[1];
        let then_inst = func.inst(then_inst_id);
        let then_br = func.inst(then_br_id);

        if then_br.opcode != AArch64Opcode::B {
            continue;
        }

        // The then instruction must be a register move for safe conversion.
        if then_inst.opcode != AArch64Opcode::MovR {
            continue;
        }

        // Safety check.
        if !is_safe_to_speculate(then_inst.opcode) {
            continue;
        }

        let cond = match decode_cond(cond_encoding) {
            Some(c) => c,
            None => continue,
        };

        // Build CSEL: dst = cond ? then_value : dst
        // When the condition is true, we take the then path (then_value).
        // When false, we fall through (identity: keep dst unchanged).
        if then_inst.operands.len() < 2 {
            continue;
        }
        let dst = then_inst.operands[0].clone();
        let then_src = mov_register_source(then_inst);
        let then_src = match then_src {
            Some(s) => s,
            None => continue,
        };

        let mut csel = MachInst::new(
            AArch64Opcode::Csel,
            vec![
                dst.clone(),
                then_src,
                dst,
                MachOperand::Imm(cond.encoding() as i64),
            ],
        );
        csel.source_loc = then_inst.source_loc;
        apply_source_loc_fallback(&mut csel, source_loc_fallback);

        transforms.push(TriangleTransform {
            header: header_id,
            then_block,
            join_block,
            new_inst: csel,
            condition_inst_id,
            bcond_inst_id: last_inst_id,
            then_inst_id,
            then_br_inst_id: then_br_id,
        });
    }

    transforms
}

/// Apply a triangle transform.
fn apply_triangle_transform(
    func: &mut MachFunction,
    xform: &TriangleTransform,
    provenance: Option<&mut ProvenanceMap>,
) {
    // 1. Insert CSEL before BCond.
    let new_inst_id = func.push_inst(xform.new_inst.clone());
    let header = func.block_mut(xform.header);
    if let Some(pos) = header
        .insts
        .iter()
        .position(|&id| id == xform.bcond_inst_id)
    {
        header.insts.insert(pos, new_inst_id);
    }

    // 2. Replace BCond with B .join.
    let bcond_source_loc = func.inst(xform.bcond_inst_id).source_loc;
    let mut b_join = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(xform.join_block)]);
    b_join.source_loc = bcond_source_loc;
    *func.inst_mut(xform.bcond_inst_id) = b_join;

    // 3. Update CFG.
    let header = func.block_mut(xform.header);
    header.succs.clear();
    header.succs.push(xform.join_block);

    let join = func.block_mut(xform.join_block);
    join.preds.retain(|&bid| bid != xform.then_block);
    if !join.preds.contains(&xform.header) {
        join.preds.push(xform.header);
    }

    // 4. Remove then block from block_order. Per-instruction provenance is
    // updated below for the moved value and deleted branch.
    func.block_order.retain(|&bid| bid != xform.then_block);

    if let Some(provenance) = provenance {
        record_triangle_provenance(provenance, xform, new_inst_id);
    }
}

fn predicated_source_loc_fallback(
    func: &MachFunction,
    bcond_inst_id: InstId,
    condition_inst_id: Option<InstId>,
) -> Option<SourceLoc> {
    func.inst(bcond_inst_id)
        .source_loc
        .or_else(|| condition_inst_id.and_then(|inst_id| func.inst(inst_id).source_loc))
}

fn apply_source_loc_fallback(inst: &mut MachInst, fallback: Option<SourceLoc>) {
    if inst.source_loc.is_none() {
        inst.source_loc = fallback;
    }
}

fn apply_predicated_source_loc_fallback(
    insts: &mut [MachInst],
    provenance: &[NewInstProvenance],
    fallback: Option<SourceLoc>,
) {
    for (inst, provenance) in insts.iter_mut().zip(provenance) {
        if matches!(provenance, NewInstProvenance::Merged(_)) {
            apply_source_loc_fallback(inst, fallback);
        }
    }
}

fn record_diamond_provenance(
    provenance: &mut ProvenanceMap,
    xform: &DiamondTransform,
    new_inst_ids: &[InstId],
) {
    let pass = if_convert_pass_id();

    for (&new_inst_id, source) in new_inst_ids.iter().zip(&xform.new_inst_provenance) {
        match source {
            NewInstProvenance::Replaced(old_inst_id) => {
                provenance.record_replacement(*old_inst_id, new_inst_id, pass.clone());
            }
            NewInstProvenance::Merged(source_inst_ids) => {
                record_predicated_inst_merge(
                    provenance,
                    new_inst_id,
                    source_inst_ids,
                    xform.condition_inst_id,
                    xform.bcond_inst_id,
                    pass.clone(),
                );
            }
        }
    }

    provenance.record_creation(
        xform.bcond_inst_id,
        pass.clone(),
        "unconditional branch replacing converted conditional branch after if-conversion",
    );
    provenance.record_deletion(
        xform.true_br_inst_id,
        pass.clone(),
        "diamond arm branch removed after if-conversion",
    );
    provenance.record_deletion(
        xform.false_br_inst_id,
        pass.clone(),
        "diamond arm branch removed after if-conversion",
    );
    if let Some(dead_cmp) = xform.dead_condition_inst {
        provenance.record_deletion(
            dead_cmp,
            pass,
            "div-guard compare removed: dead after full collapse to a total division",
        );
    }
}

fn record_triangle_provenance(
    provenance: &mut ProvenanceMap,
    xform: &TriangleTransform,
    new_inst_id: InstId,
) {
    let pass = if_convert_pass_id();

    record_predicated_inst_merge(
        provenance,
        new_inst_id,
        &[xform.then_inst_id],
        xform.condition_inst_id,
        xform.bcond_inst_id,
        pass.clone(),
    );
    provenance.record_creation(
        xform.bcond_inst_id,
        pass.clone(),
        "unconditional branch replacing converted conditional branch after if-conversion",
    );
    provenance.record_deletion(
        xform.then_br_inst_id,
        pass,
        "triangle then-branch removed after if-conversion",
    );
}

fn record_predicated_inst_merge(
    provenance: &mut ProvenanceMap,
    new_inst_id: InstId,
    value_source_inst_ids: &[InstId],
    condition_inst_id: Option<InstId>,
    bcond_inst_id: InstId,
    pass: PassId,
) {
    let mut merge_sources = value_source_inst_ids.to_vec();

    // The condition-producing instruction remains live, so clone its source
    // chain into the new predicated instruction before merging removed inputs.
    if let Some(condition_inst_id) = condition_inst_id
        && provenance.get_entry(condition_inst_id).is_some()
    {
        provenance.record_clone(condition_inst_id, new_inst_id, pass.clone());
        merge_sources.push(new_inst_id);
    }

    merge_sources.push(bcond_inst_id);
    if merge_sources
        .iter()
        .any(|&inst_id| provenance.get_entry(inst_id).is_some())
    {
        provenance.record_merge(&merge_sources, new_inst_id, pass);
    }
}

fn latest_flag_writer_before(
    func: &MachFunction,
    block: &trust_cg_ir::MachBlock,
    before_inst_id: InstId,
) -> Option<InstId> {
    let before_pos = block.insts.iter().position(|&id| id == before_inst_id)?;
    block.insts[..before_pos]
        .iter()
        .rev()
        .copied()
        .find(|&inst_id| writes_flags(func.inst(inst_id).opcode))
}

// ---------------------------------------------------------------------------
// Instruction helpers
// ---------------------------------------------------------------------------

fn is_register_operand(operand: &MachOperand) -> bool {
    matches!(
        operand,
        MachOperand::VReg(_) | MachOperand::PReg(_) | MachOperand::Special(_)
    )
}

fn register_operand_at(inst: &MachInst, index: usize) -> Option<MachOperand> {
    let operand = inst.operands.get(index)?.clone();
    is_register_operand(&operand).then_some(operand)
}

// ---------------------------------------------------------------------------
// Cross-arm clobber analysis (multi-instruction diamond if-conversion)
// ---------------------------------------------------------------------------

/// Compare two register operands for identity. Register identity is the same
/// notion the rest of the IR uses: a VReg matches on id + class, a PReg / a
/// Special matches on the register itself. `MachOperand` derives structural
/// `PartialEq`, so a direct comparison captures exactly that.
fn operands_equal(a: &MachOperand, b: &MachOperand) -> bool {
    a == b
}

/// Returns true if `set` already contains a register operand equal to `reg`.
fn contains_register(set: &[MachOperand], reg: &MachOperand) -> bool {
    set.iter().any(|r| operands_equal(r, reg))
}

/// Push a register operand into `set` if not already present (dedup).
fn push_register(set: &mut Vec<MachOperand>, reg: MachOperand) {
    if !contains_register(set, &reg) {
        set.push(reg);
    }
}

/// Returns true if the two register sets share at least one register.
fn registers_overlap(a: &[MachOperand], b: &[MachOperand]) -> bool {
    a.iter().any(|r| contains_register(b, r))
}

/// Collect the explicit register operands of `inst` at the given operand
/// positions (skipping non-register operands like immediates / block labels).
fn collect_register_operands(inst: &MachInst, positions: &[usize], out: &mut Vec<MachOperand>) {
    for &pos in positions {
        if let Some(op) = inst.operands.get(pos)
            && is_register_operand(op)
        {
            push_register(out, op.clone());
        }
    }
}

/// All registers an instruction *defines*: its explicit def-operand positions
/// (per the architectural operand roles, which also covers tied def-use and
/// multi-def layouts) unioned with its implicit physical defs.
fn inst_def_registers(inst: &MachInst) -> Vec<MachOperand> {
    let mut defs = Vec::new();
    let positions = aarch64_def_operand_positions(inst.opcode, inst.operands.len());
    collect_register_operands(inst, &positions, &mut defs);
    for &preg in inst.implicit_defs {
        push_register(&mut defs, MachOperand::PReg(preg));
    }
    defs
}

/// All registers an instruction *reads*: its explicit use-operand positions
/// (covering tied def-use operands) unioned with its implicit physical uses.
fn inst_use_registers(inst: &MachInst) -> Vec<MachOperand> {
    let mut uses = Vec::new();
    let positions = aarch64_use_operand_positions(inst.opcode, inst.operands.len());
    collect_register_operands(inst, &positions, &mut uses);
    for &preg in inst.implicit_uses {
        push_register(&mut uses, MachOperand::PReg(preg));
    }
    uses
}

/// Union of all registers defined by the *hoisted* (non-final) instructions of
/// an arm — i.e. `body[..body.len() - 1]`, EXCLUDING the final MovR whose def is
/// the merged CSEL destination (`csel_dst`).
///
/// These are the registers that, after if-conversion, will be computed
/// unconditionally in the header on BOTH paths. The final MOV is never emitted
/// as a separate def (it is folded into the CSEL), so its destination
/// (`csel_dst`) must NOT appear in this set: `csel_dst` is the one register both
/// arms are *allowed* to co-define and to be live past the diamond (the CSEL
/// recomputes it). A single-instruction arm (`body.len() < 2`) contributes no
/// hoisted defs (its only def is `csel_dst`).
fn arm_hoisted_def_registers(func: &MachFunction, body: &[InstId]) -> Vec<MachOperand> {
    let mut defs = Vec::new();
    if body.len() < 2 {
        return defs;
    }
    for &id in &body[..body.len() - 1] {
        for reg in inst_def_registers(func.inst(id)) {
            push_register(&mut defs, reg);
        }
    }
    defs
}

/// Union of all registers read across every instruction of an arm (the hoisted
/// body insts plus the final MovR, whose use is the CSEL source).
fn arm_use_registers(func: &MachFunction, body: &[InstId]) -> Vec<MachOperand> {
    let mut uses = Vec::new();
    for &id in body {
        for reg in inst_use_registers(func.inst(id)) {
            push_register(&mut uses, reg);
        }
    }
    uses
}

/// Sound live-out guard for hoisted (speculated) temps.
///
/// After if-conversion the hoisted (non-final) instructions of BOTH arms execute
/// *unconditionally* in the header. A register they define therefore holds the
/// speculated value on EVERY path leaving the diamond — including the path that
/// originally did not take that arm. If any such register is read OUTSIDE the
/// two arms (in the join/merge block, or any other block / successor reachable
/// in the function), the read would observe the speculated value instead of the
/// value it had on the not-taken path, which is a miscompile.
///
/// This pass has no precomputed liveness available, so we use a sound,
/// conservative whole-function use-scan: we examine every instruction in every
/// block EXCEPT the two arm bodies (`true_block`, `false_block`) and refuse if
/// any of them reads a hoisted def register. Pre-regalloc VRegs are uniquely
/// identified, so this over-approximates the live-out set (it may also flag
/// reads that are actually dead/dominated) and can therefore only ever cause us
/// to REFUSE more transforms — never to permit an unsafe one. Refusal leaves the
/// branchy diamond intact, which is always correct.
///
/// `csel_dst` (the merged CSEL destination, folded from each arm's final MOV) is
/// intentionally NOT part of `hoisted_defs`; it is allowed to be live-out
/// because the emitted CSEL recomputes it. Callers must build `hoisted_defs` via
/// [`arm_hoisted_def_registers`], which already excludes it.
fn hoisted_defs_used_outside_arms(
    func: &MachFunction,
    hoisted_defs: &[MachOperand],
    true_block: BlockId,
    false_block: BlockId,
) -> bool {
    if hoisted_defs.is_empty() {
        return false;
    }
    for &bid in &func.block_order {
        if bid == true_block || bid == false_block {
            continue;
        }
        for &iid in &func.block(bid).insts {
            let reads = inst_use_registers(func.inst(iid));
            if registers_overlap(&reads, hoisted_defs) {
                return true;
            }
        }
    }
    false
}

/// Returns the register source operand of a MOVR instruction.
fn mov_register_source(inst: &MachInst) -> Option<MachOperand> {
    if inst.opcode != AArch64Opcode::MovR {
        return None;
    }
    register_operand_at(inst, 1)
}

/// Returns true if the instruction is ADD dst, src, #1.
fn is_add_imm1(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::AddRI
        && inst.operands.len() >= 3
        && inst.operands[2].as_imm() == Some(1)
}

/// Returns the base register of an ADD #1 instruction (operand[1]).
fn add_register_base(inst: &MachInst) -> Option<MachOperand> {
    if !is_add_imm1(inst) {
        return None;
    }
    register_operand_at(inst, 1)
}

/// Decode a condition code encoding (0-15) to a CondCode variant.
fn decode_cond(encoding: u8) -> Option<CondCode> {
    match encoding {
        0b0000 => Some(CondCode::EQ),
        0b0001 => Some(CondCode::NE),
        0b0010 => Some(CondCode::HS),
        0b0011 => Some(CondCode::LO),
        0b0100 => Some(CondCode::MI),
        0b0101 => Some(CondCode::PL),
        0b0110 => Some(CondCode::VS),
        0b0111 => Some(CondCode::VC),
        0b1000 => Some(CondCode::HI),
        0b1001 => Some(CondCode::LS),
        0b1010 => Some(CondCode::GE),
        0b1011 => Some(CondCode::LT),
        0b1100 => Some(CondCode::GT),
        0b1101 => Some(CondCode::LE),
        0b1110 => Some(CondCode::AL),
        0b1111 => Some(CondCode::NV),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Late tiny-loop-diamond if-conversion (unpredictable non-affine-recurrence gate)
// ---------------------------------------------------------------------------
//
// A SECOND, LATE admission for the exact shape the primary `if-convert` pass
// cannot reach: a loop-resident diamond whose CONDITION is derived from a
// NON-AFFINE in-loop self-recurrence (an xorshift eor/shift mixing chain), with
// one arm doing a single pure compute and the other the identity — b1_mispredict's
// `if s&6==2 { acc = acc.rotate_left(7) }`. LLVM if-converts it to a CSEL; the
// bridge's primary if-convert can NOT, because at its pass position (before
// dce+cfg-simplify) the rotate arm is neither a clean 2-edge diamond nor a
// ≤2-inst arm (rotate-idiom leaves dead LSL/LSR and a chained merge block). Only
// after cfg-simplify is it a clean `header -> {rot-arm, identity-arm} -> join`
// diamond. This pass runs THERE.
//
// WHY NON-AFFINE IS LOAD-BEARING: converting a WELL-PREDICTED branch to a CSEL
// forces both arms + costs a select on the hot path and REGRESSES (a periodic-
// condition microbench loses ~0.26 ns/iter). The admission therefore fires ONLY
// when the branch condition flows, across the loop back-edge, from a register
// that is BOTH loop-carried (a def cycle) AND mixed by an EOR-family op — the
// xorshift signature a branch predictor fails on. A monotone/affine IV (Add/Sub
// only) never satisfies the EOR-cycle requirement, so predictable diamonds stay
// branchy.
//
// SOUNDNESS: identical to the primary diamond conversion — both arms are hoisted
// and a CSEL recomputes the merge. The hoisted compute is `is_safe_to_speculate`
// (pure, flag-neutral, non-trapping, non-memory, non-control) and its temps are
// proven not live outside the arms. The CSEL is value-exact for the select. This
// pass NEVER speculates a trapping/memory/div/call op (the arm-shape check
// rejects anything but a single pure compute + register moves). No new opcode.
//
// Kill switch: `TRUST_CG_DISABLE_PASSES=tinyloop` (default ON).

/// Late tiny-loop-diamond if-conversion pass (see the section comment).
pub struct TinyLoopDiamondConvert;

impl MachinePass for TinyLoopDiamondConvert {
    fn name(&self) -> &str {
        "tiny-loop-diamond"
    }

    fn run(&mut self, _func: &mut MachFunction) -> bool {
        // Needs loop analysis; the analysis-driven driver is the real entry.
        false
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let la = analyses.loop_analysis(func);
        run_tiny_loop_diamond(func, None, Some(la))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let la = analyses.loop_analysis(func);
        run_tiny_loop_diamond(func, Some(provenance), Some(la))
    }
}

/// Pure predicate: does a `TRUST_CG_DISABLE_PASSES` value disable the tiny-loop
/// diamond conversion? True iff the comma list contains the `tinyloop` token.
fn tiny_loop_disabled_by(list: &str) -> bool {
    list.split(',').map(str::trim).any(|tok| tok == "tinyloop")
}

#[cfg(test)]
thread_local! {
    static TEST_TINY_LOOP_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

fn tiny_loop_enabled() -> bool {
    #[cfg(test)]
    {
        !TEST_TINY_LOOP_DISABLED.with(std::cell::Cell::get)
    }
    #[cfg(not(test))]
    match crate::env_lock::var("TRUST_CG_DISABLE_PASSES") {
        Ok(list) => !tiny_loop_disabled_by(&list),
        Err(_) => true,
    }
}

fn is_eor_family(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::EorRR
            | AArch64Opcode::EorRI
            | AArch64Opcode::EorRRShift
            | AArch64Opcode::EorRRLsl
            | AArch64Opcode::EorRRLsr
    )
}

fn run_tiny_loop_diamond(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
    loop_analysis: Option<&LoopAnalysis>,
) -> bool {
    if !tiny_loop_enabled() {
        return false;
    }
    let Some(la) = loop_analysis else {
        return false;
    };
    let xforms = collect_tiny_loop_diamonds(func, la);
    if xforms.is_empty() {
        return false;
    }
    for xform in &xforms {
        apply_diamond_transform(func, xform, provenance.as_deref_mut());
    }
    true
}

/// The pure-compute arm of a tiny-loop diamond: its hoistable non-final
/// instructions (an optional leading rename `MovR` plus one pure compute op) and
/// the register the arm's value ultimately comes from (the final `MovR` source).
struct TinyComputeArm {
    /// Non-final instructions to hoist into the header (rename?, compute).
    hoist: Vec<InstId>,
    /// The register the arm's merged value is read from (final `MovR` src).
    value: MachOperand,
    /// Registers the hoisted instructions define (for the live-out guard).
    hoisted_defs: Vec<MachOperand>,
}

/// Recognize a tiny pure-compute arm body `[MovR tmp,src]? PURE_COMPUTE
/// [MovR merge,result]` writing `merge`. Returns the hoist list + value source,
/// or `None`. The compute op must be `is_safe_to_speculate` (pure/flag-neutral/
/// non-trapping/non-memory/non-control) so hoisting it past the branch is sound.
fn parse_tiny_compute_arm(
    func: &MachFunction,
    body: &[InstId],
    merge: &MachOperand,
) -> Option<TinyComputeArm> {
    // Final instruction: `MovR merge, result`.
    let (&last_id, front) = body.split_last()?;
    let last = func.inst(last_id);
    if last.opcode != AArch64Opcode::MovR
        || last.operands.first().map(|d| operands_equal(d, merge)) != Some(true)
    {
        return None;
    }
    let value = register_operand_at(last, 1)?;
    // `front` (the hoisted body) must be 1 or 2 insts: [compute] or [rename, compute].
    if front.is_empty() || front.len() > 2 {
        return None;
    }
    // Every hoisted inst must be safe to speculate (pure, flag-neutral, no
    // trap/memory/control). A leading rename `MovR` qualifies; the compute op
    // (e.g. RorRI) qualifies. This is what forbids speculating a load/div/etc.
    for &id in front {
        if !is_safe_to_speculate(func.inst(id).opcode) {
            return None;
        }
    }
    // Exactly ONE of the hoisted insts is a non-move compute op; any leading move
    // is a pure rename. (Two compute ops would exceed the "≤1 compute op" gate.)
    let compute_count = front
        .iter()
        .filter(|&&id| func.inst(id).opcode != AArch64Opcode::MovR)
        .count();
    if compute_count != 1 {
        return None;
    }
    let mut hoisted_defs = Vec::new();
    for &id in front {
        for d in inst_def_registers(func.inst(id)) {
            push_register(&mut hoisted_defs, d);
        }
    }
    Some(TinyComputeArm {
        hoist: front.to_vec(),
        value,
        hoisted_defs,
    })
}

/// Recognize an identity arm body `[MovR merge, src]` writing `merge`; returns
/// the value source `src`.
fn parse_identity_arm(
    func: &MachFunction,
    body: &[InstId],
    merge: &MachOperand,
) -> Option<MachOperand> {
    if body.len() != 1 {
        return None;
    }
    let inst = func.inst(body[0]);
    if inst.opcode != AArch64Opcode::MovR
        || inst.operands.first().map(|d| operands_equal(d, merge)) != Some(true)
    {
        return None;
    }
    register_operand_at(inst, 1)
}

/// Does the branch condition source reach, within the loop, a NON-AFFINE
/// self-recurrence — a register that is both (a) part of an in-loop def cycle and
/// (b) defined by an EOR-family op (the xorshift mixing signature)? A monotone /
/// affine IV (Add/Sub-only cycle) never satisfies (b), so it is excluded.
fn cond_reaches_nonaffine_recurrence(
    func: &MachFunction,
    def_map: &std::collections::HashMap<VReg, Vec<InstId>>,
    cond_source_regs: &[MachOperand],
) -> bool {
    // Backward-reachable register set from the condition sources.
    let mut reachable: std::collections::HashSet<VReg> = std::collections::HashSet::new();
    let mut work: Vec<VReg> = cond_source_regs
        .iter()
        .filter_map(MachOperand::as_vreg)
        .collect();
    while let Some(v) = work.pop() {
        if !reachable.insert(v) {
            continue;
        }
        if let Some(defs) = def_map.get(&v) {
            for &d in defs {
                for u in inst_use_registers(func.inst(d)) {
                    if let Some(uv) = u.as_vreg() {
                        work.push(uv);
                    }
                }
            }
        }
    }
    // Some reachable register is EOR-defined in-loop AND lies on a def cycle.
    for &v in &reachable {
        let Some(defs) = def_map.get(&v) else {
            continue;
        };
        if defs.iter().any(|&d| is_eor_family(func.inst(d).opcode))
            && vreg_reaches_self(func, def_map, v)
        {
            return true;
        }
    }
    false
}

/// Is `target` reachable backward from its own in-loop defs (i.e. `target` lies
/// on a def cycle)? A visited set bounds the walk.
fn vreg_reaches_self(
    func: &MachFunction,
    def_map: &std::collections::HashMap<VReg, Vec<InstId>>,
    target: VReg,
) -> bool {
    let mut visited: std::collections::HashSet<VReg> = std::collections::HashSet::new();
    let mut work: Vec<VReg> = Vec::new();
    if let Some(defs) = def_map.get(&target) {
        for &d in defs {
            for u in inst_use_registers(func.inst(d)) {
                if let Some(uv) = u.as_vreg() {
                    work.push(uv);
                }
            }
        }
    }
    while let Some(v) = work.pop() {
        if v == target {
            return true;
        }
        if !visited.insert(v) {
            continue;
        }
        if let Some(defs) = def_map.get(&v) {
            for &d in defs {
                for u in inst_use_registers(func.inst(d)) {
                    if let Some(uv) = u.as_vreg() {
                        work.push(uv);
                    }
                }
            }
        }
    }
    false
}

/// Collect tiny-loop-diamond transforms over the post-cfg-simplify CFG. Mirrors
/// the header/arm structural checks of [`collect_diamond_transforms`] but admits
/// ONLY the tight tiny-pure-arm + non-affine-recurrence-condition shape.
fn collect_tiny_loop_diamonds(
    func: &MachFunction,
    loop_analysis: &LoopAnalysis,
) -> Vec<DiamondTransform> {
    let mut transforms = Vec::new();

    for &header_id in &func.block_order {
        let header = func.block(header_id);
        let insts_len = header.insts.len();
        let Some(&last_inst_id) = header.insts.last() else {
            continue;
        };
        // Header ends `BCond T` (fallthrough form) or `BCond T; B F` (explicit).
        let last_inst = func.inst(last_inst_id);
        let (bcond_inst_id, header_fallthrough_br) = if last_inst.opcode == AArch64Opcode::BCond {
            (last_inst_id, None)
        } else if last_inst.is_unconditional_branch() && insts_len >= 2 {
            let prev_id = header.insts[insts_len - 2];
            if func.inst(prev_id).opcode == AArch64Opcode::BCond {
                (prev_id, Some(last_inst_id))
            } else {
                continue;
            }
        } else {
            continue;
        };

        let bcond = func.inst(bcond_inst_id);
        if bcond.operands.len() < 2 || header.succs.len() != 2 {
            continue;
        }
        let cond_encoding = match bcond.operands[0].as_imm() {
            Some(v) => v as u8,
            None => continue,
        };
        let true_block = match &bcond.operands[1] {
            MachOperand::Block(bid) => *bid,
            _ => continue,
        };
        let false_block = if header.succs[0] == true_block {
            header.succs[1]
        } else if header.succs[1] == true_block {
            header.succs[0]
        } else {
            continue;
        };

        // (1) Loop-resident.
        let Some(lp) = loop_analysis.containing_loop(header_id) else {
            continue;
        };

        // Arm blocks: single pred (header), single succ = shared join.
        if func.block(true_block).preds.len() != 1 || func.block(false_block).preds.len() != 1 {
            continue;
        }
        let true_blk = func.block(true_block);
        let false_blk = func.block(false_block);
        if true_blk.succs.len() != 1 || false_blk.succs.len() != 1 {
            continue;
        }
        let join_block = true_blk.succs[0];
        if false_blk.succs[0] != join_block {
            continue;
        }
        let (Some(&true_last_id), Some(&false_last_id)) =
            (true_blk.insts.last(), false_blk.insts.last())
        else {
            continue;
        };
        if !func.inst(true_last_id).is_unconditional_branch()
            || !func.inst(false_last_id).is_unconditional_branch()
        {
            continue;
        }
        let true_body: Vec<InstId> = true_blk.insts[..true_blk.insts.len() - 1].to_vec();
        let false_body: Vec<InstId> = false_blk.insts[..false_blk.insts.len() - 1].to_vec();

        // The merge register: both arms' FINAL instruction writes the same dst.
        let (Some(&t_final), Some(&f_final)) = (true_body.last(), false_body.last()) else {
            continue;
        };
        let (Some(t_dst), Some(f_dst)) = (
            func.inst(t_final).operands.first(),
            func.inst(f_final).operands.first(),
        ) else {
            continue;
        };
        if !operands_equal(t_dst, f_dst) {
            continue;
        }
        let merge = t_dst.clone();

        // (2) Tiny-pure/identity arm shapes (exactly one of each).
        let cond = match decode_cond(cond_encoding) {
            Some(c) => c,
            None => continue,
        };
        let (compute_in_true, compute_arm, identity_value) = if let (Some(ca), Some(iv)) = (
            parse_tiny_compute_arm(func, &true_body, &merge),
            parse_identity_arm(func, &false_body, &merge),
        ) {
            (true, ca, iv)
        } else if let (Some(ca), Some(iv)) = (
            parse_tiny_compute_arm(func, &false_body, &merge),
            parse_identity_arm(func, &true_body, &merge),
        ) {
            (false, ca, iv)
        } else {
            continue;
        };

        // (3) Condition source reaches a NON-AFFINE in-loop self-recurrence.
        let condition_inst_id = latest_flag_writer_before(func, header, bcond_inst_id);
        let Some(cond_id) = condition_inst_id else {
            continue;
        };
        let cond_source_regs = inst_use_registers(func.inst(cond_id));
        let def_map = build_inloop_def_map(func, &lp.body);
        if !cond_reaches_nonaffine_recurrence(func, &def_map, &cond_source_regs) {
            continue;
        }

        // Live-out guard: hoisted temps must not be observed outside the arms.
        if hoisted_defs_used_outside_arms(func, &compute_arm.hoisted_defs, true_block, false_block)
        {
            continue;
        }

        // Build the hoisted instructions + the merged CSEL.
        let mut new_insts: Vec<MachInst> = Vec::new();
        let mut new_inst_provenance: Vec<NewInstProvenance> = Vec::new();
        for &id in &compute_arm.hoist {
            new_insts.push(func.inst(id).clone());
            new_inst_provenance.push(NewInstProvenance::Replaced(id));
        }
        // CSEL merge = cond ? true-value : false-value.
        let (on_true, on_false) = if compute_in_true {
            (compute_arm.value.clone(), identity_value.clone())
        } else {
            (identity_value.clone(), compute_arm.value.clone())
        };
        let mut csel = MachInst::new(
            AArch64Opcode::Csel,
            vec![
                merge.clone(),
                on_true,
                on_false,
                MachOperand::Imm(cond.encoding() as i64),
            ],
        );
        csel.source_loc = func
            .inst(t_final)
            .source_loc
            .or(func.inst(f_final).source_loc);
        let fallback = predicated_source_loc_fallback(func, bcond_inst_id, condition_inst_id);
        apply_source_loc_fallback(&mut csel, fallback);
        new_insts.push(csel);
        new_inst_provenance.push(NewInstProvenance::Merged(vec![t_final, f_final]));

        transforms.push(DiamondTransform {
            header: header_id,
            true_block,
            false_block,
            join_block,
            new_insts,
            new_inst_provenance,
            condition_inst_id,
            bcond_inst_id,
            true_br_inst_id: true_last_id,
            false_br_inst_id: false_last_id,
            header_fallthrough_br,
            dead_condition_inst: None,
        });
    }

    transforms
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, PassId,
        ProvenanceMap, ProvenanceStatus, RegClass, Signature, TransformKind, TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn source_loc(line: u32) -> trust_cg_ir::SourceLoc {
        trust_cg_ir::SourceLoc {
            file: 1,
            line,
            col: 7,
        }
    }

    #[test]
    fn materialized_boolean_matchers_reject_shifted_or_malformed_moves() {
        let shifted_one = MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(1), imm(16)]);
        assert!(!inst_materializes_one(&shifted_one));

        let shifted_zero = MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(0), imm(16)]);
        assert!(!inst_materializes_zero(&shifted_zero));

        let explicit_zero_shift = MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(1), imm(0)]);
        assert!(inst_materializes_one(&explicit_zero_shift));

        let malformed_movi = MachInst::new(
            AArch64Opcode::MovI,
            vec![
                vreg(0),
                imm(0),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::X0),
            ],
        );
        assert!(!inst_materializes_zero(&malformed_movi));
    }

    fn assert_optimized_away_by_if_convert(provenance: &ProvenanceMap, inst_id: InstId) {
        let entry = provenance
            .get_entry(inst_id)
            .expect("removed instruction should retain optimized-away provenance");
        match &entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass, &PassId::new("if-convert"));
                assert!(justification.contains("if-conversion"));
            }
            other => panic!("expected if-convert optimized-away provenance, got {other:?}"),
        }
    }

    fn assert_compiler_generated_by_if_convert(provenance: &ProvenanceMap, inst_id: InstId) {
        let entry = provenance
            .get_entry(inst_id)
            .expect("replacement branch should have compiler-generated provenance");
        match &entry.status {
            ProvenanceStatus::CompilerGenerated { pass, reason } => {
                assert_eq!(pass, &PassId::new("if-convert"));
                assert!(reason.contains("converted conditional branch"));
            }
            other => panic!("expected compiler-generated branch provenance, got {other:?}"),
        }
    }

    /// Build a diamond CFG:
    /// bb0: CMP + BCond -> bb1
    /// bb2 (false): false_insts + B bb3
    /// bb1 (true): true_insts + B bb3
    /// bb3 (join): RET
    fn make_diamond(
        cmp: MachInst,
        cond: CondCode,
        true_insts: Vec<MachInst>,
        false_insts: Vec<MachInst>,
    ) -> MachFunction {
        let mut func = MachFunction::new(
            "test_if_convert".to_string(),
            Signature::new(vec![], vec![]),
        );

        let bb0 = func.entry;
        let bb1 = func.create_block(); // true
        let bb2 = func.create_block(); // false
        let bb3 = func.create_block(); // join

        // bb0: CMP + BCond
        let cmp_id = func.push_inst(cmp);
        func.append_inst(bb0, cmp_id);
        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(cond.encoding() as i64), MachOperand::Block(bb1)],
        );
        let bcond_id = func.push_inst(bcond);
        func.append_inst(bb0, bcond_id);

        // bb1 (true): true_insts + B bb3
        for inst in true_insts {
            let id = func.push_inst(inst);
            func.append_inst(bb1, id);
        }
        let b1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, b1);

        // bb2 (false): false_insts + B bb3
        for inst in false_insts {
            let id = func.push_inst(inst);
            func.append_inst(bb2, id);
        }
        let b2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, b2);

        // bb3 (join): RET
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret_id);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        func
    }

    /// Build a triangle CFG:
    /// bb0: CMP + BCond -> bb1, fallthrough -> bb2
    /// bb1 (then): then_inst + B bb2
    /// bb2 (join): RET
    fn make_triangle(cmp: MachInst, cond: CondCode, then_inst: MachInst) -> MachFunction {
        let mut func =
            MachFunction::new("test_triangle".to_string(), Signature::new(vec![], vec![]));

        let bb0 = func.entry;
        let bb1 = func.create_block(); // then
        let bb2 = func.create_block(); // join

        // bb0: CMP + BCond
        let cmp_id = func.push_inst(cmp);
        func.append_inst(bb0, cmp_id);
        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(cond.encoding() as i64), MachOperand::Block(bb1)],
        );
        let bcond_id = func.push_inst(bcond);
        func.append_inst(bb0, bcond_id);

        // bb1 (then): then_inst + B bb2
        let ti = func.push_inst(then_inst);
        func.append_inst(bb1, ti);
        let b1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, b1);

        // bb2 (join): RET
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret_id);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb2);

        func
    }

    // ---- Provenance preservation ----

    #[test]
    fn test_diamond_provenance_merges_condition_branch_and_arm_values() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_mov]);
        let cmp_id = func.block(BlockId(0)).insts[0];
        let bcond_id = func.block(BlockId(0)).insts[1];
        let true_mov_id = func.block(BlockId(1)).insts[0];
        let true_br_id = func.block(BlockId(1)).insts[1];
        let false_mov_id = func.block(BlockId(2)).insts[0];
        let false_br_id = func.block(BlockId(2)).insts[1];
        let ret_id = func.block(BlockId(3)).insts[0];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(90), &[cmp_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(91), &[bcond_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(92), &[true_mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(93), &[false_mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(94), &[true_br_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(95), &[false_br_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(96), &[ret_id], PassId::new("isel"));

        let mut pass = IfConversion;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 3);
        let csel_id = header.insts[1];
        assert_eq!(header.insts[2], bcond_id);

        let csel = func.inst(csel_id);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(csel.operands[0], vreg(2));
        assert_eq!(csel.operands[1], vreg(3));
        assert_eq!(csel.operands[2], vreg(4));

        let csel_entry = provenance
            .get_entry(csel_id)
            .expect("CSEL should inherit condition, branch, and arm value provenance");
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(90)));
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(91)));
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(92)));
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(93)));
        assert!(csel_entry.transforms.iter().any(|record| {
            record.pass == PassId::new("if-convert")
                && record.kind == TransformKind::Cloned { source: cmp_id }
        }));
        let transform = csel_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("if-convert"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![true_mov_id, false_mov_id, csel_id, bcond_id],
            }
        );
        assert!(csel_entry.is_active());
        assert!(provenance.get_entry(true_mov_id).is_none());
        assert!(provenance.get_entry(false_mov_id).is_none());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(90)),
            Some(&[cmp_id, csel_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(91)),
            Some(&[csel_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(92)),
            Some(&[csel_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(93)),
            Some(&[csel_id][..])
        );

        let rewritten_branch = func.inst(bcond_id);
        assert_eq!(rewritten_branch.opcode, AArch64Opcode::B);
        assert_compiler_generated_by_if_convert(&provenance, bcond_id);

        assert_optimized_away_by_if_convert(&provenance, true_br_id);
        assert_optimized_away_by_if_convert(&provenance, false_br_id);
        assert_eq!(provenance.get_entry(cmp_id).unwrap().transforms.len(), 1);
        assert_eq!(provenance.get_entry(ret_id).unwrap().transforms.len(), 1);
    }

    #[test]
    fn test_triangle_direct_provenance_merges_condition_branch_and_then_value() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let then_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);

        let mut func = make_triangle(cmp, CondCode::NE, then_mov);
        let cmp_id = func.block(BlockId(0)).insts[0];
        let bcond_id = func.block(BlockId(0)).insts[1];
        let then_mov_id = func.block(BlockId(1)).insts[0];
        let then_br_id = func.block(BlockId(1)).insts[1];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(100), &[cmp_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(101), &[bcond_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(102), &[then_mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(103), &[then_br_id], PassId::new("isel"));

        let mut pass = IfConversion;
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 3);
        let csel_id = header.insts[1];
        assert_eq!(header.insts[2], bcond_id);

        let csel = func.inst(csel_id);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(csel.operands[0], vreg(2));
        assert_eq!(csel.operands[1], vreg(3));
        assert_eq!(csel.operands[2], vreg(2));

        let csel_entry = provenance
            .get_entry(csel_id)
            .expect("triangle CSEL should inherit condition, branch, and then-value provenance");
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(100)));
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(101)));
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(102)));
        assert!(csel_entry.transforms.iter().any(|record| {
            record.pass == PassId::new("if-convert")
                && record.kind == TransformKind::Cloned { source: cmp_id }
        }));
        let transform = csel_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("if-convert"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![then_mov_id, csel_id, bcond_id],
            }
        );
        assert!(provenance.get_entry(then_mov_id).is_none());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(100)),
            Some(&[cmp_id, csel_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(101)),
            Some(&[csel_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(102)),
            Some(&[csel_id][..])
        );

        assert_compiler_generated_by_if_convert(&provenance, bcond_id);
        assert_optimized_away_by_if_convert(&provenance, then_br_id);
    }

    #[test]
    fn test_diamond_csel_source_loc_falls_back_to_branch_then_condition() {
        let cmp_loc = source_loc(31);
        let branch_loc = source_loc(41);
        let cmp =
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]).with_source_loc(cmp_loc);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_mov]);
        let bcond_id = func.block(BlockId(0)).insts[1];
        func.inst_mut(bcond_id).source_loc = Some(branch_loc);

        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let csel = func.inst(header.insts[1]);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(
            csel.source_loc,
            Some(branch_loc),
            "if-convert should use the converted branch line when arm values have no source_loc"
        );
        assert_eq!(func.inst(bcond_id).source_loc, Some(branch_loc));

        let cmp =
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]).with_source_loc(cmp_loc);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);
        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_mov]);

        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let csel = func.inst(header.insts[1]);
        assert_eq!(
            csel.source_loc,
            Some(cmp_loc),
            "if-convert should use the flag-writer line when neither arm nor branch has source_loc"
        );
    }

    #[test]
    fn test_triangle_csel_source_loc_falls_back_to_branch() {
        let branch_loc = source_loc(53);
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let then_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);

        let mut func = make_triangle(cmp, CondCode::NE, then_mov);
        let bcond_id = func.block(BlockId(0)).insts[1];
        func.inst_mut(bcond_id).source_loc = Some(branch_loc);

        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let csel = func.inst(header.insts[1]);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(
            csel.source_loc,
            Some(branch_loc),
            "triangle if-convert should use the converted branch line when then-value has no source_loc"
        );
    }

    // ---- Diamond: CSEL formation ----

    #[test]
    fn test_diamond_csel_movr() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 3); // CMP, CSEL, B

        let csel = func.inst(header.insts[1]);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(csel.operands[0], vreg(2));
        assert_eq!(csel.operands[1], vreg(3));
        assert_eq!(csel.operands[2], vreg(4));
        assert_eq!(csel.operands[3], imm(CondCode::EQ.encoding() as i64));

        // Arm blocks removed.
        assert!(!func.block_order.contains(&BlockId(1)));
        assert!(!func.block_order.contains(&BlockId(2)));
    }

    #[test]
    fn test_diamond_movi_does_not_form_invalid_csel() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(42)]);
        let false_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(99)]);

        let mut func = make_diamond(cmp, CondCode::GE, vec![true_mov], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));

        assert_eq!(func.block_order.len(), 4);
        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 2);
        assert_eq!(func.inst(header.insts[1]).opcode, AArch64Opcode::BCond);
    }

    // ---- Diamond: CSINC formation ----

    #[test]
    fn test_diamond_csinc() {
        // true: MOV v2, v3; false: ADD v2, v4, #1
        // -> CSINC v2, v3, v4, EQ
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(4), imm(1)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_add]);
        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let csinc = func.inst(header.insts[1]);
        assert_eq!(csinc.opcode, AArch64Opcode::Csinc);
        assert_eq!(csinc.operands[0], vreg(2)); // dst
        assert_eq!(csinc.operands[1], vreg(3)); // true_src
        assert_eq!(csinc.operands[2], vreg(4)); // false_base (will be incremented)
        assert_eq!(csinc.operands[3], imm(CondCode::EQ.encoding() as i64));
    }

    #[test]
    fn test_diamond_csinc_swapped() {
        // true: ADD v2, v3, #1; false: MOV v2, v4
        // -> CSINC v2, v4, v3, NE (inverted from EQ)
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(3), imm(1)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_add], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let csinc = func.inst(header.insts[1]);
        assert_eq!(csinc.opcode, AArch64Opcode::Csinc);
        assert_eq!(csinc.operands[0], vreg(2));
        assert_eq!(csinc.operands[1], vreg(4)); // MOV source (now true for inverted cond)
        assert_eq!(csinc.operands[2], vreg(3)); // ADD base
        assert_eq!(csinc.operands[3], imm(CondCode::NE.encoding() as i64));
    }

    #[test]
    fn test_diamond_csinc_movi_source_does_not_convert() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(7)]);
        let false_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(4), imm(1)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_add]);
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    // ---- Diamond: CSNEG formation ----

    #[test]
    fn test_diamond_csneg() {
        // true: MOV v2, v3; false: NEG v2, v4
        // -> CSNEG v2, v3, v4, LT
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_neg = MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::LT, vec![true_mov], vec![false_neg]);
        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let csneg = func.inst(header.insts[1]);
        assert_eq!(csneg.opcode, AArch64Opcode::Csneg);
        assert_eq!(csneg.operands[0], vreg(2));
        assert_eq!(csneg.operands[1], vreg(3));
        assert_eq!(csneg.operands[2], vreg(4));
        assert_eq!(csneg.operands[3], imm(CondCode::LT.encoding() as i64));
    }

    #[test]
    fn test_diamond_csneg_swapped() {
        // true: NEG v2, v3; false: MOV v2, v4
        // -> CSNEG v2, v4, v3, GE (inverted from LT)
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_neg = MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::LT, vec![true_neg], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let csneg = func.inst(header.insts[1]);
        assert_eq!(csneg.opcode, AArch64Opcode::Csneg);
        assert_eq!(csneg.operands[0], vreg(2));
        assert_eq!(csneg.operands[1], vreg(4)); // MOV source
        assert_eq!(csneg.operands[2], vreg(3)); // NEG source
        assert_eq!(csneg.operands[3], imm(CondCode::GE.encoding() as i64));
    }

    #[test]
    fn test_diamond_csneg_movi_source_does_not_convert() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(7)]);
        let false_neg = MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::LT, vec![true_mov], vec![false_neg]);
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    // ---- Diamond: multi-instruction ----

    #[test]
    fn test_diamond_multi_inst() {
        // true: ADD v5, v3, #10; MOV v2, v5; false: MOV v2, v4
        // -> hoist ADD v5, v3, #10; CSEL v2, v5, v4, EQ
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(10)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_add, true_mov], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        // CMP, hoisted ADD, CSEL, B = 4 instructions
        assert_eq!(header.insts.len(), 4);

        let add = func.inst(header.insts[1]);
        assert_eq!(add.opcode, AArch64Opcode::AddRI);

        let csel = func.inst(header.insts[2]);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(csel.operands[0], vreg(2));
        assert_eq!(csel.operands[1], vreg(5));
        assert_eq!(csel.operands[2], vreg(4));
    }

    #[test]
    fn test_diamond_multi_inst_disjoint_both_arms_converts() {
        // Positive / over-suppression guard: both arms have 2 instructions but
        // use DISJOINT intermediate registers, so unconditional speculation of
        // both is sound and the diamond MUST still if-convert.
        //
        // true:  ADD v5, v3, #1 ; MOV v2, v5
        // false: ADD v6, v4, #2 ; MOV v2, v6   (distinct temps v5 vs v6)
        // -> hoist ADD v5,v3,#1 and ADD v6,v4,#2; CSEL v2, v5, v6, EQ
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);
        let false_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(6), vreg(4), imm(2)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(6)]);

        let mut func = make_diamond(
            cmp,
            CondCode::EQ,
            vec![true_add, true_mov],
            vec![false_add, false_mov],
        );
        let mut pass = IfConversion;
        assert!(
            pass.run(&mut func),
            "safe disjoint multi-inst diamond must still if-convert"
        );

        // Both arm blocks removed (header + join remain); header now holds
        // CMP, both hoisted ADDs, CSEL, B.
        assert_eq!(func.block_order.len(), 2);
        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 5);

        // Find the CSEL: its two sources must be the distinct per-arm temps.
        let csel = header
            .insts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::Csel)
            .expect("expected a CSEL in the converted header");
        assert_eq!(csel.operands[0], vreg(2));
        assert_eq!(csel.operands[1], vreg(5));
        assert_eq!(csel.operands[2], vreg(6));
        assert_ne!(
            csel.operands[1], csel.operands[2],
            "disjoint arms must keep distinct CSEL sources"
        );
    }

    #[test]
    fn test_diamond_cross_arm_clobber_is_refused() {
        // NON-MASKING regression test for the cross-arm-clobber miscompile.
        //
        // Both arms write the SAME intermediate register v5 (the source that
        // feeds the merged CSEL) and the SAME destination v2. Hoisting both
        // arms unconditionally into the header would compute v5 = a+1 then
        // v5 = a+2, so by the time the CSEL runs v5 holds a+2 for BOTH inputs:
        // the true arm's value (a+1) is lost -> CSEL v2, v5, v5 -> live
        // miscompile. The fix must REFUSE this transform and leave the branchy
        // diamond intact.
        //
        // true:  ADD v5, v3, #1 ; MOV v2, v5
        // false: ADD v5, v3, #2 ; MOV v2, v5   (SAME temp v5, SAME dst v2)
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);
        let false_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(2)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);

        let mut func = make_diamond(
            cmp,
            CondCode::EQ,
            vec![true_add, true_mov],
            vec![false_add, false_mov],
        );
        let mut pass = IfConversion;
        let changed = pass.run(&mut func);

        // Primary, non-masking check: the transform must be refused. Refusal is
        // always sound (leaves the branchy form). Pre-fix this fails because
        // the pass converts and returns true.
        assert!(
            !changed,
            "cross-arm clobber diamond must NOT be if-converted (unsound speculation)"
        );
        // Arm blocks must remain when conversion is refused.
        assert_eq!(
            func.block_order.len(),
            4,
            "arm blocks must remain when conversion is refused"
        );
        // Header must still end in a conditional branch.
        let header = func.block(BlockId(0));
        let last = func.inst(header.insts.last().copied().unwrap());
        assert_eq!(
            last.opcode,
            AArch64Opcode::BCond,
            "header must still end in BCond when not converted"
        );

        // Secondary smoking-gun check: had the buggy pass run, it would have
        // emitted `CSEL v2, v5, v5` (both sources collapsed to the clobbered
        // temp). Assert no such collapsed CSEL exists anywhere in the header.
        for &id in &header.insts {
            let i = func.inst(id);
            if i.opcode == AArch64Opcode::Csel {
                assert_ne!(
                    i.operands[1], i.operands[2],
                    "CSEL sources collapsed to one clobbered reg -> miscompile (true arm value lost)"
                );
            }
        }
    }

    #[test]
    fn test_diamond_cross_arm_def_used_by_other_arm_is_refused() {
        // Variant: the false arm's hoisted ADD defines v5, which the TRUE arm
        // reads as its final MOV source. Hoisting both unconditionally would
        // make the false arm overwrite v5 before the CSEL reads it for the
        // true side -> clobber. Must be refused.
        //
        // true:  MOV v2, v5            (reads v5)
        // false: ADD v5, v3, #2 ; MOV v2, v5   (defines v5)
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);
        let false_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(2)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);

        let mut func = make_diamond(
            cmp,
            CondCode::EQ,
            vec![true_mov],
            vec![false_add, false_mov],
        );
        let mut pass = IfConversion;
        assert!(
            !pass.run(&mut func),
            "cross-arm def/use overlap must NOT be if-converted"
        );
        assert_eq!(func.block_order.len(), 4);
        let header = func.block(BlockId(0));
        assert_eq!(
            func.inst(header.insts.last().copied().unwrap()).opcode,
            AArch64Opcode::BCond
        );
    }

    #[test]
    fn test_diamond_hoisted_def_live_out_in_join_is_refused() {
        // DEFECT 1 (residual miscompile) regression, NON-MASKING.
        //
        // The true arm's hoisted ADD defines v5 and the join block READS v5
        // (MOV v7, v5 before RET). The arm-local liveness check passes (v5 is
        // used by the true arm's own final MOV v2, v5), but after if-conversion
        // the ADD runs unconditionally, so on the FALSE path the join would
        // observe v5 = v3+1 (the speculated true-arm value) instead of whatever
        // v5 held on the not-taken path -> v7 wrong. The fix's live-out scan
        // must REFUSE this.
        //
        // true:  ADD v5, v3, #1 ; MOV v2, v5      (v5 escapes to the join)
        // false: MOV v2, v4
        // join:  MOV v7, v5 ; RET                 (reads the hoisted temp v5)
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_add, true_mov], vec![false_mov]);

        // Inject `MOV v7, v5` at the top of the join block (BlockId(3)), before
        // its RET, so the hoisted temp v5 is read OUTSIDE the two arms.
        let join_read = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(7), vreg(5)]));
        func.block_mut(BlockId(3)).insts.insert(0, join_read);

        let mut pass = IfConversion;
        let changed = pass.run(&mut func);

        assert!(
            !changed,
            "hoisted def read in the join (live-out) must NOT be if-converted (residual miscompile)"
        );
        // Arm blocks must remain when conversion is refused.
        assert_eq!(
            func.block_order.len(),
            4,
            "arm blocks must remain when live-out conversion is refused"
        );
        // Header must still end in a conditional branch.
        let header = func.block(BlockId(0));
        assert_eq!(
            func.inst(header.insts.last().copied().unwrap()).opcode,
            AArch64Opcode::BCond,
            "header must still end in BCond when not converted"
        );
        // Smoking gun: no hoisted ADD must have leaked into the header.
        for &id in &header.insts {
            assert_ne!(
                func.inst(id).opcode,
                AArch64Opcode::AddRI,
                "hoisted ADD must NOT be speculated into the header when its def is live-out"
            );
        }
    }

    #[test]
    fn test_diamond_self_move_idiom_converts() {
        // DEFECT 2 (over-suppression) regression, NON-MASKING.
        //
        // The `x = cond ? f(...) : x` idiom: the false arm's final MOV is a
        // self-move `MOV v2, v2`, so csel_dst (v2) appears as both a "def" (the
        // final MOV) and a "use" (the self-move source). With the buggy
        // whole-body DEF set this falsely fired check (1)/(2) and refused. With
        // the DEF set computed over HOISTED insts only (csel_dst excluded), it
        // must CONVERT.
        //
        // true:  ADD v5, v3, #1 ; MOV v2, v5
        // false: MOV v2, v2                       (self-move = keep x)
        // -> hoist ADD v5, v3, #1 ; CSEL v2, v5, v2, EQ
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);
        let false_self = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(2)]);

        let mut func = make_diamond(
            cmp,
            CondCode::EQ,
            vec![true_add, true_mov],
            vec![false_self],
        );
        let mut pass = IfConversion;
        assert!(
            pass.run(&mut func),
            "x = cond ? f(...) : x self-move idiom must if-convert (no over-suppression)"
        );

        // Both arm blocks removed (header + join remain).
        assert_eq!(func.block_order.len(), 2);
        let header = func.block(BlockId(0));

        // Hoisted ADD must be present.
        assert!(
            header
                .insts
                .iter()
                .any(|&id| func.inst(id).opcode == AArch64Opcode::AddRI),
            "hoisted ADD must appear in the converted header"
        );

        // CSEL v2, v5, v2, EQ — sources are the true temp and the preserved x.
        let csel = header
            .insts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::Csel)
            .expect("expected a CSEL in the converted header");
        assert_eq!(csel.operands[0], vreg(2));
        assert_eq!(csel.operands[1], vreg(5));
        assert_eq!(csel.operands[2], vreg(2));
    }

    #[test]
    fn test_diamond_self_move_idiom_would_convert_proves_live_out_repro_distinct() {
        // Cross-check that the DEFECT 1 repro's refusal is caused specifically by
        // the live-out read, not by some unrelated rejection: remove the join
        // read and the otherwise-identical shape (true two-inst arm escaping a
        // temp that is arm-local) MUST convert. This makes the live-out test
        // non-masking — the only difference is the external read of v5.
        //
        // true:  ADD v5, v3, #1 ; MOV v2, v5      (v5 arm-local now)
        // false: MOV v2, v4
        // join:  RET                              (no read of v5)
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_add, true_mov], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(
            pass.run(&mut func),
            "same shape WITHOUT the join read must convert (proves the live-out test is non-masking)"
        );
        assert_eq!(func.block_order.len(), 2);
    }

    // ---- Triangle: CSEL formation ----

    #[test]
    fn test_triangle_csel_movr() {
        // bb0: CMP; B.EQ bb1; (fallthrough bb2)
        // bb1: MOV v2, v3; B bb2
        // bb2: RET
        // -> CSEL v2, v3, v2, EQ
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let then_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);

        let mut func = make_triangle(cmp, CondCode::EQ, then_mov);
        let mut pass = IfConversion;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 3); // CMP, CSEL, B

        let csel = func.inst(header.insts[1]);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(csel.operands[0], vreg(2)); // dst
        assert_eq!(csel.operands[1], vreg(3)); // then_src
        assert_eq!(csel.operands[2], vreg(2)); // identity (keep dst)
        assert_eq!(csel.operands[3], imm(CondCode::EQ.encoding() as i64));

        // Then block removed.
        assert!(!func.block_order.contains(&BlockId(1)));
    }

    #[test]
    fn test_triangle_movi_does_not_form_invalid_csel() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(5)]);
        let then_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(100)]);

        let mut func = make_triangle(cmp, CondCode::GT, then_mov);
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));

        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 2);
        assert_eq!(func.inst(header.insts[1]).opcode, AArch64Opcode::BCond);
        assert!(func.block_order.contains(&BlockId(1)));
    }

    // ---- Negative tests ----

    #[test]
    fn test_no_convert_different_destinations() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(5), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    #[test]
    fn test_no_convert_direct_provenance_leaves_map_unchanged() {
        // Different destinations are not a valid if-conversion candidate, so
        // there are no converted or removed control-flow instructions to record.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(5), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_mov]);
        let cmp_id = func.block(BlockId(0)).insts[0];
        let bcond_id = func.block(BlockId(0)).insts[1];
        let true_mov_id = func.block(BlockId(1)).insts[0];
        let true_br_id = func.block(BlockId(1)).insts[1];
        let false_mov_id = func.block(BlockId(2)).insts[0];
        let false_br_id = func.block(BlockId(2)).insts[1];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(110), &[cmp_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(111), &[bcond_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(112), &[true_mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(113), &[false_mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(114), &[true_br_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(115), &[false_br_id], PassId::new("isel"));

        let mut pass = IfConversion;
        assert!(!pass.run_with_provenance(&mut func, &mut provenance));

        assert_eq!(func.block_order.len(), 4);
        assert_eq!(func.inst(bcond_id).opcode, AArch64Opcode::BCond);
        for inst_id in [
            cmp_id,
            bcond_id,
            true_mov_id,
            true_br_id,
            false_mov_id,
            false_br_id,
        ] {
            let entry = provenance
                .get_entry(inst_id)
                .expect("no-op if-conversion should keep original provenance");
            assert!(entry.is_active());
            assert_eq!(entry.transforms.len(), 1);
        }
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(111)),
            Some(&[bcond_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(114)),
            Some(&[true_br_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(115)),
            Some(&[false_br_id][..])
        );
    }

    #[test]
    fn test_no_convert_memory_in_arm() {
        // False arm has a load -> not safe to speculate.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(4), imm(0)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_ldr]);
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_no_convert_call_in_arm() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_call = MachInst::new(AArch64Opcode::Bl, vec![]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_call]);
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_no_convert_too_many_insts() {
        // True arm has 3 instructions -> exceeds limit.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let t1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(1)]);
        let t2 = MachInst::new(AArch64Opcode::SubRI, vec![vreg(6), vreg(5), imm(2)]);
        let t3 = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(6)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![t1, t2, t3], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    #[test]
    fn test_no_convert_flag_setting_in_arm() {
        // True arm has a hoistable-looking ADDS before the final MOV. The MOV
        // shape would otherwise be eligible for multi-instruction conversion,
        // but ADDS writes NZCV and cannot be speculated.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(6), vreg(3), vreg(4)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(6)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);

        let mut func = make_diamond(
            cmp,
            CondCode::EQ,
            vec![true_adds, true_mov],
            vec![false_mov],
        );
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_no_convert_flag_reader_in_arm() {
        // True arm has a hoistable-looking CSET before the final MOV. The MOV
        // shape would otherwise be eligible for multi-instruction conversion,
        // but CSET reads NZCV and cannot be speculated.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_cset = MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(6), imm(CondCode::EQ.encoding() as i64)],
        );
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(6)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);

        let mut func = make_diamond(
            cmp,
            CondCode::EQ,
            vec![true_cset, true_mov],
            vec![false_mov],
        );
        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
    }

    // ---- Idempotency ----

    #[test]
    fn test_idempotent() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, vec![true_mov], vec![false_mov]);
        let mut pass = IfConversion;
        assert!(pass.run(&mut func));
        assert!(!pass.run(&mut func));
    }

    // ---- Edge cases ----

    #[test]
    fn test_no_change_empty_func() {
        let mut func = MachFunction::new("empty".to_string(), Signature::new(vec![], vec![]));
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(func.entry, ret_id);

        let mut pass = IfConversion;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_cfgcleanup_join_preds() {
        // After diamond conversion, join block should have correct preds.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::NE, vec![true_mov], vec![false_mov]);
        let mut pass = IfConversion;
        pass.run(&mut func);

        let join = func.block(BlockId(3));
        assert_eq!(join.preds.len(), 1);
        assert!(join.preds.contains(&BlockId(0)));
    }

    #[test]
    fn test_trap_null_if_zero_not_safe_to_speculate() {
        assert!(!is_safe_to_speculate(AArch64Opcode::TrapNullIfZero));
    }

    #[test]
    fn test_triangle_cfgcleanup() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let then_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);

        let mut func = make_triangle(cmp, CondCode::EQ, then_mov);
        let mut pass = IfConversion;
        pass.run(&mut func);

        // Join block (bb2) should only have header (bb0) as pred.
        let join = func.block(BlockId(2));
        assert_eq!(join.preds.len(), 1);
        assert!(join.preds.contains(&BlockId(0)));

        // Header should only have join as successor.
        let header = func.block(BlockId(0));
        assert_eq!(header.succs.len(), 1);
        assert_eq!(header.succs[0], BlockId(2));
    }

    // ---- Multiple conditions ----

    #[test]
    fn test_diamond_all_cond_codes() {
        // Verify the pass works with various condition codes.
        for &cc in &[
            CondCode::EQ,
            CondCode::NE,
            CondCode::LT,
            CondCode::GT,
            CondCode::LE,
            CondCode::GE,
        ] {
            let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
            let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
            let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

            let mut func = make_diamond(cmp, cc, vec![true_mov], vec![false_mov]);
            let mut pass = IfConversion;
            assert!(pass.run(&mut func), "should convert for {:?}", cc);

            let header = func.block(BlockId(0));
            let csel = func.inst(header.insts[1]);
            assert_eq!(csel.opcode, AArch64Opcode::Csel);
            assert_eq!(csel.operands[3], imm(cc.encoding() as i64));
        }
    }

    // -----------------------------------------------------------------------
    // Div-guard diamond collapse (HARDWARE-TOTAL div semantics)
    // -----------------------------------------------------------------------

    /// Build a div-guard diamond:
    ///   bb0: MOVZ vzero,#0; CMP vdivisor, vzero; B.cond -> bb1(true)
    ///   bb1 (true):  div_inst; B bb3
    ///   bb2 (false): else_inst; B bb3
    ///   bb3 (join):  RET
    /// `vzero` (vreg 9) is materialized to 0 so `reg_holds_zero` sees the def.
    fn make_div_diamond(
        div_inst: MachInst,
        else_inst: MachInst,
        cond: CondCode,
        divisor: MachOperand,
    ) -> MachFunction {
        let mut func = MachFunction::new(
            "test_div_diamond".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let movz = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![vreg(9), imm(0)]));
        func.append_inst(bb0, movz);
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![divisor, vreg(9)]));
        func.append_inst(bb0, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(cond.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond);

        let ti = func.push_inst(div_inst);
        func.append_inst(bb1, ti);
        let b1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, b1);

        let fi = func.push_inst(else_inst);
        func.append_inst(bb2, fi);
        let b2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, b2);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);
        func
    }

    /// FULL COLLAPSE: `select(b != 0, a/b, 0)` -> bare SDIV, no CSEL.
    /// true arm = SDIV dst,a,b ; false arm = MOV dst,zero ; cond = NE (b!=0).
    #[test]
    fn test_div_guard_full_collapse_sdiv() {
        // dst=vreg2, a=vreg3, b(divisor)=vreg4.
        let sdiv = MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(3), vreg(4)]);
        let mov0 = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(9)]); // dst = zero
        let mut func = make_div_diamond(sdiv, mov0, CondCode::NE, vreg(4));

        let mut pass = IfConversion;
        assert!(pass.run(&mut func), "div-guard diamond should collapse");

        // Header now holds a single bare SDIV writing the merge reg. NO Csel, and
        // the now-dead div-guard CMP is deleted.
        let header = func.block(BlockId(0));
        let sdiv_id = header
            .insts
            .iter()
            .find(|&&iid| func.inst(iid).opcode == AArch64Opcode::SDiv)
            .expect("header must contain the bare SDIV");
        let new = func.inst(*sdiv_id);
        assert_eq!(new.operands[0], vreg(2));
        assert_eq!(new.operands[1], vreg(3));
        assert_eq!(new.operands[2], vreg(4));
        for &bid in &func.block_order {
            for &iid in &func.block(bid).insts {
                assert_ne!(
                    func.inst(iid).opcode,
                    AArch64Opcode::Csel,
                    "full collapse must not emit a CSEL"
                );
                assert_ne!(
                    func.inst(iid).opcode,
                    AArch64Opcode::CmpRR,
                    "dead div-guard compare must be removed on full collapse"
                );
            }
        }
    }

    /// FULL COLLAPSE with the divisor in the FALSE arm and cond = EQ (b==0 picks
    /// the zero true-arm, so the div runs when b!=0).
    #[test]
    fn test_div_guard_full_collapse_div_in_false_arm() {
        let mov0 = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(9)]); // true arm: dst=0
        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(3), vreg(4)]); // false: div
        let mut func = make_div_diamond_swapped(mov0, udiv, CondCode::EQ, vreg(4));

        let mut pass = IfConversion;
        assert!(
            pass.run(&mut func),
            "swapped div-guard diamond should collapse"
        );
        let header = func.block(BlockId(0));
        let udiv_id = header
            .insts
            .iter()
            .find(|&&iid| func.inst(iid).opcode == AArch64Opcode::UDiv)
            .expect("header must contain the bare UDIV");
        assert_eq!(func.inst(*udiv_id).operands[2], vreg(4));
    }

    /// Like `make_div_diamond` but the caller supplies the true/false arm insts
    /// explicitly (used for the div-in-false-arm case).
    fn make_div_diamond_swapped(
        true_inst: MachInst,
        false_inst: MachInst,
        cond: CondCode,
        divisor: MachOperand,
    ) -> MachFunction {
        make_div_diamond_impl(true_inst, false_inst, cond, divisor)
    }

    fn make_div_diamond_impl(
        true_inst: MachInst,
        false_inst: MachInst,
        cond: CondCode,
        divisor: MachOperand,
    ) -> MachFunction {
        make_div_diamond(true_inst, false_inst, cond, divisor)
    }

    /// CSEL VARIANT: non-zero else value -> speculate div + CSEL (branchless,
    /// not a full collapse).
    #[test]
    fn test_div_guard_csel_variant_nonzero_else() {
        // true arm = SDIV dst,a,b ; false arm = MOV dst, vK (K != 0, vreg 5).
        let sdiv = MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(3), vreg(4)]);
        let mov_k = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);
        let mut func = make_div_diamond(sdiv, mov_k, CondCode::NE, vreg(4));

        let mut pass = IfConversion;
        assert!(pass.run(&mut func), "should form div + CSEL");
        let header = func.block(BlockId(0));
        // MOVZ, CMP, SDIV(speculated), CSEL, B.
        let div = func.inst(header.insts[2]);
        let csel = func.inst(header.insts[3]);
        assert_eq!(div.opcode, AArch64Opcode::SDiv);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(csel.operands[0], vreg(2)); // dst
        assert_eq!(csel.operands[1], vreg(2)); // on-true = speculated div result
        assert_eq!(csel.operands[2], vreg(5)); // on-false = K
        assert_eq!(csel.operands[3], imm(CondCode::NE.encoding() as i64));
    }

    /// A guard that does NOT test the divisor (tests a different reg) must NOT
    /// full-collapse — it may only take the (still-sound) CSEL path.
    #[test]
    fn test_div_guard_wrong_guard_reg_no_full_collapse() {
        // Guard compares vreg(7) (not the divisor vreg(4)) against zero.
        let sdiv = MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(3), vreg(4)]);
        let mov0 = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(9)]);
        let mut func = make_div_diamond(sdiv, mov0, CondCode::NE, vreg(7));

        let mut pass = IfConversion;
        assert!(pass.run(&mut func));
        // Because the guard tests the wrong reg, it must NOT be a bare SDIV;
        // instead a CSEL is emitted (sound, else value is zero-reg).
        let header = func.block(BlockId(0));
        let has_csel = header
            .insts
            .iter()
            .any(|&iid| func.inst(iid).opcode == AArch64Opcode::Csel);
        assert!(
            has_csel,
            "wrong-guard-reg diamond must fall back to CSEL, not bare div"
        );
    }

    /// Soundness: when the join reads the guard's flags BEFORE overwriting them,
    /// the div-guard compare is LIVE and must NOT be deleted (only the branch is
    /// converted). Builds a join whose first flag op is a reader (a second BCond).
    #[test]
    fn test_div_guard_full_collapse_keeps_live_compare() {
        // Reuse the standard collapse diamond, then splice a flag-reader as the
        // join's first instruction so `flags_dead_from_block(join)` is false.
        let sdiv = MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(3), vreg(4)]);
        let mov0 = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(9)]);
        let mut func = make_div_diamond(sdiv, mov0, CondCode::NE, vreg(4));
        // Prepend a flag-reader (BCond) to the join block (bb3) so incoming flags
        // are live at join entry.
        let live_reader = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(CondCode::EQ.encoding() as i64),
                MachOperand::Block(BlockId(3)),
            ],
        ));
        func.block_mut(BlockId(3)).insts.insert(0, live_reader);

        let mut pass = IfConversion;
        assert!(pass.run(&mut func), "diamond still collapses");
        // The guard compare must be RETAINED (flags live at join entry).
        let kept = func
            .block_order
            .iter()
            .flat_map(|&b| func.block(b).insts.iter())
            .any(|&iid| func.inst(iid).opcode == AArch64Opcode::CmpRR);
        assert!(
            kept,
            "compare must be kept when its flags are live downstream"
        );
    }

    /// The env-var token parser (pure — no global state, no race).
    #[test]
    fn test_div_collapse_disable_token_parsing() {
        assert!(div_collapse_disabled_by("ifconv_div"));
        assert!(div_collapse_disabled_by("dce, ifconv_div , cse"));
        assert!(div_collapse_disabled_by("ifconv,ifconv_div"));
        assert!(!div_collapse_disabled_by(""));
        assert!(!div_collapse_disabled_by("ifconv"));
        assert!(!div_collapse_disabled_by("cse,dce"));
    }

    /// Kill switch: disabling the collapse (via the per-thread test override,
    /// which the production path keys off `TRUST_CG_DISABLE_PASSES=ifconv_div`)
    /// leaves the div-guard diamond branchy.
    #[test]
    fn test_div_guard_kill_switch() {
        let sdiv = MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(3), vreg(4)]);
        let mov0 = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(9)]);
        let mut func = make_div_diamond(sdiv, mov0, CondCode::NE, vreg(4));

        // Per-thread override: no process-global env mutation, so no race with
        // parallel tests. The pass runs synchronously on this same thread.
        TEST_DIV_COLLAPSE_DISABLED.with(|c| c.set(true));
        let mut pass = IfConversion;
        let changed = pass.run(&mut func);
        TEST_DIV_COLLAPSE_DISABLED.with(|c| c.set(false));

        assert!(
            !changed,
            "kill switch must leave the div-guard diamond branchy"
        );
        let header = func.block(BlockId(0));
        assert!(
            header
                .insts
                .iter()
                .all(|&iid| func.inst(iid).opcode != AArch64Opcode::SDiv),
            "kill switch must not hoist the div"
        );
    }

    // =====================================================================
    // Loop-diamond if-conversion (branchless self-recurrent CSEL)
    // =====================================================================

    fn app(func: &mut MachFunction, bb: BlockId, inst: MachInst) {
        let id = func.push_inst(inst);
        func.append_inst(bb, id);
    }

    /// Build a loop-resident diamond. The diamond header is `bb1` (also the loop
    /// header); `bb4` is the latch with the loop back-edge `bb4 -> bb1`:
    ///
    ///   bb0 (preheader): MovR c, init ; Movz one, #1 ; B bb1
    ///   bb1 (diamond hdr): AndRR r, c, one ; CmpRI r, #0 ; BCond EQ -> bb2 ; B bb3
    ///   bb2 (true arm):  <true_insts> ; B bb4
    ///   bb3 (false arm): <false_insts> ; B bb4
    ///   bb4 (latch):     <carry_insts> ; CmpRI c, #1 ; BCond NE -> bb1 ; B bb5
    ///   bb5 (exit):      Ret
    ///
    /// `c = vreg(10)`, `one = vreg(11)`, `r = vreg(12)`. `carry_insts` decide
    /// whether the loop-carried `c` is a self-recurrence (`c = <merge>`) or a
    /// monotone induction variable (`c = c + 1`).
    fn make_loop_diamond(
        true_insts: Vec<MachInst>,
        false_insts: Vec<MachInst>,
        carry_insts: Vec<MachInst>,
    ) -> MachFunction {
        let mut func =
            MachFunction::new("loop_diamond".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let bb5 = func.create_block();

        let c = vreg(10);
        let one = vreg(11);
        let r = vreg(12);
        let init = vreg(30);

        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::MovR, vec![c.clone(), init]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![one.clone(), imm(1)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );

        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::AndRR, vec![r.clone(), c.clone(), one]),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::CmpRI, vec![r, imm(0)]),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb2)],
            ),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );

        for inst in true_insts {
            app(&mut func, bb2, inst);
        }
        app(
            &mut func,
            bb2,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb4)]),
        );

        for inst in false_insts {
            app(&mut func, bb3, inst);
        }
        app(
            &mut func,
            bb3,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb4)]),
        );

        for inst in carry_insts {
            app(&mut func, bb4, inst);
        }
        app(
            &mut func,
            bb4,
            MachInst::new(AArch64Opcode::CmpRI, vec![c, imm(1)]),
        );
        app(
            &mut func,
            bb4,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb1)],
            ),
        );
        app(
            &mut func,
            bb4,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb5)]),
        );

        app(&mut func, bb5, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb4);
        func.add_edge(bb3, bb4);
        func.add_edge(bb4, bb1);
        func.add_edge(bb4, bb5);
        func
    }

    /// Collatz-shaped self-recurrent arms: even = `c >> 1`, odd = `c + 1`, both
    /// written into the merge register `vreg(20)`; the latch feeds the merge back
    /// into `c` (`c = merge`).
    fn self_recurrent_bodies() -> (Vec<MachInst>, Vec<MachInst>, Vec<MachInst>) {
        let c = vreg(10);
        let merge = vreg(20);
        let t_even = vreg(21);
        let t_odd = vreg(22);
        let true_insts = vec![
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![t_even.clone(), c.clone(), imm(1)],
            ),
            MachInst::new(AArch64Opcode::MovR, vec![merge.clone(), t_even]),
        ];
        let false_insts = vec![
            MachInst::new(AArch64Opcode::AddRI, vec![t_odd.clone(), c.clone(), imm(1)]),
            MachInst::new(AArch64Opcode::MovR, vec![merge.clone(), t_odd]),
        ];
        // Self-recurrence: the loop-carried c becomes the diamond's merged value.
        let carry = vec![MachInst::new(AArch64Opcode::MovR, vec![c, merge])];
        (true_insts, false_insts, carry)
    }

    fn run_ifconv(func: &mut MachFunction) -> bool {
        let mut pass = IfConversion;
        let mut analyses = AnalysisCache::new();
        let mut provenance = ProvenanceMap::new();
        pass.run_with_analyses_and_provenance(func, &mut analyses, &mut provenance)
    }

    fn block_has_csel(func: &MachFunction, bb: BlockId) -> bool {
        func.block(bb)
            .insts
            .iter()
            .any(|&iid| func.inst(iid).opcode == AArch64Opcode::Csel)
    }

    #[test]
    fn test_loop_diamond_self_recurrent_converts_to_csel() {
        let (t, f, carry) = self_recurrent_bodies();
        let mut func = make_loop_diamond(t, f, carry);
        assert!(
            run_ifconv(&mut func),
            "self-recurrent loop diamond must convert"
        );

        // The diamond header (bb1) now holds a CSEL; both arm blocks are gone.
        assert!(
            block_has_csel(&func, BlockId(1)),
            "header should hold the merged CSEL"
        );
        assert!(
            !func.block_order.contains(&BlockId(2)),
            "true arm block removed"
        );
        assert!(
            !func.block_order.contains(&BlockId(3)),
            "false arm block removed"
        );

        // The CSEL selects between the two arm values on the EQ condition, and
        // both hoisted producers (LsrRI, AddRI) now live unconditionally.
        let hdr = func.block(BlockId(1));
        let csel = hdr
            .insts
            .iter()
            .map(|&i| func.inst(i))
            .find(|i| i.opcode == AArch64Opcode::Csel)
            .unwrap();
        assert_eq!(csel.operands[0], vreg(20), "CSEL writes the merge register");
        assert_eq!(csel.operands[3], imm(CondCode::EQ.encoding() as i64));
        let has = |op| hdr.insts.iter().any(|&i| func.inst(i).opcode == op);
        assert!(has(AArch64Opcode::LsrRI), "even producer hoisted");
        assert!(has(AArch64Opcode::AddRI), "odd producer hoisted");
    }

    #[test]
    fn test_loop_diamond_monotone_iv_condition_stays_branchy() {
        // Structurally identical to collatz EXCEPT the loop-carried c is a
        // monotone induction variable (c = c + 1) that the diamond's own merged
        // value never feeds — a well-predicted parity branch a CSEL would
        // regress. Must NOT convert.
        let (t, f, _) = self_recurrent_bodies();
        let c = vreg(10);
        let iv_next = vreg(50);
        let carry = vec![
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![iv_next.clone(), c.clone(), imm(1)],
            ),
            MachInst::new(AArch64Opcode::MovR, vec![c, iv_next]),
        ];
        let mut func = make_loop_diamond(t, f, carry);
        assert!(
            !run_ifconv(&mut func),
            "monotone-IV parity diamond must stay branchy"
        );
        assert!(!block_has_csel(&func, BlockId(1)));
        assert!(
            func.block_order.contains(&BlockId(2)),
            "arm blocks preserved"
        );
    }

    #[test]
    fn test_loop_diamond_load_arm_stays_branchy_trap_adversary() {
        // Self-recurrent shape, but the true arm speculatively loads memory — an
        // unsafe-to-speculate op. is_safe_to_speculate rejects it before the
        // profitability gate, so the branch MUST be kept (a load past its guard
        // could fault).
        let c = vreg(10);
        let merge = vreg(20);
        let t_ld = vreg(21);
        let t_odd = vreg(22);
        let true_insts = vec![
            MachInst::new(AArch64Opcode::LdrRI, vec![t_ld.clone(), c.clone(), imm(0)]),
            MachInst::new(AArch64Opcode::MovR, vec![merge.clone(), t_ld]),
        ];
        let false_insts = vec![
            MachInst::new(AArch64Opcode::AddRI, vec![t_odd.clone(), c.clone(), imm(1)]),
            MachInst::new(AArch64Opcode::MovR, vec![merge.clone(), t_odd]),
        ];
        let carry = vec![MachInst::new(AArch64Opcode::MovR, vec![c, merge])];
        let mut func = make_loop_diamond(true_insts, false_insts, carry);
        assert!(!run_ifconv(&mut func), "a load arm must keep the branch");
        assert!(!block_has_csel(&func, BlockId(1)));
    }

    #[test]
    fn test_loop_diamond_kill_switch_stays_branchy() {
        let (t, f, carry) = self_recurrent_bodies();
        let mut func = make_loop_diamond(t, f, carry);
        TEST_LOOP_IFCONV_DISABLED.with(|c| c.set(true));
        let changed = run_ifconv(&mut func);
        TEST_LOOP_IFCONV_DISABLED.with(|c| c.set(false));
        assert!(
            !changed,
            "ifconv_loop kill switch must leave the diamond branchy"
        );
        assert!(!block_has_csel(&func, BlockId(1)));
        assert!(func.block_order.contains(&BlockId(2)));
    }

    #[test]
    fn test_non_loop_explicit_diamond_still_bounded() {
        // A non-loop diamond in the explicit two-edge header form (BCond T; B F)
        // is still bounded out by the blast-radius gate — the widening only
        // admits loop-resident self-recurrences, never a plain acyclic diamond.
        let mut func = MachFunction::new("acyclic".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb1)],
            ),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );
        app(
            &mut func,
            bb2,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]),
        );
        app(
            &mut func,
            bb2,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );
        app(&mut func, bb3, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        assert!(
            !run_ifconv(&mut func),
            "acyclic explicit-form diamond must stay bounded"
        );
        assert!(!block_has_csel(&func, BlockId(0)));
    }

    /// The env-var token parser (pure — no global state, no race).
    #[test]
    fn test_loop_ifconv_disable_token_parsing() {
        assert!(loop_ifconv_disabled_by("ifconv_loop"));
        assert!(loop_ifconv_disabled_by("dce, ifconv_loop , cse"));
        assert!(loop_ifconv_disabled_by("ifconv,ifconv_loop"));
        assert!(!loop_ifconv_disabled_by(""));
        assert!(!loop_ifconv_disabled_by("ifconv"));
        assert!(!loop_ifconv_disabled_by("ifconv_div"));
    }

    // -----------------------------------------------------------------------
    // CSEL -> CSINC increment fold
    // -----------------------------------------------------------------------

    fn run_csinc(func: &mut MachFunction) -> bool {
        let mut pass = CsincFold;
        let mut analyses = AnalysisCache::new();
        let mut provenance = ProvenanceMap::new();
        pass.run_with_analyses_and_provenance(func, &mut analyses, &mut provenance)
    }

    fn single_block_func() -> (MachFunction, BlockId) {
        let func = MachFunction::new("csinc_test".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        (func, bb0)
    }

    fn only_inst_with(func: &MachFunction, bb: BlockId, opc: AArch64Opcode) -> Option<MachInst> {
        func.block(bb)
            .insts
            .iter()
            .map(|&i| func.inst(i).clone())
            .find(|i| i.opcode == opc)
    }

    fn has_op(func: &MachFunction, bb: BlockId, opc: AArch64Opcode) -> bool {
        func.block(bb)
            .insts
            .iter()
            .any(|&i| func.inst(i).opcode == opc)
    }

    /// FALSE-arm fold: `Csel dst, T, (t+1), EQ` (AddRI) -> `Csinc dst, T, t, EQ`.
    /// Pins the exact operand order and polarity (a wrong CSINC is a miscompile).
    #[test]
    fn test_csinc_fold_false_arm_addri() {
        let (mut func, bb0) = single_block_func();
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(20), vreg(10), imm(1)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Csel,
                vec![
                    vreg(30),
                    vreg(11),
                    vreg(20),
                    imm(CondCode::EQ.encoding() as i64),
                ],
            ),
        );
        app(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        assert!(run_csinc(&mut func), "false-arm t+1 must fold to CSINC");
        assert!(!has_op(&func, bb0, AArch64Opcode::AddRI), "add deleted");
        assert!(!has_op(&func, bb0, AArch64Opcode::Csel), "csel rewritten");
        let csinc = only_inst_with(&func, bb0, AArch64Opcode::Csinc).unwrap();
        // Csinc dst, Xn=T(v11), Xm=base(v10), EQ  ==  EQ ? v11 : v10+1.
        assert_eq!(csinc.operands[0], vreg(30));
        assert_eq!(csinc.operands[1], vreg(11));
        assert_eq!(csinc.operands[2], vreg(10));
        assert_eq!(csinc.operands[3], imm(CondCode::EQ.encoding() as i64));
    }

    /// FALSE-arm fold via `AddRR t, one` with `one` a proven `Movz #1`.
    #[test]
    fn test_csinc_fold_false_arm_addrr_const_one() {
        let (mut func, bb0) = single_block_func();
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![vreg(12), imm(1)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(20), vreg(10), vreg(12)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Csel,
                vec![
                    vreg(30),
                    vreg(11),
                    vreg(20),
                    imm(CondCode::EQ.encoding() as i64),
                ],
            ),
        );
        app(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        assert!(run_csinc(&mut func), "AddRR-by-const-1 must fold");
        let csinc = only_inst_with(&func, bb0, AArch64Opcode::Csinc).unwrap();
        assert_eq!(csinc.operands[1], vreg(11));
        assert_eq!(csinc.operands[2], vreg(10), "base is the non-1 operand");
        assert_eq!(csinc.operands[3], imm(CondCode::EQ.encoding() as i64));
    }

    /// TRUE-arm fold: `Csel dst, (t+1), F, EQ` -> `Csinc dst, F, t, NE` (inverted).
    #[test]
    fn test_csinc_fold_true_arm_inverts_condition() {
        let (mut func, bb0) = single_block_func();
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(20), vreg(10), imm(1)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Csel,
                vec![
                    vreg(30),
                    vreg(20),
                    vreg(11),
                    imm(CondCode::EQ.encoding() as i64),
                ],
            ),
        );
        app(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        assert!(
            run_csinc(&mut func),
            "true-arm t+1 must fold with inverted cc"
        );
        let csinc = only_inst_with(&func, bb0, AArch64Opcode::Csinc).unwrap();
        // Csinc dst, Xn=F(v11), Xm=base(v10), NE  ==  NE ? v11 : v10+1 == EQ ? v10+1 : v11.
        assert_eq!(csinc.operands[1], vreg(11));
        assert_eq!(csinc.operands[2], vreg(10));
        assert_eq!(csinc.operands[3], imm(CondCode::NE.encoding() as i64));
    }

    /// A multi-use `+1` producer must NOT fold (deleting it would strand a read).
    #[test]
    fn test_csinc_fold_multi_use_add_bails() {
        let (mut func, bb0) = single_block_func();
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(20), vreg(10), imm(1)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Csel,
                vec![
                    vreg(30),
                    vreg(11),
                    vreg(20),
                    imm(CondCode::EQ.encoding() as i64),
                ],
            ),
        );
        // Second reader of v20 defeats the single-use requirement.
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(31), vreg(20), vreg(11)]),
        );
        app(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        assert!(!run_csinc(&mut func), "multi-use add must not fold");
        assert!(has_op(&func, bb0, AArch64Opcode::Csel));
        assert!(has_op(&func, bb0, AArch64Opcode::AddRI));
    }

    /// `AddRR t, k` with `k != 1` must NOT fold (not an increment).
    #[test]
    fn test_csinc_fold_addrr_non_one_bails() {
        let (mut func, bb0) = single_block_func();
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![vreg(12), imm(2)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(20), vreg(10), vreg(12)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Csel,
                vec![
                    vreg(30),
                    vreg(11),
                    vreg(20),
                    imm(CondCode::EQ.encoding() as i64),
                ],
            ),
        );
        app(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        assert!(!run_csinc(&mut func), "add-by-2 is not an increment");
        assert!(has_op(&func, bb0, AArch64Opcode::Csel));
    }

    /// Redefining the base between the add and the CSEL must BAIL — the CSINC
    /// recomputes `base + 1` at the CSEL site, which would differ.
    #[test]
    fn test_csinc_fold_base_redefined_between_bails() {
        let (mut func, bb0) = single_block_func();
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(20), vreg(10), imm(1)]),
        );
        // Redefine the base v10 AFTER the add, BEFORE the csel.
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(5)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Csel,
                vec![
                    vreg(30),
                    vreg(11),
                    vreg(20),
                    imm(CondCode::EQ.encoding() as i64),
                ],
            ),
        );
        app(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        assert!(
            !run_csinc(&mut func),
            "base redefined between add and csel must not fold"
        );
        assert!(has_op(&func, bb0, AArch64Opcode::Csel));
    }

    /// The kill switch leaves the CSEL intact.
    #[test]
    fn test_csinc_fold_kill_switch() {
        let (mut func, bb0) = single_block_func();
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(20), vreg(10), imm(1)]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Csel,
                vec![
                    vreg(30),
                    vreg(11),
                    vreg(20),
                    imm(CondCode::EQ.encoding() as i64),
                ],
            ),
        );
        app(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        TEST_CSINC_FOLD_DISABLED.with(|c| c.set(true));
        let changed = run_csinc(&mut func);
        TEST_CSINC_FOLD_DISABLED.with(|c| c.set(false));
        assert!(!changed, "kill switch disables the fold");
        assert!(has_op(&func, bb0, AArch64Opcode::Csel));
    }

    #[test]
    fn test_csinc_fold_disable_token_parsing() {
        assert!(csinc_fold_disabled_by("csincfold"));
        assert!(csinc_fold_disabled_by("dce, csincfold , cse"));
        assert!(!csinc_fold_disabled_by(""));
        assert!(!csinc_fold_disabled_by("ifconv"));
        assert!(!csinc_fold_disabled_by("csinc"));
    }

    // -----------------------------------------------------------------------
    // Late tiny-loop-diamond if-conversion
    // -----------------------------------------------------------------------

    fn run_tinyloop(func: &mut MachFunction) -> bool {
        let mut pass = TinyLoopDiamondConvert;
        let mut analyses = AnalysisCache::new();
        let mut provenance = ProvenanceMap::new();
        pass.run_with_analyses_and_provenance(func, &mut analyses, &mut provenance)
    }

    /// Build a b1-shaped loop: the diamond condition is derived from a state
    /// register mixed by `mix_op` (EOR = non-affine; ADD = affine control), which
    /// is loop-carried across the back-edge. One arm rotates `acc` (tiny pure),
    /// the other is the identity. `mix_is_eor` picks EOR vs affine ADD mixing.
    ///
    ///   bb0: MovR s=init; MovR acc=init2; B bb1
    ///   bb1(header): LslRI tmp=s<<3; <mix> s2 = s ^/+  tmp; AndRI cnd=s2&6;
    ///                CmpRI cnd,2; BCond EQ->bb2; B bb3
    ///   bb2(true):  RorRI rr=acc ror57; MovR merge=rr; B bb4
    ///   bb3(false): MovR merge=acc; B bb4
    ///   bb4(latch): MovR acc=merge; MovR s=s2; CmpRI s2,0; BCond NE->bb1; B bb5
    ///   bb5: Ret
    fn make_tiny_loop(mix_is_eor: bool) -> MachFunction {
        let mut func = MachFunction::new("tiny_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let bb5 = func.create_block();

        let s = vreg(10);
        let acc = vreg(11);
        let tmp = vreg(12);
        let s2 = vreg(13);
        let cnd = vreg(14);
        let rr = vreg(15);
        let merge = vreg(16);
        let init = vreg(30);
        let init2 = vreg(31);

        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::MovR, vec![s.clone(), init]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::MovR, vec![acc.clone(), init2]),
        );
        app(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );

        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::LslRI, vec![tmp.clone(), s.clone(), imm(3)]),
        );
        let mix = if mix_is_eor {
            AArch64Opcode::EorRR
        } else {
            AArch64Opcode::AddRR
        };
        app(
            &mut func,
            bb1,
            MachInst::new(mix, vec![s2.clone(), s.clone(), tmp]),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::AndRI, vec![cnd.clone(), s2.clone(), imm(6)]),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::CmpRI, vec![cnd, imm(2)]),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb2)],
            ),
        );
        app(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );

        app(
            &mut func,
            bb2,
            MachInst::new(AArch64Opcode::RorRI, vec![rr.clone(), acc.clone(), imm(57)]),
        );
        app(
            &mut func,
            bb2,
            MachInst::new(AArch64Opcode::MovR, vec![merge.clone(), rr]),
        );
        app(
            &mut func,
            bb2,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb4)]),
        );

        app(
            &mut func,
            bb3,
            MachInst::new(AArch64Opcode::MovR, vec![merge.clone(), acc.clone()]),
        );
        app(
            &mut func,
            bb3,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb4)]),
        );

        app(
            &mut func,
            bb4,
            MachInst::new(AArch64Opcode::MovR, vec![acc, merge]),
        );
        app(
            &mut func,
            bb4,
            MachInst::new(AArch64Opcode::MovR, vec![s, s2.clone()]),
        );
        app(
            &mut func,
            bb4,
            MachInst::new(AArch64Opcode::CmpRI, vec![s2, imm(0)]),
        );
        app(
            &mut func,
            bb4,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb1)],
            ),
        );
        app(
            &mut func,
            bb4,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb5)]),
        );

        app(&mut func, bb5, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb4);
        func.add_edge(bb3, bb4);
        func.add_edge(bb4, bb1);
        func.add_edge(bb4, bb5);
        func
    }

    /// The EOR (non-affine) self-recurrence condition converts the tiny rotate
    /// diamond to a CSEL; the arm blocks are removed and the header holds the
    /// hoisted RorRI + CSEL.
    #[test]
    fn test_tiny_loop_eor_recurrence_converts() {
        let mut func = make_tiny_loop(true);
        assert!(
            run_tinyloop(&mut func),
            "EOR-recurrence tiny diamond must convert"
        );
        assert!(block_has_csel(&func, BlockId(1)), "header holds the CSEL");
        assert!(
            func.block(BlockId(1))
                .insts
                .iter()
                .any(|&i| func.inst(i).opcode == AArch64Opcode::RorRI),
            "the rotate is hoisted into the header"
        );
        assert!(!func.block_order.contains(&BlockId(2)), "true arm removed");
        assert!(!func.block_order.contains(&BlockId(3)), "false arm removed");
        // CSEL selects rotate (v15) vs acc (v11) on EQ, writing merge (v16).
        let hdr = func.block(BlockId(1));
        let csel = hdr
            .insts
            .iter()
            .map(|&i| func.inst(i))
            .find(|i| i.opcode == AArch64Opcode::Csel)
            .unwrap();
        assert_eq!(csel.operands[0], vreg(16), "CSEL writes merge");
        assert_eq!(
            csel.operands[1],
            vreg(15),
            "true value is the rotate result"
        );
        assert_eq!(csel.operands[2], vreg(11), "false value is acc (identity)");
        assert_eq!(csel.operands[3], imm(CondCode::EQ.encoding() as i64));
    }

    /// An AFFINE (ADD) self-recurrence condition is PREDICTABLE — must stay
    /// branchy (the load-bearing non-affine requirement).
    #[test]
    fn test_tiny_loop_affine_recurrence_stays_branchy() {
        let mut func = make_tiny_loop(false);
        assert!(
            !run_tinyloop(&mut func),
            "affine-IV condition must not convert"
        );
        assert!(!block_has_csel(&func, BlockId(1)));
        assert!(func.block_order.contains(&BlockId(2)), "arms preserved");
    }

    /// The kill switch leaves the tiny diamond branchy.
    #[test]
    fn test_tiny_loop_kill_switch() {
        let mut func = make_tiny_loop(true);
        TEST_TINY_LOOP_DISABLED.with(|c| c.set(true));
        let changed = run_tinyloop(&mut func);
        TEST_TINY_LOOP_DISABLED.with(|c| c.set(false));
        assert!(!changed, "kill switch keeps the diamond branchy");
        assert!(!block_has_csel(&func, BlockId(1)));
    }

    #[test]
    fn test_tiny_loop_disable_token_parsing() {
        assert!(tiny_loop_disabled_by("tinyloop"));
        assert!(tiny_loop_disabled_by("dce, tinyloop , cse"));
        assert!(!tiny_loop_disabled_by(""));
        assert!(!tiny_loop_disabled_by("ifconv"));
    }
}
