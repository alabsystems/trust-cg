// trust-cg-opt - AArch64 Select/Flag Fusion
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 select/flag fusion pass.
//!
//! The isel lowers `select(icmp)` by materializing the boolean and
//! re-testing it per select:
//!
//! ```text
//! CMP   a, b            ; flag source F
//! CSET  xb, cc          ; xb := (cc holds in F)
//! ...                   ; select-arm computation (no NZCV writes)
//! CMP   xb, #0
//! CSEL  d, t, f, NE     ; d := (xb != 0) ? t : f
//! ```
//!
//! This pass deletes the re-test and retargets the CSEL onto the original
//! condition — the `CMP; CSEL cc` shape clang emits:
//!
//! ```text
//! CMP   a, b
//! ...
//! CSEL  d, t, f, cc
//! ```
//!
//! When every use of the boolean was one of the deleted re-tests, the CSET
//! is deleted too.
//!
//! # Soundness
//!
//! The rewrite relies on one invariant: **`xb != 0` holds iff `cc` holds
//! in the NZCV state the CSET observed**, which is the definition of CSET.
//! Retargeting `CSEL ..., NE` (over `CMP xb, #0` flags) to `CSEL ..., cc`
//! (over the CSET-observed flags) is therefore exact — PROVIDED the NZCV
//! state at the CSEL still equals the state the CSET observed. The scan
//! enforces this transactionally, per CSET, within a single block:
//!
//! - A fused `CMP xb, #0` must be immediately followed by the CSELs that
//!   consume it (condition NE or EQ; EQ fuses to the inverted condition).
//! - Any OTHER flag-writing instruction ends the scan (`commit`): flags
//!   are re-established, everything downstream is unaffected.
//! - Any flag-READING instruction encountered after a planned deletion
//!   ABORTS the whole plan (it would observe changed flags) — fail-closed.
//!   Flag readers seen before any deletion are unaffected and benign.
//! - A redefinition of the boolean register stops further matching (later
//!   re-tests test the NEW value).
//! - Flags are never live across block boundaries in this backend (the
//!   same-block discipline every fusion pass relies on: isel emits the
//!   flag setter immediately before each consumer; cmp-branch-fusion and
//!   cmp-select both assume it), so reaching the end of the block commits.
//!
//! This pass runs LATE — after the NEON vectorizers, whose recognizers
//! decode the materialized CSET shape (they also accept the direct
//! `CmpRR; Csel(cc)` shape, but running late means their input is
//! byte-for-byte what they were built against).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, CondCode, InstId, MachFunction, MachOperand, PassId, ProvenanceMap, VReg,
};

use crate::effects::{aarch64_def_operand_positions, aarch64_use_operand_positions, writes_flags};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// AArch64 select/flag fusion pass.
pub struct SelectFlagFuse;

impl MachinePass for SelectFlagFuse {
    fn name(&self) -> &str {
        "select-fuse"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_select_fuse(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_select_fuse(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }
}

/// One fused re-test: the deleted `CMP xb, #0` and the CSELs retargeted
/// onto the CSET's condition.
struct FuseGroup {
    cmp_zero_id: InstId,
    /// (csel inst id, new condition encoding)
    rewrites: Vec<(InstId, i64)>,
}

/// The committed plan for one CSET.
struct CsetPlan {
    cset_id: InstId,
    bool_vreg: VReg,
    groups: Vec<FuseGroup>,
}

fn run_select_fuse(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    let use_counts = count_vreg_uses(func);
    let mut plans: Vec<CsetPlan> = Vec::new();

    for block_id in func.block_order.clone() {
        let insts = func.block(block_id).insts.clone();
        for (position, &inst_id) in insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::CSet || inst.operands.len() != 2 {
                continue;
            }
            let Some(bool_vreg) = inst.operands[0].as_vreg() else {
                continue;
            };
            let Some(cset_cond) = inst.operands[1].as_imm().and_then(decode_cond) else {
                continue;
            };
            if let Some(groups) = scan_from_cset(func, &insts, position, bool_vreg, cset_cond)
                && !groups.is_empty()
            {
                plans.push(CsetPlan {
                    cset_id: inst_id,
                    bool_vreg,
                    groups,
                });
            }
        }
    }

    if plans.is_empty() {
        return false;
    }

    let mut to_delete: HashSet<InstId> = HashSet::new();
    let mut changed = false;

    for plan in &plans {
        let mut deleted_uses = 0u32;
        for group in &plan.groups {
            to_delete.insert(group.cmp_zero_id);
            deleted_uses += 1;
            for &(csel_id, new_cc) in &group.rewrites {
                let csel = func.inst_mut(csel_id);
                csel.operands[3] = MachOperand::Imm(new_cc);
            }
        }
        changed = true;

        // Delete the CSET when every use of the boolean was a deleted
        // re-test.
        let total_uses = use_counts.get(&plan.bool_vreg).copied().unwrap_or(0);
        if total_uses == deleted_uses {
            to_delete.insert(plan.cset_id);
        }

        if let Some(provenance) = provenance.as_deref_mut() {
            let pass = PassId::new("select-fuse");
            for group in &plan.groups {
                let first_csel = group.rewrites[0].0;
                provenance.record_merge(&[group.cmp_zero_id, first_csel], first_csel, pass.clone());
                for &(csel_id, _) in group.rewrites.iter().skip(1) {
                    provenance.record_in_place_transform(csel_id, pass.clone());
                }
            }
            if to_delete.contains(&plan.cset_id) {
                provenance.record_deletion(
                    plan.cset_id,
                    pass,
                    "boolean materialization consumed by select-flag fusion",
                );
            }
        }
    }

    if !to_delete.is_empty() {
        for block_id in func.block_order.clone() {
            let block = func.block_mut(block_id);
            block.insts.retain(|id| !to_delete.contains(id));
        }
    }

    changed
}

/// Scan forward from the CSET at `insts[cset_pos]`, building the fuse plan.
///
/// Returns `None` on abort (fail-closed: no changes for this CSET), or the
/// (possibly empty) list of committed fuse groups.
fn scan_from_cset(
    func: &MachFunction,
    insts: &[InstId],
    cset_pos: usize,
    bool_vreg: VReg,
    cset_cond: CondCode,
) -> Option<Vec<FuseGroup>> {
    let mut groups: Vec<FuseGroup> = Vec::new();
    let mut matching = true;
    let mut j = cset_pos + 1;

    while j < insts.len() {
        let inst_id = insts[j];
        let inst = func.inst(inst_id);

        // Fusable re-test: CMP bool, #0 immediately followed by >=1 CSELs
        // whose condition is NE or EQ.
        if matching && is_cmp_zero_of(inst, bool_vreg) {
            let mut rewrites: Vec<(InstId, i64)> = Vec::new();
            let mut k = j + 1;
            let mut redefines_bool = false;
            while k < insts.len() {
                let csel = func.inst(insts[k]);
                if csel.opcode != AArch64Opcode::Csel || csel.operands.len() != 4 {
                    break;
                }
                let Some(csel_cond) = csel.operands[3].as_imm().and_then(decode_cond) else {
                    break;
                };
                let new_cc = match csel_cond {
                    CondCode::NE => cset_cond,
                    CondCode::EQ => invert_cond(cset_cond)?,
                    _ => break,
                };
                rewrites.push((insts[k], new_cc.encoding() as i64));
                if csel
                    .operands
                    .first()
                    .and_then(|op| op.as_vreg())
                    .is_some_and(|dst| dst == bool_vreg)
                {
                    redefines_bool = true;
                }
                k += 1;
            }
            if !rewrites.is_empty() {
                groups.push(FuseGroup {
                    cmp_zero_id: inst_id,
                    rewrites,
                });
                if redefines_bool {
                    matching = false;
                }
                j = k;
                continue;
            }
            // No consumable CSEL run: fall through — the untouched CMP is a
            // real flag writer.
        }

        // Any real flag writer re-establishes NZCV: everything downstream
        // is unaffected by our deletions. Commit.
        if writes_flags(inst.opcode) {
            return Some(groups);
        }

        // Flag readers after a planned deletion would observe changed
        // flags — abort the whole plan (fail-closed). Readers before any
        // deletion are unaffected.
        if reads_nzcv(inst.opcode) && !groups.is_empty() {
            return None;
        }

        // A redefinition of the boolean stops further re-test matching
        // (later CMP bool, #0 test the NEW value).
        if matching && defines_vreg(func, inst_id, bool_vreg) {
            matching = false;
        }

        j += 1;
    }

    // End of block: flags are not live across block boundaries in this
    // backend (same-block flag discipline). Commit.
    Some(groups)
}

fn is_cmp_zero_of(inst: &trust_cg_ir::MachInst, bool_vreg: VReg) -> bool {
    inst.opcode == AArch64Opcode::CmpRI
        && inst.operands.len() == 2
        && inst.operands[0].as_vreg() == Some(bool_vreg)
        && inst.operands[1].as_imm() == Some(0)
}

/// True if the opcode reads the NZCV flags (conditional ops, carry ops,
/// and conditional branches).
fn reads_nzcv(opcode: AArch64Opcode) -> bool {
    crate::effects::reads_flags(opcode) || opcode == AArch64Opcode::BCond
}

fn defines_vreg(func: &MachFunction, inst_id: InstId, vreg: VReg) -> bool {
    let inst = func.inst(inst_id);
    aarch64_def_operand_positions(inst.opcode, inst.operands.len())
        .into_iter()
        .any(|idx| inst.operands.get(idx).and_then(|op| op.as_vreg()) == Some(vreg))
}

fn count_vreg_uses(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            for idx in aarch64_use_operand_positions(inst.opcode, inst.operands.len()) {
                if let Some(MachOperand::VReg(vreg)) = inst.operands.get(idx) {
                    *counts.entry(*vreg).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

/// Decode a condition code encoding (0-15) to a CondCode variant.
fn decode_cond(encoding: i64) -> Option<CondCode> {
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
        _ => None,
    }
}

/// Invert a condition code. AL/NV are not invertible here.
fn invert_cond(cond: CondCode) -> Option<CondCode> {
    Some(match cond {
        CondCode::EQ => CondCode::NE,
        CondCode::NE => CondCode::EQ,
        CondCode::HS => CondCode::LO,
        CondCode::LO => CondCode::HS,
        CondCode::MI => CondCode::PL,
        CondCode::PL => CondCode::MI,
        CondCode::VS => CondCode::VC,
        CondCode::VC => CondCode::VS,
        CondCode::HI => CondCode::LS,
        CondCode::LS => CondCode::HI,
        CondCode::GE => CondCode::LT,
        CondCode::LT => CondCode::GE,
        CondCode::GT => CondCode::LE,
        CondCode::LE => CondCode::GT,
        CondCode::AL | CondCode::NV => return None,
    })
}

#[cfg(test)]
mod tests;
