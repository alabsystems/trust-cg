// trust-cg-opt - AArch64 Address Mode Formation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 address mode formation pass.
//!
//! A late machine-level optimization that folds ADD instructions into
//! the addressing mode of subsequent LDR/STR instructions, exploiting
//! AArch64's rich addressing modes.
//!
//! # Patterns
//!
//! ## Base + Immediate (form_base_plus_imm)
//!
//! | Pattern | Transformation |
//! |---------|---------------|
//! | `ADD Xd, Xn, #imm` + `LDR Xt, [Xd, #0]` | `LDR Xt, [Xn, #imm]` |
//! | `ADD Xd, Xn, #imm` + `STR Xt, [Xd, #0]` | `STR Xt, [Xn, #imm]` |
//! | `ADD Xd, Xn, #imm1` + `LDR Xt, [Xd, #imm2]` | `LDR Xt, [Xn, #(imm1+imm2)]` |
//! | `ADD Xd, Xn, #imm1` + `STR Xt, [Xd, #imm2]` | `STR Xt, [Xn, #(imm1+imm2)]` |
//! | `ADD Xd, Xn, #imm1` + narrow `LDR*/STR* Wt, [Xd, #imm2]` | narrow `LDR*/STR* Wt, [Xn, #(imm1+imm2)]` |
//!
//! ## Base + Register (form_base_plus_reg)
//!
//! | Pattern | Transformation |
//! |---------|---------------|
//! | `ADD Xd, Xn, Xm` + `LDR Xt, [Xd, #0]` | `LDR Xt, [Xn, Xm]` (LdrRO) |
//! | `ADD Xd, Xn, Xm` + `STR Xt, [Xd, #0]` | `STR Xt, [Xn, Xm]` (StrRO) |
//!
//! ## Pre-Index / Post-Index (form_pre_index / form_post_index)
//!
//! Pre-index (`LDR Xt, [Xn, #imm]!`) and post-index (`LDR Xt, [Xn], #imm`)
//! fold adjacent in-place base updates into single-register writeback
//! load/store opcodes when the rewrite is conservative and imm9-encodable.
//!
//! # Safety Constraints
//!
//! - The ADD result must have exactly one use (the LDR/STR base operand).
//!   If the ADD result is used elsewhere, folding would break those uses.
//! - For base+imm: the combined offset must fit the memory opcode's immediate
//!   form. Generic 64-bit LDR/STR accepts either unsigned scaled offsets or
//!   signed imm9 unscaled offsets; narrow opcodes use unsigned scaled offsets.
//! - For base+reg: the LDR/STR offset must be exactly 0 (folding a non-zero
//!   offset into a register-offset form is not valid).
//! - For single-register pre/post-index writeback: the ADD and memory op must
//!   be adjacent, the memory offset must be zero, the base update must be
//!   in-place, and the transfer register must not overlap the writeback base.
//! - Proof annotations on the LDR/STR are preserved (unchanged).
//! - The ADD instruction is deleted after folding.
//!
//! # Offset Encoding
//!
//! AArch64 LDR/STR unsigned immediate offset is 12 bits, scaled by the
//! access size:
//!
//! | Access Size | Scale | Max Offset | Range |
//! |-------------|-------|------------|-------|
//! | 1 byte      | 1     | 4095       | 0..=4095 |
//! | 2 bytes     | 2     | 8190       | 0..=8190 (2-aligned) |
//! | 4 bytes     | 4     | 16380      | 0..=16380 (4-aligned) |
//! | 8 bytes     | 8     | 32760      | 0..=32760 (8-aligned) |

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachOperand, PassId, ProvenanceMap, RegClass,
    VReg,
};

use crate::dom::DomTree;
use crate::effects::{aarch64_def_operand_positions, aarch64_use_operand_positions};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Bounded depth for the early proof-use address walk.
const EARLY_ADDR_CHAIN_LIMIT: usize = 4;

#[derive(Clone, Copy, Debug)]
struct AddDef {
    inst_id: InstId,
    block_id: BlockId,
    position: usize,
}

#[derive(Clone, Copy, Debug)]
struct ConstDef {
    inst_id: InstId,
    block_id: BlockId,
    position: usize,
    imm: i64,
}

#[derive(Clone, Debug)]
struct ConstOffsetAddrDef {
    block_id: BlockId,
    position: usize,
    base: MachOperand,
    offset: i64,
    chain: Vec<InstId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EarlyPairMemKind {
    Load,
    Store,
}

#[derive(Clone, Copy, Debug)]
enum OffsetEncoding {
    /// Generic scalar LDR/STR fold policy for existing 64-bit memory ops.
    Generic64,
    /// AArch64 unsigned scaled immediate with this access size in bytes.
    ScaledUnsigned(u8),
}

#[derive(Clone, Copy, Debug)]
enum SingleWritebackMode {
    Pre,
    Post,
}

#[derive(Clone, Copy, Debug)]
struct MemAccessInfo {
    base_idx: usize,
    offset_idx: usize,
    offset_encoding: OffsetEncoding,
    supports_reg_offset: bool,
}

#[derive(Clone, Debug)]
struct EarlyPairCandidate {
    kind: EarlyPairMemKind,
    inst_id: InstId,
    position: usize,
    base: MachOperand,
    offset: i64,
    chain: Vec<InstId>,
}

#[derive(Clone, Debug)]
struct EarlyPairRewrite {
    inst_id: InstId,
    base: MachOperand,
    offset: i64,
    chain: Vec<InstId>,
}

// ---------------------------------------------------------------------------
// Offset encoding helpers
// ---------------------------------------------------------------------------

/// Check if an offset is encodable as an AArch64 scaled unsigned 12-bit
/// immediate for a load/store of the given access size.
///
/// AArch64 LDR/STR unsigned immediate: `imm12 * access_size`, where
/// `imm12` is a 12-bit unsigned value (0..4095).
///
/// Requirements:
/// - `offset >= 0`
/// - `offset` is aligned to `access_size`
/// - `offset / access_size <= 4095`
///
/// `access_size` must be 1, 2, 4, or 8. Other values return `false`.
pub fn is_encodable_offset(offset: i64, access_size: u8) -> bool {
    if offset < 0 {
        return false;
    }
    match access_size {
        1 | 2 | 4 | 8 => {
            let scale = access_size as i64;
            offset % scale == 0 && offset / scale <= 4095
        }
        _ => false,
    }
}

/// Check if an offset is encodable as an AArch64 signed 9-bit immediate
/// for pre-index or post-index addressing.
///
/// Pre/post-index immediates are unscaled, range: -256..=255.
pub fn is_encodable_pre_post_offset(offset: i64) -> bool {
    (-256..=255).contains(&offset)
}

// ---------------------------------------------------------------------------
// Pass implementation
// ---------------------------------------------------------------------------

/// AArch64 address mode formation pass.
pub struct AddrModeFormation;

impl MachinePass for AddrModeFormation {
    fn name(&self) -> &str {
        "addr-mode"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_addr_mode(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_addr_mode(func, Some(provenance))
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

/// Conservative early AArch64 address formation for proof pair-op reach.
///
/// This pass is intentionally narrower than [`AddrModeFormation`]. It only
/// rewrites adjacent 64-bit `LdrRI`/`StrRI` pair candidates whose private,
/// one-use immediate address chains can be folded to the same Gpr64 base plus
/// encodable immediate offsets. It handles `AddRI` chains and the constant
/// `Madd(index, scale, base)` shape generated for constant-index trust_ir GEPs,
/// but it does not form single memory addresses or register offset modes.
pub struct AddrModeEarlyFormation;

impl MachinePass for AddrModeEarlyFormation {
    fn name(&self) -> &str {
        "addr-mode-early"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_addr_mode_early(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_addr_mode_early(func, Some(provenance))
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

fn run_addr_mode_early(func: &mut MachFunction, provenance: Option<&mut ProvenanceMap>) -> bool {
    let use_counts = count_vreg_uses(func);
    let def_counts = count_vreg_defs(func);
    let add_ri_defs = collect_add_ri_defs(func, &def_counts);
    let const_defs = collect_private_movz_const_defs(func, &def_counts, &use_counts);
    let const_offset_defs =
        collect_madd_const_offset_defs(func, &def_counts, &use_counts, &const_defs);
    let analyses = EarlyPairAnalyses {
        add_ri_defs: &add_ri_defs,
        const_offset_defs: &const_offset_defs,
        use_counts: &use_counts,
        def_counts: &def_counts,
    };

    let mut rewrites: Vec<EarlyPairRewrite> = Vec::new();
    let mut to_delete: HashSet<InstId> = HashSet::new();

    for block_id in func.block_order.clone() {
        let block_insts = func.block(block_id).insts.clone();
        let mut candidates = Vec::new();

        for (position, &inst_id) in block_insts.iter().enumerate() {
            if let Some(candidate) =
                early_pair_candidate(func, block_id, position, inst_id, &analyses)
            {
                candidates.push(candidate);
            }
        }

        let mut idx = 0;
        while idx + 1 < candidates.len() {
            let first = &candidates[idx];
            let second = &candidates[idx + 1];

            if let Some(pair_rewrites) =
                try_early_pair_rewrites(first, second, &block_insts, &to_delete)
            {
                for rewrite in pair_rewrites {
                    to_delete.extend(rewrite.chain.iter().copied());
                    rewrites.push(rewrite);
                }
                idx += 2;
            } else {
                idx += 1;
            }
        }
    }

    if rewrites.is_empty() {
        return false;
    }

    for rewrite in &rewrites {
        let inst = func.inst_mut(rewrite.inst_id);
        inst.operands[1] = rewrite.base.clone();
        inst.operands[2] = MachOperand::Imm(rewrite.offset);
    }

    if let Some(provenance) = provenance {
        let pass = PassId::new("addr-mode-early");
        for rewrite in &rewrites {
            if rewrite.chain.is_empty() {
                continue;
            }
            let mut sources = rewrite.chain.clone();
            sources.sort_unstable();
            sources.push(rewrite.inst_id);
            provenance.record_merge(&sources, rewrite.inst_id, pass.clone());
        }
    }

    for block_id in func.block_order.clone() {
        let block = func.block_mut(block_id);
        block.insts.retain(|id| !to_delete.contains(id));
    }

    true
}

struct EarlyPairAnalyses<'a> {
    add_ri_defs: &'a HashMap<VReg, AddDef>,
    const_offset_defs: &'a HashMap<VReg, ConstOffsetAddrDef>,
    use_counts: &'a HashMap<VReg, u32>,
    def_counts: &'a HashMap<VReg, u32>,
}

fn early_pair_candidate(
    func: &MachFunction,
    block_id: BlockId,
    position: usize,
    inst_id: InstId,
    analyses: &EarlyPairAnalyses<'_>,
) -> Option<EarlyPairCandidate> {
    let EarlyPairAnalyses {
        add_ri_defs,
        const_offset_defs,
        use_counts,
        def_counts,
    } = analyses;
    let inst = func.inst(inst_id);
    let kind = match inst.opcode {
        AArch64Opcode::LdrRI => EarlyPairMemKind::Load,
        AArch64Opcode::StrRI => EarlyPairMemKind::Store,
        _ => return None,
    };
    if inst.operands.len() < 3 || !is_gpr64_vreg_operand(&inst.operands[0]) {
        return None;
    }

    let mut base = inst.operands[1].clone();
    let mut offset = inst.operands[2].as_imm()?;
    let mut chain = Vec::new();
    let mut current_position = position;

    while let Some(base_vreg) = base.as_vreg() {
        if base_vreg.class != RegClass::Gpr64 {
            return None;
        }

        if let Some(&add_def) = add_ri_defs.get(&base_vreg) {
            if add_def.block_id != block_id {
                break;
            }
            if add_def.position >= current_position {
                return None;
            }
            if use_counts.get(&base_vreg).copied().unwrap_or(0) != 1 {
                break;
            }
            if chain.len() == EARLY_ADDR_CHAIN_LIMIT {
                return None;
            }

            let add_inst = func.inst(add_def.inst_id);
            if add_inst.operands.len() < 3
                || add_inst.operands[0].as_vreg() != Some(base_vreg)
                || !is_gpr64_vreg_operand(&add_inst.operands[1])
            {
                return None;
            }

            let add_offset = add_inst.operands[2].as_imm()?;
            offset = add_offset.checked_add(offset)?;
            base = add_inst.operands[1].clone();
            chain.push(add_def.inst_id);
            current_position = add_def.position;
            continue;
        }

        if let Some(const_offset_def) = const_offset_defs.get(&base_vreg) {
            if const_offset_def.block_id != block_id {
                break;
            }
            if const_offset_def.position >= current_position {
                return None;
            }
            if use_counts.get(&base_vreg).copied().unwrap_or(0) != 1 {
                break;
            }
            if chain.len() + const_offset_def.chain.len() > EARLY_ADDR_CHAIN_LIMIT {
                return None;
            }

            offset = const_offset_def.offset.checked_add(offset)?;
            base = const_offset_def.base.clone();
            chain.extend(const_offset_def.chain.iter().copied());
            current_position = const_offset_def.position;
            continue;
        }

        break;
    }

    let final_base = base.as_vreg()?;
    if final_base.class != RegClass::Gpr64
        || def_counts.get(&final_base).copied().unwrap_or(0) > 1
        || !is_encodable_offset(offset, 8)
    {
        return None;
    }

    Some(EarlyPairCandidate {
        kind,
        inst_id,
        position,
        base,
        offset,
        chain,
    })
}

fn try_early_pair_rewrites(
    first: &EarlyPairCandidate,
    second: &EarlyPairCandidate,
    block_insts: &[InstId],
    already_deleted: &HashSet<InstId>,
) -> Option<Vec<EarlyPairRewrite>> {
    if first.kind != second.kind
        || first.base != second.base
        || first.offset.checked_add(8)? != second.offset
        || !is_encodable_store_pair_offset(first.offset)
        || (first.chain.is_empty() && second.chain.is_empty())
    {
        return None;
    }

    let mut pair_deletes = HashSet::new();
    for id in first.chain.iter().chain(second.chain.iter()).copied() {
        if already_deleted.contains(&id) || !pair_deletes.insert(id) {
            return None;
        }
    }

    if first.position >= second.position {
        return None;
    }
    for inst_id in &block_insts[first.position + 1..second.position] {
        if !pair_deletes.contains(inst_id) {
            return None;
        }
    }

    Some(vec![
        EarlyPairRewrite {
            inst_id: first.inst_id,
            base: first.base.clone(),
            offset: first.offset,
            chain: first.chain.clone(),
        },
        EarlyPairRewrite {
            inst_id: second.inst_id,
            base: second.base.clone(),
            offset: second.offset,
            chain: second.chain.clone(),
        },
    ])
}

fn is_gpr64_vreg_operand(operand: &MachOperand) -> bool {
    matches!(operand, MachOperand::VReg(vreg) if vreg.class == RegClass::Gpr64)
}

fn is_encodable_store_pair_offset(offset: i64) -> bool {
    offset % 8 == 0 && (-64..=63).contains(&(offset / 8))
}

fn run_addr_mode(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    let mut changed = false;

    // Step 1: Count uses and defs by full VReg identity.
    let use_counts = count_vreg_uses(func);
    let def_counts = count_vreg_defs(func);

    // Step 2: Build maps from full VReg identity -> ADD definitions.
    let add_ri_defs = collect_add_ri_defs(func, &def_counts);
    let sub_ri_defs = collect_sub_ri_defs(func, &def_counts, !sub_addr_fold_disabled());
    let add_rr_defs = collect_add_rr_defs(func, &def_counts);

    // Every def position of every vreg. Used to reject folds whose ADD source
    // is redefined between the ADD and the memory op (a multiply-defined
    // base is possible in this non-SSA vreg stream, e.g. block-arg copies).
    let def_positions = collect_def_positions(func);

    // Step 3: Scan for LDR/STR instructions and try to fold.
    let mut to_delete: HashSet<InstId> = HashSet::new();
    let mut folded_pairs: Vec<(InstId, InstId)> = Vec::new();

    for block_id in func.block_order.clone() {
        let block_insts = func.block(block_id).insts.clone();
        for (position, &inst_id) in block_insts.iter().enumerate() {
            let inst = func.inst(inst_id);

            let Some(mem_info) = mem_access_info(inst.opcode) else {
                continue;
            };
            let base_idx = mem_info.base_idx;
            let offset_idx = mem_info.offset_idx;

            if inst.operands.len() <= offset_idx {
                continue;
            }

            // Get the base VReg.
            let base_vreg = match inst.operands[base_idx].as_vreg() {
                Some(v) => v,
                None => continue,
            };

            // Get the current offset immediate.
            let mem_offset = match inst.operands[offset_idx].as_imm() {
                Some(v) => v,
                None => continue,
            };

            // Check the base vreg use count. In-place writeback candidates
            // have two expected uses in the original adjacent pair: the ADD
            // source and the memory base.
            let count = use_counts.get(&base_vreg).copied().unwrap_or(0);
            if count == 2 {
                if position > 0 {
                    let add_id = block_insts[position - 1];
                    if !to_delete.contains(&add_id)
                        && form_pre_index(func, inst_id, add_id, mem_offset)
                    {
                        to_delete.insert(add_id);
                        folded_pairs.push((add_id, inst_id));
                        changed = true;
                        continue;
                    }
                }

                if let Some(&add_id) = block_insts.get(position + 1)
                    && !to_delete.contains(&add_id)
                    && form_post_index(func, inst_id, add_id, mem_offset)
                {
                    to_delete.insert(add_id);
                    folded_pairs.push((add_id, inst_id));
                    changed = true;
                    continue;
                }
            }

            if count != 1 {
                continue;
            }

            // --- Try form_base_plus_imm: fold AddRI into LDR/STR offset ---
            if let Some(&add_def) = add_ri_defs.get(&base_vreg)
                && add_def.block_id == block_id
                && add_def.position < position
                && !to_delete.contains(&add_def.inst_id)
                && add_srcs_unchanged_between(
                    func,
                    &def_positions,
                    add_def.inst_id,
                    block_id,
                    add_def.position,
                    position,
                )
                && form_base_plus_imm(
                    func,
                    inst_id,
                    add_def.inst_id,
                    base_idx,
                    offset_idx,
                    mem_offset,
                    mem_info.offset_encoding,
                )
            {
                to_delete.insert(add_def.inst_id);
                folded_pairs.push((add_def.inst_id, inst_id));
                changed = true;
                continue;
            }

            // --- Try form_base_plus_imm on a SubRI producer -------------
            // `sub xD, xB, #k ; ldr xT, [xD]` -> `ldur xT, [xB, #-k]`.
            // Same admission checks as the AddRI arm; `form_base_plus_imm`
            // reads the signed displacement via `addr_producer_displacement`,
            // and `is_foldable_offset` rejects anything the target opcode's
            // immediate form cannot encode (so an out-of-range negative offset
            // simply does not fold).
            if let Some(&sub_def) = sub_ri_defs.get(&base_vreg)
                && sub_def.block_id == block_id
                && sub_def.position < position
                && !to_delete.contains(&sub_def.inst_id)
                && add_srcs_unchanged_between(
                    func,
                    &def_positions,
                    sub_def.inst_id,
                    block_id,
                    sub_def.position,
                    position,
                )
                && form_base_plus_imm(
                    func,
                    inst_id,
                    sub_def.inst_id,
                    base_idx,
                    offset_idx,
                    mem_offset,
                    mem_info.offset_encoding,
                )
            {
                to_delete.insert(sub_def.inst_id);
                folded_pairs.push((sub_def.inst_id, inst_id));
                changed = true;
                continue;
            }

            // --- Try form_base_plus_reg: fold AddRR into LdrRO/StrRO ---
            if mem_info.supports_reg_offset
                && let Some(&add_def) = add_rr_defs.get(&base_vreg)
                && add_def.block_id == block_id
                && add_def.position < position
                && !to_delete.contains(&add_def.inst_id)
                && add_srcs_unchanged_between(
                    func,
                    &def_positions,
                    add_def.inst_id,
                    block_id,
                    add_def.position,
                    position,
                )
                && form_base_plus_reg(
                    func,
                    inst_id,
                    add_def.inst_id,
                    base_idx,
                    offset_idx,
                    mem_offset,
                )
            {
                to_delete.insert(add_def.inst_id);
                folded_pairs.push((add_def.inst_id, inst_id));
                changed = true;
                continue;
            }
        }
    }

    // Step 4: Record folded address computations and delete their ADD slots.
    if !to_delete.is_empty() {
        if let Some(provenance) = provenance.as_deref_mut() {
            let pass = PassId::new("addr-mode");

            folded_pairs.sort_unstable();
            folded_pairs.dedup();
            for (add_id, mem_id) in folded_pairs {
                provenance.record_merge(&[add_id, mem_id], mem_id, pass.clone());
            }
        }

        for block_id in func.block_order.clone() {
            let block = func.block_mut(block_id);
            block.insts.retain(|id| !to_delete.contains(id));
        }
    }

    // Step 5: multi-use / cross-block base+imm fold. This generalizes
    // form_base_plus_imm to a single-def `AddRI base, #C` whose result is used
    // ONLY as the base of RI load/store ops, with any number of uses in any
    // block, provided `base` is available (dominates, never redefined) at each
    // use and every combined offset encodes. Runs on the post-Step-4 stream.
    changed |= fold_multiuse_base_plus_imm(func, provenance);

    changed
}

fn mem_access_info(opcode: AArch64Opcode) -> Option<MemAccessInfo> {
    let info = match opcode {
        // Generic LDR/STR keep the pre-existing 64-bit unsigned-offset policy.
        AArch64Opcode::LdrRI | AArch64Opcode::StrRI => MemAccessInfo {
            base_idx: 1,
            offset_idx: 2,
            offset_encoding: OffsetEncoding::Generic64,
            supports_reg_offset: true,
        },
        AArch64Opcode::LdrbRI | AArch64Opcode::LdrsbRI | AArch64Opcode::StrbRI => MemAccessInfo {
            base_idx: 1,
            offset_idx: 2,
            offset_encoding: OffsetEncoding::ScaledUnsigned(1),
            supports_reg_offset: false,
        },
        AArch64Opcode::LdrhRI | AArch64Opcode::LdrshRI | AArch64Opcode::StrhRI => MemAccessInfo {
            base_idx: 1,
            offset_idx: 2,
            offset_encoding: OffsetEncoding::ScaledUnsigned(2),
            supports_reg_offset: false,
        },
        _ => return None,
    };
    Some(info)
}

fn is_foldable_offset(offset: i64, encoding: OffsetEncoding) -> bool {
    match encoding {
        OffsetEncoding::Generic64 => is_encodable_generic64_offset(offset),
        OffsetEncoding::ScaledUnsigned(access_size) => is_encodable_offset(offset, access_size),
    }
}

fn is_encodable_generic64_offset(offset: i64) -> bool {
    is_encodable_offset(offset, 8) || is_encodable_pre_post_offset(offset)
}

// ---------------------------------------------------------------------------
// form_base_plus_imm: AddRI + LDR/STR -> LDR/STR with combined offset
// ---------------------------------------------------------------------------

/// Kill switch for the SubRI negative-offset address fold
/// (`TCG_NO_SUB_ADDR_FOLD=1` restores the AddRI-only behaviour).
///
/// AArch64 load/store offsets are SIGNED (the unscaled `LDUR`/`STUR` imm9 form
/// covers -256..255), so `sub xD, xB, #k` feeding `ldr xT, [xD]` is just
/// `ldur xT, [xB, #-k]`. This pass folded only `AddRI`, so the subtract stayed
/// as a real ALU instruction AND kept the two accesses on DIFFERENT base
/// registers -- which also blocks `MemPairFormation`, since pairing needs one
/// base with adjacent displacements.
///
/// MEASURED (huffbench `compdecomp`): trust-cg emitted
/// `sub x0, x2, #0x8 ; ldr x1, [x0] ; ldr x0, [x2]` where clang emits a single
/// `ldp x1, x0, [x0, #-0x8]` -- and folding the subtract lets `MemPairFormation`
/// form that `ldp` on its own, so the site goes 7 instructions to 5:
///
/// ```text
/// before  sxtw x0,w4 ; add x2,x20,x0,lsl#3 ; sub x0,x2,#8 ; ldr x1,[x0] ;
///         ldr x3,[x19,x1,lsl#3] ; ldr x0,[x2] ; ldr x1,[x19,x0,lsl#3]
/// after   sxtw x1,w4 ; add x0,x20,x1,lsl#3 ; ldp x1,x3,[x0,#-0x8] ;
///         ldr x2,[x19,x1,lsl#3] ; ldr x0,[x19,x3,lsl#3]
/// ```
///
/// SITE COUNT, from an env-gated trace at the fire point (NOT from counting the
/// shape in finished objects -- that over-counts badly, because frame lowering
/// creates the same `sub`+access shape POST-RA where this pre-RA pass can never
/// see it, and those post-RA sites are unfoldable anyway: 8 of them are the
/// stack-protector canary at offsets -296..-16456, far outside the LDUR/STUR
/// imm9 window, and the rest target a live call-argument register):
///
/// * SingleSource: 5 candidates, 5 fire, in 3 programs -- huffbench/compdecomp
///   x3, exptree/recSearch x1, ary3/main x1.
/// * gcc-c-torture: 14 candidates, 12 fire, in 7 programs; the 2 that are
///   REFUSED keep the guard path corpus-exercised, so the 1114-PASS torture
///   result is real coverage of this fold rather than a vacuous gate.
///
/// EFFECT, with `TCG_NO_LOOP_HEAD_ALIGN=1` so the alignment lottery cannot
/// masquerade as a win (house rule: a delta that exists only with padding on is
/// repadding, not the transform): 3 of 65 objects change, together -8 real
/// (non-NOP) instructions and -3 memory operations, with `d_nop == 0`.
/// huffbench alone is -6 real / -3 memory ops (722 -> 716 insts, pair ops
/// 27 -> 30). At the shipping default the same 3 objects change by the same
/// -8/-3 while NOPs move +7, which is why the raw instruction total looks flat.
fn sub_addr_fold_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("TCG_NO_SUB_ADDR_FOLD").is_some())
}

/// The SIGNED displacement an address-producing instruction applies to its
/// base: `+imm` for `AddRI`, `-imm` for `SubRI`. Returning `None` refuses any
/// other opcode, so callers can never fold something whose sign they have not
/// modelled.
fn addr_producer_displacement(inst: &trust_cg_ir::MachInst) -> Option<i64> {
    let imm = inst.operands.get(2)?.as_imm()?;
    match inst.opcode {
        AArch64Opcode::AddRI => Some(imm),
        AArch64Opcode::SubRI => imm.checked_neg(),
        _ => None,
    }
}

/// Attempt to fold an AddRI instruction into a LDR/STR's addressing mode.
///
/// Returns `true` if the fold was performed. The ADD instruction should
/// then be deleted by the caller.
fn form_base_plus_imm(
    func: &mut MachFunction,
    load_store_id: InstId,
    add_inst_id: InstId,
    base_idx: usize,
    offset_idx: usize,
    mem_offset: i64,
    offset_encoding: OffsetEncoding,
) -> bool {
    let add_inst = func.inst(add_inst_id);
    if add_inst.operands.len() < 3 {
        return false;
    }

    let add_base = add_inst.operands[1].clone();
    // Sign-aware: `AddRI` contributes +imm, `SubRI` contributes -imm. Any other
    // opcode is refused outright.
    let add_offset = match addr_producer_displacement(add_inst) {
        Some(v) => v,
        None => return false,
    };

    // Compute combined offset.
    let Some(combined_offset) = add_offset.checked_add(mem_offset) else {
        return false;
    };

    // Validate range: must fit the target memory opcode's immediate form.
    if !is_foldable_offset(combined_offset, offset_encoding) {
        return false;
    }

    // Rewrite the LDR/STR: replace base with the ADD's source,
    // replace offset with combined offset.
    let load_store = func.inst_mut(load_store_id);
    load_store.operands[base_idx] = add_base;
    load_store.operands[offset_idx] = MachOperand::Imm(combined_offset);
    preserve_folded_addr_source_loc(func, load_store_id, add_inst_id);

    true
}

// ---------------------------------------------------------------------------
// form_base_plus_reg: AddRR + LDR/STR -> LdrRO/StrRO
// ---------------------------------------------------------------------------

/// Attempt to fold an AddRR instruction into a register-offset addressing
/// mode (LdrRO/StrRO).
///
/// Pattern: `ADD Xd, Xn, Xm` + `LDR Xt, [Xd, #0]` -> `LDR Xt, [Xn, Xm]`
///
/// Constraints:
/// - The LDR/STR must have offset == 0 (register-offset mode has no
///   additional immediate offset).
/// - The ADD must have exactly 3 operands: [dst, src1, src2].
///
/// Returns `true` if the fold was performed. The ADD instruction should
/// then be deleted by the caller.
fn form_base_plus_reg(
    func: &mut MachFunction,
    load_store_id: InstId,
    add_inst_id: InstId,
    base_idx: usize,
    _offset_idx: usize,
    mem_offset: i64,
) -> bool {
    // Register-offset addressing does not support an additional immediate,
    // so the existing LDR/STR offset must be exactly 0.
    if mem_offset != 0 {
        return false;
    }

    let add_inst = func.inst(add_inst_id);
    if add_inst.operands.len() < 3 {
        return false;
    }

    // AddRR: [dst, src1, src2] — both src1 and src2 must be VRegs.
    let add_src1 = add_inst.operands[1].clone();
    let add_src2 = add_inst.operands[2].clone();

    if !add_src1.is_vreg() || !add_src2.is_vreg() {
        return false;
    }

    // Determine the new opcode: LdrRI -> LdrRO, StrRI -> StrRO.
    let load_store = func.inst(load_store_id);
    let new_opcode = match load_store.opcode {
        AArch64Opcode::LdrRI => AArch64Opcode::LdrRO,
        AArch64Opcode::StrRI => AArch64Opcode::StrRO,
        _ => return false,
    };

    // Rewrite: change opcode and replace base+offset with src1+src2.
    // LdrRO operands: [dst, base, index]
    // StrRO operands: [src, base, index]
    let load_store = func.inst_mut(load_store_id);
    load_store.opcode = new_opcode;
    load_store.operands[base_idx] = add_src1;
    // offset_idx holds the offset operand; replace with the index register.
    load_store.operands[base_idx + 1] = add_src2;

    // Update flags to match the new opcode.
    load_store.flags = new_opcode.default_flags();
    preserve_folded_addr_source_loc(func, load_store_id, add_inst_id);

    true
}

fn preserve_folded_addr_source_loc(
    func: &mut MachFunction,
    load_store_id: InstId,
    add_inst_id: InstId,
) {
    let fallback_source_loc = func.inst(add_inst_id).source_loc;
    let load_store = func.inst_mut(load_store_id);
    if load_store.source_loc.is_none() {
        load_store.source_loc = fallback_source_loc;
    }
}

fn single_writeback_opcode(
    opcode: AArch64Opcode,
    mode: SingleWritebackMode,
) -> Option<AArch64Opcode> {
    match (opcode, mode) {
        (AArch64Opcode::LdrRI, SingleWritebackMode::Pre) => Some(AArch64Opcode::LdrPreIndex),
        (AArch64Opcode::StrRI, SingleWritebackMode::Pre) => Some(AArch64Opcode::StrPreIndex),
        (AArch64Opcode::LdrRI, SingleWritebackMode::Post) => Some(AArch64Opcode::LdrPostIndex),
        (AArch64Opcode::StrRI, SingleWritebackMode::Post) => Some(AArch64Opcode::StrPostIndex),
        _ => None,
    }
}

fn same_vreg(lhs: &MachOperand, rhs: &MachOperand) -> bool {
    matches!(
        (lhs.as_vreg(), rhs.as_vreg()),
        (Some(left), Some(right)) if left == right
    )
}

fn transfer_base_overlap(inst: &trust_cg_ir::MachInst) -> bool {
    inst.operands.len() > 1 && same_vreg(&inst.operands[0], &inst.operands[1])
}

fn zero_offset_64bit_single_writeback_candidate(
    inst: &trust_cg_ir::MachInst,
    mem_offset: i64,
) -> bool {
    matches!(inst.opcode, AArch64Opcode::LdrRI | AArch64Opcode::StrRI)
        && mem_offset == 0
        && inst.operands.len() >= 3
        && is_gpr64_vreg_operand(&inst.operands[0])
        && is_gpr64_vreg_operand(&inst.operands[1])
        && !transfer_base_overlap(inst)
}

fn add_ri_in_place_update(
    func: &MachFunction,
    add_inst_id: InstId,
    expected_base: VReg,
) -> Option<i64> {
    let add_inst = func.inst(add_inst_id);
    if add_inst.opcode != AArch64Opcode::AddRI || add_inst.operands.len() < 3 {
        return None;
    }

    let dst = add_inst.operands[0].as_vreg()?;
    let src = add_inst.operands[1].as_vreg()?;
    if dst != expected_base
        || src != expected_base
        || dst.class != RegClass::Gpr64
        || src.class != RegClass::Gpr64
    {
        return None;
    }

    let offset = add_inst.operands[2].as_imm()?;
    is_encodable_pre_post_offset(offset).then_some(offset)
}

fn rewrite_single_writeback(
    func: &mut MachFunction,
    load_store_id: InstId,
    add_inst_id: InstId,
    new_opcode: AArch64Opcode,
    writeback_offset: i64,
) {
    let load_store = func.inst_mut(load_store_id);
    load_store.opcode = new_opcode;
    load_store.operands[2] = MachOperand::Imm(writeback_offset);
    load_store.flags = new_opcode.default_flags();
    preserve_folded_addr_source_loc(func, load_store_id, add_inst_id);
}

// ---------------------------------------------------------------------------
// form_pre_index / form_post_index
// ---------------------------------------------------------------------------

/// Form a pre-index addressing pattern.
///
/// Pattern: `ADD Rbase, Rbase, #N` followed by `LDR Rt, [Rbase, #0]`
/// where Rbase is updated in place (dst == src) and N is in -256..255.
///
/// Folds to `LDR/STR Rt, [Rbase, #N]!` with single-register writeback.
fn form_pre_index(
    func: &mut MachFunction,
    load_store_id: InstId,
    add_inst_id: InstId,
    mem_offset: i64,
) -> bool {
    let load_store = func.inst(load_store_id);
    if !zero_offset_64bit_single_writeback_candidate(load_store, mem_offset) {
        return false;
    }

    let Some(base) = load_store.operands[1].as_vreg() else {
        return false;
    };
    let Some(new_opcode) = single_writeback_opcode(load_store.opcode, SingleWritebackMode::Pre)
    else {
        return false;
    };
    let Some(writeback_offset) = add_ri_in_place_update(func, add_inst_id, base) else {
        return false;
    };

    rewrite_single_writeback(
        func,
        load_store_id,
        add_inst_id,
        new_opcode,
        writeback_offset,
    );
    true
}

/// Form a post-index addressing pattern.
///
/// Pattern: `LDR Rt, [Rbase, #0]` followed by `ADD Rbase, Rbase, #N`
/// where N is in -256..255 and Rbase is updated after the access.
///
/// Folds to `LDR/STR Rt, [Rbase], #N` with single-register writeback.
fn form_post_index(
    func: &mut MachFunction,
    load_store_id: InstId,
    add_inst_id: InstId,
    mem_offset: i64,
) -> bool {
    let load_store = func.inst(load_store_id);
    if !zero_offset_64bit_single_writeback_candidate(load_store, mem_offset) {
        return false;
    }

    let Some(base) = load_store.operands[1].as_vreg() else {
        return false;
    };
    let Some(new_opcode) = single_writeback_opcode(load_store.opcode, SingleWritebackMode::Post)
    else {
        return false;
    };
    let Some(writeback_offset) = add_ri_in_place_update(func, add_inst_id, base) else {
        return false;
    };

    rewrite_single_writeback(
        func,
        load_store_id,
        add_inst_id,
        new_opcode,
        writeback_offset,
    );
    true
}

// ---------------------------------------------------------------------------
// Analysis helpers
// ---------------------------------------------------------------------------

/// Count how many times each VReg appears as a source (use) operand
/// across the entire function.
///
/// Uses target-specific operand roles so DefUse writeback bases count as
/// uses without treating ordinary defs as sources.
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

/// Count explicit definitions by full VReg identity.
///
/// Some late machine passes can temporarily see duplicate virtual-register
/// definitions after rewrites. Address-mode formation must not use such a
/// VReg as a value identity, because a later duplicate def can otherwise
/// overwrite the candidate map for an earlier memory access.
fn count_vreg_defs(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            for idx in aarch64_def_operand_positions(inst.opcode, inst.operands.len()) {
                if let Some(vreg) = inst.operands.get(idx).and_then(|op| op.as_vreg()) {
                    *counts.entry(vreg).or_insert(0) += 1;
                }
            }
        }
    }

    counts
}

/// Collect a map from VReg (def) -> AddDef for all safe AddRI instructions.
///
/// Only records AddRI instructions since those are the ones we can fold
/// into base+immediate addressing modes.
fn collect_add_ri_defs(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
) -> HashMap<VReg, AddDef> {
    let mut defs: HashMap<VReg, AddDef> = HashMap::new();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::AddRI
                && let Some(vreg) = inst.operands.first().and_then(|op| op.as_vreg())
                && def_counts.get(&vreg).copied().unwrap_or(0) == 1
            {
                defs.insert(
                    vreg,
                    AddDef {
                        inst_id,
                        block_id: *block_id,
                        position,
                    },
                );
            }
        }
    }

    defs
}

/// Collect a map from VReg (def) -> AddDef for safe `SubRI` instructions --
/// the negative-displacement twin of [`collect_add_ri_defs`].
///
/// Deliberately kept as a SEPARATE map rather than merged into the AddRI one:
/// the pre/post-index writeback path (`add_ri_in_place_update`) and the
/// generalized multi-use path both assume a POSITIVE `AddRI` displacement, and
/// feeding them a subtract would silently invert the sign. Only the direct
/// `form_base_plus_imm` fold consumes this map.
///
/// `enabled` is the kill-switch decision, passed in rather than read from the
/// environment here so the off-path is unit-testable without an in-process
/// `set_var` racing the parallel test threads (see the sibling NOTE in
/// `ext_addr/tests.rs`). Production callers pass `!sub_addr_fold_disabled()`.
fn collect_sub_ri_defs(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
    enabled: bool,
) -> HashMap<VReg, AddDef> {
    let mut defs: HashMap<VReg, AddDef> = HashMap::new();
    if !enabled {
        return defs;
    }
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::SubRI
                && let Some(vreg) = inst.operands.first().and_then(|op| op.as_vreg())
                && def_counts.get(&vreg).copied().unwrap_or(0) == 1
            {
                defs.insert(
                    vreg,
                    AddDef {
                        inst_id,
                        block_id: *block_id,
                        position,
                    },
                );
            }
        }
    }
    defs
}

/// Collect a map from VReg (def) -> AddDef for all safe AddRR instructions.
///
/// Only records AddRR instructions since those are the ones we can fold
/// into base+register addressing modes (LdrRO/StrRO).
fn collect_add_rr_defs(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
) -> HashMap<VReg, AddDef> {
    let mut defs: HashMap<VReg, AddDef> = HashMap::new();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::AddRR
                && let Some(vreg) = inst.operands.first().and_then(|op| op.as_vreg())
                && def_counts.get(&vreg).copied().unwrap_or(0) == 1
            {
                defs.insert(
                    vreg,
                    AddDef {
                        inst_id,
                        block_id: *block_id,
                        position,
                    },
                );
            }
        }
    }

    defs
}

/// Every def position of every vreg, in block order.
fn collect_def_positions(func: &MachFunction) -> HashMap<VReg, Vec<(BlockId, usize)>> {
    let mut defs: HashMap<VReg, Vec<(BlockId, usize)>> = HashMap::new();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            for idx in aarch64_def_operand_positions(inst.opcode, inst.operands.len()) {
                if let Some(vreg) = inst.operands.get(idx).and_then(|op| op.as_vreg()) {
                    defs.entry(vreg).or_default().push((*block_id, position));
                }
            }
        }
    }

    defs
}

/// Whether every source vreg of the ADD at `add_inst_id` is free of
/// redefinitions strictly between the ADD (at `add_pos`) and the memory op
/// (at `mem_pos`) within `block_id`.
///
/// The fold re-evaluates the ADD's sources AT THE MEMORY OP, so an
/// intervening redefinition of any source would change the computed address.
/// Multiply-defined sources are possible in this non-SSA vreg stream (e.g.
/// block-arg copies), so this must be checked even for a single-def ADD
/// result (fail-closed).
fn add_srcs_unchanged_between(
    func: &MachFunction,
    def_positions: &HashMap<VReg, Vec<(BlockId, usize)>>,
    add_inst_id: InstId,
    block_id: BlockId,
    add_pos: usize,
    mem_pos: usize,
) -> bool {
    let add_inst = func.inst(add_inst_id);
    for idx in aarch64_use_operand_positions(add_inst.opcode, add_inst.operands.len()) {
        if let Some(src) = add_inst.operands.get(idx).and_then(|op| op.as_vreg())
            && let Some(defs) = def_positions.get(&src)
            && defs
                .iter()
                .any(|&(b, p)| b == block_id && p > add_pos && p < mem_pos)
        {
            return false;
        }
    }
    true
}

fn collect_private_movz_const_defs(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
    use_counts: &HashMap<VReg, u32>,
) -> HashMap<VReg, ConstDef> {
    let mut defs: HashMap<VReg, ConstDef> = HashMap::new();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if let Some((vreg, value)) = crate::reaching_const::movz_value(inst)
                && let Ok(imm) = i64::try_from(value)
                && vreg.class == RegClass::Gpr64
                && def_counts.get(&vreg).copied().unwrap_or(0) == 1
                && use_counts.get(&vreg).copied().unwrap_or(0) == 1
            {
                defs.insert(
                    vreg,
                    ConstDef {
                        inst_id,
                        block_id: *block_id,
                        position,
                        imm,
                    },
                );
            }
        }
    }

    defs
}

fn collect_madd_const_offset_defs(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
    use_counts: &HashMap<VReg, u32>,
    const_defs: &HashMap<VReg, ConstDef>,
) -> HashMap<VReg, ConstOffsetAddrDef> {
    let mut defs: HashMap<VReg, ConstOffsetAddrDef> = HashMap::new();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::Madd || inst.operands.len() < 4 {
                continue;
            }

            let Some(dst) = inst.operands.first().and_then(|op| op.as_vreg()) else {
                continue;
            };
            if dst.class != RegClass::Gpr64
                || def_counts.get(&dst).copied().unwrap_or(0) != 1
                || use_counts.get(&dst).copied().unwrap_or(0) != 1
            {
                continue;
            }

            let (Some(lhs), Some(rhs)) = (
                inst.operands.get(1).and_then(|op| op.as_vreg()),
                inst.operands.get(2).and_then(|op| op.as_vreg()),
            ) else {
                continue;
            };
            if lhs.class != RegClass::Gpr64 || rhs.class != RegClass::Gpr64 {
                continue;
            }
            let Some(base) = inst.operands.get(3).cloned() else {
                continue;
            };
            if !is_gpr64_vreg_operand(&base) {
                continue;
            }
            if let Some(base_vreg) = base.as_vreg()
                && def_counts.get(&base_vreg).copied().unwrap_or(0) > 1
            {
                continue;
            }

            let (Some(lhs_const), Some(rhs_const)) = (const_defs.get(&lhs), const_defs.get(&rhs))
            else {
                continue;
            };
            if lhs_const.block_id != *block_id
                || rhs_const.block_id != *block_id
                || lhs_const.position >= position
                || rhs_const.position >= position
            {
                continue;
            }

            let Some(offset) = lhs_const.imm.checked_mul(rhs_const.imm) else {
                continue;
            };

            defs.insert(
                dst,
                ConstOffsetAddrDef {
                    block_id: *block_id,
                    position,
                    base,
                    offset,
                    chain: vec![lhs_const.inst_id, rhs_const.inst_id, inst_id],
                },
            );
        }
    }

    defs
}

// ---------------------------------------------------------------------------
// fold_multiuse_base_plus_imm
//
// Generalization of form_base_plus_imm: a single-def `AddRI d, base, #C` whose
// result `d` is used ONLY as the base operand of RI load/store ops — for ANY
// number of uses, possibly in different blocks — is folded away by rewriting
// every such use to `[base, #(C + its own offset)]` and deleting the AddRI.
//
// Soundness (each condition fail-closed):
//   * the AddRI is single-def, so `d` is exactly `base + C` wherever it holds;
//   * the AddRI's def dominates every use of `d`, so the fold only rewrites
//     uses where `d` is genuinely defined (never a use-before-def / unreachable
//     def whose "value" the fold would otherwise invent);
//   * `base` is a single-def (or live-in) Gpr64 vreg, so its value is identical
//     everywhere, and its definition dominates every use site — available and
//     never redefined between the def and the use, so `base` at the use equals
//     `base` at the AddRI (hence `[base, C+off]` == the original `[d, off]`);
//   * `d` appears ONLY as the base of each use (never as stored data, an index,
//     or an arithmetic operand);
//   * every combined offset is encodable, using the SAME per-opcode policy as
//     `form_base_plus_imm` (`mem_access_info` + `is_foldable_offset`).
// If ANY use fails, the whole candidate is rejected and its AddRI is untouched.
//
// Benefit gate: the candidate is committed when at least one use is in a
// DIFFERENT block than the AddRI (cross-block folds delete a pointer that
// would otherwise live — and spill/rematerialize — across the span between
// the AddRI and its far uses, e.g. salsa20's per-element `&x[i]`), OR when the
// AddRI feeds at least TWO rewritten mem ops (a struct-field base like Towers'
// `&cell.next`: folding deletes the ADD outright and lets both accesses share
// the enclosing base, which also exposes LDP/STP pairing). A single-use
// intra-block AddRI stays with the existing `form_base_plus_imm` path.
//
// Multi-def base extension: when `base` has more than one def (the common
// non-SSA loop-carried pointer, e.g. Treesort's tree-walk node), the fold is
// still sound iff at every rewritten use `base` provably holds the value it
// had at the MOST RECENT execution of the AddRI. That is proven by the
// [`BaseCleanliness`] block-level dataflow below; any use it cannot prove
// clean rejects the whole candidate (fail-closed). A profitability cut skips
// the pointer-chase idiom (rewritten load feeding a `base` redefinition),
// where the fold is sound but breaks load/pointer coalescing.
//
// Kill switches:
//   * `TCG_NO_ADDR_MODE_MULTIUSE_FOLD`       — disable this whole step;
//   * `TCG_NO_ADDR_MODE_MULTIDEF_BASE`       — restrict to single-def bases;
//   * `TCG_NO_ADDR_MODE_INTRABLOCK_MULTIUSE` — restore the cross-block-only
//     benefit gate.
// ---------------------------------------------------------------------------

/// One occurrence of a virtual register as an operand of some instruction.
#[derive(Clone, Copy)]
struct OperandOcc {
    inst_id: InstId,
    block_id: BlockId,
    position: usize,
}

/// Whether a definition at `(def_block, def_pos)` is available at a use at
/// `(use_block, use_pos)`: within a block, the def must precede the use; across
/// blocks, the def's block must dominate the use's block (unreachable use
/// blocks have no idom chain and are therefore never dominated). The dominator
/// tree is built lazily on the first cross-block query.
fn def_available_at_use(
    func: &MachFunction,
    dom: &mut Option<DomTree>,
    def_block: BlockId,
    def_pos: usize,
    use_block: BlockId,
    use_pos: usize,
) -> bool {
    if def_block == use_block {
        def_pos < use_pos
    } else {
        dom.get_or_insert_with(|| DomTree::compute(func))
            .dominates(def_block, use_block)
    }
}

/// Cleanliness proof for a multiply-defined fold base.
///
/// The fold rewrites each use `[d, #off]` to `[base, #(C + off)]`, where `d`
/// is the single def of `AddRI d = base + C`. At a use, `d` holds
/// `base_at_last_AddRI + C`, so the rewrite is sound iff `base` at the use
/// still equals `base` at the MOST RECENT execution of the AddRI.
///
/// Block-level forward dataflow over {clean, dirty}, seeded just after the
/// AddRI. A block entry is "dirty" when some path from the AddRI reaches it
/// with an intervening redefinition of `base` that did not pass through the
/// AddRI again. Machine blocks are straight-line, so re-entering the AddRI's
/// block always re-executes the AddRI, which recomputes `d` from the current
/// `base` and resets the state to clean. Nothing else cleans a dirty state.
/// Each block is visited with at most two entry states, so the walk
/// terminates.
struct BaseCleanliness {
    /// Blocks whose entry can be reached from the AddRI with `base` changed
    /// since the most recent AddRI execution.
    dirty_entry: HashSet<BlockId>,
    /// Positions of instructions defining `base`, per block.
    defs_in_block: HashMap<BlockId, Vec<usize>>,
    add_block: BlockId,
    add_pos: usize,
}

impl BaseCleanliness {
    fn compute(
        func: &MachFunction,
        base_defs: &[(BlockId, usize)],
        add_block: BlockId,
        add_pos: usize,
    ) -> Self {
        let mut defs_in_block: HashMap<BlockId, Vec<usize>> = HashMap::new();
        for &(block_id, position) in base_defs {
            defs_in_block.entry(block_id).or_default().push(position);
        }

        // Exit state of the AddRI's block is independent of its entry state:
        // executing it always passes the AddRI (reset to clean), after which
        // only a later `base` def in the same block can dirty the exit.
        let add_exit_dirty = defs_in_block
            .get(&add_block)
            .is_some_and(|defs| defs.iter().any(|&p| p > add_pos));

        let mut dirty_entry: HashSet<BlockId> = HashSet::new();
        let mut visited: HashSet<(BlockId, bool)> = HashSet::new();
        let mut work: Vec<(BlockId, bool)> = func
            .block(add_block)
            .succs
            .iter()
            .map(|&succ| (succ, add_exit_dirty))
            .collect();
        while let Some((block_id, entry_dirty)) = work.pop() {
            if !visited.insert((block_id, entry_dirty)) {
                continue;
            }
            if entry_dirty {
                dirty_entry.insert(block_id);
            }
            let exit_dirty = if block_id == add_block {
                add_exit_dirty
            } else {
                entry_dirty || defs_in_block.contains_key(&block_id)
            };
            for &succ in &func.block(block_id).succs {
                if !visited.contains(&(succ, exit_dirty)) {
                    work.push((succ, exit_dirty));
                }
            }
        }

        Self {
            dirty_entry,
            defs_in_block,
            add_block,
            add_pos,
        }
    }

    /// Whether `base` at `(use_block, use_pos)` provably equals `base` at the
    /// most recent execution of the AddRI. The caller has already proven that
    /// the AddRI dominates the use (in particular, `add_pos < use_pos` when
    /// `use_block == add_block`). A use instruction that itself redefines
    /// `base` (e.g. `LDR base, [d]`) reads its address before writing, so
    /// defs AT the use position do not matter.
    fn base_unchanged_at(&self, use_block: BlockId, use_pos: usize) -> bool {
        if use_block == self.add_block {
            // Every entry re-executes the AddRI before reaching the use; only
            // a redefinition strictly between them can change `base`.
            !self.has_def_in_range(use_block, self.add_pos + 1, use_pos)
        } else {
            !self.dirty_entry.contains(&use_block) && !self.has_def_in_range(use_block, 0, use_pos)
        }
    }

    /// Any def of `base` at position `p` with `lo <= p < hi` in `block`.
    fn has_def_in_range(&self, block: BlockId, lo: usize, hi: usize) -> bool {
        self.defs_in_block
            .get(&block)
            .is_some_and(|defs| defs.iter().any(|&p| lo <= p && p < hi))
    }
}

fn fold_multiuse_base_plus_imm(
    func: &mut MachFunction,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    if std::env::var_os("TCG_NO_ADDR_MODE_MULTIUSE_FOLD").is_some() {
        return false;
    }
    let multidef_base_enabled = std::env::var_os("TCG_NO_ADDR_MODE_MULTIDEF_BASE").is_none();
    let intrablock_enabled = std::env::var_os("TCG_NO_ADDR_MODE_INTRABLOCK_MULTIUSE").is_none();

    // Fresh analysis on the post-Step-4 instruction stream.
    let def_counts = count_vreg_defs(func);
    let add_ri_defs = collect_add_ri_defs(func, &def_counts);
    if add_ri_defs.is_empty() {
        return false;
    }

    // Every def position of every vreg (first entry = the unique def site of
    // a single-def vreg), plus every operand occurrence of every vreg.
    let def_positions = collect_def_positions(func);
    let mut occ: HashMap<VReg, Vec<OperandOcc>> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            for op in &inst.operands {
                if let Some(v) = op.as_vreg() {
                    occ.entry(v).or_default().push(OperandOcc {
                        inst_id,
                        block_id: *block_id,
                        position,
                    });
                }
            }
        }
    }

    // Dominator tree, built lazily on the first cross-block availability query.
    let mut dom: Option<DomTree> = None;

    // Transforms validated against the snapshot above, applied only at the end.
    let mut rewrites: Vec<(InstId, MachOperand, i64)> = Vec::new();
    let mut to_delete: HashSet<InstId> = HashSet::new();
    let mut folded_pairs: Vec<(InstId, InstId)> = Vec::new();

    // Deterministic iteration order (defining-AddRI instruction id).
    let mut candidates: Vec<(VReg, AddDef)> = add_ri_defs.iter().map(|(v, d)| (*v, *d)).collect();
    candidates.sort_unstable_by_key(|(_, d)| d.inst_id);

    'candidate: for (d, add_def) in candidates {
        let add_id = add_def.inst_id;

        // AddRI shape: [dst = d (Gpr64), base (Gpr64 vreg), imm C].
        let (base_operand, add_offset) = {
            let add_inst = func.inst(add_id);
            if add_inst.operands.len() < 3
                || add_inst.operands[0].as_vreg() != Some(d)
                || d.class != RegClass::Gpr64
                || !is_gpr64_vreg_operand(&add_inst.operands[1])
            {
                continue;
            }
            let Some(off) = add_inst.operands[2].as_imm() else {
                continue;
            };
            (add_inst.operands[1].clone(), off)
        };
        let Some(base_vreg) = base_operand.as_vreg() else {
            continue;
        };
        if base_vreg == d {
            continue;
        }
        // Single-def (or live-in) `base`: its value is identical at every use
        // its def dominates (0 defs = live-in; 1 def = SSA-like single
        // assignment); availability is checked per use below via `base_def`.
        // Multi-def `base` (a non-SSA loop-carried pointer): run the
        // cleanliness dataflow instead — every rewritten use must be provably
        // reached with `base` unchanged since the most recent AddRI execution.
        let base_multi_def = def_counts.get(&base_vreg).copied().unwrap_or(0) > 1;
        if base_multi_def && !multidef_base_enabled {
            continue;
        }
        let base_def = if base_multi_def {
            None
        } else {
            def_positions
                .get(&base_vreg)
                .and_then(|defs| defs.first())
                .copied()
        };
        // LAZY. `BaseCleanliness::compute` is a whole-CFG dataflow walk
        // (O(blocks + edges)) and this loop runs once per single-def AddRI in
        // the function, so computing it eagerly cost O(instructions x blocks) —
        // the quadratic that made addr-mode 11.8ms -> 38.6ms for a 2x block
        // count on the `branchy` shape.
        //
        // It is only ever read at the multi-def check further down, which is
        // reached only after two earlier `continue 'candidate` bailouts. Most
        // candidates never get there, so deferring it to first use skips the
        // walk entirely for them. Same value, computed at most once per
        // candidate — `get_or_init` runs the closure only on the first read.
        let base_clean: std::cell::OnceCell<BaseCleanliness> = std::cell::OnceCell::new();
        let base_clean_defs: &[(BlockId, usize)] =
            def_positions.get(&base_vreg).map_or(&[][..], Vec::as_slice);

        // Every occurrence of `d` other than its own defining AddRI must be the
        // base of a foldable RI mem op with an encodable combined offset, and
        // `base` must be available (its def dominates, never redefined) there.
        let Some(occs) = occ.get(&d) else {
            continue;
        };
        let mut local_rewrites: Vec<(InstId, i64)> = Vec::new();
        let mut cross_block_use = false;
        for o in occs {
            if o.inst_id == add_id {
                // The defining AddRI itself (d at the def operand). Skip.
                continue;
            }
            let combined = {
                let use_inst = func.inst(o.inst_id);
                // Foldable RI mem op? (rejects LdrRO/StrRO and non-mem ops.)
                let Some(mem_info) = mem_access_info(use_inst.opcode) else {
                    continue 'candidate;
                };
                let base_idx = mem_info.base_idx;
                let offset_idx = mem_info.offset_idx;
                if use_inst.operands.len() <= offset_idx {
                    continue 'candidate;
                }
                // `d` must appear ONLY as the base of this op.
                if use_inst.operands[base_idx].as_vreg() != Some(d) {
                    continue 'candidate;
                }
                if use_inst
                    .operands
                    .iter()
                    .enumerate()
                    .any(|(i, op)| i != base_idx && op.as_vreg() == Some(d))
                {
                    continue 'candidate;
                }
                let Some(mem_offset) = use_inst.operands[offset_idx].as_imm() else {
                    continue 'candidate;
                };
                let Some(combined) = add_offset.checked_add(mem_offset) else {
                    continue 'candidate;
                };
                // Same per-opcode encodability policy as form_base_plus_imm.
                if !is_foldable_offset(combined, mem_info.offset_encoding) {
                    continue 'candidate;
                }
                combined
            };
            // `d` must be genuinely defined at this use: the AddRI dominates it.
            if !def_available_at_use(
                func,
                &mut dom,
                add_def.block_id,
                add_def.position,
                o.block_id,
                o.position,
            ) {
                continue 'candidate;
            }
            // `base` must be available (defined, never redefined) at this use.
            if let Some((bd_block, bd_pos)) = base_def
                && !def_available_at_use(func, &mut dom, bd_block, bd_pos, o.block_id, o.position)
            {
                continue 'candidate;
            }
            // Multi-def `base`: must provably hold the value it had at the
            // most recent execution of the AddRI when this use runs.
            if base_multi_def {
                let clean = base_clean.get_or_init(|| {
                    BaseCleanliness::compute(
                        func,
                        base_clean_defs,
                        add_def.block_id,
                        add_def.position,
                    )
                });
                if !clean.base_unchanged_at(o.block_id, o.position) {
                    continue 'candidate;
                }
            }
            if o.block_id != add_def.block_id {
                cross_block_use = true;
            }
            local_rewrites.push((o.inst_id, combined));
        }

        // Commit when the fold collapses a value that lives ACROSS a block
        // boundary — the pointer would otherwise be live (and often
        // spilled/rematerialized) across the region between the AddRI and its
        // far uses (e.g. salsa20's per-element `&x[i]` held across the round
        // loop) — or when it feeds at least TWO mem ops in the AddRI's own
        // block (a struct-field base like Towers' `&cell.next`: the ADD is
        // deleted outright and both accesses share the enclosing base, which
        // also exposes LDP/STP pairing). A single-use intra-block AddRI is
        // left to the existing `form_base_plus_imm` path.
        if local_rewrites.is_empty() {
            continue;
        }
        if !(cross_block_use || intrablock_enabled && local_rewrites.len() >= 2) {
            continue;
        }

        // Profitability cut for multiply-defined bases: skip the
        // pointer-chase idiom, where a rewritten load's result feeds a
        // redefinition of `base` (e.g. Treesort's `node = node->left`).
        // Folding is SOUND there (cleanliness proved above) but keeps the OLD
        // base live across the load, so the load result can no longer
        // coalesce with the loop-carried pointer: the hot loop gains a copy
        // and loses a fallthrough — a measured net loss on Treesort. A load
        // that redefines `base` directly (in-place chase) has no such copy
        // and is exempt.
        if base_multi_def {
            let rewritten: HashSet<InstId> = local_rewrites.iter().map(|&(id, _)| id).collect();
            let load_dsts: HashSet<VReg> = local_rewrites
                .iter()
                .filter_map(|&(mem_id, _)| {
                    let inst = func.inst(mem_id);
                    matches!(
                        inst.opcode,
                        AArch64Opcode::LdrRI
                            | AArch64Opcode::LdrbRI
                            | AArch64Opcode::LdrsbRI
                            | AArch64Opcode::LdrhRI
                            | AArch64Opcode::LdrshRI
                    )
                    .then(|| inst.operands.first().and_then(|op| op.as_vreg()))
                    .flatten()
                })
                .collect();
            let feeds_base_redef = def_positions.get(&base_vreg).is_some_and(|defs| {
                defs.iter().any(|&(block_id, position)| {
                    let def_id = func.block(block_id).insts[position];
                    if rewritten.contains(&def_id) {
                        return false;
                    }
                    let inst = func.inst(def_id);
                    aarch64_use_operand_positions(inst.opcode, inst.operands.len())
                        .into_iter()
                        .any(|idx| {
                            inst.operands
                                .get(idx)
                                .and_then(|op| op.as_vreg())
                                .is_some_and(|v| load_dsts.contains(&v))
                        })
                })
            });
            if feeds_base_redef {
                continue;
            }
        }

        // All uses validated: commit this candidate.
        for (mem_id, combined) in local_rewrites {
            rewrites.push((mem_id, base_operand.clone(), combined));
            folded_pairs.push((add_id, mem_id));
        }
        to_delete.insert(add_id);
    }

    if rewrites.is_empty() {
        return false;
    }

    // Apply rewrites. Each mem op has a unique base vreg, so no two candidates
    // target the same mem op; application order does not matter.
    for (mem_id, base, combined) in &rewrites {
        let inst = func.inst_mut(*mem_id);
        inst.operands[1] = base.clone();
        inst.operands[2] = MachOperand::Imm(*combined);
    }

    // Carry each folded AddRI's source location onto its consumers.
    for (add_id, mem_id) in &folded_pairs {
        preserve_folded_addr_source_loc(func, *mem_id, *add_id);
    }

    if let Some(provenance) = provenance {
        let pass = PassId::new("addr-mode");
        let mut pairs = folded_pairs.clone();
        pairs.sort_unstable();
        pairs.dedup();
        for (add_id, mem_id) in pairs {
            provenance.record_merge(&[add_id, mem_id], mem_id, pass.clone());
        }
    }

    for block_id in func.block_order.clone() {
        let block = func.block_mut(block_id);
        block.insts.retain(|id| !to_delete.contains(id));
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use trust_cg_ir::{
        AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PassId, ProofAnnotation,
        ProvenanceMap, RegClass, Signature, SourceLoc, TransformKind, TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func =
            MachFunction::new("test_addr_mode".to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 0,
            line,
            col: 3,
        }
    }

    // ================================================================
    // is_encodable_offset tests
    // ================================================================

    #[test]
    fn test_encodable_offset_byte() {
        // Byte: scale=1, max=4095
        assert!(is_encodable_offset(0, 1));
        assert!(is_encodable_offset(1, 1));
        assert!(is_encodable_offset(4095, 1));
        assert!(!is_encodable_offset(4096, 1));
        assert!(!is_encodable_offset(-1, 1));
    }

    #[test]
    fn test_encodable_offset_half() {
        // Half: scale=2, max=8190, must be 2-aligned
        assert!(is_encodable_offset(0, 2));
        assert!(is_encodable_offset(2, 2));
        assert!(is_encodable_offset(8190, 2));
        assert!(!is_encodable_offset(8192, 2));
        assert!(!is_encodable_offset(1, 2)); // misaligned
        assert!(!is_encodable_offset(3, 2)); // misaligned
        assert!(!is_encodable_offset(-2, 2));
    }

    #[test]
    fn test_encodable_offset_word() {
        // Word: scale=4, max=16380, must be 4-aligned
        assert!(is_encodable_offset(0, 4));
        assert!(is_encodable_offset(4, 4));
        assert!(is_encodable_offset(16380, 4));
        assert!(!is_encodable_offset(16384, 4));
        assert!(!is_encodable_offset(1, 4)); // misaligned
        assert!(!is_encodable_offset(2, 4)); // misaligned
        assert!(!is_encodable_offset(-4, 4));
    }

    #[test]
    fn test_encodable_offset_double() {
        // Double: scale=8, max=32760, must be 8-aligned
        assert!(is_encodable_offset(0, 8));
        assert!(is_encodable_offset(8, 8));
        assert!(is_encodable_offset(32760, 8));
        assert!(!is_encodable_offset(32768, 8));
        assert!(!is_encodable_offset(1, 8)); // misaligned
        assert!(!is_encodable_offset(4, 8)); // misaligned
        assert!(!is_encodable_offset(-8, 8));
    }

    #[test]
    fn test_encodable_offset_invalid_size() {
        assert!(!is_encodable_offset(0, 0));
        assert!(!is_encodable_offset(0, 3));
        assert!(!is_encodable_offset(0, 16));
    }

    #[test]
    fn test_encodable_pre_post_offset() {
        assert!(is_encodable_pre_post_offset(0));
        assert!(is_encodable_pre_post_offset(255));
        assert!(is_encodable_pre_post_offset(-256));
        assert!(!is_encodable_pre_post_offset(256));
        assert!(!is_encodable_pre_post_offset(-257));
        assert!(is_encodable_pre_post_offset(1));
        assert!(is_encodable_pre_post_offset(-1));
    }

    // ================================================================
    // form_base_plus_imm tests (existing tests, preserved)
    // ================================================================

    #[test]
    fn test_fold_add_imm_into_ldr() {
        // ADD v1, v0, #16
        // LDR v2, [v1, #0]
        // RET
        // -> LDR v2, [v0, #16], ADD deleted
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        // ADD should be deleted, leaving LDR + RET
        assert_eq!(block.insts.len(), 2);

        // LDR should now use v0 as base with offset 16
        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRI);
        assert_eq!(ldr_inst.operands[0], vreg(2)); // dst unchanged
        assert_eq!(ldr_inst.operands[1], vreg(0)); // base = ADD's source
        assert_eq!(ldr_inst.operands[2], imm(16)); // offset = ADD's imm
    }

    #[test]
    fn test_fold_add_imm_into_str() {
        // ADD v1, v0, #8
        // STR v2, [v1, #0]
        // RET
        // -> STR v2, [v0, #8], ADD deleted
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // STR + RET

        let str_result = func.inst(InstId(1));
        assert_eq!(str_result.opcode, AArch64Opcode::StrRI);
        assert_eq!(str_result.operands[0], vreg(2)); // src unchanged
        assert_eq!(str_result.operands[1], vreg(0)); // base = ADD's source
        assert_eq!(str_result.operands[2], imm(8)); // offset = ADD's imm
    }

    #[test]
    fn test_fold_add_imm_into_ldrb() {
        // ADD v1, v0, #37
        // LDRB w2, [v1, #5]
        // RET
        // -> LDRB w2, [v0, #42], ADD deleted
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(37)]);
        let ldrb = MachInst::new(AArch64Opcode::LdrbRI, vec![vreg32(2), vreg(1), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldrb, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);

        let ldrb_inst = func.inst(InstId(1));
        assert_eq!(ldrb_inst.opcode, AArch64Opcode::LdrbRI);
        assert_eq!(ldrb_inst.operands, vec![vreg32(2), vreg(0), imm(42)]);
    }

    #[test]
    fn test_fold_add_imm_into_strh() {
        // ADD v1, v0, #4
        // STRH w2, [v1, #6]
        // RET
        // -> STRH w2, [v0, #10], ADD deleted
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(4)]);
        let strh = MachInst::new(AArch64Opcode::StrhRI, vec![vreg32(2), vreg(1), imm(6)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, strh, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);

        let strh_inst = func.inst(InstId(1));
        assert_eq!(strh_inst.opcode, AArch64Opcode::StrhRI);
        assert_eq!(strh_inst.operands, vec![vreg32(2), vreg(0), imm(10)]);
    }

    #[test]
    fn test_fold_add_imm_into_ldrsh_preserves_proof_and_source_loc() {
        let loc = source_loc(43);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)])
            .with_source_loc(loc);
        let ldrsh = MachInst::new(AArch64Opcode::LdrshRI, vec![vreg32(2), vreg(1), imm(4)])
            .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldrsh, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let ldrsh_inst = func.inst(InstId(1));
        assert_eq!(ldrsh_inst.opcode, AArch64Opcode::LdrshRI);
        assert_eq!(ldrsh_inst.operands, vec![vreg32(2), vreg(0), imm(12)]);
        assert_eq!(ldrsh_inst.proof, Some(ProofAnnotation::InBounds));
        assert_eq!(ldrsh_inst.source_loc, Some(loc));
    }

    #[test]
    fn test_no_fold_strh_unaligned_combined_offset() {
        // Halfword unsigned offsets must be 2-byte aligned.
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(3)]);
        let strh = MachInst::new(AArch64Opcode::StrhRI, vec![vreg32(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, strh, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        let strh_inst = func.inst(InstId(1));
        assert_eq!(strh_inst.operands, vec![vreg32(2), vreg(1), imm(0)]);
    }

    #[test]
    fn test_no_fold_ldrh_offset_beyond_scaled_unsigned_range() {
        // Halfword unsigned offsets are 12-bit scaled, max byte offset 8190.
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8192)]);
        let ldrh = MachInst::new(AArch64Opcode::LdrhRI, vec![vreg32(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldrh, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        let ldrh_inst = func.inst(InstId(1));
        assert_eq!(ldrh_inst.operands, vec![vreg32(2), vreg(1), imm(0)]);
    }

    #[test]
    fn test_fold_add_imm_source_loc_falls_back_to_add_when_memory_has_none() {
        let loc = source_loc(41);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)])
            .with_source_loc(loc);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.source_loc, Some(loc));
    }

    #[test]
    fn test_fold_combined_offsets() {
        // ADD v1, v0, #8
        // LDR v2, [v1, #16]
        // RET
        // -> LDR v2, [v0, #24]
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);

        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.operands[1], vreg(0));
        assert_eq!(ldr_inst.operands[2], imm(24)); // 8 + 16
    }

    // ---- Safety: no fold when multiple uses ----

    #[test]
    fn test_no_fold_multiple_uses() {
        // ADD v1, v0, #16
        // LDR v2, [v1, #0]
        // ADD v3, v1, #4    <- second use of v1
        // RET
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(1), imm(4)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, add2, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        // All instructions preserved
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
    }

    #[test]
    fn test_fold_add_imm_ignores_same_id_different_class_def() {
        // ADD x1, x0, #16
        // ADD w1, w4, #7    <- same numeric id, different register class
        // LDR x2, [x1, #0]
        // RET
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let decoy = MachInst::new(AArch64Opcode::AddRI, vec![vreg32(1), vreg32(4), imm(7)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, decoy, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(
            pass.run(&mut func),
            "same numeric id in another class must not block the Gpr64 fold"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(1), InstId(2), InstId(3)]);
        assert_eq!(func.inst(InstId(1)).operands[0], vreg32(1));
        let ldr_inst = func.inst(InstId(2));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRI);
        assert_eq!(ldr_inst.operands, vec![vreg(2), vreg(0), imm(16)]);
    }

    #[test]
    fn test_no_fold_duplicate_add_ri_defs() {
        // ADD v1, v0, #8
        // LDR v2, [v1, #0]
        // ADD v1, v3, #16   <- duplicate def of v1 must not be used as identity
        // RET
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(3), imm(16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, ldr, add2, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.operands[1], vreg(1));
        assert_eq!(ldr_inst.operands[2], imm(0));
    }

    #[test]
    fn test_no_fold_add_after_memory_same_block() {
        // LDR v2, [v1, #0]
        // ADD v1, v0, #8    <- later def cannot dominate the earlier load
        // RET
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, add, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        let ldr_inst = func.inst(InstId(0));
        assert_eq!(ldr_inst.operands[1], vreg(1));
        assert_eq!(ldr_inst.operands[2], imm(0));
    }

    #[test]
    fn test_no_fold_add_ri_across_blocks_without_dominance() {
        // ADD v1, v0, #8     in entry block
        // LDR v2, [v1, #0]   in a later block
        //
        // The pass intentionally avoids cross-block folding until it has a
        // real dominance/order proof for machine blocks.
        let mut func = MachFunction::new(
            "test_addr_mode_cross_block".to_string(),
            Signature::new(vec![], vec![]),
        );
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(8)],
        ));
        func.append_inst(func.entry, add);
        let later = func.create_block();
        let ldr = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(1), imm(0)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(later, ldr);
        func.append_inst(later, ret);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let entry = func.block(func.entry);
        let later_block = func.block(later);
        assert_eq!(entry.insts.len(), 1);
        assert_eq!(later_block.insts.len(), 2);
        let ldr_inst = func.inst(ldr);
        assert_eq!(ldr_inst.operands[1], vreg(1));
        assert_eq!(ldr_inst.operands[2], imm(0));
    }

    // ---- Safety: offset range validation ----

    #[test]
    fn test_no_fold_offset_out_of_range() {
        // ADD v1, v0, #32000
        // LDR v2, [v1, #1000]
        // RET
        // Combined = 33000, exceeds 32760
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(32000)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(1000)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3); // unchanged
    }

    #[test]
    fn test_fold_negative_signed_imm9_generic_offset() {
        // ADD v1, v0, #-8
        // LDR v2, [v1, #0]
        // RET
        // Combined offset = -8, signed imm9 unscaled -> fold
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(-8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.operands[1], vreg(0));
        assert_eq!(ldr_inst.operands[2], imm(-8));
    }

    #[test]
    fn test_fold_positive_unaligned_signed_imm9_generic_store_offset() {
        // ADD v1, v0, #7
        // STR v2, [v1, #0]
        // RET
        // Combined offset = 7, signed imm9 unscaled -> fold
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(7)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let str_inst = func.inst(InstId(1));
        assert_eq!(str_inst.operands[1], vreg(0));
        assert_eq!(str_inst.operands[2], imm(7));
    }

    #[test]
    fn test_no_fold_negative_offset_below_signed_imm9_range() {
        // ADD v1, v0, #-257
        // LDR v2, [v1, #0]
        // RET
        // Combined offset = -257, below signed imm9 -> reject
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(-257)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
    }

    // ================================================================
    // SubRI negative-offset fold (kill switch TCG_NO_SUB_ADDR_FOLD)
    // ================================================================

    #[test]
    fn test_fold_sub_imm_into_ldr() {
        // SUB v1, v0, #8
        // LDR v2, [v1, #0]
        // RET
        // -> LDR v2, [v0, #-8] (LDUR form), SUB deleted.
        // This is the huffbench sift-down shape verbatim.
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2, "SUB deleted, LDR + RET remain");
        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRI);
        assert_eq!(ldr_inst.operands[0], vreg(2)); // dst unchanged
        assert_eq!(ldr_inst.operands[1], vreg(0)); // base = SUB's source
        assert_eq!(ldr_inst.operands[2], imm(-8)); // displacement NEGATED
    }

    #[test]
    fn test_fold_sub_imm_into_str() {
        // SUB v1, v0, #16
        // STR v2, [v1, #0]  ->  STR v2, [v0, #-16]
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(16)]);
        let st = MachInst::new(AArch64Opcode::StrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub, st, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        assert_eq!(func.block(func.entry).insts.len(), 2);
        let st_inst = func.inst(InstId(1));
        assert_eq!(st_inst.operands[1], vreg(0));
        assert_eq!(st_inst.operands[2], imm(-16));
    }

    #[test]
    fn test_fold_sub_imm_combines_with_memory_offset_sign_aware() {
        // SUB v1, v0, #24
        // LDR v2, [v1, #8]   ->  LDR v2, [v0, #-16]
        // The combined offset is (-24) + 8, NOT (24 + 8) and NOT (-24 - 8):
        // this is the pin that catches a sign inversion in
        // `addr_producer_displacement`.
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(24)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        assert_eq!(func.block(func.entry).insts.len(), 2);
        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.operands[1], vreg(0));
        assert_eq!(ldr_inst.operands[2], imm(-16));
    }

    #[test]
    fn test_no_fold_sub_imm_below_signed_imm9_range() {
        // SUB v1, v0, #257
        // LDR v2, [v1, #0]
        // Combined = -257, one below the LDUR signed-imm9 floor (-256), and a
        // negative value can never take the scaled-unsigned form -> refuse.
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(257)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3, "unchanged");
        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.operands[1], vreg(1), "still uses the SUB result");
        assert_eq!(ldr_inst.operands[2], imm(0));
    }

    #[test]
    fn test_fold_sub_imm_at_signed_imm9_floor() {
        // SUB v1, v0, #256 -> combined -256, exactly the LDUR floor: folds.
        // Paired with the test above this brackets the encodable boundary.
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(256)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        assert_eq!(func.block(func.entry).insts.len(), 2);
        assert_eq!(func.inst(InstId(1)).operands[2], imm(-256));
    }

    #[test]
    fn test_no_fold_sub_imm_into_ldrb_scaled_unsigned_only() {
        // SUB v1, v0, #4
        // LDRB v2, [v1, #0]
        // LDRB's immediate form is SCALED UNSIGNED (0..4095) -- there is no
        // negative encoding for it in this pass's model, so the fold must be
        // refused even though the magnitude is tiny.
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(4)]);
        let ldrb = MachInst::new(AArch64Opcode::LdrbRI, vec![vreg32(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub, ldrb, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        assert_eq!(func.block(func.entry).insts.len(), 3);
        assert_eq!(func.inst(InstId(1)).operands[1], vreg(1));
    }

    #[test]
    fn test_no_fold_sub_imm_base_redefined_between_sub_and_load() {
        // MOV v0, v3        (initial def of the base)
        // SUB v1, v0, #8
        // MOV v0, v4        (base redefined between the SUB and the load)
        // LDR v2, [v1, #0]
        // RET
        //
        // Folding to `LDR v2, [v0, #-8]` would read the NEW v0; must not fold.
        let init = MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(3)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(8)]);
        let redef = MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(4)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![init, sub, redef, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5, "unchanged");
        let ldr_inst = func.inst(InstId(3));
        assert_eq!(ldr_inst.operands[1], vreg(1));
        assert_eq!(ldr_inst.operands[2], imm(0));
    }

    #[test]
    fn test_no_fold_sub_imm_multiple_uses() {
        // SUB v1, v0, #8 with TWO uses -> the SUB cannot be deleted, so the
        // single-def admission (`def_counts == 1` plus the use census) must
        // decline it exactly as it does for AddRI.
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let use2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub, ldr, use2, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        assert_eq!(func.block(func.entry).insts.len(), 4);
        assert_eq!(func.inst(InstId(1)).operands[1], vreg(1));
    }

    #[test]
    fn test_fold_sub_imm_idempotent() {
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func)); // folds
        assert!(!pass.run(&mut func)); // nothing left to do
    }

    #[test]
    fn test_addr_producer_displacement_is_sign_aware_and_fails_closed() {
        // The single point where the fold's sign model lives. AddRI is +imm,
        // SubRI is -imm, and EVERY other opcode is refused so an unmodelled
        // address producer can never be folded with a guessed sign.
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        assert_eq!(addr_producer_displacement(&add), Some(16));

        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(16)]);
        assert_eq!(addr_producer_displacement(&sub), Some(-16));

        // Unmodelled producers fail closed, including ones that also write a
        // GPR from a base + immediate.
        for op in [
            AArch64Opcode::MovR,
            AArch64Opcode::AddRR,
            AArch64Opcode::SubRR,
            AArch64Opcode::OrrRI,
        ] {
            let inst = MachInst::new(op, vec![vreg(1), vreg(0), imm(16)]);
            assert_eq!(
                addr_producer_displacement(&inst),
                None,
                "{op:?} must not be treated as an address producer"
            );
        }

        // i64::MIN cannot be negated; the SubRI arm must return None rather
        // than wrap to a positive displacement.
        let overflow = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(i64::MIN)]);
        assert_eq!(addr_producer_displacement(&overflow), None);
    }

    #[test]
    fn test_collect_sub_ri_defs_kill_switch_off_path_is_inert() {
        // The `TCG_NO_SUB_ADDR_FOLD` off-path. The env read itself is hoisted
        // into `sub_addr_fold_disabled()` at the call site (an in-process
        // `set_var` would race the parallel test threads), so the gate is
        // pinned here on the collector that consumes the decision: disabled ->
        // EMPTY map, which is what makes the pass byte-identical to the
        // pre-fold behaviour.
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![sub, ldr, ret]);
        let def_counts = count_vreg_defs(&func);

        let off = collect_sub_ri_defs(&func, &def_counts, false);
        assert!(off.is_empty(), "kill switch on -> no SubRI candidates");

        let on = collect_sub_ri_defs(&func, &def_counts, true);
        assert_eq!(on.len(), 1, "kill switch off -> the SubRI is a candidate");
        let (vr, def) = on.iter().next().unwrap();
        assert_eq!(*vr, VReg::new(1, RegClass::Gpr64));
        assert_eq!(def.inst_id, InstId(0));
        assert_eq!(def.position, 0);
    }

    #[test]
    fn test_collect_sub_ri_defs_skips_multiply_defined_vregs() {
        // Two SubRI defs of the same vreg: the map must stay empty, otherwise
        // the fold would rewrite the load against whichever def was recorded
        // last.
        let sub1 = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(8)]);
        let sub2 = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![sub1, sub2, ldr, ret]);
        let def_counts = count_vreg_defs(&func);
        assert!(collect_sub_ri_defs(&func, &def_counts, true).is_empty());

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 4);
    }

    // ---- Non-ADD definitions ----

    #[test]
    fn test_no_fold_non_add_def() {
        // MOV v1, v0
        // LDR v2, [v1, #0]
        // RET
        // v1 defined by MOV, not ADD -> no fold
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
    }

    // ---- Idempotency ----

    #[test]
    fn test_idempotent() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func)); // First run: folds
        assert!(!pass.run(&mut func)); // Second run: nothing to do
    }

    // ---- Proof annotation preservation ----

    #[test]
    fn test_preserves_ldr_proof() {
        // ADD v1, v0, #16
        // LDR v2, [v1, #0] [InBounds]
        // RET
        // -> LDR v2, [v0, #16] [InBounds] — proof preserved
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.proof, Some(ProofAnnotation::InBounds));
    }

    // ---- Provenance preservation ----

    #[test]
    fn test_addr_mode_provenance_merges_folded_add_into_rewritten_load() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);
        let add_id = func.block(func.entry).insts[0];
        let ldr_id = func.block(func.entry).insts[1];
        let ret_id = func.block(func.entry).insts[2];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(30), &[add_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(31), &[ldr_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(32), &[ret_id], PassId::new("isel"));

        let mut pass = AddrModeFormation;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![ldr_id, ret_id]);

        let ldr_inst = func.inst(ldr_id);
        assert_eq!(ldr_inst.operands[1], vreg(0));
        assert_eq!(ldr_inst.operands[2], imm(16));

        let ldr_entry = provenance.get_entry(ldr_id).unwrap();
        assert!(ldr_entry.trust_ir_origins.contains(&TrustIrInstId(30)));
        assert!(ldr_entry.trust_ir_origins.contains(&TrustIrInstId(31)));
        let transform = ldr_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("addr-mode"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![add_id, ldr_id],
            }
        );
        assert!(ldr_entry.is_active());

        assert!(provenance.get_entry(add_id).is_none());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(30)).unwrap(),
            &[ldr_id]
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(31)).unwrap(),
            &[ldr_id]
        );

        assert_eq!(provenance.get_entry(ret_id).unwrap().transforms.len(), 1);
    }

    // ---- Edge cases ----

    #[test]
    fn test_max_valid_offset() {
        // ADD v1, v0, #32760 (max valid)
        // LDR v2, [v1, #0]
        // RET
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(32760)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.operands[2], imm(32760));
    }

    #[test]
    fn test_no_fold_large_unaligned_generic_offset() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(32759)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(
            block.insts.len(),
            3,
            "unencodable large unaligned fold must keep the ADD"
        );
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddRI);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::LdrRI);
        assert_eq!(func.inst(InstId(1)).operands[1], vreg(1));
    }

    #[test]
    fn test_just_over_max_offset() {
        // ADD v1, v0, #32761 (one over max)
        // LDR v2, [v1, #0]
        // RET
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(32761)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_zero_offset_add() {
        // ADD v1, v0, #0 + LDR v2, [v1, #8] -> LDR v2, [v0, #8]
        // (Peephole would normally remove this ADD, but if it reaches
        // addr-mode first, we can still fold it.)
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(0)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.operands[1], vreg(0));
        assert_eq!(ldr_inst.operands[2], imm(8));
    }

    #[test]
    fn test_multiple_folds_in_one_block() {
        // ADD v1, v0, #8
        // LDR v2, [v1, #0]   <- fold this
        // ADD v4, v3, #16
        // STR v5, [v4, #0]   <- fold this
        // RET
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(3), imm(16)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(5), vreg(4), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, ldr, add2, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        // Both ADDs deleted: LDR + STR + RET = 3
        assert_eq!(block.insts.len(), 3);

        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.operands[1], vreg(0));
        assert_eq!(ldr_inst.operands[2], imm(8));

        let str_inst = func.inst(InstId(3));
        assert_eq!(str_inst.operands[1], vreg(3));
        assert_eq!(str_inst.operands[2], imm(16));
    }

    #[test]
    fn test_no_fold_base_redefined_between_add_and_load() {
        // MOV v0, v3        (initial def of the base)
        // ADD v1, v0, #16
        // MOV v0, v4        (base redefined between the ADD and the load)
        // LDR v2, [v1, #0]
        // RET
        //
        // Folding to `LDR v2, [v0, #16]` would read the NEW v0; must not fold.
        let init = MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(3)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let redef = MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(4)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![init, add, redef, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let ldr_inst = func.inst(InstId(3));
        assert_eq!(ldr_inst.operands[1], vreg(1));
        assert_eq!(ldr_inst.operands[2], imm(0));
    }

    #[test]
    fn test_no_fold_add_rr_src_redefined_between_add_and_load() {
        // MOV v0, v3        (initial def of src1)
        // ADD v1, v0, v5
        // MOV v0, v4        (src1 redefined between the ADD and the load)
        // LDR v2, [v1, #0]
        // RET
        let init = MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(3)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(1), vreg(0), vreg(5)]);
        let redef = MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(4)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![init, add, redef, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let ldr_inst = func.inst(InstId(3));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRI);
        assert_eq!(ldr_inst.operands[1], vreg(1));
    }

    #[test]
    fn test_no_change_empty_function() {
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_str_base_is_use_not_def() {
        // Ensure that for STR [src, base, offset], the base (operand[1])
        // is correctly identified as a use, not a def.
        // ADD v1, v0, #8    (v1 is used once by STR as base)
        // STR v2, [v1, #0]  (v1 is base at index 1, v2 is src at index 0)
        // RET
        //
        // v1 use count: used by STR operand[1] = 1 use
        // v2 use count: used by STR operand[0] = 1 use (STR has no def, all are uses)
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        // ADD deleted, STR rewritten
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);

        let str_result = func.inst(InstId(1));
        assert_eq!(str_result.operands[1], vreg(0));
        assert_eq!(str_result.operands[2], imm(8));
    }

    // ================================================================
    // Early proof-use pair address formation
    // ================================================================

    #[test]
    fn test_early_store_pair_folds_private_add_ri_chains_to_same_base_strri() {
        // ADD v3, v2, #0
        // STR v0, [v3, #0]
        // ADD v4, v2, #8
        // STR v1, [v4, #0]
        // RET
        //
        // -> STR v0, [v2, #0]
        //    STR v1, [v2, #8]
        //    RET
        let add0 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(0)]);
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(3), imm(0)]);
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(2), imm(8)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(4), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add0, str0, add1, str1, ret]);

        let mut pass = AddrModeEarlyFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(1), InstId(3), InstId(4)]);

        let first = func.inst(InstId(1));
        assert_eq!(first.opcode, AArch64Opcode::StrRI);
        assert_eq!(first.operands, vec![vreg(0), vreg(2), imm(0)]);

        let second = func.inst(InstId(3));
        assert_eq!(second.opcode, AArch64Opcode::StrRI);
        assert_eq!(second.operands, vec![vreg(1), vreg(2), imm(8)]);
    }

    #[test]
    fn test_early_store_pair_stops_at_shared_one_use_root() {
        // ADD v3, v2, #16    ; shared by both address chains, so it stays.
        // ADD v4, v3, #0
        // STR v0, [v4, #0]
        // ADD v5, v3, #8
        // STR v1, [v5, #0]
        //
        // -> ADD v3, v2, #16
        //    STR v0, [v3, #0]
        //    STR v1, [v3, #8]
        let shared = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(16)]);
        let add0 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(3), imm(0)]);
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(4), imm(0)]);
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(8)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(5), imm(0)]);
        let mut func = make_func_with_insts(vec![shared, add0, str0, add1, str1]);

        let mut pass = AddrModeEarlyFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(0), InstId(2), InstId(4)]);
        assert_eq!(
            func.inst(InstId(2)).operands,
            vec![vreg(0), vreg(3), imm(0)]
        );
        assert_eq!(
            func.inst(InstId(4)).operands,
            vec![vreg(1), vreg(3), imm(8)]
        );
    }

    #[test]
    fn test_early_store_pair_folds_private_madd_const_offsets_to_same_base_strri() {
        // Constant-index trust_ir GEPs reach early proof optimization as:
        //   MADD tmp, index_const, elem_size_const, base
        //   STR value, [tmp, #0]
        // Canonicalize adjacent private chains to same-base immediates so
        // proof-opts can consume pair-start alignment facts.
        let idx2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(5), imm(2)]);
        let scale0 = MachInst::new(AArch64Opcode::Movz, vec![vreg(6), imm(8)]);
        let madd0 = MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(7), vreg(5), vreg(6), vreg(2)],
        );
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(7), imm(0)]);
        let idx3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(8), imm(3)]);
        let scale1 = MachInst::new(AArch64Opcode::Movz, vec![vreg(9), imm(8)]);
        let madd1 = MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(10), vreg(8), vreg(9), vreg(2)],
        );
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![
            idx2, scale0, madd0, str0, idx3, scale1, madd1, str1, ret,
        ]);

        let mut pass = AddrModeEarlyFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(3), InstId(7), InstId(8)]);

        let first = func.inst(InstId(3));
        assert_eq!(first.opcode, AArch64Opcode::StrRI);
        assert_eq!(first.operands, vec![vreg(0), vreg(2), imm(16)]);

        let second = func.inst(InstId(7));
        assert_eq!(second.opcode, AArch64Opcode::StrRI);
        assert_eq!(second.operands, vec![vreg(1), vreg(2), imm(24)]);
    }

    #[test]
    fn test_early_store_pair_rejects_madd_const_offsets_with_redefined_base() {
        let base0 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(64)]);
        let idx2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(5), imm(2)]);
        let scale0 = MachInst::new(AArch64Opcode::Movz, vec![vreg(6), imm(8)]);
        let madd0 = MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(7), vreg(5), vreg(6), vreg(2)],
        );
        let base1 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(96)]);
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(7), imm(0)]);
        let idx3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(8), imm(3)]);
        let scale1 = MachInst::new(AArch64Opcode::Movz, vec![vreg(9), imm(8)]);
        let madd1 = MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(10), vreg(8), vreg(9), vreg(2)],
        );
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]);
        let mut func = make_func_with_insts(vec![
            base0, idx2, scale0, madd0, base1, str0, idx3, scale1, madd1, str1,
        ]);

        let mut pass = AddrModeEarlyFormation;
        assert!(!pass.run(&mut func));

        assert_eq!(
            func.block(func.entry).insts,
            vec![
                InstId(0),
                InstId(1),
                InstId(2),
                InstId(3),
                InstId(4),
                InstId(5),
                InstId(6),
                InstId(7),
                InstId(8),
                InstId(9),
            ]
        );
        assert_eq!(
            func.inst(InstId(5)).operands,
            vec![vreg(0), vreg(7), imm(0)]
        );
        assert_eq!(
            func.inst(InstId(9)).operands,
            vec![vreg(1), vreg(10), imm(0)]
        );
    }

    #[test]
    fn test_early_store_pair_rejects_madd_const_offsets_with_invalid_movz_constant() {
        let idx2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(5), imm(2)]);
        let scale0 = MachInst::new(AArch64Opcode::Movz, vec![vreg(6), imm(0x1_0000)]);
        let madd0 = MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(7), vreg(5), vreg(6), vreg(2)],
        );
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(7), imm(0)]);
        let idx3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(8), imm(3)]);
        let scale1 = MachInst::new(AArch64Opcode::Movz, vec![vreg(9), imm(8)]);
        let madd1 = MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(10), vreg(8), vreg(9), vreg(2)],
        );
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]);
        let mut func =
            make_func_with_insts(vec![idx2, scale0, madd0, str0, idx3, scale1, madd1, str1]);

        let mut pass = AddrModeEarlyFormation;
        assert!(!pass.run(&mut func));

        assert_eq!(
            func.block(func.entry).insts,
            vec![
                InstId(0),
                InstId(1),
                InstId(2),
                InstId(3),
                InstId(4),
                InstId(5),
                InstId(6),
                InstId(7),
            ]
        );
        assert_eq!(
            func.inst(InstId(3)).operands,
            vec![vreg(0), vreg(7), imm(0)]
        );
        assert_eq!(
            func.inst(InstId(7)).operands,
            vec![vreg(1), vreg(10), imm(0)]
        );
    }

    #[test]
    fn test_early_store_pair_rejects_madd_const_offsets_with_gpr32_index() {
        let idx2 = MachInst::new(AArch64Opcode::Movz, vec![vreg32(5), imm(2)]);
        let scale0 = MachInst::new(AArch64Opcode::Movz, vec![vreg(6), imm(8)]);
        let madd0 = MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(7), vreg32(5), vreg(6), vreg(2)],
        );
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(7), imm(0)]);
        let idx3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(8), imm(3)]);
        let scale1 = MachInst::new(AArch64Opcode::Movz, vec![vreg(9), imm(8)]);
        let madd1 = MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(10), vreg(8), vreg(9), vreg(2)],
        );
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]);
        let mut func =
            make_func_with_insts(vec![idx2, scale0, madd0, str0, idx3, scale1, madd1, str1]);

        let mut pass = AddrModeEarlyFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(
            func.inst(InstId(3)).operands,
            vec![vreg(0), vreg(7), imm(0)]
        );
        assert_eq!(
            func.inst(InstId(7)).operands,
            vec![vreg(1), vreg(10), imm(0)]
        );
    }

    #[test]
    fn test_early_store_pair_does_not_fold_single_store_chain() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(8)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(3), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, str_inst, ret]);

        let mut pass = AddrModeEarlyFormation;
        assert!(!pass.run(&mut func));

        assert_eq!(
            func.block(func.entry).insts,
            vec![InstId(0), InstId(1), InstId(2)]
        );
        assert_eq!(
            func.inst(InstId(1)).operands,
            vec![vreg(0), vreg(3), imm(0)]
        );
    }

    #[test]
    fn test_early_pair_folds_private_add_ri_chains_to_same_base_ldri() {
        let add0 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(0)]);
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(3), imm(0)]);
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(2), imm(8)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(4), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add0, ldr0, add1, ldr1, ret]);

        let mut pass = AddrModeEarlyFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(1), InstId(3), InstId(4)]);

        let first = func.inst(InstId(1));
        assert_eq!(first.opcode, AArch64Opcode::LdrRI);
        assert_eq!(first.operands, vec![vreg(0), vreg(2), imm(0)]);

        let second = func.inst(InstId(3));
        assert_eq!(second.opcode, AArch64Opcode::LdrRI);
        assert_eq!(second.operands, vec![vreg(1), vreg(2), imm(8)]);
    }

    #[test]
    fn test_early_store_pair_rejects_non_chain_instruction_between_stores() {
        let add0 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(0)]);
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(3), imm(0)]);
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(9), vreg(8)]);
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(2), imm(8)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(4), imm(0)]);
        let mut func = make_func_with_insts(vec![add0, str0, mov, add1, str1]);

        let mut pass = AddrModeEarlyFormation;
        assert!(!pass.run(&mut func));

        assert_eq!(
            func.block(func.entry).insts,
            vec![InstId(0), InstId(1), InstId(2), InstId(3), InstId(4)]
        );
        assert_eq!(
            func.inst(InstId(1)).operands,
            vec![vreg(0), vreg(3), imm(0)]
        );
        assert_eq!(
            func.inst(InstId(4)).operands,
            vec![vreg(1), vreg(4), imm(0)]
        );
    }

    #[test]
    fn test_early_store_pair_rejects_gpr32_store_value() {
        let add0 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(0)]);
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg32(0), vreg(3), imm(0)]);
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(2), imm(8)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(4), imm(0)]);
        let mut func = make_func_with_insts(vec![add0, str0, add1, str1]);

        let mut pass = AddrModeEarlyFormation;
        assert!(!pass.run(&mut func));

        assert_eq!(
            func.block(func.entry).insts,
            vec![InstId(0), InstId(1), InstId(2), InstId(3)]
        );
    }

    #[test]
    fn test_early_store_pair_rejects_over_limit_chain() {
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(2), imm(0)]);
        let mut insts = vec![str0];
        let mut current = 2;
        for depth in 0..=EARLY_ADDR_CHAIN_LIMIT {
            let next = 10 + depth as u32;
            let offset = if depth == 0 { 8 } else { 0 };
            insts.push(MachInst::new(
                AArch64Opcode::AddRI,
                vec![vreg(next), vreg(current), imm(offset)],
            ));
            current = next;
        }
        insts.push(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(1), vreg(current), imm(0)],
        ));
        let mut func = make_func_with_insts(insts);

        let mut pass = AddrModeEarlyFormation;
        assert!(!pass.run(&mut func));
    }

    // ================================================================
    // form_base_plus_reg tests
    // ================================================================

    #[test]
    fn test_fold_add_rr_into_ldr_ro() {
        // ADD v2, v0, v1     (v2 = v0 + v1)
        // LDR v3, [v2, #0]   (load from [v2])
        // RET
        // -> LDR v3, [v0, v1] (LdrRO), ADD deleted
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        // ADD deleted: LDR + RET = 2
        assert_eq!(block.insts.len(), 2);

        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRO);
        assert_eq!(ldr_inst.operands[0], vreg(3)); // dst unchanged
        assert_eq!(ldr_inst.operands[1], vreg(0)); // base = ADD src1
        assert_eq!(ldr_inst.operands[2], vreg(1)); // index = ADD src2
    }

    #[test]
    fn test_fold_add_rr_into_str_ro() {
        // ADD v2, v0, v1
        // STR v3, [v2, #0]
        // RET
        // -> STR v3, [v0, v1] (StrRO), ADD deleted
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(3), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);

        let str_result = func.inst(InstId(1));
        assert_eq!(str_result.opcode, AArch64Opcode::StrRO);
        assert_eq!(str_result.operands[0], vreg(3)); // src unchanged
        assert_eq!(str_result.operands[1], vreg(0)); // base = ADD src1
        assert_eq!(str_result.operands[2], vreg(1)); // index = ADD src2
    }

    #[test]
    fn test_fold_add_rr_source_loc_falls_back_to_add_when_memory_has_none() {
        let loc = source_loc(52);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_source_loc(loc);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(3), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let str_result = func.inst(InstId(1));
        assert_eq!(str_result.opcode, AArch64Opcode::StrRO);
        assert_eq!(str_result.source_loc, Some(loc));
    }

    #[test]
    fn test_fold_add_rr_source_loc_keeps_memory_loc_over_add_fallback() {
        let add_loc = source_loc(53);
        let mem_loc = source_loc(54);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_source_loc(add_loc);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(3), vreg(2), imm(0)])
            .with_source_loc(mem_loc);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let str_result = func.inst(InstId(1));
        assert_eq!(str_result.opcode, AArch64Opcode::StrRO);
        assert_eq!(str_result.source_loc, Some(mem_loc));
    }

    #[test]
    fn test_no_fold_add_rr_nonzero_offset() {
        // ADD v2, v0, v1
        // LDR v3, [v2, #8]   <- offset != 0, can't fold to reg-offset
        // RET
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3); // unchanged
    }

    #[test]
    fn test_no_fold_add_rr_multiple_uses() {
        // ADD v2, v0, v1
        // LDR v3, [v2, #0]
        // ADD v4, v2, v5    <- second use of v2
        // RET
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(0)]);
        let add2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(2), vreg(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, add2, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
    }

    #[test]
    fn test_fold_add_rr_ignores_same_id_different_class_def() {
        // ADD x2, x0, x1
        // ADD w2, w4, w5    <- same numeric id, different register class
        // LDR x3, [x2, #0]
        // RET
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let decoy = MachInst::new(AArch64Opcode::AddRR, vec![vreg32(2), vreg32(4), vreg32(5)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, decoy, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(
            pass.run(&mut func),
            "same numeric id in another class must not block the Gpr64 AddRR fold"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(1), InstId(2), InstId(3)]);
        assert_eq!(func.inst(InstId(1)).operands[0], vreg32(2));
        let ldr_inst = func.inst(InstId(2));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRO);
        assert_eq!(ldr_inst.operands, vec![vreg(3), vreg(0), vreg(1)]);
    }

    #[test]
    fn test_no_fold_duplicate_add_rr_defs() {
        // ADD v2, v0, v1
        // LDR v3, [v2, #0]
        // ADD v2, v4, v5    <- duplicate def of v2 must not be used as identity
        // RET
        let add1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(0)]);
        let add2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(4), vreg(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, ldr, add2, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRI);
        assert_eq!(ldr_inst.operands[1], vreg(2));
        assert_eq!(ldr_inst.operands[2], imm(0));
    }

    #[test]
    fn test_fold_add_rr_preserves_proof() {
        // ADD v2, v0, v1
        // LDR v3, [v2, #0] [InBounds]
        // RET
        // -> LDR v3, [v0, v1] [InBounds] — proof preserved
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(0)])
            .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRO);
        assert_eq!(ldr_inst.proof, Some(ProofAnnotation::InBounds));
    }

    #[test]
    fn test_fold_add_rr_idempotent() {
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func)); // First: folds
        assert!(!pass.run(&mut func)); // Second: nothing to do
    }

    #[test]
    fn test_mixed_imm_and_reg_folds() {
        // ADD v1, v0, #8
        // LDR v2, [v1, #0]   <- fold via AddRI (base+imm)
        // ADD v4, v3, v5
        // STR v6, [v4, #0]   <- fold via AddRR (base+reg)
        // RET
        let add_ri = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(8)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let add_rr = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(5)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(6), vreg(4), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add_ri, ldr, add_rr, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        // Both ADDs deleted: LDR + STR + RET = 3
        assert_eq!(block.insts.len(), 3);

        // LDR got base+imm fold
        let ldr_inst = func.inst(InstId(1));
        assert_eq!(ldr_inst.opcode, AArch64Opcode::LdrRI);
        assert_eq!(ldr_inst.operands[1], vreg(0));
        assert_eq!(ldr_inst.operands[2], imm(8));

        // STR got base+reg fold
        let str_result = func.inst(InstId(3));
        assert_eq!(str_result.opcode, AArch64Opcode::StrRO);
        assert_eq!(str_result.operands[1], vreg(3));
        assert_eq!(str_result.operands[2], vreg(5));
    }

    // ================================================================
    // form_pre_index / form_post_index tests
    // ================================================================

    #[test]
    fn test_pre_index_rewrites_adjacent_add_before_ldr_zero_offset() {
        // ADD v0, v0, #16  (in-place update, pre-index candidate)
        // LDR v1, [v0, #0]
        // RET
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)])
            .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(1), InstId(2)]);
        let inst = func.inst(InstId(1));
        assert_eq!(inst.opcode, AArch64Opcode::LdrPreIndex);
        assert_eq!(inst.operands, vec![vreg(1), vreg(0), imm(16)]);
        assert_eq!(inst.proof, Some(ProofAnnotation::InBounds));
    }

    #[test]
    fn test_post_index_rewrites_adjacent_ldr_before_add_zero_offset() {
        // LDR v1, [v0, #0]
        // ADD v0, v0, #16  (post-index candidate)
        // RET
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, add, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(0), InstId(2)]);
        let inst = func.inst(InstId(0));
        assert_eq!(inst.opcode, AArch64Opcode::LdrPostIndex);
        assert_eq!(inst.operands, vec![vreg(1), vreg(0), imm(16)]);
    }

    #[test]
    fn test_pre_index_rewrites_adjacent_add_before_str_zero_offset() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(-16)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(0), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(1), InstId(2)]);
        let inst = func.inst(InstId(1));
        assert_eq!(inst.opcode, AArch64Opcode::StrPreIndex);
        assert_eq!(inst.operands, vec![vreg(1), vreg(0), imm(-16)]);
    }

    #[test]
    fn test_post_index_rewrites_adjacent_str_before_add_zero_offset() {
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(0), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(-16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![str_inst, add, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(0), InstId(2)]);
        let inst = func.inst(InstId(0));
        assert_eq!(inst.opcode, AArch64Opcode::StrPostIndex);
        assert_eq!(inst.operands, vec![vreg(1), vreg(0), imm(-16)]);
    }

    #[test]
    fn test_pre_index_rejects_out_of_signed_imm9_range() {
        // ADD v0, v0, #300 (> 255, not encodable in 9-bit signed)
        // LDR v1, [v0, #0]
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(300)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let mut func = make_func_with_insts(vec![add, ldr]);

        assert!(!form_pre_index(&mut func, InstId(1), InstId(0), 0));
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::LdrRI);
    }

    #[test]
    fn test_pre_index_rejects_non_in_place_add() {
        // ADD v1, v0, #16 (dst != src, not an in-place update)
        // LDR v2, [v1, #0]
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let mut func = make_func_with_insts(vec![add, ldr]);

        assert!(!form_pre_index(&mut func, InstId(1), InstId(0), 0));
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::LdrRI);
    }

    #[test]
    fn test_single_writeback_rejects_nonzero_memory_offset() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 3);
        assert_eq!(
            func.inst(InstId(1)).operands,
            vec![vreg(1), vreg(0), imm(8)]
        );
    }

    #[test]
    fn test_single_writeback_rejects_transfer_base_overlap() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(0), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 3);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::LdrRI);
    }

    #[test]
    fn test_transfer_base_overlap_is_class_exact() {
        let same_id_different_class =
            MachInst::new(AArch64Opcode::LdrRI, vec![vreg32(0), vreg(0), imm(0)]);
        assert!(
            !transfer_base_overlap(&same_id_different_class),
            "same numeric id in another register class is not the writeback base"
        );

        let same_vreg = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(0), imm(0)]);
        assert!(transfer_base_overlap(&same_vreg));
    }

    // ================================================================
    // fold_multiuse_base_plus_imm: multi-use / cross-block base+imm fold
    // ================================================================

    #[test]
    fn test_multiuse_fold_same_block_two_mem_uses() {
        // ADD v1, v0, #16      (v0 is a live-in base)
        // LDR v2, [v1, #0]     use 1 of v1 (same block as ADD)
        // STR v3, [v1, #4]     use 2 of v1 (same block as ADD)
        // RET
        // Two intra-block mem uses (a struct-field base like Towers'
        // `&cell.next`): the ADD is deleted and both accesses share v0.
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(3), vreg(1), imm(4)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 3);
        assert_eq!(
            func.inst(InstId(1)).operands,
            vec![vreg(2), vreg(0), imm(16)]
        );
        assert_eq!(
            func.inst(InstId(2)).operands,
            vec![vreg(3), vreg(0), imm(20)]
        );
    }

    #[test]
    fn test_multiuse_fold_multidef_base_off_path_redefinition() {
        // Treesort's Insert shape, but with the far use a STORE-only block
        // (no pointer-chase): the base v0 is multiply defined, yet neither
        // def lies on a path from the AddRI to a rewritten use without
        // re-executing the AddRI.
        //
        // entry: MOV v0, v9; br header
        // header: ADD v1, v0, #8 ; LDR v2, [v1, #0] ; bcond latch else exit
        // latch: MOV v0, v8 ; br header       (redefines v0, then re-adds;
        //                                      v8 is unrelated to the load,
        //                                      so this is not a pointer chase)
        // exit:  STR v3, [v1, #4] ; RET       (v0 unchanged since the ADD)
        let mut func = MachFunction::new(
            "test_multiuse_multidef".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        let init = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(9)]));
        let b0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        func.append_inst(entry, init);
        func.append_inst(entry, b0);
        func.add_edge(entry, header);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(8)],
        ));
        let ldr = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(1), imm(0)],
        ));
        let bc = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(1), MachOperand::Block(latch)],
        ));
        let b1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        func.append_inst(header, add);
        func.append_inst(header, ldr);
        func.append_inst(header, bc);
        func.append_inst(header, b1);
        func.add_edge(header, latch);
        func.add_edge(header, exit);

        let redef = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(8)]));
        let b2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        func.append_inst(latch, redef);
        func.append_inst(latch, b2);
        func.add_edge(latch, header);

        let str_inst = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(3), vreg(1), imm(4)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, str_inst);
        func.append_inst(exit, ret);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        // AddRI deleted; both uses rewritten onto v0.
        assert_eq!(func.block(header).insts, vec![ldr, bc, b1]);
        assert_eq!(func.inst(ldr).operands, vec![vreg(2), vreg(0), imm(8)]);
        assert_eq!(
            func.inst(str_inst).operands,
            vec![vreg(3), vreg(0), imm(12)]
        );
    }

    #[test]
    fn test_multiuse_no_fold_multidef_base_dirty_path() {
        // Same CFG as above, but the far use sits BEHIND the latch's
        // redefinition of v0: latch redefines v0 and branches to exit
        // without re-executing the AddRI, so exit's entry is dirty.
        //
        // entry: MOV v0, v9; br header
        // header: ADD v1, v0, #8 ; LDR v2, [v1, #0] ; bcond latch else exit
        // latch: MOV v0, v8 ; bcond header else exit   (dirty edge to exit;
        //                                                v8 unrelated to the
        //                                                load, so it is the
        //                                                cleanliness dataflow
        //                                                that must reject)
        // exit:  STR v3, [v1, #4] ; RET
        let mut func = MachFunction::new(
            "test_multiuse_multidef_dirty".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        let init = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(9)]));
        let b0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        func.append_inst(entry, init);
        func.append_inst(entry, b0);
        func.add_edge(entry, header);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(8)],
        ));
        let ldr = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(1), imm(0)],
        ));
        let bc = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(1), MachOperand::Block(latch)],
        ));
        let b1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        func.append_inst(header, add);
        func.append_inst(header, ldr);
        func.append_inst(header, bc);
        func.append_inst(header, b1);
        func.add_edge(header, latch);
        func.add_edge(header, exit);

        let redef = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(8)]));
        let bc2 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(1), MachOperand::Block(header)],
        ));
        let b2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        func.append_inst(latch, redef);
        func.append_inst(latch, bc2);
        func.append_inst(latch, b2);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);

        let str_inst = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(3), vreg(1), imm(4)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, str_inst);
        func.append_inst(exit, ret);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(header).insts, vec![add, ldr, bc, b1]);
        assert_eq!(func.inst(ldr).operands, vec![vreg(2), vreg(1), imm(0)]);
        assert_eq!(func.inst(str_inst).operands, vec![vreg(3), vreg(1), imm(4)]);
    }

    #[test]
    fn test_multiuse_no_fold_multidef_base_pointer_chase() {
        // Treesort's exact shape: the rewritten LOAD's result feeds the
        // latch's redefinition of the base (`node = node->left`). Sound to
        // fold, but the profitability cut keeps the AddRI so the load result
        // can still coalesce with the loop-carried pointer.
        //
        // entry: MOV v0, v9; br header
        // header: ADD v1, v0, #8 ; LDR v2, [v1, #0] ; bcond latch else exit
        // latch: MOV v0, v2 ; br header        (v2 = rewritten load's dst)
        // exit:  STR v3, [v1, #0] ; RET
        let mut func = MachFunction::new(
            "test_multiuse_chase".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        let init = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(9)]));
        let b0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        func.append_inst(entry, init);
        func.append_inst(entry, b0);
        func.add_edge(entry, header);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(8)],
        ));
        let ldr = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(1), imm(0)],
        ));
        let bc = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(1), MachOperand::Block(latch)],
        ));
        let b1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        func.append_inst(header, add);
        func.append_inst(header, ldr);
        func.append_inst(header, bc);
        func.append_inst(header, b1);
        func.add_edge(header, latch);
        func.add_edge(header, exit);

        let redef = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(2)]));
        let b2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        func.append_inst(latch, redef);
        func.append_inst(latch, b2);
        func.add_edge(latch, header);

        let str_inst = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(3), vreg(1), imm(0)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, str_inst);
        func.append_inst(exit, ret);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(header).insts, vec![add, ldr, bc, b1]);
        assert_eq!(func.inst(ldr).operands, vec![vreg(2), vreg(1), imm(0)]);
    }

    #[test]
    fn test_multiuse_fold_cross_block_dominating_base() {
        // entry: ADD v1, v0, #8   (v0 live-in), br body
        // body:  LDR v2, [v1, #0]
        //        STR v3, [v1, #4]
        //        RET
        // entry dominates body -> fold both uses to base v0; ADD deleted.
        let mut func = MachFunction::new(
            "test_multiuse_cross".to_string(),
            Signature::new(vec![], vec![]),
        );
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(8)],
        ));
        func.append_inst(func.entry, add);
        let body = func.create_block();
        func.add_edge(func.entry, body);
        let ldr = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(1), imm(0)],
        ));
        let str_inst = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(3), vreg(1), imm(4)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(body, ldr);
        func.append_inst(body, str_inst);
        func.append_inst(body, ret);

        let mut pass = AddrModeFormation;
        assert!(pass.run(&mut func));

        assert_eq!(func.block(func.entry).insts.len(), 0); // ADD deleted
        assert_eq!(func.inst(ldr).operands, vec![vreg(2), vreg(0), imm(8)]);
        assert_eq!(
            func.inst(str_inst).operands,
            vec![vreg(3), vreg(0), imm(12)]
        );
    }

    #[test]
    fn test_multiuse_no_fold_when_base_not_dominating() {
        // entry: br body        (no ADD here; v0 base defined in body)
        // body:  ADD v1, v0, #8
        //        LDR v2, [v1, #0]
        // other: STR v3, [v1, #4]   (NOT dominated by body)
        // The use in `other` is not dominated by the AddRI in `body`, so the
        // candidate is rejected wholesale (fail-closed): nothing folds.
        let mut func = MachFunction::new(
            "test_multiuse_nodom".to_string(),
            Signature::new(vec![], vec![]),
        );
        // entry falls through to body and other.
        let body = func.create_block();
        let other = func.create_block();
        func.add_edge(func.entry, body);
        func.add_edge(func.entry, other);
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(8)],
        ));
        let ldr = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(1), imm(0)],
        ));
        let str_inst = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(3), vreg(1), imm(4)],
        ));
        func.append_inst(body, add);
        func.append_inst(body, ldr);
        func.append_inst(other, str_inst);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));

        // Everything preserved.
        assert_eq!(func.inst(add).opcode, AArch64Opcode::AddRI);
        assert_eq!(func.inst(ldr).operands, vec![vreg(2), vreg(1), imm(0)]);
        assert_eq!(func.inst(str_inst).operands, vec![vreg(3), vreg(1), imm(4)]);
    }

    #[test]
    fn test_multiuse_no_fold_when_used_as_store_data() {
        // ADD v1, v0, #16
        // LDR v2, [v1, #0]     v1 as base (ok)
        // STR v1, [v4, #0]     v1 as STORED DATA (not a base) -> reject all
        // RET
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(4), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 4);
        assert_eq!(
            func.inst(InstId(1)).operands,
            vec![vreg(2), vreg(1), imm(0)]
        );
    }

    #[test]
    fn test_multiuse_no_fold_when_used_arithmetically() {
        // ADD v1, v0, #16
        // LDR v2, [v1, #0]     base use (ok)
        // ADD v3, v1, #4       arithmetic use of v1 -> reject all
        // STR v3, [v5, #0]
        // RET
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(1), imm(4)]);
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(3), vreg(5), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr, add2, str_inst, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 5);
    }

    #[test]
    fn test_multiuse_no_fold_when_one_offset_unencodable() {
        // ADD v1, v0, #32760
        // LDR v2, [v1, #0]     combined 32760 (ok alone)
        // LDR v3, [v1, #16]    combined 32776 > max -> reject the WHOLE candidate
        // RET
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(32760)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let ldr2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(1), imm(16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ldr1, ldr2, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 4);
        assert_eq!(
            func.inst(InstId(1)).operands,
            vec![vreg(2), vreg(1), imm(0)]
        );
        assert_eq!(
            func.inst(InstId(2)).operands,
            vec![vreg(3), vreg(1), imm(16)]
        );
    }

    #[test]
    fn test_multiuse_no_fold_when_base_multiply_defined() {
        // MOV v0, v8          def 1 of v0
        // ADD v1, v0, #16     v1 = v0(def1) + 16
        // LDR v2, [v1, #0]    use
        // MOV v0, v9          def 2 of v0  -> base has two defs
        // LDR v6, [v1, #4]    use after v0 reassigned
        // RET
        // Folding the second use to [v0, #20] would read v0's *second* def, a
        // different value. The def_counts>1 guard rejects the candidate.
        let mov0 = MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(8)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(16)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(0)]);
        let mov1 = MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(9)]);
        let ldr2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(6), vreg(1), imm(4)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov0, add, ldr1, mov1, ldr2, ret]);

        let mut pass = AddrModeFormation;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 6);
        assert_eq!(
            func.inst(InstId(2)).operands,
            vec![vreg(2), vreg(1), imm(0)]
        );
        assert_eq!(
            func.inst(InstId(4)).operands,
            vec![vreg(6), vreg(1), imm(4)]
        );
    }

    #[test]
    fn test_multiuse_provenance_and_deletion() {
        // entry: ADD v1, v0, #16, br body   body: LDR v2,[v1,#0]; STR v3,[v1,#4]
        // (cross-block so the fold's benefit gate fires).
        let mut func = MachFunction::new(
            "test_multiuse_prov".to_string(),
            Signature::new(vec![], vec![]),
        );
        let add_id = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(16)],
        ));
        func.append_inst(func.entry, add_id);
        let body = func.create_block();
        func.add_edge(func.entry, body);
        let ldr_id = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(1), imm(0)],
        ));
        let str_id = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(3), vreg(1), imm(4)],
        ));
        func.append_inst(body, ldr_id);
        func.append_inst(body, str_id);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(10), &[add_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(11), &[ldr_id], PassId::new("isel"));

        let mut pass = AddrModeFormation;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        // ADD deleted; its trust-ir origin absorbed by the first consumer.
        assert!(provenance.get_entry(add_id).is_none());
        assert!(!func.block(func.entry).insts.contains(&add_id));
        assert_eq!(func.inst(ldr_id).operands, vec![vreg(2), vreg(0), imm(16)]);
        assert_eq!(func.inst(str_id).operands, vec![vreg(3), vreg(0), imm(20)]);
    }
}
