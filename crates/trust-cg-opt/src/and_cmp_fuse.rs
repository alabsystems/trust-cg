//! `AND Rd, Rn, #imm` + `CMP Rd, #0`  ->  `TST Rn, #imm`
//!
//! AArch64 `TST Rn, #imm` is `ANDS XZR, Rn, #imm`: it computes the mask and sets
//! NZCV without materializing the result. When a masked value is only tested
//! against zero, the AND and the CMP collapse into one instruction.
//!
//! Measured worth on `p2_collatz`, whose hot loop is exactly this shape. The
//! emitted binary was patched in place -- `and x0,x2,#1` / `cmp x0,#0` replaced
//! by `tst x2,#1` / `nop`, identical layout, registers and symbols, exactly one
//! instruction changed semantically:
//!
//! ```text
//! trust-cg 245ms  ->  patched 153ms  ->  LLVM 155ms
//! ```
//!
//! One instruction closed the whole 1.55x gap and slightly beat LLVM.
//!
//! # THE C-FLAG HAZARD — read before touching the guard
//!
//! **`ANDS` CLEARS the C flag. `SUBS #0` SETS it.**
//!
//! So this rewrite is NOT unconditionally valid, and when it is wrong the
//! symptom is a silently mis-taken branch, not a crash. `CMP Rd,#0` is
//! `SUBS XZR, Rd, #0`, which always produces C=1; `TST` always produces C=0.
//! Every other flag (N, Z, V) agrees between the two forms -- V is 0 for both,
//! N and Z describe the same value -- so C is the entire difference.
//!
//! The pass therefore fires only when it can prove NO consumer of those flags
//! observes C. Conditions that read C are exactly:
//!
//! | cond   | meaning                     |
//! |--------|-----------------------------|
//! | HS/CS  | C == 1                      |
//! | LO/CC  | C == 0                      |
//! | HI     | C == 1 && Z == 0            |
//! | LS     | C == 0 \|\| Z == 1          |
//!
//! `ADC`/`SBC` are worse: they consume C arithmetically with no condition code
//! at all, so they are rejected outright rather than inspected.
//!
//! This mirrors how [`crate::shift_alu_fuse`] calls out SUB non-commutativity:
//! the guard is the pass, and the rewrite is the easy part.
//!
//! # Fail-closed conditions
//!
//! All must hold, and anything unrecognized bails:
//!
//! 1. `t` (the AND result) is read exactly ONCE function-wide, by this CMP. If
//!    the masked value is live, only an ANDS-with-destination would do, which is
//!    out of scope here.
//! 2. The AND is the reaching definition of `t` at the CMP, in the same block.
//! 3. `Rn` is not redefined between the AND and the CMP -- its read moves down.
//! 4. The CMP immediate is exactly 0.
//! 5. The mask has a valid AArch64 logical-immediate encoding. (The encoder
//!    also fails closed on this; checking here keeps us from rewriting into
//!    something unencodable.)
//! 6. **No flag consumer reads C** (see above), proven by
//!    `flags_safe_after`.
//!
//! Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    VReg,
};

use crate::pass_manager::MachinePass;

/// AND+CMP -> TST fusion pass.
pub struct AndCmpFuse;

impl MachinePass for AndCmpFuse {
    fn name(&self) -> &str {
        "and-cmp-fuse"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_and_cmp_fuse(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_and_cmp_fuse(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_and_cmp_fuse(func, Some(provenance))
    }
}

fn and_cmp_fuse_pass_id() -> PassId {
    PassId::new("and-cmp-fuse")
}

/// Kill switch: set `TCG_NO_AND_CMP_FUSE` (any value) to disable.
fn and_cmp_fuse_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_AND_CMP_FUSE").is_none()
}

/// Condition codes that observe the C flag: HS(0b0010), LO(0b0011),
/// HI(0b1000), LS(0b1001). See the module docs -- this is the whole reason the
/// pass needs a guard.
fn cond_reads_carry(cond: i64) -> bool {
    matches!(cond & 0xF, 0b0010 | 0b0011 | 0b1000 | 0b1001)
}

/// Operand index carrying the condition code, per opcode.
///
/// `None` means "this reads flags but I cannot locate its condition" — which
/// includes `Adc`/`Sbc`, who read C arithmetically and have no condition at all.
/// Callers must treat `None` as UNSAFE, never as "no condition to check".
fn cond_operand_index(opcode: AArch64Opcode) -> Option<usize> {
    use AArch64Opcode::*;
    match opcode {
        BCond | Bcc => Some(0),
        CSet => Some(1),
        Csel | Csinc | Csinv | Csneg => Some(3),
        _ => None,
    }
}

/// Is this instruction a consumer of NZCV?
fn is_flag_consumer(inst: &MachInst) -> bool {
    crate::effects::reads_flags(inst.opcode)
        || matches!(inst.opcode, AArch64Opcode::BCond | AArch64Opcode::Bcc)
}

/// Blocks reachable from `block` according to the authoritative CFG.
///
/// Do not reconstruct this from block operands: a conditional branch can name
/// only its taken edge while the fallthrough exists solely in `succs`. Missing
/// that edge can miss a carry-reading consumer and turn this optimization into
/// a silent miscompile.
fn successors_of(func: &MachFunction, block: BlockId) -> Vec<BlockId> {
    func.block(block).succs.clone()
}

fn block_ends_in_return(func: &MachFunction, block: BlockId) -> bool {
    func.block(block)
        .insts
        .last()
        .is_some_and(|&i| func.inst(i).opcode == AArch64Opcode::Ret)
}

/// Prove that no consumer of the flags defined at `block[cmp_pos]` observes C.
///
/// Walks forward from the CMP. A flag WRITER kills the definition and ends the
/// search successfully; a flag CONSUMER must carry a condition that does not
/// read C. If the block ends with the flags still live, every successor must
/// kill them before reading them -- checked transitively with a visited set.
///
/// Returns false on anything it cannot account for. That includes an
/// unrecognized flag reader, a missing/non-immediate condition operand, a
/// successor that reads flags first, and exhausting the traversal budget. This
/// is deliberately conservative: a missed fusion costs speed, a wrong one
/// miscompiles.
fn flags_safe_after(func: &MachFunction, block: BlockId, cmp_pos: usize) -> bool {
    // Scan the remainder of the defining block.
    let insts = &func.block(block).insts;
    for &inst_id in insts.iter().skip(cmp_pos + 1) {
        let inst = func.inst(inst_id);
        if is_flag_consumer(inst) {
            let Some(idx) = cond_operand_index(inst.opcode) else {
                // Adc/Sbc (read C directly) or an unrecognized reader.
                return false;
            };
            let Some(MachOperand::Imm(cond)) = inst.operands.get(idx) else {
                return false;
            };
            if cond_reads_carry(*cond) {
                return false;
            }
        }
        if crate::effects::writes_flags(inst.opcode) {
            // Flags redefined here; nothing downstream can see ours.
            return true;
        }
    }

    // Flags are still live at the end of the block. Every path out must
    // overwrite them before any read.
    //
    // A block with no successors is only safe if it genuinely RETURNS: NZCV is
    // not preserved across a call boundary and is not part of the return value,
    // so flags are dead at function exit. A successor-less block with no `Ret`
    // is something this analysis does not understand (malformed, or a terminator
    // shape not modelled here), and per this function's contract that bails
    // rather than guessing.
    let succs = successors_of(func, block);
    if succs.is_empty() {
        return block_ends_in_return(func, block);
    }

    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut work: Vec<BlockId> = succs;
    // Bound the walk; an irreducible or very large CFG bails rather than
    // spending compile time proving a peephole.
    let mut budget = 64usize;

    while let Some(b) = work.pop() {
        if !seen.insert(b) {
            continue;
        }
        if budget == 0 {
            return false;
        }
        budget -= 1;

        let mut killed = false;
        for &inst_id in &func.block(b).insts {
            let inst = func.inst(inst_id);
            if is_flag_consumer(inst) {
                let Some(idx) = cond_operand_index(inst.opcode) else {
                    return false;
                };
                let Some(MachOperand::Imm(cond)) = inst.operands.get(idx) else {
                    return false;
                };
                if cond_reads_carry(*cond) {
                    return false;
                }
            }
            if crate::effects::writes_flags(inst.opcode) {
                killed = true;
                break;
            }
        }
        if !killed {
            // Flags survive this block too — keep going. A successor-less block
            // must return, for the same reason as above.
            let next = successors_of(func, b);
            if next.is_empty() {
                if !block_ends_in_return(func, b) {
                    return false;
                }
            }
            for s in next {
                work.push(s);
            }
        }
    }
    true
}

/// Is `m` encodable as an AArch64 logical immediate at `width` bits?
/// Delegate to the shared encoder-side recognizer so this pass cannot drift
/// into accepting an immediate the backend later interprets differently.
fn is_logical_immediate(m: i64, width: u32) -> bool {
    crate::const_materialize::is_logical_immediate(m as u64, width)
}

fn run_and_cmp_fuse(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    if !and_cmp_fuse_enabled() {
        return false;
    }

    // Function-wide read counts: `t` must be single-use across the WHOLE
    // function, not merely this block.
    let read_counts = count_vreg_reads(func);

    let mut changed = false;
    for block_id in func.block_order.clone() {
        // AndRI defs seen so far in this block, invalidated on redefinition so a
        // hit is the true reaching definition.
        let mut and_defs: HashMap<VReg, (InstId, usize)> = HashMap::new();
        let mut last_def_pos: HashMap<VReg, usize> = HashMap::new();

        let insts = func.block(block_id).insts.clone();
        for (pos, &inst_id) in insts.iter().enumerate() {
            let inst = func.inst(inst_id).clone();

            if let Some(fused) = try_fuse(
                func,
                &inst,
                block_id,
                pos,
                &and_defs,
                &last_def_pos,
                &read_counts,
            ) {
                let (and_inst_id, tst) = fused;
                // Rewrite the CMP into the TST and neutralize the AND.
                let src_loc = func.inst(inst_id).source_loc.clone();
                let mut new_inst = tst;
                new_inst.source_loc = src_loc;
                *func.inst_mut(inst_id) = new_inst;
                *func.inst_mut(and_inst_id) = MachInst::new(AArch64Opcode::Nop, vec![]);
                if let Some(prov) = provenance.as_deref_mut() {
                    prov.record_merge(&[and_inst_id, inst_id], inst_id, and_cmp_fuse_pass_id());
                }
                changed = true;
            }

            // Maintain the def maps AFTER attempting the fuse. Use the shared
            // operand-role table: operand zero is not the only possible def
            // (LSE old-value destinations, post-index bases, paired loads), and
            // a missed source redefinition would move the TST read across a
            // write.
            let opcode = inst.opcode;
            crate::effects::aarch64_for_each_def_position(opcode, inst.operands.len(), |i| {
                let Some(MachOperand::VReg(v)) = inst.operands.get(i) else {
                    return;
                };
                last_def_pos.insert(*v, pos);
                if opcode == AArch64Opcode::AndRI && i == 0 {
                    and_defs.insert(*v, (inst_id, pos));
                } else {
                    and_defs.remove(v);
                }
            });
        }
    }
    changed
}

/// Attempt the rewrite at `inst` (a candidate `CmpRI`). Returns the AND's
/// `InstId` and the replacement `Tst` on success.
#[allow(clippy::too_many_arguments)]
fn try_fuse(
    func: &MachFunction,
    inst: &MachInst,
    block_id: BlockId,
    pos: usize,
    and_defs: &HashMap<VReg, (InstId, usize)>,
    last_def_pos: &HashMap<VReg, usize>,
    read_counts: &HashMap<VReg, u32>,
) -> Option<(InstId, MachInst)> {
    if inst.opcode != AArch64Opcode::CmpRI {
        return None;
    }
    if inst.operands.len() != 2 {
        return None;
    }
    // (4) immediate must be exactly zero
    let MachOperand::Imm(0) = inst.operands.get(1)? else {
        return None;
    };
    let MachOperand::VReg(t) = inst.operands.first()? else {
        return None;
    };

    // (1) single-use function-wide: this CMP is the only reader
    if read_counts.get(t).copied().unwrap_or(0) != 1 {
        return None;
    }

    // (2) reaching AND def in this block
    let (and_id, and_pos) = *and_defs.get(t)?;
    let and_inst = func.inst(and_id);
    if and_inst.opcode != AArch64Opcode::AndRI || and_inst.operands.len() != 3 {
        return None;
    }

    let MachOperand::VReg(src) = and_inst.operands.get(1)? else {
        return None;
    };
    let MachOperand::Imm(mask) = and_inst.operands.get(2)? else {
        return None;
    };

    // (3) source must not be redefined between the AND and the CMP
    if let Some(&d) = last_def_pos.get(src) {
        if d > and_pos {
            return None;
        }
    }

    // (5) Both operations must use the same scalar GPR width, and the mask
    // must be encodable at exactly that width. A malformed cross-width pair is
    // not something this local rewrite may reinterpret.
    if t.class != src.class {
        return None;
    }
    let width = reg_width(*t)?;
    if !is_logical_immediate(*mask, width) {
        return None;
    }

    // (6) THE C-FLAG GUARD
    if !flags_safe_after(func, block_id, pos) {
        return None;
    }

    Some((
        and_id,
        MachInst::new(
            AArch64Opcode::Tst,
            vec![MachOperand::VReg(*src), MachOperand::Imm(*mask)],
        ),
    ))
}

fn reg_width(v: VReg) -> Option<u32> {
    match v.class {
        trust_cg_ir::RegClass::Gpr32 => Some(32),
        trust_cg_ir::RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

fn count_vreg_reads(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            crate::effects::aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |i| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(i) {
                    *counts.entry(*v).or_insert(0) += 1;
                }
            });
        }
    }
    counts
}

#[cfg(test)]
mod tests;
