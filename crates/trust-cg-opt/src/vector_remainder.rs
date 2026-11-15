//! Remainder-loop detection shared by the reduction vectorizers.
//!
//! Every loop vectorizer here keeps the scalar loop as the REMAINDER of the
//! vector loop it builds: the vector latch advances the same iv, the vector
//! exit block reduces the NEON lanes into the same accumulator, and that exit
//! block becomes the scalar loop's new preheader. On the next fixpoint
//! iteration the remainder loop looks exactly like the original (same iv, acc
//! and bound), so a recognizer without a guard vectorizes it AGAIN — nesting
//! one zero-trip vector loop per iteration until the pass manager's iteration
//! cap (found on p7_sieve / v2_memfill, 2026-08-27; see the
//! `second_run_is_a_no_op` tests of every vectorizer).
//!
//! The one thing that distinguishes a remainder loop from a fresh one is its
//! preheader: only a vector exit block DEFINES the loop's accumulator from a
//! value extracted out of a NEON register (`NeonUmovGen`). A scalar reduction
//! loop's own preheader never does.

use crate::effects::{for_each_inst_def, for_each_inst_use};
use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, VReg};

/// Whether some instruction in `preheader` defines `acc` from a value that
/// derives — within that block, through at most `MAX_HOPS` single-def
/// links — from a `NeonUmovGen` lane extraction.
pub(crate) fn preheader_folds_neon_lane_into(
    func: &MachFunction,
    preheader: BlockId,
    acc: VReg,
) -> bool {
    const MAX_HOPS: u32 = 12;
    let block = func.block(preheader);
    // Last def of each vreg WITHIN the preheader (later defs shadow earlier
    // ones, matching what a use after them reads).
    let mut local_def: HashMap<u32, InstId> = HashMap::default();
    for &id in &block.insts {
        for_each_inst_def(func.inst(id), |d| {
            local_def.insert(d.id, id);
        });
    }
    fn uses_of(func: &MachFunction, id: InstId) -> Vec<VReg> {
        let mut v = Vec::new();
        for_each_inst_use(func.inst(id), |u| v.push(u));
        v
    }
    fn from_neon_lane(
        func: &MachFunction,
        local_def: &HashMap<u32, InstId>,
        v: VReg,
        hops: u32,
    ) -> bool {
        if hops > MAX_HOPS {
            return false;
        }
        let Some(&d) = local_def.get(&v.id) else {
            return false;
        };
        if func.inst(d).opcode == AArch64Opcode::NeonUmovGen {
            return true;
        }
        uses_of(func, d)
            .into_iter()
            .any(|s| s != v && from_neon_lane(func, local_def, s, hops + 1))
    }
    block.insts.iter().any(|&id| {
        let mut defines_acc = false;
        for_each_inst_def(func.inst(id), |d| defines_acc |= d == acc);
        defines_acc
            && uses_of(func, id)
                .into_iter()
                .any(|s| from_neon_lane(func, &local_def, s, 0))
    })
}

/// Whether `iv` is advanced by more than one (`AddRI`/`SubRI iv, iv, k`, `k > 1`) in
/// a block within three CFG hops upstream of `preheader`, outside the loop
/// being recognized: the vector loop [`apply`] builds (`vx <- vh <- vl <- vb`)
/// sits exactly there, and a scalar unit-stride fill loop's own iv is only
/// ever advanced by one. Recognizes precisely the remainder loops this pass
/// leaves behind. Shared by the map-style vectorizers (fill, condstore,
/// fmap), whose loops carry no accumulator.
pub(crate) fn iv_is_vector_advanced_upstream(
    func: &MachFunction,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    iv: VReg,
) -> bool {
    let mut frontier = vec![preheader];
    let mut seen: HashSet<BlockId> = HashSet::default();
    for _ in 0..3 {
        let mut next = Vec::new();
        for b in frontier {
            if !seen.insert(b) {
                continue;
            }
            for &id in &func.block(b).insts {
                if loop_insts.contains(&id) {
                    continue;
                }
                let inst = func.inst(id);
                // `AddRI iv, iv, k` (ascending) or `SubRI iv, iv, k` (the
                // descending maps) with k > 1: a scalar loop steps by one.
                if matches!(inst.opcode, AArch64Opcode::AddRI | AArch64Opcode::SubRI)
                    && inst.operands.len() == 3
                    && inst.operands[0].as_vreg() == Some(iv)
                    && inst.operands[1].as_vreg() == Some(iv)
                    && inst.operands[2].as_imm().is_some_and(|k| k > 1)
                {
                    return true;
                }
            }
            next.extend(func.block(b).preds.iter().copied());
        }
        frontier = next;
    }
    false
}
