//! Demanded-bits rewrite for the xorshift idiom `y = x ^ (x << k)`.
//!
//! Shifting left by `k` cannot change bits below `k`, so
//!
//! ```text
//!     y = x ^ (x << k)   =>   y[i] == x[i]  for all i < k
//! ```
//!
//! Any consumer that reads ONLY bits `[0, k)` of `y` may therefore read `x`
//! instead. The rewrite does not remove an instruction — `y` is still computed
//! — it SHORTENS THE DEPENDENCY CHAIN feeding that consumer by one shifted-EOR.
//!
//! # Why this is worth a pass
//!
//! On `b1_mispredict` the loop is `s ^= s<<13; s ^= s>>7; s ^= s<<17`, and the
//! branch that decides the two arms tests `s & 1` — bit 0 of the FINAL value.
//! trust-cg computes that predicate from `s3`; LLVM computes it from `s2`, one
//! dependent operation earlier. Because `s3 = s2 ^ (s2 << 17)`, bits 0..16 agree,
//! and every predicate/index use in that loop reads only bits 0..11.
//!
//! Resolving a 50%-mispredicting branch one ALU op sooner was measured (assembly
//! isolation, core 19, min-of-7) at **-9ms of b1's 29ms gap**, independently
//! reproduced at -11ms. It is latency, not instruction count: the extra EOR is
//! free on an out-of-order core, but the BRANCH cannot resolve until its input
//! does.
//!
//! # Fail-closed conditions
//!
//! The producer must be exactly `EorRRLsl dst, a, b, #k` where `a` and `b` are
//! the SAME register — i.e. genuinely `x ^ (x << k)`, not a two-source EOR that
//! happens to carry a shift. A consumer is rewritten only when its demanded bit
//! range is provably within `[0, k)`:
//!
//! * `Tbz`/`Tbnz Rt, #b`      — demands bit `b`;            requires `b < k`
//! * `Ubfm Rd, Rn, #lsb,#imms`— demands `[lsb, imms]`;      requires `imms < k`
//! * `AndRI Rd, Rn, #m`       — demands the set bits of `m`; requires
//!                              `m < 2^k` (all set bits below `k`)
//!
//! Anything else — including any consumer this pass does not recognize — is left
//! alone. Reading a bit at or above `k` from `x` instead of `y` is a WRONG VALUE,
//! so the bit-range test is the entire correctness argument and every unproven
//! case keeps the original operand.
//!
//! Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0

use std::collections::HashMap;

use trust_cg_ir::{AArch64Opcode, MachFunction, MachOperand, ProvenanceMap, VReg};

use crate::pass_manager::MachinePass;

/// Xorshift demanded-bits pass.
pub struct XorshiftDemandedBits;

impl MachinePass for XorshiftDemandedBits {
    fn name(&self) -> &str {
        "xorshift-demanded-bits"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_pass(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_pass(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_pass(func, Some(provenance))
    }
}

/// Kill switch: set `TCG_NO_XORSHIFT_DEMANDED_BITS` (any value) to disable.
fn enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_XORSHIFT_DEMANDED_BITS").is_none()
}

/// Highest bit index this instruction reads from operand `op_idx`, or `None`
/// when the demanded range cannot be bounded (which must be treated as "all
/// bits").
fn highest_demanded_bit(inst: &trust_cg_ir::MachInst, op_idx: usize) -> Option<u32> {
    let imm = |i: usize| -> Option<i64> {
        match inst.operands.get(i) {
            Some(MachOperand::Imm(v)) => Some(*v),
            _ => None,
        }
    };
    match inst.opcode {
        // TBZ/TBNZ Rt, #bit, target — reads exactly one bit.
        AArch64Opcode::Tbz | AArch64Opcode::Tbnz if op_idx == 0 => u32::try_from(imm(1)?).ok(),
        // UBFM Rd, Rn, #immr, #imms — for the UBFX form the highest bit read is
        // `imms`. Only the source operand (index 1) is a candidate.
        AArch64Opcode::Ubfm if op_idx == 1 => u32::try_from(imm(3)?).ok(),
        // AND Rd, Rn, #mask — reads exactly the set bits of the mask.
        AArch64Opcode::AndRI if op_idx == 1 => {
            let m = imm(2)? as u64;
            if m == 0 {
                return None;
            }
            Some(63 - m.leading_zeros())
        }
        _ => None,
    }
}

fn run_pass(func: &mut MachFunction, _provenance: Option<&mut ProvenanceMap>) -> bool {
    if !enabled() {
        return false;
    }

    // Producers: dst -> (source x, shift k). Only `x ^ (x << k)`.
    let mut producers: HashMap<VReg, (VReg, u32)> = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::EorRRLsl || inst.operands.len() != 4 {
                continue;
            }
            let (
                Some(MachOperand::VReg(dst)),
                Some(MachOperand::VReg(a)),
                Some(MachOperand::VReg(b)),
            ) = (
                inst.operands.first(),
                inst.operands.get(1),
                inst.operands.get(2),
            )
            else {
                continue;
            };
            // Must be the SAME register on both sides: genuinely x ^ (x << k).
            if a != b {
                continue;
            }
            let Some(MachOperand::Imm(k)) = inst.operands.get(3) else {
                continue;
            };
            let Ok(k) = u32::try_from(*k) else { continue };
            if k == 0 {
                continue;
            }
            producers.insert(*dst, (*a, k));
        }
    }
    if producers.is_empty() {
        return false;
    }

    let mut changed = false;
    for block_id in func.block_order.clone() {
        for &inst_id in &func.block(block_id).insts.clone() {
            for op_idx in 0..func.inst(inst_id).operands.len() {
                let Some(MachOperand::VReg(y)) = func.inst(inst_id).operands.get(op_idx).cloned()
                else {
                    continue;
                };
                let Some(&(x, k)) = producers.get(&y) else {
                    continue;
                };
                let inst = func.inst(inst_id);
                let Some(hi) = highest_demanded_bit(inst, op_idx) else {
                    continue;
                };
                // The whole correctness argument: every demanded bit must lie
                // strictly below the shift amount, where y and x agree.
                if hi >= k {
                    continue;
                }
                // In-place operand swap: no instruction is created, merged or
                // deleted, so there is no provenance edge to record — the
                // instruction keeps its identity and its trust_ir origin.
                func.inst_mut(inst_id).operands[op_idx] = MachOperand::VReg(x);
                changed = true;
            }
        }
    }
    changed
}

#[cfg(test)]
mod tests;
