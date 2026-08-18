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

/// The REGISTER-operand arm (`AND Rd,Rn,Rm` + `CMP Rd,#0` -> `TST Rn,Rm`) is
/// **OPT-IN**: set `TCG_AND_CMP_FUSE_RR=1` to enable it. Default OFF, so the
/// shipped compiler is byte-identical to the immediate-only pass.
///
/// # Why it is off, when it is provably correct and removes real instructions
///
/// It works exactly as designed. On CoyoteBench/huffbench's encode inner loop
/// (1.5e9 iterations, measured, not estimated) it collapses
/// `and x1,x0,x6` + `cmp x1,#0` into `tst x0,x6`, removing **exactly
/// 1.50e9 dynamic instructions** -- 1 per iteration, as predicted to 3 digits
/// -- and shortening the chain into the dependent `cset`. stdout is bit-exact
/// against clang -O3 in all four arms tested.
///
/// **It buys nothing.** Corpus measurement (tcg-vs-tcg, same `.ll`, same driver
/// object, interleaved, min of 13, byte-identical null arm on every row; the
/// arm changes 6 of 65 SingleSource programs):
///
/// | program | enabled vs disabled (min/tmed) | dyn insts |
/// |---|---|---|
/// | huffbench | 1.0016 / 1.0013 (null 0.9991) | **-1.63%** |
/// | ReedSolomon | 1.0054 / 1.0064 | -0.01% |
/// | nsieve-bits | 1.0109 / 1.0069 | **+2.48%** |
/// | geomean (6) | 1.0030 / 1.0152 (null 1.0024 / 1.0104) | |
///
/// So it REMOVES 1.6% of huffbench's instructions for zero cycles, and COSTS
/// nsieve-bits 1.1% while ADDING 2.5% of its instructions -- the extra work is a
/// downstream reshuffle the peephole triggers, not anything it emits.
///
/// R3: huffbench's two alignment regimes DISAGREE IN SIGN (default 1.0015 min /
/// 1.0016 tmed against no-align 0.9771 / 0.9759), which is the loop_align
/// lottery signature. A lever whose sign flips with padding is not a lever.
///
/// This is the same lesson as `loop_align.rs` and the LICM depth-1 tier: on this
/// target, removing instructions that are not on a real resource bottleneck buys
/// nothing, and the layout perturbation dominates whatever it saves. Enable it
/// only with a per-program measurement in hand.
///
/// # It is parked for being useless, NOT for being unsafe
///
/// `torture_ship` was run a second time with `TCG_AND_CMP_FUSE_RR=1` and lands
/// **exactly on pin** -- 1114 PASS / 337 IMPORT_FAIL / **0 MISCOMPILE** / 0
/// LINKFAIL / 0 TIMEOUT / 1 TCG_PASSES_ORACLE_FAILS / 2 BOTH_FAIL_DIFF, the same
/// tuple as the default build. So the C-flag guard and the two-source
/// redefinition guard hold across 1114 programs with the arm live. Turning it on
/// costs correctness nothing; it simply does not pay.
fn and_cmp_fuse_rr_enabled() -> bool {
    crate::env_lock::var_os("TCG_AND_CMP_FUSE_RR").is_some()
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
        // FcselRR is the scalar-FP conditional select. `effects::reads_flags`
        // already classifies it as an NZCV reader, so omitting it here did not
        // make the pass unsound — it made it INERT: `flags_safe_after` treats an
        // unlocatable condition as unsafe and bails. Its condition operand sits
        // at index 3, exactly like the integer CSEL family (see the FcselRR arm
        // of the encoder, which reads `imm_val(inst, 3)`).
        Csel | Csinc | Csinv | Csneg | FcselRR => Some(3),
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
    if crate::env_lock::var_os("TCG_DUMP_ANDCMP").is_some() {
        let mut census: HashMap<String, usize> = HashMap::new();
        for &b in &func.block_order {
            for &i in &func.block(b).insts {
                let inst = func.inst(i);
                let k = format!("{:?}", inst.opcode);
                if k.starts_with("Cmp") || k.starts_with("CMP") || k.starts_with("And") {
                    let zero = matches!(inst.operands.get(1), Some(MachOperand::Imm(0)));
                    *census
                        .entry(format!("{k}{}", if zero { " #0" } else { "" }))
                        .or_default() += 1;
                }
            }
        }
        let mut v: Vec<_> = census.into_iter().collect();
        v.sort();
        for (k, n) in v {
            eprintln!("TCG_ANDCMP census {k} = {n}");
        }
    }
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
                let fusable_and = opcode == AArch64Opcode::AndRI
                    || (opcode == AArch64Opcode::AndRR && and_cmp_fuse_rr_enabled());
                if fusable_and && i == 0 {
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

    // DIAGNOSTIC (default off, TCG_DUMP_ANDCMP=1): why a CmpRI #0 whose operand
    // has a reaching AND was declined. Only such candidates are reported.
    let dump = crate::env_lock::var_os("TCG_DUMP_ANDCMP").is_some();
    macro_rules! decline {
        ($why:expr) => {{
            if dump {
                eprintln!(
                    "TCG_ANDCMP decline v{} and={:?} why={}",
                    t.id,
                    and_defs.get(t).map(|&(id, _)| func.inst(id).opcode),
                    $why
                );
            }
            return None;
        }};
    }

    // (1) single-use function-wide: this CMP is the only reader
    if read_counts.get(t).copied().unwrap_or(0) != 1 {
        decline!(format!(
            "not single-use: {} reads",
            read_counts.get(t).copied().unwrap_or(0)
        ));
    }

    // (2) reaching AND def in this block. Two admissible shapes:
    //   AndRI Rd, Rn, #imm  ->  TST Rn, #imm
    //   AndRR Rd, Rn, Rm    ->  TST Rn, Rm      (register arm)
    // `Tst` already encodes BOTH forms, so the register arm needs no new opcode.
    let (and_id, and_pos) = *and_defs.get(t)?;
    let and_inst = func.inst(and_id);
    let is_rr = match and_inst.opcode {
        AArch64Opcode::AndRI => false,
        AArch64Opcode::AndRR if and_cmp_fuse_rr_enabled() => true,
        _ => decline!(format!(
            "reaching def not a fusable AND: {:?}",
            and_inst.opcode
        )),
    };
    if and_inst.operands.len() != 3 {
        decline!("AND arity != 3");
    }

    let MachOperand::VReg(src) = and_inst.operands.get(1)? else {
        return None;
    };

    // The second operand, and the full set of source registers whose reads this
    // rewrite moves DOWN to the CMP's position.
    let (second, srcs): (MachOperand, Vec<VReg>) = if is_rr {
        let MachOperand::VReg(src2) = and_inst.operands.get(2)? else {
            return None;
        };
        (MachOperand::VReg(*src2), vec![*src, *src2])
    } else {
        let MachOperand::Imm(mask) = and_inst.operands.get(2)? else {
            return None;
        };
        // (5a) immediate arm only: the mask must be encodable at exactly this
        // width. The encoder also fails closed, but rewriting into something
        // unencodable is not this pass's business.
        if t.class != src.class {
            decline!("imm arm: class mismatch");
        }
        if !is_logical_immediate(*mask, reg_width(*t)?) {
            decline!("imm arm: mask not a logical immediate");
        }
        (MachOperand::Imm(*mask), vec![*src])
    };

    // (3) NO source may be redefined between the AND and the CMP. The register
    // arm has TWO reads to move, not one -- missing either would let the TST
    // read a value written after the AND.
    for s in &srcs {
        if let Some(&d) = last_def_pos.get(s)
            && d > and_pos
        {
            decline!(format!("source v{} redefined after the AND", s.id));
        }
    }

    // (5b) All operands must share one scalar GPR width. A malformed
    // cross-width triple is not something this local rewrite may reinterpret.
    if srcs.iter().any(|s| s.class != t.class) {
        decline!("cross-width operands");
    }
    reg_width(*t)?;

    // (6) THE C-FLAG GUARD -- unchanged, and it is the whole reason this pass
    // has a guard at all. `TST` is `ANDS XZR,..` and CLEARS C; `CMP Rd,#0` is
    // `SUBS XZR,Rd,#0` and SETS it. Identical for the register arm.
    if !flags_safe_after(func, block_id, pos) {
        decline!("C-FLAG GUARD: a consumer reads C");
    }

    Some((
        and_id,
        MachInst::new(AArch64Opcode::Tst, vec![MachOperand::VReg(*src), second]),
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
