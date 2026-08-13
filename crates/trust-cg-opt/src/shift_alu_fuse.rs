// trust-cg-opt - shift-into-ADD/SUB fusion peephole
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shift-into-ADD/SUB/EOR fusion — the LSL/LSR sibling of
//! [`crate::eor_rotate_fuse`] (LSL here, ROR there).
//!
//! Collapses a logical-shift-left feeding an add or subtract into a single
//! AArch64 shifted-register instruction. A statement like an explicit
//! `y + (x << k)` / `y - (x << k)`, or the two-instruction sequence the
//! mul-by-constant strength reduction ([`crate::mul_shift_reduce`]) emits
//! (`LslRI` + `AddRR`/`SubRR` for `x * (2^k ± 1)`), is a chain
//!
//! ```text
//!   t = LslRI(s, k)          ; LSL s, #k
//!   d = AddRR(x, t)          ; ADD x, t        (either order — ADD commutes)
//!   d = SubRR(x, t)          ; SUB x, t        (t MUST be the subtrahend)
//! ```
//!
//! which this pass rewrites to the two-become-one form
//!
//! ```text
//!   d = AddRRShift(x, s, k)  ; ADD d, x, s, LSL #k
//!   d = SubRRShift(x, s, k)  ; SUB d, x, s, LSL #k
//! ```
//!
//! (the `LslRI` is deleted, `Nop`ped in place). This removes one instruction AND
//! one serial node from the per-statement critical path.
//!
//! The LSR sibling is also fused (ADD only — see MINIMAL SURFACE below):
//!
//! ```text
//!   t = LsrRI(s, k)             ; LSR s, #k
//!   d = AddRR(x, t)             ; ADD x, t     (either order — ADD commutes)
//!   =>
//!   d = AddRRShiftLsr(x, s, k)  ; ADD d, x, s, LSR #k
//! ```
//!
//! This is the one remaining per-site difference of the srem/sdiv-by-constant
//! magic sequence vs clang: the sign-bit correction `lsr t, x, #31; add r, r, t`
//! becomes the single `add r, r, x, lsr #31` clang emits, and the udiv magic
//! add-back `lsr t, sub, #1; add r, mh, t` becomes `add r, mh, sub, lsr #1`.
//! MINIMAL SURFACE: no SUB+LSR form is fused (no `SubRRShiftLsr` opcode exists —
//! nothing emits that shape), and LSL fusion is tried FIRST so existing LSL
//! output is byte-identical.
//!
//! # NON-COMMUTATIVITY (load-bearing correctness)
//!
//! `ADD Rd, Rn, Rm, LSL #k` = `Rn + (Rm << k)` and `SUB Rd, Rn, Rm, LSL #k` =
//! `Rn - (Rm << k)`: the shift binds to `Rm` ONLY. ADD is commutative in value,
//! so the shifted temp may be either add operand (both orders are tried). SUB is
//! **NOT** commutative — the shift can only sit on the subtrahend — so a shifted
//! temp is fused ONLY when it is the SUBTRAHEND (`SubRR` operand 2). A shifted
//! temp in the MINUEND position (`SubRR` operand 1) is left UNFUSED: folding it
//! would silently compute `(s<<k) - x` as the wrong `x - (s<<k)`. This is the
//! single highest-severity item in this pass; `try_fuse_sub` never tries the
//! minuend order.
//!
//! # FAIL-CLOSED
//!
//! The rewrite fires ONLY when:
//!   * the `AddRR`/`SubRR` and the `LslRI`/`LsrRI` are in the SAME block (shift
//!     before the consumer), so no cross-block/dominance reasoning is needed;
//!   * the shift result `t` is SINGLE-USE across the whole function (its only
//!     read is this consumer), so folding it and deleting the shift is safe;
//!   * the shift amount `k` is a real in-register shift, `k` in `[1, width)`;
//!   * the operand register classes match (all W or all X).
//!
//! Only plain `AddRR`/`SubRR` are matched — NEVER the flag-setting `AddsRR`/
//! `SubsRR` (fusing a flags-consumer's producer would drop the NZCV side
//! effect). The emitted `AddRRShift`/`SubRRShift`/`AddRRShiftLsr` are the
//! VERIFIED opcodes (`lowering_proof::all_add_sub_lsl_shift_proofs` /
//! `all_add_lsr_shift_proofs`, gate-covered W+X); their encoders are
//! byte-verified against clang. Runs AFTER `mul_shift_reduce` in the pipeline so
//! it also collapses that pass's `LslRI`+`AddRR`/`SubRR` output.
//!
//! # Redundant shift-amount mask elision (second pattern)
//!
//! The same walk also elides a redundant AND that masks a VARIABLE shift
//! amount:
//!
//! ```text
//!   t = AndRI(amt, #mask)            ; AND t, amt, #mask
//!   d = LslRR/LsrRR/AsrRR(x, t)      ; LSL/LSR/ASR d, x, t
//!   =>
//!   d = LslRR/LsrRR/AsrRR(x, amt)    ; the AndRI is deleted
//! ```
//!
//! SOUNDNESS: the AArch64 register-amount shifts (LSLV/LSRV/ASRV) take the
//! amount MODULO the register width in hardware — `Rd = Rn <shift> (Rm &
//! (width-1))` (ARM ARM; modeled FAITHFULLY by the verifier's
//! `encode_lsl_rr_masked`/`encode_lsr_rr_masked`/`encode_asr_rr_masked` in
//! `trust-cg-verify/src/aarch64_semantics.rs`). Whenever `mask` keeps ALL of
//! the low `log2(width)` bits (`mask & (width-1) == width-1`, e.g. `#31` for a
//! W-register shift, `#63` for an X-register shift), `(amt & mask) mod width
//! == amt mod width` for EVERY value of `amt` — including amounts >= width and
//! "negative" amounts — so the AND is architecturally dead. This is exactly
//! the `1 << (x % 32)` bit-mask idiom clang folds and tcg previously kept
//! (nsieve-bits' BTEST/BFLIP hot loops).
//!
//! Fail-closed conditions: same block, `t` single-use function-wide, all four
//! registers the same GPR width, and `amt` NOT redefined between the `AndRI`
//! and the shift (checked via the walk's last-def positions — see below).
//!
//! # Reaching-definition hygiene (applies to ALL patterns in this pass)
//!
//! The walk tracks the most recent in-block def position of EVERY vreg and
//! invalidates producer-map entries on redefinition, so a fusion only fires
//! when (a) the producer is the RE reaching def of `t` at the consumer and
//! (b) the producer's SOURCE operand is not redefined between producer and
//! consumer (folding moves the source read down to the consumer site).
//!
//! # Kill switches
//!
//! Per-pass bisect: `TRUST_CG_DISABLE_PASSES=shiftalufuse`. The LSR-into-ADD
//! fusion alone: set `TCG_NO_LSR_ADD_FUSE` (any value) — LSL fusion keeps
//! running, LSR fusion becomes a no-op. The shift-amount mask elision alone:
//! set `TCG_NO_SHIFT_AMT_MASK_ELIDE` (any value).

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap, VReg,
    regs::RegClass,
};

use crate::pass_manager::MachinePass;

/// Shift-into-ADD/SUB fusion pass.
pub struct ShiftAluFuse;

impl MachinePass for ShiftAluFuse {
    fn name(&self) -> &str {
        "shift-alu-fuse"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_shift_alu_fuse(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_shift_alu_fuse(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_shift_alu_fuse(func, Some(provenance))
    }
}

fn shift_alu_fuse_pass_id() -> PassId {
    PassId::new("shift-alu-fuse")
}

/// Compile-time kill switch for the LSR-into-ADD fusion alone: set
/// `TCG_NO_LSR_ADD_FUSE` (any value) to disable it (LSL fusion keeps running).
fn lsr_add_fuse_enabled() -> bool {
    std::env::var_os("TCG_NO_LSR_ADD_FUSE").is_none()
}

/// Compile-time kill switch for the variable-shift amount-mask elision alone:
/// set `TCG_NO_SHIFT_AMT_MASK_ELIDE` (any value) to disable it (the ADD/SUB
/// shift fusions keep running).
fn shift_amt_mask_elide_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_SHIFT_AMT_MASK_ELIDE").is_none()
}

/// A same-block producer definition: the defining instruction plus its
/// position in the block walk (for source-redefinition guards).
#[derive(Clone, Copy)]
struct ProducerDef {
    inst: InstId,
    pos: usize,
}

fn run_shift_alu_fuse(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    // Function-wide READ counts: a VReg's single-use status must hold across the
    // WHOLE function, not just the current block (a later block could read `t`).
    let read_counts = count_vreg_reads(func);
    let lsr_enabled = lsr_add_fuse_enabled();
    let mask_elide_enabled = shift_amt_mask_elide_enabled();

    let mut changed = false;
    for block_id in func.block_order.clone() {
        // LslRI/LsrRI/AndRI defs seen so far IN THIS BLOCK (VReg -> producer).
        // Only same-block defs are eligible (the def precedes the use in program
        // order because we populate this as we walk), and entries are
        // INVALIDATED when any later instruction redefines the vreg, so a map
        // hit is the true reaching definition at the consumer.
        let mut lsl_defs: HashMap<VReg, ProducerDef> = HashMap::new();
        let mut lsr_defs: HashMap<VReg, ProducerDef> = HashMap::new();
        let mut and_defs: HashMap<VReg, ProducerDef> = HashMap::new();
        // Most recent in-block def position of EVERY vreg (any opcode). Guards
        // the folded SOURCE operand: moving its read down to the consumer is
        // only sound if no intervening instruction redefined it.
        let mut last_def_pos: HashMap<VReg, usize> = HashMap::new();

        for (pos, inst_id) in func.block(block_id).insts.clone().into_iter().enumerate() {
            let opcode = func.inst(inst_id).opcode;
            match opcode {
                AArch64Opcode::AddRR | AArch64Opcode::SubRR | AArch64Opcode::EorRR => {
                    if let Some((lsl_id, fused)) = try_fuse(
                        func.inst(inst_id),
                        func,
                        &lsl_defs,
                        &lsr_defs,
                        lsr_enabled,
                        &read_counts,
                        &last_def_pos,
                    ) {
                        // Rewrite the ADD/SUB in place, preserving proof/source_loc.
                        let orig = func.inst(inst_id);
                        let mut new_inst = fused;
                        new_inst.proof = orig.proof;
                        if new_inst.source_loc.is_none() {
                            new_inst.source_loc = orig.source_loc;
                        }
                        *func.inst_mut(inst_id) = new_inst;
                        // Delete the now-dead LslRI/LsrRI (single-use, consumed).
                        *func.inst_mut(lsl_id) = MachInst::new(AArch64Opcode::Nop, vec![]);
                        if let Some(provenance) = provenance.as_deref_mut() {
                            provenance.record_in_place_transform(inst_id, shift_alu_fuse_pass_id());
                            provenance.record_in_place_transform(lsl_id, shift_alu_fuse_pass_id());
                        }
                        changed = true;
                    }
                }
                AArch64Opcode::LslRR | AArch64Opcode::LsrRR | AArch64Opcode::AsrRR
                    if mask_elide_enabled =>
                {
                    if let Some((and_id, amt)) = try_elide_shift_amount_mask(
                        func.inst(inst_id),
                        func,
                        &and_defs,
                        &read_counts,
                        &last_def_pos,
                    ) {
                        // Rewrite the shift amount in place (opcode unchanged),
                        // then delete the now-dead AndRI (single-use, consumed).
                        func.inst_mut(inst_id).operands[2] = MachOperand::VReg(amt);
                        *func.inst_mut(and_id) = MachInst::new(AArch64Opcode::Nop, vec![]);
                        if let Some(provenance) = provenance.as_deref_mut() {
                            provenance.record_in_place_transform(inst_id, shift_alu_fuse_pass_id());
                            provenance.record_in_place_transform(and_id, shift_alu_fuse_pass_id());
                        }
                        changed = true;
                    }
                }
                _ => {}
            }

            // Record this instruction's defs (AFTER matching — an instruction
            // is never its own producer). Any def invalidates stale producer
            // entries for that vreg; an eligible producer then (re)registers.
            let mut defs: Vec<VReg> = Vec::new();
            {
                let inst = func.inst(inst_id);
                crate::effects::aarch64_for_each_def_position(
                    inst.opcode,
                    inst.operands.len(),
                    |def_pos| {
                        if let Some(MachOperand::VReg(v)) = inst.operands.get(def_pos) {
                            defs.push(*v);
                        }
                    },
                );
            }
            for v in defs {
                lsl_defs.remove(&v);
                lsr_defs.remove(&v);
                and_defs.remove(&v);
                last_def_pos.insert(v, pos);
            }
            let producer = ProducerDef { inst: inst_id, pos };
            match func.inst(inst_id).opcode {
                AArch64Opcode::LslRI => {
                    if let Some(MachOperand::VReg(dst)) = func.inst(inst_id).operands.first() {
                        lsl_defs.insert(*dst, producer);
                    }
                }
                AArch64Opcode::LsrRI => {
                    if let Some(MachOperand::VReg(dst)) = func.inst(inst_id).operands.first() {
                        lsr_defs.insert(*dst, producer);
                    }
                }
                AArch64Opcode::AndRI if mask_elide_enabled => {
                    if let Some(MachOperand::VReg(dst)) = func.inst(inst_id).operands.first() {
                        and_defs.insert(*dst, producer);
                    }
                }
                _ => {}
            }
        }
    }

    changed
}

/// Try to elide a redundant amount-mask `AndRI` feeding a register-amount
/// shift. On success returns `(and_inst_id, amt)` — the caller replaces the
/// shift's amount operand with `amt` and deletes the `AndRI`.
///
/// SOUND because LSLV/LSRV/ASRV take the amount mod the register width in
/// hardware (see the module note): when `mask` keeps all low `log2(width)`
/// bits, `(amt & mask) mod width == amt mod width` for every `amt`.
fn try_elide_shift_amount_mask(
    shift: &MachInst,
    func: &MachFunction,
    and_defs: &HashMap<VReg, ProducerDef>,
    read_counts: &HashMap<VReg, u32>,
    last_def_pos: &HashMap<VReg, usize>,
) -> Option<(InstId, VReg)> {
    if shift.operands.len() != 3 {
        return None;
    }
    let dst = shift.operands[0].as_vreg()?;
    let src = shift.operands[1].as_vreg()?;
    let t = shift.operands[2].as_vreg()?;
    // t must be SINGLE-USE (only this shift reads it) so deleting its AndRI is
    // safe.
    if read_counts.get(&t).copied().unwrap_or(0) != 1 {
        return None;
    }
    let and_def = *and_defs.get(&t)?;
    let and = func.inst(and_def.inst);
    if and.opcode != AArch64Opcode::AndRI || and.operands.len() != 3 {
        return None;
    }
    let amt = and.operands[1].as_vreg()?;
    let mask = and.operands[2].as_imm()?;

    // Width match: the shift's datasize is its register width; the AND must be
    // computed at the same width for the mod-width argument to apply.
    let width = gpr_width(dst.class)?;
    if gpr_width(src.class)? != width
        || gpr_width(t.class)? != width
        || gpr_width(amt.class)? != width
    {
        return None;
    }
    // The mask must keep ALL low log2(width) bits: then the AND cannot change
    // `amt mod width`, which is all the hardware shift reads.
    let low_bits = u64::from(width - 1);
    if (mask as u64) & low_bits != low_bits {
        return None;
    }
    // amt must not be redefined between the AndRI and the shift (its read
    // moves down to the shift site). A def AT the AndRI position is the AndRI
    // itself writing amt (t == amt) — also unsafe, also declined.
    if last_def_pos.get(&amt).is_some_and(|&p| p >= and_def.pos) {
        return None;
    }
    Some((and_def.inst, amt))
}

/// Count, for every VReg, how many times it appears as a READ operand across
/// the whole function, using the shared operand-role oracle (which also counts
/// tied def-use reads such as `Movk`'s operand 0 — a plain "skip operand 0"
/// scan would miss those and overstate single-use). This is the single-use
/// oracle: `read_counts[t] == 1` means the only reader of `t` is the candidate
/// consumer, so folding it and deleting its producer is safe.
fn count_vreg_reads(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            crate::effects::aarch64_for_each_use_position(
                inst.opcode,
                inst.operands.len(),
                |pos| {
                    if let Some(MachOperand::VReg(vreg)) = inst.operands.get(pos) {
                        *counts.entry(*vreg).or_insert(0) += 1;
                    }
                },
            );
        }
    }
    counts
}

/// Try to fuse `alu` (an `AddRR` or `SubRR`) with a single-use, same-block
/// `LslRI` (or, for ADD only, `LsrRI`) feeding an eligible source operand. On
/// success returns `(shift_inst_id, {Add,Sub}RRShift/AddRRShiftLsr MachInst)`.
///
/// ADD commutes, so BOTH operand orders are tried (LSL first, so pre-existing
/// LSL output is unchanged; then LSR). SUB does NOT commute, so ONLY the
/// subtrahend (operand 2) is a fuse candidate — never the minuend — and only
/// the LSL form exists (no `SubRRShiftLsr` opcode — MINIMAL SURFACE).
fn try_fuse(
    alu: &MachInst,
    func: &MachFunction,
    lsl_defs: &HashMap<VReg, ProducerDef>,
    lsr_defs: &HashMap<VReg, ProducerDef>,
    lsr_add_enabled: bool,
    read_counts: &HashMap<VReg, u32>,
    last_def_pos: &HashMap<VReg, usize>,
) -> Option<(InstId, MachInst)> {
    if alu.operands.len() != 3 {
        return None;
    }
    let dst = alu.operands.first()?.as_vreg()?;
    let context = ShiftFuseContext {
        func,
        read_counts,
        last_def_pos,
    };
    match alu.opcode {
        AArch64Opcode::AddRR => {
            // ADD Rd, Rn, Rm — commutes. Try the shift on operand 2 (Rn=operand
            // 1), then on operand 1 (Rn=operand 2); LSL (AddRRShift) before LSR
            // (AddRRShiftLsr).
            try_fuse_shifted(
                AArch64Opcode::LslRI,
                AArch64Opcode::AddRRShift,
                dst,
                &alu.operands[2],
                &alu.operands[1],
                lsl_defs,
                context,
            )
            .or_else(|| {
                try_fuse_shifted(
                    AArch64Opcode::LslRI,
                    AArch64Opcode::AddRRShift,
                    dst,
                    &alu.operands[1],
                    &alu.operands[2],
                    lsl_defs,
                    context,
                )
            })
            .or_else(|| {
                if lsr_add_enabled {
                    try_fuse_shifted(
                        AArch64Opcode::LsrRI,
                        AArch64Opcode::AddRRShiftLsr,
                        dst,
                        &alu.operands[2],
                        &alu.operands[1],
                        lsr_defs,
                        context,
                    )
                } else {
                    None
                }
            })
            .or_else(|| {
                if lsr_add_enabled {
                    try_fuse_shifted(
                        AArch64Opcode::LsrRI,
                        AArch64Opcode::AddRRShiftLsr,
                        dst,
                        &alu.operands[1],
                        &alu.operands[2],
                        lsr_defs,
                        context,
                    )
                } else {
                    None
                }
            })
        }
        AArch64Opcode::SubRR => {
            // SUB Rd, Rn, Rm = Rn - Rm — NON-COMMUTATIVE. The shift can ONLY sit
            // on the subtrahend Rm (operand 2); the minuend Rn (operand 1) is
            // NEVER a fuse candidate. Emitted as SubRRShift [dst, Rn, s, k].
            // LSL only — no SubRRShiftLsr opcode exists (MINIMAL SURFACE).
            try_fuse_shifted(
                AArch64Opcode::LslRI,
                AArch64Opcode::SubRRShift,
                dst,
                &alu.operands[2], // subtrahend (Rm) — the only shiftable slot
                &alu.operands[1], // minuend (Rn) — the un-shifted base
                lsl_defs,
                context,
            )
        }
        AArch64Opcode::EorRR => {
            // EOR commutes, so either operand may be the shifted temporary.
            // The fused AArch64 form always places the shifted source in Rm.
            // Keep the kind-to-opcode mapping explicit: selecting LSR for an
            // LSL producer is a silent wrong-value transformation.
            try_fuse_shifted(
                AArch64Opcode::LslRI,
                AArch64Opcode::EorRRLsl,
                dst,
                &alu.operands[2],
                &alu.operands[1],
                lsl_defs,
                context,
            )
            .or_else(|| {
                try_fuse_shifted(
                    AArch64Opcode::LslRI,
                    AArch64Opcode::EorRRLsl,
                    dst,
                    &alu.operands[1],
                    &alu.operands[2],
                    lsl_defs,
                    context,
                )
            })
            .or_else(|| {
                try_fuse_shifted(
                    AArch64Opcode::LsrRI,
                    AArch64Opcode::EorRRLsr,
                    dst,
                    &alu.operands[2],
                    &alu.operands[1],
                    lsr_defs,
                    context,
                )
            })
            .or_else(|| {
                try_fuse_shifted(
                    AArch64Opcode::LsrRI,
                    AArch64Opcode::EorRRLsr,
                    dst,
                    &alu.operands[1],
                    &alu.operands[2],
                    lsr_defs,
                    context,
                )
            })
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct ShiftFuseContext<'a> {
    func: &'a MachFunction,
    read_counts: &'a HashMap<VReg, u32>,
    last_def_pos: &'a HashMap<VReg, usize>,
}

/// `shifted_op` is the candidate `shift_opcode` (`LslRI`/`LsrRI`) result (the
/// operand to fold into the shift); `plain_op` is the other ALU operand (becomes
/// ARM `Rn`). Builds `out_opcode [dst, plain(Rn), s(Rm), Imm(k)]` when all
/// fail-closed conditions hold.
fn try_fuse_shifted(
    shift_opcode: AArch64Opcode,
    out_opcode: AArch64Opcode,
    dst: VReg,
    shifted_op: &MachOperand,
    plain_op: &MachOperand,
    shift_defs: &HashMap<VReg, ProducerDef>,
    context: ShiftFuseContext<'_>,
) -> Option<(InstId, MachInst)> {
    let ShiftFuseContext {
        func,
        read_counts,
        last_def_pos,
    } = context;
    let t = shifted_op.as_vreg()?;
    // t must be SINGLE-USE (only this ALU reads it) so deleting its shift is safe.
    if read_counts.get(&t).copied().unwrap_or(0) != 1 {
        return None;
    }
    let shift_def = *shift_defs.get(&t)?;
    let lsl_id = shift_def.inst;
    let lsl = func.inst(lsl_id);
    if lsl.opcode != shift_opcode || lsl.operands.len() != 3 {
        return None;
    }
    let s = lsl.operands[1].as_vreg()?; // shifted SOURCE
    let k = lsl.operands[2].as_imm()?; // shift amount

    // s must not be redefined between the shift and the ALU: the fusion moves
    // the read of s down to the ALU site.
    if last_def_pos.get(&s).is_some_and(|&p| p >= shift_def.pos) {
        return None;
    }

    // Width match: dst, plain (Rn), s (Rm), t must all be the same GPR width, and
    // the shift amount must be a real in-register shift in [1, width).
    let width = gpr_width(dst.class)?;
    let plain = plain_op.as_vreg()?;
    if gpr_width(plain.class)? != width
        || gpr_width(s.class)? != width
        || gpr_width(t.class)? != width
    {
        return None;
    }
    if k < 1 || k >= i64::from(width) {
        return None;
    }

    // Shifted ALU form [Rd, Rn (un-shifted = plain), Rm (shifted source = s),
    // Imm(k)].
    Some((
        lsl_id,
        MachInst::new(
            out_opcode,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(plain),
                MachOperand::VReg(s),
                MachOperand::Imm(k),
            ],
        ),
    ))
}

/// The bit width of a GPR register class (32 for W, 64 for X); `None` for any
/// non-GPR class (fail-closed — the fusion only applies to integer ADD/SUB/LSL).
fn gpr_width(class: RegClass) -> Option<u32> {
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
