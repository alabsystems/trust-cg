// trust-cg-opt - Migrated peephole patterns
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Peephole patterns expressed as declarative [`Rule`]s in the rewrite
//! framework.
//!
//! These rules are the active implementation of former hand-written peephole
//! patterns 1-52. Pattern 53 needs cross-block dominator information and lives
//! in [`crate::rotate_idiom`]. See
//! `designs/2026-04-19-rewrite-wave3-plan.md` for the migration inventory and
//! wave breakdown.
//!
//! # Migrated (single-instruction)
//!
//! | # | Pattern | Action |
//! |---|---------|--------|
//! | 1 | `mov x, x` | delete |
//! | 2 | `add x, y, #0` | → `mov x, y` |
//! | 3 | `sub x, y, #0` | → `mov x, y` |
//! | 4 | `lsl x, y, #0` | → `mov x, y` |
//! | 5 | `lsr x, y, #0` | → `mov x, y` |
//! | 6 | `asr x, y, #0` | → `mov x, y` |
//! | 7 | `orr x, y, y` | → `mov x, y` |
//! | 8 | `and x, y, y` | → `mov x, y` |
//! | 9 | `eor x, y, #0` | → `mov x, y` |
//! | 10 | `orr x, y, #0` | → `mov x, y` |
//! | 11 | `and x, y, #-1` | → `mov x, y` |
//! | 12 | `sub x, y, y` | → `mov x, #0` |
//! | 13 | `eor x, y, y` | → `mov x, #0` |
//! | 14 | `and x, y, #0` | → `mov x, #0` |
//! | 15 | `orr x, y, #-1` | → `mov x, #-1` |
//! | 16 | `add x, y, y` | → `lsl x, y, #1` |
//! | 17 | `nop` | delete |
//! | 18 | `add x, y, #-N` | → `sub x, y, #N` (N > 0, N != i64::MIN) |
//! | 19 | `sub x, y, #-N` | → `add x, y, #N` (N > 0, N != i64::MIN) |
//! | 26 | `bic x, y, y` | → `mov x, #0` |
//! | 27 | `orn x, y, y` | → `mov x, #-1` |
//! | 43 | `csel x, y, y, cond` | → `mov x, y` |
//!
//! # Migrated (multi-instruction, same-opcode def-use)
//!
//! | # | Pattern | Action |
//! |---|---------|--------|
//! | 20 | `neg(neg(x))` | → `mov x` |
//! | 28 | `sxtb(sxtb(x))`, `sxth(sxth(x))`, `sxtw(sxtw(x))` | collapse to one |
//! | 46 | `uxtb(uxtb(x))` | collapse |
//! | 47 | `uxth(uxth(x))` | collapse |
//!
//! # Migrated (Wave 4, definer-driven)
//!
//! | # | Pattern | Action |
//! |---|---------|--------|
//! | 21 | `add x, y, neg(z)` (either operand) | → `sub x, y, z` |
//! | 22 | `sub x, y, neg(z)` | → `add x, y, z` |
//! | 30 | `neg(sub(x, y))` | → `sub y, x` |
//! | 39 | `sxth(sxtb(x))` | → `sxtb(x)` |
//! | 40 | `sxtw(sxtb(x))`, `sxtw(sxth(x))` | → narrower |
//! | 48 | `uxth(uxtb(x))` | → `uxtb(x)` |
//! | 49-50 | `uxtw(uxtb(x))`, `uxtw(uxth(x))` | → narrower |
//!
//! # Migrated (Wave 5, definer-driven — MovI imm + cross-operand match)
//!
//! | # | Pattern | Action |
//! |---|---------|--------|
//! | 25 | `mul x, MovI(#1), y` (either mul operand) | → `mov x, y` |
//! | 31 | `mul x, MovI(#-1), y` (either mul operand) | → `neg x, y` |
//! | 33 | `sdiv x, y, MovI(#1)` | → `mov x, y` |
//! | 34 | `mul x, MovI(#0), _` (either mul operand) | → `mov x, #0` |
//! | 41 | `add(sub(x, y), y)` and commutations | → `mov x` |
//! | 42 | `sub(add(x, y), y)` and commuted add | → `mov x` |
//! | 44 | `udiv x, y, MovI(#1)` | → `mov x, y` |
//! | 45 | `sdiv x, y, MovI(#-1)` | → `neg x, y` |
//! | 51 | `add(x, sub(y, x))` and commutation | → `mov y` |
//! | 52 | `eor(eor(x, y), y)` and 3 commutations | → `mov x` |
//!
//! # Migrated (Wave 6, definer-driven — MADD/MSUB with MovI multiplicand)
//!
//! | # | Pattern | Action |
//! |---|---------|--------|
//! | 35 | `madd x, MovI(#1), y, z` (either multiplicand) | → `add x, y, z` |
//! | 36 | `madd x, MovI(#0), _, z` (either multiplicand) | → `mov x, z` |
//! | 37 | `msub x, MovI(#1), y, z` (either multiplicand) | → `sub x, z, y` |
//! | 38 | `msub x, MovI(#0), _, z` (either multiplicand) | → `mov x, z` |
//!
//! # Migrated (constraint extensions)
//!
//! | # | Pattern | Action |
//! |---|---------|--------|
//! | 23 | `mul x, y, MovI(#2^k)` (either mul operand) | → `lsl x, y, #k` |
//! | 24 | `udiv x, y, MovI(#2^k)` | → `lsr x, y, #k` |
//! | 29 | `lsl(lsr(x, #k), #k)` | → `and x, clear-low-mask` |
//! | 32 | `lsr(lsl(x, #k), #k)` | → `and x, clear-high-mask` |
//!
//! [`DefinerImmIsPowerOfTwo`] and [`DefinerImmEqualsOuterImm`] carry the
//! former missing relations. [`register_migrated`] registers all patterns
//! 1-52; [`crate::rotate_idiom::RotateIdiom`] carries pattern 53.

use trust_cg_ir::{AArch64Opcode, AArch64Target, MachInst, MachOperand, TargetInfo};

use crate::rewrite::constraint::{
    DefinedByOneOf, DefinedByOpcode, DefinerImmEquals, DefinerImmEqualsOuterImm,
    DefinerImmIsPowerOfTwo, DefinerOperandEqualsOuter, ImmEquals, ImmNegativeNonMin, OperandsEqual,
};
use crate::rewrite::engine::RewriteEngine;
use crate::rewrite::matcher::MatchCtx;
use crate::rewrite::rewriter::RewriteAction;
use crate::rewrite::rule::{Rule, RuleBuilder};

// =========================================================================
// Pattern 1: self-move delete (mov x, x → delete)
// =========================================================================

/// Build the `mov x, x` → delete rule.
pub fn rule_self_move_delete() -> Rule {
    RuleBuilder::match_opcode("self-move-delete", AArch64Opcode::MovR)
        .benefit(20)
        .constrain(OperandsEqual { a: 0, b: 1 })
        .rewrite_with(|_ctx| RewriteAction::Delete)
}

// =========================================================================
// Pattern 2: add x, y, #0 → mov x, y
// =========================================================================

/// Build the `add x, y, #0` → `mov x, y` rule.
pub fn rule_add_ri_zero() -> Rule {
    RuleBuilder::match_opcode("add-ri-zero-to-mov", AArch64Opcode::AddRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: 0 })
        .rewrite_with(add_ri_zero_rewrite)
}

fn add_ri_zero_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

// =========================================================================
// Pattern 3: sub x, y, #0 → mov x, y
// =========================================================================

/// Build the `sub x, y, #0` → `mov x, y` rule.
pub fn rule_sub_ri_zero() -> Rule {
    RuleBuilder::match_opcode("sub-ri-zero-to-mov", AArch64Opcode::SubRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: 0 })
        .rewrite_with(sub_ri_zero_rewrite)
}

fn sub_ri_zero_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

// =========================================================================
// Pattern 13: eor x, y, y → mov x, #0
// =========================================================================

/// Build the `eor x, y, y` → `mov x, #0` rule.
pub fn rule_xor_self_zero() -> Rule {
    RuleBuilder::match_opcode("xor-self-to-zero", AArch64Opcode::EorRR)
        .benefit(10)
        .constrain(OperandsEqual { a: 1, b: 2 })
        .rewrite_with(xor_self_rewrite)
}

fn xor_self_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    // `x ^ x == 0` holds ONLY for the un-shifted `EOR Rd, Rn, Rm` form.
    //
    // `OpcodeCategory::XorRR` also covers the shifted-register variants
    // (`EorRRShift` / `EorRRLsl` / `EorRRLsr`, see `target_info.rs`), which
    // carry the shift amount in a FOURTH operand. There the identity does not
    // hold: `eor Rd, Rn, Rn, LSL #k` is `Rn ^ (Rn << k)`, which is non-zero for
    // every `k != 0`. `OperandsEqual { a: 1, b: 2 }` compares only the two
    // source registers and is blind to that trailing modifier, so the operand
    // count is what distinguishes the two forms.
    //
    // This guard must be `!= 3`, not `< 3`: the previous `< 3` admitted the
    // 4-operand shifted forms and rewrote them to `mov #0`, miscompiling them.
    // Caught by trust-cg-fuzz `mutual_recursion_mixed_abi_pressure`, which only
    // diverged at O3 because O3 alone re-runs the pipeline to a fixpoint — the
    // shifted EOR is produced by a later fusion pass, so the rule sees it only
    // on a second iteration.
    if ctx.inst.operands.len() != 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_ri(),
        vec![ctx.inst.operands[0].clone(), MachOperand::Imm(0)],
    ))
}

// =========================================================================
// Pattern 4/5/6: lsl/lsr/asr x, y, #0 → mov x, y
// =========================================================================

/// Build the `lsl x, y, #0` → `mov x, y` rule.
pub fn rule_lsl_ri_zero() -> Rule {
    RuleBuilder::match_opcode("lsl-ri-zero-to-mov", AArch64Opcode::LslRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: 0 })
        .rewrite_with(shift_ri_zero_rewrite)
}

/// Build the `lsr x, y, #0` → `mov x, y` rule.
pub fn rule_lsr_ri_zero() -> Rule {
    RuleBuilder::match_opcode("lsr-ri-zero-to-mov", AArch64Opcode::LsrRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: 0 })
        .rewrite_with(shift_ri_zero_rewrite)
}

/// Build the `asr x, y, #0` → `mov x, y` rule.
pub fn rule_asr_ri_zero() -> Rule {
    RuleBuilder::match_opcode("asr-ri-zero-to-mov", AArch64Opcode::AsrRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: 0 })
        .rewrite_with(shift_ri_zero_rewrite)
}

fn shift_ri_zero_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

// =========================================================================
// Pattern 12: sub x, y, y → mov x, #0
// =========================================================================

/// Build the `sub x, y, y` → `mov x, #0` rule.
pub fn rule_sub_self_zero() -> Rule {
    RuleBuilder::match_opcode("sub-self-to-zero", AArch64Opcode::SubRR)
        .benefit(10)
        .constrain(OperandsEqual { a: 1, b: 2 })
        .rewrite_with(sub_self_rewrite)
}

fn sub_self_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() != 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_ri(),
        vec![ctx.inst.operands[0].clone(), MachOperand::Imm(0)],
    ))
}

// =========================================================================
// Pattern 10: orr x, y, #0 → mov x, y
// Pattern 15: orr x, y, #-1 → mov x, #-1
// =========================================================================

/// Build the `orr x, y, #0` → `mov x, y` rule.
pub fn rule_orr_ri_zero() -> Rule {
    RuleBuilder::match_opcode("orr-ri-zero-to-mov", AArch64Opcode::OrrRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: 0 })
        .rewrite_with(orr_ri_zero_rewrite)
}

fn orr_ri_zero_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

/// Build the `orr x, y, #-1` → `mov x, #-1` rule.
pub fn rule_orr_ri_minus_one() -> Rule {
    RuleBuilder::match_opcode("orr-ri-all-ones-to-movi", AArch64Opcode::OrrRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: -1 })
        .rewrite_with(orr_ri_minus_one_rewrite)
}

fn orr_ri_minus_one_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_ri(),
        vec![ctx.inst.operands[0].clone(), MachOperand::Imm(-1)],
    ))
}

// =========================================================================
// Pattern 9: eor x, y, #0 → mov x, y
// =========================================================================

/// Build the `eor x, y, #0` → `mov x, y` rule.
pub fn rule_eor_ri_zero() -> Rule {
    RuleBuilder::match_opcode("eor-ri-zero-to-mov", AArch64Opcode::EorRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: 0 })
        .rewrite_with(eor_ri_zero_rewrite)
}

fn eor_ri_zero_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

// =========================================================================
// Pattern 14: and x, y, #0 → mov x, #0
// Pattern 11: and x, y, #-1 → mov x, y
// =========================================================================

/// Build the `and x, y, #0` → `mov x, #0` rule.
pub fn rule_and_ri_zero() -> Rule {
    RuleBuilder::match_opcode("and-ri-zero-to-zero", AArch64Opcode::AndRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: 0 })
        .rewrite_with(and_ri_zero_rewrite)
}

fn and_ri_zero_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_ri(),
        vec![ctx.inst.operands[0].clone(), MachOperand::Imm(0)],
    ))
}

/// Build the `and x, y, #-1` → `mov x, y` rule.
pub fn rule_and_ri_minus_one() -> Rule {
    RuleBuilder::match_opcode("and-ri-all-ones-to-mov", AArch64Opcode::AndRI)
        .benefit(10)
        .constrain(ImmEquals { idx: 2, value: -1 })
        .rewrite_with(and_ri_minus_one_rewrite)
}

fn and_ri_minus_one_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

// =========================================================================
// Pattern 7/8: orr/and self → mov
// =========================================================================

/// Build the `orr x, y, y` → `mov x, y` rule.
pub fn rule_orr_self() -> Rule {
    RuleBuilder::match_opcode("orr-self-to-mov", AArch64Opcode::OrrRR)
        .benefit(10)
        .constrain(OperandsEqual { a: 1, b: 2 })
        .rewrite_with(logical_self_rewrite)
}

/// Build the `and x, y, y` → `mov x, y` rule.
pub fn rule_and_self() -> Rule {
    RuleBuilder::match_opcode("and-self-to-mov", AArch64Opcode::AndRR)
        .benefit(10)
        .constrain(OperandsEqual { a: 1, b: 2 })
        .rewrite_with(logical_self_rewrite)
}

fn logical_self_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

// =========================================================================
// Pattern 16: add x, y, y → lsl x, y, #1 (strength reduction)
// =========================================================================

/// Build the `add x, y, y` → `lsl x, y, #1` rule.
pub fn rule_add_self_to_shl() -> Rule {
    RuleBuilder::match_opcode("add-self-to-shl", AArch64Opcode::AddRR)
        .benefit(10)
        .constrain(OperandsEqual { a: 1, b: 2 })
        .rewrite_with(add_self_to_shl_rewrite)
}

fn add_self_to_shl_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() != 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::shl_ri(),
        vec![
            ctx.inst.operands[0].clone(),
            ctx.inst.operands[1].clone(),
            MachOperand::Imm(1),
        ],
    ))
}

// =========================================================================
// Pattern 17: nop → delete
// =========================================================================

/// Build the `nop` → delete rule.
pub fn rule_nop_delete() -> Rule {
    RuleBuilder::match_opcode("nop-delete", AArch64Opcode::Nop)
        .benefit(20)
        .rewrite_with(|_ctx| RewriteAction::Delete)
}

// =========================================================================
// Pattern 18: add x, y, #-N → sub x, y, #N (negative imm canonicalization)
// Pattern 19: sub x, y, #-N → add x, y, #N
// =========================================================================

/// Build the `add x, y, #-N` → `sub x, y, #N` rule.
pub fn rule_add_ri_negative_canonicalize() -> Rule {
    RuleBuilder::match_opcode("add-ri-negative-to-sub", AArch64Opcode::AddRI)
        .benefit(5)
        .constrain(ImmNegativeNonMin { idx: 2 })
        .rewrite_with(add_ri_negative_rewrite)
}

fn add_ri_negative_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    // `OpcodeCategory::AddRI` covers BOTH `AddRI` and `AddRIShift12`
    // (`target_info.rs`), and the two have the SAME operand shape
    // `[Rd, Rn, Imm]` — so unlike the shifted-EOR trap in `xor_self_rewrite`,
    // an operand-count guard cannot separate them here. `AddRIShift12` means
    // `Rd = Rn + (imm12 << 12)`; rewriting it to a plain `SubRI` with the
    // negated immediate drops that `<< 12` and is wrong by a factor of 4096.
    // (`const_fold` performs exactly this discrimination via
    // `effective_register_immediate`.) The discriminator must be the OPCODE.
    if ctx.inst.opcode != AArch64Opcode::AddRI {
        return RewriteAction::None;
    }
    let val = match ctx.inst.operands.get(2) {
        Some(MachOperand::Imm(v)) if *v < 0 && *v != i64::MIN => *v,
        _ => return RewriteAction::None,
    };
    RewriteAction::Replace(MachInst::new(
        AArch64Target::sub_ri(),
        vec![
            ctx.inst.operands[0].clone(),
            ctx.inst.operands[1].clone(),
            MachOperand::Imm(-val),
        ],
    ))
}

/// Build the `sub x, y, #-N` → `add x, y, #N` rule.
pub fn rule_sub_ri_negative_canonicalize() -> Rule {
    RuleBuilder::match_opcode("sub-ri-negative-to-add", AArch64Opcode::SubRI)
        .benefit(5)
        .constrain(ImmNegativeNonMin { idx: 2 })
        .rewrite_with(sub_ri_negative_rewrite)
}

fn sub_ri_negative_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    let val = match ctx.inst.operands.get(2) {
        Some(MachOperand::Imm(v)) if *v < 0 && *v != i64::MIN => *v,
        _ => return RewriteAction::None,
    };
    RewriteAction::Replace(MachInst::new(
        AArch64Target::add_ri(),
        vec![
            ctx.inst.operands[0].clone(),
            ctx.inst.operands[1].clone(),
            MachOperand::Imm(-val),
        ],
    ))
}

// =========================================================================
// Pattern 26: bic x, y, y → mov x, #0
// Pattern 27: orn x, y, y → mov x, #-1
// =========================================================================

/// Build the `bic x, y, y` → `mov x, #0` rule.
pub fn rule_bic_self() -> Rule {
    RuleBuilder::match_opcode("bic-self-to-zero", AArch64Opcode::BicRR)
        .benefit(10)
        .constrain(OperandsEqual { a: 1, b: 2 })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 3 {
                return RewriteAction::None;
            }
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_ri(),
                vec![ctx.inst.operands[0].clone(), MachOperand::Imm(0)],
            ))
        })
}

/// Build the `orn x, y, y` → `mov x, #-1` rule.
pub fn rule_orn_self() -> Rule {
    RuleBuilder::match_opcode("orn-self-to-minus-one", AArch64Opcode::OrnRR)
        .benefit(10)
        .constrain(OperandsEqual { a: 1, b: 2 })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 3 {
                return RewriteAction::None;
            }
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_ri(),
                vec![ctx.inst.operands[0].clone(), MachOperand::Imm(-1)],
            ))
        })
}

// =========================================================================
// Pattern 43: csel x, y, y, cond → mov x, y
// =========================================================================

/// Build the `csel x, y, y, cond` → `mov x, y` rule.
///
/// If both arms of a conditional select name the same register, the
/// condition is irrelevant. Matching `Csel` by opcode keeps this
/// target-specific rule explicit (no generic CSEL category exists).
pub fn rule_csel_same_arms() -> Rule {
    RuleBuilder::match_opcode("csel-same-arms-to-mov", AArch64Opcode::Csel)
        .benefit(10)
        .constrain(OperandsEqual { a: 1, b: 2 })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 4 {
                return RewriteAction::None;
            }
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_rr(),
                vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
            ))
        })
}

// =========================================================================
// Pattern 20: neg(neg(x)) → mov x (double-negation elimination)
// =========================================================================

/// Build the `neg(neg(x))` → `mov x` rule (multi-instruction, same-block
/// def-use).
///
/// The outer NEG matches by opcode; `DefinedByOpcode` checks that the
/// operand-1 VReg is produced in the same block by another NEG. The
/// rewriter copies the inner NEG's `operand[1]` as the mov source.
pub fn rule_neg_neg() -> Rule {
    RuleBuilder::match_opcode("neg-neg-to-mov", AArch64Opcode::Neg)
        .benefit(15)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::Neg,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 2 {
                return RewriteAction::None;
            }
            let def = match ctx.operand_def(1) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_rr(),
                vec![ctx.inst.operands[0].clone(), def.operands[1].clone()],
            ))
        })
}

// =========================================================================
// Patterns 28, 46, 47: same-opcode extension collapse (idempotent)
// =========================================================================

/// Helper that builds a "same-extension collapses" rule for an opcode.
///
/// `sxtb(sxtb(x))` → `sxtb(x)`, and likewise for `sxth`, `sxtw`, `uxtb`,
/// `uxth`, `uxtw`. The outer and inner instructions share the same
/// opcode; the outer is replaced by applying the opcode directly to the
/// inner source.
fn rule_same_ext_collapse(name: &'static str, opcode: AArch64Opcode) -> Rule {
    RuleBuilder::match_opcode(name, opcode)
        .benefit(15)
        .constrain(DefinedByOpcode { idx: 1, opcode })
        .rewrite_with(move |ctx| {
            if ctx.inst.operands.len() < 2 {
                return RewriteAction::None;
            }
            let def = match ctx.operand_def(1) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                ctx.inst.opcode,
                vec![ctx.inst.operands[0].clone(), def.operands[1].clone()],
            ))
        })
}

/// `sxtb(sxtb(x))` → `sxtb(x)` (pattern 28, byte sign-extension).
pub fn rule_sxtb_sxtb() -> Rule {
    rule_same_ext_collapse("sxtb-sxtb-collapse", AArch64Opcode::Sxtb)
}

/// `sxth(sxth(x))` → `sxth(x)` (pattern 28, halfword sign-extension).
pub fn rule_sxth_sxth() -> Rule {
    rule_same_ext_collapse("sxth-sxth-collapse", AArch64Opcode::Sxth)
}

/// `sxtw(sxtw(x))` → `sxtw(x)` (pattern 28, word sign-extension).
pub fn rule_sxtw_sxtw() -> Rule {
    rule_same_ext_collapse("sxtw-sxtw-collapse", AArch64Opcode::Sxtw)
}

/// `uxtb(uxtb(x))` → `uxtb(x)` (pattern 46).
pub fn rule_uxtb_uxtb() -> Rule {
    rule_same_ext_collapse("uxtb-uxtb-collapse", AArch64Opcode::Uxtb)
}

/// `uxth(uxth(x))` → `uxth(x)` (pattern 47).
pub fn rule_uxth_uxth() -> Rule {
    rule_same_ext_collapse("uxth-uxth-collapse", AArch64Opcode::Uxth)
}

/// `uxtw(uxtw(x))` → `uxtw(x)` (pattern 46/47 companion).
pub fn rule_uxtw_uxtw() -> Rule {
    rule_same_ext_collapse("uxtw-uxtw-collapse", AArch64Opcode::Uxtw)
}

// =========================================================================
// Wave 4 multi-instruction patterns (definer-driven)
//
// Each rule below uses `MatchCtx::definer_of` (via the `DefinedByOpcode` /
// `DefinedByOneOf` constraints and in-rewriter reads). The same-block
// The engine maintains one forward def map per block — these rules re-use it.
// =========================================================================

// -------------------------------------------------------------------------
// Pattern 21: add x, y, neg(z) → sub x, y, z
// Pattern 21': add x, neg(z), y → sub x, y, z    (ADD is commutative)
// -------------------------------------------------------------------------

/// `add x, y, neg(z)` → `sub x, y, z` — RHS operand is defined by NEG.
pub fn rule_add_neg_rhs() -> Rule {
    RuleBuilder::match_opcode("add-of-neg-rhs-to-sub", AArch64Opcode::AddRR)
        .benefit(15)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::Neg,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() != 3 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(2) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::sub_rr(),
                vec![
                    ctx.inst.operands[0].clone(),
                    ctx.inst.operands[1].clone(),
                    def.operands[1].clone(),
                ],
            ))
        })
}

/// `add x, neg(z), y` → `sub x, y, z` — LHS operand is defined by NEG.
pub fn rule_add_neg_lhs() -> Rule {
    RuleBuilder::match_opcode("add-of-neg-lhs-to-sub", AArch64Opcode::AddRR)
        .benefit(14)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::Neg,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() != 3 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(1) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::sub_rr(),
                vec![
                    ctx.inst.operands[0].clone(),
                    // Swap: y (the non-neg operand) becomes the minuend.
                    ctx.inst.operands[2].clone(),
                    def.operands[1].clone(),
                ],
            ))
        })
}

// -------------------------------------------------------------------------
// Pattern 22: sub x, y, neg(z) → add x, y, z   (only subtrahend checked)
// -------------------------------------------------------------------------

/// `sub x, y, neg(z)` → `add x, y, z`.
pub fn rule_sub_neg_to_add() -> Rule {
    RuleBuilder::match_opcode("sub-of-neg-to-add", AArch64Opcode::SubRR)
        .benefit(15)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::Neg,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() != 3 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(2) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::add_rr(),
                vec![
                    ctx.inst.operands[0].clone(),
                    ctx.inst.operands[1].clone(),
                    def.operands[1].clone(),
                ],
            ))
        })
}

// -------------------------------------------------------------------------
// Pattern 30: neg(sub(x, y)) → sub(y, x)    (-(x-y) = y-x)
// -------------------------------------------------------------------------

/// `neg(sub(x, y))` → `sub(y, x)`.
pub fn rule_neg_sub_swap() -> Rule {
    RuleBuilder::match_opcode("neg-of-sub-swap-operands", AArch64Opcode::Neg)
        .benefit(14) // Less than rule_neg_neg (15) so double-neg wins first.
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::SubRR,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 2 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(1) {
                Some(d) if d.operands.len() >= 3 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::sub_rr(),
                vec![
                    ctx.inst.operands[0].clone(),
                    def.operands[2].clone(), // y
                    def.operands[1].clone(), // x
                ],
            ))
        })
}

// -------------------------------------------------------------------------
// Narrower sign-extension subsumes wider (patterns 39, 40).
//
//   sxth(sxtb(x)) → sxtb(x)        (8-bit dominates 16-bit)
//   sxtw(sxtb(x)) → sxtb(x)        (8-bit dominates 32-bit)
//   sxtw(sxth(x)) → sxth(x)        (16-bit dominates 32-bit)
// -------------------------------------------------------------------------

/// Build a "narrower extension subsumes wider" rule.
///
/// `outer_opcode` is the wider extension we match; `narrower` lists the
/// strictly narrower extensions that, if they produced the operand, make
/// the outer one redundant. The rewrite keeps the narrower opcode and
/// copies its inner source. Works for sign- and zero-extension alike.
fn rule_narrower_ext(
    name: &'static str,
    outer_opcode: AArch64Opcode,
    narrower: &'static [AArch64Opcode],
) -> Rule {
    RuleBuilder::match_opcode(name, outer_opcode)
        .benefit(12)
        .constrain(DefinedByOneOf {
            idx: 1,
            opcodes: narrower,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 2 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(1) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                def.opcode,
                vec![ctx.inst.operands[0].clone(), def.operands[1].clone()],
            ))
        })
}

/// Pattern 39: `sxth(sxtb(x))` → `sxtb(x)`.
pub fn rule_sxth_of_sxtb() -> Rule {
    rule_narrower_ext(
        "sxth-of-sxtb-subsumes",
        AArch64Opcode::Sxth,
        &[AArch64Opcode::Sxtb],
    )
}

/// Pattern 40: `sxtw(sxtb(x))` / `sxtw(sxth(x))` → narrower.
pub fn rule_sxtw_of_narrower_sext() -> Rule {
    rule_narrower_ext(
        "sxtw-of-sxtb-or-sxth-subsumes",
        AArch64Opcode::Sxtw,
        &[AArch64Opcode::Sxtb, AArch64Opcode::Sxth],
    )
}

// -------------------------------------------------------------------------
// Narrower zero-extension subsumes wider (patterns 48, 49, 50).
// -------------------------------------------------------------------------

/// Pattern 48: `uxth(uxtb(x))` → `uxtb(x)`.
pub fn rule_uxth_of_uxtb() -> Rule {
    rule_narrower_ext(
        "uxth-of-uxtb-subsumes",
        AArch64Opcode::Uxth,
        &[AArch64Opcode::Uxtb],
    )
}

/// Patterns 49/50: `uxtw(uxtb(x))` / `uxtw(uxth(x))` → narrower.
pub fn rule_uxtw_of_narrower_zext() -> Rule {
    rule_narrower_ext(
        "uxtw-of-uxtb-or-uxth-subsumes",
        AArch64Opcode::Uxtw,
        &[AArch64Opcode::Uxtb, AArch64Opcode::Uxth],
    )
}

// -------------------------------------------------------------------------
// Patterns 25 / 31 / 34: MUL with a MovI constant operand.
//
//   mul x, MovI(#0), y → mov x, #0   (pattern 34, both orderings)
//   mul x, MovI(#1), y → mov x, y    (pattern 25, both orderings)
//   mul x, MovI(#-1), y → neg x, y   (pattern 31, both orderings)
// -------------------------------------------------------------------------

/// Factory: match MUL whose operand at `const_idx` is a `MovI(#value)`.
/// The `rewriter` is a function pointer that will consume the matched
/// instruction — it is responsible for looking up the non-const operand
/// index that matches this constant position.
fn rule_mul_movi_const(
    name: &'static str,
    const_idx: usize,
    value: i64,
    benefit: i32,
    rewriter: fn(&MatchCtx<'_>) -> RewriteAction,
) -> Rule {
    RuleBuilder::match_opcode(name, AArch64Opcode::MulRR)
        .benefit(benefit)
        .constrain(DefinedByOpcode {
            idx: const_idx,
            opcode: AArch64Opcode::MovI,
        })
        .constrain(DefinerImmEquals {
            idx: const_idx,
            def_operand_idx: 1,
            value,
        })
        .rewrite_with(rewriter)
}

fn mul_to_zero(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_ri(),
        vec![ctx.inst.operands[0].clone(), MachOperand::Imm(0)],
    ))
}

fn mul_to_mov_from_op1(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

fn mul_to_mov_from_op2(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[2].clone()],
    ))
}

fn mul_to_neg_from_op1(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Opcode::Neg,
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
    ))
}

fn mul_to_neg_from_op2(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Opcode::Neg,
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[2].clone()],
    ))
}

/// Pattern 34: `mul x, y, MovI(#0)` → `mov x, #0`.
pub fn rule_mul_by_zero_rhs() -> Rule {
    rule_mul_movi_const("mul-by-zero-rhs-to-movi", 2, 0, 17, mul_to_zero)
}

/// Pattern 34 commuted: `mul x, MovI(#0), y` → `mov x, #0`.
pub fn rule_mul_by_zero_lhs() -> Rule {
    rule_mul_movi_const("mul-by-zero-lhs-to-movi", 1, 0, 17, mul_to_zero)
}

/// Pattern 25: `mul x, y, MovI(#1)` → `mov x, y`.
pub fn rule_mul_by_one_rhs() -> Rule {
    rule_mul_movi_const("mul-by-one-rhs-to-mov", 2, 1, 16, mul_to_mov_from_op1)
}

/// Pattern 25 commuted: `mul x, MovI(#1), y` → `mov x, y`.
pub fn rule_mul_by_one_lhs() -> Rule {
    rule_mul_movi_const("mul-by-one-lhs-to-mov", 1, 1, 16, mul_to_mov_from_op2)
}

/// Pattern 31: `mul x, y, MovI(#-1)` → `neg x, y`.
pub fn rule_mul_by_neg_one_rhs() -> Rule {
    rule_mul_movi_const("mul-by-neg-one-rhs-to-neg", 2, -1, 15, mul_to_neg_from_op1)
}

/// Pattern 31 commuted: `mul x, MovI(#-1), y` → `neg x, y`.
pub fn rule_mul_by_neg_one_lhs() -> Rule {
    rule_mul_movi_const("mul-by-neg-one-lhs-to-neg", 1, -1, 15, mul_to_neg_from_op2)
}

// Pattern 23: MUL by power-of-two MovI -> LSL by log2.
// Pattern 24: UDIV by power-of-two MovI divisor -> LSR by log2.
// DefinerImmIsPowerOfTwo proves the definer's immediate is a positive
// power of two; the rewriter reads it back to compute the shift amount.
// UDIV is not commutative (divisor at idx 2 only); MUL is commutative.

fn pow2_log2(v: i64) -> Option<i64> {
    if v > 0 && (v & (v - 1)) == 0 {
        Some(v.trailing_zeros() as i64)
    } else {
        None
    }
}

fn pow2_shift_rewrite(
    ctx: &MatchCtx<'_>,
    const_idx: usize,
    keep_idx: usize,
    shift_opcode: AArch64Opcode,
) -> RewriteAction {
    if ctx.inst.operands.len() != 3 {
        return RewriteAction::None;
    }
    let def = match ctx.definer_of(const_idx) {
        Some(d) => d,
        None => return RewriteAction::None,
    };
    let imm = match def.operands.get(1) {
        Some(MachOperand::Imm(v)) => *v,
        _ => return RewriteAction::None,
    };
    let shift = match pow2_log2(imm) {
        Some(s) => s,
        None => return RewriteAction::None,
    };
    RewriteAction::Replace(MachInst::new(
        shift_opcode,
        vec![
            ctx.inst.operands[0].clone(),
            ctx.inst.operands[keep_idx].clone(),
            MachOperand::Imm(shift),
        ],
    ))
}

fn mul_pow2_rhs_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    pow2_shift_rewrite(ctx, 2, 1, AArch64Target::shl_ri())
}

fn mul_pow2_lhs_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    pow2_shift_rewrite(ctx, 1, 2, AArch64Target::shl_ri())
}

fn udiv_pow2_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    // AArch64 has no shr_ri() accessor; legacy peephole emitted LsrRI.
    pow2_shift_rewrite(ctx, 2, 1, AArch64Opcode::LsrRI)
}

/// Pattern 23: `mul x, y, MovI(#2^k)` -> `lsl x, y, #k`.
pub fn rule_mul_pow2_rhs() -> Rule {
    RuleBuilder::match_opcode("mul-pow2-rhs-to-lsl", AArch64Opcode::MulRR)
        .benefit(14)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::MovI,
        })
        .constrain(DefinerImmIsPowerOfTwo {
            idx: 2,
            def_operand_idx: 1,
        })
        .rewrite_with(mul_pow2_rhs_rewrite)
}

/// Pattern 23 commuted: `mul x, MovI(#2^k), y` -> `lsl x, y, #k`.
pub fn rule_mul_pow2_lhs() -> Rule {
    RuleBuilder::match_opcode("mul-pow2-lhs-to-lsl", AArch64Opcode::MulRR)
        .benefit(14)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::MovI,
        })
        .constrain(DefinerImmIsPowerOfTwo {
            idx: 1,
            def_operand_idx: 1,
        })
        .rewrite_with(mul_pow2_lhs_rewrite)
}

/// Pattern 24: `udiv x, y, MovI(#2^k)` -> `lsr x, y, #k`.
pub fn rule_udiv_pow2() -> Rule {
    RuleBuilder::match_opcode("udiv-pow2-to-lsr", AArch64Opcode::UDiv)
        .benefit(14)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::MovI,
        })
        .constrain(DefinerImmIsPowerOfTwo {
            idx: 2,
            def_operand_idx: 1,
        })
        .rewrite_with(udiv_pow2_rewrite)
}

// Pattern 29: lsl(lsr(x, #k), #k) -> and x, #clear_low_mask
// Pattern 32: lsr(lsl(x, #k), #k) -> and x, #clear_high_mask
// DefinerImmEqualsOuterImm proves inner shift == outer shift; rewriter
// recomputes width from inner source reg and mask from (width, k).

fn operand_register_width(operand: &MachOperand) -> Option<i64> {
    use trust_cg_ir::regs::{RegClass, SpecialReg, preg_class};
    let class = match operand {
        MachOperand::VReg(vreg) => vreg.class,
        MachOperand::PReg(preg) => preg_class(*preg),
        MachOperand::Special(special) => {
            return Some(match special {
                SpecialReg::WZR => 32,
                SpecialReg::SP | SpecialReg::XZR => 64,
            });
        }
        _ => return None,
    };
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

fn shift_pair_width(outer: &MachInst, src: &MachOperand) -> Option<i64> {
    operand_register_width(src).or_else(|| operand_register_width(&outer.operands[0]))
}

fn shift_amount_in_width(k: i64, width: i64) -> bool {
    (1..width).contains(&k)
}

fn clear_low_bits_mask(width: i64, k: i64) -> Option<i64> {
    if !shift_amount_in_width(k, width) {
        return None;
    }
    let width = u32::try_from(width).ok()?;
    let k = u32::try_from(k).ok()?;
    let all_ones = (1u128 << width) - 1;
    let low_bits = (1u128 << k) - 1;
    Some((all_ones & !low_bits) as u64 as i64)
}

fn clear_high_bits_mask(width: i64, k: i64) -> Option<i64> {
    if !shift_amount_in_width(k, width) {
        return None;
    }
    let width = u32::try_from(width).ok()?;
    let k = u32::try_from(k).ok()?;
    let kept_width = width.checked_sub(k)?;
    let mask = (1u128 << kept_width) - 1;
    Some(mask as u64 as i64)
}

fn shift_pair_to_and_rewrite(
    ctx: &MatchCtx<'_>,
    mask_fn: fn(i64, i64) -> Option<i64>,
) -> RewriteAction {
    if ctx.inst.operands.len() < 3 {
        return RewriteAction::None;
    }
    let k = match ctx.inst.operands.get(2) {
        Some(MachOperand::Imm(v)) => *v,
        _ => return RewriteAction::None,
    };
    if !(1..=62).contains(&k) {
        return RewriteAction::None;
    }
    let def = match ctx.definer_of(1) {
        Some(d) if d.operands.len() >= 3 => d,
        _ => return RewriteAction::None,
    };
    let inner_src = def.operands[1].clone();
    let Some(width) = shift_pair_width(ctx.inst, &inner_src) else {
        return RewriteAction::None;
    };
    let Some(mask) = mask_fn(width, k) else {
        return RewriteAction::None;
    };
    RewriteAction::Replace(MachInst::new(
        AArch64Opcode::AndRI,
        vec![
            ctx.inst.operands[0].clone(),
            inner_src,
            MachOperand::Imm(mask),
        ],
    ))
}

fn lsl_lsr_to_and_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    shift_pair_to_and_rewrite(ctx, clear_low_bits_mask)
}

fn lsr_lsl_to_and_rewrite(ctx: &MatchCtx<'_>) -> RewriteAction {
    shift_pair_to_and_rewrite(ctx, clear_high_bits_mask)
}

/// Pattern 29: `lsl(lsr(x, #k), #k)` -> `and x, #clear_low_mask`.
pub fn rule_lsl_lsr_to_and() -> Rule {
    RuleBuilder::match_opcode("lsl-lsr-to-and-mask", AArch64Opcode::LslRI)
        .benefit(13)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::LsrRI,
        })
        .constrain(DefinerImmEqualsOuterImm {
            outer_imm_idx: 2,
            outer_def_idx: 1,
            def_imm_idx: 2,
        })
        .rewrite_with(lsl_lsr_to_and_rewrite)
}

/// Pattern 32: `lsr(lsl(x, #k), #k)` -> `and x, #clear_high_mask`.
pub fn rule_lsr_lsl_to_and() -> Rule {
    RuleBuilder::match_opcode("lsr-lsl-to-and-mask", AArch64Opcode::LsrRI)
        .benefit(13)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::LslRI,
        })
        .constrain(DefinerImmEqualsOuterImm {
            outer_imm_idx: 2,
            outer_def_idx: 1,
            def_imm_idx: 2,
        })
        .rewrite_with(lsr_lsl_to_and_rewrite)
}

// -------------------------------------------------------------------------
// Patterns 33 / 44 / 45: UDIV/SDIV with a MovI divisor.
//
//   udiv x, y, MovI(#1)  → mov x, y   (pattern 44)
//   sdiv x, y, MovI(#1)  → mov x, y   (pattern 33)
//   sdiv x, y, MovI(#-1) → neg x, y   (pattern 45)
//
// Only the divisor is checked; UDIV/SDIV are not commutative. Pattern 24
// (UDIV pow2) is the separate `rule_udiv_pow2` below because it needs the
// `DefinerImmIsPowerOfTwo` constraint and a computed shift.
// -------------------------------------------------------------------------

/// Pattern 44: `udiv x, y, MovI(#1)` → `mov x, y`.
pub fn rule_udiv_by_one() -> Rule {
    RuleBuilder::match_opcode("udiv-by-one-to-mov", AArch64Opcode::UDiv)
        .benefit(15)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::MovI,
        })
        .constrain(DefinerImmEquals {
            idx: 2,
            def_operand_idx: 1,
            value: 1,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 3 {
                return RewriteAction::None;
            }
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_rr(),
                vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
            ))
        })
}

/// Pattern 33: `sdiv x, y, MovI(#1)` → `mov x, y`.
pub fn rule_sdiv_by_one() -> Rule {
    RuleBuilder::match_opcode("sdiv-by-one-to-mov", AArch64Opcode::SDiv)
        .benefit(15)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::MovI,
        })
        .constrain(DefinerImmEquals {
            idx: 2,
            def_operand_idx: 1,
            value: 1,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 3 {
                return RewriteAction::None;
            }
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_rr(),
                vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
            ))
        })
}

/// Pattern 45: `sdiv x, y, MovI(#-1)` → `neg x, y`.
pub fn rule_sdiv_by_neg_one() -> Rule {
    RuleBuilder::match_opcode("sdiv-by-neg-one-to-neg", AArch64Opcode::SDiv)
        .benefit(15)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::MovI,
        })
        .constrain(DefinerImmEquals {
            idx: 2,
            def_operand_idx: 1,
            value: -1,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() < 3 {
                return RewriteAction::None;
            }
            RewriteAction::Replace(MachInst::new(
                AArch64Opcode::Neg,
                vec![ctx.inst.operands[0].clone(), ctx.inst.operands[1].clone()],
            ))
        })
}

// -------------------------------------------------------------------------
// Pattern 42: SUB(ADD(x, y), y) → MOV x, and commuted ADD source.
//
//   sub(add(x, y), y) → mov x       (two forms, ADD is commutative)
//
// The outer SUB is not commutative; only the minuend is checked.
// -------------------------------------------------------------------------

/// Pattern 42 with ADD in its canonical form: `sub(add(x, y), y)` → `mov x`.
pub fn rule_sub_of_add_cancel_rhs() -> Rule {
    RuleBuilder::match_opcode("sub-of-add-cancel-rhs", AArch64Opcode::SubRR)
        .benefit(15)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::AddRR,
        })
        .constrain(DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 2,
            outer_operand_idx: 2,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() != 3 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(1) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_rr(),
                vec![ctx.inst.operands[0].clone(), def.operands[1].clone()],
            ))
        })
}

/// Pattern 42 with ADD commuted: `sub(add(y, x), y)` → `mov x`.
pub fn rule_sub_of_add_cancel_lhs() -> Rule {
    RuleBuilder::match_opcode("sub-of-add-cancel-lhs", AArch64Opcode::SubRR)
        .benefit(14)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::AddRR,
        })
        .constrain(DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 1,
            outer_operand_idx: 2,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() != 3 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(1) {
                Some(d) if d.operands.len() >= 3 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_rr(),
                vec![ctx.inst.operands[0].clone(), def.operands[2].clone()],
            ))
        })
}

// -------------------------------------------------------------------------
// Patterns 41 / 51: ADD with SUB-defined operand (cross-inst cancellation).
//
//   add(sub(x, y), y) → mov x          (pattern 41, outer-def is LHS)
//   add(y, sub(x, y)) → mov x          (pattern 41 commuted, outer-def RHS)
//   add(x, sub(y, x)) → mov y          (pattern 51, outer-def RHS with
//                                       outer-LHS equal to sub-subtrahend)
// Pattern 51 is captured by the same constraint (def_operand_idx=2 equals
// outer_operand_idx=1) applied to the RHS-def case; see comments below.
// -------------------------------------------------------------------------

/// Pattern 41: `add(sub(x, y), y)` → `mov x` — LHS is the SUB definer.
pub fn rule_add_of_sub_cancel_lhs_def() -> Rule {
    RuleBuilder::match_opcode("add-of-sub-cancel-lhs-def", AArch64Opcode::AddRR)
        .benefit(15)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::SubRR,
        })
        .constrain(DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 2,
            outer_operand_idx: 2,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() != 3 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(1) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_rr(),
                vec![ctx.inst.operands[0].clone(), def.operands[1].clone()],
            ))
        })
}

/// Pattern 41 (commuted) + Pattern 51:
/// `add(y, sub(x, y))` → `mov x`, and `add(x, sub(y, x))` → `mov y`. Both
/// collapse to "`outer[1]` equals the SUB subtrahend; emit `mov` of the
/// SUB minuend".
pub fn rule_add_of_sub_cancel_rhs_def() -> Rule {
    RuleBuilder::match_opcode("add-of-sub-cancel-rhs-def", AArch64Opcode::AddRR)
        .benefit(14)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::SubRR,
        })
        .constrain(DefinerOperandEqualsOuter {
            outer_def_idx: 2,
            def_operand_idx: 2,
            outer_operand_idx: 1,
        })
        .rewrite_with(|ctx| {
            if ctx.inst.operands.len() != 3 {
                return RewriteAction::None;
            }
            let def = match ctx.definer_of(2) {
                Some(d) if d.operands.len() >= 2 => d,
                _ => return RewriteAction::None,
            };
            RewriteAction::Replace(MachInst::new(
                AArch64Target::mov_rr(),
                vec![ctx.inst.operands[0].clone(), def.operands[1].clone()],
            ))
        })
}

// -------------------------------------------------------------------------
// Pattern 52: EOR(EOR(x, y), y) → MOV x (and three commutations).
//
//   eor(eor(x, y), y) → mov x   (LHS def, outer-rhs matches inner-rhs)
//   eor(eor(y, x), y) → mov x   (LHS def, outer-rhs matches inner-lhs)
//   eor(y, eor(x, y)) → mov x   (RHS def, outer-lhs matches inner-rhs)
//   eor(y, eor(y, x)) → mov x   (RHS def, outer-lhs matches inner-lhs)
// -------------------------------------------------------------------------

// Each EOR cancellation variant is a separate rule. We cannot factor out
// the rewriter via a closure (the `Rewriter` trait requires a `fn` pointer
// to stay `Send + Sync` without capture), so the four rules are expanded
// explicitly below. Indices are named `def_idx` (the outer ADD/SUB/EOR
// operand whose producer we introspect) and `src_idx` (the producer's
// operand we copy into the emitted `mov`).

/// Pattern 52a: `eor(eor(x, y), y)` → `mov x` — LHS def, outer-rhs matches inner-rhs.
pub fn rule_eor_cancel_lhs_def_outer_rhs_matches_inner_rhs() -> Rule {
    RuleBuilder::match_opcode("eor-cancel-lhs-def-rhs-rhs", AArch64Opcode::EorRR)
        .benefit(13)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::EorRR,
        })
        .constrain(DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 2,
            outer_operand_idx: 2,
        })
        .rewrite_with(eor_cancel_take_def_op1)
}

/// Pattern 52b: `eor(eor(y, x), y)` → `mov x` — LHS def, outer-rhs matches inner-lhs.
pub fn rule_eor_cancel_lhs_def_outer_rhs_matches_inner_lhs() -> Rule {
    RuleBuilder::match_opcode("eor-cancel-lhs-def-rhs-lhs", AArch64Opcode::EorRR)
        .benefit(13)
        .constrain(DefinedByOpcode {
            idx: 1,
            opcode: AArch64Opcode::EorRR,
        })
        .constrain(DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 1,
            outer_operand_idx: 2,
        })
        .rewrite_with(eor_cancel_take_def_op2)
}

/// Pattern 52c: `eor(y, eor(x, y))` → `mov x` — RHS def, outer-lhs matches inner-rhs.
pub fn rule_eor_cancel_rhs_def_outer_lhs_matches_inner_rhs() -> Rule {
    RuleBuilder::match_opcode("eor-cancel-rhs-def-lhs-rhs", AArch64Opcode::EorRR)
        .benefit(13)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::EorRR,
        })
        .constrain(DefinerOperandEqualsOuter {
            outer_def_idx: 2,
            def_operand_idx: 2,
            outer_operand_idx: 1,
        })
        .rewrite_with(eor_cancel_rhs_take_def_op1)
}

/// Pattern 52d: `eor(y, eor(y, x))` → `mov x` — RHS def, outer-lhs matches inner-lhs.
pub fn rule_eor_cancel_rhs_def_outer_lhs_matches_inner_lhs() -> Rule {
    RuleBuilder::match_opcode("eor-cancel-rhs-def-lhs-lhs", AArch64Opcode::EorRR)
        .benefit(13)
        .constrain(DefinedByOpcode {
            idx: 2,
            opcode: AArch64Opcode::EorRR,
        })
        .constrain(DefinerOperandEqualsOuter {
            outer_def_idx: 2,
            def_operand_idx: 1,
            outer_operand_idx: 1,
        })
        .rewrite_with(eor_cancel_rhs_take_def_op2)
}

fn eor_cancel_take_def_op1(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() != 3 {
        return RewriteAction::None;
    }
    let def = match ctx.definer_of(1) {
        Some(d) if d.operands.len() >= 3 => d,
        _ => return RewriteAction::None,
    };
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), def.operands[1].clone()],
    ))
}

fn eor_cancel_take_def_op2(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() != 3 {
        return RewriteAction::None;
    }
    let def = match ctx.definer_of(1) {
        Some(d) if d.operands.len() >= 3 => d,
        _ => return RewriteAction::None,
    };
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), def.operands[2].clone()],
    ))
}

fn eor_cancel_rhs_take_def_op1(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() != 3 {
        return RewriteAction::None;
    }
    let def = match ctx.definer_of(2) {
        Some(d) if d.operands.len() >= 3 => d,
        _ => return RewriteAction::None,
    };
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), def.operands[1].clone()],
    ))
}

fn eor_cancel_rhs_take_def_op2(ctx: &MatchCtx<'_>) -> RewriteAction {
    if ctx.inst.operands.len() != 3 {
        return RewriteAction::None;
    }
    let def = match ctx.definer_of(2) {
        Some(d) if d.operands.len() >= 3 => d,
        _ => return RewriteAction::None,
    };
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), def.operands[2].clone()],
    ))
}

// =========================================================================
// Wave 6 (definer-driven — MADD / MSUB with a MovI multiplicand).
//
// MADD Rd, Rn, Rm, Ra = Ra + Rn * Rm.
// MSUB Rd, Rn, Rm, Ra = Ra - Rn * Rm.
//
// The multiplication is commutative (Rn * Rm), so a #0 or #1 may appear in
// either operand[1] (Rn) or operand[2] (Rm). Each value/position combination
// registers as a distinct rule:
//
//   | Pattern | MovI in | Action                          |
//   |---------|---------|---------------------------------|
//   | 35      | Rn or Rm = #1 | MADD → ADD Rd, other_mul, Ra |
//   | 36      | Rn or Rm = #0 | MADD → MOV Rd, Ra            |
//   | 37      | Rn or Rm = #1 | MSUB → SUB Rd, Ra, other_mul |
//   | 38      | Rn or Rm = #0 | MSUB → MOV Rd, Ra            |
//
// No new constraint is required — `DefinedByOpcode { idx, opcode: MovI }`
// plus `DefinerImmEquals { idx, def_operand_idx: 1, value }` already
// express the match. The rewriter picks the "other" multiplicand index
// statically so it remains a `fn` pointer.
// =========================================================================

/// Factory: match MADD/MSUB whose multiplicand at `const_idx` is `MovI(#value)`.
/// The supplied `rewriter` already knows which is the "other" multiplicand
/// index (the constant slot index is fixed per rule).
fn rule_muladd_movi_const(
    name: &'static str,
    outer_opcode: AArch64Opcode,
    const_idx: usize,
    value: i64,
    benefit: i32,
    rewriter: fn(&MatchCtx<'_>) -> RewriteAction,
) -> Rule {
    RuleBuilder::match_opcode(name, outer_opcode)
        .benefit(benefit)
        .constrain(DefinedByOpcode {
            idx: const_idx,
            opcode: AArch64Opcode::MovI,
        })
        .constrain(DefinerImmEquals {
            idx: const_idx,
            def_operand_idx: 1,
            value,
        })
        .rewrite_with(rewriter)
}

// -- MADD rewriters --------------------------------------------------------

fn madd_to_mov_from_addend(ctx: &MatchCtx<'_>) -> RewriteAction {
    // MADD #0 (pattern 36): regardless of which operand is zero, result = Ra.
    if ctx.inst.operands.len() < 4 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[3].clone()],
    ))
}

fn madd_to_add_other_is_rm(ctx: &MatchCtx<'_>) -> RewriteAction {
    // MADD #1 at Rn (operand[1]): result = Ra + 1*Rm = Ra + Rm → ADD Rd, Rm, Ra.
    if ctx.inst.operands.len() < 4 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::add_rr(),
        vec![
            ctx.inst.operands[0].clone(),
            ctx.inst.operands[2].clone(),
            ctx.inst.operands[3].clone(),
        ],
    ))
}

fn madd_to_add_other_is_rn(ctx: &MatchCtx<'_>) -> RewriteAction {
    // MADD #1 at Rm (operand[2]): result = Ra + Rn*1 = Ra + Rn → ADD Rd, Rn, Ra.
    if ctx.inst.operands.len() < 4 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::add_rr(),
        vec![
            ctx.inst.operands[0].clone(),
            ctx.inst.operands[1].clone(),
            ctx.inst.operands[3].clone(),
        ],
    ))
}

// -- MSUB rewriters --------------------------------------------------------

fn msub_to_mov_from_addend(ctx: &MatchCtx<'_>) -> RewriteAction {
    // MSUB #0 (pattern 38): regardless of which operand is zero, result = Ra.
    if ctx.inst.operands.len() < 4 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::mov_rr(),
        vec![ctx.inst.operands[0].clone(), ctx.inst.operands[3].clone()],
    ))
}

fn msub_to_sub_other_is_rm(ctx: &MatchCtx<'_>) -> RewriteAction {
    // MSUB #1 at Rn: result = Ra - 1*Rm = Ra - Rm → SUB Rd, Ra, Rm.
    if ctx.inst.operands.len() < 4 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::sub_rr(),
        vec![
            ctx.inst.operands[0].clone(),
            ctx.inst.operands[3].clone(),
            ctx.inst.operands[2].clone(),
        ],
    ))
}

fn msub_to_sub_other_is_rn(ctx: &MatchCtx<'_>) -> RewriteAction {
    // MSUB #1 at Rm: result = Ra - Rn*1 = Ra - Rn → SUB Rd, Ra, Rn.
    if ctx.inst.operands.len() < 4 {
        return RewriteAction::None;
    }
    RewriteAction::Replace(MachInst::new(
        AArch64Target::sub_rr(),
        vec![
            ctx.inst.operands[0].clone(),
            ctx.inst.operands[3].clone(),
            ctx.inst.operands[1].clone(),
        ],
    ))
}

// -- MADD rules (patterns 35, 36) -----------------------------------------

/// Pattern 36 at Rn: `madd Rd, MovI(#0), Rm, Ra` → `mov Rd, Ra`.
pub fn rule_madd_by_zero_at_rn() -> Rule {
    rule_muladd_movi_const(
        "madd-zero-at-rn-to-mov",
        AArch64Opcode::Madd,
        1,
        0,
        17,
        madd_to_mov_from_addend,
    )
}

/// Pattern 36 at Rm: `madd Rd, Rn, MovI(#0), Ra` → `mov Rd, Ra`.
pub fn rule_madd_by_zero_at_rm() -> Rule {
    rule_muladd_movi_const(
        "madd-zero-at-rm-to-mov",
        AArch64Opcode::Madd,
        2,
        0,
        17,
        madd_to_mov_from_addend,
    )
}

/// Pattern 35 at Rn: `madd Rd, MovI(#1), Rm, Ra` → `add Rd, Rm, Ra`.
pub fn rule_madd_by_one_at_rn() -> Rule {
    rule_muladd_movi_const(
        "madd-one-at-rn-to-add",
        AArch64Opcode::Madd,
        1,
        1,
        16,
        madd_to_add_other_is_rm,
    )
}

/// Pattern 35 at Rm: `madd Rd, Rn, MovI(#1), Ra` → `add Rd, Rn, Ra`.
pub fn rule_madd_by_one_at_rm() -> Rule {
    rule_muladd_movi_const(
        "madd-one-at-rm-to-add",
        AArch64Opcode::Madd,
        2,
        1,
        16,
        madd_to_add_other_is_rn,
    )
}

// -- MSUB rules (patterns 37, 38) -----------------------------------------

/// Pattern 38 at Rn: `msub Rd, MovI(#0), Rm, Ra` → `mov Rd, Ra`.
pub fn rule_msub_by_zero_at_rn() -> Rule {
    rule_muladd_movi_const(
        "msub-zero-at-rn-to-mov",
        AArch64Opcode::Msub,
        1,
        0,
        17,
        msub_to_mov_from_addend,
    )
}

/// Pattern 38 at Rm: `msub Rd, Rn, MovI(#0), Ra` → `mov Rd, Ra`.
pub fn rule_msub_by_zero_at_rm() -> Rule {
    rule_muladd_movi_const(
        "msub-zero-at-rm-to-mov",
        AArch64Opcode::Msub,
        2,
        0,
        17,
        msub_to_mov_from_addend,
    )
}

/// Pattern 37 at Rn: `msub Rd, MovI(#1), Rm, Ra` → `sub Rd, Ra, Rm`.
pub fn rule_msub_by_one_at_rn() -> Rule {
    rule_muladd_movi_const(
        "msub-one-at-rn-to-sub",
        AArch64Opcode::Msub,
        1,
        1,
        16,
        msub_to_sub_other_is_rm,
    )
}

/// Pattern 37 at Rm: `msub Rd, Rn, MovI(#1), Ra` → `sub Rd, Ra, Rn`.
pub fn rule_msub_by_one_at_rm() -> Rule {
    rule_muladd_movi_const(
        "msub-one-at-rm-to-sub",
        AArch64Opcode::Msub,
        2,
        1,
        16,
        msub_to_sub_other_is_rn,
    )
}

// =========================================================================
// Rule-set registration
// =========================================================================

/// Register the migrated rules on an engine in benefit order.
///
/// The call is idempotent but cheap; used by
/// [`crate::pipeline`] to wire the pass into O1/O2.
pub fn register_migrated(engine: &mut RewriteEngine) {
    // Wave 1/2 (single-inst identity/constant).
    engine.register(rule_add_ri_zero());
    engine.register(rule_sub_ri_zero());
    engine.register(rule_xor_self_zero());
    engine.register(rule_lsl_ri_zero());
    engine.register(rule_lsr_ri_zero());
    engine.register(rule_asr_ri_zero());
    engine.register(rule_sub_self_zero());
    engine.register(rule_orr_ri_zero());
    engine.register(rule_and_ri_zero());
    engine.register(rule_orr_self());
    engine.register(rule_and_self());
    // Wave 3 (single-inst).
    engine.register(rule_self_move_delete());
    engine.register(rule_eor_ri_zero());
    engine.register(rule_and_ri_minus_one());
    engine.register(rule_orr_ri_minus_one());
    engine.register(rule_add_self_to_shl());
    engine.register(rule_nop_delete());
    engine.register(rule_add_ri_negative_canonicalize());
    engine.register(rule_sub_ri_negative_canonicalize());
    engine.register(rule_bic_self());
    engine.register(rule_orn_self());
    engine.register(rule_csel_same_arms());
    // Wave 3 (multi-inst, same-opcode def-use).
    engine.register(rule_neg_neg());
    engine.register(rule_sxtb_sxtb());
    engine.register(rule_sxth_sxth());
    engine.register(rule_sxtw_sxtw());
    engine.register(rule_uxtb_uxtb());
    engine.register(rule_uxth_uxth());
    engine.register(rule_uxtw_uxtw());
    // Wave 4 (definer-driven).
    engine.register(rule_add_neg_rhs());
    engine.register(rule_add_neg_lhs());
    engine.register(rule_sub_neg_to_add());
    engine.register(rule_neg_sub_swap());
    engine.register(rule_sxth_of_sxtb());
    engine.register(rule_sxtw_of_narrower_sext());
    engine.register(rule_uxth_of_uxtb());
    engine.register(rule_uxtw_of_narrower_zext());
    // Wave 5 (definer-driven — MovI immediate + cross-operand equality).
    // Multiply-by-constant (patterns 25/31/34), both orderings.
    engine.register(rule_mul_by_zero_rhs());
    engine.register(rule_mul_by_zero_lhs());
    engine.register(rule_mul_by_one_rhs());
    engine.register(rule_mul_by_one_lhs());
    engine.register(rule_mul_by_neg_one_rhs());
    engine.register(rule_mul_by_neg_one_lhs());
    // Divide-by-constant (patterns 33/44/45).
    engine.register(rule_udiv_by_one());
    engine.register(rule_sdiv_by_one());
    engine.register(rule_sdiv_by_neg_one());
    // Wave 7: strength reduction mul/udiv by power-of-two (patterns 23/24).
    engine.register(rule_mul_pow2_rhs());
    engine.register(rule_mul_pow2_lhs());
    engine.register(rule_udiv_pow2());
    // Wave 7: shift-pair-to-mask collapses (patterns 29/32).
    engine.register(rule_lsl_lsr_to_and());
    engine.register(rule_lsr_lsl_to_and());
    // ADD/SUB cross-instruction cancellation (patterns 41/42/51).
    engine.register(rule_sub_of_add_cancel_rhs());
    engine.register(rule_sub_of_add_cancel_lhs());
    engine.register(rule_add_of_sub_cancel_lhs_def());
    engine.register(rule_add_of_sub_cancel_rhs_def());
    // EOR cross-instruction cancellation (pattern 52, four commutations).
    engine.register(rule_eor_cancel_lhs_def_outer_rhs_matches_inner_rhs());
    engine.register(rule_eor_cancel_lhs_def_outer_rhs_matches_inner_lhs());
    engine.register(rule_eor_cancel_rhs_def_outer_lhs_matches_inner_rhs());
    engine.register(rule_eor_cancel_rhs_def_outer_lhs_matches_inner_lhs());
    // Wave 6 (definer-driven — MADD/MSUB with MovI multiplicand).
    // MADD/MSUB by zero (patterns 36 / 38) — both operand positions.
    engine.register(rule_madd_by_zero_at_rn());
    engine.register(rule_madd_by_zero_at_rm());
    engine.register(rule_msub_by_zero_at_rn());
    engine.register(rule_msub_by_zero_at_rm());
    // MADD/MSUB by one (patterns 35 / 37) — both operand positions.
    engine.register(rule_madd_by_one_at_rn());
    engine.register(rule_madd_by_one_at_rm());
    engine.register(rule_msub_by_one_at_rn());
    engine.register(rule_msub_by_one_at_rm());
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, MachFunction, OpcodeCategory, RegClass, Signature, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn single_block_func(insts: Vec<MachInst>) -> (MachFunction, BlockId) {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        for i in insts {
            let id = func.push_inst(i);
            func.append_inst(entry, id);
        }
        (func, entry)
    }

    // -----------------------------------------------------------------
    // Single-instruction patterns — wave 1/2 kept for regression.
    // -----------------------------------------------------------------

    #[test]
    fn add_ri_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands.len(), 2);
    }

    #[test]
    fn add_ri_nonzero_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(4)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn sub_ri_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
    }

    #[test]
    fn xor_self_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::EorRR,
            vec![vreg(0), vreg(7), vreg(7)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_xor_self_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_ri());
        assert!(matches!(after.operands[1], MachOperand::Imm(0)));
    }

    #[test]
    fn xor_different_operands_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::EorRR,
            vec![vreg(0), vreg(7), vreg(8)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_xor_self_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    /// `eor Rd, Rn, Rn, LSL #k` is `Rn ^ (Rn << k)`, NOT zero — the self-XOR
    /// identity holds only for the un-shifted form. `OpcodeCategory::XorRR`
    /// covers the shifted-register variants too, so the rule must reject them
    /// on operand count.
    ///
    /// Regression: the guard was `< 3`, which admitted these 4-operand forms
    /// and rewrote them to `mov #0`. That miscompiled at O3 only, because O3
    /// alone iterates the pipeline to a fixpoint and a later fusion pass is
    /// what produces the shifted EOR.
    #[test]
    fn xor_self_shifted_does_not_fire() {
        for opcode in [
            AArch64Opcode::EorRRLsl,
            AArch64Opcode::EorRRLsr,
            AArch64Opcode::EorRRShift,
        ] {
            for shift in [1i64, 7, 63] {
                let (mut func, entry) = single_block_func(vec![MachInst::new(
                    opcode,
                    vec![vreg(0), vreg(7), vreg(7), MachOperand::Imm(shift)],
                )]);
                let mut engine = RewriteEngine::new();
                engine.register(rule_xor_self_zero());
                let stats = engine.run_to_fixpoint(&mut func, 4);
                assert_eq!(
                    stats.rewrites, 0,
                    "{opcode:?} with shift #{shift} must not be rewritten to mov #0"
                );
                let after = func.inst(func.block(entry).insts[0]);
                assert_eq!(after.opcode, opcode, "{opcode:?} must be left intact");
                assert_eq!(after.operands.len(), 4);
            }
        }
    }

    #[test]
    fn xor_self_rejects_shifted_eor_category_neighbors() {
        // `y ^ rotate(y, 1)`, `y ^ (y << 1)`, and `y ^ (y >> 1)` are not
        // zero. These fused instructions share the target-independent XorRR
        // category with EorRR, so the scalar identity rule must match exactly.
        for opcode in [
            AArch64Opcode::EorRRShift,
            AArch64Opcode::EorRRLsl,
            AArch64Opcode::EorRRLsr,
        ] {
            let (mut func, entry) = single_block_func(vec![MachInst::new(
                opcode,
                vec![vreg(0), vreg(7), vreg(7), MachOperand::Imm(1)],
            )]);
            let mut engine = RewriteEngine::new();
            engine.register(rule_xor_self_zero());
            let stats = engine.run_to_fixpoint(&mut func, 4);

            assert_eq!(stats.rewrites, 0, "{opcode:?} matched EorRR identity");
            assert_eq!(func.inst(func.block(entry).insts[0]).opcode, opcode);
        }
    }

    #[test]
    fn scalar_rules_reject_distinct_arithmetic_category_neighbors() {
        // AddRIShift12 applies its immediate after a 12-bit shift; rewriting
        // it as an unshifted SubRI changes the value. NeonAddV/NeonSubV are
        // SIMD operations and must never enter scalar integer identities.
        let fpr = |id| MachOperand::VReg(VReg::new(id, RegClass::Fpr128));
        let cases = [
            (
                MachInst::new(
                    AArch64Opcode::AddRIShift12,
                    vec![vreg(0), vreg(1), MachOperand::Imm(-1)],
                ),
                rule_add_ri_negative_canonicalize(),
            ),
            (
                MachInst::new(AArch64Opcode::NeonAddV, vec![fpr(0), fpr(3), fpr(3)]),
                rule_add_self_to_shl(),
            ),
            (
                MachInst::new(AArch64Opcode::NeonSubV, vec![fpr(0), fpr(3), fpr(3)]),
                rule_sub_self_zero(),
            ),
        ];

        for (inst, rule) in cases {
            let opcode = inst.opcode;
            let (mut func, entry) = single_block_func(vec![inst]);
            let mut engine = RewriteEngine::new();
            engine.register(rule);
            let stats = engine.run_to_fixpoint(&mut func, 4);

            assert_eq!(stats.rewrites, 0, "{opcode:?} matched a scalar identity");
            assert_eq!(func.inst(func.block(entry).insts[0]).opcode, opcode);
        }
    }

    #[test]
    fn scalar_mul_rule_rejects_neon_category_neighbor() {
        let fpr = |id| MachOperand::VReg(VReg::new(id, RegClass::Fpr128));
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![fpr(1), MachOperand::Imm(1)]),
            MachInst::new(AArch64Opcode::NeonMulV, vec![fpr(0), fpr(2), fpr(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_one_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);

        assert_eq!(stats.rewrites, 0, "NeonMulV matched scalar MulRR rule");
        let neon_mul = func.block(entry).insts[1];
        assert_eq!(func.inst(neon_mul).opcode, AArch64Opcode::NeonMulV);
    }

    #[test]
    fn lsl_ri_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_lsl_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands.len(), 2);
    }

    #[test]
    fn lsl_ri_nonzero_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(3)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_lsl_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn lsr_ri_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_lsr_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands.len(), 2);
    }

    #[test]
    fn lsr_ri_nonzero_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(5)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_lsr_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn asr_ri_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AsrRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_asr_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands.len(), 2);
    }

    #[test]
    fn asr_ri_nonzero_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AsrRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(9)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_asr_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn sub_self_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::SubRR,
            vec![vreg(0), vreg(7), vreg(7)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_self_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_ri());
        assert!(matches!(after.operands[1], MachOperand::Imm(0)));
    }

    #[test]
    fn sub_self_different_operands_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::SubRR,
            vec![vreg(0), vreg(7), vreg(8)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_self_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn orr_ri_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::OrrRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_orr_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands.len(), 2);
    }

    #[test]
    fn orr_ri_nonzero_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::OrrRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0x0f)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_orr_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn and_ri_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_and_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_ri());
        assert!(matches!(after.operands[1], MachOperand::Imm(0)));
    }

    #[test]
    fn and_ri_nonzero_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0xff)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_and_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn orr_self_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::OrrRR,
            vec![vreg(0), vreg(7), vreg(7)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_orr_self());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands.len(), 2);
    }

    #[test]
    fn orr_self_different_operands_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::OrrRR,
            vec![vreg(0), vreg(7), vreg(8)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_orr_self());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn and_self_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AndRR,
            vec![vreg(0), vreg(7), vreg(7)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_and_self());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands.len(), 2);
    }

    #[test]
    fn and_self_different_operands_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AndRR,
            vec![vreg(0), vreg(7), vreg(8)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_and_self());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // -----------------------------------------------------------------
    // Wave 3 single-instruction patterns.
    // -----------------------------------------------------------------

    #[test]
    fn self_move_fires_and_deletes() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::MovR,
            vec![vreg(0), vreg(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_self_move_delete());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        assert!(func.block(entry).insts.is_empty());
    }

    #[test]
    fn non_self_move_does_not_fire() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::MovR,
            vec![vreg(0), vreg(1)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_self_move_delete());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
        assert_eq!(func.block(entry).insts.len(), 1);
    }

    #[test]
    fn eor_ri_zero_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::EorRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_eor_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Target::mov_rr());
    }

    #[test]
    fn eor_ri_nonzero_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::EorRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0xaa)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_eor_ri_zero());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn and_ri_minus_one_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(-1)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_and_ri_minus_one());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Target::mov_rr());
    }

    #[test]
    fn and_ri_minus_two_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(-2)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_and_ri_minus_one());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn orr_ri_minus_one_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::OrrRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(-1)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_orr_ri_minus_one());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Target::mov_ri());
        assert!(matches!(inst.operands[1], MachOperand::Imm(-1)));
    }

    #[test]
    fn orr_ri_other_nonzero_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::OrrRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0x7f)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_orr_ri_minus_one());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn add_rr_self_to_shl_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(0), vreg(3), vreg(3)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_self_to_shl());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Target::shl_ri());
        assert!(matches!(inst.operands[2], MachOperand::Imm(1)));
    }

    #[test]
    fn add_rr_distinct_operands_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(0), vreg(3), vreg(4)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_self_to_shl());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn nop_delete_fires() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Nop, vec![]),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_nop_delete());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        // Only Ret remains.
        assert_eq!(func.block(entry).insts.len(), 1);
    }

    #[test]
    fn nop_delete_does_not_touch_ret() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_nop_delete());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
        assert_eq!(func.block(entry).insts.len(), 1);
    }

    #[test]
    fn add_ri_negative_rewrites_to_sub() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(-7)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_negative_canonicalize());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Opcode::SubRI);
        assert!(matches!(inst.operands[2], MachOperand::Imm(7)));
    }

    #[test]
    fn add_ri_positive_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(4)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_negative_canonicalize());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn add_ri_int_min_does_not_fire() {
        // i64::MIN is excluded to avoid -i64::MIN overflow.
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(i64::MIN)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_negative_canonicalize());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn sub_ri_negative_rewrites_to_add() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(-11)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_ri_negative_canonicalize());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Opcode::AddRI);
        assert!(matches!(inst.operands[2], MachOperand::Imm(11)));
    }

    #[test]
    fn sub_ri_positive_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(3)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_ri_negative_canonicalize());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn bic_self_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::BicRR,
            vec![vreg(0), vreg(5), vreg(5)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_bic_self());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Target::mov_ri());
        assert!(matches!(inst.operands[1], MachOperand::Imm(0)));
    }

    #[test]
    fn bic_distinct_operands_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::BicRR,
            vec![vreg(0), vreg(5), vreg(6)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_bic_self());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn orn_self_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::OrnRR,
            vec![vreg(0), vreg(5), vreg(5)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_orn_self());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Target::mov_ri());
        assert!(matches!(inst.operands[1], MachOperand::Imm(-1)));
    }

    #[test]
    fn orn_distinct_operands_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::OrnRR,
            vec![vreg(0), vreg(5), vreg(6)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_orn_self());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn csel_same_arms_fires() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::Csel,
            vec![vreg(0), vreg(9), vreg(9), MachOperand::Imm(13)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_csel_same_arms());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let inst = func.inst(func.block(entry).insts[0]);
        assert_eq!(inst.opcode, AArch64Target::mov_rr());
    }

    #[test]
    fn csel_distinct_arms_does_not_fire() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::Csel,
            vec![vreg(0), vreg(9), vreg(10), MachOperand::Imm(13)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_csel_same_arms());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // -----------------------------------------------------------------
    // Multi-instruction patterns (same-opcode def-use).
    // -----------------------------------------------------------------

    #[test]
    fn neg_neg_collapses_to_mov() {
        // neg v1, v0 ; neg v2, v1  →  neg v1, v0 ; mov v2, v0
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Neg, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_neg_neg());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second_id = func.block(entry).insts[1];
        let second = func.inst(second_id);
        assert_eq!(second.opcode, AArch64Target::mov_rr());
        // Source should be v0 (the inner NEG's source), not v1.
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn neg_over_non_neg_does_not_fire() {
        // add v1, v0, v0 ; neg v2, v1   — no double negation.
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(1), vreg(0), vreg(0)]),
            MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_neg_neg());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn sxtb_sxtb_collapses() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Sxtb, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Sxtb, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sxtb_sxtb());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Sxtb);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn sxtb_over_non_sxtb_does_not_fire() {
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Sxth, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Sxtb, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sxtb_sxtb());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn uxtb_uxtb_collapses() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Uxtb, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Uxtb, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_uxtb_uxtb());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Uxtb);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn uxth_uxth_collapses() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Uxth, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Uxth, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_uxth_uxth());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Uxth);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn uxth_over_uxtb_does_not_collapse_under_same_ext() {
        // Different opcode — the same-opcode rule should NOT fire (that's a
        // future narrower-subsumes-wider rule).
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Uxtb, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Uxth, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_uxth_uxth());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // -----------------------------------------------------------------
    // Invariant tests.
    // -----------------------------------------------------------------

    #[test]
    fn proof_is_preserved_on_replace() {
        use trust_cg_ir::ProofAnnotation;
        let mut inst = MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        );
        inst.proof = Some(ProofAnnotation::NoOverflow);
        let (mut func, entry) = single_block_func(vec![inst]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_zero());
        let _ = engine.run_to_fixpoint(&mut func, 4);
        let inst_id = func.block(entry).insts[0];
        assert_eq!(func.inst(inst_id).proof, Some(ProofAnnotation::NoOverflow));
    }

    #[test]
    fn source_loc_is_preserved_on_replace() {
        use trust_cg_ir::SourceLoc;
        let mut inst = MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        );
        inst.source_loc = Some(SourceLoc {
            file: 1,
            line: 42,
            col: 3,
        });
        let (mut func, entry) = single_block_func(vec![inst]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_zero());
        let _ = engine.run_to_fixpoint(&mut func, 4);
        let inst_id = func.block(entry).insts[0];
        let after = func.inst(inst_id);
        assert!(after.source_loc.is_some());
        assert_eq!(after.source_loc.unwrap().line, 42);
    }

    #[test]
    fn fixpoint_terminates_quickly_on_noop() {
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(5)],
        )]);
        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let stats = engine.run_to_fixpoint(&mut func, 16);
        // Fixpoint reached in one iteration with no changes.
        assert_eq!(stats.iterations, 1);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn benefit_wins_conflict() {
        fn delete_rewrite(_ctx: &MatchCtx<'_>) -> RewriteAction {
            RewriteAction::Delete
        }
        let high_benefit = RuleBuilder::match_category("add-ri-zero-delete", OpcodeCategory::AddRI)
            .benefit(100)
            .constrain(ImmEquals { idx: 2, value: 0 })
            .rewrite_with(delete_rewrite);

        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(0)],
        )]);

        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_zero());
        engine.register(high_benefit);
        let _ = engine.run_to_fixpoint(&mut func, 4);
        // Higher-benefit rule deletes.
        assert!(func.block(entry).insts.is_empty());
    }

    // -----------------------------------------------------------------
    // Wave 4 — definer-driven multi-instruction patterns.
    // -----------------------------------------------------------------

    #[test]
    fn add_neg_rhs_rewrites_to_sub() {
        // neg v2, v1 ; add v3, v0, v2   →   neg v2, v1 ; sub v3, v0, v1
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(1)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(2)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_neg_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Target::sub_rr());
        assert_eq!(second.operands[0], vreg(3));
        assert_eq!(second.operands[1], vreg(0));
        // Inner NEG source is v1, not v2.
        assert_eq!(second.operands[2], vreg(1));
    }

    #[test]
    fn add_neg_lhs_rewrites_to_sub_with_swap() {
        // neg v2, v1 ; add v3, v2, v0   →   neg v2, v1 ; sub v3, v0, v1
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(1)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(2), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_neg_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Target::sub_rr());
        assert_eq!(second.operands[0], vreg(3));
        // Minuend is the non-neg operand (v0).
        assert_eq!(second.operands[1], vreg(0));
        // Subtrahend is the NEG's inner source (v1).
        assert_eq!(second.operands[2], vreg(1));
    }

    #[test]
    fn add_neg_does_not_fire_without_neg_definer() {
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(2)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_neg_rhs());
        engine.register(rule_add_neg_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn sub_neg_rewrites_to_add() {
        // neg v2, v1 ; sub v3, v0, v2   →   neg v2, v1 ; add v3, v0, v1
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(1)]),
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(0), vreg(2)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_neg_to_add());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Target::add_rr());
        assert_eq!(second.operands[1], vreg(0));
        assert_eq!(second.operands[2], vreg(1));
    }

    #[test]
    fn sub_neg_does_not_fire_when_minuend_is_neg() {
        // The rule only probes the subtrahend (operand[2]).
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(1)]),
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(2), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_neg_to_add());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn neg_sub_swaps_operands() {
        // sub v2, v0, v1 ; neg v3, v2   →   sub v2, v0, v1 ; sub v3, v1, v0
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::Neg, vec![vreg(3), vreg(2)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_neg_sub_swap());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Target::sub_rr());
        assert_eq!(second.operands[0], vreg(3));
        // Operands swapped: (x, y) becomes (y, x).
        assert_eq!(second.operands[1], vreg(1));
        assert_eq!(second.operands[2], vreg(0));
    }

    #[test]
    fn neg_sub_does_not_fire_over_non_sub_definer() {
        // neg(add(..)) should not fire the sub-swap rule.
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::Neg, vec![vreg(3), vreg(2)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_neg_sub_swap());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn neg_neg_preferred_over_neg_sub_swap() {
        // neg(neg(x)) must reduce to mov — the double-neg rule has higher
        // benefit than neg-sub-swap and should win.
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Neg, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_neg_neg());
        engine.register(rule_neg_sub_swap());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Target::mov_rr());
    }

    #[test]
    fn sxth_of_sxtb_collapses_to_sxtb() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Sxtb, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Sxth, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sxth_of_sxtb());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Sxtb);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn sxtw_of_sxtb_collapses_to_sxtb() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Sxtb, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Sxtw, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sxtw_of_narrower_sext());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Sxtb);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn sxtw_of_sxth_collapses_to_sxth() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Sxth, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Sxtw, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sxtw_of_narrower_sext());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Sxth);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn sxtw_does_not_fire_over_same_opcode() {
        // sxtw(sxtw(x)) is handled by the same-opcode rule, not the narrower rule.
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Sxtw, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Sxtw, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sxtw_of_narrower_sext());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn uxth_of_uxtb_collapses_to_uxtb() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Uxtb, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Uxth, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_uxth_of_uxtb());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Uxtb);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn uxtw_of_uxtb_collapses_to_uxtb() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Uxtb, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Uxtw, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_uxtw_of_narrower_zext());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Uxtb);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn uxtw_of_uxth_collapses_to_uxth() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Uxth, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Uxtw, vec![vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_uxtw_of_narrower_zext());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let second = func.inst(func.block(entry).insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::Uxth);
        assert_eq!(second.operands[1], vreg(0));
    }

    #[test]
    fn narrower_ext_rules_do_not_cross_blocks() {
        // If the inner Sxtb is in another block (simulated here by no
        // def map entry), the rule should not fire.
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::Sxth,
            vec![vreg(2), vreg(99)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sxth_of_sxtb());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // -----------------------------------------------------------------
    // Pipeline-level: full ruleset still sees these patterns.
    // -----------------------------------------------------------------

    #[test]
    fn full_ruleset_wave4_mixed_block() {
        // Block with one NEG + ADD pair and one SXTB + SXTW chain.
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Neg, vec![vreg(2), vreg(1)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(2)]),
            MachInst::new(AArch64Opcode::Sxtb, vec![vreg(5), vreg(4)]),
            MachInst::new(AArch64Opcode::Sxtw, vec![vreg(6), vreg(5)]),
        ]);
        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let stats = engine.run_to_fixpoint(&mut func, 8);
        // Two rewrites: AddRR→SubRR (via rule_add_neg_rhs), Sxtw→Sxtb.
        assert_eq!(stats.rewrites, 2);
        let ids = func.block(entry).insts.clone();
        assert_eq!(func.inst(ids[1]).opcode, AArch64Target::sub_rr());
        assert_eq!(func.inst(ids[3]).opcode, AArch64Opcode::Sxtb);
    }

    #[test]
    fn full_ruleset_migrates_mixed_block() {
        // A little fixture that exercises several patterns together.
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::Nop, vec![]),
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![vreg(0), vreg(1), MachOperand::Imm(0)],
            ),
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(2), vreg(3), vreg(3)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(5), vreg(5)]),
            MachInst::new(
                AArch64Opcode::OrrRI,
                vec![vreg(6), vreg(7), MachOperand::Imm(-1)],
            ),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        ]);
        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let stats = engine.run_to_fixpoint(&mut func, 8);
        // All four non-nop/ret instructions get rewritten; the nop is
        // deleted. That's 5 rewrites.
        assert_eq!(stats.rewrites, 5);
        // After the pass we expect: [AddRI→MovR, EorRR→MovI, AddRR→LslRI,
        // OrrRI→MovI, Ret]. Nop was deleted.
        let ids = func.block(entry).insts.clone();
        assert_eq!(ids.len(), 5);
        assert_eq!(func.inst(ids[0]).opcode, AArch64Target::mov_rr());
        assert_eq!(func.inst(ids[1]).opcode, AArch64Target::mov_ri());
        assert_eq!(func.inst(ids[2]).opcode, AArch64Target::shl_ri());
        assert_eq!(func.inst(ids[3]).opcode, AArch64Target::mov_ri());
        assert_eq!(func.inst(ids[4]).opcode, AArch64Opcode::Ret);
    }

    // -----------------------------------------------------------------
    // Wave 5 — MUL / UDIV / SDIV with a MovI constant operand.
    // -----------------------------------------------------------------

    #[test]
    fn mul_by_zero_rhs_collapses() {
        // v0 = movi #0; v2 = mul v1, v0  →  v2 = movi #0
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(0)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_zero_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_ri());
        assert!(matches!(after.operands[1], MachOperand::Imm(0)));
    }

    #[test]
    fn mul_by_zero_lhs_collapses() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(0)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_zero_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_ri());
        assert!(matches!(after.operands[1], MachOperand::Imm(0)));
    }

    #[test]
    fn mul_by_one_rhs_becomes_mov() {
        // v0 = movi #1; v2 = mul v1, v0  →  v2 = mov v1
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(1)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_one_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(1));
    }

    #[test]
    fn mul_by_one_lhs_becomes_mov() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(1)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_one_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(1));
    }

    #[test]
    fn mul_by_neg_one_rhs_becomes_neg() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(-1)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_neg_one_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Opcode::Neg);
        assert_eq!(after.operands[1], vreg(1));
    }

    #[test]
    fn mul_by_neg_one_lhs_becomes_neg() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(-1)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_neg_one_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Opcode::Neg);
        assert_eq!(after.operands[1], vreg(1));
    }

    #[test]
    fn mul_by_non_const_does_not_fire() {
        // Divisor is not produced by MovI.
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(2), vreg(1), vreg(5)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_one_rhs());
        engine.register(rule_mul_by_zero_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn udiv_by_one_becomes_mov() {
        // v0 = movi #1; v2 = udiv v1, v0 → v2 = mov v1
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(1)]),
            MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_udiv_by_one());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(1));
    }

    #[test]
    fn sdiv_by_one_becomes_mov() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(1)]),
            MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sdiv_by_one());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(1));
    }

    #[test]
    fn sdiv_by_neg_one_becomes_neg() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(-1)]),
            MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sdiv_by_neg_one());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Opcode::Neg);
        assert_eq!(after.operands[1], vreg(1));
    }

    #[test]
    fn udiv_by_two_does_not_fire_here() {
        // `udiv_by_one` must not fire for divisor=2. Pattern 24 is handled by
        // the independently registered `rule_udiv_pow2`.
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(2)]),
            MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_udiv_by_one());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // -----------------------------------------------------------------
    // Wave 5 — SUB(ADD(x, y), y) → MOV x and commuted.
    // -----------------------------------------------------------------

    #[test]
    fn sub_of_add_cancels_rhs_shape() {
        // v2 = add v0, v1; v3 = sub v2, v1  →  v3 = mov v0
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_of_add_cancel_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(0));
    }

    #[test]
    fn sub_of_add_cancels_lhs_shape() {
        // v2 = add v1, v0; v3 = sub v2, v1  →  v3 = mov v0
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_of_add_cancel_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(0));
    }

    #[test]
    fn sub_of_add_does_not_fire_without_match() {
        // Subtrahend does not match either ADD operand.
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(2), vreg(7)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_sub_of_add_cancel_rhs());
        engine.register(rule_sub_of_add_cancel_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // -----------------------------------------------------------------
    // Wave 5 — ADD(SUB(x, y), y) and commutations.
    // -----------------------------------------------------------------

    #[test]
    fn add_of_sub_cancels_lhs_def() {
        // v2 = sub v0, v1; v3 = add v2, v1  →  v3 = mov v0
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(2), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_of_sub_cancel_lhs_def());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(0));
    }

    #[test]
    fn add_of_sub_cancels_rhs_def() {
        // v2 = sub v0, v1; v3 = add v1, v2  →  v3 = mov v0
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_of_sub_cancel_rhs_def());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(0));
    }

    // -----------------------------------------------------------------
    // Wave 5 — EOR(EOR(x, y), y) and three commutations.
    // -----------------------------------------------------------------

    #[test]
    fn eor_cancel_all_four_shapes() {
        // Shape A: v2 = eor v0, v1; v3 = eor v2, v1  → v3 = mov v0
        let (mut func_a, entry_a) = single_block_func(vec![
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(2), vreg(1)]),
        ]);
        let mut engine_a = RewriteEngine::new();
        engine_a.register(rule_eor_cancel_lhs_def_outer_rhs_matches_inner_rhs());
        let stats_a = engine_a.run_to_fixpoint(&mut func_a, 4);
        assert_eq!(stats_a.rewrites, 1);
        let after_a = func_a.inst(func_a.block(entry_a).insts[1]);
        assert_eq!(after_a.opcode, AArch64Target::mov_rr());
        assert_eq!(after_a.operands[1], vreg(0));

        // Shape B: v2 = eor v1, v0; v3 = eor v2, v1  → v3 = mov v0
        let (mut func_b, entry_b) = single_block_func(vec![
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(2), vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(2), vreg(1)]),
        ]);
        let mut engine_b = RewriteEngine::new();
        engine_b.register(rule_eor_cancel_lhs_def_outer_rhs_matches_inner_lhs());
        let stats_b = engine_b.run_to_fixpoint(&mut func_b, 4);
        assert_eq!(stats_b.rewrites, 1);
        let after_b = func_b.inst(func_b.block(entry_b).insts[1]);
        assert_eq!(after_b.opcode, AArch64Target::mov_rr());
        assert_eq!(after_b.operands[1], vreg(0));

        // Shape C: v2 = eor v0, v1; v3 = eor v1, v2  → v3 = mov v0
        let (mut func_c, entry_c) = single_block_func(vec![
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        ]);
        let mut engine_c = RewriteEngine::new();
        engine_c.register(rule_eor_cancel_rhs_def_outer_lhs_matches_inner_rhs());
        let stats_c = engine_c.run_to_fixpoint(&mut func_c, 4);
        assert_eq!(stats_c.rewrites, 1);
        let after_c = func_c.inst(func_c.block(entry_c).insts[1]);
        assert_eq!(after_c.opcode, AArch64Target::mov_rr());
        assert_eq!(after_c.operands[1], vreg(0));

        // Shape D: v2 = eor v1, v0; v3 = eor v1, v2  → v3 = mov v0
        let (mut func_d, entry_d) = single_block_func(vec![
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(2), vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        ]);
        let mut engine_d = RewriteEngine::new();
        engine_d.register(rule_eor_cancel_rhs_def_outer_lhs_matches_inner_lhs());
        let stats_d = engine_d.run_to_fixpoint(&mut func_d, 4);
        assert_eq!(stats_d.rewrites, 1);
        let after_d = func_d.inst(func_d.block(entry_d).insts[1]);
        assert_eq!(after_d.opcode, AArch64Target::mov_rr());
        assert_eq!(after_d.operands[1], vreg(0));
    }

    /// The four eor-cancel rules match `OpcodeCategory::XorRR` on the OUTER
    /// instruction, and that category also covers the shifted-register forms.
    /// `eor v3, v2, v1, LSL #k` is `v2 ^ (v1 << k)`, so the XOR-cancellation
    /// identity does NOT hold and the pair must be left alone.
    ///
    /// Same bug class as `rule_xor_self_zero`: the guard was `< 3`, which
    /// admitted the 4-operand forms.
    #[test]
    fn eor_cancel_shifted_outer_does_not_fire() {
        let rules: Vec<(&str, fn() -> Rule)> = vec![
            (
                "lhs_def_rhs_rhs",
                rule_eor_cancel_lhs_def_outer_rhs_matches_inner_rhs,
            ),
            (
                "lhs_def_rhs_lhs",
                rule_eor_cancel_lhs_def_outer_rhs_matches_inner_lhs,
            ),
            (
                "rhs_def_lhs_rhs",
                rule_eor_cancel_rhs_def_outer_lhs_matches_inner_rhs,
            ),
            (
                "rhs_def_lhs_lhs",
                rule_eor_cancel_rhs_def_outer_lhs_matches_inner_lhs,
            ),
        ];
        for outer_opcode in [
            AArch64Opcode::EorRRLsl,
            AArch64Opcode::EorRRLsr,
            AArch64Opcode::EorRRShift,
        ] {
            for (name, mk) in &rules {
                // Cover both operand orders so every rule sees its own shape.
                for outer in [
                    vec![vreg(3), vreg(2), vreg(1), MachOperand::Imm(3)],
                    vec![vreg(3), vreg(1), vreg(2), MachOperand::Imm(3)],
                ] {
                    let (mut func, _) = single_block_func(vec![
                        MachInst::new(AArch64Opcode::EorRR, vec![vreg(2), vreg(0), vreg(1)]),
                        MachInst::new(outer_opcode, outer),
                    ]);
                    let mut engine = RewriteEngine::new();
                    engine.register(mk());
                    let stats = engine.run_to_fixpoint(&mut func, 4);
                    assert_eq!(
                        stats.rewrites, 0,
                        "{name}: shifted outer {outer_opcode:?} must not be cancelled"
                    );
                }
            }
        }
    }

    /// `OpcodeCategory::AddRI` covers `AddRIShift12`, which has the SAME
    /// 3-operand shape as `AddRI` but means `Rn + (imm12 << 12)`. An operand
    /// count cannot separate them, so the rule discriminates on the opcode.
    /// Rewriting it to a plain `SubRI` would be wrong by a factor of 4096.
    #[test]
    fn add_ri_shift12_negative_is_not_canonicalized() {
        let (mut func, entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRIShift12,
            vec![vreg(0), vreg(1), MachOperand::Imm(-1)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_add_ri_negative_canonicalize());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0, "AddRIShift12 must not lose its <<12");
        let after = func.inst(func.block(entry).insts[0]);
        assert_eq!(after.opcode, AArch64Opcode::AddRIShift12);

        // The plain form is still canonicalized, so the guard costs nothing.
        let (mut plain, plain_entry) = single_block_func(vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), MachOperand::Imm(-1)],
        )]);
        let mut engine2 = RewriteEngine::new();
        engine2.register(rule_add_ri_negative_canonicalize());
        assert_eq!(engine2.run_to_fixpoint(&mut plain, 4).rewrites, 1);
        let after_plain = plain.inst(plain.block(plain_entry).insts[0]);
        assert_eq!(after_plain.opcode, AArch64Target::sub_ri());
        assert_eq!(after_plain.operands[2], MachOperand::Imm(1));
    }

    #[test]
    fn eor_cancel_does_not_fire_without_shared_operand() {
        // Inner EOR produces v2 from v0 and v1; outer EOR uses v2 and v7.
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(2), vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(2), vreg(7)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_eor_cancel_lhs_def_outer_rhs_matches_inner_rhs());
        engine.register(rule_eor_cancel_lhs_def_outer_rhs_matches_inner_lhs());
        engine.register(rule_eor_cancel_rhs_def_outer_lhs_matches_inner_rhs());
        engine.register(rule_eor_cancel_rhs_def_outer_lhs_matches_inner_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // -----------------------------------------------------------------
    // Wave 5 — full ruleset sees the full set of Wave-5 migrations.
    // -----------------------------------------------------------------

    #[test]
    fn full_ruleset_wave5_mixed_block() {
        // Build a block that exercises one representative of each Wave 5
        // family: MUL-by-one, UDIV-by-one, SUB-of-ADD cancel, EOR-EOR
        // cancel.
        let (mut func, entry) = single_block_func(vec![
            // v10 = movi #1
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(1)]),
            // v11 = mul v0, v10            (pattern 25 rhs → mov v0)
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(11), vreg(0), vreg(10)]),
            // v12 = udiv v1, v10           (pattern 44 → mov v1)
            MachInst::new(AArch64Opcode::UDiv, vec![vreg(12), vreg(1), vreg(10)]),
            // v13 = add v2, v3
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(13), vreg(2), vreg(3)]),
            // v14 = sub v13, v3            (pattern 42 rhs → mov v2)
            MachInst::new(AArch64Opcode::SubRR, vec![vreg(14), vreg(13), vreg(3)]),
            // v15 = eor v4, v5
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(15), vreg(4), vreg(5)]),
            // v16 = eor v15, v5            (pattern 52a → mov v4)
            MachInst::new(AArch64Opcode::EorRR, vec![vreg(16), vreg(15), vreg(5)]),
        ]);
        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let stats = engine.run_to_fixpoint(&mut func, 16);
        // Four of the seven instructions rewrite: mul, udiv, sub, outer-eor.
        assert_eq!(stats.rewrites, 4);
        let ids = func.block(entry).insts.clone();
        assert_eq!(func.inst(ids[1]).opcode, AArch64Target::mov_rr());
        assert_eq!(func.inst(ids[1]).operands[1], vreg(0));
        assert_eq!(func.inst(ids[2]).opcode, AArch64Target::mov_rr());
        assert_eq!(func.inst(ids[2]).operands[1], vreg(1));
        assert_eq!(func.inst(ids[4]).opcode, AArch64Target::mov_rr());
        assert_eq!(func.inst(ids[4]).operands[1], vreg(2));
        assert_eq!(func.inst(ids[6]).opcode, AArch64Target::mov_rr());
        assert_eq!(func.inst(ids[6]).operands[1], vreg(4));
    }

    // -----------------------------------------------------------------
    // Wave 6 — MADD / MSUB with MovI(#0) or MovI(#1) multiplicand.
    // MADD operands: [Rd, Rn, Rm, Ra]; Rd = Ra + Rn * Rm.
    // MSUB operands: [Rd, Rn, Rm, Ra]; Rd = Ra - Rn * Rm.
    // -----------------------------------------------------------------

    #[test]
    fn madd_zero_at_rm_collapses_to_mov_ra() {
        // MADD operands: [Rd, Rn, Rm, Ra].
        // v10 = movi #0; Rd=v3, Rn=v1, Rm=v10, Ra=v9  →  v3 = mov v9
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(0)]),
            MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(3), vreg(1), vreg(10), vreg(9)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_madd_by_zero_at_rm());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[0], vreg(3));
        assert_eq!(after.operands[1], vreg(9));
    }

    #[test]
    fn madd_zero_at_rn_collapses_to_mov_ra() {
        // v10 = movi #0; v3 = madd Rd=v3, Rn=v10, Rm=v2, Ra=v9  →  v3 = mov v9
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(0)]),
            MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(3), vreg(10), vreg(2), vreg(9)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_madd_by_zero_at_rn());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(9));
    }

    #[test]
    fn madd_one_at_rm_becomes_add_rn_ra() {
        // v10 = movi #1; Rd=v3, Rn=v1, Rm=v10, Ra=v9  →  add v3, v1, v9
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(1)]),
            MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(3), vreg(1), vreg(10), vreg(9)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_madd_by_one_at_rm());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::add_rr());
        assert_eq!(after.operands[0], vreg(3));
        assert_eq!(after.operands[1], vreg(1)); // the "other" (Rn)
        assert_eq!(after.operands[2], vreg(9)); // Ra
    }

    #[test]
    fn madd_one_at_rn_becomes_add_rm_ra() {
        // v10 = movi #1; Rd=v3, Rn=v10, Rm=v2, Ra=v9  →  add v3, v2, v9
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(1)]),
            MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(3), vreg(10), vreg(2), vreg(9)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_madd_by_one_at_rn());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::add_rr());
        assert_eq!(after.operands[0], vreg(3));
        assert_eq!(after.operands[1], vreg(2)); // the "other" (Rm)
        assert_eq!(after.operands[2], vreg(9)); // Ra
    }

    #[test]
    fn madd_with_nonconst_multiplicands_does_not_fire() {
        // No MovI — no rules should fire.
        let (mut func, _) = single_block_func(vec![MachInst::new(
            AArch64Opcode::Madd,
            vec![vreg(3), vreg(1), vreg(2), vreg(9)],
        )]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_madd_by_zero_at_rn());
        engine.register(rule_madd_by_zero_at_rm());
        engine.register(rule_madd_by_one_at_rn());
        engine.register(rule_madd_by_one_at_rm());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    #[test]
    fn msub_zero_at_rm_collapses_to_mov_ra() {
        // v10 = movi #0; Rd=v3, Rn=v1, Rm=v10, Ra=v9  →  v3 = mov v9
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(0)]),
            MachInst::new(
                AArch64Opcode::Msub,
                vec![vreg(3), vreg(1), vreg(10), vreg(9)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_msub_by_zero_at_rm());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(9));
    }

    #[test]
    fn msub_zero_at_rn_collapses_to_mov_ra() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(0)]),
            MachInst::new(
                AArch64Opcode::Msub,
                vec![vreg(3), vreg(10), vreg(2), vreg(9)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_msub_by_zero_at_rn());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::mov_rr());
        assert_eq!(after.operands[1], vreg(9));
    }

    #[test]
    fn msub_one_at_rm_becomes_sub_ra_rn() {
        // v10 = movi #1; Rd=v3, Rn=v1, Rm=v10, Ra=v9  →  sub v3, v9, v1
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(1)]),
            MachInst::new(
                AArch64Opcode::Msub,
                vec![vreg(3), vreg(1), vreg(10), vreg(9)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_msub_by_one_at_rm());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::sub_rr());
        assert_eq!(after.operands[0], vreg(3));
        assert_eq!(after.operands[1], vreg(9)); // Ra
        assert_eq!(after.operands[2], vreg(1)); // the "other" (Rn)
    }

    #[test]
    fn msub_one_at_rn_becomes_sub_ra_rm() {
        // v10 = movi #1; Rd=v3, Rn=v10, Rm=v2, Ra=v9  →  sub v3, v9, v2
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(10), MachOperand::Imm(1)]),
            MachInst::new(
                AArch64Opcode::Msub,
                vec![vreg(3), vreg(10), vreg(2), vreg(9)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_msub_by_one_at_rn());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::sub_rr());
        assert_eq!(after.operands[0], vreg(3));
        assert_eq!(after.operands[1], vreg(9)); // Ra
        assert_eq!(after.operands[2], vreg(2)); // the "other" (Rm)
    }

    #[test]
    fn full_ruleset_wave6_madd_msub_mixed() {
        // Mixed block covering MADD #0/#1 and MSUB #0/#1 in one fixpoint run.
        let (mut func, entry) = single_block_func(vec![
            // v20 = movi #0
            MachInst::new(AArch64Opcode::MovI, vec![vreg(20), MachOperand::Imm(0)]),
            // v21 = movi #1
            MachInst::new(AArch64Opcode::MovI, vec![vreg(21), MachOperand::Imm(1)]),
            // v30 = madd Rd=v30, Rn=v1, Rm=v20, Ra=v2   → v30 = mov v2 (pattern 36)
            MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(30), vreg(1), vreg(20), vreg(2)],
            ),
            // v31 = madd Rd=v31, Rn=v21, Rm=v3, Ra=v4  → v31 = add v3, v4 (pattern 35)
            MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(31), vreg(21), vreg(3), vreg(4)],
            ),
            // v32 = msub Rd=v32, Rn=v5, Rm=v20, Ra=v6  → v32 = mov v6 (pattern 38)
            MachInst::new(
                AArch64Opcode::Msub,
                vec![vreg(32), vreg(5), vreg(20), vreg(6)],
            ),
            // v33 = msub Rd=v33, Rn=v21, Rm=v7, Ra=v8  → v33 = sub v8, v7 (pattern 37)
            MachInst::new(
                AArch64Opcode::Msub,
                vec![vreg(33), vreg(21), vreg(7), vreg(8)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let stats = engine.run_to_fixpoint(&mut func, 16);
        // All four MADD/MSUB instructions rewrite.
        assert_eq!(stats.rewrites, 4);
        let ids = func.block(entry).insts.clone();
        // v30 → mov v30, v2
        assert_eq!(func.inst(ids[2]).opcode, AArch64Target::mov_rr());
        assert_eq!(func.inst(ids[2]).operands[1], vreg(2));
        // v31 → add v31, v3, v4
        assert_eq!(func.inst(ids[3]).opcode, AArch64Target::add_rr());
        assert_eq!(func.inst(ids[3]).operands[1], vreg(3));
        assert_eq!(func.inst(ids[3]).operands[2], vreg(4));
        // v32 → mov v32, v6
        assert_eq!(func.inst(ids[4]).opcode, AArch64Target::mov_rr());
        assert_eq!(func.inst(ids[4]).operands[1], vreg(6));
        // v33 → sub v33, v8, v7
        assert_eq!(func.inst(ids[5]).opcode, AArch64Target::sub_rr());
        assert_eq!(func.inst(ids[5]).operands[1], vreg(8));
        assert_eq!(func.inst(ids[5]).operands[2], vreg(7));
    }

    // Wave 7: pattern 23 (mul by pow2 -> lsl).
    #[test]
    fn mul_pow2_rhs_fires_and_uses_log2_shift() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(1), MachOperand::Imm(8)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_pow2_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::shl_ri());
        assert_eq!(after.operands[1], vreg(0));
        assert_eq!(after.operands[2], MachOperand::Imm(3));
    }

    #[test]
    fn mul_pow2_lhs_fires_and_keeps_other_operand() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(1), MachOperand::Imm(16)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(1), vreg(3)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_pow2_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Target::shl_ri());
        assert_eq!(after.operands[1], vreg(3));
        assert_eq!(after.operands[2], MachOperand::Imm(4));
    }

    #[test]
    fn mul_non_pow2_does_not_fire() {
        let (mut func, _entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(1), MachOperand::Imm(6)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_pow2_rhs());
        engine.register(rule_mul_pow2_lhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // Wave 7: pattern 24 (udiv by pow2 -> lsr).
    #[test]
    fn udiv_pow2_fires_and_uses_log2_shift() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(1), MachOperand::Imm(32)]),
            MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_udiv_pow2());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Opcode::LsrRI);
        assert_eq!(after.operands[1], vreg(0));
        assert_eq!(after.operands[2], MachOperand::Imm(5));
    }

    #[test]
    fn udiv_pow2_does_not_fire_when_dividend_is_movi_pow2() {
        let (mut func, _entry) = single_block_func(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(1), MachOperand::Imm(8)]),
            MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_udiv_pow2());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // Wave 7: pattern 29 (lsl(lsr) -> and clear-low).
    #[test]
    fn lsl_lsr_to_and_clears_low_bits_64() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(1), vreg(0), MachOperand::Imm(4)],
            ),
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(2), vreg(1), MachOperand::Imm(4)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_lsl_lsr_to_and());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Opcode::AndRI);
        assert_eq!(after.operands[1], vreg(0));
        assert_eq!(after.operands[2], MachOperand::Imm(!0xF_i64));
    }

    #[test]
    fn lsl_lsr_to_and_does_not_fire_on_mismatched_shift() {
        let (mut func, _entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(1), vreg(0), MachOperand::Imm(4)],
            ),
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(2), vreg(1), MachOperand::Imm(5)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_lsl_lsr_to_and());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 0);
    }

    // Wave 7: pattern 32 (lsr(lsl) -> and clear-high).
    #[test]
    fn lsr_lsl_to_and_clears_high_bits_64() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(1), vreg(0), MachOperand::Imm(40)],
            ),
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(2), vreg(1), MachOperand::Imm(40)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        engine.register(rule_lsr_lsl_to_and());
        let stats = engine.run_to_fixpoint(&mut func, 4);
        assert_eq!(stats.rewrites, 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Opcode::AndRI);
        assert_eq!(after.operands[1], vreg(0));
        assert_eq!(after.operands[2], MachOperand::Imm((1_i64 << 24) - 1));
    }

    #[test]
    fn shift_pair_to_and_registered_in_migrated_set() {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(1), vreg(0), MachOperand::Imm(8)],
            ),
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![vreg(2), vreg(1), MachOperand::Imm(8)],
            ),
        ]);
        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let stats = engine.run_to_fixpoint(&mut func, 8);
        assert!(stats.rewrites >= 1);
        let after = func.inst(func.block(entry).insts[1]);
        assert_eq!(after.opcode, AArch64Opcode::AndRI);
        assert_eq!(after.operands[2], MachOperand::Imm(!0xFF_i64));
    }
}
