// trust-cg-opt - Rewrite constraints
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`Constraint`] is a semantic predicate evaluated after a rule's
//! [`Matcher`](super::Matcher) accepts an instruction.
//!
//! Constraints compose: a rule may require "operand 2 is zero", "operand
//! 1 equals operand 2", and "the operand-1 def is `Pure`" all at once.
//! Each check is independent; failing any one disqualifies the rule.

use trust_cg_ir::{AArch64Opcode, MachOperand, OpcodeCategory};

use crate::interfaces::OpInterfaces;
use crate::rewrite::matcher::MatchCtx;

/// Semantic predicate on a matched instruction.
///
/// Constraints run after the [`Matcher`](super::Matcher) returns true. They
/// can look at operand values, call the interface catalog, or walk the
/// in-block def map via [`MatchCtx::operand_def`].
pub trait Constraint: Send + Sync {
    /// Returns true if the rule may fire.
    fn check(&self, ctx: &MatchCtx<'_>) -> bool;
}

// ---------------------------------------------------------------------------
// Immediate predicates
// ---------------------------------------------------------------------------

/// Operand at `idx` is an immediate with the given value.
pub struct ImmEquals {
    pub idx: usize,
    pub value: i64,
}

impl Constraint for ImmEquals {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        matches!(ctx.inst.operands.get(self.idx), Some(MachOperand::Imm(v)) if *v == self.value)
    }
}

/// Operand at `idx` is an immediate matching an arbitrary predicate.
pub struct ImmIs {
    pub idx: usize,
    /// Immediate predicate, e.g., `|v| v < 0`.
    pub pred: fn(i64) -> bool,
}

impl Constraint for ImmIs {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        match ctx.inst.operands.get(self.idx) {
            Some(MachOperand::Imm(v)) => (self.pred)(*v),
            _ => false,
        }
    }
}

/// Operand at `idx` is an immediate that is a positive power of two.
pub struct ImmIsPowerOfTwo {
    pub idx: usize,
}

impl Constraint for ImmIsPowerOfTwo {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        match ctx.inst.operands.get(self.idx) {
            Some(MachOperand::Imm(v)) => *v > 0 && (*v & (*v - 1)) == 0,
            _ => false,
        }
    }
}

/// Operand at `idx` is a strictly negative immediate, but not `i64::MIN`.
///
/// Used by patterns that negate the immediate to canonicalize the
/// opcode (e.g. `add x, y, #-N` → `sub x, y, #N`). `i64::MIN` is
/// excluded because `-i64::MIN` overflows.
pub struct ImmNegativeNonMin {
    pub idx: usize,
}

impl Constraint for ImmNegativeNonMin {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        matches!(
            ctx.inst.operands.get(self.idx),
            Some(MachOperand::Imm(v)) if *v < 0 && *v != i64::MIN
        )
    }
}

// ---------------------------------------------------------------------------
// Operand relation predicates
// ---------------------------------------------------------------------------

/// Operands at indices `a` and `b` are the same VReg.
pub struct OperandsEqual {
    pub a: usize,
    pub b: usize,
}

impl Constraint for OperandsEqual {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        match (ctx.inst.operands.get(self.a), ctx.inst.operands.get(self.b)) {
            (Some(MachOperand::VReg(x)), Some(MachOperand::VReg(y))) => x == y,
            (Some(MachOperand::PReg(x)), Some(MachOperand::PReg(y))) => x == y,
            (Some(MachOperand::Imm(x)), Some(MachOperand::Imm(y))) => x == y,
            _ => false,
        }
    }
}

// ---------------------------------------------------------------------------
// Def-use predicates
// ---------------------------------------------------------------------------

/// The VReg in operand position `idx` is defined in the same block by an
/// instruction with the given opcode.
pub struct DefinedByOpcode {
    pub idx: usize,
    pub opcode: AArch64Opcode,
}

impl Constraint for DefinedByOpcode {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        ctx.operand_def(self.idx)
            .map(|def| def.opcode == self.opcode)
            .unwrap_or(false)
    }
}

/// The VReg in operand position `idx` is defined in the same block by an
/// instruction whose opcode falls in the given category.
pub struct DefinedByCategory {
    pub idx: usize,
    pub category: OpcodeCategory,
}

impl Constraint for DefinedByCategory {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        ctx.operand_def(self.idx)
            .map(|def| def.opcode.categorize() == self.category)
            .unwrap_or(false)
    }
}

/// The VReg in operand position `idx` is defined in the same block by an
/// instruction whose opcode is one of `opcodes`.
///
/// Useful when the definer may take several shapes, e.g. the `narrower
/// sign-extension subsumes wider` peephole accepts a definer that is
/// `Sxtb` *or* `Sxth`.
pub struct DefinedByOneOf {
    pub idx: usize,
    pub opcodes: &'static [AArch64Opcode],
}

impl Constraint for DefinedByOneOf {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        ctx.operand_def(self.idx)
            .map(|def| self.opcodes.contains(&def.opcode))
            .unwrap_or(false)
    }
}

/// The VReg in operand position `idx` has a same-block definer whose
/// operand `def_operand_idx` is an immediate equal to `value`.
///
/// This is the building block for patterns like `mul x, #2^k -> lsl x, #k`
/// where the definer is a `MovI` and we need to read its immediate.
pub struct DefinerImmEquals {
    /// Operand position on the matched (outer) instruction whose definer
    /// we want to probe.
    pub idx: usize,
    /// Operand position on the definer (inner) instruction that we
    /// expect to be an immediate.
    pub def_operand_idx: usize,
    /// The expected immediate value.
    pub value: i64,
}

impl Constraint for DefinerImmEquals {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        let Some(def) = ctx.operand_def(self.idx) else {
            return false;
        };
        matches!(
            def.operands.get(self.def_operand_idx),
            Some(MachOperand::Imm(v)) if *v == self.value,
        )
    }
}

/// The VReg in operand position `idx` has a same-block definer whose
/// operand `def_operand_idx` is an immediate that is a positive power of
/// two (`v > 0 && (v & (v - 1)) == 0`).
///
/// Building block for `mul x, #2^k -> lsl x, #k` and
/// `udiv x, #2^k -> lsr x, #k`. Mirrors [`DefinerImmEquals`] but matches
/// the power-of-two predicate instead of a fixed value.
pub struct DefinerImmIsPowerOfTwo {
    /// Operand position on the matched (outer) instruction whose definer
    /// we want to probe.
    pub idx: usize,
    /// Operand position on the definer (inner) instruction expected to be
    /// a power-of-two immediate.
    pub def_operand_idx: usize,
}

impl Constraint for DefinerImmIsPowerOfTwo {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        let Some(def) = ctx.operand_def(self.idx) else {
            return false;
        };
        matches!(
            def.operands.get(self.def_operand_idx),
            Some(MachOperand::Imm(v)) if *v > 0 && (*v & (*v - 1)) == 0,
        )
    }
}

/// The VReg in operand position `outer_def_idx` has a same-block definer
/// whose operand at `def_imm_idx` is an immediate equal to the immediate
/// at the outer instruction's operand `outer_imm_idx`.
///
/// Building block for the shift-pair-to-mask collapses (patterns 29/32).
/// The outer shift's amount must equal the inner (definer) shift's amount.
/// Both positions must be immediates, else the constraint is `false`.
pub struct DefinerImmEqualsOuterImm {
    /// Operand position on the matched (outer) instruction holding the
    /// immediate to compare.
    pub outer_imm_idx: usize,
    /// Operand position on the matched (outer) instruction whose definer
    /// we want to inspect.
    pub outer_def_idx: usize,
    /// Operand position on the definer (inner) instruction that must be an
    /// immediate equal to the outer immediate.
    pub def_imm_idx: usize,
}

impl Constraint for DefinerImmEqualsOuterImm {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        let outer_imm = match ctx.inst.operands.get(self.outer_imm_idx) {
            Some(MachOperand::Imm(v)) => *v,
            _ => return false,
        };
        let Some(def) = ctx.operand_def(self.outer_def_idx) else {
            return false;
        };
        matches!(
            def.operands.get(self.def_imm_idx),
            Some(MachOperand::Imm(v)) if *v == outer_imm,
        )
    }
}

/// The definer of the outer operand at `outer_def_idx` has its own
/// operand at `def_operand_idx` equal to the outer operand at
/// `outer_operand_idx` (as VRegs).
///
/// # Use
///
/// This is the building block for cross-instruction cancellation rules
/// like `add(sub(x, y), y) → mov x`. The outer ADD's `operand[2]` must
/// match the SUB definer's `operand[2]` for the cancellation to be legal.
/// Comparisons are strictly VReg-based; if either position is not a
/// VReg the constraint is `false`. Constants cannot match VRegs even
/// when they hold "the same value", which is the right call for a
/// local in-block rewriter — we don't do value numbering here.
///
/// # Example
///
/// `add v3, v1, v2` where `v1` was defined by `sub v1, v0, v2` satisfies
/// `DefinerOperandEqualsOuter { outer_def_idx: 1, def_operand_idx: 2,
/// outer_operand_idx: 2 }` — the outer ADD's rhs (v2) matches the inner
/// SUB's rhs (v2), which is exactly the cancellation condition.
pub struct DefinerOperandEqualsOuter {
    /// Operand position on the matched (outer) instruction whose definer
    /// we want to inspect.
    pub outer_def_idx: usize,
    /// Operand position on the definer (inner) instruction to compare.
    pub def_operand_idx: usize,
    /// Operand position on the matched (outer) instruction that must
    /// equal the definer's operand at `def_operand_idx`.
    pub outer_operand_idx: usize,
}

impl Constraint for DefinerOperandEqualsOuter {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        let Some(def) = ctx.operand_def(self.outer_def_idx) else {
            return false;
        };
        let inner = match def.operands.get(self.def_operand_idx) {
            Some(MachOperand::VReg(v)) => v,
            _ => return false,
        };
        let outer = match ctx.inst.operands.get(self.outer_operand_idx) {
            Some(MachOperand::VReg(v)) => v,
            _ => return false,
        };
        inner == outer
    }
}

// ---------------------------------------------------------------------------
// Interface predicates
// ---------------------------------------------------------------------------

/// The matched instruction (or, if `operand_idx.is_some()`, the definer
/// of that operand) satisfies the [`OpInterfaces::is_pure`] query.
pub struct InterfacePure {
    /// If `None`, query the matched instruction itself.
    /// If `Some(i)`, query the in-block definer of operand `i`.
    pub operand_idx: Option<usize>,
}

impl Constraint for InterfacePure {
    fn check(&self, ctx: &MatchCtx<'_>) -> bool {
        match self.operand_idx {
            None => ctx.inst.is_pure(),
            Some(i) => ctx.operand_def(i).map(|d| d.is_pure()).unwrap_or(false),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use trust_cg_ir::{
        AArch64Target, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, Signature,
        TargetInfo, VReg,
    };

    fn make_ctx<'a>(
        func: &'a MachFunction,
        inst: &'a MachInst,
        inst_id: InstId,
        block_id: BlockId,
        def_map: &'a HashMap<VReg, InstId>,
    ) -> MatchCtx<'a> {
        MatchCtx {
            inst,
            inst_id,
            block_id,
            func,
            def_map,
        }
    }

    fn vreg_class(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    #[test]
    fn imm_equals_hits_zero() {
        let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let def_map: HashMap<VReg, InstId> = HashMap::new();
        let inst = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::Imm(0),
                MachOperand::Imm(1),
                MachOperand::Imm(0),
            ],
        );
        let ctx = make_ctx(&func, &inst, InstId(0), BlockId(0), &def_map);
        assert!(ImmEquals { idx: 2, value: 0 }.check(&ctx));
        assert!(!ImmEquals { idx: 2, value: 1 }.check(&ctx));
    }

    #[test]
    fn imm_is_pred() {
        let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let def_map: HashMap<VReg, InstId> = HashMap::new();
        let inst = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::Imm(0),
                MachOperand::Imm(1),
                MachOperand::Imm(-7),
            ],
        );
        let ctx = make_ctx(&func, &inst, InstId(0), BlockId(0), &def_map);
        assert!(
            ImmIs {
                idx: 2,
                pred: |v| v < 0
            }
            .check(&ctx)
        );
        assert!(
            !ImmIs {
                idx: 2,
                pred: |v| v >= 0
            }
            .check(&ctx)
        );
    }

    #[test]
    fn imm_power_of_two() {
        let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let def_map: HashMap<VReg, InstId> = HashMap::new();
        let c = ImmIsPowerOfTwo { idx: 2 };
        for (v, want) in [
            (1, true),
            (2, true),
            (4, true),
            (8, true),
            (3, false),
            (0, false),
            (-4, false),
        ] {
            let inst = MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::Imm(0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(v),
                ],
            );
            let ctx = make_ctx(&func, &inst, InstId(0), BlockId(0), &def_map);
            assert_eq!(c.check(&ctx), want, "value {v}");
        }
    }

    #[test]
    fn imm_negative_non_min() {
        let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let def_map: HashMap<VReg, InstId> = HashMap::new();
        let c = ImmNegativeNonMin { idx: 2 };
        for (v, want) in [
            (-1i64, true),
            (-7, true),
            (i64::MIN + 1, true),
            (0, false),
            (1, false),
            (i64::MIN, false),
        ] {
            let inst = MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::Imm(0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(v),
                ],
            );
            let ctx = make_ctx(&func, &inst, InstId(0), BlockId(0), &def_map);
            assert_eq!(c.check(&ctx), want, "value {v}");
        }
    }

    #[test]
    fn operands_equal_vregs() {
        let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let def_map: HashMap<VReg, InstId> = HashMap::new();
        let same = VReg::new(7, trust_cg_ir::RegClass::Gpr64);
        let other = VReg::new(8, trust_cg_ir::RegClass::Gpr64);
        let equal_inst = MachInst::new(
            AArch64Target::sub_rr(),
            vec![
                MachOperand::VReg(VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(same),
                MachOperand::VReg(same),
            ],
        );
        let ctx = make_ctx(&func, &equal_inst, InstId(0), BlockId(0), &def_map);
        assert!(OperandsEqual { a: 1, b: 2 }.check(&ctx));

        let unequal_inst = MachInst::new(
            AArch64Target::sub_rr(),
            vec![
                MachOperand::VReg(VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(same),
                MachOperand::VReg(other),
            ],
        );
        let ctx = make_ctx(&func, &unequal_inst, InstId(0), BlockId(0), &def_map);
        assert!(!OperandsEqual { a: 1, b: 2 }.check(&ctx));

        let same_id_different_class = MachInst::new(
            AArch64Target::sub_rr(),
            vec![
                vreg_class(0, RegClass::Gpr64),
                vreg_class(7, RegClass::Gpr64),
                vreg_class(7, RegClass::Gpr32),
            ],
        );
        let ctx = make_ctx(
            &func,
            &same_id_different_class,
            InstId(0),
            BlockId(0),
            &def_map,
        );
        assert!(
            !OperandsEqual { a: 1, b: 2 }.check(&ctx),
            "same numeric id in different register classes is not the same VReg"
        );
    }

    // ---------------------------------------------------------------------
    // DefinedByOneOf / DefinerImmEquals tests. These constraints are built
    // on top of MatchCtx::definer_of and exercised end-to-end in
    // rewrite::patterns tests; this module covers only the predicate itself.
    // ---------------------------------------------------------------------

    fn push(func: &mut MachFunction, inst: MachInst) -> InstId {
        let id = func.push_inst(inst);
        let entry = func.entry;
        func.append_inst(entry, id);
        id
    }

    #[test]
    fn defined_by_one_of_accepts_any_listed() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let sxtb_id = push(
            &mut func,
            MachInst::new(
                AArch64Opcode::Sxtb,
                vec![
                    MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::VReg(VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                ],
            ),
        );
        let outer = MachInst::new(
            AArch64Opcode::Sxtw,
            vec![
                MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
            ],
        );
        let mut def_map: HashMap<VReg, InstId> = HashMap::new();
        def_map.insert(VReg::new(1, trust_cg_ir::RegClass::Gpr64), sxtb_id);
        let ctx = make_ctx(&func, &outer, InstId(99), BlockId(0), &def_map);

        let accepts = DefinedByOneOf {
            idx: 1,
            opcodes: &[AArch64Opcode::Sxtb, AArch64Opcode::Sxth],
        };
        assert!(accepts.check(&ctx), "Sxtb definer should match");

        let rejects = DefinedByOneOf {
            idx: 1,
            opcodes: &[AArch64Opcode::Sxtw], // self-ref excluded
        };
        assert!(!rejects.check(&ctx), "Sxtw is not in the accept list");
    }

    #[test]
    fn defined_by_one_of_block_param_false() {
        let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let def_map: HashMap<VReg, InstId> = HashMap::new();
        let outer = MachInst::new(
            AArch64Opcode::Sxtw,
            vec![
                MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(99, trust_cg_ir::RegClass::Gpr64)),
            ],
        );
        let ctx = make_ctx(&func, &outer, InstId(0), BlockId(0), &def_map);
        let c = DefinedByOneOf {
            idx: 1,
            opcodes: &[AArch64Opcode::Sxtb, AArch64Opcode::Sxth],
        };
        assert!(!c.check(&ctx), "no definer => false");
    }

    #[test]
    fn definer_imm_equals_matches_when_definer_is_movi() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let movi_id = push(
            &mut func,
            MachInst::new(
                AArch64Opcode::MovI,
                vec![
                    MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(1),
                ],
            ),
        );
        // Outer: MulRR v2, v1, vX — we probe definer(operand[1]).imm == 1.
        let outer = MachInst::new(
            AArch64Opcode::MulRR,
            vec![
                MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(3, trust_cg_ir::RegClass::Gpr64)),
            ],
        );
        let mut def_map: HashMap<VReg, InstId> = HashMap::new();
        def_map.insert(VReg::new(1, trust_cg_ir::RegClass::Gpr64), movi_id);
        let ctx = make_ctx(&func, &outer, InstId(42), BlockId(0), &def_map);

        let is_one = DefinerImmEquals {
            idx: 1,
            def_operand_idx: 1,
            value: 1,
        };
        assert!(is_one.check(&ctx));
        let is_two = DefinerImmEquals {
            idx: 1,
            def_operand_idx: 1,
            value: 2,
        };
        assert!(!is_two.check(&ctx));
    }

    #[test]
    fn definer_operand_equals_outer_matches_cancel_shape() {
        // Build:
        //   v1 = sub v0, v2      (SubRR definer)
        //   v3 = add v1, v2      (outer ADD)
        //
        // The cancellation rule `add(sub(x, y), y) → mov x` fires when
        // the outer ADD's rhs (operand[2] = v2) matches the SUB's rhs
        // (operand[2] = v2). That's exactly what this constraint checks.
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let sub_id = push(
            &mut func,
            MachInst::new(
                AArch64Opcode::SubRR,
                vec![
                    MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::VReg(VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
                ],
            ),
        );
        let outer = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(VReg::new(3, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
            ],
        );
        let mut def_map: HashMap<VReg, InstId> = HashMap::new();
        def_map.insert(VReg::new(1, trust_cg_ir::RegClass::Gpr64), sub_id);
        let ctx = make_ctx(&func, &outer, InstId(99), BlockId(0), &def_map);

        let matches = DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 2,
            outer_operand_idx: 2,
        };
        assert!(matches.check(&ctx));

        // Probing the wrong inner slot (operand[1] = v0 ≠ v2) must fail.
        let misses = DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 1,
            outer_operand_idx: 2,
        };
        assert!(!misses.check(&ctx));
    }

    #[test]
    fn definer_operand_equals_outer_rejects_same_id_different_class() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let sub_id = push(
            &mut func,
            MachInst::new(
                AArch64Opcode::SubRR,
                vec![
                    vreg_class(1, RegClass::Gpr64),
                    vreg_class(0, RegClass::Gpr64),
                    vreg_class(2, RegClass::Gpr32),
                ],
            ),
        );
        let outer = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                vreg_class(3, RegClass::Gpr64),
                vreg_class(1, RegClass::Gpr64),
                vreg_class(2, RegClass::Gpr64),
            ],
        );
        let mut def_map: HashMap<VReg, InstId> = HashMap::new();
        def_map.insert(VReg::new(1, RegClass::Gpr64), sub_id);
        let ctx = make_ctx(&func, &outer, InstId(99), BlockId(0), &def_map);

        let c = DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 2,
            outer_operand_idx: 2,
        };
        assert!(
            !c.check(&ctx),
            "same numeric id in different register classes is not the same VReg"
        );
    }

    #[test]
    fn definer_operand_equals_outer_no_definer_false() {
        // Block param: no in-block definer, constraint must be false.
        let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let def_map: HashMap<VReg, InstId> = HashMap::new();
        let outer = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(VReg::new(3, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(99, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
            ],
        );
        let ctx = make_ctx(&func, &outer, InstId(0), BlockId(0), &def_map);
        let c = DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 2,
            outer_operand_idx: 2,
        };
        assert!(!c.check(&ctx));
    }

    #[test]
    fn definer_operand_equals_outer_rejects_non_vregs() {
        // If the inner operand is an immediate (not a VReg), the
        // constraint must be false even if the outer operand is a VReg.
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let addi_id = push(
            &mut func,
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::VReg(VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(4),
                ],
            ),
        );
        let outer = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(VReg::new(3, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
            ],
        );
        let mut def_map: HashMap<VReg, InstId> = HashMap::new();
        def_map.insert(VReg::new(1, trust_cg_ir::RegClass::Gpr64), addi_id);
        let ctx = make_ctx(&func, &outer, InstId(9), BlockId(0), &def_map);

        let c = DefinerOperandEqualsOuter {
            outer_def_idx: 1,
            def_operand_idx: 2, // Imm(4), not a VReg
            outer_operand_idx: 2,
        };
        assert!(!c.check(&ctx));
    }

    #[test]
    fn definer_imm_is_power_of_two_matches_only_pow2() {
        for (imm, want) in [
            (1i64, true),
            (2, true),
            (8, true),
            (256, true),
            (3, false),
            (6, false),
            (0, false),
            (-4, false),
        ] {
            let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
            let movi_id = push(
                &mut func,
                MachInst::new(
                    AArch64Opcode::MovI,
                    vec![
                        MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                        MachOperand::Imm(imm),
                    ],
                ),
            );
            let outer = MachInst::new(
                AArch64Opcode::MulRR,
                vec![
                    MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::VReg(VReg::new(3, trust_cg_ir::RegClass::Gpr64)),
                ],
            );
            let mut def_map: HashMap<VReg, InstId> = HashMap::new();
            def_map.insert(VReg::new(1, trust_cg_ir::RegClass::Gpr64), movi_id);
            let ctx = make_ctx(&func, &outer, InstId(7), BlockId(0), &def_map);
            let c = DefinerImmIsPowerOfTwo {
                idx: 1,
                def_operand_idx: 1,
            };
            assert_eq!(c.check(&ctx), want, "imm {imm}");
        }
    }

    #[test]
    fn definer_imm_equals_outer_imm_matches_same_shift_only() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let lsr_id = push(
            &mut func,
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![
                    MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::VReg(VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(4),
                ],
            ),
        );
        let mut def_map: HashMap<VReg, InstId> = HashMap::new();
        def_map.insert(VReg::new(1, trust_cg_ir::RegClass::Gpr64), lsr_id);
        let c = DefinerImmEqualsOuterImm {
            outer_imm_idx: 2,
            outer_def_idx: 1,
            def_imm_idx: 2,
        };
        let outer_eq = MachInst::new(
            AArch64Opcode::LslRI,
            vec![
                MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(4),
            ],
        );
        let ctx = make_ctx(&func, &outer_eq, InstId(9), BlockId(0), &def_map);
        assert!(c.check(&ctx));
        let outer_ne = MachInst::new(
            AArch64Opcode::LslRI,
            vec![
                MachOperand::VReg(VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(5),
            ],
        );
        let ctx = make_ctx(&func, &outer_ne, InstId(9), BlockId(0), &def_map);
        assert!(!c.check(&ctx));
    }
}
