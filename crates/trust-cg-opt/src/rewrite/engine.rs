// trust-cg-opt - Rewrite engine (fixed-point driver)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`RewriteEngine`] drives a set of [`Rule`]s against a [`MachFunction`]
//! until no rule fires (or `max_iterations` is reached).
//!
//! The engine:
//! - visits each instruction in block order,
//! - evaluates every rule and picks the highest-benefit firing rule,
//! - applies the action (`Replace` / `Delete`),
//! - preserves the original instruction's proof annotation and source
//!   location when replacing, matching the behavior of the hand-written
//!   peephole pass,
//! - optionally records provenance for in-place replacements and deletions,
//! - maintains a forward, block-local reaching-definition map over the
//!   surviving post-rewrite instructions, and
//! - iterates to fixed point.

use std::collections::HashMap;
use std::collections::HashSet;

use trust_cg_ir::{InstId, MachFunction, PassId, ProvenanceMap, VReg};

use crate::rewrite::matcher::MatchCtx;
use crate::rewrite::rewriter::RewriteAction;
use crate::rewrite::rule::Rule;

/// Per-engine statistics.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RewriteStats {
    /// Number of rewrites applied (Replace + Delete).
    pub rewrites: u32,
    /// Number of fixed-point iterations executed.
    pub iterations: u32,
    /// Per-rule firing count (indexed by rule registration order).
    pub rule_fires: Vec<u32>,
}

/// Fixed-point rewrite driver.
pub struct RewriteEngine {
    rules: Vec<Rule>,
}

impl RewriteEngine {
    /// Create an empty engine.
    pub fn new() -> Self {
        Self { rules: Vec::new() }
    }

    /// Register a rule. Rules are evaluated in registration order; if
    /// multiple rules match with the same benefit, the earlier-registered
    /// rule wins.
    pub fn register(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    /// Registered rule count.
    #[inline]
    pub fn num_rules(&self) -> usize {
        self.rules.len()
    }

    /// Run all rules to fixed point.
    pub fn run_to_fixpoint(&self, func: &mut MachFunction, max_iterations: u32) -> RewriteStats {
        self.run_to_fixpoint_impl(func, max_iterations, None, None)
    }

    /// Run all rules to fixed point while recording provenance updates.
    pub fn run_to_fixpoint_with_provenance(
        &self,
        func: &mut MachFunction,
        max_iterations: u32,
        provenance: &mut ProvenanceMap,
        pass: &PassId,
    ) -> RewriteStats {
        self.run_to_fixpoint_impl(func, max_iterations, Some(provenance), Some(pass))
    }

    fn run_to_fixpoint_impl(
        &self,
        func: &mut MachFunction,
        max_iterations: u32,
        mut provenance: Option<&mut ProvenanceMap>,
        provenance_pass: Option<&PassId>,
    ) -> RewriteStats {
        let mut stats = RewriteStats {
            rule_fires: vec![0; self.rules.len()],
            ..Default::default()
        };
        for iter in 0..max_iterations {
            stats.iterations = iter + 1;
            let iter_changes =
                self.run_once(func, &mut stats, provenance.as_deref_mut(), provenance_pass);
            if iter_changes == 0 {
                break;
            }
        }
        stats
    }

    /// Single pass over the function. Returns the number of rewrites
    /// applied this pass.
    fn run_once(
        &self,
        func: &mut MachFunction,
        stats: &mut RewriteStats,
        mut provenance: Option<&mut ProvenanceMap>,
        provenance_pass: Option<&PassId>,
    ) -> u32 {
        let mut changes: u32 = 0;
        let mut to_delete: HashSet<InstId> = HashSet::new();

        for block_id in func.block_order.clone() {
            // Forward reaching-definition map for this block. Start empty and
            // record a definition only after its instruction has been visited:
            // preloading the block's final writers lets a rule inspect a future
            // redefinition and is unsound in non-SSA machine IR.
            let mut def_map = HashMap::new();
            let inst_ids = func.block(block_id).insts.clone();
            for inst_id in inst_ids {
                if to_delete.contains(&inst_id) {
                    continue;
                }

                // Pick the best-firing rule.
                let best = {
                    let inst = func.inst(inst_id);
                    let ctx = MatchCtx {
                        inst,
                        inst_id,
                        block_id,
                        func,
                        def_map: &def_map,
                    };
                    let mut best: Option<(usize, RewriteAction)> = None;
                    for (idx, rule) in self.rules.iter().enumerate() {
                        if let Some(action) = rule.evaluate(&ctx) {
                            let better = match &best {
                                None => true,
                                Some((b_idx, _)) => rule.benefit > self.rules[*b_idx].benefit,
                            };
                            if better {
                                best = Some((idx, action));
                            }
                        }
                    }
                    best
                };

                if let Some((rule_idx, action)) = best {
                    // Snapshot proof + source_loc from the original inst so
                    // we can transfer them onto the replacement.
                    let (orig_proof, orig_loc) = {
                        let inst = func.inst(inst_id);
                        (inst.proof, inst.source_loc)
                    };
                    match action {
                        RewriteAction::None => {
                            // No provenance update: Rule::evaluate filters
                            // this action out before selection, so this arm is
                            // retained only as an exhaustive safety net.
                        }
                        RewriteAction::Replace(mut new_inst) => {
                            if new_inst.proof.is_none() {
                                new_inst.proof = orig_proof;
                            }
                            if new_inst.source_loc.is_none() {
                                new_inst.source_loc = orig_loc;
                            }
                            *func.inst_mut(inst_id) = new_inst;
                            if let (Some(provenance), Some(pass)) =
                                (provenance.as_deref_mut(), provenance_pass)
                            {
                                provenance.record_in_place_transform(inst_id, pass.clone());
                            }
                            stats.rewrites += 1;
                            stats.rule_fires[rule_idx] += 1;
                            changes += 1;
                        }
                        RewriteAction::Delete => {
                            to_delete.insert(inst_id);
                            if let (Some(provenance), Some(pass)) =
                                (provenance.as_deref_mut(), provenance_pass)
                            {
                                provenance.record_deletion(
                                    inst_id,
                                    pass.clone(),
                                    format!(
                                        "declarative rewrite rule '{}' deleted instruction",
                                        self.rules[rule_idx].name
                                    ),
                                );
                            }
                            stats.rewrites += 1;
                            stats.rule_fires[rule_idx] += 1;
                            changes += 1;
                        }
                    }
                }

                // Only a surviving instruction may become the reaching
                // definer for later instructions. Use its post-rewrite shape.
                if !to_delete.contains(&inst_id) {
                    record_definition(&mut def_map, func.inst(inst_id), inst_id);
                }
            }
        }

        if !to_delete.is_empty() {
            for block_id in func.block_order.clone() {
                let block = func.block_mut(block_id);
                block.insts.retain(|id| !to_delete.contains(id));
            }
        }

        changes
    }
}

impl Default for RewriteEngine {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Record one instruction's value definition in a forward block-local map.
fn record_definition(
    def_map: &mut HashMap<VReg, InstId>,
    inst: &trust_cg_ir::MachInst,
    id: InstId,
) {
    crate::effects::for_each_inst_def(inst, |dst| {
        def_map.insert(dst, id);
    });
}

#[cfg(test)]
mod tests {
    use trust_cg_ir::MachOperand;

    use super::*;
    use crate::rewrite::patterns::{
        rule_add_self_to_shl, rule_lsr_lsl_to_and, rule_mul_by_one_rhs, rule_mul_by_zero_rhs,
        rule_self_move_delete,
    };
    use trust_cg_ir::{AArch64Opcode, RegClass, Signature};

    fn vreg(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    #[test]
    fn reaching_def_map_keeps_same_id_different_classes_distinct() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let gpr32 = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::MovI,
            vec![vreg(1, RegClass::Gpr32), MachOperand::Imm(5)],
        ));
        func.append_inst(entry, gpr32);
        let gpr64 = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::MovI,
            vec![vreg(1, RegClass::Gpr64), MachOperand::Imm(9)],
        ));
        func.append_inst(entry, gpr64);

        let mut def_map = HashMap::new();
        record_definition(&mut def_map, func.inst(gpr32), gpr32);
        record_definition(&mut def_map, func.inst(gpr64), gpr64);

        assert_eq!(def_map.get(&VReg::new(1, RegClass::Gpr32)), Some(&gpr32));
        assert_eq!(def_map.get(&VReg::new(1, RegClass::Gpr64)), Some(&gpr64));
    }

    #[test]
    fn rewrite_uses_latest_prior_writer_never_future_redefinition() {
        // movi v1, #1
        // mul  v2, v3, v1   ; must see #1 and rewrite to mov v2, v3
        // movi v1, #0       ; future writer must not rewrite the MUL to zero
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let v = |id| MachOperand::VReg(VReg::new(id, RegClass::Gpr64));
        let prior = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::MovI,
            vec![v(1), MachOperand::Imm(1)],
        ));
        func.append_inst(entry, prior);
        let mul = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::MulRR,
            vec![v(2), v(3), v(1)],
        ));
        func.append_inst(entry, mul);
        let future = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::MovI,
            vec![v(1), MachOperand::Imm(0)],
        ));
        func.append_inst(entry, future);

        let mut engine = RewriteEngine::new();
        engine.register(rule_mul_by_zero_rhs());
        engine.register(rule_mul_by_one_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);

        assert_eq!(stats.rewrites, 1);
        let rewritten = func.inst(mul);
        assert_eq!(rewritten.opcode, AArch64Opcode::MovR);
        assert_eq!(rewritten.operands, vec![v(2), v(3)]);
    }

    #[test]
    fn rewritten_instruction_becomes_reaching_def_for_later_rule() {
        // add v1, v0, v0  -> lsl v1, v0, #1
        // lsr v2, v1, #1  -> and v2, v0, #0x7fff_ffff_ffff_ffff
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let v = |id| MachOperand::VReg(VReg::new(id, RegClass::Gpr64));
        let add = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::AddRR,
            vec![v(1), v(0), v(0)],
        ));
        func.append_inst(entry, add);
        let lsr = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::LsrRI,
            vec![v(2), v(1), MachOperand::Imm(1)],
        ));
        func.append_inst(entry, lsr);

        let mut engine = RewriteEngine::new();
        engine.register(rule_add_self_to_shl());
        engine.register(rule_lsr_lsl_to_and());
        let stats = engine.run_to_fixpoint(&mut func, 4);

        assert_eq!(stats.rewrites, 2);
        assert_eq!(func.inst(add).opcode, AArch64Opcode::LslRI);
        let rewritten = func.inst(lsr);
        assert_eq!(rewritten.opcode, AArch64Opcode::AndRI);
        assert_eq!(
            rewritten.operands,
            vec![v(2), v(0), MachOperand::Imm(i64::MAX)]
        );
    }

    #[test]
    fn deleted_self_move_preserves_prior_reaching_def() {
        // movi v1, #1
        // mov  v1, v1      ; deleted, prior v1 definition remains reaching
        // mul  v2, v3, v1  ; therefore rewrites by one, not by zero/unknown
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let v = |id| MachOperand::VReg(VReg::new(id, RegClass::Gpr64));
        let prior = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::MovI,
            vec![v(1), MachOperand::Imm(1)],
        ));
        func.append_inst(entry, prior);
        let self_move = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::MovR,
            vec![v(1), v(1)],
        ));
        func.append_inst(entry, self_move);
        let mul = func.push_inst(trust_cg_ir::MachInst::new(
            AArch64Opcode::MulRR,
            vec![v(2), v(3), v(1)],
        ));
        func.append_inst(entry, mul);

        let mut engine = RewriteEngine::new();
        engine.register(rule_self_move_delete());
        engine.register(rule_mul_by_zero_rhs());
        engine.register(rule_mul_by_one_rhs());
        let stats = engine.run_to_fixpoint(&mut func, 4);

        assert_eq!(stats.rewrites, 2);
        assert!(!func.block(entry).insts.contains(&self_move));
        let rewritten = func.inst(mul);
        assert_eq!(rewritten.opcode, AArch64Opcode::MovR);
        assert_eq!(rewritten.operands, vec![v(2), v(3)]);
    }
}
