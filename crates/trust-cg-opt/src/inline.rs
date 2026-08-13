// trust-cg-opt - Function Inlining
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Function inlining pass for machine-level IR.
//!
//! Replaces direct call instructions (`BL`/`Bl`) to small, single-block
//! callee functions with the callee's body inlined at the call site.
//!
//! # Algorithm
//!
//! For each basic block in the caller:
//! 1. Scan instructions for direct calls (`Bl`/`BL`) with a `Symbol` operand.
//! 2. Look up the callee by name in the registered callee map.
//! 3. Check eligibility:
//!    - Cloneable callee instruction count <= `max_callee_size` (default 20).
//!    - Callee is not recursive (caller name != callee name).
//!    - Callee has exactly one basic block (single-block only in v1).
//! 4. Inline by computing a VReg offset, copying each callee instruction
//!    except the trailing `Ret`, replacing the call with the inlined body,
//!    and advancing `caller.next_vreg` past the callee's namespace.
//!
//! # Limitations (v1)
//!
//! - Only single-block callees are inlined.
//! - Indirect calls (`BLR`/`Blr`) are not inlined.
//! - No parameter/return value remapping beyond vreg renumbering.
//! - Recursive calls are unconditionally skipped.
//!
//! Reference: LLVM `InlineFunction.cpp`, `InlineCost.cpp`

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    VReg,
};

use crate::pass_manager::{AnalysisCache, MachinePass};
use crate::pgo::ProfileHotness;

/// Default maximum callee instruction count for inlining eligibility.
const DEFAULT_MAX_CALLEE_SIZE: usize = 20;
/// Maximum callee instruction count for hot profile-use call sites.
const HOT_CALLSITE_MAX_CALLEE_SIZE: usize = 32;

fn inline_pass_id() -> PassId {
    PassId::new("inline")
}

/// Function inlining pass.
///
/// Holds a map of known callee functions. When the pass encounters a
/// direct call to a callee in this map that is small enough, it replaces
/// the call with the callee's body.
pub struct FunctionInlining {
    /// Available callee functions for inlining lookups.
    callees: HashMap<String, MachFunction>,
    /// Maximum number of instructions in a callee to consider for inlining.
    max_callee_size: usize,
    /// Optional profile-use hotness summary for bounded call-site budgets.
    profile_hotness: Option<ProfileHotness>,
}

impl FunctionInlining {
    /// Create a new inlining pass with default settings.
    pub fn new() -> Self {
        Self {
            callees: HashMap::new(),
            max_callee_size: DEFAULT_MAX_CALLEE_SIZE,
            profile_hotness: None,
        }
    }

    /// Register a callee function available for inlining.
    pub fn with_callee(mut self, name: String, func: MachFunction) -> Self {
        self.callees.insert(name, func);
        self
    }

    /// Set the maximum callee instruction count threshold.
    pub fn with_max_size(mut self, max_size: usize) -> Self {
        self.max_callee_size = max_size;
        self
    }

    /// Attach profile-use hotness for bounded call-site budget decisions.
    pub fn with_profile_hotness(mut self, profile_hotness: Option<ProfileHotness>) -> Self {
        self.profile_hotness = profile_hotness;
        self
    }

    /// Add a callee function (non-builder API).
    pub fn add_callee(&mut self, name: String, func: MachFunction) {
        self.callees.insert(name, func);
    }

    fn max_callee_size_for_callsite(&self, caller_name: &str, block: BlockId) -> usize {
        let is_hot_callsite = self
            .profile_hotness
            .as_ref()
            .and_then(|hotness| hotness.block(caller_name, block))
            .is_some_and(|hotness| hotness.class.is_hot());

        if is_hot_callsite {
            self.max_callee_size.max(HOT_CALLSITE_MAX_CALLEE_SIZE)
        } else {
            self.max_callee_size
        }
    }

    fn cloneable_inst_count(callee: &MachFunction) -> usize {
        callee
            .block(callee.entry)
            .insts
            .iter()
            .filter(|&&inst_id| !callee.inst(inst_id).is_return())
            .count()
    }

    /// Check whether a callee is eligible for inlining.
    fn is_eligible(&self, caller_name: &str, block: BlockId, callee_name: &str) -> bool {
        // Skip recursive calls.
        if caller_name == callee_name {
            return false;
        }

        let callee = match self.callees.get(callee_name) {
            Some(c) => c,
            None => return false,
        };

        // Single-block only in v1.
        if callee.num_blocks() != 1 {
            return false;
        }

        // Count only the callee instructions that try_inline_call will clone.
        if Self::cloneable_inst_count(callee)
            > self.max_callee_size_for_callsite(caller_name, block)
        {
            return false;
        }

        true
    }

    /// Remap a single operand: if it is a VReg, add the offset to its id.
    fn remap_operand(op: &MachOperand, vreg_offset: u32) -> MachOperand {
        match op {
            MachOperand::VReg(v) => MachOperand::VReg(VReg::new(v.id + vreg_offset, v.class)),
            other => other.clone(),
        }
    }

    /// Clone a callee instruction with remapped vreg IDs.
    fn remap_inst(inst: &MachInst, vreg_offset: u32) -> MachInst {
        let remapped_operands: Vec<MachOperand> = inst
            .operands
            .iter()
            .map(|op| Self::remap_operand(op, vreg_offset))
            .collect();

        MachInst {
            opcode: inst.opcode,
            operands: remapped_operands,
            implicit_defs: inst.implicit_defs,
            implicit_uses: inst.implicit_uses,
            flags: inst.flags,
            proof: inst.proof,
            source_loc: inst.source_loc,
        }
    }

    fn record_inlined_inst_provenance(
        provenance: &mut ProvenanceMap,
        callee_inst_id: InstId,
        new_id: InstId,
        call_inst_id: InstId,
        caller_inst_count_before_inline: usize,
    ) {
        // A pre-existing entry for a freshly allocated caller InstId means
        // this map also contains another function's local InstId namespace.
        // ProvenanceMap cannot distinguish those functions yet, so do not
        // overwrite the unrelated entry.
        if provenance.get_entry(new_id).is_some() {
            return;
        }

        let callee_source_is_unambiguous = callee_inst_id.0 as usize
            >= caller_inst_count_before_inline
            && provenance.get_entry(callee_inst_id).is_some();

        if callee_source_is_unambiguous {
            provenance.record_clone(callee_inst_id, new_id, inline_pass_id());
        } else if provenance.get_entry(call_inst_id).is_some() {
            provenance.record_clone(call_inst_id, new_id, inline_pass_id());
        } else {
            provenance.record_creation(
                new_id,
                inline_pass_id(),
                "inline cloned callee body without source provenance",
            );
        }
    }

    fn record_inlined_call_deletion(provenance: &mut ProvenanceMap, call_inst_id: InstId) {
        provenance.record_deletion(
            call_inst_id,
            inline_pass_id(),
            "inline replaced direct call with callee body",
        );
    }

    /// Inline a single call site. Returns the list of new InstIds that
    /// replace the call, or None if the call is not eligible.
    fn try_inline_call(
        &self,
        caller: &mut MachFunction,
        call_inst_id: InstId,
        callee_name: &str,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> Option<Vec<InstId>> {
        let callee = self.callees.get(callee_name)?;

        let vreg_offset = caller.next_vreg;
        let caller_inst_count_before_inline = caller.insts.len();
        let call_source_loc = caller.inst(call_inst_id).source_loc;
        let callee_entry = callee.block(callee.entry);

        // Collect inlined instruction IDs.
        let mut inlined_ids = Vec::new();

        for &callee_inst_id in &callee_entry.insts {
            let callee_inst = callee.inst(callee_inst_id);

            // Skip the trailing Ret instruction — the caller's control flow
            // continues after the inlined body. The callee function itself is
            // not mutated, so any Ret provenance remains valid in the callee.
            if callee_inst.is_return() {
                continue;
            }

            let mut remapped = Self::remap_inst(callee_inst, vreg_offset);
            if remapped.source_loc.is_none() {
                remapped.source_loc = call_source_loc;
            }
            let new_id = caller.push_inst(remapped);
            if let Some(provenance) = provenance.as_deref_mut() {
                Self::record_inlined_inst_provenance(
                    provenance,
                    callee_inst_id,
                    new_id,
                    call_inst_id,
                    caller_inst_count_before_inline,
                );
            }
            inlined_ids.push(new_id);
        }

        if let Some(provenance) = provenance {
            Self::record_inlined_call_deletion(provenance, call_inst_id);
        }

        // Advance the caller's vreg counter past the callee's namespace.
        if callee.next_vreg > 0 {
            caller.next_vreg += callee.next_vreg;
        }

        Some(inlined_ids)
    }

    fn run_impl(
        &self,
        func: &mut MachFunction,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let mut changed = false;
        let caller_name = func.name.clone();

        // Process each block. We iterate over block_order by index because
        // we mutate blocks during iteration.
        let block_ids: Vec<_> = func.block_order.clone();

        for block_id in block_ids {
            // Build a new instruction list for this block, replacing calls
            // with inlined bodies where eligible.
            let old_insts: Vec<InstId> = func.block(block_id).insts.clone();
            let mut new_insts = Vec::new();
            let mut block_changed = false;

            for &inst_id in &old_insts {
                let inst = func.inst(inst_id);

                // Check if this is a direct call (Bl or BL) with a Symbol operand.
                let callee_name = if matches!(inst.opcode, AArch64Opcode::Bl | AArch64Opcode::BL) {
                    inst.operands.iter().find_map(|op| {
                        if let MachOperand::Symbol(s) = op {
                            Some(s.clone())
                        } else {
                            None
                        }
                    })
                } else {
                    None
                };

                if let Some(ref target) = callee_name
                    && self.is_eligible(&caller_name, block_id, target)
                    && let Some(inlined_ids) =
                        self.try_inline_call(func, inst_id, target, provenance.as_deref_mut())
                {
                    new_insts.extend(inlined_ids);
                    block_changed = true;
                    continue;
                }

                // Not inlined: the original InstId remains live and unchanged,
                // so any existing provenance entry still points at the right IR.
                new_insts.push(inst_id);
            }

            if block_changed {
                func.block_mut(block_id).insts = new_insts;
                changed = true;
            }
        }

        changed
    }
}

impl Default for FunctionInlining {
    fn default() -> Self {
        Self::new()
    }
}

impl MachinePass for FunctionInlining {
    fn name(&self) -> &str {
        "inline"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        self.run_impl(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_impl(func, Some(provenance))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use crate::pgo::{BlockProfile, FunctionProfile, ProfData, ProfileHotness};
    use trust_cg_ir::{
        AArch64Opcode, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
        ProvenanceStatus, RegClass, Signature, SourceLoc, TransformKind, TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 1,
            line,
            col: 9,
        }
    }

    fn make_func_with_insts(name: &str, insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    /// Helper: create a simple callee function with given instructions + Ret.
    fn make_callee(name: &str, body_insts: Vec<MachInst>, next_vreg: u32) -> MachFunction {
        let mut func = make_func_with_insts(name, body_insts);
        // Append a Ret at the end.
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(func.entry, ret_id);
        func.next_vreg = next_vreg;
        func
    }

    fn make_sparse_callee(
        name: &str,
        padding: usize,
        body_insts: Vec<MachInst>,
        next_vreg: u32,
    ) -> (MachFunction, Vec<InstId>, InstId) {
        let mut func = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));

        for _ in 0..padding {
            func.push_inst(MachInst::new(AArch64Opcode::Nop, vec![]));
        }

        let mut body_ids = Vec::new();
        for inst in body_insts {
            let id = func.push_inst(inst);
            func.append_inst(func.entry, id);
            body_ids.push(id);
        }

        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(func.entry, ret_id);
        func.next_vreg = next_vreg;

        (func, body_ids, ret_id)
    }

    fn profile_hotness_for_callsite(caller: &str, block: BlockId, hits: u64) -> ProfileHotness {
        let mut profile = ProfData::new(0x396);
        let mut function = FunctionProfile::new(caller);
        function.call_count = hits;
        function.blocks.push(BlockProfile::new(block.0, hits));
        profile.functions.push(function);
        ProfileHotness::from_profile(&profile)
    }

    #[test]
    fn test_inline_simple_callee() {
        // Callee: "add_fn" has one add instruction + ret
        //   v0 = add v1, v2
        //   ret
        let callee_add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let callee = make_callee("add_fn", vec![callee_add], 3);

        // Caller: "main" calls add_fn, then returns
        //   bl add_fn
        //   ret
        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("add_fn".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);
        caller.next_vreg = 5; // caller uses vregs 0..4

        let mut pass = FunctionInlining::new().with_callee("add_fn".to_string(), callee);

        assert!(pass.run(&mut caller));

        // After inlining: the call is replaced by the add instruction (Ret skipped),
        // followed by the original Ret.
        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2); // inlined add + original ret

        // The inlined add should have remapped vregs: offset=5, so v0->v5, v1->v6, v2->v7
        let inlined_add = caller.inst(block.insts[0]);
        assert_eq!(inlined_add.opcode, AArch64Opcode::AddRR);
        assert_eq!(inlined_add.operands.len(), 3);
        assert_eq!(inlined_add.operands[0], vreg(5));
        assert_eq!(inlined_add.operands[1], vreg(6));
        assert_eq!(inlined_add.operands[2], vreg(7));

        // next_vreg should have advanced: 5 + 3 = 8
        assert_eq!(caller.next_vreg, 8);
    }

    #[test]
    fn test_inline_skips_large_callee() {
        // Create a callee with more instructions than the threshold.
        let mut body = Vec::new();
        for i in 0..5 {
            body.push(MachInst::new(
                AArch64Opcode::AddRI,
                vec![vreg(i), vreg(i), imm(1)],
            ));
        }
        let callee = make_callee("big_fn", body, 5);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("big_fn".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);

        // Set threshold to 3; callee has 5 cloneable body instructions.
        let mut pass = FunctionInlining::new()
            .with_callee("big_fn".to_string(), callee)
            .with_max_size(3);

        assert!(!pass.run(&mut caller));

        // Call should still be present.
        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_inline_budget_excludes_skipped_ret_at_exact_limit() {
        let mut body = Vec::new();
        for i in 0..3 {
            body.push(MachInst::new(
                AArch64Opcode::AddRI,
                vec![vreg(i), vreg(i), imm(1)],
            ));
        }
        let callee = make_callee("exact_fn", body, 3);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("exact_fn".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);

        let mut pass = FunctionInlining::new()
            .with_callee("exact_fn".to_string(), callee)
            .with_max_size(3);

        assert!(pass.run(&mut caller));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 4);
        for &inst_id in &block.insts[..3] {
            assert_eq!(caller.inst(inst_id).opcode, AArch64Opcode::AddRI);
        }
        assert_eq!(caller.inst(block.insts[3]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_inline_budget_still_rejects_body_over_limit() {
        let mut body = Vec::new();
        for i in 0..4 {
            body.push(MachInst::new(
                AArch64Opcode::AddRI,
                vec![vreg(i), vreg(i), imm(1)],
            ));
        }
        let callee = make_callee("over_fn", body, 4);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("over_fn".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);

        let mut pass = FunctionInlining::new()
            .with_callee("over_fn".to_string(), callee)
            .with_max_size(3);

        assert!(!pass.run(&mut caller));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(caller.inst(block.insts[0]).opcode, AArch64Opcode::Bl);
        assert_eq!(caller.inst(block.insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_hot_profile_callsite_raises_inline_budget() {
        let mut body = Vec::new();
        for i in 0..25 {
            body.push(MachInst::new(
                AArch64Opcode::AddRI,
                vec![vreg(i), vreg(i), imm(1)],
            ));
        }
        let callee = make_callee("hot_helper", body, 25);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("hot_helper".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);

        let mut unprofiled_caller = make_func_with_insts("main", vec![call.clone(), ret.clone()]);
        let mut unprofiled_pass =
            FunctionInlining::new().with_callee("hot_helper".to_string(), callee.clone());
        assert!(!unprofiled_pass.run(&mut unprofiled_caller));

        let mut profiled_caller = make_func_with_insts("main", vec![call, ret]);
        let hotness = profile_hotness_for_callsite("main", profiled_caller.entry, 100);
        let mut profiled_pass = FunctionInlining::new()
            .with_callee("hot_helper".to_string(), callee)
            .with_profile_hotness(Some(hotness));

        assert!(profiled_pass.run(&mut profiled_caller));
        let block = profiled_caller.block(profiled_caller.entry);
        assert_eq!(block.insts.len(), 26);
        assert_eq!(
            profiled_caller.inst(block.insts[0]).opcode,
            AArch64Opcode::AddRI
        );
        assert_eq!(
            profiled_caller.inst(block.insts[25]).opcode,
            AArch64Opcode::Ret
        );
    }

    #[test]
    fn test_inline_skips_recursive() {
        // Caller calls itself — should not inline.
        let callee_add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let callee = make_callee("my_func", vec![callee_add], 3);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("my_func".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("my_func", vec![call, ret]);

        let mut pass = FunctionInlining::new().with_callee("my_func".to_string(), callee);

        assert!(!pass.run(&mut caller));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2); // call + ret still present
    }

    #[test]
    fn test_inline_skips_indirect_call() {
        // BLR (indirect call) should not be inlined.
        let call = MachInst::new(AArch64Opcode::Blr, vec![vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);

        let callee_add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let callee = make_callee("target", vec![callee_add], 3);

        let mut pass = FunctionInlining::new().with_callee("target".to_string(), callee);

        assert!(!pass.run(&mut caller));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_inline_skips_multi_block() {
        // Create a callee with two blocks — not eligible for v1 inlining.
        let mut callee =
            MachFunction::new("multi_block".to_string(), Signature::new(vec![], vec![]));
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let add_id = callee.push_inst(add);
        callee.append_inst(callee.entry, add_id);

        // Create a second block.
        let bb1 = callee.create_block();
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = callee.push_inst(ret);
        callee.append_inst(bb1, ret_id);
        callee.next_vreg = 3;

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("multi_block".to_string())],
        );
        let caller_ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, caller_ret]);

        let mut pass = FunctionInlining::new().with_callee("multi_block".to_string(), callee);

        assert!(!pass.run(&mut caller));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_inline_no_calls() {
        // Function without any calls — pass should return false.
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts("main", vec![add, ret]);

        let mut pass = FunctionInlining::new();
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_inline_remaps_vregs() {
        // Callee uses vregs 0, 1, 2. Caller's next_vreg is 10.
        // After inlining, callee vregs should be 10, 11, 12.
        let callee_sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(0), vreg(1), imm(42)]);
        let callee_add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let callee = make_callee("helper", vec![callee_sub, callee_add], 3);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("helper".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);
        caller.next_vreg = 10;

        let mut pass = FunctionInlining::new().with_callee("helper".to_string(), callee);

        assert!(pass.run(&mut caller));

        let block = caller.block(caller.entry);
        // 2 inlined instructions + original ret = 3
        assert_eq!(block.insts.len(), 3);

        // First inlined: sub v10, v11, #42
        let inlined_sub = caller.inst(block.insts[0]);
        assert_eq!(inlined_sub.opcode, AArch64Opcode::SubRI);
        assert_eq!(inlined_sub.operands[0], vreg(10));
        assert_eq!(inlined_sub.operands[1], vreg(11));
        assert_eq!(inlined_sub.operands[2], imm(42)); // immediates unchanged

        // Second inlined: add v12, v10, v11
        let inlined_add = caller.inst(block.insts[1]);
        assert_eq!(inlined_add.opcode, AArch64Opcode::AddRR);
        assert_eq!(inlined_add.operands[0], vreg(12));
        assert_eq!(inlined_add.operands[1], vreg(10));
        assert_eq!(inlined_add.operands[2], vreg(11));

        // next_vreg: 10 + 3 = 13
        assert_eq!(caller.next_vreg, 13);
    }

    #[test]
    fn test_inline_multiple_calls() {
        // Caller has two calls to the same callee — both should be inlined.
        let callee_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(99)]);
        let callee = make_callee("tiny", vec![callee_mov], 1);

        let call1 = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("tiny".to_string())],
        );
        let call2 = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("tiny".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call1, call2, ret]);
        caller.next_vreg = 5;

        let mut pass = FunctionInlining::new().with_callee("tiny".to_string(), callee);

        assert!(pass.run(&mut caller));

        let block = caller.block(caller.entry);
        // Two inlined mov instructions + ret = 3
        assert_eq!(block.insts.len(), 3);

        // First inlined mov: vreg offset 5 -> v5
        let mov1 = caller.inst(block.insts[0]);
        assert_eq!(mov1.opcode, AArch64Opcode::MovI);
        assert_eq!(mov1.operands[0], vreg(5));

        // Second inlined mov: vreg offset 5+1=6 -> v6
        let mov2 = caller.inst(block.insts[1]);
        assert_eq!(mov2.opcode, AArch64Opcode::MovI);
        assert_eq!(mov2.operands[0], vreg(6));

        // next_vreg: 5 + 1 + 1 = 7
        assert_eq!(caller.next_vreg, 7);
    }

    #[test]
    fn test_inline_preserves_proof_annotations() {
        use trust_cg_ir::ProofAnnotation;

        // Callee has an instruction with a proof annotation.
        let callee_add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let callee = make_callee("proven", vec![callee_add], 3);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("proven".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);
        caller.next_vreg = 0;

        let mut pass = FunctionInlining::new().with_callee("proven".to_string(), callee);

        assert!(pass.run(&mut caller));

        let block = caller.block(caller.entry);
        let inlined = caller.inst(block.insts[0]);
        assert_eq!(inlined.proof, Some(ProofAnnotation::NoOverflow));
    }

    #[test]
    fn test_inline_provenance_clones_callee_body_and_deletes_call() {
        let callee_sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(0), vreg(1), imm(7)]);
        let callee_add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let (callee, callee_body_ids, callee_ret_id) =
            make_sparse_callee("helper", 16, vec![callee_sub, callee_add], 3);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("helper".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);
        caller.next_vreg = 10;

        let call_id = caller.block(caller.entry).insts[0];
        let caller_ret_id = caller.block(caller.entry).insts[1];
        let call_origin = TrustIrInstId(10);
        let caller_ret_origin = TrustIrInstId(11);
        let callee_first_origin = TrustIrInstId(20);
        let callee_second_origin = TrustIrInstId(21);
        let callee_ret_origin = TrustIrInstId(22);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(call_origin, &[call_id], PassId::new("isel"));
        provenance.record_lowering(caller_ret_origin, &[caller_ret_id], PassId::new("isel"));
        provenance.record_lowering(
            callee_first_origin,
            &[callee_body_ids[0]],
            PassId::new("isel"),
        );
        provenance.record_lowering(
            callee_second_origin,
            &[callee_body_ids[1]],
            PassId::new("isel"),
        );
        provenance.record_lowering(callee_ret_origin, &[callee_ret_id], PassId::new("isel"));

        let mut pass = FunctionInlining::new().with_callee("helper".to_string(), callee);
        assert!(pass.run_with_provenance(&mut caller, &mut provenance));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 3);
        let inlined_first = block.insts[0];
        let inlined_second = block.insts[1];

        let first_entry = provenance
            .get_entry(inlined_first)
            .expect("first inlined instruction should keep provenance");
        assert_eq!(first_entry.trust_ir_origins, vec![callee_first_origin]);
        assert!(first_entry.is_active());
        assert_eq!(
            first_entry.transforms.last().unwrap().kind,
            TransformKind::Cloned {
                source: callee_body_ids[0]
            }
        );
        assert_eq!(
            provenance.get_mach_insts(callee_first_origin).unwrap(),
            &[callee_body_ids[0], inlined_first]
        );

        let second_entry = provenance
            .get_entry(inlined_second)
            .expect("second inlined instruction should keep provenance");
        assert_eq!(second_entry.trust_ir_origins, vec![callee_second_origin]);
        assert!(second_entry.is_active());
        assert_eq!(
            second_entry.transforms.last().unwrap().kind,
            TransformKind::Cloned {
                source: callee_body_ids[1]
            }
        );

        let call_entry = provenance
            .get_entry(call_id)
            .expect("deleted call should retain provenance");
        match &call_entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass, &PassId::new("inline"));
                assert!(justification.contains("replaced direct call"));
            }
            other => panic!("expected inline-optimized-away call, got {other:?}"),
        }

        assert!(provenance.get_entry(callee_ret_id).unwrap().is_active());
        assert_eq!(
            provenance.get_mach_insts(callee_ret_origin).unwrap(),
            &[callee_ret_id]
        );
    }

    #[test]
    fn test_inline_provenance_falls_back_to_callsite_through_analysis_hook() {
        let callee_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(99)]);
        let callee = make_callee("tiny", vec![callee_mov], 1);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("tiny".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);
        caller.next_vreg = 5;

        let call_id = caller.block(caller.entry).insts[0];
        let call_origin = TrustIrInstId(30);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(call_origin, &[call_id], PassId::new("isel"));

        let mut analyses = AnalysisCache::new();
        let mut pass = FunctionInlining::new().with_callee("tiny".to_string(), callee);
        assert!(pass.run_with_analyses_and_provenance(&mut caller, &mut analyses, &mut provenance));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2);
        let inlined_id = block.insts[0];

        let inlined_entry = provenance
            .get_entry(inlined_id)
            .expect("inlined instruction should inherit call-site provenance");
        assert_eq!(inlined_entry.trust_ir_origins, vec![call_origin]);
        assert!(inlined_entry.is_active());
        assert_eq!(
            inlined_entry.transforms.last().unwrap().kind,
            TransformKind::Cloned { source: call_id }
        );
        assert_eq!(
            provenance.get_mach_insts(call_origin).unwrap(),
            &[call_id, inlined_id]
        );
        assert!(provenance.get_entry(call_id).unwrap().is_optimized_away());
    }

    #[test]
    fn test_inline_source_loc_falls_back_to_callsite_when_callee_has_none() {
        let callee_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(99)]);
        let callee = make_callee("tiny", vec![callee_mov], 1);

        let call_loc = source_loc(77);
        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("tiny".to_string())],
        )
        .with_source_loc(call_loc);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);
        caller.next_vreg = 5;

        let mut pass = FunctionInlining::new().with_callee("tiny".to_string(), callee);
        assert!(pass.run(&mut caller));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(
            caller.inst(block.insts[0]).source_loc,
            Some(call_loc),
            "inline fallback provenance should keep a usable debug line"
        );
    }

    #[test]
    fn test_inline_unknown_callee() {
        // Call to a function not in the callees map — should not inline.
        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("unknown".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);

        let mut pass = FunctionInlining::new();
        assert!(!pass.run(&mut caller));

        let block = caller.block(caller.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_inline_idempotent() {
        // After inlining, running the pass again should not change anything
        // (the inlined body contains no calls).
        let callee_add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let callee = make_callee("add_fn", vec![callee_add], 3);

        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("add_fn".to_string())],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut caller = make_func_with_insts("main", vec![call, ret]);
        caller.next_vreg = 5;

        let mut pass = FunctionInlining::new().with_callee("add_fn".to_string(), callee);

        assert!(pass.run(&mut caller)); // First pass inlines
        assert!(!pass.run(&mut caller)); // Second pass: no calls remain
    }
}
