// trust-cg-opt - x86-64 pass manager scaffold
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! x86-64 pass manager scaffold for ISel-output machine functions.
//!
//! This module is intentionally separate from [`crate::pass_manager`], whose
//! [`crate::MachinePass`] trait accepts the canonical AArch64-shaped
//! `trust_cg_ir::MachFunction`. x86-64 optimization passes operate on
//! [`trust_cg_lower::X86ISelFunction`] and [`trust_cg_lower::X86ISelInst`] until the
//! machine IR type universe is generalized.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use trust_cg_lower::X86ISelFunction;

use crate::pass_manager::PassStats;

/// Statistics collected during x86 pass execution.
pub type X86PassStats = PassStats;

/// Structural fingerprint of an [`X86ISelFunction`] used by the fixpoint loop
/// to detect non-convergence.
///
/// `X86ISelInst`/`X86ISelOperand` are not `Hash` (operands carry an `f64`
/// float immediate, so the types are not `Eq`/`Hash`). We therefore hash a
/// deterministic `Debug` rendering of each instruction together with the block
/// structure. This is only used as a change detector — false "different"
/// verdicts are harmless (they cannot mask non-convergence, only fail to
/// shortcut it), and the `Debug` rendering is total and stable for a given IR
/// shape.
fn function_fingerprint(func: &X86ISelFunction) -> u64 {
    let mut hasher = DefaultHasher::new();
    func.name.hash(&mut hasher);
    func.next_vreg.hash(&mut hasher);
    func.block_order.len().hash(&mut hasher);
    for block_id in &func.block_order {
        block_id.0.hash(&mut hasher);
        let Some(block) = func.blocks.get(block_id) else {
            // A missing block is itself part of the shape.
            0xFFFF_FFFFu32.hash(&mut hasher);
            continue;
        };
        block.insts.len().hash(&mut hasher);
        for inst in &block.insts {
            // `{:?}` is deterministic for a fixed IR and covers opcode,
            // operands (including float immediates), flags, and proof origin.
            format!("{:?}", inst).hash(&mut hasher);
        }
        block.successors.len().hash(&mut hasher);
        for succ in &block.successors {
            succ.0.hash(&mut hasher);
        }
    }
    hasher.finish()
}

/// Returns true if the x86 fixpoint loop should emit non-convergence
/// diagnostics to stderr. Controlled by `TRUST_CG_X86_FIXPOINT_LOG`; off by
/// default so it is harmless in production runs.
fn fixpoint_log_enabled() -> bool {
    std::env::var_os("TRUST_CG_X86_FIXPOINT_LOG").is_some()
}

/// Diagnostic IR dump hook: `TCG_X86_PM_DUMP=<substr>` dumps every function's
/// IR to stderr after each pass whose name contains `<substr>` (empty value =
/// every pass). `TCG_X86_PM_DUMP_FN=<substr>` additionally restricts the dump
/// to functions whose name contains `<substr>`. Purely observational — never
/// changes the IR or pass verdicts; off by default.
fn dump_filter() -> Option<(String, Option<String>)> {
    static FILTER: std::sync::OnceLock<Option<(String, Option<String>)>> =
        std::sync::OnceLock::new();
    FILTER
        .get_or_init(|| {
            std::env::var("TCG_X86_PM_DUMP")
                .ok()
                .map(|pass| (pass, std::env::var("TCG_X86_PM_DUMP_FN").ok()))
        })
        .clone()
}

fn maybe_dump_after(pass_name: &str, func: &X86ISelFunction) {
    let Some((pass_filter, fn_filter)) = dump_filter() else {
        return;
    };
    if !pass_filter.is_empty() && !pass_name.contains(&pass_filter) {
        return;
    }
    if let Some(f) = &fn_filter
        && !func.name.contains(f.as_str())
    {
        return;
    }
    eprintln!("=== [pm-dump] after `{}` fn `{}` ===", pass_name, func.name);
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        eprintln!("  Block({}) succs={:?}", block_id.0, block.successors);
        for (i, inst) in block.insts.iter().enumerate() {
            eprintln!("    [{i}] {:?} {:?}", inst.opcode, inst.operands);
        }
    }
    eprintln!("=== [pm-dump] end `{}` ===", func.name);
}

/// A single x86-64 machine pass over ISel-output instructions.
///
/// Implementations may inspect or mutate `X86ISelInst`s through the function's
/// ordered blocks. Returning `true` reports that the function changed.
pub trait X86MachinePass {
    /// Human-readable name for diagnostics and logging.
    fn name(&self) -> &str;

    /// Run the pass on an x86-64 ISel function.
    fn run(&mut self, func: &mut X86ISelFunction) -> bool;
}

/// Manages and executes an ordered list of x86-64 machine passes.
pub struct X86PassManager {
    passes: Vec<Box<dyn X86MachinePass>>,
}

impl X86PassManager {
    /// Create an empty x86 pass manager.
    pub fn new() -> Self {
        Self { passes: Vec::new() }
    }

    /// Add a pass to the end of the pipeline.
    pub fn add_pass(&mut self, pass: Box<dyn X86MachinePass>) {
        self.passes.push(pass);
    }

    /// Add a pass to the end of the pipeline (builder pattern).
    pub fn with_pass(mut self, pass: Box<dyn X86MachinePass>) -> Self {
        self.passes.push(pass);
        self
    }

    /// Returns the number of registered passes.
    pub fn num_passes(&self) -> usize {
        self.passes.len()
    }

    /// Returns registered pass names in pipeline order.
    pub fn pass_names(&self) -> Vec<&str> {
        self.passes.iter().map(|pass| pass.name()).collect()
    }

    /// Run all passes once in order.
    ///
    /// Returns `true` if any pass modified the function.
    pub fn run_once(&mut self, func: &mut X86ISelFunction) -> bool {
        let mut changed = false;
        for pass in &mut self.passes {
            if pass.run(func) {
                changed = true;
            }
            maybe_dump_after(pass.name(), func);
        }
        changed
    }

    /// Run all passes once in order, collecting per-pass statistics.
    pub fn run_once_with_stats(&mut self, func: &mut X86ISelFunction) -> X86PassStats {
        let mut stats = self.empty_stats();
        stats.iterations = 1;

        for (i, pass) in self.passes.iter_mut().enumerate() {
            stats.runs[i].1 = 1;
            if pass.run(func) {
                stats.changes += 1;
            }
            maybe_dump_after(pass.name(), func);
        }

        stats
    }

    /// Run all passes repeatedly until no pass reports changes, or
    /// `max_iterations` is reached.
    ///
    /// # Convergence
    ///
    /// The loop stops as soon as a full iteration reports no changes (a fixed
    /// point). Two failure modes are detected and reported rather than being
    /// silently truncated:
    ///
    /// 1. **Stable-state guard.** A pass may return `true` ("changed") while
    ///    leaving the IR byte-for-byte identical — e.g. a rewrite that toggles
    ///    a form back and forth, or a `changed` flag that does not reflect a
    ///    real edit. Left unchecked this burns the entire iteration budget on a
    ///    no-op. After each iteration we compare a structural
    ///    `function_fingerprint`; if the IR is unchanged from the previous
    ///    iteration we treat the function as converged, stop early, and (under
    ///    `TRUST_CG_X86_FIXPOINT_LOG`) report the spurious-change cycle.
    ///
    /// 2. **Budget exhaustion.** If we run all `max_iterations` and the last
    ///    iteration still reported a change *and* still mutated the IR, the
    ///    function did not reach a fixed point within budget. We report this
    ///    (under `TRUST_CG_X86_FIXPOINT_LOG`) so non-convergence is visible.
    ///
    /// Either way the function is returned in its last state; detection never
    /// changes the optimization result, only surfaces diagnostics.
    pub fn run_to_fixpoint(
        &mut self,
        func: &mut X86ISelFunction,
        max_iterations: u32,
    ) -> X86PassStats {
        let mut stats = self.empty_stats();

        if max_iterations == 0 {
            return stats;
        }

        let mut prev_fingerprint = function_fingerprint(func);
        let mut converged = false;

        for iteration in 0..max_iterations {
            stats.iterations = iteration + 1;
            let mut any_changed = false;

            for (i, pass) in self.passes.iter_mut().enumerate() {
                stats.runs[i].1 += 1;
                if pass.run(func) {
                    any_changed = true;
                    stats.changes += 1;
                }
                maybe_dump_after(pass.name(), func);
            }

            if !any_changed {
                converged = true;
                break;
            }

            // Stable-state guard: a pass reported a change but the IR is
            // structurally identical to the previous iteration. This is a
            // non-progressing cycle; converge and report rather than spinning
            // the budget on a no-op.
            let fingerprint = function_fingerprint(func);
            if fingerprint == prev_fingerprint {
                if fixpoint_log_enabled() {
                    eprintln!(
                        "x86-fixpoint: function `{}` reported a change at iteration {} \
                         without mutating the IR (spurious-change cycle); treating as \
                         converged after {} iteration(s)",
                        func.name,
                        iteration + 1,
                        stats.iterations,
                    );
                }
                converged = true;
                break;
            }
            prev_fingerprint = fingerprint;
        }

        // Budget exhaustion: ran the full budget and the IR was still changing.
        if !converged && fixpoint_log_enabled() {
            eprintln!(
                "x86-fixpoint: function `{}` did not converge within the \
                 {}-iteration budget (still changing); optimization may be \
                 truncated",
                func.name, max_iterations,
            );
        }

        stats
    }

    fn empty_stats(&self) -> X86PassStats {
        X86PassStats {
            runs: self
                .passes
                .iter()
                .map(|pass| (pass.name().to_string(), 0))
                .collect(),
            changes: 0,
            iterations: 0,
            proof_optimization_certificates: Vec::new(),
            certified_pass_runs: Vec::new(),
            kernel_recheck: Ok(()),
        }
    }
}

impl Default for X86PassManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::rc::Rc;

    use trust_cg_ir::inst::InstFlags;
    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::x86_64_ops::X86Opcode;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;
    use trust_cg_lower::{X86ISelInst, X86ISelOperand};

    #[derive(Debug, PartialEq)]
    struct InstSnapshot {
        opcode: X86Opcode,
        operands: Vec<X86ISelOperand>,
        flags: InstFlags,
    }

    #[derive(Debug, PartialEq)]
    struct FunctionSnapshot {
        name: String,
        block_order: Vec<Block>,
        blocks: Vec<(Block, Vec<InstSnapshot>, Vec<Block>)>,
        next_vreg: u32,
    }

    struct NamedNoOpPass(&'static str);

    impl X86MachinePass for NamedNoOpPass {
        fn name(&self) -> &str {
            self.0
        }

        fn run(&mut self, _func: &mut X86ISelFunction) -> bool {
            false
        }
    }

    struct ReplaceNopPass {
        visits: Rc<Cell<usize>>,
    }

    impl X86MachinePass for ReplaceNopPass {
        fn name(&self) -> &str {
            "replace-nop"
        }

        fn run(&mut self, func: &mut X86ISelFunction) -> bool {
            let mut changed = false;
            for block_id in func.block_order.clone() {
                let Some(block) = func.blocks.get_mut(&block_id) else {
                    continue;
                };
                for inst in &mut block.insts {
                    self.visits.set(self.visits.get() + 1);
                    if inst.opcode == X86Opcode::Nop {
                        *inst = X86ISelInst::new(
                            X86Opcode::MovRI,
                            vec![
                                X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                                X86ISelOperand::Imm(7),
                            ],
                        );
                        changed = true;
                    }
                }
            }
            changed
        }
    }

    /// Pass that always claims it changed the function but never mutates the
    /// IR. Used to exercise the fixpoint stable-state (spurious-change) guard.
    struct AlwaysClaimsChangedPass {
        runs: Rc<Cell<usize>>,
    }

    impl X86MachinePass for AlwaysClaimsChangedPass {
        fn name(&self) -> &str {
            "always-claims-changed"
        }

        fn run(&mut self, _func: &mut X86ISelFunction) -> bool {
            self.runs.set(self.runs.get() + 1);
            true
        }
    }

    /// Pass that appends a fresh `Nop` to the entry block every run, so the IR
    /// genuinely changes on each iteration and never reaches a fixed point.
    /// Used to exercise the iteration-budget exhaustion path.
    struct GrowsEveryRunPass {
        runs: Rc<Cell<usize>>,
    }

    impl X86MachinePass for GrowsEveryRunPass {
        fn name(&self) -> &str {
            "grows-every-run"
        }

        fn run(&mut self, func: &mut X86ISelFunction) -> bool {
            self.runs.set(self.runs.get() + 1);
            let block_id = func.block_order[0];
            let block = func.blocks.get_mut(&block_id).unwrap();
            block
                .insts
                .insert(0, X86ISelInst::new(X86Opcode::Nop, vec![]));
            true
        }
    }

    /// Pass that performs exactly one real edit (turning the first `Nop` into a
    /// `MovRI`) on its first run, then reports no change forever after. Used to
    /// confirm the fixpoint loop terminates promptly at the true fixed point.
    struct OneShotEditPass {
        runs: Rc<Cell<usize>>,
    }

    impl X86MachinePass for OneShotEditPass {
        fn name(&self) -> &str {
            "one-shot-edit"
        }

        fn run(&mut self, func: &mut X86ISelFunction) -> bool {
            self.runs.set(self.runs.get() + 1);
            let block_id = func.block_order[0];
            let block = func.blocks.get_mut(&block_id).unwrap();
            for inst in &mut block.insts {
                if inst.opcode == X86Opcode::Nop {
                    *inst = X86ISelInst::new(
                        X86Opcode::MovRI,
                        vec![
                            X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                            X86ISelOperand::Imm(1),
                        ],
                    );
                    return true;
                }
            }
            false
        }
    }

    fn make_x86_func() -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_pm_test".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 1;
        func.push_inst(entry, X86ISelInst::new(X86Opcode::Nop, vec![]));
        func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));
        func
    }

    fn snapshot(func: &X86ISelFunction) -> FunctionSnapshot {
        let blocks = func
            .block_order
            .iter()
            .map(|&block_id| {
                let block = func.blocks.get(&block_id).unwrap();
                let insts = block
                    .insts
                    .iter()
                    .map(|inst| InstSnapshot {
                        opcode: inst.opcode,
                        operands: inst.operands.clone(),
                        flags: inst.flags,
                    })
                    .collect();
                (block_id, insts, block.successors.clone())
            })
            .collect();

        FunctionSnapshot {
            name: func.name.clone(),
            block_order: func.block_order.clone(),
            blocks,
            next_vreg: func.next_vreg,
        }
    }

    #[test]
    fn empty_x86_pass_manager_preserves_isel_output() {
        let mut pm = X86PassManager::new();
        let mut func = make_x86_func();
        let before = snapshot(&func);

        let stats = pm.run_once_with_stats(&mut func);

        assert_eq!(stats.total_pass_runs(), 0);
        assert_eq!(stats.changes, 0);
        assert_eq!(stats.iterations, 1);
        assert_eq!(snapshot(&func), before);
    }

    #[test]
    fn x86_pass_manager_runs_passes_in_order() {
        let pm = X86PassManager::new()
            .with_pass(Box::new(NamedNoOpPass("first")))
            .with_pass(Box::new(NamedNoOpPass("second")));

        assert_eq!(pm.num_passes(), 2);
        assert_eq!(pm.pass_names(), vec!["first", "second"]);
    }

    #[test]
    fn x86_machine_pass_can_visit_and_mutate_instructions() {
        let visits = Rc::new(Cell::new(0));
        let mut pm = X86PassManager::new().with_pass(Box::new(ReplaceNopPass {
            visits: visits.clone(),
        }));
        let mut func = make_x86_func();

        assert!(pm.run_once(&mut func));

        let entry = func.blocks.get(&Block(0)).unwrap();
        assert_eq!(visits.get(), 2);
        assert_eq!(entry.insts[0].opcode, X86Opcode::MovRI);
        assert_eq!(
            entry.insts[0].operands,
            vec![
                X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                X86ISelOperand::Imm(7),
            ]
        );
        assert_eq!(entry.insts[0].flags, X86Opcode::MovRI.default_flags());
        assert_eq!(entry.insts[1].opcode, X86Opcode::Ret);
    }

    #[test]
    fn fixpoint_stops_at_true_fixed_point_without_burning_budget() {
        let runs = Rc::new(Cell::new(0));
        let mut pm =
            X86PassManager::new().with_pass(Box::new(OneShotEditPass { runs: runs.clone() }));
        let mut func = make_x86_func();

        let stats = pm.run_to_fixpoint(&mut func, 8);

        // Iteration 1 edits (returns true); iteration 2 sees nothing to do
        // (returns false) and the loop stops. The budget of 8 is not consumed.
        assert_eq!(stats.iterations, 2);
        assert_eq!(runs.get(), 2);
        assert_eq!(stats.changes, 1);
        let entry = func.blocks.get(&Block(0)).unwrap();
        assert_eq!(entry.insts[0].opcode, X86Opcode::MovRI);
    }

    #[test]
    fn fixpoint_stable_state_guard_stops_spurious_change_cycle() {
        // A pass that always reports "changed" but never edits the IR must not
        // spin the full iteration budget: the structural fingerprint is
        // unchanged after the first iteration, so the loop converges at
        // iteration 2.
        let runs = Rc::new(Cell::new(0));
        let mut pm = X86PassManager::new()
            .with_pass(Box::new(AlwaysClaimsChangedPass { runs: runs.clone() }));
        let mut func = make_x86_func();
        let before = snapshot(&func);

        let stats = pm.run_to_fixpoint(&mut func, 16);

        // Iteration 1 runs the pass; the fingerprint is unchanged from the
        // pre-loop fingerprint, so the stable-state guard breaks immediately at
        // iteration 1 instead of running all 16.
        assert_eq!(stats.iterations, 1);
        assert_eq!(runs.get(), 1);
        // The IR is untouched.
        assert_eq!(snapshot(&func), before);
    }

    #[test]
    fn fixpoint_reports_budget_exhaustion_when_not_converged() {
        // A pass that genuinely grows the IR every run never converges; the
        // loop must run exactly `max_iterations` and surface the truncation
        // (here we assert the budget was fully consumed, which is the
        // observable signal alongside the gated stderr diagnostic).
        let runs = Rc::new(Cell::new(0));
        let mut pm =
            X86PassManager::new().with_pass(Box::new(GrowsEveryRunPass { runs: runs.clone() }));
        let mut func = make_x86_func();

        let stats = pm.run_to_fixpoint(&mut func, 3);

        assert_eq!(stats.iterations, 3);
        assert_eq!(runs.get(), 3);
        assert_eq!(stats.changes, 3);
        // The IR really did change each iteration (3 Nops prepended).
        let entry = func.blocks.get(&Block(0)).unwrap();
        let nop_count = entry
            .insts
            .iter()
            .filter(|i| i.opcode == X86Opcode::Nop)
            .count();
        assert_eq!(nop_count, 1 + 3, "one seeded Nop plus three prepended");
    }

    #[test]
    fn fixpoint_zero_budget_is_a_noop() {
        let runs = Rc::new(Cell::new(0));
        let mut pm =
            X86PassManager::new().with_pass(Box::new(GrowsEveryRunPass { runs: runs.clone() }));
        let mut func = make_x86_func();
        let before = snapshot(&func);

        let stats = pm.run_to_fixpoint(&mut func, 0);

        assert_eq!(stats.iterations, 0);
        assert_eq!(runs.get(), 0);
        assert_eq!(snapshot(&func), before);
    }

    #[test]
    fn function_fingerprint_changes_with_ir_and_is_stable_otherwise() {
        let func = make_x86_func();
        let fp1 = function_fingerprint(&func);
        let fp2 = function_fingerprint(&func);
        assert_eq!(fp1, fp2, "fingerprint must be deterministic for fixed IR");

        let mut mutated = make_x86_func();
        let block = mutated.blocks.get_mut(&Block(0)).unwrap();
        block
            .insts
            .insert(0, X86ISelInst::new(X86Opcode::Nop, vec![]));
        assert_ne!(
            fp1,
            function_fingerprint(&mutated),
            "fingerprint must change when the IR changes"
        );
    }
}
