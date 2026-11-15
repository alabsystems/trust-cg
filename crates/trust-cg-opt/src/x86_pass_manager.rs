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
use trust_cg_lower::x86_64_isel::{X86ISelInst, X86ISelOperand};

use crate::pass_manager::PassStats;

/// Statistics collected during x86 pass execution.
pub type X86PassStats = PassStats;

/// Hash one ISel operand into `hasher`, structurally.
///
/// Every variant contributes a distinct leading tag byte followed by ALL of its
/// fields, so two operands hash the same input only when they agree field by
/// field. The `f64` immediate is hashed by `to_bits`, which is strictly FINER
/// than the previous `{:?}` rendering (it separates `+0.0`/`-0.0` and distinct
/// NaN payloads that `Debug` collapses) — see `function_fingerprint` for why a
/// finer fingerprint is always safe and a coarser one never is.
///
/// The `match` is exhaustive with NO wildcard arm on purpose: adding a variant
/// to [`X86ISelOperand`] must be a compile error here, not a silent loss of
/// fingerprint resolution.
fn hash_x86_isel_operand<H: Hasher>(op: &X86ISelOperand, hasher: &mut H) {
    match op {
        X86ISelOperand::VReg(v) => {
            0u8.hash(hasher);
            v.hash(hasher);
        }
        X86ISelOperand::PReg(p) => {
            1u8.hash(hasher);
            p.hash(hasher);
        }
        X86ISelOperand::Imm(i) => {
            2u8.hash(hasher);
            i.hash(hasher);
        }
        X86ISelOperand::FImm(f) => {
            3u8.hash(hasher);
            f.to_bits().hash(hasher);
        }
        X86ISelOperand::Block(b) => {
            4u8.hash(hasher);
            b.hash(hasher);
        }
        X86ISelOperand::CondCode(cc) => {
            5u8.hash(hasher);
            cc.hash(hasher);
        }
        X86ISelOperand::Symbol(s) => {
            6u8.hash(hasher);
            s.hash(hasher);
        }
        X86ISelOperand::ExactModuleSymbol(s) => {
            12u8.hash(hasher);
            s.hash(hasher);
        }
        X86ISelOperand::StackSlot(s) => {
            7u8.hash(hasher);
            s.hash(hasher);
        }
        X86ISelOperand::MemAddr { base, disp } => {
            8u8.hash(hasher);
            hash_x86_isel_operand(base, hasher);
            disp.hash(hasher);
        }
        X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } => {
            9u8.hash(hasher);
            hash_x86_isel_operand(base, hasher);
            hash_x86_isel_operand(index, hasher);
            scale.hash(hasher);
            disp.hash(hasher);
        }
        X86ISelOperand::ConstPoolEntry(i) => {
            10u8.hash(hasher);
            i.hash(hasher);
        }
        X86ISelOperand::JumpTableIndex(i) => {
            11u8.hash(hasher);
            i.hash(hasher);
        }
    }
}

/// Hash one ISel instruction into `hasher`, structurally.
///
/// The instruction is destructured with NO `..` rest pattern: a new field on
/// [`X86ISelInst`] must be a compile error here, so the fingerprint can never
/// silently stop observing part of the instruction.
fn hash_x86_isel_inst<H: Hasher>(inst: &X86ISelInst, hasher: &mut H) {
    let X86ISelInst {
        opcode,
        operands,
        flags,
        proof_origin,
        call_arg_regs,
        call_result_regs,
        internal_return_regs,
        lowering_provenance,
    } = inst;

    opcode.hash(hasher);

    operands.len().hash(hasher);
    for op in operands {
        hash_x86_isel_operand(op, hasher);
    }

    // `InstFlags` derives `Hash` over its whole u16 bitfield — strictly finer
    // than its hand-written `Debug`, which renders only the named flags.
    flags.hash(hasher);

    // `X86ProofOrigin` is a field-less enum without a `Hash` derive; its
    // discriminant carries exactly the information `Debug` prints.
    match proof_origin {
        None => 0u8.hash(hasher),
        Some(origin) => {
            1u8.hash(hasher);
            std::mem::discriminant(origin).hash(hasher);
        }
    }

    call_arg_regs.len().hash(hasher);
    for arg in call_arg_regs {
        arg.reg.hash(hasher);
        arg.read_bits.hash(hasher);
    }

    match call_result_regs {
        None => 0u8.hash(hasher),
        Some(regs) => {
            1u8.hash(hasher);
            regs.len().hash(hasher);
            for r in regs {
                r.reg.hash(hasher);
                r.defined_bits.hash(hasher);
            }
        }
    }

    // Hashed only when present, under its own tag, so every instruction that
    // carries none (all but the `ret` of a signature using the internal
    // multi-result registers) fingerprints exactly as before the field existed.
    if !internal_return_regs.is_empty() {
        2u8.hash(hasher);
        internal_return_regs.len().hash(hasher);
        for r in internal_return_regs {
            r.reg.hash(hasher);
            r.defined_bits.hash(hasher);
        }
    }

    lowering_provenance.hash(hasher);
}

/// Structural fingerprint of an [`X86ISelFunction`] used by the fixpoint loop
/// to detect non-convergence.
///
/// `X86ISelInst`/`X86ISelOperand` are not `Hash` (operands carry an `f64`
/// float immediate, so the types are not `Eq`/`Hash`), so each instruction is
/// hashed field by field by [`hash_x86_isel_inst`] — opcode, operands
/// (including the float immediate's bit pattern), flags, proof origin, the
/// call argument/result register declarations, and the lowering provenance.
/// That is the same information the previous `format!("{:?}", inst)` rendering
/// carried, at strictly finer resolution and without allocating a `String` per
/// instruction (this hash was 18% of the whole x86 optimization phase at 2400
/// functions, measured 2026-08-31).
///
/// # Why finer is safe and coarser is not
///
/// The fixpoint loop stops early when two consecutive iterations fingerprint
/// equal. A COARSER fingerprint could report "same" for genuinely different
/// IR and truncate optimization, changing emitted bytes. A FINER one can only
/// fail to take a shortcut: if the IR really is unchanged then, because every
/// pass is a deterministic function of the IR, the next iteration reproduces
/// it exactly, so the extra iterations are no-ops and the emitted bytes are
/// identical. Hence resolution may only ever be increased here, never reduced.
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
            hash_x86_isel_inst(inst, &mut hasher);
        }
        block.successors.len().hash(&mut hasher);
        for succ in &block.successors {
            succ.0.hash(&mut hasher);
        }
    }
    hasher.finish()
}

// ---------------------------------------------------------------------------
// DIAGNOSTIC (default off, `TCG_TIME_X86PM=1`): per-pass wall time
// ---------------------------------------------------------------------------
//
// `TCG_TIME`'s `x86_optimization` row is a single number covering ~16 passes
// run to a 4-iteration fixpoint. This splits it per pass (plus the fixpoint's
// own `function_fingerprint`) so the phase can be attributed instead of
// guessed. Purely observational: the timers are behind a memoized env check
// and never touch the IR or a pass verdict.

fn pm_timing_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TCG_TIME_X86PM").is_some())
}

static PM_TIMES: std::sync::Mutex<std::collections::BTreeMap<String, (u128, u64)>> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

fn pm_record(name: &str, elapsed: std::time::Duration) {
    let Ok(mut table) = PM_TIMES.lock() else {
        return;
    };
    let entry = table.entry(name.to_string()).or_insert((0, 0));
    entry.0 += elapsed.as_nanos();
    entry.1 += 1;
}

/// Ranked per-pass timing report, or `None` unless `TCG_TIME_X86PM` is set.
///
/// Diagnostic only; the caller (the `TCG_TIME` trace in `trust-cg-codegen`)
/// prints it next to the `x86_optimization` row.
pub fn x86_pass_timing_report() -> Option<String> {
    if !pm_timing_enabled() {
        return None;
    }
    let table = PM_TIMES.lock().ok()?;
    let mut rows: Vec<(&String, u128, u64)> =
        table.iter().map(|(k, (ns, n))| (k, *ns, *n)).collect();
    rows.sort_by_key(|row| std::cmp::Reverse(row.1));
    let total: u128 = rows.iter().map(|r| r.1).sum();
    let denom = total.max(1) as f64;
    let mut out = format!(
        "TCG_TIME_X86PM total={:.1}ms over {} entries\n",
        total as f64 / 1e6,
        rows.len()
    );
    for (name, ns, runs) in rows {
        out.push_str(&format!(
            "  {:<38} {:>9.1}ms {:>5.1}%  runs={}\n",
            name,
            ns as f64 / 1e6,
            100.0 * ns as f64 / denom,
            runs
        ));
    }
    Some(out)
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
        }
        changed
    }

    /// Run all passes once in order, collecting per-pass statistics.
    pub fn run_once_with_stats(&mut self, func: &mut X86ISelFunction) -> X86PassStats {
        let mut stats = self.empty_stats();
        stats.iterations = 1;
        let timing = pm_timing_enabled();

        for (i, pass) in self.passes.iter_mut().enumerate() {
            stats.runs[i].1 = 1;
            let started = timing.then(std::time::Instant::now);
            let changed = pass.run(func);
            if let Some(started) = started {
                pm_record(pass.name(), started.elapsed());
            }
            if changed {
                stats.changes += 1;
                stats.changed_runs[i].1 += 1;
            }
        }

        stats
    }

    /// Run all passes repeatedly until no pass reports changes, or
    /// `max_iterations` is reached.
    ///
    /// # Convergence
    ///
    /// The loop stops as soon as a full iteration reports no changes (a fixed
    /// point), or at the stable-state guard: a pass may return `true` ("changed")
    /// while leaving the IR byte-for-byte identical — e.g. a rewrite that toggles a
    /// form back and forth, or a `changed` flag that does not reflect a real edit.
    /// Left unchecked this burns the entire iteration budget on a no-op. After each
    /// iteration we compare a structural `function_fingerprint`; if the IR is
    /// unchanged from the previous iteration we treat the function as converged and
    /// stop early.
    ///
    /// A function still changing after `max_iterations` is returned in its
    /// last state; `stats.iterations` then equals the budget.
    pub fn run_to_fixpoint(
        &mut self,
        func: &mut X86ISelFunction,
        max_iterations: u32,
    ) -> X86PassStats {
        let mut stats = self.empty_stats();

        if max_iterations == 0 {
            return stats;
        }

        let timing = pm_timing_enabled();
        let fp_started = timing.then(std::time::Instant::now);
        let mut prev_fingerprint = function_fingerprint(func);
        if let Some(started) = fp_started {
            pm_record("<function_fingerprint>", started.elapsed());
        }

        for iteration in 0..max_iterations {
            stats.iterations = iteration + 1;
            let mut any_changed = false;

            for (i, pass) in self.passes.iter_mut().enumerate() {
                stats.runs[i].1 += 1;
                let started = timing.then(std::time::Instant::now);
                let changed = pass.run(func);
                if let Some(started) = started {
                    pm_record(pass.name(), started.elapsed());
                }
                if changed {
                    any_changed = true;
                    stats.changes += 1;
                    stats.changed_runs[i].1 += 1;
                }
            }

            if !any_changed {
                break;
            }

            // Stable-state guard: a pass reported a change but the IR is
            // structurally identical to the previous iteration. This is a
            // non-progressing cycle; converge and report rather than spinning
            // the budget on a no-op.
            let fp_started = timing.then(std::time::Instant::now);
            let fingerprint = function_fingerprint(func);
            if let Some(started) = fp_started {
                pm_record("<function_fingerprint>", started.elapsed());
            }
            if fingerprint == prev_fingerprint {
                break;
            }
            prev_fingerprint = fingerprint;
        }

        stats
    }

    fn empty_stats(&self) -> X86PassStats {
        let names = || {
            self.passes
                .iter()
                .map(|pass| (pass.name().to_string(), 0))
                .collect()
        };
        X86PassStats {
            runs: names(),
            changed_runs: names(),
            changes: 0,
            iterations: 0,
            proof_optimization_certificates: Vec::new(),
            certified_pass_runs: Vec::new(),
            kernel_recheck: Ok(()),
            // The L10-P5 admission reads `trust_cg_ir::MachFunction`; x86
            // passes run on `X86ISelFunction`, which it does not cover.
            id_admission: Ok(()),
            // The x86 pass manager has no per-pass validation.
            pass_validation: crate::pass_validation::PassValidationSummary::default(),
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

    #[test]
    fn exact_function_address_operand_has_distinct_fingerprint() {
        let fingerprint = |operand| {
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            hash_x86_isel_operand(&operand, &mut hash);
            hash.finish()
        };
        assert_ne!(
            fingerprint(X86ISelOperand::Symbol("target".into())),
            fingerprint(X86ISelOperand::ExactModuleSymbol("target".into()))
        );
        assert_ne!(
            fingerprint(X86ISelOperand::ExactModuleSymbol("target".into())),
            fingerprint(X86ISelOperand::ExactModuleSymbol("_target".into()))
        );
    }

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
        // loop must run exactly `max_iterations` (the budget is fully
        // consumed).
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
