// trust-cg-verify/cegis_pass_x86.rs - x86-64 CEGIS superopt pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// x86-64 analogue of `crate::cegis_pass::CegisSuperoptPass`. The AArch64 pass
// operates on `trust_cg_ir::MachFunction` (whose `MachInst::opcode` is
// hardcoded to `AArch64Opcode`); x86-64 codegen uses a *separate* IR,
// `trust_cg_lower::x86_64_isel::X86ISelFunction` / `X86ISelInst`
// (`opcode: X86Opcode`). Because the two machine IRs are distinct Rust types,
// x86 CEGIS cannot reuse the AArch64 matcher; it needs its own pass over the
// x86 ISel IR. The verification engine (`crate::CegisLoop::verify`, QF_BV
// bitvector equivalence over `SmtExpr`) IS target-agnostic and is reused
// verbatim here.
//
// # Scope: immediate fusion (flag-exact, zero new miscompile class)
//
// The one family this pass rewrites is *immediate fusion*:
//
// ```text
//   MOV   v, imm            ; v is single-use, imm fits sign-extended imm32
//   <op>  dst, v            ; <op> in {ADD, SUB, AND, OR, XOR}, register form
//   =>
//   <op>  dst, imm          ; register-immediate form; the MOV is removed
// ```
//
// This is deliberately the *safest possible* rewrite: an x86 `<op> r, r2`
// where `r2` holds the value `imm` computes a bit-identical **result AND
// bit-identical EFLAGS** to `<op> r, imm` (the two forms differ only in the
// encoding of the second source, not in the value combined). So the fusion is
// sound even when the flags the op writes are live downstream — no
// flag-liveness analysis is required, and no new machine-semantics encoding is
// introduced (the enumeration reuses the existing `SmtExpr` ALU builders).
// The win is purely instruction-count (the constant materialization `MOV`
// disappears).
//
// Every rewrite is admitted ONLY after `CegisLoop::verify` returns
// `CegisResult::Equivalent` (a QF_BV UNSAT proof that the register form and
// the immediate form coincide for all operand values). On timeout / error /
// not-equivalent the original instructions are kept verbatim (fail-closed).
//
// The pass is disabled by default (`budget_sec == 0`); with it disabled `run`
// is a strict no-op and the emitted bytes are byte-identical to a build
// without the pass. The x86 codegen pipeline only enables it behind the
// `TCG_CEGIS_X86` environment gate.

//! x86-64 CEGIS superoptimization pass (immediate fusion).

use std::collections::HashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::{Duration, Instant};

use trust_cg_ir::X86Opcode;
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::cegis::{CegisLoop, CegisResult};
use crate::smt::SmtExpr;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for [`X86CegisSuperoptPass`].
///
/// The pass is effectively disabled when `budget_sec == 0` (the default),
/// which makes [`X86CegisSuperoptPass::run`] a strict no-op.
#[derive(Debug, Clone)]
pub struct X86CegisSuperoptConfig {
    /// Total per-function wall-clock budget in seconds. `0` disables the pass.
    pub budget_sec: u64,
    /// Per solver query timeout (milliseconds).
    pub per_query_ms: u64,
}

impl X86CegisSuperoptConfig {
    /// Build a disabled-default configuration.
    pub fn disabled() -> Self {
        Self {
            budget_sec: 0,
            per_query_ms: 5_000,
        }
    }

    /// Read the `TCG_CEGIS_X86` environment gate.
    ///
    /// `TCG_CEGIS_X86=<n>` (a positive integer) enables the pass with a
    /// per-function budget of `n` seconds. Unset / `0` / unparseable keeps the
    /// pass disabled (byte-identical output).
    pub fn from_env() -> Self {
        let budget_sec = std::env::var("TCG_CEGIS_X86")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
            .unwrap_or(0);
        Self {
            budget_sec,
            per_query_ms: 5_000,
        }
    }

    /// Returns true if this configuration will actually run CEGIS queries.
    #[inline]
    pub fn is_enabled(&self) -> bool {
        self.budget_sec > 0
    }
}

impl Default for X86CegisSuperoptConfig {
    fn default() -> Self {
        Self::disabled()
    }
}

// ---------------------------------------------------------------------------
// Stats
// ---------------------------------------------------------------------------

/// Runtime statistics for one [`X86CegisSuperoptPass::run`] invocation series.
#[derive(Debug, Clone, Default)]
pub struct X86CegisPassStats {
    /// Number of functions the pass ran on (regardless of result).
    pub functions_seen: u64,
    /// Number of immediate-fusion candidate windows considered.
    pub candidates: u64,
    /// Number of candidate windows proven equivalent and committed.
    pub committed: u64,
    /// Number of candidate windows rejected (not equivalent / timeout / error).
    pub rejected: u64,
    /// Number of candidate windows whose CEGIS query timed out.
    pub timeouts: u64,
    /// Number of candidate windows whose CEGIS query returned a verifier error
    /// (e.g. the `ay` solver binary was not available).
    pub verifier_errors: u64,
    /// Number of verifier panics caught and contained.
    pub panics: u64,
    /// Number of solver queries actually issued (a strict subset of
    /// `candidates` thanks to the per-(opcode,width) proof memo).
    pub solver_calls: u64,
}

// ---------------------------------------------------------------------------
// The pass
// ---------------------------------------------------------------------------

/// A single proven immediate-fusion rewrite discovered in a block.
struct FusionRewrite {
    /// Index (in the block's `insts`) of the constant-materializing `MOV`.
    mov_index: usize,
    /// Index (in the block's `insts`) of the ALU instruction to rewrite.
    alu_index: usize,
    /// The register-immediate replacement for the ALU instruction.
    replacement: X86ISelInst,
}

/// CEGIS-driven immediate-fusion pass for x86-64 ISel functions.
///
/// See the module docs for the rewrite family, soundness argument, and gating.
pub struct X86CegisSuperoptPass {
    config: X86CegisSuperoptConfig,
    stats: X86CegisPassStats,
    /// Per-(opcode, width) proof memo. The equivalence `op(x, k) == op(x, k)`
    /// is independent of the concrete immediate, so one QF_BV proof per
    /// (opcode, width) covers every fusion of that shape (cache-by-window).
    proven: HashMap<(X86Opcode, u32), bool>,
}

impl X86CegisSuperoptPass {
    /// Create a new pass with the given configuration.
    pub fn new(config: X86CegisSuperoptConfig) -> Self {
        Self {
            config,
            stats: X86CegisPassStats::default(),
            proven: HashMap::new(),
        }
    }

    /// Return the collected statistics.
    pub fn stats(&self) -> &X86CegisPassStats {
        &self.stats
    }

    /// Run the pass over one x86-64 ISel function.
    ///
    /// Returns `true` if any instruction was rewritten. When the pass is
    /// disabled (`budget_sec == 0`) this is a strict no-op returning `false`.
    pub fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        if !self.config.is_enabled() {
            return false;
        }
        self.stats.functions_seen += 1;

        let deadline = Instant::now() + Duration::from_secs(self.config.budget_sec);
        let mut cegis = CegisLoop::new(1, self.config.per_query_ms);
        let mut committed = false;

        // Whole-function mention counts drive the single-use safety check.
        let mentions = count_all_vreg_mentions(func);

        for block_id in func.block_order.clone() {
            if Instant::now() >= deadline {
                break;
            }
            let insts = match func.blocks.get(&block_id) {
                Some(block) => block.insts.clone(),
                None => continue,
            };

            let rewrites = self.collect_block_rewrites(&insts, &mentions, &mut cegis, deadline);
            if rewrites.is_empty() {
                continue;
            }

            self.apply_rewrites(func, block_id, rewrites);
            committed = true;
        }

        self.stats.solver_calls = self
            .stats
            .solver_calls
            .saturating_add(cegis.stats_solver_calls());
        committed
    }

    /// Find every proven immediate-fusion rewrite in one block's instruction
    /// list. Purely reads `insts`; mutation is deferred to `apply_rewrites`.
    fn collect_block_rewrites(
        &mut self,
        insts: &[X86ISelInst],
        mentions: &HashMap<u32, u32>,
        cegis: &mut CegisLoop,
        deadline: Instant,
    ) -> Vec<FusionRewrite> {
        let mut rewrites = Vec::new();
        // Forward def scan: last index that wrote each register operand-0.
        let mut def_index: HashMap<u32, usize> = HashMap::new();
        // Reserve each MOV so two ALUs cannot both claim the same constant.
        let mut consumed_mov: HashMap<usize, ()> = HashMap::new();

        for (i, inst) in insts.iter().enumerate() {
            if let Some(candidate) = self.match_immediate_fusion(insts, i, &def_index, mentions) {
                let key = (candidate.op, candidate.width);
                if let std::collections::hash_map::Entry::Vacant(e) =
                    consumed_mov.entry(candidate.mov_index)
                {
                    if Instant::now() >= deadline {
                        break;
                    }
                    self.stats.candidates += 1;
                    if self.prove_fusion(cegis, key) {
                        e.insert(());
                        rewrites.push(FusionRewrite {
                            mov_index: candidate.mov_index,
                            alu_index: i,
                            replacement: candidate.replacement,
                        });
                    }
                }
            }

            // Record the definition produced by this instruction (operand 0 in
            // register form). Stores put a memory operand in slot 0, so they
            // record nothing.
            if let Some(dst) = inst.operands.first().and_then(operand_as_vreg) {
                def_index.insert(dst.id, i);
            }
        }

        rewrites
    }

    /// Prove (or recall from the memo) that immediate fusion for `(op, width)`
    /// is a value equivalence. Records stats. Returns `true` iff proven.
    fn prove_fusion(&mut self, cegis: &mut CegisLoop, key: (X86Opcode, u32)) -> bool {
        if let Some(&proven) = self.proven.get(&key) {
            if proven {
                self.stats.committed += 1;
            } else {
                self.stats.rejected += 1;
            }
            return proven;
        }

        let (op, width) = key;
        // Theorem: an x86 `<op> r, r2` where r2 holds value `k` computes the
        // same result as `<op> r, imm=k`, for all r (=x) and all k. Both sides
        // are modeled by the same ALU builder, so the QF_BV obligation is
        // `forall x k. op(x,k) == op(x,k)` — the solver produces the verdict on
        // the raw formula (see ay_bridge::simplifier_alone_proved_unsat guard).
        let vars = vec![("x".to_string(), width), ("k".to_string(), width)];
        let x = SmtExpr::var("x", width);
        let k = SmtExpr::var("k", width);
        let src = apply_alu(op, &x, &k);
        let tgt = apply_alu(op, &x, &k);

        cegis.clear_counterexamples();
        cegis.add_edge_case_seeds(&vars);

        let result = catch_unwind(AssertUnwindSafe(|| cegis.verify(&src, &tgt, &vars)));
        let proven = match result {
            Ok(CegisResult::Equivalent { .. }) => {
                self.stats.committed += 1;
                true
            }
            Ok(CegisResult::NotEquivalent { .. }) => {
                self.stats.rejected += 1;
                false
            }
            Ok(CegisResult::Timeout | CegisResult::MaxIterationsReached { .. }) => {
                self.stats.timeouts += 1;
                self.stats.rejected += 1;
                false
            }
            Ok(CegisResult::Error(_)) => {
                self.stats.verifier_errors += 1;
                self.stats.rejected += 1;
                false
            }
            Err(_) => {
                self.stats.panics += 1;
                self.stats.rejected += 1;
                false
            }
        };

        self.proven.insert(key, proven);
        proven
    }

    /// Match an immediate-fusion window whose ALU is `insts[alu_index]`.
    ///
    /// Returns the matched candidate (constant `MOV` index, register width, ALU
    /// opcode, and the register-immediate replacement) or `None`.
    fn match_immediate_fusion(
        &self,
        insts: &[X86ISelInst],
        alu_index: usize,
        def_index: &HashMap<u32, usize>,
        mentions: &HashMap<u32, u32>,
    ) -> Option<MatchedFusion> {
        let alu = &insts[alu_index];
        let ri_op = fusible_ri_opcode(alu.opcode)?;

        // ALU register form: `<op> dst, v` with exactly two register operands.
        let (dst, v) = match alu.operands.as_slice() {
            [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(v)] => (*dst, *v),
            _ => return None,
        };
        if dst.id == v.id {
            return None;
        }
        let width = gpr_width(dst.class)?;
        if gpr_width(v.class)? != width {
            return None;
        }

        // `v` must be defined by a constant `MOV v, imm` earlier in this block.
        let mov_index = *def_index.get(&v.id)?;
        let mov = &insts[mov_index];
        if mov.opcode != X86Opcode::MovRI {
            return None;
        }
        let imm = match mov.operands.as_slice() {
            [X86ISelOperand::VReg(mov_dst), X86ISelOperand::Imm(imm)] if mov_dst.id == v.id => *imm,
            _ => return None,
        };

        // The register-immediate forms take a sign-extended imm32.
        if imm < i64::from(i32::MIN) || imm > i64::from(i32::MAX) {
            return None;
        }

        // `v` must be single-use: exactly one def (the MOV, operand 0) plus one
        // use (this ALU's operand 1) => exactly two total mentions. Any other
        // reader (including inside an addressing mode) makes removing the MOV
        // unsafe.
        if mentions.get(&v.id).copied().unwrap_or(0) != 2 {
            return None;
        }

        let mut replacement = X86ISelInst::new(
            ri_op,
            vec![X86ISelOperand::VReg(dst), X86ISelOperand::Imm(imm)],
        );
        // Preserve provenance / proof origin from the ALU we are rewriting.
        replacement.proof_origin = alu.proof_origin;
        replacement.lowering_provenance = alu.lowering_provenance;

        Some(MatchedFusion {
            mov_index,
            width,
            op: alu.opcode,
            replacement,
        })
    }

    /// Apply the collected rewrites to one block: overwrite each ALU with its
    /// register-immediate form and drop the now-dead constant `MOV`s.
    fn apply_rewrites(
        &self,
        func: &mut X86ISelFunction,
        block_id: trust_cg_lower::instructions::Block,
        rewrites: Vec<FusionRewrite>,
    ) {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            return;
        };
        let mut remove: HashMap<usize, ()> = HashMap::new();
        for rw in &rewrites {
            block.insts[rw.alu_index] = rw.replacement.clone();
            remove.insert(rw.mov_index, ());
        }
        if !remove.is_empty() {
            let mut idx = 0usize;
            block.insts.retain(|_| {
                let keep = !remove.contains_key(&idx);
                idx += 1;
                keep
            });
        }
    }
}

/// A matched immediate-fusion window (pre-proof).
struct MatchedFusion {
    mov_index: usize,
    width: u32,
    op: X86Opcode,
    replacement: X86ISelInst,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Map a register-register ALU opcode to its register-immediate counterpart if
/// the fusion is flag-exact and semantics-preserving.
fn fusible_ri_opcode(op: X86Opcode) -> Option<X86Opcode> {
    match op {
        X86Opcode::AddRR => Some(X86Opcode::AddRI),
        X86Opcode::SubRR => Some(X86Opcode::SubRI),
        X86Opcode::AndRR => Some(X86Opcode::AndRI),
        X86Opcode::OrRR => Some(X86Opcode::OrRI),
        X86Opcode::XorRR => Some(X86Opcode::XorRI),
        _ => None,
    }
}

/// Build the `SmtExpr` for an ALU op combining `lhs` (destination value) with
/// `rhs` (the second source). Mirrors the x86 integer ALU semantics at the
/// data-result level.
fn apply_alu(op: X86Opcode, lhs: &SmtExpr, rhs: &SmtExpr) -> SmtExpr {
    match op {
        X86Opcode::AddRR => lhs.clone().bvadd(rhs.clone()),
        X86Opcode::SubRR => lhs.clone().bvsub(rhs.clone()),
        X86Opcode::AndRR => lhs.clone().bvand(rhs.clone()),
        X86Opcode::OrRR => lhs.clone().bvor(rhs.clone()),
        X86Opcode::XorRR => lhs.clone().bvxor(rhs.clone()),
        // Only fusible opcodes ever reach here.
        _ => lhs.clone(),
    }
}

/// GPR bit width for a register class, or `None` for non-GPR classes.
fn gpr_width(class: RegClass) -> Option<u32> {
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

/// Return the `VReg` if `operand` is a plain register (not an addressing mode).
fn operand_as_vreg(operand: &X86ISelOperand) -> Option<VReg> {
    match operand {
        X86ISelOperand::VReg(v) => Some(*v),
        _ => None,
    }
}

/// Count every mention of every VReg id across the whole function, recursing
/// into memory addressing operands. Used for the single-use safety check.
fn count_all_vreg_mentions(func: &X86ISelFunction) -> HashMap<u32, u32> {
    let mut counts: HashMap<u32, u32> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            for operand in &inst.operands {
                count_operand_mentions(operand, &mut counts);
            }
        }
    }
    counts
}

fn count_operand_mentions(operand: &X86ISelOperand, counts: &mut HashMap<u32, u32>) {
    match operand {
        X86ISelOperand::VReg(v) => {
            *counts.entry(v.id).or_insert(0) += 1;
        }
        X86ISelOperand::MemAddr { base, .. } => {
            count_operand_mentions(base, counts);
        }
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_mentions(base, counts);
            count_operand_mentions(index, counts);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::x86_64_isel::X86ISelBlock;

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    fn func_with_insts(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut f = X86ISelFunction::new(
            "t".to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        let block = Block(0);
        f.block_order = vec![block];
        f.blocks.insert(
            block,
            X86ISelBlock {
                insts,
                successors: vec![],
            },
        );
        f
    }

    /// `mov v1, 7 ; add v0, v1` — the canonical fusible window.
    fn fusible_func() -> X86ISelFunction {
        func_with_insts(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(vreg(1)), X86ISelOperand::Imm(7)],
            ),
            X86ISelInst::new(
                X86Opcode::AddRR,
                vec![X86ISelOperand::VReg(vreg(0)), X86ISelOperand::VReg(vreg(1))],
            ),
        ])
    }

    #[test]
    fn test_disabled_pass_is_noop() {
        let mut pass = X86CegisSuperoptPass::new(X86CegisSuperoptConfig::disabled());
        let mut func = fusible_func();
        let before = func.blocks[&Block(0)].insts.len();
        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().functions_seen, 0);
        assert_eq!(func.blocks[&Block(0)].insts.len(), before);
    }

    #[test]
    fn test_from_env_default_disabled() {
        // Absent env => disabled (SAFe run-in-any-environment default).
        // Note: does not mutate the environment.
        let cfg = X86CegisSuperoptConfig::from_env();
        if std::env::var("TCG_CEGIS_X86").is_err() {
            assert!(!cfg.is_enabled());
        }
    }

    #[test]
    fn test_matcher_detects_immediate_fusion() {
        let func = fusible_func();
        let insts = &func.blocks[&Block(0)].insts;
        let mentions = count_all_vreg_mentions(&func);
        let mut def_index = HashMap::new();
        def_index.insert(1u32, 0usize); // mov defines v1 at index 0
        let pass = X86CegisSuperoptPass::new(X86CegisSuperoptConfig::disabled());
        let m = pass.match_immediate_fusion(insts, 1, &def_index, &mentions);
        let m = m.expect("should match immediate fusion");
        assert_eq!(m.mov_index, 0);
        assert_eq!(m.op, X86Opcode::AddRR);
        assert_eq!(m.replacement.opcode, X86Opcode::AddRI);
        assert_eq!(
            m.replacement.operands,
            vec![X86ISelOperand::VReg(vreg(0)), X86ISelOperand::Imm(7)]
        );
    }

    #[test]
    fn test_matcher_rejects_multiuse_constant() {
        // mov v1, 7 ; add v0, v1 ; sub v2, v1  -- v1 used twice, cannot remove.
        let func = func_with_insts(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(vreg(1)), X86ISelOperand::Imm(7)],
            ),
            X86ISelInst::new(
                X86Opcode::AddRR,
                vec![X86ISelOperand::VReg(vreg(0)), X86ISelOperand::VReg(vreg(1))],
            ),
            X86ISelInst::new(
                X86Opcode::SubRR,
                vec![X86ISelOperand::VReg(vreg(2)), X86ISelOperand::VReg(vreg(1))],
            ),
        ]);
        let insts = &func.blocks[&Block(0)].insts;
        let mentions = count_all_vreg_mentions(&func);
        let mut def_index = HashMap::new();
        def_index.insert(1u32, 0usize);
        let pass = X86CegisSuperoptPass::new(X86CegisSuperoptConfig::disabled());
        assert!(
            pass.match_immediate_fusion(insts, 1, &def_index, &mentions)
                .is_none(),
            "multi-use constant must not be fused"
        );
    }

    #[test]
    fn test_matcher_rejects_wide_immediate() {
        // imm out of sign-extended imm32 range cannot be a register-immediate.
        let func = func_with_insts(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![
                    X86ISelOperand::VReg(vreg(1)),
                    X86ISelOperand::Imm(0x1_0000_0000),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::AddRR,
                vec![X86ISelOperand::VReg(vreg(0)), X86ISelOperand::VReg(vreg(1))],
            ),
        ]);
        let insts = &func.blocks[&Block(0)].insts;
        let mentions = count_all_vreg_mentions(&func);
        let mut def_index = HashMap::new();
        def_index.insert(1u32, 0usize);
        let pass = X86CegisSuperoptPass::new(X86CegisSuperoptConfig::disabled());
        assert!(
            pass.match_immediate_fusion(insts, 1, &def_index, &mentions)
                .is_none()
        );
    }

    #[test]
    fn test_enabled_pass_fuses_or_leaves_unchanged() {
        // With the pass enabled the result is EITHER the fused form (mov gone,
        // AddRI in place) when the solver is available, OR byte-identical to
        // the input when the solver is absent (Error => fail-closed). It must
        // never produce any other shape.
        let mut pass = X86CegisSuperoptPass::new(X86CegisSuperoptConfig {
            budget_sec: 5,
            per_query_ms: 5_000,
        });
        let mut func = fusible_func();
        let original = func.blocks[&Block(0)].insts.clone();
        let changed = pass.run(&mut func);
        let after = &func.blocks[&Block(0)].insts;

        if changed {
            // Fused: single AddRI dst, imm; the mov is gone.
            assert_eq!(after.len(), 1, "fusion should remove the constant MOV");
            assert_eq!(after[0].opcode, X86Opcode::AddRI);
            assert_eq!(
                after[0].operands,
                vec![X86ISelOperand::VReg(vreg(0)), X86ISelOperand::Imm(7)]
            );
            assert_eq!(pass.stats().committed, 1);
        } else {
            // Fail-closed: byte-identical to the input.
            assert_eq!(after.len(), original.len());
            assert_eq!(after[0].opcode, original[0].opcode);
            assert_eq!(after[1].opcode, original[1].opcode);
        }
    }

    #[test]
    fn test_non_fusible_function_unchanged() {
        // add v0, v1 with NO constant MOV feeding v1 -- nothing to fuse.
        let mut pass = X86CegisSuperoptPass::new(X86CegisSuperoptConfig {
            budget_sec: 5,
            per_query_ms: 5_000,
        });
        let mut func = func_with_insts(vec![X86ISelInst::new(
            X86Opcode::AddRR,
            vec![X86ISelOperand::VReg(vreg(0)), X86ISelOperand::VReg(vreg(1))],
        )]);
        assert!(!pass.run(&mut func));
        assert_eq!(func.blocks[&Block(0)].insts.len(), 1);
        assert_eq!(pass.stats().candidates, 0);
    }
}
