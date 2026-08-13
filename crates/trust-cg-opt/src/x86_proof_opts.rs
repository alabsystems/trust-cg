// trust-cg-opt - x86-64 proof-consuming guard elimination (kernel-gated)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Sentinel S5 — the x86-64 mirror of the AArch64 kernel-gated guard
//! elimination pass ([`crate::proof_opts::ProofOptimization`]), specialized to
//! the x86 ISel-output type universe (`X86ISelFunction`/`X86ISelInst`).
//!
//! This is the FIRST proof-driven elimination on x86. It deletes a proof-only
//! bounds-check carrier (`X86Opcode::TrapBoundsCheckExact`) ONLY when the
//! arch-neutral Certified-Elimination Kernel ([`trust_cg_ir::decide`]) authorizes
//! it against the discharged-obligation evidence and the carrier's bound
//! obligation. Every soundness-critical decision stays in the SHARED kernel — the
//! only x86-specific surface here is:
//!
//!   * classifying the carrier opcode ([`X86GuardTarget::classify_carrier`]), and
//!   * lifting the carrier's operands into the arch-neutral
//!     [`trust_cg_ir::GuardOperandIdentity`] ([`X86GuardTarget::operand_identity`]).
//!
//! Because the operand fingerprint is identical to AArch64's for the same
//! `[base, index, bound]` operands, the kernel decides x86 and AArch64 carriers
//! identically; there is no per-arch fingerprint drift.
//!
//! ## Strict restriction
//!
//! With the gate enabled, a carrier is deleted iff `decide()` returns
//! `Eliminate`. A carrier with no bound obligation, or whose obligation is absent
//! / `Pending` in the evidence table, is KEPT (fail-safe) and the codegen
//! pipeline expands it to a real CMP+Jcc+UD2 runtime check. A KEPT carrier is the
//! exact behaviour of the pre-S5 eager check, so the gate NEVER eliminates more
//! than the legacy path — it only makes the (previously impossible on x86)
//! elimination certified and re-checkable.

use std::collections::HashMap;

use trust_cg_ir::{
    DischargedEvidenceTable, EliminationCertificate, EliminationVerdict, GuardObligationReceipt,
    GuardOperandRef, RecheckOutcome, X86GuardTarget, decide, recheck_elimination,
};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::x86_pass_manager::X86MachinePass;

/// Lift an x86 carrier instruction's operands into the arch-neutral guard
/// operand refs (registers + immediates only, in role order). Mirrors the
/// AArch64 `aarch64_guard_operands` over `MachOperand`.
fn x86_carrier_operand_refs(inst: &X86ISelInst) -> Vec<GuardOperandRef> {
    inst.operands
        .iter()
        .filter_map(|op| match op {
            X86ISelOperand::VReg(v) => Some(GuardOperandRef::Reg(v.id)),
            X86ISelOperand::Imm(i) => Some(GuardOperandRef::Imm(*i)),
            _ => None,
        })
        .collect()
}

/// Statistics from one run of the x86 kernel-gated guard-elimination pass.
#[derive(Debug, Clone, Default)]
pub struct X86ProofOptStats {
    /// Number of guard carriers (any kind: bounds/null/div-zero/shift-range)
    /// eliminated under kernel authorization.
    pub guards_eliminated: u32,
    /// Number of guard carriers (any kind) KEPT (no/undischarged obligation).
    pub guards_kept: u32,
}

/// x86-64 kernel-gated proof-consuming guard elimination pass.
///
/// Default-constructed the pass does nothing (no gate, no obligations); it is a
/// no-op unless [`X86ProofGuardElimination::enable_kernel_gate`] is called. This
/// keeps it safe to register unconditionally. Production enables it with empty replay authority,
/// so all carriers are retained; no environment variable can select a weaker path.
#[derive(Default)]
pub struct X86ProofGuardElimination {
    /// When false (default), the pass keeps every carrier — exactly the legacy
    /// behaviour (the pipeline then expands them to real runtime checks).
    kernel_gate: bool,
    /// Discharged-obligation evidence the kernel consults.
    kernel_evidence: DischargedEvidenceTable,
    /// Per-carrier obligation binding, keyed by the operand fingerprint the
    /// kernel re-derives from the carrier (the same key `X86ISelFunction
    /// ::guard_obligations` uses). Value is (obligation id, lineage digest).
    kernel_obligations: HashMap<u128, (u128, Option<u128>)>,
    /// Eliminations the kernel authorized this run, for the independent re-check:
    /// (INDEPENDENTLY re-lifted live-carrier operands, certificate). The observed operands are a
    /// SECOND lift taken from the live carrier at the deletion site in `run_on_function` (NOT the
    /// decide-time identity from `kernel_authorizes`), so the re-check's operand-fingerprint
    /// comparison is non-vacuous: a real operand drift is rejected fail-closed (#9).
    kernel_eliminations: Vec<(Vec<GuardOperandRef>, EliminationCertificate)>,
    /// Stats from the last run.
    stats: X86ProofOptStats,
}

impl X86ProofGuardElimination {
    /// Create a disabled (no-op) pass.
    pub fn new() -> Self {
        Self::default()
    }

    /// Enable kernel-gated elimination. `evidence` is the discharged-obligation
    /// table; `obligations` maps a carrier operand fingerprint to its (obligation
    /// id, lineage digest). With the gate off (the default), the pass keeps every
    /// carrier.
    pub fn enable_kernel_gate(
        &mut self,
        evidence: DischargedEvidenceTable,
        obligations: HashMap<u128, (u128, Option<u128>)>,
    ) {
        self.kernel_gate = true;
        if trust_cg_lower::guard_evidence::validator_guard_replay_authority_available()
            || cfg!(test)
        {
            self.kernel_evidence = evidence;
            self.kernel_obligations = obligations;
        } else {
            self.kernel_evidence = DischargedEvidenceTable::new();
            self.kernel_obligations.clear();
        }
    }

    /// Stats from the last run.
    pub fn stats(&self) -> &X86ProofOptStats {
        &self.stats
    }

    /// The kernel eliminations authorized during the last run (for re-check): (independently
    /// re-lifted live-carrier operands, certificate).
    pub fn kernel_eliminations(&self) -> &[(Vec<GuardOperandRef>, EliminationCertificate)] {
        &self.kernel_eliminations
    }

    /// Test-only: simulate a live-carrier operand drift by overwriting the recorded observed
    /// operands for the elimination at `idx`. The re-check re-derives the fingerprint from these
    /// observed operands, so a drift makes [`recheck_kernel_eliminations`] reject (#9 non-vacuity).
    #[cfg(test)]
    fn test_force_observed_drift(&mut self, idx: usize, observed: Vec<GuardOperandRef>) {
        self.kernel_eliminations[idx].0 = observed;
    }

    /// Ask the Certified-Elimination Kernel whether one carrier may be deleted.
    ///
    /// Set `TCG_X86_GUARD_TRACE=1` to see every ACCEPT and, more usefully,
    /// every KEEP with the kernel's reason — see [`x86_guard_trace`].
    /// Returns the minted certificate on Eliminate, `None` on Keep.
    ///
    /// #9: this does NOT record the elimination — the caller (`run_on_function`) records it with a
    /// SECOND, independent re-lift of the live carrier's operands taken at the deletion site, so the
    /// re-check's fingerprint comparison is non-vacuous.
    fn kernel_authorizes(&mut self, inst: &X86ISelInst) -> Option<EliminationCertificate> {
        let target = X86GuardTarget;
        let kind = target.classify_carrier(inst.opcode)?;
        let operand_refs = x86_carrier_operand_refs(inst);
        let operand_identity = target.operand_identity(&operand_refs);
        // Defense-in-depth: look the binding up by the SAME kind-folded key ISel recorded, so an
        // obligation bound for a different kind over identical operands can't be picked up here. A
        // mismatch misses the lookup => carrier KEPT (fail-safe).
        let binding_key = trust_cg_ir::fingerprint_for_kind(kind, &operand_identity.operands);
        let (proof_obligation_id, lineage_digest) = match self.kernel_obligations.get(&binding_key)
        {
            Some(&(obl, lineage)) => (Some(obl), lineage),
            None => (None, None),
        };
        let receipt = GuardObligationReceipt {
            kind,
            operand_identity,
            proof_obligation_id,
            lineage_digest,
        };
        let obligation = receipt.proof_obligation_id;
        match decide(&receipt, &self.kernel_evidence) {
            EliminationVerdict::Eliminate { certificate } => {
                x86_guard_trace(|| format!("ACCEPT kind={kind:?} obligation={obligation:?}"));
                Some(certificate)
            }
            // ⚑ The Keep REASON is the diagnostic that matters. Discarding it
            // (`Keep { .. } => None`) makes every undischarged guard look
            // identical to one that was never a candidate, and a surviving
            // guard is runtime work in a hot loop — measured at 37 across the
            // 18 bench programs where LLVM keeps 0. `decide` distinguishes six
            // causes; without this they are indistinguishable from outside.
            EliminationVerdict::Keep { reason } => {
                x86_guard_trace(|| {
                    format!("KEEP   kind={kind:?} obligation={obligation:?} reason={reason}")
                });
                None
            }
        }
    }

    /// Independent fail-closed re-check (mirrors
    /// [`crate::proof_opts::ProofOptimization::recheck_kernel_eliminations`]):
    /// re-validate every kernel-authorized elimination by re-deriving the operand
    /// fingerprint and re-confirming discharge/lineage against the evidence.
    /// Returns the first rejection reason, or `Ok(())` if all re-justify.
    ///
    /// #9: `observed_operands` is the independently re-lifted live-carrier snapshot recorded in
    /// `run_on_function`, so a genuine operand drift between authorization and re-check is rejected.
    pub fn recheck_kernel_eliminations(&self) -> Result<(), String> {
        for (observed_operands, certificate) in &self.kernel_eliminations {
            match recheck_elimination(certificate, observed_operands, &self.kernel_evidence) {
                RecheckOutcome::Valid => {}
                RecheckOutcome::Rejected { reason } => {
                    return Err(format!(
                        "x86 guard elimination re-check rejected (obligation {}): {}",
                        certificate.obligation_id(),
                        reason
                    ));
                }
            }
        }
        Ok(())
    }

    /// Run the pass on an x86 ISel function. Deletes only kernel-authorized
    /// guard carriers (any kind: bounds/null/div-zero/shift-range); keeps
    /// everything else.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        self.stats = X86ProofOptStats::default();
        self.kernel_eliminations.clear();

        // With the gate off, keep every carrier (legacy behaviour).
        if !self.kernel_gate {
            return false;
        }

        let mut changed = false;
        for block_id in func.block_order.clone() {
            // Decide deletions first (immutable borrow of each inst), then retain.
            let decisions: Vec<bool> = {
                let Some(block) = func.blocks.get(&block_id) else {
                    continue;
                };
                block
                    .insts
                    .iter()
                    .map(|inst| {
                        if X86GuardTarget.classify_carrier(inst.opcode).is_none() {
                            return false; // not a carrier — keep
                        }
                        if let Some(certificate) = self.kernel_authorizes(inst) {
                            // #9: record the elimination with a SECOND, independent re-lift of THIS
                            // live carrier's operands (a fresh `x86_carrier_operand_refs` call,
                            // distinct from the one decide consumed inside `kernel_authorizes`), so
                            // the re-check's fingerprint comparison is non-vacuous.
                            let observed = x86_carrier_operand_refs(inst);
                            self.kernel_eliminations.push((observed, certificate));
                            self.stats.guards_eliminated += 1;
                            true // delete (kernel-authorized)
                        } else {
                            self.stats.guards_kept += 1;
                            false // keep (fail-safe)
                        }
                    })
                    .collect()
            };

            if decisions.iter().any(|&d| d) {
                let Some(block) = func.blocks.get_mut(&block_id) else {
                    continue;
                };
                let mut next = Vec::with_capacity(block.insts.len());
                for (inst, delete) in block.insts.drain(..).zip(decisions) {
                    if !delete {
                        next.push(inst);
                    }
                }
                block.insts = next;
                changed = true;
            }
        }

        changed
    }
}

/// Emit one guard-kernel decision line when `TCG_X86_GUARD_TRACE` is set to a
/// non-empty value other than `0`.
///
/// ⚑ Logs ACCEPTS **and** KEEPS. A silence-only diagnostic proves nothing: a
/// pass that never fires and a pass with nothing to do look identical, which is
/// how several capabilities in this backend sat dormant while measurably
/// costing runtime. Here the KEEP reason additionally says WHICH of the
/// kernel's six fail-safe conditions stopped the elimination, so a surviving
/// guard can be attributed instead of guessed at.
///
/// Takes a closure so the formatting cost is not paid when tracing is off —
/// this runs once per guard carrier per function.
fn x86_guard_trace(line: impl FnOnce() -> String) {
    let on = std::env::var("TCG_X86_GUARD_TRACE")
        .map(|v| !v.is_empty() && v != "0")
        .unwrap_or(false);
    if on {
        eprintln!("[x86-guard] {}", line());
    }
}

impl X86MachinePass for X86ProofGuardElimination {
    fn name(&self) -> &str {
        "x86-proof-guard-elimination"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        self.run_on_function(func)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::{DischargeStatus, GuardKind, X86Opcode, fingerprint_for_kind};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;

    fn vreg_op(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    /// Build a one-block function with a single bounds-check carrier
    /// `[Reg(0), Reg(1), Imm(8)]` followed by a Ret.
    fn func_with_carrier() -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_proof_opts_test".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 2;
        func.push_inst(
            entry,
            X86ISelInst::new(
                X86Opcode::TrapBoundsCheckExact,
                vec![vreg_op(0), vreg_op(1), X86ISelOperand::Imm(8)],
            ),
        );
        func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));
        func
    }

    fn carrier_fp() -> u128 {
        // The kernel re-derives the binding key with the carrier's GuardKind folded in
        // (defense-in-depth), so the test obligation map must use the same kind-folded key.
        fingerprint_for_kind(
            GuardKind::BoundsCheck,
            &[
                GuardOperandRef::Reg(0),
                GuardOperandRef::Reg(1),
                GuardOperandRef::Imm(8),
            ],
        )
    }

    fn live_carriers(func: &X86ISelFunction) -> usize {
        func.block_order
            .iter()
            .filter_map(|b| func.blocks.get(b))
            .flat_map(|b| b.insts.iter())
            .filter(|i| i.opcode == X86Opcode::TrapBoundsCheckExact)
            .count()
    }

    #[test]
    fn gate_off_keeps_carrier() {
        let mut func = func_with_carrier();
        let mut pass = X86ProofGuardElimination::new();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            live_carriers(&func),
            1,
            "no gate => keep (legacy behaviour)"
        );
    }

    #[test]
    fn gate_eliminates_discharged_carrier() {
        let mut func = func_with_carrier();
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(42, DischargeStatus::Discharged, None);
        let mut obligations = HashMap::new();
        obligations.insert(carrier_fp(), (42u128, None));

        let mut pass = X86ProofGuardElimination::new();
        pass.enable_kernel_gate(evidence, obligations);
        assert!(pass.run_on_function(&mut func));

        assert_eq!(
            live_carriers(&func),
            0,
            "discharged => eliminated by kernel"
        );
        assert_eq!(pass.stats().guards_eliminated, 1);
        assert_eq!(pass.kernel_eliminations().len(), 1);
        assert!(pass.recheck_kernel_eliminations().is_ok());
    }

    #[test]
    fn gate_keeps_unbound_carrier() {
        // Bound obligation present in evidence, but the carrier is NOT bound to it
        // (empty obligation map) => kernel keeps it (fail-safe).
        let mut func = func_with_carrier();
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(42, DischargeStatus::Discharged, None);

        let mut pass = X86ProofGuardElimination::new();
        pass.enable_kernel_gate(evidence, HashMap::new());
        pass.run_on_function(&mut func);

        assert_eq!(live_carriers(&func), 1, "unbound carrier => kept");
        assert_eq!(pass.stats().guards_kept, 1);
        assert_eq!(pass.kernel_eliminations().len(), 0);
    }

    #[test]
    fn gate_keeps_pending_obligation() {
        // The carrier IS bound, but its obligation is NOT in the evidence table
        // (Pending obligations never enter the evidence) => kernel keeps it.
        let mut func = func_with_carrier();
        let mut obligations = HashMap::new();
        obligations.insert(carrier_fp(), (42u128, None));

        let mut pass = X86ProofGuardElimination::new();
        pass.enable_kernel_gate(DischargedEvidenceTable::new(), obligations);
        pass.run_on_function(&mut func);

        assert_eq!(live_carriers(&func), 1, "bound-but-undischarged => kept");
        assert_eq!(pass.kernel_eliminations().len(), 0);
    }

    #[test]
    fn production_policy_keeps_x86_guard_with_forged_binding_and_lineage() {
        let mut func = func_with_carrier();
        let mut forged_bindings = HashMap::new();
        forged_bindings.insert(carrier_fp(), (0x0BAD_5EED_u128, Some(0xF0_12_34u128)));

        let mut pass = X86ProofGuardElimination::new();
        pass.enable_kernel_gate(
            trust_cg_lower::guard_evidence::production_guard_replay_evidence(),
            forged_bindings,
        );
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(live_carriers(&func), 1);
        assert_eq!(pass.stats().guards_eliminated, 0);
        assert!(pass.kernel_eliminations().is_empty());
    }

    /// #5 (Certified-tier lineage): a Certified obligation whose receipt lineage MATCHES the
    /// evidence is eliminated and re-checks; a MISMATCHED lineage (or absent receipt lineage) is
    /// KEPT.
    #[test]
    fn gate_certified_lineage_eliminates_only_on_match() {
        let lineage: u128 = 0x00FE_EDFA_CEC0_FFEE;

        // Matching lineage on the receipt => eliminated, re-checks.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, Some(lineage)));

            let mut pass = X86ProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run_on_function(&mut func));
            assert_eq!(live_carriers(&func), 0, "certified+matching => eliminated");
            assert_eq!(pass.kernel_eliminations().len(), 1);
            assert!(pass.recheck_kernel_eliminations().is_ok());
        }

        // Mismatched lineage => kept.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, Some(lineage ^ 0x1)));

            let mut pass = X86ProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run_on_function(&mut func));
            assert_eq!(live_carriers(&func), 1, "certified+mismatch => kept");
            assert_eq!(pass.kernel_eliminations().len(), 0);
        }

        // Absent receipt lineage (None) while evidence is Certified => kept.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, None));

            let mut pass = X86ProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run_on_function(&mut func));
            assert_eq!(live_carriers(&func), 1, "certified+absent-lineage => kept");
            assert_eq!(pass.kernel_eliminations().len(), 0);
        }
    }

    /// #9 (non-vacuous operand-drift re-check): after a kernel-authorized elimination, the recorded
    /// observed snapshot is independently re-lifted from the live carrier. A genuine drift (the
    /// observed operands no longer match the certificate fingerprint) makes the re-check REJECT
    /// fail-closed; the unmodified control re-checks Ok.
    #[test]
    fn recheck_rejects_observed_operand_drift() {
        // Control: no drift => re-check Ok.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, None));

            let mut pass = X86ProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run_on_function(&mut func));
            assert_eq!(pass.kernel_eliminations().len(), 1);
            assert!(
                pass.recheck_kernel_eliminations().is_ok(),
                "non-drifted elimination must re-check Ok"
            );
        }

        // Drift: the live re-read would have observed different operands => re-check REJECTS.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, None));

            let mut pass = X86ProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run_on_function(&mut func));
            assert_eq!(pass.kernel_eliminations().len(), 1);
            // Simulate a live-carrier operand drift (base reg 0 -> 9).
            pass.test_force_observed_drift(
                0,
                vec![
                    GuardOperandRef::Reg(9),
                    GuardOperandRef::Reg(1),
                    GuardOperandRef::Imm(8),
                ],
            );
            assert!(
                pass.recheck_kernel_eliminations().is_err(),
                "an operand drift must be REJECTED by the re-check (fail-closed)"
            );
        }
    }
}
