// trust-cg-codegen/guard_ledger.rs — AArch64 guard-elimination ledger observation (Sentinel S1)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Sentinel S1 — observe AArch64 guard elimination against the arch-neutral kernel.
//!
//! This wires the S0 [`GuardSiteLedger`] / [`decide`] kernel (in `trust-cg-ir`) into the live
//! AArch64 compile path **in shadow mode, with zero behavior change**:
//!
//! 1. [`observe_carrier_births`] snapshots every proof-only guard carrier
//!    (`TrapBoundsCheckExact`, `TrapNullIfZero`) in the function *before* the optimization pass,
//!    recording each into a per-function [`GuardSiteLedger`] (born trapping). The carrier's live
//!    operands are captured into a reproducible [`GuardOperandIdentity`].
//! 2. [`finalize_and_observe`] runs *after* optimization: each carrier that the existing pass
//!    deleted is marked eliminated, each survivor (which will be expanded to a real trap) is
//!    marked trapped, and guard-count conservation is checked. It also runs the shadow kernel
//!    [`decide`] over each site and (optionally) logs the verdict.
//!
//! In S1 the kernel sees an empty [`DischargedEvidenceTable`], so it returns `Keep` for every
//! site — the legacy pass still makes the actual deletion decisions. The divergence between
//! "legacy pass eliminated this" and "kernel would Keep (no evidence yet)" is the intended audit
//! signal until S3 threads real obligation evidence and S4 turns the kernel into the gate.
//!
//! All output is gated behind the `TRUST_CG_GUARD_SHADOW` environment variable; by default this
//! module is silent and never fails the compile (the conservation gate turns on in S4).

use std::collections::HashSet;

use trust_cg_ir::types::InstId;
use trust_cg_ir::{
    AArch64GuardTarget, DischargedEvidenceTable, GuardObligationReceipt, GuardSiteLedger,
    GuardTarget, MachFunction, decide,
};

/// A per-function carrier-birth snapshot, awaiting reconciliation after optimization.
pub struct GuardObservation {
    ledger: GuardSiteLedger,
    /// (carrier inst id, ledger site id) pairs recorded at birth.
    sites: Vec<(InstId, u64)>,
}

/// Collect the set of carrier instruction ids currently referenced by the function's blocks,
/// using the shared per-backend [`GuardTarget`] descriptor for classification.
fn live_carrier_ids(func: &MachFunction) -> HashSet<InstId> {
    let target = AArch64GuardTarget;
    let mut set = HashSet::new();
    for block in &func.blocks {
        for &inst_id in &block.insts {
            if target.classify_carrier(func.inst(inst_id)).is_some() {
                set.insert(inst_id);
            }
        }
    }
    set
}

/// Snapshot all guard carriers present *before* optimization into a fresh ledger, classifying and
/// lifting operands via the shared [`AArch64GuardTarget`] descriptor.
pub fn observe_carrier_births(func: &MachFunction) -> GuardObservation {
    let target = AArch64GuardTarget;
    let mut ledger = GuardSiteLedger::new(func.name.clone());
    let mut sites = Vec::new();
    for block in &func.blocks {
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if let Some(kind) = target.classify_carrier(inst) {
                let identity = target.operand_identity(inst);
                let site_id = ledger.record_carrier_birth(kind, identity, None);
                sites.push((inst_id, site_id));
            }
        }
    }
    GuardObservation { ledger, sites }
}

/// True iff shadow logging is enabled via `TRUST_CG_GUARD_SHADOW` (non-empty, not "0").
fn shadow_logging_enabled() -> bool {
    std::env::var("TRUST_CG_GUARD_SHADOW")
        .map(|v| !v.is_empty() && v != "0")
        .unwrap_or(false)
}

/// Reconcile the birth snapshot against the post-optimization function: mark each carrier as
/// eliminated (deleted by the pass) or trapped (survives → expanded to a real trap). Pure and
/// testable; returns the reconciled ledger.
pub fn reconcile(observation: GuardObservation, func_after_opt: &MachFunction) -> GuardSiteLedger {
    let GuardObservation { mut ledger, sites } = observation;
    let surviving = live_carrier_ids(func_after_opt);

    for (inst_id, site_id) in &sites {
        if surviving.contains(inst_id) {
            // Survivor: expansion will lower it to a real runtime trap.
            ledger.mark_trapped(*site_id);
        } else {
            // The existing pass deleted it. S1 has no kernel certificate yet (cert id = 0);
            // S2 replaces this with the kernel-minted certificate id.
            ledger.mark_eliminated(*site_id, 0);
        }
    }
    ledger
}

/// Reconcile the snapshot, run the shadow kernel, and check conservation. Never fails the compile
/// in S1 (shadow only); all output is gated behind `TRUST_CG_GUARD_SHADOW`.
pub fn finalize_and_observe(observation: GuardObservation, func_after_opt: &MachFunction) {
    let ledger = reconcile(observation, func_after_opt);

    if !shadow_logging_enabled() {
        return;
    }

    // Shadow kernel: what would the (evidence-free) kernel decide for each site? In S1 this is
    // always Keep — the audit signal that evidence threading (S3) is still pending.
    let evidence = DischargedEvidenceTable::new();
    for site in ledger.sites() {
        let receipt = GuardObligationReceipt::unbound(site.kind, site.operand_identity.clone());
        let verdict = decide(&receipt, &evidence);
        eprintln!(
            "[guard-shadow] fn={} site={} kind={:?} kernel_verdict={:?}",
            ledger.function(),
            site.site_id,
            site.kind,
            verdict
        );
    }

    match ledger.verify_conservation() {
        Ok(report) => eprintln!(
            "[guard-conservation] fn={} emitted={} trapped={} eliminated={} OK",
            ledger.function(),
            report.emitted,
            report.trapped,
            report.eliminated
        ),
        Err(violation) => eprintln!(
            "[guard-conservation] VIOLATION fn={} detail={}",
            violation.function, violation.detail
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{
        AArch64Opcode, GuardKind, MachFunction, MachInst, MachOperand, RegClass, Signature, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    /// A function with a single bounds-check carrier in the entry block.
    fn func_with_one_bounds_carrier() -> (MachFunction, InstId) {
        let mut f = MachFunction::new("t".to_string(), Signature::new(vec![], vec![]));
        let carrier = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), MachOperand::Imm(64)],
        );
        let id = f.push_inst(carrier);
        f.blocks[0].insts.push(id);
        (f, id)
    }

    #[test]
    fn observe_records_carrier_birth() {
        let (f, _) = func_with_one_bounds_carrier();
        let obs = observe_carrier_births(&f);
        assert_eq!(obs.ledger.len(), 1);
        assert_eq!(obs.sites.len(), 1);
        assert_eq!(obs.ledger.sites()[0].kind, GuardKind::BoundsCheck);
    }

    #[test]
    fn reconcile_marks_survivor_trapped() {
        let (f, _) = func_with_one_bounds_carrier();
        let obs = observe_carrier_births(&f);
        // Carrier still present after "optimization" => survivor => trapped.
        let ledger = reconcile(obs, &f);
        let report = ledger.verify_conservation().expect("conserved");
        assert_eq!(
            (report.emitted, report.trapped, report.eliminated),
            (1, 1, 0)
        );
    }

    #[test]
    fn reconcile_marks_deleted_eliminated() {
        let (f, _) = func_with_one_bounds_carrier();
        let obs = observe_carrier_births(&f);
        // Simulate the pass deleting the carrier: drop it from the block's inst list.
        let mut f_after = f.clone();
        f_after.blocks[0].insts.clear();
        let ledger = reconcile(obs, &f_after);
        let report = ledger.verify_conservation().expect("conserved");
        assert_eq!(
            (report.emitted, report.trapped, report.eliminated),
            (1, 0, 1)
        );
    }
}
