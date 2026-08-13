// trust-cg-opt - Declarative rewrite as a MachinePass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`DeclarativeRewritePass`] wraps a [`RewriteEngine`] behind the
//! [`MachinePass`] trait so it can be plugged into the existing
//! [`PassManager`](crate::pass_manager::PassManager) pipeline.
//!
//! The wrapper runs the engine's internal fixed-point loop once per
//! invocation and returns whether anything changed. The outer
//! PassManager's fixed-point loop still iterates with other passes.
//!
//! The wrapped engine may be either *owned* (the historical case, used when
//! the pass needs a private, mutable engine — e.g. to register additional
//! admitted rewrite rules) or *shared* via an [`Arc`]. The shared case lets
//! the pipeline build the (constant) migrated-peephole rule set once and reuse
//! it across every function/pipeline construction, avoiding a full engine
//! rebuild each time. Sharing is observationally identical: the engine is only
//! ever consulted immutably at run time (`run_to_fixpoint(&self, ...)`), so a
//! shared engine produces exactly the same rewrites as a freshly built one
//! carrying the same rules.

use std::sync::Arc;

use trust_cg_ir::{MachFunction, PassId, ProvenanceMap};

use crate::pass_manager::{AnalysisCache, MachinePass};
use crate::rewrite::engine::RewriteEngine;

const DECLARATIVE_REWRITE_PASS_NAME: &str = "declarative-rewrite";

fn declarative_rewrite_pass_id() -> PassId {
    PassId::new(DECLARATIVE_REWRITE_PASS_NAME)
}

/// Holds the engine either by value (mutable, private) or behind a shared
/// [`Arc`] (read-only, reusable). Both variants expose the engine immutably
/// for `run`; only the owned variant permits in-place rule mutation.
enum EngineRef {
    /// A private engine owned by this pass; mutable via [`engine_mut`].
    Owned(RewriteEngine),
    /// A shared, read-only engine reused across passes/pipelines.
    Shared(Arc<RewriteEngine>),
}

impl EngineRef {
    #[inline]
    fn get(&self) -> &RewriteEngine {
        match self {
            EngineRef::Owned(engine) => engine,
            EngineRef::Shared(engine) => engine,
        }
    }
}

/// A [`MachinePass`] that runs a [`RewriteEngine`] to local fixed point.
pub struct DeclarativeRewritePass {
    engine: EngineRef,
    name: &'static str,
    max_inner_iterations: u32,
}

impl DeclarativeRewritePass {
    /// Create a new pass with the given (owned) engine, pass name, and inner
    /// fixed-point iteration cap.
    pub fn new(name: &'static str, engine: RewriteEngine, max_inner_iterations: u32) -> Self {
        Self {
            engine: EngineRef::Owned(engine),
            name,
            max_inner_iterations,
        }
    }

    /// Create a new pass that shares a read-only engine via [`Arc`].
    ///
    /// This is used on the hot pipeline-construction path when the engine
    /// carries only the constant migrated-peephole rule set (no admitted
    /// rewrites), so it can be built once and reused. The pass output is
    /// identical to a pass built with an owned engine carrying the same rules
    /// because the engine is consulted immutably at run time.
    pub fn new_shared(
        name: &'static str,
        engine: Arc<RewriteEngine>,
        max_inner_iterations: u32,
    ) -> Self {
        Self {
            engine: EngineRef::Shared(engine),
            name,
            max_inner_iterations,
        }
    }

    /// Access the underlying engine mutably (e.g., to register more rules).
    ///
    /// Only valid for passes constructed with an owned engine ([`new`]); a
    /// pass built from a shared engine ([`new_shared`]) has no private engine
    /// to mutate and will panic. The pipeline only ever shares engines that
    /// require no further mutation.
    ///
    /// [`new`]: DeclarativeRewritePass::new
    /// [`new_shared`]: DeclarativeRewritePass::new_shared
    pub fn engine_mut(&mut self) -> &mut RewriteEngine {
        match &mut self.engine {
            EngineRef::Owned(engine) => engine,
            EngineRef::Shared(_) => {
                panic!("engine_mut() called on a DeclarativeRewritePass with a shared engine")
            }
        }
    }

    /// Number of rules in the wrapped engine (works for owned and shared).
    pub fn num_rules(&self) -> usize {
        self.engine.get().num_rules()
    }
}

impl MachinePass for DeclarativeRewritePass {
    fn name(&self) -> &str {
        self.name
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let stats = self
            .engine
            .get()
            .run_to_fixpoint(func, self.max_inner_iterations);
        stats.rewrites > 0
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let pass = declarative_rewrite_pass_id();
        let stats = self.engine.get().run_to_fixpoint_with_provenance(
            func,
            self.max_inner_iterations,
            provenance,
            &pass,
        );
        stats.rewrites > 0
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rewrite::patterns::register_migrated;
    use trust_cg_ir::{
        AArch64Opcode, AArch64Target, MachInst, MachOperand, ProvenanceStatus, RegClass, Signature,
        TargetInfo, TransformKind, TrustIrInstId, VReg,
    };

    #[test]
    fn pass_fires_on_migrated_patterns() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let inst = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, RegClass::Gpr64)),
                MachOperand::Imm(0),
            ],
        );
        let id = func.push_inst(inst);
        func.append_inst(entry, id);

        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let mut pass = DeclarativeRewritePass::new("declarative-rewrite", engine, 16);
        assert!(pass.run(&mut func));
        assert_eq!(
            func.inst(func.block(entry).insts[0]).opcode,
            AArch64Target::mov_rr()
        );
    }

    #[test]
    fn pass_idempotent_on_no_match() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let inst = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, RegClass::Gpr64)),
                MachOperand::Imm(42),
            ],
        );
        let id = func.push_inst(inst);
        func.append_inst(entry, id);

        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let mut pass = DeclarativeRewritePass::new("declarative-rewrite", engine, 16);
        assert!(!pass.run(&mut func));
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn pass_with_provenance_records_migrated_rewrite_in_place() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let inst = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(1, RegClass::Gpr64)),
                MachOperand::Imm(0),
            ],
        );
        let id = func.push_inst(inst);
        func.append_inst(entry, id);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(10), &[id], PassId::new("isel"));

        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let mut pass = DeclarativeRewritePass::new("declarative-rewrite", engine, 16);
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        assert_eq!(
            func.inst(func.block(entry).insts[0]).opcode,
            AArch64Target::mov_rr()
        );
        assert_eq!(provenance.get_mach_insts(TrustIrInstId(10)).unwrap(), &[id]);

        let entry = provenance
            .get_entry(id)
            .expect("rewritten instruction should keep provenance");
        assert!(entry.is_active());
        assert!(entry.transforms.iter().any(|record| {
            record.pass == PassId::new("declarative-rewrite")
                && record.kind == TransformKind::Survived
        }));
    }

    #[test]
    fn pass_with_provenance_records_migrated_delete_justification() {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let nop_id = func.push_inst(MachInst::new(AArch64Opcode::Nop, vec![]));
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(entry, nop_id);
        func.append_inst(entry, ret_id);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(20), &[nop_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(21), &[ret_id], PassId::new("isel"));

        let mut engine = RewriteEngine::new();
        register_migrated(&mut engine);
        let mut pass = DeclarativeRewritePass::new("declarative-rewrite", engine, 16);
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        assert_eq!(func.block(entry).insts, vec![ret_id]);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(20)).unwrap(),
            &[nop_id]
        );

        let entry = provenance
            .get_entry(nop_id)
            .expect("deleted instruction should keep provenance");
        match &entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass, &PassId::new("declarative-rewrite"));
                assert!(justification.contains("nop-delete"));
            }
            other => panic!("expected optimized-away provenance, got {other:?}"),
        }
        assert!(provenance.get_entry(ret_id).unwrap().is_active());
    }
}
