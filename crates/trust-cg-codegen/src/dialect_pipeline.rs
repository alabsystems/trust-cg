// trust-cg-codegen/dialect_pipeline.rs - Pre-adapter dialect lowering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: issue #433, trust_ir #428. Wires trust_ir's dialect framework into
// the Trust Codegen compilation pipeline so that upstream dialects (currently the
// opt-in `verif.*` contract surface used by ty) are rewritten out of
// `Inst::DialectOp` before the trust_ir->LIR adapter runs.

//! Pre-adapter dialect lowering.
//!
//! Runs `trust_ir::dialect::lower_module` against a [`DialectRegistry`] with at
//! least one dialect registered (per Trust Codegen issue #433 / trust_ir #428). The goal
//! is to catch unknown `DialectOp` instances at a known location *before*
//! they reach [`trust_cg_lower::translate_module`] — the adapter has no
//! `DialectOp` handler and would otherwise emit a translation error deep in
//! the ISel stack.
//!
//! The registry currently ships with trust_ir's opt-in `VerifDialect`, trust_ir's
//! portable `vector.*` dialect, and Trust Codegen-local typed dialects that the
//! adapter understands directly. Additional dialects can be registered here
//! without touching the rest of the pipeline. See `default_registry()` for
//! the hook.

use std::borrow::Cow;

use thiserror::Error;

/// Error from pre-adapter dialect lowering.
#[derive(Debug, Error)]
pub enum DialectPipelineError {
    /// trust_ir dialect framework reported a lowering failure (fixpoint not
    /// reached, pass returned an error, or an op references an unknown
    /// dialect).
    #[error("trust_ir dialect lowering failed: {0}")]
    Lowering(String),
}

/// Maximum number of lowering fixpoint iterations.
///
/// trust_ir's `lower_module` iterates passes until no rewrites fire, or this
/// limit is hit. Empirically the `verif` example converges in at most 3
/// iterations; 16 is a conservative ceiling that still cuts off runaway
/// rewriters.
pub const MAX_LOWERING_ITERS: usize = 16;

/// Build the default [`trust_ir::dialect::DialectRegistry`] used by the
/// Trust Codegen compile path.
///
/// Includes trust_ir's opt-in `VerifDialect` so that modules
/// emitting `verif.bfs_step` / `verif.frontier_drain` /
/// `verif.fingerprint_batch` round-trip through the pipeline, and trust_ir's
/// portable `vector.*` dialect so Trust Codegen can lower those ops in the adapter.
pub fn default_registry() -> trust_ir::dialect::DialectRegistry {
    let mut reg = trust_ir::dialect::DialectRegistry::new();
    // Feature-gated on trust_ir's `dialect-verif-example`; enabled in
    // `[workspace.dependencies]` via `features = ["dialect-verif-example"]`.
    reg.register(Box::new(trust_ir::dialect::examples::verif::VerifDialect));
    // Portable vector ops are intentionally left as DialectOp nodes here:
    // trust-cg-lower handles supported shapes directly in the trust_ir adapter.
    // We register a THIN wrapper over trust_ir's `vector` dialect that also
    // admits the 64-bit (D-register) `<8 x i8>` `pack_lanes` splat (see
    // `LenientVectorDialect`); the adapter lowers it to a genuine `dup.8b`.
    reg.register(Box::new(LenientVectorDialect));
    // Trust Codegen-local typed surface for ops the pinned core trust_ir crate does not
    // have yet: bitfields and compact vector mask extraction.
    reg.register(Box::new(trust_cg_lower::bitfield_dialect::BitfieldDialect));
    reg
}

/// Trust Codegen-local wrapper over trust_ir's `vector` dialect.
///
/// It behaves exactly like [`trust_ir::dialect::vector::VectorDialect`] except
/// that its `validate` ADDITIONALLY admits the 64-bit (D-register) `<8 x i8>`
/// `vector.pack_lanes` splat — hashbrown's `uint8x8_t` control-byte broadcast.
/// The backend's pinned trust_ir may still gate `VectorDialect::validate` to
/// 128-bit lane vectors only; this shim accepts the `<8 x i8>` shape here (the
/// trust_ir->LIR adapter reads the DialectInst's raw operands + result type and
/// lowers it to a real `dup.8b`), and delegates every other vector op to the
/// real dialect gate. Keeps trust-cg robust regardless of which trust_ir it
/// links against — no format-crate change or path override required.
///
/// Like `VectorDialect`, it contributes no lowering passes (`lowerings()`
/// defaults to empty): supported vector ops stay `DialectOp` nodes for the
/// adapter.
#[derive(Debug, Clone, Copy, Default)]
struct LenientVectorDialect;

impl trust_ir::dialect::Dialect for LenientVectorDialect {
    fn name(&self) -> &'static str {
        trust_ir::dialect::vector::VectorDialect.name()
    }

    fn version(&self) -> u32 {
        trust_ir::dialect::vector::VectorDialect.version()
    }

    fn ops(&self) -> &'static [&'static str] {
        trust_ir::dialect::vector::VectorDialect.ops()
    }

    fn validate(
        &self,
        inst: &trust_ir::dialect::DialectInst,
    ) -> Result<(), trust_ir::dialect::DialectError> {
        inst.validate_names()?;
        // Admit the V64 `<8 x i8>` pack_lanes splat that the adapter lowers to
        // `dup.8b`; some pinned trust_ir gates `VectorDialect::validate` to
        // 128-bit lane vectors and would reject it here.
        if trust_ir::dialect::vector::is_pack_lanes_op(inst)
            && let Some(trust_ir::ty::Ty::Vector(elem, 8)) = inst.result_tys.first()
            && elem.as_ref() == &trust_ir::ty::Ty::I8
        {
            return Ok(());
        }
        trust_ir::dialect::vector::VectorDialect.validate(inst)
    }
}

/// Return true if `module` contains at least one dialect op.
pub fn has_dialect_ops(module: &trust_ir::Module) -> bool {
    module
        .instructions()
        .any(|node| matches!(&node.inst, trust_ir::Inst::DialectOp(_)))
}

/// Run pre-adapter dialect lowering on `module` only when needed.
///
/// The common cold-start path from tRust/tSwift/tC emits core trust_ir with no
/// dialect ops. Borrowing that module avoids an unconditional full-module clone
/// and registry fixpoint walk before the adapter.
pub fn lower_dialects_if_needed(
    module: &trust_ir::Module,
) -> Result<(Cow<'_, trust_ir::Module>, usize), DialectPipelineError> {
    if !has_dialect_ops(module) {
        return Ok((Cow::Borrowed(module), 0));
    }

    let mut lowered = module.clone();
    let rewrites = lower_dialects(&mut lowered)?;
    Ok((Cow::Owned(lowered), rewrites))
}

/// Run pre-adapter dialect lowering on `module`.
///
/// Uses [`default_registry`] to progressively rewrite any
/// `Inst::DialectOp` in the module. Callers that do not already own a mutable
/// module should prefer [`lower_dialects_if_needed`] to avoid cloning modules
/// that have no dialect ops.
///
/// Returns the number of rewrites applied, for tracing / diagnostics.
pub fn lower_dialects(module: &mut trust_ir::Module) -> Result<usize, DialectPipelineError> {
    let registry = default_registry();
    // Validate that every DialectOp in the module references a registered
    // dialect. Unknown dialects are the hard error trust_ir#428 §"Dialect
    // framework" calls out — this surfaces it at a known pipeline stage
    // rather than letting the adapter skip over an unrecognized op.
    registry
        .validate_module(module)
        .map_err(|e| DialectPipelineError::Lowering(format!("{e}")))?;
    let result = registry
        .lower(module, MAX_LOWERING_ITERS)
        .map_err(|e| DialectPipelineError::Lowering(format!("{e}")))?;
    Ok(result.rewrites_applied)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Cow;
    use trust_ir::dialect::{DialectInst, examples::verif};
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::Ty;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Function, Module};

    fn mk_func_with_body(body: Vec<InstrNode>) -> Function {
        let mut func = Function::new(FuncId::new(0), "test", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body = body;
        func.blocks.push(block);
        func
    }

    /// Empty module lowers cleanly with zero rewrites.
    #[test]
    fn empty_module_is_noop() {
        let mut module = Module::new("empty");
        let n = lower_dialects(&mut module).expect("empty lower");
        assert_eq!(n, 0);
    }

    #[test]
    fn lower_dialects_if_needed_borrows_core_trust_ir() {
        let module = Module::new("empty");
        let (lowered, rewrites) =
            lower_dialects_if_needed(&module).expect("empty module should be borrowed");

        assert_eq!(rewrites, 0);
        assert!(matches!(lowered, Cow::Borrowed(_)));
    }

    #[test]
    fn lower_dialects_if_needed_owns_dialect_module() {
        let v4_i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let func = mk_func_with_body(vec![
            InstrNode::new(Inst::DialectOp(Box::new(
                trust_ir::dialect::vector::pack_lanes(
                    v4_i32,
                    [
                        ValueId::new(0),
                        ValueId::new(1),
                        ValueId::new(2),
                        ValueId::new(3),
                    ],
                ),
            )))
            .with_result(ValueId::new(4)),
        ]);
        let mut module = Module::new("vector_registered");
        module.functions.push(func);

        let (lowered, rewrites) =
            lower_dialects_if_needed(&module).expect("vector dialect validates");

        assert_eq!(rewrites, 0);
        assert!(matches!(lowered, Cow::Owned(_)));
    }

    #[test]
    fn vector_dialect_is_registered_for_adapter_lowering() {
        let v4_i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let func = mk_func_with_body(vec![
            InstrNode::new(Inst::DialectOp(Box::new(
                trust_ir::dialect::vector::pack_lanes(
                    v4_i32,
                    [
                        ValueId::new(0),
                        ValueId::new(1),
                        ValueId::new(2),
                        ValueId::new(3),
                    ],
                ),
            )))
            .with_result(ValueId::new(4)),
        ]);
        let mut module = Module::new("vector_registered");
        module.functions.push(func);

        let n = lower_dialects(&mut module).expect("vector dialect validates");

        assert_eq!(n, 0);
        assert!(matches!(
            &module.functions[0].blocks[0].body[0].inst,
            Inst::DialectOp(op) if trust_ir::dialect::vector::is_pack_lanes_op(op)
        ));
    }

    /// The lenient vector wrapper admits the 64-bit `<8 x i8>` `pack_lanes`
    /// splat (hashbrown's `simd_splat`): it validates cleanly and stays a
    /// `DialectOp` for the trust_ir->LIR adapter to lower to `dup.8b`.
    #[test]
    fn v8i8_pack_lanes_splat_validates_and_survives() {
        let v8_i8 = Ty::Vector(Box::new(Ty::I8), 8);
        let func = mk_func_with_body(vec![
            InstrNode::new(Inst::DialectOp(Box::new(
                trust_ir::dialect::vector::pack_lanes(v8_i8, [ValueId::new(0); 8]),
            )))
            .with_result(ValueId::new(1)),
        ]);
        let mut module = Module::new("v8i8_splat");
        module.functions.push(func);

        let n = lower_dialects(&mut module).expect("v8i8 pack_lanes validates via lenient wrapper");
        assert_eq!(n, 0, "vector pack_lanes stays a DialectOp for the adapter");
        assert!(matches!(
            &module.functions[0].blocks[0].body[0].inst,
            Inst::DialectOp(op) if trust_ir::dialect::vector::is_pack_lanes_op(op)
        ));
    }

    /// A malformed vector op (a non-64-bit odd shape) is still rejected by the
    /// lenient wrapper — it only special-cases the `<8 x i8>` splat and
    /// delegates everything else to the real dialect gate.
    #[test]
    fn lenient_wrapper_still_rejects_unsupported_vector_shape() {
        // `<3 x i8>` is not a lowered shape — the real gate rejects it, and the
        // wrapper must NOT swallow that error.
        let bad = Ty::Vector(Box::new(Ty::I8), 3);
        let func = mk_func_with_body(vec![
            InstrNode::new(Inst::DialectOp(Box::new(
                trust_ir::dialect::vector::pack_lanes(
                    bad,
                    [ValueId::new(0), ValueId::new(1), ValueId::new(2)],
                ),
            )))
            .with_result(ValueId::new(3)),
        ]);
        let mut module = Module::new("bad_vector");
        module.functions.push(func);

        lower_dialects(&mut module).expect_err("unsupported vector shape must be rejected");
    }

    /// Module with a `verif.frontier_drain` op lowers (pass erases it).
    #[test]
    fn frontier_drain_erased() {
        let mut module = Module::new("test");
        let func = mk_func_with_body(vec![InstrNode::new(Inst::DialectOp(Box::new(
            verif::frontier_drain(ValueId::new(0)),
        )))]);
        module.functions.push(func);

        // Before lowering: one DialectOp body entry.
        assert_eq!(module.functions[0].blocks[0].body.len(), 1);
        assert!(matches!(
            module.functions[0].blocks[0].body[0].inst,
            Inst::DialectOp(_)
        ));

        let n = lower_dialects(&mut module).expect("lower");
        // FrontierDrainErase deletes the op.
        assert!(n >= 1, "expected at least one rewrite, got {n}");
        assert_eq!(module.functions[0].blocks[0].body.len(), 0);
    }

    /// Module with a `verif.bfs_step` lowers to a core `Inst::Call`.
    #[test]
    fn bfs_step_lowers_to_call() {
        let mut module = Module::new("test");
        let mut node = InstrNode::new(Inst::DialectOp(Box::new(verif::bfs_step(
            ValueId::new(0),
            ValueId::new(1),
            false,
        ))));
        node.results = vec![ValueId::new(42)];
        let func = mk_func_with_body(vec![node]);
        module.functions.push(func);

        let n = lower_dialects(&mut module).expect("lower");
        assert!(n >= 2, "expected progressive lowering rewrites, got {n}");

        let body = &module.functions[0].blocks[0].body;
        assert_eq!(body.len(), 1);
        match &body[0].inst {
            Inst::Call { callee, args } => {
                assert_eq!(*callee, FuncId::new(0));
                assert_eq!(args, &vec![ValueId::new(0), ValueId::new(1)]);
            }
            inst => panic!("expected Inst::Call after lowering, got {inst:?}"),
        }
        assert_eq!(body[0].results, vec![ValueId::new(42)]);
    }

    /// Unknown dialect (not registered) is rejected up front.
    #[test]
    fn unknown_dialect_rejected() {
        let mut module = Module::new("bad");
        let func = mk_func_with_body(vec![InstrNode::new(Inst::DialectOp(Box::new(
            DialectInst::new("no_such_dialect", "op").with_result_ty(Ty::I32),
        )))]);
        module.functions.push(func);

        let err = lower_dialects(&mut module).expect_err("unknown dialect must be rejected");
        let msg = format!("{err}");
        assert!(
            msg.contains("no_such_dialect"),
            "error message missing dialect name: {msg}"
        );
    }
}
