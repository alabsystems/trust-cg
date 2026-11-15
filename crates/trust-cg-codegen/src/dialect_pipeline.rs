// trust-cg-codegen/dialect_pipeline.rs - Pre-adapter dialect lowering (compatibility facade)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: issue #433, trust_ir #428. The pre-adapter dialect stage is now
// the registry-driven legalization of `crate::dialect_legalization` (ledger
// L05-P11); this module keeps the original entry points for callers that hold
// a bare module and want the default registry.

//! Pre-adapter dialect lowering with the backend's default registry.
//!
//! Every entry here runs [`crate::dialect_legalization::legalize_module`] with
//! [`DialectLegalizationRegistry::trust_cg_default`] for the host architecture
//! and no proof requirement, and discards the legalization report. The
//! [`crate::compiler::Compiler`] entries call the legalization directly, with
//! the compile's own target, proof policy and registry, and record the report
//! on their results.
//!
//! An unknown dialect, op or nominal type is refused by exact name before the
//! trust_ir->LIR adapter runs; the adapter's own refusals remain the backstop
//! for paths that skip this stage.

use std::borrow::Cow;

use crate::dialect_legalization::{
    DialectLegalizationRegistry, LegalizationOptions, legalize_module,
    module_has_dialect_constructs,
};
pub use crate::dialect_legalization::{DialectPipelineError, MAX_LOWERING_ITERS};

/// Return true if `module` contains at least one dialect op or nominal
/// dialect type.
pub fn has_dialect_ops(module: &trust_ir::Module) -> bool {
    module_has_dialect_constructs(module)
}

/// Legalize `module`'s dialect constructs with the default registry only when
/// it carries any.
///
/// The common cold-start path from tRust/tSwift/tC emits core trust_ir with no
/// dialect construct; that module is borrowed, not cloned. Returns the module
/// to translate and the number of op sites rewritten.
pub fn lower_dialects_if_needed(
    module: &trust_ir::Module,
) -> Result<(Cow<'_, trust_ir::Module>, usize), DialectPipelineError> {
    let legalized = legalize_module(
        module,
        &DialectLegalizationRegistry::trust_cg_default(),
        LegalizationOptions::host(),
    )?;
    let rewrites = legalized
        .report
        .as_ref()
        .map_or(0, |report| report.rewritten_op_sites());
    Ok((legalized.module, rewrites))
}

/// Legalize `module` in place with the default registry.
///
/// Returns the number of op sites rewritten. Callers that do not already own
/// a mutable module should prefer [`lower_dialects_if_needed`].
pub fn lower_dialects(module: &mut trust_ir::Module) -> Result<usize, DialectPipelineError> {
    let (legalized, rewrites) = lower_dialects_if_needed(module)?;
    if let Cow::Owned(legalized) = legalized {
        *module = legalized;
    }
    Ok(rewrites)
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

    /// A module whose dialect ops all stay for the adapter is not cloned.
    #[test]
    fn adapter_native_vector_ops_are_kept_and_borrowed() {
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
        assert!(matches!(lowered, Cow::Borrowed(_)));
        assert!(matches!(
            &lowered.functions[0].blocks[0].body[0].inst,
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

        let error =
            lower_dialects(&mut module).expect_err("unsupported vector shape must be rejected");
        assert!(
            matches!(error, DialectPipelineError::Grammar { ref op, .. } if op == "pack_lanes"),
            "{error}"
        );
    }

    /// The default registry carries the `verif` v1 payload contract but binds
    /// no runtime: trust-ir's illustrative lowering (an erased
    /// `frontier_drain`, a `bfs_step` call to function id 0) is not applied,
    /// and the op is refused by name.
    #[test]
    fn verif_contract_ops_are_refused_unbound_by_default() {
        for op in [
            verif::frontier_drain(ValueId::new(0)),
            verif::bfs_step(ValueId::new(0), ValueId::new(1), false),
            verif::fingerprint_batch(ValueId::new(0), ValueId::new(2)),
        ] {
            let name = op.op.clone();
            let has_result = !op.result_tys.is_empty();
            let mut node = InstrNode::new(Inst::DialectOp(Box::new(op)));
            if has_result {
                node.results = vec![ValueId::new(3)];
            }
            let mut module = Module::new("verif");
            let ty = module
                .add_func_type(trust_ir::FuncTy {
                    params: vec![Ty::Ptr, Ty::Ptr, Ty::I64],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "test", ty, BlockId::new(0));
            let mut block = Block::new(BlockId::new(0));
            block.params = vec![
                (ValueId::new(0), Ty::Ptr),
                (ValueId::new(1), Ty::Ptr),
                (ValueId::new(2), Ty::I64),
            ];
            block.body = vec![node, InstrNode::new(Inst::Return { values: vec![] })];
            func.blocks.push(block);
            module.functions.push(func);
            let error = lower_dialects(&mut module).expect_err("unbound verif op must be refused");
            assert!(
                matches!(&error, DialectPipelineError::Unbound { dialect, op, .. }
                    if dialect == "verif" && *op == name),
                "{error}"
            );
            assert!(
                error.to_string().contains("[TCG-DIALECT-UNBOUND]"),
                "{error}"
            );
        }
    }

    /// Unknown dialect (not registered) is rejected up front, by name.
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
            msg.contains("no_such_dialect") && msg.contains("[TCG-DIALECT-UNREGISTERED]"),
            "error message missing dialect name: {msg}"
        );
    }
}
