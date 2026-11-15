// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! v52 source assertions retain their panic identity or refuse before a
//! native/WASM lowering can erase it into an internal generic trap.

use trust_cg_lower::adapter::{AdapterError, reject_unconsumed_v41_target_neutral_surface};
use trust_ir::{
    AssertKind, AssertOverflowOp, Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode,
    Linkage, Module, Ty, ValueId,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn kinds() -> Vec<AssertKind> {
    let mut kinds = vec![AssertKind::Unspecified];
    kinds.extend(AssertOverflowOp::ALL.map(AssertKind::Overflow));
    kinds.extend([
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        },
        AssertKind::MisalignedPtr {
            required: v(1),
            found: v(2),
        },
        AssertKind::NullPtr,
    ]);
    kinds
}

fn module(kind: AssertKind) -> Module {
    let mut module = Module::new("assert_panic_surface");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::Usize, Ty::Usize],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "checked", signature, BlockId::new(7));
    let mut block = Block::new(BlockId::new(7));
    block.params = vec![(v(0), Ty::Bool), (v(1), Ty::Usize), (v(2), Ty::Usize)];
    block.body = vec![
        InstrNode::new(Inst::Assert {
            cond: v(0),
            kind,
            site: None,
        }),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    module
}

#[test]
fn every_panic_kind_is_refused_without_identity_erasure() {
    for kind in kinds() {
        let module = module(kind);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        for error in [
            reject_unconsumed_v41_target_neutral_surface(&module).unwrap_err(),
            trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &permit_unlicensed(),
            )
            .unwrap_err(),
        ] {
            if kind.is_unspecified() {
                assert!(
                    matches!(
                        error,
                        AdapterError::TrustIrAdmissionRefused { ref error }
                            if error.contains("fn checked: bb7#0")
                                && error.contains("unspecified panic kind")
                                && error.contains("require_assert_panic_kinds")
                    ),
                    "{error:?}"
                );
            } else {
                assert!(
                    matches!(
                        error,
                        AdapterError::AssertPanicUnsupported { kind: actual, ref location, .. }
                            if actual == kind && location == "function `checked` bb7 instruction 0"
                    ),
                    "{error:?}"
                );
                assert!(
                    error
                        .to_string()
                        .contains("never lowered to a generic trap")
                );
            }
        }
    }
}

#[test]
fn skipped_available_externally_body_cannot_hide_a_panic() {
    let mut module = module(AssertKind::DivByZero);
    module.functions[0].linkage = Linkage::AvailableExternally;
    assert!(matches!(
        reject_unconsumed_v41_target_neutral_surface(&module),
        Err(AdapterError::AssertPanicUnsupported {
            kind: AssertKind::DivByZero,
            ..
        })
    ));
}

#[test]
fn changing_only_the_stated_kind_changes_the_refusal() {
    let mut module = module(AssertKind::BoundsCheck {
        index: v(1),
        len: v(2),
    });
    let before = reject_unconsumed_v41_target_neutral_surface(&module).unwrap_err();
    module.functions[0].blocks[0].body[0].inst = Inst::Assert {
        cond: v(0),
        kind: AssertKind::MisalignedPtr {
            required: v(1),
            found: v(2),
        },
        site: None,
    };
    let after = reject_unconsumed_v41_target_neutral_surface(&module).unwrap_err();
    assert_ne!(before.to_string(), after.to_string());
    assert!(before.to_string().contains("BoundsCheck"));
    assert!(after.to_string().contains("MisalignedPtr"));
}

#[test]
fn no_assert_and_internal_checked_assume_remain_admitted() {
    let mut module = module(AssertKind::Unspecified);
    module.functions[0].blocks[0].body[0].inst = Inst::Assume { cond: v(0) };
    reject_unconsumed_v41_target_neutral_surface(&module).unwrap();
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    assert!(
        lir.blocks
            .values()
            .flat_map(|block| &block.instructions)
            .any(|inst| matches!(inst.opcode, trust_cg_lower::instructions::Opcode::Assert))
    );
    module.functions[0].blocks[0].body.remove(0);
    reject_unconsumed_v41_target_neutral_surface(&module).unwrap();
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
