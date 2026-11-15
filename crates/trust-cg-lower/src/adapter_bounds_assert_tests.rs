// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, InstrNode, Module, ProofAnnotation};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn fixture(ty: Ty, bound: i128) -> Module {
    let mut module = Module::new("canonical_bounds_assert");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "checked_index", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(0), ty.clone())];
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Int(bound),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ult,
            ty,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::Assert {
            cond: v(2),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        }),
        InstrNode::new(Inst::Return { values: vec![v(0)] }),
    ];
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn assert_refused(module: &Module) {
    let errors = trust_ir_build::validate_module(module);
    assert!(errors.is_empty(), "{errors:?}");
    let err =
        crate::translate_function_with_license(&module.functions[0], module, &permit_unlicensed())
            .unwrap_err();
    assert!(err.to_string().contains("unspecified panic kind"), "{err}");
    assert!(
        err.to_string().contains("require_assert_panic_kinds"),
        "{err}"
    );
}

#[test]
fn canonical_bounds_assert_refuses_even_a_historical_fusion_candidate() {
    for ty in [Ty::I64, Ty::U64] {
        for bound in [0, 1, 8, 4096, i128::from(i32::MAX)] {
            let module = fixture(ty.clone(), bound);
            assert_eq!(
                index(&module.functions[0], GuardCarrierArch::AArch64).len(),
                1
            );
            assert_refused(&module);
        }
    }
}

#[test]
fn canonical_bounds_assert_observable_compare_is_not_a_fusion_or_admission_license() {
    let mut module = fixture(Ty::I64, 8);
    module.func_types[0].returns.push(Ty::Bool);
    let block = &mut module.functions[0].blocks[0];
    block.body.last_mut().unwrap().inst = Inst::Return {
        values: vec![v(0), v(2)],
    };
    assert!(index(&module.functions[0], GuardCarrierArch::AArch64).is_empty());
    assert_refused(&module);
}

#[test]
fn canonical_bounds_assert_other_predicates_widths_and_large_bounds_also_refuse() {
    for ty in [Ty::I32, Ty::U32, Ty::I16, Ty::U16] {
        let module = fixture(ty, 8);
        assert!(index(&module.functions[0], GuardCarrierArch::AArch64).is_empty());
        assert_refused(&module);
    }
    for op in [ICmpOp::Ule, ICmpOp::Slt, ICmpOp::Eq, ICmpOp::Ne] {
        let mut module = fixture(Ty::I64, 8);
        let Inst::ICmp { op: actual, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
            unreachable!()
        };
        *actual = op;
        assert!(index(&module.functions[0], GuardCarrierArch::AArch64).is_empty());
        assert_refused(&module);
    }
    for bound in [-1, i128::from(i32::MAX) + 1] {
        let module = fixture(Ty::I64, bound);
        assert!(index(&module.functions[0], GuardCarrierArch::AArch64).is_empty());
        assert_refused(&module);
    }
}

#[test]
fn canonical_bounds_assert_never_moves_past_an_intervening_effect() {
    let mut module = fixture(Ty::I64, 8);
    let block = &mut module.functions[0].blocks[0];
    block.body.insert(
        2,
        InstrNode::new(Inst::Assert {
            cond: v(2),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        }),
    );
    assert!(index(&module.functions[0], GuardCarrierArch::AArch64).is_empty());
    assert_refused(&module);
}

#[test]
fn canonical_bounds_assert_rejects_duplicate_definitions_and_foreign_conditions() {
    let module = fixture(Ty::I64, 8);
    for (position, value) in [(0, v(0)), (0, v(2)), (1, v(0)), (1, v(1))] {
        let mut changed = module.clone();
        changed.functions[0].blocks[0].body[position].results = vec![value];
        assert!(index(&changed.functions[0], GuardCarrierArch::AArch64).is_empty());
        assert!(!trust_ir_build::validate_module(&changed).is_empty());
    }
    let mut changed = module;
    changed.functions[0].blocks[0].body[2].inst = Inst::Assert {
        cond: v(99),
        kind: trust_ir::AssertKind::Unspecified,
        site: None,
    };
    assert!(index(&changed.functions[0], GuardCarrierArch::AArch64).is_empty());
}

#[test]
fn canonical_bounds_assert_metadata_and_nondominating_constants_do_not_fuse() {
    for position in [1, 2] {
        let mut module = fixture(Ty::I64, 8);
        module.functions[0].blocks[0].body[position]
            .proofs
            .push(ProofAnnotation::NoPanic);
        assert!(index(&module.functions[0], GuardCarrierArch::AArch64).is_empty());
    }
    for position in [1, 2] {
        let mut module = fixture(Ty::I64, 8);
        module.functions[0].blocks[0].body[position].proof_context =
            Some(trust_ir::proof::ProofContext {
                assumes: vec![],
                establishes: vec![],
            });
        assert!(index(&module.functions[0], GuardCarrierArch::AArch64).is_empty());
    }
    let mut module = fixture(Ty::I64, 8);
    let block = &mut module.functions[0].blocks[0];
    let bound = block.body.remove(0);
    block.body.insert(2, bound);
    assert!(index(&module.functions[0], GuardCarrierArch::AArch64).is_empty());
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> crate::CodegenLicensePolicy {
    crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
}
