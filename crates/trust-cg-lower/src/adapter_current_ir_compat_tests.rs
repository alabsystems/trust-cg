// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit current-cohort boundaries. These call the actual adapter and its
//! before-transformation floor; no fixture grants source, ABI or CER authority.

use super::*;
use trust_ir::box_validity::{
    BoxDerefSite, BoxFactSession, BoxPointee, BoxValidityFact, PremiseRoot,
};
use trust_ir::{Block as IrBlock, BlockId, FuncTyId, ValueId};

fn function(inst: Inst) -> TrustIrFunction {
    let mut function = TrustIrFunction::new(
        FuncId::new(0),
        "current_ir_boundary",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = IrBlock::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(inst).with_result(ValueId::new(7)));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    function
}

fn unsupported<T>(value: Result<T, AdapterError>, expected: &str) {
    let Err(AdapterError::UnmodeledTrustIrConstruct { construct, .. }) = value else {
        panic!("the adapter must explicitly refuse {expected}");
    };
    assert_eq!(construct, expected);
}

fn box_deref() -> Inst {
    Inst::BoxDeref {
        ptr_ty: Ty::Ptr,
        pointee: BoxPointee::Sized { ty: Ty::U32 },
        operand: ValueId::new(99),
        fact: Box::new(BoxValidityFact::premise(
            BoxDerefSite {
                item: [9; 16],
                ordinal: 2,
            },
            BoxFactSession::PROOF_SNAPSHOT,
            PremiseRoot::ParamByValue,
        )),
    }
}

#[test]
fn nominal_types_do_not_become_unit_integer_or_address_carriers() {
    assert_eq!(translate_type(&Ty::Unit).unwrap(), Type::Struct(vec![]));
    assert_eq!(translate_type(&Ty::U32).unwrap(), Type::I32);
    for target in [0, 1, u32::MAX] {
        let nominal = Ty::FnItem(FuncId::new(target));
        unsupported(translate_type(&nominal), "Ty::FnItem");
        unsupported(
            translate_type(&Ty::Tuple(vec![Ty::U8, nominal, Ty::U64])),
            "Ty::FnItem",
        );
    }
}

#[test]
fn unused_box_operation_is_refused_before_a_lane_can_erase_it() {
    let mut function = function(box_deref());
    let mut adapter = TrustIrAdapter::new(&[], HashMap::new());
    assert!(matches!(
        adapter.translate(&function),
        Err(AdapterError::BoxDerefNotAdmitted { .. })
    ));
    function.blocks[0].body.remove(0);
    assert!(unmodeled_body_construct_floor(&function, None).is_ok());
}

#[test]
fn box_type_roots_preserve_both_pointer_and_pointee() {
    let mut roots = Vec::new();
    box_deref().visit_type_roots(|ty| roots.push(ty.clone()));
    assert_eq!(roots, vec![Ty::Ptr, Ty::U32]);
    roots.clear();
    visit_top_level_types(&box_deref(), |ty| roots.push(ty.clone()));
    assert_eq!(
        roots,
        vec![Ty::Ptr],
        "only a pointer crosses the native value ABI"
    );
}

#[test]
fn nominal_constants_are_refused_through_stored_aggregate_and_splat_children() {
    let id = FuncId::new(17);
    for value in [
        Constant::FnItem(id),
        Constant::Aggregate(vec![Constant::Int(1), Constant::FnItem(id)]),
        Constant::Closure {
            func: FuncId::new(3),
            captures: vec![Constant::FnItem(id)],
        },
        Constant::Splat {
            elem: Box::new(Constant::FnItem(id)),
            len: u64::MAX,
        },
    ] {
        let function = function(Inst::Const {
            ty: Ty::FnItem(id),
            value,
        });
        unsupported(
            unmodeled_body_construct_floor(&function, None),
            "Constant::FnItem",
        );
    }
    let function = function(Inst::Const {
        ty: Ty::I32,
        value: Constant::Int(17),
    });
    assert!(unmodeled_body_construct_floor(&function, None).is_ok());
}
