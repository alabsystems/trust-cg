// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Current IR forms are refused by the actual bounded scanner, without
//! changing their nominal identity, point-specific facts or storage profiles.

use super::*;
use trust_ir::box_validity::{
    BoxDerefSite, BoxFactSession, BoxPointee, BoxValidityFact, PremiseRoot,
};
use trust_ir::{
    EnumDef, EnumId, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    FieldStorageLayout, FuncTy, FuncTyId, UninhabitedVariantLayout,
};

fn boxed(operand: ValueId) -> Inst {
    Inst::BoxDeref {
        ptr_ty: Ty::Ptr,
        pointee: BoxPointee::Sized { ty: Ty::U32 },
        operand,
        fact: Box::new(BoxValidityFact::premise(
            BoxDerefSite {
                item: [7; 16],
                ordinal: 3,
            },
            BoxFactSession::PROOF_SNAPSHOT,
            PremiseRoot::ParamByValue,
        )),
    }
}

fn module_with(node: InstrNode, params: Vec<(ValueId, Ty)>) -> Module {
    let mut module = Module::new("current_fsym_boundary");
    module.func_types.push(FuncTy::unrecorded(
        params.iter().map(|(_, ty)| ty.clone()).collect(),
        vec![],
        false,
    ));
    let mut function = Function::new(FuncId::new(0), "subject", FuncTyId::new(0), BlockId::new(0));
    function.blocks.push(Block {
        id: BlockId::new(0),
        params,
        body: vec![node, InstrNode::new(Inst::Return { values: vec![] })],
    });
    module.functions.push(function);
    module
}

fn assert_refused(module: &Module, name: &str) {
    let report = scan_function_in_module(module, &module.functions[0]);
    assert_eq!(report.scanned_functions, 0, "{report:?}");
    assert_eq!(report.skipped_functions.len(), 1, "{report:?}");
    let refusal = &report.skipped_functions[0];
    assert_eq!(
        refusal.reason,
        FsymTrustIrSkipReason::UnsupportedInstruction
    );
    assert!(refusal.detail.contains(name), "{refusal:?}");
    assert!(report.diagnostics.is_empty() && report.unknown_obligations.is_empty());
}

#[test]
fn box_refusal_keeps_its_actual_ssa_operand_and_does_not_scan_safe() {
    for id in [17, 71] {
        let operand = ValueId::new(id);
        let inst = boxed(operand);
        let mut actual = Vec::new();
        inst.visit_value_operands(|value| actual.push(value));
        assert_eq!(actual, vec![operand]);
        assert_eq!(
            crate::ssa_loop_complete::non_terminator_value_uses(&inst),
            actual
        );
        assert_eq!(
            crate::fsym_ub_map::fsym_inst_variant_name(&inst),
            "BoxDeref"
        );
        assert!(crate::fsym_ub_map::FSYM_INST_VARIANTS.contains(&("BoxDeref", false)));
        let module = module_with(
            InstrNode::new(inst).with_result(ValueId::new(90)),
            vec![(operand, Ty::Ptr)],
        );
        assert_refused(&module, "BoxDeref");
    }
}

#[test]
fn nominal_constants_are_refused_through_stored_children_without_splat_expansion() {
    let id = FuncId::new(1);
    for (ty, value, element_types) in [
        (Ty::FnItem(id), Constant::FnItem(id), vec![]),
        (
            Ty::Tuple(vec![Ty::U8, Ty::FnItem(id)]),
            Constant::Aggregate(vec![Constant::Int(7), Constant::FnItem(id)]),
            vec![],
        ),
        (
            Ty::Array(trust_ir::TyId::new(0), u64::MAX),
            Constant::Splat {
                elem: Box::new(Constant::FnItem(id)),
                len: u64::MAX,
            },
            vec![Ty::FnItem(id)],
        ),
    ] {
        assert!(carries_fn_item(&value));
        assert!(constant_expr(&ty, &value, Some(64)).is_none());
        let mut module = module_with(
            InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(90)),
            vec![],
        );
        module.types = element_types;
        module.functions.push(Function::new(
            id,
            "nominal_target",
            FuncTyId::new(0),
            BlockId::new(0),
        ));
        // The complete typed-module fence precedes instruction evaluation;
        // these stored children must hit that nominal boundary as well.
        assert_refused(
            &module,
            "FnItem nominal identity has no complete bounded fsym value model",
        );
    }
    assert!(carries_fn_item(&Constant::Closure {
        func: FuncId::new(2),
        captures: vec![Constant::FnItem(id)],
    }));
    let ordinary = module_with(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(90)),
        vec![],
    );
    assert_eq!(
        scan_function_in_module(&ordinary, &ordinary.functions[0]).scanned_functions,
        1
    );
}

#[test]
fn nominal_entry_values_do_not_become_the_existing_code_address_class() {
    let id = FuncId::new(7);
    let nominal = trust_ir::InterpretValue {
        ty: Ty::FnItem(id),
        kind: trust_ir::InterpretValueKind::FnItem(id),
    };
    assert!(
        forged_part(&nominal)
            .unwrap()
            .contains("nominal function item")
    );
    assert!(
        FSYM_RUN_MODEL
            .breach(
                &trust_ir::InterpretOptions::default(),
                std::slice::from_ref(&nominal)
            )
            .unwrap()
            .contains("nominal function item")
    );
    let nested = trust_ir::InterpretValue {
        ty: Ty::Tuple(vec![nominal.ty.clone()]),
        kind: trust_ir::InterpretValueKind::Aggregate(vec![nominal]),
    };
    assert!(forged_part(&nested).is_some());
    let address = trust_ir::InterpretValue {
        ty: Ty::Func(FuncTyId::new(0)),
        kind: trust_ir::InterpretValueKind::FnDef(id),
    };
    assert!(
        forged_part(&address).is_none(),
        "the existing input class is unchanged"
    );
}

#[test]
fn storage_profiled_direct_enum_has_a_named_refusal_and_preserves_legacy_layouts() {
    let dead = EnumDef::new(EnumId::new(9), "Infallible", vec![]);
    let mut def = EnumDef::new(
        EnumId::new(7),
        "StorageProfile",
        vec![
            EnumVariant {
                name: "Dead".into(),
                fields: vec![Ty::Enum(dead.id)],
                field_names: vec![],
            },
            EnumVariant {
                name: "Live".into(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
        ],
    )
    .with_repr(EnumTagRepr::U32);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::DirectWithUninhabited {
            tag_offset: 0,
            variants: vec![UninhabitedVariantLayout {
                variant: 0,
                size: 4,
                align: 4,
                fields: vec![FieldStorageLayout { size: 0, align: 1 }],
            }],
        },
        size: 8,
        align: 4,
        variant_field_offsets: vec![vec![4], vec![4]],
    });
    let mut module = Module::new("fsym_current_enum");
    module.enums = vec![def, dead];
    assert!(module.enum_layout_shape(EnumId::new(7)).is_ok());
    let original = module.enums.clone();
    let error = crate::fsym_layout::FsymLayout::new(&module)
        .enum_layout(&Ty::Enum(EnumId::new(7)))
        .unwrap_err();
    assert!(error.contains("DirectWithUninhabited"), "{error}");
    assert_eq!(module.enums, original);
    module.enums[0].layout = None;
    module.enums[0].variants[0].fields = vec![Ty::U32];
    assert!(
        crate::fsym_layout::FsymLayout::new(&module)
            .enum_layout(&Ty::Enum(EnumId::new(7)))
            .is_ok()
    );
}
