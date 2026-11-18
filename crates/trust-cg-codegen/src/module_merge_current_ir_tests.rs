// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Structural transport controls. These mint no native admission or source ABI.

use super::*;
use trust_ir::box_validity::{
    BoxDerefSite, BoxFactSession, BoxPointee, BoxValidityFact, PremiseRoot,
};
use trust_ir::{Block, BlockId, InstrNode, ValueId};

fn table_module(prefix: &str) -> Module {
    let mut module = Module::new(prefix);
    let target = FuncId::new(17);
    module.types = vec![Ty::FnItem(target), Ty::Array(TyId::new(0), 3)];
    module.func_types = vec![
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(
            vec![
                Ty::Tuple(vec![Ty::U8, Ty::Array(TyId::new(0), 3)]),
                Ty::Closure(ClosureTyId::new(0)),
                Ty::Func(FuncTyId::new(2)),
            ],
            vec![],
            false,
        ),
        FuncTy::unrecorded(vec![Ty::FnItem(target)], vec![Ty::FnItem(target)], false),
    ];
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(2),
        captures: vec![Ty::FnItem(target), Ty::Array(TyId::new(0), 3)],
    });
    // Sparse original IDs are intentional; neither may pass through raw.
    module.functions = vec![
        Function::new(
            FuncId::new(23),
            format!("{prefix}_holder"),
            FuncTyId::new(1),
            BlockId::new(0),
        ),
        Function::new(
            target,
            format!("{prefix}_target"),
            FuncTyId::new(0),
            BlockId::new(0),
        ),
    ];
    module
}

#[test]
fn nominal_targets_are_reserved_before_interning_nested_callable_and_aggregate_tables() {
    let inputs = [table_module("a"), table_module("b")];
    let merged = merge_modules(&inputs).unwrap();
    let mut expected = HashSet::new();
    for source in &inputs {
        let target = merged
            .functions
            .iter()
            .find(|f| f.name == format!("{}_target", source.name))
            .unwrap();
        expected.insert(target.id);
        assert_ne!(target.id, FuncId::new(17));
        for source_ty in &source.types {
            assert!(merged.types.iter().any(|actual| {
                tys_equal_name_resolved(source, source_ty, &merged, actual, TY_CMP_DEPTH_LIMIT)
                    .is_ok()
            }));
        }
        let source_holder = &source.functions[0];
        let actual_holder = merged
            .functions
            .iter()
            .find(|f| f.name == source_holder.name)
            .unwrap();
        func_tys_equal_name_resolved(
            source,
            source_holder.ty,
            &merged,
            actual_holder.ty,
            TY_CMP_DEPTH_LIMIT,
        )
        .unwrap();
    }
    assert_eq!(
        expected.len(),
        2,
        "equal target signatures do not identify two targets"
    );
    let mut actual = HashSet::new();
    merged.visit_types(|root| {
        root.visit_types(|ty| {
            if let Ty::FnItem(id) = ty {
                actual.insert(*id);
            }
        })
    });
    assert_eq!(actual, expected);
    let a = merged
        .functions
        .iter()
        .find(|f| f.name == "a_target")
        .unwrap()
        .id;
    let b = merged
        .functions
        .iter()
        .find(|f| f.name == "b_target")
        .unwrap()
        .id;
    assert!(
        tys_equal_name_resolved(
            &merged,
            &Ty::FnItem(a),
            &merged,
            &Ty::FnItem(b),
            TY_CMP_DEPTH_LIMIT
        )
        .is_err()
    );
    assert!(
        tys_equal_name_resolved(
            &merged,
            &Ty::FnItem(a),
            &merged,
            &Ty::Func(FuncTyId::new(0)),
            TY_CMP_DEPTH_LIMIT
        )
        .is_err()
    );
}

#[test]
fn missing_and_ambiguous_original_nominal_namespaces_refuse_without_changing_inputs() {
    for mode in 0..3 {
        let mut module = table_module("invalid");
        match mode {
            0 => module.types[0] = Ty::FnItem(FuncId::new(999)),
            1 => module.functions[1].id = module.functions[0].id,
            2 => module.functions[1].name = module.functions[0].name.clone(),
            _ => unreachable!(),
        }
        let original = module.clone();
        assert!(merge_modules(std::slice::from_ref(&module)).is_err());
        assert_eq!(module, original);
    }
}

#[test]
fn nested_nominal_constants_keep_target_and_class_even_with_equal_signatures() {
    let source = table_module("a");
    let mut merged = Module::new("relocated");
    merged.func_types.push(source.func_types[0].clone());
    merged.functions = vec![
        Function::new(
            FuncId::new(41),
            "a_target",
            FuncTyId::new(0),
            BlockId::new(0),
        ),
        Function::new(
            FuncId::new(42),
            "other_target",
            FuncTyId::new(0),
            BlockId::new(0),
        ),
    ];
    let original = Constant::Closure {
        func: FuncId::new(17),
        captures: vec![
            Constant::Aggregate(vec![Constant::FnItem(FuncId::new(17))]),
            Constant::Splat {
                elem: Box::new(Constant::FnItem(FuncId::new(17))),
                len: u64::MAX,
            },
        ],
    };
    let mut actual = original.clone();
    remap_constant(&mut actual, &HashMap::from([(17, 41)])).unwrap();
    check_constant_in_range(&actual, 43, "relocated").unwrap();
    constants_identity_preserved(&original, &source, &actual, &merged).unwrap();
    for replacement in [
        Constant::Splat {
            elem: Box::new(Constant::FnItem(FuncId::new(41))),
            len: u64::MAX - 1,
        },
        Constant::Splat {
            elem: Box::new(Constant::FnItem(FuncId::new(42))),
            len: u64::MAX,
        },
        Constant::Splat {
            elem: Box::new(Constant::FnDef(FuncId::new(41))),
            len: u64::MAX,
        },
    ] {
        let mut changed = actual.clone();
        let Constant::Closure { captures, .. } = &mut changed else {
            unreachable!();
        };
        captures[1] = replacement;
        assert!(constants_identity_preserved(&original, &source, &changed, &merged).is_err());
    }
    assert!(
        constant_batch_deferred(&Constant::FnItem(FuncId::new(17)))
            .unwrap()
            .contains("FnItem")
    );
    assert!(remap_constant(&mut original.clone(), &HashMap::new()).is_err());
    assert!(check_constant_in_range(&actual, 41, "wrong-bound").is_err());
    assert!(
        constants_identity_preserved(
            &Constant::FnItem(FuncId::new(17)),
            &source,
            &Constant::FnItem(FuncId::new(42)),
            &merged
        )
        .is_err()
    );
    assert!(
        constants_identity_preserved(
            &Constant::FnItem(FuncId::new(17)),
            &source,
            &Constant::FnDef(FuncId::new(41)),
            &merged
        )
        .is_err()
    );
}

#[test]
fn box_transport_remaps_both_type_roots_and_preserves_the_point_fact() {
    let mut maps = ModMaps {
        func_map: HashMap::from([(17, 41)]),
        func_ty_base: 0,
        func_ty_len: 0,
        func_ty_canon: HashMap::new(),
        closure_base: 0,
        closure_len: 0,
        struct_map: HashMap::from([(4, 8)]),
        enum_map: HashMap::new(),
        record_map: HashMap::new(),
        global_map: HashMap::new(),
        ty_map: HashMap::new(),
        file_map: HashMap::new(),
        files_len: 0,
    };
    let original = Inst::BoxDeref {
        ptr_ty: Ty::PtrConst(Box::new(Ty::FnItem(FuncId::new(17)))),
        pointee: BoxPointee::Sized {
            ty: Ty::Struct(StructId::new(4)),
        },
        operand: ValueId::new(99),
        fact: Box::new(BoxValidityFact::premise(
            BoxDerefSite {
                item: [9; 16],
                ordinal: 7,
            },
            BoxFactSession::PROOF_SNAPSHOT,
            PremiseRoot::ParamByValue,
        )),
    };
    let mut actual = original.clone();
    remap_inst(&mut actual, &maps, &maps.func_map, &mut 0).unwrap();
    let Inst::BoxDeref {
        ptr_ty,
        pointee,
        operand,
        fact,
    } = &actual
    else {
        panic!()
    };
    assert_eq!(ptr_ty, &Ty::PtrConst(Box::new(Ty::FnItem(FuncId::new(41)))));
    assert_eq!(pointee.ty(), &Ty::Struct(StructId::new(8)));
    let Inst::BoxDeref { fact: old_fact, .. } = &original else {
        panic!()
    };
    assert_eq!(fact, old_fact);
    assert_eq!(*operand, ValueId::new(99));
    maps.struct_map.clear();
    assert!(remap_inst(&mut original.clone(), &maps, &maps.func_map, &mut 0).is_err());
    // Canonical batch transport now carries this data. It preserves the
    // complete point fact; it does not grant the separate native fact permit.
    // Use a valid module here, independently of the sparse private-map probe.
    let mut module = Module::new("box_structural_transport");
    module
        .func_types
        .push(FuncTy::unrecorded(vec![Ty::Ptr], vec![Ty::Ptr], false));
    let mut function = Function::new(FuncId::new(0), "box", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(99), Ty::Ptr));
    block.body = vec![
        InstrNode::new(Inst::BoxDeref {
            ptr_ty: Ty::Ptr,
            pointee: BoxPointee::Sized { ty: Ty::I64 },
            operand: ValueId::new(99),
            fact: old_fact.clone(),
        })
        .with_result(ValueId::new(100)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(100)],
        }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let retained = module.clone();
    module_batch_eligible(&module).unwrap();
    let merged = merge_modules(std::slice::from_ref(&module)).unwrap();
    assert_eq!(module, retained);
    let actual = &merged.functions[0].blocks[0].body[0];
    assert_eq!(actual.results, vec![ValueId::new(100)]);
    assert!(matches!(&actual.inst,
        Inst::BoxDeref { ptr_ty: Ty::Ptr, pointee: BoxPointee::Sized { ty: Ty::I64 }, operand, fact }
        if *operand == ValueId::new(99) && fact == old_fact));
}
