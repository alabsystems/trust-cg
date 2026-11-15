// aggregate_ops.rs — aggregate operation lowering tests (#391)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::instructions::{Instruction, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_ir::{
    Block as TrustIrBlock, BlockId, ClosureTy, ClosureTyId, Constant, FieldDef, FuncId, FuncTy,
    FuncTyId, Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, RecordDef,
    RecordId, StructDef, StructId, Ty, TyId, ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn f(n: u32) -> FuncId {
    FuncId::new(n)
}

fn single_function_module(
    func_name: &str,
    ty: FuncTy,
    structs: Vec<StructDef>,
    types: Vec<Ty>,
    blocks: Vec<TrustIrBlock>,
) -> TrustIrModule {
    let entry = blocks.first().expect("module must have a block").id;
    let mut module = TrustIrModule::new(func_name);
    module.structs = structs;
    module.types = types;
    let fty_id: FuncTyId = module
        .add_func_type(ty)
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), func_name, fty_id, entry);
    func.blocks = blocks;
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// An insert into the parameter `Value(0)` is value-semantic: the parameter
/// is copied into a fresh slot, field `field_index` of that copy is stored as
/// an `I64`, and the copy is the result — the parameter's storage is never
/// written.
fn assert_value_semantic_i64_insert(instructions: &[Instruction], field_index: u32) {
    let [slot, len, copy, gep, store, result, ..] = instructions else {
        panic!("too few instructions: {instructions:?}");
    };
    assert!(matches!(slot.opcode, Opcode::StackAddr { .. }), "{slot:?}");
    let fresh = slot.results[0];
    assert!(matches!(len.opcode, Opcode::Iconst { .. }), "{len:?}");
    assert!(matches!(copy.opcode, Opcode::Memcpy), "{copy:?}");
    assert_eq!(copy.args, vec![fresh, Value(0), len.results[0]]);
    assert!(
        matches!(gep.opcode, Opcode::StructGep { field_index: f, .. } if f == field_index),
        "{gep:?}"
    );
    assert_eq!(gep.args, vec![fresh], "the field is addressed in the copy");
    assert!(matches!(
        store.opcode,
        Opcode::Store {
            ty: Type::I64,
            align: None
        }
    ));
    assert_eq!(store.args, vec![Value(1), gep.results[0]]);
    assert!(matches!(result.opcode, Opcode::Copy));
    assert_eq!(result.args, vec![fresh], "the result is the copy");
}

fn single_function(module: &TrustIrModule) -> &TrustIrFunction {
    module
        .functions
        .first()
        .expect("module must have one function")
}

fn record_function_module(
    func_name: &str,
    ty: FuncTy,
    records: Vec<RecordDef>,
    types: Vec<Ty>,
    blocks: Vec<TrustIrBlock>,
) -> TrustIrModule {
    let entry = blocks.first().expect("module must have a block").id;
    let mut module = TrustIrModule::new(func_name);
    module.records = records;
    module.types = types;
    let fty_id: FuncTyId = module
        .add_func_type(ty)
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), func_name, fty_id, entry);
    func.blocks = blocks;
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn pair_record_def() -> RecordDef {
    RecordDef {
        id: RecordId::new(0),
        name: "PairRecord".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
    }
}

fn nested_matrix_struct() -> (Vec<StructDef>, Vec<Ty>, Ty) {
    let row_ty = Ty::Array(TyId::new(0), 4);
    let matrix_ty = Ty::Array(TyId::new(1), 3);
    let outer_ty = Ty::Struct(StructId::new(0));
    let structs = vec![StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Outer".to_string(),
        fields: vec![
            FieldDef {
                name: "tag".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "matrix".to_string(),
                ty: matrix_ty,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }];
    (structs, vec![Ty::I32, row_ty], outer_ty)
}

fn assert_unsupported_message(err: AdapterError, needle: &str) {
    match err {
        AdapterError::UnsupportedInstruction(msg) => {
            assert!(
                msg.contains(needle),
                "expected unsupported message containing `{needle}`, got `{msg}`"
            );
        }
        other => panic!("expected UnsupportedInstruction, got {other:?}"),
    }
}

#[test]
fn struct_field_extract_lowers_through_struct_gep() {
    let structs = vec![StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }];
    let pair = Ty::Struct(StructId::new(0));

    let module = single_function_module(
        "extract_pair_field",
        FuncTy {
            params: vec![pair.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        },
        structs,
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), pair.clone())],
            body: vec![
                InstrNode::new(Inst::ExtractField {
                    ty: pair,
                    aggregate: v(0),
                    field: 1,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower struct field extract");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    assert!(matches!(
        bb.instructions[0].opcode,
        Opcode::StructGep { field_index: 1, .. }
    ));
    assert!(matches!(bb.instructions[1].opcode, Opcode::Load { .. }));
    assert!(
        bb.instructions
            .iter()
            .all(|inst| !matches!(inst.opcode, Opcode::Iadd | Opcode::Imul)),
        "aggregate field extract must not use aggregate-typed arithmetic"
    );
}

#[test]
fn array_element_extract_lowers_through_array_gep() {
    let array = Ty::Array(TyId::new(0), 2);
    let module = single_function_module(
        "extract_array_element",
        FuncTy {
            params: vec![array.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        },
        vec![],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), array.clone())],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::I64,
                    array: v(0),
                    index: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower array element extract");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        bb.instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::ArrayGep { .. }))
    );
    assert!(
        bb.instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Load { .. }))
    );
    assert!(
        bb.instructions
            .iter()
            .all(|inst| !matches!(inst.opcode, Opcode::Iadd | Opcode::Imul)),
        "aggregate element extract must not use aggregate-typed arithmetic"
    );
}

#[test]
fn array_element_insert_lowers_through_array_gep_store_copy() {
    let array = Ty::Array(TyId::new(0), 2);
    let module = single_function_module(
        "insert_array_element",
        FuncTy {
            params: vec![array.clone(), Ty::I64, Ty::I64],
            returns: vec![array.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), array.clone()), (v(1), Ty::I64), (v(2), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::InsertElement {
                    ty: array,
                    array: v(0),
                    index: v(1),
                    value: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower array element insert");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        bb.instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::ArrayGep { elem_ty: Type::I64 }))
    );
    assert!(bb.instructions.iter().any(|inst| matches!(
        inst.opcode,
        Opcode::Store {
            ty: Type::I64,
            align: None
        }
    )));
    assert!(
        bb.instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Copy))
    );
}

#[test]
fn record_field_extract_lowers_with_record_def() {
    let record = Ty::Record(RecordId::new(0));
    let module = record_function_module(
        "extract_record_field",
        FuncTy {
            params: vec![record.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        },
        vec![pair_record_def()],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), record.clone())],
            body: vec![
                InstrNode::new(Inst::ExtractField {
                    ty: record,
                    aggregate: v(0),
                    field: 1,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower record field extract");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    assert!(matches!(
        bb.instructions[0].opcode,
        Opcode::StructGep { field_index: 1, .. }
    ));
    assert!(matches!(
        bb.instructions[1].opcode,
        Opcode::Load {
            ty: Type::I64,
            align: None
        }
    ));
}

#[test]
fn record_field_insert_lowers_with_record_def() {
    let record = Ty::Record(RecordId::new(0));
    let module = record_function_module(
        "insert_record_field",
        FuncTy {
            params: vec![record.clone(), Ty::I64],
            returns: vec![record.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![pair_record_def()],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), record.clone()), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::InsertField {
                    ty: record,
                    aggregate: v(0),
                    field: 1,
                    value: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower record field insert");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    assert_value_semantic_i64_insert(&bb.instructions, 1);
}

#[test]
fn insert_field_rejects_value_type_mismatch() {
    let record = Ty::Record(RecordId::new(0));
    let module = record_function_module(
        "insert_record_field_mismatch",
        FuncTy {
            params: vec![record.clone(), Ty::I32],
            returns: vec![record.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![pair_record_def()],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), record.clone()), (v(1), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::InsertField {
                    ty: record,
                    aggregate: v(0),
                    field: 1,
                    value: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );

    let err = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .unwrap_err();
    assert_unsupported_message(err, "does not match field type");
}

fn assert_flat_gep_steps(
    instructions: &[trust_cg_lower::instructions::Instruction],
    count: usize,
    stride: u32,
) {
    let strides: Vec<_> = instructions
        .iter()
        .filter_map(|inst| match &inst.opcode {
            Opcode::ArrayGep { elem_ty } => Some(elem_ty.bytes()),
            _ => None,
        })
        .collect();
    assert_eq!(strides, vec![stride; count]);
    assert!(
        !instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { .. }))
    );
}

#[test]
fn multi_index_record_gep_strides_whole_records() {
    let record = Ty::Record(RecordId::new(0));
    let module = record_function_module(
        "record_multi_index_gep",
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        },
        vec![pair_record_def()],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: record,
                    base: v(0),
                    indices: vec![v(1), v(2)],
                    inbounds: false,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(3),
                    volatile: false,
                    align: None,
                })
                .with_result(v(4)),
                InstrNode::new(Inst::Return { values: vec![v(4)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower record multi-index GEP");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    assert_flat_gep_steps(&bb.instructions, 2, 16);
    assert!(bb.instructions.iter().any(|inst| matches!(
        inst.opcode,
        Opcode::Load {
            ty: Type::I64,
            align: None
        }
    )));
}

#[test]
fn nested_struct_array_multi_index_gep_keeps_one_scale() {
    let (structs, types, outer_ty) = nested_matrix_struct();
    let module = single_function_module(
        "nested_struct_array_gep",
        FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        },
        structs,
        types,
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(4)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: outer_ty,
                    base: v(0),
                    indices: vec![v(3), v(4), v(1), v(2)],
                    inbounds: false,
                })
                .with_result(v(5)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(5),
                    volatile: false,
                    align: None,
                })
                .with_result(v(6)),
                InstrNode::new(Inst::Return { values: vec![v(6)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower nested multi-index GEP");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    // All four indices stride the complete outer struct, never its fields.
    let strides: Vec<_> = bb
        .instructions
        .iter()
        .filter_map(|inst| match &inst.opcode {
            Opcode::ArrayGep { elem_ty } => Some(elem_ty.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(strides.len(), 4);
    assert!(strides.iter().all(|ty| ty == &strides[0]));
    assert!(matches!(strides[0], Type::Struct(_)));
    assert!(
        !bb.instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { .. }))
    );
    assert!(bb.instructions.iter().any(|inst| matches!(
        inst.opcode,
        Opcode::Load {
            ty: Type::I32,
            align: None
        }
    )));
}

#[test]
fn multi_index_gep_accepts_dynamic_indices_for_struct_pointees() {
    let (structs, types, outer_ty) = nested_matrix_struct();
    let module = single_function_module(
        "dynamic_struct_field_gep",
        FuncTy {
            params: vec![Ty::Ptr, Ty::I64],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        },
        structs,
        types,
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: outer_ty,
                    base: v(0),
                    indices: vec![v(2), v(1)],
                    inbounds: false,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    );

    let (lir, _) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    let steps: Vec<_> = lir.blocks[&lir.entry_block]
        .instructions
        .iter()
        .filter_map(|inst| match &inst.opcode {
            Opcode::ArrayGep { elem_ty } => Some(elem_ty),
            _ => None,
        })
        .collect();
    assert_eq!(steps.len(), 2);
    assert_eq!(steps[0], steps[1]);
}

#[test]
fn multi_index_gep_indices_are_not_limited_by_field_count() {
    let (structs, types, outer_ty) = nested_matrix_struct();
    let module = single_function_module(
        "oob_struct_field_gep",
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        },
        structs,
        types,
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(9),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: outer_ty,
                    base: v(0),
                    indices: vec![v(1), v(2)],
                    inbounds: false,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    );

    let (lir, _) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    let bb = &lir.blocks[&lir.entry_block];
    assert_eq!(
        bb.instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::ArrayGep { .. }))
            .count(),
        2
    );
    assert!(
        !bb.instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { .. }))
    );
}

#[test]
fn multi_index_gep_accepts_scalar_pointees() {
    let module = single_function_module(
        "scalar_trailing_index_gep",
        FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        },
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I32,
                    base: v(0),
                    indices: vec![v(1), v(2)],
                    inbounds: false,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    );

    let (lir, _) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    assert_flat_gep_steps(&lir.blocks[&lir.entry_block].instructions, 2, 4);
}

// ---------------------------------------------------------------------------
// First-class closure aggregates.
//
// `Ty::Closure(ClosureTyId)` resolves through `module.closure_types` to a
// `ClosureTy { captures: Vec<Ty> }` — an ordered list of captured value types,
// i.e. a struct of its captures. The adapter lowers it to `Type::Struct` with
// natural-alignment (C-layout) field offsets, so capture access reuses the
// proven StructGep + Load / Store struct machinery.
// ---------------------------------------------------------------------------

/// A closure capturing `[I32, I64, I8]`. The bare-fn signature is irrelevant to
/// the capture layout, so reuse a trivial one.
fn heterogeneous_closure_ty(module_func_ty: FuncTyId) -> ClosureTy {
    ClosureTy {
        func: module_func_ty,
        captures: vec![Ty::I32, Ty::I64, Ty::I8],
    }
}

#[test]
fn closure_capture_extract_lowers_via_struct_gep() {
    let closure = Ty::Closure(ClosureTyId::new(0));
    let mut module = TrustIrModule::new("extract_closure_capture");
    // The closure's bare-fn signature references a func type; add one first.
    let bare_fn = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .add_closure_type(heterogeneous_closure_ty(bare_fn))
        .expect("Module::add_closure_type: test fixture");
    let fty_id = module
        .add_func_type(FuncTy {
            params: vec![closure.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(1), "extract_closure_capture", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), closure.clone())],
        body: vec![
            // ExtractElement over a closure source at capture index 1 (the I64).
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: v(0),
                index: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![v(2)] }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower closure capture extract");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        bb.instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { field_index: 1, .. })),
        "closure capture extract must emit StructGep at the capture's field index"
    );
    assert!(
        bb.instructions.iter().any(|inst| matches!(
            inst.opcode,
            Opcode::Load {
                ty: Type::I64,
                align: None
            }
        )),
        "closure capture extract must Load the I64 capture"
    );
}

#[test]
fn closure_capture_insert_lowers_via_struct_gep() {
    let closure = Ty::Closure(ClosureTyId::new(0));
    let mut module = TrustIrModule::new("insert_closure_capture");
    let bare_fn = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .add_closure_type(heterogeneous_closure_ty(bare_fn))
        .expect("Module::add_closure_type: test fixture");
    let fty_id = module
        .add_func_type(FuncTy {
            params: vec![closure.clone(), Ty::I64],
            returns: vec![closure.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(1), "insert_closure_capture", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), closure.clone()), (v(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::InsertField {
                ty: closure.clone(),
                aggregate: v(0),
                field: 1,
                value: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![v(2)] }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must lower closure capture insert");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    assert_value_semantic_i64_insert(&bb.instructions, 1);
}

#[test]
fn closure_capture_extract_rejects_type_mismatch() {
    let closure = Ty::Closure(ClosureTyId::new(0));
    let mut module = TrustIrModule::new("extract_closure_capture_mismatch");
    let bare_fn = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .add_closure_type(heterogeneous_closure_ty(bare_fn))
        .expect("Module::add_closure_type: test fixture");
    let fty_id = module
        .add_func_type(FuncTy {
            params: vec![closure.clone()],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(1), "extract_closure_capture_mismatch", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), closure.clone())],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(v(1)),
            // Capture 1 is I64, but we declare I32 — must fail closed, never
            // emit a wrong-width load.
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![v(2)] }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let err = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap_err();
    assert_unsupported_message(err, "does not match closure capture type");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
