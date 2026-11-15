// aggregate_constants.rs — aggregate-constant lowering (#391)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Aggregate-constant lowering tests for #391.
//!
//! A `Const { value: Constant::Aggregate(..) }` of a struct / tuple / array
//! type with all-scalar fields must survive the adapter without erroring and
//! must materialise as:
//!
//! ```text
//!   StackAddr slot            -> result (pointer to aggregate)
//!   Iconst/Fconst <field 0>
//!   StructGep/ArrayGep        -> field_ptr 0
//!   Store <field 0>, field_ptr 0
//!   ... (repeat per field) ...
//! ```
//!
//! Downstream SROA (see `crates/trust-cg-opt/tests/sroa_pipeline.rs`) eliminates
//! the stack traffic at O1+ when the aggregate pointer does not escape.
//!
//! Enum aggregate constants use the #398 tagged-union decision: tag element
//! first, then the selected variant payload fields.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::instructions::Opcode;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, EnumDef, EnumId, EnumVariant, FatPtrKind, FieldDef,
    FuncId, FuncTy, FuncTyId, Function as TrustIrFunction, Global, Inst, InstrNode, Linkage,
    Module as TrustIrModule, StructDef, StructId, Ty, TyId, ValueId, Visibility,
};

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::assert_typed_const_refusal;

#[path = "common/below_admission.rs"]
mod below_admission;
use below_admission::{body_below_admission, body_refusal_below_admission};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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

fn single_function(module: &TrustIrModule) -> &TrustIrFunction {
    module
        .functions
        .first()
        .expect("module must have one function")
}

fn bytes_constant_module(ty: Ty, value: Constant, types: Vec<Ty>) -> TrustIrModule {
    single_function_module(
        "nested_bytes",
        FuncTy {
            params: vec![],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![],
        types,
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const { ty, value }).with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    )
}

fn expand_bytes(value: &mut Constant) {
    match value {
        Constant::Bytes { data, .. } => {
            *value = Constant::Array(data.iter().map(|b| Constant::Int(*b as i128)).collect());
        }
        Constant::Aggregate(fields) | Constant::Array(fields) => {
            fields.iter_mut().for_each(expand_bytes);
        }
        _ => {}
    }
}

#[test]
fn nested_bytes_match_interpreter_and_expanded_integer_lowering() {
    let bytes_ty = Ty::Array(TyId::new(0), 3);
    let raw = Constant::Bytes {
        data: vec![0, 0xff, 0x80],
        utf8: false,
    };
    let text = Constant::Bytes {
        data: b"TIR".to_vec(),
        utf8: true,
    };
    let cases = [
        (
            Ty::Tuple(vec![Ty::U16, bytes_ty.clone(), Ty::U64]),
            Constant::Aggregate(vec![
                Constant::Int(0x1234),
                raw.clone(),
                Constant::Int(0x5678),
            ]),
        ),
        (Ty::Array(TyId::new(1), 2), Constant::Array(vec![raw, text])),
        (
            Ty::Tuple(vec![Ty::Array(TyId::new(0), 0), Ty::U8]),
            Constant::Aggregate(vec![
                Constant::Bytes {
                    data: vec![],
                    utf8: true,
                },
                Constant::Int(0xa5),
            ]),
        ),
    ];
    for (ty, value) in cases {
        let module = bytes_constant_module(ty, value, vec![Ty::U8, bytes_ty.clone()]);
        let errors = trust_ir_build::validate_module(&module);
        assert!(
            errors.is_empty(),
            "nested byte constant is valid TrustIR: {errors:?}"
        );
        let mut expanded = module.clone();
        let Inst::Const { value, .. } = &mut expanded.functions[0].blocks[0].body[0].inst else {
            unreachable!()
        };
        expand_bytes(value);
        let errors = trust_ir_build::validate_module(&expanded);
        assert!(
            errors.is_empty(),
            "expanded integer array is valid TrustIR: {errors:?}"
        );
        let expected = trust_ir::Interpreter::with_module(&expanded)
            .execute_func(f(0), [])
            .expect("expanded oracle")
            .returns;
        let actual = trust_ir::Interpreter::with_module(&module)
            .execute_func(f(0), [])
            .expect("bytes oracle")
            .returns;
        assert_eq!(actual, expected, "reference typed values must be identical");
        let (actual, _) = trust_cg_lower::translate_function_with_license(
            single_function(&module),
            &module,
            &permit_unlicensed(),
        )
        .expect("nested byte constants must lower");
        let (expected, _) = trust_cg_lower::translate_function_with_license(
            single_function(&expanded),
            &expanded,
            &permit_unlicensed(),
        )
        .expect("expanded byte arrays must lower");
        assert_eq!(
            actual.blocks[&actual.entry_block].instructions,
            expected.blocks[&expected.entry_block].instructions,
            "byte leaves must use the same layout/stores as explicit U8 arrays"
        );
        assert_eq!(actual.stack_slots, expected.stack_slots);
        assert_eq!(actual.value_types, expected.value_types);
        assert_eq!(
            actual.blocks[&actual.entry_block]
                .instructions
                .iter()
                .filter(|i| matches!(i.opcode, Opcode::StackAddr { .. }))
                .count(),
            1,
            "nested arrays must share the parent's stack allocation"
        );
    }
}

#[test]
fn nested_bytes_reject_malformed_leaf_types_lengths_and_utf8() {
    let cases = [
        (Ty::Array(TyId::new(0), 2), vec![Ty::U8], vec![1], false),
        (Ty::Array(TyId::new(0), 1), vec![Ty::U8], vec![0xff], true),
        (Ty::Array(TyId::new(0), 1), vec![Ty::I8], vec![1], false),
        (Ty::Array(TyId::new(0), 1), vec![Ty::U16], vec![1], false),
        (Ty::Array(TyId::new(9), 1), vec![Ty::U8], vec![1], false),
        (Ty::U8, vec![Ty::U8], vec![1], false),
        (Ty::Tuple(vec![Ty::U8]), vec![Ty::U8], vec![1], false),
    ];
    for (leaf_ty, types, data, utf8) in cases {
        let module = bytes_constant_module(
            Ty::Tuple(vec![leaf_ty]),
            Constant::Aggregate(vec![Constant::Bytes { data, utf8 }]),
            types,
        );
        assert!(
            !trust_ir_build::validate_module(&module).is_empty(),
            "invalid fixture must not validate"
        );
        assert!(
            trust_cg_lower::translate_function_with_license(
                single_function(&module),
                &module,
                &permit_unlicensed()
            )
            .is_err(),
            "adapter must independently reject invalid byte leaves"
        );
    }
}

// ---------------------------------------------------------------------------
// Tests — structs, tuples, arrays
// ---------------------------------------------------------------------------

/// A struct aggregate const with two i64 fields lowers to StackAddr + 2×(Iconst + StructGep + Store).
#[test]
fn struct_aggregate_const_lowers() {
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
    let struct_ty = Ty::Struct(StructId::new(0));

    let module = single_function_module(
        "mk_pair",
        FuncTy {
            params: vec![],
            returns: vec![struct_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        structs,
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: struct_ty.clone(),
                    value: Constant::Aggregate(vec![Constant::Int(7), Constant::Int(42)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must accept struct const");

    // Inspect the entry block's instruction stream.
    let entry = lir_func.entry_block;
    let bb = &lir_func.blocks[&entry];

    let stack_addrs = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StackAddr { .. }))
        .count();
    let struct_geps = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StructGep { .. }))
        .count();
    let stores = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();
    let iconsts = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Iconst { .. }))
        .count();

    assert_eq!(stack_addrs, 1, "one StackAddr for the aggregate slot");
    assert_eq!(struct_geps, 2, "one StructGep per field");
    assert_eq!(stores, 2, "one Store per field");
    assert_eq!(iconsts, 2, "one Iconst per integer field");
}

/// A tuple aggregate const lowers the same way as a struct const.
#[test]
fn tuple_aggregate_const_lowers() {
    let tuple_ty = Ty::Tuple(vec![Ty::I32, Ty::I64, Ty::Bool]);
    let module = single_function_module(
        "mk_tuple",
        FuncTy {
            params: vec![],
            returns: vec![tuple_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: tuple_ty.clone(),
                    value: Constant::Aggregate(vec![
                        Constant::Int(1),
                        Constant::Int(2),
                        Constant::Bool(true),
                    ]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must accept tuple const");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    let struct_geps = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StructGep { .. }))
        .count();
    let stores = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();
    assert_eq!(struct_geps, 3, "three fields → three StructGeps");
    assert_eq!(stores, 3, "three Stores");
}

/// An array aggregate const lowers to ArrayGep per element (not StructGep).
#[test]
fn array_aggregate_const_lowers_via_array_gep() {
    // types[0] = I32, array_ty = [I32; 3]
    let types = vec![Ty::I32];
    let array_ty = Ty::Array(TyId::new(0), 3);

    let module = single_function_module(
        "mk_arr",
        FuncTy {
            params: vec![],
            returns: vec![array_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![],
        types,
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: array_ty.clone(),
                    value: Constant::Aggregate(vec![
                        Constant::Int(10),
                        Constant::Int(20),
                        Constant::Int(30),
                    ]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter must accept array const");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    let array_geps = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::ArrayGep { .. }))
        .count();
    let struct_geps = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StructGep { .. }))
        .count();
    let stores = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();

    assert_eq!(array_geps, 3, "array const uses ArrayGep per element");
    assert_eq!(struct_geps, 0, "array const must not emit StructGep");
    assert_eq!(stores, 3, "three elements → three Stores");
}

/// Nested aggregates (struct-of-struct constants) recurse into the same
/// outer stack slot. Phase 2c of #443 lifts the earlier Phase 2b rejection:
/// the inner aggregate is written through a parent `StructGep` + per-leaf
/// `Store`, with **no nested StackAddr** emitted.
#[test]
fn nested_aggregate_const_lowers_into_one_slot() {
    let structs = vec![StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Wrapper".to_string(),
        fields: vec![FieldDef {
            name: "inner".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
    }];
    let tuple_ty = Ty::Tuple(vec![Ty::Struct(StructId::new(0))]);

    let module = single_function_module(
        "mk_nested",
        FuncTy {
            params: vec![],
            returns: vec![tuple_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        structs,
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: tuple_ty.clone(),
                    value: Constant::Aggregate(vec![Constant::Aggregate(vec![Constant::Int(1)])]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("nested aggregate constants lower in Phase 2c");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    let stack_addrs = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StackAddr { .. }))
        .count();
    let struct_geps = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StructGep { .. }))
        .count();
    let stores = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();
    let iconsts = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Iconst { .. }))
        .count();

    assert_eq!(
        stack_addrs, 1,
        "nested aggregate reuses the outer StackAddr — no nested slot"
    );
    // Outer tuple field + inner struct field = 2 StructGeps.
    assert_eq!(
        struct_geps, 2,
        "one GEP to the tuple field + one GEP to the nested struct field"
    );
    assert_eq!(stores, 1, "one Store at the innermost leaf");
    assert_eq!(iconsts, 1, "one Iconst for the leaf i64 value");
}

/// Deeply nested aggregate: struct { inner: struct { leaf: i64, flag: bool } }
/// must lower into exactly one stack slot with two GEPs per leaf and per-leaf
/// scalar stores.
#[test]
fn deeply_nested_aggregate_const_lowers() {
    let structs = vec![
        StructDef {
            origin: None,
            id: StructId::new(0),
            name: "Leaf".to_string(),
            fields: vec![
                FieldDef {
                    name: "leaf".to_string(),
                    ty: Ty::I64,
                    offset: None,
                },
                FieldDef {
                    name: "flag".to_string(),
                    ty: Ty::Bool,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        },
        StructDef {
            origin: None,
            id: StructId::new(1),
            name: "Outer".to_string(),
            fields: vec![FieldDef {
                name: "inner".to_string(),
                ty: Ty::Struct(StructId::new(0)),
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
        },
    ];
    let outer_ty = Ty::Struct(StructId::new(1));

    let module = single_function_module(
        "mk_deep",
        FuncTy {
            params: vec![],
            returns: vec![outer_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        structs,
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: outer_ty.clone(),
                    value: Constant::Aggregate(vec![Constant::Aggregate(vec![
                        Constant::Int(7),
                        Constant::Bool(true),
                    ])]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("deeply nested aggregate constants lower in Phase 2c");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    let stack_addrs = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StackAddr { .. }))
        .count();
    let stores = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();

    assert_eq!(
        stack_addrs, 1,
        "exactly one StackAddr regardless of nesting depth"
    );
    // Two leaf fields -> two Stores.
    assert_eq!(stores, 2, "two leaves -> two Stores");
}

/// Closure-style aggregate: a struct whose first field is a function pointer
/// (`Ty::Func`) and whose second field is a captured `i64` must lower in
/// Phase 2c — the function pointer is treated as a 64-bit scalar pointer.
#[test]
fn func_ptr_aggregate_const_lowers() {
    // Build a `FuncTy` id for the function-pointer field.
    let mut module = TrustIrModule::new("closure_mod");
    let callee_fty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let closure_fields = vec![
        FieldDef {
            name: "fptr".to_string(),
            ty: Ty::Func(callee_fty),
            offset: None,
        },
        FieldDef {
            name: "env".to_string(),
            ty: Ty::I64,
            offset: None,
        },
    ];
    module.structs = vec![StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Closure".to_string(),
        fields: closure_fields,
        size: None,
        align: None,
        repr: Default::default(),
    }];
    let closure_ty = Ty::Struct(StructId::new(0));
    let sig_id: FuncTyId = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![closure_ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), "mk_closure", sig_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: closure_ty.clone(),
                // A `Ty::Func` field is spelled as the function item it names
                // (`Constant::FnDef`); an integer stand-in address is refused
                // by TrustIR's typed admission.
                value: Constant::Aggregate(vec![Constant::FnDef(f(1)), Constant::Int(42)]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![v(0)] }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    let mut callee = TrustIrFunction::new(f(1), "closure_body", callee_fty, b(0));
    callee.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
    }];
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");

    let mut stand_in = module.clone();
    let Inst::Const { value, .. } = &mut stand_in.functions[0].blocks[0].body[0].inst else {
        panic!("mk_closure opens with its aggregate constant")
    };
    *value = Constant::Aggregate(vec![Constant::Int(0x1000), Constant::Int(42)]);
    let err = trust_cg_lower::translate_function_with_license(
        single_function(&stand_in),
        &stand_in,
        &permit_unlicensed(),
    )
    .expect_err("an integer stand-in at a Ty::Func field must be refused");
    assert_typed_const_refusal(&err, "function 'mk_closure' bb0[0]", "functy.0", "int");

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("func-ptr aggregate constants lower in Phase 2c");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    let stack_addrs = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StackAddr { .. }))
        .count();
    let stores = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();
    let iconsts = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Iconst { .. }))
        .count();

    assert_eq!(
        stack_addrs, 1,
        "closure struct lowers into a single stack slot"
    );
    assert_eq!(stores, 2, "one Store per field (fptr + env)");
    assert_eq!(iconsts, 1, "one Iconst for the Int env field");
    assert_eq!(
        bb.instructions
            .iter()
            .filter(|i| matches!(&i.opcode, Opcode::GlobalRef { name } if name == "closure_body"))
            .count(),
        1,
        "the fptr field materializes the function symbol's address"
    );
}

/// `Ty::Enum` aggregate constants lower as tag plus payload after the #398
/// tagged-union decision.
#[test]
fn enum_aggregate_const_lowers_tagged_union() {
    let enum_ty = Ty::Enum(EnumId::new(0));

    let mut module = single_function_module(
        "mk_enum",
        FuncTy {
            params: vec![],
            returns: vec![enum_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: enum_ty.clone(),
                    value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(42)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    module.enums = vec![EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "OptionI64".to_string(),
        variants: vec![
            EnumVariant {
                name: "None".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Some".to_string(),
                fields: vec![Ty::I64],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    }];

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("enum aggregate lowers");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    let stack_addrs = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StackAddr { .. }))
        .count();
    let stores = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();
    let struct_geps = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StructGep { .. }))
        .count();
    // The payload base is `slot + payload_offset`: a byte-stride address
    // (`ArrayGep { elem_ty: I8 }`, b79533c9c; it was a numeric `Iadd`).
    let byte_offset_addresses = byte_offset_addresses(&bb.instructions);

    assert_eq!(stack_addrs, 1, "one stack slot for the enum storage");
    assert_eq!(stores, 2, "one tag store plus one payload field store");
    assert_eq!(
        struct_geps, 1,
        "payload field address is computed in the payload tuple"
    );
    assert_eq!(
        byte_offset_addresses,
        vec![8],
        "payload base is tag-width aligned to payload offset 8, got {:?}",
        bb.instructions
    );
}

/// The constant byte offsets of every byte-stride address
/// (`ArrayGep { elem_ty: I8 }` over an `Iconst` offset) in `instructions`, in
/// order. An address computed any other way (a numeric `Iadd`, a wider
/// element) is not one, so a regression to either drops it from the list.
fn byte_offset_addresses(instructions: &[trust_cg_lower::instructions::Instruction]) -> Vec<i64> {
    let constants: std::collections::HashMap<_, _> = instructions
        .iter()
        .filter_map(|i| match i.opcode {
            Opcode::Iconst { imm, .. } => i.results.first().map(|r| (*r, imm)),
            _ => None,
        })
        .collect();
    instructions
        .iter()
        .filter(|i| {
            matches!(
                i.opcode,
                Opcode::ArrayGep {
                    elem_ty: trust_cg_lower::types::Type::I8
                }
            )
        })
        .filter_map(|i| {
            i.args
                .get(1)
                .and_then(|offset| constants.get(offset).copied())
        })
        .collect()
}

/// A payloadless enum variant stores only the tag. This covers the other
/// half of the v1 tagged-union representation: variants may have no payload,
/// but their variant identity still reaches memory as the discriminator.
#[test]
fn enum_aggregate_const_payloadless_variant_stores_tag_only() {
    let enum_ty = Ty::Enum(EnumId::new(0));

    let mut module = single_function_module(
        "mk_enum_none",
        FuncTy {
            params: vec![],
            returns: vec![enum_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: enum_ty.clone(),
                    value: Constant::Aggregate(vec![Constant::Int(0)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    module.enums = vec![EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "OptionI64".to_string(),
        variants: vec![
            EnumVariant {
                name: "None".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Some".to_string(),
                fields: vec![Ty::I64],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    }];

    let (lir_func, _proofs) = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect("enum aggregate lowers");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    let stack_addrs = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StackAddr { .. }))
        .count();
    let stores = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();
    let struct_geps = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::StructGep { .. }))
        .count();
    let address_arithmetic = bb
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Iadd | Opcode::ArrayGep { .. }))
        .count();

    assert_eq!(stack_addrs, 1, "one stack slot for the enum storage");
    assert_eq!(stores, 1, "payloadless variant stores only the tag");
    assert_eq!(struct_geps, 0, "no payload fields means no payload GEP");
    assert_eq!(
        address_arithmetic, 0,
        "payload base is not materialised without payload, got {:?}",
        bb.instructions
    );
}

/// Arity mismatch (type says 2 fields, const supplies 1) must be caught early.
#[test]
fn aggregate_const_arity_mismatch_rejected() {
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
    let struct_ty = Ty::Struct(StructId::new(0));

    let module = single_function_module(
        "bad_arity",
        FuncTy {
            params: vec![],
            returns: vec![struct_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        structs,
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: struct_ty.clone(),
                    value: Constant::Aggregate(vec![Constant::Int(1)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );

    let result = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    );
    assert!(
        result.is_err(),
        "arity mismatch between type and Constant::Aggregate must be rejected"
    );
}

/// Trust (B3-3): the enum constant head is the variant's effective
/// DISCRIMINANT VALUE (the trust-ir interpreter contract), not a variant
/// index. On the admitted all-implicit dense fragment the two coincide, so
/// this pins the semantics at the boundary of that coincidence: a head that
/// names NO variant discriminant must be rejected with discriminant wording —
/// the old index-semantics path would instead have compared it against the
/// variant COUNT. TrustIR's typed admission resolves the head first on every
/// codegen entry; the adapter's own resolution is pinned below that
/// admission, naming the discriminants the variants carry.
#[test]
fn enum_aggregate_const_head_resolves_as_discriminant_not_index() {
    let enum_ty = Ty::Enum(EnumId::new(0));

    let mut module = single_function_module(
        "mk_enum_bad_head",
        FuncTy {
            params: vec![],
            returns: vec![enum_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: enum_ty.clone(),
                    // Head 7: names no effective discriminant of a 2-variant
                    // all-implicit enum ({0, 1}).
                    value: Constant::Aggregate(vec![Constant::Int(7)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    module.enums = vec![EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "OptionI64".to_string(),
        variants: vec![
            EnumVariant {
                name: "None".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Some".to_string(),
                fields: vec![Ty::I64],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    }];

    let err = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect_err("a head naming no variant discriminant must fail closed");
    assert_typed_const_refusal(
        &err,
        "function 'mk_enum_bad_head' bb0",
        "a discriminant of enum OptionI64",
        "7",
    );
    assert_eq!(
        body_refusal_below_admission(&module),
        "not lowerable: unsupported trust_ir instruction: Constant::Aggregate for \
         Enum(EnumId(0)) head 7 names no variant discriminant (variants carry [0, 1])"
    );
}

/// Trust (B3-3): a NEGATIVE head fails closed by discriminant resolution
/// (it names no effective discriminant of an all-implicit enum), not by a
/// usize conversion — the old seam died in `usize::try_from` with
/// index-semantics wording before ever consulting the discriminant table.
/// TrustIR's typed admission now resolves the head against the enum's
/// effective discriminants and refuses it before the adapter does; the
/// adapter's own resolution is pinned below that admission.
#[test]
fn enum_aggregate_const_negative_head_fails_by_discriminant_resolution() {
    let enum_ty = Ty::Enum(EnumId::new(0));

    let mut module = single_function_module(
        "mk_enum_neg_head",
        FuncTy {
            params: vec![],
            returns: vec![enum_ty.clone()],
            abi: None,
            is_vararg: false,
        },
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: enum_ty.clone(),
                    value: Constant::Aggregate(vec![Constant::Int(-1)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    module.enums = vec![EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "E".to_string(),
        variants: vec![EnumVariant {
            name: "Only".to_string(),
            fields: vec![],
            field_names: Vec::new(),
        }],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    }];

    let err = trust_cg_lower::translate_function_with_license(
        single_function(&module),
        &module,
        &permit_unlicensed(),
    )
    .expect_err("a negative head naming no discriminant must fail closed");
    assert_typed_const_refusal(
        &err,
        "function 'mk_enum_neg_head' bb0",
        "a discriminant of enum E",
        "-1",
    );
    assert_eq!(
        body_refusal_below_admission(&module),
        "not lowerable: unsupported trust_ir instruction: Constant::Aggregate for \
         Enum(EnumId(0)) head -1 names no variant discriminant (variants carry [0])"
    );
}

/// A scalar constant at a field whose LIR type is an AGGREGATE is refused by
/// name, never lowered to a whole-aggregate `Store`. `Ty::FatPtr` and
/// `Ty::Unit` are not among the trust-ir aggregate spellings the field walk
/// refuses up front, yet both translate to a LIR aggregate (an address in
/// LIR), and the `Bool`/`Float` arms take the field's type unchecked: before
/// this refusal, `Bool(true)` at a `&str` field emitted
/// `Store { ty: Struct([I64, I64]) }` — one register-width write over a
/// 16-byte fat pointer — and at a `()` field a write past a zero-sized lane.
/// TrustIR's typed admission now refuses each spelling at the field's type
/// on every codegen entry; below that admission the field walk's own refusal
/// is pinned by its whole text, and a scalar at a scalar field still lowers.
#[test]
fn scalar_constant_at_an_aggregate_lir_field_is_refused_not_stored_whole() {
    let module_with = |field_ty: &Ty, scalar: &Constant| {
        let tuple_ty = Ty::Tuple(vec![field_ty.clone(), Ty::I64]);
        single_function_module(
            "ill_typed_field_const",
            FuncTy {
                params: vec![],
                returns: vec![tuple_ty.clone()],
                abi: None,
                is_vararg: false,
            },
            vec![],
            vec![],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: tuple_ty,
                        value: Constant::Aggregate(vec![scalar.clone(), Constant::Int(1)]),
                    })
                    .with_result(v(0)),
                    InstrNode::new(Inst::Return { values: vec![v(0)] }),
                ],
            }],
        )
    };
    for (field_ty, scalar, lir_field_ty) in [
        (
            Ty::FatPtr(FatPtrKind::Str),
            Constant::Bool(true),
            "Struct([I64, I64])",
        ),
        (
            Ty::FatPtr(FatPtrKind::Str),
            Constant::Float(1.0),
            "Struct([I64, I64])",
        ),
        (Ty::Unit, Constant::Bool(false), "Struct([])"),
    ] {
        let module = module_with(&field_ty, &scalar);
        let err = trust_cg_lower::translate_function_with_license(
            single_function(&module),
            &module,
            &permit_unlicensed(),
        )
        .expect_err("a scalar constant at an aggregate LIR field must be refused");
        assert_typed_const_refusal(
            &err,
            "function 'ill_typed_field_const' bb0[0]",
            &field_ty.to_string(),
            &scalar.shape_label(),
        );
        assert_eq!(
            body_refusal_below_admission(&module),
            format!(
                "not lowerable: unsupported trust_ir instruction: Constant::Aggregate field 0 of \
                 type {field_ty:?} is the aggregate {lir_field_ty} in LIR, but its constant \
                 {scalar:?} is a scalar; storing it would be a whole-aggregate Store"
            )
        );
    }
    body_below_admission(&module_with(&Ty::Bool, &Constant::Bool(true)))
        .expect("a Bool constant at a Bool field lowers below admission");
}

/// An out-of-range integer at a signed or pointer-width aggregate field. Typed
/// admission refuses it on every codegen entry; below admission the field
/// walk's own range rows (`translate_int_const_into`, which the scalar
/// `translate_int_const` bounds do not cover) refuse it by name, and each
/// row's last in-range value lowers.
#[test]
fn signed_and_pointer_width_field_constants_beyond_their_range_are_refused_below_admission() {
    for (field_ty, beyond, last) in [
        (Ty::I32, u32::MAX as i128 + 1, u32::MAX as i128),
        (Ty::I32, i32::MIN as i128 - 1, i32::MIN as i128),
        (Ty::I64, u64::MAX as i128 + 1, u64::MAX as i128),
        (Ty::I64, i64::MIN as i128 - 1, i64::MIN as i128),
        (Ty::Isize, i64::MAX as i128 + 1, i64::MAX as i128),
        (Ty::Isize, i64::MIN as i128 - 1, i64::MIN as i128),
    ] {
        let tuple_ty = Ty::Tuple(vec![field_ty.clone(), Ty::I64]);
        let module_with = |value: i128| {
            single_function_module(
                "wide_field_const",
                FuncTy {
                    params: vec![],
                    returns: vec![tuple_ty.clone()],
                    abi: None,
                    is_vararg: false,
                },
                vec![],
                vec![],
                vec![TrustIrBlock {
                    id: b(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: tuple_ty.clone(),
                            value: Constant::Aggregate(vec![
                                Constant::Int(value),
                                Constant::Int(1),
                            ]),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Return { values: vec![v(0)] }),
                    ],
                }],
            )
        };
        let module = module_with(beyond);
        assert!(
            trust_cg_lower::translate_function_with_license(
                single_function(&module),
                &module,
                &permit_unlicensed()
            )
            .is_err(),
            "{field_ty:?} {beyond}: typed admission refuses it on the codegen entry"
        );
        let refusal = body_refusal_below_admission(&module);
        assert!(
            refusal.contains(&format!(
                "Constant::Int({beyond}) does not fit in {field_ty:?}"
            )),
            "{field_ty:?} {beyond}: {refusal}"
        );
        body_below_admission(&module_with(last))
            .unwrap_or_else(|e| panic!("{field_ty:?} {last} lowers: {e}"));
    }
}

/// A `u64` static a typed-pointer field may name. TrustIR admits a
/// `SymbolAddr` at `Ref` only for an immutable global, at `PtrMut` only for a
/// mutable one, and at `PtrConst` for either.
fn pointee_global(name: &str, mutable: bool) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::U64,
        mutable,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

/// The aggregate constant that holds a pointer field.
#[derive(Clone, Copy, Debug)]
enum PointerHolder {
    Struct,
    Tuple,
    Array,
    /// Two equal elements, whose one canonical spelling is a splat; the
    /// adapter fills its lane 0 through the same field walk.
    Splat,
}

/// `typed_pointer_field` materializes one `holder` constant whose pointer
/// field has type `field_ty` and holds `address`, and returns nothing.
/// Returns the module and the field index the field walk reports.
fn pointer_field_module(
    holder: PointerHolder,
    field_ty: &Ty,
    address: &Constant,
) -> (TrustIrModule, usize) {
    let (structs, types, ty, value, field) = match holder {
        PointerHolder::Struct => (
            vec![StructDef {
                origin: None,
                id: StructId::new(0),
                name: "Holder".to_string(),
                fields: vec![
                    FieldDef {
                        name: "n".to_string(),
                        ty: Ty::I64,
                        offset: None,
                    },
                    FieldDef {
                        name: "p".to_string(),
                        ty: field_ty.clone(),
                        offset: None,
                    },
                ],
                size: None,
                align: None,
                repr: Default::default(),
            }],
            vec![],
            Ty::Struct(StructId::new(0)),
            Constant::Aggregate(vec![Constant::Int(1), address.clone()]),
            1,
        ),
        PointerHolder::Tuple => (
            vec![],
            vec![],
            Ty::Tuple(vec![Ty::I64, field_ty.clone()]),
            Constant::Aggregate(vec![Constant::Int(1), address.clone()]),
            1,
        ),
        PointerHolder::Array => (
            vec![],
            vec![field_ty.clone()],
            Ty::Array(TyId::new(0), 1),
            Constant::Array(vec![address.clone()]),
            0,
        ),
        PointerHolder::Splat => (
            vec![],
            vec![field_ty.clone()],
            Ty::Array(TyId::new(0), 2),
            Constant::Splat {
                elem: Box::new(address.clone()),
                len: 2,
            },
            0,
        ),
    };
    let mut module = single_function_module(
        "typed_pointer_field",
        FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        },
        structs,
        types,
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const { ty, value }).with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );
    module.globals = vec![
        pointee_global("FROZEN", false),
        pointee_global("CELL", true),
    ];
    (module, field)
}

/// TrustIR admits a `SymbolAddr` at a typed thin pointer (`Ref`, `PtrConst`
/// or `PtrMut` over the type of the module-defined global it names), but the
/// aggregate field walk stores a symbol address only into a `Ty::Ptr` or
/// `Ty::Func` field. A struct, tuple or array constant, a splat included,
/// that holds one at a typed-pointer field therefore passes typed admission
/// and is refused by name after it. The same constant at a `Ty::Ptr` field
/// lowers to one relocated reference. Ruled in docs/decision-record.md,
/// OD-TYPED-ADMISSION-GAPS-20261010.
#[test]
fn symbol_address_at_a_typed_pointer_field_passes_admission_and_is_refused_by_name() {
    for (pointer_ty, symbol, spelled) in [
        (Ty::Ref(Box::new(Ty::U64)), "FROZEN", "Ref(U64)"),
        (Ty::PtrConst(Box::new(Ty::U64)), "FROZEN", "PtrConst(U64)"),
        (Ty::PtrMut(Box::new(Ty::U64)), "CELL", "PtrMut(U64)"),
    ] {
        let address = Constant::SymbolAddr {
            symbol: symbol.to_string(),
            addend: 0,
        };
        for holder in [
            PointerHolder::Struct,
            PointerHolder::Tuple,
            PointerHolder::Array,
            PointerHolder::Splat,
        ] {
            let (module, field) = pointer_field_module(holder, &pointer_ty, &address);
            let errors = trust_ir_build::validate_module(&module);
            assert!(
                errors.is_empty(),
                "{holder:?} at {spelled}: TrustIR admits the constant: {errors:?}"
            );
            let err = trust_cg_lower::translate_function_with_license(
                single_function(&module),
                &module,
                &permit_unlicensed(),
            )
            .expect_err("a symbol address at a typed-pointer field must be refused");
            let AdapterError::UnsupportedInstruction(message) = &err else {
                panic!("{holder:?} at {spelled}: the field walk must refuse it, got {err:?}");
            };
            assert_eq!(
                *message,
                format!(
                    "Constant::SymbolAddr {{ symbol: \"{symbol}\", addend: 0 }} at aggregate \
                     field {field} requires a Ty::Ptr or Ty::Func field, got {spelled}"
                ),
                "{holder:?} at {spelled}"
            );

            let (module, _) = pointer_field_module(holder, &Ty::Ptr, &address);
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{holder:?} at Ptr: {errors:?}");
            let (lir, _) = trust_cg_lower::translate_function_with_license(
                single_function(&module),
                &module,
                &permit_unlicensed(),
            )
            .unwrap_or_else(|err| panic!("{holder:?} at Ptr must lower: {err}"));
            assert_eq!(
                lir.blocks[&lir.entry_block]
                    .instructions
                    .iter()
                    .filter(|i| matches!(&i.opcode, Opcode::GlobalRef { name } if name == symbol))
                    .count(),
                1,
                "{holder:?} at Ptr: one relocated reference to `{symbol}`"
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
