// aggregate_types.rs — aggregate type translation tests (#391)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Aggregate-type translation tests for #391.
//!
//! These tests cover the adapter's extended type translator which now accepts
//! `Ty::Array(TyId, len)`, `Ty::Tuple(Vec<Ty>)`, and `Ty::Enum(EnumId)`.
//! The adapter resolves array `TyId`s via the module's `types` table, flattens
//! tuples to anonymous LIR structs, and resolves enums via the module enum
//! table into the tagged-union representation chosen in #398.
//!
//! Design: `designs/2026-04-18-aggregate-lowering.md`.

use trust_cg_ir::function::EnumTagWidth;
use trust_cg_lower::adapter::{
    AdapterError, translate_type, translate_type_with_structs, translate_type_with_tables,
};
use trust_cg_lower::types::Type;
use trust_ir::{
    Block as TrustIrBlock, BlockId, CallingConv, EnumDef, EnumId, EnumLayoutDescriptor,
    EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, FuncId, FuncTy, Function, Inst, InstrNode,
    Linkage, Module, StructDef, StructId, Ty, TyId, ValueId,
};

// ---------------------------------------------------------------------------
// translate_type_with_tables — direct unit tests
// ---------------------------------------------------------------------------

#[test]
fn array_of_i32_resolves_through_types_table() {
    // types[0] = i32, so Array(TyId(0), 8) -> Array<I32; 8>
    let types = vec![Ty::I32];
    let arr = Ty::Array(TyId::new(0), 8);
    let lir = translate_type_with_tables(&arr, &[], &types).unwrap();
    assert_eq!(lir, Type::Array(Box::new(Type::I32), 8));
    // Size/align sanity-check: 8 * 4 = 32 bytes, align 4.
    assert_eq!(lir.bytes(), 32);
    assert_eq!(lir.align(), 4);
}

#[test]
fn array_length_zero_is_valid() {
    // A zero-length array is legal in trust_ir (e.g., C-style `int[0]`); adapter
    // should not reject it. Downstream size calculations handle zero cleanly
    // (`Array(elem, 0).bytes() == 0`).
    let types = vec![Ty::I64];
    let arr = Ty::Array(TyId::new(0), 0);
    let lir = translate_type_with_tables(&arr, &[], &types).unwrap();
    assert_eq!(lir, Type::Array(Box::new(Type::I64), 0));
    assert_eq!(lir.bytes(), 0);
}

#[test]
fn array_of_f64_preserves_element_type() {
    let types = vec![Ty::F64];
    let arr = Ty::Array(TyId::new(0), 4);
    let lir = translate_type_with_tables(&arr, &[], &types).unwrap();
    assert_eq!(lir, Type::Array(Box::new(Type::F64), 4));
    assert_eq!(lir.bytes(), 32); // 4 * 8
    assert_eq!(lir.align(), 8);
}

#[test]
fn array_with_out_of_range_tyid_errors_cleanly() {
    // types table is empty, so TyId(0) cannot resolve — must not panic.
    let arr = Ty::Array(TyId::new(0), 4);
    let err = translate_type_with_tables(&arr, &[], &[]).unwrap_err();
    match err {
        AdapterError::UnsupportedType(msg) => {
            assert!(msg.contains("Array"), "error msg: {}", msg);
            assert!(msg.contains("out of range"), "error msg: {}", msg);
        }
        other => panic!("expected UnsupportedType, got {:?}", other),
    }
}

#[test]
fn array_length_exceeding_u32_max_is_rejected() {
    // trust_ir's `Ty::Array(TyId, u64)` allows lengths up to `u64::MAX`, but LIR
    // stores array lengths as `u32`. The adapter uses `u32::try_from` to
    // surface oversized lengths as a clean `UnsupportedType` error rather
    // than silently truncating (which a future lossy `as u32` would do).
    let types = vec![Ty::I32];
    let arr = Ty::Array(TyId::new(0), u32::MAX as u64 + 1);
    let err = translate_type_with_tables(&arr, &[], &types).unwrap_err();
    match err {
        AdapterError::UnsupportedType(msg) => {
            assert!(msg.contains("exceeds u32::MAX"), "got: {}", msg);
        }
        other => panic!("expected UnsupportedType, got {:?}", other),
    }
}

#[test]
fn array_of_struct_resolves_recursively() {
    // types[0] = Struct(Point{x:F64, y:F64}); array of 3 points.
    let structs = vec![StructDef {
        id: StructId::new(0),
        name: "Point".to_string(),
        fields: vec![
            FieldDef {
                name: "x".to_string(),
                ty: Ty::F64,
                offset: None,
            },
            FieldDef {
                name: "y".to_string(),
                ty: Ty::F64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }];
    let types = vec![Ty::Struct(StructId::new(0))];
    let arr = Ty::Array(TyId::new(0), 3);
    let lir = translate_type_with_tables(&arr, &structs, &types).unwrap();
    let point = Type::Struct(vec![Type::F64, Type::F64]);
    assert_eq!(lir, Type::Array(Box::new(point), 3));
    // Each Point is 16 bytes (2 × F64), so 3 × 16 = 48.
    assert_eq!(lir.bytes(), 48);
}

#[test]
fn array_of_array_via_nested_tyids() {
    // types[0] = I32 (inner element),
    // types[1] = Array(TyId(0), 4)  (inner Array<I32; 4>).
    // outer = Array(TyId(1), 2) -> Array<Array<I32; 4>; 2>.
    let types = vec![Ty::I32, Ty::Array(TyId::new(0), 4)];
    let outer = Ty::Array(TyId::new(1), 2);
    let lir = translate_type_with_tables(&outer, &[], &types).unwrap();
    let inner = Type::Array(Box::new(Type::I32), 4);
    assert_eq!(lir, Type::Array(Box::new(inner), 2));
    assert_eq!(lir.bytes(), 32); // 2 × (4 × 4)
}

#[test]
fn empty_tuple_maps_to_empty_struct() {
    let t = Ty::Tuple(vec![]);
    let lir = translate_type(&t).unwrap();
    assert_eq!(lir, Type::Struct(vec![]));
    assert_eq!(lir.bytes(), 0);
}

#[test]
fn tuple_of_scalars_maps_to_struct() {
    // (i32, bool, f64) — bool is B1 in LIR.
    let t = Ty::Tuple(vec![Ty::I32, Ty::Bool, Ty::F64]);
    let lir = translate_type(&t).unwrap();
    assert_eq!(lir, Type::Struct(vec![Type::I32, Type::B1, Type::F64]));
}

#[test]
fn tuple_of_mixed_sizes_has_c_padding() {
    // (i8, i64) — expect padding between i8 and i64 (7 bytes), total 16, align 8.
    let t = Ty::Tuple(vec![Ty::I8, Ty::I64]);
    let lir = translate_type(&t).unwrap();
    assert_eq!(lir, Type::Struct(vec![Type::I8, Type::I64]));
    assert_eq!(lir.bytes(), 16);
    assert_eq!(lir.align(), 8);
    // offset_of must reflect alignment.
    assert_eq!(lir.offset_of(0), Some(0));
    assert_eq!(lir.offset_of(1), Some(8));
}

#[test]
fn tuple_of_tuples_nests_correctly() {
    let t = Ty::Tuple(vec![Ty::Tuple(vec![Ty::I32, Ty::I32]), Ty::F64]);
    let lir = translate_type(&t).unwrap();
    assert_eq!(
        lir,
        Type::Struct(vec![Type::Struct(vec![Type::I32, Type::I32]), Type::F64,])
    );
}

#[test]
fn tuple_of_array_resolves_through_types_table() {
    // Tuple elements are inline Tys, but an Array element inside the tuple
    // still needs the types table.
    let types = vec![Ty::U8];
    let t = Ty::Tuple(vec![Ty::I32, Ty::Array(TyId::new(0), 4)]);
    let lir = translate_type_with_tables(&t, &[], &types).unwrap();
    assert_eq!(
        lir,
        Type::Struct(vec![
            Type::I32,
            Type::Array(Box::new(Type::I8), 4), // U8 normalises to I8
        ])
    );
}

#[test]
fn struct_containing_array_field_resolves() {
    // Regression for design-doc Gap B: struct fields that contain arrays
    // previously failed to lower because the adapter rejected Ty::Array.
    let structs = vec![StructDef {
        id: StructId::new(0),
        name: "Buf".to_string(),
        fields: vec![
            FieldDef {
                name: "len".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "data".to_string(),
                ty: Ty::Array(TyId::new(0), 16),
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }];
    let types = vec![Ty::U8];
    let lir = translate_type_with_tables(&Ty::Struct(StructId::new(0)), &structs, &types).unwrap();
    assert_eq!(
        lir,
        Type::Struct(vec![Type::I64, Type::Array(Box::new(Type::I8), 16),])
    );
    // Layout: i64 (8) + [u8; 16] (16), aligned to 8. 8 + 16 = 24.
    assert_eq!(lir.bytes(), 24);
}

#[test]
fn direct_enum_type_requires_enum_table() {
    // `translate_type` has no module enum table, so an enum id cannot be
    // resolved through this back-compat wrapper. Full function/module
    // translation provides the table and is covered below.
    let e = Ty::Enum(EnumId::new(0));
    assert!(translate_type(&e).is_err());
}

#[test]
fn translate_type_with_structs_still_rejects_array() {
    // The back-compat wrapper passes an empty types slice, so Array must
    // continue to error (matches pre-Phase-2a semantics).
    let structs: Vec<StructDef> = vec![];
    let arr = Ty::Array(TyId::new(0), 4);
    assert!(translate_type_with_structs(&arr, &structs).is_err());
}

// ---------------------------------------------------------------------------
// Integration tests — translate a full function whose signature contains
// Array / Tuple types, exercising the adapter end-to-end.
// ---------------------------------------------------------------------------

/// Build a trust_ir function `fn id(x: Ptr) -> Ptr` so we can verify aggregate
/// parameter/return types flow through `translate_signature` without
/// failing at signature translation.
fn make_identity_function(params: Vec<Ty>, returns: Vec<Ty>) -> Module {
    let mut module = Module::new("aggregate_sig_test");
    let ft = FuncTy {
        params: params.clone(),
        returns,
        is_vararg: false,
    };
    let ft_id = module.add_func_type(ft);

    // One block with params matching the function params, returning the first
    // param unchanged. We use `Ty::Ptr` for inputs to avoid needing an aggregate
    // value in the body — the signature types themselves are what we're testing.
    let entry = BlockId::new(0);
    let v0 = ValueId::new(0);
    let block = TrustIrBlock {
        id: entry,
        params: params
            .iter()
            .enumerate()
            .map(|(i, t)| (ValueId::new(i as u32), t.clone()))
            .collect(),
        body: vec![InstrNode {
            inst: Inst::Return { values: vec![v0] },
            results: vec![],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }],
    };

    let mut func = Function::new(FuncId::new(0), "id", ft_id, entry);
    func.linkage = Linkage::External;
    func.calling_conv = CallingConv::C;
    func.blocks = vec![block];
    module.add_function(func);
    module
}

#[test]
fn function_with_array_param_translates_through_signature() {
    // fn f(a: [i32; 4]) -> [i32; 4] — types[0] = i32, param/return = Array(TyId(0), 4).
    let mut module = make_identity_function(
        vec![Ty::Array(TyId::new(0), 4)],
        vec![Ty::Array(TyId::new(0), 4)],
    );
    // Register the element type in the module's types table.
    module.types.push(Ty::I32);

    let results = trust_cg_lower::adapter::translate_module(&module).unwrap();
    assert_eq!(results.len(), 1);
    let (func, _proofs) = &results[0];
    let expected = Type::Array(Box::new(Type::I32), 4);
    assert_eq!(func.signature.params, vec![expected.clone()]);
    assert_eq!(func.signature.returns, vec![expected]);
}

#[test]
fn function_with_tuple_param_translates_through_signature() {
    // fn f((i32, f64)) -> (i32, f64).
    let tup = Ty::Tuple(vec![Ty::I32, Ty::F64]);
    let module = make_identity_function(vec![tup.clone()], vec![tup]);
    let results = trust_cg_lower::adapter::translate_module(&module).unwrap();
    let (func, _proofs) = &results[0];
    let expected = Type::Struct(vec![Type::I32, Type::F64]);
    assert_eq!(func.signature.params, vec![expected.clone()]);
    assert_eq!(func.signature.returns, vec![expected]);
}

#[test]
fn function_with_tuple_of_array_param_translates() {
    // fn f((i32, [u8; 8])) -> (i32, [u8; 8]).
    let mut module = make_identity_function(
        vec![Ty::Tuple(vec![Ty::I32, Ty::Array(TyId::new(0), 8)])],
        vec![Ty::Tuple(vec![Ty::I32, Ty::Array(TyId::new(0), 8)])],
    );
    module.types.push(Ty::U8);

    let results = trust_cg_lower::adapter::translate_module(&module).unwrap();
    let (func, _proofs) = &results[0];
    let expected = Type::Struct(vec![Type::I32, Type::Array(Box::new(Type::I8), 8)]);
    assert_eq!(func.signature.params, vec![expected]);
}

#[test]
fn typed_record_state_pointer_params_preserve_pointee_metadata() {
    let state_struct_id = StructId::new(0);
    let state_ty = Ty::Struct(state_struct_id);
    let mut module = make_identity_function(
        vec![
            Ty::Ptr,
            Ty::PtrConst(Box::new(state_ty.clone())),
            Ty::PtrMut(Box::new(state_ty)),
            Ty::I32,
        ],
        vec![Ty::Ptr],
    );
    module.structs = vec![StructDef {
        id: state_struct_id,
        name: "RecordState".to_string(),
        fields: vec![
            FieldDef {
                name: "pc".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "counter".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "owner".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }];

    let results = trust_cg_lower::adapter::translate_module(&module).unwrap();
    let (func, _proofs) = &results[0];
    let record_state = Type::Struct(vec![Type::I64, Type::I64, Type::I64]);

    assert_eq!(
        func.signature.params,
        vec![Type::I64, Type::I64, Type::I64, Type::I32],
        "typed state pointers must keep today's scalar pointer ABI"
    );
    let entry = func.blocks.get(&func.entry_block).unwrap();
    let entry_param_tys: Vec<_> = entry.params.iter().map(|(_, ty)| ty.clone()).collect();
    assert_eq!(
        entry_param_tys,
        vec![Type::I64, Type::I64, Type::I64, Type::I32]
    );
    assert_eq!(func.param_pointee_types.len(), 2);
    assert_eq!(func.param_pointee_types[0].param_index, 1);
    assert_eq!(&func.param_pointee_types[0].pointee_ty, &record_state);
    assert_eq!(func.param_pointee_types[1].param_index, 2);
    assert_eq!(&func.param_pointee_types[1].pointee_ty, &record_state);
}

#[test]
fn function_with_enum_param_translates_through_signature() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let mut module = make_identity_function(vec![enum_ty.clone()], vec![enum_ty]);
    module.enums = vec![EnumDef {
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
                field_names: vec!["value".to_string()],
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    }];

    let results = trust_cg_lower::adapter::translate_module(&module).unwrap();
    let (func, _proofs) = &results[0];
    let expected = Type::Enum {
        tag_width: EnumTagWidth::U8,
        variants: vec![vec![], vec![Type::I64]],
    };
    assert_eq!(func.signature.params, vec![expected.clone()]);
    assert_eq!(func.signature.returns, vec![expected]);
}

#[test]
fn enum_with_producer_layout_fails_closed() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let mut module = make_identity_function(vec![enum_ty.clone()], vec![enum_ty]);
    module.enums = vec![EnumDef {
        id: EnumId::new(0),
        name: "LayoutOptionI64".to_string(),
        variants: vec![
            EnumVariant {
                name: "None".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Some".to_string(),
                fields: vec![Ty::I64],
                field_names: vec!["value".to_string()],
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 0 },
            size: 16,
            align: 8,
            variant_field_offsets: vec![vec![], vec![8]],
        }),
    }];

    // THIS FIXTURE AGREES WITH THE CANONICAL LAYOUT, and is therefore ACCEPTED.
    // Canonical for 2 variants: tag U8 at offset 0, payload aligned to 8 (the
    // I64 field), so payload starts at byte 8, size rounds to 16, align 8 —
    // exactly what the descriptor above declares. Emitting the canonical shape
    // IS emitting the declared one, so refusing would cost coverage and buy
    // nothing.
    //
    // This assertion used to require a REFUSAL. That pinned the blanket
    // "any producer layout is unsupported" behaviour rather than the fail-closed
    // property, which is about DISAGREEMENT and is exercised by
    // `enum_semantics_that_canonical_lowering_does_not_honor_fail_closed` below
    // (tag_offset 4) and by the divergent case immediately following.
    trust_cg_lower::adapter::translate_module(&module)
        .expect("a producer layout that AGREES with the canonical one must be accepted");

    // ...and the same enum with ONE byte moved is still refused, naming the axis.
    let mut divergent = module.clone();
    if let Some(layout) = divergent.enums[0].layout.as_mut() {
        layout.variant_field_offsets = vec![vec![], vec![12]];
    }
    match trust_cg_lower::adapter::translate_module(&divergent)
        .expect_err("a producer layout that DISAGREES must not be synthesized away")
    {
        AdapterError::UnsupportedType(msg) => {
            assert!(msg.contains("EnumDef.layout"), "must name the field: {msg}");
            assert!(msg.contains("LayoutOptionI64"), "must name the enum: {msg}");
            assert!(
                msg.contains("variant 1 field 0 at byte 12"),
                "must name the offending offset: {msg}"
            );
        }
        other => panic!("expected UnsupportedType, got {other:?}"),
    }
}

#[test]
fn enum_semantics_that_canonical_lowering_does_not_honor_fail_closed() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let canonical = EnumDef {
        id: EnumId::new(0),
        name: "ExplicitOptionI64".to_string(),
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
    };

    let mut with_layout = canonical.clone();
    with_layout.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 4 },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![], vec![8]],
    });
    let mut with_discriminants = canonical.clone();
    with_discriminants.discriminants = vec![Some(7), Some(11)];
    // A SIGNED repr. `U16` used to belong here, but a wider-than-minimum
    // UNSIGNED tag is no longer an unsupported semantic — it is the ordinary
    // shape rustc produces when it pads an enum's tag out to the payload's
    // alignment (a two-variant `Option<Box<T>>` declares an eight-byte tag), and
    // the adapter now takes the producer's width instead of deriving one. What
    // remains genuinely unsupported is SIGNEDNESS: the canonical tag lane is
    // unsigned, so an `iN` repr states an intent it would silently mis-serve.
    let mut with_repr = canonical;
    with_repr.repr = Some(EnumTagRepr::I8);

    for (unsupported_field, enum_def) in [
        ("EnumDef.layout", with_layout),
        ("EnumDef.discriminants", with_discriminants),
        ("EnumDef.repr", with_repr),
    ] {
        let mut module = make_identity_function(vec![enum_ty.clone()], vec![enum_ty.clone()]);
        module.enums = vec![enum_def];

        match trust_cg_lower::adapter::translate_module(&module).unwrap_err() {
            AdapterError::UnsupportedType(msg) => assert!(
                msg.contains(unsupported_field),
                "{unsupported_field} rejection must name the unsupported semantic field: {msg}"
            ),
            other => {
                panic!("{unsupported_field} must fail closed as UnsupportedType, got {other:?}")
            }
        }
    }
}

#[test]
fn function_with_array_returns_error_when_types_table_missing() {
    // Adapter must surface a clean error (not panic) when the types table
    // is missing an entry for an Array(TyId).
    let module = make_identity_function(
        vec![Ty::Array(TyId::new(0), 4)],
        vec![Ty::Array(TyId::new(0), 4)],
    );
    // Intentionally don't push to module.types — leave it empty.
    let result = trust_cg_lower::adapter::translate_module(&module);
    assert!(result.is_err(), "expected error for unresolvable TyId");
    match result.unwrap_err() {
        AdapterError::UnsupportedType(msg) => {
            assert!(msg.contains("Array"), "msg={}", msg);
        }
        other => panic!("expected UnsupportedType, got {:?}", other),
    }
}
