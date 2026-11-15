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

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::assert_typed_const_refusal;

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
        origin: None,
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
        origin: None,
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
        abi: None,
        is_vararg: false,
    };
    let ft_id = module
        .add_func_type(ft)
        .expect("Module::add_func_type: test fixture");

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
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
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

    let results = permit_translate_module(&module).unwrap();
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
    let results = permit_translate_module(&module).unwrap();
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

    let results = permit_translate_module(&module).unwrap();
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
        origin: None,
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

    let results = permit_translate_module(&module).unwrap();
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
                field_names: vec!["value".to_string()],
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    }];

    let results = permit_translate_module(&module).unwrap();
    let (func, _proofs) = &results[0];
    let expected = Type::Enum {
        tag_width: EnumTagWidth::U8,
        variants: vec![vec![], vec![Type::I64]],
    };
    assert_eq!(func.signature.params, vec![expected.clone()]);
    assert_eq!(func.signature.returns, vec![expected]);
}

#[test]
fn enum_with_producer_layout_is_carried_at_its_declared_bytes() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let mut module = make_identity_function(vec![enum_ty.clone()], vec![enum_ty]);
    module.enums = vec![EnumDef {
        origin: None,
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

    // THIS FIXTURE AGREES WITH THE CANONICAL LAYOUT: tag U8 at offset 0, the
    // I64 payload at byte 8, size 16, align 8 — exactly what the descriptor
    // declares. Emitting the canonical shape IS emitting the declared one, so
    // the carrier stays `Type::Enum`, the encoding every canonical projection
    // reads.
    let results = permit_translate_module(&module)
        .expect("a producer layout that AGREES with the canonical one must be accepted");
    assert_eq!(
        results[0].0.signature.params[0],
        Type::Enum {
            tag_width: EnumTagWidth::U8,
            variants: vec![vec![], vec![Type::I64]],
        }
    );

    // A DIFFERENT producer layout is no longer refused (L05-P5): the enum is
    // carried at exactly the declared size and alignment, addressed from the
    // descriptor at every access site, and never as the canonical `Type::Enum`
    // whose bytes it does not have.
    let mut padded = module.clone();
    if let Some(layout) = padded.enums[0].layout.as_mut() {
        layout.size = 24;
        layout.variant_field_offsets = vec![vec![], vec![16]];
    }
    let results = permit_translate_module(&padded)
        .expect("a producer layout the canonical shape does not reproduce is carried as declared");
    let carrier = &results[0].0.signature.params[0];
    assert_eq!(
        *carrier,
        Type::Struct(vec![Type::Array(Box::new(Type::I64), 3)]),
        "the byte-image carrier of the declared 24/8"
    );
    assert_eq!((carrier.bytes(), carrier.align()), (24, 8));

    // ...and a descriptor that places a field OUTSIDE its own image is still
    // refused by TrustIR's typed admission, naming the enum, the field and the
    // offending offset.
    let mut divergent = module.clone();
    if let Some(layout) = divergent.enums[0].layout.as_mut() {
        layout.variant_field_offsets = vec![vec![], vec![12]];
    }
    let err = permit_translate_module(&divergent)
        .expect_err("a field past the declared size must not be synthesized away");
    assert_typed_const_refusal(
        &err,
        "enum.0 (LayoutOptionI64) layout",
        "variant 1 field 0 entirely within size 16",
        "offset 12, field size 8",
    );
}

/// A v37 tag-free image must NEVER become TrustCg's tag-CARRYING `Type::Enum`.
/// That invariant is unchanged; what changed is the ALTERNATIVE.
///
/// CORRECTION, kept rather than silently replaced: this test used to require a
/// REFUSAL, and its own name said why — "until LIR has a tag-free carrier".
/// That was the honest answer while TrustCg had none, but refusing the TYPE
/// killed every signature, alloca, load, store and constant mentioning the
/// enum, which is not fail-closed so much as lost coverage. There is now a
/// carrier (`untagged_enum_carrier`, pinned end-to-end in
/// `tests/untagged_enum_carrier.rs`): an untagged enum IS its sole variant's
/// payload, admitted only by EQUALITY against the producer's own declared
/// size, align and offsets. The assertion moves with the behaviour, and the
/// invariant it was really about is asserted directly below.
#[test]
fn an_untagged_layout_lowers_to_its_payload_never_to_a_tag_carrying_enum() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let mut module = make_identity_function(vec![enum_ty.clone()], vec![enum_ty]);
    module.enums = vec![EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "TagFreeI64".to_string(),
        variants: vec![EnumVariant {
            name: "Only".to_string(),
            fields: vec![Ty::I64],
            field_names: vec!["value".to_string()],
        }],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![0]],
        }),
    }];

    let results = permit_translate_module(&module)
        .expect("an untagged descriptor whose payload reproduces it must be admitted");
    let param = &results[0].0.signature.params[0];
    assert!(
        !matches!(param, Type::Enum { .. }),
        "a tag-free image must not become CG's tag-carrying Type::Enum: {param:?}"
    );
    assert_eq!(
        *param,
        Type::Struct(vec![Type::I64]),
        "it is the sole variant's payload, at the producer's declared 8/8"
    );
    assert_eq!((param.bytes(), param.align()), (8, 8));

    // ...and the same descriptor with the SIZE moved is still refused, naming
    // its own encoding rather than borrowing the canonical-layout message.
    let mut divergent = module.clone();
    if let Some(layout) = divergent.enums[0].layout.as_mut() {
        layout.size = 16;
    }
    match permit_translate_module(&divergent)
        .expect_err("a carrier that misses the declared size must not be synthesized away")
    {
        AdapterError::UnsupportedType(msg) => {
            assert!(
                msg.contains("EnumDef.layout"),
                "must name the authority: {msg}"
            );
            assert!(msg.contains("UNTAGGED"), "must name the encoding: {msg}");
            assert!(
                msg.contains("has size 8, the descriptor declares size 16"),
                "must name the axis and both numbers: {msg}"
            );
        }
        other => panic!("expected UnsupportedType, got {other:?}"),
    }
}

/// Richer enum semantics lower through trust-ir's own tables (L05-P5):
/// explicit discriminants that are not the variant index, a SIGNED repr, and a
/// producer layout the canonical shape does not reproduce. What trust-ir itself
/// cannot name still fails closed, naming the field.
#[test]
fn richer_enum_semantics_lower_through_trust_ir_tables() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let canonical = EnumDef {
        origin: None,
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
    let lower = |enum_def: EnumDef| {
        let mut module = make_identity_function(vec![enum_ty.clone()], vec![enum_ty.clone()]);
        module.enums = vec![enum_def];
        permit_translate_module(&module).map(|results| results[0].0.signature.params[0].clone())
    };
    let canonical_carrier = Type::Enum {
        tag_width: EnumTagWidth::U8,
        variants: vec![vec![], vec![Type::I64]],
    };

    // A tag at byte 4 (a u8, 1-aligned) with the payload at 8: a valid 16/8
    // producer image the canonical shape (tag at 0) does not reproduce.
    let mut with_layout = canonical.clone();
    with_layout.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 4 },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![], vec![8]],
    });
    assert_eq!(
        lower(with_layout).expect("a producer layout is carried at its declared bytes"),
        Type::Struct(vec![Type::Array(Box::new(Type::I64), 2)])
    );

    // Explicit discriminants 7 and 11: the lane still fits a u8, and the VALUES
    // are what the tag word carries (`Constant::Aggregate` writes them, `Switch`
    // cases compare against them), never the index.
    let mut with_discriminants = canonical.clone();
    with_discriminants.discriminants = vec![Some(7), Some(11)];
    assert_eq!(
        lower(with_discriminants).expect("explicit discriminants lower"),
        canonical_carrier
    );

    // A SIGNED repr takes the same-width lane; signedness belongs to the reads
    // and compares that consume the tag, exactly as for any other `i8` value.
    let mut with_repr = canonical.clone();
    with_repr.repr = Some(EnumTagRepr::I8);
    with_repr.discriminants = vec![Some(-1), Some(1)];
    assert_eq!(
        lower(with_repr).expect("a signed repr lowers"),
        canonical_carrier
    );

    // Still refused, naming what trust-ir cannot resolve: duplicate
    // discriminants, a repr too narrow for its values and a descriptor whose
    // field overlaps its tag word are refused by TrustIR's typed admission; a
    // 128-bit lane passes that admission and is refused by the adapter.
    let mut duplicate = canonical.clone();
    duplicate.discriminants = vec![Some(7), Some(7)];
    let mut narrow = canonical.clone();
    narrow.repr = Some(EnumTagRepr::U8);
    narrow.discriminants = vec![Some(0), Some(300)];
    let mut wide = canonical.clone();
    wide.repr = Some(EnumTagRepr::I128);
    let mut overlapping = canonical.clone();
    overlapping.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 8 },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![], vec![8]],
    });
    for (location, expected, actual, enum_def) in [
        (
            "enum.0 (ExplicitOptionI64)",
            "resolvable, duplicate-free discriminant assignment",
            "ill-formed discriminants",
            duplicate,
        ),
        (
            "enum.0 (ExplicitOptionI64)",
            "a canonical tag repr (non-empty, values fit the hint and the 64-bit cap)",
            "no canonical tag",
            narrow,
        ),
        (
            "enum.0 (ExplicitOptionI64) layout",
            "a direct tag disjoint from every non-ZST field",
            "tag overlaps variant 1 field 0",
            overlapping,
        ),
    ] {
        let err = lower(enum_def).expect_err("must fail closed");
        assert_typed_const_refusal(&err, location, expected, actual);
    }
    match lower(wide).expect_err("a 128-bit tag lane must fail closed") {
        AdapterError::UnsupportedType(msg) => assert!(
            msg.contains("128-bit") && msg.contains("ExplicitOptionI64"),
            "the rejection must name the semantic and the enum: {msg}"
        ),
        other => panic!("a 128-bit tag lane must fail closed as UnsupportedType, got {other:?}"),
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
    let result = permit_translate_module(&module);
    assert!(result.is_err(), "expected error for unresolvable TyId");
    match result.unwrap_err() {
        AdapterError::UnsupportedType(msg) => {
            assert!(msg.contains("Array"), "msg={}", msg);
        }
        other => panic!("expected UnsupportedType, got {:?}", other),
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

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
