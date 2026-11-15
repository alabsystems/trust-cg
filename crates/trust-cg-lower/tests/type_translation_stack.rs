// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Public type-translation controls for scalar/recursive frame separation.
//! The small-stack test measures the actual public helper, not a replica of
//! its match. The other controls pin carrier, admission and refusal behavior;
//! none of these tests grants semantic or native proof authority.

use trust_cg_ir::function::EnumTagWidth;
use trust_cg_lower::adapter::{
    AdapterError, translate_type, translate_type_in_module, translate_type_with_tables,
};
use trust_cg_lower::types::Type;
use trust_ir::ty::{DialectTy, FatPtrKind, TypeOrigin};
use trust_ir::{
    ClosureLayoutDescriptor, ClosureTy, ClosureTyId, EnumDef, EnumId, EnumVariant, FieldDef,
    FuncTyId, Module, PredId, RecordDef, RecordId, SetRepr, StructDef, StructId, StructRepr, Ty,
    TyId,
};

fn scalar_cases() -> Vec<(Ty, Type)> {
    vec![
        (Ty::Bool, Type::B1),
        (Ty::I8, Type::I8),
        (Ty::U8, Type::I8),
        (Ty::I16, Type::I16),
        (Ty::U16, Type::I16),
        (Ty::I32, Type::I32),
        (Ty::U32, Type::I32),
        (Ty::I64, Type::I64),
        (Ty::U64, Type::I64),
        (Ty::I128, Type::I128),
        (Ty::U128, Type::I128),
        (Ty::F16, Type::F16),
        (Ty::F32, Type::F32),
        (Ty::F64, Type::F64),
        (Ty::Isize, Type::I64),
        (Ty::Usize, Type::I64),
        (Ty::Char, Type::I32),
        (Ty::Ptr, Type::I64),
        (Ty::Func(FuncTyId::new(17)), Type::I64),
        (Ty::Unit, Type::Struct(vec![])),
        (
            Ty::FatPtr(FatPtrKind::Str),
            Type::Struct(vec![Type::I64, Type::I64]),
        ),
        (
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(19))),
            Type::Struct(vec![Type::I64, Type::I64]),
        ),
    ]
}

fn pointers(pointee: Ty) -> [Ty; 4] {
    [
        Ty::Ref(Box::new(pointee.clone())),
        Ty::RefMut(Box::new(pointee.clone())),
        Ty::PtrConst(Box::new(pointee.clone())),
        Ty::PtrMut(Box::new(pointee)),
    ]
}

#[test]
fn public_scalar_and_pointer_translation_runs_on_a_256_kib_stack() {
    let mut cases = scalar_cases();
    for pointee in [Ty::U64, Ty::Struct(StructId::new(71))] {
        cases.extend(pointers(pointee).into_iter().map(|ty| (ty, Type::I64)));
    }
    // Build the inputs outside the measured stack. No aggregate table is
    // expanded by a pointer, including a named pointee absent from the tables.
    std::thread::Builder::new()
        .name("type-translation-small-stack".into())
        .stack_size(256 << 10)
        .spawn(move || {
            for _ in 0..128 {
                for (ty, expected) in &cases {
                    assert_eq!(translate_type(ty).unwrap(), *expected, "{ty:?}");
                }
                assert!(matches!(
                    translate_type(&Ty::Never),
                    Err(AdapterError::VoidValue)
                ));
            }
        })
        .expect("spawn the explicitly bounded thread")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

fn structure(id: u32, fields: Vec<Ty>) -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(id),
        name: format!("Structure{id}"),
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: format!("field{i}"),
                ty,
                offset: None,
            })
            .collect(),
        size: None,
        align: None,
        repr: StructRepr::C,
    }
}

#[test]
fn recursive_tables_preserve_field_order_and_exact_carriers() {
    let mut module = Module::new("type_translation_frames");
    module.types = vec![Ty::U64];
    module.structs = vec![structure(41, vec![Ty::U8, Ty::I64])];
    module.records = vec![RecordDef {
        id: RecordId::new(7),
        name: "SparseRecord".into(),
        fields: vec![
            FieldDef {
                name: "first".into(),
                ty: Ty::U32,
                offset: None,
            },
            FieldDef {
                name: "second".into(),
                ty: Ty::I16,
                offset: None,
            },
        ],
    }];
    module.closure_types = vec![ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::Ptr, Ty::U32, Ty::Array(TyId::new(0), 3)],
    }];
    module.enums = vec![EnumDef::new(
        EnumId::new(17),
        "SparseEnum",
        vec![
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Some".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
        ],
    )];
    let before = module.clone();
    for (ty, expected) in [
        (
            Ty::Struct(StructId::new(41)),
            Type::Struct(vec![Type::I8, Type::I64]),
        ),
        (
            Ty::Record(RecordId::new(7)),
            Type::Struct(vec![Type::I32, Type::I16]),
        ),
        (
            Ty::Closure(ClosureTyId::new(0)),
            Type::Struct(vec![
                Type::I64,
                Type::I32,
                Type::Array(Box::new(Type::I64), 3),
            ]),
        ),
        (
            Ty::Enum(EnumId::new(17)),
            Type::Enum {
                tag_width: EnumTagWidth::U8,
                variants: vec![vec![], vec![Type::I64]],
            },
        ),
        (
            Ty::Tuple(vec![
                Ty::Struct(StructId::new(41)),
                Ty::Array(TyId::new(0), 2),
            ]),
            Type::Struct(vec![
                Type::Struct(vec![Type::I8, Type::I64]),
                Type::Array(Box::new(Type::I64), 2),
            ]),
        ),
    ] {
        assert_eq!(
            translate_type_in_module(&module, &ty).unwrap(),
            expected,
            "{ty:?}"
        );
    }
    assert_eq!(
        module, before,
        "translation never rewrites nominal source types"
    );
}

#[test]
fn inline_pointer_guards_keep_handle_identity_and_dialect_precedence() {
    let dialect = Ty::Dialect(Box::new(DialectTy::new("Example", "Value", 3)));
    for runtime in ["trust_bignum::Nat", "other_runtime::Nat"] {
        let handle = Ty::handle("Nat", runtime);
        for pointer in pointers(handle.clone()) {
            let error = translate_type(&pointer).unwrap_err();
            assert!(matches!(
                error,
                AdapterError::OpaqueHandleNotAdmitted { name, runtime: actual, location, .. }
                    if name == "Nat" && actual == runtime && location == format!("pointee of {pointer:?}")
            ));
        }
        for pointer in pointers(Ty::Tuple(vec![handle, dialect.clone()])) {
            let error = translate_type(&pointer).unwrap_err();
            assert!(matches!(
                error,
                AdapterError::UnsupportedType(message)
                    if message == format!("pointer to an unlegalized dialect type has no Core representation: {pointer:?}")
            ));
        }
    }
}

#[test]
fn opaque_handles_remain_transport_only_at_the_same_depth() {
    let handle = Ty::handle("Nat", "trust_bignum::Nat");
    // A carrier is not authorization to forge or execute a runtime handle.
    assert_eq!(translate_type(&handle).unwrap(), Type::I64);
    let arrays = [handle.clone()];
    for ty in [Ty::Tuple(vec![handle.clone()]), Ty::Array(TyId::new(0), 1)] {
        assert!(matches!(
            translate_type_with_tables(&ty, &[], &arrays).unwrap_err(),
            AdapterError::OpaqueHandleNotAdmitted { name, runtime, location, .. }
                if name == "Nat" && runtime == "trust_bignum::Nat" && location == "an interior type position"
        ));
    }
    let vector = Ty::Vector(Box::new(handle), 2);
    assert!(matches!(
        translate_type(&vector).unwrap_err(),
        AdapterError::OpaqueHandleNotAdmitted { location, .. } if location == "lane type of Vector(_, 2)"
    ));
}

fn array_chain(leaf_depth: u32) -> Vec<Ty> {
    (0..leaf_depth)
        .map(|index| {
            if index + 1 == leaf_depth {
                Ty::U64
            } else {
                Ty::Array(TyId::new(index + 1), 1)
            }
        })
        .collect()
}

#[test]
fn the_original_128_depth_boundary_still_counts_each_actual_child_once() {
    let root = Ty::Array(TyId::new(0), 1);
    let accepted = translate_type_with_tables(&root, &[], &array_chain(127)).unwrap();
    let mut carrier = &accepted;
    for _ in 0..127 {
        let Type::Array(element, 1) = carrier else {
            panic!("every actual array edge is retained")
        };
        carrier = element;
    }
    assert_eq!(*carrier, Type::I64);
    let error = translate_type_with_tables(&root, &[], &array_chain(128)).unwrap_err();
    assert!(matches!(
        error,
        AdapterError::UnsupportedType(message)
            if message == "type graph exceeds the adapter recursion limit (128); possible cyclic type-table reference near U64"
    ));
}

#[test]
fn cyclic_dangling_and_oversized_tables_keep_their_refusals() {
    let cycle = Ty::Array(TyId::new(0), 1);
    assert!(matches!(
        translate_type_with_tables(&cycle, &[], std::slice::from_ref(&cycle)).unwrap_err(),
        AdapterError::UnsupportedType(message) if message.contains("recursion limit (128)")
    ));
    let dangling = Ty::Array(TyId::new(9), 1);
    assert!(matches!(
        translate_type_with_tables(&dangling, &[], &[Ty::U64]).unwrap_err(),
        AdapterError::UnsupportedType(message)
            if message == "Array(TyId(9), 1) — types table 1 entries, index out of range"
    ));
    let oversized = Ty::Array(TyId::new(0), u64::from(u32::MAX) + 1);
    assert!(matches!(
        translate_type_with_tables(&oversized, &[], &[Ty::U64]).unwrap_err(),
        AdapterError::UnsupportedType(message) if message.contains("exceeds u32::MAX")
    ));
    let extent = Ty::Tuple(vec![Ty::Array(TyId::new(0), u32::MAX.into()), Ty::U8]);
    assert!(matches!(
        translate_type_with_tables(&extent, &[], &[Ty::U8]).unwrap_err(),
        AdapterError::UnsupportedType(message) if message.contains("natural extent")
    ));
}

#[test]
fn table_only_helpers_still_refuse_unvalidated_refinements_before_erasure() {
    for base in [0, 99] {
        let ty = Ty::Refine(TyId::new(base), PredId::new(0));
        assert!(matches!(
            translate_type_with_tables(&ty, &[], &[Ty::U64]).unwrap_err(),
            AdapterError::InvalidRefinement(message)
                if message == "Ty::Refine cannot be erased by a table-only type helper; validate and translate its containing Module instead"
        ));
    }
}

#[test]
fn scalar_fast_path_does_not_bypass_module_nominal_or_closure_admission() {
    let mut module = Module::new("scalar_source_admission");
    let mut first = structure(0, vec![Ty::U64]);
    first.origin = Some(TypeOrigin::Clean {
        decl: "Example.Scalar".into(),
        env_digest: trust_ir::proof::ProofDigest::sha256([11; 32]),
    });
    let mut second = first.clone();
    second.id = StructId::new(1);
    second.name = "Second".into();
    module.structs = vec![first, second];
    let expected = trust_ir_build::ValidationError::TypeOriginConflict {
        origin: module.structs[0].origin.as_ref().unwrap().to_string(),
        first_module: None,
        first_table: "struct",
        first: "Structure0".into(),
        second_module: None,
        second_table: "struct",
        second: "Second".into(),
    }
    .to_string();
    let before = module.clone();
    assert!(matches!(
        translate_type_in_module(&module, &Ty::U64).unwrap_err(),
        AdapterError::TrustIrAdmissionRefused { error } if error == expected
    ));
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 0,
        align: 1,
        capture_offsets: vec![],
    });
    // Nominal identity still refuses before the unconsumed closure image.
    assert!(matches!(
        translate_type_in_module(&module, &Ty::U64).unwrap_err(),
        AdapterError::TrustIrAdmissionRefused { error } if error == expected
    ));
    module.closure_layouts.clear();
    assert_eq!(module, before);
    module.structs[1].origin = None;
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 0,
        align: 1,
        capture_offsets: vec![],
    });
    assert!(matches!(
        translate_type_in_module(&module, &Ty::U64).unwrap_err(),
        AdapterError::TrustIrAdmissionRefused { .. }
    ));
}

#[test]
fn vector_and_collection_carriers_do_not_gain_uncontracted_shapes() {
    for (signed, unsigned, lanes, expected) in [
        (Ty::I8, Ty::U8, 16, Type::V128),
        (Ty::I16, Ty::U16, 8, Type::V128),
        (Ty::I32, Ty::U32, 4, Type::V128),
        (Ty::I64, Ty::U64, 2, Type::V128),
        (Ty::I8, Ty::U8, 8, Type::V64),
    ] {
        for lane in [signed, unsigned] {
            assert_eq!(
                translate_type(&Ty::Vector(Box::new(lane), lanes)).unwrap(),
                expected
            );
        }
    }
    for ty in [
        Ty::Vector(Box::new(Ty::U8), 7),
        Ty::Vector(Box::new(Ty::Ptr), 2),
    ] {
        assert!(matches!(
            translate_type(&ty),
            Err(AdapterError::UnsupportedType(_))
        ));
    }
    let sequence = Ty::Sequence(TyId::new(0));
    let boxed = Ty::Set(TyId::new(0), SetRepr::Boxed);
    for ty in [sequence, boxed] {
        assert_eq!(
            translate_type_with_tables(&ty, &[], &[Ty::U64]).unwrap(),
            Type::I64
        );
        let nested = Ty::Tuple(vec![ty]);
        assert!(translate_type_with_tables(&nested, &[], &[Ty::U64]).is_err());
    }
    let bitset = Ty::Set(TyId::new(0), SetRepr::Bitset);
    assert!(translate_type_with_tables(&bitset, &[], &[Ty::U64]).is_err());
}
