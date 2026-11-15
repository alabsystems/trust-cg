//! WS7.6 — by-value `Ty::Enum` projections of a DIRECT-TAG enum (F-112).
//!
//! Adapter-level pins for `TrustIrAdapter::direct_enum_field_access`: what a
//! tag read and a payload read lower to, and every refusal by its NAME. The
//! native differential (JIT vs the trust-ir interpreter) is
//! `trust-cg-codegen/tests/enum_field_projection.rs`.
//!
//! trust-ir's enum value is `[tag, fields of the ACTIVE variant..]`, and
//! `ExtractField` names an element, not a variant. So element `i > 0` resolves
//! over every variant with a field of the projected type at `i - 1`; it is a
//! static load only when all of them place it at one offset.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::function::Function;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;
use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, StructRepr};
use trust_ir::{
    Block, BlockId, EnumDef, EnumId, EnumVariant, FieldDef, FuncId, FuncTy, Function as IrFunction,
    Inst, InstrNode, Module, StructDef, StructId, Ty, ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.to_string(),
        fields,
        field_names: Vec::new(),
    }
}

/// `enum Shape { sq(u64), rect(u64, u64) }` — the Part A-Lean enum.
fn shape() -> EnumDef {
    EnumDef::new(
        EnumId::new(0),
        "Shape",
        vec![
            variant("sq", vec![Ty::U64]),
            variant("rect", vec![Ty::U64, Ty::U64]),
        ],
    )
}

fn struct_def(fields: &[(Ty, u64)], size: u64, align: u64) -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(0),
        name: "S".to_string(),
        fields: fields
            .iter()
            .enumerate()
            .map(|(i, (ty, offset))| FieldDef {
                name: format!("f{i}"),
                ty: ty.clone(),
                offset: Some(*offset),
            })
            .collect(),
        size: Some(size),
        align: Some(align),
        repr: StructRepr::Rust,
    }
}

fn module(
    edef: EnumDef,
    structs: Vec<StructDef>,
    body: Vec<InstrNode>,
    params: Vec<(ValueId, Ty)>,
) -> Module {
    let mut module = Module::new("ws7_6_direct_enum");
    for sd in structs {
        module.add_struct(sd);
    }
    module.add_enum(edef);
    let returns = match body.first().map(|node| &node.inst) {
        Some(Inst::ExtractField { ty, .. }) => vec![ty.clone()],
        _ => vec![],
    };
    let func_ty = module
        .add_func_type(FuncTy {
            params: params.iter().map(|(_, ty)| ty.clone()).collect(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = IrFunction::new(FuncId::new(0), "project", func_ty, BlockId::new(0));
    func.blocks = vec![Block {
        id: BlockId::new(0),
        params,
        body,
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// `fn project(e: enum.0) -> ty { ret extractfield ty e, field }`.
fn extract(edef: EnumDef, structs: Vec<StructDef>, ty: Ty, field: u32) -> Module {
    let enum_ty = Ty::Enum(edef.id);
    module(
        edef,
        structs,
        vec![
            InstrNode::new(Inst::ExtractField {
                ty,
                aggregate: v(0),
                field,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
        vec![(v(0), enum_ty)],
    )
}

/// `fn project(e: enum.0, x: ty) { insertfield enum.0 e, field, x; ret }`.
fn insert(edef: EnumDef, ty: Ty, field: u32) -> Module {
    let enum_ty = Ty::Enum(edef.id);
    module(
        edef,
        vec![],
        vec![
            InstrNode::new(Inst::InsertField {
                ty: enum_ty.clone(),
                aggregate: v(0),
                field,
                value: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
        vec![(v(0), enum_ty), (v(1), ty)],
    )
}

fn lower(module: &Module) -> Result<Function, AdapterError> {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .map(|(func, _)| func)
}

fn opcodes(func: &Function) -> Vec<Opcode> {
    func.blocks[&func.entry_block]
        .instructions
        .iter()
        .map(|inst| inst.opcode.clone())
        .collect()
}

/// The byte offset the one load in `func` reads at: 0 when it loads through
/// the parameter itself, else the one `Iconst` added to it.
fn loaded_at(func: &Function) -> (u64, Type) {
    let ops = opcodes(func);
    let loads: Vec<Type> = ops
        .iter()
        .filter_map(|op| match op {
            Opcode::Load { ty, .. } => Some(ty.clone()),
            _ => None,
        })
        .collect();
    let [load_ty] = loads.as_slice() else {
        panic!("expected exactly one load, got {ops:?}")
    };
    let offsets: Vec<u64> = ops
        .iter()
        .filter_map(|op| match op {
            Opcode::Iconst { imm, .. } => Some(*imm as u64),
            _ => None,
        })
        .collect();
    let offset = match offsets.as_slice() {
        [] => 0,
        [offset] => *offset,
        _ => panic!("expected at most one offset constant, got {ops:?}"),
    };
    (offset, load_ty.clone())
}

#[test]
fn tag_lane_loads_the_canonical_tag_word_at_byte_0() {
    let func = lower(&extract(shape(), vec![], Ty::U8, 0)).expect("tag read lowers");
    assert_eq!(loaded_at(&func), (0, Type::I8));
}

#[test]
fn payload_lane_both_variants_share_is_one_static_load() {
    // `sq.0` and `rect.0` are both `u64` at payload offset 8.
    let func = lower(&extract(shape(), vec![], Ty::U64, 1)).expect("payload read lowers");
    assert_eq!(loaded_at(&func), (8, Type::I64));
}

#[test]
fn payload_lane_only_one_variant_has_is_a_static_load() {
    let func = lower(&extract(shape(), vec![], Ty::U64, 2)).expect("rect.1 lowers");
    assert_eq!(loaded_at(&func), (16, Type::I64));
}

#[test]
fn explicit_repr_widens_the_tag_word() {
    let mut edef = shape();
    edef.repr = Some(trust_ir::ty::EnumTagRepr::U32);
    let func = lower(&extract(edef.clone(), vec![], Ty::U32, 0)).expect("u32 tag read");
    assert_eq!(loaded_at(&func), (0, Type::I32));
    let err = lower(&extract(edef, vec![], Ty::U8, 0)).expect_err("u8 read of a u32 tag");
    assert!(
        matches!(&err, AdapterError::UnsupportedType(m) if m.contains("canonical tag type U32")),
        "{err:?}"
    );
}

#[test]
fn aggregate_payload_field_is_carried_by_address() {
    // `enum E { a(u8, S) }` with `S = { u64, u64 }` at its natural layout.
    let sd = struct_def(&[(Ty::U64, 0), (Ty::U64, 8)], 16, 8);
    let edef = EnumDef::new(
        EnumId::new(0),
        "E",
        vec![variant("a", vec![Ty::U8, Ty::Struct(StructId::new(0))])],
    );
    let func = lower(&extract(edef, vec![sd], Ty::Struct(StructId::new(0)), 2))
        .expect("struct payload field lowers");
    let ops = opcodes(&func);
    assert!(
        !ops.iter().any(|op| matches!(op, Opcode::Load { .. })),
        "an aggregate field is its address, never a load: {ops:?}"
    );
    assert!(
        ops.iter()
            .any(|op| matches!(op, Opcode::Iconst { imm: 16, .. }))
            && ops
                .iter()
                .any(|op| matches!(op, Opcode::ArrayGep { elem_ty: Type::I8 })),
        "payload offset 8 + field offset 8: {ops:?}"
    );
}

#[test]
fn tag_lane_at_a_noncanonical_type_is_refused() {
    let err = lower(&extract(shape(), vec![], Ty::U64, 0)).expect_err("u64 read of a u8 tag");
    assert!(
        matches!(&err, AdapterError::UnsupportedType(m) if m.contains("canonical tag type U8")),
        "{err:?}"
    );
}

#[test]
fn lane_no_variant_has_at_that_type_is_refused_by_name() {
    for (ty, field) in [(Ty::U32, 1), (Ty::U64, 3)] {
        let err =
            lower(&extract(shape(), vec![], ty.clone(), field)).expect_err("no candidate variant");
        assert!(
            matches!(
                &err,
                AdapterError::EnumProjectionNoCandidate { lane, enum_name, .. }
                    if *lane == field && enum_name == "Shape"
            ),
            "{ty:?} at {field}: {err:?}"
        );
    }
}

/// `enum Amb { a(u8, u8), b(u16, u8) }`: element 2 is `u8` in both variants,
/// at payload byte 1 in `a` and 2 in `b`.
fn ambiguous() -> EnumDef {
    EnumDef::new(
        EnumId::new(0),
        "Amb",
        vec![
            variant("a", vec![Ty::U8, Ty::U8]),
            variant("b", vec![Ty::U16, Ty::U8]),
        ],
    )
}

#[test]
fn same_type_at_different_offsets_is_refused_as_ambiguous() {
    let err = lower(&extract(ambiguous(), vec![], Ty::U8, 2)).expect_err("ambiguous lane");
    match &err {
        AdapterError::EnumProjectionOffsetAmbiguous { lane, offsets, .. } => {
            assert_eq!(*lane, 2);
            assert!(
                offsets.contains("variant 0 `a` at byte 3")
                    && offsets.contains("variant 1 `b` at byte 4"),
                "{offsets}"
            );
        }
        other => panic!("expected EnumProjectionOffsetAmbiguous, got {other:?}"),
    }
    // Element 1 names a DIFFERENT type in each variant, so each type has one
    // candidate and one offset: not ambiguous.
    let func = lower(&extract(ambiguous(), vec![], Ty::U16, 1)).expect("b.0 lowers");
    assert_eq!(loaded_at(&func), (2, Type::I16));
}

#[test]
fn payload_struct_whose_trust_ir_layout_differs_is_refused_as_canonical_disagreement() {
    // `S = { u64 }` declared 16 bytes: trust-ir's canonical enum payload is
    // then 16 bytes, trust-cg's natural `Type::Struct` 8.
    let sd = struct_def(&[(Ty::U64, 0)], 16, 8);
    let edef = EnumDef::new(
        EnumId::new(0),
        "Padded",
        vec![variant("a", vec![Ty::Struct(StructId::new(0)), Ty::U64])],
    );
    let err = lower(&extract(edef, vec![sd], Ty::U64, 2)).expect_err("layouts disagree");
    assert!(
        matches!(&err, AdapterError::EnumCanonicalLayoutDisagrees { enum_name, .. } if enum_name == "Padded"),
        "{err:?}"
    );
}

#[test]
fn packed_payload_enum_stays_refused() {
    // `#[repr(packed)] P = { u8, u64 }`: 9 bytes, 1-aligned.
    let sd = StructDef {
        repr: StructRepr::Packed(1),
        ..struct_def(&[(Ty::U8, 0), (Ty::U64, 1)], 9, 1)
    };
    let edef = EnumDef::new(
        EnumId::new(0),
        "Packed",
        vec![variant("a", vec![Ty::Struct(StructId::new(0)), Ty::U8])],
    );
    for field in [0, 2] {
        let err = lower(&extract(edef.clone(), vec![sd.clone()], Ty::U8, field))
            .expect_err("packed payload must stay refused");
        assert!(
            matches!(&err, AdapterError::EnumCanonicalLayoutDisagrees { .. }),
            "element {field}: {err:?}"
        );
    }
}

#[test]
fn agreeing_direct_descriptor_projects_without_the_canonical_recheck() {
    let mut edef = shape();
    edef.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 24,
        align: 8,
        variant_field_offsets: vec![vec![8], vec![8, 16]],
    });
    let func = lower(&extract(edef, vec![], Ty::U64, 2)).expect("descriptor agrees");
    assert_eq!(loaded_at(&func), (16, Type::I64));
}

/// A `Direct` descriptor the canonical shape does not reproduce is carried at
/// its own bytes (L05-P5): `Shape` padded to 32 bytes still reads `rect.1` at
/// the descriptor's byte 16, through a 32-byte carrier that is not
/// `Type::Enum`, and a tag the descriptor moves is read where it says.
#[test]
fn disagreeing_direct_descriptor_is_addressed_from_the_descriptor() {
    let mut edef = shape();
    edef.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 32,
        align: 8,
        variant_field_offsets: vec![vec![8], vec![8, 16]],
    });
    let func =
        lower(&extract(edef.clone(), vec![], Ty::U64, 2)).expect("descriptor is the authority");
    assert_eq!(loaded_at(&func), (16, Type::I64));
    assert_eq!(
        func.signature.params[0],
        Type::Struct(vec![Type::Array(Box::new(Type::I64), 4)]),
        "the byte-image carrier of the declared 32/8"
    );
    if let Some(layout) = edef.layout.as_mut() {
        layout.encoding = EnumTagEncoding::Direct { tag_offset: 24 };
    }
    let func = lower(&extract(edef, vec![], Ty::U8, 0)).expect("tag at the descriptor's offset");
    assert_eq!(loaded_at(&func), (24, Type::I8));
}

#[test]
fn insert_field_at_the_tag_lane_is_refused_by_name() {
    let err = lower(&insert(shape(), Ty::U8, 0)).expect_err("re-tag");
    assert!(
        matches!(&err, AdapterError::EnumTagWriteUnsupported { enum_name, .. } if enum_name == "Shape"),
        "{err:?}"
    );
}

/// WS7.1(c): a payload lane now LOWERS. It used to be refused as
/// `EnumPayloadInsertUnsupported` because the value-semantic (fresh-slot) insert that
/// struct, array and sequence values use was not wired to this carrier's field walk.
///
/// The two halves it needed already existed: `direct_enum_field_access` supplies the byte
/// offset every candidate variant agrees on (and refuses by name when they do not), and
/// `insert_destination` supplies the fresh slot that keeps the insert value-semantic. Only
/// the connection was missing.
///
/// This test pins the SHAPE (it lowers, and it writes rather than reads). That the write is
/// value-semantic — an insert into a shared base not clobbering its sibling — is pinned
/// against the interpreter by
/// `trust-cg-codegen/tests/enum_field_projection.rs::ws71c_direct_tag_payload_insert_is_value_semantic`,
/// whose `no_alias` entry is 15 with fresh slots and would be 25 with an in-place update.
#[test]
fn insert_field_at_a_payload_lane_lowers_with_value_semantics() {
    let func = lower(&insert(shape(), Ty::U64, 1)).expect("payload insert must lower");
    let ops = opcodes(&func);
    assert!(
        ops.iter().any(|op| matches!(op, Opcode::Store { .. })),
        "the payload lane must be written with a store: {ops:?}"
    );
}

#[test]
fn insert_field_at_a_payload_lane_no_variant_has_is_still_refused() {
    // The offset authority still refuses what it always refused: a lane no candidate
    // variant has at that type. Wiring the insert must not widen the projection.
    let err = lower(&insert(shape(), Ty::U8, 1)).expect_err("ill-typed payload lane");
    assert!(
        matches!(
            &err,
            AdapterError::EnumProjectionNoCandidate { lane: 1, .. }
                | AdapterError::EnumPayloadInsertUnsupported { lane: 1, .. }
        ),
        "{err:?}"
    );
}

// The mutation-knob controls (a perturbed trust-cg layout, an off-by-one
// payload offset) live in `trust-cg-codegen/tests/enum_field_projection.rs`,
// whose tests serialize on the process-global knobs; the tests here run in
// parallel and must never observe a knob.

/// `fn project(s: struct.0) -> enum.0 { ret extractfield enum.0 s, 1 }` over
/// `struct S { u64, Shape }`, with `offsets` declared or natural.
fn struct_enum_field(offsets: Option<(u64, u64)>) -> Module {
    let fields = [Ty::U64, Ty::Enum(EnumId::new(0))];
    let sd = StructDef {
        origin: None,
        id: StructId::new(0),
        name: "S".to_string(),
        fields: fields
            .iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: format!("f{i}"),
                ty: ty.clone(),
                offset: offsets.map(|(a, b)| if i == 0 { a } else { b }),
            })
            .collect(),
        size: offsets.map(|_| 32),
        align: offsets.map(|_| 8),
        repr: StructRepr::Rust,
    };
    module(
        shape(),
        vec![sd],
        vec![
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Enum(EnumId::new(0)),
                aggregate: v(0),
                field: 1,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
        vec![(v(0), Ty::Struct(StructId::new(0)))],
    )
}

/// REVIEW FIX: an enum-typed FIELD of a struct is an aggregate, carried by
/// ADDRESS like a struct or array field — never `Load`ed as a scalar, which
/// handed a later enum projection the tag word as an address (a SIGSEGV; the
/// native twin is `review_enum_field_of_a_struct_is_projected_by_address`).
/// Both the natural-layout (`StructGep`) and the declared-offset arm.
#[test]
fn enum_field_of_a_struct_is_carried_by_address_not_loaded() {
    for offsets in [None, Some((24, 0))] {
        let func = lower(&struct_enum_field(offsets)).expect("struct enum field lowers");
        let ops = opcodes(&func);
        assert!(
            !ops.iter().any(|op| matches!(
                op,
                Opcode::Load {
                    ty: Type::Enum { .. },
                    ..
                }
            )),
            "offsets {offsets:?}: an enum field must not be loaded as a scalar: {ops:?}"
        );
    }
}

/// REVIEW FIX, the write side: `InsertField` of an enum VALUE into a struct
/// with declared offsets copies the enum's bytes (`Memmove`), never a scalar
/// `Store` of the enum's address.
#[test]
fn enum_value_inserted_into_a_declared_offset_struct_is_copied_not_stored() {
    let mut m = struct_enum_field(Some((24, 0)));
    let func_ty = m.functions[0].ty;
    m.func_types[func_ty.index() as usize] = FuncTy {
        params: vec![Ty::Struct(StructId::new(0)), Ty::Enum(EnumId::new(0))],
        returns: vec![],
        abi: None,
        is_vararg: false,
    };
    m.functions[0].blocks[0].params = vec![
        (v(0), Ty::Struct(StructId::new(0))),
        (v(1), Ty::Enum(EnumId::new(0))),
    ];
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::InsertField {
            ty: Ty::Struct(StructId::new(0)),
            aggregate: v(0),
            field: 1,
            value: v(1),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    let func = lower(&m).expect("struct insert of an enum lowers");
    let ops = opcodes(&func);
    assert!(
        !ops.iter().any(|op| matches!(
            op,
            Opcode::Store {
                ty: Type::Enum { .. },
                ..
            }
        )),
        "an enum value must not be stored as a scalar: {ops:?}"
    );
    assert!(
        ops.iter().any(|op| matches!(op, Opcode::Memmove)),
        "an enum value is copied by bytes: {ops:?}"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
