// niche_enum_carrier.rs — a NICHE-encoded enum admitted as its payload struct
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A niche-encoded enum has NO TAG LANE. Its discriminant lives in
//! otherwise-invalid values of a payload field — `Option<&T>`'s `None` is the
//! null pointer — so `Type::Enum`, which is exactly a tag lane plus a payload
//! region, cannot express it. (c) MEASURED over the 68-module corpus: of 373
//! niche descriptors, ZERO agree with the canonical tagged-union shape, and all
//! 225 whose payloads translate disagree on SIZE and on every field offset. So
//! the whole family was refused, and it was the single largest converter gap:
//! 3,097 corpus functions.
//!
//! `niche_enum_carrier` (`adapter.rs`) admits one only as the payload struct
//! the producer's own descriptor describes, by EQUALITY against that
//! descriptor's size, align and every declared field offset. It never
//! synthesizes an address.
//!
//! THE ORACLE IS STOCK RUSTC — `rustc 1.97.0 (2d8144b78 2026-07-07)`,
//! `size_of` / `align_of` / `offset_of!`, plus `transmute` to read the raw byte
//! image where the offset is what is in question:
//!
//! ```text
//! &u64                              size  8 align 8
//! Option<&u64>                      size  8 align 8   Some(&x) bytes ARE &x; None is 0x00…
//! Result<&u64, ()>                  size  8 align 8   Ok.0@0 and Err.0@0 (Err's is a ZST)
//! enum { A(NonZeroU32,u32,u32), B } size 12 align 4   A.0@0 A.1@4 A.2@8
//!     A(0x11111111, 0x22222222, 0x33333333) transmutes to
//!     [11 11 11 11 22 22 22 22 33 33 33 33]
//! Box<dyn Fn()>                     size 16 align 8
//! Option<Box<dyn Fn()>>             size 16 align 8
//! Option<u64>                       size 16 align 8   (NOT niche — the Direct control)
//! Result<u64, u64>                  size 16 align 8   (NOT niche — the Direct control)
//! ```
//!
//! # The index shift, which is the part that mis-addresses silently
//!
//! trust-ir indexes an enum aggregate FLATLY: element 0 is the DISCRIMINANT and
//! element `i > 0` is payload field `i - 1`. The carrier is the payload ALONE,
//! at `0..n`. So every field-access site must translate the index and refuse
//! element 0. On the three-field fixture above, `ExtractField { field: 2 }`
//! means payload field 1, at rustc's byte 4 — an unshifted index would address
//! byte 8, silently, which is field 2's bytes. That is pinned below in BYTES
//! (`StructGep`'s resolved `Type::offset_of`), not in index numbers.
//!
//! # What stays refused, and why each refusal is here
//!
//! * element 0 — recovering the discriminant needs the niche RANGE TEST, which
//!   TrustCg does not emit; byte 0 is payload.
//! * `Constant::Aggregate` — its first act is to store the discriminant as a
//!   plain tag word at byte 0, and there is no tag word to store it in.
//! * variants that place a field at DIFFERENT bytes (119 of 373 measured) —
//!   `ExtractField` names a field but not a variant, so the address is
//!   unresolvable.
//! * variants that give a shared field DIFFERENT TYPES — the same argument, one
//!   axis over. (c) MEASURED: of the 171 carriers the equality gate admits, 31
//!   have a field index declared by two or more variants and ALL 31 of those
//!   disagree on the field's `Ty` and on its emitted (size, align).
//! * a carrier that misses the declared size, align or any declared offset —
//!   the 5 residual `Option<Box<dyn Fn…>>` cases, where trust-ir declares 16/8
//!   and the natural-C carrier recomputes to 0/1.

use trust_cg_lower::adapter::{AdapterError, translate_function, translate_module};
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;
use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, EnumDef, EnumId, EnumVariant, FieldDef, FuncId,
    FuncTy, FuncTyId, Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule,
    StructDef, StructId, StructRepr, Ty, ValueId,
};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.to_string(),
        fields,
        field_names: Vec::new(),
    }
}

/// A niche descriptor. The niche parameters themselves are never read by the
/// carrier rule — what matters is that the encoding IS `Niche`, plus the
/// declared totals and offsets — so one plausible spelling serves every
/// fixture: variant 0 niched into the low value of the field at byte 0, variant
/// 1 untagged.
fn niche(size: u64, align: u64, variant_field_offsets: Vec<Vec<u64>>) -> EnumLayoutDescriptor {
    EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 1,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U64,
        },
        size,
        align,
        variant_field_offsets,
    }
}

/// `Option<&u64>` — (c) MEASURED size 8 align 8, `Some(&x)`'s bytes ARE the
/// pointer (payload at byte 0) and `None` is all-zero.
fn option_ref() -> EnumDef {
    EnumDef {
        id: EnumId::new(0),
        name: "OptionRef".to_string(),
        variants: vec![variant("None", vec![]), variant("Some", vec![Ty::Ptr])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(niche(8, 8, vec![vec![], vec![0]])),
    }
}

/// `enum { A(NonZeroU32, u32, u32), B }` — (c) MEASURED size 12 align 4 with
/// `A`'s fields at bytes 0, 4 and 8 (its transmuted image is
/// `[11 11 11 11 22 22 22 22 33 33 33 33]`). The three-field payload is what
/// makes the INDEX SHIFT observable as a byte address rather than as an
/// out-of-bounds error.
fn three_field() -> EnumDef {
    EnumDef {
        id: EnumId::new(0),
        name: "ThreeField".to_string(),
        variants: vec![
            variant("A", vec![Ty::U32, Ty::U32, Ty::U32]),
            variant("B", vec![]),
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(niche(12, 4, vec![vec![0, 4, 8], vec![]])),
    }
}

/// `Result<&u64, ()>` — (c) MEASURED size 8 align 8, `Ok(&x)`'s bytes ARE the
/// pointer and `Err(())` is all-zero, so BOTH variants declare a field 0 at
/// byte 0 while typing it differently (`&u64` vs the ZST). This is the shape
/// that is common in the corpus (`object::Result`, `cc::Result`,
/// `proc_macro2::Span`): the ADDRESS is agreed, the TYPE is not.
fn result_ref_unit() -> EnumDef {
    EnumDef {
        id: EnumId::new(0),
        name: "ResultRefUnit".to_string(),
        variants: vec![variant("Ok", vec![Ty::Ptr]), variant("Err", vec![Ty::Unit])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(niche(8, 8, vec![vec![0], vec![0]])),
    }
}

/// Build a module out of one enum plus a single function whose body is `body`
/// and whose signature is `params -> ()`.
fn module_with(
    enums: Vec<EnumDef>,
    params: Vec<(ValueId, Ty)>,
    body: Vec<InstrNode>,
) -> TrustIrModule {
    let mut module = TrustIrModule::new("niche_carrier");
    module.enums = enums;
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: params.iter().map(|(_, t)| t.clone()).collect(),
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params,
        body,
    }];
    module.add_function(func);
    module
}

fn opcodes(module: &TrustIrModule) -> Vec<Opcode> {
    let func = module.functions.first().expect("one function");
    let (lir_func, _proofs) =
        translate_function(func, module).expect("adapter must lower the fixture");
    let entry = lir_func.entry_block;
    lir_func.blocks[&entry]
        .instructions
        .iter()
        .map(|i| i.opcode.clone())
        .collect()
}

/// THE BYTE ADDRESS every `StructGep` in the stream resolves to — the number
/// the backends actually compute (`isel.rs`, `x86_64_isel.rs` both resolve
/// `StructGep` with natural-C `Type::offset_of` on the LIR type). Pinning the
/// index alone would not catch a shift applied to the wrong carrier.
fn struct_gep_bytes(opcodes: &[Opcode]) -> Vec<u64> {
    opcodes
        .iter()
        .filter_map(|o| match o {
            Opcode::StructGep {
                struct_ty,
                field_index,
            } => Some(
                struct_ty
                    .offset_of(*field_index as usize)
                    .map(u64::from)
                    .expect("StructGep must name a field the carrier has"),
            ),
            _ => None,
        })
        .collect()
}

fn extract(ty: Ty, field: u32) -> Vec<InstrNode> {
    vec![
        InstrNode::new(Inst::ExtractField {
            ty,
            aggregate: v(0),
            field,
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Return { values: vec![] }),
    ]
}

fn lower_err(module: &TrustIrModule) -> AdapterError {
    let func = module.functions.first().expect("one function");
    translate_function(func, module).expect_err("the fixture must fail closed")
}

// ---------------------------------------------------------------------------
// The admission: the enum IS its payload, at the producer's own bytes
// ---------------------------------------------------------------------------

/// `Option<&u64>` is 8 bytes with the pointer at byte 0 — (c) MEASURED, the
/// same size and align as `&u64` alone, and `Some(&x)`'s raw bytes ARE the
/// pointer's. So its LIR carrier is one pointer-wide field, not a tag plus a
/// payload.
#[test]
fn a_niche_enum_lowers_to_the_payload_struct_its_descriptor_describes() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let module = module_with(
        vec![option_ref()],
        vec![(v(0), enum_ty.clone())],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results = translate_module(&module).expect("a niche descriptor must be admitted");
    let (func, _proofs) = &results[0];
    assert_eq!(
        func.signature.params,
        vec![Type::Struct(vec![Type::I64])],
        "rustc: Option<&u64> is size 8 align 8, the pointer at byte 0 — the payload alone"
    );
    let carrier = &func.signature.params[0];
    assert_eq!(
        (carrier.bytes(), carrier.align()),
        (8, 8),
        "and the emitted totals ARE the producer's declared 8/8"
    );
}

/// The three-field fixture: `Type::Struct([I32, I32, I32])`, whose natural-C
/// offsets are rustc's measured 0 / 4 / 8.
#[test]
fn the_carrier_reproduces_every_declared_field_offset() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let module = module_with(
        vec![three_field()],
        vec![(v(0), enum_ty)],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results = translate_module(&module).expect("a niche descriptor must be admitted");
    let carrier = &results[0].0.signature.params[0];
    assert_eq!(
        *carrier,
        Type::Struct(vec![Type::I32, Type::I32, Type::I32])
    );
    assert_eq!(
        (0..3)
            .map(|i| carrier.offset_of(i).map(u64::from).expect("offset"))
            .collect::<Vec<_>>(),
        vec![0, 4, 8],
        "rustc lays A(0x11111111, 0x22222222, 0x33333333) out as 11.. 22.. 33.."
    );
    assert_eq!((carrier.bytes(), carrier.align()), (12, 4));
}

// ---------------------------------------------------------------------------
// THE INDEX SHIFT, in bytes
// ---------------------------------------------------------------------------

/// trust-ir element 2 is payload field 1, which rustc puts at byte 4. An
/// unshifted index addresses byte 8 — field 2's bytes, at an address the
/// producer never named for field 1. This is the whole reason the shift exists,
/// and it is pinned as an ADDRESS, not as an index.
#[test]
fn extract_of_the_second_payload_field_addresses_rustcs_byte_four() {
    let module = module_with(
        vec![three_field()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 2),
    );
    assert_eq!(
        struct_gep_bytes(&opcodes(&module)),
        vec![4],
        "trust-ir element 2 = payload field 1 = rustc's byte 4; unshifted it would be byte 8"
    );
}

/// The same shift on the write side. `InsertField` element 2 STORES to byte 4.
#[test]
fn insert_into_the_second_payload_field_addresses_rustcs_byte_four() {
    let module = module_with(
        vec![three_field()],
        vec![(v(0), Ty::Enum(EnumId::new(0))), (v(1), Ty::U32)],
        vec![
            InstrNode::new(Inst::InsertField {
                ty: Ty::Enum(EnumId::new(0)),
                aggregate: v(0),
                field: 2,
                value: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let ops = opcodes(&module);
    assert_eq!(
        struct_gep_bytes(&ops),
        vec![4],
        "trust-ir element 2 = payload field 1 = rustc's byte 4"
    );
    assert!(
        ops.iter()
            .any(|o| matches!(o, Opcode::Store { ty: Type::I32, .. })),
        "and it is a 32-bit store, the payload field's own width: {ops:?}"
    );
}

/// The one-field case, where the shift is the difference between working and
/// erroring: element 1 is payload field 0 at byte 0 (rustc: `Some(&x)`'s bytes
/// ARE the pointer). An unshifted index 1 is out of bounds for a one-field
/// carrier.
#[test]
fn extract_of_the_only_payload_field_addresses_byte_zero() {
    let module = module_with(
        vec![option_ref()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 1),
    );
    assert_eq!(struct_gep_bytes(&opcodes(&module)), vec![0]);
}

// ---------------------------------------------------------------------------
// The refusals — each names its axis
// ---------------------------------------------------------------------------

/// Element 0 is the DISCRIMINANT. A niche encoding has no tag lane to read it
/// from; byte 0 is payload — for `Option<&u64>` it is the pointer itself.
#[test]
fn element_zero_is_the_discriminant_and_is_refused() {
    let module = module_with(
        vec![option_ref()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 0),
    );
    let msg = format!("{}", lower_err(&module));
    assert!(msg.contains("DISCRIMINANT"), "must name the axis: {msg}");
    assert!(msg.contains("OptionRef"), "must name the enum: {msg}");
    assert!(
        msg.contains("niche range test"),
        "must name what is missing: {msg}"
    );
}

/// The same for the write side — an `InsertField` at element 0 would write a
/// variant index over the payload.
#[test]
fn inserting_at_element_zero_is_refused() {
    let module = module_with(
        vec![option_ref()],
        vec![(v(0), Ty::Enum(EnumId::new(0))), (v(1), Ty::Ptr)],
        vec![
            InstrNode::new(Inst::InsertField {
                ty: Ty::Enum(EnumId::new(0)),
                aggregate: v(0),
                field: 0,
                value: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(msg.contains("DISCRIMINANT"), "must name the axis: {msg}");
}

/// `Constant::Aggregate` for an enum stores the discriminant as a plain tag
/// word at byte 0 and fills the payload behind it. For a niche encoding byte 0
/// IS the payload — `Some(&x)`'s bytes are the pointer — so that store would
/// overwrite the value it is meant to build.
#[test]
fn aggregate_constant_on_a_niche_enum_is_refused() {
    let module = module_with(
        vec![option_ref()],
        vec![],
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Enum(EnumId::new(0)),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0)]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("no tag lane"),
        "must name the missing tag word: {msg}"
    );
    assert!(msg.contains("OptionRef"), "must name the enum: {msg}");
}

/// 119 of 373 corpus niche enums place a field at DIFFERENT bytes in different
/// variants — `Result` with field 0 at both 0 and 8. `ExtractField` names a
/// field but not a variant, so that field has no resolvable address.
#[test]
fn variants_that_disagree_on_a_field_offset_are_refused() {
    let mut edef = result_ref_unit();
    edef.layout = Some(niche(16, 8, vec![vec![0], vec![8]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("DISAGREE on the byte offset of field 0"),
        "must name the axis and the field: {msg}"
    );
    assert!(msg.contains("byte 0"), "must name both bytes: {msg}");
    assert!(msg.contains("byte 8"), "must name both bytes: {msg}");
    assert!(msg.contains("EnumDef.layout"), "must name the field: {msg}");
}

/// A field two variants type differently is unresolvable for the same reason a
/// field two variants ADDRESS differently is: the instruction names a field, not
/// a variant. `Result<&u64, ()>` — (c) MEASURED size 8, `Ok.0` and `Err.0` both
/// at byte 0 — is that shape. The TYPE is still admitted (its extent is the
/// producer's either way); only the ambiguous ACCESS fails closed.
#[test]
fn a_payload_field_the_variants_type_differently_is_refused_at_the_access() {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let admitted = module_with(
        vec![result_ref_unit()],
        vec![(v(0), enum_ty.clone())],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results = translate_module(&admitted).expect("the TYPE is admitted");
    assert_eq!(
        results[0].0.signature.params,
        vec![Type::Struct(vec![Type::I64])],
        "the carrier is Ok's pointer payload; rustc sizes Result<&u64,()> at 8/8"
    );

    let module = module_with(
        vec![result_ref_unit()],
        vec![(v(0), enum_ty.clone())],
        extract(enum_ty, 1),
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("DIFFERENT types by different variants"),
        "must name the axis: {msg}"
    );
    assert!(msg.contains("ResultRefUnit"), "must name the enum: {msg}");
}

/// The declared SIZE is an equality, not a lower bound.
#[test]
fn a_carrier_that_misses_the_declared_size_is_refused() {
    let mut edef = option_ref();
    edef.layout = Some(niche(16, 8, vec![vec![], vec![0]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("has size 8, the descriptor declares size 16"),
        "must name the size axis and both numbers: {msg}"
    );
}

/// And so is the declared ALIGN. This is the `Option<Box<dyn Fn…>>` family —
/// (c) MEASURED 16/8 in rustc, 5 cases in the corpus — where the natural-C
/// carrier recomputes to something else entirely and the gate earns its keep.
#[test]
fn a_carrier_that_misses_the_declared_align_is_refused() {
    let mut edef = option_ref();
    edef.layout = Some(niche(8, 16, vec![vec![], vec![0]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("has align 8, the descriptor declares align 16"),
        "must name the align axis and both numbers: {msg}"
    );
}

/// The `Option<Box<dyn Fn()>>` residual, spelled the way the corpus carries it:
/// rustc declares 16/8 (measured), the payload is a fat-pointer struct whose two
/// component structs recompute to nothing, and the natural-C carrier is 0/1.
#[test]
fn the_fat_pointer_closure_family_is_refused_on_size_and_align() {
    let mut module = TrustIrModule::new("niche_fatptr");
    module.structs = vec![
        StructDef {
            id: StructId::new(0),
            name: "Data".to_string(),
            fields: vec![],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        },
        StructDef {
            id: StructId::new(1),
            name: "Vtable".to_string(),
            fields: vec![],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        },
        StructDef {
            id: StructId::new(2),
            name: "BoxDynFn".to_string(),
            fields: vec![
                FieldDef {
                    name: "data".to_string(),
                    ty: Ty::Struct(StructId::new(0)),
                    offset: None,
                },
                FieldDef {
                    name: "vtable".to_string(),
                    ty: Ty::Struct(StructId::new(1)),
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        },
    ];
    module.enums = vec![EnumDef {
        id: EnumId::new(0),
        name: "OptionBoxDynFn".to_string(),
        variants: vec![
            variant("None", vec![]),
            variant("Some", vec![Ty::Struct(StructId::new(2))]),
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(niche(16, 8, vec![vec![], vec![0]])),
    }];
    let fty_id = module.add_func_type(FuncTy {
        params: vec![Ty::Enum(EnumId::new(0))],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Enum(EnumId::new(0)))],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    module.add_function(func);

    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("has size 0, the descriptor declares size 16"),
        "must name the size axis: {msg}"
    );
    assert!(msg.contains("OptionBoxDynFn"), "must name the enum: {msg}");
}

/// A declared offset the carrier does not put the field at is refused, even
/// when the totals agree.
#[test]
fn a_carrier_that_misses_a_declared_field_offset_is_refused() {
    let mut edef = option_ref();
    edef.layout = Some(niche(8, 8, vec![vec![], vec![4]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("puts field 0 at byte 0, the descriptor declares variant 1 field 0 at byte 4"),
        "must name the offset axis and both bytes: {msg}"
    );
}

/// Two variants whose payloads have the SAME size and align but DIFFERENT types
/// both reproduce the descriptor, so the carrier is not determined. There is no
/// "widest variant" tie-break to fall back on — (c) MEASURED, a tie-break is
/// exactly what produced the earlier undercount of 146 — so this fails closed.
/// (0 corpus enums are ambiguous; this shape is constructible, so it is gated.)
#[test]
fn an_ambiguous_carrier_is_refused_rather_than_tie_broken() {
    let edef = EnumDef {
        id: EnumId::new(0),
        name: "AmbiguousEight".to_string(),
        variants: vec![variant("A", vec![Ty::U64]), variant("B", vec![Ty::F64])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(niche(8, 8, vec![vec![0], vec![0]])),
    };
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("the carrier is ambiguous"),
        "must name the ambiguity: {msg}"
    );
    assert!(
        msg.contains("`A`") && msg.contains("`B`"),
        "must name both variants: {msg}"
    );
}

/// A descriptor that does not describe every variant is refused wholesale,
/// exactly as `declared_layout` refuses a half-declared struct: a
/// half-declared, half-synthesized layout is one no authority stands behind.
#[test]
fn an_incomplete_descriptor_is_refused_wholesale() {
    let mut edef = option_ref();
    edef.layout = Some(niche(8, 8, vec![vec![0]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("states field offsets for 1 variants, the enum has 2"),
        "must name the completeness axis: {msg}"
    );

    // ...and so is one whose per-variant list does not match the variant's
    // field count.
    let mut edef = option_ref();
    edef.layout = Some(niche(8, 8, vec![vec![], vec![0, 8]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("states 2 field offsets for variant 1 (`Some`), which has 1 fields"),
        "must name the variant and both counts: {msg}"
    );
}

// ---------------------------------------------------------------------------
// The controls — nothing that worked before moves
// ---------------------------------------------------------------------------

/// `Option<u64>` is NOT niche-encoded — (c) MEASURED size 16 align 8, a real
/// tag word plus a payload — and it keeps the canonical `Type::Enum` lowering
/// with no index shift anywhere near it.
#[test]
fn a_direct_encoded_enum_still_lowers_to_the_canonical_tagged_union() {
    let edef = EnumDef {
        id: EnumId::new(0),
        name: "OptionU64".to_string(),
        variants: vec![variant("None", vec![]), variant("Some", vec![Ty::U64])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 0 },
            size: 16,
            align: 8,
            variant_field_offsets: vec![vec![], vec![8]],
        }),
    };
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results = translate_module(&module).expect("the Direct control must still be admitted");
    let carrier = &results[0].0.signature.params[0];
    assert!(
        matches!(carrier, Type::Enum { .. }),
        "a Direct encoding keeps the tagged union: {carrier:?}"
    );
    assert_eq!((carrier.bytes(), carrier.align()), (16, 8));
}

/// A niche enum's `EnumDef.repr` and `EnumDef.discriminants` name a TAG WORD
/// this lowering never emits, so they cannot reach the emitted stream and are
/// not grounds to refuse. `Ordering`-shaped discriminants (-1, 0, 1) on a
/// Direct enum still are — that is pinned in `tests/aggregate_types.rs`.
#[test]
fn tag_lane_semantics_do_not_refuse_an_enum_that_has_no_tag_lane() {
    let mut edef = option_ref();
    edef.discriminants = vec![Some(7), Some(11)];
    edef.repr = Some(EnumTagRepr::I8);
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results = translate_module(&module)
        .expect("a niche enum emits no tag, so tag semantics cannot be mis-served");
    assert_eq!(
        results[0].0.signature.params,
        vec![Type::Struct(vec![Type::I64])]
    );
}
