// untagged_enum_carrier.rs — a v37 UNTAGGED enum admitted as its sole variant's
// payload struct, with element 0 answered as a CONSTANT
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TrustIr v37 added `EnumTagEncoding::Untagged` for one shape: the
//! single-INHABITED-variant `repr(Rust)` enum, whose memory image rustc stores
//! WITHOUT a discriminant because there is nothing to discriminate.
//! `enum UnOp { Not(Vec<()>) }` IS its 24-byte payload. Before that encoding
//! existed a producer had to DECLINE a descriptor for such a def — the grammar
//! could only say direct-or-niche, and neither is true — and a descriptor-less
//! enum falls back to trust-ir's canonical tagged-union layout, which budgets a
//! tag. That is what made `Option<UnOp>` unvalidatable: Option's own correct
//! descriptor says 24, while the canonical recomputation of its `UnOp` field
//! says 8 + 24 = 32.
//!
//! TrustCg then had no route for the new encoding: `Ty::Enum` refused it
//! outright ("untagged encoding; the LIR enum has no tag-free
//! representation"), so the enum's TYPE could not be translated and every
//! signature, alloca, load, store and constant mentioning it died. v37 had
//! moved the failure one repo downstream. This file pins the route.
//!
//! THE ORACLE IS STOCK RUSTC — `rustc 1.96.0 (ac68faa20 2026-05-25)`,
//! `size_of` / `align_of`, plus raw field addresses and `transmute` where the
//! offset is what is in question:
//!
//! ```text
//! Vec<()>                       size 24 align 8
//! enum UnOp { Not(Vec<()>) }    size 24 align 8   the payload alone, at byte 0
//! Option<UnOp>                  size 24 align 8   niche; Some's payload at byte 0
//! enum Three { A(u64,u32,u32) } size 16 align 8   A.0@0 A.1@8 A.2@12
//!     A(0x1111111111111111, 0x22222222, 0x33333333) transmutes to
//!     [11 11 11 11 11 11 11 11 22 22 22 22 33 33 33 33]
//! enum Reord { A(u8, u64) }     size 16 align 8   A.0@8 A.1@0  (rustc REORDERS)
//! enum Seven { A = 7 }          size  0 align 1
//! ```
//!
//! # Why this is the EASY half of the tag-free family
//!
//! A niche encoding hides the discriminant in otherwise-invalid values of a
//! payload lane, so recovering it needs a runtime range test — which
//! `niche_field_access` answers through the niche codec (`src/niche_codec.rs`,
//! pinned in `tests/niche_enum_codec.rs`). Here the variant is a static fact of
//! the TYPE: with one variant, no byte of the image participates in the answer,
//! so element 0 lowers to a single `Iconst` of the sole variant's EFFECTIVE
//! discriminant. That is the same conclusion trust-ir's own reference
//! interpreter reaches — `EnumByteView::Untagged` decodes the variant without
//! touching memory and then SYNTHESIZES the tag the value model expects
//! (`interpret.rs`, `synthesized_tag_value`).
//!
//! # What stays refused, and why each refusal is here
//!
//! * a MULTI-VARIANT untagged descriptor — nothing in the image discriminates
//!   them, so admitting one would let a load invent a variant. trust-ir's
//!   validator, `shape` and interpreter each reject it independently; TrustCg
//!   re-checks rather than inheriting the guarantee.
//! * a carrier that misses the declared size, align or ANY declared field
//!   offset — `Reord { A(u8, u64) }` is the live case: rustc puts the `u64`
//!   first, and the natural-C carrier cannot reproduce that.
//! * `InsertField` at element 0 — the read side answers a constant because no
//!   byte participates; a WRITE has nowhere to land, and no lane in which a
//!   disagreeing value could be caught, so dropping it would make an
//!   unsatisfiable write silently succeed.
//! * an aggregate constant whose head names a discriminant the sole variant
//!   does not have.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;
use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, EnumDef, EnumId, EnumVariant, FieldDef, FuncId,
    FuncTy, FuncTyId, Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule,
    StructDef, StructId, StructRepr, Ty, ValueId,
};

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::assert_typed_const_refusal;

#[path = "common/below_admission.rs"]
mod below_admission;
use below_admission::{body_refusal_below_admission, type_refusal_below_admission};

/// The untagged carrier rule's refusal of enum 0, as the module-aware type
/// conversion reports it: the untagged admission wraps the rule's `reason`.
fn untagged_carrier_refusal(enum_name: &str, reason: &str) -> String {
    format!(
        "unsupported trust_ir type: enum EnumId(0) (`{enum_name}`) has an UNTAGGED (v37) \
         producer-provided layout descriptor (normative EnumDef.layout), and TrustCg admits one \
         only as the sole variant's payload struct the descriptor itself describes ({reason}); \
         refusing to synthesize a layout the producer did not specify"
    )
}

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

fn untagged(size: u64, align: u64, variant_field_offsets: Vec<Vec<u64>>) -> EnumLayoutDescriptor {
    EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size,
        align,
        variant_field_offsets,
    }
}

/// `Vec<()>` — (c) MEASURED size 24 align 8. Spelled as the three pointer-wide
/// words it is, so the carrier's natural-C recomputation has something real to
/// agree with, and DECLARED at that layout: TrustIR's typed admission bounds
/// an enum descriptor's fields by their layout, and a struct without declared
/// size and offsets has none.
fn vec_unit_struct() -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(0),
        name: "VecUnit".to_string(),
        fields: vec![
            FieldDef {
                name: "ptr".to_string(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "cap".to_string(),
                ty: Ty::U64,
                offset: Some(8),
            },
            FieldDef {
                name: "len".to_string(),
                ty: Ty::U64,
                offset: Some(16),
            },
        ],
        size: Some(24),
        align: Some(8),
        repr: StructRepr::Rust,
    }
}

/// `enum UnOp { Not(Vec<()>) }` — the v37 motivating shape. (c) MEASURED size
/// 24 align 8, identical to `Vec<()>` alone: the enum IS its payload.
fn unop() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "UnOp".to_string(),
        variants: vec![variant("Not", vec![Ty::Struct(StructId::new(0))])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(untagged(24, 8, vec![vec![0]])),
    }
}

/// `enum Three { A(u64, u32, u32) }` — (c) MEASURED size 16 align 8 with the
/// fields at bytes 0, 8 and 12 (transmuted image
/// `[11×8, 22×4, 33×4]`). The three-field payload is what makes the INDEX SHIFT
/// observable as a byte address rather than as an out-of-bounds error.
fn three() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "Three".to_string(),
        variants: vec![variant("A", vec![Ty::U64, Ty::U32, Ty::U32])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(untagged(16, 8, vec![vec![0, 8, 12]])),
    }
}

/// `enum Reord { A(u8, u64) }` — (c) MEASURED size 16 align 8 with field 0
/// (`u8`) at byte 8 and field 1 (`u64`) at byte 0: rustc REORDERS `repr(Rust)`
/// fields, and TrustCg's natural-C carrier does not. The descriptor is
/// truthful; the carrier cannot reproduce it, so it fails closed.
fn reordered() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "Reord".to_string(),
        variants: vec![variant("A", vec![Ty::U8, Ty::U64])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(untagged(16, 8, vec![vec![8, 0]])),
    }
}

/// `enum Seven { A = 7 }` — (c) MEASURED size 0 align 1. The EFFECTIVE
/// discriminant is 7, not the variant index 0, and an untagged image stores
/// neither: the constant element 0 lowers to has to be 7.
fn seven() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "Seven".to_string(),
        variants: vec![variant("A", vec![])],
        discriminants: vec![Some(7)],
        repr: None,
        layout: Some(untagged(0, 1, vec![vec![]])),
    }
}

/// Build a module out of `structs` + `enums` plus a single function whose body
/// is `body` and whose signature is `params -> ()`.
fn module_with(
    structs: Vec<StructDef>,
    enums: Vec<EnumDef>,
    params: Vec<(ValueId, Ty)>,
    body: Vec<InstrNode>,
) -> TrustIrModule {
    let mut module = TrustIrModule::new("untagged_carrier");
    module.structs = structs;
    module.enums = enums;
    let fty_id: FuncTyId = module
        .add_func_type(FuncTy {
            params: params.iter().map(|(_, t)| t.clone()).collect(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params,
        body,
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn opcodes(module: &TrustIrModule) -> Vec<Opcode> {
    let func = module.functions.first().expect("one function");
    let (lir_func, _proofs) =
        trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
            .expect("adapter must lower the fixture");
    let entry = lir_func.entry_block;
    lir_func.blocks[&entry]
        .instructions
        .iter()
        .map(|i| i.opcode.clone())
        .collect()
}

/// THE BYTE ADDRESS every `StructGep` in the stream resolves to — the number the
/// backends actually compute (`isel.rs` / `x86_64_isel.rs` both resolve
/// `StructGep` with natural-C `Type::offset_of`). Pinning the index alone would
/// not catch a shift applied to the wrong carrier.
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

fn iconsts(opcodes: &[Opcode]) -> Vec<(Type, i64)> {
    opcodes
        .iter()
        .filter_map(|o| match o {
            Opcode::Iconst { ty, imm } => Some((ty.clone(), *imm)),
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
    trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
        .expect_err("the fixture must fail closed")
}

// ---------------------------------------------------------------------------
// The admission: the enum IS its sole variant's payload
// ---------------------------------------------------------------------------

/// `enum UnOp { Not(Vec<()>) }` is 24 bytes with the payload at byte 0 — (c)
/// MEASURED, the same size and align as `Vec<()>` alone. So its LIR carrier is
/// the payload struct, not a tag plus a payload.
#[test]
fn an_untagged_enum_lowers_to_its_sole_variants_payload_struct() {
    let module = module_with(
        vec![vec_unit_struct()],
        vec![unop()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results =
        permit_translate_module(&module).expect("an untagged descriptor must be admitted");
    let carrier = &results[0].0.signature.params[0];
    assert_eq!(
        *carrier,
        Type::Struct(vec![Type::Struct(vec![Type::I64, Type::I64, Type::I64])]),
        "rustc: UnOp is size 24 align 8 — Vec<()> at byte 0, and nothing else"
    );
    assert_eq!(
        (carrier.bytes(), carrier.align()),
        (24, 8),
        "and the emitted totals ARE the producer's declared 24/8"
    );
}

/// The three-field fixture: `Type::Struct([I64, I32, I32])`, whose natural-C
/// offsets are rustc's measured 0 / 8 / 12.
#[test]
fn the_carrier_reproduces_every_declared_field_offset() {
    let module = module_with(
        vec![],
        vec![three()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results =
        permit_translate_module(&module).expect("an untagged descriptor must be admitted");
    let carrier = &results[0].0.signature.params[0];
    assert_eq!(
        *carrier,
        Type::Struct(vec![Type::I64, Type::I32, Type::I32])
    );
    assert_eq!(
        (0..3)
            .map(|i| carrier.offset_of(i).map(u64::from).expect("offset"))
            .collect::<Vec<_>>(),
        vec![0, 8, 12],
        "rustc lays A(0x1111111111111111, 0x22222222, 0x33333333) out as 11.. 22.. 33.."
    );
    assert_eq!((carrier.bytes(), carrier.align()), (16, 8));
}

/// THE CASCADE, and the reason v37 exists at all. `Option<UnOp>` is
/// niche-encoded at (c) MEASURED 24/8 with `Some`'s payload at byte 0, so
/// `niche_enum_carrier` admits it as that payload — but only if the payload
/// TRANSLATES. While `UnOp` was refused, `Option<UnOp>` cascaded to refused
/// with it, which is exactly the unvalidatable pair the v37 ledger names.
#[test]
fn a_niche_enum_whose_payload_is_untagged_now_translates() {
    let option_unop = EnumDef {
        origin: None,
        id: EnumId::new(1),
        name: "OptionUnOp".to_string(),
        variants: vec![
            variant("None", vec![]),
            variant("Some", vec![Ty::Enum(EnumId::new(0))]),
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U64,
            },
            size: 24,
            align: 8,
            variant_field_offsets: vec![vec![], vec![0]],
        }),
    };
    let module = module_with(
        vec![vec_unit_struct()],
        vec![unop(), option_unop],
        vec![(v(0), Ty::Enum(EnumId::new(1)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results = permit_translate_module(&module).expect("the cascade must clear");
    let carrier = &results[0].0.signature.params[0];
    assert_eq!(
        (carrier.bytes(), carrier.align()),
        (24, 8),
        "rustc: Option<UnOp> is 24/8, the same object as UnOp — {carrier:?}"
    );
}

// ---------------------------------------------------------------------------
// Element 0: a CONSTANT, not a memory read
// ---------------------------------------------------------------------------

/// The whole point of (b). An untagged image stores no discriminant, so element
/// 0 is answered from the TYPE: one `Iconst`, no `Load`, no `StructGep`.
/// Reading byte 0 instead would hand back the first PAYLOAD field's bytes —
/// eight bytes of `Three::A`'s `u64`.
#[test]
fn element_zero_lowers_to_a_constant_with_no_memory_read() {
    let module = module_with(
        vec![],
        vec![three()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 0),
    );
    let ops = opcodes(&module);
    assert_eq!(
        iconsts(&ops),
        vec![(Type::I8, 0)],
        "the sole variant's effective discriminant, at trust-ir's canonical tag width: {ops:?}"
    );
    assert!(
        !ops.iter()
            .any(|o| matches!(o, Opcode::Load { .. } | Opcode::StructGep { .. })),
        "no byte of the image participates in the answer: {ops:?}"
    );
}

/// And it is the EFFECTIVE discriminant, not the variant index.
/// `enum Seven { A = 7 }` is (c) MEASURED size 0 — the 7 is stored nowhere —
/// so the only place it can come from is the definition.
#[test]
fn element_zero_carries_the_effective_discriminant_not_the_index() {
    let module = module_with(
        vec![],
        vec![seven()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 0),
    );
    let ops = opcodes(&module);
    assert_eq!(
        iconsts(&ops),
        vec![(Type::I8, 7)],
        "`A = 7` has discriminant 7, and index 0 would be a different number: {ops:?}"
    );
}

// ---------------------------------------------------------------------------
// THE INDEX SHIFT, in bytes
// ---------------------------------------------------------------------------

/// trust-ir element 2 is payload field 1, which rustc puts at byte 8. An
/// unshifted index addresses byte 12 — field 2's bytes, at an address the
/// producer never named for field 1. Pinned as an ADDRESS, not as an index.
#[test]
fn extract_of_the_second_payload_field_addresses_rustcs_byte_eight() {
    let module = module_with(
        vec![],
        vec![three()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 2),
    );
    assert_eq!(
        struct_gep_bytes(&opcodes(&module)),
        vec![8],
        "trust-ir element 2 = payload field 1 = rustc's byte 8; unshifted it would be byte 12"
    );
}

/// The same shift on the write side: `InsertField` element 2 STORES to byte 8,
/// at the payload field's own 32-bit width.
#[test]
fn insert_into_the_second_payload_field_addresses_rustcs_byte_eight() {
    let module = module_with(
        vec![],
        vec![three()],
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
    assert_eq!(struct_gep_bytes(&ops), vec![8]);
    assert!(
        ops.iter()
            .any(|o| matches!(o, Opcode::Store { ty: Type::I32, .. })),
        "and it is a 32-bit store, the payload field's own width: {ops:?}"
    );
}

/// The one-field case, where the shift is the difference between working and
/// erroring: element 1 is payload field 0 at byte 0. An unshifted index 1 is out
/// of bounds for a one-field carrier.
#[test]
fn extract_of_the_only_payload_field_addresses_byte_zero() {
    let module = module_with(
        vec![vec_unit_struct()],
        vec![unop()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 1),
    );
    assert_eq!(struct_gep_bytes(&opcodes(&module)), vec![0]);
}

/// A payload index past the sole variant's fields names nothing, and says so.
#[test]
fn a_payload_index_past_the_sole_variant_is_refused() {
    let module = module_with(
        vec![],
        vec![three()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 4),
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("names payload field 3"),
        "must name the shifted index: {msg}"
    );
    assert!(msg.contains("Three"), "must name the enum: {msg}");
}

// ---------------------------------------------------------------------------
// The refusals — each names its axis
// ---------------------------------------------------------------------------

/// A WRITE to element 0 has nowhere to land: the image has no tag lane, and no
/// lane in which a disagreeing value could be detected either. Dropping the
/// store would make an unsatisfiable write silently succeed.
#[test]
fn inserting_at_element_zero_is_refused() {
    let module = module_with(
        vec![],
        vec![three()],
        vec![(v(0), Ty::Enum(EnumId::new(0))), (v(1), Ty::U8)],
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
    assert!(msg.contains("Three"), "must name the enum: {msg}");
    assert!(
        msg.contains("ExtractField at element 0 answers the constant"),
        "must say what DOES work, so the reader is not left guessing: {msg}"
    );
}

/// An untagged image carries no discriminating information, so a multi-variant
/// descriptor is undiscriminable. trust-ir's validator, `shape` and interpreter
/// each reject it; TrustCg re-checks rather than inheriting the guarantee. Its
/// codegen entries consume TrustIR's typed admission first, so the carrier
/// rule's own refusal is pinned below that admission.
#[test]
fn a_multi_variant_untagged_descriptor_is_refused() {
    let mut edef = three();
    edef.variants.push(variant("B", vec![]));
    edef.layout = Some(untagged(16, 8, vec![vec![0, 8, 12], vec![]]));
    let module = module_with(
        vec![],
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    assert_typed_const_refusal(
        &lower_err(&module),
        "enum.0 (Three) layout",
        "exactly one variant under the untagged encoding",
        "2 variants",
    );
    assert_eq!(
        type_refusal_below_admission(&module, &Ty::Enum(EnumId::new(0))).to_string(),
        untagged_carrier_refusal(
            "Three",
            "the descriptor declares the untagged encoding but the enum has 2 variants; an \
             untagged image stores nothing that could discriminate them"
        )
    );
}

/// rustc REORDERS `repr(Rust)` fields and TrustCg's natural-C carrier does not.
/// `Reord { A(u8, u64) }` is (c) MEASURED with the `u64` FIRST — field 0 at byte
/// 8, field 1 at byte 0 — which no declaration-ordered carrier reproduces. The
/// descriptor is truthful and the refusal is the honest answer.
#[test]
fn a_carrier_that_misses_a_declared_field_offset_is_refused() {
    let module = module_with(
        vec![],
        vec![reordered()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("puts field 0 at byte 0"),
        "must name what the carrier does: {msg}"
    );
    assert!(
        msg.contains("declares variant 0 field 0 at byte 8"),
        "must name what the producer declared: {msg}"
    );
    assert!(msg.contains("UNTAGGED"), "must name the encoding: {msg}");
}

/// The declared SIZE is an equality, not a lower bound.
#[test]
fn a_carrier_that_misses_the_declared_size_is_refused() {
    let mut edef = three();
    edef.layout = Some(untagged(24, 8, vec![vec![0, 8, 12]]));
    let module = module_with(
        vec![],
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("has size 16, the descriptor declares size 24"),
        "must name the size axis and both numbers: {msg}"
    );
}

/// A descriptor that states offsets for a different number of fields than the
/// variant has, or for a different number of variants than the enum has, is
/// partial data, and is refused wholesale. TrustIR's typed admission counts
/// both axes first on every codegen entry; the carrier rule's own counts are
/// pinned below that admission.
#[test]
fn an_incomplete_descriptor_is_refused() {
    let mut edef = three();
    edef.layout = Some(untagged(16, 8, vec![vec![0, 8]]));
    let module = module_with(
        vec![],
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    assert_typed_const_refusal(
        &lower_err(&module),
        "enum.0 (Three) layout",
        "variant 0 (A): 3 field offsets",
        "2 offsets",
    );
    assert_eq!(
        type_refusal_below_admission(&module, &Ty::Enum(EnumId::new(0))).to_string(),
        untagged_carrier_refusal(
            "Three",
            "the descriptor states 2 field offsets for the sole variant (`A`), which has 3 fields"
        )
    );

    let mut edef = three();
    edef.layout = Some(untagged(16, 8, vec![vec![0, 8, 12], vec![]]));
    let module = module_with(
        vec![],
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    assert_typed_const_refusal(
        &lower_err(&module),
        "enum.0 (Three) layout",
        "1 per-variant offset lists",
        "2 offset lists",
    );
    assert_eq!(
        type_refusal_below_admission(&module, &Ty::Enum(EnumId::new(0))).to_string(),
        untagged_carrier_refusal(
            "Three",
            "the descriptor states field offsets for 2 variants, the enum has 1"
        )
    );
}

// ---------------------------------------------------------------------------
// Aggregate constants
// ---------------------------------------------------------------------------

/// A `Constant::Aggregate` for an untagged enum writes the payload and NOTHING
/// else: there is no tag word, so the head element contributes no store. The
/// direct-encoded path would have opened with `Iconst`+`Store` of the tag at
/// byte 0 — which for this shape is the `u64` payload field's own bytes.
#[test]
fn an_aggregate_constant_writes_the_payload_and_no_tag() {
    let module = module_with(
        vec![],
        vec![three()],
        vec![],
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Enum(EnumId::new(0)),
                value: Constant::Aggregate(vec![
                    Constant::Int(0),
                    Constant::Int(0x1111_1111_1111_1111),
                    Constant::Int(0x2222_2222),
                    Constant::Int(0x3333_3333),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let ops = opcodes(&module);
    let stores: Vec<Type> = ops
        .iter()
        .filter_map(|o| match o {
            Opcode::Store { ty, .. } => Some(ty.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(
        stores,
        vec![Type::I64, Type::I32, Type::I32],
        "exactly the three payload lanes rustc lays out at 0 / 8 / 12, and no tag: {ops:?}"
    );
    assert_eq!(
        struct_gep_bytes(&ops),
        vec![0, 8, 12],
        "written at the producer's own declared bytes: {ops:?}"
    );
}

/// The head element is still checked. An untagged image stores no tag, so a
/// constant naming a variant the enum does not have could never show up later —
/// it has to be caught here. TrustIR's typed admission does so on every codegen
/// entry; the adapter's own head check is pinned below that admission.
#[test]
fn an_aggregate_constant_naming_another_variant_is_refused() {
    let module = module_with(
        vec![],
        vec![three()],
        vec![],
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Enum(EnumId::new(0)),
                value: Constant::Aggregate(vec![
                    Constant::Int(1),
                    Constant::Int(0),
                    Constant::Int(0),
                    Constant::Int(0),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    assert_typed_const_refusal(
        &lower_err(&module),
        "function 'k' bb0",
        "a discriminant of enum Three",
        "1",
    );
    assert_eq!(
        body_refusal_below_admission(&module),
        "not lowerable: unsupported trust_ir instruction: Constant::Aggregate for untagged \
         enum EnumId(0) (`Three`) has head 1, but its sole variant (`A`) has discriminant 0; an \
         untagged image stores no tag, so no other variant exists to name"
    );
}

// ---------------------------------------------------------------------------
// Controls — the route is keyed on the ENCODING, not on the variant count
// ---------------------------------------------------------------------------

/// A single-variant enum with NO descriptor keeps trust-ir's canonical
/// tagged-union shape, tag lane and all. Nothing about "one variant" triggers
/// the tag-free route; only the producer saying `Untagged` does.
#[test]
fn a_single_variant_enum_without_a_descriptor_keeps_the_canonical_tag() {
    let mut edef = three();
    edef.layout = None;
    let module = module_with(
        vec![],
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results = permit_translate_module(&module).expect("the canonical path is unchanged");
    assert!(
        matches!(results[0].0.signature.params[0], Type::Enum { .. }),
        "still a tag lane plus a payload region: {:?}",
        results[0].0.signature.params[0]
    );
}

/// And a single-variant enum whose descriptor says DIRECT is carried at the
/// producer's own bytes — never as the untagged payload. `#[repr(C)] enum H {
/// X(u8) }` is (c) MEASURED size 8 align 4 with the field at byte 4: rustc
/// keeps a real discriminant for it, which is exactly why the producer must
/// not spell it `Untagged`, and since L05-P5 the descriptor is the authority
/// for where that discriminant and the field live.
#[test]
fn a_single_variant_enum_with_a_direct_descriptor_is_carried_at_its_declared_bytes() {
    let mut edef = EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "ReprCOne".to_string(),
        variants: vec![variant("X", vec![Ty::U8])],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    };
    edef.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 8,
        align: 4,
        variant_field_offsets: vec![vec![4]],
    });
    let module = module_with(
        vec![],
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let results =
        permit_translate_module(&module).expect("a Direct descriptor is carried as declared");
    let carrier = &results[0].0.signature.params[0];
    assert!(
        !matches!(carrier, Type::Enum { .. }),
        "the canonical tagged union does not reproduce 8/4: {carrier:?}"
    );
    assert_ne!(
        *carrier,
        Type::Struct(vec![Type::I8]),
        "and it is not the untagged payload: the discriminant is real"
    );
    assert_eq!(
        *carrier,
        Type::Struct(vec![Type::Array(Box::new(Type::I32), 2)])
    );
    assert_eq!((carrier.bytes(), carrier.align()), (8, 4));
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

fn single_inhabited(active: usize) -> Vec<EnumDef> {
    let mut variants = vec![variant("Absent", vec![Ty::Enum(EnumId::new(1))]); 2];
    variants[active] = variant("Present", vec![Ty::U32]);
    let mut offsets = vec![vec![]; 2];
    offsets[active] = vec![0];
    let mut def = EnumDef::new(EnumId::new(0), "SingleInhabited", variants);
    def.discriminants = vec![Some(7), Some(23)];
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::SingleInhabited {
            variant: active as u32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: offsets,
    });
    vec![def, EnumDef::new(EnumId::new(1), "Infallible", vec![])]
}

#[test]
fn single_inhabited_v65_selects_payload_and_effective_discriminant_at_either_index() {
    for active in 0..2 {
        let module = module_with(
            vec![],
            single_inhabited(active),
            vec![(v(0), Ty::Enum(EnumId::new(0)))],
            extract(Ty::Enum(EnumId::new(0)), 0),
        );
        let translated = permit_translate_module(&module).unwrap();
        assert_eq!(
            translated[0].0.signature.params[0],
            Type::Struct(vec![Type::I32])
        );
        let ops = opcodes(&module);
        assert_eq!(iconsts(&ops), vec![(Type::I8, [7, 23][active])]);
        assert!(
            !ops.iter()
                .any(|op| matches!(op, Opcode::Load { .. } | Opcode::StructGep { .. }))
        );
        let payload = module_with(
            vec![],
            single_inhabited(active),
            vec![(v(0), Ty::Enum(EnumId::new(0)))],
            extract(Ty::Enum(EnumId::new(0)), 1),
        );
        assert_eq!(struct_gep_bytes(&opcodes(&payload)), vec![0]);
    }
}

#[test]
fn single_inhabited_v65_constant_stores_only_the_selected_payload() {
    for active in 0..2 {
        let module = module_with(
            vec![],
            single_inhabited(active),
            vec![],
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Enum(EnumId::new(0)),
                    value: Constant::Aggregate(vec![
                        Constant::Int([7, 23][active]),
                        Constant::Int(0x12345678),
                    ]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        );
        let ops = opcodes(&module);
        let stores: Vec<_> = ops
            .iter()
            .filter_map(|op| match op {
                Opcode::Store { ty, .. } => Some(ty.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(stores, vec![Type::I32]);
        assert_eq!(struct_gep_bytes(&ops), vec![0]);
    }
}

#[test]
fn single_inhabited_v65_runtime_construction_preserves_the_active_payload() {
    for active in 0..2 {
        let module = module_with(
            vec![],
            single_inhabited(active),
            vec![(v(0), Ty::U32)],
            vec![
                InstrNode::new(Inst::MakeAggregate {
                    ty: Ty::Enum(EnumId::new(0)),
                    variant: Some(active as u32),
                    fields: vec![v(0)],
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::Enum(EnumId::new(0)),
                    aggregate: v(1),
                    field: 0,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        );
        let ops = opcodes(&module);
        assert_eq!(
            ops.iter()
                .filter(|op| matches!(op, Opcode::Store { ty: Type::I32, .. }))
                .count(),
            1
        );
        assert!(iconsts(&ops).contains(&(Type::I8, [7, 23][active])));
    }
}

#[test]
fn single_inhabited_v65_refuses_unproved_absence_and_nonempty_inactive_offsets() {
    for mutate in 0..4 {
        let mut enums = single_inhabited(1);
        let layout = enums[0].layout.as_mut().unwrap();
        match mutate {
            0 => layout.encoding = EnumTagEncoding::SingleInhabited { variant: 2 },
            1 => layout.variant_field_offsets[0] = vec![0],
            2 => enums[0].variants[0].fields = vec![Ty::U32],
            _ => enums[0].variants[1].fields = vec![Ty::Never],
        }
        let module = module_with(
            vec![],
            enums,
            vec![(v(0), Ty::Enum(EnumId::new(0)))],
            vec![InstrNode::new(Inst::Return { values: vec![] })],
        );
        let error = type_refusal_below_admission(&module, &Ty::Enum(EnumId::new(0)));
        assert!(
            error.to_string().contains("single-inhabited"),
            "mutation {mutate}: {error}"
        );
    }
}
