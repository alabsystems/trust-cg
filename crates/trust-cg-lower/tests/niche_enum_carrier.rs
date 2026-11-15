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
//! at `0..n`. So every field-access site must translate the index, and element
//! 0 is answered by the niche discriminant codec (`src/niche_codec.rs`) rather
//! than by reading byte 0 as a tag. On the three-field fixture above,
//! `ExtractField { field: 2 }` means payload field 1, at rustc's byte 4 — an
//! unshifted index would address byte 8, silently, which is field 2's bytes.
//! That is pinned below in BYTES (`StructGep`'s resolved `Type::offset_of`),
//! not in index numbers. The codec itself — decode, encode, constants and its
//! refusals — is pinned in `tests/niche_enum_codec.rs`.
//!
//! # What stays refused, and why each refusal is here
//!
//! * ANY value written at element 0 — that would rewrite the discriminant,
//!   which trust-ir makes undefined behaviour (`EnumTagWriteUnsupported`); the
//!   axis is closed to `InsertField` regardless of the written value's type.
//! * an untagged `Constant::Aggregate` whose payload puts a RESERVED value in
//!   the lane (`Some(null)` for `Option<&T>`): its image would decode as the
//!   niche-tagged variant.
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
use below_admission::type_refusal_below_admission;

/// The carrier rule's refusal of enum 0, as the type conversion reports it:
/// the niche admission wraps the rule's `reason`.
fn niche_carrier_refusal(enum_name: &str, reason: &str) -> String {
    format!(
        "unsupported trust_ir type: enum EnumId(0) (`{enum_name}`) has a NICHE-encoded \
         producer-provided v31 layout descriptor (normative EnumDef.layout), and TrustCg admits \
         one only as the payload struct the descriptor itself describes ({reason}); refusing to \
         synthesize a layout the producer did not specify"
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

/// A niche descriptor: variant `niched` is the one niche-tagged variant,
/// encoded as the reserved value 0 of the `lane` scalar at byte
/// `niche_offset`, and `untagged` is the variant that carries data. The carrier
/// rule reads only the encoding, the declared totals and the offsets, but
/// TrustIR's typed admission checks the niche parameters against the variants
/// (the lane lies inside a non-ZST field of the untagged variant, clear of
/// every niche-tagged variant's non-ZST fields, and no more aligned than the
/// descriptor), so each fixture spells rustc's own parameters.
fn niche_lane(
    untagged: u32,
    niched: u32,
    lane: EnumTagRepr,
    niche_offset: u64,
    size: u64,
    align: u64,
    variant_field_offsets: Vec<Vec<u64>>,
) -> EnumLayoutDescriptor {
    EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: untagged,
            niche_variants_start: niched,
            niche_variants_end: niched,
            niche_start: 0,
            niche_offset,
            niche_ty: lane,
        },
        size,
        align,
        variant_field_offsets,
    }
}

/// `Option<&T>`'s niche: `None` (variant 0) is the null pointer in the
/// pointer-wide lane at byte 0 of `Some` (variant 1).
fn niche(size: u64, align: u64, variant_field_offsets: Vec<Vec<u64>>) -> EnumLayoutDescriptor {
    niche_lane(
        1,
        0,
        EnumTagRepr::U64,
        0,
        size,
        align,
        variant_field_offsets,
    )
}

/// `Option<&u64>` — (c) MEASURED size 8 align 8, `Some(&x)`'s bytes ARE the
/// pointer (payload at byte 0) and `None` is all-zero.
fn option_ref() -> EnumDef {
    EnumDef {
        origin: None,
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
        origin: None,
        id: EnumId::new(0),
        name: "ThreeField".to_string(),
        variants: vec![
            variant("A", vec![Ty::U32, Ty::U32, Ty::U32]),
            variant("B", vec![]),
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(niche_lane(
            0,
            1,
            EnumTagRepr::U32,
            0,
            12,
            4,
            vec![vec![0, 4, 8], vec![]],
        )),
    }
}

/// `Result<&u64, ()>` — (c) MEASURED size 8 align 8, `Ok(&x)`'s bytes ARE the
/// pointer and `Err(())` is all-zero, so BOTH variants declare a field 0 at
/// byte 0 while typing it differently (`&u64` vs the ZST). This is the shape
/// that is common in the corpus (`object::Result`, `cc::Result`,
/// `proc_macro2::Span`): the ADDRESS is agreed, the TYPE is not.
fn result_ref_unit() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "ResultRefUnit".to_string(),
        variants: vec![variant("Ok", vec![Ty::Ptr]), variant("Err", vec![Ty::Unit])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(result_ref_unit_niche(8, vec![vec![0], vec![0]])),
    }
}

/// `Result<&u64, ()>`'s niche: `Err(())` (variant 1) is the null pointer in
/// `Ok`'s (variant 0) pointer lane at byte 0.
fn result_ref_unit_niche(size: u64, variant_field_offsets: Vec<Vec<u64>>) -> EnumLayoutDescriptor {
    niche_lane(0, 1, EnumTagRepr::U64, 0, size, 8, variant_field_offsets)
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
    trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
        .expect_err("the fixture must fail closed")
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
    let results = permit_translate_module(&module).expect("a niche descriptor must be admitted");
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
    let results = permit_translate_module(&module).expect("a niche descriptor must be admitted");
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
/// from — byte 0 is payload, for `Option<&u64>` the pointer itself — so it is
/// DECODED from the lane: one 8-byte load of the pointer, compared with the
/// null niche, selecting `None`'s or `Some`'s discriminant, narrowed to the
/// canonical `u8` tag. Never a byte-0 tag read.
#[test]
fn element_zero_is_the_discriminant_and_is_decoded_from_the_lane() {
    let module = module_with(
        vec![option_ref()],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        extract(Ty::Enum(EnumId::new(0)), 0),
    );
    let ops = opcodes(&module);
    assert!(
        matches!(ops.first(), Some(Opcode::Load { ty: Type::I64, .. })),
        "the whole pointer-wide lane is loaded: {ops:?}"
    );
    assert!(
        ops.iter().any(|o| matches!(
            o,
            Opcode::Icmp {
                cond: trust_cg_lower::instructions::IntCC::Equal
            }
        )),
        "one niche variant is one equality: {ops:?}"
    );
    assert!(
        ops.iter()
            .any(|o| matches!(o, Opcode::Trunc { to_ty: Type::I8 })),
        "the discriminant has the canonical u8 tag type: {ops:?}"
    );
}

/// Element 0 is CLOSED to `InsertField`, whatever the written value's type:
/// rewriting a discriminant in place is undefined behaviour in trust-ir, so a
/// variant is constructed with `Const`, never patched. The refusal is
/// `EnumTagWriteUnsupported`.
///
/// This test previously asserted that the refusal names the "canonical tag
/// type", i.e. that the write side rejects a pointer because its TYPE is not
/// the tag's. It never reached that check and now never can: the axis is
/// refused before any type comparison. That is strictly stronger, so the test
/// pins the stronger property — BOTH a wrongly-typed value (a pointer) and a
/// plainly tag-shaped one are refused on the same axis. An implementation that
/// only compared types would let the second case through and fail here.
///
/// (The "canonical tag type" wording belongs to a different refusal — an enum
/// that HAS no canonical tag type — and is pinned by
/// `direct_enum_projection.rs`.)
#[test]
fn inserting_any_value_at_element_zero_is_refused() {
    // A pointer (the original case: plainly not a discriminant) and a
    // tag-shaped integer (which a type-only check would ACCEPT).
    for written in [Ty::Ptr, Ty::U64] {
        let module = module_with(
            vec![option_ref()],
            vec![(v(0), Ty::Enum(EnumId::new(0))), (v(1), written.clone())],
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
        assert!(
            msg.contains("element 0"),
            "{written:?}: must name the axis: {msg}"
        );
        assert!(
            msg.contains("discriminant"),
            "{written:?}: must say what element 0 IS: {msg}"
        );
        assert!(
            msg.contains("Const"),
            "{written:?}: must name the supported construction: {msg}"
        );
    }
}

/// `Some(null)` for `Option<&u64>`: the untagged variant's payload IS the lane,
/// and null is the reserved value that encodes `None`. The image would read
/// back as `None`, so the constant is refused rather than silently changed.
#[test]
fn an_untagged_constant_holding_the_reserved_niche_value_is_refused() {
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
        msg.contains("[TCG-NICHE-ENUM]") && msg.contains("reserved niche value"),
        "must name the reserved lane value: {msg}"
    );
    assert!(msg.contains("OptionRef"), "must name the enum: {msg}");
}

/// 119 of 373 corpus niche enums place a field at DIFFERENT bytes in different
/// variants — `Result` with field 0 at both 0 and 8. `ExtractField` names a
/// field but not a variant, so that field has no resolvable address.
#[test]
fn variants_that_disagree_on_a_field_offset_are_refused() {
    let mut edef = result_ref_unit();
    edef.layout = Some(result_ref_unit_niche(16, vec![vec![0], vec![8]]));
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
    let results = permit_translate_module(&admitted).expect("the TYPE is admitted");
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

/// And so is the declared ALIGN: a payload carrier with the declared size and
/// every declared offset is still refused when its alignment differs. (The
/// `Option<Box<dyn Fn…>>` family misses both totals; it is pinned by
/// `the_fat_pointer_closure_family_is_refused_on_size_and_align`.)
#[test]
fn a_carrier_that_misses_the_declared_align_is_refused() {
    // A descriptor whose size is not a multiple of its align describes no
    // image at all: TrustIR's typed admission refuses it first.
    let mut edef = option_ref();
    edef.layout = Some(niche(8, 16, vec![vec![], vec![0]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    assert_typed_const_refusal(
        &lower_err(&module),
        "enum.0 (OptionRef) layout",
        "size a multiple of align 16",
        "size 8",
    );

    // A well-formed 16/8 image whose payload carrier (four u32 lanes) has the
    // declared size and every declared offset but only align 4.
    let edef = EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "FourLanes".to_string(),
        variants: vec![
            variant("A", vec![Ty::U32, Ty::U32, Ty::U32, Ty::U32]),
            variant("B", vec![]),
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(niche_lane(
            0,
            1,
            EnumTagRepr::U32,
            0,
            16,
            8,
            vec![vec![0, 4, 8, 12], vec![]],
        )),
    };
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("has align 4, the descriptor declares align 8"),
        "must name the align axis and both numbers: {msg}"
    );
}

/// The `Option<Box<dyn Fn()>>` residual, spelled the way the corpus carries it:
/// rustc declares 16/8 (measured), the payload is a fat-pointer struct whose two
/// component structs recompute to nothing, and the natural-C carrier is 0/1.
/// TrustIR's typed admission refuses the descriptor first on every codegen
/// entry; below that admission the carrier gate refuses it, naming the first
/// axis the 0/1 carrier misses, the size.
#[test]
fn the_fat_pointer_closure_family_is_refused_on_size_and_align() {
    let mut module = TrustIrModule::new("niche_fatptr");
    module.structs = vec![
        StructDef {
            origin: None,
            id: StructId::new(0),
            name: "Data".to_string(),
            fields: vec![],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        },
        StructDef {
            origin: None,
            id: StructId::new(1),
            name: "Vtable".to_string(),
            fields: vec![],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        },
        StructDef {
            origin: None,
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
        origin: None,
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
    let fty_id = module
        .add_func_type(FuncTy {
            params: vec![Ty::Enum(EnumId::new(0))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Enum(EnumId::new(0)))],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    // The payload's component structs have no layout to bound it within the
    // declared 16 bytes, so TrustIR's typed admission refuses the descriptor
    // before the carrier's recomputed 0/1 can be compared with it.
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains(
            "enum.0 (OptionBoxDynFn) layout: const type mismatch: expected variant 1 \
             field 0 to have a resolvable layout (needed to bound it within size 16)"
        ),
        "must name the enum, the field and the size axis: {msg}"
    );
    assert_eq!(
        type_refusal_below_admission(&module, &Ty::Enum(EnumId::new(0))).to_string(),
        niche_carrier_refusal(
            "OptionBoxDynFn",
            "no variant's payload struct reproduces the declared layout (variant 0 (`None`) \
             payload struct has size 0, the descriptor declares size 16; variant 1 (`Some`) \
             payload struct has size 0, the descriptor declares size 16)"
        )
    );
}

/// A declared offset the carrier does not put the field at is refused, even
/// when the totals agree.
#[test]
fn a_carrier_that_misses_a_declared_field_offset_is_refused() {
    // A field that runs past the declared image is refused by TrustIR's typed
    // admission before any carrier is built.
    let mut edef = option_ref();
    edef.layout = Some(niche(8, 8, vec![vec![], vec![4]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    assert_typed_const_refusal(
        &lower_err(&module),
        "enum.0 (OptionRef) layout",
        "variant 1 field 0 entirely within size 8",
        "offset 4, field size 8",
    );

    // Inside the image, with the totals agreeing: the three-field payload with
    // its last two fields swapped. The natural carrier puts field 1 at byte 4.
    let mut edef = three_field();
    if let Some(layout) = edef.layout.as_mut() {
        layout.variant_field_offsets = vec![vec![0, 8, 4], vec![]];
    }
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let msg = format!("{}", lower_err(&module));
    assert!(
        msg.contains("puts field 1 at byte 4, the descriptor declares variant 0 field 1 at byte 8"),
        "must name the offset axis and both bytes: {msg}"
    );
}

/// Two variants whose payloads have the SAME size and align but DIFFERENT types
/// both reproduce the descriptor, so the carrier is not determined. There is no
/// "widest variant" tie-break to fall back on — (c) MEASURED, a tie-break is
/// exactly what produced the earlier undercount of 146 — so this fails closed.
/// (0 corpus enums are ambiguous; this shape is constructible, so it is gated.)
///
/// The shape is a well-formed niche: the one-byte lane at byte 15 lies inside
/// the untagged `A`'s second field and clear of `B`'s fields, and both
/// `A(f64, u64)` and `B(f64, u32)` lay out as 16/8 with fields at 0 and 8.
#[test]
fn an_ambiguous_carrier_is_refused_rather_than_tie_broken() {
    let edef = EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "AmbiguousSixteen".to_string(),
        variants: vec![
            variant("A", vec![Ty::F64, Ty::U64]),
            variant("B", vec![Ty::F64, Ty::U32]),
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(niche_lane(
            0,
            1,
            EnumTagRepr::U8,
            15,
            16,
            8,
            vec![vec![0, 8], vec![0, 8]],
        )),
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
/// TrustIR's typed admission counts both axes before the adapter does on
/// every codegen entry; the carrier rule's own counts are pinned below that
/// admission.
#[test]
fn an_incomplete_descriptor_is_refused_wholesale() {
    let mut edef = option_ref();
    edef.layout = Some(niche(8, 8, vec![vec![0]]));
    let module = module_with(
        vec![edef],
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    assert_typed_const_refusal(
        &lower_err(&module),
        "enum.0 (OptionRef) layout",
        "2 per-variant offset lists",
        "1 offset lists",
    );
    assert_eq!(
        type_refusal_below_admission(&module, &Ty::Enum(EnumId::new(0))).to_string(),
        niche_carrier_refusal(
            "OptionRef",
            "the descriptor states field offsets for 1 variants, the enum has 2"
        )
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
    assert_typed_const_refusal(
        &lower_err(&module),
        "enum.0 (OptionRef) layout",
        "variant 1 (Some): 1 field offsets",
        "2 offsets",
    );
    assert_eq!(
        type_refusal_below_admission(&module, &Ty::Enum(EnumId::new(0))).to_string(),
        niche_carrier_refusal(
            "OptionRef",
            "the descriptor states 2 field offsets for variant 1 (`Some`), which has 1 fields"
        )
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
        origin: None,
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
    let results =
        permit_translate_module(&module).expect("the Direct control must still be admitted");
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
    let results = permit_translate_module(&module)
        .expect("a niche enum emits no tag, so tag semantics cannot be mis-served");
    assert_eq!(
        results[0].0.signature.params,
        vec![Type::Struct(vec![Type::I64])]
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
