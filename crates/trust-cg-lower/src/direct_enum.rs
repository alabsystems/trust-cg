// trust-cg-lower/direct_enum.rs - the emitted direct-tag enum image authority
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! **THE** direct-tag enum layout authority the byte path emits, in one place
//! (ledger L05-P5).
//!
//! A DIRECT-TAG enum stores its discriminant in a tag word. trust-ir gives such
//! an enum two facts the byte path has to honour:
//!
//! * **The tag VALUE table.** Element 0 of trust-ir's enum aggregate is the
//!   variant's EFFECTIVE DISCRIMINANT (`EnumDef::effective_discriminants`), not
//!   its index, and the tag lane's integer type is
//!   `EnumDef::canonical_tag_repr` — the explicit `repr` hint, else the
//!   narrowest type that fits every discriminant, SIGNED when one is negative.
//!   `Ordering { Less = -1, Equal = 0, Greater = 1 }` is an `i8` lane holding
//!   `0xFF`, `0x00`, `0x01`; the reference interpreter decodes that lane
//!   signed (`interpret.rs`, `tag_int_discriminant`) and matches the value
//!   against the same table.
//! * **The producer's LAYOUT.** A v31 `EnumLayoutDescriptor` is normative when
//!   present: its `tag_offset`, `variant_field_offsets`, `size` and `align`
//!   replace the canonical tagged union. rustc lays each variant out as its
//!   own struct behind the tag, so `enum E { A(u8, u32), B(u64) }` is `tag@0,
//!   A.0@1, A.1@4, B.0@8`, 16 bytes, where the canonical shape puts every
//!   payload at byte 8.
//!
//! Before this module the type translation refused every explicit discriminant
//! that was not the variant index, every signed repr, and every descriptor that
//! disagreed with the canonical shape ((c) MEASURED over the 68-module corpus
//! at that tree state: 38 explicit-discriminant enums and 42 layout
//! disagreements failed closed). Now:
//!
//! 1. [`direct_enum_tag_lane`] resolves the tag from trust-ir's own tables and
//!    refuses only what trust-ir itself cannot name — duplicate or overflowing
//!    discriminants, a hint too narrow for the values, a 128-bit lane.
//! 2. [`direct_enum_carrier`] keeps `Type::Enum` for the canonical shape (no
//!    descriptor, or a Direct descriptor that equals it byte for byte) and
//!    otherwise lowers the enum to a BYTE-IMAGE carrier of exactly the declared
//!    size and alignment, so every extent, copy, slot and ABI class is the
//!    producer's.
//! 3. [`DirectEnumImage`] answers every address the byte path emits — the tag
//!    word and each variant field — from the descriptor when there is one, and
//!    from the canonical `Type::Enum` (cross-checked against trust-ir's
//!    `enum_layout_shape`) when there is not. `ExtractField`,
//!    `Constant::Aggregate` and the object writer's global initializer
//!    ([`module_direct_enum_image`]) all read the same image.
//!
//! What stays refused, by name: niche and untagged encodings (their own
//! carriers answer them), 128-bit tag lanes, a descriptor trust-ir's own layout
//! judge declines (a misplaced tag, overlapping or out-of-bounds fields), and
//! `InsertField` on a direct-tag enum (element 0 is a re-tag trust-ir makes
//! undefined behaviour; a payload lane needs fresh-slot value semantics).
//!
//! This is execution-checked lowering evidence, not a proof of enum semantics.

use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
use trust_ir::value::EnumId;
use trust_ir::{EnumDef, Module, Ty};

use crate::adapter::{AdapterError, translate_type_with_enum_tables_inner};
use crate::declared_layout::{LayoutTables, emitted_value_extent};
use crate::types::Type;
use trust_cg_ir::function::EnumTagWidth;

/// The prefix every direct-tag enum refusal carries, so a caller can tell this
/// module's refusals from the niche codec's (`[TCG-NICHE-ENUM]`).
pub const REFUSAL_PREFIX: &str = "[TCG-DIRECT-ENUM]";

/// The one refusal shape for this module.
fn refusal(edef: &EnumDef, reason: impl std::fmt::Display) -> AdapterError {
    AdapterError::UnsupportedType(format!(
        "{REFUSAL_PREFIX} enum {:?} (`{}`): {reason}",
        edef.id, edef.name
    ))
}

/// The tag lane of a direct-tag enum, resolved from trust-ir's own tables and
/// never from the variant count.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectEnumTagLane {
    /// trust-ir's canonical tag repr (`EnumDef::canonical_tag_repr`).
    pub repr: EnumTagRepr,
    /// The LIR tag lane width. The lane carries a bit pattern; signedness
    /// belongs to the reads and compares that consume it.
    pub width: EnumTagWidth,
    /// The trust-ir type element 0 of the enum aggregate carries.
    pub ty: Ty,
    /// The LIR type the tag word is loaded and stored at.
    pub lir: Type,
    /// Every variant's effective discriminant, in variant order.
    pub discriminants: Vec<i128>,
}

impl DirectEnumTagLane {
    /// The lane's width in bytes.
    pub fn bytes(&self) -> u64 {
        u64::from(self.width.bytes())
    }

    /// The variant whose effective discriminant is `disc`.
    pub fn variant_of_discriminant(&self, disc: i128) -> Option<usize> {
        self.discriminants.iter().position(|d| *d == disc)
    }

    /// The `Iconst` immediate that stores `disc` in this lane.
    ///
    /// The backend treats an immediate as a raw bit pattern and lets each use
    /// site extend it by its own signedness, so a negative discriminant is its
    /// two's-complement pattern (`-1` in an `i8` lane is the byte `0xFF`) and
    /// a `u64` value above `i64::MAX` is its unsigned bit pattern. A value the
    /// repr cannot hold is refused, never truncated.
    pub fn immediate(&self, disc: i128) -> Result<i64, String> {
        if !self.repr.fits(disc) {
            return Err(format!(
                "discriminant {disc} does not fit the {} tag lane",
                self.repr
            ));
        }
        match i64::try_from(disc) {
            Ok(imm) => Ok(imm),
            // `fits` bounds `disc` to `u64::MAX` here, so the truncating cast
            // to `u64` is exact and the `i64` reinterpretation is the pattern.
            Err(_) => Ok(disc as u64 as i64),
        }
    }
}

/// Resolve the tag lane of `edef` from trust-ir's own discriminant and repr
/// rules. `Err(reason)` names what trust-ir itself cannot name.
pub fn direct_enum_tag_lane(edef: &EnumDef) -> Result<DirectEnumTagLane, String> {
    if edef.variants.is_empty() {
        return Err(
            "has no variants, so no tag value names one (an uninhabited enum has no layout)"
                .to_string(),
        );
    }
    let discriminants = edef.effective_discriminants().ok_or_else(|| {
        format!(
            "EnumDef.discriminants {:?} has no canonical assignment (a duplicate value, or an \
             implicit increment that overflows)",
            edef.discriminants
        )
    })?;
    let repr = edef.canonical_tag_repr().ok_or_else(|| match edef.repr {
        Some(hint) => format!(
            "EnumDef.repr {hint:?} cannot hold every effective discriminant {discriminants:?}"
        ),
        None => format!(
            "no 64-bit tag type holds every effective discriminant {discriminants:?}; only an \
             explicit 128-bit repr could, and that lane is refused"
        ),
    })?;
    let width = match repr {
        EnumTagRepr::U8 | EnumTagRepr::I8 => EnumTagWidth::U8,
        EnumTagRepr::U16 | EnumTagRepr::I16 => EnumTagWidth::U16,
        EnumTagRepr::U32 | EnumTagRepr::I32 => EnumTagWidth::U32,
        EnumTagRepr::U64 | EnumTagRepr::I64 => EnumTagWidth::U64,
        // v45 (WS3.14(b)): there is no 128-bit tag lane. `EnumTagWidth` tops
        // out at `U64`, so a declared 128-bit tag is refused rather than
        // narrowed onto the widest lane that exists.
        EnumTagRepr::U128 | EnumTagRepr::I128 => {
            return Err(format!(
                "EnumDef.repr {repr:?} is a 128-bit tag lane (trust-ir v45); the widest tag lane \
                 is 64 bits and a declared 128-bit tag is refused rather than narrowed"
            ));
        }
    };
    let lir = match width {
        EnumTagWidth::U8 => Type::I8,
        EnumTagWidth::U16 => Type::I16,
        EnumTagWidth::U32 => Type::I32,
        EnumTagWidth::U64 => Type::I64,
    };
    Ok(DirectEnumTagLane {
        repr,
        width,
        ty: repr.ty(),
        lir,
        discriminants,
    })
}

/// One payload field of a direct-tag enum image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectEnumField {
    /// Byte offset of the field within the enum image.
    pub offset: u64,
    /// The field's AUTHORITATIVE extent in bytes — what a copy of it moves
    /// (`crate::declared_layout::emitted_value_extent`), which a declared
    /// struct layout can make smaller than its natural-C carrier.
    pub extent: u64,
    /// The field's trust-ir type.
    pub ty: Ty,
    /// The field's LIR type.
    pub lir: Type,
}

/// Who placed the tag word and the payload fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectEnumLayoutSource {
    /// The producer's v31 descriptor, read verbatim.
    Descriptor,
    /// trust-cg's canonical `Type::Enum`, cross-checked against trust-ir's
    /// `enum_layout_shape` before any address was emitted.
    Canonical,
}

/// Every address the byte path emits for a direct-tag enum, and the facts a
/// tag write needs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectEnumImage {
    pub enum_id: EnumId,
    pub enum_name: String,
    /// The tag lane.
    pub tag: DirectEnumTagLane,
    /// Byte offset of the tag word.
    pub tag_offset: u64,
    /// Total size in bytes.
    pub size: u64,
    /// Alignment in bytes.
    pub align: u64,
    /// Per variant, per field, in declaration order.
    pub variants: Vec<Vec<DirectEnumField>>,
    pub source: DirectEnumLayoutSource,
    /// The LIR type the enum lowers to: `Type::Enum` for the canonical shape,
    /// else the byte-image carrier of the declared size and alignment.
    pub carrier: Type,
}

impl DirectEnumImage {
    /// The variant whose effective discriminant is `disc`.
    pub fn variant_of_discriminant(&self, disc: i128) -> Option<usize> {
        self.tag.variant_of_discriminant(disc)
    }
}

/// The `EnumDef` behind `ty` when `ty` is a DIRECT-TAG `Ty::Enum`: one with
/// no producer descriptor, or a `Direct`-encoded one. Niche and untagged
/// encodings answer `None`; their carriers are answered elsewhere.
pub(crate) fn direct_enum_def<'a>(ty: &Ty, enums: &'a [EnumDef]) -> Option<&'a EnumDef> {
    let Ty::Enum(eid) = ty else {
        return None;
    };
    let edef = enums.iter().find(|e| e.id == *eid)?;
    match edef.layout.as_ref().map(|layout| &layout.encoding) {
        None | Some(EnumTagEncoding::Direct { .. }) => Some(edef),
        Some(
            EnumTagEncoding::Niche { .. }
            | EnumTagEncoding::Untagged
            | EnumTagEncoding::SingleInhabited { .. },
        ) => None,
    }
}

/// trust-cg's own payload offset in the canonical `Type::Enum` image.
///
/// Every canonical projection reads the number here, so the
/// `perturb_enum_canonical_layout` mutation knob (feature `mutation-knobs`)
/// can move it and prove the canonical-agreement check catches a trust-cg
/// layout that differs from trust-ir's.
pub(crate) fn canonical_payload_offset(lowered: &Type) -> Option<u32> {
    let offset = lowered.enum_payload_offset()?;
    #[cfg(feature = "mutation-knobs")]
    if crate::mutation_knobs::perturb_enum_canonical_layout() {
        return offset.checked_add(1);
    }
    Some(offset)
}

/// Does the producer's declared layout describe EXACTLY the image the
/// canonical tagged-union shape already emits?
///
/// `Ok(())` means the two are indistinguishable, so emitting the canonical
/// shape emits the declared one. `Err(reason)` names the first axis on which
/// they differ, and the caller lowers the enum to the byte-image carrier the
/// descriptor itself describes instead.
///
/// Only [`EnumTagEncoding::Direct`] can agree. `Niche` and `Untagged` both omit
/// the tag lane that `Type::Enum` necessarily emits, so "agreement" is not even
/// definable for either encoding — they are reported as differences, never
/// silently accepted.
pub(crate) fn enum_layout_matches_canonical(
    layout: &EnumLayoutDescriptor,
    lowered: &Type,
) -> Result<(), String> {
    let tag_offset = match layout.encoding {
        EnumTagEncoding::Direct { tag_offset } => tag_offset,
        EnumTagEncoding::Niche { .. } => {
            return Err("niche tag encoding; the LIR enum has no niche representation".to_string());
        }
        EnumTagEncoding::Untagged | EnumTagEncoding::SingleInhabited { .. } => {
            return Err(
                "untagged encoding; the LIR enum has no tag-free representation".to_string(),
            );
        }
    };
    // The canonical shape puts the tag at offset 0, by construction.
    if tag_offset != 0 {
        return Err(format!("tag at byte {tag_offset}, canonical puts it at 0"));
    }
    let Type::Enum { variants, .. } = lowered else {
        return Err("lowered type is not an enum".to_string());
    };
    let canonical_size = u64::from(lowered.bytes());
    if layout.size != canonical_size {
        return Err(format!(
            "size {} vs canonical {canonical_size}",
            layout.size
        ));
    }
    let canonical_align = u64::from(lowered.align());
    if layout.align != canonical_align {
        return Err(format!(
            "align {} vs canonical {canonical_align}",
            layout.align
        ));
    }
    let Some(payload_offset) = lowered.enum_payload_offset() else {
        return Err("canonical payload offset is undefined".to_string());
    };
    if layout.variant_field_offsets.len() > variants.len() {
        return Err(format!(
            "layout describes {} variants, the enum has {}",
            layout.variant_field_offsets.len(),
            variants.len()
        ));
    }
    for (vi, offsets) in layout.variant_field_offsets.iter().enumerate() {
        let fields = &variants[vi];
        if offsets.len() > fields.len() {
            return Err(format!(
                "variant {vi} layout describes {} fields, the variant has {}",
                offsets.len(),
                fields.len()
            ));
        }
        let variant_struct = Type::Struct(fields.clone());
        for (fi, declared) in offsets.iter().enumerate() {
            let Some(natural) = variant_struct.offset_of(fi) else {
                return Err(format!("variant {vi} field {fi} has no canonical offset"));
            };
            let canonical = u64::from(payload_offset) + u64::from(natural);
            if *declared != canonical {
                return Err(format!(
                    "variant {vi} field {fi} at byte {declared}, canonical puts it at {canonical}"
                ));
            }
        }
    }
    Ok(())
}

/// The LIR types of every variant's payload fields, through the same
/// translation the rest of the byte path uses.
fn variant_lir_types(
    edef: &EnumDef,
    tables: LayoutTables<'_>,
    refinements_validated: bool,
    depth: usize,
) -> Result<Vec<Vec<Type>>, AdapterError> {
    edef.variants
        .iter()
        .map(|variant| {
            variant
                .fields
                .iter()
                .map(|field| {
                    translate_type_with_enum_tables_inner(
                        field,
                        tables.structs,
                        tables.types,
                        tables.enums,
                        tables.records,
                        tables.closures,
                        refinements_validated,
                        depth,
                    )
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect()
}

/// The opaque carrier of a producer-laid-out enum: a `Type::Struct` holding
/// one array of the alignment's integer unit, which reproduces the declared
/// size and alignment and nothing else. Every address inside it comes from
/// the [`DirectEnumImage`], never from the carrier's own field walk.
fn byte_image_carrier(size: u64, align: u64) -> Result<Type, String> {
    let unit = match align {
        1 => Type::I8,
        2 => Type::I16,
        4 => Type::I32,
        8 => Type::I64,
        16 => Type::I128,
        other => {
            return Err(format!(
                "declares align {other}; the byte-image carrier expresses power-of-two alignments \
                 from 1 to 16 bytes"
            ));
        }
    };
    if size == 0 || !size.is_multiple_of(align) {
        return Err(format!(
            "declares size {size} for align {align}; a direct-tag image is at least its tag lane \
             and a multiple of its alignment"
        ));
    }
    let count = u32::try_from(size / align)
        .map_err(|_| format!("declares size {size}, which does not fit the u32 LIR carrier"))?;
    let carrier = Type::Struct(vec![Type::Array(Box::new(unit), count)]);
    if carrier.checked_bytes() != Some(size) || u64::from(carrier.align()) != align {
        return Err(format!(
            "declares size {size} align {align}, which the byte-image carrier does not reproduce"
        ));
    }
    Ok(carrier)
}

fn ranges_overlap(a_start: u64, a_len: u64, b_start: u64, b_len: u64) -> bool {
    a_len != 0
        && b_len != 0
        && a_start < b_start.saturating_add(b_len)
        && b_start < a_start.saturating_add(a_len)
}

/// The image the producer's `Direct` descriptor declares, validated field by
/// field against the tag lane and the carrier's extents. `carrier` is the
/// LIR type the enum lowers to and must reproduce the declared size and
/// alignment.
///
/// This is an admission check, never a synthesis: every number in the image
/// is the descriptor's own, and any of them the byte path could not emit
/// exactly refuses the enum by name.
fn descriptor_image(
    edef: &EnumDef,
    layout: &EnumLayoutDescriptor,
    lane: &DirectEnumTagLane,
    variants: &[Vec<Type>],
    tables: LayoutTables<'_>,
    carrier: Type,
) -> Result<DirectEnumImage, AdapterError> {
    let EnumTagEncoding::Direct { tag_offset } = layout.encoding else {
        return Err(refusal(
            edef,
            "the descriptor is not Direct-encoded; niche and untagged images have their own carriers",
        ));
    };
    if layout.align == 0 || !layout.align.is_power_of_two() {
        return Err(refusal(
            edef,
            format!(
                "EnumDef.layout declares align {}, which is not a power of two",
                layout.align
            ),
        ));
    }
    if carrier.checked_bytes() != Some(layout.size) || u64::from(carrier.align()) != layout.align {
        return Err(refusal(
            edef,
            format!(
                "EnumDef.layout declares size {} align {}, which the carrier {carrier:?} does not \
                 reproduce",
                layout.size, layout.align
            ),
        ));
    }
    if layout.variant_field_offsets.len() != edef.variants.len() {
        return Err(refusal(
            edef,
            format!(
                "EnumDef.layout states field offsets for {} variants, the enum has {}",
                layout.variant_field_offsets.len(),
                edef.variants.len()
            ),
        ));
    }
    let tag_bytes = lane.bytes();
    if tag_bytes > layout.align
        || !tag_offset.is_multiple_of(tag_bytes)
        || tag_offset
            .checked_add(tag_bytes)
            .is_none_or(|end| end > layout.size)
    {
        return Err(refusal(
            edef,
            format!(
                "EnumDef.layout places the {}-byte {} tag at byte {tag_offset} of a {}-byte, \
                 {}-aligned image, which is out of bounds, misaligned or over-aligned",
                tag_bytes, lane.repr, layout.size, layout.align
            ),
        ));
    }
    let mut image_variants = Vec::with_capacity(edef.variants.len());
    for (vi, ((variant, offsets), lir_fields)) in edef
        .variants
        .iter()
        .zip(&layout.variant_field_offsets)
        .zip(variants)
        .enumerate()
    {
        if offsets.len() != variant.fields.len() || lir_fields.len() != variant.fields.len() {
            return Err(refusal(
                edef,
                format!(
                    "EnumDef.layout states {} field offsets for variant {vi} (`{}`), which has {} \
                     fields",
                    offsets.len(),
                    variant.name,
                    variant.fields.len()
                ),
            ));
        }
        let mut fields: Vec<DirectEnumField> = Vec::with_capacity(variant.fields.len());
        let mut extents: Vec<u64> = Vec::with_capacity(variant.fields.len());
        for (fi, ((field_ty, offset), lir)) in variant
            .fields
            .iter()
            .zip(offsets)
            .zip(lir_fields)
            .enumerate()
        {
            let extent = emitted_value_extent(field_ty, lir, tables)?;
            let field_align = u64::from(lir.align());
            if field_align > layout.align
                || !offset.is_multiple_of(field_align)
                || offset
                    .checked_add(extent)
                    .is_none_or(|end| end > layout.size)
            {
                return Err(refusal(
                    edef,
                    format!(
                        "EnumDef.layout places variant {vi} (`{}`) field {fi} ({field_ty:?}, \
                         {extent} bytes, align {field_align}) at byte {offset} of a {}-byte, \
                         {}-aligned image, which is out of bounds, misaligned or over-aligned",
                        variant.name, layout.size, layout.align
                    ),
                ));
            }
            if ranges_overlap(tag_offset, tag_bytes, *offset, extent) {
                return Err(refusal(
                    edef,
                    format!(
                        "EnumDef.layout places variant {vi} (`{}`) field {fi} at bytes \
                         {offset}..{} over the tag word at bytes {tag_offset}..{}",
                        variant.name,
                        offset + extent,
                        tag_offset + tag_bytes
                    ),
                ));
            }
            for (pi, (previous, previous_extent)) in fields.iter().zip(&extents).enumerate() {
                if ranges_overlap(previous.offset, *previous_extent, *offset, extent) {
                    return Err(refusal(
                        edef,
                        format!(
                            "EnumDef.layout places variant {vi} (`{}`) field {fi} at bytes \
                             {offset}..{} over its field {pi} at bytes {}..{}",
                            variant.name,
                            offset + extent,
                            previous.offset,
                            previous.offset + previous_extent
                        ),
                    ));
                }
            }
            fields.push(DirectEnumField {
                offset: *offset,
                extent,
                ty: field_ty.clone(),
                lir: lir.clone(),
            });
            extents.push(extent);
        }
        image_variants.push(fields);
    }
    Ok(DirectEnumImage {
        enum_id: edef.id,
        enum_name: edef.name.clone(),
        tag: lane.clone(),
        tag_offset,
        size: layout.size,
        align: layout.align,
        variants: image_variants,
        source: DirectEnumLayoutSource::Descriptor,
        carrier,
    })
}

/// The image of the canonical `Type::Enum` `lowered`: the tag at byte 0 and
/// each variant's fields C-style from `payload_offset`.
fn canonical_image(
    edef: &EnumDef,
    lane: DirectEnumTagLane,
    lowered: &Type,
    payload_offset: u32,
) -> Result<DirectEnumImage, AdapterError> {
    let Type::Enum { variants, .. } = lowered else {
        return Err(refusal(
            edef,
            format!("the canonical carrier {lowered:?} is not a tagged union"),
        ));
    };
    let size = lowered.checked_bytes().ok_or_else(|| {
        refusal(
            edef,
            "the canonical carrier's extent does not fit the u32 LIR carrier",
        )
    })?;
    if variants.len() != edef.variants.len() {
        return Err(refusal(
            edef,
            format!(
                "the canonical carrier has {} variants, the enum has {}",
                variants.len(),
                edef.variants.len()
            ),
        ));
    }
    let mut image_variants = Vec::with_capacity(variants.len());
    for (vi, (variant, lir_fields)) in edef.variants.iter().zip(variants).enumerate() {
        if lir_fields.len() != variant.fields.len() {
            return Err(refusal(
                edef,
                format!(
                    "the canonical carrier gives variant {vi} (`{}`) {} fields, the variant has {}",
                    variant.name,
                    lir_fields.len(),
                    variant.fields.len()
                ),
            ));
        }
        let variant_struct = Type::Struct(lir_fields.clone());
        let mut fields = Vec::with_capacity(lir_fields.len());
        for (fi, (field_ty, lir)) in variant.fields.iter().zip(lir_fields).enumerate() {
            let offset = variant_struct
                .offset_of(fi)
                .and_then(|natural| payload_offset.checked_add(natural))
                .ok_or_else(|| {
                    refusal(
                        edef,
                        format!(
                            "the canonical carrier computes no offset for variant {vi} (`{}`) \
                             field {fi}",
                            variant.name
                        ),
                    )
                })?;
            let extent = lir.checked_bytes().ok_or_else(|| {
                refusal(
                    edef,
                    format!(
                        "the canonical carrier's variant {vi} (`{}`) field {fi} has no u32 extent",
                        variant.name
                    ),
                )
            })?;
            fields.push(DirectEnumField {
                offset: u64::from(offset),
                extent,
                ty: field_ty.clone(),
                lir: lir.clone(),
            });
        }
        image_variants.push(fields);
    }
    Ok(DirectEnumImage {
        enum_id: edef.id,
        enum_name: edef.name.clone(),
        tag: lane,
        tag_offset: 0,
        size,
        align: u64::from(lowered.align()),
        variants: image_variants,
        source: DirectEnumLayoutSource::Canonical,
        carrier: lowered.clone(),
    })
}

/// THE CANONICAL-AGREEMENT PRECONDITION for a descriptor-less enum (WS7.6).
///
/// Without a producer descriptor, trust-cg lays the enum out as its own
/// `Type::Enum` and trust-ir lays it out by `Module::enum_layout_shape`. The
/// same value crosses memory between them: a `Store`, a by-address parameter,
/// Clean's heap. So before any address is emitted, the two layouts must be
/// EQUAL on every axis a byte of the value depends on: tag width, total size,
/// alignment, the shared payload offset, and every variant field's offset and
/// size. trust-ir's per-field offsets are recomputed from its own
/// `ty_layout_shape` of each field, by the C-style rule `enum_layout_shape`
/// documents, never from trust-cg's `Type`.
pub(crate) fn check_canonical_agreement(
    module: &Module,
    edef: &EnumDef,
    lowered: &Type,
    payload_offset: u32,
) -> Result<(), AdapterError> {
    let disagrees = |axis: String| AdapterError::EnumCanonicalLayoutDisagrees {
        enum_id: edef.id.index(),
        enum_name: edef.name.clone(),
        axis,
    };
    let overflow = || disagrees("layout arithmetic (a byte offset overflows)".to_string());
    let shape = module.enum_layout_shape(edef.id).map_err(|error| {
        disagrees(format!(
            "availability (trust-ir computes no canonical layout: {error:?})"
        ))
    })?;
    let Type::Enum {
        tag_width,
        variants: lir_variants,
    } = lowered
    else {
        return Err(disagrees(
            "representation (trust-cg did not lower it to a tagged union)".to_string(),
        ));
    };
    let tag_bits = u64::from(tag_width.bytes()) * 8;
    if shape.tag_size_bits != tag_bits {
        return Err(disagrees(format!(
            "tag width (trust-ir {} bits, trust-cg {tag_bits} bits)",
            shape.tag_size_bits
        )));
    }
    let size_bits = lowered
        .checked_bytes()
        .and_then(|bytes| bytes.checked_mul(8))
        .ok_or_else(overflow)?;
    if shape.size_bits != size_bits {
        return Err(disagrees(format!(
            "size (trust-ir {} bits, trust-cg {size_bits} bits)",
            shape.size_bits
        )));
    }
    let align_bits = u64::from(lowered.align()) * 8;
    if shape.align_bits != align_bits {
        return Err(disagrees(format!(
            "alignment (trust-ir {} bits, trust-cg {align_bits} bits)",
            shape.align_bits
        )));
    }
    let payload_bits = u64::from(payload_offset) * 8;
    if shape.payload_offset_bits != payload_bits {
        return Err(disagrees(format!(
            "payload offset (trust-ir {} bits, trust-cg {payload_bits} bits)",
            shape.payload_offset_bits
        )));
    }
    if lir_variants.len() != edef.variants.len() {
        return Err(disagrees(format!(
            "variant count (trust-ir {}, trust-cg {})",
            edef.variants.len(),
            lir_variants.len()
        )));
    }
    for (vi, (variant, lir_fields)) in edef.variants.iter().zip(lir_variants).enumerate() {
        if variant.fields.len() != lir_fields.len() {
            return Err(disagrees(format!(
                "variant {vi} (`{}`) field count (trust-ir {}, trust-cg {})",
                variant.name,
                variant.fields.len(),
                lir_fields.len()
            )));
        }
        let lir_struct = Type::Struct(lir_fields.clone());
        let mut offset_bits: u64 = 0;
        for (fi, (field_ty, lir_field)) in variant.fields.iter().zip(lir_fields).enumerate() {
            let field = module.ty_layout_shape(field_ty).map_err(|error| {
                disagrees(format!(
                    "variant {vi} (`{}`) field {fi} (trust-ir computes no layout for \
                     {field_ty:?}: {error:?})",
                    variant.name
                ))
            })?;
            let field_align_bits = field
                .align_bits
                .ok_or_else(|| {
                    disagrees(format!(
                        "variant {vi} (`{}`) field {fi} (trust-ir gives {field_ty:?} no \
                         alignment)",
                        variant.name
                    ))
                })?
                .max(8);
            offset_bits = offset_bits
                .div_ceil(field_align_bits)
                .checked_mul(field_align_bits)
                .ok_or_else(overflow)?;
            let ir_offset_bits = shape
                .payload_offset_bits
                .checked_add(offset_bits)
                .ok_or_else(overflow)?;
            let cg_offset_bits = lir_struct
                .offset_of(fi)
                .map(|natural| (u64::from(payload_offset) + u64::from(natural)) * 8);
            if cg_offset_bits != Some(ir_offset_bits) {
                return Err(disagrees(format!(
                    "variant {vi} (`{}`) field {fi} offset (trust-ir {ir_offset_bits} bits, \
                     trust-cg {cg_offset_bits:?} bits)",
                    variant.name
                )));
            }
            let cg_size_bits = lir_field
                .checked_bytes()
                .and_then(|bytes| bytes.checked_mul(8))
                .ok_or_else(overflow)?;
            if field.size_bits != cg_size_bits {
                return Err(disagrees(format!(
                    "variant {vi} (`{}`) field {fi} size (trust-ir {} bits, trust-cg \
                     {cg_size_bits} bits)",
                    variant.name, field.size_bits
                )));
            }
            offset_bits = offset_bits
                .checked_add(field.size_bits)
                .ok_or_else(overflow)?;
        }
    }
    Ok(())
}

/// The LIR type a direct-tag enum lowers to.
///
/// * The tag lane comes from trust-ir's tables ([`direct_enum_tag_lane`]).
/// * With no descriptor, or a `Direct` descriptor that
///   [`enum_layout_matches_canonical`] finds byte-identical to the canonical
///   shape, the carrier is `Type::Enum` — the encoding every existing
///   canonical projection reads.
/// * A `Direct` descriptor that differs is admitted through
///   [`descriptor_image`] and lowered to the byte-image carrier of exactly its
///   declared size and alignment; a descriptor that admission declines refuses
///   the type here, before any function is translated.
pub(crate) fn direct_enum_carrier(
    edef: &EnumDef,
    tables: LayoutTables<'_>,
    refinements_validated: bool,
    depth: usize,
) -> Result<Type, AdapterError> {
    let lane = direct_enum_tag_lane(edef).map_err(|reason| refusal(edef, reason))?;
    let variants = variant_lir_types(edef, tables, refinements_validated, depth)?;
    let canonical = Type::Enum {
        tag_width: lane.width,
        variants,
    };
    let Some(layout) = edef.layout.as_ref() else {
        return Ok(canonical);
    };
    if enum_layout_matches_canonical(layout, &canonical).is_ok() {
        return Ok(canonical);
    }
    let Type::Enum { variants, .. } = &canonical else {
        return Err(refusal(edef, "the canonical carrier is not a tagged union"));
    };
    let carrier = byte_image_carrier(layout.size, layout.align)
        .map_err(|reason| refusal(edef, format!("EnumDef.layout {reason}")))?;
    let image = descriptor_image(edef, layout, &lane, variants, tables, carrier)?;
    Ok(image.carrier)
}

/// The image of the direct-tag enum `edef`, whose type translation produced
/// `lowered`.
///
/// A descriptor is read verbatim and, when the module is at hand, must also be
/// a layout trust-ir itself computes (`Module::enum_layout_shape`): the
/// reference interpreter refuses an enum whose descriptor its layout judge
/// declines, and nothing is emitted for one either. A descriptor-less enum
/// needs the module for [`check_canonical_agreement`]; `payload_offset` is the
/// (mutation-knob-aware) canonical payload offset the caller read from
/// `lowered`.
pub(crate) fn direct_enum_image(
    edef: &EnumDef,
    tables: LayoutTables<'_>,
    lowered: &Type,
    payload_offset: Option<u32>,
    module: Option<&Module>,
) -> Result<DirectEnumImage, AdapterError> {
    let lane = direct_enum_tag_lane(edef).map_err(|reason| refusal(edef, reason))?;
    match edef.layout.as_ref() {
        Some(layout) => {
            let variants = variant_lir_types(edef, tables, true, 1)?;
            let image = descriptor_image(edef, layout, &lane, &variants, tables, lowered.clone())?;
            if let Some(module) = module {
                module.enum_layout_shape(edef.id).map_err(|error| {
                    refusal(
                        edef,
                        format!(
                            "trust-ir computes no layout for its own descriptor ({error:?}); the \
                             reference interpreter refuses this enum, so nothing is emitted for it"
                        ),
                    )
                })?;
            }
            Ok(image)
        }
        None => {
            let module = module.ok_or(AdapterError::ModuleNotSet)?;
            let payload_offset =
                payload_offset.ok_or_else(|| AdapterError::EnumCanonicalLayoutDisagrees {
                    enum_id: edef.id.index(),
                    enum_name: edef.name.clone(),
                    axis: "payload offset (trust-cg has none)".to_string(),
                })?;
            check_canonical_agreement(module, edef, lowered, payload_offset)?;
            canonical_image(edef, lane, lowered, payload_offset)
        }
    }
}

/// The image of direct-tag enum `id` of `module`, for a consumer outside the
/// function adapter — the object writer's global initializer. It resolves the
/// carrier through the same type translation and the same admission the
/// function path uses, so a global's bytes and the code that reads them come
/// from one authority.
pub fn module_direct_enum_image(
    module: &Module,
    id: EnumId,
) -> Result<DirectEnumImage, AdapterError> {
    let ty = Ty::Enum(id);
    let Some(edef) = module.enums.iter().find(|e| e.id == id) else {
        return Err(AdapterError::UnsupportedType(format!(
            "{REFUSAL_PREFIX} unknown enum {id:?}"
        )));
    };
    if direct_enum_def(&ty, &module.enums).is_none() {
        return Err(refusal(
            edef,
            "the descriptor is not Direct-encoded; niche and untagged images have their own carriers",
        ));
    }
    let tables = LayoutTables {
        structs: &module.structs,
        types: &module.types,
        enums: &module.enums,
        records: &module.records,
        closures: &module.closure_types,
    };
    let lowered = crate::adapter::translate_type_with_enum_tables(
        &ty,
        tables.structs,
        tables.types,
        tables.enums,
        tables.records,
        tables.closures,
    )?;
    let payload_offset = canonical_payload_offset(&lowered);
    direct_enum_image(edef, tables, &lowered, payload_offset, Some(module))
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::EnumVariant;

    fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
        EnumVariant {
            name: name.to_string(),
            fields,
            field_names: Vec::new(),
        }
    }

    fn ordering() -> EnumDef {
        EnumDef::new(
            EnumId::new(0),
            "Ordering",
            vec![
                variant("Less", vec![]),
                variant("Equal", vec![]),
                variant("Greater", vec![]),
            ],
        )
        .with_discriminants(vec![Some(-1), Some(0), Some(1)])
        .with_repr(EnumTagRepr::I8)
    }

    #[test]
    fn signed_tag_lane_holds_the_two_s_complement_pattern() {
        let lane = direct_enum_tag_lane(&ordering()).expect("Ordering has an i8 lane");
        assert_eq!(lane.repr, EnumTagRepr::I8);
        assert_eq!(lane.lir, Type::I8);
        assert_eq!(lane.discriminants, vec![-1, 0, 1]);
        assert_eq!(lane.immediate(-1), Ok(-1));
        assert_eq!(lane.variant_of_discriminant(1), Some(2));
        assert!(lane.immediate(200).is_err(), "200 does not fit i8");
    }

    #[test]
    fn inferred_lane_is_the_narrowest_signed_type_and_u64_patterns_are_raw_bits() {
        let inferred = EnumDef::new(
            EnumId::new(1),
            "Inferred",
            vec![variant("a", vec![]), variant("b", vec![])],
        )
        .with_discriminants(vec![Some(-300), Some(5)]);
        let lane = direct_enum_tag_lane(&inferred).expect("i16 lane");
        assert_eq!(lane.repr, EnumTagRepr::I16);
        assert_eq!(lane.width, EnumTagWidth::U16);

        let wide = EnumDef::new(EnumId::new(2), "Wide", vec![variant("a", vec![])])
            .with_discriminants(vec![Some(u64::MAX as i128)])
            .with_repr(EnumTagRepr::U64);
        let lane = direct_enum_tag_lane(&wide).expect("u64 lane");
        assert_eq!(lane.immediate(u64::MAX as i128), Ok(-1));
    }

    #[test]
    fn what_trust_ir_cannot_name_is_refused() {
        let duplicate = EnumDef::new(
            EnumId::new(3),
            "Dup",
            vec![variant("a", vec![]), variant("b", vec![])],
        )
        .with_discriminants(vec![Some(4), Some(4)]);
        assert!(
            direct_enum_tag_lane(&duplicate)
                .unwrap_err()
                .contains("EnumDef.discriminants")
        );
        let narrow = EnumDef::new(EnumId::new(4), "Narrow", vec![variant("a", vec![])])
            .with_discriminants(vec![Some(300)])
            .with_repr(EnumTagRepr::U8);
        assert!(
            direct_enum_tag_lane(&narrow)
                .unwrap_err()
                .contains("EnumDef.repr")
        );
        let wide = EnumDef::new(EnumId::new(5), "Wide", vec![variant("a", vec![])])
            .with_repr(EnumTagRepr::I128);
        assert!(direct_enum_tag_lane(&wide).unwrap_err().contains("128-bit"));
        let empty = EnumDef::new(EnumId::new(6), "Empty", vec![]);
        assert!(
            direct_enum_tag_lane(&empty)
                .unwrap_err()
                .contains("no variants")
        );
    }

    #[test]
    fn byte_image_carrier_reproduces_size_and_align() {
        assert_eq!(
            byte_image_carrier(16, 8),
            Ok(Type::Struct(vec![Type::Array(Box::new(Type::I64), 2)]))
        );
        assert_eq!(
            byte_image_carrier(1, 1),
            Ok(Type::Struct(vec![Type::Array(Box::new(Type::I8), 1)]))
        );
        assert!(byte_image_carrier(12, 8).is_err(), "not a multiple");
        assert!(byte_image_carrier(0, 1).is_err(), "empty");
        assert!(byte_image_carrier(32, 32).is_err(), "over-aligned");
    }
}
