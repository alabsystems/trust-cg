// trust-cg-lower/niche_codec.rs - the discriminant codec of a niche-encoded enum
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The DISCRIMINANT half of a trust-ir niche-encoded `Ty::Enum`.
//!
//! [`crate::adapter`] admits a niche enum as the payload struct its producer
//! descriptor describes (`niche_enum_carrier`). That admission answers where
//! the payload bytes are. This module answers the other question: how the
//! discriminant is stored in, and recovered from, otherwise-invalid values of
//! one payload lane.
//!
//! # The formula
//!
//! It is trust-ir's own (`interpret.rs`, `EnumByteView::Niche`) and the one the
//! rustc bridge ports from `rustc_codegen_ssa` (`lower_niche_discriminant_decode`,
//! `store_memory_niche_tag`). With `w` the lane width in bits:
//!
//! ```text
//! encode(variant v != untagged) = (niche_start + (v - niche_variants_start)) mod 2^w
//! encode(untagged)              = nothing; the payload's own value is the lane
//! decode(lane):
//!     relative = (lane - niche_start) mod 2^w
//!     variant  = relative <=u (niche_variants_end - niche_variants_start)
//!                    ? niche_variants_start + relative
//!                    : untagged_variant
//! ```
//!
//! The niche arithmetic is over variant INDICES. trust-ir's value model puts
//! the variant's effective DISCRIMINANT at element 0, so the codec also maps
//! index to discriminant. That mapping is affine over the niche range only when
//! the discriminants of `niche_variants_start..=niche_variants_end` step by
//! one; anything else is refused rather than lowered through a lookup table.
//! rustc never niche-encodes an enum whose discriminants differ from its
//! variant indices, so the affine case covers every rustc layout.
//!
//! # What is validated, and against what
//!
//! [`niche_codec`] checks the producer's niche parameters against trust-cg's
//! own computed layout, independently of `trust_ir_build::validate_module`
//! (which the adapter does not consume for enum layouts):
//!
//! 1. **Coherent parameters.** The untagged variant exists, the niche variant
//!    interval is ordered and in range, the interval plus the untagged variant
//!    covers every variant exactly, `niche_start` and the interval span fit the
//!    lane width, and the lane is aligned, inside the declared size and no more
//!    aligned than the enum.
//! 2. **The lane is a scalar of the untagged payload.** Walking the untagged
//!    variant's payload through trust-cg's layout authorities (declared struct
//!    layouts, natural-C tuples, authoritative array strides, nested enum
//!    carriers), the lane must coincide exactly, in offset and width, with one
//!    scalar leaf: an integer, `bool`, `char`, pointer, fat-pointer word, a
//!    nested Direct enum's tag or a nested niche enum's own lane. A lane that
//!    straddles fields, lands in padding or covers a float is refused.
//! 3. **Reserved values are invalid payload values.** Where trust-ir's type
//!    states a validity range (`bool` is 0..=1, `char` is a Unicode scalar
//!    value, references, `Rc` and function pointers are non-null, a Direct
//!    enum tag is one of its discriminants, a nested niche lane is its own
//!    payload range plus its own reserved values), no reserved value may be a
//!    valid payload value. Integers and raw pointers state no range, so for
//!    them the reserved range is the producer's invariant, exactly as trust-ir
//!    defines it (its interpreter refuses to store an untagged payload that
//!    occupies a reserved value).
//! 4. **Niche-tagged variants leave the lane alone.** No non-zero-sized field
//!    of a niche-tagged variant overlaps the lane.
//! 5. **The discriminant is nameable.** trust-ir can assign the enum a
//!    canonical tag type and effective discriminants, and the niche range's
//!    discriminants step by one.
//!
//! The codec is built only where the discriminant is touched (`ExtractField`
//! and `InsertField` at element 0, and `Constant::Aggregate` construction), so
//! a module that only addresses payload fields keeps exactly the admission it
//! had.

use crate::adapter::{MAX_TYPE_TRANSLATION_DEPTH, translate_type_with_enum_tables_inner};
use crate::declared_layout::{
    LayoutTables, emitted_field_layout, emitted_struct_layout, struct_def_for_ty,
};
use crate::types::Type;
use trust_ir::ty::{EnumTagEncoding, EnumTagRepr};
use trust_ir::{Constant, EnumDef, Ty};

/// A closed interval of lane values, in the lane's unsigned interpretation.
type LaneInterval = (u128, u128);

/// One step from a payload value to the constant element that holds the lane.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NicheLaneStep {
    /// Element `i` of a struct, tuple, array or fat-pointer constant.
    Element(usize),
    /// Payload field `i` of a nested UNTAGGED enum constant (flat element
    /// `i + 1`, element 0 being its discriminant).
    UntaggedPayload(usize),
}

/// What the lane's bytes are, at the end of the path.
#[derive(Debug, Clone)]
pub(crate) enum NicheLaneLeaf {
    /// A scalar value whose bytes are exactly the lane.
    Scalar,
    /// The tag word of a nested Direct-encoded enum.
    DirectTag,
    /// The lane of a nested niche-encoded enum.
    NestedNiche(Box<NicheCodec>),
}

/// The complete discriminant codec of one niche-encoded enum.
#[derive(Debug, Clone)]
pub(crate) struct NicheCodec {
    pub(crate) enum_id: trust_ir::value::EnumId,
    pub(crate) enum_name: String,
    pub(crate) untagged_variant: usize,
    pub(crate) niche_variants_start: usize,
    pub(crate) niche_variants_end: usize,
    /// `niche_start`, already known to fit the lane.
    pub(crate) niche_start: u128,
    /// Byte offset of the lane within the enum image.
    pub(crate) niche_offset: u64,
    /// Lane width in bytes: 1, 2, 4 or 8.
    pub(crate) lane_bytes: u32,
    /// trust-ir type of element 0: the enum's canonical tag type.
    pub(crate) tag_ty: Ty,
    /// Effective discriminant of every variant, by index.
    pub(crate) discriminants: Vec<i128>,
    /// Declared per-variant field offsets and types.
    pub(crate) variant_offsets: Vec<Vec<u64>>,
    pub(crate) variant_fields: Vec<Vec<Ty>>,
    /// Which untagged-variant payload field holds the lane, and the path
    /// inside that field to the leaf.
    pub(crate) lane_field: usize,
    pub(crate) lane_steps: Vec<NicheLaneStep>,
    pub(crate) lane_leaf: NicheLaneLeaf,
    /// Valid values of the untagged payload at the lane, when trust-ir's type
    /// states them; `None` when the range is the producer's invariant.
    pub(crate) payload_validity: Option<Vec<LaneInterval>>,
}

/// The niche lane's width in bytes, or `None` for a repr this codec has no lane
/// for.
///
/// `None` for the v45 128-bit reprs, and that is not a shortcut. The mask
/// arithmetic below is `(1u128 << (bytes * 8)) - 1`, which at 16 bytes shifts a
/// `u128` by 128 and overflows — so a 16 arm would not merely be unsupported,
/// it would be wrong. The caller refuses instead.
fn lane_bytes_of(repr: EnumTagRepr) -> Option<u32> {
    match repr {
        EnumTagRepr::U8 | EnumTagRepr::I8 => Some(1),
        EnumTagRepr::U16 | EnumTagRepr::I16 => Some(2),
        EnumTagRepr::U32 | EnumTagRepr::I32 => Some(4),
        EnumTagRepr::U64 | EnumTagRepr::I64 => Some(8),
        EnumTagRepr::U128 | EnumTagRepr::I128 => None,
    }
}

fn mask_for_bytes(bytes: u32) -> u128 {
    (1u128 << (bytes * 8)) - 1
}

fn intervals_overlap(
    a: &[LaneInterval],
    b: &[LaneInterval],
) -> Option<(LaneInterval, LaneInterval)> {
    for x in a {
        for y in b {
            if x.0 <= y.1 && y.0 <= x.1 {
                return Some((*x, *y));
            }
        }
    }
    None
}

impl NicheCodec {
    /// All-ones mask of the lane width.
    pub(crate) fn mask(&self) -> u128 {
        mask_for_bytes(self.lane_bytes)
    }

    /// `niche_variants_end - niche_variants_start`.
    pub(crate) fn span(&self) -> u128 {
        (self.niche_variants_end - self.niche_variants_start) as u128
    }

    /// The LIR type of the lane.
    pub(crate) fn lane_lir_ty(&self) -> Type {
        match self.lane_bytes {
            1 => Type::I8,
            2 => Type::I16,
            4 => Type::I32,
            _ => Type::I64,
        }
    }

    /// The lane value that encodes `variant`, or `None` for the untagged
    /// variant, whose payload IS the lane.
    pub(crate) fn reserved_value(&self, variant: usize) -> Option<u128> {
        if variant == self.untagged_variant
            || variant < self.niche_variants_start
            || variant > self.niche_variants_end
        {
            return None;
        }
        let relative = (variant - self.niche_variants_start) as u128;
        Some(self.niche_start.wrapping_add(relative) & self.mask())
    }

    /// True when `lane` is one of the reserved values.
    pub(crate) fn is_reserved(&self, lane: u128) -> bool {
        (lane.wrapping_sub(self.niche_start) & self.mask()) <= self.span()
    }

    /// The reserved values as at most two non-wrapping intervals.
    pub(crate) fn reserved_intervals(&self) -> Vec<LaneInterval> {
        let mask = self.mask();
        let lo = self.niche_start;
        let hi = lo + self.span();
        if hi <= mask {
            vec![(lo, hi)]
        } else {
            vec![(lo, mask), (0, hi - mask - 1)]
        }
    }

    /// Every lane value an object of THIS enum can hold, when known: the
    /// untagged payload's valid values plus the reserved values. Used when
    /// this enum is itself the untagged payload of an outer niche enum.
    fn valid_lane_values(&self) -> Option<Vec<LaneInterval>> {
        let mut values = self.payload_validity.clone()?;
        values.extend(self.reserved_intervals());
        Some(values)
    }

    /// The variant index whose effective discriminant is `disc`.
    pub(crate) fn variant_of_discriminant(&self, disc: i128) -> Option<usize> {
        self.discriminants.iter().position(|d| *d == disc)
    }

    /// Discriminant of `niche_variants_start`; the decode adds the relative
    /// lane value to it.
    pub(crate) fn niche_base_discriminant(&self) -> i128 {
        self.discriminants[self.niche_variants_start]
    }

    /// Discriminant of the untagged variant.
    pub(crate) fn untagged_discriminant(&self) -> i128 {
        self.discriminants[self.untagged_variant]
    }

    /// The lane bits a `Constant::Aggregate` of this enum writes, when they
    /// are statically determined by the constant.
    pub(crate) fn constant_lane_value(&self, elems: &[Constant]) -> Option<u128> {
        let Constant::Int(disc) = elems.first()? else {
            return None;
        };
        let variant = self.variant_of_discriminant(*disc)?;
        if variant != self.untagged_variant {
            return self.reserved_value(variant);
        }
        let mut current = elems.get(1 + self.lane_field)?;
        for (position, step) in self.lane_steps.iter().enumerate() {
            current = match (step, current) {
                (NicheLaneStep::Element(i), Constant::Aggregate(es) | Constant::Array(es)) => {
                    es.get(*i)?
                }
                // trust-ir v50: every in-range element of a uniform array is
                // its one element.
                (NicheLaneStep::Element(i), Constant::Splat { elem, len })
                    if u64::try_from(*i).is_ok_and(|i| i < *len) =>
                {
                    elem
                }
                (NicheLaneStep::Element(i), Constant::Bytes { data, .. }) => {
                    // A byte string can only be the LAST container: its
                    // elements are the leaf itself, one byte each. A wider
                    // lane (a fat-pointer word, say) is not one of its
                    // elements, so the constant does not determine it here.
                    if position + 1 != self.lane_steps.len()
                        || !matches!(self.lane_leaf, NicheLaneLeaf::Scalar)
                        || self.lane_bytes != 1
                    {
                        return None;
                    }
                    return data.get(*i).map(|byte| u128::from(*byte) & self.mask());
                }
                (NicheLaneStep::UntaggedPayload(i), Constant::Aggregate(es)) => es.get(1 + *i)?,
                _ => return None,
            };
        }
        match &self.lane_leaf {
            NicheLaneLeaf::Scalar => match current {
                Constant::Int(v) => Some((*v as u128) & self.mask()),
                Constant::Bool(b) => Some(u128::from(*b)),
                Constant::U128(v) => Some(*v & self.mask()),
                _ => None,
            },
            NicheLaneLeaf::DirectTag => match current {
                Constant::Aggregate(es) => match es.first()? {
                    Constant::Int(d) => Some((*d as u128) & self.mask()),
                    _ => None,
                },
                _ => None,
            },
            NicheLaneLeaf::NestedNiche(inner) => match current {
                Constant::Aggregate(es) => inner.constant_lane_value(es),
                _ => None,
            },
        }
    }
}

/// Byte extent of a value of type `ty` as the byte path lays it out.
fn extent(ty: &Ty, tables: LayoutTables<'_>, depth: usize) -> Result<u64, String> {
    let lir = lir_of(ty, tables, depth)?;
    emitted_field_layout(ty, &lir, tables, depth)
        .map(|layout| layout.size)
        .map_err(|err| format!("{ty:?} has no emitted extent ({err})"))
}

fn lir_of(ty: &Ty, tables: LayoutTables<'_>, depth: usize) -> Result<Type, String> {
    translate_type_with_enum_tables_inner(
        ty,
        tables.structs,
        tables.types,
        tables.enums,
        tables.records,
        tables.closures,
        true,
        depth,
    )
    .map_err(|err| format!("{ty:?} does not translate ({err})"))
}

/// Among `fields` (offset, type), the one non-zero-sized field that contains
/// `[offset, offset + width)`.
fn containing_field(
    fields: &[(u64, Ty)],
    offset: u64,
    width: u64,
    tables: LayoutTables<'_>,
    depth: usize,
    what: &str,
) -> Result<(usize, u64), String> {
    for (index, (field_offset, field_ty)) in fields.iter().enumerate() {
        let size = extent(field_ty, tables, depth)?;
        if size == 0 {
            continue;
        }
        if *field_offset <= offset && offset + width <= field_offset + size {
            return Ok((index, offset - field_offset));
        }
    }
    Err(format!(
        "the {width}-byte lane at byte {offset} of {what} is not contained in one of its \
         non-zero-sized fields (it lands in padding or straddles a field boundary)"
    ))
}

fn scalar_leaf(
    ty: &Ty,
    offset: u64,
    width: u64,
    size: u64,
    validity: Option<Vec<LaneInterval>>,
) -> Result<(NicheLaneLeaf, Option<Vec<LaneInterval>>), String> {
    if offset != 0 || width != size {
        return Err(format!(
            "the {width}-byte lane at byte {offset} of a {size}-byte {ty:?} does not cover the \
             scalar exactly"
        ));
    }
    Ok((NicheLaneLeaf::Scalar, validity))
}

/// Walk `ty` to the scalar leaf at `[offset, offset + width)`, recording the
/// constant-navigation steps, and return the leaf with the valid values
/// trust-ir's type states for it.
fn lane_leaf(
    ty: &Ty,
    offset: u64,
    width: u64,
    tables: LayoutTables<'_>,
    depth: usize,
    steps: &mut Vec<NicheLaneStep>,
) -> Result<(NicheLaneLeaf, Option<Vec<LaneInterval>>), String> {
    if depth >= MAX_TYPE_TRANSLATION_DEPTH {
        return Err(format!(
            "the lane walk exceeds the adapter recursion limit ({MAX_TYPE_TRANSLATION_DEPTH})"
        ));
    }
    let next = depth + 1;
    const NON_NULL: (u128, u128) = (1, u64::MAX as u128);
    match ty {
        Ty::Bool => scalar_leaf(ty, offset, width, 1, Some(vec![(0, 1)])),
        Ty::Char => scalar_leaf(
            ty,
            offset,
            width,
            4,
            Some(vec![(0, 0xD7FF), (0xE000, 0x10_FFFF)]),
        ),
        Ty::I8 | Ty::U8 => scalar_leaf(ty, offset, width, 1, None),
        Ty::I16 | Ty::U16 => scalar_leaf(ty, offset, width, 2, None),
        Ty::I32 | Ty::U32 => scalar_leaf(ty, offset, width, 4, None),
        Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize => scalar_leaf(ty, offset, width, 8, None),
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) => scalar_leaf(ty, offset, width, 8, None),
        Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) | Ty::Func(_) => {
            scalar_leaf(ty, offset, width, 8, Some(vec![NON_NULL]))
        }
        // `{data, metadata}`, two pointer words. Neither word's range is stated
        // by the type (a raw fat pointer may be null), so both are the
        // producer's invariant.
        Ty::FatPtr(_) => {
            if width != 8 || !(offset == 0 || offset == 8) {
                return Err(format!(
                    "the {width}-byte lane at byte {offset} of a fat pointer is not one of its \
                     two pointer words"
                ));
            }
            steps.push(NicheLaneStep::Element((offset / 8) as usize));
            Ok((NicheLaneLeaf::Scalar, None))
        }
        Ty::Struct(_) => {
            let sdef = struct_def_for_ty(ty, tables.structs)
                .ok_or_else(|| format!("{ty:?} is not in the struct table"))?;
            let layout = emitted_struct_layout(sdef, tables)
                .map_err(|err| format!("struct `{}` has no emitted layout ({err})", sdef.name))?;
            let fields: Vec<(u64, Ty)> = layout
                .offsets
                .iter()
                .copied()
                .zip(sdef.fields.iter().map(|field| field.ty.clone()))
                .collect();
            let (index, inner) = containing_field(
                &fields,
                offset,
                width,
                tables,
                next,
                &format!("struct `{}`", sdef.name),
            )?;
            steps.push(NicheLaneStep::Element(index));
            lane_leaf(&fields[index].1, inner, width, tables, next, steps)
        }
        Ty::Tuple(elements) => {
            let lir = lir_of(ty, tables, depth)?;
            let mut fields = Vec::with_capacity(elements.len());
            for (index, element) in elements.iter().enumerate() {
                let field_offset = lir
                    .offset_of(index)
                    .ok_or_else(|| format!("tuple {ty:?} has no offset for element {index}"))?;
                fields.push((u64::from(field_offset), element.clone()));
            }
            let (index, inner) =
                containing_field(&fields, offset, width, tables, next, &format!("{ty:?}"))?;
            steps.push(NicheLaneStep::Element(index));
            lane_leaf(&elements[index], inner, width, tables, next, steps)
        }
        Ty::Array(elem_id, count) => {
            let elem = tables
                .types
                .get(elem_id.as_usize())
                .ok_or_else(|| format!("array element {elem_id:?} is not in the type table"))?;
            let stride = extent(elem, tables, next)?;
            if stride == 0 {
                return Err(format!(
                    "{ty:?} has zero-sized elements and cannot hold a lane"
                ));
            }
            let index = offset / stride;
            if index >= *count {
                return Err(format!(
                    "the lane at byte {offset} is past the end of {ty:?}"
                ));
            }
            steps.push(NicheLaneStep::Element(index as usize));
            lane_leaf(elem, offset % stride, width, tables, next, steps)
        }
        Ty::Enum(eid) => {
            let inner = tables
                .enums
                .iter()
                .find(|e| e.id == *eid)
                .ok_or_else(|| format!("{ty:?} is not in the enum table"))?;
            match inner
                .layout
                .as_ref()
                .map(|layout| (&layout.encoding, layout))
            {
                Some((EnumTagEncoding::Niche { .. }, _)) => {
                    // The inner carrier must itself be admitted.
                    lir_of(ty, tables, depth)?;
                    let codec = niche_codec(inner, tables, next).map_err(|reason| {
                        format!("nested niche enum `{}`: {reason}", inner.name)
                    })?;
                    if offset != codec.niche_offset || width != u64::from(codec.lane_bytes) {
                        return Err(format!(
                            "the lane at byte {offset} ({width} bytes) of nested niche enum `{}` \
                             is not that enum's own niche lane (byte {}, {} bytes); no other \
                             byte of it is valid in every variant",
                            inner.name, codec.niche_offset, codec.lane_bytes
                        ));
                    }
                    let validity = codec.valid_lane_values();
                    Ok((NicheLaneLeaf::NestedNiche(Box::new(codec)), validity))
                }
                Some((
                    EnumTagEncoding::Untagged | EnumTagEncoding::SingleInhabited { .. },
                    layout,
                )) => {
                    lir_of(ty, tables, depth)?;
                    let active = match layout.encoding {
                        EnumTagEncoding::SingleInhabited { variant } => variant as usize,
                        _ => 0,
                    };
                    let (Some(offsets), Some(variant)) = (
                        layout.variant_field_offsets.get(active),
                        inner.variants.get(active),
                    ) else {
                        return Err(format!(
                            "untagged enum `{}` has no sole variant",
                            inner.name
                        ));
                    };
                    let fields: Vec<(u64, Ty)> = offsets
                        .iter()
                        .copied()
                        .zip(variant.fields.iter().cloned())
                        .collect();
                    let (index, rest) = containing_field(
                        &fields,
                        offset,
                        width,
                        tables,
                        next,
                        &format!("untagged enum `{}`", inner.name),
                    )?;
                    steps.push(NicheLaneStep::UntaggedPayload(index));
                    lane_leaf(&fields[index].1, rest, width, tables, next, steps)
                }
                _ => {
                    let lir = lir_of(ty, tables, depth)?;
                    let tag = lir.enum_tag_type().ok_or_else(|| {
                        format!(
                            "enum `{}` lowers to {lir:?}, which has no tag lane",
                            inner.name
                        )
                    })?;
                    let tag_bytes = u64::from(tag.bytes());
                    if offset != 0 || width != tag_bytes {
                        return Err(format!(
                            "the lane at byte {offset} ({width} bytes) of Direct enum `{}` is \
                             not its {tag_bytes}-byte tag word at byte 0",
                            inner.name
                        ));
                    }
                    let discriminants = inner.effective_discriminants().ok_or_else(|| {
                        format!("enum `{}` has no effective discriminants", inner.name)
                    })?;
                    let mask = mask_for_bytes(tag_bytes as u32);
                    let validity = discriminants
                        .iter()
                        .map(|d| {
                            let value = (*d as u128) & mask;
                            (value, value)
                        })
                        .collect();
                    Ok((NicheLaneLeaf::DirectTag, Some(validity)))
                }
            }
        }
        // A refinement is erased to its base after module validation; its
        // constants are base constants, so the walk continues with no step.
        Ty::Refine(base_id, _) => {
            let base = tables
                .types
                .get(base_id.as_usize())
                .ok_or_else(|| format!("refinement base {base_id:?} is not in the type table"))?;
            lane_leaf(base, offset, width, tables, next, steps)
        }
        other => Err(format!(
            "the lane lands in a {other:?}, which is not an integer, bool, char, pointer, fat \
             pointer, struct, tuple, array or enum"
        )),
    }
}

/// Build and validate the codec of niche-encoded `edef`. `Err(reason)` names
/// the first rule the descriptor breaks; the caller fails closed.
pub(crate) fn niche_codec(
    edef: &EnumDef,
    tables: LayoutTables<'_>,
    depth: usize,
) -> Result<NicheCodec, String> {
    if depth >= MAX_TYPE_TRANSLATION_DEPTH {
        return Err(format!(
            "niche enum nesting exceeds the adapter recursion limit ({MAX_TYPE_TRANSLATION_DEPTH})"
        ));
    }
    let layout = edef
        .layout
        .as_ref()
        .ok_or_else(|| "the enum has no layout descriptor".to_string())?;
    let EnumTagEncoding::Niche {
        untagged_variant,
        niche_variants_start,
        niche_variants_end,
        niche_start,
        niche_offset,
        niche_ty,
    } = &layout.encoding
    else {
        return Err("the descriptor is not niche-encoded".to_string());
    };
    let variant_count = edef.variants.len();
    if layout.variant_field_offsets.len() != variant_count {
        return Err(format!(
            "the descriptor states field offsets for {} variants, the enum has {variant_count}",
            layout.variant_field_offsets.len()
        ));
    }
    for (vi, (offsets, variant)) in layout
        .variant_field_offsets
        .iter()
        .zip(&edef.variants)
        .enumerate()
    {
        if offsets.len() != variant.fields.len() {
            return Err(format!(
                "the descriptor states {} field offsets for variant {vi}, which has {} fields",
                offsets.len(),
                variant.fields.len()
            ));
        }
    }

    // 1. COHERENT PARAMETERS.
    let untagged = *untagged_variant as usize;
    let start = *niche_variants_start as usize;
    let end = *niche_variants_end as usize;
    if untagged >= variant_count {
        return Err(format!(
            "untagged_variant {untagged} does not name one of the {variant_count} variants"
        ));
    }
    if start > end || end >= variant_count {
        return Err(format!(
            "the niche variant interval {start}..={end} is not an ordered interval of the \
             {variant_count} variants"
        ));
    }
    let extra = usize::from(!(start..=end).contains(&untagged));
    if end - start + 1 + extra != variant_count {
        return Err(format!(
            "the niche variant interval {start}..={end} plus untagged variant {untagged} does \
             not cover the {variant_count} variants exactly"
        ));
    }
    let Some(lane_bytes) = lane_bytes_of(*niche_ty) else {
        return Err(format!(
            "niche tag repr {niche_ty:?} is 128-bit (trust-ir v45); this codec's lane mask is a \
             u128 and cannot express a 16-byte lane, so the repr is refused rather than narrowed"
        ));
    };
    let mask = mask_for_bytes(lane_bytes);
    if *niche_start > mask {
        return Err(format!(
            "niche_start {niche_start:#x} does not fit the {}-bit lane",
            lane_bytes * 8
        ));
    }
    if ((end - start) as u128) > mask {
        return Err(format!(
            "{} niche variants do not fit the {}-bit lane",
            end - start + 1,
            lane_bytes * 8
        ));
    }
    let lane = u64::from(lane_bytes);
    if lane > layout.align || !niche_offset.is_multiple_of(lane) {
        return Err(format!(
            "the {lane}-byte lane at byte {niche_offset} is misaligned or more aligned than the \
             enum's align {}",
            layout.align
        ));
    }
    if niche_offset
        .checked_add(lane)
        .is_none_or(|lane_end| lane_end > layout.size)
    {
        return Err(format!(
            "the {lane}-byte lane at byte {niche_offset} runs past the declared size {}",
            layout.size
        ));
    }

    // 4. NICHE-TAGGED VARIANTS LEAVE THE LANE ALONE.
    for vi in start..=end {
        if vi == untagged {
            continue;
        }
        for (fi, (field_offset, field_ty)) in layout.variant_field_offsets[vi]
            .iter()
            .zip(&edef.variants[vi].fields)
            .enumerate()
        {
            let size = extent(field_ty, tables, depth + 1)?;
            if size > 0
                && *field_offset < niche_offset + lane
                && *niche_offset < field_offset + size
            {
                return Err(format!(
                    "field {fi} of niche-tagged variant {vi} (`{}`) overlaps the lane at byte \
                     {niche_offset}",
                    edef.variants[vi].name
                ));
            }
        }
    }

    // 2. THE LANE IS A SCALAR OF THE UNTAGGED PAYLOAD.
    let untagged_fields: Vec<(u64, Ty)> = layout.variant_field_offsets[untagged]
        .iter()
        .copied()
        .zip(edef.variants[untagged].fields.iter().cloned())
        .collect();
    let (lane_field, inner_offset) = containing_field(
        &untagged_fields,
        *niche_offset,
        lane,
        tables,
        depth + 1,
        &format!(
            "untagged variant {untagged} (`{}`)",
            edef.variants[untagged].name
        ),
    )?;
    let mut lane_steps = Vec::new();
    let (lane_leaf, payload_validity) = lane_leaf(
        &untagged_fields[lane_field].1,
        inner_offset,
        lane,
        tables,
        depth + 1,
        &mut lane_steps,
    )?;

    // 5. THE DISCRIMINANT IS NAMEABLE.
    let discriminants = edef.effective_discriminants().ok_or_else(|| {
        "the enum has no effective discriminant assignment (duplicate or overflowing values)"
            .to_string()
    })?;
    let tag_ty = edef
        .canonical_tag_repr()
        .ok_or_else(|| {
            "the enum has no canonical tag type (a repr hint too narrow, or a discriminant beyond \
             64 bits), so element 0 has no type"
                .to_string()
        })?
        .ty();
    let base = discriminants[start];
    for k in 0..=(end - start) {
        let expected = base.checked_add(k as i128);
        if expected != Some(discriminants[start + k]) {
            return Err(format!(
                "the niche variants' discriminants do not step by one ({} is variant {}'s, \
                 {base} + {k} expected); the index-to-discriminant map is not affine",
                discriminants[start + k],
                start + k
            ));
        }
    }

    let codec = NicheCodec {
        enum_id: edef.id,
        enum_name: edef.name.clone(),
        untagged_variant: untagged,
        niche_variants_start: start,
        niche_variants_end: end,
        niche_start: *niche_start,
        niche_offset: *niche_offset,
        lane_bytes,
        tag_ty,
        discriminants,
        variant_offsets: layout.variant_field_offsets.clone(),
        variant_fields: edef.variants.iter().map(|v| v.fields.clone()).collect(),
        lane_field,
        lane_steps,
        lane_leaf,
        payload_validity,
    };

    // 3. RESERVED VALUES ARE INVALID PAYLOAD VALUES.
    if let Some(valid) = &codec.payload_validity
        && let Some((reserved, valid_range)) = intervals_overlap(&codec.reserved_intervals(), valid)
    {
        return Err(format!(
            "reserved lane values {:#x}..={:#x} overlap the valid payload values {:#x}..={:#x} \
             of the untagged variant's lane; a valid payload would decode as a niche variant",
            reserved.0, reserved.1, valid_range.0, valid_range.1
        ));
    }
    Ok(codec)
}
