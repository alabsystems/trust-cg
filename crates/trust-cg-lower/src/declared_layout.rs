// trust-cg-lower/declared_layout.rs - the emitted struct-layout authority
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! **THE** struct-layout authority the byte path emits, in one place.
//!
//! # The defect this closes
//!
//! The producer already records rustc's real, authoritative layout. It reads
//! `tcx.layout_of(..)` and stores `layout.fields.offset(i).bytes()` into
//! [`trust_ir::FieldDef::offset`], plus the struct's `size` and `align`
//! (`crates/trust-thir-lower/src/lib.rs:9335-9337` and `:9392-9395`).
//!
//! The byte path used to throw all of that away and RECOMPUTE the layout as
//! declaration-ordered natural C ([`crate::types::Type::offset_of`],
//! `types.rs:169-183`). For `#[repr(Rust)]` — where rustc is free to reorder
//! fields by alignment — the two disagree, and the byte path then computes a
//! different address than the producer specified. (c) MEASURED against stock
//! `rustc 1.97.0`:
//!
//! ```text
//! struct TypeCheckId { expr_hash: u64, env_hash: u64, mode_hash: u64, expr: Arc<Expr> }
//!   rustc / producer : expr@0  expr_hash@8  env_hash@16 mode_hash@24, size 32
//!   recomputed       : expr@24 expr_hash@0  env_hash@8  mode_hash@16, size 32
//! ```
//!
//! This module makes the **declared** layout win whenever the producer stated
//! a complete one that the byte path can actually emit, and names the
//! recomputation as what it is: the explicit fallback for the structs that
//! carry no declared layout at all.
//!
//! # The three authorities, in priority order
//!
//! [`LayoutSource`] is the whole answer to "who laid this struct out":
//!
//! 1. [`LayoutSource::Declared`] — the producer's own offsets/size/align,
//!    read verbatim. Wins whenever [`declared_layout`] accepts them.
//! 2. [`LayoutSource::Packed`] — [`crate::adapter::packed_struct_layout`], for
//!    EVERY `#[repr(packed(N))]` struct. Unchanged from before this module
//!    existed: a packed struct is never handed to authority D, deliberately.
//! 3. [`LayoutSource::NaturalC`] — **THE NAMED FALLBACK**: declaration-ordered
//!    natural C off the LIR type. This is what every struct with no declared
//!    layout still gets, and its behaviour is byte-identical to before.
//!    (c) MEASURED over a 69-module corpus: 952 of 6,051 struct defs (15.7%),
//!    carrying 1,811 fields, record no layout at all, so this fallback is
//!    load-bearing and permanent, not a transition state.
//!
//! # Why a declared layout can be REFUSED — and must be
//!
//! The producer's offsets describe rustc's layout of the WHOLE object,
//! interiors included. trust-cg does not address every interior the way rustc
//! lays it out: a `Ty::Tuple` / `Ty::Record` / `Ty::Closure` is synthesized in
//! declaration order, an array is addressed at the natural element stride by
//! `ArrayGep`, and an enum gets LIR's canonical tagged-union layout. So a
//! field's EMITTED image can be wider than the hole rustc left for it.
//!
//! Honouring the declared offsets for such a struct would not be "more
//! correct" — it would be an overlap or an out-of-bounds write. (c) MEASURED
//! against stock `rustc 1.97.0`:
//!
//! ```text
//! #[repr(C, packed)] struct ArrOfP { h: u8, arr: [P; 2] }   // P = #[repr(packed)] {u8,u64}
//!   rustc  : h@0 arr@1, size 19
//!   emitted: [P;2] is addressed by ArrayGep at the NATURAL 16-byte stride,
//!            so its image is 32 bytes; arr@1 would run to byte 33 in a
//!            19-byte object.
//! ```
//!
//! [`declared_layout`] therefore accepts a declared layout only when it is
//! EMITTABLE. Four gates ask that, each with its own failure mode, and none of
//! them asks whether the OFFSETS agree with the recomputation — offset
//! agreement is never consulted, which is the whole point. (A fifth gate, on
//! the TOTALS, is a different question and has its own section below.)
//!
//! 1. **Complete.** Every field carries an `offset` and the struct carries both
//!    a `size` and an `align`. Partial data is refused wholesale — a
//!    half-declared, half-recomputed layout is one no authority stands behind.
//! 2. **Not packed.** `#[repr(packed(N))]` keeps authority P; see
//!    [`declared_layout`] for why closing the packed offset split without the
//!    packed size split would be the wrong trade.
//! 3. **Coherent.** `size` is a whole number of `align`, `align` is at least
//!    every field's alignment, and every offset is divisible by its field's
//!    alignment. Producer data that is not a real layout would turn a
//!    wrong-address defect into a misaligned access.
//! 4. **Contained and non-overlapping.** Every field's EMITTED image fits
//!    inside the declared size at its declared offset, and no two images
//!    overlap — the `ArrOfP` hazard above. (c) MEASURED over the same
//!    69-module corpus: 0 of 2,952 complete-offset structs overlap and 0 exceed
//!    their declared size, so this gate costs nothing on real input; it exists
//!    because the shape above is constructible.
//!
//! A struct that fails any gate falls back to the recomputation — the layout
//! the byte path can actually express — and [`crate::layout_refusal`] keeps
//! scoring it, so the divergence stays counted instead of being silently
//! "fixed".
//!
//! # Why nothing but the ADDRESS moves — the totals gate
//!
//! The ordering constraint the nested-packed repair learned the hard way is
//! that offsets and EXTENTS have to move in one change, because honouring an
//! offset inside an under-allocated slot is an out-of-bounds write. (c)
//! MEASURED: 6 of 2,952 corpus structs would write outside a
//! `Type::bytes()`-sized slot if their declared offsets alone were honoured —
//! `crossbeam_epoch::internal::Global` needs 392 where the recomputation
//! reserves 32 and rustc declares 512.
//!
//! This module satisfies that constraint by REFUSING those structs, not by
//! moving slots. A fifth gate requires the declared `size` and `align` to
//! **already equal** the natural-C recomputation's. So for every struct
//! authority D owns, `emitted == natural` on both totals, and every extent this
//! repair does not reach — the C register-ABI classifier in `abi.rs` (called
//! from ISel on `sig.params`, after the struct identity is gone), the byval
//! stack slots, the small-aggregate `<= 16` decisions in both ISels, every
//! `alloca` and aggregate stack slot — measures exactly what it measured
//! before. The emitted stream changes in one way only: the ADDRESS of a field.
//!
//! (c) MEASURED, corpus-wide before/after over 68 modules (`clean_kernel`
//! excluded for runtime): 31,481 of 31,578 lowered functions are BYTE-IDENTICAL
//! (99.69%); the 97 that changed differ only by `StructGep` becoming
//! `Iconst`+`Iadd` at rustc's offset; 0 functions started failing to lower and
//! 0 started succeeding. With every producer layout stripped from the same
//! corpus — i.e. every struct forced onto the fallback — the emitted stream is
//! byte-identical to the pre-repair compiler, sha256 `710024e5…` on both sides.
//!
//! [`emitted_value_extent`] is therefore the one extent this module exports:
//! how many bytes a BY-VALUE copy of the value moves. It is EXACT, which is
//! what stops a copy reaching into the sibling the same authority placed right
//! behind it, and under the totals gate it returns the natural-C answer for
//! every declared struct.
//!
//! What the totals gate declines is the whole size/align half of the defect:
//! (c) MEASURED, of 251 corpus disagreements 197 are offset-only and are fixed,
//! while 54 diverge on size or align — the `#[repr(align(N))]` / 128-bit /
//! `CachePadded` / NEON-vector family. Those keep the recomputation and stay
//! counted as `Disagrees` by [`crate::layout_refusal`] (251 -> 54 measured).
//! Closing them means giving the LIR `Type` a size/align of its own, which is a
//! cross-crate change with its own blocker (`Type::Struct(Vec<Type>)` is not
//! injective onto declared layouts) and is deliberately not bundled here.

use crate::adapter::{
    AdapterError, MAX_TYPE_TRANSLATION_DEPTH, packed_struct_layout_inner,
    translate_type_with_enum_tables,
};
use crate::types::Type;
use trust_ir::{ClosureTy, EnumDef, RecordDef, StructDef, StructRepr, Ty};

/// Which of trust-cg's three layout authorities produced a layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LayoutSource {
    /// The producer's own `FieldDef::offset` / `StructDef::size` / `align`,
    /// read verbatim — rustc's real layout. Wins whenever it is emittable.
    Declared,
    /// [`crate::adapter::packed_struct_layout`], for a `#[repr(packed(N))]`
    /// struct with no complete declared layout.
    Packed,
    /// **The named fallback**: declaration-ordered natural C, recomputed off
    /// the LIR type by [`Type::offset_of`] / [`Type::bytes`] / [`Type::align`].
    NaturalC,
}

impl LayoutSource {
    /// A short name for diagnostics and census reasons.
    pub fn name(self) -> &'static str {
        match self {
            LayoutSource::Declared => "producer-declared (rustc's own layout, read verbatim)",
            LayoutSource::Packed => "packed (`packed_struct_layout`)",
            LayoutSource::NaturalC => "natural-C recomputation (`Type::offset_of`) — the fallback",
        }
    }
}

/// A complete struct layout plus the authority that produced it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmittedStructLayout {
    /// One byte offset per declared field, in DECLARATION order (the offsets
    /// themselves need not be ascending — rustc reorders).
    pub offsets: Vec<u64>,
    /// The struct's total size under this authority.
    pub size: u64,
    /// The struct's alignment under this authority.
    pub align: u64,
    /// Who produced it.
    pub source: LayoutSource,
}

/// The module tables every layout authority needs to resolve field types.
#[derive(Clone, Copy)]
pub struct LayoutTables<'a> {
    pub structs: &'a [StructDef],
    pub types: &'a [Ty],
    pub enums: &'a [EnumDef],
    pub records: &'a [RecordDef],
    pub closures: &'a [ClosureTy],
}

/// The `StructDef` behind `ty`, under the byte path's FIRST-MATCH resolution
/// rule (`adapter.rs`, `structs.iter().find(|s| s.id == *sid)`).
///
/// Deliberately identical to `TrustIrAdapter::is_packed_struct_ty`: a bare
/// `Ty::Struct` only. `Ty::Refine` is not followed and `Ty::Tuple` /
/// `Ty::Array` / `Ty::Record` / `Ty::Closure` are not inspected, because those
/// are exactly the shapes the producer states no offsets for and the byte path
/// synthesizes.
pub fn struct_def_for_ty<'a>(ty: &Ty, structs: &'a [StructDef]) -> Option<&'a StructDef> {
    let Ty::Struct(sid) = ty else {
        return None;
    };
    structs.iter().find(|s| s.id == *sid)
}

/// The layout the byte path emits for `sdef`: declared if the producer stated
/// an emittable one, else packed, else the natural-C fallback.
pub fn emitted_struct_layout(
    sdef: &StructDef,
    tables: LayoutTables<'_>,
) -> Result<EmittedStructLayout, AdapterError> {
    emitted_struct_layout_inner(sdef, tables, 0)
}

fn emitted_struct_layout_inner(
    sdef: &StructDef,
    tables: LayoutTables<'_>,
    depth: usize,
) -> Result<EmittedStructLayout, AdapterError> {
    if depth >= MAX_TYPE_TRANSLATION_DEPTH {
        return Err(AdapterError::UnsupportedType(format!(
            "struct nesting in `{}` exceeds the adapter recursion limit \
             ({MAX_TYPE_TRANSLATION_DEPTH}) while resolving its layout authority",
            sdef.name
        )));
    }

    // Translate every field type FIRST, with the same conversion the byte path
    // uses. This is the call that diagnoses a cyclic or over-deep field graph,
    // and it is what the natural-C fallback measures.
    let mut lir_fields: Vec<Type> = Vec::with_capacity(sdef.fields.len());
    for field in &sdef.fields {
        lir_fields.push(translate_type_with_enum_tables(
            &field.ty,
            tables.structs,
            tables.types,
            tables.enums,
            tables.records,
            tables.closures,
        )?);
    }

    // 1. DECLARED WINS.
    if let Some(declared) = declared_layout(sdef, &lir_fields, tables, depth) {
        return Ok(declared);
    }

    // 2. PACKED — unchanged from before this module existed.
    if matches!(sdef.repr, StructRepr::Packed(_)) {
        let packed = packed_struct_layout_inner(
            sdef,
            tables.structs,
            tables.types,
            tables.enums,
            tables.records,
            tables.closures,
            None,
            depth,
        )?;
        if let Some(size) = packed.size {
            return Ok(EmittedStructLayout {
                offsets: packed.offsets,
                size,
                align: packed.align,
                source: LayoutSource::Packed,
            });
        }
    }

    // 3. THE NAMED FALLBACK — declaration-ordered natural C.
    let lir_ty = Type::Struct(lir_fields);
    let mut offsets = Vec::with_capacity(sdef.fields.len());
    for index in 0..sdef.fields.len() {
        let offset = lir_ty.offset_of(index).ok_or_else(|| {
            AdapterError::UnsupportedType(format!(
                "natural-C `Type::offset_of` yielded no offset for field {index} of `{}`",
                sdef.name
            ))
        })?;
        offsets.push(u64::from(offset));
    }
    Ok(EmittedStructLayout {
        offsets,
        size: u64::from(lir_ty.bytes()),
        align: u64::from(lir_ty.align()),
        source: LayoutSource::NaturalC,
    })
}

/// The producer's declared layout for `sdef`, accepted only when it is
/// COMPLETE and EMITTABLE.
///
/// Complete: every field carries an `offset` **and** the struct carries both a
/// `size` and an `align`. Anything partial is refused wholesale rather than
/// mixed with a recomputation — a half-declared, half-recomputed layout is a
/// layout no authority stands behind. (c) MEASURED over a 69-module corpus:
/// MIXED offsets = 0 and "sized but offset-less" = 0, so the all-or-nothing
/// gate selects exactly the 5,099 of 6,051 struct defs (84.3%) that carry a
/// full layout.
///
/// Emittable: see the module docs. Five gates, in the order they appear below —
/// not packed, complete, totals equal to the recomputation's, coherent, and
/// contained + non-overlapping under the EMITTED interior extents.
fn declared_layout(
    sdef: &StructDef,
    lir_fields: &[Type],
    tables: LayoutTables<'_>,
    depth: usize,
) -> Option<EmittedStructLayout> {
    // A `#[repr(packed(N))]` struct is OUT OF SCOPE for this repair, and that is
    // a deliberate boundary rather than an oversight.
    //
    // trust-cg lays a packed struct out two ways — `packed_struct_layout` for
    // its field addresses and copy extents, natural C for its slots and ABI —
    // and `crate::layout_refusal` declines to certify one for exactly that
    // reason. Letting the declared layout in would resolve the OFFSET half of
    // that split while leaving the SIZE half open, which needs a disposition for
    // "offsets compared, totals not" — a predicate-shaped change that must not
    // ride along with a codegen fix. Worse, a declared layout whose totals
    // happen to equal the NATURAL ones would silently take the array stride and
    // copy length back off authority P and hand them to authority C, undoing the
    // packed stride repair.
    //
    // So packed structs keep authority P exactly as before, and the one packed
    // shape this leaves wrong stays named: `#[repr(packed(N))]` with `N > 1` and
    // no `repr(C)` REORDERS fields — (c) MEASURED with stock `rustc 1.97.0`,
    // `#[repr(packed(2))] { a: u8, b: u64, c: u16 }` is `a@10 b@0 c@8`, size 12
    // — and a declaration-ordered walk structurally cannot express that.
    if matches!(sdef.repr, StructRepr::Packed(_)) {
        return None;
    }

    let size = sdef.size?;
    let align = sdef.align?;
    if lir_fields.len() != sdef.fields.len() {
        return None;
    }

    // THE TOTALS GATE — this repair moves OFFSETS, and only offsets.
    //
    // A struct's total size and alignment are read by consumers this change
    // cannot reach, because by then the struct identity is gone and only the
    // LIR `Type` survives: the C register-ABI classifier (`abi.rs`, called from
    // ISel on `sig.params`), the byval stack slots, the small-aggregate `<= 16`
    // decisions in both ISels, every `alloca` and aggregate stack slot. All of
    // them measure the natural-C `Type::bytes()` / `align()`.
    //
    // So a declared layout is honoured only where its TOTALS ALREADY MATCH the
    // recomputation. Two things follow, and both are the point:
    //
    // * **Nothing but the address moves.** Every extent, slot, stride and ABI
    //   decision in the emitted stream is bit-for-bit what it was before this
    //   repair. There is no under-allocated slot to write past — the hazard the
    //   nested-packed repair hit from the other side, where honouring a smaller
    //   layout inside a natural-C-lengthed copy was an out-of-bounds write.
    // * **The size/align half of the defect stays COUNTED.** A struct whose
    //   declared totals differ is exactly a struct the byte path really does
    //   size two ways, and it keeps the recomputation so
    //   `crate::layout_refusal` keeps reporting it as `Disagrees`. Certifying
    //   it here would hide a live ABI divergence behind a fixed address.
    //
    // (c) MEASURED over a 69-module corpus: of 251 producer/byte-path
    // disagreements, 197 are offset-only — declared totals equal recomputed
    // totals — and pass this gate; 42 are size/align-only and 12 diverge on
    // both. Those 54 are the `#[repr(align(N))]` / 128-bit / `CachePadded`
    // family, where the recomputed size is never larger than declared (28
    // smaller, 26 equal), and closing them needs the LIR `Type` to carry a
    // size/align of its own — a cross-crate change with its own blocker
    // (`Type::Struct(Vec<Type>)` is not injective onto declared layouts) that is
    // deliberately not bundled here.
    let natural = Type::Struct(lir_fields.to_vec());
    if size != u64::from(natural.bytes()) || align != u64::from(natural.align()) {
        return None;
    }

    let mut offsets = Vec::with_capacity(sdef.fields.len());
    for field in &sdef.fields {
        offsets.push(field.offset?);
    }

    // COHERENCE. A real layout — one rustc could have produced — has a size
    // that is a whole number of its own alignment, an alignment at least as
    // strict as every field's alignment, and every field sitting at an offset
    // its own alignment divides. Producer data that violates any of those is
    // not a layout the byte path can honour: `{ a: u64@0 }, size 9` would
    // misalign element 1 of an array of it, turning a wrong-address defect into
    // a misaligned access, and a field parked at an offset its type is not
    // aligned for is an unaligned access the emitted `Load`/`Store` does not
    // declare. Such a struct keeps the recomputation and stays a scored
    // divergence. (Packed structs, the one repr where a field legitimately sits
    // at an under-aligned offset, exited above.)
    if align == 0 || size % align != 0 {
        return None;
    }

    // Emitted image of each field, under whichever authority addresses it.
    // A field whose extent cannot be resolved makes the whole declared layout
    // unprovable, so it is refused rather than assumed to fit.
    let mut images: Vec<(u64, u64)> = Vec::with_capacity(offsets.len());
    for (index, offset) in offsets.iter().copied().enumerate() {
        let field_layout =
            emitted_field_layout(&sdef.fields[index].ty, &lir_fields[index], tables, depth).ok()?;
        let placement_align = field_layout.align.max(1);
        if placement_align > align || offset % placement_align != 0 {
            return None;
        }
        // CONTAINMENT: the image must not run off the end of the object.
        if offset.checked_add(field_layout.size)? > size {
            return None;
        }
        if field_layout.size > 0 {
            images.push((offset, field_layout.size));
        }
    }

    // NON-OVERLAP: rustc reorders, so sort by offset before checking. Zero-size
    // images are dropped above — a ZST shares an address with its neighbour by
    // construction and writes nothing.
    images.sort_unstable();
    for pair in images.windows(2) {
        let (offset, extent) = pair[0];
        if offset.checked_add(extent)? > pair[1].0 {
            return None;
        }
    }

    Some(EmittedStructLayout {
        offsets,
        size,
        align,
        source: LayoutSource::Declared,
    })
}

/// How many bytes a BY-VALUE copy of a value of type `ty` moves — EXACTLY.
///
/// The authoritative extent for a struct (declared, else packed, else natural
/// C), that extent times the count for an ARRAY of such a struct, and the
/// natural-C LIR extent for everything else, because every other aggregate
/// shape is synthesized by the byte path in declaration order.
///
/// Exactness matters in both directions: too few bytes truncates the value,
/// too many reach into the sibling the same authority placed behind it.
pub fn emitted_value_extent(
    ty: &Ty,
    lir_ty: &Type,
    tables: LayoutTables<'_>,
) -> Result<u64, AdapterError> {
    emitted_value_extent_inner(ty, lir_ty, tables, 0)
}

fn emitted_value_extent_inner(
    ty: &Ty,
    lir_ty: &Type,
    tables: LayoutTables<'_>,
    depth: usize,
) -> Result<u64, AdapterError> {
    Ok(emitted_field_layout(ty, lir_ty, tables, depth)?.size)
}

/// The AUTHORITATIVE element stride of `Ty::Array(elem, _)` — the extent the
/// byte path advances by from one element to the next — paired with the
/// element's own `Ty` and LIR type so a caller that has to materialise the
/// stride arithmetic itself does not resolve the element table twice.
///
/// `None` for every non-array `ty`, and for an array whose element type the
/// module tables cannot resolve, or whose LIR carrier is not a `Type::Array`
/// (a `Ty::Vector`, a refinement that erased the shape): those keep the
/// natural-C `ArrayGep` stride they already had.
fn array_element_layout<'a>(
    ty: &'a Ty,
    lir_ty: &'a Type,
    tables: LayoutTables<'a>,
    depth: usize,
) -> Option<(&'a Ty, &'a Type, FieldLayout)> {
    let Ty::Array(elem_tyid, _) = ty else {
        return None;
    };
    let Type::Array(lir_elem_ty, _) = lir_ty else {
        return None;
    };
    let elem_ty = tables.types.get(elem_tyid.as_usize())?;
    let elem = emitted_field_layout(elem_ty, lir_elem_ty, tables, depth + 1).ok()?;
    Some((elem_ty, lir_elem_ty, elem))
}

/// `(size, align)` of a value of type `ty` as the byte path lays it out — the
/// authoritative pair for a struct, the element-authoritative pair for an
/// array, the natural-C pair for every other shape.
pub(crate) struct FieldLayout {
    pub(crate) size: u64,
    pub(crate) align: u64,
}

/// THE one extent/alignment selector. Every consumer that asks "how much room
/// does a value of this type actually occupy" comes here, so the walk that
/// PLACES a field ([`crate::adapter::packed_struct_layout_inner`]), the copy
/// that WRITES it ([`emitted_value_extent`]), the containment gate that admits
/// a declared layout, and the stride that ADDRESSES an array element all read
/// the same number by construction.
pub(crate) fn emitted_field_layout(
    ty: &Ty,
    lir_ty: &Type,
    tables: LayoutTables<'_>,
    depth: usize,
) -> Result<FieldLayout, AdapterError> {
    if depth >= MAX_TYPE_TRANSLATION_DEPTH {
        return Err(AdapterError::UnsupportedType(format!(
            "type nesting exceeds the adapter recursion limit \
             ({MAX_TYPE_TRANSLATION_DEPTH}) while resolving the extent of {ty:?}"
        )));
    }
    if let Some(sdef) = struct_def_for_ty(ty, tables.structs) {
        let layout = emitted_struct_layout_inner(sdef, tables, depth + 1)?;
        return Ok(FieldLayout {
            size: layout.size,
            align: layout.align,
        });
    }
    // An ARRAY is `count` copies of its element at the element's OWN
    // authoritative stride — not at natural-C `elem.bytes()`. (c) MEASURED
    // with stock `rustc 1.97.0`, `P = #[repr(C,packed)] { a: u8, b: u64 }`:
    // `size_of::<[P; 2]>() == 18` (stride 9), where `Type::Array(Struct([I8,
    // I64]), 2).bytes()` is 32. Reporting 32 here is what used to make
    // `#[repr(C,packed)] { h: u8, arr: [P; 2] }` 33 bytes instead of rustc's
    // 19, and what made every array-element copy over-long.
    //
    // The ALIGNMENT is the element's, unmultiplied — `align_of::<[P; 2]>() ==
    // 1 == align_of::<P>()` (measured), which is also what natural-C
    // `Type::Array::align()` already reports for a natural element, so this
    // arm only ever moves an array whose ELEMENT has a non-natural authority.
    //
    // This number is only correct because the ADDRESSING moved with it: the
    // `ArrayGep` sites in `translate_multi_index_gep`, `ExtractElement`,
    // `InsertElement` and `fill_aggregate_at_ptr` all take their stride from
    // [`array_element_layout`], which is this same recursion. Reporting a
    // 9-byte stride here while those still strode by 16 would place the next
    // sibling INSIDE the bytes element 1 actually writes — an overlap, which
    // is strictly worse than the over-report it replaced.
    if let Some((_, _, elem)) = array_element_layout(ty, lir_ty, tables, depth) {
        let Ty::Array(_, count) = ty else {
            unreachable!("array_element_layout answers Some only for Ty::Array");
        };
        let size = elem.size.checked_mul(*count).ok_or_else(|| {
            AdapterError::UnsupportedType(format!(
                "array extent overflows u64: {} x {count} for {ty:?}",
                elem.size
            ))
        })?;
        // DOMINATION, ASSERTED RATHER THAN ASSUMED. Everything downstream that
        // reserves storage — the `Alloca` slot, `__rust_alloc`, the ABI
        // classifier — sizes it from the natural carrier, so an authoritative
        // extent ABOVE that carrier is an out-of-bounds write, not a rounding
        // difference. Every authority in play only ever shrinks an object, so
        // this holds by construction for every representable type; it stops
        // holding exactly when the carrier saturates and this `u64` product
        // does not. `translate_type_*` refuses to build such a `Type` at all,
        // which makes this unreachable through the byte path — but `Type` is
        // `pub` and constructible directly, and this is the one comparison
        // that makes the arm safe however its inputs were built.
        let carrier = u64::from(lir_ty.bytes());
        if size > carrier {
            return Err(AdapterError::UnsupportedType(format!(
                "array extent {size} exceeds its natural carrier {carrier} for {ty:?}; \
                 the LIR type cannot represent this object"
            )));
        }
        return Ok(FieldLayout {
            size,
            align: elem.align,
        });
    }
    Ok(FieldLayout {
        size: u64::from(lir_ty.bytes()),
        align: u64::from(lir_ty.align()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{FieldDef, StructId, TyId};

    fn tables<'a>(structs: &'a [StructDef]) -> LayoutTables<'a> {
        LayoutTables {
            structs,
            types: &[],
            enums: &[],
            records: &[],
            closures: &[],
        }
    }

    fn field(name: &str, ty: Ty, offset: Option<u64>) -> FieldDef {
        FieldDef {
            name: name.to_string(),
            ty,
            offset,
        }
    }

    /// `struct TypeCheckId { expr_hash: u64, env_hash: u64, mode_hash: u64,
    /// expr: Arc<Expr> }` — (c) MEASURED with stock `rustc 1.97.0`:
    /// `expr@0 expr_hash@8 env_hash@16 mode_hash@24`, size 32.
    fn type_check_id() -> StructDef {
        StructDef {
            id: StructId::new(1),
            name: "TypeCheckId".to_string(),
            fields: vec![
                field("expr_hash", Ty::U64, Some(8)),
                field("env_hash", Ty::U64, Some(16)),
                field("mode_hash", Ty::U64, Some(24)),
                field("expr", Ty::Ptr, Some(0)),
            ],
            size: Some(32),
            align: Some(8),
            repr: StructRepr::Rust,
        }
    }

    #[test]
    fn declared_offsets_win_over_the_recomputation() {
        let structs = vec![type_check_id()];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::Declared);
        assert_eq!(layout.offsets, vec![8, 16, 24, 0]);
        assert_eq!(layout.size, 32);
    }

    #[test]
    fn a_struct_with_no_declared_layout_falls_back_to_the_recomputation() {
        let structs = vec![StructDef {
            id: StructId::new(1),
            name: "NoLayout".to_string(),
            fields: vec![
                field("a", Ty::U8, None),
                field("b", Ty::U64, None),
                field("c", Ty::U16, None),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        }];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::NaturalC);
        assert_eq!(layout.offsets, vec![0, 8, 16]);
        assert_eq!(layout.size, 24);
        assert_eq!(layout.align, 8);
    }

    #[test]
    fn a_partial_declared_layout_is_refused_wholesale() {
        // Half-declared is not half-honoured: the whole struct falls back.
        let mut sdef = type_check_id();
        sdef.fields[2].offset = None;
        let structs = vec![sdef];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::NaturalC);

        let mut sdef = type_check_id();
        sdef.size = None;
        let structs = vec![sdef];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::NaturalC);
    }

    #[test]
    fn a_declared_layout_whose_field_runs_off_the_end_is_refused() {
        // `expr` is 8 bytes at offset 0 but the object claims to be 4 bytes.
        let mut sdef = type_check_id();
        sdef.size = Some(4);
        let structs = vec![sdef];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::NaturalC);
    }

    #[test]
    fn a_declared_layout_whose_fields_overlap_is_refused() {
        let mut sdef = type_check_id();
        // `env_hash` (8 bytes) now starts inside `expr_hash`'s image.
        sdef.fields[1].offset = Some(12);
        let structs = vec![sdef];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::NaturalC);
    }

    #[test]
    fn a_declared_layout_whose_totals_diverge_is_refused_in_both_directions() {
        // BIGGER — `#[repr(align(16))] struct Over { a: u8 }`, (c) MEASURED
        // with stock `rustc 1.97.0`: size 16, align 16 where the recomputation
        // says 1/1. Honouring 16 while every unreached extent consumer still
        // reserves 1 would be an out-of-bounds write, not a fix.
        let structs = vec![StructDef {
            id: StructId::new(1),
            name: "Over".to_string(),
            fields: vec![field("a", Ty::U8, Some(0))],
            size: Some(16),
            align: Some(16),
            repr: StructRepr::Rust,
        }];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::NaturalC);
        assert_eq!((layout.size, layout.align), (1, 1));

        // SMALLER — the same gate, the other way. `{ a: u8, b: u64, c: u16 }`
        // is 16/8 in rustc (`a@10 b@0 c@8`) and 24/8 recomputed. Taking rustc's
        // 16 as the copy length and array stride while the ABI classifier and
        // every slot still say 24 would put two sizes back in the compiler, so
        // this size/align family stays on the recomputation and stays counted.
        let structs = vec![StructDef {
            id: StructId::new(1),
            name: "Mixed".to_string(),
            fields: vec![
                field("a", Ty::U8, Some(10)),
                field("b", Ty::U64, Some(0)),
                field("c", Ty::U16, Some(8)),
            ],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        }];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::NaturalC);
        assert_eq!((layout.size, layout.align), (24, 8));
    }

    #[test]
    fn an_incoherent_declared_layout_is_refused() {
        // A `u64` parked at 4 in a non-packed struct. rustc never mints it, and
        // emitting it would be an unaligned access the `Load`/`Store` does not
        // declare.
        let structs = vec![StructDef {
            id: StructId::new(1),
            name: "Incoherent".to_string(),
            fields: vec![field("a", Ty::U64, Some(0)), field("b", Ty::U64, Some(4))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        }];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::NaturalC);
    }

    #[test]
    fn a_packed_struct_is_never_handed_to_the_declared_authority() {
        // `#[repr(packed(2))] { a: u8, b: u64, c: u16 }` is `a@10 b@0 c@8`,
        // size 12, in rustc — it REORDERS. Authority P is declaration-ordered
        // and cannot express that; letting authority D in would close the
        // packed OFFSET split while leaving the packed SIZE split open.
        let structs = vec![StructDef {
            id: StructId::new(1),
            name: "P2".to_string(),
            fields: vec![
                field("a", Ty::U8, Some(10)),
                field("b", Ty::U64, Some(0)),
                field("c", Ty::U16, Some(8)),
            ],
            size: Some(12),
            align: Some(2),
            repr: StructRepr::Packed(2),
        }];
        let layout = emitted_struct_layout(&structs[0], tables(&structs)).expect("layout");
        assert_eq!(layout.source, LayoutSource::Packed);
        assert_eq!(
            layout.offsets,
            vec![0, 2, 10],
            "declaration-ordered, clamped"
        );
    }

    /// THE INVARIANT the whole repair rests on: for every authority, the
    /// emitted totals are EXACTLY the natural-C ones, so every extent consumer
    /// this repair does not reach measures what it measured before.
    #[test]
    fn a_declared_layout_never_changes_the_totals() {
        let structs = vec![type_check_id()];
        let tables = tables(&structs);
        let layout = emitted_struct_layout(&structs[0], tables).expect("layout");
        assert_eq!(layout.source, LayoutSource::Declared);
        let natural = Type::Struct(vec![Type::I64, Type::I64, Type::I64, Type::I64]);
        assert_eq!(layout.size, u64::from(natural.bytes()));
        assert_eq!(layout.align, u64::from(natural.align()));
        assert_eq!(
            emitted_value_extent(&Ty::Struct(StructId::new(1)), &natural, tables).expect("extent"),
            u64::from(natural.bytes()),
            "the copy length is unchanged; only the ADDRESS of a field moved"
        );
    }

    /// `Nat = #[repr(C)] { a: u8, b: u64 }`, 16 bytes natural, no declared
    /// layout, in an array of 2^28 — a type stock `rustc 1.97.0` accepts and
    /// sizes at exactly 2^32.
    fn natural_sixteen_byte_struct() -> Vec<StructDef> {
        vec![StructDef {
            id: StructId::new(1),
            name: "Nat".to_string(),
            fields: vec![field("a", Ty::U8, None), field("b", Ty::U64, None)],
            size: None,
            align: None,
            repr: StructRepr::C,
        }]
    }

    /// THE ARRAY ARM MAY NOT OUT-RUN ITS CARRIER.
    ///
    /// The authoritative extent is computed in `u64`; the carrier that sizes
    /// every `Alloca`, `__rust_alloc` and by-value ABI slot is a `u32`. When
    /// the two disagree the emitted copy length can exceed the storage
    /// reserved for it — an out-of-bounds WRITE, not a rounding error.
    ///
    /// (c) MEASURED before this guard: `emitted_value_extent` answered
    /// 4294967296 for `[Nat; 268435456]` while `Type::bytes()` answered 0,
    /// because the `u32` product wrapped. That is a 4 GiB `Memmove` into a
    /// zero-byte stack slot.
    #[test]
    fn an_array_extent_above_its_u32_carrier_is_refused_not_emitted() {
        let structs = natural_sixteen_byte_struct();
        let types = vec![Ty::Struct(StructId::new(1))];
        let tables = LayoutTables {
            structs: &structs,
            types: &types,
            enums: &[],
            records: &[],
            closures: &[],
        };
        let count: u64 = 268_435_456;
        let ty = Ty::Array(TyId::new(0), count);
        let lir = Type::Array(
            Box::new(Type::Struct(vec![Type::I8, Type::I64])),
            count as u32,
        );

        let err = emitted_value_extent(&ty, &lir, tables)
            .expect_err("an extent that cannot fit its carrier must be refused");
        let msg = format!("{err}");
        assert!(
            msg.contains("exceeds its natural carrier"),
            "expected the domination refusal, got: {msg}"
        );
    }

    /// The guard above is a REFUSAL, not a ceiling: an array whose extent does
    /// fit the carrier is still answered exactly, and still at the element's
    /// AUTHORITATIVE stride rather than the natural one. `P` is 9 packed
    /// bytes inside a 16-byte natural carrier — (c) MEASURED with stock
    /// `rustc 1.97.0`, `size_of::<[P; 4]>() == 36`.
    #[test]
    fn an_array_extent_that_fits_its_carrier_is_still_the_packed_one() {
        let structs = vec![StructDef {
            id: StructId::new(1),
            name: "P".to_string(),
            fields: vec![field("a", Ty::U8, None), field("b", Ty::U64, None)],
            size: None,
            align: None,
            repr: StructRepr::Packed(1),
        }];
        let types = vec![Ty::Struct(StructId::new(1))];
        let tables = LayoutTables {
            structs: &structs,
            types: &types,
            enums: &[],
            records: &[],
            closures: &[],
        };
        let ty = Ty::Array(TyId::new(0), 4);
        let lir = Type::Array(Box::new(Type::Struct(vec![Type::I8, Type::I64])), 4);
        assert_eq!(
            emitted_value_extent(&ty, &lir, tables).expect("extent"),
            36,
            "rustc sizes [P; 4] at 36; the natural carrier is 64"
        );
        assert!(36 <= u64::from(lir.bytes()), "and it is dominated by it");
    }
}
