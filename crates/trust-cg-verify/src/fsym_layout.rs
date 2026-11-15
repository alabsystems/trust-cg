// Symbolic execution: the reference interpreter's byte layout, for the bounded trust_ir scanner
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The ONE layout authority the bounded fsym scanner reasons with: trust-ir's
//! reference interpreter's own byte layout (`trust_ir::interpret`, at the rev
//! `Cargo.lock` pins).
//!
//! The interpreter is trust-ir's executable semantics, and every UB fsym
//! owes a verdict for is the interpreter's (`fsym_ub_map`). An object's
//! extent, an access's width, a GEP's stride, an allocation's size and
//! alignment and which bytes a typed store writes are therefore the
//! interpreter's numbers, or the verdicts are about some other program. The
//! native backends' layout (`translate_type_with_tables`) is NOT that
//! authority: it gives `<4 x bool>` 16 bytes where the interpreter gives 4,
//! and ignores a producer's declared struct size and field offsets.
//!
//! The interpreter's layout functions are private, so this module PORTS them
//! verbatim — `byte_size_in`, `byte_align_in`, `struct_layout_unguarded`,
//! `declared_struct_layout`, `tuple_layout_in`, `aggregate_layout`,
//! `enum_layout_unguarded` (canonical layout and producer descriptors), and
//! the covered-byte walks of `encode_image` / `first_uninit_covered` (which
//! bytes a typed aggregate store writes and a typed load needs) — each error
//! a named refusal. Two tests pin the port:
//! `tests/fsym_layout.rs` measures the interpreter's sizes, strides and
//! alignments by EXECUTING probes and compares every one against this
//! module, and `tests/fsym_ub_map.rs` fingerprints the ported functions'
//! source at the pinned rev (a trust-ir bump that changes one fails until the
//! port is re-derived).
//!
//! A type this module cannot lay out has no interpreter layout either (the
//! interpreter faults with a type error, never a UB); the scanner refuses a
//! function that needs one by name (`fsym_trust_ir::layout_refusal`).

use trust_ir::{
    DEFAULT_POINTER_BITS, EnumId, EnumTagEncoding, Module, StructDef, StructId, StructRepr, Ty,
    TyId,
};

/// Field offsets, size and alignment of a struct or tuple (the interpreter's
/// `StructLayout`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AggregateLayout {
    pub(crate) size: u64,
    pub(crate) align: u64,
    pub(crate) fields: Vec<(u64, Ty)>,
}

/// Where an enum's tag lives in its byte image (the interpreter's
/// `EnumByteView`), reduced to the bytes a covered-byte mask needs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TagLane {
    /// No tag bytes; the selected inhabited variant is a type fact.
    Untagged { variant: usize },
    /// The tag (or niche) occupies `[offset, offset + size)`.
    Bytes { offset: u64, size: u64 },
}

/// An enum's byte layout (the interpreter's `EnumLayout`): each variant's
/// fields at ABSOLUTE offsets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EnumLayout {
    pub(crate) size: u64,
    pub(crate) align: u64,
    tag: TagLane,
    variants: Vec<Vec<(u64, Ty)>>,
}

/// A by-value edge on the current layout path (the interpreter's
/// `LayoutVisit`): re-entry means a type contains itself by value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Visit {
    Struct(StructId),
    Enum(EnumId),
    Ty(TyId),
}

/// The reference interpreter's functions this module ports, each with a
/// fingerprint of its source at the pinned rev (FNV-1a 64 over the code with
/// comments and string contents blanked and whitespace collapsed).
/// `tests/fsym_ub_map.rs` recomputes them from the interpreter's source: a
/// trust-ir bump that changes one fails until the port is re-derived from it
/// (and `tests/fsym_layout.rs` re-measured).
///
/// At trust-ir 794227ad `global_pointer`, `eval_load` and `eval_store` gained
/// only v49 unwritten-lane branches, each taken only when a value or
/// initializer carries a `Constant::Uninit` lane (a global initializer with
/// one is refused, a load of recorded unwritten-lane bytes decodes them, a
/// store of a value carrying one records them). fsym scans no module that
/// spells one (`module_unwritten_lane`), so the port is unchanged.
///
/// At trust-ir 066e1765 (v50) the interpreter's byte images became compact
/// ropes and its allocations sparse. `mark_covered_bytes` /
/// `covered_byte_mask` are gone: the bytes a typed store leaves initialized
/// are now what `encode_image` writes on an uninitialized background, and
/// the bytes a typed load needs are what `first_uninit_covered` scans — each
/// the same set as before (struct / tuple fields, every array element, an
/// enum's tag lane then its active variant, a scalar's every byte), so the
/// sets `FsymLayout::coverage` describes are unchanged. `global_pointer` zeroes the uncovered
/// bytes of the encoded image (as the old dense encoding did), and
/// `alloc_with_slack` places exactly as before, reporting an exhausted
/// address space as `OutOfMemory` instead of UB.
///
/// At trust-ir c06a487f (the live-borrow free rule) `alloc_with_slack` only
/// initializes two new allocation-record fields, `requested` (the size
/// without the slack tail) and `live_borrows` (0); base, alignment, bump and
/// footprint are unchanged, so the port places exactly as before. The count
/// is read only by `Dealloc`, whose new site the UB map owns
/// (`fsym_ub_map`, "allocation is under a live borrow").
///
/// At trust-ir fb477354 (the layout table) `enum_layout_unguarded` decides
/// its variants' inhabitedness through one `InhabitMemo` and reads the niche
/// coverage rule off those verdicts instead of calling
/// `Module::niche_unencoded_inhabited_variant`; both are the same
/// `InhabitMemo` rule (`Module::variant_is_uninhabited` and that helper each
/// run a fresh memo), so every answer is unchanged and the port, which calls
/// the `Module` helpers, stays exact. Re-pinned after that review.
///
/// At trust-ir 9a327ea5, function pointers gained pointer-sized and
/// pointer-aligned storage. The size and alignment arms below mirror that
/// rule; the executable catalog already probes `Ty::Func` on all three
/// reference target layouts (including an enclosing alignment probe).
/// At trust-ir432f7642 Storage adds exact geometry size/alignment; typed
/// load/store refuse it before accessing memory. The port exposes dimensions
/// only, rejects transitive initialized coverage, and fsym refuses the new
/// module surface until its full bounded policy model exists.
/// At trust-ir8f90eaf2, wire65 selects one inhabited enum variant explicitly.
/// Its inactive offset rows are empty; the port independently checks finite
/// structural absence and uses the selected payload for tag-free coverage.
/// At trust-ir627e5cea, closure storage uses the exact immutable module's
/// checked unique constructor/layout binding. Size and alignment come from
/// that binding; initialized-byte coverage visits the captures at their
/// declared offsets, preserving padding and conservative nested enum rules.
/// Missing/conflicting targets or malformed layouts remain named refusals;
/// no function-pointer word or source/ABI authority is inferred from bytes.
pub const FSYM_LAYOUT_PORTED_FROM: &[(&str, u64)] = &[
    ("pointer_bits", 0xf928c342cfd35470),
    ("pointer_bytes", 0xdabcdd464382c4d9),
    ("require_reference_execution_layout", 0x1dff6e49b2c4a08a),
    ("require_fat_pointer_layout", 0x48d52a50cc728b34),
    ("resolve_ty", 0xa8a38b48256f1717),
    ("global_pointer", 0x4178c49c04b8d2d7),
    ("eval_alloca", 0x6884918e128b1fd0),
    ("eval_load", 0x902731b5fd68f12d),
    ("eval_store", 0x8e3472405e9fff8e),
    ("byte_size", 0x263ee81a230b286f),
    ("with_layout_visit", 0x634043d91c719db0),
    ("byte_size_in", 0xb129e1e20668a28d),
    ("struct_layout_in", 0x7ee9bcabf44f23c9),
    ("struct_layout_unguarded", 0xff26ba1f5ac0bb05),
    ("declared_struct_layout", 0xdbe8ac259aa3046a),
    ("tuple_layout_in", 0xe960761157a701f4),
    ("aggregate_layout", 0x13f9028b610f5373),
    ("descriptor_field_size", 0xe33711e8baecfcba),
    ("descriptor_field_align", 0x4092533baed5921f),
    ("enum_layout_in", 0x2a3638e63d746667),
    ("enum_layout_unguarded", 0x94cb0a8d05fd86dd),
    ("byte_align", 0x68710b1cce47d0e9),
    ("byte_align_in", 0x08577c781eb421bd),
    ("encode_image", 0x434f76e08bd7441a),
    ("first_uninit_covered", 0x2861888e8de3aff4),
    ("alloc_with_slack", 0xe8f833caf49a31ec),
    ("align_addr", 0x550bc2c9d6df8f10),
    ("align_up", 0x7e5fc57dcfbe11af),
    ("byte_ranges_overlap", 0x66c6cdbb8146ddb2),
    ("int_mask", 0xfcf72bb6188284cf),
];

/// A layout, or the interpreter's reason there is none.
pub type LayoutResult<T> = Result<T, String>;

/// The interpreter's layout of `module`'s types.
#[derive(Debug, Clone, Copy)]
pub struct FsymLayout<'m> {
    module: &'m Module,
}

impl<'m> FsymLayout<'m> {
    pub fn new(module: &'m Module) -> Self {
        Self { module }
    }

    /// The interpreter's `pointer_bits`: the module's pinned pointer width,
    /// else trust-ir's 64-bit default.
    pub fn pointer_bits(&self) -> u32 {
        self.module
            .target_info
            .as_ref()
            .and_then(|target| target.pointer_size.checked_mul(8))
            .unwrap_or(DEFAULT_POINTER_BITS)
    }

    fn pointer_bytes(&self) -> u64 {
        u64::from(self.pointer_bits() / 8)
    }

    /// The interpreter's `require_reference_execution_layout`: a target-free
    /// module, or a little-endian canonical-scalar-table target with 32- or
    /// 64-bit pointers. Anything else it refuses to execute at all.
    pub fn reference_execution(&self) -> LayoutResult<()> {
        let Some(target) = &self.module.target_info else {
            return Ok(());
        };
        let pointer_bits = self.pointer_bits();
        if matches!(pointer_bits, 32 | 64)
            && target.endianness == trust_ir::Endianness::Little
            && self.module.target_has_canonical_scalar_layout()
        {
            Ok(())
        } else {
            Err(format!(
                "reference execution requires a canonical-scalar-table target with a 32- or 64-bit little-endian layout; got {:?} with {pointer_bits}-bit pointers and {}-endian byte order",
                target.triple, target.endianness
            ))
        }
    }

    /// The byte size of `ty` (`byte_size`).
    pub fn size(&self, ty: &Ty) -> LayoutResult<u64> {
        self.size_in(ty, &mut Vec::new())
    }

    /// The byte alignment of `ty` (`byte_align`): its NATURAL alignment.
    pub fn align(&self, ty: &Ty) -> LayoutResult<u64> {
        self.align_in(ty, &mut Vec::new())
    }

    fn with_visit<T>(
        &self,
        key: Visit,
        ty: &Ty,
        visiting: &mut Vec<Visit>,
        layout: impl FnOnce(&mut Vec<Visit>) -> LayoutResult<T>,
    ) -> LayoutResult<T> {
        if visiting.contains(&key) {
            return Err(format!(
                "type {ty} contains itself by value (no finite layout)"
            ));
        }
        visiting.push(key);
        let result = layout(visiting);
        visiting.pop();
        result
    }

    fn resolve_ty(&self, id: TyId) -> LayoutResult<Ty> {
        self.module
            .ty(id)
            .cloned()
            .ok_or_else(|| format!("type id {id} not found"))
    }

    fn size_in(&self, ty: &Ty, visiting: &mut Vec<Visit>) -> LayoutResult<u64> {
        match ty {
            Ty::Closure(id) => self
                .module
                .closure_storage_binding(*id)
                .map(|binding| binding.layout.size)
                .map_err(str::to_owned),
            Ty::Storage(layout) => {
                if layout.is_well_formed(self.pointer_bits()) {
                    Ok(layout.size_bytes)
                } else {
                    Err("invalid storage-only layout".into())
                }
            }
            Ty::Bool => Ok(1),
            Ty::I8 | Ty::U8 => Ok(1),
            Ty::I16 | Ty::U16 | Ty::F16 => Ok(2),
            Ty::I32 | Ty::U32 | Ty::F32 => Ok(4),
            Ty::I64 | Ty::U64 | Ty::F64 => Ok(8),
            Ty::I128 | Ty::U128 => Ok(16),
            Ty::Isize | Ty::Usize => Ok(self.pointer_bytes()),
            Ty::Char => Ok(4),
            Ty::Func(_)
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_) => Ok(self.pointer_bytes()),
            Ty::FatPtr(_) => {
                self.reference_execution()?;
                Ok(2 * self.pointer_bytes())
            }
            Ty::Unit => Ok(0),
            Ty::Vector(elem, lanes) => {
                if *lanes == 0 {
                    return Err("zero-lane vectors are not executable".to_string());
                }
                self.size_in(elem, visiting)?
                    .checked_mul(u64::from(*lanes))
                    .ok_or_else(|| "vector byte size overflow".to_string())
            }
            Ty::Array(elem, len) => {
                let elem_ty = self.resolve_ty(*elem)?;
                self.with_visit(Visit::Ty(*elem), ty, visiting, |visiting| {
                    self.size_in(&elem_ty, visiting)
                })?
                .checked_mul(*len)
                .ok_or_else(|| "array byte size overflow".to_string())
            }
            Ty::Struct(_) => Ok(self.struct_layout_in(ty, visiting)?.size),
            Ty::Tuple(_) => Ok(self.tuple_layout_in(ty, visiting)?.size),
            Ty::Enum(_) => Ok(self.enum_layout_in(ty, visiting)?.size),
            _ => Err(format!("{ty} has no byte layout")),
        }
    }

    fn align_in(&self, ty: &Ty, visiting: &mut Vec<Visit>) -> LayoutResult<u64> {
        match ty {
            Ty::Closure(id) => self
                .module
                .closure_storage_binding(*id)
                .map(|binding| binding.layout.align)
                .map_err(str::to_owned),
            Ty::Storage(layout) => {
                if layout.is_well_formed(self.pointer_bits()) {
                    Ok(layout.align_bytes)
                } else {
                    Err("invalid storage-only layout".into())
                }
            }
            Ty::Bool | Ty::I8 | Ty::U8 => Ok(1),
            Ty::I16 | Ty::U16 | Ty::F16 => Ok(2),
            Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => Ok(4),
            Ty::I64 | Ty::U64 | Ty::F64 => Ok(8),
            Ty::Func(_)
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_) => Ok(self.pointer_bytes()),
            Ty::Isize | Ty::Usize => Ok(self.pointer_bytes()),
            Ty::FatPtr(_) => {
                self.reference_execution()?;
                Ok(self.pointer_bytes())
            }
            Ty::I128 | Ty::U128 => Ok(16),
            Ty::Unit => Ok(1),
            Ty::Vector(elem, lanes) => {
                if *lanes == 0 {
                    return Err("zero-lane vectors are not executable".to_string());
                }
                self.align_in(elem, visiting)
            }
            Ty::Array(elem, _) => {
                let elem_ty = self.resolve_ty(*elem)?;
                self.with_visit(Visit::Ty(*elem), ty, visiting, |visiting| {
                    self.align_in(&elem_ty, visiting)
                })
            }
            Ty::Struct(_) => Ok(self.struct_layout_in(ty, visiting)?.align),
            Ty::Tuple(_) => Ok(self.tuple_layout_in(ty, visiting)?.align),
            Ty::Enum(_) => Ok(self.enum_layout_in(ty, visiting)?.align),
            _ => Err(format!("{ty} has no byte alignment")),
        }
    }

    /// A struct's layout (`struct_layout`): its producer-DECLARED size,
    /// alignment and field offsets when it declares them (re-validated), else
    /// the canonical declaration-order C layout.
    pub(crate) fn struct_layout(&self, ty: &Ty) -> LayoutResult<AggregateLayout> {
        self.struct_layout_in(ty, &mut Vec::new())
    }

    fn struct_layout_in(
        &self,
        ty: &Ty,
        visiting: &mut Vec<Visit>,
    ) -> LayoutResult<AggregateLayout> {
        let Ty::Struct(sid) = ty else {
            return Err(format!("{ty} is not a struct"));
        };
        self.with_visit(Visit::Struct(*sid), ty, visiting, |visiting| {
            let def = self
                .module
                .struct_def(*sid)
                .ok_or_else(|| format!("struct id {} not found in module", sid.0))?;
            match (def.size, def.align) {
                (Some(size), Some(align)) => {
                    self.declared_struct_layout(ty, def, size, align, visiting)
                }
                (None, None) => {
                    if let Some(index) = def.fields.iter().position(|field| field.offset.is_some())
                    {
                        return Err(format!(
                            "struct {ty} declares a byte offset for field {index} but no struct size or alignment"
                        ));
                    }
                    self.aggregate_layout(def.fields.iter().map(|field| &field.ty), "struct", visiting)
                }
                (Some(_), None) | (None, Some(_)) => Err(format!(
                    "struct {ty} declares a size without an alignment, or the reverse"
                )),
            }
        })
    }

    fn declared_struct_layout(
        &self,
        ty: &Ty,
        def: &StructDef,
        size: u64,
        align: u64,
        visiting: &mut Vec<Visit>,
    ) -> LayoutResult<AggregateLayout> {
        self.reference_execution()?;
        if align == 0 || !align.is_power_of_two() || !size.is_multiple_of(align) {
            return Err(format!(
                "struct {ty} declares an incoherent size {size} / alignment {align}"
            ));
        }
        let clamp = match def.repr {
            StructRepr::Packed(packed) => {
                if packed == 0 || !packed.is_power_of_two() {
                    return Err(format!(
                        "struct {ty} declares repr(packed({packed})): the alignment clamp must be a non-zero power of two"
                    ));
                }
                u64::from(packed)
            }
            _ => u64::MAX,
        };
        if align > clamp {
            return Err(format!(
                "struct {ty} declares alignment {align} above its repr(packed({clamp})) clamp"
            ));
        }
        let mut fields: Vec<(u64, Ty)> = Vec::with_capacity(def.fields.len());
        let mut sizes: Vec<u64> = Vec::with_capacity(def.fields.len());
        let mut transparent_carrier = None;
        let mut transparent_nontrivial = 0usize;
        for (index, field) in def.fields.iter().enumerate() {
            let field_size = self.size_in(&field.ty, visiting)?;
            let field_align = self.align_in(&field.ty, visiting)?.max(1).min(clamp);
            let offset = match field.offset {
                Some(offset) => {
                    if !offset.is_multiple_of(field_align)
                        || field_align > align
                        || offset.checked_add(field_size).is_none_or(|end| end > size)
                    {
                        return Err(format!(
                            "struct {ty} field {index} at declared offset {offset} ({field_size} bytes, align {field_align}) is out of bounds, misaligned, or over-aligned for declared size {size} / align {align}"
                        ));
                    }
                    offset
                }
                None => {
                    if field_size != 0 {
                        return Err(format!(
                            "struct {ty} field {index} occupies {field_size} bytes but the declared layout gives it no offset"
                        ));
                    }
                    0
                }
            };
            if def.repr == StructRepr::Transparent && (field_size != 0 || field_align != 1) {
                transparent_nontrivial += 1;
                transparent_carrier = Some((field_size, field_align, offset));
            }
            fields.push((offset, field.ty.clone()));
            sizes.push(field_size);
        }
        for left in 0..fields.len() {
            for right in left + 1..fields.len() {
                if byte_ranges_overlap(fields[left].0, sizes[left], fields[right].0, sizes[right]) {
                    return Err(format!(
                        "struct {ty} declared layout has overlapping fields {left} and {right}"
                    ));
                }
            }
        }
        if def.repr == StructRepr::Transparent {
            let (carrier_size, carrier_align, carrier_offset) =
                transparent_carrier.unwrap_or((0, 1, 0));
            if transparent_nontrivial > 1
                || size != carrier_size
                || align != carrier_align
                || carrier_offset != 0
            {
                return Err(format!(
                    "struct {ty} declares repr(transparent) but its size {size}, alignment {align}, field count, or representation-bearing field offset does not match its sole non-1-ZST field"
                ));
            }
        }
        Ok(AggregateLayout {
            size,
            align,
            fields,
        })
    }

    /// A tuple's layout (`tuple_layout`): the module's declared tuple layout
    /// when it has one, else the canonical declaration-order C layout.
    pub(crate) fn tuple_layout(&self, ty: &Ty) -> LayoutResult<AggregateLayout> {
        self.tuple_layout_in(ty, &mut Vec::new())
    }

    fn tuple_layout_in(&self, ty: &Ty, visiting: &mut Vec<Visit>) -> LayoutResult<AggregateLayout> {
        let Ty::Tuple(elems) = ty else {
            return Err(format!("{ty} is not a tuple"));
        };
        self.module
            .validate_tuple_layouts()
            .map_err(|error| error.to_string())?;
        if let Some(desc) = self
            .module
            .tuple_layout_descriptor(ty)
            .map_err(|error| error.to_string())?
        {
            return Ok(AggregateLayout {
                size: desc.size,
                align: desc.align,
                fields: desc
                    .field_offsets
                    .iter()
                    .copied()
                    .zip(elems.iter().cloned())
                    .collect(),
            });
        }
        self.aggregate_layout(elems.iter(), "tuple", visiting)
    }

    /// The C-style layout shared by undeclared structs, tuples and enum
    /// variants (`aggregate_layout`).
    fn aggregate_layout<'a>(
        &self,
        fields: impl Iterator<Item = &'a Ty>,
        kind: &str,
        visiting: &mut Vec<Visit>,
    ) -> LayoutResult<AggregateLayout> {
        let mut offset: u64 = 0;
        let mut max_align: u64 = 1;
        let mut out = Vec::new();
        for field_ty in fields {
            let field_align = self.align_in(field_ty, visiting)?.max(1);
            let field_size = self.size_in(field_ty, visiting)?;
            offset = align_up(offset, field_align)?;
            out.push((offset, field_ty.clone()));
            offset = offset
                .checked_add(field_size)
                .ok_or_else(|| format!("{kind} byte size overflow"))?;
            max_align = max_align.max(field_align);
        }
        let size = align_up(offset, max_align)?;
        Ok(AggregateLayout {
            size,
            align: max_align,
            fields: out,
        })
    }

    /// An enum's layout (`enum_layout`): its producer descriptor when it has
    /// one (re-validated), else trust-ir's canonical tagged union.
    pub(crate) fn enum_layout(&self, ty: &Ty) -> LayoutResult<EnumLayout> {
        self.enum_layout_in(ty, &mut Vec::new())
    }

    fn enum_layout_in(&self, ty: &Ty, visiting: &mut Vec<Visit>) -> LayoutResult<EnumLayout> {
        let Ty::Enum(eid) = ty else {
            return Err(format!("{ty} is not an enum"));
        };
        self.with_visit(Visit::Enum(*eid), ty, visiting, |visiting| {
            self.enum_layout_unguarded(ty, *eid, visiting)
        })
    }

    fn descriptor_field_size(&self, ty: &Ty, visiting: &mut Vec<Visit>) -> LayoutResult<u64> {
        match ty {
            Ty::Never => Ok(0),
            _ => self.size_in(ty, visiting),
        }
    }

    fn descriptor_field_align(&self, ty: &Ty, visiting: &mut Vec<Visit>) -> LayoutResult<u64> {
        match ty {
            Ty::Never => Ok(1),
            _ => self.align_in(ty, visiting),
        }
    }

    fn enum_layout_unguarded(
        &self,
        ty: &Ty,
        eid: EnumId,
        visiting: &mut Vec<Visit>,
    ) -> LayoutResult<EnumLayout> {
        let module = self.module;
        let def = module
            .enum_def(eid)
            .ok_or_else(|| format!("enum id {} not found in module", eid.0))?;
        def.effective_discriminants().ok_or_else(|| {
            format!(
                "enum {ty} has no canonical discriminant assignment (duplicate or overflowing values)"
            )
        })?;
        let tag = def.canonical_tag_repr().ok_or_else(|| {
            format!(
                "enum {ty} has no canonical tag (uninhabited, discriminants beyond 64-bit, or a repr hint too narrow)"
            )
        })?;
        let tag_ty = tag.ty();
        let tag_size = self.size_in(&tag_ty, visiting)?;
        let tag_align = self.align_in(&tag_ty, visiting)?;

        if let Some(desc) = &def.layout {
            if desc.align == 0
                || !desc.align.is_power_of_two()
                || !desc.size.is_multiple_of(desc.align)
                || desc.variant_field_offsets.len() != def.variants.len()
            {
                return Err(format!("enum {ty} has an incoherent layout descriptor"));
            }
            let mut variants = Vec::with_capacity(def.variants.len());
            for (variant_idx, (variant, offsets)) in def
                .variants
                .iter()
                .zip(&desc.variant_field_offsets)
                .enumerate()
            {
                if matches!(desc.encoding, EnumTagEncoding::SingleInhabited { variant } if usize::try_from(variant).ok() != Some(variant_idx))
                {
                    if !offsets.is_empty() {
                        return Err(format!(
                            "enum {ty} inactive variant {variant_idx} has a physical offset row"
                        ));
                    }
                    variants.push(Vec::new());
                    continue;
                }
                if offsets.len() != variant.fields.len() {
                    return Err(format!(
                        "enum {ty} layout descriptor variant {variant_idx} has {} offsets for {} fields",
                        offsets.len(),
                        variant.fields.len()
                    ));
                }
                let mut fields = Vec::with_capacity(offsets.len());
                for (field_ty, offset) in variant.fields.iter().zip(offsets) {
                    let field_size = self.descriptor_field_size(field_ty, visiting)?;
                    let field_align = self.descriptor_field_align(field_ty, visiting)?;
                    if !offset.is_multiple_of(field_align)
                        || field_align > desc.align
                        || offset
                            .checked_add(field_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(format!(
                            "enum {ty} layout descriptor variant {variant_idx} field at offset {offset} ({field_size} bytes, align {field_align}) is out of bounds, misaligned, or over-aligned for descriptor align {}",
                            desc.align,
                        ));
                    }
                    fields.push((*offset, field_ty.clone()));
                }
                for left in 0..fields.len() {
                    let left_size = self.descriptor_field_size(&fields[left].1, visiting)?;
                    for right in left + 1..fields.len() {
                        let right_size = self.descriptor_field_size(&fields[right].1, visiting)?;
                        if byte_ranges_overlap(
                            fields[left].0,
                            left_size,
                            fields[right].0,
                            right_size,
                        ) {
                            return Err(format!(
                                "enum {ty} layout descriptor variant {variant_idx} has overlapping fields {left} and {right}"
                            ));
                        }
                    }
                }
                variants.push(fields);
            }
            let tag = match &desc.encoding {
                EnumTagEncoding::Untagged => {
                    if def.variants.len() != 1 {
                        return Err(format!(
                            "enum {ty} declares the untagged encoding but has {} variants; an untagged layout can only describe a single-variant enum",
                            def.variants.len()
                        ));
                    }
                    TagLane::Untagged { variant: 0 }
                }
                EnumTagEncoding::SingleInhabited { variant } => {
                    let active = usize::try_from(*variant)
                        .ok()
                        .filter(|index| *index < def.variants.len())
                        .ok_or_else(|| {
                            format!("enum {ty} single-inhabited selector is out of range")
                        })?;
                    let mut query = trust_ir::Inhabitedness::for_module(module);
                    if def.variants.iter().enumerate().any(|(index, variant)| {
                        query.variant_is_uninhabited(variant) != (index != active)
                    }) {
                        return Err(format!(
                            "enum {ty} single-inhabited selection does not identify exactly one inhabited variant"
                        ));
                    }
                    TagLane::Untagged { variant: active }
                }
                EnumTagEncoding::Direct { tag_offset } => {
                    if tag_align > desc.align
                        || !tag_offset.is_multiple_of(tag_align)
                        || tag_offset
                            .checked_add(tag_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(format!(
                            "enum {ty} layout descriptor tag at offset {tag_offset} ({tag_size} bytes, align {tag_align}) is out of bounds, misaligned, or over-aligned for descriptor align {}",
                            desc.align,
                        ));
                    }
                    for (variant_idx, fields) in variants.iter().enumerate() {
                        for (field_idx, (field_offset, field_ty)) in fields.iter().enumerate() {
                            let field_size = self.descriptor_field_size(field_ty, visiting)?;
                            if byte_ranges_overlap(*tag_offset, tag_size, *field_offset, field_size)
                            {
                                return Err(format!(
                                    "enum {ty} layout descriptor direct tag overlaps variant {variant_idx} field {field_idx}"
                                ));
                            }
                        }
                    }
                    TagLane::Bytes {
                        offset: *tag_offset,
                        size: tag_size,
                    }
                }
                EnumTagEncoding::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_variants_end,
                    niche_start,
                    niche_offset,
                    niche_ty,
                } => {
                    let variant_count = u32::try_from(def.variants.len()).map_err(|_| {
                        format!("enum {ty} has too many variants for a niche encoding")
                    })?;
                    let niche_size = self.size_in(&niche_ty.ty(), visiting)?;
                    let niche_align = self.align_in(&niche_ty.ty(), visiting)?;
                    let niche_bits = (niche_size * 8) as u32;
                    let niche_mask = int_mask(niche_bits)
                        .ok_or_else(|| format!("unsupported niche lane width {niche_bits}"))?;
                    let niche_span = niche_variants_end
                        .checked_sub(*niche_variants_start)
                        .map(u128::from);
                    let covers_every_variant = niche_span.is_some()
                        && module
                            .niche_unencoded_inhabited_variant(
                                def,
                                *untagged_variant,
                                *niche_variants_start,
                                *niche_variants_end,
                            )
                            .is_none();
                    if *untagged_variant >= variant_count
                        || niche_variants_start > niche_variants_end
                        || *niche_variants_end >= variant_count
                        || !covers_every_variant
                        || *niche_start > niche_mask
                        || niche_span.is_none_or(|span| span > niche_mask)
                        || niche_align > desc.align
                        || !niche_offset.is_multiple_of(niche_align)
                        || niche_offset
                            .checked_add(niche_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(format!("enum {ty} has an incoherent niche encoding"));
                    }
                    let untagged_fields = &variants[*untagged_variant as usize];
                    let lane_is_covered = untagged_fields.iter().any(|(field_offset, field_ty)| {
                        self.size_in(field_ty, visiting).is_ok_and(|field_size| {
                            field_size > 0
                                && *field_offset <= *niche_offset
                                && field_offset
                                    .checked_add(field_size)
                                    .is_some_and(|field_end| {
                                        niche_offset
                                            .checked_add(niche_size)
                                            .is_some_and(|niche_end| field_end >= niche_end)
                                    })
                        })
                    });
                    if !lane_is_covered {
                        return Err(format!(
                            "enum {ty} niche lane is not covered by the untagged variant payload"
                        ));
                    }
                    for variant_idx in *niche_variants_start..=*niche_variants_end {
                        if variant_idx == *untagged_variant {
                            continue;
                        }
                        for (field_idx, (field_offset, field_ty)) in
                            variants[variant_idx as usize].iter().enumerate()
                        {
                            let field_size = self.descriptor_field_size(field_ty, visiting)?;
                            if byte_ranges_overlap(
                                *niche_offset,
                                niche_size,
                                *field_offset,
                                field_size,
                            ) {
                                return Err(format!(
                                    "enum {ty} niche lane overlaps niche-tagged variant {variant_idx} field {field_idx}"
                                ));
                            }
                        }
                    }
                    TagLane::Bytes {
                        offset: *niche_offset,
                        size: niche_size,
                    }
                }
            };
            return Ok(EnumLayout {
                size: desc.size,
                align: desc.align,
                tag,
                variants,
            });
        }

        let mut payload_size: u64 = 0;
        let mut payload_align: u64 = 1;
        let mut relative = Vec::with_capacity(def.variants.len());
        for variant in &def.variants {
            let layout = self.aggregate_layout(variant.fields.iter(), "enum variant", visiting)?;
            payload_size = payload_size.max(layout.size);
            payload_align = payload_align.max(layout.align);
            relative.push(layout.fields);
        }
        let payload_offset = align_up(tag_size, payload_align)?;
        let align = tag_align.max(payload_align);
        let size = align_up(
            payload_offset
                .checked_add(payload_size)
                .ok_or_else(|| "enum byte size overflow".to_string())?,
            align,
        )?;
        let variants = relative
            .into_iter()
            .map(|fields| {
                fields
                    .into_iter()
                    .map(|(offset, ty)| (payload_offset + offset, ty))
                    .collect()
            })
            .collect();
        Ok(EnumLayout {
            size,
            align,
            tag: TagLane::Bytes {
                offset: 0,
                size: tag_size,
            },
            variants,
        })
    }

    /// The bytes a typed `Store` of a `ty` value leaves INITIALIZED
    /// (`eval_store` + `encode_image`): a struct / tuple its fields'
    /// covered bytes, an array each element's, an enum its tag lane plus the
    /// fields of the variant stored — `variant` when the scanner knows it,
    /// else the tag lane only (under-approximated: fewer bytes marked written
    /// is never wrong). Padding and an inactive variant's tail are written
    /// UNINITIALIZED. Any other type writes every byte.
    ///
    /// The answer costs the type's description, not its byte size: an array
    /// is one periodic run of its element's coverage ([`ByteCoverage`]).
    pub fn written_coverage(&self, ty: &Ty, variant: Option<u32>) -> LayoutResult<ByteCoverage> {
        if self.module.type_contains_storage_by_value(ty) {
            return Err("Storage has no typed initialized write image".into());
        }
        self.coverage(ty, variant, Coverage::Written)
    }

    /// The bytes a typed `Load` of `ty` needs initialized (`eval_load`): a
    /// scalar all of them (a plain load of an uninitialized one yields
    /// poison), an aggregate the bytes a live field covers — for an enum the
    /// tag lane plus EVERY variant's fields (the variant is read from memory;
    /// requiring the union is never weaker than what the read needs). Costs
    /// the type's description, as [`Self::written_coverage`].
    pub fn read_coverage(&self, ty: &Ty) -> LayoutResult<ByteCoverage> {
        if self.module.type_contains_storage_by_value(ty) {
            return Err("Storage has no typed initialized read image".into());
        }
        self.coverage(ty, None, Coverage::Read)
    }

    /// The covered bytes of a `ty` image: the same byte sets the
    /// interpreter's `encode_image` / `first_uninit_covered` walks cover, as
    /// a structure over the type (fields at their offsets, an array as one
    /// periodic run) instead of one flag per byte.
    fn coverage(
        &self,
        ty: &Ty,
        variant: Option<u32>,
        coverage: Coverage,
    ) -> LayoutResult<ByteCoverage> {
        let size = self.size(ty)?;
        let inside = |offset: u64, part_size: u64, what: &str| {
            if offset.checked_add(part_size).is_some_and(|end| end <= size) {
                Ok(())
            } else {
                Err(format!("{what} of {ty} lies outside its image"))
            }
        };
        let span = |offset: u64, field_ty: &Ty| -> LayoutResult<(u64, ByteCoverage)> {
            let part = self.coverage(field_ty, None, coverage)?;
            inside(offset, part.size, "field")?;
            Ok((offset, part))
        };
        let node = match ty {
            Ty::Closure(id) => {
                let binding = self
                    .module
                    .closure_storage_binding(*id)
                    .map_err(str::to_owned)?;
                CoverageNode::Parts(
                    binding
                        .captures
                        .iter()
                        .zip(&binding.layout.capture_offsets)
                        .map(|(field_ty, offset)| span(*offset, field_ty))
                        .collect::<LayoutResult<_>>()?,
                )
            }
            Ty::Struct(_) | Ty::Tuple(_) => {
                let layout = match ty {
                    Ty::Struct(_) => self.struct_layout(ty)?,
                    _ => self.tuple_layout(ty)?,
                };
                CoverageNode::Parts(
                    layout
                        .fields
                        .iter()
                        .map(|(offset, field_ty)| span(*offset, field_ty))
                        .collect::<LayoutResult<_>>()?,
                )
            }
            Ty::Array(elem, len) => {
                let elem_ty = self.resolve_ty(*elem)?;
                let elem_size = self.size(&elem_ty)?;
                if elem_size == 0 || *len == 0 {
                    CoverageNode::Empty
                } else {
                    let extent = elem_size
                        .checked_mul(*len)
                        .ok_or_else(|| format!("element of {ty} lies outside its image"))?;
                    inside(0, extent, "element")?;
                    CoverageNode::Repeat {
                        stride: elem_size,
                        count: *len,
                        element: Box::new(self.coverage(&elem_ty, None, coverage)?),
                    }
                }
            }
            Ty::Enum(id) => {
                if self
                    .module
                    .enum_def(*id)
                    .and_then(|def| def.layout.as_ref())
                    .is_some_and(|desc| {
                        matches!(desc.encoding, EnumTagEncoding::SingleInhabited { .. })
                    })
                    && !trust_ir::ByValueStorageQuery::for_module(self.module).is_storage_free(ty)
                {
                    return Err(format!(
                        "enum {ty} carries Storage or an incomplete/ambiguous by-value schema; no initialized coverage"
                    ));
                }
                let layout = self.enum_layout(ty)?;
                if let (Coverage::Written, Some(variant), TagLane::Untagged { variant: active }) =
                    (coverage, variant, layout.tag)
                    && usize::try_from(variant).ok() != Some(active)
                {
                    return Err(format!(
                        "{ty} tag-free image cannot encode inactive variant {variant}"
                    ));
                }
                let mut parts = Vec::new();
                if let TagLane::Bytes { offset, size } = layout.tag {
                    inside(offset, size, "tag")?;
                    parts.push((
                        offset,
                        ByteCoverage {
                            size,
                            node: CoverageNode::Full,
                        },
                    ));
                }
                let variants: Vec<usize> = match (coverage, variant) {
                    (Coverage::Read, _) => (0..layout.variants.len()).collect(),
                    (Coverage::Written, Some(variant)) => vec![variant as usize],
                    // The absent tag still identifies the selected type variant.
                    (Coverage::Written, None) => match layout.tag {
                        TagLane::Untagged { variant } => vec![variant],
                        TagLane::Bytes { .. } => Vec::new(),
                    },
                };
                for index in variants {
                    let fields = layout
                        .variants
                        .get(index)
                        .ok_or_else(|| format!("{ty} has no variant {index}"))?;
                    for (offset, field_ty) in fields {
                        parts.push(span(*offset, field_ty)?);
                    }
                }
                CoverageNode::Parts(parts)
            }
            _ => CoverageNode::Full,
        };
        Ok(ByteCoverage { size, node })
    }
}

/// The bytes of one typed image a store leaves initialized or a load needs
/// ([`FsymLayout::written_coverage`] / [`FsymLayout::read_coverage`]).
///
/// It is a structure over the type, not one flag per byte: struct, tuple and
/// enum parts sit at their offsets and an array is ONE periodic run of its
/// element's coverage, so its size is the type's description and never the
/// image's byte count (an array of `2^59` padded structs costs one struct).
/// [`Self::contains`] answers one byte in time bounded by the type's nesting
/// and part count.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ByteCoverage {
    size: u64,
    node: CoverageNode,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CoverageNode {
    /// No byte (an empty array, or a zero-sized element).
    Empty,
    /// Every byte.
    Full,
    /// The union of these parts, each at its offset within the image. Parts
    /// may overlap: an enum read needs every variant's fields.
    Parts(Vec<(u64, ByteCoverage)>),
    /// `count` copies of `element`, the `k`-th at offset `k * stride`.
    Repeat {
        stride: u64,
        count: u64,
        element: Box<ByteCoverage>,
    },
}

impl ByteCoverage {
    /// The image's byte size.
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Whether every byte of the image is covered. Exact where parts are
    /// disjoint (a struct, a tuple, an array); where they overlap (an enum's
    /// tag lane beside its fields, every variant of a read) it credits only
    /// parts that are wholly covered themselves, so a union of partial parts
    /// that happens to cover every byte answers `false`: an
    /// under-approximation, never a false `true`.
    pub fn covers_all(&self) -> bool {
        match &self.node {
            CoverageNode::Full => true,
            CoverageNode::Empty => self.size == 0,
            CoverageNode::Repeat {
                stride,
                count,
                element,
            } => {
                element.size == *stride
                    && stride.checked_mul(*count) == Some(self.size)
                    && element.covers_all()
            }
            CoverageNode::Parts(parts) => {
                let mut full: Vec<(u64, u64)> = parts
                    .iter()
                    .filter(|(_, part)| part.covers_all())
                    .map(|(offset, part)| (*offset, offset.saturating_add(part.size)))
                    .collect();
                full.sort_unstable();
                let mut reach = 0u64;
                for (start, end) in full {
                    if start > reach {
                        break;
                    }
                    reach = reach.max(end);
                }
                reach >= self.size
            }
        }
    }

    /// Whether byte `byte` of the image is covered (`false` past its end).
    pub fn contains(&self, byte: u64) -> bool {
        let mut coverage = self;
        let mut byte = byte;
        loop {
            if byte >= coverage.size {
                return false;
            }
            match &coverage.node {
                CoverageNode::Empty => return false,
                CoverageNode::Full => return true,
                CoverageNode::Repeat {
                    stride,
                    count,
                    element,
                } => {
                    let index = byte / stride;
                    if index >= *count {
                        return false;
                    }
                    byte -= index * stride;
                    coverage = element;
                }
                CoverageNode::Parts(parts) => {
                    return parts.iter().any(|(offset, part)| {
                        byte.checked_sub(*offset)
                            .is_some_and(|within| part.contains(within))
                    });
                }
            }
        }
    }
}

/// Which covered-byte set `FsymLayout::coverage` describes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Coverage {
    /// What a store of a value writes initialized (under-approximated).
    Written,
    /// What a load needs initialized (over-approximated).
    Read,
}

/// The interpreter's `align_addr` / `align_up`.
fn align_up(value: u64, align: u64) -> LayoutResult<u64> {
    let mask = align
        .checked_sub(1)
        .ok_or_else(|| "struct layout offset overflow".to_string())?;
    value
        .checked_add(mask)
        .map(|value| value & !mask)
        .ok_or_else(|| "struct layout offset overflow".to_string())
}

fn byte_ranges_overlap(a_offset: u64, a_size: u64, b_offset: u64, b_size: u64) -> bool {
    if a_size == 0 || b_size == 0 {
        return false;
    }
    let Some(a_end) = a_offset.checked_add(a_size) else {
        return true;
    };
    let Some(b_end) = b_offset.checked_add(b_size) else {
        return true;
    };
    a_offset < b_end && b_offset < a_end
}

fn int_mask(bits: u32) -> Option<u128> {
    match bits {
        1..=127 => Some((1u128 << bits) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

/// The alignment an `Alloca` / `HeapAlloc` of `count` `ty`s is placed at:
/// its explicit `align`, else `ty`'s natural alignment (the interpreter's
/// `eval_alloca`: `align.unwrap_or(natural_align)`). `None` when `ty` has
/// no layout.
pub(crate) fn allocation_align(module: &Module, ty: &Ty, align: Option<u64>) -> Option<u64> {
    match align {
        Some(align) => Some(align),
        None => FsymLayout::new(module).align(ty).ok(),
    }
}

/// The alignment a module global's storage is placed at (the interpreter's
/// `global_pointer`): the max of its type's natural alignment, its declared
/// power-of-two alignment, and the 16-byte section floor. `None` when the
/// type has no layout.
pub(crate) fn global_align(module: &Module, global: &trust_ir::Global) -> Option<u64> {
    const GLOBAL_SECTION_ALIGN: u64 = 16;
    let natural = FsymLayout::new(module).align(&global.ty).ok()?;
    let declared = global
        .align
        .map(u64::from)
        .filter(|align| align.is_power_of_two())
        .unwrap_or(1);
    Some(natural.max(declared).max(GLOBAL_SECTION_ALIGN))
}
