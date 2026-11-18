// trust-cg-codegen/wasm/layout.rs - wasm32 byte layout of trust-ir values
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The wasm32 byte layout of every trust-ir value the wasm lane carries.
//!
//! WebAssembly has four value types, so most trust-ir values do not fit in a
//! wasm local. This module decides, once, how each trust-ir type is CARRIED:
//!
//! * [`Carrier::Scalar`] — one wasm local (integers up to 64 bits, `bool`,
//!   `f32`/`f64`, thin pointers, function pointers);
//! * [`Carrier::Void`] — nothing at all (`()` and every zero-sized type);
//! * [`Carrier::Mem`] — the value's BYTES in linear memory, laid out exactly
//!   as trust-ir's layout engine lays them out, with a wasm `i32` local holding
//!   their address (structs, tuples, enums, arrays, fat pointers, and the
//!   128-bit integers).
//!
//! [`carrier_of`] is the TYPE's carrier: the one the ABI, the memory image
//! and every by-type decision use. The lowering may carry one 128-bit integer
//! VALUE as a [`Carrier::Pair`] instead (`lower/pair.rs` decides which); no
//! type is ever given that carrier here.
//!
//! A memory-carried value's image IS its trust-ir memory image, so a `Load` or
//! `Store` of one is a byte copy and a field access is a load at the field's
//! layout offset — there is no second representation to keep in sync.
//!
//! The layout authority is the reference interpreter's byte funnel
//! (`interpret.rs`, `byte_size_in` / `byte_align_in`), mirrored recursively
//! here so every aggregate is laid out by ONE rule at every depth:
//!
//! * leaves (scalars, pointers, fat pointers, 128-bit integers, `()`) take
//!   trust-ir's own [`Module::ty_layout_shape`];
//! * a tuple takes its declared descriptor (validated as the interpreter
//!   validates it; the compile entry points currently refuse declared tuple
//!   layouts upstream), else the C-style rule (each field at the next offset
//!   aligned to its own alignment, the size rounded up to the widest
//!   alignment);
//! * a struct takes its declared `size`/`align`/offsets verbatim after the
//!   interpreter's structural re-validation, else (nothing declared) the same
//!   C-style rule;
//! * an array is its element's stride times its length;
//! * an enum takes its producer-supplied `EnumLayoutDescriptor` (direct, niche
//!   or untagged encoding), else the canonical tagged union (tag at offset 0,
//!   each variant laid out C-style from the shared payload offset).
//!
//! Wherever trust-ir's shape API answers for an aggregate it must agree with
//! this rule, or the type is refused; it declines any aggregate with an
//! undeclared tuple or struct inside, and there the interpreter's rule alone
//! is the semantics.
//!
//! Everything this module cannot place EXACTLY is refused by name: a guessed
//! offset is a silent data miscompile.

use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
use trust_ir::{Constant, EnumId, Module, StructDef, StructId, StructRepr, Ty, TyId};

use super::encode::ValType;
use super::lower::WasmLowerError;

/// How one trust-ir value is carried by the wasm lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Carrier {
    /// One wasm local of this value type.
    Scalar(ValType),
    /// A zero-sized value: no local, no bytes, no wasm parameter.
    Void,
    /// `size` bytes of linear memory, aligned to `align`; the value's wasm
    /// local holds their `i32` address.
    Mem { size: u32, align: u32 },
    /// Two `i64` locals holding the low and high halves of a 128-bit integer
    /// value, which has no address. Chosen per VALUE by the lowering
    /// (`lower/pair.rs`), never by [`carrier_of`]: the value's bytes, when
    /// they cross memory or a call, are its 16-byte little-endian image, low
    /// half first, exactly as a [`Carrier::Mem`] 128-bit integer's.
    Pair,
}

impl Carrier {
    pub(crate) fn is_mem(self) -> bool {
        matches!(self, Carrier::Mem { .. })
    }
}

fn unsupported(ty: &Ty, why: impl std::fmt::Display) -> WasmLowerError {
    WasmLowerError::UnsupportedType(format!("{ty:?}: {why}"))
}

/// The wasm value type of a SCALAR trust-ir type, or `None` when the type is
/// not carried in one local.
///
/// Pointer-sized integers are 32-bit: the lane only accepts modules pinned to
/// the wasm32 shape (`require_wasm32_target_info`). A function pointer is its
/// `funcref` table index — an `i32`.
pub(crate) fn scalar_valtype(ty: &Ty) -> Option<ValType> {
    Some(match ty {
        Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16 | Ty::I32 | Ty::U32 | Ty::Bool => ValType::I32,
        Ty::Isize | Ty::Usize | Ty::Char => ValType::I32,
        Ty::I64 | Ty::U64 => ValType::I64,
        Ty::F32 => ValType::F32,
        Ty::F64 => ValType::F64,
        Ty::Ptr
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::Rc(_)
        | Ty::Func(_) => ValType::I32,
        _ => return None,
    })
}

/// A type on the current BY-VALUE layout path: laying out one of these again
/// before the first finishes means the type contains itself inline and has no
/// finite layout. Refused by name, as the reference interpreter's
/// `with_layout_visit` refuses it (modules reach the lane unvalidated, and
/// unbounded recursion would be a crash, not an error). A pointer never
/// recurses into its pointee, so `*mut Node` inside `Node` is not a cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Visit {
    Struct(StructId),
    Enum(EnumId),
    Ty(TyId),
}

fn with_visit<T>(
    key: Visit,
    ty: &Ty,
    visiting: &mut Vec<Visit>,
    layout: impl FnOnce(&mut Vec<Visit>) -> Result<T, WasmLowerError>,
) -> Result<T, WasmLowerError> {
    if visiting.contains(&key) {
        return Err(unsupported(
            ty,
            "contains itself by value (no finite layout)",
        ));
    }
    visiting.push(key);
    let result = layout(visiting);
    visiting.pop();
    result
}

/// A record's byte layout: size, alignment and every field at its offset.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct RecordLayout {
    pub size: u32,
    pub align: u32,
    pub parts: Vec<Part>,
}

/// The C-style aggregate layout the reference interpreter uses for an
/// undeclared tuple, a struct that declares no layout, and each canonical enum
/// variant (`interpret.rs`, `aggregate_layout`): each field at the next offset
/// aligned to its own alignment, the size rounded up to the widest alignment
/// (at least 1).
fn c_layout<'t>(
    module: &Module,
    ty: &Ty,
    fields: impl Iterator<Item = &'t Ty>,
    visiting: &mut Vec<Visit>,
) -> Result<RecordLayout, WasmLowerError> {
    let overflow = || unsupported(ty, "layout overflows the wasm32 space");
    let mut cursor = 0u32;
    let mut max_align = 1u32;
    let mut parts = Vec::new();
    for t in fields {
        let (size, align) = size_align_in(module, t, visiting)?;
        cursor = cursor
            .checked_next_multiple_of(align)
            .ok_or_else(overflow)?;
        parts.push(Part {
            offset: cursor,
            ty: t.clone(),
        });
        cursor = cursor.checked_add(size).ok_or_else(overflow)?;
        max_align = max_align.max(align);
    }
    let size = cursor
        .checked_next_multiple_of(max_align)
        .ok_or_else(overflow)?;
    Ok(RecordLayout {
        size,
        align: max_align,
        parts,
    })
}

/// A tuple's layout: the module's declared tuple layout when it has one, else
/// the interpreter's C-style rule ([`c_layout`], `interpret.rs`
/// `tuple_layout_in`). trust-ir's shape API declines undeclared tuples; the
/// interpreter's rule is the semantics.
///
/// A declared descriptor is used only after the interpreter's own validation
/// of it (`validate_tuple_layouts`, then the shape API on this tuple: one
/// offset per element, every element in bounds, aligned for its type, not
/// over-aligned for the tuple, no two elements overlapping); an incoherent
/// descriptor is refused by name. The compile entry points refuse any module
/// that declares a tuple layout before this module runs (trust-cg-lower's
/// contract surface), so this branch is reached only by direct lowering.
fn tuple_layout_in(
    module: &Module,
    ty: &Ty,
    visiting: &mut Vec<Visit>,
) -> Result<RecordLayout, WasmLowerError> {
    let Ty::Tuple(elems) = ty else {
        return Err(unsupported(ty, "not a tuple"));
    };
    if let Some(desc) = module
        .tuple_layout_descriptor(ty)
        .map_err(|e| unsupported(ty, format!("tuple layout ({e:?})")))?
    {
        module
            .validate_tuple_layouts()
            .and_then(|()| module.ty_layout_shape(ty))
            .map_err(|e| unsupported(ty, format!("incoherent declared tuple layout ({e:?})")))?;
        if desc.field_offsets.len() != elems.len() {
            return Err(unsupported(
                ty,
                "declared tuple layout offset count disagrees with the elements",
            ));
        }
        let size = u32::try_from(desc.size).map_err(|_| unsupported(ty, "tuple size"))?;
        let align = u32::try_from(desc.align).map_err(|_| unsupported(ty, "tuple align"))?;
        let parts = desc
            .field_offsets
            .iter()
            .zip(elems)
            .map(|(off, t)| {
                Ok(Part {
                    offset: u32::try_from(*off).map_err(|_| unsupported(ty, "tuple offset"))?,
                    ty: t.clone(),
                })
            })
            .collect::<Result<Vec<_>, WasmLowerError>>()?;
        return Ok(RecordLayout {
            size,
            align: align.max(1),
            parts,
        });
    }
    c_layout(module, ty, elems.iter(), visiting)
}

/// A struct's layout, exactly as the reference interpreter derives it
/// (`interpret.rs`, `struct_layout_unguarded` / `declared_struct_layout`):
///
/// * `size` and `align` declared: the DECLARED layout is used verbatim, after
///   the interpreter's structural re-validation — a power-of-two alignment the
///   size is a multiple of, a `repr(packed(N))` clamp that is a non-zero power
///   of two the alignment does not exceed, every field in bounds and aligned
///   for its own type (clamped), no field over-aligned for the struct, no two
///   fields overlapping, a field without an offset only when zero-sized, and
///   the `repr(transparent)` carrier rule;
/// * neither declared and no field offset declared: the C-style layout
///   ([`c_layout`]) — nothing was claimed, so the canonical declaration-order
///   layout applies;
/// * anything in between is a contradiction the interpreter refuses too.
///
/// Every field is sized by this module's own rule, so a declared struct whose
/// field is an undeclared tuple or struct is laid out, as the interpreter lays
/// it out.
fn struct_layout_in(
    module: &Module,
    ty: &Ty,
    visiting: &mut Vec<Visit>,
) -> Result<RecordLayout, WasmLowerError> {
    let Ty::Struct(sid) = ty else {
        return Err(unsupported(ty, "not a struct"));
    };
    with_visit(Visit::Struct(*sid), ty, visiting, |visiting| {
        let def = module
            .struct_def(*sid)
            .ok_or_else(|| unsupported(ty, "unknown struct"))?;
        match (def.size, def.align) {
            (Some(size), Some(align)) => {
                declared_struct_layout(module, ty, def, size, align, visiting)
            }
            (None, None) => {
                if let Some(index) = def.fields.iter().position(|f| f.offset.is_some()) {
                    return Err(unsupported(
                        ty,
                        format!(
                            "field {index} declares an offset but the struct declares no size or alignment"
                        ),
                    ));
                }
                c_layout(module, ty, def.fields.iter().map(|f| &f.ty), visiting)
            }
            _ => Err(unsupported(
                ty,
                "declares a size without an alignment, or the reverse",
            )),
        }
    })
}

fn declared_struct_layout(
    module: &Module,
    ty: &Ty,
    def: &StructDef,
    size: u64,
    align: u64,
    visiting: &mut Vec<Visit>,
) -> Result<RecordLayout, WasmLowerError> {
    if align == 0 || !align.is_power_of_two() || !size.is_multiple_of(align) {
        return Err(unsupported(
            ty,
            format!("incoherent declared size {size} / alignment {align}"),
        ));
    }
    let clamp = match def.repr {
        StructRepr::Packed(n) => {
            if n == 0 || !n.is_power_of_two() {
                return Err(unsupported(
                    ty,
                    format!("repr(packed({n})): the clamp must be a non-zero power of two"),
                ));
            }
            u64::from(n)
        }
        _ => u64::MAX,
    };
    if align > clamp {
        return Err(unsupported(
            ty,
            format!("declared alignment {align} exceeds its repr(packed({clamp})) clamp"),
        ));
    }
    let mut placed: Vec<(u64, u64, Ty)> = Vec::with_capacity(def.fields.len());
    let mut transparent_nontrivial = 0usize;
    let mut transparent_carrier = (0u64, 1u64, 0u64);
    for (index, field) in def.fields.iter().enumerate() {
        let (fsize, falign) = size_align_in(module, &field.ty, visiting)?;
        let (fsize, falign) = (u64::from(fsize), u64::from(falign).max(1).min(clamp));
        let offset = match field.offset {
            Some(offset) => {
                if !offset.is_multiple_of(falign)
                    || falign > align
                    || offset.checked_add(fsize).is_none_or(|end| end > size)
                {
                    return Err(unsupported(
                        ty,
                        format!(
                            "field {index} at declared offset {offset} ({fsize} bytes, align \
                             {falign}) is out of bounds, misaligned, or over-aligned for size \
                             {size} / align {align}"
                        ),
                    ));
                }
                offset
            }
            None if fsize == 0 => 0,
            None => {
                return Err(unsupported(
                    ty,
                    format!("field {index} occupies {fsize} bytes but has no declared offset"),
                ));
            }
        };
        if def.repr == StructRepr::Transparent && (fsize != 0 || falign != 1) {
            transparent_nontrivial += 1;
            transparent_carrier = (fsize, falign, offset);
        }
        placed.push((offset, fsize, field.ty.clone()));
    }
    for (l, left) in placed.iter().enumerate() {
        for (r, right) in placed.iter().enumerate().skip(l + 1) {
            let overlap = left.1 != 0
                && right.1 != 0
                && left.0 < right.0 + right.1
                && right.0 < left.0 + left.1;
            if overlap {
                return Err(unsupported(
                    ty,
                    format!("declared fields {l} and {r} overlap"),
                ));
            }
        }
    }
    if def.repr == StructRepr::Transparent
        && (transparent_nontrivial > 1
            || size != transparent_carrier.0
            || align != transparent_carrier.1
            || transparent_carrier.2 != 0)
    {
        return Err(unsupported(
            ty,
            "repr(transparent) does not match its sole non-trivial field",
        ));
    }
    let size = u32::try_from(size).map_err(|_| unsupported(ty, "larger than the wasm32 space"))?;
    let align = u32::try_from(align).map_err(|_| unsupported(ty, "alignment overflows"))?;
    let parts = placed
        .into_iter()
        .map(|(offset, _, ty)| Part {
            // offset + size <= declared size, which fits u32.
            offset: offset as u32,
            ty,
        })
        .collect();
    Ok(RecordLayout { size, align, parts })
}

/// Byte size and alignment of a LEAF type (a scalar, pointer, fat pointer,
/// 128-bit integer or `()`) from trust-ir's layout engine.
fn shape_size_align(module: &Module, ty: &Ty) -> Result<(u32, u32), WasmLowerError> {
    let shape = module
        .ty_layout_shape(ty)
        .map_err(|e| unsupported(ty, format!("no layout ({e:?})")))?;
    let size = shape
        .size_bytes()
        .ok_or_else(|| unsupported(ty, "size is not a whole number of bytes"))?;
    let align = shape.align_bits.map_or(1, |bits| (bits / 8).max(1));
    let size = u32::try_from(size).map_err(|_| unsupported(ty, "larger than the wasm32 space"))?;
    let align = u32::try_from(align).map_err(|_| unsupported(ty, "alignment overflows"))?;
    if !align.is_power_of_two() {
        return Err(unsupported(
            ty,
            format!("alignment {align} is not a power of two"),
        ));
    }
    Ok((size, align))
}

/// Wherever trust-ir's shape API DOES answer for an aggregate, it must agree
/// with the lane's recursive rule: if the two disagree, this module's reading
/// of the layout rules is wrong and nothing it emits for the type can be
/// trusted. Where the shape API declines (an undeclared tuple or struct
/// anywhere inside), the interpreter's rule alone is the semantics.
fn cross_check(module: &Module, ty: &Ty, size: u32, align: u32) -> Result<(), WasmLowerError> {
    let Ok(shape) = module.ty_layout_shape(ty) else {
        return Ok(());
    };
    let agrees = shape.size_bytes() == Some(u64::from(size))
        && shape
            .align_bits
            .is_none_or(|bits| (bits / 8).max(1) == u64::from(align));
    if agrees {
        Ok(())
    } else {
        Err(unsupported(
            ty,
            format!(
                "the lane lays it out as {size} bytes / align {align}, trust-ir's shape as {:?} \
                 bits / align {:?} bits",
                shape.size_bits, shape.align_bits
            ),
        ))
    }
}

/// Byte size and alignment of `ty`: the reference interpreter's `byte_size` /
/// `byte_align` (tuples, undeclared structs and every aggregate containing
/// them by the interpreter's C-style rule; declared structs and enum
/// descriptors verbatim after re-validation; leaves from trust-ir's layout
/// engine).
pub(crate) fn size_align(module: &Module, ty: &Ty) -> Result<(u32, u32), WasmLowerError> {
    size_align_in(module, ty, &mut Vec::new())
}

fn size_align_in(
    module: &Module,
    ty: &Ty,
    visiting: &mut Vec<Visit>,
) -> Result<(u32, u32), WasmLowerError> {
    let (size, align) = match ty {
        Ty::Tuple(_) => {
            let l = tuple_layout_in(module, ty, visiting)?;
            (l.size, l.align)
        }
        Ty::Struct(_) => {
            let l = struct_layout_in(module, ty, visiting)?;
            (l.size, l.align)
        }
        Ty::Array(elem_id, len) => {
            let (_, stride, align) = array_stride_in(module, ty, *elem_id, visiting)?;
            let size = u64::from(stride)
                .checked_mul(*len)
                .and_then(|s| u32::try_from(s).ok())
                .ok_or_else(|| unsupported(ty, "larger than the wasm32 space"))?;
            (size, align)
        }
        Ty::Enum(_) => {
            let image = enum_image_in(module, ty, visiting)?;
            (image.size, image.align)
        }
        // Named, not left to trust-ir's layout engine: since v58 that engine
        // sizes a closure with a declared frame.
        Ty::Closure(_) => return Err(closure_refusal(ty)),
        _ => return shape_size_align(module, ty),
    };
    cross_check(module, ty, size, align)?;
    Ok((size, align))
}

/// An array's element type, stride (the element's size rounded up to its
/// alignment) and alignment.
fn array_stride_in(
    module: &Module,
    ty: &Ty,
    elem_id: TyId,
    visiting: &mut Vec<Visit>,
) -> Result<(Ty, u32, u32), WasmLowerError> {
    let elem = module
        .ty(elem_id)
        .cloned()
        .ok_or_else(|| unsupported(ty, "unknown element type"))?;
    with_visit(Visit::Ty(elem_id), ty, visiting, |visiting| {
        let (esize, ealign) = size_align_in(module, &elem, visiting)?;
        let stride = esize
            .checked_next_multiple_of(ealign)
            .ok_or_else(|| unsupported(ty, "array stride overflows"))?;
        Ok((elem.clone(), stride, ealign))
    })
}

/// The refusal of a first-class closure value, by value or inside an
/// aggregate. Since trust-ir v58 a declared frame (`Module.closure_layouts`)
/// gives a closure a byte size in trust-ir's layout engine; the lane still
/// lays out no closure environment, whatever is declared.
fn closure_refusal(ty: &Ty) -> WasmLowerError {
    unsupported(
        ty,
        "[TCG-WASM-CLOSURE] is a first-class closure value (a function bundled with its \
         captured environment, applied by `call_indirect` with the captures as leading \
         arguments); the wasm32 lane lays out no closure environment and closure \
         application is outside the lowering-target subset it compiles, so it is \
         refused (a producer spells a closure as an environment in memory plus a \
         function pointer taking it)",
    )
}

/// How `ty` is carried. Refuses types with no wasm32 layout this lane can
/// honor (SIMD vectors, `f16`/`f128`, abstract sequences and sets, closures).
pub(crate) fn carrier_of(module: &Module, ty: &Ty) -> Result<Carrier, WasmLowerError> {
    if let Some(vt) = scalar_valtype(ty) {
        return Ok(Carrier::Scalar(vt));
    }
    match ty {
        Ty::Unit | Ty::Never => return Ok(Carrier::Void),
        Ty::I128
        | Ty::U128
        | Ty::Struct(_)
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Array(_, _)
        | Ty::FatPtr(_) => {}
        Ty::Closure(_) => return Err(closure_refusal(ty)),
        other => {
            return Err(unsupported(
                other,
                "no wasm32 carrier (the lane carries integers, floats, pointers, structs, \
                 tuples, enums, arrays, fat pointers and 128-bit integers)",
            ));
        }
    }
    let (size, align) = size_align(module, ty)?;
    if size == 0 {
        return Ok(Carrier::Void);
    }
    Ok(Carrier::Mem { size, align })
}

/// One addressable part of a memory-carried value: its byte offset from the
/// value's address and its trust-ir type.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Part {
    pub offset: u32,
    pub ty: Ty,
}

/// Every field of a struct or tuple with its byte offset.
pub(crate) fn record_fields(module: &Module, ty: &Ty) -> Result<Vec<Part>, WasmLowerError> {
    let mut visiting = Vec::new();
    match ty {
        Ty::Tuple(_) => Ok(tuple_layout_in(module, ty, &mut visiting)?.parts),
        Ty::Struct(_) => Ok(struct_layout_in(module, ty, &mut visiting)?.parts),
        other => Err(unsupported(other, "not a struct or tuple")),
    }
}

/// An array's element type, stride in bytes, and length. The whole array is
/// sized first, so every `index * stride` below `len` fits the wasm32 space.
pub(crate) fn array_elem(module: &Module, ty: &Ty) -> Result<(Ty, u32, u64), WasmLowerError> {
    let Ty::Array(elem_id, len) = ty else {
        return Err(unsupported(ty, "not an array"));
    };
    size_align(module, ty)?;
    let (elem, stride, _) = array_stride_in(module, ty, *elem_id, &mut Vec::new())?;
    Ok((elem, stride, *len))
}

/// The two lanes of a fat pointer: the data pointer at offset 0 and the
/// metadata word after it (wasm32: 4 bytes each).
pub(crate) fn fat_ptr_lanes(ty: &Ty) -> Result<(Part, Part), WasmLowerError> {
    let meta = ty
        .pointer_metadata_ty(32)
        .ok_or_else(|| unsupported(ty, "not a fat pointer"))?;
    Ok((
        Part {
            offset: 0,
            ty: Ty::Ptr,
        },
        Part {
            offset: 4,
            ty: meta,
        },
    ))
}

/// How an enum's discriminant is kept in its byte image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EnumView {
    /// No tag bytes: the (single) variant is a fact of the type.
    Untagged { variant: usize },
    /// The discriminant is stored at `offset` as the canonical tag integer.
    Direct { offset: u32 },
    /// The discriminant is encoded in otherwise-invalid values of a payload
    /// lane of the `untagged_variant`.
    Niche {
        untagged_variant: usize,
        start: u32,
        end: u32,
        niche_start: u128,
        offset: u32,
        bytes: u32,
    },
}

/// The byte image of a `Ty::Enum`: exactly the reference interpreter's.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct EnumImage {
    /// The integer type lane 0 of the enum value carries (the canonical tag).
    pub tag_ty: Ty,
    /// Effective discriminant of each variant.
    pub discriminants: Vec<i128>,
    /// Each variant's fields at their ABSOLUTE byte offsets.
    pub variants: Vec<Vec<Part>>,
    pub view: EnumView,
    /// The enum's byte size and alignment.
    pub size: u32,
    pub align: u32,
}

fn tag_int_ty(repr: EnumTagRepr) -> Ty {
    repr.ty()
}

/// Resolve the byte image of enum `ty`.
pub(crate) fn enum_image(module: &Module, ty: &Ty) -> Result<EnumImage, WasmLowerError> {
    enum_image_in(module, ty, &mut Vec::new())
}

fn enum_image_in(
    module: &Module,
    ty: &Ty,
    visiting: &mut Vec<Visit>,
) -> Result<EnumImage, WasmLowerError> {
    let Ty::Enum(eid) = ty else {
        return Err(unsupported(ty, "not an enum"));
    };
    with_visit(Visit::Enum(*eid), ty, visiting, |visiting| {
        enum_image_unguarded(module, ty, *eid, visiting)
    })
}

fn enum_image_unguarded(
    module: &Module,
    ty: &Ty,
    eid: EnumId,
    visiting: &mut Vec<Visit>,
) -> Result<EnumImage, WasmLowerError> {
    let def = module
        .enum_def(eid)
        .ok_or_else(|| unsupported(ty, "unknown enum"))?;
    let discriminants = def
        .effective_discriminants()
        .ok_or_else(|| unsupported(ty, "duplicate or overflowing discriminants"))?;
    let repr = def
        .canonical_tag_repr()
        .ok_or_else(|| unsupported(ty, "no canonical tag representation"))?;
    if matches!(repr, EnumTagRepr::U128 | EnumTagRepr::I128) {
        return Err(unsupported(ty, "128-bit enum tags are not lowered"));
    }
    let tag_ty = tag_int_ty(repr);
    if let Some(desc) = &def.layout {
        return descriptor_image(module, ty, def, desc, tag_ty, discriminants, visiting);
    }
    // Canonical tagged union (`interpret.rs`, `enum_layout_unguarded`): tag at
    // 0; each variant laid out C-style from the payload offset (the tag size
    // aligned up to the widest variant alignment); the enum aligned to the
    // wider of tag and payload, its size rounded up to that alignment.
    let overflow = || unsupported(ty, "enum layout overflows the wasm32 space");
    let (tag_size, tag_align) = size_align_in(module, &tag_ty, visiting)?;
    let mut payload_size = 0u32;
    let mut payload_align = 1u32;
    let mut variants = Vec::with_capacity(def.variants.len());
    for variant in &def.variants {
        let l = c_layout(module, ty, variant.fields.iter(), visiting)?;
        payload_size = payload_size.max(l.size);
        payload_align = payload_align.max(l.align);
        variants.push(l.parts);
    }
    let payload_offset = tag_size
        .checked_next_multiple_of(payload_align)
        .ok_or_else(overflow)?;
    for fields in &mut variants {
        for f in fields.iter_mut() {
            f.offset = f.offset.checked_add(payload_offset).ok_or_else(overflow)?;
        }
    }
    let align = tag_align.max(payload_align);
    let size = payload_offset
        .checked_add(payload_size)
        .and_then(|end| end.checked_next_multiple_of(align))
        .ok_or_else(overflow)?;
    // Where trust-ir's shape API answers (no undeclared tuple or struct in any
    // variant), its canonical payload offset must be this one: if the two
    // disagree this module's reading of the layout rules is wrong, and nothing
    // it emits for this enum can be trusted.
    if let Ok(shape) = module.enum_layout_shape(eid)
        && u64::from(payload_offset) * 8 != shape.payload_offset_bits
    {
        return Err(unsupported(
            ty,
            format!(
                "canonical payload offset {payload_offset} disagrees with trust-ir's {} bits",
                shape.payload_offset_bits
            ),
        ));
    }
    Ok(EnumImage {
        tag_ty,
        discriminants,
        variants,
        view: EnumView::Direct { offset: 0 },
        size,
        align,
    })
}

fn descriptor_image(
    module: &Module,
    ty: &Ty,
    def: &trust_ir::EnumDef,
    desc: &EnumLayoutDescriptor,
    tag_ty: Ty,
    discriminants: Vec<i128>,
    visiting: &mut Vec<Visit>,
) -> Result<EnumImage, WasmLowerError> {
    if matches!(desc.encoding, EnumTagEncoding::DirectWithUninhabited { .. }) {
        return Err(unsupported(
            ty,
            "DirectWithUninhabited storage profiles are outside the wasm value-image model",
        ));
    }
    if desc.variant_field_offsets.len() != def.variants.len()
        || desc.align == 0
        || !desc.align.is_power_of_two()
        || !desc.size.is_multiple_of(desc.align)
    {
        return Err(unsupported(ty, "incoherent layout descriptor"));
    }
    let size = u32::try_from(desc.size).map_err(|_| unsupported(ty, "descriptor size"))?;
    let align = u32::try_from(desc.align).map_err(|_| unsupported(ty, "descriptor align"))?;
    let mut variants = Vec::with_capacity(def.variants.len());
    for (index, (variant, offsets)) in def
        .variants
        .iter()
        .zip(&desc.variant_field_offsets)
        .enumerate()
    {
        if matches!(desc.encoding, EnumTagEncoding::SingleInhabited { variant } if usize::try_from(variant).ok() != Some(index))
        {
            if !offsets.is_empty() {
                return Err(unsupported(
                    ty,
                    "inactive single-inhabited variant has physical offsets",
                ));
            }
            variants.push(Vec::new());
            continue;
        }
        if offsets.len() != variant.fields.len() {
            return Err(unsupported(
                ty,
                "descriptor offset count disagrees with fields",
            ));
        }
        let mut fields = Vec::with_capacity(offsets.len());
        for (fty, off) in variant.fields.iter().zip(offsets) {
            let offset = u32::try_from(*off).map_err(|_| unsupported(ty, "field offset"))?;
            let (fsize, falign) = size_align_in(module, fty, visiting)?;
            if offset.checked_add(fsize).is_none_or(|end| end > size)
                || !offset.is_multiple_of(falign)
                || falign > align
            {
                return Err(unsupported(
                    ty,
                    "descriptor field runs past the enum, or is misaligned",
                ));
            }
            fields.push(Part {
                offset,
                ty: fty.clone(),
            });
        }
        variants.push(fields);
    }
    let view = match &desc.encoding {
        EnumTagEncoding::Untagged => {
            if def.variants.len() != 1 {
                return Err(unsupported(ty, "untagged encoding with several variants"));
            }
            EnumView::Untagged { variant: 0 }
        }
        EnumTagEncoding::SingleInhabited { variant } => {
            if !trust_ir::ByValueStorageQuery::for_module(module).is_storage_free(ty) {
                return Err(unsupported(
                    ty,
                    "Storage or incomplete/ambiguous by-value schema has no value image",
                ));
            }
            let active = usize::try_from(*variant)
                .ok()
                .filter(|index| *index < def.variants.len())
                .ok_or_else(|| unsupported(ty, "single-inhabited selector is out of range"))?;
            let mut query = trust_ir::Inhabitedness::for_module(module);
            if def
                .variants
                .iter()
                .enumerate()
                .any(|(index, variant)| query.variant_is_uninhabited(variant) != (index != active))
            {
                return Err(unsupported(
                    ty,
                    "single-inhabited selection does not identify exactly one inhabited variant",
                ));
            }
            EnumView::Untagged { variant: active }
        }
        EnumTagEncoding::Direct { tag_offset } => {
            let offset = u32::try_from(*tag_offset).map_err(|_| unsupported(ty, "tag offset"))?;
            let (tsize, _) = size_align_in(module, &tag_ty, visiting)?;
            if offset.checked_add(tsize).is_none_or(|end| end > size) {
                return Err(unsupported(ty, "descriptor tag runs past the enum"));
            }
            EnumView::Direct { offset }
        }
        EnumTagEncoding::DirectWithUninhabited { .. } => {
            return Err(unsupported(
                ty,
                "direct-with-uninhabited storage profiles are not represented by the Wasm enum image",
            ));
        }
        EnumTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
            niche_start,
            niche_offset,
            niche_ty,
        } => {
            let count = def.variants.len();
            if *untagged_variant as usize >= count
                || niche_variants_start > niche_variants_end
                || *niche_variants_end as usize >= count
            {
                return Err(unsupported(ty, "incoherent niche encoding"));
            }
            let offset =
                u32::try_from(*niche_offset).map_err(|_| unsupported(ty, "niche offset"))?;
            let (bytes, _) = size_align_in(module, &niche_ty.ty(), visiting)?;
            if bytes > 8 {
                return Err(unsupported(
                    ty,
                    "niche lanes wider than 64 bits are not lowered",
                ));
            }
            if offset.checked_add(bytes).is_none_or(|end| end > size) {
                return Err(unsupported(ty, "niche lane runs past the enum"));
            }
            EnumView::Niche {
                untagged_variant: *untagged_variant as usize,
                start: *niche_variants_start,
                end: *niche_variants_end,
                niche_start: *niche_start,
                offset,
                bytes,
            }
        }
    };
    Ok(EnumImage {
        tag_ty,
        discriminants,
        variants,
        view,
        size,
        align,
    })
}

/// Where lane `field` of an aggregate lives.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Lane {
    /// Bytes at a fixed offset of the value.
    At(Part),
    /// Lane 0 of an enum: the discriminant, decoded from the tag image.
    EnumTag(Box<EnumImage>),
}

/// Resolve lane `field` of aggregate `ty` for an access at `access_ty`.
///
/// An enum lane `k >= 1` is field `k - 1` of the ACTIVE variant, and the
/// instruction does not name the variant. The variants whose field `k - 1`
/// has the accessed type are the only ones the access can be about (any other
/// active variant makes the access undefined behaviour); if they all place it
/// at one offset the lane is resolved, and if they disagree it is refused —
/// guessing between two offsets is a silent miscompile.
pub(crate) fn lane(
    module: &Module,
    ty: &Ty,
    field: u32,
    access_ty: &Ty,
) -> Result<Lane, WasmLowerError> {
    match ty {
        Ty::Struct(_) | Ty::Tuple(_) => {
            let fields = record_fields(module, ty)?;
            let part = fields
                .get(field as usize)
                .cloned()
                .ok_or_else(|| unsupported(ty, format!("field {field} is out of range")))?;
            Ok(Lane::At(part))
        }
        Ty::Array(_, _) => {
            let (elem, stride, len) = array_elem(module, ty)?;
            if u64::from(field) >= len {
                return Err(unsupported(ty, format!("element {field} is out of range")));
            }
            let offset = field
                .checked_mul(stride)
                .ok_or_else(|| unsupported(ty, "element offset overflows"))?;
            Ok(Lane::At(Part { offset, ty: elem }))
        }
        Ty::Enum(_) => {
            let image = enum_image(module, ty)?;
            if field == 0 {
                return Ok(Lane::EnumTag(Box::new(image)));
            }
            let index = field as usize - 1;
            // A zero-sized lane has no bytes: every offset names the same
            // (empty) value, so where it sits in each variant cannot make
            // the projection ambiguous.
            let zero_sized = size_align(module, access_ty).is_ok_and(|(size, _)| size == 0);
            let mut found: Option<Part> = None;
            for fields in &image.variants {
                let Some(part) = fields.get(index) else {
                    continue;
                };
                if &part.ty != access_ty {
                    continue;
                }
                match &found {
                    None => found = Some(part.clone()),
                    Some(prev) if prev.offset == part.offset || zero_sized => {}
                    Some(prev) => {
                        return Err(unsupported(
                            ty,
                            format!(
                                "lane {field} at {access_ty:?} is at offset {} in one variant and \
                                 {} in another; the instruction does not name the variant, so the \
                                 lane is ambiguous",
                                prev.offset, part.offset
                            ),
                        ));
                    }
                }
            }
            found.map(Lane::At).ok_or_else(|| {
                unsupported(ty, format!("no variant has lane {field} at {access_ty:?}"))
            })
        }
        other => Err(unsupported(other, "has no fields this lane can address")),
    }
}

/// A reference a constant image makes to something whose address is only
/// known to the module/linker: a function's table index or a data address.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ImageRef {
    /// The `funcref` table index of this function.
    Func(trust_ir::FuncId),
    /// The linear-memory address of this global, plus `addend` bytes.
    Global(trust_ir::value::GlobalId, i64),
    /// The address of a symbol resolved only by name (outside this module).
    Symbol(String, i64),
}

/// A constant's byte image plus the 4-byte words that must be patched with an
/// address once one is known.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ConstImage {
    pub bytes: Vec<u8>,
    pub refs: Vec<(u32, ImageRef)>,
}

fn refuse_const(ty: &Ty, c: &Constant, why: &str) -> WasmLowerError {
    WasmLowerError::UnsupportedConstantData(format!("constant {c:?} at {ty:?}: {why}"))
}

/// The little-endian two's-complement image of an integer constant at `bytes`
/// bytes.
fn int_bytes(value: u128, bytes: u32) -> Vec<u8> {
    value.to_le_bytes()[..bytes as usize].to_vec()
}

/// Build the byte image of `c` at type `ty`.
pub(crate) fn const_image(
    module: &Module,
    ty: &Ty,
    c: &Constant,
) -> Result<ConstImage, WasmLowerError> {
    let (size, _) = size_align(module, ty)?;
    // The image's bytes ARE the output (a data segment or data item), so
    // their count is inherent to it; the buffer is still reserved fallibly,
    // and a size this host cannot hold is refused by name rather than
    // aborting.
    let mut bytes = Vec::new();
    bytes.try_reserve_exact(size as usize).map_err(|error| {
        refuse_const(
            ty,
            c,
            &format!("its {size}-byte data image cannot be allocated: {error}"),
        )
    })?;
    bytes.resize(size as usize, 0);
    let mut image = ConstImage {
        bytes,
        refs: Vec::new(),
    };
    write_const(module, ty, c, 0, &mut image)?;
    Ok(image)
}

/// Whether `c` at `ty` is a trust-ir v50 splat whose element image is all
/// zero bytes with no address in it: its whole image is zero whatever its
/// length, so a closed module leaves it to zero-initialized memory (BSS)
/// without building it. Decided from ONE element.
pub(crate) fn is_zero_splat(
    module: &Module,
    ty: &Ty,
    c: &Constant,
) -> Result<bool, WasmLowerError> {
    let Constant::Splat { elem, len } = c else {
        return Ok(false);
    };
    let (elem_ty, _, declared) = array_elem(module, ty)?;
    if *len != declared {
        return Err(refuse_const(ty, c, "splat length disagrees with the array"));
    }
    let image = const_image(module, &elem_ty, elem)?;
    Ok(image.refs.is_empty() && image.bytes.iter().all(|byte| *byte == 0))
}

/// What `symaddr<symbol + addend>` refers to, in static data or a function
/// body. wasm symbols are typed: a function's address is its `funcref` table
/// index, a data symbol's a linear-memory address, so the kind is taken from
/// the module's own global or function (defined or declared) of that name. A
/// name the module neither defines nor declares is external DATA
/// ([`ImageRef::Symbol`]); a producer that stores an external function's
/// address declares that function, which is what makes it [`ImageRef::Func`].
/// A function's table index plus a byte offset addresses nothing, so a
/// nonzero addend on a function is refused with the reason returned.
pub(crate) fn resolve_symbol(
    module: &Module,
    symbol: &str,
    addend: i64,
) -> Result<ImageRef, &'static str> {
    if let Some(index) = module.globals.iter().position(|g| g.name == symbol) {
        return Ok(ImageRef::Global(
            trust_ir::value::GlobalId::new(index as u32),
            addend,
        ));
    }
    if let Some(f) = module.functions.iter().find(|f| f.name == symbol) {
        if addend != 0 {
            return Err(
                "a function's address is its wasm32 table index, which a byte offset does not \
                 address",
            );
        }
        return Ok(ImageRef::Func(f.id));
    }
    Ok(ImageRef::Symbol(symbol.to_string(), addend))
}

fn write_const(
    module: &Module,
    ty: &Ty,
    c: &Constant,
    at: u32,
    image: &mut ConstImage,
) -> Result<(), WasmLowerError> {
    let (size, _) = size_align(module, ty)?;
    let dst = at as usize..(at + size) as usize;
    match (ty, c) {
        (_, Constant::Uninit | Constant::PhantomData) => Ok(()),
        (Ty::Bool, Constant::Bool(b)) => {
            image.bytes[dst.start] = u8::from(*b);
            Ok(())
        }
        (Ty::F32, Constant::Float(f)) => {
            image.bytes[dst].copy_from_slice(&(*f as f32).to_le_bytes());
            Ok(())
        }
        (Ty::F64, Constant::Float(f)) => {
            image.bytes[dst].copy_from_slice(&f.to_le_bytes());
            Ok(())
        }
        (_, Constant::Int(n)) if int_like(ty) => {
            image.bytes[dst].copy_from_slice(&int_bytes(*n as u128, size));
            Ok(())
        }
        (_, Constant::U128(n)) if int_like(ty) => {
            image.bytes[dst].copy_from_slice(&int_bytes(*n, size));
            Ok(())
        }
        (_, Constant::Int(0)) if scalar_valtype(ty) == Some(ValType::I32) => Ok(()),
        (Ty::Func(_) | Ty::Ptr, Constant::FnDef(fid)) => {
            image.refs.push((at, ImageRef::Func(*fid)));
            Ok(())
        }
        (_, Constant::SymbolAddr { symbol, addend }) if scalar_valtype(ty).is_some() => {
            if size != 4 {
                return Err(refuse_const(
                    ty,
                    c,
                    "a symbol address is a 4-byte wasm32 word",
                ));
            }
            let target =
                resolve_symbol(module, symbol, *addend).map_err(|why| refuse_const(ty, c, why))?;
            image.refs.push((at, target));
            Ok(())
        }
        (_, Constant::Bytes { data, .. }) => {
            if data.len() > size as usize {
                return Err(refuse_const(ty, c, "more bytes than the type holds"));
            }
            image.bytes[dst.start..dst.start + data.len()].copy_from_slice(data);
            Ok(())
        }
        (Ty::Array(_, _), Constant::Array(elems) | Constant::Aggregate(elems)) => {
            let (elem, stride, len) = array_elem(module, ty)?;
            if elems.len() as u64 != len {
                return Err(refuse_const(
                    ty,
                    c,
                    "element count disagrees with the array",
                ));
            }
            for (i, e) in elems.iter().enumerate() {
                write_const(module, &elem, e, at + i as u32 * stride, image)?;
            }
            Ok(())
        }
        // trust-ir v50: `len` copies of one element (the one spelling of a
        // uniform array). The element is written ONCE into lane 0; a lane 0
        // that is all zero with no address needs nothing more (the image
        // starts zeroed), any other is repeated by a doubling copy, and each
        // address in it is recorded once per lane (every one is output).
        (Ty::Array(_, _), Constant::Splat { elem: e, len }) => {
            let (elem, stride, declared) = array_elem(module, ty)?;
            if *len != declared {
                return Err(refuse_const(ty, c, "splat length disagrees with the array"));
            }
            if *len == 0 {
                return Ok(());
            }
            let first_ref = image.refs.len();
            write_const(module, &elem, e, at, image)?;
            let lane_refs: Vec<(u32, ImageRef)> = image.refs[first_ref..].to_vec();
            let base = at as usize;
            let lane = stride as usize;
            let total = size as usize;
            if lane_refs.is_empty() && image.bytes[base..base + lane].iter().all(|b| *b == 0) {
                return Ok(());
            }
            let mut done = lane;
            while done < total {
                let chunk = done.min(total - done);
                image.bytes.copy_within(base..base + chunk, base + done);
                done += chunk;
            }
            for i in 1..*len {
                let shift = i as u32 * stride;
                for (offset, target) in &lane_refs {
                    image.refs.push((offset + shift, target.clone()));
                }
            }
            Ok(())
        }
        (Ty::Struct(_) | Ty::Tuple(_), Constant::Aggregate(elems)) => {
            let fields = record_fields(module, ty)?;
            if fields.len() != elems.len() {
                return Err(refuse_const(ty, c, "field count disagrees with the type"));
            }
            for (part, e) in fields.iter().zip(elems) {
                write_const(module, &part.ty, e, at + part.offset, image)?;
            }
            Ok(())
        }
        (Ty::FatPtr(_), Constant::Aggregate(elems)) if elems.len() == 2 => {
            let (data, meta) = fat_ptr_lanes(ty)?;
            write_const(module, &data.ty, &elems[0], at + data.offset, image)?;
            write_const(module, &meta.ty, &elems[1], at + meta.offset, image)
        }
        (Ty::Enum(_), Constant::Aggregate(elems)) if !elems.is_empty() => {
            let enum_image = enum_image(module, ty)?;
            let disc = match &elems[0] {
                Constant::Int(n) => *n,
                other => return Err(refuse_const(ty, other, "enum lane 0 is not an integer")),
            };
            let variant = enum_image
                .discriminants
                .iter()
                .position(|d| *d == disc)
                .ok_or_else(|| refuse_const(ty, c, "no variant has this discriminant"))?;
            let fields = &enum_image.variants[variant];
            if fields.len() + 1 != elems.len() {
                return Err(refuse_const(ty, c, "lane count disagrees with the variant"));
            }
            for (part, e) in fields.iter().zip(&elems[1..]) {
                write_const(module, &part.ty, e, at + part.offset, image)?;
            }
            write_tag(module, ty, &enum_image, variant, at, image)
        }
        _ => Err(refuse_const(
            ty,
            c,
            "no byte image for this constant/type pair",
        )),
    }
}

/// Integer-like: every trust-ir integer type (pointer-sized ones included).
fn int_like(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::U8
            | Ty::I16
            | Ty::U16
            | Ty::I32
            | Ty::U32
            | Ty::I64
            | Ty::U64
            | Ty::I128
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
    )
}

/// The bytes an enum's tag image holds for `variant`, as `(offset, width,
/// value)`, or `None` when this variant writes no tag bytes (untagged, or the
/// niche encoding's untagged variant).
pub(crate) fn tag_write(
    module: &Module,
    ty: &Ty,
    image: &EnumImage,
    variant: usize,
) -> Result<Option<(u32, u32, u128)>, WasmLowerError> {
    match &image.view {
        EnumView::Untagged { variant: active } => {
            if variant != *active {
                return Err(unsupported(
                    ty,
                    "tag-free image cannot encode an inactive variant",
                ));
            }
            Ok(None)
        }
        EnumView::Direct { offset } => {
            let (bytes, _) = size_align(module, &image.tag_ty)?;
            let disc = image.discriminants[variant];
            Ok(Some((*offset, bytes, disc as u128)))
        }
        EnumView::Niche {
            untagged_variant,
            start,
            niche_start,
            offset,
            bytes,
            ..
        } => {
            if variant == *untagged_variant {
                return Ok(None);
            }
            let relative = (variant as u128).wrapping_sub(u128::from(*start));
            let mask = if *bytes >= 16 {
                u128::MAX
            } else {
                (1u128 << (bytes * 8)) - 1
            };
            let _ = ty;
            Ok(Some((
                *offset,
                *bytes,
                niche_start.wrapping_add(relative) & mask,
            )))
        }
    }
}

fn write_tag(
    module: &Module,
    ty: &Ty,
    enum_image: &EnumImage,
    variant: usize,
    at: u32,
    image: &mut ConstImage,
) -> Result<(), WasmLowerError> {
    if let Some((offset, bytes, value)) = tag_write(module, ty, enum_image, variant)? {
        let start = (at + offset) as usize;
        image.bytes[start..start + bytes as usize].copy_from_slice(&int_bytes(value, bytes));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_storage_profiles_have_a_named_refusal_before_inactive_field_layout() {
        use trust_ir::{EnumDef, EnumVariant, FieldStorageLayout, UninhabitedVariantLayout};
        let mut m = module("");
        let mut def = EnumDef::new(
            EnumId::new(0),
            "Profiled",
            vec![
                EnumVariant {
                    name: "Dead".into(),
                    fields: vec![Ty::Never],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "Live".into(),
                    fields: vec![Ty::U32],
                    field_names: vec![],
                },
            ],
        )
        .with_repr(EnumTagRepr::U8);
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::DirectWithUninhabited {
                tag_offset: 0,
                variants: vec![UninhabitedVariantLayout {
                    variant: 0,
                    size: 1,
                    align: 1,
                    fields: vec![FieldStorageLayout { size: 0, align: 1 }],
                }],
            },
            size: 8,
            align: 4,
            variant_field_offsets: vec![vec![1], vec![4]],
        });
        m.enums.push(def);
        assert!(m.enum_layout_shape(EnumId::new(0)).is_ok());
        let before = m.clone();
        let error = enum_image(&m, &Ty::Enum(EnumId::new(0))).unwrap_err();
        assert!(matches!(error, WasmLowerError::UnsupportedType(detail)
            if detail.contains("DirectWithUninhabited")));
        assert_eq!(m, before);
        m.enums[0].variants[0].fields = vec![Ty::U32];
        let desc = m.enums[0].layout.as_mut().unwrap();
        desc.encoding = EnumTagEncoding::Direct { tag_offset: 0 };
        desc.variant_field_offsets[0] = vec![4];
        assert!(enum_image(&m, &Ty::Enum(EnumId::new(0))).is_ok());
    }

    #[test]
    fn single_inhabited_enum_images_preserve_payload_and_reject_inactive_values() {
        for active in 0..2 {
            let mut m = module("");
            let mut variants = vec![
                trust_ir::EnumVariant {
                    name: "Absent".into(),
                    fields: vec![Ty::Never],
                    field_names: vec![]
                };
                2
            ];
            variants[active] = trust_ir::EnumVariant {
                name: "Present".into(),
                fields: vec![Ty::U32],
                field_names: vec![],
            };
            let mut offsets = vec![vec![]; 2];
            offsets[active] = vec![0];
            let mut def = trust_ir::EnumDef::new(EnumId::new(0), "Selected", variants);
            def.discriminants = vec![Some(7), Some(23)];
            def.layout = Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::SingleInhabited {
                    variant: active as u32,
                },
                size: 4,
                align: 4,
                variant_field_offsets: offsets,
            });
            m.enums.push(def);
            let ty = Ty::Enum(EnumId::new(0));
            let image = enum_image(&m, &ty).unwrap();
            assert!(matches!(image.view, EnumView::Untagged { variant } if variant == active));
            let value = Constant::Aggregate(vec![
                Constant::Int([7, 23][active]),
                Constant::Int(0x12345678),
            ]);
            assert_eq!(
                const_image(&m, &ty, &value).unwrap().bytes,
                [0x78, 0x56, 0x34, 0x12]
            );
            let inactive = Constant::Aggregate(vec![Constant::Int([7, 23][1 - active])]);
            assert!(const_image(&m, &ty, &inactive).is_err());
            for hidden in [
                Ty::Storage(trust_ir::StorageLayout::new(8, 8)),
                Ty::Enum(EnumId::new(999)),
                ty.clone(),
            ] {
                m.enums[0].variants[1 - active].fields = vec![Ty::Never, hidden];
                assert!(
                    enum_image(&m, &ty).is_err(),
                    "Never cannot hide NoValue or incomplete schema"
                );
            }
            m.enums[0].variants[1 - active].fields = vec![Ty::U32];
            assert!(enum_image(&m, &ty).is_err());
        }
    }

    fn module(decls: &str) -> Module {
        trust_ir::parser::parse_module(&format!(
            "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n{decls}"
        ))
        .expect("parse")
    }

    fn offsets(parts: &[Part]) -> Vec<u32> {
        parts.iter().map(|p| p.offset).collect()
    }

    /// A struct that declares no layout takes the interpreter's C rule.
    #[test]
    fn an_undeclared_struct_takes_the_c_layout() {
        let m = module("struct @Q { : i32, : i64 } id=0\n");
        let ty = Ty::Struct(StructId::new(0));
        assert_eq!(size_align(&m, &ty).unwrap(), (16, 8));
        assert_eq!(offsets(&record_fields(&m, &ty).unwrap()), [0, 8]);
    }

    /// An undeclared tuple is laid out by the C rule at every depth: inside a
    /// declared struct, an enum payload and an array of arrays.
    #[test]
    fn an_undeclared_tuple_is_laid_out_at_every_depth() {
        let m = module(
            "type ty.0 = (u8, u32)\ntype ty.1 = [ty.0 x 2]\ntype ty.2 = [ty.1 x 3]\n\
             struct @S { : (u8, u32) @0, : u8 @8 } size=12 align=4 id=0\n\
             enum @E repr(u8) { A((u8, u32)) = 0, B = 1 } id=0\n",
        );
        let tuple = Ty::Tuple(vec![Ty::U8, Ty::U32]);
        assert_eq!(size_align(&m, &tuple).unwrap(), (8, 4));
        assert_eq!(
            size_align(&m, &Ty::Struct(StructId::new(0))).unwrap(),
            (12, 4)
        );
        let e = enum_image(&m, &Ty::Enum(EnumId::new(0))).unwrap();
        assert_eq!((e.size, e.align), (12, 4));
        assert_eq!(offsets(&e.variants[0]), [4]);
        let rows = Ty::Array(TyId::new(2), 1);
        assert_eq!(
            size_align(&m, &Ty::Array(TyId::new(1), 3)).unwrap(),
            (48, 4)
        );
        assert_eq!(size_align(&m, &rows).unwrap(), (48, 4));
    }

    /// A declared tuple layout is used verbatim once it passes the
    /// interpreter's validation; an incoherent one (wrong offset count, a
    /// misaligned or out-of-bounds element) is refused by name.
    #[test]
    fn a_declared_tuple_layout_is_validated_before_use() {
        let decls = "type ty.0 = (u8, u32)\ntuple_layout ty.0 size=8 align=4 offsets=[4, 0]\n";
        let m = module(decls);
        let tuple = Ty::Tuple(vec![Ty::U8, Ty::U32]);
        assert_eq!(size_align(&m, &tuple).unwrap(), (8, 4));
        assert_eq!(offsets(&record_fields(&m, &tuple).unwrap()), [4, 0]);
        for bad in [vec![4], vec![4, 0, 0], vec![0, 2], vec![8, 0], vec![0, 0]] {
            let mut m = module(decls);
            m.tuple_layouts[0].field_offsets = bad.clone();
            let err = size_align(&m, &tuple).unwrap_err().to_string();
            assert!(err.contains("declared tuple layout"), "{bad:?}: {err}");
        }
    }

    /// A closure with a declared frame (trust-ir v58) has a size in trust-ir's
    /// layout engine; the lane still refuses it by name, alone, inside a
    /// tuple and inside an array (OD-154).
    #[test]
    fn a_declared_closure_frame_is_refused_by_name_at_every_depth() {
        let mut m = module("");
        let func = m
            .add_func_type(trust_ir::FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        m.closure_types.push(trust_ir::ClosureTy {
            func,
            captures: vec![Ty::U64, Ty::U8],
        });
        m.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
            origin: None,
            closure: trust_ir::ClosureTyId::new(0),
            size: 16,
            align: 8,
            capture_offsets: vec![8, 0],
        });
        let closure = Ty::Closure(trust_ir::ClosureTyId::new(0));
        assert!(
            m.ty_layout_shape(&closure)
                .is_ok_and(|shape| shape.size_bytes() == Some(16)),
            "the premise: a declared frame gives the closure a size"
        );
        let elem = m
            .add_type(closure.clone())
            .expect("Module::add_type: test fixture");
        for ty in [
            closure.clone(),
            Ty::Tuple(vec![Ty::U32, closure]),
            Ty::Array(elem, 2),
        ] {
            let err = size_align(&m, &ty).unwrap_err().to_string();
            assert!(err.contains("[TCG-WASM-CLOSURE]"), "{ty:?}: {err}");
            let err = carrier_of(&m, &ty).unwrap_err().to_string();
            assert!(err.contains("[TCG-WASM-CLOSURE]"), "{ty:?}: {err}");
        }
    }

    /// An array too large for wasm32 is refused, never an arithmetic panic.
    #[test]
    fn an_oversized_array_of_tuples_is_refused() {
        let m = module("type ty.0 = (u8, u32)\n");
        let err = size_align(&m, &Ty::Array(TyId::new(0), 1 << 62)).unwrap_err();
        assert!(
            err.to_string().contains("larger than the wasm32 space"),
            "{err}"
        );
    }

    /// A declared struct layout is re-validated as the interpreter does: a
    /// field running past the declared size is refused.
    #[test]
    fn a_declared_struct_field_out_of_bounds_is_refused() {
        let m = module("struct @S { : i32 @0, : i64 @8 } size=12 align=4 id=0\n");
        let err = size_align(&m, &Ty::Struct(StructId::new(0))).unwrap_err();
        assert!(err.to_string().contains("out of bounds"), "{err}");
    }
}
