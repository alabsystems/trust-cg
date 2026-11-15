// trust-cg-lower/global_image.rs - canonical storage types for flat data images
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Give a flat byte/relocation data image its canonical TrustIR storage type.
//!
//! Producers that start from an object image rather than a source type (the
//! LLVM importer, a const-evaluated allocation) hold a global's contents as a
//! flat list: one `Constant::Int` per byte and one `Constant::SymbolAddr` per
//! pointer-width relocation. TrustIR types a global's initializer against the
//! global's declared type, so that list is not a constant of any scalar or
//! pointer type. This module spells it as one:
//!
//! - no relocation: `[u8; N]`, initialized by raw `Bytes`, or by
//!   `splat[ b; N ]` when every byte is equal (trust-ir v50,
//!   `SPEC_RATIFICATIONS` §3.1: the uniform array has exactly one spelling);
//! - with relocations: a `repr(packed)` struct whose fields are the maximal
//!   byte runs (each `[u8; n]`, spelled as above) and one `ptr` per
//!   relocation, at their exact image offsets.
//!
//! Packed fields describe byte offsets only. Allocation alignment belongs to
//! the global (`Global::align`), independently of the fields' alignment. No
//! pointer validity or lifetime is inferred from a relocation.

use trust_ir::{Constant, FieldDef, Module, StructDef, StructId, StructRepr, Ty, TyId};

/// One run of plain bytes in its one canonical spelling: two or more equal
/// bytes are the uniform array `Splat { elem: Int(b), len }`, which the
/// validator refuses as raw `Bytes { utf8: false }`; any other run stays raw
/// bytes. Constant size in the run's length either way.
pub fn byte_run(data: Vec<u8>) -> Constant {
    if Constant::is_uniform_bytes(&data, false) {
        Constant::splat(Constant::Int(i128::from(data[0])), data.len() as u64)
    } else {
        Constant::Bytes { data, utf8: false }
    }
}

/// A flat image's canonical storage type and initializer.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedImage {
    /// `[u8; size]`, or the packed allocation struct when the image relocates.
    pub ty: Ty,
    /// The initializer at `ty`.
    pub initializer: Constant,
    /// The image's byte size; relocations occupy `pointer_bytes` each.
    pub size: u64,
}

/// The byte size of the flat image `elements` (see [`type_flat_image`]), or
/// its refusal: for a producer that must check the size against its own
/// allocation before any table changes.
pub fn flat_image_size(
    name: &str,
    elements: &[Constant],
    pointer_bytes: u64,
) -> Result<u64, String> {
    measure(name, elements, pointer_bytes).map(|(size, _)| size)
}

/// `(byte size, relocation count)` of a flat image, refusing any element that
/// is neither a byte nor a named relocation.
fn measure(name: &str, elements: &[Constant], pointer_bytes: u64) -> Result<(u64, usize), String> {
    if pointer_bytes == 0 {
        return Err(format!(
            "global image `{name}` needs a nonzero pointer width"
        ));
    }
    let mut size = 0_u64;
    let mut pointers = 0_usize;
    for element in elements {
        let width = match element {
            Constant::Int(value) if u8::try_from(*value).is_ok() => 1,
            Constant::SymbolAddr { symbol, .. } if !symbol.is_empty() => {
                pointers += 1;
                pointer_bytes
            }
            _ => {
                return Err(format!(
                    "global image `{name}` has an unsupported byte/relocation element"
                ));
            }
        };
        size = size
            .checked_add(width)
            .ok_or_else(|| format!("global image `{name}` size overflows"))?;
    }
    Ok((size, pointers))
}

/// Type the flat image `elements` of global `name`.
///
/// `elements` holds one `Constant::Int` in `0..=255` per byte and one non-empty
/// `Constant::SymbolAddr` per relocation, which occupies `pointer_bytes`. Any
/// other element is refused by name: this never guesses a width.
///
/// May append `Ty::U8` to `module.types` and, when the image relocates, one
/// packed `StructDef` named `<name>.allocation`. Existing type and struct
/// indices are unchanged; every identity is checked before any table changes.
pub fn type_flat_image(
    module: &mut Module,
    name: &str,
    elements: Vec<Constant>,
    pointer_bytes: u64,
) -> Result<TypedImage, String> {
    let (size, pointers) = measure(name, &elements, pointer_bytes)?;

    // Reserve checked identities before changing any catalog.
    let byte_id = match module.types.iter().position(|ty| *ty == Ty::U8) {
        Some(index) => u32::try_from(index),
        None => u32::try_from(module.types.len()),
    }
    .map(TyId::new)
    .map_err(|_| format!("global image `{name}` exhausts type IDs"))?;
    let struct_id = if pointers > 0 {
        Some(
            match module.structs.iter().map(|def| def.id.index()).max() {
                None => 0,
                Some(id) => id
                    .checked_add(1)
                    .ok_or_else(|| format!("global image `{name}` exhausts struct IDs"))?,
            },
        )
    } else {
        None
    };

    // Adjacent bytes form one array field; relocations remain distinct pointer
    // fields even at unaligned offsets. No implicit inter-field or tail padding
    // may change the image.
    let mut fields = Vec::new();
    let mut values = Vec::new();
    let mut bytes = Vec::new();
    let mut offset = 0_u64;
    let flush = |bytes: &mut Vec<u8>,
                 fields: &mut Vec<FieldDef>,
                 values: &mut Vec<Constant>,
                 offset: &mut u64| {
        if !bytes.is_empty() {
            let len = bytes.len() as u64;
            fields.push(FieldDef {
                name: format!("part{}", fields.len()),
                ty: Ty::Array(byte_id, len),
                offset: Some(*offset),
            });
            values.push(byte_run(std::mem::take(bytes)));
            *offset += len;
        }
    };
    for element in elements {
        match element {
            Constant::Int(value) => bytes.push(u8::try_from(value).map_err(|_| {
                format!("global image `{name}` has a non-byte integer element {value}")
            })?),
            pointer @ Constant::SymbolAddr { .. } => {
                flush(&mut bytes, &mut fields, &mut values, &mut offset);
                fields.push(FieldDef {
                    name: format!("part{}", fields.len()),
                    ty: Ty::Ptr,
                    offset: Some(offset),
                });
                values.push(pointer);
                offset += pointer_bytes;
            }
            _ => {
                return Err(format!(
                    "global image `{name}` has an unsupported byte/relocation element"
                ));
            }
        }
    }
    if module.types.get(byte_id.as_usize()).is_none() {
        module.types.push(Ty::U8);
    }
    let Some(id) = struct_id else {
        return Ok(TypedImage {
            ty: Ty::Array(byte_id, size),
            initializer: byte_run(bytes),
            size,
        });
    };
    flush(&mut bytes, &mut fields, &mut values, &mut offset);
    let id = StructId::new(id);
    module.structs.push(StructDef {
        id,
        name: format!("{name}.allocation"),
        fields,
        size: Some(size),
        align: Some(1),
        repr: StructRepr::Packed(1),
        // Synthetic allocation image, not a nominal source definition.
        origin: None,
    });
    Ok(TypedImage {
        ty: Ty::Struct(id),
        initializer: Constant::Aggregate(values),
        size,
    })
}

/// The flat image a [`type_flat_image`] spelling stands for: its inverse,
/// one `Constant::Int` per byte and each relocation as its `SymbolAddr`.
///
/// `None` for an ill-formed one (another type, a byte run whose length
/// disagrees with its array, an inconsistent packed layout), or an output
/// whose allocation cannot be reserved. It also reads well-formed spellings
/// [`type_flat_image`] never emits, such as a uniform run as raw `Bytes` or a
/// packed relocation of another consistent width, as the bytes they render. A
/// reader of a producer's globals uses this to see the bytes it meant without
/// re-deriving the spelling rule. Pointer widths are inferred from the packed
/// offsets and must agree; this is not a target ABI or pointer-validity check.
pub fn flat_image_elements(
    module: &Module,
    ty: &Ty,
    initializer: &Constant,
) -> Option<Vec<Constant>> {
    let image = image_view(module, ty, initializer, None)?;
    let mut elements = Vec::new();
    elements.try_reserve_exact(image.len()).ok()?;
    match image {
        ImageView::Bytes(run) => run.append_to(&mut elements),
        ImageView::Packed { def, values, .. } => {
            for (field, value) in def.fields.iter().zip(values) {
                match (&field.ty, value) {
                    (Ty::Ptr, Constant::SymbolAddr { .. }) => elements.push(value.clone()),
                    (field_ty, run) => {
                        image_byte_run(module, field_ty, run)?.append_to(&mut elements);
                    }
                }
            }
        }
    }
    Some(elements)
}

/// Compare a typed flat image with byte/relocation elements without expanding
/// byte runs, cloning relocations, or allocating an intermediate image.
///
/// The same complete extent and packed-layout checks as [`flat_image_elements`]
/// run before comparison; a malformed spelling returns `None`, and a valid
/// spelling of different contents returns `Some(false)`. This is a producer
/// image reader, not a module validator, target ABI verifier, or native proof
/// gate. Every relocation extent must equal the caller's nonzero
/// `pointer_bytes`; matching flattened elements alone cannot establish that.
pub fn flat_image_matches(
    module: &Module,
    ty: &Ty,
    initializer: &Constant,
    elements: &[Constant],
    pointer_bytes: u64,
) -> Option<bool> {
    if pointer_bytes == 0 {
        return None;
    }
    let image = image_view(module, ty, initializer, Some(pointer_bytes))?;
    if image.len() != elements.len() {
        return Some(false);
    }
    match image {
        ImageView::Bytes(run) => Some(run.matches(elements)),
        ImageView::Packed { def, values, .. } => {
            let mut remaining = elements;
            for (field, value) in def.fields.iter().zip(values) {
                match (&field.ty, value) {
                    (Ty::Ptr, Constant::SymbolAddr { .. }) => {
                        if remaining.first()? != value {
                            return Some(false);
                        }
                        remaining = &remaining[1..];
                    }
                    (field_ty, run) => {
                        let run = image_byte_run(module, field_ty, run)?;
                        let (actual, rest) = remaining.split_at_checked(run.len())?;
                        if !run.matches(actual) {
                            return Some(false);
                        }
                        remaining = rest;
                    }
                }
            }
            Some(remaining.is_empty())
        }
    }
}

enum ImageView<'a> {
    Bytes(ImageByteRun<'a>),
    Packed {
        def: &'a StructDef,
        values: &'a [Constant],
        count: usize,
    },
}

impl ImageView<'_> {
    fn len(&self) -> usize {
        match self {
            Self::Bytes(run) => run.len(),
            Self::Packed { count, .. } => *count,
        }
    }
}

/// Fully validate the shape before either reader allocates or compares bytes.
fn image_view<'a>(
    module: &'a Module,
    ty: &Ty,
    initializer: &'a Constant,
    pointer_bytes: Option<u64>,
) -> Option<ImageView<'a>> {
    match ty {
        Ty::Array(..) => image_byte_run(module, ty, initializer).map(ImageView::Bytes),
        Ty::Struct(id) => {
            let def = module.structs.iter().find(|def| def.id == *id)?;
            let Constant::Aggregate(values) = initializer else {
                return None;
            };
            if def.repr != StructRepr::Packed(1)
                || def.align != Some(1)
                || values.len() != def.fields.len()
                || def.fields.first()?.offset != Some(0)
            {
                return None;
            }
            // Validate every extent and the complete output capacity before
            // allocating. In particular, never expand a malformed Splat to
            // discover afterward that its length disagrees with the array.
            let mut count = 0_usize;
            let mut pointer_width = None;
            for (index, (field, value)) in def.fields.iter().zip(values).enumerate() {
                let end = match def.fields.get(index + 1) {
                    Some(next) => next.offset?,
                    None => def.size?,
                };
                let width = end.checked_sub(field.offset?)?;
                let field_count = match (&field.ty, value) {
                    (Ty::Ptr, Constant::SymbolAddr { symbol, .. }) => {
                        if symbol.is_empty()
                            || width == 0
                            || pointer_bytes.is_some_and(|expected| expected != width)
                        {
                            return None;
                        }
                        if pointer_width.is_some_and(|previous| previous != width) {
                            return None;
                        }
                        pointer_width = Some(width);
                        1
                    }
                    (field_ty, run) => {
                        let run = image_byte_run(module, field_ty, run)?;
                        if width == 0 || u64::try_from(run.len()).ok()? != width {
                            return None;
                        }
                        run.len()
                    }
                };
                count = count.checked_add(field_count)?;
            }
            Some(ImageView::Packed { def, values, count })
        }
        _ => None,
    }
}

/// A validated run borrows raw bytes or stores only a repeat count. Neither
/// spelling needs an intermediate byte allocation before the final image.
enum ImageByteRun<'a> {
    Bytes(&'a [u8]),
    Repeat { byte: u8, len: usize },
}

impl ImageByteRun<'_> {
    fn len(&self) -> usize {
        match self {
            Self::Bytes(data) => data.len(),
            Self::Repeat { len, .. } => *len,
        }
    }

    fn append_to(self, elements: &mut Vec<Constant>) {
        match self {
            Self::Bytes(data) => {
                elements.extend(data.iter().map(|byte| Constant::Int(i128::from(*byte))));
            }
            Self::Repeat { byte, len } => {
                elements.extend(std::iter::repeat_n(Constant::Int(i128::from(byte)), len));
            }
        }
    }

    fn matches(self, elements: &[Constant]) -> bool {
        if self.len() != elements.len() {
            return false;
        }
        match self {
            Self::Bytes(data) => data.iter().zip(elements).all(|(byte, element)| {
                matches!(element, Constant::Int(value) if *value == i128::from(*byte))
            }),
            Self::Repeat { byte, .. } => elements.iter().all(|element| {
                matches!(element, Constant::Int(value) if *value == i128::from(byte))
            }),
        }
    }
}

fn image_byte_run<'a>(module: &Module, ty: &Ty, run: &'a Constant) -> Option<ImageByteRun<'a>> {
    let Ty::Array(element, declared_len) = ty else {
        return None;
    };
    if module.types.get(element.as_usize()) != Some(&Ty::U8) {
        return None;
    }
    let declared_len = usize::try_from(*declared_len).ok()?;
    match run {
        Constant::Bytes { data, utf8: false } if data.len() == declared_len => {
            Some(ImageByteRun::Bytes(data))
        }
        Constant::Splat { elem, len } if usize::try_from(*len).ok()? == declared_len => {
            let Constant::Int(byte) = **elem else {
                return None;
            };
            Some(ImageByteRun::Repeat {
                byte: u8::try_from(byte).ok()?,
                len: declared_len,
            })
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(data: &[u8]) -> Vec<Constant> {
        data.iter().map(|b| Constant::Int(i128::from(*b))).collect()
    }

    #[test]
    fn flat_image_elements_inverts_every_spelling() {
        let mut module = Module::new("image");
        let mut relocated = bytes(&[0xAA; 3]);
        relocated.push(Constant::symbol_addr("target"));
        relocated.extend(bytes(&[1, 2]));
        relocated.push(Constant::SymbolAddr {
            symbol: "other".into(),
            addend: 4,
        });
        for image in [
            bytes(&[0; 64]),
            bytes(&[1, 2, 2]),
            bytes(&[9]),
            Vec::new(),
            relocated,
        ] {
            let typed = type_flat_image(&mut module, "R", image.clone(), 8).expect("typed");
            assert_eq!(
                flat_image_elements(&module, &typed.ty, &typed.initializer),
                Some(image)
            );
        }
        // Not a flat-image spelling: a scalar global.
        assert_eq!(
            flat_image_elements(&module, &Ty::U64, &Constant::Int(7)),
            None
        );
    }

    #[test]
    fn byte_images_are_u8_arrays_in_their_one_spelling() {
        let mut module = Module::new("image");
        let zeros = type_flat_image(&mut module, "Z", bytes(&[0; 64]), 8).expect("a zero image");
        assert_eq!(zeros.ty, Ty::Array(TyId::new(0), 64));
        assert_eq!(zeros.initializer, Constant::splat(Constant::Int(0), 64));
        assert_eq!(zeros.size, 64);

        let mixed = type_flat_image(&mut module, "M", bytes(&[1, 2, 2]), 8).expect("mixed");
        assert_eq!(
            mixed.initializer,
            Constant::Bytes {
                data: vec![1, 2, 2],
                utf8: false
            }
        );
        let one = type_flat_image(&mut module, "O", bytes(&[9]), 8).expect("one byte");
        assert_eq!(
            one.initializer,
            Constant::Bytes {
                data: vec![9],
                utf8: false
            }
        );
        // `u8` is interned once and no struct was added for a byte image.
        assert_eq!(module.types, vec![Ty::U8]);
        assert!(module.structs.is_empty());
    }

    #[test]
    fn relocations_are_packed_pointer_fields_at_their_image_offsets() {
        let mut module = Module::new("image");
        let mut elements = bytes(&[0xAA; 3]);
        elements.push(Constant::symbol_addr("target"));
        elements.extend(bytes(&[1, 2]));
        let image = type_flat_image(&mut module, "P", elements, 8).expect("a relocated image");
        assert_eq!(image.size, 13);
        let Ty::Struct(id) = image.ty else {
            panic!("a relocated image is a struct, got {:?}", image.ty);
        };
        let def = &module.structs[0];
        assert_eq!(def.id, id);
        assert_eq!(def.name, "P.allocation");
        assert_eq!((def.size, def.align), (Some(13), Some(1)));
        assert_eq!(def.repr, StructRepr::Packed(1));
        let offsets: Vec<_> = def.fields.iter().map(|field| field.offset).collect();
        assert_eq!(offsets, vec![Some(0), Some(3), Some(11)]);
        assert_eq!(def.fields[1].ty, Ty::Ptr);
        let Constant::Aggregate(fields) = image.initializer else {
            panic!("a relocated image is a packed struct aggregate");
        };
        assert_eq!(fields[0], Constant::splat(Constant::Int(0xAA), 3));
        assert!(matches!(fields[1], Constant::SymbolAddr { .. }));
        assert_eq!(
            fields[2],
            Constant::Bytes {
                data: vec![1, 2],
                utf8: false
            }
        );
    }

    #[test]
    fn widths_it_cannot_know_are_refused_by_name() {
        let mut module = Module::new("image");
        for element in [Constant::Int(256), Constant::Int(-1), Constant::Float(1.0)] {
            let error = type_flat_image(&mut module, "W", vec![element], 8)
                .expect_err("not a byte or a relocation");
            assert!(error.contains("global image `W`"), "{error}");
        }
        let error = type_flat_image(&mut module, "E", vec![Constant::symbol_addr("")], 8)
            .expect_err("an unnamed relocation");
        assert!(
            error.contains("unsupported byte/relocation element"),
            "{error}"
        );
        let error =
            type_flat_image(&mut module, "N", bytes(&[1]), 0).expect_err("a zero pointer width");
        assert!(error.contains("nonzero pointer width"), "{error}");
        // A refusal changes no table.
        assert!(module.types.is_empty() && module.structs.is_empty());
    }

    #[test]
    fn reader_borrows_bytes_and_keeps_repeats_unexpanded() {
        let mut module = Module::new("image");
        module.types.push(Ty::U8);
        let ty = Ty::Array(TyId::new(0), 3);
        let raw = Constant::Bytes {
            data: vec![1, 2, 3],
            utf8: false,
        };
        let ImageByteRun::Bytes(borrowed) = image_byte_run(&module, &ty, &raw).expect("raw bytes")
        else {
            panic!("raw bytes must stay borrowed");
        };
        let Constant::Bytes { data, .. } = &raw else {
            unreachable!();
        };
        assert_eq!(borrowed.as_ptr(), data.as_ptr());
        assert!(matches!(
            image_byte_run(&module, &ty, &Constant::splat(Constant::Int(7), 3)),
            Some(ImageByteRun::Repeat { byte: 7, len: 3 })
        ));
        assert_eq!(
            flat_image_elements(&module, &ty, &raw),
            Some(bytes(&[1, 2, 3]))
        );
    }

    #[test]
    fn reader_refuses_bad_extents_before_expanding_or_reserving() {
        let mut module = Module::new("image");
        module.types.push(Ty::U8);
        let ty = Ty::Array(TyId::new(0), 3);
        for initializer in [
            Constant::splat(Constant::Int(1), u64::MAX),
            Constant::splat(Constant::Int(1), 2),
            Constant::splat(Constant::Int(256), 3),
            Constant::Bytes {
                data: vec![1, 2],
                utf8: false,
            },
            Constant::Bytes {
                data: vec![1, 2, 3],
                utf8: true,
            },
        ] {
            assert!(flat_image_elements(&module, &ty, &initializer).is_none());
        }
        // Matching extents can still exceed Vec's addressable capacity. The
        // reservation refusal is not a new semantic size cap or a panic.
        let huge = Ty::Array(TyId::new(0), u64::MAX);
        let repeat = Constant::splat(Constant::Int(0), u64::MAX);
        assert!(flat_image_elements(&module, &huge, &repeat).is_none());
    }

    #[test]
    fn reader_refuses_inconsistent_packed_offsets_sizes_and_pointer_widths() {
        let mut module = Module::new("image");
        let elements = vec![
            Constant::Int(1),
            Constant::symbol_addr("left"),
            Constant::Int(2),
            Constant::symbol_addr("right"),
        ];
        let typed = type_flat_image(&mut module, "R", elements.clone(), 8).expect("typed");
        assert_eq!(
            flat_image_elements(&module, &typed.ty, &typed.initializer),
            Some(elements)
        );
        for mutation in 0..6 {
            let mut changed = module.clone();
            let def = &mut changed.structs[0];
            match mutation {
                0 => def.fields[0].offset = Some(1),
                1 => def.fields[1].offset = Some(2),
                2 => def.fields[2].offset = Some(0),
                3 => def.size = Some(19),
                4 => def.size = None,
                5 => def.align = Some(8),
                _ => unreachable!(),
            }
            assert!(flat_image_elements(&changed, &typed.ty, &typed.initializer).is_none());
        }
        let mut unnamed = typed.initializer.clone();
        let Constant::Aggregate(values) = &mut unnamed else {
            unreachable!();
        };
        values[1] = Constant::symbol_addr("");
        assert!(flat_image_elements(&module, &typed.ty, &unnamed).is_none());
    }

    #[test]
    fn borrowed_comparison_matches_each_flat_spelling_and_ordered_element() {
        let mut module = Module::new("image");
        let mut relocated = bytes(&[0xAA; 3]);
        relocated.push(Constant::symbol_addr_with_addend("left", -7));
        relocated.extend(bytes(&[1, 2]));
        relocated.push(Constant::symbol_addr_with_addend("right", 4));
        for elements in [
            bytes(&[0; 64]),
            bytes(&[1, 2, 2]),
            bytes(&[9]),
            vec![],
            relocated,
        ] {
            let typed = type_flat_image(&mut module, "C", elements.clone(), 8).expect("typed");
            let compare = |actual: &[Constant]| {
                flat_image_matches(&module, &typed.ty, &typed.initializer, actual, 8)
            };
            assert_eq!(compare(&elements), Some(true));
            for (index, element) in elements.iter().enumerate() {
                let mut changed = elements.clone();
                changed[index] = match element {
                    Constant::Int(byte) => Constant::Int((byte + 1) % 256),
                    Constant::SymbolAddr { symbol, addend } => {
                        Constant::symbol_addr_with_addend(symbol.clone(), addend + 1)
                    }
                    _ => unreachable!(),
                };
                assert_eq!(compare(&changed), Some(false));
            }
            let mut longer = elements.clone();
            longer.push(Constant::Int(0));
            assert_eq!(compare(&longer), Some(false));
            if !elements.is_empty() {
                assert_eq!(compare(&elements[1..]), Some(false));
                for wrong in [Constant::Int(-1), Constant::Int(256), Constant::Float(1.0)] {
                    let mut changed = elements.clone();
                    changed[0] = wrong;
                    assert_eq!(compare(&changed), Some(false));
                }
            }
            if elements
                .iter()
                .any(|value| matches!(value, Constant::SymbolAddr { .. }))
            {
                let mut changed = elements.clone();
                let index = changed
                    .iter()
                    .position(|value| matches!(value, Constant::SymbolAddr { .. }))
                    .expect("relocation");
                changed[index] = Constant::symbol_addr_with_addend("another-symbol", -7);
                assert_eq!(compare(&changed), Some(false));
                changed = elements.clone();
                changed.swap(0, index);
                assert_eq!(compare(&changed), Some(false));
            }
        }
    }

    #[test]
    fn borrowed_comparison_validates_complete_layout_and_explicit_pointer_width() {
        let mut module = Module::new("image");
        let elements = vec![
            Constant::Int(1),
            Constant::symbol_addr("left"),
            Constant::Int(2),
            Constant::symbol_addr("right"),
        ];
        let typed = type_flat_image(&mut module, "C", elements.clone(), 8).expect("typed");
        assert_eq!(
            flat_image_matches(&module, &typed.ty, &typed.initializer, &elements, 8),
            Some(true)
        );
        assert_eq!(
            flat_image_matches(&module, &typed.ty, &typed.initializer, &elements, 4),
            None
        );
        assert_eq!(
            flat_image_matches(&module, &typed.ty, &typed.initializer, &elements, 0),
            None
        );
        let mut different = elements.clone();
        different[0] = Constant::Int(3);
        for mutation in 0..6 {
            let mut changed = module.clone();
            let def = &mut changed.structs[0];
            match mutation {
                0 => def.fields[0].offset = Some(1),
                1 => def.fields[1].offset = Some(2),
                2 => def.fields[2].offset = Some(0),
                3 => def.size = Some(19),
                4 => def.size = None,
                5 => def.align = Some(8),
                _ => unreachable!(),
            }
            // Even a mismatch in the first byte must not hide a malformed
            // later field behind Some(false).
            assert_eq!(
                flat_image_matches(&changed, &typed.ty, &typed.initializer, &different, 8),
                None
            );
        }
        let mut unnamed = typed.initializer.clone();
        let Constant::Aggregate(values) = &mut unnamed else {
            unreachable!()
        };
        values[3] = Constant::symbol_addr("");
        assert_eq!(
            flat_image_matches(&module, &typed.ty, &unnamed, &different, 8),
            None
        );

        // A well-formed image for another width has the same flattened
        // elements, but cannot be reused on this caller's eight-byte lane.
        let narrow = type_flat_image(&mut module, "W", elements.clone(), 4).expect("typed32");
        assert_eq!(
            flat_image_matches(&module, &narrow.ty, &narrow.initializer, &elements, 4),
            Some(true)
        );
        assert_eq!(
            flat_image_matches(&module, &narrow.ty, &narrow.initializer, &elements, 8),
            None
        );
    }

    #[test]
    fn borrowed_comparison_refuses_bad_byte_extents_without_expanding() {
        let mut module = Module::new("image");
        module.types.push(Ty::U8);
        let ty = Ty::Array(TyId::new(0), 3);
        let raw = Constant::Bytes {
            data: vec![1, 2, 3],
            utf8: false,
        };
        assert_eq!(
            flat_image_matches(&module, &Ty::Array(TyId::new(1), 3), &raw, &[], 8),
            None
        );
        let mut wrong_element = module.clone();
        wrong_element.types[0] = Ty::U16;
        assert_eq!(flat_image_matches(&wrong_element, &ty, &raw, &[], 8), None);
        for initializer in [
            Constant::splat(Constant::Int(1), u64::MAX),
            Constant::splat(Constant::Int(1), 2),
            Constant::splat(Constant::Int(256), 3),
            Constant::Bytes {
                data: vec![1, 2],
                utf8: false,
            },
            Constant::Bytes {
                data: vec![1, 2, 3],
                utf8: true,
            },
        ] {
            assert_eq!(flat_image_matches(&module, &ty, &initializer, &[], 8), None);
        }
        let huge_len = usize::MAX as u64;
        let huge = Ty::Array(TyId::new(0), huge_len);
        let repeat = Constant::splat(Constant::Int(0), huge_len);
        assert_eq!(
            flat_image_matches(&module, &huge, &repeat, &[Constant::Int(0)], 8),
            Some(false)
        );
        assert_eq!(
            flat_image_matches(&module, &Ty::U64, &Constant::Int(7), &[Constant::Int(7)], 8),
            None
        );
    }
}
