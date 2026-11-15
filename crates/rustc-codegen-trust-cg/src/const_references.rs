// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Replace the bridge's tagged immutable-reference constants with canonical
//! SymbolAddr constants. Reconcile all uses of an allocation before changing
//! its storage type, and require identical object-global output. This is a
//! frontend representation repair, not a pointer-validity or native theorem.

use std::collections::{BTreeMap, BTreeSet};
use trust_cg_codegen::{compiler::module_object_globals, global_stub::decode_global_addr_stub};
use trust_ir::{Constant, Endianness, Inst, Module, Ty};

pub(crate) fn canonicalize(module: &mut Module) -> usize {
    if !module.proof_obligations.is_empty()
        || !module.proof_certificates.is_empty()
        || module.target_info.as_ref().is_some_and(|target| {
            target.pointer_size != 8 || target.endianness != Endianness::Little
        })
    {
        return 0;
    }
    let mut wanted = BTreeMap::<usize, Ty>::new();
    let mut rejected = BTreeSet::new();
    let mut mentioned = BTreeSet::new();
    for global in &module.globals {
        if let Some(value) = &global.initializer {
            symbol_mentions(value, &mut mentioned);
        }
    }
    for function in &module.functions {
        if !function.proofs.is_empty() {
            return 0;
        }
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            if !node.proofs.is_empty() || node.proof_context.is_some() {
                return 0;
            }
            match &node.inst {
                Inst::Const { ty, value } => {
                    symbol_mentions(value, &mut mentioned);
                    let Constant::Int(value) = value else {
                        continue;
                    };
                    let Some((index, offset)) = decode_global_addr_stub(*value) else {
                        continue;
                    };
                    let index = index as usize;
                    match ty {
                        Ty::Ref(pointee) if offset == 0 => {
                            if wanted
                                .get(&index)
                                .is_some_and(|old| old != pointee.as_ref())
                            {
                                rejected.insert(index);
                            } else {
                                wanted.insert(index, pointee.as_ref().clone());
                            }
                        }
                        Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) => {
                            rejected.insert(index);
                        }
                        // Bare addresses and numeric constants do not assert a
                        // storage view. Their original spelling stays untouched.
                        _ => {}
                    }
                }
                Inst::Switch { cases, .. } => {
                    for case in cases {
                        symbol_mentions(&case.value, &mut mentioned);
                    }
                }
                _ => {}
            }
        }
    }
    if wanted.is_empty() {
        return 0;
    }
    let Ok(original_images) = module_object_globals(module) else {
        return 0;
    };
    let mut candidate = module.clone();
    let mut accepted = BTreeSet::new();
    for (index, pointee) in wanted {
        let Some(global) = module.globals.get(index) else {
            continue;
        };
        if rejected.contains(&index)
            || mentioned.contains(&global.name)
            || global.mutable
            || global.tls.is_some()
            || !global.linkage.is_module_local()
            || module
                .globals
                .iter()
                .filter(|other| other.name == global.name)
                .count()
                != 1
            || module
                .functions
                .iter()
                .any(|function| function.name == global.name)
        {
            continue;
        }
        let (Ty::Array(element, count), Some(image)) = (
            &global.ty,
            global.initializer.as_ref().and_then(ByteImage::of),
        ) else {
            continue;
        };
        if module.types.get(element.as_usize()) != Some(&Ty::U8) || image.len() != *count {
            continue;
        }
        let Some(initializer) = scalar_image(module, &pointee, &image) else {
            continue;
        };
        let Some(required_align) = required_alignment(module, &pointee) else {
            continue;
        };
        if global
            .align
            .is_none_or(|align| !align.is_power_of_two() || u64::from(align) < required_align)
        {
            continue;
        }
        candidate.globals[index].ty = pointee;
        candidate.globals[index].initializer = Some(initializer);
        accepted.insert(index);
    }
    if accepted.is_empty() {
        return 0;
    }
    // The emitter checks exact declared layouts and effective alignment. Equality
    // includes extent, every byte/relocation, binding, mutability and TLS/section
    // attributes. Failure publishes no changes, including to function constants.
    if module_object_globals(&candidate).ok().as_ref() != Some(&original_images) {
        return 0;
    }
    let names: Vec<_> = candidate
        .globals
        .iter()
        .map(|global| global.name.clone())
        .collect();
    let mut changed = 0;
    for function in &mut candidate.functions {
        for node in function.blocks.iter_mut().flat_map(|block| &mut block.body) {
            let Inst::Const {
                ty: Ty::Ref(_),
                value: Constant::Int(value),
            } = &node.inst
            else {
                continue;
            };
            let Some((index, offset)) = decode_global_addr_stub(*value) else {
                continue;
            };
            if offset == 0 && accepted.contains(&(index as usize)) {
                // Nested rather than a `&& let` chain: this crate is edition
                // 2021, where let chains do not parse. The pattern always
                // matches (the read-only match above admitted the node); the
                // `else` keeps it non-panicking without changing the outcome.
                let Inst::Const { value, .. } = &mut node.inst else {
                    continue;
                };
                *value = Constant::symbol_addr(&names[index as usize]);
                changed += 1;
            }
        }
    }
    *module = candidate;
    changed
}

fn symbol_mentions(value: &Constant, symbols: &mut BTreeSet<String>) {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        if let Constant::SymbolAddr { symbol, .. } = value {
            symbols.insert(symbol.clone());
        }
        pending.extend(value.children());
    }
}

fn scalar_width(ty: &Ty) -> Option<(usize, bool)> {
    Some(match ty {
        Ty::I8 => (1, true),
        Ty::I16 => (2, true),
        Ty::I32 => (4, true),
        Ty::I64 | Ty::Isize => (8, true),
        Ty::I128 => (16, true),
        Ty::U8 => (1, false),
        Ty::U16 => (2, false),
        Ty::U32 => (4, false),
        Ty::U64 | Ty::Usize => (8, false),
        Ty::U128 => (16, false),
        Ty::Bool => (1, false),
        Ty::Char | Ty::F32 => (4, false),
        Ty::F64 => (8, false),
        _ => return None,
    })
}

fn scalar(ty: &Ty, bytes: &[u8]) -> Option<Constant> {
    let (width, signed) = scalar_width(ty)?;
    if bytes.len() != width {
        return None;
    }
    match ty {
        Ty::Bool => {
            return match bytes[0] {
                0 => Some(Constant::Bool(false)),
                1 => Some(Constant::Bool(true)),
                _ => None,
            };
        }
        Ty::Char => {
            let value = u32::from_le_bytes(bytes.try_into().ok()?);
            char::from_u32(value)?;
            return Some(Constant::Int(i128::from(value)));
        }
        // A signaling NaN has no `Constant::Float` spelling: `None` (no constant).
        Ty::F32 => {
            return f32_bits_float_carrier(u32::from_le_bytes(bytes.try_into().ok()?))
                .map(Constant::Float);
        }
        Ty::F64 => return Some(Constant::Float(f64::from_le_bytes(bytes.try_into().ok()?))),
        _ => {}
    }
    let extend = if signed && bytes.last()? & 0x80 != 0 {
        0xff
    } else {
        0
    };
    let mut bits = [extend; 16];
    bits[..width].copy_from_slice(bytes);
    let value = u128::from_le_bytes(bits);
    Some(if *ty == Ty::U128 && value > i128::MAX as u128 {
        Constant::U128(value)
    } else {
        Constant::Int(i128::from_le_bytes(bits))
    })
}

/// A `[u8; N]` global's byte image, in either canonical spelling the bridge
/// emits (`global_image::type_image`): raw bytes, or — trust-ir v50 §3.1 —
/// `N` copies of one byte, which stays constant-size here too.
enum ByteImage<'a> {
    Bytes(&'a [u8]),
    Uniform { byte: u8, len: u64 },
}

impl<'a> ByteImage<'a> {
    fn of(initializer: &'a Constant) -> Option<Self> {
        match initializer {
            Constant::Bytes { data, .. } => Some(Self::Bytes(data)),
            Constant::Splat { elem, len } => match **elem {
                Constant::Int(byte) => Some(Self::Uniform {
                    byte: u8::try_from(byte).ok()?,
                    len: *len,
                }),
                _ => None,
            },
            _ => None,
        }
    }

    fn len(&self) -> u64 {
        match self {
            Self::Bytes(data) => data.len() as u64,
            Self::Uniform { len, .. } => *len,
        }
    }

    /// The bytes, materialized only for a view whose exact extent `size` the
    /// caller already knows (a scalar or a tuple of scalars: its size is its
    /// type's, never the array length).
    fn bytes_of_extent(&self, size: usize) -> Option<std::borrow::Cow<'a, [u8]>> {
        if self.len() != u64::try_from(size).ok()? {
            return None;
        }
        Some(match self {
            Self::Bytes(data) => std::borrow::Cow::Borrowed(*data),
            Self::Uniform { byte, .. } => std::borrow::Cow::Owned(vec![*byte; size]),
        })
    }
}

fn scalar_image(module: &Module, ty: &Ty, image: &ByteImage<'_>) -> Option<Constant> {
    match ty {
        Ty::Array(element, count) => {
            let element = module.types.get(element.as_usize())?;
            let (width, _) = scalar_width(element)?;
            if count.checked_mul(u64::try_from(width).ok()?)? != image.len() {
                return None;
            }
            // Each array is emitted in its ONE canonical spelling (trust-ir
            // v50 §3.1): a uniform image is one element repeated, never a list.
            match image {
                ByteImage::Uniform { byte, .. } => Some(Constant::splat(
                    scalar(element, &vec![*byte; width])?,
                    *count,
                )),
                ByteImage::Bytes(bytes) => Some(Constant::array(
                    bytes
                        .chunks_exact(width)
                        .map(|chunk| scalar(element, chunk))
                        .collect::<Option<Vec<_>>>()?,
                )),
            }
        }
        Ty::Tuple(fields) => {
            if let Some(declared) = module.tuple_layout_descriptor(ty).ok()? {
                let layout = module.ty_layout_shape(ty).ok()?;
                let bytes = image.bytes_of_extent(usize::try_from(layout.size_bytes()?).ok()?)?;
                let bytes: &[u8] = &bytes;
                return Some(Constant::Aggregate(
                    fields
                        .iter()
                        .zip(&declared.field_offsets)
                        .map(|(field, offset)| {
                            let offset = usize::try_from(*offset).ok()?;
                            let end = offset.checked_add(scalar_width(field)?.0)?;
                            scalar(field, bytes.get(offset..end)?)
                        })
                        .collect::<Option<Vec<_>>>()?,
                ));
            }
            // A scalar storage view: the fields back to back, so the image is
            // exactly their widths' sum.
            let size = fields.iter().try_fold(0_usize, |size, field| {
                size.checked_add(scalar_width(field)?.0)
            })?;
            let bytes = image.bytes_of_extent(size)?;
            let bytes: &[u8] = &bytes;
            let mut offset = 0_usize;
            let mut values = Vec::with_capacity(fields.len());
            for field in fields {
                let width = scalar_width(field)?.0;
                let end = offset.checked_add(width)?;
                values.push(scalar(field, bytes.get(offset..end)?)?);
                offset = end;
            }
            (offset == bytes.len()).then_some(Constant::Aggregate(values))
        }
        _ => scalar(ty, &image.bytes_of_extent(scalar_width(ty)?.0)?),
    }
}

fn required_alignment(module: &Module, ty: &Ty) -> Option<u64> {
    // Nested rather than a let-chain: this crate is edition 2021, where
    // `&& let` is a parse error. Do not let a clippy `collapsible_if`
    // suggestion re-collapse this.
    // EDITION 2021: this crate is `edition = "2021"`, where clippy's
    // suggested `&& let` chain is a PARSE ERROR. Taking that suggestion
    // once already made this crate unbuildable (4d50932d0, reverted by
    // 39d3cc125). The nesting stays until the crate moves to 2024.
    #[allow(clippy::collapsible_if)]
    if let Ty::Tuple(fields) = ty {
        if module.tuple_layout_descriptor(ty).ok()?.is_none() {
            // Without a descriptor this is only a scalar storage view. The
            // exact emitted-image comparison additionally checks padding and
            // extent; no Rust field order or formal tuple layout is inferred.
            return fields
                .iter()
                .map(|field| {
                    module
                        .ty_layout_shape(field)
                        .ok()?
                        .align_bits?
                        .checked_div(8)
                })
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .max()
                .or(Some(1));
        }
    }
    let bits = module.ty_layout_shape(ty).ok()?.align_bits?;
    (bits != 0 && bits.is_multiple_of(8)).then_some(bits / 8)
}

/// The trust-ir `Constant::Float` carrier for the f32 bit pattern `bits`, or
/// `None` when no carrier spells it.
///
/// trust-ir reads an F32 `Constant::Float(v)` as `(v as f32).to_bits()`, and
/// that narrowing quiets a signaling NaN, so a signaling NaN has no carrier. Every
/// other pattern round-trips exactly through the carrier built here: a non-NaN
/// widens exactly, and a quiet NaN is widened on its bits (sign, quiet bit and
/// payload shifted into the f64 payload's top), which the narrowing truncates
/// back. The host's own f32->f64 conversion is not used: it quiets a signaling
/// NaN.
pub(crate) fn f32_bits_float_carrier(bits: u32) -> Option<f64> {
    let value = f32::from_bits(bits);
    if !value.is_nan() {
        return Some(f64::from(value));
    }
    if bits & 0x0040_0000 == 0 {
        return None;
    }
    let sign = u64::from(bits >> 31) << 63;
    let payload = u64::from(bits & 0x007f_ffff) << 29;
    Some(f64::from_bits(sign | 0x7ff0_0000_0000_0000 | payload))
}
