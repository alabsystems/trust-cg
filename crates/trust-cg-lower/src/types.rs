// trust-cg-lower/types.rs - LIR type system
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Type system for Trust Codegen Low-level IR (input-level types).
//!
//! ## Why this is NOT a re-export of `trust_cg_ir::function::Type`
//!
//! This `Type` enum represents trust_ir/LIR input-level scalar types, while
//! `trust_cg_ir::function::Type` represents machine-level types used by the
//! backend after instruction selection. The key differences:
//!
//! | Aspect | `trust_cg_lower::Type` | `trust_cg_ir::Type` |
//! |--------|---------------------|------------------|
//! | Purpose | trust_ir input types | MachIR types |
//! | `Ptr` variant | No (pointers are I64 at LIR level) | Yes |
//! | `serde` derives | Yes (for trust_ir serialization) | No (zero-dep core) |
//! | `bits()` method | Yes | No |
//!
//! Once trust_ir integration matures, this enum will align with `trust_ir::Ty`.
//! See issue #37 for tracking type unification.

use serde::{Deserialize, Serialize};
use trust_cg_ir::function::EnumTagWidth;

/// Types in LIR (input-level, pre-instruction-selection).
///
/// This is intentionally separate from `trust_cg_ir::function::Type` — see
/// module-level docs for rationale. Includes aggregate types (Struct, Array)
/// for representing trust_ir aggregate operations before they are decomposed
/// into scalar loads/stores during instruction selection.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    /// 8-bit integer
    I8,
    /// 16-bit integer
    I16,
    /// 32-bit integer
    I32,
    /// 64-bit integer
    I64,
    /// 128-bit integer
    I128,
    /// 16-bit float
    F16,
    /// 32-bit float
    F32,
    /// 64-bit float
    F64,
    /// Boolean (1-bit)
    B1,
    /// 128-bit NEON/SIMD vector (e.g., float32x4, int32x4).
    ///
    /// Passed in V0-V7 (FPR128 class) per Apple AArch64 ABI.
    /// Size: 16 bytes, alignment: 16 bytes.
    V128,
    /// 64-bit NEON/SIMD vector (e.g., int8x8, uint64x1 — AArch64 D registers).
    ///
    /// Held in the Fpr64 register class (`D0`-`D31`); `ldr d`/`str d` for
    /// memory, `.8b`/`.4h`/`.2s`/`.1d` NEON arrangements for arithmetic.
    /// Size: 8 bytes, alignment: 8 bytes. This backs hashbrown's NEON group
    /// scan (`uint8x8_t` control-byte compares) lowered through trust-ir.
    V64,
    /// Aggregate structure type with C-like field layout.
    Struct(Vec<Type>),
    /// Fixed-size array type: element type and count.
    Array(Box<Type>, u32),
    /// Tagged-union enum: tag plus a max-sized, max-aligned payload.
    Enum {
        tag_width: EnumTagWidth,
        variants: Vec<Vec<Type>>,
    },
}

impl Type {
    /// Round `offset` up to the next multiple of `align`.
    fn align_to(offset: u32, align: u32) -> u32 {
        if align <= 1 {
            offset
        } else {
            let rem = offset % align;
            if rem == 0 {
                offset
            } else {
                offset.saturating_add(align - rem)
            }
        }
    }

    fn enum_payload_layout(variants: &[Vec<Type>]) -> (u32, u32) {
        let mut payload_bytes = 0;
        let mut payload_align = 1;
        for fields in variants {
            let payload_ty = Self::Struct(fields.clone());
            payload_bytes = payload_bytes.max(payload_ty.bytes());
            payload_align = payload_align.max(payload_ty.align());
        }
        (payload_bytes, payload_align)
    }

    /// The natural-C extent of `self` in checked `u64` — `None` when any
    /// intermediate exceeds what [`Type::bytes`]'s `u32` can hold.
    ///
    /// # Why this exists next to `bytes()` rather than somewhere else
    ///
    /// This IS `bytes()`, with the arithmetic checked instead of saturated, and
    /// keeping the two adjacent is the point: they are one layout algorithm
    /// with two failure conventions, and a caller that needs to know "can this
    /// type be described at all" must not have to re-derive natural C to ask.
    /// `crate::layout_refusal` carried a private copy of exactly this walk for
    /// precisely that reason; it now calls here, so the count of independent
    /// natural-C reimplementations in this workspace goes down by one.
    ///
    /// # What `None` means to a caller
    ///
    /// That no `Type` can describe the object, so every downstream number —
    /// the stack-slot size, the `__rust_alloc` request, the by-value ABI
    /// classification, every field offset past the overflow — is a guess.
    /// `translate_type_*` refuses to build such a type; `layout_refusal` scores
    /// it `NotComparable { Unrepresentable }` rather than certifying it.
    ///
    /// The bound is `u32::MAX` on every INTERMEDIATE, not just the total, since
    /// `bytes()` accumulates struct offsets in `u32` as it goes.
    pub fn checked_bytes(&self) -> Option<u64> {
        let bytes = match self {
            Type::Struct(fields) => Self::checked_struct_bytes(fields)?,
            Type::Array(elem, count) => elem.checked_bytes()?.checked_mul(u64::from(*count))?,
            Type::Enum {
                tag_width,
                variants,
            } => {
                let (payload_bytes, payload_align) = Self::checked_enum_payload(variants)?;
                let tag = u64::from(tag_width.bytes());
                let payload_offset = Self::checked_align_to(tag, payload_align)?;
                let total = payload_offset.checked_add(payload_bytes)?;
                Self::checked_align_to(total, tag.max(payload_align))?
            }
            // Scalars are constant-width; `bytes()` cannot overflow on them.
            scalar => u64::from(scalar.bytes()),
        };
        (bytes <= u64::from(u32::MAX)).then_some(bytes)
    }

    /// Checked mirror of [`Type::align`]; `None` only where computing it would
    /// overflow, which is reachable solely through an `Enum`'s payload-size
    /// computation.
    fn checked_align(&self) -> Option<u64> {
        match self {
            Type::Struct(fields) => Self::checked_struct_align(fields),
            Type::Array(elem, _) => elem.checked_align(),
            Type::Enum {
                tag_width,
                variants,
            } => {
                let (_, payload_align) = Self::checked_enum_payload(variants)?;
                Some(u64::from(tag_width.bytes()).max(payload_align))
            }
            scalar => Some(u64::from(scalar.align())),
        }
    }

    /// `offset` rounded up to a multiple of `align`, or `None` on overflow.
    fn checked_align_to(offset: u64, align: u64) -> Option<u64> {
        if align <= 1 {
            return Some(offset);
        }
        let rem = offset % align;
        if rem == 0 {
            Some(offset)
        } else {
            offset.checked_add(align - rem)
        }
    }

    fn checked_struct_bytes(fields: &[Type]) -> Option<u64> {
        let mut offset: u64 = 0;
        let mut max_align: u64 = 1;
        for field in fields {
            let a = field.checked_align()?;
            max_align = max_align.max(a);
            offset = Self::checked_align_to(offset, a)?;
            offset = offset.checked_add(field.checked_bytes()?)?;
            // A FAST PATH, NOT A GUARD — recorded as such rather than left
            // looking load-bearing. `offset` only ever grows, so the running
            // total can never exceed the final one, and [`Type::checked_bytes`]
            // bounds that final total itself. Removing this line leaves all
            // 1,699 lib tests green, which is the honest characterisation:
            // it makes the walk give up early on a hopeless struct, and it
            // cannot change any answer.
            if offset > u64::from(u32::MAX) {
                return None;
            }
        }
        Self::checked_align_to(offset, max_align)
    }

    fn checked_struct_align(fields: &[Type]) -> Option<u64> {
        let mut max_align: u64 = 1;
        for field in fields {
            max_align = max_align.max(field.checked_align()?);
        }
        Some(max_align)
    }

    /// Checked mirror of [`Type::enum_payload_layout`] — `(payload_bytes,
    /// payload_align)` over every variant.
    fn checked_enum_payload(variants: &[Vec<Type>]) -> Option<(u64, u64)> {
        let mut payload_bytes: u64 = 0;
        let mut payload_align: u64 = 1;
        for fields in variants {
            payload_bytes = payload_bytes.max(Self::checked_struct_bytes(fields)?);
            payload_align = payload_align.max(Self::checked_struct_align(fields)?);
        }
        Some((payload_bytes, payload_align))
    }

    /// Returns the size in bytes.
    ///
    /// For structs, uses C-like layout with alignment padding.
    /// For arrays, returns element_size * count.
    ///
    /// # Every accumulation here SATURATES, and that is load-bearing
    ///
    /// This is a `u32`, so a type whose natural extent reaches 2^32 cannot be
    /// represented. Until this arithmetic was made saturating it WRAPPED in a
    /// release build and PANICKED in a debug one, so the shipping profile and
    /// the test profile disagreed about the same type.
    ///
    /// The wrap was not merely a wrong number, it was a memory-safety hazard.
    /// (c) MEASURED, `Nat = #[repr(C)] { a: u8, b: u64 }` (16 bytes) and
    /// `[Nat; 268435456]` — a type stock `rustc 1.97.0` accepts, `size_of` =
    /// 4294967296: [`crate::declared_layout::emitted_value_extent`] multiplies
    /// in `u64` and answered 4294967296 while this function answered **0**, so
    /// the emitted `Memmove` length exceeded the carrier that sizes the stack
    /// slot by 4 GiB. The whole decision to leave `Alloca`/`HeapAlloc` on the
    /// natural extent (defect B) rests on `emitted <= natural`; a wrap here
    /// inverts it and turns a benign over-allocation into an out-of-bounds
    /// write.
    ///
    /// Saturation makes this function monotone and profile-independent, which
    /// is what the invariant needs. It is NOT the primary defence: a type this
    /// large is refused outright at construction, in `translate_type_*`'s
    /// `Ty::Array` arm, so no such `Type` reaches the byte path. This arm keeps
    /// any directly-constructed `Type` (tests, other crates — `Type` is `pub`)
    /// from observing a wrapped extent.
    pub fn bytes(&self) -> u32 {
        match self {
            Type::B1 | Type::I8 => 1,
            Type::I16 | Type::F16 => 2,
            Type::I32 | Type::F32 => 4,
            Type::I64 | Type::F64 | Type::V64 => 8,
            Type::I128 | Type::V128 => 16,
            Type::Struct(fields) => {
                let mut offset: u32 = 0;
                let mut max_align: u32 = 1;
                for field in fields {
                    let a = field.align();
                    max_align = max_align.max(a);
                    offset = Self::align_to(offset, a);
                    offset = offset.saturating_add(field.bytes());
                }
                Self::align_to(offset, max_align)
            }
            Type::Array(elem, count) => elem.bytes().saturating_mul(*count),
            Type::Enum {
                tag_width,
                variants,
            } => {
                let (payload_bytes, payload_align) = Self::enum_payload_layout(variants);
                let payload_offset = Self::align_to(tag_width.bytes(), payload_align);
                Self::align_to(payload_offset.saturating_add(payload_bytes), self.align())
            }
        }
    }

    /// Alias for `bytes()`.
    pub fn size_of(&self) -> u32 {
        self.bytes()
    }

    /// Natural alignment in bytes.
    ///
    /// The `_` arm's `min(8)` cap is the natural-C rule for a scalar that fits
    /// a general-purpose register. A 128-bit scalar does NOT, and rustc gives
    /// it 16 — (c) MEASURED with stock `rustc 1.97.0`, `align_of::<u128>() ==
    /// 16`, `#[repr(C)] { a: u8, b: u128 }` is size 32 align 16 with `b@16`,
    /// and `align_of::<[u128; 2]>() == 16`. The cap used to swallow `I128` and
    /// report 8, which under-aligned every `u128` slot, mis-sized every struct
    /// containing one, and put its fields at the wrong offsets.
    ///
    /// # Why 16 is a constant and not a `TargetSpec` field
    ///
    /// `i128` alignment IS target-dependent in general, so this was checked
    /// rather than assumed. (c) MEASURED this run from `rustc -Z
    /// unstable-options --print target-spec-json`: the data-layout carries
    /// `i128:128` for `x86_64-{apple-darwin, unknown-linux-gnu, unknown-linux-
    /// musl, pc-windows-msvc}`, `aarch64-{apple-darwin, unknown-linux-gnu}` and
    /// `riscv64gc-{unknown-linux-gnu, unknown-none-elf}` — i.e. for every
    /// triple reachable from `trust_cg_codegen::target::Target`, whose whole
    /// domain is `{X86_64, Aarch64, Riscv64}`. It is ABSENT (and so 8) only for
    /// `armv7-unknown-linux-gnueabihf`, `s390x-unknown-linux-gnu` and
    /// `mips-unknown-linux-gnu`, none of which trust-cg emits for.
    ///
    /// So 16 is correct for the entire current target set. Adding a 32-bit ARM,
    /// MIPS or s390x backend is what makes this a `TargetSpec` field — and that
    /// backend, not this constant, is where the plumbing belongs.
    pub fn align(&self) -> u32 {
        match self {
            // V128 has 16-byte alignment (NEON requirement).
            Type::V128 => 16,
            // A 128-bit scalar is 16-byte aligned; see the note above for why
            // this is not target-dependent within trust-cg's target set.
            Type::I128 => 16,
            // V64 (D-register vector) is 8-byte aligned.
            Type::V64 => 8,
            Type::Struct(fields) => fields.iter().map(|f| f.align()).max().unwrap_or(1),
            Type::Array(elem, _) => elem.align(),
            Type::Enum {
                tag_width,
                variants,
            } => {
                let (_, payload_align) = Self::enum_payload_layout(variants);
                tag_width.bytes().max(payload_align)
            }
            _ => self.bytes().min(8),
        }
    }

    /// Alias for `align()`.
    pub fn align_of(&self) -> u32 {
        self.align()
    }

    /// Byte offset of a struct field using C-like layout rules.
    ///
    /// Returns `None` if not a struct type or index is out of range.
    pub fn offset_of(&self, field_index: usize) -> Option<u32> {
        let Self::Struct(fields) = self else {
            return None;
        };
        if field_index >= fields.len() {
            return None;
        }
        let mut offset: u32 = 0;
        for (idx, field) in fields.iter().enumerate() {
            offset = Self::align_to(offset, field.align());
            if idx == field_index {
                return Some(offset);
            }
            offset += field.bytes();
        }
        None
    }

    /// Byte offset where the enum payload begins for the tagged-union layout.
    pub fn enum_payload_offset(&self) -> Option<u32> {
        let Self::Enum {
            tag_width,
            variants,
        } = self
        else {
            return None;
        };
        let (_, payload_align) = Self::enum_payload_layout(variants);
        Some(Self::align_to(tag_width.bytes(), payload_align))
    }

    /// LIR type used to store the enum tag.
    pub fn enum_tag_type(&self) -> Option<Type> {
        let Self::Enum { tag_width, .. } = self else {
            return None;
        };
        Some(match tag_width {
            EnumTagWidth::U8 => Type::I8,
            EnumTagWidth::U16 => Type::I16,
            EnumTagWidth::U32 => Type::I32,
            EnumTagWidth::U64 => Type::I64,
        })
    }

    /// Returns the semantic width in bits.
    ///
    /// Note: B1 returns 1 (semantic bit-width), not 8 (storage size).
    /// Use `storage_bits()` or `bytes()` for the storage/register size.
    /// Aggregate types return their total storage size in bits.
    pub fn bits(&self) -> u32 {
        match self {
            Type::B1 => 1,
            _ => self.bytes() * 8,
        }
    }

    /// Returns the storage width in bits (register/memory size).
    ///
    /// Unlike `bits()`, this always returns the physical storage size.
    /// B1 returns 8 (stored in a byte), not 1 (its semantic width).
    /// This is equivalent to `self.bytes() * 8`.
    pub fn storage_bits(&self) -> u32 {
        self.bytes() * 8
    }

    /// Returns true if this is an aggregate type.
    pub fn is_aggregate(&self) -> bool {
        matches!(
            self,
            Self::Struct(_) | Self::Array(_, _) | Self::Enum { .. }
        )
    }

    /// Returns true if this is a SIMD vector type.
    pub fn is_vector(&self) -> bool {
        matches!(self, Self::V128)
    }

    /// Returns true if this is a scalar (non-aggregate) type.
    pub fn is_scalar(&self) -> bool {
        !self.is_aggregate()
    }
}

// ---------------------------------------------------------------------------
// From<trust_cg_lower::Type> for trust_cg_ir::function::Type
// ---------------------------------------------------------------------------
//
// Centralizes the type conversion that was previously scattered in
// pipeline.rs (convert_lower_type_to_ir). The trust-cg-ir Type has a `Ptr`
// variant that trust-cg-lower's Type lacks; this conversion never produces Ptr.
//
// Impl lives here (trust-cg-lower) because the orphan rule requires the `From`
// impl to be in the crate that owns the source type.

impl From<&Type> for trust_cg_ir::function::Type {
    fn from(t: &Type) -> Self {
        match t {
            Type::I8 => trust_cg_ir::function::Type::I8,
            Type::I16 => trust_cg_ir::function::Type::I16,
            Type::I32 => trust_cg_ir::function::Type::I32,
            Type::I64 => trust_cg_ir::function::Type::I64,
            Type::I128 => trust_cg_ir::function::Type::I128,
            Type::F16 => trust_cg_ir::function::Type::F16,
            Type::F32 => trust_cg_ir::function::Type::F32,
            Type::F64 => trust_cg_ir::function::Type::F64,
            Type::B1 => trust_cg_ir::function::Type::B1,
            Type::V128 => trust_cg_ir::function::Type::V128,
            // V64 maps to I64 as a placeholder (same size, 8 bytes).
            // TODO: Add a proper V64 variant to trust_cg_ir::function::Type.
            Type::V64 => trust_cg_ir::function::Type::I64,
            Type::Struct(fields) => {
                let ir_fields: Vec<trust_cg_ir::function::Type> =
                    fields.iter().map(|f| f.into()).collect();
                trust_cg_ir::function::Type::Struct(ir_fields)
            }
            Type::Array(elem, count) => {
                let ir_elem: trust_cg_ir::function::Type = elem.as_ref().into();
                trust_cg_ir::function::Type::Array(Box::new(ir_elem), *count)
            }
            Type::Enum {
                tag_width,
                variants,
            } => {
                let ir_variants: Vec<Vec<trust_cg_ir::function::Type>> = variants
                    .iter()
                    .map(|fields| fields.iter().map(|f| f.into()).collect())
                    .collect();
                trust_cg_ir::function::Type::Enum {
                    tag_width: *tag_width,
                    variants: ir_variants,
                }
            }
        }
    }
}

impl From<Type> for trust_cg_ir::function::Type {
    fn from(t: Type) -> Self {
        (&t).into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn b1_bits_returns_1() {
        // Issue #39: B1.bits() must return 1 (semantic bit-width), not 8.
        assert_eq!(Type::B1.bits(), 1);
    }

    #[test]
    fn b1_storage_bits_returns_8() {
        // B1 is stored in a byte (8 bits) even though its semantic width is 1.
        assert_eq!(Type::B1.storage_bits(), 8);
    }

    #[test]
    fn b1_bytes_returns_1() {
        assert_eq!(Type::B1.bytes(), 1);
    }

    #[test]
    fn integer_bits() {
        assert_eq!(Type::I8.bits(), 8);
        assert_eq!(Type::I16.bits(), 16);
        assert_eq!(Type::I32.bits(), 32);
        assert_eq!(Type::I64.bits(), 64);
        assert_eq!(Type::I128.bits(), 128);
    }

    #[test]
    fn integer_storage_bits_equals_bits() {
        // For integer types, storage_bits == bits.
        for ty in &[Type::I8, Type::I16, Type::I32, Type::I64, Type::I128] {
            assert_eq!(ty.bits(), ty.storage_bits(), "mismatch for {:?}", ty);
        }
    }

    #[test]
    fn float_bits() {
        assert_eq!(Type::F16.bits(), 16);
        assert_eq!(Type::F32.bits(), 32);
        assert_eq!(Type::F64.bits(), 64);
    }

    #[test]
    fn float_storage_bits_equals_bits() {
        assert_eq!(Type::F16.bits(), Type::F16.storage_bits());
        assert_eq!(Type::F32.bits(), Type::F32.storage_bits());
        assert_eq!(Type::F64.bits(), Type::F64.storage_bits());
    }

    #[test]
    fn v128_is_a_distinct_vector_carrier() {
        assert!(Type::V128.is_vector());
        assert!(!Type::I128.is_vector());
        assert!(Type::V128.is_scalar());
        assert_eq!(Type::V128.bytes(), 16);
        assert_eq!(Type::V128.align(), 16);
    }

    #[test]
    fn struct_bytes_with_padding() {
        // struct { I8, I32 } -> 1 byte + 3 padding + 4 bytes = 8 bytes
        let s = Type::Struct(vec![Type::I8, Type::I32]);
        assert_eq!(s.bytes(), 8);
        assert_eq!(s.bits(), 64);
        assert_eq!(s.storage_bits(), 64);
    }

    #[test]
    fn array_bytes() {
        let a = Type::Array(Box::new(Type::I32), 4);
        assert_eq!(a.bytes(), 16);
        assert_eq!(a.bits(), 128);
    }

    /// A 128-bit scalar is 16-byte aligned, and every derived layout follows.
    ///
    /// THE ORACLE IS STOCK RUSTC — `rustc 1.97.0 (2d8144b78 2026-07-07)`, via
    /// `size_of` / `align_of` / `offset_of!`, cross-checked with a `const`
    /// assertion compiled for aarch64-apple-darwin, x86_64-apple-darwin,
    /// x86_64-unknown-linux-musl, x86_64-pc-windows-msvc and
    /// wasm32-unknown-unknown (with a negative control that DOES fail, so the
    /// probe is not vacuous):
    ///
    /// ```text
    /// u128 / i128                    size 16  align 16
    /// #[repr(C)] { a: u8, b: u128 }  size 32  align 16   a@0  b@16
    /// [u128; 2]                      size 32  align 16
    /// ```
    ///
    /// `Type::align`'s `_ => self.bytes().min(8)` arm used to swallow `I128`
    /// and answer 8, which made all four of these wrong: a `u128` stack slot
    /// was under-aligned (AAPCS64 requires 16, and `LDXP`/`STXP` fault below
    /// it), a struct containing one was mis-SIZED, and its fields were placed
    /// at the wrong OFFSETS.
    #[test]
    fn i128_is_sixteen_byte_aligned_like_rustc() {
        assert_eq!(Type::I128.bytes(), 16);
        assert_eq!(Type::I128.align(), 16, "rustc: align_of::<u128>() == 16");

        // `#[repr(C)] { a: u8, b: u128 }` — was 24 / 8 with `b@8`.
        let s = Type::Struct(vec![Type::I8, Type::I128]);
        assert_eq!(
            (s.bytes(), s.align(), s.offset_of(1)),
            (32, 16, Some(16)),
            "rustc: size 32, align 16, b@16"
        );

        // `[u128; 2]` — an array takes its element's alignment.
        let a = Type::Array(Box::new(Type::I128), 2);
        assert_eq!((a.bytes(), a.align()), (32, 16), "rustc: size 32, align 16");

        // Every OTHER scalar keeps the `min(8)` cap — the fix is one arm wide.
        for (ty, want) in [
            (Type::I8, 1),
            (Type::I16, 2),
            (Type::I32, 4),
            (Type::I64, 8),
            (Type::F64, 8),
        ] {
            assert_eq!(ty.align(), want, "{ty:?} must keep the min(8) cap");
        }
    }

    #[test]
    fn b1_differs_from_storage() {
        // The key distinction: bits() != storage_bits() only for B1.
        assert_ne!(Type::B1.bits(), Type::B1.storage_bits());
    }

    // ---- From<Type> for trust_cg_ir::function::Type tests ----

    #[test]
    fn from_scalar_types() {
        use trust_cg_ir::function::Type as IrType;
        assert_eq!(IrType::from(Type::I8), IrType::I8);
        assert_eq!(IrType::from(Type::I16), IrType::I16);
        assert_eq!(IrType::from(Type::I32), IrType::I32);
        assert_eq!(IrType::from(Type::I64), IrType::I64);
        assert_eq!(IrType::from(Type::I128), IrType::I128);
        assert_eq!(IrType::from(Type::F16), IrType::F16);
        assert_eq!(IrType::from(Type::F32), IrType::F32);
        assert_eq!(IrType::from(Type::F64), IrType::F64);
        assert_eq!(IrType::from(Type::B1), IrType::B1);
        assert_eq!(IrType::from(Type::V128), IrType::V128);
    }

    #[test]
    fn from_struct_type() {
        use trust_cg_ir::function::Type as IrType;
        let lower_struct = Type::Struct(vec![Type::I8, Type::V128]);
        let ir_struct = IrType::from(lower_struct);
        assert_eq!(ir_struct, IrType::Struct(vec![IrType::I8, IrType::V128]));
        assert_eq!(ir_struct.offset_of(1), Some(16));
    }

    #[test]
    fn from_array_type() {
        use trust_cg_ir::function::Type as IrType;
        let lower_array = Type::Array(Box::new(Type::V128), 3);
        let ir_array = IrType::from(lower_array);
        assert_eq!(ir_array, IrType::Array(Box::new(IrType::V128), 3));
        assert_eq!(ir_array.align(), 16);
        assert_eq!(ir_array.bytes(), 48);
    }

    #[test]
    fn from_ref_type() {
        use trust_cg_ir::function::Type as IrType;
        let lower_ty = Type::I64;
        let ir_ty: IrType = (&lower_ty).into();
        assert_eq!(ir_ty, IrType::I64);
    }

    /// A NATURAL EXTENT AT OR ABOVE 2^32 SATURATES; IT DOES NOT WRAP.
    ///
    /// `bytes()` is a `u32`, so it cannot describe an object this large. What
    /// it must not do is answer a SMALL number for a huge one: everything that
    /// reserves storage sizes it from this figure, while
    /// [`crate::declared_layout::emitted_value_extent`] computes the
    /// authoritative extent in `u64`. A wrap makes the copy longer than the
    /// slot — an out-of-bounds write.
    ///
    /// (c) MEASURED before this was saturating: `[#[repr(C)]{u8,u64};
    /// 268435456]` (stock `rustc 1.97.0` accepts it, `size_of` = 4294967296)
    /// reported **0** in a release build and PANICKED in a debug one. Both
    /// answers are now `u32::MAX`, and the type is refused at construction.
    #[test]
    fn a_natural_extent_beyond_the_u32_carrier_saturates_rather_than_wrapping() {
        // 16 x 2^28 == 2^32 exactly — the first product that does not fit.
        let elem = Type::Struct(vec![Type::I8, Type::I64]);
        assert_eq!(elem.bytes(), 16);
        let huge = Type::Array(Box::new(elem), 268_435_456);
        assert_eq!(
            huge.bytes(),
            u32::MAX,
            "a wrap here answers 0 for a 4 GiB object"
        );

        // Saturation is MONOTONE: a longer array never reports a smaller
        // extent. That is the property the domination invariant needs, and it
        // is exactly what wrapping destroys.
        let longer = Type::Array(
            Box::new(Type::Struct(vec![Type::I8, Type::I64])),
            400_000_000,
        );
        assert!(longer.bytes() >= huge.bytes());

        // A struct whose FIELDS sum past the carrier saturates the same way,
        // and so does an array one element below the boundary, which must
        // still be exact rather than clamped.
        let exact = Type::Array(
            Box::new(Type::Struct(vec![Type::I8, Type::I64])),
            268_435_455,
        );
        assert_eq!(
            exact.bytes(),
            4_294_967_280,
            "one element short must be exact"
        );
        let summed = Type::Struct(vec![exact.clone(), exact]);
        assert_eq!(
            summed.bytes(),
            u32::MAX,
            "the struct accumulation saturates too"
        );
    }
}
