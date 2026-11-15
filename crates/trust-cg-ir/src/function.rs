// trust-cg-ir - Shared machine IR model
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Machine-level function and block types.
//!
//! Storage model: arena-based Vec indexed by typed wrappers.
//! No HashMap for blocks/values — Vec + index only (cache-friendly).

use crate::inst::{MachInst, ProofAnnotation};
use crate::provenance::{
    LoweringProvenance, LoweringProvenanceCoverage, SourceInstId, TrustIrVarId,
};
use crate::target_machine::{AArch64IsaFeature, TargetFeatureSet};
use crate::types::{BlockId, InstId, StackSlotId};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::sync::Arc;

mod eh_edge_census;
pub use eh_edge_census::EhEdgeCensus;

/// A basic block of machine instructions.
#[derive(Debug, Clone)]
pub struct MachBlock {
    /// Instructions in this block (indices into MachFunction::insts).
    pub insts: Vec<InstId>,
    /// Predecessor blocks.
    pub preds: Vec<BlockId>,
    /// Successor blocks.
    pub succs: Vec<BlockId>,
    /// Loop nesting depth (0 = not in a loop). Used by regalloc for spill
    /// weight computation and by optimization passes (LICM) for hoisting
    /// decisions. Populated by loop analysis; defaults to 0.
    pub loop_depth: u32,
}

impl MachBlock {
    /// Create a new empty block.
    pub fn new() -> Self {
        Self {
            insts: Vec::new(),
            preds: Vec::new(),
            succs: Vec::new(),
            loop_depth: 0,
        }
    }

    /// Returns true if the block has no instructions.
    pub fn is_empty(&self) -> bool {
        self.insts.is_empty()
    }

    /// Returns the number of instructions in this block.
    pub fn len(&self) -> usize {
        self.insts.len()
    }
}

impl Default for MachBlock {
    fn default() -> Self {
        Self::new()
    }
}

/// Tag storage width for the v1 tagged-union enum representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EnumTagWidth {
    U8,
    U16,
    U32,
    /// An eight-byte tag lane.
    ///
    /// NEVER produced by [`EnumTagWidth::for_variant_count`] — no variant count
    /// requires it. It exists because producers DECLARE it: rustc pads an enum's
    /// tag out to the payload's alignment, so `Option<Box<T>>` and its family
    /// arrive with a `#[repr(u64)]`-shaped tag on a TWO-variant enum. (c)
    /// MEASURED over a 68-module corpus: of 259 enums carrying an explicit repr,
    /// 118 declare U64 — 101 of those on two-variant enums — and before this
    /// variant existed the LIR could not name that layout at all.
    U64,
}

impl EnumTagWidth {
    pub fn for_variant_count(count: usize) -> Option<Self> {
        if count <= (u8::MAX as usize) + 1 {
            Some(Self::U8)
        } else if count <= (u16::MAX as usize) + 1 {
            Some(Self::U16)
        } else if count <= (u32::MAX as usize) + 1 {
            Some(Self::U32)
        } else {
            None
        }
    }

    pub fn bytes(self) -> u32 {
        match self {
            Self::U8 => 1,
            Self::U16 => 2,
            Self::U32 => 4,
            Self::U64 => 8,
        }
    }

    pub fn ty(self) -> Type {
        match self {
            Self::U8 => Type::I8,
            Self::U16 => Type::I16,
            Self::U32 => Type::I32,
            Self::U64 => Type::I64,
        }
    }
}

/// Type information for function signatures and stack slots.
///
/// Scalar types (I8..I128, F16..F64, B1, Ptr), SIMD vector types, and
/// aggregate types used by machine-level function signatures and stack slots.
/// V64/V128 are intentionally distinct from I64/I128: matching storage widths
/// do not imply matching ABI or register-class semantics.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    I8,
    I16,
    I32,
    I64,
    I128,
    F16,
    F32,
    F64,
    /// Boolean (1-bit).
    B1,
    /// Pointer-sized integer.
    Ptr,
    /// Aggregate structure type with C-like field layout.
    Struct(Vec<Type>),
    /// Fixed-size array type: element type and count.
    Array(Box<Type>, u32),
    /// Tagged-union enum: tag plus a max-sized, max-aligned payload.
    Enum {
        tag_width: EnumTagWidth,
        variants: Vec<Vec<Type>>,
    },
    /// Opaque 128-bit SIMD vector carrier.
    ///
    /// Lane interpretation belongs to the opcode using the value. The carrier
    /// itself is allocated in the 128-bit floating-point/vector register class
    /// and has 16-byte natural alignment. This variant is deliberately appended
    /// so existing variant discriminants—and derived type hashes—do not drift.
    V128,
    /// Opaque 64-bit SIMD vector carrier, held in AArch64 D registers.
    ///
    /// Has 8-byte size and natural alignment, but a floating-point/vector
    /// register class rather than I64's general-purpose register class.
    /// Appended to preserve existing variant discriminants and type hashes.
    V64,
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

    /// Size of this type in bytes.
    ///
    /// For structs, uses C-like layout with alignment padding between fields
    /// and trailing padding to the struct's alignment.
    /// For arrays, returns element_size * count.
    pub fn bytes(&self) -> u32 {
        match self {
            Self::I8 | Self::B1 => 1,
            Self::I16 | Self::F16 => 2,
            Self::I32 | Self::F32 => 4,
            Self::I64 | Self::F64 | Self::Ptr | Self::V64 => 8,
            Self::I128 | Self::V128 => 16,
            Self::Struct(fields) => {
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
            // SATURATING, not wrapping — this is a `u32`, so a type whose
            // natural extent reaches 2^32 has no representable size. Wrapping
            // made a release build report a small extent for a huge object
            // while a debug build panicked on the same type. See the extended
            // rationale on `trust_cg_lower::types::Type::bytes`, which carries
            // the measured out-of-bounds-write consequence; this enum is the
            // MachIR-level twin and gets the identical treatment.
            Self::Array(elem, count) => elem.bytes().saturating_mul(*count),
            Self::Enum {
                tag_width,
                variants,
            } => {
                let (payload_bytes, payload_align) = Self::enum_payload_layout(variants);
                let tag_bytes = tag_width.bytes();
                let payload_offset = Self::align_to(tag_bytes, payload_align);
                Self::align_to(payload_offset.saturating_add(payload_bytes), self.align())
            }
        }
    }

    /// Alias for `bytes()`.
    pub fn size_of(&self) -> u32 {
        self.bytes()
    }

    /// Natural alignment of this type in bytes.
    ///
    /// Scalars: min(size, 8), EXCEPT the 128-bit ones, which are 16. Struct:
    /// max alignment of fields. Array: element alignment.
    ///
    /// The `min(8)` cap is the natural-C rule for a scalar that fits a
    /// general-purpose register; a 128-bit scalar does not, and rustc gives it
    /// 16. (c) MEASURED with stock `rustc 1.97.0`: `align_of::<u128>() == 16`,
    /// `#[repr(C)] { a: u8, b: u128 }` is size 32 align 16 with `b@16`. The cap
    /// used to swallow `I128` and report 8.
    ///
    /// Not target-dependent within trust-cg's target set: the `i128:128`
    /// data-layout entry is present for every triple reachable from
    /// `trust_cg_codegen::target::Target` (`{X86_64, Aarch64, Riscv64}`) and
    /// absent only for 32-bit ARM / s390x / MIPS, which trust-cg does not
    /// emit for. See the twin note on `trust_cg_lower::types::Type::align`,
    /// which this enum must stay in step with.
    pub fn align(&self) -> u32 {
        match self {
            Self::V128 | Self::I128 => 16,
            Self::Struct(fields) => fields.iter().map(|f| f.align()).max().unwrap_or(1),
            Self::Array(elem, _) => elem.align(),
            Self::Enum {
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
    /// Returns `None` if this is not a struct type or the index is out of range.
    pub fn offset_of(&self, field_index: usize) -> Option<u32> {
        // An ARRAY is indexable by the same field index as the equivalent
        // uniform struct: `Array(t, n)` and `Struct([t; n])` place element `k`
        // at the same byte offset, because `Self::bytes()` models an array as
        // `elem.bytes() * count` (stride == element size, no inter-element
        // padding) and the struct walk below adds `align_to(offset, t.align())`
        // per field, which is a no-op when every field is the same `t`.
        //
        // Returning `None` here is NOT harmless: both `select_struct_gep`
        // implementations do `offset_of(..).unwrap_or(0)`, so a missing arm
        // silently addresses element 0 for every index.
        if let Self::Array(elem, count) = self {
            if field_index >= *count as usize {
                return None;
            }
            return u32::try_from(field_index)
                .ok()
                .and_then(|index| index.checked_mul(elem.bytes()));
        }
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
        Some(tag_width.ty())
    }

    /// Returns true if this is an aggregate (struct, array, or enum) type.
    pub fn is_aggregate(&self) -> bool {
        matches!(
            self,
            Self::Struct(_) | Self::Array(_, _) | Self::Enum { .. }
        )
    }

    /// Returns true if this is an integer type.
    pub fn is_int(&self) -> bool {
        matches!(
            self,
            Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128
        )
    }

    /// Returns true if this is a floating-point type.
    pub fn is_float(&self) -> bool {
        matches!(self, Self::F16 | Self::F32 | Self::F64)
    }

    /// Returns true if this is a SIMD vector type.
    pub fn is_vector(&self) -> bool {
        matches!(self, Self::V64 | Self::V128)
    }

    /// Returns true if this is a scalar (non-aggregate) type.
    pub fn is_scalar(&self) -> bool {
        !self.is_aggregate()
    }
}

/// Function signature: parameter and return types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    pub params: Vec<Type>,
    pub returns: Vec<Type>,
}

impl Signature {
    pub fn new(params: Vec<Type>, returns: Vec<Type>) -> Self {
        Self { params, returns }
    }
}

/// A stack slot allocated in the function's stack frame.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StackSlotAllocationKind {
    /// Size is known at compile time.
    #[default]
    Fixed,
    /// Size is computed at runtime.
    ///
    /// `size_source` is backend-agnostic metadata for the producer of the
    /// runtime size (for example, the SSA value that contributes a dynamic
    /// alloca count).
    RuntimeSized { size_source: StackSlotSizeSource },
}

/// Provenance metadata for runtime-sized slots.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StackSlotSizeSource {
    /// General-purpose runtime size source marker.
    Value(u32),
    /// Dynamic size source not yet associated with a concrete value.
    Unknown,
}

/// Stack slot placement and size metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct StackSlot {
    /// Size in bytes.
    ///
    /// For runtime-sized slots this is `0` when the unit size is unknown, or
    /// the per-element byte stride when the lowering pipeline preserved it.
    pub size: u32,
    /// Alignment in bytes (must be power of 2).
    pub align: u32,
    /// Whether this is fixed-size or runtime-sized.
    pub allocation: StackSlotAllocationKind,
}

impl StackSlot {
    /// Create a fixed-size stack slot.
    pub fn new(size: u32, align: u32) -> Self {
        // Soundness precondition: a non-power-of-two (or zero) alignment is a
        // genuine miscompile if it reaches frame layout / address computation,
        // so enforce it in ALL profiles (was a debug_assert, which release
        // compiled out — item 4).
        assert!(align.is_power_of_two(), "alignment must be power of 2");
        Self {
            size,
            align,
            allocation: StackSlotAllocationKind::Fixed,
        }
    }

    /// Create a runtime-sized stack slot.
    ///
    /// `size` is intentionally deferred; consumers should check
    /// `is_runtime_sized()` and read `size_source()`.
    pub fn new_dynamic(size_source: StackSlotSizeSource, align: u32) -> Self {
        // Same soundness precondition as `new`; always-on (item 4).
        assert!(align.is_power_of_two(), "alignment must be power of 2");
        Self {
            size: 0,
            align,
            allocation: StackSlotAllocationKind::RuntimeSized { size_source },
        }
    }

    /// Create a runtime-sized stack slot with a known per-element byte stride.
    ///
    /// The total allocation size is still runtime-computed from `size_source`;
    /// `unit_size` lets AArch64 dynamic-stack lowering materialize
    /// `count * unit_size` instead of treating every runtime source as an
    /// already-byte-sized value.
    pub fn new_dynamic_with_unit(
        size_source: StackSlotSizeSource,
        unit_size: u32,
        align: u32,
    ) -> Self {
        // Same soundness precondition as `new`; always-on (item 4).
        assert!(align.is_power_of_two(), "alignment must be power of 2");
        // Same soundness class as the alignment asserts above (and the 3
        // already promoted): a zero unit stride makes AArch64 dynamic-stack
        // lowering materialize `count * 0 = 0` bytes for a non-empty runtime
        // allocation — an under-sized frame that only debug builds would
        // catch. Enforce in ALL profiles (was a debug_assert, which release
        // builds compile out).
        assert!(unit_size > 0, "runtime slot unit size must be non-zero");
        Self {
            size: unit_size,
            align,
            allocation: StackSlotAllocationKind::RuntimeSized { size_source },
        }
    }

    /// Returns true if this slot is known-size at compile time.
    pub fn is_fixed_size(&self) -> bool {
        matches!(self.allocation, StackSlotAllocationKind::Fixed)
    }

    /// Returns true if this slot requires runtime size metadata.
    pub fn is_runtime_sized(&self) -> bool {
        matches!(
            self.allocation,
            StackSlotAllocationKind::RuntimeSized { .. }
        )
    }

    /// Returns runtime-size provenance metadata when present.
    pub fn size_source(&self) -> Option<StackSlotSizeSource> {
        match self.allocation {
            StackSlotAllocationKind::RuntimeSized { size_source } => Some(size_source),
            StackSlotAllocationKind::Fixed => None,
        }
    }

    /// Returns the fixed slot size when known, otherwise `None`.
    pub fn fixed_size(&self) -> Option<u32> {
        if self.is_fixed_size() {
            Some(self.size)
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Exception handling metadata
// ---------------------------------------------------------------------------

/// Landing pad entry in the function's exception handling table.
///
/// Records the block offset of a landing pad and its catch/cleanup behavior.
/// Populated during ISel from `Invoke` / `LandingPad` instructions and
/// consumed by LSDA generation in the codegen pipeline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LandingPadEntry {
    /// Block ID of the landing pad block.
    pub block: BlockId,
    /// Byte offset of the landing pad from function start (filled after layout).
    pub offset: u32,
    /// Type indices this landing pad catches. 0 = catch-all.
    pub catch_type_indices: Vec<u32>,
    /// Whether this landing pad runs cleanup (destructors/drops).
    pub is_cleanup: bool,
}

/// Call site entry mapping a PC range to a landing pad.
///
/// Each entry describes a region of code (typically surrounding a `BL`
/// instruction from an `Invoke`) that may throw, and the landing pad that
/// should handle exceptions from that region.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EhCallSiteEntry {
    /// Block ID containing the invoke / call site.
    pub call_block: BlockId,
    /// Byte offset of the call site region start (filled after layout).
    pub start_offset: u32,
    /// Length of the call site region in bytes (filled after layout).
    pub length: u32,
    /// Block ID of the landing pad (None = exception propagates to caller).
    pub landing_pad_block: Option<BlockId>,
}

/// The exact selected call that owns one invoke's exceptional continuation.
///
/// IDs describe the current machine arena. An arena-rebuilding owner must
/// transport the instruction identity explicitly; matching a callee spelling
/// or choosing another call in the block cannot replace this binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EhInvokeBinding {
    /// The protected call in the current instruction arena.
    pub call_inst: InstId,
    /// Its unique laid-out instruction owner.
    pub call_block: BlockId,
    /// The original invoke's exceptional destination.
    pub landing_pad_block: BlockId,
}

/// How semantic handler rows bind their protected calls.
///
/// Legacy rows require exactly one eligible call in their block. Modern
/// selection uses exact identities, including an explicitly empty vector when
/// a required binding is missing; emptiness never requests legacy inference.
/// The vector retains duplicate/orphan records for checked refusal.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub enum EhCallSiteBindings {
    /// Explicit compatibility state: one eligible call per handler block.
    #[default]
    LegacyBlocks,
    /// Modern custody: every handler row needs one exact selected call.
    ExactInstructions(Vec<EhInvokeBinding>),
}

/// A function's EH type table: entry `k - 1` is the linker-level typeinfo
/// symbol bound to catch type index `k` (trust-ir landing pads carry only the
/// indices).
///
/// trust-ir v50 (`SPEC_RATIFICATIONS` §3.1) spells a table whose entries all
/// name ONE typeinfo as `Constant::Splat { elem, len }`. This type keeps that
/// spelling, so such a table holds one symbol whatever its length, and its
/// length, lookup and clone cost O(1). A list is shared behind an [`Arc`], so
/// every function that catches a typed exception carries the module's one
/// table without copying it.
///
/// The representation is canonical, as trust-ir's is: two or more equal
/// entries are always the splat and a splat always has two or more entries,
/// so two tables are equal exactly when their representations are.
#[derive(Clone, PartialEq, Eq, Default, Deserialize)]
#[serde(from = "EhTypeTableWire")]
pub struct EhTypeTable(EhTypeTableRepr);

#[derive(Clone, PartialEq, Eq, Default)]
enum EhTypeTableRepr {
    #[default]
    Empty,
    /// One or more entries, not all equal when two or more.
    List(Arc<[String]>),
    /// `len >= 2` copies of `symbol`.
    Splat { symbol: Arc<str>, len: u64 },
}

/// The two spellings of an [`EhTypeTable`], borrowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EhTypeTableEntries<'a> {
    /// Every entry, in catch-type-index order (possibly none).
    List(&'a [String]),
    /// `len >= 2` entries, every one `symbol`.
    Splat {
        /// The typeinfo symbol every entry names.
        symbol: &'a str,
        /// The number of entries.
        len: u64,
    },
}

/// Serialized spelling: a list is the plain symbol sequence it always was; a
/// splat is `{ "splat": symbol, "len": len }`. Deserializing canonicalizes.
#[derive(Deserialize)]
#[serde(untagged)]
enum EhTypeTableWire {
    List(Vec<String>),
    Splat { splat: String, len: u64 },
}

impl From<EhTypeTableWire> for EhTypeTable {
    fn from(wire: EhTypeTableWire) -> Self {
        match wire {
            EhTypeTableWire::List(symbols) => Self::from_symbols(symbols),
            EhTypeTableWire::Splat { splat, len } => Self::splat(splat, len),
        }
    }
}

impl Serialize for EhTypeTable {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        match self.entries() {
            EhTypeTableEntries::List(symbols) => symbols.serialize(serializer),
            EhTypeTableEntries::Splat { symbol, len } => {
                let mut state = serializer.serialize_struct("EhTypeTableSplat", 2)?;
                state.serialize_field("splat", symbol)?;
                state.serialize_field("len", &len)?;
                state.end()
            }
        }
    }
}

impl std::fmt::Debug for EhTypeTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.entries() {
            EhTypeTableEntries::List(symbols) => f.debug_list().entries(symbols).finish(),
            EhTypeTableEntries::Splat { symbol, len } => write!(f, "splat[{symbol:?}; {len}]"),
        }
    }
}

impl EhTypeTable {
    /// The empty table (a function that catches no typed exception).
    pub const fn new() -> Self {
        Self(EhTypeTableRepr::Empty)
    }

    /// The table whose entry `k - 1` is `symbols[k - 1]`. Two or more equal
    /// entries become the splat (one comparison per entry given).
    pub fn from_symbols(symbols: Vec<String>) -> Self {
        match symbols.as_slice() {
            [] => Self::new(),
            [first, rest @ ..] if !rest.is_empty() && rest.iter().all(|s| s == first) => {
                let len = symbols.len() as u64;
                let mut symbols = symbols;
                Self::splat(symbols.swap_remove(0), len)
            }
            _ => Self(EhTypeTableRepr::List(Arc::from(symbols))),
        }
    }

    /// The table of `len` entries that all name `symbol`, in O(1) whatever
    /// `len` is. Fewer than two entries are the list.
    pub fn splat(symbol: String, len: u64) -> Self {
        match len {
            0 => Self::new(),
            1 => Self(EhTypeTableRepr::List(Arc::from(vec![symbol]))),
            len => Self(EhTypeTableRepr::Splat {
                symbol: Arc::from(symbol),
                len,
            }),
        }
    }

    /// The number of entries (the largest catch type index it binds).
    pub fn len(&self) -> u64 {
        match &self.0 {
            EhTypeTableRepr::Empty => 0,
            EhTypeTableRepr::List(symbols) => symbols.len() as u64,
            EhTypeTableRepr::Splat { len, .. } => *len,
        }
    }

    /// Whether the table binds no catch type index.
    pub fn is_empty(&self) -> bool {
        matches!(self.0, EhTypeTableRepr::Empty)
    }

    /// The symbol at zero-based `position` (catch type index `position + 1`),
    /// or `None` past the end. O(1).
    pub fn get(&self, position: u64) -> Option<&str> {
        match &self.0 {
            EhTypeTableRepr::Empty => None,
            EhTypeTableRepr::List(symbols) => usize::try_from(position)
                .ok()
                .and_then(|position| symbols.get(position))
                .map(String::as_str),
            EhTypeTableRepr::Splat { symbol, len } => (position < *len).then_some(&**symbol),
        }
    }

    /// The symbol bound to catch type index `index` (`1..=len`); `None` for
    /// the catch-all index `0` and for an index the table does not bind.
    pub fn symbol_for_catch_index(&self, index: u32) -> Option<&str> {
        index
            .checked_sub(1)
            .and_then(|position| self.get(u64::from(position)))
    }

    /// Whether `self` and `other` are clones of ONE table (they share its
    /// storage). Two empty tables are. Equal tables read separately are not.
    pub fn shares_storage_with(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (EhTypeTableRepr::Empty, EhTypeTableRepr::Empty) => true,
            (EhTypeTableRepr::List(a), EhTypeTableRepr::List(b)) => Arc::ptr_eq(a, b),
            (
                EhTypeTableRepr::Splat { symbol: a, len: m },
                EhTypeTableRepr::Splat { symbol: b, len: n },
            ) => m == n && Arc::ptr_eq(a, b),
            _ => false,
        }
    }

    /// The table's spelling, borrowed: a list's entries, or a splat's one
    /// symbol and length.
    pub fn entries(&self) -> EhTypeTableEntries<'_> {
        match &self.0 {
            EhTypeTableRepr::Empty => EhTypeTableEntries::List(&[]),
            EhTypeTableRepr::List(symbols) => EhTypeTableEntries::List(&symbols[..]),
            EhTypeTableRepr::Splat { symbol, len } => {
                EhTypeTableEntries::Splat { symbol, len: *len }
            }
        }
    }
}

/// Exception handling metadata for a function.
///
/// Collected during ISel and consumed by the codegen pipeline to generate
/// the LSDA (Language-Specific Data Area) in the `__gcc_except_tab` section.
///
/// This is the IR-level representation that bridges the gap between
/// ISel-level EH instructions (Invoke/LandingPad/Resume) and the
/// codegen-level LSDA generation (`trust_cg_codegen::exception_handling`).
#[derive(Debug, Clone, Default)]
pub struct ExceptionHandlingMetadata {
    /// Personality function symbol name (e.g., "__gxx_personality_v0").
    /// `None` for functions without exception handling.
    pub personality: Option<String>,
    /// Landing pad entries.
    pub landing_pads: Vec<LandingPadEntry>,
    /// Call site entries (invoke regions mapped to landing pads).
    pub call_sites: Vec<EhCallSiteEntry>,
    /// Selected-call custody, independent of layout offsets and filler rows.
    pub call_site_bindings: EhCallSiteBindings,
    /// EH type table: entry `k - 1` is the linker-level typeinfo symbol bound
    /// to catch type index `k` of every landing pad in this function (trust-ir
    /// carries only indices). The LSDA emitter relocates each typed slot to
    /// the named symbol. Empty unless a pad catches a typed exception.
    pub eh_type_table: EhTypeTable,
}

impl ExceptionHandlingMetadata {
    /// Create a new empty EH metadata.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns true if this function has exception handling metadata.
    pub fn has_eh_info(&self) -> bool {
        self.personality.is_some()
            || !self.landing_pads.is_empty()
            || !self.call_sites.is_empty()
            || matches!(&self.call_site_bindings, EhCallSiteBindings::ExactInstructions(bindings) if !bindings.is_empty())
    }

    /// Add a landing pad entry.
    pub fn add_landing_pad(&mut self, entry: LandingPadEntry) {
        self.landing_pads.push(entry);
    }

    /// Add a call site entry.
    pub fn add_call_site(&mut self, entry: EhCallSiteEntry) {
        self.call_sites.push(entry);
    }
}

/// Jump table data for switch lowering.
///
/// Carried on [`MachFunction`] through the compilation pipeline. The ISel
/// emits an `Adr` instruction whose second operand is
/// [`MachOperand::JumpTableIndex(idx)`](crate::operand::MachOperand::JumpTableIndex),
/// referencing an entry in [`MachFunction::jump_tables`]. The codegen
/// pipeline resolves this to a PC-relative byte offset once block layout
/// is known, and appends the table entries (32-bit signed PC-relative
/// offsets from the table base to each target block) immediately after the
/// function body in the `__text` section.
///
/// Table entries are computed as `target_block_byte_offset - table_base_byte_offset`
/// and are indexed by `selector - min_val`. Holes (values in the range
/// without an explicit case) map to the default block.
#[derive(Debug, Clone)]
pub struct JumpTableData {
    /// Minimum case value. The selector is normalized by subtracting this
    /// before indexing into the table.
    pub min_val: i64,
    /// Dense vector of target blocks, indexed from 0. `targets[i]` is the
    /// block to jump to for case value `min_val + i`. Holes map to the
    /// default block.
    pub targets: Vec<BlockId>,
}

/// Custody of a scratch-free local table-address expansion. The keyed ADR
/// now has its actual low-byte immediate; `add` is the immediately following
/// ADD-immediate LSL12 on that same 64-bit register. These are measurement
/// metadata, not a certificate: final-byte checks must independently bind the
/// composed address to `table` in the final layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JumpTableAddressExpansion {
    pub table: u32,
    pub add: InstId,
}

/// Scalar debug type used by DWARF metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DebugBaseType {
    I8,
    I16,
    I32,
    I64,
    I128,
    F32,
    F64,
    Bool,
    U8,
    U16,
    U32,
    U64,
    U128,
    Ptr,
}

/// Debug metadata for one struct member.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DebugStructMember {
    pub name: String,
    pub offset: u32,
    pub ty: DebugBaseType,
}

/// Debug metadata for one aggregate structure type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DebugStructType {
    pub name: String,
    pub byte_size: u32,
    pub members: Vec<DebugStructMember>,
}

/// Debug metadata for one enum variant as a DWARF enumerator.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DebugEnumerator {
    pub name: String,
    pub value: i64,
}

/// Debug metadata for one enumeration type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DebugEnumType {
    pub name: String,
    pub byte_size: u32,
    pub underlying_type: DebugBaseType,
    pub enumerators: Vec<DebugEnumerator>,
}

/// Source-variable storage known before final frame lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DebugVariableStorage {
    /// Variable lives in a machine stack slot. The final FP-relative offset is
    /// computed after register allocation and frame lowering.
    StackSlot(u32),
    /// Variable has been proven to a constant integer value.
    ConstantInt(u64),
    /// Variable location is described by a post-optimization provenance
    /// live-range record. The trust_ir adapter does not populate this yet; this
    /// variant supports the bounded synthetic/O3-consumer slice first.
    ProvenanceVar(TrustIrVarId),
}

/// Source-level local variable metadata preserved for DWARF emission.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DebugLocalVariable {
    pub name: String,
    pub ty: DebugBaseType,
    pub storage: DebugVariableStorage,
    pub decl_line: u32,
}

/// Debug metadata extracted from trust_ir for DWARF emission.
///
/// Carried on [`MachFunction`] through the compilation pipeline so the
/// codegen can populate [`FunctionDebugInfo`](crate::dwarf_info::FunctionDebugInfo)
/// with real source-level information rather than stubs.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FunctionDebugMeta {
    /// Source file name (e.g., "main.rs"). `None` if unknown.
    pub source_file: Option<String>,
    /// The producer's human name for the function (trust-ir
    /// `Function::display_path`, e.g. `crate::module::item`), which DWARF uses
    /// as the subprogram's `DW_AT_name` in place of the object symbol. `None`
    /// keeps the object symbol as the name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub display_name: Option<String>,
    /// Source line where the function is declared (1-based, 0 = unknown).
    pub decl_line: u32,
    /// Parameter names (from trust_ir signature or generated as "arg0", "arg1", ...).
    pub param_names: Vec<String>,
    /// Source locals with known storage before final frame lowering.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub local_variables: Vec<DebugLocalVariable>,
    /// Aggregate type definitions available in the trust_ir module.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub struct_types: Vec<DebugStructType>,
    /// Enum type definitions available in the trust_ir module.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub enum_types: Vec<DebugEnumType>,
}

/// Function-level stack-protector lowering requirement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub enum StackProtectorMode {
    /// No stack canary is required.
    #[default]
    None,
    /// Emit the platform stack guard save/check sequence.
    StackGuard,
}

impl StackProtectorMode {
    /// Returns true when this function requires stack canary lowering.
    pub fn is_enabled(self) -> bool {
        !matches!(self, Self::None)
    }
}

/// Where a U10 prologue stack-limit check reads its limit `L`
/// (`docs/u10-prologue-stack-limit.md` §2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum StackLimitSource {
    /// The request's parameter holds `L` itself.
    Value,
    /// The request's parameter points at a little-endian u64 `L` at byte
    /// `offset` (8-aligned, at most [`STACK_LIMIT_MAX_POINTEE_OFFSET`]). The
    /// producer guarantees that word is readable on every entry.
    Pointee {
        /// Byte offset of `L` from the pointer.
        offset: u16,
    },
}

/// Largest `Pointee` offset a request tag can carry (`off/8` in 12 bits).
pub const STACK_LIMIT_MAX_POINTEE_OFFSET: u16 = 4095 * 8;

/// What a U10 stack-limit check does when the frame would cross `L`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum StackLimitOverflow {
    /// Undo the callee-saved stores and tail-call `symbol`, the module's
    /// handler for this function's `FuncTy`, with the entry arguments intact.
    Handler {
        /// The handler's symbol name.
        symbol: String,
    },
    /// Execute `brk #`[`STACK_LIMIT_TRAP_IMM`] with the frame intact.
    Trap,
}

/// The `BRK` immediate a U10 `Trap` overflow executes (ASCII "SL").
pub const STACK_LIMIT_TRAP_IMM: u16 = 0x534c;

/// A function's U10 prologue stack-limit request, decoded and validated from
/// its producer tags by the trust-ir adapter.
///
/// The request is a *requirement*: a backend that cannot emit and verify the
/// check refuses the function, never drops the request.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StackLimitRequest {
    /// Index of the signature parameter that holds or points at `L`. It is a
    /// parameter index, not a register number: the target's signature
    /// lowering resolves the register.
    pub param: u8,
    /// How the parameter supplies `L`.
    pub source: StackLimitSource,
    /// The overflow action.
    pub overflow: StackLimitOverflow,
}

/// A [`StackLimitRequest`] after AArch64 signature lowering resolved its
/// parameter to one X register (X0-X7) that holds the parameter's full entry
/// value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MachStackLimit {
    /// The source request.
    pub request: StackLimitRequest,
    /// The X register that carries parameter `request.param` at entry.
    pub limit_reg: crate::regs::PReg,
    /// Every register the function's formal arguments arrive in, in
    /// signature order: the implicit uses of the overflow `TailCall`, which
    /// hands the handler the requester's entry arguments unchanged.
    pub arg_regs: Vec<crate::regs::PReg>,
}

/// The callee-saved register set a call's convention preserves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CalleeSavedSet {
    /// The AAPCS64 / DarwinPCS set: X19-X28, FP and the low 64 bits of
    /// V8-V15. Every convention instruction selection lowers (C, Fast, Cold,
    /// Rust and the scalar Swift subset) preserves exactly this set, which is
    /// also the set every lowered function preserves for its own caller.
    Aapcs64,
}

/// One outgoing stack-argument store a call site's classification requires:
/// `bytes` bytes at `offset` from the stack pointer at the call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StackArgStore {
    /// Byte offset in the outgoing argument area.
    pub offset: i64,
    /// Store width in bytes.
    pub bytes: u8,
}

/// One trap carrier and the instructions its late expansion left in the
/// function (`trust-cg-codegen` `lower::expand_trap_*`).
///
/// `carrier` is the guard as instruction selection emitted it and register
/// allocation rewrote it (`TrapNullIfZero ptr`, `TrapBoundsCheckExact base,
/// index, bound`, ...): it names the trap condition of the source operation.
/// `insts` are the expansion's instructions in stream order, the last being
/// the `BRK`. The verifier and the per-compile decode check judge these words
/// against that condition (`trust_cg_verify::aarch64_trap_expansion`). A
/// carrier the expansion degraded to a bare trap (a malformed carrier) has no
/// record.
#[derive(Debug, Clone)]
pub struct TrapExpansionRecord {
    /// The carrier before its expansion.
    pub carrier: MachInst,
    /// The expansion's instructions, in stream order.
    pub insts: Vec<InstId>,
}

/// ABI facts of one AArch64 call site, recorded by instruction selection
/// where the target calling convention classified every argument.
///
/// Consumers (sibling tail-call eligibility) read these instead of guessing
/// from operand counts. They describe the call as selected; a pass that
/// rewrites or clones a call does not inherit them (see
/// [`MachFunction::call_abi_facts`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallAbiFacts {
    /// Direct callee symbol; `None` for an indirect call.
    pub callee: Option<String>,
    /// End of the highest outgoing stack-argument byte the call writes
    /// (0 when every argument is passed in registers).
    pub stack_arg_bytes: u32,
    /// The scalar stack-argument stores instruction selection emitted for
    /// this call, one entry per store.
    pub stack_stores: Vec<StackArgStore>,
    /// Some stack argument is an aggregate copied by a sequence that is not
    /// a list of scalar stores.
    pub aggregate_stack_args: bool,
    /// The call passes a hidden result pointer in X8: the callee returns a
    /// large aggregate through caller-provided memory.
    pub hidden_result_pointer: bool,
    /// Some argument is a composite passed by reference (AAPCS64 B.4, kept
    /// by DarwinPCS): its register or stack slot holds the address of a
    /// copy in the caller's frame, which the callee owns for the call.
    pub by_reference_argument_copies: bool,
    /// The callee is variadic.
    pub variadic: bool,
    /// Callee-saved registers the callee's convention preserves.
    pub callee_saved: CalleeSavedSet,
}

/// A complete machine-level function, ready for register allocation and encoding.
#[derive(Debug, Clone)]
pub struct MachFunction {
    /// Function name (mangled symbol name).
    pub name: String,
    /// Function signature.
    pub signature: Signature,
    /// All instructions, indexed by InstId.
    pub insts: Vec<MachInst>,
    /// All basic blocks, indexed by BlockId.
    pub blocks: Vec<MachBlock>,
    /// Block layout order (for code emission).
    pub block_order: Vec<BlockId>,
    /// Entry block.
    pub entry: BlockId,
    /// Next virtual register ID to allocate.
    pub next_vreg: u32,
    /// Stack slots allocated by this function.
    pub stack_slots: Vec<StackSlot>,
    /// Exception handling metadata (landing pads, call sites, personality).
    /// Populated during ISel for functions that contain invoke/landingpad
    /// instructions. Consumed by the codegen pipeline to generate the LSDA.
    pub eh_metadata: ExceptionHandlingMetadata,
    /// Function-level proof annotations from trust_ir.
    ///
    /// These proofs apply to the function as a whole (e.g., Pure, Associative,
    /// Commutative, Idempotent) rather than to individual instructions.
    /// Populated by the compilation pipeline from the adapter's ProofContext
    /// function_proofs.
    ///
    /// Per-instruction proofs are stored on each [`MachInst::proof`] field.
    pub function_proofs: Vec<ProofAnnotation>,
    /// Debug metadata extracted from trust_ir for DWARF emission.
    ///
    /// Populated by the compilation pipeline from the trust_ir adapter's debug
    /// info extraction. Consumed by the codegen pipeline to generate DWARF
    /// debug sections with real source-level information.
    pub debug_meta: FunctionDebugMeta,
    /// Function-level stack-protector lowering requirement.
    pub stack_protector: StackProtectorMode,
    /// Stack slot reserved for the saved guard value after frame preparation.
    pub stack_protector_slot: Option<StackSlotId>,
    /// U10 prologue stack-limit requirement, copied from the source LIR
    /// function with its limit register resolved. `None` for every function
    /// that did not request one; frame lowering then emits nothing new.
    pub stack_limit: Option<MachStackLimit>,
    /// The overflow block frame insertion built for [`Self::stack_limit`]
    /// (`None` before frame insertion, or when the check was elided for a
    /// zero frame). Block layout keeps it cold.
    pub stack_limit_overflow_block: Option<BlockId>,
    /// Jump tables for switch lowering. Each `Adr` instruction that loads
    /// a jump table base address carries a
    /// [`MachOperand::JumpTableIndex`](crate::operand::MachOperand::JumpTableIndex)
    /// referencing an entry in this vector. The codegen pipeline appends
    /// the table entries after the function body and patches the `Adr`
    /// with the correct PC-relative byte offset.
    pub jump_tables: Vec<JumpTableData>,
    /// Long local table addresses, keyed by the original ADR's stable arena ID.
    /// Instructions and their block/EH ownership remain in place.
    pub jump_table_address_expansions: BTreeMap<InstId, JumpTableAddressExpansion>,
    /// Virtual-register ids of pointer parameters marked `noalias` in trust_ir.
    ///
    /// Populated by the compilation pipeline (`apply_proof_annotations`) from the
    /// adapter's [`ProofContext`] param-noalias set, resolved through the ISel
    /// value map to the machine vreg that carries each noalias pointer parameter.
    /// Empty for functions with no noalias pointer parameters (the default) and
    /// for any construction path that does not thread param attributes.
    ///
    /// These ids transport source `ParamAttrs::noalias` claims, not independently
    /// replayed alias proofs or caller/storage authority. The source attribute
    /// states non-aliasing with other arguments; populating this list does not
    /// authenticate object bounds or arbitrary address descendants. The
    /// `neon-map` store-vectorizer is the only consumer; it
    /// requires the store base pointer to appear here (and every load base to be
    /// either the identical vreg, in-place, or another entry, disjoint) before it
    /// will vectorize a memory MAP loop. Under-population is safe (the pass merely
    /// BAILS to the scalar loop); over-population would be unsound. This list is
    /// written only from the corresponding source attribute, whose truth remains
    /// a producer/caller obligation.
    pub noalias_params: Vec<u32>,
    /// Required start alignment (log2 bytes) of this function's code within
    /// its text section. Default 2 (AArch64 instruction alignment).
    ///
    /// Raised to 5 (32 bytes) by the emission-time loop-head alignment pass
    /// (`trust_cg_codegen::loop_align`) when it aligned at least one innermost
    /// loop header to a FUNCTION-RELATIVE 32-byte boundary: the intra-function
    /// padding only yields absolutely aligned loop heads if the function start
    /// itself sits on a 32-byte boundary in the final image, so the module
    /// emitters must (a) pad the combined text stream up to this alignment
    /// before placing the function and (b) raise the text section's alignment
    /// to at least this value. Perf-only: ignoring it cannot miscompile, it
    /// only forfeits the alignment.
    pub text_align_log2: u8,
    /// True when a loaded execution profile (PGO use) explicitly ordered this
    /// function's `block_order` (the ProfileUsePass hot-chain layout committed
    /// a reorder). The codegen-final static branch layout treats the profile
    /// order as authoritative for such functions: it skips its own reorder and
    /// performs only the sound branch-to-next elision. Without this bit the
    /// static re-layout silently overrode profile placement on functions whose
    /// shape did not trip its fail-closed bails (measured on Stanford/Towers).
    /// Default `false`; only ever set by profile-use compiles.
    pub profile_ordered: bool,
    /// TV-1 lowering-provenance sidecar, keyed by arena [`InstId`].
    ///
    /// Populated by the ISel->MachFunction adapter
    /// (`trust_cg_lower::isel::ISelFunction::to_ir_func`) for every
    /// instruction it converts. Keyed by `InstId` rather than stored as a
    /// parallel Vec because the instruction arena is append-only (`push_inst`
    /// never renumbers existing ids; passes unlink `InstId`s from blocks but
    /// never compact the arena), so keyed entries can never be misaligned by
    /// downstream mutation. Instructions without an entry (pass-created,
    /// pass-cloned, or test-constructed) report
    /// [`LoweringProvenance::UNATTRIBUTED`] via
    /// [`MachFunction::inst_lowering_provenance`] — under-attribution is safe,
    /// misattribution is not. See the schema comment in
    /// [`crate::provenance`] (LoweringProvenance section).
    pub lowering_provenance: BTreeMap<InstId, LoweringProvenance>,
    /// TV-3 fusion edges recorded by instruction selection: each key is a
    /// lowering-input instruction that emitted nothing of its own, mapped to
    /// the source instruction whose stamped machine instruction represents it.
    ///
    /// Populated by the ISel->MachFunction adapter from the selector's own
    /// edges. The AArch64 selector records one only after an exact idiom match
    /// has proved the fused effect unobservable (today: the stores of a
    /// private stack slot folded into a bit-reverse `RBIT`). The raw TV-3
    /// check follows these edges to an emitted witness; an effectful source
    /// with no edge stays unwitnessed and fails closed. Keyed by source
    /// coordinates, so no machine pass can invalidate an entry; passes neither
    /// read nor write it.
    pub source_fusion_targets: BTreeMap<SourceInstId, SourceInstId>,
    /// Call-site ABI facts, keyed by the call's arena [`InstId`].
    ///
    /// Populated by the ISel->MachFunction adapter for the calls instruction
    /// selection classified. Keyed like [`Self::lowering_provenance`] because
    /// the arena is append-only. A call without an entry (pass-created,
    /// pass-cloned or test-constructed) has no classified facts, and a
    /// consumer must treat it as unknown -- never as register-only. Each entry
    /// names its callee, so a consumer also checks that the instruction still
    /// calls that symbol.
    pub call_abi_facts: BTreeMap<InstId, CallAbiFacts>,
    /// End of this function's own incoming stack-argument area as classified
    /// by instruction selection (0 when every parameter arrives in
    /// registers); `None` when no selector recorded it.
    pub incoming_stack_arg_bytes: Option<u32>,
    /// Optional AArch64 features this function's own source attribute
    /// (trust-ir `FuncAttrs.target_features`, rustc's
    /// `#[target_feature(enable = ...)]`) admits beyond the target profile,
    /// for this function alone. Empty for a function without such an
    /// attribute and for every non-AArch64 function.
    ///
    /// Instruction selection reads it to choose feature instructions (LSE,
    /// CRC32, FP16, ...) only here; output-feature checks validate this
    /// function's instructions against the profile plus this set
    /// (`TargetMachine::for_function`); the JIT install gate refuses a set
    /// the executing host does not implement.
    pub function_target_features: TargetFeatureSet<AArch64IsaFeature>,
    /// Trap carriers the late expansion rewrote, and the instructions each
    /// expansion left (see [`TrapExpansionRecord`]). Empty until the
    /// expansion runs. Keyed by arena [`InstId`]s like
    /// [`Self::lowering_provenance`]; a pass that removes an expansion's
    /// instructions must remove all of them or the per-compile check refuses
    /// the function.
    pub trap_expansions: Vec<TrapExpansionRecord>,
    /// L10-P5 allocation-time identity admission (see
    /// [`crate::id_admission`]): whether the next allocation must first
    /// re-derive every live identity, and a sticky refusal. Opaque in `Debug`,
    /// so `Debug` equality remains IR equality.
    pub(crate) id_admission: crate::id_admission::IdAdmissionCell,
}

impl MachFunction {
    /// Create a new function with the given name and signature.
    pub fn new(name: String, signature: Signature) -> Self {
        // Create entry block (bb0).
        let entry_block = MachBlock::new();
        Self {
            name,
            signature,
            insts: Vec::new(),
            blocks: vec![entry_block],
            block_order: vec![BlockId(0)],
            entry: BlockId(0),
            next_vreg: 0,
            stack_slots: Vec::new(),
            eh_metadata: ExceptionHandlingMetadata::new(),
            function_proofs: Vec::new(),
            debug_meta: FunctionDebugMeta::default(),
            stack_protector: StackProtectorMode::None,
            stack_protector_slot: None,
            stack_limit: None,
            stack_limit_overflow_block: None,
            jump_tables: Vec::new(),
            jump_table_address_expansions: BTreeMap::new(),
            noalias_params: Vec::new(),
            text_align_log2: 2,
            profile_ordered: false,
            lowering_provenance: BTreeMap::new(),
            source_fusion_targets: BTreeMap::new(),
            call_abi_facts: BTreeMap::new(),
            incoming_stack_arg_bytes: None,
            function_target_features: TargetFeatureSet::EMPTY,
            trap_expansions: Vec::new(),
            id_admission: crate::id_admission::IdAdmissionCell::ADMITTED,
        }
    }

    /// The local table this address producer names. Expanded pairs keep the
    /// table identity here while both real instructions use literal immediates.
    pub fn jump_table_at_address(&self, id: crate::InstId) -> Option<u32> {
        let inst = self.insts.get(id.0 as usize)?;
        if inst.opcode != crate::AArch64Opcode::Adr {
            return None;
        }
        self.jump_table_address_expansions
            .get(&id)
            .map(|row| row.table)
            .or_else(|| {
                inst.operands
                    .get(1)
                    .and_then(crate::MachOperand::as_jump_table_index)
            })
    }

    /// Allocate a new virtual register ID (legacy infallible API).
    ///
    /// The ID is fresh while `next_vreg` exceeds every register the function
    /// references. After a pipeline boundary (each optimizer pass entry,
    /// [`Self::require_id_admission_before_allocation`]) the first allocation
    /// of any kind re-derives every live identity
    /// ([`Self::admit_id_counters`]); a stale counter becomes a sticky
    /// refusal the pipeline reports by name, so the function is never emitted.
    /// On exhaustion this never wraps: it returns the sentinel `u32::MAX` and
    /// leaves the counter there, and since no counter can exceed `u32::MAX`
    /// the next admission refuses any function that uses the sentinel
    /// (`[TCG-MIR-ID-EXHAUSTED]`). Use [`Self::try_alloc_vreg`] to handle
    /// exhaustion and refusal at the call site instead.
    pub fn alloc_vreg(&mut self) -> u32 {
        self.admit_before_allocation();
        match self.next_vreg.checked_add(1) {
            Some(next) => {
                let id = self.next_vreg;
                self.next_vreg = next;
                id
            }
            None => u32::MAX,
        }
    }

    /// Allocate one virtual-register ID, or leave the counter unchanged on
    /// exhaustion or a refused identity admission (see [`Self::alloc_vreg`]).
    /// `u32::MAX` represents an exhausted counter, not an ID this allocator
    /// can issue: the next unused ID must remain representable.
    ///
    /// Freshness against direct mutation of the public IR fields is checked
    /// only by the first allocation after a marked boundary; between
    /// boundaries this checks numeric capacity, so callers that insert
    /// register operands directly must first synchronize `next_vreg` above
    /// those IDs.
    pub fn try_alloc_vreg(&mut self) -> Option<u32> {
        if !self.admit_before_allocation() {
            return None;
        }
        let next = self.next_vreg.checked_add(1)?;
        let id = self.next_vreg;
        self.next_vreg = next;
        Some(id)
    }

    /// Allocate `count` consecutive virtual-register IDs at once, or none:
    /// the counter is unchanged on exhaustion (the range end must remain a
    /// representable counter, as for [`Self::try_alloc_vreg`]) or a refused
    /// identity admission. The admission runs even for `count == 0`.
    ///
    /// For a pass that plans its new registers before it can mutate the
    /// function (SROA numbers its shadow registers while the function is
    /// borrowed for analysis): it reads `next_vreg`, numbers from it, and
    /// allocates exactly that range here before any operand names one. An
    /// admitted counter is the one the numbering read when nothing changed
    /// the function in between, so the caller can check
    /// `range.start == planned_first`.
    pub fn try_alloc_vreg_range(&mut self, count: u32) -> Option<core::ops::Range<u32>> {
        if !self.admit_before_allocation() {
            return None;
        }
        let first = self.next_vreg;
        let end = first.checked_add(count)?;
        self.next_vreg = end;
        Some(first..end)
    }

    /// Synchronize the counter with all register operands in the arena and
    /// noalias parameter identities, including detached instructions. This
    /// scans once and jumps over sparse IDs instead of allocating through the
    /// numeric gap. Refusal leaves the counter unchanged.
    ///
    /// Call once before a sequence of checked allocations; subsequent direct
    /// mutation of public operands/metadata requires another synchronization.
    pub fn try_sync_vreg_counter(&mut self) -> Option<()> {
        let highest = self
            .insts
            .iter()
            .flat_map(|inst| inst.operands.iter())
            .filter_map(|operand| operand.as_vreg().map(|reg| reg.id))
            .chain(self.noalias_params.iter().copied())
            .max();
        if let Some(highest) = highest {
            let next = highest.checked_add(1)?;
            self.next_vreg = self.next_vreg.max(next);
        }
        Some(())
    }

    /// Add an instruction to the arena and return its InstId (legacy
    /// infallible API). The arena length is the counter, so the ID is fresh
    /// while no block or sidecar names an instruction past the arena, which
    /// the allocation-time admission checks as for [`Self::alloc_vreg`]. An
    /// index past the u32 ID domain never narrows into an existing ID's
    /// range: the sentinel `InstId(u32::MAX)` is returned and the next
    /// admission refuses the oversized arena. Use `try_push_inst` to refuse
    /// at the call site.
    pub fn push_inst(&mut self, inst: MachInst) -> InstId {
        self.admit_before_allocation();
        let id = Self::checked_inst_id(self.insts.len()).unwrap_or(InstId(u32::MAX));
        self.insts.push(inst);
        id
    }

    /// Append an instruction only when its arena index fits the ID domain and
    /// the identity admission accepts the function. Refusal leaves the arena
    /// unchanged. Unlike the register counter, the arena length can represent
    /// one past the final u32 ID on 64-bit hosts.
    pub fn try_push_inst(&mut self, inst: MachInst) -> Option<InstId> {
        if !self.admit_before_allocation() {
            return None;
        }
        let id = Self::checked_inst_id(self.insts.len())?;
        self.insts.push(inst);
        Some(id)
    }

    fn checked_inst_id(index: usize) -> Option<InstId> {
        u32::try_from(index).ok().map(InstId)
    }

    /// Create a new basic block and return its BlockId (legacy infallible
    /// API; freshness and exhaustion as for [`Self::push_inst`]). Use
    /// [`Self::try_create_block`] to refuse at the call site.
    pub fn create_block(&mut self) -> BlockId {
        self.admit_before_allocation();
        let id = Self::checked_block_id(self.blocks.len()).unwrap_or(BlockId(u32::MAX));
        self.blocks.push(MachBlock::new());
        self.block_order.push(id);
        id
    }

    /// Create a block only if its index fits the ID domain. ID refusal leaves
    /// both the block arena and layout unchanged; this does not bound memory.
    pub fn try_create_block(&mut self) -> Option<BlockId> {
        if !self.admit_before_allocation() {
            return None;
        }
        let id = Self::checked_block_id(self.blocks.len())?;
        self.blocks.push(MachBlock::new());
        self.block_order.push(id);
        Some(id)
    }

    fn checked_block_id(index: usize) -> Option<BlockId> {
        u32::try_from(index).ok().map(BlockId)
    }

    /// Append an instruction to a block.
    pub fn append_inst(&mut self, block: BlockId, inst_id: InstId) {
        self.blocks[block.0 as usize].insts.push(inst_id);
    }

    /// Add a stack slot and return its ID (legacy infallible API; freshness
    /// and exhaustion as for [`Self::push_inst`]). Use
    /// [`Self::try_alloc_stack_slot`] for fallible ID allocation.
    pub fn alloc_stack_slot(&mut self, slot: StackSlot) -> StackSlotId {
        self.admit_before_allocation();
        let id =
            Self::checked_stack_slot_id(self.stack_slots.len()).unwrap_or(StackSlotId(u32::MAX));
        self.stack_slots.push(slot);
        id
    }

    /// Append a stack slot only if its index fits the ID domain. ID refusal
    /// leaves the arena unchanged; slot layout validity is a separate concern.
    pub fn try_alloc_stack_slot(&mut self, slot: StackSlot) -> Option<StackSlotId> {
        if !self.admit_before_allocation() {
            return None;
        }
        let id = Self::checked_stack_slot_id(self.stack_slots.len())?;
        self.stack_slots.push(slot);
        Some(id)
    }

    fn checked_stack_slot_id(index: usize) -> Option<StackSlotId> {
        u32::try_from(index).ok().map(StackSlotId)
    }

    /// TV-1: record which lowering-input instruction produced `id`.
    ///
    /// [`LoweringProvenance::UNATTRIBUTED`] values are not stored (absent ==
    /// unattributed by definition), keeping the sidecar proportional to the
    /// stamped surface.
    pub fn set_inst_lowering_provenance(&mut self, id: InstId, provenance: LoweringProvenance) {
        if provenance == LoweringProvenance::UNATTRIBUTED {
            self.lowering_provenance.remove(&id);
        } else {
            self.lowering_provenance.insert(id, provenance);
        }
    }

    /// TV-1: the lowering provenance of `id`.
    ///
    /// Total function: instructions without a recorded entry report
    /// [`LoweringProvenance::UNATTRIBUTED`] (never a wrong attribution).
    pub fn inst_lowering_provenance(&self, id: InstId) -> LoweringProvenance {
        self.lowering_provenance
            .get(&id)
            .copied()
            .unwrap_or_default()
    }

    /// TV-3: the source instruction whose stamped machine instruction
    /// represents the fused, emission-free `source`, if selection recorded
    /// one (see [`Self::source_fusion_targets`]).
    pub fn source_fusion_target(&self, source: SourceInstId) -> Option<SourceInstId> {
        self.source_fusion_targets.get(&source).copied()
    }

    /// TV-1: per-opcode stamping-coverage report over all block-linked
    /// instructions (the TV-2 absent-provenance flip's measurement artifact).
    pub fn lowering_provenance_coverage(&self) -> LoweringProvenanceCoverage {
        let mut coverage = LoweringProvenanceCoverage::default();
        for &block_id in &self.block_order {
            for &inst_id in &self.blocks[block_id.0 as usize].insts {
                let provenance = self.inst_lowering_provenance(inst_id);
                let mnemonic = format!("{:?}", self.insts[inst_id.0 as usize].opcode);
                coverage.record(&mnemonic, &provenance);
            }
        }
        coverage
    }

    /// Get an instruction by ID.
    pub fn inst(&self, id: InstId) -> &MachInst {
        &self.insts[id.0 as usize]
    }

    /// Get a mutable instruction by ID.
    pub fn inst_mut(&mut self, id: InstId) -> &mut MachInst {
        &mut self.insts[id.0 as usize]
    }

    /// Get a block by ID.
    pub fn block(&self, id: BlockId) -> &MachBlock {
        &self.blocks[id.0 as usize]
    }

    /// Get a mutable block by ID.
    pub fn block_mut(&mut self, id: BlockId) -> &mut MachBlock {
        &mut self.blocks[id.0 as usize]
    }

    /// Returns the total number of instructions.
    pub fn num_insts(&self) -> usize {
        self.insts.len()
    }

    /// Returns the total number of blocks.
    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    /// Add a CFG edge from `from` to `to`.
    pub fn add_edge(&mut self, from: BlockId, to: BlockId) {
        self.blocks[from.0 as usize].succs.push(to);
        self.blocks[to.0 as usize].preds.push(from);
    }
}

#[cfg(test)]
mod tests {

    /// The array spelling of a uniform aggregate MUST index identically to the
    /// struct spelling -- `memory_slot_lane_ty` in the rustc bridge emits
    /// `Array(lane, n)` where it used to emit `Tuple([lane; n])`, and every
    /// `StructGep` resolves the element offset through `offset_of`.
    ///
    /// This is a REGRESSION test for a real wrong-code bug: `offset_of` returned
    /// `None` for arrays while both `select_struct_gep` implementations do
    /// `.unwrap_or(0)`, so every element resolved to offset 0 and an sret
    /// aggregate return read the wrong lanes. It survived the 18-program
    /// byte-identity corpus and was caught only by `shape-coverage`.
    ///
    /// `offset_of` is implemented TWICE -- here and in
    /// `trust_cg_ir::function::Type` -- so both are pinned.
    #[test]
    fn array_indexes_identically_to_the_uniform_struct_spelling() {
        for lane in [Type::I8, Type::I16, Type::I32, Type::I64, Type::I128] {
            for n in [1usize, 2, 3, 12, 64] {
                let array = Type::Array(Box::new(lane.clone()), n as u32);
                let structure = Type::Struct(vec![lane.clone(); n]);
                assert_eq!(
                    array.bytes(),
                    structure.bytes(),
                    "size mismatch for [{lane:?}; {n}]"
                );
                assert_eq!(
                    array.align(),
                    structure.align(),
                    "align mismatch for [{lane:?}; {n}]"
                );
                for k in 0..n {
                    assert_eq!(
                        array.offset_of(k),
                        structure.offset_of(k),
                        "offset mismatch at element {k} of [{lane:?}; {n}]"
                    );
                }
                assert_eq!(
                    array.offset_of(n),
                    None,
                    "out-of-range element must be None for [{lane:?}; {n}]"
                );
            }
        }
    }
    use super::*;
    use crate::inst::{AArch64Opcode, MachInst};
    use crate::operand::MachOperand;
    use crate::regs::{RegClass, VReg};
    use crate::types::BlockId;

    // ---- MachBlock tests ----

    #[test]
    fn machblock_new_is_empty() {
        let block = MachBlock::new();
        assert!(block.is_empty());
        assert_eq!(block.len(), 0);
        assert!(block.preds.is_empty());
        assert!(block.succs.is_empty());
    }

    #[test]
    fn machblock_default_is_new() {
        let a = MachBlock::new();
        let b = MachBlock::default();
        assert_eq!(a.is_empty(), b.is_empty());
        assert_eq!(a.len(), b.len());
    }

    #[test]
    fn machblock_add_instructions() {
        let mut block = MachBlock::new();
        block.insts.push(InstId(0));
        assert!(!block.is_empty());
        assert_eq!(block.len(), 1);
        block.insts.push(InstId(1));
        assert_eq!(block.len(), 2);
    }

    #[test]
    fn machblock_predecessors_successors() {
        let mut block = MachBlock::new();
        block.preds.push(BlockId(0));
        block.preds.push(BlockId(1));
        block.succs.push(BlockId(3));
        assert_eq!(block.preds.len(), 2);
        assert_eq!(block.succs.len(), 1);
    }

    // ---- Type tests ----

    #[test]
    fn type_bytes() {
        assert_eq!(Type::I8.bytes(), 1);
        assert_eq!(Type::B1.bytes(), 1);
        assert_eq!(Type::I16.bytes(), 2);
        assert_eq!(Type::F16.bytes(), 2);
        assert_eq!(Type::I32.bytes(), 4);
        assert_eq!(Type::F32.bytes(), 4);
        assert_eq!(Type::I64.bytes(), 8);
        assert_eq!(Type::F64.bytes(), 8);
        assert_eq!(Type::Ptr.bytes(), 8);
        assert_eq!(Type::I128.bytes(), 16);
        assert_eq!(Type::V128.bytes(), 16);
    }

    /// Alignment is `min(bytes, 8)` for everything that fits a
    /// general-purpose register, and 16 for the 128-bit types that do not.
    ///
    /// Every value here is rustc's, (c) MEASURED with stock `rustc 1.97.0` via
    /// `align_of`. The `I128` row used to assert 8 with the comment "capped at
    /// 8"; `align_of::<u128>()` is 16 on every target trust-cg emits for, so
    /// the cap was pinning the defect rather than a rule.
    #[test]
    fn type_align() {
        assert_eq!(Type::I8.align(), 1);
        assert_eq!(Type::B1.align(), 1);
        assert_eq!(Type::I16.align(), 2);
        assert_eq!(Type::F16.align(), 2);
        assert_eq!(Type::I32.align(), 4);
        assert_eq!(Type::F32.align(), 4);
        assert_eq!(Type::I64.align(), 8);
        assert_eq!(Type::F64.align(), 8);
        assert_eq!(Type::Ptr.align(), 8);
        assert_eq!(Type::I128.align(), 16, "rustc: align_of::<u128>() == 16");
        assert_eq!(Type::V128.align(), 16);
    }

    #[test]
    fn type_is_int() {
        assert!(Type::I8.is_int());
        assert!(Type::I16.is_int());
        assert!(Type::I32.is_int());
        assert!(Type::I64.is_int());
        assert!(Type::I128.is_int());
        assert!(!Type::F32.is_int());
        assert!(!Type::F64.is_int());
        assert!(!Type::B1.is_int());
        assert!(!Type::Ptr.is_int());
        assert!(!Type::V128.is_int());
    }

    #[test]
    fn type_is_float() {
        assert!(Type::F16.is_float());
        assert!(Type::F32.is_float());
        assert!(Type::F64.is_float());
        assert!(!Type::I8.is_float());
        assert!(!Type::I32.is_float());
        assert!(!Type::I64.is_float());
        assert!(!Type::B1.is_float());
        assert!(!Type::Ptr.is_float());
        assert!(!Type::V128.is_float());
    }

    #[test]
    fn type_v128_is_a_distinct_vector_with_vector_layout() {
        assert!(Type::V128.is_vector());
        assert!(!Type::I128.is_vector());
        assert_ne!(Type::V128, Type::I128);

        let vector_struct = Type::Struct(vec![Type::I8, Type::V128]);
        assert_eq!(vector_struct.offset_of(1), Some(16));
        assert_eq!(vector_struct.align(), 16);
        assert_eq!(vector_struct.bytes(), 32);

        // `V128` and `I128` are distinct TYPES with distinct opcode behaviour,
        // but they share a LAYOUT: both are 16 bytes, 16-aligned. (c) MEASURED,
        // `#[repr(C)] { a: u8, b: u128 }` is size 32, align 16, `b@16` — the
        // same triple this asserts for the vector case above. These three used
        // to assert (8, 8, 24), the natural consequence of the `min(8)` cap.
        let integer_struct = Type::Struct(vec![Type::I8, Type::I128]);
        assert_eq!(integer_struct.offset_of(1), Some(16));
        assert_eq!(integer_struct.align(), 16);
        assert_eq!(integer_struct.bytes(), 32);
    }

    #[test]
    fn type_v64_preserves_vector_identity_layout_and_register_class() {
        use crate::regs::RegClass;

        assert!(Type::V64.is_vector());
        assert!(!Type::V64.is_int());
        assert!(!Type::V64.is_float());
        assert!(!Type::I64.is_vector());
        assert_ne!(Type::V64, Type::I64);
        assert_ne!(Type::V64, Type::F64);
        assert_ne!(Type::V64, Type::V128);
        assert_eq!(Type::V64.bytes(), 8);
        assert_eq!(Type::V64.align(), 8);
        assert_eq!(RegClass::for_type(&Type::V64), RegClass::Fpr64);
        assert_eq!(RegClass::for_type(&Type::I64), RegClass::Gpr64);

        let structure = Type::Struct(vec![Type::I8, Type::V64, Type::I8]);
        assert_eq!(structure.offset_of(1), Some(8));
        assert_eq!(structure.offset_of(2), Some(16));
        assert_eq!(structure.align(), 8);
        assert_eq!(structure.bytes(), 24);

        let array = Type::Array(Box::new(Type::V64), 3);
        assert_eq!(array.offset_of(2), Some(16));
        assert_eq!(array.align(), 8);
        assert_eq!(array.bytes(), 24);
    }

    #[test]
    fn type_b1_is_neither_int_nor_float() {
        assert!(!Type::B1.is_int());
        assert!(!Type::B1.is_float());
    }

    #[test]
    fn type_ptr_is_neither_int_nor_float() {
        assert!(!Type::Ptr.is_int());
        assert!(!Type::Ptr.is_float());
    }

    #[test]
    fn type_equality() {
        assert_eq!(Type::I32, Type::I32);
        assert_ne!(Type::I32, Type::I64);
        assert_ne!(Type::I32, Type::F32);
    }

    #[test]
    fn type_clone_hash() {
        use std::hash::{Hash, Hasher};

        #[derive(Default)]
        struct StableTestHasher(u64);

        impl Hasher for StableTestHasher {
            fn write(&mut self, bytes: &[u8]) {
                for &byte in bytes {
                    self.0 = self.0.wrapping_mul(16_777_619) ^ u64::from(byte);
                }
            }

            fn finish(&self) -> u64 {
                self.0
            }
        }

        fn hash_value<T: Hash>(value: &T) -> u64 {
            let mut hasher = StableTestHasher::default();
            value.hash(&mut hasher);
            hasher.finish()
        }

        let a = Type::I64;
        let b = a.clone(); // Clone
        let c = a.clone(); // Clone
        assert_eq!(a, b);
        assert_eq!(a, c);

        assert_eq!(hash_value(&Type::I32), hash_value(&Type::I32));
        assert_ne!(hash_value(&Type::I32), hash_value(&Type::I64));
        assert_ne!(
            hash_value(&Type::V128),
            hash_value(&Type::I128),
            "machine-IR type fingerprints must not collapse vector and integer carriers",
        );
        assert_ne!(hash_value(&Type::V64), hash_value(&Type::I64));
        assert_ne!(hash_value(&Type::V64), hash_value(&Type::F64));
        assert_ne!(hash_value(&Type::V64), hash_value(&Type::V128));
    }

    // ---- Signature tests ----

    #[test]
    fn signature_creation() {
        let sig = Signature::new(vec![Type::I64, Type::I32], vec![Type::I64]);
        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.returns.len(), 1);
        assert_eq!(sig.params[0], Type::I64);
        assert_eq!(sig.params[1], Type::I32);
        assert_eq!(sig.returns[0], Type::I64);
    }

    #[test]
    fn signature_empty() {
        let sig = Signature::new(vec![], vec![]);
        assert!(sig.params.is_empty());
        assert!(sig.returns.is_empty());
    }

    #[test]
    fn signature_equality() {
        let a = Signature::new(vec![Type::I64], vec![Type::I32]);
        let b = Signature::new(vec![Type::I64], vec![Type::I32]);
        let c = Signature::new(vec![Type::I32], vec![Type::I32]);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    // ---- StackSlot tests ----

    #[test]
    fn stack_slot_creation() {
        let slot = StackSlot::new(8, 8);
        assert_eq!(slot.size, 8);
        assert_eq!(slot.align, 8);
        assert!(slot.is_fixed_size());
        assert_eq!(slot.allocation, StackSlotAllocationKind::Fixed);
        assert_eq!(slot.size_source(), None);
        assert_eq!(slot.fixed_size(), Some(8));
    }

    #[test]
    fn stack_slot_various_sizes() {
        let slot1 = StackSlot::new(1, 1);
        assert_eq!(slot1.size, 1);
        assert_eq!(slot1.align, 1);
        assert!(slot1.is_fixed_size());

        let slot16 = StackSlot::new(16, 16);
        assert_eq!(slot16.size, 16);
        assert_eq!(slot16.align, 16);
        assert!(slot16.is_fixed_size());

        let slot_mixed = StackSlot::new(12, 4);
        assert_eq!(slot_mixed.size, 12);
        assert_eq!(slot_mixed.align, 4);
        assert!(slot_mixed.is_fixed_size());
    }

    #[test]
    fn stack_slot_runtime_sized() {
        let slot = StackSlot::new_dynamic(StackSlotSizeSource::Value(7), 16);
        assert_eq!(slot.size, 0);
        assert_eq!(slot.align, 16);
        assert!(slot.is_runtime_sized());
        assert_eq!(slot.size_source(), Some(StackSlotSizeSource::Value(7)));
        assert_eq!(slot.fixed_size(), None);

        let fallback_slot = StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 8);
        assert_eq!(fallback_slot.size, 0);
        assert_eq!(fallback_slot.align, 8);
        assert!(fallback_slot.is_runtime_sized());
        assert_eq!(
            fallback_slot.size_source(),
            Some(StackSlotSizeSource::Unknown)
        );
    }

    #[test]
    fn stack_slot_equality() {
        let a = StackSlot::new(8, 8);
        let b = StackSlot::new(8, 8);
        let c = StackSlot::new(8, 4);
        assert_eq!(a, b);
        assert_ne!(a, c);

        let a_dyn = StackSlot::new_dynamic(StackSlotSizeSource::Value(1), 8);
        let b_dyn = StackSlot::new_dynamic(StackSlotSizeSource::Value(1), 8);
        let c_dyn = StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 8);
        assert_eq!(a_dyn, b_dyn);
        assert_ne!(a_dyn, c_dyn);
    }

    #[test]
    #[should_panic(expected = "alignment must be power of 2")]
    fn stack_slot_non_power_of_two_panics() {
        let _ = StackSlot::new(8, 3);
    }

    #[test]
    #[should_panic(expected = "alignment must be power of 2")]
    fn stack_slot_zero_alignment_panics() {
        let _ = StackSlot::new(8, 0);
    }

    /// Covers the promoted (always-on) `unit_size > 0` assert in
    /// `new_dynamic_with_unit`. Must panic in BOTH profiles: run under
    /// `scripts/trust_cargo.sh test` and `scripts/trust_cargo.sh test --release`
    /// — a regression back to `debug_assert!` fails the release-profile run.
    #[test]
    #[should_panic(expected = "runtime slot unit size must be non-zero")]
    fn stack_slot_dynamic_zero_unit_size_panics() {
        let _ = StackSlot::new_dynamic_with_unit(StackSlotSizeSource::Value(1), 0, 8);
    }

    // ---- MachFunction tests ----

    #[test]
    fn machfunction_new_has_entry_block() {
        let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
        let func = MachFunction::new("test_fn".to_string(), sig);
        assert_eq!(func.name, "test_fn");
        assert_eq!(func.num_blocks(), 1); // entry block
        assert_eq!(func.entry, BlockId(0));
        assert_eq!(func.num_insts(), 0);
        assert_eq!(func.next_vreg, 0);
        assert!(func.stack_slots.is_empty());
        assert_eq!(func.block_order.len(), 1);
        assert_eq!(func.block_order[0], BlockId(0));
    }

    #[test]
    fn machfunction_alloc_vreg() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);
        assert_eq!(func.alloc_vreg(), 0);
        assert_eq!(func.alloc_vreg(), 1);
        assert_eq!(func.alloc_vreg(), 2);
        assert_eq!(func.next_vreg, 3);
    }

    #[test]
    fn machfunction_try_alloc_vreg_ordinary_ids() {
        let mut func = MachFunction::new("f".into(), Signature::new(vec![], vec![]));
        assert_eq!(func.try_alloc_vreg(), Some(0));
        assert_eq!(func.try_alloc_vreg(), Some(1));
        assert_eq!(func.try_alloc_vreg(), Some(2));
        assert_eq!(func.next_vreg, 3);
    }

    #[test]
    fn machfunction_try_alloc_vreg_exhaustion_is_stable() {
        let mut func = MachFunction::new("f".into(), Signature::new(vec![], vec![]));
        func.next_vreg = u32::MAX - 1;
        assert_eq!(func.try_alloc_vreg(), Some(u32::MAX - 1));
        assert_eq!(func.next_vreg, u32::MAX);
        for _ in 0..3 {
            assert_eq!(func.try_alloc_vreg(), None);
            assert_eq!(func.next_vreg, u32::MAX);
        }
    }

    #[test]
    fn machfunction_checked_sync_jumps_sparse_detached_and_noalias_ids() {
        let mut func = MachFunction::new("sparse".into(), Signature::new(vec![], vec![]));
        let detached = MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(VReg::new(1_000_000_000, RegClass::Gpr64))],
        );
        func.insts.push(detached);
        func.noalias_params.push(1_000_000_007);
        func.next_vreg = 3;
        assert_eq!(func.try_sync_vreg_counter(), Some(()));
        assert_eq!(func.next_vreg, 1_000_000_008);
        assert_eq!(func.try_alloc_vreg(), Some(1_000_000_008));
        assert_eq!(func.try_sync_vreg_counter(), Some(()));
        assert_eq!(
            func.next_vreg, 1_000_000_009,
            "synchronization must not rewind reserved IDs"
        );
    }

    #[test]
    fn machfunction_checked_sync_preserves_empty_and_exhausted_state() {
        let mut func = MachFunction::new("bounded".into(), Signature::new(vec![], vec![]));
        func.next_vreg = 17;
        assert_eq!(func.try_sync_vreg_counter(), Some(()));
        assert_eq!(func.next_vreg, 17);
        func.noalias_params.push(u32::MAX);
        let before = format!("{func:?}");
        for _ in 0..3 {
            assert_eq!(func.try_sync_vreg_counter(), None);
            assert_eq!(format!("{func:?}"), before);
        }
        func.noalias_params[0] = u32::MAX - 1;
        assert_eq!(func.try_sync_vreg_counter(), Some(()));
        assert_eq!(func.next_vreg, u32::MAX);
        assert_eq!(func.try_alloc_vreg(), None);
    }

    #[test]
    fn machfunction_checked_sync_rejects_maximum_arena_operand() {
        let mut func = MachFunction::new("operand".into(), Signature::new(vec![], vec![]));
        func.insts.push(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(VReg::new(u32::MAX, RegClass::Gpr64))],
        ));
        let before = format!("{func:?}");
        assert_eq!(func.try_sync_vreg_counter(), None);
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn machfunction_checked_block_and_slot_allocation_preserves_order() {
        let mut func = MachFunction::new("arenas".into(), Signature::new(vec![], vec![]));
        assert_eq!(func.try_create_block(), Some(BlockId(1)));
        assert_eq!(func.try_create_block(), Some(BlockId(2)));
        assert_eq!(func.block_order, [BlockId(0), BlockId(1), BlockId(2)]);
        assert_eq!(func.blocks.len(), 3);
        let a = StackSlot::new(8, 8);
        let b = StackSlot::new(16, 16);
        assert_eq!(func.try_alloc_stack_slot(a), Some(StackSlotId(0)));
        assert_eq!(func.try_alloc_stack_slot(b), Some(StackSlotId(1)));
        assert_eq!(func.stack_slots, [a, b]);
    }

    #[test]
    fn machfunction_checked_block_and_slot_indices_cannot_narrow() {
        assert_eq!(
            MachFunction::checked_block_id(u32::MAX as usize),
            Some(BlockId(u32::MAX))
        );
        assert_eq!(
            MachFunction::checked_stack_slot_id(u32::MAX as usize),
            Some(StackSlotId(u32::MAX))
        );
        // Test the exact projection without attempting multi-billion-entry arenas.
        if let Some(overflow) = (u32::MAX as usize).checked_add(1) {
            for index in [overflow, usize::MAX] {
                assert_eq!(MachFunction::checked_block_id(index), None);
                assert_eq!(MachFunction::checked_stack_slot_id(index), None);
            }
        }
    }

    #[test]
    fn machfunction_push_inst() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);
        let inst = MachInst::new(AArch64Opcode::Nop, vec![]);
        let id = func.push_inst(inst);
        assert_eq!(id, InstId(0));
        assert_eq!(func.num_insts(), 1);

        let inst2 = MachInst::new(AArch64Opcode::Ret, vec![]);
        let id2 = func.push_inst(inst2);
        assert_eq!(id2, InstId(1));
        assert_eq!(func.num_insts(), 2);
    }

    #[test]
    fn machfunction_try_push_inst_preserves_ordinary_order() {
        let mut function =
            MachFunction::new("checked_arena".into(), Signature::new(vec![], vec![]));
        assert_eq!(
            function.try_push_inst(MachInst::new(AArch64Opcode::Nop, vec![])),
            Some(InstId(0))
        );
        assert_eq!(
            function.try_push_inst(MachInst::new(AArch64Opcode::Ret, vec![])),
            Some(InstId(1))
        );
        assert_eq!(
            function
                .insts
                .iter()
                .map(|inst| inst.opcode)
                .collect::<Vec<_>>(),
            [AArch64Opcode::Nop, AArch64Opcode::Ret]
        );
    }

    #[test]
    fn machfunction_checked_inst_id_accepts_last_index_and_rejects_narrowing() {
        assert_eq!(
            MachFunction::checked_inst_id(u32::MAX as usize),
            Some(InstId(u32::MAX))
        );
        if let Some(overflow) = (u32::MAX as usize).checked_add(1) {
            assert_eq!(MachFunction::checked_inst_id(overflow), None);
            assert_eq!(MachFunction::checked_inst_id(usize::MAX), None);
        }
    }

    #[test]
    fn machfunction_create_block() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);
        assert_eq!(func.num_blocks(), 1); // entry

        let bb1 = func.create_block();
        assert_eq!(bb1, BlockId(1));
        assert_eq!(func.num_blocks(), 2);

        let bb2 = func.create_block();
        assert_eq!(bb2, BlockId(2));
        assert_eq!(func.num_blocks(), 3);

        // Block order should include all blocks
        assert_eq!(func.block_order.len(), 3);
    }

    #[test]
    fn machfunction_append_inst() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);
        let inst_id = func.push_inst(MachInst::new(AArch64Opcode::Nop, vec![]));
        func.append_inst(BlockId(0), inst_id);

        let block = func.block(BlockId(0));
        assert_eq!(block.len(), 1);
        assert_eq!(block.insts[0], inst_id);
    }

    #[test]
    fn machfunction_alloc_stack_slot() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);
        let ss0 = func.alloc_stack_slot(StackSlot::new(8, 8));
        assert_eq!(ss0, crate::types::StackSlotId(0));
        let ss1 = func.alloc_stack_slot(StackSlot::new(16, 16));
        assert_eq!(ss1, crate::types::StackSlotId(1));
        assert_eq!(func.stack_slots.len(), 2);
    }

    #[test]
    fn machfunction_inst_access() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);
        let id = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![MachOperand::Imm(42)],
        ));

        let inst = func.inst(id);
        assert_eq!(inst.opcode, AArch64Opcode::AddRR);
        assert_eq!(inst.operands.len(), 1);

        // Mutable access
        let inst_mut = func.inst_mut(id);
        inst_mut.operands.push(MachOperand::Imm(99));
        assert_eq!(func.inst(id).operands.len(), 2);
    }

    #[test]
    fn machfunction_block_access() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);

        let block = func.block(BlockId(0));
        assert!(block.is_empty());

        // Mutable access
        let block_mut = func.block_mut(BlockId(0));
        block_mut.preds.push(BlockId(1));
        assert_eq!(func.block(BlockId(0)).preds.len(), 1);
    }

    #[test]
    fn machfunction_add_edge() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);
        let bb1 = func.create_block();

        func.add_edge(BlockId(0), bb1);

        assert_eq!(func.block(BlockId(0)).succs.len(), 1);
        assert_eq!(func.block(BlockId(0)).succs[0], bb1);
        assert_eq!(func.block(bb1).preds.len(), 1);
        assert_eq!(func.block(bb1).preds[0], BlockId(0));
    }

    #[test]
    fn machfunction_add_multiple_edges() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("f".to_string(), sig);
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        // bb0 -> bb1, bb0 -> bb2 (conditional branch)
        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);

        assert_eq!(func.block(BlockId(0)).succs.len(), 2);
        assert_eq!(func.block(bb1).preds.len(), 1);
        assert_eq!(func.block(bb2).preds.len(), 1);
    }

    #[test]
    fn machfunction_diamond_cfg() {
        // bb0 -> bb1, bb0 -> bb2, bb1 -> bb3, bb2 -> bb3
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("diamond".to_string(), sig);
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        assert_eq!(func.block(BlockId(0)).succs.len(), 2);
        assert_eq!(func.block(bb3).preds.len(), 2);
        assert_eq!(func.num_blocks(), 4);
    }

    #[test]
    fn machfunction_full_workflow() {
        // Build a simple function: entry block with an add and a return
        let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
        let mut func = MachFunction::new("add_two".to_string(), sig);

        // Allocate virtual registers
        let v0 = func.alloc_vreg();
        let v1 = func.alloc_vreg();
        let v2 = func.alloc_vreg();
        assert_eq!(v0, 0);
        assert_eq!(v1, 1);
        assert_eq!(v2, 2);

        // Create instructions
        let add_id = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(crate::regs::VReg::new(v2, crate::regs::RegClass::Gpr64)),
                MachOperand::VReg(crate::regs::VReg::new(v0, crate::regs::RegClass::Gpr64)),
                MachOperand::VReg(crate::regs::VReg::new(v1, crate::regs::RegClass::Gpr64)),
            ],
        ));
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));

        // Append to entry block
        func.append_inst(BlockId(0), add_id);
        func.append_inst(BlockId(0), ret_id);

        // Allocate a stack slot
        let ss = func.alloc_stack_slot(StackSlot::new(8, 8));

        // Verify
        assert_eq!(func.num_insts(), 2);
        assert_eq!(func.num_blocks(), 1);
        assert_eq!(func.block(BlockId(0)).len(), 2);
        assert_eq!(func.next_vreg, 3);
        assert_eq!(func.stack_slots.len(), 1);
        assert!(!func.inst(add_id).is_return());
        assert!(func.inst(ret_id).is_return());
        assert_eq!(ss, crate::types::StackSlotId(0));
    }

    // ---- EhTypeTable tests ----

    #[test]
    fn eh_type_table_splat_is_constant_size_whatever_its_length() {
        for len in [2u64, 3, 1 << 20, 1 << 40, u64::MAX] {
            let table = EhTypeTable::splat("_ZTIi".to_string(), len);
            assert_eq!(table.len(), len);
            assert!(!table.is_empty());
            assert_eq!(table.get(0), Some("_ZTIi"));
            assert_eq!(table.get(len - 1), Some("_ZTIi"));
            assert_eq!(table.get(len), None);
            assert_eq!(table.symbol_for_catch_index(0), None);
            assert_eq!(table.symbol_for_catch_index(1), Some("_ZTIi"));
            assert_eq!(
                table.entries(),
                EhTypeTableEntries::Splat {
                    symbol: "_ZTIi",
                    len
                }
            );
            // A clone shares the one symbol; it copies no entry.
            assert!(table.clone().shares_storage_with(&table));
            assert!(!EhTypeTable::splat("_ZTIi".to_string(), len).shares_storage_with(&table));
        }
    }

    #[test]
    fn eh_type_table_spelling_is_canonical() {
        assert!(EhTypeTable::splat("_ZTIi".to_string(), 0).is_empty());
        assert_eq!(EhTypeTable::from_symbols(Vec::new()), EhTypeTable::new());
        let one = EhTypeTable::splat("_ZTIi".to_string(), 1);
        assert_eq!(one, EhTypeTable::from_symbols(vec!["_ZTIi".to_string()]));
        assert_eq!(
            one.entries(),
            EhTypeTableEntries::List(&["_ZTIi".to_string()])
        );
        let equal = EhTypeTable::from_symbols(vec!["_ZTIi".to_string(); 3]);
        assert_eq!(equal, EhTypeTable::splat("_ZTIi".to_string(), 3));
        let mixed = EhTypeTable::from_symbols(vec!["_ZTIi".to_string(), "_ZTId".to_string()]);
        assert_eq!(mixed.len(), 2);
        assert_eq!(mixed.get(1), Some("_ZTId"));
        assert_eq!(mixed.get(2), None);
        assert_eq!(mixed.symbol_for_catch_index(2), Some("_ZTId"));
        assert_ne!(mixed, equal);
    }

    #[test]
    fn eh_type_table_serde_keeps_the_list_spelling_and_the_splat_small() {
        let list = EhTypeTable::from_symbols(vec!["_ZTIi".to_string(), "_ZTId".to_string()]);
        let text = serde_json::to_string(&list).unwrap();
        assert_eq!(text, r#"["_ZTIi","_ZTId"]"#);
        assert_eq!(serde_json::from_str::<EhTypeTable>(&text).unwrap(), list);

        let splat = EhTypeTable::splat("_ZTIi".to_string(), 1 << 40);
        let text = serde_json::to_string(&splat).unwrap();
        assert_eq!(text, r#"{"splat":"_ZTIi","len":1099511627776}"#);
        assert_eq!(serde_json::from_str::<EhTypeTable>(&text).unwrap(), splat);
        // A list of equal entries deserializes to the canonical splat.
        assert_eq!(
            serde_json::from_str::<EhTypeTable>(r#"["_ZTIi","_ZTIi"]"#).unwrap(),
            EhTypeTable::splat("_ZTIi".to_string(), 2)
        );
    }

    // ---- ExceptionHandlingMetadata tests ----

    #[test]
    fn eh_metadata_default_is_empty() {
        let eh = ExceptionHandlingMetadata::new();
        assert!(!eh.has_eh_info());
        assert!(eh.personality.is_none());
        assert!(eh.landing_pads.is_empty());
        assert!(eh.call_sites.is_empty());
    }

    #[test]
    fn eh_metadata_has_eh_info_with_personality() {
        let mut eh = ExceptionHandlingMetadata::new();
        eh.personality = Some("__gxx_personality_v0".to_string());
        assert!(eh.has_eh_info());
    }

    #[test]
    fn eh_metadata_has_eh_info_with_landing_pad() {
        let mut eh = ExceptionHandlingMetadata::new();
        eh.add_landing_pad(LandingPadEntry {
            block: BlockId(1),
            offset: 0x40,
            catch_type_indices: vec![1],
            is_cleanup: false,
        });
        assert!(eh.has_eh_info());
    }

    #[test]
    fn eh_metadata_has_eh_info_with_call_site_alone() {
        let mut eh = ExceptionHandlingMetadata::new();
        eh.add_call_site(EhCallSiteEntry {
            call_block: BlockId(0),
            start_offset: 0,
            length: 0,
            landing_pad_block: None,
        });
        assert!(
            eh.has_eh_info(),
            "call-site metadata must enter the EH validation/emission path"
        );
    }

    #[test]
    fn eh_metadata_add_call_site() {
        let mut eh = ExceptionHandlingMetadata::new();
        eh.add_call_site(EhCallSiteEntry {
            call_block: BlockId(0),
            start_offset: 0x10,
            length: 0x08,
            landing_pad_block: Some(BlockId(1)),
        });
        assert_eq!(eh.call_sites.len(), 1);
        assert_eq!(eh.call_sites[0].start_offset, 0x10);
    }

    #[test]
    fn machfunction_has_default_eh_metadata() {
        let func = MachFunction::new("test".to_string(), Signature::new(vec![], vec![]));
        assert!(!func.eh_metadata.has_eh_info());
    }

    #[test]
    fn machfunction_eh_metadata_roundtrip() {
        let mut func = MachFunction::new(
            "with_eh".to_string(),
            Signature::new(vec![Type::I64], vec![Type::I64]),
        );

        func.eh_metadata.personality = Some("rust_eh_personality".to_string());
        func.eh_metadata.add_landing_pad(LandingPadEntry {
            block: BlockId(1),
            offset: 0x80,
            catch_type_indices: Vec::new(),
            is_cleanup: true,
        });
        func.eh_metadata.add_call_site(EhCallSiteEntry {
            call_block: BlockId(0),
            start_offset: 0,
            length: 0x20,
            landing_pad_block: Some(BlockId(1)),
        });

        assert!(func.eh_metadata.has_eh_info());
        assert_eq!(
            func.eh_metadata.personality.as_deref(),
            Some("rust_eh_personality")
        );
        assert_eq!(func.eh_metadata.landing_pads.len(), 1);
        assert!(func.eh_metadata.landing_pads[0].is_cleanup);
        assert_eq!(func.eh_metadata.call_sites.len(), 1);
    }

    // --- FunctionDebugMeta tests ---

    #[test]
    fn test_debug_meta_default() {
        let meta = FunctionDebugMeta::default();
        assert!(meta.source_file.is_none());
        assert_eq!(meta.decl_line, 0);
        assert!(meta.param_names.is_empty());
        assert!(meta.local_variables.is_empty());
        assert!(meta.struct_types.is_empty());
        assert!(meta.enum_types.is_empty());
    }

    #[test]
    fn test_debug_meta_on_mach_function() {
        let mut func = MachFunction::new("test_func".to_string(), Signature::new(vec![], vec![]));
        func.debug_meta = FunctionDebugMeta {
            source_file: Some("main.rs".to_string()),
            display_name: None,
            decl_line: 42,
            param_names: vec!["arg0".to_string(), "arg1".to_string()],
            local_variables: vec![],
            struct_types: vec![],
            enum_types: vec![],
        };
        assert_eq!(func.debug_meta.source_file.as_deref(), Some("main.rs"));
        assert_eq!(func.debug_meta.decl_line, 42);
        assert_eq!(func.debug_meta.param_names.len(), 2);
    }

    #[test]
    fn test_debug_meta_constant_int_local_storage() {
        let mut func = MachFunction::new("test_func".to_string(), Signature::new(vec![], vec![]));
        func.debug_meta.local_variables.push(DebugLocalVariable {
            name: "folded".to_string(),
            ty: DebugBaseType::U32,
            storage: DebugVariableStorage::ConstantInt(42),
            decl_line: 7,
        });

        assert_eq!(
            func.debug_meta.local_variables[0].storage,
            DebugVariableStorage::ConstantInt(42)
        );
    }

    #[test]
    fn test_debug_meta_provenance_var_local_storage() {
        let mut func = MachFunction::new("test_func".to_string(), Signature::new(vec![], vec![]));
        func.debug_meta.local_variables.push(DebugLocalVariable {
            name: "tracked".to_string(),
            ty: DebugBaseType::U64,
            storage: DebugVariableStorage::ProvenanceVar(TrustIrVarId(7)),
            decl_line: 11,
        });

        assert_eq!(
            func.debug_meta.local_variables[0].storage,
            DebugVariableStorage::ProvenanceVar(TrustIrVarId(7))
        );
    }
}
