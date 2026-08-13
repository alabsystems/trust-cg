// trust-cg-ir - Shared machine IR model
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Machine-level function and block types.
//!
//! Storage model: arena-based Vec indexed by typed wrappers.
//! No HashMap for blocks/values — Vec + index only (cache-friendly).

use crate::inst::{MachInst, ProofAnnotation};
use crate::provenance::{LoweringProvenance, LoweringProvenanceCoverage, TrustIrVarId};
use crate::types::{BlockId, InstId, StackSlotId};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

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
/// Scalar types (I8..I128, F16..F64, B1, Ptr), the V128 SIMD vector type, and
/// aggregate types used by machine-level function signatures and stack slots.
/// V128 is intentionally distinct from I128: they have the same storage width,
/// but different ABI and register-class semantics.
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
            Self::I64 | Self::F64 | Self::Ptr => 8,
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
        matches!(self, Self::V128)
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
}

impl ExceptionHandlingMetadata {
    /// Create a new empty EH metadata.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns true if this function has exception handling metadata.
    pub fn has_eh_info(&self) -> bool {
        self.personality.is_some() || !self.landing_pads.is_empty() || !self.call_sites.is_empty()
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
    /// Jump tables for switch lowering. Each `Adr` instruction that loads
    /// a jump table base address carries a
    /// [`MachOperand::JumpTableIndex`](crate::operand::MachOperand::JumpTableIndex)
    /// referencing an entry in this vector. The codegen pipeline appends
    /// the table entries after the function body and patches the `Adr`
    /// with the correct PC-relative byte offset.
    pub jump_tables: Vec<JumpTableData>,
    /// Virtual-register ids of pointer parameters marked `noalias` in trust_ir.
    ///
    /// Populated by the compilation pipeline (`apply_proof_annotations`) from the
    /// adapter's [`ProofContext`] param-noalias set, resolved through the ISel
    /// value map to the machine vreg that carries each noalias pointer parameter.
    /// Empty for functions with no noalias pointer parameters (the default) and
    /// for any construction path that does not thread param attributes.
    ///
    /// SOUNDNESS: a value in this list is a *distinct* formal-argument pointer
    /// that trust_ir proved does not alias any other pointer visible to the
    /// callee. Two distinct ids in this list therefore name provably-disjoint
    /// memory regions. The `neon-map` store-vectorizer is the only consumer; it
    /// requires the store base pointer to appear here (and every load base to be
    /// either the identical vreg, in-place, or another entry, disjoint) before it
    /// will vectorize a memory MAP loop. Under-population is safe (the pass merely
    /// BAILS to the scalar loop); over-population would be unsound, so it is only
    /// ever written from a proven trust_ir `noalias` param attribute.
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
            jump_tables: Vec::new(),
            noalias_params: Vec::new(),
            text_align_log2: 2,
            profile_ordered: false,
            lowering_provenance: BTreeMap::new(),
        }
    }

    /// Allocate a new virtual register ID.
    pub fn alloc_vreg(&mut self) -> u32 {
        let id = self.next_vreg;
        self.next_vreg += 1;
        id
    }

    /// Add an instruction to the arena and return its InstId.
    pub fn push_inst(&mut self, inst: MachInst) -> InstId {
        let id = InstId(self.insts.len() as u32);
        self.insts.push(inst);
        id
    }

    /// Create a new basic block and return its BlockId.
    pub fn create_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(MachBlock::new());
        self.block_order.push(id);
        id
    }

    /// Append an instruction to a block.
    pub fn append_inst(&mut self, block: BlockId, inst_id: InstId) {
        self.blocks[block.0 as usize].insts.push(inst_id);
    }

    /// Add a stack slot and return its ID.
    pub fn alloc_stack_slot(&mut self, slot: StackSlot) -> StackSlotId {
        let id = StackSlotId(self.stack_slots.len() as u32);
        self.stack_slots.push(slot);
        id
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
    use super::*;
    use crate::inst::{AArch64Opcode, MachInst};
    use crate::operand::MachOperand;
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
    /// `cargo test` and `cargo test --release` — a regression back to
    /// `debug_assert!` fails the release-profile run.
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
