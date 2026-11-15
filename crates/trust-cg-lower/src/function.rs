// trust-cg-lower/function.rs - Function representation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Function and basic block representation for Trust Codegen LIR.

#[cfg(test)]
#[path = "function_layout_tests.rs"]
mod layout_tests;

use crate::instructions::{Block, Instruction, Opcode, Value};
use crate::types::Type;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
pub use trust_cg_ir::function::{EhTypeTable, EhTypeTableEntries};
use trust_cg_ir::function::{
    FunctionDebugMeta, StackProtectorMode, StackSlot, StackSlotAllocationKind, StackSlotSizeSource,
};
pub use trust_cg_ir::function::{StackLimitOverflow, StackLimitRequest, StackLimitSource};
use trust_cg_ir::provenance::TrustIrVarId;
use trust_cg_ir::{SourceLoc, TrustIrInstId};

/// A basic block containing a sequence of instructions.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BasicBlock {
    pub params: Vec<(Value, Type)>,
    pub instructions: Vec<Instruction>,
    /// Source locations for each instruction (parallel to `instructions`).
    ///
    /// Populated from trust_ir `SourceSpan` during adapter translation.
    /// Carried through ISel to produce DWARF line number program entries.
    /// When shorter than `instructions`, missing entries are treated as None.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub source_locs: Vec<Option<SourceLoc>>,
}

/// Stack slot metadata for the LIR.
///
/// Tracks size and alignment for each stack allocation emitted by the adapter.
/// Propagated through ISel to the canonical `MachFunction::stack_slots`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct StackSlotInfo {
    /// Fixed size in bytes, or runtime allocation unit size when known.
    pub size: u32,
    /// Alignment in bytes (must be power of 2).
    pub align: u32,
    /// Whether this stack slot has a compile-time size or is runtime-sized.
    #[serde(default)]
    pub allocation: StackSlotAllocationKind,
}

impl StackSlotInfo {
    /// Create fixed-size stack-slot metadata.
    pub fn new(size: u32, align: u32) -> Self {
        Self {
            size,
            align,
            allocation: StackSlotAllocationKind::Fixed,
        }
    }

    /// Create runtime-sized stack-slot metadata.
    pub fn new_dynamic(size_source: StackSlotSizeSource, align: u32) -> Self {
        Self {
            size: 0,
            align,
            allocation: StackSlotAllocationKind::RuntimeSized { size_source },
        }
    }

    /// Create runtime-sized stack-slot metadata with a known per-element size.
    pub fn new_dynamic_with_unit(
        size_source: StackSlotSizeSource,
        unit_size: u32,
        align: u32,
    ) -> Self {
        Self {
            size: unit_size,
            align,
            allocation: StackSlotAllocationKind::RuntimeSized { size_source },
        }
    }

    /// Returns true if this slot must be sized at runtime.
    pub fn is_runtime_sized(&self) -> bool {
        matches!(
            self.allocation,
            StackSlotAllocationKind::RuntimeSized { .. }
        )
    }

    /// Convert to the canonical machine-IR stack-slot representation.
    pub fn to_ir_stack_slot(&self) -> StackSlot {
        match self.allocation {
            StackSlotAllocationKind::Fixed => StackSlot::new(self.size, self.align),
            StackSlotAllocationKind::RuntimeSized { size_source } if self.size > 0 => {
                StackSlot::new_dynamic_with_unit(size_source, self.size, self.align)
            }
            StackSlotAllocationKind::RuntimeSized { size_source } => {
                StackSlot::new_dynamic(size_source, self.align)
            }
        }
    }
}

/// Binding from a source-visible debug provenance variable to the LIR value
/// whose selected VReg carries that source value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct DebugValueBinding {
    pub var_id: TrustIrVarId,
    pub value: Value,
}

/// Original aggregate pointee metadata for a pointer-shaped function parameter.
///
/// The callable ABI still sees the parameter as `Type::I64`; this sidecar keeps
/// the source aggregate shape available to downstream adapter consumers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParamPointeeType {
    pub param_index: u32,
    pub pointee_ty: Type,
}

/// The hidden RETURN-BUFFER pointer parameter of an indirect (`sret`) return.
///
/// Some source ABIs return a by-value aggregate through a buffer the CALLER
/// allocates: the callee receives the buffer's address in a hidden parameter,
/// writes the result through it, and returns no value at all. rustc's Rust ABI
/// does this for every `BackendRepr::Memory` aggregate larger than one pointer
/// (`PassMode::Indirect`), which is why a 9-16 byte struct that the C ABI would
/// return in `x0`/`x1` is NOT returned in registers by a Rust callee.
///
/// The convention is stated STRUCTURALLY in the IR — the signature really does
/// carry the extra pointer parameter and really does return nothing — so a
/// verifier can see it. What the structure cannot state is the REGISTER: AAPCS64
/// reserves `X8` for this pointer, which is not an argument register at all, so
/// an ordinary leading pointer parameter would arrive in `X0` and shift every
/// real argument one register along. This marker is what tells the AArch64
/// selector to bind the parameter from `X8` and to classify the REMAINING
/// parameters as if it were absent.
///
/// System V x86-64 needs no special argument placement: the return-buffer
/// pointer is an ordinary leading integer argument in `RDI`. The marker is
/// still needed to check the declaration and return that address in `RAX`.
///
/// Source of truth: the frontend's own ABI (for the Rust bridge, rustc's
/// `FnAbi`/`PassMode`), carried into trust-ir as `ParamAttrs::sret` and read out
/// by the adapter. Never re-derived from a size rule here.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbiSretParam {
    /// Which signature parameter carries the buffer address. Only `0` (a
    /// LEADING hidden parameter) is lowered; the adapter fails closed on any
    /// other position rather than guess a register for it.
    pub param_index: u32,
}

/// A function in the LIR.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Function {
    pub name: String,
    pub signature: Signature,
    pub blocks: HashMap<Block, BasicBlock>,
    /// Preferred block layout/selection order.
    ///
    /// trust_ir block ids are stable identifiers, not a dominance or layout
    /// ordering. The adapter fills this from the source trust_ir block sequence so
    /// ISel does not have to guess by sorting numeric ids.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub block_order: Vec<Block>,
    /// trust_ir instruction origins parallel to each block's `instructions`.
    ///
    /// This is transient compile-time provenance, populated by the trust_ir
    /// adapter and consumed by codegen proof-citation plumbing. It is skipped
    /// during serde because the canonical persisted provenance lives in
    /// `trust_cg_ir::ProvenanceMap`.
    #[serde(skip)]
    pub trust_ir_origins: HashMap<Block, Vec<Option<TrustIrInstId>>>,
    pub entry_block: Block,
    /// Stack slots allocated during adapter translation.
    ///
    /// Each entry corresponds to a `StackAddr { slot: N }` instruction,
    /// where N is the index into this Vec. Populated by the adapter to
    /// ensure each Alloc/Struct gets a unique slot index.
    pub stack_slots: Vec<StackSlotInfo>,
    /// Type hints for LIR `Value`s whose producing opcode does not carry
    /// enough type information for ISel to infer on its own.
    ///
    /// In particular, `Opcode::Call` and `Opcode::CallIndirect` result
    /// values only get a type if the adapter records it here — otherwise
    /// `InstructionSelector::value_type()` falls back to `Type::I64`,
    /// which silently miscompiles non-I64 callee returns (#381).
    ///
    /// Pipelines seed `InstructionSelector::value_types` from this map
    /// before running `select_block()`.
    pub value_types: HashMap<Value, Type>,
    /// Set of direct-call callee names known to be pure (i.e. the trust_ir
    /// source function carried `ProofAnnotation::Pure`).
    ///
    /// Populated by the adapter when the trust_ir module contains a function
    /// with `ProofAnnotation::Pure` that is reachable via `Inst::Call`.
    /// Pipelines seed `InstructionSelector::pure_callees` from this set so
    /// that ISel can stamp `ProofAnnotation::Pure` onto the emitted `Bl`
    /// MachInst, which SROA consumes for partial-escape reasoning (#456).
    #[serde(default, skip_serializing_if = "HashSet::is_empty")]
    pub pure_callees: HashSet<String>,
    /// Set of direct-call callee names licensed libm-pure by the LLVM importer
    /// (intrinsic-origin math libcalls; see
    /// `adapter::LLVM_LIBM_PURE_FUNCTION_ATTR_TAG`). Pipelines seed
    /// `InstructionSelector::libm_pure_callees` from this set so AArch64 ISel
    /// can stamp `InstFlags::LIBM_PURE_CALL` onto the emitted `Bl` MachInst
    /// (metadata read only by the gated `loop-dead-pure-sink` pass).
    #[serde(default, skip_serializing_if = "HashSet::is_empty")]
    pub libm_pure_callees: HashSet<String>,
    /// Source-level metadata used by codegen DWARF emission.
    #[serde(default)]
    pub debug_meta: FunctionDebugMeta,
    /// Debug value bindings consumed after ISel to recover the actual VReg for
    /// source-spanned value locals.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub debug_value_bindings: Vec<DebugValueBinding>,
    /// Function-level stack-protector lowering requirement.
    #[serde(default)]
    pub stack_protector: StackProtectorMode,
    /// U10 prologue stack-limit requirement decoded from the producer's tags
    /// (`docs/u10-prologue-stack-limit.md`). `None` for every function that
    /// did not request one, and then omitted from the serialized form, so a
    /// non-requesting function serializes and hashes exactly as before.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stack_limit: Option<StackLimitRequest>,
    /// Aggregate pointee types for pointer-shaped ABI parameters.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub param_pointee_types: Vec<ParamPointeeType>,
    /// This function's own hidden return-buffer (`sret`) parameter, if its
    /// source ABI returns by-value through a caller-allocated buffer.
    ///
    /// `None` is the ordinary case: the value comes back in the return
    /// registers. See [`AbiSretParam`] for why the register cannot be inferred
    /// from the signature's shape on AAPCS64.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub abi_sret_param: Option<AbiSretParam>,
    /// Direct-call callee symbols whose ARGUMENT 0 is a hidden return-buffer
    /// (`sret`) pointer.
    ///
    /// The caller half of [`AbiSretParam`]: the buffer address must go in `X8`
    /// on AAPCS64 rather than `X0`, and the remaining arguments must be
    /// classified as if it were absent. Keyed by symbol NAME, which is exact —
    /// a symbol has ONE signature, so every call to it in this function shares
    /// one convention — and follows the existing `pure_callees` channel rather
    /// than inventing a second one. This channel keys DIRECT calls only; the
    /// indirect half is [`Self::sret_arg_indirect_callees`]. The name is not
    /// exact for a routine the backend also calls on its own
    /// ([`crate::RuntimeSymbol`]: `memcpy` for a `Memcpy`, `fmod` for `frem`,
    /// ...), whose call keeps the routine's C convention; the AArch64
    /// selector refuses such an entry (LD-100 rule 11).
    #[serde(default, skip_serializing_if = "HashSet::is_empty")]
    pub sret_arg_callees: HashSet<String>,
    /// Indirect-call callee VALUES whose ARGUMENT 0 is a hidden return-buffer
    /// (`sret`) pointer: the `CallIndirect` half of [`Self::sret_arg_callees`].
    ///
    /// The pinned trust-ir states `sret` only as a per-parameter attribute of
    /// a declared `Function` (`FuncAttrs::params`); a `FuncTy` has no
    /// attribute slot and a `CallIndirect` carries no call-site attributes. So
    /// the adapter records this fact only for a callee value whose provenance
    /// trust-ir's own `StaticFunctionPointerAnalysis` resolves (a `Const FnDef`
    /// reached through `Copy` / `ReifyFnPointer`) to a declaration carrying the
    /// attribute, and it fails closed when that declaration and the call edge
    /// disagree. Keyed by the callee's SSA `Value`, which has one definition
    /// and therefore one denotation, so every call through it shares one
    /// convention. A pointer that flows dynamically (a parameter, a load)
    /// carries no such fact and is lowered as the ordinary call its signature
    /// declares; a producer expresses a dynamically-called hidden result
    /// structurally (`returns: [Struct]`, classified indirect by the target
    /// ABI) so that the function type itself carries the identity.
    #[serde(default, skip_serializing_if = "HashSet::is_empty")]
    pub sret_arg_indirect_callees: HashSet<Value>,
    /// Exception-handling structure, populated by the adapter when the trust_ir
    /// source carries `Inst::Invoke` / `Inst::LandingPad`. ISel forwards this to
    /// `MachFunction.eh_metadata` (as BlockId-level entries); the codegen
    /// pipeline resolves the byte offsets after block layout and emits the LSDA
    /// + compact unwind. Empty for functions without exception handling.
    #[serde(default, skip_serializing_if = "EhFunctionInfo::is_empty")]
    pub eh_info: EhFunctionInfo,
    /// EH type table for this function's typed catches: entry `k - 1` is the
    /// linker-level typeinfo symbol bound to catch type index `k`. The adapter
    /// reads it from the module's reserved [`EH_TYPE_TABLE_GLOBAL`]; like the
    /// personality it is frontend-owned and not part of the structural
    /// Invoke/LandingPad view. Empty unless a landing pad catches a typed
    /// exception.
    ///
    /// A module table spelled `Constant::Splat` stays one symbol and a length
    /// ([`EhTypeTable`]), and every function shares the module's one table.
    #[serde(default, skip_serializing_if = "EhTypeTable::is_empty")]
    pub eh_type_table: EhTypeTable,
    /// The target features this function's source states it may assume
    /// (trust-ir `FuncAttrs.target_features`, rustc spellings), exactly as
    /// the adapter admitted them against its target vocabulary.
    ///
    /// The AArch64 pipeline resolves them to the function's optional ISA
    /// admission (the profile plus these, within the target's function
    /// ceiling) and selects feature instructions only in this function;
    /// every other function keeps the profile's baseline lowering.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub target_features: Vec<String>,
}

/// LIR-level exception-handling structure.
///
/// This is the input-side counterpart of `trust_cg_ir::ExceptionHandlingMetadata`
/// (which references `BlockId` and carries the post-layout byte offsets). The
/// adapter fills it from trust_ir `Invoke` / `LandingPad`; ISel translates it
/// into the MachFunction's `eh_metadata` (still by block, offsets unresolved).
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct EhFunctionInfo {
    /// Linker-level personality routine symbol (e.g. `rust_eh_personality`).
    /// Object writers apply any platform prefix such as Mach-O's `_`.
    pub personality: Option<String>,
    /// Landing pads, keyed by the LIR block that begins with the landing pad.
    pub landing_pads: Vec<EhLandingPad>,
    /// Invoke call sites: which block ends in an invoke, and which landing-pad
    /// block its unwind edge targets.
    pub call_sites: Vec<EhCallSite>,
}

impl EhFunctionInfo {
    /// True when the function carries no exception-handling structure.
    pub fn is_empty(&self) -> bool {
        self.personality.is_none() && self.landing_pads.is_empty() && self.call_sites.is_empty()
    }

    /// Compare the block-keyed EH structure while deliberately ignoring the
    /// personality name and insertion order. The LIR opcode stream owns which
    /// blocks invoke and land; the frontend owns the personality symbol.
    pub fn structurally_matches(&self, other: &Self) -> bool {
        fn calls(info: &EhFunctionInfo) -> Vec<(u32, u32)> {
            let mut entries: Vec<_> = info
                .call_sites
                .iter()
                .map(|site| (site.call_block.0, site.landing_pad_block.0))
                .collect();
            entries.sort_unstable();
            entries
        }

        fn pads(info: &EhFunctionInfo) -> Vec<(u32, Vec<u32>, bool)> {
            let mut entries: Vec<_> = info
                .landing_pads
                .iter()
                .map(|pad| (pad.block.0, pad.catch_type_indices.clone(), pad.is_cleanup))
                .collect();
            entries.sort_by_key(|entry| entry.0);
            entries
        }

        calls(self) == calls(other) && pads(self) == pads(other)
    }
}

/// Name of the reserved trust-ir module global that binds landing-pad catch
/// type indices to typeinfo symbols.
///
/// The pinned trust-ir `Inst::LandingPad` carries only `catch_type_indices`;
/// the compiler defines the binding explicitly: an immutable, non-TLS global
/// of this name whose initializer is a `Constant::Array` (or `Aggregate`) of
/// `Constant::SymbolAddr { symbol, addend: 0 }` entries, where entry `k - 1`
/// names the typeinfo symbol (linker spelling, e.g. `_ZTIi`) of catch type
/// index `k` — or, when every entry names one typeinfo, the trust-ir v50
/// `Constant::Splat` of that entry. The adapter reads it once per module and
/// shares it with every function that catches a typed exception
/// ([`Function::eh_type_table`]; a splat stays one symbol and a length) and
/// refuses an index the table does not bind; the object emitters never emit the table itself. Typed catches
/// are bound only under `__gxx_personality_v0` (a typed catch in a function
/// that unwinds under `rust_eh_personality` is refused). Under that
/// personality the selector a `LandingPad` delivers equals the matched catch
/// type index, and a catch-all match delivers `N + 1` for the `N`-entry table
/// in a function that catches a typed exception (`1` in one that does not);
/// see the codegen `exception_handling` module docs.
pub const EH_TYPE_TABLE_GLOBAL: &str = "__trust_cg_eh_type_table";

/// Compiler extension for an empty exception-specification filter in the
/// pinned trust-ir landing-pad carrier. This value cannot be a positive
/// signed LSDA catch index. It is accepted only as the sole clause of a
/// non-cleanup pad under `rust_eh_personality`, and encodes filter -1 plus an
/// empty filter list. It stops phase-one search, but the Rust personality
/// skips it during forced unwinding. Catch-all (0) does not have that behavior.
/// The adapter, retained LIR identity, and machine EH metadata preserve this
/// exact clause; it is never looked up in the module's typeinfo table.
pub const RUST_EH_EMPTY_FILTER: u32 = u32::MAX;

/// Validate the restricted empty-filter extension before interpreting indices
/// as catch types. Unsupported clause combinations must not become handlers.
pub fn validate_rust_eh_empty_filter(
    indices: &[u32],
    is_cleanup: bool,
    personality: &str,
) -> Result<bool, &'static str> {
    if !indices.contains(&RUST_EH_EMPTY_FILTER) {
        return Ok(false);
    }
    if indices != [RUST_EH_EMPTY_FILTER] || is_cleanup || personality != "rust_eh_personality" {
        return Err(
            "empty exception filter requires a sole clause, no cleanup, and rust_eh_personality [TCG-EH-FILTER]",
        );
    }
    Ok(true)
}

/// A landing-pad block in the LIR (pre-layout; the byte offset is resolved by
/// the codegen pipeline after block layout).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EhLandingPad {
    /// The LIR block that begins with the landing pad.
    pub block: Block,
    /// Type indices this pad catches (0 == catch-all). Empty + `is_cleanup` is
    /// a pure cleanup pad. See [`RUST_EH_EMPTY_FILTER`] for the compiler's
    /// restricted empty-filter extension.
    pub catch_type_indices: Vec<u32>,
    /// True if this pad runs cleanup (Drop glue) without catching.
    pub is_cleanup: bool,
}

/// An invoke call site in the LIR (pre-layout).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EhCallSite {
    /// The LIR block whose terminator is the invoke (the throwing `Bl`).
    pub call_block: Block,
    /// The landing-pad block the unwind edge targets.
    pub landing_pad_block: Block,
}

/// LIR function signature (input-level, uses `trust_cg_lower::Type`).
///
/// Separate from `trust_cg_ir::function::Signature` which uses
/// `trust_cg_ir::function::Type` (includes `Ptr`, no serde). This signature
/// is used by the instruction selector and ABI classifier before
/// lowering to the canonical MachIR representation.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Signature {
    pub params: Vec<Type>,
    pub returns: Vec<Type>,
}

impl Function {
    /// Create a new function with the given name and signature.
    pub fn new(name: impl Into<String>, signature: Signature) -> Self {
        Self {
            name: name.into(),
            signature,
            blocks: HashMap::new(),
            block_order: Vec::new(),
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: Vec::new(),
            value_types: HashMap::new(),
            pure_callees: HashSet::new(),
            libm_pure_callees: HashSet::new(),
            abi_sret_param: None,
            sret_arg_callees: HashSet::new(),
            sret_arg_indirect_callees: HashSet::new(),
            debug_meta: FunctionDebugMeta::default(),
            debug_value_bindings: Vec::new(),
            stack_protector: StackProtectorMode::None,
            stack_limit: None,
            param_pointee_types: Vec::new(),
            eh_info: EhFunctionInfo::default(),
            eh_type_table: EhTypeTable::new(),
            target_features: Vec::new(),
        }
    }

    /// Whether some block of this function, reachable or not, branches to
    /// `entry_block`.
    ///
    /// trust-ir admits a branch to the entry block, so the entry can head a
    /// loop. Its parameters then carry a back edge's arguments as well as the
    /// formal arguments, and code that must run once per call (reading the
    /// incoming ABI registers and stack slots) cannot be placed at its top.
    pub fn entry_block_is_branch_target(&self) -> bool {
        self.blocks
            .values()
            .any(|block| block.successors().contains(&self.entry_block))
    }

    /// Return blocks in a valid selection/layout order.
    ///
    /// trust_ir/source block order is stable, but it is not guaranteed to place a
    /// dominating definition before all dominated uses. Instruction selection
    /// tracks values as it walks blocks, so reachable blocks are always emitted
    /// in CFG reverse postorder from the entry. Any unreachable blocks are
    /// appended deterministically, preferring the adapter-provided order when
    /// present.
    pub fn layout_order(&self) -> Vec<Block> {
        let mut order = Vec::new();
        let mut seen = HashSet::new();

        self.push_rpo(self.entry_block, &mut seen, &mut order);
        order.reverse();

        for &block in &self.block_order {
            if self.blocks.contains_key(&block) && seen.insert(block) {
                order.push(block);
            }
        }
        let mut fallback_remaining: Vec<_> = self
            .blocks
            .keys()
            .copied()
            .filter(|block| !seen.contains(block))
            .collect();
        fallback_remaining.sort_by_key(|block| block.0);
        order.extend(fallback_remaining);

        order
    }

    /// Validate the single canonical LIR exception-handling authority.
    ///
    /// `Invoke` and `LandingPad` opcodes describe executable control flow;
    /// [`EhFunctionInfo`] describes the same edges for LSDA emission. Backends
    /// must not guess when those views disagree: a missing entry strands a
    /// cleanup, while a stale entry can dispatch the unwinder into the wrong
    /// block. This check therefore requires an exact one-to-one structural
    /// match and a nonempty personality for every EH function.
    pub fn validate_eh_structure(&self) -> Result<(), String> {
        let mut opcode_info = EhFunctionInfo::default();
        let mut has_eh_opcode = false;
        let mut invoke_blocks = HashSet::new();
        let mut landing_pad_blocks = HashSet::new();

        for (&block, body) in &self.blocks {
            for (index, inst) in body.instructions.iter().enumerate() {
                match &inst.opcode {
                    Opcode::Invoke {
                        normal_dest,
                        unwind_dest,
                        ..
                    } => {
                        has_eh_opcode = true;
                        if index + 1 != body.instructions.len() {
                            return Err(format!(
                                "function `{}` block {} has Invoke at instruction {index}, but Invoke must terminate the block",
                                self.name, block.0
                            ));
                        }
                        if normal_dest == unwind_dest {
                            return Err(format!(
                                "function `{}` block {} Invoke uses block {} for both normal and unwind control flow; the destinations must be distinct",
                                self.name, block.0, normal_dest.0
                            ));
                        }
                        if !self.blocks.contains_key(normal_dest)
                            || !self.blocks.contains_key(unwind_dest)
                        {
                            return Err(format!(
                                "function `{}` block {} Invoke targets missing normal/unwind block ({}, {})",
                                self.name, block.0, normal_dest.0, unwind_dest.0
                            ));
                        }
                        if !invoke_blocks.insert(block) {
                            return Err(format!(
                                "function `{}` has more than one Invoke in block {}",
                                self.name, block.0
                            ));
                        }
                        opcode_info.call_sites.push(EhCallSite {
                            call_block: block,
                            landing_pad_block: *unwind_dest,
                        });
                    }
                    Opcode::LandingPad {
                        is_cleanup,
                        catch_type_indices,
                    } => {
                        has_eh_opcode = true;
                        if index != 0 {
                            return Err(format!(
                                "function `{}` block {} has LandingPad at instruction {index}; it must be the first instruction",
                                self.name, block.0
                            ));
                        }
                        if !landing_pad_blocks.insert(block) {
                            return Err(format!(
                                "function `{}` has more than one LandingPad in block {}",
                                self.name, block.0
                            ));
                        }
                        opcode_info.landing_pads.push(EhLandingPad {
                            block,
                            catch_type_indices: catch_type_indices.clone(),
                            is_cleanup: *is_cleanup,
                        });
                    }
                    Opcode::Resume => {
                        has_eh_opcode = true;
                        if index + 1 != body.instructions.len() {
                            return Err(format!(
                                "function `{}` block {} has Resume at instruction {index}, but Resume must terminate the block",
                                self.name, block.0
                            ));
                        }
                    }
                    _ => {}
                }
            }
        }

        if !has_eh_opcode {
            if self.eh_info.is_empty() {
                return Ok(());
            }
            return Err(format!(
                "function `{}` carries EH metadata but has no Invoke/LandingPad/Resume opcode",
                self.name
            ));
        }

        if self
            .eh_info
            .personality
            .as_deref()
            .is_none_or(str::is_empty)
        {
            return Err(format!(
                "function `{}` contains EH opcodes but has no personality symbol",
                self.name
            ));
        }

        let mut metadata_call_blocks = HashSet::new();
        for site in &self.eh_info.call_sites {
            if !metadata_call_blocks.insert(site.call_block) {
                return Err(format!(
                    "function `{}` EH metadata duplicates call block {}",
                    self.name, site.call_block.0
                ));
            }
        }
        let mut metadata_pad_blocks = HashSet::new();
        for pad in &self.eh_info.landing_pads {
            if !metadata_pad_blocks.insert(pad.block) {
                return Err(format!(
                    "function `{}` EH metadata duplicates landing-pad block {}",
                    self.name, pad.block.0
                ));
            }
        }

        if !self.eh_info.structurally_matches(&opcode_info) {
            return Err(format!(
                "function `{}` EH sidecar does not exactly match its Invoke/LandingPad opcodes: sidecar={:?}, opcode-derived={:?}",
                self.name, self.eh_info, opcode_info
            ));
        }

        if opcode_info.landing_pads.is_empty() {
            return Err(format!(
                "function `{}` contains EH control flow but has no LandingPad",
                self.name
            ));
        }

        for site in &opcode_info.call_sites {
            if !landing_pad_blocks.contains(&site.landing_pad_block) {
                return Err(format!(
                    "function `{}` Invoke in block {} unwinds to block {}, which does not begin with LandingPad",
                    self.name, site.call_block.0, site.landing_pad_block.0
                ));
            }
        }
        for pad in &opcode_info.landing_pads {
            if !opcode_info
                .call_sites
                .iter()
                .any(|site| site.landing_pad_block == pad.block)
            {
                return Err(format!(
                    "function `{}` landing pad block {} has no Invoke unwind edge",
                    self.name, pad.block.0
                ));
            }
        }

        Ok(())
    }

    /// Canonical, frontend-neutral identity of the complete LIR verifier input.
    ///
    /// JIT certificate caches use this alongside emitted bytes and symbolic
    /// fixups. A machine-byte collision must never reuse a verdict whose TV-2
    /// source instruction, type metadata, proof policy, or TrustIR provenance
    /// differs. Hash-backed collections are removed from the derived `Debug`
    /// snapshot and appended in sorted order so identical programs retain warm
    /// cache hits across independently seeded `HashMap`/`HashSet` instances.
    pub fn canonical_verifier_identity_bytes(&self) -> Result<Vec<u8>, std::fmt::Error> {
        let mut out = String::new();
        self.write_canonical_verifier_identity(&mut out)?;
        Ok(out.into_bytes())
    }

    /// A conservative identity of the executable body, excluding function names
    /// and normalizing value/block numbering. Equal renderings bind the same
    /// supported body and metadata; this is not a semantic-equivalence decision
    /// or a complete alpha-isomorphism check (unreachable ordering and metadata
    /// order may conservatively differ). Returns `None` outside the comparable
    /// class (exception-handling structure, missing entry,
    /// duplicate definitions, runtime-sized slots, or values used/annotated
    /// but never defined).
    ///
    /// Canonical numbering: blocks in [`Self::layout_order`] (reverse
    /// postorder from the entry, then unreachable blocks deterministically),
    /// values in definition order (each block's parameters, then each
    /// instruction's results). Rendered: the signature; every block's
    /// parameters with their types; every instruction's opcode (its block and
    /// value fields renumbered), arguments and results; the recorded type of
    /// every numbered value; bit-exact floating constants; stack slots; the
    /// pure and libm-pure callee sets; executable ABI and stack-protector facts.
    /// Source and debug metadata (`source_locs`, `debug_meta`, trust_ir
    /// origins) are not semantics and are left out.
    ///
    /// Used to authenticate an inline-only body against the definition an
    /// authenticated dependency exports: both are translated by this adapter,
    /// in their own module, and must render identically.
    #[must_use]
    pub fn canonical_body_identity(&self) -> Option<String> {
        use std::fmt::Write as _;
        if !self.eh_info.is_empty()
            || !self.eh_type_table.is_empty()
            || !self.blocks.contains_key(&self.entry_block)
            // Dynamic size sources carry non-canonical IDs; do not infer that
            // they share the LIR value namespace or compare their raw numbers.
            || self.stack_slots.iter().any(StackSlotInfo::is_runtime_sized)
        {
            return None;
        }
        let order = self.layout_order();
        let block_index: HashMap<Block, usize> = order
            .iter()
            .enumerate()
            .map(|(index, block)| (*block, index))
            .collect();
        let mut value_index: HashMap<Value, usize> = HashMap::new();
        let define = |value: Value, value_index: &mut HashMap<Value, usize>| {
            let next = value_index.len();
            if value_index.insert(value, next).is_some() {
                None
            } else {
                Some(())
            }
        };
        for block in &order {
            let bb = self.blocks.get(block)?;
            for (value, _) in &bb.params {
                define(*value, &mut value_index)?;
            }
            for inst in &bb.instructions {
                for result in &inst.results {
                    define(*result, &mut value_index)?;
                }
            }
        }
        let v = |value: &Value| value_index.get(value).map(|index| format!("v{index}"));
        let b = |block: &Block| block_index.get(block).map(|index| format!("b{index}"));
        let mut out = String::new();
        writeln!(out, "sig={:?}", self.signature).ok()?;
        for block in &order {
            let bb = self.blocks.get(block)?;
            let params = bb
                .params
                .iter()
                .map(|(value, ty)| Some(format!("{}:{ty:?}", v(value)?)))
                .collect::<Option<Vec<_>>>()?;
            writeln!(out, "{}({})", b(block)?, params.join(",")).ok()?;
            for inst in &bb.instructions {
                let opcode = match &inst.opcode {
                    // Like the verifier identity below, preserve IEEE payload and
                    // sign bits: derived Debug renders distinct NaNs identically.
                    Opcode::Fconst { ty, imm } => {
                        format!("Fconst {ty:?} bits={:016x}", imm.to_bits())
                    }
                    Opcode::Jump { dest } => format!("Jump {}", b(dest)?),
                    Opcode::Brif {
                        cond,
                        then_dest,
                        else_dest,
                    } => format!("Brif {} {} {}", v(cond)?, b(then_dest)?, b(else_dest)?),
                    Opcode::Invoke {
                        binding,
                        name,
                        normal_dest,
                        unwind_dest,
                    } => format!(
                        "Invoke {name:?} {binding:?} {} {}",
                        b(normal_dest)?,
                        b(unwind_dest)?
                    ),
                    Opcode::Switch { cases, default } => {
                        let cases = cases
                            .iter()
                            .map(|(key, dest)| Some(format!("{key}:{}", b(dest)?)))
                            .collect::<Option<Vec<_>>>()?;
                        format!("Switch [{}] {}", cases.join(","), b(default)?)
                    }
                    other => format!("{other:?}"),
                };
                let args = inst.args.iter().map(v).collect::<Option<Vec<_>>>()?;
                let results = inst.results.iter().map(v).collect::<Option<Vec<_>>>()?;
                writeln!(
                    out,
                    "  {} = {opcode} ({})",
                    results.join(","),
                    args.join(",")
                )
                .ok()?;
            }
        }
        let mut types: Vec<(usize, String)> = self
            .value_types
            .iter()
            .map(|(value, ty)| Some((*value_index.get(value)?, format!("{ty:?}"))))
            .collect::<Option<_>>()?;
        types.sort();
        writeln!(out, "types={types:?}").ok()?;
        writeln!(out, "stack_slots={:?}", self.stack_slots).ok()?;
        let mut pure: Vec<&String> = self.pure_callees.iter().collect();
        pure.sort();
        let mut libm: Vec<&String> = self.libm_pure_callees.iter().collect();
        libm.sort();
        writeln!(out, "pure={pure:?} libm_pure={libm:?}").ok()?;
        // These sidecars affect ABI lowering, even when the instruction stream
        // and scalar signature match in two different module environments.
        writeln!(
            out,
            "stack_protector={:?} pointees={:?} sret={:?}",
            self.stack_protector, self.param_pointee_types, self.abi_sret_param
        )
        .ok()?;
        // Only a requesting function gets this line, so every other
        // function's rendering is unchanged; its unique prefix keeps the
        // rendering injective.
        if let Some(limit) = &self.stack_limit {
            writeln!(out, "stack_limit={limit:?}").ok()?;
        }
        let mut direct: Vec<_> = self.sret_arg_callees.iter().collect();
        direct.sort();
        let mut indirect: Vec<_> = self
            .sret_arg_indirect_callees
            .iter()
            .map(|value| value_index.get(value).copied())
            .collect::<Option<_>>()?;
        indirect.sort();
        writeln!(out, "sret_direct={direct:?} sret_indirect={indirect:?}").ok()?;
        Some(out)
    }

    /// Stream [`Self::canonical_verifier_identity_bytes`] without cloning the
    /// function or materializing its complete identity. Only borrowed map/set
    /// entry vectors are allocated so callers can hash large functions with
    /// pointer-sized temporary storage.
    pub fn write_canonical_verifier_identity(
        &self,
        out: &mut impl std::fmt::Write,
    ) -> std::fmt::Result {
        self.write_verifier_identity(out, true)
    }

    /// The verifier-input identity with every structure rendered by the
    /// compact derived `Debug` instead of the pretty (alternate) one, under
    /// its own header.
    ///
    /// Same fields, same order, same sorted hash-backed entries and NaN bits
    /// as [`Self::write_canonical_verifier_identity`]; no `Debug` rendered here
    /// depends on the alternate flag, and pretty printing only adds layout
    /// whitespace around the same tokens (string contents are escaped), so two
    /// functions have equal compact identities exactly when they have equal
    /// canonical ones. It is several times cheaper to produce (the pretty
    /// printer's indentation adapter dominated the canonical rendering), and
    /// is for identities compared within one process; persisted keys keep the
    /// canonical form.
    pub fn write_compact_verifier_identity(
        &self,
        out: &mut impl std::fmt::Write,
    ) -> std::fmt::Result {
        self.write_verifier_identity(out, false)
    }

    fn write_verifier_identity(
        &self,
        out: &mut impl std::fmt::Write,
        pretty: bool,
    ) -> std::fmt::Result {
        /// The alternate (pretty) `Debug` when `pretty`, the compact one otherwise.
        struct Rendering<'a, T: std::fmt::Debug>(&'a T, bool);
        impl<T: std::fmt::Debug> std::fmt::Display for Rendering<'_, T> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                if self.1 {
                    write!(f, "{:#?}", self.0)
                } else {
                    write!(f, "{:?}", self.0)
                }
            }
        }
        if pretty {
            writeln!(out, "trust-cg.lir.verifier-input.v3")?;
        } else {
            writeln!(out, "trust-cg.lir.verifier-input.v3.compact")?;
        }
        writeln!(out, "name={:?}", self.name)?;
        writeln!(out, "signature={}", Rendering(&self.signature, pretty))?;
        writeln!(out, "block_order={:?}", self.block_order)?;
        writeln!(out, "entry_block={:?}", self.entry_block)?;
        writeln!(out, "stack_slots={}", Rendering(&self.stack_slots, pretty))?;
        writeln!(out, "debug_meta={}", Rendering(&self.debug_meta, pretty))?;
        writeln!(
            out,
            "debug_value_bindings={}",
            Rendering(&self.debug_value_bindings, pretty)
        )?;
        writeln!(out, "stack_protector={:?}", self.stack_protector)?;
        if let Some(limit) = &self.stack_limit {
            writeln!(out, "stack_limit={}", Rendering(limit, pretty))?;
        }
        writeln!(
            out,
            "param_pointee_types={}",
            Rendering(&self.param_pointee_types, pretty)
        )?;
        writeln!(out, "eh_info={}", Rendering(&self.eh_info, pretty))?;

        let mut blocks: Vec<_> = self.blocks.iter().collect();
        blocks.sort_by_key(|(block, _)| **block);
        writeln!(out, "blocks={}", blocks.len())?;
        for (block, body) in blocks {
            writeln!(out, "block[{block:?}]={}", Rendering(body, pretty))?;
            // Rust's derived `Debug` deliberately renders every NaN as `NaN`,
            // while the verifier and encoders distinguish the complete IEEE
            // payload. Bind those raw bits at their structural location so two
            // otherwise identical Fconst instructions cannot alias in a proof
            // cache key.
            for (instruction_index, instruction) in body.instructions.iter().enumerate() {
                if let Opcode::Fconst { imm, .. } = &instruction.opcode {
                    writeln!(
                        out,
                        "fconst_bits[{block:?}][{instruction_index}]={:016x}",
                        imm.to_bits()
                    )?;
                }
            }
        }

        let mut trust_ir_origins: Vec<_> = self.trust_ir_origins.iter().collect();
        trust_ir_origins.sort_by_key(|(block, _)| **block);
        writeln!(out, "trust_ir_origins={}", trust_ir_origins.len())?;
        for (block, origins) in trust_ir_origins {
            writeln!(out, "trust_ir_origins[{block:?}]={origins:?}")?;
        }

        let mut value_types: Vec<_> = self.value_types.iter().collect();
        value_types.sort_by_key(|(value, _)| value.0);
        writeln!(out, "value_types={}", value_types.len())?;
        for (value, ty) in value_types {
            writeln!(out, "value_type[{value:?}]={ty:?}")?;
        }

        let mut pure_callees: Vec<_> = self.pure_callees.iter().collect();
        pure_callees.sort_unstable();
        writeln!(out, "pure_callees={}", pure_callees.len())?;
        for callee in pure_callees {
            writeln!(out, "pure_callee={callee:?}")?;
        }

        let mut libm_pure_callees: Vec<_> = self.libm_pure_callees.iter().collect();
        libm_pure_callees.sort_unstable();
        writeln!(out, "libm_pure_callees={}", libm_pure_callees.len())?;
        for callee in libm_pure_callees {
            writeln!(out, "libm_pure_callee={callee:?}")?;
        }

        // The indirect-return convention changes the emitted ABI, so it belongs
        // in the identity dump: two otherwise-identical functions that disagree
        // about it are NOT the same function.
        writeln!(out, "abi_sret_param={:?}", self.abi_sret_param)?;
        let mut sret_arg_callees: Vec<_> = self.sret_arg_callees.iter().collect();
        sret_arg_callees.sort_unstable();
        writeln!(out, "sret_arg_callees={}", sret_arg_callees.len())?;
        for callee in sret_arg_callees {
            writeln!(out, "sret_arg_callee={callee:?}")?;
        }
        let mut sret_arg_indirect_callees: Vec<_> = self.sret_arg_indirect_callees.iter().collect();
        sret_arg_indirect_callees.sort_unstable_by_key(|value| value.0);
        writeln!(
            out,
            "sret_arg_indirect_callees={}",
            sret_arg_indirect_callees.len()
        )?;
        for callee in sret_arg_indirect_callees {
            writeln!(out, "sret_arg_indirect_callee={callee:?}")?;
        }
        // Per-function target features select different instructions, so two
        // functions that differ only here are not the same function. Rendered
        // only when stated, which keeps every attribute-free identity (every
        // function before per-function features) byte-identical.
        if !self.target_features.is_empty() {
            writeln!(out, "target_features={:?}", self.target_features)?;
        }
        Ok(())
    }

    fn push_rpo(&self, block: Block, seen: &mut HashSet<Block>, order: &mut Vec<Block>) {
        let Some(first) = self.blocks.get(&block) else {
            return;
        };
        if !seen.insert(block) {
            return;
        }
        // Keep exactly the recursive walk's discovery and successor order,
        // including loops and missing targets, without consuming caller stack
        // per CFG depth. A frame retains only its remaining successor iterator.
        let mut frames = vec![(block, first.layout_successors().into_iter())];
        while let Some((current, successors)) = frames.last_mut() {
            if let Some(next) = successors.next() {
                if let Some(body) = self.blocks.get(&next)
                    && seen.insert(next)
                {
                    frames.push((next, body.layout_successors().into_iter()));
                }
            } else {
                let finished = *current;
                frames.pop();
                order.push(finished);
            }
        }
    }
}

impl BasicBlock {
    /// Return CFG successors named by terminator-like instructions in this block.
    pub fn successors(&self) -> Vec<Block> {
        let mut successors = Vec::new();
        for inst in &self.instructions {
            match &inst.opcode {
                Opcode::Jump { dest } => successors.push(*dest),
                Opcode::Brif {
                    then_dest,
                    else_dest,
                    ..
                } => {
                    successors.push(*then_dest);
                    successors.push(*else_dest);
                }
                Opcode::Trap => {}
                Opcode::Invoke {
                    normal_dest,
                    unwind_dest,
                    ..
                } => {
                    successors.push(*normal_dest);
                    successors.push(*unwind_dest);
                }
                Opcode::Switch { cases, default } => {
                    successors.push(*default);
                    successors.extend(cases.iter().map(|(_, block)| *block));
                }
                _ => {}
            }
        }
        successors
    }

    /// Return CFG successors in the order used by RPO layout.
    ///
    /// `layout_order` reverses DFS postorder. For conditional branches, visit
    /// the else/fallthrough successor first so the taken path stays adjacent to
    /// the header in the final layout. This keeps simple counted loops in
    /// `header, body, exit` order for late latch-layout combines while still
    /// reporting semantic successors as then/else through `successors()`.
    fn layout_successors(&self) -> Vec<Block> {
        let mut successors = Vec::new();
        for inst in &self.instructions {
            match &inst.opcode {
                Opcode::Jump { dest } => successors.push(*dest),
                Opcode::Brif {
                    then_dest,
                    else_dest,
                    ..
                } => {
                    successors.push(*else_dest);
                    successors.push(*then_dest);
                }
                Opcode::Trap => {}
                Opcode::Invoke {
                    normal_dest,
                    unwind_dest,
                    ..
                } => {
                    successors.push(*normal_dest);
                    successors.push(*unwind_dest);
                }
                Opcode::Switch { cases, default } => {
                    successors.push(*default);
                    successors.extend(cases.iter().map(|(_, block)| *block));
                }
                _ => {}
            }
        }
        successors
    }
}

// ---------------------------------------------------------------------------
// From<trust_cg_lower::Signature> for trust_cg_ir::Signature
// ---------------------------------------------------------------------------
//
// Centralizes the signature conversion that was previously done inline in
// pipeline.rs. Uses the From<Type> impl in types.rs for individual type
// conversion.

impl From<&Signature> for trust_cg_ir::function::Signature {
    fn from(sig: &Signature) -> Self {
        let params: Vec<trust_cg_ir::function::Type> =
            sig.params.iter().map(|t| t.into()).collect();
        let returns: Vec<trust_cg_ir::function::Type> =
            sig.returns.iter().map(|t| t.into()).collect();
        trust_cg_ir::function::Signature::new(params, returns)
    }
}

impl From<Signature> for trust_cg_ir::function::Signature {
    fn from(sig: Signature) -> Self {
        (&sig).into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_identity_stream_and_buffer_agree_and_propagate_write_errors() {
        struct RefusingWriter;
        impl std::fmt::Write for RefusingWriter {
            fn write_str(&mut self, _: &str) -> std::fmt::Result {
                Err(std::fmt::Error)
            }
        }
        let function = Function::new("identity", Signature::default());
        let mut streamed = String::new();
        function
            .write_canonical_verifier_identity(&mut streamed)
            .unwrap();
        assert_eq!(
            function.canonical_verifier_identity_bytes().unwrap(),
            streamed.into_bytes()
        );
        assert_eq!(
            function.write_canonical_verifier_identity(&mut RefusingWriter),
            Err(std::fmt::Error)
        );
    }

    #[test]
    fn canonical_verifier_identity_is_hash_order_independent_and_semantic() {
        fn build(reverse: bool) -> Function {
            let mut function = Function::new("canonical", Signature::default());
            function.block_order = vec![Block(0), Block(1)];
            let block_ids = if reverse {
                [Block(1), Block(0)]
            } else {
                [Block(0), Block(1)]
            };
            for block in block_ids {
                function.blocks.insert(block, BasicBlock::default());
            }
            let values = if reverse {
                [(Value(2), Type::F64), (Value(1), Type::I64)]
            } else {
                [(Value(1), Type::I64), (Value(2), Type::F64)]
            };
            for (value, ty) in values {
                function.value_types.insert(value, ty);
            }
            function.pure_callees.insert("z".to_string());
            function.pure_callees.insert("a".to_string());
            function.libm_pure_callees.insert("cos".to_string());
            let origins = [(Block(0), vec![Some(TrustIrInstId(1))]), (Block(1), vec![])];
            if reverse {
                for (block, value) in origins.into_iter().rev() {
                    function.trust_ir_origins.insert(block, value);
                }
            } else {
                for (block, value) in origins {
                    function.trust_ir_origins.insert(block, value);
                }
            }
            function
        }

        let forward = build(false);
        let reverse = build(true);
        assert_eq!(
            forward.canonical_verifier_identity_bytes(),
            reverse.canonical_verifier_identity_bytes()
        );

        let mut changed = reverse;
        changed.value_types.insert(Value(1), Type::I32);
        assert_ne!(
            forward.canonical_verifier_identity_bytes(),
            changed.canonical_verifier_identity_bytes()
        );

        let mut first_nan = build(false);
        first_nan
            .blocks
            .get_mut(&Block(0))
            .unwrap()
            .instructions
            .push(inst(Opcode::Fconst {
                ty: Type::F64,
                imm: f64::from_bits(0x7ff8_0000_0000_0001),
            }));
        let mut second_nan = first_nan.clone();
        if let Opcode::Fconst { imm, .. } =
            &mut second_nan.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode
        {
            *imm = f64::from_bits(0x7ff8_0000_0000_0002);
        }
        assert_ne!(
            first_nan.canonical_verifier_identity_bytes(),
            second_nan.canonical_verifier_identity_bytes()
        );
    }

    fn inst(opcode: Opcode) -> Instruction {
        Instruction {
            opcode,
            args: vec![],
            results: vec![],
        }
    }

    #[test]
    fn eh_structure_accepts_landing_pad_then_multiblock_cleanup_resume() {
        let entry = Block(0);
        let normal = Block(1);
        let pad = Block(2);
        let cleanup = Block(3);
        let mut func = Function::new("multiblock_cleanup", Signature::default());
        func.entry_block = entry;
        func.block_order = vec![entry, normal, pad, cleanup];
        func.blocks.insert(
            entry,
            BasicBlock {
                instructions: vec![inst(Opcode::Invoke {
                    binding: crate::instructions::DirectCallBinding::Interposable,
                    name: "may_unwind".to_string(),
                    normal_dest: normal,
                    unwind_dest: pad,
                })],
                ..Default::default()
            },
        );
        func.blocks.insert(
            normal,
            BasicBlock {
                instructions: vec![inst(Opcode::Return)],
                ..Default::default()
            },
        );
        let mut landing = inst(Opcode::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        });
        landing.results = vec![Value(0), Value(1)];
        let mut to_cleanup = inst(Opcode::Jump { dest: cleanup });
        to_cleanup.args = vec![Value(0)];
        func.blocks.insert(
            pad,
            BasicBlock {
                instructions: vec![landing, to_cleanup],
                ..Default::default()
            },
        );
        let mut resume = inst(Opcode::Resume);
        resume.args = vec![Value(2)];
        func.blocks.insert(
            cleanup,
            BasicBlock {
                params: vec![(Value(2), Type::I64)],
                instructions: vec![resume],
                ..Default::default()
            },
        );
        func.eh_info = EhFunctionInfo {
            personality: Some("rust_eh_personality".to_string()),
            landing_pads: vec![EhLandingPad {
                block: pad,
                catch_type_indices: vec![],
                is_cleanup: true,
            }],
            call_sites: vec![EhCallSite {
                call_block: entry,
                landing_pad_block: pad,
            }],
        };

        func.validate_eh_structure()
            .expect("Resume may live in a cleanup successor of the landing-pad block");
    }

    #[test]
    fn eh_structure_rejects_opcode_sidecar_mismatch_and_missing_personality() {
        let entry = Block(0);
        let normal = Block(1);
        let pad = Block(2);
        let mut func = Function::new("bad_eh", Signature::default());
        func.entry_block = entry;
        func.block_order = vec![entry, normal, pad];
        func.blocks.insert(
            entry,
            BasicBlock {
                instructions: vec![inst(Opcode::Invoke {
                    binding: crate::instructions::DirectCallBinding::Interposable,
                    name: "may_unwind".to_string(),
                    normal_dest: normal,
                    unwind_dest: pad,
                })],
                ..Default::default()
            },
        );
        func.blocks.insert(
            normal,
            BasicBlock {
                instructions: vec![inst(Opcode::Return)],
                ..Default::default()
            },
        );
        func.blocks.insert(
            pad,
            BasicBlock {
                instructions: vec![
                    inst(Opcode::LandingPad {
                        is_cleanup: true,
                        catch_type_indices: vec![],
                    }),
                    inst(Opcode::Return),
                ],
                ..Default::default()
            },
        );

        let err = func
            .validate_eh_structure()
            .expect_err("EH opcodes without a personality/sidecar must fail closed");
        assert!(err.contains("no personality"), "{err}");

        func.eh_info.personality = Some("rust_eh_personality".to_string());
        let err = func
            .validate_eh_structure()
            .expect_err("personality alone must not replace exact block metadata");
        assert!(err.contains("does not exactly match"), "{err}");
    }

    #[test]
    fn eh_structure_rejects_identical_normal_and_unwind_destinations() {
        let entry = Block(0);
        let pad = Block(1);
        let mut func = Function::new("aliased_invoke_edges", Signature::default());
        func.entry_block = entry;
        func.block_order = vec![entry, pad];
        func.blocks.insert(
            entry,
            BasicBlock {
                instructions: vec![inst(Opcode::Invoke {
                    binding: crate::instructions::DirectCallBinding::Interposable,
                    name: "may_unwind".to_string(),
                    normal_dest: pad,
                    unwind_dest: pad,
                })],
                ..Default::default()
            },
        );
        func.blocks.insert(
            pad,
            BasicBlock {
                instructions: vec![
                    inst(Opcode::LandingPad {
                        is_cleanup: true,
                        catch_type_indices: vec![],
                    }),
                    inst(Opcode::Return),
                ],
                ..Default::default()
            },
        );
        func.eh_info = EhFunctionInfo {
            personality: Some("rust_eh_personality".to_string()),
            landing_pads: vec![EhLandingPad {
                block: pad,
                catch_type_indices: vec![],
                is_cleanup: true,
            }],
            call_sites: vec![EhCallSite {
                call_block: entry,
                landing_pad_block: pad,
            }],
        };

        let err = func
            .validate_eh_structure()
            .expect_err("normal and unwind edges must retain distinct identities");
        assert!(err.contains("both normal and unwind"), "{err}");
    }

    #[test]
    fn layout_order_uses_rpo_for_reachable_blocks() {
        let mut func = Function::new("rpo_order", Signature::default());
        func.entry_block = Block(0);
        func.block_order = vec![Block(0), Block(1), Block(2)];
        func.blocks.insert(
            Block(0),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Jump { dest: Block(2) },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        func.blocks.insert(
            Block(1),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        func.blocks.insert(
            Block(2),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Jump { dest: Block(1) },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );

        assert_eq!(func.layout_order(), vec![Block(0), Block(2), Block(1)]);
    }

    #[test]
    fn layout_order_places_conditional_taken_loop_body_before_exit() {
        let mut func = Function::new("counted_loop_order", Signature::default());
        func.entry_block = Block(0);
        func.block_order = vec![Block(0), Block(1), Block(2), Block(3)];
        func.blocks.insert(
            Block(0),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Jump { dest: Block(1) },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        func.blocks.insert(
            Block(1),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Brif {
                        cond: Value(0),
                        then_dest: Block(2),
                        else_dest: Block(3),
                    },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        func.blocks.insert(
            Block(2),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Jump { dest: Block(1) },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        func.blocks.insert(
            Block(3),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );

        assert_eq!(
            func.blocks.get(&Block(1)).unwrap().successors(),
            vec![Block(2), Block(3)]
        );
        assert_eq!(
            func.layout_order(),
            vec![Block(0), Block(1), Block(2), Block(3)]
        );
    }

    #[test]
    fn layout_order_appends_unreachable_blocks_in_explicit_order() {
        let mut func = Function::new("unreachable_order", Signature::default());
        func.entry_block = Block(0);
        func.block_order = vec![Block(0), Block(7), Block(3)];
        func.blocks.insert(
            Block(0),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        func.blocks.insert(
            Block(3),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        func.blocks.insert(
            Block(7),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );

        assert_eq!(func.layout_order(), vec![Block(0), Block(7), Block(3)]);
    }

    #[test]
    fn stack_slot_info_fixed_converts_to_ir_fixed_slot() {
        let info = StackSlotInfo::new(32, 8);
        let slot = info.to_ir_stack_slot();

        assert_eq!(slot.size, 32);
        assert_eq!(slot.align, 8);
        assert!(slot.is_fixed_size());
    }

    #[test]
    fn stack_slot_info_dynamic_converts_to_ir_runtime_slot() {
        let info = StackSlotInfo::new_dynamic(StackSlotSizeSource::Value(7), 16);
        let slot = info.to_ir_stack_slot();

        assert_eq!(slot.size, 0);
        assert_eq!(slot.align, 16);
        assert!(info.is_runtime_sized());
        assert!(slot.is_runtime_sized());
        assert_eq!(slot.size_source(), Some(StackSlotSizeSource::Value(7)));
    }
}

#[cfg(test)]
mod canonical_body_identity_tests {
    use super::*;
    use crate::instructions::IntCC;

    fn inst(opcode: Opcode, args: &[u32], results: &[u32]) -> Instruction {
        Instruction {
            opcode,
            args: args.iter().copied().map(Value).collect(),
            results: results.iter().copied().map(Value).collect(),
        }
    }

    /// `max(a, b)` as a three-block diamond, with block and value numbers
    /// offset by `shift` and the function named `name`.
    fn max(name: &str, shift: u32, then_value: u32) -> Function {
        let v = |n: u32| n + shift;
        let bl = |n: u32| Block(n + shift);
        let mut f = Function::new(
            name,
            Signature {
                params: vec![Type::I64, Type::I64],
                returns: vec![Type::I64],
            },
        );
        f.entry_block = bl(0);
        f.blocks.insert(
            bl(0),
            BasicBlock {
                params: vec![(Value(v(0)), Type::I64), (Value(v(1)), Type::I64)],
                instructions: vec![
                    inst(
                        Opcode::Icmp {
                            cond: IntCC::SignedGreaterThan,
                        },
                        &[v(0), v(1)],
                        &[v(2)],
                    ),
                    inst(
                        Opcode::Brif {
                            cond: Value(v(2)),
                            then_dest: bl(1),
                            else_dest: bl(2),
                        },
                        &[v(2)],
                        &[],
                    ),
                ],
                ..Default::default()
            },
        );
        f.blocks.insert(
            bl(1),
            BasicBlock {
                instructions: vec![inst(Opcode::Return, &[v(then_value)], &[])],
                ..Default::default()
            },
        );
        f.blocks.insert(
            bl(2),
            BasicBlock {
                instructions: vec![inst(Opcode::Return, &[v(1)], &[])],
                ..Default::default()
            },
        );
        f.block_order = vec![bl(0), bl(1), bl(2)];
        f.value_types.insert(Value(v(2)), Type::B1);
        f
    }

    #[test]
    fn renumbered_and_renamed_bodies_are_equal() {
        let a = max("max", 0, 0).canonical_body_identity();
        let b = max("other_name", 40, 0).canonical_body_identity();
        assert!(a.is_some());
        assert_eq!(a, b);
    }

    #[test]
    fn a_different_operand_is_a_different_body() {
        // The then-arm returns `b` instead of `a`.
        assert_ne!(
            max("max", 0, 0).canonical_body_identity(),
            max("max", 0, 1).canonical_body_identity()
        );
    }

    #[test]
    fn a_different_recorded_type_is_a_different_body() {
        let mut typed = max("max", 0, 0);
        typed.value_types.insert(Value(0), Type::I32);
        assert_ne!(
            max("max", 0, 0).canonical_body_identity(),
            typed.canonical_body_identity()
        );
    }

    #[test]
    fn an_undefined_value_is_not_comparable() {
        let mut broken = max("max", 0, 0);
        broken.blocks.get_mut(&Block(1)).unwrap().instructions[0].args = vec![Value(99)];
        assert_eq!(broken.canonical_body_identity(), None);
    }

    #[test]
    fn floating_constant_identity_preserves_all_ieee_bits() {
        let identity = |bits| {
            let mut f = max("bits", 0, 0);
            f.blocks.get_mut(&Block(0)).unwrap().instructions.insert(
                0,
                inst(
                    Opcode::Fconst {
                        ty: Type::F64,
                        imm: f64::from_bits(bits),
                    },
                    &[],
                    &[3],
                ),
            );
            f.canonical_body_identity().unwrap()
        };
        let bits = [
            0x7ff8_0000_0000_0001,
            0x7ff8_0000_0000_0002,
            0xfff8_0000_0000_0001,
            0x7ff0_0000_0000_0001,
            0,
            0x8000_0000_0000_0000,
        ];
        for (i, &a) in bits.iter().enumerate() {
            assert_eq!(identity(a), identity(a));
            for &b in &bits[i + 1..] {
                assert_ne!(identity(a), identity(b), "IEEE bits {a:016x} vs {b:016x}");
            }
        }
    }

    #[test]
    fn body_identity_binds_abi_sidecars_and_renumbers_indirect_callees() {
        let baseline = max("max", 0, 0);
        let identity = baseline.canonical_body_identity().unwrap();
        let mut changed = baseline.clone();
        changed.stack_protector = StackProtectorMode::StackGuard;
        assert_ne!(Some(identity.clone()), changed.canonical_body_identity());
        changed = baseline.clone();
        changed.stack_limit = Some(StackLimitRequest {
            param: 0,
            source: StackLimitSource::Value,
            overflow: StackLimitOverflow::Trap,
        });
        assert_ne!(Some(identity.clone()), changed.canonical_body_identity());
        let trap = changed.canonical_body_identity();
        changed.stack_limit = Some(StackLimitRequest {
            param: 0,
            source: StackLimitSource::Pointee { offset: 0 },
            overflow: StackLimitOverflow::Trap,
        });
        assert_ne!(trap, changed.canonical_body_identity());
        changed = baseline.clone();
        changed.abi_sret_param = Some(AbiSretParam { param_index: 0 });
        assert_ne!(Some(identity.clone()), changed.canonical_body_identity());
        changed = baseline.clone();
        changed.param_pointee_types.push(ParamPointeeType {
            param_index: 0,
            pointee_ty: Type::I64,
        });
        assert_ne!(Some(identity.clone()), changed.canonical_body_identity());
        changed = baseline.clone();
        changed.sret_arg_callees.insert("callee".into());
        assert_ne!(Some(identity.clone()), changed.canonical_body_identity());
        changed = baseline.clone();
        changed.sret_arg_indirect_callees.insert(Value(0));
        assert_ne!(Some(identity), changed.canonical_body_identity());
        let mut renamed = max("renamed", 40, 0);
        renamed.sret_arg_indirect_callees.insert(Value(40));
        assert_eq!(
            changed.canonical_body_identity(),
            renamed.canonical_body_identity()
        );
        renamed.sret_arg_indirect_callees.clear();
        renamed.sret_arg_indirect_callees.insert(Value(41));
        assert_ne!(
            changed.canonical_body_identity(),
            renamed.canonical_body_identity()
        );
    }

    #[test]
    fn malformed_body_metadata_is_not_comparable() {
        for mutant in 0..6 {
            let mut f = max("max", 0, 0);
            match mutant {
                0 => {
                    f.value_types.insert(Value(99), Type::I64);
                }
                1 => {
                    f.sret_arg_indirect_callees.insert(Value(99));
                }
                2 => {
                    f.entry_block = Block(99);
                }
                3 => {
                    f.eh_type_table = EhTypeTable::from_symbols(vec!["typeinfo".into()]);
                }
                4 => {
                    f.stack_slots
                        .push(StackSlotInfo::new_dynamic(StackSlotSizeSource::Value(0), 8));
                }
                _ => {
                    f.blocks
                        .get_mut(&Block(0))
                        .unwrap()
                        .params
                        .push((Value(0), Type::I64));
                }
            }
            assert_eq!(f.canonical_body_identity(), None, "mutant {mutant}");
        }
    }
}
