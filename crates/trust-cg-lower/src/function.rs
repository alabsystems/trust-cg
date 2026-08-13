// trust-cg-lower/function.rs - Function representation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Function and basic block representation for Trust Codegen LIR.

use crate::instructions::{Block, Instruction, Opcode, Value};
use crate::types::Type;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use trust_cg_ir::function::{
    FunctionDebugMeta, StackProtectorMode, StackSlot, StackSlotAllocationKind, StackSlotSizeSource,
};
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
    /// Aggregate pointee types for pointer-shaped ABI parameters.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub param_pointee_types: Vec<ParamPointeeType>,
    /// Exception-handling structure, populated by the adapter when the trust_ir
    /// source carries `Inst::Invoke` / `Inst::LandingPad`. ISel forwards this to
    /// `MachFunction.eh_metadata` (as BlockId-level entries); the codegen
    /// pipeline resolves the byte offsets after block layout and emits the LSDA
    /// + compact unwind. Empty for functions without exception handling.
    #[serde(default, skip_serializing_if = "EhFunctionInfo::is_empty")]
    pub eh_info: EhFunctionInfo,
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

/// A landing-pad block in the LIR (pre-layout; the byte offset is resolved by
/// the codegen pipeline after block layout).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EhLandingPad {
    /// The LIR block that begins with the landing pad.
    pub block: Block,
    /// Type indices this pad catches (0 == catch-all). Empty + `is_cleanup` is
    /// a pure cleanup pad.
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
            debug_meta: FunctionDebugMeta::default(),
            debug_value_bindings: Vec::new(),
            stack_protector: StackProtectorMode::None,
            param_pointee_types: Vec::new(),
            eh_info: EhFunctionInfo::default(),
        }
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

        let mut remaining = Vec::new();
        for &block in &self.block_order {
            if self.blocks.contains_key(&block) && !seen.contains(&block) {
                remaining.push(block);
            }
        }
        let mut fallback_remaining: Vec<_> = self
            .blocks
            .keys()
            .copied()
            .filter(|block| !seen.contains(block) && !remaining.contains(block))
            .collect();
        fallback_remaining.sort_by_key(|block| block.0);
        remaining.extend(fallback_remaining);

        for block in remaining {
            if seen.insert(block) {
                order.push(block);
            }
        }

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

    fn push_rpo(&self, block: Block, seen: &mut HashSet<Block>, order: &mut Vec<Block>) {
        if !self.blocks.contains_key(&block) || !seen.insert(block) {
            return;
        }

        if let Some(basic_block) = self.blocks.get(&block) {
            for succ in basic_block.layout_successors() {
                self.push_rpo(succ, seen, order);
            }
        }

        order.push(block);
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
