// trust-cg-ir - Provenance tracking: trust_ir-to-binary offset mapping
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-13-debugging-transparency.md (Provenance Tracking)
//
// This module maintains source-to-binary mappings through every compilation
// stage: ISel creates trust_ir->MachIR mappings, optimization passes update them,
// and encoding adds the final binary offsets. The transitive closure gives
// trust_ir->binary offset for the full chain.

//! Provenance tracking infrastructure for Trust Codegen.
//!
//! Maintains a bidirectional mapping from trust_ir source instructions to machine
//! instructions to final binary offsets. Every compilation stage participates:
//!
//! - **ISel (trust-cg-lower):** Records initial trust_ir -> MachIR mapping via
//!   [`ProvenanceMap::record_lowering`].
//! - **Optimization passes (trust-cg-opt):** Update mappings when instructions are
//!   replaced, merged, cloned, deleted, or created. See [`ProvenanceMap::record_replacement`],
//!   [`ProvenanceMap::record_merge`], [`ProvenanceMap::record_clone`],
//!   [`ProvenanceMap::record_deletion`],
//!   [`ProvenanceMap::record_creation`].
//! - **Encoding (trust-cg-codegen):** Records MachIR -> binary offset via
//!   [`ProvenanceMap::record_encoding`].
//! - **Query:** After all stages, call [`ProvenanceMap::build_transitive`] then
//!   use [`ProvenanceMap::query_offset`] or [`ProvenanceMap::query_source`].
//!
//! # Pass Update Rules
//!
//! | Pass action | Method | Provenance effect |
//! |------------|--------|-------------------|
//! | Replace A with B | `record_replacement` | `provenance[B] = provenance[A]` |
//! | Merge A,B into C | `record_merge` | `provenance[C] = union(provenance[A], provenance[B])` |
//! | Clone A into B | `record_clone` | `provenance[B] = provenance[A]`, keep A live |
//! | Delete A (DCE) | `record_deletion` | Mark as OptimizedAway with justification |
//! | Create new inst | `record_creation` | Mark as CompilerGenerated |

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::regs::PReg;
use crate::types::{InstId, StackSlotId};

// ---------------------------------------------------------------------------
// TrustIrInstId — trust_ir instruction identifier
// ---------------------------------------------------------------------------

/// Identifier for a trust_ir instruction (source-level).
///
/// This corresponds to an instruction index in the trust_ir function being compiled.
/// It is deliberately a separate type from `trust_ir::ValueId` to keep the
/// provenance system self-contained within trust-cg-ir (no dependency on trust_ir
/// for the core tracking infrastructure).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct TrustIrInstId(pub u32);

impl core::fmt::Display for TrustIrInstId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "trust_ir{}", self.0)
    }
}

// ---------------------------------------------------------------------------
// TrustIrVarId — source-visible trust_ir variable identifier
// ---------------------------------------------------------------------------

/// Identifier for a source-visible trust_ir variable.
///
/// This is deliberately separate from trust_ir value identifiers so the
/// provenance layer can track user-visible variables without depending on the
/// source IR crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TrustIrVarId(pub u32);

/// Number of variable IDs reserved for each provenance variable namespace.
pub const TRUST_IR_VAR_NAMESPACE_STRIDE: u32 = 1 << 28;

/// Variable-ID namespace reserved for provenance-backed debug producers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustIrVarNamespace {
    /// Producer-supplied source variable IDs.
    Source,
    /// O3 debug path for fixed stack locals.
    O3FixedStackLocal,
    /// O3 debug path for compile-time constants.
    O3ConstantLocal,
    /// O3 debug path for register-backed locations.
    O3RegisterLocal,
    /// O3 debug path for spill-backed locations.
    O3SpillLocal,
    /// O3 debug path for synthetic compiler variables.
    O3Synthetic,
}

impl TrustIrVarNamespace {
    const fn band(self) -> u32 {
        match self {
            Self::Source => 0,
            Self::O3FixedStackLocal => 8,
            Self::O3ConstantLocal => 9,
            Self::O3RegisterLocal => 10,
            Self::O3SpillLocal => 11,
            Self::O3Synthetic => 12,
        }
    }
}

/// Typed errors for provenance variable-ID namespace construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustIrVarIdError {
    /// The namespace-local index does not fit in its reserved band.
    NamespaceIndexOutOfRange {
        /// Namespace being allocated from.
        namespace: TrustIrVarNamespace,
        /// Requested namespace-local index.
        index: u32,
        /// Exclusive upper bound for namespace-local indices.
        limit: u32,
    },
}

impl core::fmt::Display for TrustIrVarId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "var{}", self.0)
    }
}

impl TrustIrVarId {
    /// Create a variable ID in a reserved namespace.
    pub fn namespaced(
        namespace: TrustIrVarNamespace,
        index: u32,
    ) -> Result<Self, TrustIrVarIdError> {
        if index >= TRUST_IR_VAR_NAMESPACE_STRIDE {
            return Err(TrustIrVarIdError::NamespaceIndexOutOfRange {
                namespace,
                index,
                limit: TRUST_IR_VAR_NAMESPACE_STRIDE,
            });
        }

        Ok(Self(
            namespace.band() * TRUST_IR_VAR_NAMESPACE_STRIDE + index,
        ))
    }

    /// Return this variable's reserved namespace when it belongs to one.
    pub fn namespace(self) -> Option<TrustIrVarNamespace> {
        match self.0 / TRUST_IR_VAR_NAMESPACE_STRIDE {
            0 => Some(TrustIrVarNamespace::Source),
            8 => Some(TrustIrVarNamespace::O3FixedStackLocal),
            9 => Some(TrustIrVarNamespace::O3ConstantLocal),
            10 => Some(TrustIrVarNamespace::O3RegisterLocal),
            11 => Some(TrustIrVarNamespace::O3SpillLocal),
            12 => Some(TrustIrVarNamespace::O3Synthetic),
            _ => None,
        }
    }

    /// Return the namespace-local index for this variable ID.
    pub fn namespace_index(self) -> u32 {
        self.0 % TRUST_IR_VAR_NAMESPACE_STRIDE
    }
}

// ---------------------------------------------------------------------------
// PassId — identifies which compiler pass touched an instruction
// ---------------------------------------------------------------------------

/// Identifier for a compiler pass (used in transformation chains).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub struct PassId(pub String);

impl PassId {
    /// Create a new PassId.
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }

    /// Get the pass name.
    pub fn name(&self) -> &str {
        &self.0
    }
}

impl core::fmt::Display for PassId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// ---------------------------------------------------------------------------
// Variable live ranges
// ---------------------------------------------------------------------------

/// Reason a source-visible variable has no materialized value in a range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeadReason {
    /// The defining computation was removed because it had no remaining uses.
    DeadCodeElimination,
    /// The variable was folded into a compile-time constant.
    ConstantFolded(u128),
    /// The variable was coalesced into another source-visible variable.
    CoalescedWith(TrustIrVarId),
    /// The variable's source lifetime ended naturally.
    SourceLifetimeEnded,
    /// A pass proved the value cannot be represented precisely yet.
    Unsupported(String),
}

/// Physical or logical location for a source-visible variable over a range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocationExpr {
    /// Whole value resides in one physical register.
    Reg(PReg),
    /// Whole value resides in one stack slot.
    Stack(StackSlotId),
    /// Compile-time constant value with a bit width.
    Const { value: u128, bit_width: u16 },
    /// Value is intentionally unavailable over this range.
    Dead {
        /// Pass that proved or introduced the dead range.
        killed_by: PassId,
        /// Why the value is unavailable.
        reason: DeadReason,
    },
}

/// One stable location range for a source-visible variable.
///
/// The variable holds `value` for the half-open machine-instruction range
/// `[start, end)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarLocation {
    /// Source-visible variable this range describes.
    pub var: TrustIrVarId,
    /// First machine instruction where this location is valid.
    pub start: InstId,
    /// First machine instruction after this location stops being valid.
    pub end: InstId,
    /// Where the variable's bits live in this range.
    pub value: LocationExpr,
}

impl VarLocation {
    /// Create a variable location range.
    pub fn new(var: TrustIrVarId, start: InstId, end: InstId, value: LocationExpr) -> Self {
        Self {
            var,
            start,
            end,
            value,
        }
    }

    fn is_dead(&self) -> bool {
        matches!(self.value, LocationExpr::Dead { .. })
    }
}

/// Typed validation errors for source-variable live ranges.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarLocationError {
    /// The range is empty or inverted; ranges are half-open and require
    /// `start < end`.
    InvalidRange {
        /// Variable whose range failed validation.
        var: TrustIrVarId,
        /// First instruction in the range.
        start: InstId,
        /// First instruction after the range.
        end: InstId,
    },
    /// The method's explicit variable ID and the range payload disagree.
    VarMismatch {
        /// Variable ID requested by the caller.
        expected: TrustIrVarId,
        /// Variable ID embedded in the location record.
        actual: TrustIrVarId,
    },
    /// Two materialized locations for the same variable overlap.
    OverlappingLiveRange {
        /// Variable with overlapping materialized ranges.
        var: TrustIrVarId,
        /// Earlier range start.
        previous_start: InstId,
        /// Earlier range end.
        previous_end: InstId,
        /// Later range start.
        next_start: InstId,
        /// Later range end.
        next_end: InstId,
    },
}

// ---------------------------------------------------------------------------
// ProvenanceStatus — lifecycle state of a machine instruction's provenance
// ---------------------------------------------------------------------------

/// Status of a provenance entry — tracks whether the instruction is still
/// live or has been removed/created by the compiler.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceStatus {
    /// Instruction is active and maps to source trust_ir instruction(s).
    Active,
    /// Instruction was removed by an optimization pass.
    OptimizedAway {
        /// Which pass removed it.
        pass: PassId,
        /// Why it was safe to remove.
        justification: String,
    },
    /// Instruction was created by the compiler (no direct trust_ir source).
    /// Examples: spill code, frame setup, materialized constants.
    CompilerGenerated {
        /// Which pass or phase created it.
        pass: PassId,
        /// Why it was created.
        reason: String,
    },
}

// ---------------------------------------------------------------------------
// TransformRecord — one entry in the transformation chain
// ---------------------------------------------------------------------------

/// A record of one transformation applied to an instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransformRecord {
    /// Which pass applied this transformation.
    pub pass: PassId,
    /// What kind of transformation.
    pub kind: TransformKind,
}

/// The kind of transformation applied to an instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TransformKind {
    /// Initial lowering from trust_ir to MachIR.
    Lowered,
    /// Replaced by a different instruction (1:1).
    Replaced {
        /// The old instruction that was replaced.
        old: InstId,
    },
    /// Merged from multiple source instructions.
    Merged {
        /// The source instructions that were merged.
        sources: Vec<InstId>,
    },
    /// Cloned from another instruction while the source instruction remains live.
    Cloned {
        /// The source instruction that was cloned.
        source: InstId,
    },
    /// Instruction kept the same [`InstId`] through a pass.
    ///
    /// This covers both truly unchanged instructions and transformations that
    /// mutate opcode, operands, or flags in place while preserving identity.
    Survived,
    /// Binary encoding assigned an offset.
    Encoded {
        /// The binary offset assigned.
        offset: u32,
    },
}

// ---------------------------------------------------------------------------
// ProvenanceEntry — per-instruction provenance metadata
// ---------------------------------------------------------------------------

/// Full provenance metadata for a single machine instruction.
///
/// Tracks the instruction's origin (which trust_ir instruction(s) it came from),
/// its transformation chain (which passes touched it), and its current status.
#[derive(Debug, Clone)]
pub struct ProvenanceEntry {
    /// Source trust_ir instruction(s) this machine instruction originated from.
    /// Usually one, but merges can produce entries with multiple sources.
    pub trust_ir_origins: Vec<TrustIrInstId>,
    /// Ordered record of transformations applied to this instruction.
    pub transforms: Vec<TransformRecord>,
    /// Current lifecycle status.
    pub status: ProvenanceStatus,
}

impl ProvenanceEntry {
    /// Create a new entry originating from a single trust_ir instruction.
    pub fn from_lowering(trust_ir_id: TrustIrInstId, pass: PassId) -> Self {
        Self {
            trust_ir_origins: vec![trust_ir_id],
            transforms: vec![TransformRecord {
                pass,
                kind: TransformKind::Lowered,
            }],
            status: ProvenanceStatus::Active,
        }
    }

    /// Create a compiler-generated entry (no trust_ir source).
    pub fn compiler_generated(pass: PassId, reason: String) -> Self {
        Self {
            trust_ir_origins: Vec::new(),
            transforms: Vec::new(),
            status: ProvenanceStatus::CompilerGenerated { pass, reason },
        }
    }

    /// Returns true if this instruction is still active.
    pub fn is_active(&self) -> bool {
        matches!(self.status, ProvenanceStatus::Active)
    }

    /// Returns true if this instruction was optimized away.
    pub fn is_optimized_away(&self) -> bool {
        matches!(self.status, ProvenanceStatus::OptimizedAway { .. })
    }

    /// Returns true if this instruction was compiler-generated.
    pub fn is_compiler_generated(&self) -> bool {
        matches!(self.status, ProvenanceStatus::CompilerGenerated { .. })
    }
}

// ---------------------------------------------------------------------------
// ProvenanceMap — the core tracking structure
// ---------------------------------------------------------------------------

/// Source-to-binary mapping maintained through every compilation stage.
///
/// The maps are ordered intentionally: provenance can flow into diagnostics,
/// proof artifacts, and rustc bootstrap builds, so iteration order must not
/// depend on hash seeds.
///
/// # Usage
///
/// ```text
/// // 1. ISel creates initial mapping:
/// provenance.record_lowering(trust_ir_id, &[mach_id1, mach_id2], pass);
///
/// // 2. Optimization passes update:
/// provenance.record_replacement(old_id, new_id, pass);   // 1:1 replace
/// provenance.record_merge(&[a, b], merged, pass);        // N:1 merge
/// provenance.record_clone(original, clone, pass);         // 1:N clone
/// provenance.record_deletion(dead_id, pass, "unused");   // DCE
/// provenance.record_creation(new_id, pass, "spill");     // materialization
///
/// // 3. Encoding adds offsets:
/// provenance.record_encoding(mach_id, 0x48);
///
/// // 4. Build transitive closure and query:
/// provenance.build_transitive();
/// let offsets = provenance.query_offset(trust_ir_id);   // trust_ir -> [binary offsets]
/// let sources = provenance.query_source(0x48);       // offset -> [trust_ir ids]
/// ```
#[derive(Debug, Clone)]
pub struct ProvenanceMap {
    /// trust_ir instruction -> MachIR instructions (1:N from ISel).
    trust_ir_to_mach: BTreeMap<TrustIrInstId, Vec<InstId>>,
    /// MachIR instruction -> binary offset (1:1 from encoding).
    mach_to_offset: BTreeMap<InstId, u32>,
    /// Transitive: trust_ir -> binary offsets (built by `build_transitive`).
    trust_ir_to_offset: BTreeMap<TrustIrInstId, Vec<u32>>,
    /// Reverse: binary offset -> trust_ir instructions (built by `build_transitive`).
    offset_to_trust_ir: BTreeMap<u32, Vec<TrustIrInstId>>,
    /// Per-instruction provenance metadata.
    entries: BTreeMap<InstId, ProvenanceEntry>,
    /// Source-visible variable declaration order.
    var_declaration_order: Vec<TrustIrVarId>,
    /// Source-visible variable live ranges.
    var_locations: BTreeMap<TrustIrVarId, Vec<VarLocation>>,
}

impl ProvenanceMap {
    /// Create an empty provenance map.
    pub fn new() -> Self {
        Self {
            trust_ir_to_mach: BTreeMap::new(),
            mach_to_offset: BTreeMap::new(),
            trust_ir_to_offset: BTreeMap::new(),
            offset_to_trust_ir: BTreeMap::new(),
            entries: BTreeMap::new(),
            var_declaration_order: Vec::new(),
            var_locations: BTreeMap::new(),
        }
    }

    // -- Stage 1: ISel (trust_ir -> MachIR) --

    /// Record that a trust_ir instruction was lowered to one or more machine
    /// instructions during instruction selection.
    ///
    /// This is the initial mapping created by ISel. Each trust_ir instruction
    /// may produce multiple machine instructions (e.g., a 64-bit multiply
    /// that expands to multiple AArch64 instructions).
    pub fn record_lowering(
        &mut self,
        trust_ir_id: TrustIrInstId,
        mach_ids: &[InstId],
        pass: PassId,
    ) {
        self.trust_ir_to_mach
            .entry(trust_ir_id)
            .or_default()
            .extend_from_slice(mach_ids);

        for &mach_id in mach_ids {
            self.entries.insert(
                mach_id,
                ProvenanceEntry::from_lowering(trust_ir_id, pass.clone()),
            );
        }
    }

    // -- Stage 2: Optimization pass updates --

    /// Record that an optimization pass replaced instruction `old` with `new`.
    ///
    /// The new instruction inherits all provenance from the old one.
    /// Rule: `provenance[new] = provenance[old]`
    pub fn record_replacement(&mut self, old: InstId, new: InstId, pass: PassId) {
        // Transfer provenance entry from old to new.
        if let Some(mut entry) = self.entries.remove(&old) {
            entry.transforms.push(TransformRecord {
                pass: pass.clone(),
                kind: TransformKind::Replaced { old },
            });
            self.entries.insert(new, entry);
        }

        // Update trust_ir_to_mach: replace old with new in all mappings.
        for mach_ids in self.trust_ir_to_mach.values_mut() {
            for id in mach_ids.iter_mut() {
                if *id == old {
                    *id = new;
                }
            }
        }
    }

    /// Record that multiple instructions were merged into one.
    ///
    /// The merged instruction inherits provenance from all sources.
    /// Rule: `provenance[merged] = union(provenance[sources])`
    pub fn record_merge(&mut self, sources: &[InstId], merged: InstId, pass: PassId) {
        // Collect all trust_ir origins from all source entries.
        let mut all_origins: Vec<TrustIrInstId> = Vec::new();
        let mut all_transforms: Vec<TransformRecord> = Vec::new();

        for &src in sources {
            if let Some(entry) = self.entries.remove(&src) {
                for origin in &entry.trust_ir_origins {
                    if !all_origins.contains(origin) {
                        all_origins.push(*origin);
                    }
                }
                all_transforms.extend(entry.transforms);
            }
        }

        // Create merged entry.
        let mut merged_entry = ProvenanceEntry {
            trust_ir_origins: all_origins,
            transforms: all_transforms,
            status: ProvenanceStatus::Active,
        };
        merged_entry.transforms.push(TransformRecord {
            pass: pass.clone(),
            kind: TransformKind::Merged {
                sources: sources.to_vec(),
            },
        });
        self.entries.insert(merged, merged_entry);

        // Update trust_ir_to_mach: replace all sources with merged.
        for mach_ids in self.trust_ir_to_mach.values_mut() {
            let mut found = false;
            mach_ids.retain(|id| {
                if sources.contains(id) {
                    if !found {
                        found = true;
                        // Keep this slot, will be overwritten below.
                        true
                    } else {
                        false
                    }
                } else {
                    true
                }
            });
            // Replace the first occurrence of a source with merged.
            for id in mach_ids.iter_mut() {
                if sources.contains(id) {
                    *id = merged;
                    break;
                }
            }
        }
    }

    /// Record that consumed instructions and still-live dependencies were
    /// merged into one instruction.
    ///
    /// This is for rewrites where `merged` now semantically depends on another
    /// instruction that remains in the stream, such as a branch reusing flags
    /// from a preceding compare. Consumed sources are removed like
    /// [`record_merge`]; live sources remain active and gain an additional
    /// trust_ir-to-Mach mapping to `merged`.
    pub fn record_merge_with_live_sources(
        &mut self,
        consumed_sources: &[InstId],
        live_sources: &[InstId],
        merged: InstId,
        pass: PassId,
    ) {
        let mut all_origins: Vec<TrustIrInstId> = Vec::new();
        let mut all_transforms: Vec<TransformRecord> = Vec::new();
        let mut all_sources: Vec<InstId> = Vec::new();

        for &src in live_sources {
            if let Some(entry) = self.entries.get(&src) {
                for origin in &entry.trust_ir_origins {
                    if !all_origins.contains(origin) {
                        all_origins.push(*origin);
                    }
                }
                all_transforms.extend(entry.transforms.clone());
                if !all_sources.contains(&src) {
                    all_sources.push(src);
                }
            }
        }

        for &src in consumed_sources {
            if let Some(entry) = self.entries.remove(&src) {
                for origin in &entry.trust_ir_origins {
                    if !all_origins.contains(origin) {
                        all_origins.push(*origin);
                    }
                }
                all_transforms.extend(entry.transforms);
                if !all_sources.contains(&src) {
                    all_sources.push(src);
                }
            }
        }

        let mut merged_entry = ProvenanceEntry {
            trust_ir_origins: all_origins.clone(),
            transforms: all_transforms,
            status: ProvenanceStatus::Active,
        };
        merged_entry.transforms.push(TransformRecord {
            pass,
            kind: TransformKind::Merged {
                sources: all_sources.clone(),
            },
        });
        self.entries.insert(merged, merged_entry);

        for mach_ids in self.trust_ir_to_mach.values_mut() {
            let mut found = false;
            mach_ids.retain(|id| {
                if consumed_sources.contains(id) {
                    if !found {
                        found = true;
                        true
                    } else {
                        false
                    }
                } else {
                    true
                }
            });
            for id in mach_ids.iter_mut() {
                if consumed_sources.contains(id) {
                    *id = merged;
                    break;
                }
            }
        }

        for origin in all_origins {
            let mach_ids = self.trust_ir_to_mach.entry(origin).or_default();
            if !mach_ids.contains(&merged) {
                mach_ids.push(merged);
            }
        }
    }

    /// Record that an optimization pass cloned `source` into `clone`.
    ///
    /// The clone inherits provenance from the source while the source remains
    /// live. This is useful for transforms such as loop unrolling where one
    /// trust_ir origin fans out to the original machine instruction plus cloned
    /// copies.
    ///
    /// Unknown source instructions are ignored, matching the other update
    /// helpers' conservative no-op behavior.
    pub fn record_clone(&mut self, source: InstId, clone: InstId, pass: PassId) {
        let Some(mut clone_entry) = self.entries.get(&source).cloned() else {
            return;
        };

        clone_entry.transforms.push(TransformRecord {
            pass,
            kind: TransformKind::Cloned { source },
        });
        self.entries.insert(clone, clone_entry.clone());

        for origin in clone_entry.trust_ir_origins {
            let mach_ids = self.trust_ir_to_mach.entry(origin).or_default();
            if !mach_ids.contains(&clone) {
                mach_ids.push(clone);
            }
        }
    }

    /// Record that an instruction was deleted by an optimization pass (DCE).
    ///
    /// The instruction is marked as OptimizedAway with a justification.
    pub fn record_deletion(
        &mut self,
        inst: InstId,
        pass: PassId,
        justification: impl Into<String>,
    ) {
        if let Some(entry) = self.entries.get_mut(&inst) {
            entry.status = ProvenanceStatus::OptimizedAway {
                pass,
                justification: justification.into(),
            };
        }
        // Note: we keep the entry in the map so queries can report
        // "this trust_ir instruction was optimized away" rather than silence.
    }

    /// Record that a new instruction was created by the compiler (materialization,
    /// spill code, frame setup, etc.) with no direct trust_ir source.
    pub fn record_creation(&mut self, inst: InstId, pass: PassId, reason: impl Into<String>) {
        self.entries.insert(
            inst,
            ProvenanceEntry::compiler_generated(pass, reason.into()),
        );
    }

    /// Record that an optimization pass kept an instruction's `InstId` stable.
    ///
    /// Use this for in-place rewrites where the instruction's opcode, operands,
    /// flags, or annotations may change, but the existing machine instruction
    /// slot remains the representative for the same source provenance.
    ///
    /// Unknown instructions are ignored so callers can conservatively report
    /// only the IDs they know about without first checking the map.
    pub fn record_in_place_transform(&mut self, inst: InstId, pass: PassId) {
        if let Some(entry) = self.entries.get_mut(&inst) {
            entry.transforms.push(TransformRecord {
                pass,
                kind: TransformKind::Survived,
            });
        }
    }

    // -- Variable live-range tracking --

    /// Record an initial live range for a source-visible trust_ir variable.
    ///
    /// Ranges are stored sorted by `(start, end)` so later DWARF consumers can
    /// iterate deterministically. `loc.var` must match `var`; mismatches are
    /// reported as typed validation errors.
    pub fn declare_var(
        &mut self,
        var: TrustIrVarId,
        loc: VarLocation,
    ) -> Result<(), VarLocationError> {
        if loc.var != var {
            return Err(VarLocationError::VarMismatch {
                expected: var,
                actual: loc.var,
            });
        }

        let mut ranges = self.var_locations.get(&var).cloned().unwrap_or_default();
        ranges.push(loc);
        Self::sort_var_ranges(&mut ranges);
        Self::validate_var_ranges(var, &ranges)?;

        self.record_var_declaration(var);
        self.var_locations.insert(var, ranges);
        Ok(())
    }

    /// Rewrite all tracked variable locations through a compiler pass.
    ///
    /// The callback can split, replace, delete, or move ranges between
    /// variables. Declaration order is preserved for existing variables and new
    /// variables are appended when first returned by the callback.
    pub fn rewrite_var_locations(
        &mut self,
        _pass: PassId,
        mut f: impl FnMut(&VarLocation) -> Vec<VarLocation>,
    ) -> Result<(), VarLocationError> {
        let declared = self.var_declaration_order.clone();
        let old_locations = self.var_locations.clone();
        let mut declaration_order = declared.clone();
        let mut rewritten: BTreeMap<TrustIrVarId, Vec<VarLocation>> = declared
            .iter()
            .copied()
            .map(|var| (var, Vec::new()))
            .collect();

        for ranges in old_locations.values() {
            for loc in ranges {
                for new_loc in f(loc) {
                    if !declaration_order.contains(&new_loc.var) {
                        declaration_order.push(new_loc.var);
                    }
                    rewritten.entry(new_loc.var).or_default().push(new_loc);
                }
            }
        }

        for (&var, ranges) in rewritten.iter_mut() {
            Self::sort_var_ranges(ranges);
            Self::validate_var_ranges(var, ranges)?;
        }
        self.var_declaration_order = declaration_order;
        self.var_locations = rewritten;
        Ok(())
    }

    /// Mark a variable unavailable from `start` forward over its known range.
    ///
    /// Existing ranges that cross `start` are truncated to a live prefix. Ranges
    /// at or after `start` are replaced by one dead range that covers the known
    /// tail. If no known tail exists, an open-ended sentinel range is recorded.
    pub fn kill_var(
        &mut self,
        var: TrustIrVarId,
        start: InstId,
        pass: PassId,
        reason: DeadReason,
    ) -> Result<(), VarLocationError> {
        let ranges = self.var_locations.get(&var).cloned().unwrap_or_default();
        let mut rewritten = Vec::new();
        let mut dead_end: Option<InstId> = None;

        for loc in &ranges {
            if loc.end <= start {
                rewritten.push(loc.clone());
                continue;
            }

            dead_end = Some(dead_end.map_or(loc.end, |end| end.max(loc.end)));
            if loc.start < start {
                let mut live_prefix = loc.clone();
                live_prefix.end = start;
                rewritten.push(live_prefix);
            }
        }

        let end = dead_end.unwrap_or(InstId(u32::MAX));
        if start < end {
            rewritten.push(VarLocation {
                var,
                start,
                end,
                value: LocationExpr::Dead {
                    killed_by: pass,
                    reason,
                },
            });
        }

        Self::sort_var_ranges(&mut rewritten);
        Self::validate_var_ranges(var, &rewritten)?;

        self.record_var_declaration(var);
        self.var_locations.insert(var, rewritten);
        Ok(())
    }

    /// Query all live-range records for `var`, sorted by `start`.
    pub fn var_live_ranges(&self, var: TrustIrVarId) -> &[VarLocation] {
        self.var_locations.get(&var).map_or(&[], Vec::as_slice)
    }

    /// Query variables in first-declaration order.
    pub fn declared_vars(&self) -> &[TrustIrVarId] {
        &self.var_declaration_order
    }

    fn record_var_declaration(&mut self, var: TrustIrVarId) {
        if !self.var_declaration_order.contains(&var) {
            self.var_declaration_order.push(var);
        }
        self.var_locations.entry(var).or_default();
    }

    fn sort_var_ranges(ranges: &mut [VarLocation]) {
        ranges.sort_by_key(|loc| (loc.start, loc.end));
    }

    /// Validate one variable's live-range records.
    pub fn validate_var_ranges(
        var: TrustIrVarId,
        ranges: &[VarLocation],
    ) -> Result<(), VarLocationError> {
        let mut previous_live: Option<&VarLocation> = None;

        for loc in ranges {
            if loc.var != var {
                return Err(VarLocationError::VarMismatch {
                    expected: var,
                    actual: loc.var,
                });
            }
            if loc.start >= loc.end {
                return Err(VarLocationError::InvalidRange {
                    var,
                    start: loc.start,
                    end: loc.end,
                });
            }

            if !loc.is_dead() {
                if let Some(previous) = previous_live
                    && loc.start < previous.end
                {
                    return Err(VarLocationError::OverlappingLiveRange {
                        var,
                        previous_start: previous.start,
                        previous_end: previous.end,
                        next_start: loc.start,
                        next_end: loc.end,
                    });
                }
                previous_live = Some(loc);
            }
        }

        Ok(())
    }

    // -- Stage 3: Encoding (MachIR -> binary offset) --

    /// Record that a machine instruction was encoded at a binary offset.
    pub fn record_encoding(&mut self, inst: InstId, offset: u32) {
        self.mach_to_offset.insert(inst, offset);

        if let Some(entry) = self.entries.get_mut(&inst) {
            entry.transforms.push(TransformRecord {
                pass: PassId::new("encoding"),
                kind: TransformKind::Encoded { offset },
            });
        }
    }

    // -- Stage 4: Build transitive closure --

    /// Build the transitive trust_ir -> binary offset mapping.
    ///
    /// Must be called after all encoding is complete. Populates
    /// `trust_ir_to_offset` and `offset_to_trust_ir` for query use.
    pub fn build_transitive(&mut self) {
        self.trust_ir_to_offset.clear();
        self.offset_to_trust_ir.clear();

        for (&trust_ir_id, mach_ids) in &self.trust_ir_to_mach {
            let mut offsets = Vec::new();
            for &mach_id in mach_ids {
                // Only include active instructions with binary offsets.
                if let Some(&offset) = self.mach_to_offset.get(&mach_id)
                    && self.entries.get(&mach_id).is_none_or(|e| e.is_active())
                {
                    offsets.push(offset);
                    self.offset_to_trust_ir
                        .entry(offset)
                        .or_default()
                        .push(trust_ir_id);
                }
            }
            offsets.sort_unstable();
            offsets.dedup();
            if !offsets.is_empty() {
                self.trust_ir_to_offset.insert(trust_ir_id, offsets);
            }
        }

        // Deduplicate reverse mapping entries.
        for trust_ir_ids in self.offset_to_trust_ir.values_mut() {
            trust_ir_ids.sort_unstable();
            trust_ir_ids.dedup();
        }
    }

    // -- Query methods --

    /// Query the binary offsets for a trust_ir instruction.
    ///
    /// Returns `None` if the trust_ir instruction has no binary representation
    /// (e.g., it was optimized away entirely).
    pub fn query_offset(&self, trust_ir_id: TrustIrInstId) -> Option<&[u32]> {
        self.trust_ir_to_offset
            .get(&trust_ir_id)
            .map(|v| v.as_slice())
    }

    /// Query which trust_ir instructions contributed to a binary offset.
    ///
    /// Returns `None` if the offset is compiler-generated with no trust_ir source.
    pub fn query_source(&self, offset: u32) -> Option<&[TrustIrInstId]> {
        self.offset_to_trust_ir.get(&offset).map(|v| v.as_slice())
    }

    /// Iterate encoded offsets that have active trust_ir provenance.
    ///
    /// The iterator is sorted by byte offset. Call [`build_transitive`](Self::build_transitive)
    /// after encoding before using this accessor; otherwise it reflects the
    /// most recently built transitive mapping.
    pub fn source_offsets(&self) -> impl Iterator<Item = (u32, &[TrustIrInstId])> + '_ {
        self.offset_to_trust_ir
            .iter()
            .map(|(&offset, trust_ir_ids)| (offset, trust_ir_ids.as_slice()))
    }

    /// Get the provenance entry for a machine instruction.
    pub fn get_entry(&self, inst: InstId) -> Option<&ProvenanceEntry> {
        self.entries.get(&inst)
    }

    /// Get the binary offset for a machine instruction.
    pub fn get_offset(&self, inst: InstId) -> Option<u32> {
        self.mach_to_offset.get(&inst).copied()
    }

    /// Get all machine instructions that a trust_ir instruction was lowered to.
    pub fn get_mach_insts(&self, trust_ir_id: TrustIrInstId) -> Option<&[InstId]> {
        self.trust_ir_to_mach
            .get(&trust_ir_id)
            .map(|v| v.as_slice())
    }

    /// Returns the number of trust_ir instructions tracked.
    pub fn num_trust_ir_entries(&self) -> usize {
        self.trust_ir_to_mach.len()
    }

    /// Returns the number of machine instructions with provenance entries.
    pub fn num_mach_entries(&self) -> usize {
        self.entries.len()
    }

    /// Returns the number of encoded machine instructions.
    pub fn num_encoded(&self) -> usize {
        self.mach_to_offset.len()
    }

    /// Returns an iterator over all trust_ir instructions that were optimized away.
    pub fn optimized_away(&self) -> Vec<(InstId, &ProvenanceEntry)> {
        self.entries
            .iter()
            .filter(|(_, e)| e.is_optimized_away())
            .map(|(&id, e)| (id, e))
            .collect()
    }

    /// Returns an iterator over all compiler-generated instructions.
    pub fn compiler_generated(&self) -> Vec<(InstId, &ProvenanceEntry)> {
        self.entries
            .iter()
            .filter(|(_, e)| e.is_compiler_generated())
            .map(|(&id, e)| (id, e))
            .collect()
    }

    /// Returns a summary of provenance statistics.
    pub fn stats(&self) -> ProvenanceStats {
        let mut active = 0u32;
        let mut optimized_away = 0u32;
        let mut compiler_generated = 0u32;

        for entry in self.entries.values() {
            match entry.status {
                ProvenanceStatus::Active => active += 1,
                ProvenanceStatus::OptimizedAway { .. } => optimized_away += 1,
                ProvenanceStatus::CompilerGenerated { .. } => compiler_generated += 1,
            }
        }

        ProvenanceStats {
            trust_ir_instructions: self.trust_ir_to_mach.len() as u32,
            mach_instructions: self.entries.len() as u32,
            active,
            optimized_away,
            compiler_generated,
            encoded: self.mach_to_offset.len() as u32,
            transitive_mappings: self.trust_ir_to_offset.len() as u32,
        }
    }
}

impl Default for ProvenanceMap {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// ProvenanceStats — summary statistics
// ---------------------------------------------------------------------------

/// Summary statistics for a provenance map.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenanceStats {
    /// Number of trust_ir instructions tracked.
    pub trust_ir_instructions: u32,
    /// Total number of machine instructions with provenance entries.
    pub mach_instructions: u32,
    /// Number of active (live) machine instructions.
    pub active: u32,
    /// Number of machine instructions optimized away.
    pub optimized_away: u32,
    /// Number of compiler-generated instructions.
    pub compiler_generated: u32,
    /// Number of machine instructions with binary offsets.
    pub encoded: u32,
    /// Number of trust_ir instructions with transitive binary mappings.
    pub transitive_mappings: u32,
}

// ---------------------------------------------------------------------------
// LoweringProvenance — TV-1 per-machine-instruction lowering provenance
// ---------------------------------------------------------------------------
//
// SCHEMA (consumed by TV-2/TV-3 translation validation and the ENC-4 / Lean
// encoder-linkage work — treat changes as schema changes, not refactors):
//
// Every machine instruction emitted by an instruction selector carries exactly
// one `LoweringProvenance` value stating WHICH lowering-input (LIR) instruction
// the ISel was dispatching when it emitted that machine instruction:
//
// - `LoweringProvenance::SourceInst { id, digest, trust_ir_inst }` — the
//   instruction was emitted while lowering the source instruction at
//   function-local coordinates `id` (LIR block id + index within that block).
//   `digest` is a compact, verifier-reproducible digest of the source
//   instruction's (opcode incl. any embedded type/width, operand arity) — see
//   [`SourceInstDigest::compute`]. `trust_ir_inst` additionally names the
//   originating trust_ir-crate instruction when the frontend supplied a
//   provenance sidecar (currently the AArch64 path only; `None` on x86).
//   A multi-instruction expansion (one source inst -> many machine insts)
//   stamps the SAME `id` on every emitted instruction. An idiom fusion that
//   consumes several source instructions (overflow/smulh/vector-sequence
//   interceptors) stamps the sequence's ANCHOR instruction: the source
//   instruction at the dispatch index where emission happened.
// - `LoweringProvenance::Synthetic { reason }` — the instruction has NO single
//   source instruction (ABI formal-argument moves, prologue/epilogue,
//   phi-elimination / regalloc glue, post-ISel fixups). The `reason` says why.
//   `SyntheticReason::Unattributed` is the schema's DEFAULT: any instruction
//   created outside a stamping window (including by downstream passes that do
//   not participate in provenance) reports it. The load-bearing invariant is
//   *never a wrong attribution*: an instruction is either correctly attributed
//   to its source instruction or explicitly synthetic — under-attribution
//   (Synthetic where a source exists) is allowed, misattribution is not.
//
// Pass-preservation scoping (TV-1 decision for the roadmap's open question):
// provenance is guaranteed faithful on the RAW pre-pass ISel output only.
// x86 carries it as a field on `X86ISelInst`, so post-ISel passes that
// insert/delete/clone instructions keep existing stamps with instructions and
// default new instructions to `Unattributed` (safe, never wrong). AArch64
// carries it as a parallel sidecar on `ISelBlock` and, through the
// ISel->MachFunction adapter, as an `InstId`-keyed sidecar on `MachFunction`
// (arena `InstId`s are append-only and never renumbered); pass-created or
// pass-cloned instructions have no entry and report `Unattributed`. Consumers
// that need operand-identity binding (TV-3) must therefore run on pre-pass
// output or add per-pass preservation rules first.

/// Function-local coordinates of a lowering-input (LIR) instruction as seen by
/// an instruction selector: the LIR block id plus the instruction's index
/// within that block's instruction list.
///
/// This is deliberately independent of the trust_ir crate (same rationale as
/// [`TrustIrInstId`]): the pair is meaningful against the exact LIR function
/// that was handed to ISel, which is what TV-2/TV-3 verifiers replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct SourceInstId {
    /// LIR block id (`trust_cg_lower::instructions::Block.0`).
    pub block: u32,
    /// Index of the instruction within that block's instruction list.
    pub index: u32,
}

impl core::fmt::Display for SourceInstId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "lir{}.{}", self.block, self.index)
    }
}

/// Compact digest of a lowering-input instruction's (opcode, operand shape,
/// width) for [`LoweringProvenance::SourceInst`].
///
/// Computed with [`SourceInstDigest::compute`] as FNV-1a/64 over the opcode's
/// canonical `Debug` rendering plus the argument and result arities. The
/// `Debug` rendering embeds the opcode's type/width payload where the LIR
/// opcode structurally carries one (e.g. `Iconst { ty: I32, imm: 5 }`,
/// `Load { ty: I64, .. }`); opcodes whose width lives only on their SSA values
/// (e.g. `Iadd`) contribute opcode + arity, and a width cross-check for those
/// is a TV-2 concern resolved against the replayed LIR function. The digest is
/// deterministic and reproducible by any verifier holding the same LIR
/// instruction — it is an integrity binding, not a proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct SourceInstDigest(pub u64);

impl SourceInstDigest {
    /// FNV-1a/64 offset basis.
    const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    /// FNV-1a/64 prime.
    const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

    /// Compute the digest from an opcode's canonical `Debug` rendering and the
    /// instruction's operand shape (argument / result arities).
    ///
    /// Stable by construction (no `std::hash` involvement): FNV-1a/64 over
    /// `opcode_debug` bytes, a `0xFF` separator, then `num_args` and
    /// `num_results` as little-endian u64 words.
    pub fn compute(opcode_debug: &str, num_args: usize, num_results: usize) -> Self {
        let mut h = Self::FNV_OFFSET;
        let mut step = |byte: u8| {
            h ^= u64::from(byte);
            h = h.wrapping_mul(Self::FNV_PRIME);
        };
        for b in opcode_debug.as_bytes() {
            step(*b);
        }
        step(0xFF);
        for b in (num_args as u64).to_le_bytes() {
            step(b);
        }
        for b in (num_results as u64).to_le_bytes() {
            step(b);
        }
        Self(h)
    }
}

/// Why a machine instruction has no single lowering-input source instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum SyntheticReason {
    /// Default: emitted outside any provenance-stamping window. Covers
    /// instructions created by downstream stages (opt passes, regalloc
    /// rewrites, post-RA fixups, prologue/epilogue insertion) that do not
    /// participate in provenance stamping yet, and any ISel emission that
    /// happens outside the per-source-instruction dispatch loop.
    Unattributed,
    /// ABI glue moving the function's formal arguments from their ABI
    /// locations into virtual registers at function entry.
    FormalArguments,
    /// Block-argument / phi copy glue inserted to implement control-flow-edge
    /// value transfer (reserved for stampers that distinguish it).
    BlockParamCopy,
    /// Function prologue/epilogue frame setup (reserved; prologue insertion
    /// currently happens post-ISel and reports `Unattributed`).
    PrologueEpilogue,
    /// Register-allocator glue: spill stores/reloads and inserted copies
    /// (reserved; regalloc currently reports `Unattributed`).
    RegAllocGlue,
}

/// TV-1: which lowering-input instruction produced a machine instruction.
///
/// See the module-level `LoweringProvenance` schema comment above for the full
/// contract, the never-wrong-attribution invariant, and the pass-preservation
/// scoping decision. Strictly additive metadata: nothing on the compile path
/// consumes it yet (TV-2/TV-3 will), so it must never influence emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum LoweringProvenance {
    /// Emitted while lowering the identified source (LIR) instruction.
    SourceInst {
        /// Function-local (block, index) coordinates of the source instruction.
        id: SourceInstId,
        /// Compact digest of the source instruction; see [`SourceInstDigest`].
        digest: SourceInstDigest,
        /// Originating trust_ir-crate instruction, when the frontend supplied
        /// a provenance sidecar (AArch64 path; `None` on x86 today).
        trust_ir_inst: Option<TrustIrInstId>,
    },
    /// Synthesized with no single source instruction.
    Synthetic {
        /// Why there is no source attribution.
        reason: SyntheticReason,
    },
}

impl LoweringProvenance {
    /// The schema default: synthetic, reason [`SyntheticReason::Unattributed`].
    pub const UNATTRIBUTED: Self = Self::Synthetic {
        reason: SyntheticReason::Unattributed,
    };

    /// True when this instruction is attributed to a source instruction.
    pub fn is_source_attributed(&self) -> bool {
        matches!(self, Self::SourceInst { .. })
    }

    /// The source coordinates, when attributed.
    pub fn source_id(&self) -> Option<SourceInstId> {
        match self {
            Self::SourceInst { id, .. } => Some(*id),
            Self::Synthetic { .. } => None,
        }
    }
}

impl Default for LoweringProvenance {
    fn default() -> Self {
        Self::UNATTRIBUTED
    }
}

// ---------------------------------------------------------------------------
// LoweringProvenanceCoverage — per-opcode stamping-coverage report (TV-1
// done-criterion; input to the TV-2 absent-provenance fail-closed flip)
// ---------------------------------------------------------------------------

/// Per-machine-opcode counts of source-attributed vs synthetic instructions.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct OpcodeProvenanceCount {
    /// Instructions stamped `LoweringProvenance::SourceInst`.
    pub source_attributed: u64,
    /// Instructions stamped `LoweringProvenance::Synthetic` (any reason).
    pub synthetic: u64,
}

/// Stamping-coverage measurement artifact for TV-1/TV-2.
///
/// TV-2 flips absent-provenance to fail-closed only after the corpus shows
/// the expected stamping coverage per opcode family; this report is the
/// non-vibes measurement that decision consumes. Keys are machine-opcode
/// mnemonics (`Debug` names), values count source-attributed vs synthetic
/// instructions. Purely observational: no gate consumes it on the compile
/// path.
#[derive(Debug, Clone, Default, Serialize)]
pub struct LoweringProvenanceCoverage {
    /// Machine-opcode mnemonic -> attribution counts (BTreeMap for
    /// deterministic iteration/reporting).
    pub per_opcode: BTreeMap<String, OpcodeProvenanceCount>,
}

impl LoweringProvenanceCoverage {
    /// Record one machine instruction's provenance under its opcode mnemonic.
    pub fn record(&mut self, opcode_mnemonic: &str, provenance: &LoweringProvenance) {
        let entry = self
            .per_opcode
            .entry(opcode_mnemonic.to_string())
            .or_default();
        if provenance.is_source_attributed() {
            entry.source_attributed += 1;
        } else {
            entry.synthetic += 1;
        }
    }

    /// Total (source_attributed, synthetic) counts across all opcodes.
    pub fn totals(&self) -> (u64, u64) {
        self.per_opcode.values().fold((0, 0), |(s, y), c| {
            (s + c.source_attributed, y + c.synthetic)
        })
    }

    /// Fraction of instructions that are source-attributed, in `[0.0, 1.0]`.
    /// Returns 1.0 for an empty report (vacuously covered).
    pub fn source_attributed_fraction(&self) -> f64 {
        let (source, synthetic) = self.totals();
        let total = source + synthetic;
        if total == 0 {
            1.0
        } else {
            source as f64 / total as f64
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn isel_pass() -> PassId {
        PassId::new("isel")
    }

    fn dce_pass() -> PassId {
        PassId::new("dce")
    }

    fn peephole_pass() -> PassId {
        PassId::new("peephole")
    }

    fn regalloc_pass() -> PassId {
        PassId::new("regalloc")
    }

    // -- TrustIrInstId tests --

    #[test]
    fn trust_ir_inst_id_display() {
        assert_eq!(format!("{}", TrustIrInstId(0)), "trust_ir0");
        assert_eq!(format!("{}", TrustIrInstId(42)), "trust_ir42");
    }

    #[test]
    fn trust_ir_inst_id_equality_and_ordering() {
        assert_eq!(TrustIrInstId(5), TrustIrInstId(5));
        assert_ne!(TrustIrInstId(5), TrustIrInstId(6));
        assert!(TrustIrInstId(0) < TrustIrInstId(1));
    }

    #[test]
    fn trust_ir_inst_id_hash() {
        use std::collections::BTreeSet;
        let mut set = BTreeSet::new();
        set.insert(TrustIrInstId(0));
        set.insert(TrustIrInstId(0)); // duplicate
        set.insert(TrustIrInstId(1));
        assert_eq!(set.len(), 2);
    }

    // -- PassId tests --

    #[test]
    fn pass_id_creation_and_display() {
        let p = PassId::new("dce");
        assert_eq!(p.name(), "dce");
        assert_eq!(format!("{}", p), "dce");
    }

    // -- ProvenanceEntry tests --

    #[test]
    fn provenance_entry_from_lowering() {
        let entry = ProvenanceEntry::from_lowering(TrustIrInstId(10), isel_pass());
        assert!(entry.is_active());
        assert!(!entry.is_optimized_away());
        assert!(!entry.is_compiler_generated());
        assert_eq!(entry.trust_ir_origins.len(), 1);
        assert_eq!(entry.trust_ir_origins[0], TrustIrInstId(10));
        assert_eq!(entry.transforms.len(), 1);
        assert_eq!(entry.transforms[0].kind, TransformKind::Lowered);
    }

    #[test]
    fn provenance_entry_compiler_generated() {
        let entry =
            ProvenanceEntry::compiler_generated(regalloc_pass(), "spill reload".to_string());
        assert!(!entry.is_active());
        assert!(!entry.is_optimized_away());
        assert!(entry.is_compiler_generated());
        assert!(entry.trust_ir_origins.is_empty());
    }

    // -- ProvenanceMap: basic lowering --

    #[test]
    fn record_lowering_single_inst() {
        let mut map = ProvenanceMap::new();
        let trust_ir = TrustIrInstId(0);
        let mach = InstId(0);

        map.record_lowering(trust_ir, &[mach], isel_pass());

        assert_eq!(map.num_trust_ir_entries(), 1);
        assert_eq!(map.num_mach_entries(), 1);
        assert_eq!(map.get_mach_insts(trust_ir), Some(&[mach][..]));

        let entry = map.get_entry(mach).unwrap();
        assert!(entry.is_active());
        assert_eq!(entry.trust_ir_origins, vec![trust_ir]);
    }

    #[test]
    fn record_lowering_one_to_many() {
        let mut map = ProvenanceMap::new();
        let trust_ir = TrustIrInstId(5);
        let mach_ids = [InstId(10), InstId(11), InstId(12)];

        map.record_lowering(trust_ir, &mach_ids, isel_pass());

        assert_eq!(map.num_trust_ir_entries(), 1);
        assert_eq!(map.num_mach_entries(), 3);
        assert_eq!(map.get_mach_insts(trust_ir).unwrap().len(), 3);
    }

    #[test]
    fn record_lowering_multiple_trust_ir() {
        let mut map = ProvenanceMap::new();
        map.record_lowering(TrustIrInstId(0), &[InstId(0)], isel_pass());
        map.record_lowering(TrustIrInstId(1), &[InstId(1), InstId(2)], isel_pass());
        map.record_lowering(TrustIrInstId(2), &[InstId(3)], isel_pass());

        assert_eq!(map.num_trust_ir_entries(), 3);
        assert_eq!(map.num_mach_entries(), 4);
    }

    // -- ProvenanceMap: replacement --

    #[test]
    fn record_replacement_transfers_provenance() {
        let mut map = ProvenanceMap::new();
        let trust_ir = TrustIrInstId(0);
        let old = InstId(0);
        let new = InstId(1);

        map.record_lowering(trust_ir, &[old], isel_pass());
        map.record_replacement(old, new, peephole_pass());

        // Old entry should be gone.
        assert!(map.get_entry(old).is_none());

        // New entry should have the old's provenance.
        let entry = map.get_entry(new).unwrap();
        assert!(entry.is_active());
        assert_eq!(entry.trust_ir_origins, vec![trust_ir]);
        assert_eq!(entry.transforms.len(), 2); // lowered + replaced

        // trust_ir_to_mach should point to new.
        let mach_ids = map.get_mach_insts(trust_ir).unwrap();
        assert_eq!(mach_ids, &[new]);
    }

    // -- ProvenanceMap: merge --

    #[test]
    fn record_merge_combines_provenance() {
        let mut map = ProvenanceMap::new();
        let trust_ir_a = TrustIrInstId(0);
        let trust_ir_b = TrustIrInstId(1);
        let inst_a = InstId(0);
        let inst_b = InstId(1);
        let merged = InstId(2);

        map.record_lowering(trust_ir_a, &[inst_a], isel_pass());
        map.record_lowering(trust_ir_b, &[inst_b], isel_pass());
        map.record_merge(&[inst_a, inst_b], merged, peephole_pass());

        // Source entries should be removed.
        assert!(map.get_entry(inst_a).is_none());
        assert!(map.get_entry(inst_b).is_none());

        // Merged entry has both origins.
        let entry = map.get_entry(merged).unwrap();
        assert!(entry.is_active());
        assert_eq!(entry.trust_ir_origins.len(), 2);
        assert!(entry.trust_ir_origins.contains(&trust_ir_a));
        assert!(entry.trust_ir_origins.contains(&trust_ir_b));
    }

    // -- ProvenanceMap: clone --

    #[test]
    fn record_clone_fans_out_provenance() {
        let mut map = ProvenanceMap::new();
        let trust_ir = TrustIrInstId(3);
        let source = InstId(10);
        let clone = InstId(11);

        map.record_lowering(trust_ir, &[source], isel_pass());
        map.record_clone(source, clone, peephole_pass());

        let source_entry = map.get_entry(source).unwrap();
        assert!(source_entry.is_active());
        assert_eq!(source_entry.trust_ir_origins, vec![trust_ir]);
        assert_eq!(source_entry.transforms.len(), 1);

        let clone_entry = map.get_entry(clone).unwrap();
        assert!(clone_entry.is_active());
        assert_eq!(clone_entry.trust_ir_origins, vec![trust_ir]);
        assert_eq!(clone_entry.transforms.len(), 2);
        assert_eq!(clone_entry.transforms[1].pass, peephole_pass());
        assert_eq!(
            clone_entry.transforms[1].kind,
            TransformKind::Cloned { source }
        );
        assert_eq!(map.get_mach_insts(trust_ir), Some(&[source, clone][..]));
    }

    #[test]
    fn build_transitive_includes_cloned_offsets() {
        let mut map = ProvenanceMap::new();
        let trust_ir = TrustIrInstId(4);
        let source = InstId(20);
        let clone = InstId(21);

        map.record_lowering(trust_ir, &[source], isel_pass());
        map.record_clone(source, clone, peephole_pass());
        map.record_encoding(source, 0x10);
        map.record_encoding(clone, 0x20);
        map.build_transitive();

        assert_eq!(map.query_offset(trust_ir), Some(&[0x10, 0x20][..]));
        assert_eq!(map.query_source(0x10), Some(&[trust_ir][..]));
        assert_eq!(map.query_source(0x20), Some(&[trust_ir][..]));
    }

    #[test]
    fn record_clone_unknown_source_is_noop() {
        let mut map = ProvenanceMap::new();
        map.record_clone(InstId(99), InstId(100), peephole_pass());

        assert_eq!(map.num_mach_entries(), 0);
        assert!(map.get_entry(InstId(100)).is_none());
    }

    // -- ProvenanceMap: deletion --

    #[test]
    fn record_deletion_marks_optimized_away() {
        let mut map = ProvenanceMap::new();
        let trust_ir = TrustIrInstId(0);
        let inst = InstId(0);

        map.record_lowering(trust_ir, &[inst], isel_pass());
        map.record_deletion(inst, dce_pass(), "result unused");

        let entry = map.get_entry(inst).unwrap();
        assert!(entry.is_optimized_away());
        assert!(!entry.is_active());
        assert_eq!(entry.trust_ir_origins, vec![trust_ir]);
    }

    // -- ProvenanceMap: creation --

    #[test]
    fn record_creation_marks_compiler_generated() {
        let mut map = ProvenanceMap::new();
        let inst = InstId(100);

        map.record_creation(inst, regalloc_pass(), "spill reload for vreg %5");

        let entry = map.get_entry(inst).unwrap();
        assert!(entry.is_compiler_generated());
        assert!(entry.trust_ir_origins.is_empty());
    }

    // -- ProvenanceMap: encoding --

    #[test]
    fn record_encoding_stores_offset() {
        let mut map = ProvenanceMap::new();
        let trust_ir = TrustIrInstId(0);
        let inst = InstId(0);

        map.record_lowering(trust_ir, &[inst], isel_pass());
        map.record_encoding(inst, 0x48);

        assert_eq!(map.get_offset(inst), Some(0x48));
        assert_eq!(map.num_encoded(), 1);

        // Check that encoding is in the transform chain.
        let entry = map.get_entry(inst).unwrap();
        let last = entry.transforms.last().unwrap();
        assert_eq!(last.kind, TransformKind::Encoded { offset: 0x48 });
    }

    // -- ProvenanceMap: transitive closure --

    #[test]
    fn build_transitive_basic() {
        let mut map = ProvenanceMap::new();

        // trust_ir0 -> [inst0, inst1], trust_ir1 -> [inst2]
        map.record_lowering(TrustIrInstId(0), &[InstId(0), InstId(1)], isel_pass());
        map.record_lowering(TrustIrInstId(1), &[InstId(2)], isel_pass());

        // Encode all.
        map.record_encoding(InstId(0), 0x00);
        map.record_encoding(InstId(1), 0x04);
        map.record_encoding(InstId(2), 0x08);

        map.build_transitive();

        // trust_ir0 -> [0x00, 0x04]
        let offsets = map.query_offset(TrustIrInstId(0)).unwrap();
        assert_eq!(offsets, &[0x00, 0x04]);

        // trust_ir1 -> [0x08]
        let offsets = map.query_offset(TrustIrInstId(1)).unwrap();
        assert_eq!(offsets, &[0x08]);

        // Reverse: 0x00 -> [trust_ir0]
        let sources = map.query_source(0x00).unwrap();
        assert_eq!(sources, &[TrustIrInstId(0)]);

        // Reverse: 0x08 -> [trust_ir1]
        let sources = map.query_source(0x08).unwrap();
        assert_eq!(sources, &[TrustIrInstId(1)]);
    }

    #[test]
    fn source_offsets_iterates_transitive_offsets_in_order() {
        let mut map = ProvenanceMap::new();

        map.record_lowering(TrustIrInstId(0), &[InstId(10)], isel_pass());
        map.record_lowering(TrustIrInstId(1), &[InstId(11)], isel_pass());
        map.record_encoding(InstId(10), 0x20);
        map.record_encoding(InstId(11), 0x08);
        map.build_transitive();

        let offsets: Vec<_> = map
            .source_offsets()
            .map(|(offset, trust_ir_ids)| (offset, trust_ir_ids.to_vec()))
            .collect();

        assert_eq!(
            offsets,
            vec![
                (0x08, vec![TrustIrInstId(1)]),
                (0x20, vec![TrustIrInstId(0)]),
            ]
        );
    }

    #[test]
    fn build_transitive_excludes_optimized_away() {
        let mut map = ProvenanceMap::new();

        map.record_lowering(TrustIrInstId(0), &[InstId(0), InstId(1)], isel_pass());

        // inst0 is encoded, inst1 is deleted.
        map.record_encoding(InstId(0), 0x00);
        map.record_deletion(InstId(1), dce_pass(), "dead code");

        map.build_transitive();

        // trust_ir0 -> [0x00] (inst1 was optimized away, no offset)
        let offsets = map.query_offset(TrustIrInstId(0)).unwrap();
        assert_eq!(offsets, &[0x00]);
    }

    #[test]
    fn build_transitive_after_replacement() {
        let mut map = ProvenanceMap::new();

        map.record_lowering(TrustIrInstId(0), &[InstId(0)], isel_pass());
        map.record_replacement(InstId(0), InstId(1), peephole_pass());
        map.record_encoding(InstId(1), 0x10);

        map.build_transitive();

        let offsets = map.query_offset(TrustIrInstId(0)).unwrap();
        assert_eq!(offsets, &[0x10]);
    }

    #[test]
    fn build_transitive_no_encoded_returns_none() {
        let mut map = ProvenanceMap::new();
        map.record_lowering(TrustIrInstId(0), &[InstId(0)], isel_pass());
        // No encoding step.
        map.build_transitive();

        assert!(map.query_offset(TrustIrInstId(0)).is_none());
    }

    // -- ProvenanceMap: full pipeline simulation --

    #[test]
    fn full_pipeline_simulation() {
        let mut map = ProvenanceMap::new();

        // ISel: 3 trust_ir instructions -> 5 machine instructions.
        map.record_lowering(TrustIrInstId(0), &[InstId(0), InstId(1)], isel_pass());
        map.record_lowering(TrustIrInstId(1), &[InstId(2)], isel_pass());
        map.record_lowering(TrustIrInstId(2), &[InstId(3), InstId(4)], isel_pass());

        // Optimization: peephole replaces inst1 with inst5.
        map.record_replacement(InstId(1), InstId(5), peephole_pass());

        // Optimization: DCE removes inst3 (dead).
        map.record_deletion(InstId(3), dce_pass(), "result unused");

        // Regalloc creates spill code (compiler-generated).
        map.record_creation(InstId(6), regalloc_pass(), "spill vreg %7");

        // Encoding.
        map.record_encoding(InstId(0), 0x00);
        map.record_encoding(InstId(5), 0x04); // replaced inst1
        map.record_encoding(InstId(2), 0x08);
        map.record_encoding(InstId(4), 0x0C);
        map.record_encoding(InstId(6), 0x10); // spill code

        map.build_transitive();

        // trust_ir0 -> [0x00, 0x04] (inst0 + replaced inst1->inst5)
        let offsets = map.query_offset(TrustIrInstId(0)).unwrap();
        assert_eq!(offsets, &[0x00, 0x04]);

        // trust_ir1 -> [0x08]
        let offsets = map.query_offset(TrustIrInstId(1)).unwrap();
        assert_eq!(offsets, &[0x08]);

        // trust_ir2 -> [0x0C] (inst3 was DCE'd, only inst4 remains)
        let offsets = map.query_offset(TrustIrInstId(2)).unwrap();
        assert_eq!(offsets, &[0x0C]);

        // Spill code at 0x10 has no trust_ir source.
        assert!(map.query_source(0x10).is_none());

        // Stats.
        let stats = map.stats();
        assert_eq!(stats.trust_ir_instructions, 3);
        assert_eq!(stats.active, 4); // inst0, inst5, inst2, inst4
        assert_eq!(stats.optimized_away, 1); // inst3
        assert_eq!(stats.compiler_generated, 1); // inst6
        assert_eq!(stats.encoded, 5);
        assert_eq!(stats.transitive_mappings, 3); // all 3 trust_ir have offsets
    }

    // -- ProvenanceMap: optimized_away and compiler_generated queries --

    #[test]
    fn optimized_away_query() {
        let mut map = ProvenanceMap::new();
        map.record_lowering(TrustIrInstId(0), &[InstId(0)], isel_pass());
        map.record_lowering(TrustIrInstId(1), &[InstId(1)], isel_pass());
        map.record_deletion(InstId(0), dce_pass(), "dead");

        let dead = map.optimized_away();
        assert_eq!(dead.len(), 1);
        assert_eq!(dead[0].0, InstId(0));
    }

    #[test]
    fn compiler_generated_query() {
        let mut map = ProvenanceMap::new();
        map.record_creation(InstId(0), regalloc_pass(), "spill");
        map.record_creation(InstId(1), regalloc_pass(), "reload");

        let generated = map.compiler_generated();
        assert_eq!(generated.len(), 2);
    }

    // -- ProvenanceMap: stats --

    #[test]
    fn empty_map_stats() {
        let map = ProvenanceMap::new();
        let stats = map.stats();
        assert_eq!(stats.trust_ir_instructions, 0);
        assert_eq!(stats.mach_instructions, 0);
        assert_eq!(stats.active, 0);
        assert_eq!(stats.optimized_away, 0);
        assert_eq!(stats.compiler_generated, 0);
        assert_eq!(stats.encoded, 0);
        assert_eq!(stats.transitive_mappings, 0);
    }

    // -- ProvenanceMap: Default trait --

    #[test]
    fn default_is_empty() {
        let map = ProvenanceMap::default();
        assert_eq!(map.num_trust_ir_entries(), 0);
        assert_eq!(map.num_mach_entries(), 0);
        assert_eq!(map.num_encoded(), 0);
    }

    // -- Edge cases --

    #[test]
    fn replacement_of_nonexistent_is_silent() {
        let mut map = ProvenanceMap::new();
        // Replacing a non-existent instruction should not panic.
        map.record_replacement(InstId(99), InstId(100), peephole_pass());
        assert!(map.get_entry(InstId(99)).is_none());
        assert!(map.get_entry(InstId(100)).is_none());
    }

    #[test]
    fn deletion_of_nonexistent_is_silent() {
        let mut map = ProvenanceMap::new();
        // Deleting a non-existent instruction should not panic.
        map.record_deletion(InstId(99), dce_pass(), "not real");
        assert!(map.get_entry(InstId(99)).is_none());
    }

    #[test]
    fn encoding_without_lowering_still_stores_offset() {
        let mut map = ProvenanceMap::new();
        // Encoding an instruction without prior lowering (e.g., compiler-generated).
        map.record_creation(InstId(0), regalloc_pass(), "prologue");
        map.record_encoding(InstId(0), 0x00);

        assert_eq!(map.get_offset(InstId(0)), Some(0x00));
    }

    #[test]
    fn query_nonexistent_returns_none() {
        let map = ProvenanceMap::new();
        assert!(map.query_offset(TrustIrInstId(99)).is_none());
        assert!(map.query_source(0xDEAD).is_none());
        assert!(map.get_entry(InstId(99)).is_none());
        assert!(map.get_offset(InstId(99)).is_none());
        assert!(map.get_mach_insts(TrustIrInstId(99)).is_none());
    }

    #[test]
    fn duplicate_lowering_appends() {
        let mut map = ProvenanceMap::new();
        // Same trust_ir instruction lowered in two calls (unusual but possible).
        map.record_lowering(TrustIrInstId(0), &[InstId(0)], isel_pass());
        map.record_lowering(TrustIrInstId(0), &[InstId(1)], isel_pass());

        let mach_ids = map.get_mach_insts(TrustIrInstId(0)).unwrap();
        assert_eq!(mach_ids.len(), 2);
    }

    #[test]
    fn merge_with_single_source_works() {
        let mut map = ProvenanceMap::new();
        map.record_lowering(TrustIrInstId(0), &[InstId(0)], isel_pass());
        map.record_merge(&[InstId(0)], InstId(1), peephole_pass());

        let entry = map.get_entry(InstId(1)).unwrap();
        assert!(entry.is_active());
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(0)]);
    }

    #[test]
    fn merge_deduplicates_origins() {
        let mut map = ProvenanceMap::new();
        // Two machine instructions from the same trust_ir source.
        map.record_lowering(TrustIrInstId(0), &[InstId(0), InstId(1)], isel_pass());
        map.record_merge(&[InstId(0), InstId(1)], InstId(2), peephole_pass());

        let entry = map.get_entry(InstId(2)).unwrap();
        // Should have only one origin (deduplicated).
        assert_eq!(entry.trust_ir_origins.len(), 1);
        assert_eq!(entry.trust_ir_origins[0], TrustIrInstId(0));
    }

    #[test]
    fn record_in_place_transform_preserves_provenance() {
        let mut map = ProvenanceMap::new();
        map.record_lowering(TrustIrInstId(7), &[InstId(3)], isel_pass());

        map.record_in_place_transform(InstId(3), peephole_pass());

        let entry = map.get_entry(InstId(3)).unwrap();
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(7)]);
        assert!(entry.is_active());
        assert_eq!(entry.transforms.len(), 2);
        assert_eq!(entry.transforms[1].pass, peephole_pass());
        assert_eq!(entry.transforms[1].kind, TransformKind::Survived);
        assert_eq!(map.get_mach_insts(TrustIrInstId(7)), Some(&[InstId(3)][..]));
    }

    #[test]
    fn record_in_place_transform_unknown_inst_is_noop() {
        let mut map = ProvenanceMap::new();
        map.record_in_place_transform(InstId(99), peephole_pass());

        assert_eq!(map.num_mach_entries(), 0);
    }

    // -- ProvenanceMap: variable live ranges --

    #[test]
    fn trust_ir_var_id_namespaces_prevent_collisions() {
        let source = TrustIrVarId::namespaced(TrustIrVarNamespace::Source, 7).unwrap();
        let fixed_stack =
            TrustIrVarId::namespaced(TrustIrVarNamespace::O3FixedStackLocal, 7).unwrap();
        let constant = TrustIrVarId::namespaced(TrustIrVarNamespace::O3ConstantLocal, 7).unwrap();
        let register = TrustIrVarId::namespaced(TrustIrVarNamespace::O3RegisterLocal, 7).unwrap();
        let spill = TrustIrVarId::namespaced(TrustIrVarNamespace::O3SpillLocal, 7).unwrap();

        assert_eq!(source.namespace(), Some(TrustIrVarNamespace::Source));
        assert_eq!(
            fixed_stack.namespace(),
            Some(TrustIrVarNamespace::O3FixedStackLocal)
        );
        assert_eq!(
            constant.namespace(),
            Some(TrustIrVarNamespace::O3ConstantLocal)
        );
        assert_eq!(
            register.namespace(),
            Some(TrustIrVarNamespace::O3RegisterLocal)
        );
        assert_eq!(spill.namespace(), Some(TrustIrVarNamespace::O3SpillLocal));

        let mut ids = vec![source, fixed_stack, constant, register, spill];
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), 5);
        assert_eq!(spill.namespace_index(), 7);

        assert_eq!(
            TrustIrVarId::namespaced(
                TrustIrVarNamespace::O3Synthetic,
                TRUST_IR_VAR_NAMESPACE_STRIDE
            ),
            Err(TrustIrVarIdError::NamespaceIndexOutOfRange {
                namespace: TrustIrVarNamespace::O3Synthetic,
                index: TRUST_IR_VAR_NAMESPACE_STRIDE,
                limit: TRUST_IR_VAR_NAMESPACE_STRIDE,
            })
        );
    }

    #[test]
    fn variable_declarations_preserve_first_seen_order() {
        let mut map = ProvenanceMap::new();
        let var_a = TrustIrVarId(2);
        let var_b = TrustIrVarId(1);

        map.declare_var(
            var_a,
            VarLocation::new(
                var_a,
                InstId(10),
                InstId(20),
                LocationExpr::Reg(PReg::new(0)),
            ),
        )
        .unwrap();
        map.declare_var(
            var_b,
            VarLocation::new(
                var_b,
                InstId(0),
                InstId(5),
                LocationExpr::Const {
                    value: 7,
                    bit_width: 32,
                },
            ),
        )
        .unwrap();
        map.declare_var(
            var_a,
            VarLocation::new(
                var_a,
                InstId(20),
                InstId(30),
                LocationExpr::Reg(PReg::new(1)),
            ),
        )
        .unwrap();

        assert_eq!(map.declared_vars(), &[var_a, var_b]);
        assert_eq!(map.var_live_ranges(var_a).len(), 2);
    }

    #[test]
    fn invalid_variable_ranges_are_rejected() {
        let mut map = ProvenanceMap::new();
        let var = TrustIrVarId(0);

        let invalid_range = map.declare_var(
            var,
            VarLocation::new(var, InstId(4), InstId(4), LocationExpr::Reg(PReg::new(0))),
        );
        assert_eq!(
            invalid_range,
            Err(VarLocationError::InvalidRange {
                var,
                start: InstId(4),
                end: InstId(4),
            })
        );

        let mismatch = map.declare_var(
            var,
            VarLocation::new(
                TrustIrVarId(1),
                InstId(0),
                InstId(1),
                LocationExpr::Reg(PReg::new(0)),
            ),
        );
        assert_eq!(
            mismatch,
            Err(VarLocationError::VarMismatch {
                expected: var,
                actual: TrustIrVarId(1),
            })
        );
        assert!(map.var_live_ranges(var).is_empty());
    }

    #[test]
    fn overlapping_live_ranges_are_rejected() {
        let mut map = ProvenanceMap::new();
        let var = TrustIrVarId(0);

        map.declare_var(
            var,
            VarLocation::new(var, InstId(0), InstId(10), LocationExpr::Reg(PReg::new(0))),
        )
        .unwrap();

        let err = map.declare_var(
            var,
            VarLocation::new(
                var,
                InstId(5),
                InstId(12),
                LocationExpr::Stack(StackSlotId(1)),
            ),
        );
        assert_eq!(
            err,
            Err(VarLocationError::OverlappingLiveRange {
                var,
                previous_start: InstId(0),
                previous_end: InstId(10),
                next_start: InstId(5),
                next_end: InstId(12),
            })
        );
        assert_eq!(map.var_live_ranges(var).len(), 1);
    }

    #[test]
    fn adjacent_live_ranges_are_allowed() {
        let mut map = ProvenanceMap::new();
        let var = TrustIrVarId(0);

        map.declare_var(
            var,
            VarLocation::new(var, InstId(0), InstId(5), LocationExpr::Reg(PReg::new(0))),
        )
        .unwrap();
        map.declare_var(
            var,
            VarLocation::new(
                var,
                InstId(5),
                InstId(10),
                LocationExpr::Stack(StackSlotId(1)),
            ),
        )
        .unwrap();

        let ranges = map.var_live_ranges(var);
        assert_eq!(ranges.len(), 2);
        assert_eq!((ranges[0].start, ranges[0].end), (InstId(0), InstId(5)));
        assert_eq!((ranges[1].start, ranges[1].end), (InstId(5), InstId(10)));
    }

    #[test]
    fn variable_live_ranges_are_sorted_by_start_then_end() {
        let mut map = ProvenanceMap::new();
        let var = TrustIrVarId(0);

        map.declare_var(
            var,
            VarLocation::new(var, InstId(10), InstId(20), LocationExpr::Reg(PReg::new(1))),
        )
        .unwrap();
        map.declare_var(
            var,
            VarLocation::new(var, InstId(2), InstId(8), LocationExpr::Reg(PReg::new(2))),
        )
        .unwrap();
        map.declare_var(
            var,
            VarLocation::new(
                var,
                InstId(2),
                InstId(6),
                LocationExpr::Dead {
                    killed_by: dce_pass(),
                    reason: DeadReason::ConstantFolded(5),
                },
            ),
        )
        .unwrap();

        let starts_and_ends: Vec<_> = map
            .var_live_ranges(var)
            .iter()
            .map(|loc| (loc.start, loc.end))
            .collect();
        assert_eq!(
            starts_and_ends,
            vec![
                (InstId(2), InstId(6)),
                (InstId(2), InstId(8)),
                (InstId(10), InstId(20)),
            ]
        );
    }

    #[test]
    fn rewrite_var_locations_can_split_and_replace_ranges() {
        let mut map = ProvenanceMap::new();
        let var = TrustIrVarId(0);

        map.declare_var(
            var,
            VarLocation::new(var, InstId(0), InstId(12), LocationExpr::Reg(PReg::new(0))),
        )
        .unwrap();

        map.rewrite_var_locations(peephole_pass(), |loc| {
            vec![
                VarLocation::new(
                    loc.var,
                    loc.start,
                    InstId(4),
                    LocationExpr::Reg(PReg::new(1)),
                ),
                VarLocation::new(
                    loc.var,
                    InstId(4),
                    loc.end,
                    LocationExpr::Stack(StackSlotId(3)),
                ),
            ]
        })
        .unwrap();

        let ranges = map.var_live_ranges(var);
        assert_eq!(ranges.len(), 2);
        assert_eq!(ranges[0].start, InstId(0));
        assert_eq!(ranges[0].end, InstId(4));
        assert_eq!(ranges[0].value, LocationExpr::Reg(PReg::new(1)));
        assert_eq!(ranges[1].start, InstId(4));
        assert_eq!(ranges[1].end, InstId(12));
        assert_eq!(ranges[1].value, LocationExpr::Stack(StackSlotId(3)));
    }

    #[test]
    fn rewrite_var_locations_rejects_invalid_new_var_without_state_leak() {
        let mut map = ProvenanceMap::new();
        let original_var = TrustIrVarId(0);
        let rejected_var = TrustIrVarId(1);
        let original_loc = VarLocation::new(
            original_var,
            InstId(0),
            InstId(12),
            LocationExpr::Reg(PReg::new(0)),
        );

        map.declare_var(original_var, original_loc.clone()).unwrap();

        let err = map.rewrite_var_locations(peephole_pass(), |_loc| {
            vec![VarLocation::new(
                rejected_var,
                InstId(4),
                InstId(4),
                LocationExpr::Reg(PReg::new(1)),
            )]
        });
        assert_eq!(
            err,
            Err(VarLocationError::InvalidRange {
                var: rejected_var,
                start: InstId(4),
                end: InstId(4),
            })
        );

        assert_eq!(map.declared_vars(), &[original_var]);
        assert_eq!(map.var_live_ranges(original_var), &[original_loc]);
        assert!(!map.var_locations.contains_key(&rejected_var));
        assert!(map.var_live_ranges(rejected_var).is_empty());
    }

    #[test]
    fn kill_var_truncates_live_range_and_records_dead_tail() {
        let mut map = ProvenanceMap::new();
        let var = TrustIrVarId(0);

        map.declare_var(
            var,
            VarLocation::new(var, InstId(0), InstId(10), LocationExpr::Reg(PReg::new(0))),
        )
        .unwrap();

        map.kill_var(var, InstId(4), dce_pass(), DeadReason::DeadCodeElimination)
            .unwrap();

        let ranges = map.var_live_ranges(var);
        assert_eq!(ranges.len(), 2);
        assert_eq!(ranges[0].start, InstId(0));
        assert_eq!(ranges[0].end, InstId(4));
        assert_eq!(ranges[0].value, LocationExpr::Reg(PReg::new(0)));
        assert_eq!(ranges[1].start, InstId(4));
        assert_eq!(ranges[1].end, InstId(10));
        assert_eq!(
            ranges[1].value,
            LocationExpr::Dead {
                killed_by: dce_pass(),
                reason: DeadReason::DeadCodeElimination,
            }
        );
    }

    #[test]
    fn var_live_ranges_returns_only_requested_variable() {
        let mut map = ProvenanceMap::new();
        let var_a = TrustIrVarId(0);
        let var_b = TrustIrVarId(1);

        map.declare_var(
            var_a,
            VarLocation::new(
                var_a,
                InstId(0),
                InstId(3),
                LocationExpr::Const {
                    value: 42,
                    bit_width: 64,
                },
            ),
        )
        .unwrap();
        map.declare_var(
            var_b,
            VarLocation::new(
                var_b,
                InstId(3),
                InstId(7),
                LocationExpr::Stack(StackSlotId(1)),
            ),
        )
        .unwrap();

        let ranges_a = map.var_live_ranges(var_a);
        assert_eq!(ranges_a.len(), 1);
        assert_eq!(ranges_a[0].var, var_a);
        assert_eq!(
            ranges_a[0].value,
            LocationExpr::Const {
                value: 42,
                bit_width: 64,
            }
        );

        let ranges_b = map.var_live_ranges(var_b);
        assert_eq!(ranges_b.len(), 1);
        assert_eq!(ranges_b[0].var, var_b);
        assert_eq!(ranges_b[0].value, LocationExpr::Stack(StackSlotId(1)));

        assert!(map.var_live_ranges(TrustIrVarId(99)).is_empty());
    }

    // -----------------------------------------------------------------------
    // LoweringProvenance (TV-1)
    // -----------------------------------------------------------------------

    #[test]
    fn lowering_provenance_default_is_synthetic_unattributed() {
        let p = LoweringProvenance::default();
        assert_eq!(p, LoweringProvenance::UNATTRIBUTED);
        assert_eq!(
            p,
            LoweringProvenance::Synthetic {
                reason: SyntheticReason::Unattributed
            }
        );
        assert!(!p.is_source_attributed());
        assert_eq!(p.source_id(), None);
    }

    #[test]
    fn source_inst_digest_is_deterministic_and_discriminating() {
        let a = SourceInstDigest::compute("Iadd", 2, 1);
        let b = SourceInstDigest::compute("Iadd", 2, 1);
        assert_eq!(a, b, "digest must be deterministic");

        // Different opcode, different operand shape, and embedded width all
        // change the digest.
        assert_ne!(a, SourceInstDigest::compute("Isub", 2, 1));
        assert_ne!(a, SourceInstDigest::compute("Iadd", 1, 1));
        assert_ne!(a, SourceInstDigest::compute("Iadd", 2, 0));
        assert_ne!(
            SourceInstDigest::compute("Iconst { ty: I32, imm: 5 }", 0, 1),
            SourceInstDigest::compute("Iconst { ty: I64, imm: 5 }", 0, 1),
        );
    }

    #[test]
    fn lowering_provenance_source_accessors() {
        let id = SourceInstId { block: 3, index: 7 };
        let p = LoweringProvenance::SourceInst {
            id,
            digest: SourceInstDigest::compute("Iadd", 2, 1),
            trust_ir_inst: Some(TrustIrInstId(11)),
        };
        assert!(p.is_source_attributed());
        assert_eq!(p.source_id(), Some(id));
        assert_eq!(id.to_string(), "lir3.7");
    }

    #[test]
    fn lowering_provenance_coverage_report_counts_and_fraction() {
        let mut cov = LoweringProvenanceCoverage::default();
        assert_eq!(cov.totals(), (0, 0));
        assert_eq!(cov.source_attributed_fraction(), 1.0);

        let src = LoweringProvenance::SourceInst {
            id: SourceInstId { block: 0, index: 0 },
            digest: SourceInstDigest::compute("Iadd", 2, 1),
            trust_ir_inst: None,
        };
        cov.record("AddRR", &src);
        cov.record("AddRR", &src);
        cov.record("MovRR", &LoweringProvenance::UNATTRIBUTED);
        cov.record(
            "MovRR",
            &LoweringProvenance::Synthetic {
                reason: SyntheticReason::FormalArguments,
            },
        );

        assert_eq!(cov.per_opcode["AddRR"].source_attributed, 2);
        assert_eq!(cov.per_opcode["AddRR"].synthetic, 0);
        assert_eq!(cov.per_opcode["MovRR"].source_attributed, 0);
        assert_eq!(cov.per_opcode["MovRR"].synthetic, 2);
        assert_eq!(cov.totals(), (2, 2));
        assert!((cov.source_attributed_fraction() - 0.5).abs() < 1e-12);
    }
}
