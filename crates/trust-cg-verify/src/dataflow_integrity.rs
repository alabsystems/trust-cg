// trust-cg-verify/dataflow_integrity.rs - TV-3 block-level lowering-integrity
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-3: the shared, arch-parametric ISel dataflow translation validator.
//!
//! Where TV-2 ([`crate::provenance_xcheck`]) cross-checks each emitted
//! instruction's *own* provenance stamp, TV-3 checks **block-level lowering
//! integrity** — the cross-instruction WIRING property that the per-opcode
//! certs and the regalloc validator are both blind to, and the exact class of
//! the project's dominant historical miscompiles (store-drop, select-chain,
//! the aarch64 switch/BST block-id collision, the integrator's recurring
//! by-value-stride P0s).
//!
//! The validator walks the **RAW pre-pass ISel output** (before the optimizer
//! passes run — passes do not preserve provenance; see the `LoweringProvenance`
//! schema note in `trust-cg-ir`), keyed by the TV-1 stamps, and enforces three
//! properties per function:
//!
//! 1. **STRUCTURAL — no code after an unconditional terminator.** Within one
//!    machine block, no real (non-pseudo) instruction may follow an
//!    unconditional block terminator (`JMP`/`RET`/`UD2` on x86; `B`/`BR`/`RET`
//!    and traps on aarch64). This single O(n) walk refutes the entire
//!    switch/BST-collision family: a block that got a foreign BST-compare
//!    cascade appended after its terminator — or two code segments fused so one
//!    terminator sits mid-block — fails here (see the a64-switch-bst memory
//!    note, `e49df83`).
//!
//! 2. **PROVENANCE single-source.** All source-attributed
//!    ([`LoweringProvenance::SourceInst`]) stamps within one machine block must
//!    name ONE source (LIR) block. A block holding code fused from two source
//!    blocks fails. `Synthetic`/`Unattributed` instructions (ABI glue, spill
//!    copies, trap blocks, BST intermediate nodes) are exempt — under-
//!    attribution is legal, misattribution never (TV-1 invariant).
//!
//! 3. **ENTRY COHERENCE + OMISSION DIRECTION.** (a) The machine block keyed by
//!    LIR block `B` must START (first source-attributed instruction) with code
//!    stamped from `B` — a block whose real code begins with a different
//!    source block's code fails. (b) Every EFFECTFUL trust-ir/LIR instruction
//!    (store, call, atomic, bulk-memory) must be WITNESSED by >=1 emitted
//!    instruction stamped from it. The omission direction is the store-drop
//!    catch: a dropped store leaves its `(block, index)` unwitnessed and the
//!    function fails closed. This is the exact blind spot (per-instruction
//!    proofs blind to omissions) that let the union-loop store-drop through
//!    historically.
//!
//! # Arch-parametricity
//!
//! The three checks are host-independent (they read block structure and TV-1
//! stamps only, not executed bytes). They run over the small
//! [`DataflowFunctionView`] trait, implemented once for the x86
//! `X86ISelFunction` and once for the aarch64 `MachFunction`. Only end-to-end
//! aarch64 *execution* is unavailable on an x86 host, so:
//!
//! # Rollout (§2.4 gate protocol)
//!
//! `TCG_DATAFLOW_INTEGRITY` env: `off`/`0`, `warn`, `enforce`/`1`; unset uses
//! the per-arch default. x86-64 defaults to ENFORCE (validated 0-hit in
//! warn-only mode over the full differential corpus first). AArch64 defaults to
//! WARN-ONLY — the aarch64 differential corpus cannot execute on the x86
//! validation host, so its enforce flip is deferred to the Apple-Silicon lane
//! (roadmap §3: X2 designs, AS wires/validates). `TCG_TRACE_DATAFLOW=1` prints
//! a per-function summary.

use std::collections::HashSet;
use std::sync::atomic::{AtomicU64, Ordering};

use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};

use crate::provenance_xcheck::{OpClass, classify_lir_opcode};
use trust_cg_lower::instructions::Opcode as LirOpcode;

// ---------------------------------------------------------------------------
// Arch-parametric machine-function view
// ---------------------------------------------------------------------------

/// The Copy facts TV-3's structural + provenance checks need from one emitted
/// machine instruction. Deliberately tiny (zero-alloc on the happy path);
/// opcode text for diagnostics is fetched lazily on a violation via
/// [`DataflowFunctionView::inst_opcode_debug`].
#[derive(Debug, Clone, Copy)]
pub struct InstFacts {
    /// True if this instruction unconditionally ends its block (no
    /// fallthrough): `JMP`/`RET`/`UD2` on x86, `B`/`BR`/`RET`/trap on aarch64.
    /// Conditional branches (which DO fall through) are false.
    pub is_unconditional_terminator: bool,
    /// True if this is a pseudo-instruction (no hardware encoding: `Phi`,
    /// `Nop`, proof-only trap carriers, mask-extract pseudos, `StackAlloc`).
    pub is_pseudo: bool,
    /// The TV-1 lowering provenance carried by this instruction.
    pub provenance: LoweringProvenance,
}

/// A minimal, arch-generic view of a pre-regalloc machine function, letting the
/// TV-3 core run identically over `X86ISelFunction` and aarch64 `MachFunction`.
///
/// Blocks are addressed by dense position `0..block_count()`; `block_id`
/// returns the function-local block identifier used to key TV-1 source
/// coordinates (LIR block id).
pub trait DataflowFunctionView {
    /// Function name (used to guard the LIR-source pairing).
    fn function_name(&self) -> &str;
    /// Number of machine blocks, in layout order.
    fn block_count(&self) -> usize;
    /// Function-local id of the machine block at layout position `block`.
    fn block_id(&self, block: usize) -> u32;
    /// Number of instructions in the machine block at position `block`.
    fn inst_count(&self, block: usize) -> usize;
    /// Copy facts for the instruction at `(block, inst)`.
    fn inst_facts(&self, block: usize, inst: usize) -> InstFacts;
    /// `Debug` opcode rendering for the instruction at `(block, inst)` — called
    /// only to build a diagnostic for a violation (off the happy path).
    fn inst_opcode_debug(&self, block: usize, inst: usize) -> String;
    /// For an exact multi-source idiom fusion, return the source instruction
    /// whose selection represents `source`. Selectors may report this only
    /// after an exact structural idiom match; it covers deliberate fusion of
    /// internal effects even when materialization is deferred to a later
    /// consumer. Architectures/selectors without explicit fusion metadata
    /// return `None`.
    fn source_fusion_target(&self, _source: SourceInstId) -> Option<SourceInstId> {
        None
    }
}

// ---------------------------------------------------------------------------
// Violations
// ---------------------------------------------------------------------------

/// Which block-level integrity property broke.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DataflowViolationKind {
    /// A real (non-pseudo) instruction follows an unconditional block
    /// terminator within the same block (property 1). Catches the
    /// switch/BST-collision family and any two-segment block fusion.
    InstructionAfterTerminator,
    /// Two different source (LIR) blocks are attributed within one machine
    /// block (property 2). Catches code fused from two source blocks.
    MultipleSourceBlocks,
    /// The machine block keyed by LIR block `B` does not START with code
    /// stamped from `B` (property 3a). Catches a mis-started / collided block.
    EntryIncoherent,
    /// An effectful LIR instruction (store/call/atomic/bulk-memory) has NO
    /// emitted instruction stamped from it (property 3b, the omission
    /// direction). Catches the store-drop class.
    UnwitnessedEffect,
}

impl DataflowViolationKind {
    /// Greppable tag for the diagnostic line.
    fn tag(self) -> &'static str {
        match self {
            Self::InstructionAfterTerminator => "code-after-terminator",
            Self::MultipleSourceBlocks => "multiple-source-blocks",
            Self::EntryIncoherent => "entry-incoherent",
            Self::UnwitnessedEffect => "unwitnessed-effect",
        }
    }
}

/// A single block-level lowering-integrity violation. In ENFORCE mode any one
/// of these fails the compile closed for the whole function.
#[derive(Debug, Clone)]
pub struct DataflowViolation {
    /// Which property broke.
    pub kind: DataflowViolationKind,
    /// Human-readable diagnostic (function, block, index, opcodes, sources).
    pub detail: String,
}

// ---------------------------------------------------------------------------
// Effectful-source classification (the must-be-witnessed set)
// ---------------------------------------------------------------------------

/// Does a LIR instruction of this op class have an observable side effect that
/// a correct lowering MUST realize as >=1 emitted instruction?
///
/// Only the unambiguously-must-emit classes: memory stores, atomics
/// (load/store/rmw/cmpxchg/fence — all synchronizing), bulk-memory intrinsics,
/// and calls. Deliberately EXCLUDES:
///
/// * `MemLoad` — a dead load is legitimately DCE-able.
/// * `Guard` — proof-only carriers are legitimately kernel-eliminated (they
///   emit nothing when the bound is proven), so requiring a witness would
///   false-fire on every eliminated guard.
/// * `ControlFlow` — an unconditional `Jump` to the fallthrough block is
///   legitimately elided to fallthrough (no emitted branch).
///
/// The LIR handed to ISel is already post-LIR-optimization, so any instruction
/// of these classes present in it is genuinely live and must emit.
fn is_effectful_source(class: OpClass) -> bool {
    matches!(
        class,
        OpClass::MemStore | OpClass::Atomic | OpClass::MemIntrinsic | OpClass::CallLike
    )
}

/// Is this LIR instruction a memory FENCE that legitimately lowers to ZERO
/// machine instructions on `arch`, so requiring an emitted witness would
/// false-fire (the fence-analogue of a proven-away `Guard`)?
///
/// SLICE 3 (fences). On x86-64's Total Store Order model, an Acquire, Release,
/// AcqRel, or Relaxed fence forbids only reorderings the hardware ALREADY
/// forbids, so `select_fence` emits nothing for them (matching LLVM). That is
/// NOT a dropped side effect: the required COMPILER-ordering barrier is enforced
/// BEFORE ISel — `Inst::Fence` is HAS_SIDE_EFFECTS, so no pre-ISel pass moves a
/// memory op across it — and there is no post-ISel memory-reordering pass. The
/// only fence that needs a hardware barrier on x86 is SeqCst (→ MFENCE), which
/// is NOT exempted here and so still MUST witness an emission.
///
/// This exemption is TARGET-SPECIFIC and deliberately narrow: on any other arch
/// (e.g. AArch64, whose weak model needs a DMB for these orderings) every fence
/// stays in the must-witness set, so a genuinely dropped barrier there still
/// fails closed.
fn fence_is_zero_instruction_on_target(opcode: &LirOpcode, arch: &str) -> bool {
    use trust_cg_lower::instructions::AtomicOrdering as O;
    matches!(
        (arch, opcode),
        (
            "x86_64",
            LirOpcode::Fence {
                ordering: O::Relaxed | O::Acquire | O::Release | O::AcqRel,
            }
        )
    )
}

// ---------------------------------------------------------------------------
// Core check
// ---------------------------------------------------------------------------

/// Run all three block-level integrity checks over one pre-pass machine
/// function against the EXACT LIR function its ISel consumed. Returns every
/// violation found, deterministically ordered.
///
/// Pure and side-effect-free (no telemetry, no verdict change) — the caller
/// ([`evaluate`]) decides how to report/enforce.
pub fn check_function<F: DataflowFunctionView>(
    func: &F,
    lir: &trust_cg_lower::Function,
    arch: &str,
) -> Vec<DataflowViolation> {
    let mut violations = Vec::new();

    // Coordinates of every source instruction any emitted instruction is
    // attributed to (the WITNESSED set for the omission direction).
    let mut witnessed: HashSet<(u32, u32)> = HashSet::new();

    for b in 0..func.block_count() {
        let bid = func.block_id(b);
        let n = func.inst_count(b);

        let mut seen_uncond_terminator = false;
        let mut block_source: Option<u32> = None;
        let mut reported_multi = false;

        for i in 0..n {
            let facts = func.inst_facts(b, i);

            // A pseudo has no executed machine effect, so it cannot witness an
            // effectful source instruction. Counting it would let a dropped
            // Store/Call/Atomic pass merely by leaving a stamped no-op carrier.
            if !facts.is_pseudo
                && let LoweringProvenance::SourceInst { id, .. } = facts.provenance
            {
                witnessed.insert((id.block, id.index));
            }

            // --- Property 1: STRUCTURAL (code after unconditional terminator) ---
            if seen_uncond_terminator && !facts.is_pseudo {
                violations.push(DataflowViolation {
                    kind: DataflowViolationKind::InstructionAfterTerminator,
                    detail: format!(
                        "fn `{}` machine block {bid}: instruction #{i} ({}) follows an \
                         unconditional terminator within the same block (dead/fused code — the \
                         switch-BST block-collision signature)",
                        func.function_name(),
                        func.inst_opcode_debug(b, i),
                    ),
                });
            }
            if facts.is_unconditional_terminator {
                seen_uncond_terminator = true;
            }

            // --- Property 2: PROVENANCE single-source ---
            if let LoweringProvenance::SourceInst { id, .. } = facts.provenance {
                match block_source {
                    None => block_source = Some(id.block),
                    Some(src) if src != id.block && !reported_multi => {
                        reported_multi = true;
                        violations.push(DataflowViolation {
                            kind: DataflowViolationKind::MultipleSourceBlocks,
                            detail: format!(
                                "fn `{}` machine block {bid}: attributes code from two source \
                                 blocks (LIR {src} and LIR {}) — a block holding code fused from \
                                 two source blocks",
                                func.function_name(),
                                id.block,
                            ),
                        });
                    }
                    _ => {}
                }
            }
        }

        // --- Property 3a: ENTRY COHERENCE ---
        // The first source-attributed instruction (skipping synthetic ABI/glue
        // prefix) must be stamped from this block's own LIR id — but only when
        // `bid` names a real LIR block (synthetic machine blocks — BST nodes,
        // trap blocks — carry no source code and are exempt).
        if let Some(src) = block_source
            && src != bid
            && lir.blocks.keys().any(|k| k.0 == bid)
        {
            violations.push(DataflowViolation {
                kind: DataflowViolationKind::EntryIncoherent,
                detail: format!(
                    "fn `{}` machine block {bid} (a real LIR block) starts with code stamped \
                     from a different source block LIR {src} — the block does not begin with its \
                     own lowering",
                    func.function_name(),
                ),
            });
        }
    }

    // --- Property 3b: OMISSION DIRECTION (every effectful LIR inst witnessed) ---
    // Collect the effectful source coordinates deterministically (the LIR block
    // map iteration order is unspecified), then check each is witnessed.
    let mut effectful: Vec<(u32, u32, &'static str)> = Vec::new();
    for (block, bb) in &lir.blocks {
        for (index, inst) in bb.instructions.iter().enumerate() {
            let class = classify_lir_opcode(&inst.opcode);
            if is_effectful_source(class)
                && !fence_is_zero_instruction_on_target(&inst.opcode, arch)
            {
                effectful.push((block.0, index as u32, effect_name(class)));
            }
        }
    }
    effectful.sort_unstable();
    for (block, index, kind) in effectful {
        let source = SourceInstId { block, index };
        let directly_witnessed = witnessed.contains(&(block, index));
        let fusion_witnessed = if directly_witnessed {
            true
        } else {
            // Follow deliberate fusion/deferred-materialization edges until an
            // actually emitted, non-pseudo source stamp is reached. Every node
            // must name a real LIR instruction; a missing edge, invalid target,
            // self-edge, or cycle rejects. Thus an interceptor that returns a
            // consumed span after emitting nothing cannot waive an effect: its
            // anchor remains unwitnessed unless later materialization records a
            // chain to a real machine instruction.
            let mut current = source;
            let mut seen = HashSet::new();
            loop {
                if witnessed.contains(&(current.block, current.index)) {
                    break true;
                }
                if !seen.insert(current) {
                    break false;
                }
                let Some(target) = func.source_fusion_target(current) else {
                    break false;
                };
                let target_exists = lir
                    .blocks
                    .get(&trust_cg_lower::instructions::Block(target.block))
                    .is_some_and(|bb| (target.index as usize) < bb.instructions.len());
                if !target_exists {
                    break false;
                }
                current = target;
            }
        };
        if !directly_witnessed && !fusion_witnessed {
            violations.push(DataflowViolation {
                kind: DataflowViolationKind::UnwitnessedEffect,
                detail: format!(
                    "fn `{}`: effectful LIR instruction {kind} at (block {block}, index {index}) \
                     has NO emitted machine instruction stamped from it — its side effect was \
                     DROPPED (the store-drop class)",
                    lir.name,
                ),
            });
        }
    }

    violations
}

/// Short human name for an effectful op class (for the omission diagnostic).
fn effect_name(class: OpClass) -> &'static str {
    match class {
        OpClass::MemStore => "store",
        OpClass::Atomic => "atomic",
        OpClass::MemIntrinsic => "bulk-memory",
        OpClass::CallLike => "call",
        _ => "effect",
    }
}

// ---------------------------------------------------------------------------
// Mode + telemetry (mirrors crate::provenance_xcheck)
// ---------------------------------------------------------------------------

/// Enforcement mode for the TV-3 dataflow-integrity validator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DataflowIntegrityMode {
    /// Do not run the validator at all.
    Off,
    /// Run it; count + report violations, never fail the compile.
    Warn,
    /// Run it; any violation fails the function's compile closed.
    Enforce,
}

/// Default mode for the x86-64 path: ENFORCE.
///
/// Flipped default-ON per the §2.4 gate rollout protocol after a warn-only
/// telemetry pass over the full differential corpus reported 0 hits (0
/// code-after-terminator, 0 multiple-source-blocks, 0 entry-incoherent, 0
/// unwitnessed-effect). Any NEW violation a future program surfaces fails
/// closed loudly (never a miscompile) and is triaged, never silenced.
pub const X86_DATAFLOW_INTEGRITY_DEFAULT: DataflowIntegrityMode = DataflowIntegrityMode::Enforce;

/// Default mode for the aarch64 path: WARN-ONLY.
///
/// The three checks are host-independent, but the aarch64 differential corpus
/// cannot EXECUTE on the x86 validation host, and the aarch64 stamps only reach
/// TV-3 through the post-pass `MachFunction` today (ISel→adapter→passes), so
/// the §2.4 warn→enforce flip is deferred to the Apple-Silicon lane (roadmap
/// §3: X2 designs, AS wires/validates on a pre-pass MachFunction).
pub const AARCH64_DATAFLOW_INTEGRITY_DEFAULT: DataflowIntegrityMode = DataflowIntegrityMode::Warn;

/// Resolve the active mode: `TCG_DATAFLOW_INTEGRITY` env overrides
/// (`off`/`0`/`false`, `warn`, `enforce`/`on`/`1`/`true`); unset or
/// unrecognized values use the per-arch default.
pub fn dataflow_integrity_mode(arch_default: DataflowIntegrityMode) -> DataflowIntegrityMode {
    match std::env::var("TCG_DATAFLOW_INTEGRITY") {
        Ok(value) => match value.trim().to_ascii_lowercase().as_str() {
            "off" | "0" | "false" => DataflowIntegrityMode::Off,
            "warn" | "warn-only" | "warnonly" => DataflowIntegrityMode::Warn,
            "enforce" | "on" | "1" | "true" => DataflowIntegrityMode::Enforce,
            _ => arch_default,
        },
        Err(_) => arch_default,
    }
}

/// True when `TCG_TRACE_DATAFLOW=1` requests per-function trace output.
pub fn dataflow_trace_enabled() -> bool {
    matches!(
        std::env::var("TCG_TRACE_DATAFLOW").as_deref(),
        Ok("1") | Ok("true") | Ok("on")
    )
}

/// Process-wide count of dataflow-integrity violations observed (warn or
/// enforce) — telemetry for the warn-only rollout phase and for tests.
static VIOLATION_HITS: AtomicU64 = AtomicU64::new(0);

/// Total dataflow-integrity violations observed by this process.
pub fn dataflow_integrity_hit_count() -> u64 {
    VIOLATION_HITS.load(Ordering::Relaxed)
}

/// Record one violation: bump the process-wide counter and print a greppable
/// one-line report (`[TCG-DATAFLOW-INTEGRITY-*]`). Violations are exceptional
/// by design, so the line is always printed.
pub fn record_dataflow_violation(
    arch: &str,
    function_name: &str,
    violation: &DataflowViolation,
    mode: DataflowIntegrityMode,
) {
    VIOLATION_HITS.fetch_add(1, Ordering::Relaxed);
    let tag = match mode {
        DataflowIntegrityMode::Enforce => "[TCG-DATAFLOW-INTEGRITY-FAIL]",
        _ => "[TCG-DATAFLOW-INTEGRITY-WARN]",
    };
    eprintln!(
        "{tag} arch={arch} fn={function_name} kind={}: {}",
        violation.kind.tag(),
        violation.detail
    );
}

/// Print the per-function trace summary when `TCG_TRACE_DATAFLOW=1`.
pub fn trace_function_summary(arch: &str, function_name: &str, violations: usize) {
    if dataflow_trace_enabled() {
        eprintln!("[TCG-TRACE-DATAFLOW] arch={arch} fn={function_name} violations={violations}");
    }
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

/// Validate one pre-pass machine function against the EXACT LIR function its
/// ISel consumed, applying the resolved [`DataflowIntegrityMode`].
///
/// * `Off` → returns `None` immediately.
/// * A `func`/`lir` name mismatch means the caller mis-zipped functions — this
///   is loudly reported and the validation is SKIPPED (never judged against the
///   wrong spec), returning `None`.
/// * All violations are recorded (telemetry) regardless of mode.
/// * In `Enforce` mode the FIRST violation is returned so the caller can fail
///   the compile closed; in `Warn`/`Off` mode `None` is returned (no verdict
///   change).
pub fn evaluate<F: DataflowFunctionView>(
    func: &F,
    lir: &trust_cg_lower::Function,
    arch: &str,
    mode: DataflowIntegrityMode,
) -> Option<DataflowViolation> {
    if mode == DataflowIntegrityMode::Off {
        return None;
    }
    if lir.name != func.function_name() {
        eprintln!(
            "[TCG-DATAFLOW-INTEGRITY-WARN] arch={arch} fn={} replayed LIR function name mismatch \
             (got `{}`): dataflow-integrity validation skipped",
            func.function_name(),
            lir.name
        );
        return None;
    }

    let violations = check_function(func, lir, arch);
    trace_function_summary(arch, func.function_name(), violations.len());
    for v in &violations {
        record_dataflow_violation(arch, func.function_name(), v, mode);
    }

    if mode == DataflowIntegrityMode::Enforce {
        violations.into_iter().next()
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Arch impls
// ---------------------------------------------------------------------------

impl DataflowFunctionView for trust_cg_lower::x86_64_isel::X86ISelFunction {
    fn function_name(&self) -> &str {
        &self.name
    }
    fn block_count(&self) -> usize {
        self.block_order.len()
    }
    fn block_id(&self, block: usize) -> u32 {
        self.block_order[block].0
    }
    fn inst_count(&self, block: usize) -> usize {
        self.blocks
            .get(&self.block_order[block])
            .map_or(0, |bl| bl.insts.len())
    }
    fn inst_facts(&self, block: usize, inst: usize) -> InstFacts {
        use trust_cg_ir::x86_64_ops::X86Opcode;
        let i = &self.blocks[&self.block_order[block]].insts[inst];
        InstFacts {
            // JMP / RET / UD2 unconditionally end a block; Jcc is conditional
            // (falls through) so it is NOT an unconditional terminator.
            is_unconditional_terminator: matches!(
                i.opcode,
                X86Opcode::Jmp | X86Opcode::Ret | X86Opcode::Ud2
            ),
            is_pseudo: i.opcode.is_pseudo(),
            provenance: i.lowering_provenance,
        }
    }
    fn inst_opcode_debug(&self, block: usize, inst: usize) -> String {
        format!(
            "{:?}",
            self.blocks[&self.block_order[block]].insts[inst].opcode
        )
    }
    fn source_fusion_target(&self, source: SourceInstId) -> Option<SourceInstId> {
        trust_cg_lower::x86_64_isel::X86ISelFunction::source_fusion_target(self, source)
    }
}

impl DataflowFunctionView for trust_cg_ir::MachFunction {
    fn function_name(&self) -> &str {
        &self.name
    }
    fn block_count(&self) -> usize {
        self.blocks.len()
    }
    fn block_id(&self, block: usize) -> u32 {
        // A MachBlock has no explicit id; its dense index in `blocks` IS its
        // `BlockId`. (Under-attribution safe: if the ISel→MachFunction adapter
        // renumbered blocks vs the LIR, entry-coherence simply finds no
        // matching LIR block id and skips — the structural/single-source checks
        // stay valid regardless.)
        block as u32
    }
    fn inst_count(&self, block: usize) -> usize {
        self.blocks[block].insts.len()
    }
    fn inst_facts(&self, block: usize, inst: usize) -> InstFacts {
        let inst_id = self.blocks[block].insts[inst];
        let mi = &self.insts[inst_id.0 as usize];
        InstFacts {
            // B / BR / RET and traps unconditionally end a block; a conditional
            // branch (BCond/Cbz/…) falls through, so exclude it.
            is_unconditional_terminator: mi.is_unconditional_branch()
                || mi.is_return()
                || (mi.is_terminator() && !mi.is_conditional_branch()),
            is_pseudo: mi.is_pseudo(),
            provenance: self.inst_lowering_provenance(inst_id),
        }
    }
    fn inst_opcode_debug(&self, block: usize, inst: usize) -> String {
        let inst_id = self.blocks[block].insts[inst];
        format!("{:?}", self.insts[inst_id.0 as usize].opcode)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use trust_cg_ir::provenance::{SourceInstDigest, SourceInstId, SyntheticReason};

    // -- Mock view (exercises the arch-generic core directly) --

    struct MockInst {
        facts: InstFacts,
        opcode: String,
    }
    struct MockBlock {
        id: u32,
        insts: Vec<MockInst>,
    }
    struct MockView {
        name: String,
        blocks: Vec<MockBlock>,
    }

    impl DataflowFunctionView for MockView {
        fn function_name(&self) -> &str {
            &self.name
        }
        fn block_count(&self) -> usize {
            self.blocks.len()
        }
        fn block_id(&self, block: usize) -> u32 {
            self.blocks[block].id
        }
        fn inst_count(&self, block: usize) -> usize {
            self.blocks[block].insts.len()
        }
        fn inst_facts(&self, block: usize, inst: usize) -> InstFacts {
            self.blocks[block].insts[inst].facts
        }
        fn inst_opcode_debug(&self, block: usize, inst: usize) -> String {
            self.blocks[block].insts[inst].opcode.clone()
        }
    }

    struct FusionMockView {
        inner: MockView,
        targets: HashMap<SourceInstId, SourceInstId>,
    }

    impl DataflowFunctionView for FusionMockView {
        fn function_name(&self) -> &str {
            self.inner.function_name()
        }
        fn block_count(&self) -> usize {
            self.inner.block_count()
        }
        fn block_id(&self, block: usize) -> u32 {
            self.inner.block_id(block)
        }
        fn inst_count(&self, block: usize) -> usize {
            self.inner.inst_count(block)
        }
        fn inst_facts(&self, block: usize, inst: usize) -> InstFacts {
            self.inner.inst_facts(block, inst)
        }
        fn inst_opcode_debug(&self, block: usize, inst: usize) -> String {
            self.inner.inst_opcode_debug(block, inst)
        }
        fn source_fusion_target(&self, source: SourceInstId) -> Option<SourceInstId> {
            self.targets.get(&source).copied()
        }
    }

    fn attributed(src_block: u32, src_index: u32, opcode: &str) -> MockInst {
        MockInst {
            facts: InstFacts {
                is_unconditional_terminator: false,
                is_pseudo: false,
                provenance: LoweringProvenance::SourceInst {
                    id: SourceInstId {
                        block: src_block,
                        index: src_index,
                    },
                    digest: SourceInstDigest(0),
                    trust_ir_inst: None,
                },
            },
            opcode: opcode.to_string(),
        }
    }

    fn synthetic(opcode: &str) -> MockInst {
        MockInst {
            facts: InstFacts {
                is_unconditional_terminator: false,
                is_pseudo: false,
                provenance: LoweringProvenance::Synthetic {
                    reason: SyntheticReason::Unattributed,
                },
            },
            opcode: opcode.to_string(),
        }
    }

    fn terminator(opcode: &str, src_block: u32, src_index: u32) -> MockInst {
        let mut m = attributed(src_block, src_index, opcode);
        m.facts.is_unconditional_terminator = true;
        m
    }

    fn kinds(v: &[DataflowViolation]) -> Vec<DataflowViolationKind> {
        v.iter().map(|x| x.kind).collect()
    }

    // -- LIR builders --

    use trust_cg_lower::function::{BasicBlock, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode as LirOpcode, Value};
    use trust_cg_lower::types::Type;

    /// LIR named `f` with block 0 = `[Store(ptr,val), Return]`. The store is
    /// the effectful instruction the omission direction must see witnessed.
    fn lir_with_store() -> trust_cg_lower::Function {
        let mut lir = trust_cg_lower::Function::new(
            "f",
            Signature {
                params: vec![Type::I64, Type::I64],
                returns: vec![],
            },
        );
        let block = Block(0);
        lir.block_order.push(block);
        lir.blocks.insert(
            block,
            BasicBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: LirOpcode::Store {
                            ty: Type::I64,
                            align: None,
                        },
                        args: vec![Value(1), Value(0)],
                        results: vec![],
                    },
                    Instruction {
                        opcode: LirOpcode::Return,
                        args: vec![],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );
        lir
    }

    /// LIR with no effectful instructions (block 0 = `[Iadd, Return]`), named to
    /// match a supplied machine-function name.
    fn lir_pure(name: &str) -> trust_cg_lower::Function {
        let mut lir = trust_cg_lower::Function::new(
            name,
            Signature {
                params: vec![Type::I64, Type::I64],
                returns: vec![Type::I64],
            },
        );
        let block = Block(0);
        lir.block_order.push(block);
        lir.blocks.insert(
            block,
            BasicBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: LirOpcode::Iadd,
                        args: vec![Value(0), Value(1)],
                        results: vec![Value(2)],
                    },
                    Instruction {
                        opcode: LirOpcode::Return,
                        args: vec![Value(2)],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );
        lir
    }

    // ===================================================================
    // Property 1 — STRUCTURAL (code after an unconditional terminator)
    // ===================================================================

    /// PINNED REFUTATION (a): a real instruction after an unconditional
    /// terminator within a block fails closed. This is the switch/BST-collision
    /// signature (a foreign compare/real-block-code appended behind a block's
    /// own terminator).
    #[test]
    fn code_after_unconditional_terminator_is_rejected() {
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![
                    attributed(0, 0, "AddRR"),
                    terminator("Jmp", 0, 1),
                    attributed(0, 2, "MovMR"), // <- dead/fused code behind the JMP
                ],
            }],
        };
        let lir = lir_pure("f");
        let v = check_function(&view, &lir, "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::InstructionAfterTerminator),
            "code after an unconditional terminator must be refuted: {v:?}"
        );
    }

    /// A pseudo (Phi/Nop) after the terminator is NOT flagged (only real code
    /// is dead/fused evidence).
    #[test]
    fn pseudo_after_terminator_is_allowed() {
        let mut nop = synthetic("Nop");
        nop.facts.is_pseudo = true;
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![terminator("Ret", 0, 1), nop],
            }],
        };
        let lir = lir_pure("f");
        let v = check_function(&view, &lir, "x86_64");
        assert!(
            !kinds(&v).contains(&DataflowViolationKind::InstructionAfterTerminator),
            "a trailing pseudo must not be flagged: {v:?}"
        );
    }

    // ===================================================================
    // Property 2 — PROVENANCE single-source
    // ===================================================================

    /// PINNED REFUTATION (b): a machine block whose instructions carry stamps
    /// from TWO different source blocks fails closed (code fused from two
    /// source blocks).
    #[test]
    fn two_source_blocks_in_one_machine_block_is_rejected() {
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![
                    attributed(0, 0, "AddRR"),
                    attributed(1, 0, "SubRR"), // <- from a different source block
                ],
            }],
        };
        let lir = lir_pure("f");
        let v = check_function(&view, &lir, "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::MultipleSourceBlocks),
            "two source blocks in one machine block must be refuted: {v:?}"
        );
    }

    // ===================================================================
    // Property 3a — ENTRY COHERENCE
    // ===================================================================

    /// A machine block keyed by a real LIR block id whose first attributed
    /// instruction comes from a DIFFERENT source block fails closed.
    #[test]
    fn entry_incoherent_block_is_rejected() {
        // machine block id 0 (a real LIR block) whose code is all stamped from
        // source block 5.
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![synthetic("MovRR"), attributed(5, 0, "AddRR")],
            }],
        };
        let lir = lir_pure("f");
        let v = check_function(&view, &lir, "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::EntryIncoherent),
            "a block not starting with its own lowering must be refuted: {v:?}"
        );
    }

    /// A synthetic-only machine block whose id is NOT a real LIR block (a BST
    /// intermediate node / trap block) is exempt from entry coherence.
    #[test]
    fn synthetic_only_block_is_exempt_from_entry_coherence() {
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![
                MockBlock {
                    id: 0,
                    insts: vec![attributed(0, 0, "AddRR"), terminator("Ret", 0, 1)],
                },
                MockBlock {
                    id: 99, // synthetic block id (not in LIR)
                    insts: vec![synthetic("SubsRR"), {
                        let mut b = synthetic("B");
                        b.facts.is_unconditional_terminator = true;
                        b
                    }],
                },
            ],
        };
        let lir = lir_pure("f");
        let v = check_function(&view, &lir, "x86_64");
        assert!(
            v.is_empty(),
            "synthetic BST/trap block must be exempt: {v:?}"
        );
    }

    // ===================================================================
    // Property 3b — OMISSION DIRECTION (store-drop catch)
    // ===================================================================

    /// PINNED REFUTATION (c): an effectful LIR store with NO emitted machine
    /// instruction stamped from it fails closed — the store-drop shape.
    #[test]
    fn dropped_store_is_rejected() {
        // The machine function emits only a Return stamped from (0,1); the LIR
        // Store at (0,0) is never witnessed => dropped.
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![terminator("Ret", 0, 1)],
            }],
        };
        let lir = lir_with_store();
        let v = check_function(&view, &lir, "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::UnwitnessedEffect),
            "a dropped store must be refuted by the omission direction: {v:?}"
        );
    }

    /// The same store, this time WITNESSED by an emitted instruction stamped
    /// from (0,0), passes — no false fail-closed.
    #[test]
    fn witnessed_store_passes() {
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![attributed(0, 0, "MovMR"), terminator("Ret", 0, 1)],
            }],
        };
        let lir = lir_with_store();
        let v = check_function(&view, &lir, "x86_64");
        assert!(v.is_empty(), "a witnessed store must pass: {v:?}");
    }

    /// A stamped pseudo is bookkeeping only, not executed evidence. Leaving a
    /// pseudo carrier behind after dropping the real Store must still reject.
    #[test]
    fn pseudo_stamp_does_not_witness_store() {
        let mut pseudo_store = attributed(0, 0, "StorePseudo");
        pseudo_store.facts.is_pseudo = true;
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![pseudo_store, terminator("Ret", 0, 1)],
            }],
        };
        let v = check_function(&view, &lir_with_store(), "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::UnwitnessedEffect),
            "a pseudo provenance stamp must not hide a dropped store: {v:?}"
        );
    }

    /// Forged fusion metadata cannot waive an effect merely by naming another
    /// LIR instruction: the target chain must reach a real non-pseudo machine
    /// witness.
    #[test]
    fn fusion_to_unwitnessed_source_is_rejected() {
        let view = FusionMockView {
            inner: MockView {
                name: "f".to_string(),
                blocks: vec![MockBlock {
                    id: 0,
                    insts: vec![synthetic("Ret")],
                }],
            },
            targets: HashMap::from([(
                SourceInstId { block: 0, index: 0 },
                SourceInstId { block: 0, index: 1 },
            )]),
        };
        let v = check_function(&view, &lir_with_store(), "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::UnwitnessedEffect),
            "an unwitnessed fusion target must not hide a dropped store: {v:?}"
        );
    }

    #[test]
    fn cyclic_fusion_chain_is_rejected() {
        let source = SourceInstId { block: 0, index: 0 };
        let target = SourceInstId { block: 0, index: 1 };
        let view = FusionMockView {
            inner: MockView {
                name: "f".to_string(),
                blocks: vec![MockBlock {
                    id: 0,
                    insts: vec![synthetic("Ret")],
                }],
            },
            targets: HashMap::from([(source, target), (target, source)]),
        };
        let v = check_function(&view, &lir_with_store(), "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::UnwitnessedEffect),
            "a cyclic fusion chain must fail closed: {v:?}"
        );
    }

    #[test]
    fn fusion_target_outside_lir_is_rejected() {
        let view = FusionMockView {
            inner: MockView {
                name: "f".to_string(),
                blocks: vec![MockBlock {
                    id: 0,
                    insts: vec![synthetic("Ret")],
                }],
            },
            targets: HashMap::from([(
                SourceInstId { block: 0, index: 0 },
                SourceInstId {
                    block: 99,
                    index: 99,
                },
            )]),
        };
        let v = check_function(&view, &lir_with_store(), "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::UnwitnessedEffect),
            "a fusion target outside the LIR must fail closed: {v:?}"
        );
    }

    // ===================================================================
    // Real X86ISelFunction (exercises the x86 trait impl)
    // ===================================================================

    use trust_cg_ir::x86_64_ops::X86Opcode;
    use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst};

    fn x86_stamp(block: u32, index: u32) -> LoweringProvenance {
        LoweringProvenance::SourceInst {
            id: SourceInstId { block, index },
            digest: SourceInstDigest(0),
            trust_ir_inst: None,
        }
    }

    fn x86_inst(opcode: X86Opcode, prov: LoweringProvenance) -> X86ISelInst {
        let mut i = X86ISelInst::new(opcode, vec![]);
        i.lowering_provenance = prov;
        i
    }

    fn x86_func(name: &str, insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            name.to_string(),
            Signature {
                params: vec![Type::I64, Type::I64],
                returns: vec![],
            },
        );
        let block = Block(0);
        func.ensure_block(block);
        func.blocks.get_mut(&block).unwrap().insts.extend(insts);
        func
    }

    /// PINNED POSITIVE (e): a faithful x86 lowering — a synthetic ABI move,
    /// then the store stamped from the LIR store at (0,0), then the return
    /// stamped from (0,1) — passes clean through the REAL x86 trait impl and
    /// the default ENFORCE mode.
    #[test]
    fn x86_faithful_lowering_passes_enforce() {
        let lir = lir_with_store();
        let func = x86_func(
            "f",
            vec![
                x86_inst(
                    X86Opcode::MovRR,
                    LoweringProvenance::Synthetic {
                        reason: SyntheticReason::FormalArguments,
                    },
                ),
                x86_inst(X86Opcode::MovMR, x86_stamp(0, 0)), // store witness
                x86_inst(X86Opcode::Ret, x86_stamp(0, 1)),
            ],
        );
        let out = evaluate(&func, &lir, "x86_64", DataflowIntegrityMode::Enforce);
        assert!(
            out.is_none(),
            "faithful lowering must pass enforce: {out:?}"
        );
    }

    /// PINNED REFUTATION (a) through the REAL x86 trait impl and default mode:
    /// a store dropped behind the return fails the compile closed.
    #[test]
    fn x86_code_after_ret_fails_enforce_default() {
        let lir = lir_with_store();
        // JMP terminator, then a store MOV appended behind it (fused-block
        // shape). Store IS present so the omission direction is satisfied — the
        // structural check is what fires.
        let func = x86_func(
            "f",
            vec![
                x86_inst(X86Opcode::Jmp, x86_stamp(0, 1)),
                x86_inst(X86Opcode::MovMR, x86_stamp(0, 0)),
            ],
        );
        let mode = dataflow_integrity_mode(X86_DATAFLOW_INTEGRITY_DEFAULT);
        assert_eq!(mode, DataflowIntegrityMode::Enforce);
        let out = evaluate(&func, &lir, "x86_64", mode);
        assert!(
            out.is_some(),
            "code after an unconditional terminator must fail the x86 default (ENFORCE)"
        );
    }

    // ===================================================================
    // Real aarch64 MachFunction (exercises the aarch64 trait impl):
    // the reverted A64-4 switch/BST block-id collision shape.
    // ===================================================================

    use trust_cg_ir::BlockId;
    use trust_cg_ir::{
        AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, Signature as MachSignature,
    };

    /// PINNED REFUTATION (d): the A64-4 switch/BST block-id collision shape — a
    /// BST intermediate node's compares + unconditional `B` (synthetic), with a
    /// real block's code (attributed) appended BEHIND them in the same machine
    /// block (the exact pre-fix wiring, `e49df83`). TV-3's structural check
    /// REJECTS it, on the real aarch64 `MachFunction` trait impl.
    #[test]
    fn a64_switch_bst_collision_is_rejected() {
        let mut func = MachFunction::new("f".to_string(), MachSignature::new(vec![], vec![]));
        // BST compare (synthetic selector-invented code).
        func.insts
            .push(MachInst::new(AArch64Opcode::SubsRR, vec![]));
        // BST unconditional branch to a sub-node (synthetic) — the block's
        // legitimate terminator.
        func.insts.push(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(BlockId(1))],
        ));
        // The FUTURE real block's code, mistakenly appended behind the BST B
        // (attributed to its source block 0). This is the collision.
        func.insts.push(MachInst::new(AArch64Opcode::AddRR, vec![]));
        func.blocks[0].insts = vec![InstId(0), InstId(1), InstId(2)];
        func.set_inst_lowering_provenance(
            InstId(2),
            LoweringProvenance::SourceInst {
                id: SourceInstId { block: 0, index: 0 },
                digest: SourceInstDigest(0),
                trust_ir_inst: None,
            },
        );

        let lir = lir_pure("f");
        let v = check_function(&func, &lir, "x86_64");
        assert!(
            kinds(&v).contains(&DataflowViolationKind::InstructionAfterTerminator),
            "the switch-BST block-id collision shape must be refuted: {v:?}"
        );
    }

    /// A faithful aarch64 lowering (one block, add then ret, correctly stamped)
    /// passes the real MachFunction trait impl.
    #[test]
    fn a64_faithful_lowering_passes() {
        let mut func = MachFunction::new("f".to_string(), MachSignature::new(vec![], vec![]));
        func.insts.push(MachInst::new(AArch64Opcode::AddRR, vec![]));
        func.insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.blocks[0].insts = vec![InstId(0), InstId(1)];
        func.set_inst_lowering_provenance(
            InstId(0),
            LoweringProvenance::SourceInst {
                id: SourceInstId { block: 0, index: 0 },
                digest: SourceInstDigest(0),
                trust_ir_inst: None,
            },
        );
        let lir = lir_pure("f");
        let v = check_function(&func, &lir, "x86_64");
        assert!(v.is_empty(), "a faithful aarch64 lowering must pass: {v:?}");
    }

    // ===================================================================
    // Mode / telemetry
    // ===================================================================

    /// Warn mode counts the violation but never returns it (no verdict change);
    /// enforce mode returns it (fail closed). Pins the §2.4 rollout state.
    #[test]
    fn warn_counts_without_failing_enforce_fails() {
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![terminator("Jmp", 0, 1), attributed(0, 0, "MovMR")],
            }],
        };
        let lir = lir_pure("f");

        let before = dataflow_integrity_hit_count();
        let warn = evaluate(&view, &lir, "test", DataflowIntegrityMode::Warn);
        assert!(warn.is_none(), "warn mode must not fail closed");
        assert!(
            dataflow_integrity_hit_count() > before,
            "warn mode must still count the violation"
        );

        let enforced = evaluate(&view, &lir, "test", DataflowIntegrityMode::Enforce);
        assert!(enforced.is_some(), "enforce mode must return the violation");
    }

    /// Off mode never runs the check.
    #[test]
    fn off_mode_is_a_noop() {
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![terminator("Jmp", 0, 1), attributed(0, 0, "MovMR")],
            }],
        };
        let lir = lir_pure("f");
        assert!(evaluate(&view, &lir, "test", DataflowIntegrityMode::Off).is_none());
    }

    /// The rollout-state defaults are pinned: x86 ENFORCE, aarch64 WARN.
    /// Changing either is a gate change and must follow the §2.4 protocol.
    #[test]
    fn mode_defaults_pin_the_rollout_state() {
        assert_eq!(
            X86_DATAFLOW_INTEGRITY_DEFAULT,
            DataflowIntegrityMode::Enforce
        );
        assert_eq!(
            AARCH64_DATAFLOW_INTEGRITY_DEFAULT,
            DataflowIntegrityMode::Warn
        );
    }

    /// A name mismatch skips validation (never judged against the wrong spec).
    #[test]
    fn name_mismatch_skips() {
        let view = MockView {
            name: "actual".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![terminator("Jmp", 0, 1), attributed(0, 0, "MovMR")],
            }],
        };
        let lir = lir_pure("different");
        assert!(evaluate(&view, &lir, "test", DataflowIntegrityMode::Enforce).is_none());
    }
}
