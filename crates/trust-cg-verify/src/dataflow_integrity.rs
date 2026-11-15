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
//!    (store, volatile load, call, atomic, bulk-memory) must be WITNESSED by
//!    at least one emitted instruction stamped from it. The omission direction is the store-drop
//!    catch: a dropped store leaves its `(block, index)` unwitnessed and the
//!    function fails closed. This is the exact blind spot (per-instruction
//!    proofs blind to omissions) that let the union-loop store-drop through
//!    historically. The only exception is a plain `Store` that a selector
//!    folded into an idiom and linked to its witness with a fusion edge
//!    ([`DataflowFunctionView::source_fusion_target`]); the AArch64 view
//!    admits only the bit-reverse fold's edge shape.
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

use std::sync::atomic::{AtomicU64, Ordering};
use trust_cg_ir::fast_hash::FxHashSet as HashSet;

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
    /// consumer. `lir` is the function being checked, so a view can return
    /// only the edges its selector legitimately records (the AArch64 view
    /// admits exactly the bit-reverse fold's store edges). Architectures and
    /// selectors without explicit fusion metadata return `None`.
    fn source_fusion_target(
        &self,
        _source: SourceInstId,
        _lir: &trust_cg_lower::Function,
    ) -> Option<SourceInstId> {
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
    /// An effectful LIR instruction (store/volatile load/call/atomic/
    /// bulk-memory) has NO
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
/// * `MemLoad` — a dead plain load is legitimately DCE-able. A `VolatileLoad`
///   is also `MemLoad`, but it is an observable access, so
///   [`must_witness_effect`] requires it separately.
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

/// The effect kind of a LIR instruction that a correct lowering on `arch` must
/// realize as >=1 emitted instruction stamped from it, or `None` when it may
/// legitimately emit nothing.
///
/// A volatile load is required even though it is classified `MemLoad`: each
/// source volatile read must happen, whether or not its value is used, so a
/// dropped one is the load-side twin of a dropped volatile store.
fn must_witness_effect(opcode: &LirOpcode, arch: &str) -> Option<&'static str> {
    if matches!(opcode, LirOpcode::VolatileLoad { .. }) {
        return Some("volatile-load");
    }
    let class = classify_lir_opcode(opcode);
    (is_effectful_source(class) && !fence_is_zero_instruction_on_target(opcode, arch))
        .then(|| effect_name(class))
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
    let mut witnessed: HashSet<(u32, u32)> = HashSet::default();

    for b in 0..func.block_count() {
        let bid = func.block_id(b);
        let n = func.inst_count(b);

        // Index of the FIRST unconditional terminator seen in this block, kept
        // (rather than a bare bool) so a violation can NAME the terminator it
        // follows: "which instruction ended this block" is the whole diagnosis,
        // and the opcode text is still fetched lazily, only on a violation.
        let mut uncond_terminator_at: Option<usize> = None;
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
            if let Some(term) = uncond_terminator_at
                && !facts.is_pseudo
            {
                violations.push(DataflowViolation {
                    kind: DataflowViolationKind::InstructionAfterTerminator,
                    detail: format!(
                        "fn `{}` machine block {bid}: instruction #{i} ({}) follows an \
                         unconditional terminator (#{term} {}) within the same block \
                         (dead/fused code — the switch-BST block-collision signature)",
                        func.function_name(),
                        func.inst_opcode_debug(b, i),
                        func.inst_opcode_debug(b, term),
                    ),
                });
            }
            if facts.is_unconditional_terminator && uncond_terminator_at.is_none() {
                uncond_terminator_at = Some(i);
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
    //
    // Only a plain `Store` may be represented through fusion edges. Every
    // selector fusion folds stores to stack memory (the x86-64 lane and
    // constant stack sequences, the AArch64 bit-reverse fold). A call, atomic,
    // fence, bulk-memory operation, volatile store or volatile load must be
    // witnessed by an instruction stamped from itself, whatever edges the
    // selector recorded.
    let mut effectful: Vec<(u32, u32, &'static str, bool)> = Vec::new();
    for (block, bb) in &lir.blocks {
        for (index, inst) in bb.instructions.iter().enumerate() {
            if let Some(kind) = must_witness_effect(&inst.opcode, arch) {
                let fusable = matches!(inst.opcode, LirOpcode::Store { .. });
                effectful.push((block.0, index as u32, kind, fusable));
            }
        }
    }
    effectful.sort_unstable();
    for (block, index, kind, fusable) in effectful {
        let source = SourceInstId { block, index };
        let directly_witnessed = witnessed.contains(&(block, index));
        let fusion_witnessed = if directly_witnessed {
            true
        } else if !fusable {
            false
        } else {
            // Follow deliberate fusion/deferred-materialization edges until an
            // actually emitted, non-pseudo source stamp is reached. Every node
            // must name a real LIR instruction; a missing edge, invalid target,
            // self-edge, or cycle rejects. Thus an interceptor that returns a
            // consumed span after emitting nothing cannot waive an effect: its
            // anchor remains unwitnessed unless later materialization records a
            // chain to a real machine instruction.
            let mut current = source;
            let mut seen = HashSet::default();
            loop {
                if witnessed.contains(&(current.block, current.index)) {
                    break true;
                }
                if !seen.insert(current) {
                    break false;
                }
                let Some(target) = func.source_fusion_target(current, lir) else {
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
    match trust_cg_process_env::var("TCG_DATAFLOW_INTEGRITY") {
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
        trust_cg_process_env::var("TCG_TRACE_DATAFLOW").as_deref(),
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
    fn source_fusion_target(
        &self,
        source: SourceInstId,
        _lir: &trust_cg_lower::Function,
    ) -> Option<SourceInstId> {
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
            // B / BR / RET unconditionally end a block; a conditional branch
            // (BCond/Cbz/…) falls through, so exclude it.
            //
            // THE FALLS-THROUGH TRAP/GUARD CARRIERS ARE EXCLUDED BY NAME, and
            // that exclusion is the whole of the aarch64/x86 asymmetry. AArch64 — alone among
            // the three backends — stamps `TrapBoundsCheck*`/`TrapDivZero*`/
            // `TrapShiftRange*`/`TrapOverflow*`/`TrapNull*` `IS_BRANCH |
            // IS_TERMINATOR` and NOT `IS_PSEUDO` (the `Trap*` arms of
            // `AArch64Opcode::default_flags`; x86-64 and RISC-V give the same
            // pseudos `IS_PSEUDO | HAS_SIDE_EFFECTS`, which is why the sibling
            // `X86ISelFunction` impl above needs no exclusion and why its
            // default could be flipped to ENFORCE 0-hit). A guard does NOT end
            // its block: it flows control by TRAPPING and expands LATE to
            // `CMP; B.<cc> +2; BRK`, which FALLS THROUGH — so every
            // instruction after it is LIVE. Reading the raw flags made
            // `is_terminator() && !is_conditional_branch()` — whose only
            // members beyond B/TailCall/Br/Ret are exactly those ten pseudos —
            // report an ordinary guarded table index as the switch-BST
            // block-collision signature. Measured on `library/core` at
            // trust-cg `lane/integration-2026-09-14-b` @ `5e6a978c`: 12 of the
            // 14 `[TCG-REGALLOC-063]` failed roots were that false positive.
            //
            // `is_pseudo` is deliberately NOT widened with it. A guard carrier
            // still WITNESSES its source instruction (property 3b, the
            // omission direction that catches a dropped store) and is still
            // CODE for property 1, so a guard appended behind a real `B`
            // remains a refusal —
            // `a64_trap_guard_pseudo_after_a_real_terminator_is_still_rejected`
            // pins that direction. Nor is the exclusion the whole trap family:
            // the BARE spellings (`TrapBoundsCheck`/`TrapOverflow`/`TrapNull`/
            // `TrapDivZero`/`TrapShiftRange`) encode as an UNCONDITIONAL
            // `BRK #1` and stay terminators — hence
            // `is_falls_through_trap_pseudo`, not `is_trap_pseudo`.
            is_unconditional_terminator: !mi.opcode.is_falls_through_trap_pseudo()
                && (mi.is_unconditional_branch()
                    || mi.is_return()
                    || (mi.is_terminator() && !mi.is_conditional_branch())),
            is_pseudo: mi.is_pseudo(),
            provenance: self.inst_lowering_provenance(inst_id),
        }
    }
    fn inst_opcode_debug(&self, block: usize, inst: usize) -> String {
        let inst_id = self.blocks[block].insts[inst];
        format!("{:?}", self.insts[inst_id.0 as usize].opcode)
    }
    fn source_fusion_target(
        &self,
        source: SourceInstId,
        lir: &trust_cg_lower::Function,
    ) -> Option<SourceInstId> {
        // The AArch64 selector's only fusion folds a private slot's stores
        // into the bit-reverse RBIT stamped at the ladder's root. A recorded
        // edge of any other shape is ignored, so its source stays unwitnessed.
        let target = trust_cg_ir::MachFunction::source_fusion_target(self, source)?;
        aarch64_folded_slot_store_edge_is_admissible(self, lir, source, target).then_some(target)
    }
}

/// Whether the AArch64 fusion edge `source -> target` has the shape of the
/// edges the stack-slot bit-reverse fold records (`select_bitreverse` in
/// `trust-cg-lower`'s `isel.rs`), the only fusion the AArch64 selector makes.
/// Every condition must hold:
///
/// 1. `source` is a plain LIR `Store` of `i32` or `i64` with operands
///    `[value, address]`. A volatile or atomic store, a call, bulk memory, a
///    fence and every other effect are never waived.
/// 2. The address is the result of a `StackAddr` of a slot the function
///    declares, defined earlier in the same block, so the store writes
///    function-local stack memory.
/// 3. `target` is a later instruction of the same block and is a two-operand
///    `Bor` (the ladder's root).
/// 4. The root reads the slot back after the store: its in-block operand
///    closure contains a `Load` of the store's type from a `StackAddr` of the
///    same slot, located between the store and the root.
/// 5. A non-pseudo machine `RBIT` is stamped from `target`, and its
///    destination has the store's width (a W register for `i32`, an X
///    register for `i64`).
///
/// This checks the edge's shape only. It does not show that the slot is
/// private or that the ladder computes a bit reverse; those remain selector
/// obligations (`bitreverse_stack_slots_are_private` and the idiom matcher).
fn aarch64_folded_slot_store_edge_is_admissible(
    machine: &trust_cg_ir::MachFunction,
    lir: &trust_cg_lower::Function,
    source: SourceInstId,
    target: SourceInstId,
) -> bool {
    use std::collections::HashMap;
    use trust_cg_ir::{MachOperand, RegClass};
    use trust_cg_lower::instructions::{Block, Opcode, Value};
    use trust_cg_lower::types::Type;

    if target.block != source.block || target.index <= source.index {
        return false;
    }
    let Some(block) = lir.blocks.get(&Block(source.block)) else {
        return false;
    };
    let instructions = &block.instructions;
    let (store_index, root_index) = (source.index as usize, target.index as usize);
    let (Some(store), Some(root)) = (instructions.get(store_index), instructions.get(root_index))
    else {
        return false;
    };
    let Opcode::Store { ty, .. } = &store.opcode else {
        return false;
    };
    let width = match ty {
        Type::I32 => RegClass::Gpr32,
        Type::I64 => RegClass::Gpr64,
        _ => return false,
    };
    if store.args.len() != 2
        || !store.results.is_empty()
        || root.opcode != Opcode::Bor
        || root.args.len() != 2
        || root.results.len() != 1
    {
        return false;
    }

    // In-block definitions before the root. A value defined more than once
    // (malformed SSA) has no definition here, so nothing reached through it
    // counts.
    let mut def_site: HashMap<Value, Option<usize>> = HashMap::new();
    for (index, inst) in instructions[..root_index].iter().enumerate() {
        for result in &inst.results {
            def_site
                .entry(*result)
                .and_modify(|site| *site = None)
                .or_insert(Some(index));
        }
    }
    let slot_addressed_by = |address: Value, user: usize| -> Option<u32> {
        let index = (*def_site.get(&address)?).filter(|index| *index < user)?;
        let inst = &instructions[index];
        match inst.opcode {
            Opcode::StackAddr { slot }
                if inst.args.is_empty()
                    && inst.results.len() == 1
                    && (slot as usize) < lir.stack_slots.len() =>
            {
                Some(slot)
            }
            _ => None,
        }
    };
    let Some(slot) = slot_addressed_by(store.args[1], store_index) else {
        return false;
    };

    let mut pending = root.args.clone();
    let mut visited = HashSet::default();
    let mut reads_slot_after_store = false;
    while let Some(value) = pending.pop() {
        let Some(Some(index)) = def_site.get(&value).copied() else {
            continue;
        };
        if !visited.insert(index) {
            continue;
        }
        let inst = &instructions[index];
        if index > store_index
            && matches!(&inst.opcode, Opcode::Load { ty: load_ty, .. } if load_ty == ty)
            && inst.args.len() == 1
            && slot_addressed_by(inst.args[0], index) == Some(slot)
        {
            reads_slot_after_store = true;
            break;
        }
        pending.extend(inst.args.iter().copied());
    }
    if !reads_slot_after_store {
        return false;
    }

    machine
        .blocks
        .iter()
        .flat_map(|block| block.insts.iter())
        .any(|id| {
            let inst = machine.inst(*id);
            inst.opcode == trust_cg_ir::AArch64Opcode::Rbit
                && !inst.is_pseudo()
                && machine.inst_lowering_provenance(*id).source_id() == Some(target)
                && match inst.operands.first() {
                    Some(MachOperand::VReg(vreg)) => vreg.class == width,
                    Some(MachOperand::PReg(preg)) => trust_cg_ir::regs::preg_class(*preg) == width,
                    _ => false,
                }
        })
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
        fn source_fusion_target(
            &self,
            source: SourceInstId,
            _lir: &trust_cg_lower::Function,
        ) -> Option<SourceInstId> {
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

    #[test]
    fn aarch64_conditional_guard_fallthrough_is_not_an_unconditional_exit() {
        use trust_cg_ir::{AArch64Opcode as M, MachFunction, MachInst};
        for opcode in [
            M::TrapBoundsCheckExact,
            M::TrapNullIfZero,
            M::TrapDivZeroIfZero,
            M::TrapShiftRangeIfOOB,
            M::TrapOverflowExact,
        ] {
            // This tests structural facts only, not operand admission. Actual
            // guard lowering and native trap/fallthrough controls live in the
            // codegen integration suite. Empty operands cannot reach encoding.
            let mut function = MachFunction::new(
                "guard_structure".into(),
                trust_cg_ir::function::Signature::new(vec![], vec![]),
            );
            for op in [opcode, M::AddRR, M::Ret] {
                let id = function.push_inst(MachInst::new(op, vec![]));
                function.append_inst(function.entry, id);
            }
            assert!(
                !function.inst_facts(0, 0).is_unconditional_terminator,
                "{opcode:?}"
            );
            assert!(
                crate::post_regalloc_recheck::check_structure(&function).is_empty(),
                "{opcode:?}"
            );
        }
    }

    #[test]
    fn aarch64_unconditional_and_unknown_exits_still_reject_following_code() {
        use trust_cg_ir::{AArch64Opcode as M, InstFlags, MachFunction, MachInst};
        // Preserve the existing opcode/flag terminators. BRK intentionally
        // lacks that flag: late exact guards use an intra-block conditional
        // skip over BRK. This structural view does not establish general
        // trap-path reachability; the native integration checks the real guard.
        for opcode in [
            M::B,
            M::Br,
            M::Ret,
            M::TrapOverflow,
            M::TrapBoundsCheck,
            M::TrapNull,
            M::TrapDivZero,
            M::TrapShiftRange,
            M::AddRR,
        ] {
            let mut function = MachFunction::new(
                "unconditional_structure".into(),
                trust_cg_ir::function::Signature::new(vec![], vec![]),
            );
            let mut exit = MachInst::new(opcode, vec![]);
            if opcode == M::AddRR {
                // An unknown producer's terminator flag is not silently erased.
                exit.flags = exit.flags.union(InstFlags::IS_TERMINATOR);
            }
            for instruction in [exit, MachInst::new(M::AddRR, vec![])] {
                let id = function.push_inst(instruction);
                function.append_inst(function.entry, id);
            }
            assert!(
                function.inst_facts(0, 0).is_unconditional_terminator,
                "{opcode:?}"
            );
            assert_eq!(
                crate::post_regalloc_recheck::check_structure(&function).len(),
                1,
                "{opcode:?}"
            );
        }
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

    // -- AArch64 fusion edges: only the bit-reverse fold's slot stores --

    use trust_cg_ir::{RegClass, VReg};
    use trust_cg_lower::function::StackSlotInfo;
    use trust_cg_lower::instructions::{AtomicOrdering, AtomicRmwOp, DirectCallBinding};

    fn lir_inst(opcode: LirOpcode, args: &[u32], results: &[u32]) -> Instruction {
        Instruction {
            opcode,
            args: args.iter().copied().map(Value).collect(),
            results: results.iter().copied().map(Value).collect(),
        }
    }

    fn lir_store(ty: Type, args: &[u32]) -> Instruction {
        lir_inst(LirOpcode::Store { ty, align: None }, args, &[])
    }

    fn lir_load(ty: Type, address: u32, result: u32) -> Instruction {
        lir_inst(LirOpcode::Load { ty, align: None }, &[address], &[result])
    }

    fn lir_slot_addr(slot: u32, result: u32) -> Instruction {
        lir_inst(LirOpcode::StackAddr { slot }, &[], &[result])
    }

    /// LIR `f` with one declared 8-byte slot (slot 0). `Value(0)` is an
    /// integer argument and `Value(1)` a pointer argument. Block 0 holds
    /// `block0` and, when given, block 1 holds `block1`.
    fn lir_fn(
        block0: Vec<Instruction>,
        block1: Option<Vec<Instruction>>,
    ) -> trust_cg_lower::Function {
        let mut lir = trust_cg_lower::Function::new(
            "f",
            Signature {
                params: vec![Type::I64, Type::I64],
                returns: vec![Type::I64],
            },
        );
        lir.stack_slots = vec![StackSlotInfo::new(8, 8)];
        for (block, instructions) in [(Block(0), Some(block0)), (Block(1), block1)] {
            let Some(instructions) = instructions else {
                continue;
            };
            lir.block_order.push(block);
            lir.blocks.insert(
                block,
                BasicBlock {
                    params: vec![],
                    instructions,
                    source_locs: vec![],
                },
            );
        }
        lir
    }

    /// The selector's folded ladder reduced to what TV-3 checks: `effect` at
    /// index 1 (normally a store of `Value(0)` to slot 0) is read back by a
    /// `Load` of `ty` that feeds the `Bor` root at index 4.
    ///
    /// `0: v10 = StackAddr 0; 1: effect; 2: v11 = StackAddr 0;
    /// 3: v12 = Load v11; 4: v13 = Bor v12, v12; 5: Return v13`
    fn folded_ladder(ty: Type, effect: Instruction) -> trust_cg_lower::Function {
        lir_fn(
            vec![
                lir_slot_addr(0, 10),
                effect,
                lir_slot_addr(0, 11),
                lir_load(ty, 11, 12),
                lir_inst(LirOpcode::Bor, &[12, 12], &[13]),
                lir_inst(LirOpcode::Return, &[13], &[]),
            ],
            None,
        )
    }

    /// The store the fold drops: `Value(0)` to slot 0's first address.
    fn slot_store(ty: Type) -> Instruction {
        lir_store(ty, &[0, 10])
    }

    fn mach(opcode: AArch64Opcode) -> MachInst {
        MachInst::new(opcode, vec![])
    }

    /// `RBIT` whose destination and source are virtual registers of `class`
    /// (the W form for `Gpr32`, the X form for `Gpr64`).
    fn rbit(class: RegClass) -> MachInst {
        MachInst::new(
            AArch64Opcode::Rbit,
            vec![
                MachOperand::VReg(VReg::new(1, class)),
                MachOperand::VReg(VReg::new(0, class)),
            ],
        )
    }

    /// AArch64 machine function `f` whose block `b` holds `blocks[b]`, each
    /// instruction stamped from LIR `(b, index)`.
    fn stamped_aarch64(blocks: Vec<Vec<(MachInst, u32)>>) -> MachFunction {
        let mut function = MachFunction::new("f".into(), MachSignature::new(vec![], vec![]));
        for (block, insts) in blocks.into_iter().enumerate() {
            let block_id = if block == 0 {
                function.entry
            } else {
                function.create_block()
            };
            for (inst, index) in insts {
                let id = function.push_inst(inst);
                function.set_inst_lowering_provenance(
                    id,
                    LoweringProvenance::SourceInst {
                        id: SourceInstId {
                            block: block as u32,
                            index,
                        },
                        digest: SourceInstDigest(0),
                        trust_ir_inst: None,
                    },
                );
                function.append_inst(block_id, id);
            }
        }
        function
    }

    /// The selection of [`folded_ladder`]: the root's RBIT, with destination
    /// class `class`, and the return.
    fn folded_selection(class: RegClass) -> MachFunction {
        stamped_aarch64(vec![vec![(rbit(class), 4), (mach(AArch64Opcode::Ret), 5)]])
    }

    fn src(block: u32, index: u32) -> SourceInstId {
        SourceInstId { block, index }
    }

    /// A fusion edge: the folded `(block, index)` and the one it links to.
    type FusionEdge = ((u32, u32), (u32, u32));

    fn with_edges(mut function: MachFunction, edges: &[FusionEdge]) -> MachFunction {
        for ((from_block, from_index), (to_block, to_index)) in edges {
            function
                .source_fusion_targets
                .insert(src(*from_block, *from_index), src(*to_block, *to_index));
        }
        function
    }

    /// `(block, index)` of every effect TV-3 reports as dropped on AArch64.
    /// Any other violation kind fails the test.
    fn dropped(function: &MachFunction, lir: &trust_cg_lower::Function) -> Vec<(u32, u32)> {
        check_function(function, lir, "aarch64")
            .iter()
            .map(|violation| {
                assert_eq!(
                    violation.kind,
                    DataflowViolationKind::UnwitnessedEffect,
                    "{}",
                    violation.detail
                );
                let (_, at) = violation.detail.split_once("at (block ").unwrap();
                let (block, rest) = at.split_once(", index ").unwrap();
                let (index, _) = rest.split_once(')').unwrap();
                (block.parse().unwrap(), index.parse().unwrap())
            })
            .collect()
    }

    fn view_target(
        function: &MachFunction,
        source: SourceInstId,
        lir: &trust_cg_lower::Function,
    ) -> Option<SourceInstId> {
        DataflowFunctionView::source_fusion_target(function, source, lir)
    }

    /// The fold's edge: an `i32` or `i64` store to a declared slot, read back
    /// by the root, linked to the root's RBIT of the same width. TV-3 accepts
    /// the dropped store through that edge and only through it.
    #[test]
    fn aarch64_fusion_edge_waives_the_folded_slot_store() {
        for (ty, class) in [(Type::I32, RegClass::Gpr32), (Type::I64, RegClass::Gpr64)] {
            let lir = folded_ladder(ty.clone(), slot_store(ty.clone()));
            let function = folded_selection(class);
            assert_eq!(dropped(&function, &lir), [(0, 1)], "{ty:?}: no edge");
            let function = with_edges(function, &[((0, 1), (0, 4))]);
            assert_eq!(
                view_target(&function, src(0, 1), &lir),
                Some(src(0, 4)),
                "{ty:?}"
            );
            assert_eq!(dropped(&function, &lir), [], "{ty:?}: the fold's edge");
        }
    }

    /// The independent verifier's probe: a store through the pointer argument
    /// and a call, both edged to a plain add that has a machine witness. A
    /// shape-only view followed both edges and reported nothing. A non-slot
    /// store edged to a genuine fold's RBIT is refused too, while the fold's
    /// own store beside it is still waived.
    #[test]
    fn aarch64_fusion_edges_do_not_waive_a_call_or_a_non_slot_store() {
        let lir = lir_fn(
            vec![
                lir_store(Type::I64, &[0, 1]),
                lir_inst(
                    LirOpcode::Call {
                        name: "side_effect".into(),
                        binding: DirectCallBinding::Interposable,
                    },
                    &[],
                    &[],
                ),
                lir_inst(LirOpcode::Iadd, &[0, 0], &[2]),
                lir_inst(LirOpcode::Return, &[2], &[]),
            ],
            None,
        );
        let function = stamped_aarch64(vec![vec![
            (mach(AArch64Opcode::AddRR), 2),
            (mach(AArch64Opcode::Ret), 3),
        ]]);
        assert_eq!(dropped(&function, &lir), [(0, 0), (0, 1)], "no edges");
        let function = with_edges(function, &[((0, 0), (0, 2)), ((0, 1), (0, 2))]);
        assert_eq!(
            dropped(&function, &lir),
            [(0, 0), (0, 1)],
            "edges to the add"
        );

        let lir = lir_fn(
            vec![
                lir_slot_addr(0, 10),
                slot_store(Type::I64),
                lir_store(Type::I64, &[0, 1]),
                lir_slot_addr(0, 11),
                lir_load(Type::I64, 11, 12),
                lir_inst(LirOpcode::Bor, &[12, 12], &[13]),
                lir_inst(LirOpcode::Return, &[13], &[]),
            ],
            None,
        );
        let function = stamped_aarch64(vec![vec![
            (rbit(RegClass::Gpr64), 5),
            (mach(AArch64Opcode::Ret), 6),
        ]]);
        let function = with_edges(function, &[((0, 1), (0, 5)), ((0, 2), (0, 5))]);
        assert_eq!(dropped(&function, &lir), [(0, 2)], "non-slot store to RBIT");
    }

    /// The target must be the fold's root, stamped on a machine RBIT of the
    /// store's width, reading the slot back after the store, later in the same
    /// block. Every other target waives nothing.
    #[test]
    fn aarch64_fusion_edge_to_anything_but_the_rbit_root_is_refused() {
        let edge = [((0, 1), (0, 4))];
        let ladder32 = folded_ladder(Type::I32, slot_store(Type::I32));
        let ladder64 = folded_ladder(Type::I64, slot_store(Type::I64));
        let ret = || (mach(AArch64Opcode::Ret), 5);

        let orr = stamped_aarch64(vec![vec![(mach(AArch64Opcode::OrrRR), 4), ret()]]);
        assert_eq!(
            dropped(&with_edges(orr, &edge), &ladder32),
            [(0, 1)],
            "root witnessed by ORR, not RBIT"
        );
        let bare = stamped_aarch64(vec![vec![(mach(AArch64Opcode::Rbit), 4), ret()]]);
        assert_eq!(
            dropped(&with_edges(bare, &edge), &ladder32),
            [(0, 1)],
            "RBIT without a destination has no width"
        );
        assert_eq!(
            dropped(
                &with_edges(folded_selection(RegClass::Gpr64), &edge),
                &ladder32
            ),
            [(0, 1)],
            "X-form RBIT for an i32 store"
        );
        assert_eq!(
            dropped(
                &with_edges(folded_selection(RegClass::Gpr32), &edge),
                &ladder64
            ),
            [(0, 1)],
            "W-form RBIT for an i64 store"
        );
        let at_load = stamped_aarch64(vec![vec![
            (rbit(RegClass::Gpr32), 3),
            (rbit(RegClass::Gpr32), 4),
            ret(),
        ]]);
        assert_eq!(
            dropped(&with_edges(at_load, &[((0, 1), (0, 3))]), &ladder32),
            [(0, 1)],
            "edge to the read-back load, not the root"
        );

        // Roots that do not read the stored slot back after the store.
        let root_ignores_slot = lir_fn(
            vec![
                lir_slot_addr(0, 10),
                slot_store(Type::I32),
                lir_slot_addr(0, 11),
                lir_load(Type::I32, 11, 12),
                lir_inst(LirOpcode::Bor, &[0, 0], &[13]),
                lir_inst(LirOpcode::Return, &[13], &[]),
            ],
            None,
        );
        let mut two_slots = lir_fn(
            vec![
                lir_slot_addr(0, 10),
                slot_store(Type::I32),
                lir_slot_addr(1, 11),
                lir_load(Type::I32, 11, 12),
                lir_inst(LirOpcode::Bor, &[12, 12], &[13]),
                lir_inst(LirOpcode::Return, &[13], &[]),
            ],
            None,
        );
        two_slots.stack_slots.push(StackSlotInfo::new(8, 8));
        let other_width = folded_ladder(Type::I64, slot_store(Type::I32));
        for (lir, what) in [
            (&root_ignores_slot, "root does not consume the load"),
            (&two_slots, "root reads another slot"),
            (&other_width, "read back at another width"),
        ] {
            let function = with_edges(folded_selection(RegClass::Gpr32), &edge);
            assert_eq!(dropped(&function, lir), [(0, 1)], "{what}");
        }
        let read_before_store = lir_fn(
            vec![
                lir_slot_addr(0, 11),
                lir_load(Type::I32, 11, 12),
                lir_slot_addr(0, 10),
                slot_store(Type::I32),
                lir_inst(LirOpcode::Bor, &[12, 12], &[13]),
                lir_inst(LirOpcode::Return, &[13], &[]),
            ],
            None,
        );
        let function = with_edges(folded_selection(RegClass::Gpr32), &[((0, 3), (0, 4))]);
        assert_eq!(
            dropped(&function, &read_before_store),
            [(0, 3)],
            "the root reads the slot only before the store"
        );

        // A store to a slot the function does not declare.
        let mut undeclared = folded_ladder(Type::I32, slot_store(Type::I32));
        undeclared.stack_slots.clear();
        let function = with_edges(folded_selection(RegClass::Gpr32), &edge);
        assert_eq!(dropped(&function, &undeclared), [(0, 1)], "undeclared slot");

        // A backward edge, to a root before the store.
        let backward = lir_fn(
            vec![
                lir_slot_addr(0, 10),
                lir_slot_addr(0, 11),
                lir_load(Type::I32, 11, 12),
                lir_inst(LirOpcode::Bor, &[12, 12], &[13]),
                slot_store(Type::I32),
                lir_inst(LirOpcode::Return, &[13], &[]),
            ],
            None,
        );
        let function = stamped_aarch64(vec![vec![
            (rbit(RegClass::Gpr32), 3),
            (mach(AArch64Opcode::Ret), 5),
        ]]);
        let function = with_edges(function, &[((0, 4), (0, 3))]);
        assert_eq!(dropped(&function, &backward), [(0, 4)], "backward edge");

        // A cross-block edge, to a witnessed root of another block.
        let cross = lir_fn(
            vec![
                lir_slot_addr(0, 10),
                slot_store(Type::I32),
                lir_inst(LirOpcode::Return, &[], &[]),
            ],
            Some(vec![
                lir_slot_addr(0, 11),
                lir_load(Type::I32, 11, 12),
                lir_inst(LirOpcode::Bor, &[12, 12], &[13]),
                lir_inst(LirOpcode::Return, &[13], &[]),
            ]),
        );
        let function = stamped_aarch64(vec![
            vec![(mach(AArch64Opcode::Ret), 2)],
            vec![(rbit(RegClass::Gpr32), 2), (mach(AArch64Opcode::Ret), 3)],
        ]);
        let function = with_edges(function, &[((0, 1), (1, 2))]);
        assert_eq!(dropped(&function, &cross), [(0, 1)], "cross-block edge");
    }

    /// Only a plain store is waived. With any other effect class in the
    /// fold's store position, edged to the genuine RBIT root, the effect
    /// stays unwitnessed. An edge from a plain load is not followed either.
    #[test]
    fn aarch64_fusion_edge_from_a_load_atomic_call_or_bulk_memory_is_refused() {
        let order = AtomicOrdering::SeqCst;
        let effects = [
            lir_inst(
                LirOpcode::VolatileStore {
                    ty: Type::I32,
                    align: None,
                },
                &[0, 10],
                &[],
            ),
            lir_inst(
                LirOpcode::AtomicStore {
                    ty: Type::I32,
                    ordering: order,
                },
                &[0, 10],
                &[],
            ),
            lir_inst(
                LirOpcode::AtomicLoad {
                    ty: Type::I32,
                    ordering: order,
                },
                &[10],
                &[20],
            ),
            lir_inst(
                LirOpcode::AtomicRmw {
                    op: AtomicRmwOp::Add,
                    ty: Type::I32,
                    ordering: order,
                },
                &[0, 10],
                &[20],
            ),
            lir_inst(
                LirOpcode::CmpXchg {
                    ty: Type::I32,
                    success: order,
                    failure: order,
                },
                &[0, 0, 10],
                &[20],
            ),
            lir_inst(LirOpcode::Fence { ordering: order }, &[], &[]),
            lir_inst(LirOpcode::Memset, &[10, 0, 0], &[]),
            lir_inst(LirOpcode::Memcpy, &[10, 1, 0], &[]),
            lir_inst(
                LirOpcode::Call {
                    name: "side_effect".into(),
                    binding: DirectCallBinding::Interposable,
                },
                &[10],
                &[],
            ),
        ];
        for effect in effects {
            let what = format!("{:?}", effect.opcode);
            let lir = folded_ladder(Type::I32, effect);
            let function = with_edges(folded_selection(RegClass::Gpr32), &[((0, 1), (0, 4))]);
            assert_eq!(view_target(&function, src(0, 1), &lir), None, "{what}");
            assert_eq!(dropped(&function, &lir), [(0, 1)], "{what}");
        }

        let lir = folded_ladder(Type::I32, slot_store(Type::I32));
        let function = with_edges(
            folded_selection(RegClass::Gpr32),
            &[((0, 1), (0, 4)), ((0, 3), (0, 4))],
        );
        assert_eq!(view_target(&function, src(0, 3), &lir), None, "load edge");
        assert_eq!(dropped(&function, &lir), [], "the store's edge still holds");
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

    /// The core follows fusion edges only from a plain store, whatever the
    /// view returns. The same edge to a witnessed instruction waives a dropped
    /// store and waives nothing for any other effect in its place.
    #[test]
    fn fusion_edges_waive_only_a_plain_store_on_every_arch() {
        let view = FusionMockView {
            inner: MockView {
                name: "f".to_string(),
                blocks: vec![MockBlock {
                    id: 0,
                    insts: vec![terminator("Ret", 0, 1)],
                }],
            },
            targets: HashMap::from([(src(0, 0), src(0, 1))]),
        };
        for arch in ["x86_64", "aarch64"] {
            let v = check_function(&view, &lir_with_store(), arch);
            assert!(v.is_empty(), "{arch}: a store's edge is followed: {v:?}");
        }

        let order = AtomicOrdering::SeqCst;
        for opcode in [
            LirOpcode::VolatileStore {
                ty: Type::I64,
                align: None,
            },
            LirOpcode::AtomicStore {
                ty: Type::I64,
                ordering: order,
            },
            LirOpcode::AtomicRmw {
                op: AtomicRmwOp::Add,
                ty: Type::I64,
                ordering: order,
            },
            LirOpcode::Fence { ordering: order },
            LirOpcode::Memset,
            LirOpcode::Call {
                name: "side_effect".into(),
                binding: DirectCallBinding::Interposable,
            },
        ] {
            let mut lir = lir_with_store();
            lir.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode = opcode.clone();
            for arch in ["x86_64", "aarch64"] {
                let v = check_function(&view, &lir, arch);
                assert_eq!(
                    kinds(&v),
                    [DataflowViolationKind::UnwitnessedEffect],
                    "{arch} {opcode:?}: {v:?}"
                );
            }
        }
    }

    /// LIR `f`: `load` (reading through the pointer argument `Value(1)`,
    /// result unused) at (0, 0), then `Return`.
    fn lir_unused_load(load: LirOpcode) -> trust_cg_lower::Function {
        lir_fn(
            vec![
                lir_inst(load, &[1], &[2]),
                lir_inst(LirOpcode::Return, &[], &[]),
            ],
            None,
        )
    }

    /// A volatile load is an observable access. On every arch TV-3 requires a
    /// non-pseudo instruction stamped from it, even when its value is unused,
    /// and no fusion edge waives it. A plain load that emits nothing is still
    /// accepted.
    #[test]
    fn volatile_load_must_be_witnessed_and_a_plain_load_need_not_be() {
        let volatile = lir_unused_load(LirOpcode::VolatileLoad {
            ty: Type::I64,
            align: None,
        });
        let plain = lir_unused_load(LirOpcode::Load {
            ty: Type::I64,
            align: None,
        });
        let view = |insts: Vec<MockInst>, edge: bool| FusionMockView {
            inner: MockView {
                name: "f".to_string(),
                blocks: vec![MockBlock { id: 0, insts }],
            },
            targets: if edge {
                HashMap::from([(src(0, 0), src(0, 1))])
            } else {
                HashMap::new()
            },
        };
        for arch in ["x86_64", "aarch64"] {
            let ret_only = view(vec![terminator("Ret", 0, 1)], false);
            let v = check_function(&ret_only, &volatile, arch);
            assert_eq!(
                kinds(&v),
                [DataflowViolationKind::UnwitnessedEffect],
                "{arch}: a dropped volatile load: {v:?}"
            );
            assert!(
                v[0].detail.contains("volatile-load at (block 0, index 0)"),
                "{arch}: {}",
                v[0].detail
            );

            let emitted = view(
                vec![attributed(0, 0, "VolatileLoad"), terminator("Ret", 0, 1)],
                false,
            );
            let v = check_function(&emitted, &volatile, arch);
            assert!(v.is_empty(), "{arch}: an emitted volatile load: {v:?}");

            let mut carrier = attributed(0, 0, "VolatileLoadPseudo");
            carrier.facts.is_pseudo = true;
            let pseudo = view(vec![carrier, terminator("Ret", 0, 1)], false);
            let v = check_function(&pseudo, &volatile, arch);
            assert_eq!(
                kinds(&v),
                [DataflowViolationKind::UnwitnessedEffect],
                "{arch}: a pseudo stamp is not a volatile read: {v:?}"
            );

            let edged = view(vec![terminator("Ret", 0, 1)], true);
            let v = check_function(&edged, &volatile, arch);
            assert_eq!(
                kinds(&v),
                [DataflowViolationKind::UnwitnessedEffect],
                "{arch}: a fusion edge does not waive a volatile load: {v:?}"
            );

            let v = check_function(&ret_only, &plain, arch);
            assert!(v.is_empty(), "{arch}: an unused plain load: {v:?}");
        }
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

    /// The real x86-64 fusion chain that the store-only rule keeps: a v2i64
    /// NotEqual compare materializes the block's all-ones mask, and the
    /// all-ones constant stack sequence after it reuses that mask and emits
    /// nothing. Its two lane stores are linked to the sequence anchor and the
    /// anchor to the compare, and TV-3 accepts them. With the same selection
    /// and edges, a volatile store or a call in a lane store's position waives
    /// nothing.
    #[test]
    fn x86_const_stack_lane_stores_chain_through_fusion_edges_and_only_stores_do() {
        use trust_cg_lower::instructions::IntCC;
        use trust_cg_lower::x86_64_isel::{X86ISelOperand, X86InstructionSelector};

        let mut instructions = vec![
            lir_inst(
                LirOpcode::V2I64Icmp {
                    cond: IntCC::NotEqual,
                },
                &[200, 201],
                &[2],
            ),
            lir_slot_addr(0, 10),
        ];
        for lane in 0..2u32 {
            let base = 20 + lane * 3;
            instructions.extend([
                lir_inst(
                    LirOpcode::Iconst {
                        ty: Type::I64,
                        imm: i64::from(lane),
                    },
                    &[],
                    &[base],
                ),
                lir_inst(
                    LirOpcode::ArrayGep { elem_ty: Type::I64 },
                    &[10, base],
                    &[base + 1],
                ),
                lir_inst(
                    LirOpcode::Iconst {
                        ty: Type::I64,
                        imm: -1,
                    },
                    &[],
                    &[base + 2],
                ),
                lir_store(Type::I64, &[base + 2, base + 1]),
            ]);
        }
        instructions.push(lir_load(Type::V128, 10, 1));
        let lane_stores = [5usize, 9];
        for index in lane_stores {
            assert!(matches!(
                instructions[index].opcode,
                LirOpcode::Store { .. }
            ));
        }

        let signature = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut isel = X86InstructionSelector::new("f".into(), signature.clone());
        isel.ensure_block(Block(0));
        isel.set_stack_slots(vec![StackSlotInfo::new(16, 16)]);
        for value in [200, 201] {
            let vreg = isel.new_vreg(RegClass::Fpr128);
            isel.define_value(Value(value), X86ISelOperand::VReg(vreg), Type::V128);
        }
        isel.select_block(Block(0), &instructions).unwrap();
        let func = isel.finalize();
        for index in lane_stores {
            assert_eq!(
                func.source_fusion_target(src(0, index as u32)),
                Some(src(0, 1))
            );
        }
        assert_eq!(func.source_fusion_target(src(0, 1)), Some(src(0, 0)));

        let mut lir = trust_cg_lower::Function::new("f", signature);
        lir.stack_slots = vec![StackSlotInfo::new(16, 16)];
        lir.block_order.push(Block(0));
        lir.blocks.insert(
            Block(0),
            BasicBlock {
                params: vec![],
                instructions,
                source_locs: vec![],
            },
        );
        let v = check_function(&func, &lir, "x86_64");
        assert!(v.is_empty(), "the lane stores' chain is followed: {v:?}");

        for opcode in [
            LirOpcode::VolatileStore {
                ty: Type::I64,
                align: None,
            },
            LirOpcode::Call {
                name: "side_effect".into(),
                binding: DirectCallBinding::Interposable,
            },
        ] {
            let mut altered = lir.clone();
            altered.blocks.get_mut(&Block(0)).unwrap().instructions[lane_stores[0]].opcode =
                opcode.clone();
            let v = check_function(&func, &altered, "x86_64");
            assert_eq!(
                kinds(&v),
                [DataflowViolationKind::UnwitnessedEffect],
                "{opcode:?}: {v:?}"
            );
        }
    }

    /// Unused volatile loads of each x86-64 register file, selected by the
    /// real selector, are witnessed by their stamped volatile MOVs and pass.
    /// Removing any one load's machine instructions fails the function on
    /// exactly that load.
    #[test]
    fn x86_selected_unused_volatile_loads_are_witnessed_and_refused_when_dropped() {
        use trust_cg_lower::x86_64_isel::{X86ISelOperand, X86InstructionSelector};

        let mut instructions: Vec<Instruction> = [Type::I32, Type::F64, Type::V128]
            .into_iter()
            .zip(2u32..)
            .map(|(ty, result)| {
                lir_inst(LirOpcode::VolatileLoad { ty, align: None }, &[1], &[result])
            })
            .collect();
        instructions.push(lir_inst(LirOpcode::Return, &[], &[]));
        let mut lir = lir_fn(instructions.clone(), None);
        lir.signature.returns.clear();

        let mut isel = X86InstructionSelector::new("f".into(), lir.signature.clone());
        isel.ensure_block(Block(0));
        let pointer = isel.new_vreg(RegClass::Gpr64);
        isel.define_value(Value(1), X86ISelOperand::VReg(pointer), Type::I64);
        isel.select_block(Block(0), &instructions).unwrap();
        let func = isel.finalize();

        let v = check_function(&func, &lir, "x86_64");
        assert!(v.is_empty(), "selected volatile loads: {v:?}");
        for index in 0..3u32 {
            let mut dropped = func.clone();
            let block = dropped.blocks.get_mut(&Block(0)).unwrap();
            let before = block.insts.len();
            block
                .insts
                .retain(|inst| inst.lowering_provenance.source_id() != Some(src(0, index)));
            assert_eq!(block.insts.len() + 1, before, "one MOV per load");
            let v = check_function(&dropped, &lir, "x86_64");
            assert_eq!(
                kinds(&v),
                [DataflowViolationKind::UnwitnessedEffect],
                "{index}: {v:?}"
            );
            assert!(
                v[0].detail
                    .contains(&format!("volatile-load at (block 0, index {index})")),
                "{}",
                v[0].detail
            );
        }
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

    /// PINNED REFUTATION of the pre-fix behaviour: an aarch64 TRAP/GUARD PSEUDO
    /// is NOT an unconditional terminator, and the ordinary code that follows it
    /// in the same block is NOT dead.
    ///
    /// WHY THIS EXISTS. aarch64 — alone among the three backends — stamps the
    /// guard carriers `IS_BRANCH | IS_TERMINATOR` (see the `Trap*` arms of
    /// `AArch64Opcode::default_flags`, and `is_trap_pseudo`'s doc for why the
    /// divergence is resolved on the CONSUMER side). They are also absent from
    /// the `IS_PSEUDO` flag. This view read those instance flags, so
    /// `is_terminator() && !is_conditional_branch()` classified every guard as an
    /// unconditional terminator and every real instruction after it as
    /// "dead/fused code — the switch-BST block-collision signature". A guard
    /// expands LATE to `CMP; B.<cc> +2; BRK`, which FALLS THROUGH: nothing after
    /// it is dead. Measured on `library/core` at trust-cg
    /// `lane/integration-2026-09-14-b`: 12 of the 14 `[TCG-REGALLOC-063]` failed
    /// roots were this false positive — `str::validations::utf8_char_width`,
    /// `unicode_data::white_space::lookup`, `dec2flt::Lemire::pow10_fast_path`
    /// and friends, every one of them an ordinary guarded table index.
    ///
    /// The x86 view (`X86ISelFunction`) names its terminators explicitly
    /// (`Jmp | Ret | Ud2`) and asks the OPCODE for `is_pseudo`, which is why the
    /// x86 default could be flipped to ENFORCE 0-hit and aarch64's could not.
    #[test]
    fn a64_trap_guard_pseudo_does_not_end_its_block() {
        for guard in [
            AArch64Opcode::TrapBoundsCheckExact,
            AArch64Opcode::TrapDivZeroIfZero,
            AArch64Opcode::TrapShiftRangeIfOOB,
            AArch64Opcode::TrapOverflowExact,
            AArch64Opcode::TrapNullIfZero,
        ] {
            let mut func = MachFunction::new("f".to_string(), MachSignature::new(vec![], vec![]));
            // guard; load; ret — the `utf8_char_width` shape, one block.
            func.insts.push(MachInst::new(guard, vec![]));
            func.insts
                .push(MachInst::new(AArch64Opcode::LdrbRI, vec![]));
            func.insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
            func.blocks[0].insts = vec![InstId(0), InstId(1), InstId(2)];
            func.set_inst_lowering_provenance(
                InstId(1),
                LoweringProvenance::SourceInst {
                    id: SourceInstId { block: 0, index: 0 },
                    digest: SourceInstDigest(0),
                    trust_ir_inst: None,
                },
            );
            let lir = lir_pure("f");
            let v = check_function(&func, &lir, "x86_64");
            assert!(
                !kinds(&v).contains(&DataflowViolationKind::InstructionAfterTerminator),
                "{guard:?} traps by falling through; the code after it is live: {v:?}"
            );
        }
    }

    /// THE OTHER CONTROL: the BARE trap spellings really DO end their block, and
    /// must keep doing so. `TrapBoundsCheck`/`TrapOverflow`/`TrapNull`/
    /// `TrapDivZero`/`TrapShiftRange` are the degraded carriers the `expand_*`
    /// passes fall back to when an operand is missing, and the encoder emits
    /// each as an UNCONDITIONAL `BRK #1`. Excluding the whole `is_trap_pseudo`
    /// family — rather than only `is_falls_through_trap_pseudo` — would have
    /// silently excused real dead code behind an unconditional trap.
    #[test]
    fn a64_bare_trap_spellings_still_end_their_block() {
        for bare in [
            AArch64Opcode::TrapBoundsCheck,
            AArch64Opcode::TrapOverflow,
            AArch64Opcode::TrapNull,
            AArch64Opcode::TrapDivZero,
            AArch64Opcode::TrapShiftRange,
        ] {
            let mut func = MachFunction::new("f".to_string(), MachSignature::new(vec![], vec![]));
            func.insts.push(MachInst::new(bare, vec![]));
            func.insts.push(MachInst::new(AArch64Opcode::AddRR, vec![]));
            func.blocks[0].insts = vec![InstId(0), InstId(1)];
            func.set_inst_lowering_provenance(
                InstId(1),
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
                "{bare:?} encodes as an unconditional BRK; code after it is dead: {v:?}"
            );
        }
    }

    /// THE CONTROL for the test above, in the direction that must NOT be lost: a
    /// guard pseudo that follows a REAL unconditional terminator is still dead
    /// code and is still refuted. Excluding the guards from the TERMINATOR
    /// classification must not also excuse them from being CODE — they are not
    /// `IS_PSEUDO`, they carry a machine effect (the `BRK` they expand to), and a
    /// guard appended behind a `B` is exactly the fused-block signature.
    #[test]
    fn a64_trap_guard_pseudo_after_a_real_terminator_is_still_rejected() {
        let mut func = MachFunction::new("f".to_string(), MachSignature::new(vec![], vec![]));
        func.insts.push(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(BlockId(1))],
        ));
        func.insts
            .push(MachInst::new(AArch64Opcode::TrapBoundsCheckExact, vec![]));
        func.blocks[0].insts = vec![InstId(0), InstId(1)];
        func.set_inst_lowering_provenance(
            InstId(1),
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
            "a guard carrier behind a real `B` is still dead/fused code: {v:?}"
        );
    }

    /// The violation must NAME the terminator it follows. A refusal that says
    /// only "follows an unconditional terminator" leaves the reader to find
    /// which of the block's instructions ended it — and when the answer was a
    /// guard carrier rather than a branch, that single word was the whole
    /// diagnosis and it was missing for the twelve `library/core` roots above.
    #[test]
    fn instruction_after_terminator_names_the_terminator() {
        let view = MockView {
            name: "f".to_string(),
            blocks: vec![MockBlock {
                id: 0,
                insts: vec![
                    attributed(0, 0, "MovRR"),
                    terminator("Jmp", 0, 1),
                    attributed(0, 0, "MovMR"),
                ],
            }],
        };
        let lir = lir_pure("f");
        let v = check_function(&view, &lir, "test");
        let detail = v
            .iter()
            .find(|x| x.kind == DataflowViolationKind::InstructionAfterTerminator)
            .map(|x| x.detail.clone())
            .expect("the structural violation must fire");
        assert!(
            detail.contains("#2 (MovMR)") && detail.contains("(#1 Jmp)"),
            "the detail must name BOTH the offending instruction and the \
             terminator it follows: {detail}"
        );
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
