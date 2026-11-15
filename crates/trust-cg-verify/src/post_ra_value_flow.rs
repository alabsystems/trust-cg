// trust-cg-verify/post_ra_value_flow.rs - AArch64 post-RA value-flow validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Value-flow translation validation of everything the AArch64 pipeline does
//! after register allocation (`[TCG-A64-POST-RA-VALUE-FLOW]`, ledger L10-P1).
//!
//! # What this checks
//!
//! The AArch64 pipeline runs, after `allocate`: post-RA spill optimization,
//! the allocation rewrite, physical-copy coalescing, the IR rebuild, spill
//! materialization with scratch choice, free-constant rematerialization,
//! copy-roundtrip elimination, the call-argument clobber fixup, spill-reload
//! CSE, late post-index formation, branch forwarding, copy lowering and
//! dead-definition binding; then frame lowering (frame-index elimination,
//! prologue/epilogue, shrink-wrapping), guard and LL/SC expansion, branch
//! layout, branch relaxation, loop-head alignment and branch resolution.
//! The x86-64 pipeline validates its post-RA window with TV-5
//! ([`crate::post_ra_dataflow`], [`crate::post_ra_captured_spec`]); this
//! module is the AArch64 counterpart, built as one comparison applied at two
//! stage boundaries:
//!
//! | Stage | Specification | Implementation |
//! |-------|---------------|----------------|
//! | [`Stage::Allocation`] | the function entering register allocation (virtual registers, symbolic stack slots) | the function after copy lowering and dead-definition binding (physical registers, spill slots) |
//! | [`Stage::FrameLayout`] | the allocation stage's implementation | the final stream after branch resolution (SP/FP-relative frame, resolved branch offsets) |
//!
//! For every program point both functions share (a block laid out in both,
//! an "anchor"), the implementation must perform the same effects in the
//! same order on the same values, decide every branch the same way, and
//! return or tail-call with the same values in the ABI registers. A value
//! the specification keeps in a virtual register may live anywhere in the
//! implementation (a register, a spill slot, rematerialized, coalesced); the
//! comparison infers where (see the engine) rather than trusting the
//! allocation map, so a reload from the wrong slot, a coalesce that merged
//! interfering values, a rematerialization of a value that changed, a
//! caller-saved register held across a call, a frame offset off by eight or
//! a relaxed branch retargeted to the wrong block each change a value or a
//! control decision at some effect, and are refused.
//!
//! # Model
//!
//! Values are hash-consed terms ([`term`]). Register moves, constant moves,
//! zero extensions, add/subtract of an immediate, and 64-bit register
//! add/subtract and shift-left by a constant (including `ADD Xd, Xn, Xm, LSL
//! #k`) are interpreted, the 64-bit integer arithmetic as wrapping affine
//! forms (`c + Σ k·t`, so reassociated or strength-reduced spellings of one
//! sum are one term), with the bits of a narrow mask or a logical right
//! shift known zero; every other pure operation is uninterpreted (an
//! operation of its inputs and non-register operands). Loads, stores (a pair
//! as one effect per element), calls, atomics, barriers and trap carriers
//! are effects, matched one-for-one in order; a plain access is compared at
//! its effective address whatever its spelling (immediate, pre/post-index,
//! register offset with an unscaled or size-scaled `LSL`, or the `[Xn,
//! #:lo12:sym]` form the late ELF lo12 fusion leaves, the address `ADD Xd, Xn,
//! #:lo12:sym` computes); an operand past the address is outside the model.
//! A recorded trap expansion is judged as its carrier
//! ([`trust_cg_ir::function::TrapExpansionRecord`]; the expansion's words
//! are ENC-5's to judge), and an expanded ELF TLSDESC sequence (`ADRP`, `LDR`
//! of the resolver, `ADD` of the descriptor, `BLR`) as the `TlsDescCall` it
//! replaced when x0 and x1 hold exactly the descriptor and its resolver
//! (the resolver slot is constant once the dynamic linker filled it). Allocator storage is tracked
//! as memory cells keyed by exact address: spill slots before frame
//! lowering; after it, spill slots (`SPILL_SLOT_ACCESS`), the callee-save
//! area and every access frame lowering inserted (saves, restores, stack
//! probes). A static stack-probe loop is summarized from its constant
//! counter. Calls follow AAPCS64/DarwinPCS: X0-X7 and V0-V7 are results,
//! X8-X18, X30, V16-V31, the upper halves of V8-V15 and NZCV become unknown
//! (each register its own unknown); a call argument is judged at the width
//! the specification wrote it (a `W2` argument's upper half is not the
//! callee's to read), and SP is an argument of every call (the callee finds
//! its stack-passed arguments at the SP it is entered with; before frame
//! lowering every exit reads SP too). A call in a
//! block with an exception-handling call site also continues at the landing
//! pad, with the unwinder's X0/X1 and the callee-saved registers. On Darwin
//! the implementation must never write X18 (the platform register).
//! After frame lowering the implementation's SP, X19-X29, the return
//! address and the low halves of V8-V15 must hold their entry values at
//! every exit.
//!
//! # Strength and limits
//!
//! This is translation validation of each compiled function under the
//! model above: a validated verdict means the two functions perform equal
//! effects on equal terms. It is not a proof of any pass. Its assumptions:
//!
//! * The def/use, memory-effect and NZCV tables are `trust_cg_opt`'s and the
//!   allocator's own operand roles (a shared description of each opcode).
//! * Allocator and frame storage is private. After frame lowering every
//!   storage access (a spill, a callee-save save or restore, any access frame
//!   lowering inserted) is checked to lie below the CFA, off every program
//!   stack slot the specification names and off the outgoing stack-argument
//!   area at the bottom of the frame (the stack-argument stores are program
//!   effects, and the callee reads and may overwrite the area). A stack
//!   probe (an inserted `STR XZR, [SP]` of the current SP, or a summarized
//!   probe loop) may touch a program slot or the outgoing area only where
//!   it writes wholly below every byte an earlier write on any path from
//!   the entry may have touched: a write at a known CFA offset touches that
//!   offset, and a write the model cannot place (through an unknown
//!   pointer, a call, any other opaque effect) is assumed to reach no lower
//!   than the 128-byte red zone below the SP it runs at (no pointer into the
//!   stack below SP outlives its allocation). A program store invalidates
//!   the storage cells it overlaps; a call drops the cells below its SP, and
//!   that no call writes the caller's spill or save cells is assumed (the
//!   AAPCS64 stack discipline: the callee writes below the SP it is entered
//!   with, its incoming argument area, which holds no storage, and memory
//!   the program passed it). Program memory is not tracked, so value flow
//!   through program memory is compared only as matched loads and stores.
//! * The frame layout's slot offsets are the specification of where each
//!   stack slot lives; the offsets of the slots the specification names and
//!   of every slot register allocation created are checked to lie inside the
//!   slot area and not to overlap, and the specification's program accesses
//!   are addressed through them.
//! * FP operations are treated as pure (FPCR/FPSR are not threaded).
//! * Only the effects and decisions are compared, so code that computes a
//!   dead value differently is not reported.
//!
//! The stack protector frame lowering inserts is modeled: the guard (read
//! through `___stack_chk_guard`) is constant memory, the canary flows
//! through its frame cell, and the epilogue's compare of the reloaded canary
//! with the guard decides its `B.NE` to `__stack_chk_fail` not taken.
//!
//! A construct outside the model (a loop of inserted blocks other than a
//! static probe loop, a stack-limit check, an LL/SC expansion, a dynamic
//! stack allocation, an unmodeled operand shape) yields
//! [`Verdict::Unmodeled`] with its reason; the pipeline records it and
//! refuses it under a refusing policy. Nothing is silently skipped.

mod engine;
mod model;
mod term;
#[cfg(test)]
mod tests;

use trust_cg_ir::fast_hash::FxHashMap as HashMap;

use serde::{Deserialize, Serialize};
use trust_cg_ir::MachFunction;

use model::{AddressModel, Side, SideCtx};

/// The stage boundaries the comparison is applied at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Stage {
    /// Register allocation through copy lowering.
    Allocation,
    /// Frame lowering through branch resolution.
    FrameLayout,
    /// Both at once: the function entering register allocation against the
    /// final resolved stream (what the pipeline runs by default; the split
    /// pair localizes a failure to one window).
    Composed,
}

impl Stage {
    /// Stable spelling, also the name the pipeline records the run under.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Allocation => "post-ra-allocation",
            Self::FrameLayout => "post-ra-frame-layout",
            Self::Composed => "post-ra-value-flow",
        }
    }

    /// Whether the implementation is the final, frame-lowered stream.
    fn after_frame_lowering(self) -> bool {
        matches!(self, Self::FrameLayout | Self::Composed)
    }
}

/// Which property a violation broke.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ViolationKind {
    /// An effect is missing, extra, or a different operation.
    EffectMismatch,
    /// A matched effect (or return) consumes a different value.
    ValueMismatch,
    /// The two functions continue at different places under the same
    /// conditions.
    ControlMismatch,
    /// SP, a callee-saved register or the return address is not restored at
    /// an exit, or the frame layout overlaps.
    FrameMismatch,
    /// The implementation writes the reserved platform register X18.
    ReservedRegister,
    /// The block structure the comparison relies on is broken.
    Structure,
    /// A malformed function (an arena index out of range).
    Malformed,
}

impl ViolationKind {
    /// Greppable tag.
    pub fn tag(self) -> &'static str {
        match self {
            Self::EffectMismatch => "effect-mismatch",
            Self::ValueMismatch => "value-mismatch",
            Self::ControlMismatch => "control-mismatch",
            Self::FrameMismatch => "frame-mismatch",
            Self::ReservedRegister => "reserved-register",
            Self::Structure => "structure",
            Self::Malformed => "malformed",
        }
    }
}

/// The frame facts the [`Stage::FrameLayout`] comparison maps the
/// specification's stack slots with: the layout frame lowering computed.
/// They are checked (every fixed slot inside the frame's slot area, no two
/// overlapping) before they are used.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FrameFacts {
    /// CFA-relative byte offset of each stack slot (by slot id); `None` for
    /// a runtime-sized slot.
    pub slot_cfa_offsets: Vec<Option<i64>>,
    /// Byte size of each stack slot (by slot id).
    pub slot_sizes: Vec<u64>,
    /// Bytes from the CFA down to the post-prologue SP.
    pub total_frame_size: i64,
    /// Bytes of the callee-save area directly below the CFA.
    pub callee_saved_area_size: i64,
    /// Bytes of the outgoing-argument area at the bottom of the frame.
    pub outgoing_arg_area_size: i64,
}

/// One comparison's inputs.
#[derive(Clone, Copy)]
pub struct StageInputs<'a> {
    pub spec: &'a MachFunction,
    pub implementation: &'a MachFunction,
    pub stage: Stage,
    /// Stack slots with this id or above were created by register
    /// allocation (the specification of [`Stage::Allocation`] has exactly
    /// this many slots).
    pub allocator_slot_start: u32,
    /// The frame layout (after frame lowering only).
    pub frame: Option<&'a FrameFacts>,
    /// The implementation's instructions with this id or above were
    /// inserted by frame lowering (after frame lowering only; `None` takes
    /// the specification's arena length, right when the specification is
    /// the function frame lowering started from).
    pub inserted_from: Option<u32>,
    /// X18 is reserved (the Darwin platform register): the implementation
    /// may not write it.
    pub reserved_x18: bool,
}

/// What one comparison concluded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The implementation performs the specification's effects on equal
    /// values and decides every branch the same way, under the model.
    Validated,
    /// A definite violation of the model's equalities.
    Violation { kind: ViolationKind, detail: String },
    /// The function holds a construct outside the model.
    Unmodeled(String),
}

impl Verdict {
    /// Stable lowercase spelling.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Validated => "validated",
            Self::Violation { .. } => "violation",
            Self::Unmodeled(_) => "unmodeled",
        }
    }
}

/// Deterministic work counters of one comparison.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkCounters {
    /// Anchors (blocks laid out in both functions) reached.
    pub anchors: u32,
    /// Anchors no path from the entry reaches.
    pub unreachable_anchors: u32,
    /// Anchor visits of the fixpoint.
    pub visits: u32,
    /// Effects matched (including exits).
    pub effects: u32,
    /// Specification and implementation instructions executed.
    pub spec_insts: u32,
    pub impl_insts: u32,
    /// Interned terms.
    pub terms: u32,
}

/// The result of one comparison.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Report {
    pub stage: Stage,
    pub verdict: Verdict,
    pub work: WorkCounters,
}

impl Report {
    /// One diagnostic line: `[TCG-A64-POST-RA-VALUE-FLOW] fn ... stage ...`.
    pub fn line(&self, function: &str) -> String {
        match &self.verdict {
            Verdict::Validated => {
                format!("{TAG} fn `{function}` {}: validated", self.stage.as_str())
            }
            Verdict::Violation { kind, detail } => format!(
                "{TAG} fn `{function}` {}: {} ({detail})",
                self.stage.as_str(),
                kind.tag()
            ),
            Verdict::Unmodeled(why) => format!(
                "{TAG} fn `{function}` {}: unmodeled ({why})",
                self.stage.as_str()
            ),
        }
    }
}

/// Greppable diagnostic tag.
pub const TAG: &str = "[TCG-A64-POST-RA-VALUE-FLOW]";

/// The stack slots `func`'s laid-out instructions name.
fn referenced_slots(func: &MachFunction) -> std::collections::BTreeSet<usize> {
    let mut out = std::collections::BTreeSet::new();
    for &b in &func.block_order {
        let Some(block) = func.blocks.get(b.0 as usize) else {
            continue;
        };
        for &id in &block.insts {
            let Some(inst) = func.insts.get(id.0 as usize) else {
                continue;
            };
            for op in &inst.operands {
                match op {
                    trust_cg_ir::MachOperand::StackSlot(s) => {
                        out.insert(s.0 as usize);
                    }
                    trust_cg_ir::MachOperand::FrameIndex(i) => {
                        if let Ok(i) = usize::try_from(i.0) {
                            out.insert(i);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// Check the frame facts: every fixed slot the specification names lies
/// inside the slot area `[CFA - total + outgoing, CFA - callee_saved)` and
/// no two of them overlap. (A slot no instruction names gets no storage.)
fn check_frame_facts(
    facts: &FrameFacts,
    referenced: &std::collections::BTreeSet<usize>,
) -> Result<(), String> {
    let lo = -facts.total_frame_size + facts.outgoing_arg_area_size;
    let hi = -facts.callee_saved_area_size;
    let mut ranges: Vec<(i64, i64, usize)> = Vec::new();
    for (slot, offset) in facts.slot_cfa_offsets.iter().enumerate() {
        if !referenced.contains(&slot) {
            continue;
        }
        let Some(offset) = *offset else { continue };
        let size = facts.slot_sizes.get(slot).copied().unwrap_or(0);
        let Ok(size) = i64::try_from(size) else {
            return Err(format!("stack slot {slot} has an unrepresentable size"));
        };
        if size == 0 {
            continue;
        }
        let end = offset.saturating_add(size);
        if offset < lo || end > hi {
            return Err(format!(
                "stack slot {slot} at CFA{offset:+} ({size} bytes) lies outside the slot area [CFA{lo:+}, CFA{hi:+})"
            ));
        }
        ranges.push((offset, end, slot));
    }
    ranges.sort_unstable();
    for pair in ranges.windows(2) {
        let (a, b) = (pair[0], pair[1]);
        if b.0 < a.1 {
            return Err(format!(
                "stack slots {} [CFA{:+}, CFA{:+}) and {} [CFA{:+}, CFA{:+}) overlap",
                a.2, a.0, a.1, b.2, b.0, b.1
            ));
        }
    }
    Ok(())
}

/// The CFA-relative byte ranges `[start, end)` of the program's stack
/// slots (ids below `allocator_slot_start` the specification names, with a
/// fixed offset and a nonzero size).
fn program_slot_ranges(
    facts: &FrameFacts,
    referenced: &std::collections::BTreeSet<usize>,
    allocator_slot_start: u32,
) -> Vec<(i64, i64, u32)> {
    referenced
        .iter()
        .filter(|&&slot| slot < allocator_slot_start as usize)
        .filter_map(|&slot| {
            let start = facts.slot_cfa_offsets.get(slot).copied().flatten()?;
            let size = i64::try_from(facts.slot_sizes.get(slot).copied().unwrap_or(0)).ok()?;
            (size > 0).then(|| (start, start.saturating_add(size), slot as u32))
        })
        .collect()
}

/// Recorded trap expansions of `func`: each instruction id to its record
/// and position.
fn trap_records(func: &MachFunction) -> HashMap<trust_cg_ir::InstId, (usize, usize)> {
    let mut out = HashMap::default();
    for (record, rec) in func.trap_expansions.iter().enumerate() {
        for (position, &id) in rec.insts.iter().enumerate() {
            out.insert(id, (record, position));
        }
    }
    out
}

/// Compare `inputs.implementation` with `inputs.spec` at `inputs.stage`.
pub fn compare(inputs: StageInputs<'_>) -> Report {
    let stage = inputs.stage;
    let mut report = Report {
        stage,
        verdict: Verdict::Validated,
        work: WorkCounters::default(),
    };
    let (spec_address, spec_initial_sp, frame_storage, program_slots, outgoing_area) = match stage {
        Stage::Allocation => (AddressModel::Symbolic, None, None, Vec::new(), (0, 0)),
        Stage::FrameLayout | Stage::Composed => {
            let Some(facts) = inputs.frame else {
                report.verdict =
                    Verdict::Unmodeled("the frame-layout comparison has no frame facts".into());
                return report;
            };
            let referenced = referenced_slots(inputs.spec);
            // Every slot register allocation created gets storage whether
            // or not the specification names it (the composed specification
            // names none), so its offset is checked too.
            let mut checked = referenced.clone();
            checked.extend((inputs.allocator_slot_start as usize)..facts.slot_cfa_offsets.len());
            if let Err(why) = check_frame_facts(facts, &checked) {
                report.verdict = Verdict::Violation {
                    kind: ViolationKind::FrameMismatch,
                    detail: why,
                };
                return report;
            }
            if inputs.implementation.stack_limit.is_some() {
                report.verdict = Verdict::Unmodeled("a stack-limit check".into());
                return report;
            }
            (
                AddressModel::Frame {
                    slot_cfa: facts.slot_cfa_offsets.clone(),
                },
                Some(-facts.total_frame_size),
                Some((-facts.callee_saved_area_size, 0)),
                program_slot_ranges(facts, &referenced, inputs.allocator_slot_start),
                (
                    -facts.total_frame_size,
                    (-facts.total_frame_size).saturating_add(facts.outgoing_arg_area_size.max(0)),
                ),
            )
        }
    };
    if stage.after_frame_lowering()
        && inputs
            .spec
            .insts
            .iter()
            .any(|inst| trust_cg_ir::llsc::LlscPseudo::of(inst.opcode).is_some())
    {
        report.verdict = Verdict::Unmodeled("an LL/SC atomic expansion".into());
        return report;
    }
    // Frame lowering turns a dynamic stack allocation into SP arithmetic
    // (and a probe loop for a large or unknown size); SP is then no longer
    // a constant offset from the CFA, which the frame model relies on.
    if stage.after_frame_lowering()
        && inputs
            .spec
            .insts
            .iter()
            .any(|inst| inst.opcode == trust_cg_ir::AArch64Opcode::StackAlloc)
    {
        report.verdict = Verdict::Unmodeled("a dynamic stack allocation".into());
        return report;
    }

    let spec = SideCtx {
        func: inputs.spec,
        side: Side::Spec,
        address: spec_address,
        allocator_slot_start: inputs.allocator_slot_start,
        frame_storage: None,
        program_slots: Vec::new(),
        outgoing_area: (0, 0),
        reserved_x18: false,
        inserted_from: None,
        trap_records: HashMap::default(),
    };
    let imp = SideCtx {
        func: inputs.implementation,
        side: Side::Impl,
        address: AddressModel::Symbolic,
        allocator_slot_start: inputs.allocator_slot_start,
        frame_storage,
        program_slots,
        outgoing_area,
        reserved_x18: inputs.reserved_x18,
        // After frame lowering the arena is the specification's plus what
        // frame lowering, guard expansion and relaxation appended.
        inserted_from: match stage {
            Stage::Allocation => None,
            Stage::FrameLayout | Stage::Composed => inputs
                .inserted_from
                .or_else(|| u32::try_from(inputs.spec.insts.len()).ok()),
        },
        trap_records: match stage {
            Stage::Allocation => HashMap::default(),
            Stage::FrameLayout | Stage::Composed => trap_records(inputs.implementation),
        },
    };
    let mut comparison = match engine::Comparison::new(spec, imp, stage, spec_initial_sp) {
        Ok(c) => c,
        Err(stop) => {
            report.verdict = verdict_of(stop);
            return report;
        }
    };
    let result = comparison.run();
    let w = comparison.work;
    report.work = WorkCounters {
        anchors: w.anchors,
        unreachable_anchors: w.unreachable_anchors,
        visits: w.visits,
        effects: w.effects,
        spec_insts: w.spec_insts,
        impl_insts: w.impl_insts,
        terms: comparison.arena.len() as u32,
    };
    if let Err(stop) = result {
        report.verdict = verdict_of(stop);
    }
    report
}

fn verdict_of(stop: engine::Stop) -> Verdict {
    match stop {
        engine::Stop::Violation(kind, detail) => Verdict::Violation { kind, detail },
        engine::Stop::Unmodeled(why) => Verdict::Unmodeled(why),
    }
}
