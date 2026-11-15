// trust-cg-codegen/post_ra_value_flow.rs - pipeline wiring of AArch64 post-RA value flow
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pipeline wiring of the AArch64 post-allocation value-flow validation
//! (`trust_cg_verify::post_ra_value_flow`, ledger L10-P1).
//!
//! A [`Session`] captures the function entering register allocation and
//! compares the final resolved stream with it under the frame layout
//! ([`Stage::Composed`], recorded as `post-ra-value-flow`): one comparison
//! covering every post-allocation stage. With
//! `TRUST_CG_POST_RA_VALUE_FLOW_STAGES=split` (diagnostic aid) it instead
//! compares the function after copy lowering with the captured one
//! ([`Stage::Allocation`]), captures it, and compares the final stream with
//! that ([`Stage::FrameLayout`]), which localizes a failure to one window at
//! about twice the cost. Each comparison is recorded in a
//! [`PassValidationSummary`] under the stage's name with
//! [`ValidatorKind::PostAllocationValueFlow`]; the pipeline refuses a
//! non-validated stage under a refusing policy (proof-grade publication and
//! certified pass execution enforce at least
//! [`PassValidationPolicy::Enforce`]) and reports it under the diagnostic
//! policy.
//!
//! The comparison runs in the dedicated and all-passes scopes
//! ([`PassValidationScope::Dedicated`], [`PassValidationScope::AllPasses`]),
//! which every proof-grade publication and certified pass-execution pipeline
//! runs at least and `TRUST_CG_PASS_VALIDATION_SCOPE` can select. It is not
//! cheap enough for the default schedulers tier (measured on the compile
//! corpus, 2026-10-13: +5.4% to +6.1% instructions retired on the AOT
//! lanes, +8% to +9% on the JIT lanes, up to +23% on the ay kernels and
//! 1.34x on one small fixture, against the same dedicated scope without
//! it), so there the
//! post-allocation stages are recorded as an uncovered changed run, as every
//! other pass without a running validator is: never silently skipped, and
//! refused by a `require-coverage` policy. `Pipeline::encode_and_emit`
//! receives an already allocated function, so it has no pre-allocation
//! function to compare with and records nothing. With
//! `TRUST_CG_POST_RA_VALUE_FLOW_DUMP=<dir>` every comparison that does not
//! validate writes both functions and the verdict to a file in `<dir>`
//! (diagnostic aid; it changes no verdict).

use trust_cg_ir::MachFunction;
use trust_cg_opt::{
    PassValidationConfig, PassValidationRecord, PassValidationScope, PassValidationSummary,
    ValidationVerdict, ValidatorKind,
};
use trust_cg_verify::post_ra_value_flow::{
    FrameFacts, Report, Stage, StageInputs, Verdict, ViolationKind, compare,
};

use crate::frame::FrameLayout;

/// Whether the comparisons run under `config`: an active policy in the
/// dedicated or all-passes scope.
pub(crate) fn runs(config: PassValidationConfig) -> bool {
    config.policy.is_active() && config.scope != PassValidationScope::Schedulers
}

/// One function's post-allocation validation in progress.
pub(crate) struct Session {
    pub(crate) config: PassValidationConfig,
    spec: Option<Box<MachFunction>>,
    allocator_slot_start: u32,
    /// Compare at both stage boundaries instead of once.
    split: bool,
    /// Composed mode: the arena length after copy lowering (frame lowering
    /// appends from here).
    inserted_from: Option<u32>,
    /// X18 is the platform register (Mach-O targets).
    reserved_x18: bool,
}

fn split_requested() -> bool {
    snapshots::split_forced()
        || std::env::var_os("TRUST_CG_POST_RA_VALUE_FLOW_STAGES").is_some_and(|v| v == "split")
}

impl Session {
    /// Capture `func`, the function entering register allocation.
    pub(crate) fn begin(
        config: PassValidationConfig,
        func: &MachFunction,
        reserved_x18: bool,
    ) -> Self {
        let active = runs(config);
        Self {
            config,
            spec: active.then(|| Box::new(func.clone())),
            allocator_slot_start: u32::try_from(func.stack_slots.len()).unwrap_or(u32::MAX),
            split: split_requested(),
            inserted_from: None,
            reserved_x18,
        }
    }

    /// Compare `func` with the captured function at `stage`, returning the
    /// recorded verdict (`None` when validation does not run or, composed,
    /// at the allocation boundary). Split, after the allocation stage `func`
    /// is captured for the frame/layout stage.
    pub(crate) fn check(
        &mut self,
        stage: Stage,
        func: &MachFunction,
        layout: Option<&FrameLayout>,
    ) -> Option<PassValidationSummary> {
        if self.spec.is_none() {
            // Not run in this tier: the post-allocation stages are an
            // uncovered changed run (recorded once, at the final stream).
            if self.config.policy.is_active() && stage == Stage::FrameLayout {
                let mut summary = PassValidationSummary::new(self.config);
                summary.record(
                    PassValidationRecord {
                        pass_name: Stage::Composed.as_str().to_string(),
                        function_name: func.name.clone(),
                        validator: None,
                        verdict: ValidationVerdict::Uncovered,
                    },
                    true,
                );
                return Some(summary);
            }
            return None;
        }
        let stage = match (self.split, stage) {
            (false, Stage::Allocation) => {
                // Composed: remember where frame lowering starts appending.
                self.inserted_from = u32::try_from(func.insts.len()).ok();
                return None;
            }
            (false, _) => Stage::Composed,
            (true, stage) => stage,
        };
        let spec = self.spec.take()?;
        let facts = layout.map(|layout| frame_facts(func, layout));
        let report = compare(StageInputs {
            spec: &spec,
            implementation: func,
            stage,
            allocator_slot_start: self.allocator_slot_start,
            frame: facts.as_ref(),
            inserted_from: if stage == Stage::Composed {
                self.inserted_from
            } else {
                None
            },
            reserved_x18: self.reserved_x18,
        });
        if report.verdict != Verdict::Validated {
            dump_failure(&report, &spec, func);
        }
        snapshots::record(
            stage,
            &spec,
            func,
            facts.as_ref(),
            self.allocator_slot_start,
            self.inserted_from,
            &report,
        );
        if stage == Stage::Allocation {
            self.spec = Some(Box::new(func.clone()));
        }
        let mut summary = PassValidationSummary::new(self.config);
        summary.examined_instructions =
            u64::from(report.work.spec_insts) + u64::from(report.work.impl_insts);
        summary.record(
            PassValidationRecord {
                pass_name: stage.as_str().to_string(),
                function_name: func.name.clone(),
                validator: Some(ValidatorKind::PostAllocationValueFlow),
                verdict: verdict_record(&report.verdict),
            },
            true,
        );
        Some(summary)
    }
}

/// The pass-validation verdict of a comparison. A structural violation the
/// comparison decides exactly (a write of the reserved X18, overlapping
/// frame slots, a malformed function) is refuted; a term inequality or an
/// unmodeled construct is unproved (unequal normalized terms mean "not shown
/// equal", the convention of `trust_cg_opt::pass_validation`).
fn verdict_record(verdict: &Verdict) -> ValidationVerdict {
    match verdict {
        Verdict::Validated => ValidationVerdict::Validated,
        Verdict::Violation { kind, detail } => {
            let reason = format!("{}: {detail}", kind.tag());
            match kind {
                ViolationKind::ReservedRegister | ViolationKind::Malformed => {
                    ValidationVerdict::Refuted(reason)
                }
                ViolationKind::FrameMismatch if detail.starts_with("stack slot") => {
                    ValidationVerdict::Refuted(reason)
                }
                _ => ValidationVerdict::Unproved(reason),
            }
        }
        Verdict::Unmodeled(why) => ValidationVerdict::Unproved(format!("unmodeled: {why}")),
    }
}

/// The frame facts of a lowered function: each fixed slot's CFA offset under
/// `layout`. Frame-pointer frames address a slot at `FP + fp_offset` with
/// `FP = CFA - 16`; frames without a frame pointer address it at
/// `SP + fp_offset + sp_adjustment`, i.e. `CFA + fp_offset - callee_saved`.
pub(crate) fn frame_facts(func: &MachFunction, layout: &FrameLayout) -> FrameFacts {
    let callee_saved = i64::from(layout.callee_saved_area_size);
    let base = if layout.uses_frame_pointer {
        -16
    } else {
        -callee_saved
    };
    FrameFacts {
        slot_cfa_offsets: crate::frame::stack_slot_frame_offsets(func, layout)
            .into_iter()
            .map(|offset| offset.map(|o| i64::from(o) + base))
            .collect(),
        slot_sizes: func
            .stack_slots
            .iter()
            .map(|slot| u64::from(slot.size))
            .collect(),
        total_frame_size: i64::from(layout.total_frame_size),
        callee_saved_area_size: callee_saved,
        outgoing_arg_area_size: i64::from(layout.outgoing_arg_area_size),
    }
}

/// `TRUST_CG_POST_RA_VALUE_FLOW_DUMP=<dir>`: write a non-validated
/// comparison's two functions and verdict to `<dir>`.
fn dump_failure(report: &Report, spec: &MachFunction, implementation: &MachFunction) {
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicU32, Ordering};
    static DIR: OnceLock<Option<std::path::PathBuf>> = OnceLock::new();
    static SEQ: AtomicU32 = AtomicU32::new(0);
    let Some(dir) = DIR
        .get_or_init(|| std::env::var_os("TRUST_CG_POST_RA_VALUE_FLOW_DUMP").map(Into::into))
        .as_ref()
    else {
        return;
    };
    let mut out = String::new();
    out.push_str(&report.line(&implementation.name));
    out.push_str("\n\n== specification ==\n");
    out.push_str(&listing(spec));
    out.push_str("\n== implementation ==\n");
    out.push_str(&listing(implementation));
    let seq = SEQ.fetch_add(1, Ordering::Relaxed);
    let name: String = implementation
        .name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .take(80)
        .collect();
    let path = dir.join(format!(
        "{}-{}-{seq}-{name}.txt",
        std::process::id(),
        report.stage.as_str()
    ));
    let _ = std::fs::create_dir_all(dir);
    let _ = std::fs::write(path, out);
}

/// A plain listing of a function (layout order).
#[doc(hidden)]
pub fn listing(func: &MachFunction) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let _ = writeln!(
        out,
        "fn {} entry={} slots={:?}",
        func.name,
        func.entry.0,
        func.stack_slots
            .iter()
            .map(|s| (s.size, s.align))
            .collect::<Vec<_>>()
    );
    for &b in &func.block_order {
        let Some(block) = func.blocks.get(b.0 as usize) else {
            continue;
        };
        let _ = writeln!(out, "bb{} succs={:?}", b.0, block.succs);
        for &id in &block.insts {
            let Some(inst) = func.insts.get(id.0 as usize) else {
                continue;
            };
            let _ = writeln!(
                out,
                "  {:5} {:?} {:?} flags={:#x} iu={:?} id={:?}",
                id.0,
                inst.opcode,
                inst.operands,
                inst.flags.bits(),
                inst.implicit_uses,
                inst.implicit_defs
            );
        }
    }
    out
}

/// Test support: capture every stage comparison a closure's compiles run on
/// this thread, with both functions, so corruption controls can mutate the
/// real implementation and re-run the comparison.
#[doc(hidden)]
pub mod snapshots {
    use std::cell::RefCell;

    use trust_cg_ir::MachFunction;
    use trust_cg_verify::post_ra_value_flow::{FrameFacts, Report, Stage};

    /// One recorded comparison.
    #[derive(Debug, Clone)]
    pub struct Snapshot {
        pub stage: Stage,
        pub spec: MachFunction,
        pub implementation: MachFunction,
        pub frame: Option<FrameFacts>,
        pub allocator_slot_start: u32,
        /// The composed comparison's frame-lowering boundary.
        pub inserted_from: Option<u32>,
        pub report: Report,
    }

    thread_local! {
        static SINK: RefCell<Option<Vec<Snapshot>>> = const { RefCell::new(None) };
        static SPLIT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    }

    pub(crate) fn split_forced() -> bool {
        SPLIT.with(std::cell::Cell::get)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record(
        stage: Stage,
        spec: &MachFunction,
        implementation: &MachFunction,
        frame: Option<&FrameFacts>,
        allocator_slot_start: u32,
        inserted_from: Option<u32>,
        report: &Report,
    ) {
        SINK.with(|sink| {
            if let Some(list) = sink.borrow_mut().as_mut() {
                list.push(Snapshot {
                    stage,
                    spec: spec.clone(),
                    implementation: implementation.clone(),
                    frame: frame.cloned(),
                    allocator_slot_start,
                    inserted_from,
                    report: report.clone(),
                });
            }
        });
    }

    /// Run `f`, returning its result and every comparison it ran.
    pub fn capture<T>(f: impl FnOnce() -> T) -> (T, Vec<Snapshot>) {
        SINK.with(|sink| *sink.borrow_mut() = Some(Vec::new()));
        let out = f();
        let list = SINK
            .with(|sink| sink.borrow_mut().take())
            .unwrap_or_default();
        (out, list)
    }

    /// [`capture`] with the comparison split at both stage boundaries.
    pub fn capture_split<T>(f: impl FnOnce() -> T) -> (T, Vec<Snapshot>) {
        SPLIT.with(|split| split.set(true));
        let out = capture(f);
        SPLIT.with(|split| split.set(false));
        out
    }
}
