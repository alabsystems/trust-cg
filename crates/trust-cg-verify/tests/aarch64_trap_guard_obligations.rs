// trust-cg-verify/tests/aarch64_trap_guard_obligations.rs - trap-guard obligations (L04-P12)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The trap-guard obligation (`aarch64_trap_guard`) against the LIVE
//! expansions and the real pipeline, at O0 through O3:
//!
//! * the module's shape catalog is exactly what `expand_trap_*` emits for
//!   every carrier kind, width and idiom, and each expansion records the
//!   carrier it rewrote with the instructions it emitted
//!   (`MachFunction::trap_expansions`), so the window model's self-check
//!   cannot drift from codegen;
//! * a malformed carrier the expansions degrade to an unconditional trap is
//!   left unrecorded; it is refused per instance, and FAILS where its stamp
//!   names a source guard;
//! * every guard window the pipeline emits holds against its recorded carrier,
//!   executes and binds to its stamped source guard, so the trap-guard layer
//!   leaves the trap-expansion verdict on its `BRK` (uncredited without a
//!   Clean-checked replay) and the skip branch's own row; a source `Trap`
//!   keeps its bound role; the 32-bit-index bounds windows also compile, and
//!   on a Linux AArch64 host the encoded function returns an in-range index
//!   and dies with SIGTRAP on an out-of-range one, while the same function
//!   with its skip condition inverted (the control) does the opposite;
//! * mutating a pipeline function fails or refuses it, and never leaves it
//!   promotable: an inverted skip, another tested register, a displaced or
//!   dropped trap, a deleted window (with or without its record), a window
//!   that can never run, sits outside the layout or in an unreached block, a
//!   dropped first trap of two adjacent windows, a carrier and window moved
//!   together to another constant or to a register write outside X16/X17, a
//!   re-widened operand, a source `Trap` that is no longer last in its block,
//!   a `BRK` stamped with a non-trap source, and an un-expanded carrier naming
//!   another source guard;
//! * an `Assert` trap block's `BRK` and a narrow (`I16`) guard operand are
//!   refused; a guard on a constant divisor nonzero at its width needs no
//!   trap; a guard on a wrapped narrow (`I8`/`I16`) value tests the value at
//!   its width, run natively (a division by a wrapped 0 traps, a shift by or
//!   an index of it does not);
//! * a carrier and window re-targeted together to another register still
//!   hold and bind (the obligation binds the carrier's registers, not source
//!   values): the documented limit.

#[path = "support/trap_guard_fixtures.rs"]
mod fixtures;

use trust_cg_ir::{AArch64Opcode as Op, InstId, MachFunction, MachInst, MachOperand, PReg};
use trust_cg_verify::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT;
use trust_cg_verify::aarch64_trap_guard::{
    TRAP_GUARD_BOUND_ROLE, TRAP_GUARD_FAILED, TRAP_GUARD_REFUSED, TRAP_GUARD_TAG,
    trap_guard_shape_catalog,
};
use trust_cg_verify::function_verifier::{
    FunctionVerificationPreconditionFailure, FunctionVerificationReport, FunctionVerifier,
    InstructionVerificationResult,
};
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;

/// Every expansion, in the pipeline's order (Phase 7.25).
fn expand_all(func: &mut MachFunction) {
    trust_cg_codegen::lower::expand_trap_bounds_check_exact(func);
    trust_cg_codegen::lower::expand_trap_null_if_zero(func);
    trust_cg_codegen::lower::expand_trap_div_zero_if_zero(func);
    trust_cg_codegen::lower::expand_trap_shift_range_if_oob(func);
    trust_cg_codegen::lower::expand_trap_overflow_exact(func);
}

fn one_block(insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new(
        "trap_guard_live".to_string(),
        trust_cg_ir::Signature::new(vec![], vec![]),
    );
    for inst in insts {
        let id = func.push_inst(inst);
        func.blocks[0].insts.push(id);
    }
    func
}

fn shape_of(inst: &MachInst) -> (Op, Vec<MachOperand>) {
    (inst.opcode, inst.operands.clone())
}

#[test]
fn the_catalog_is_what_the_live_expansions_emit() {
    let catalog = trap_guard_shape_catalog();
    assert_eq!(catalog.len(), 24);
    for shape in catalog {
        let mut func = one_block(vec![shape.carrier.clone(), MachInst::new(Op::Ret, vec![])]);
        expand_all(&mut func);
        let emitted: Vec<_> = func.blocks[0]
            .insts
            .iter()
            .map(|id| func.inst(*id))
            .filter(|inst| inst.opcode != Op::Ret)
            .map(shape_of)
            .collect();
        let expected: Vec<_> = shape.window.iter().map(shape_of).collect();
        assert_eq!(
            emitted, expected,
            "shape `{}` drifted from its expansion",
            shape.name
        );
        assert_eq!(
            func.trap_expansions.len(),
            1,
            "shape `{}`: one expansion record",
            shape.name
        );
        let record = &func.trap_expansions[0];
        assert_eq!(
            format!("{:?}", record.carrier),
            format!("{:?}", shape.carrier),
            "shape `{}`: the record is the pre-expansion carrier",
            shape.name
        );
        assert_eq!(
            record.insts,
            func.blocks[0].insts[..shape.window.len()],
            "shape `{}`: the record lists the window, starting at the reused carrier id",
            shape.name
        );
    }
}

fn trap_failures(report: &FunctionVerificationReport) -> Vec<String> {
    report
        .instructions
        .iter()
        .filter_map(|r| match &r.result {
            InstructionVerificationResult::Failed { proof_name, detail }
                if proof_name == TRAP_GUARD_FAILED =>
            {
                Some(detail.clone())
            }
            _ => None,
        })
        .collect()
}

/// `one_block`'s LIR twin: `GuardNull v0; Return`, so a stamp can name a
/// source guard.
fn guard_null_lir() -> trust_cg_lower::Function {
    use trust_cg_lower::function::{BasicBlock, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
    let mut lir = trust_cg_lower::Function::new(
        "trap_guard_live",
        Signature {
            params: vec![trust_cg_lower::Type::I64],
            returns: vec![],
        },
    );
    lir.entry_block = Block(0);
    lir.block_order = vec![Block(0)];
    lir.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![(Value(0), trust_cg_lower::Type::I64)],
            instructions: vec![
                Instruction {
                    opcode: Opcode::GuardNull { obligation: None },
                    args: vec![Value(0)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            ..Default::default()
        },
    );
    lir
}

/// A malformed carrier degrades to a bare trap pseudo and no expansion is
/// recorded for it. With no source it is refused by name; where its stamp
/// names a source guard it FAILS, since it traps unconditionally where the
/// guard traps conditionally.
#[test]
fn a_degraded_carrier_fails_per_instance() {
    use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};
    let lir = guard_null_lir();
    let digest =
        lir.blocks[&trust_cg_lower::instructions::Block(0)].instructions[0].lowering_digest();
    let x = |n| MachOperand::PReg(PReg::new(n));
    let bad_mul_tag = trust_cg_ir::pack_overflow_tag(trust_cg_ir::OverflowOp::SignedMul, 32);
    for carrier in [
        MachInst::new(Op::TrapNullIfZero, vec![]),
        MachInst::new(Op::TrapDivZeroIfZero, vec![]),
        MachInst::new(Op::TrapShiftRangeIfOOB, vec![x(1)]),
        MachInst::new(Op::TrapBoundsCheckExact, vec![x(1)]),
        MachInst::new(
            Op::TrapOverflowExact,
            vec![x(1), x(2), MachOperand::Imm(-1)],
        ),
        MachInst::new(
            Op::TrapOverflowExact,
            vec![x(1), x(2), MachOperand::Imm(bad_mul_tag)],
        ),
    ] {
        let mut func = one_block(vec![carrier.clone(), MachInst::new(Op::Ret, vec![])]);
        expand_all(&mut func);
        assert!(func.trap_expansions.is_empty(), "{carrier:?}");
        let report = FunctionVerifier::new().verify(&func);
        let reason = refusal_of(&report.instructions[0].result, &format!("{carrier:?}"));
        assert!(reason.contains("bare trap pseudo"), "{carrier:?}: {reason}");
        assert!(!report.emitted_opcode_inventory().is_promotable());

        let mut stamped = func.clone();
        stamped.set_inst_lowering_provenance(
            stamped.blocks[0].insts[0],
            LoweringProvenance::SourceInst {
                id: SourceInstId { block: 0, index: 0 },
                digest,
                trust_ir_inst: None,
            },
        );
        let report = FunctionVerifier::new().verify_with_lir_source_and_mode(
            &stamped,
            Some(&lir),
            ProvenanceXCheckMode::Warn,
        );
        let failures = trap_failures(&report);
        assert_eq!(failures.len(), 1, "{carrier:?}: {:#?}", report.instructions);
        assert!(
            failures[0].contains("unconditional BRK #1"),
            "{carrier:?}: {}",
            failures[0]
        );
    }
}

fn verify_enforced(
    machine: &MachFunction,
    lir: &trust_cg_lower::Function,
) -> FunctionVerificationReport {
    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion())
        .verify_with_lir_source_and_mode(machine, Some(lir), ProvenanceXCheckMode::Enforce)
}

/// The row of instruction `id` (the first, if it appears twice).
fn row_of(report: &FunctionVerificationReport, id: InstId) -> &InstructionVerificationResult {
    &report
        .instructions
        .iter()
        .find(|r| r.inst_index == id.0 as usize)
        .unwrap_or_else(|| panic!("no row for instruction {}", id.0))
        .result
}

/// Whether the trap-guard layer wrote (or joined) this row.
fn is_trap_guard_row(row: &InstructionVerificationResult) -> bool {
    match row {
        InstructionVerificationResult::Failed { proof_name, detail } => {
            proof_name == TRAP_GUARD_FAILED || detail.contains(TRAP_GUARD_TAG)
        }
        InstructionVerificationResult::Unverified { reason }
        | InstructionVerificationResult::Skipped { reason } => reason.contains(TRAP_GUARD_TAG),
        InstructionVerificationResult::Verified { .. } => false,
    }
}

/// The trap-expansion verdict on a recorded expansion's `BRK` that holds:
/// uncredited without a Clean-checked replay, credited with one.
fn expansion_holds(row: &InstructionVerificationResult) -> bool {
    match row {
        InstructionVerificationResult::Unverified { reason } => {
            reason.starts_with(TRAP_EXPANSION_IS_NOT_CREDIT)
        }
        InstructionVerificationResult::Verified { proof_name, .. } => {
            proof_name.contains("trap expansion")
        }
        _ => false,
    }
}

/// The window at `first` holds, executes and binds: the trap-guard layer
/// writes no row on it, and its `BRK` carries the holding trap-expansion
/// verdict.
fn window_holds(
    machine: &MachFunction,
    report: &FunctionVerificationReport,
    first: InstId,
) -> bool {
    let window = window_at(machine, first);
    let members = &machine.blocks[window.block].insts[window.start..=window.skip + 1];
    members
        .iter()
        .all(|id| !is_trap_guard_row(row_of(report, *id)))
        && expansion_holds(row_of(report, window.brk_id(machine)))
}

/// The trap-guard refusal text of a row, or a panic naming what it was.
fn refusal_of(row: &InstructionVerificationResult, what: &str) -> String {
    match row {
        InstructionVerificationResult::Unverified { reason }
            if reason.starts_with(TRAP_GUARD_REFUSED) =>
        {
            reason.clone()
        }
        other => panic!("{what}: expected a trap-guard refusal, got {other:?}"),
    }
}

/// The trap-guard failure text of a row, or a panic naming what it was.
fn failure_of(row: &InstructionVerificationResult, what: &str) -> String {
    match row {
        InstructionVerificationResult::Failed { proof_name, detail }
            if proof_name == TRAP_GUARD_FAILED =>
        {
            detail.clone()
        }
        other => panic!("{what}: expected a trap-guard failure, got {other:?}"),
    }
}

/// The trap accounting precondition of a report, if that is what failed.
fn accounting(
    report: &FunctionVerificationReport,
) -> Option<&trust_cg_verify::aarch64_trap_guard::TrapGuardAccountingFailure> {
    match &report.precondition_failure {
        Some(FunctionVerificationPreconditionFailure::TrapGuardAccounting(failure)) => {
            Some(failure)
        }
        _ => None,
    }
}

#[test]
fn every_pipeline_guard_window_holds_and_binds_to_its_source() {
    for fixture in fixtures::fixtures() {
        for opt in fixtures::ALL_LEVELS {
            let machine = fixtures::prepare(&fixture, opt);
            let report = verify_enforced(&machine, &fixture.lir);
            assert!(
                report.precondition_failure.is_none(),
                "{} {opt:?}: {:?}",
                fixture.name,
                report.precondition_failure
            );
            assert!(
                trap_failures(&report).is_empty(),
                "{} {opt:?}: {:#?}",
                fixture.name,
                report.instructions
            );
            if fixture.name == "source_trap" {
                assert!(machine.trap_expansions.is_empty());
                let bound: Vec<_> = report
                    .instructions
                    .iter()
                    .filter(|r| {
                        matches!(&r.result, InstructionVerificationResult::Skipped { reason }
                            if reason.starts_with(TRAP_GUARD_BOUND_ROLE)
                                && reason.contains("source `Trap`"))
                    })
                    .collect();
                assert_eq!(bound.len(), 1, "{opt:?}: {:#?}", report.instructions);
                continue;
            }
            assert_eq!(
                machine.trap_expansions.len(),
                1,
                "{} {opt:?}: the pipeline records its one expansion",
                fixture.name
            );
            let first = the_window(&machine).first;
            assert!(
                window_holds(&machine, &report, first),
                "{} {opt:?}: the window holds, executes and binds, leaving the \
                 trap-expansion verdict on its BRK: {:#?}",
                fixture.name,
                report.instructions
            );
        }
    }
}

/// Where the function's one recorded window sits.
struct Window {
    first: InstId,
    block: usize,
    start: usize,
    /// Block position of the skip branch; the `BRK` follows it.
    skip: usize,
}

impl Window {
    fn skip_id(&self, machine: &MachFunction) -> InstId {
        machine.blocks[self.block].insts[self.skip]
    }

    fn brk_id(&self, machine: &MachFunction) -> InstId {
        machine.blocks[self.block].insts[self.skip + 1]
    }
}

fn window_at(machine: &MachFunction, first: InstId) -> Window {
    for (block, body) in machine.blocks.iter().enumerate() {
        if let Some(start) = body.insts.iter().position(|id| *id == first) {
            let skip = body.insts[start..]
                .iter()
                .position(|id| matches!(machine.inst(*id).opcode, Op::BCond | Op::Cbnz | Op::Cbz))
                .map(|offset| start + offset)
                .expect("a skip branch");
            return Window {
                first,
                block,
                start,
                skip,
            };
        }
    }
    panic!("the recorded carrier id {} is not in any block", first.0);
}

/// The function's one recorded window.
fn the_window(machine: &MachFunction) -> Window {
    let first = machine
        .trap_expansions
        .first()
        .and_then(|record| record.insts.first().copied())
        .expect("one recorded expansion");
    window_at(machine, first)
}

/// The carrier recorded for the window starting at `first`.
fn carrier_at(machine: &MachFunction, first: InstId) -> &MachInst {
    &machine
        .trap_expansions
        .iter()
        .find(|record| record.insts.first() == Some(&first))
        .expect("a record for the window")
        .carrier
}

/// [`carrier_at`], mutably.
fn carrier_at_mut(machine: &mut MachFunction, first: InstId) -> &mut MachInst {
    &mut machine
        .trap_expansions
        .iter_mut()
        .find(|record| record.insts.first() == Some(&first))
        .expect("a record for the window")
        .carrier
}

/// Every guard fixture prepared at every level.
fn guard_functions() -> Vec<(
    String,
    trust_cg_codegen::pipeline::OptLevel,
    MachFunction,
    trust_cg_lower::Function,
)> {
    let mut out = Vec::new();
    for fixture in fixtures::fixtures() {
        if fixture.name == "source_trap" {
            continue;
        }
        for opt in fixtures::ALL_LEVELS {
            let machine = fixtures::prepare(&fixture, opt);
            out.push((fixture.name.clone(), opt, machine, fixture.lir.clone()));
        }
    }
    out
}

fn other_register(op: &MachOperand) -> MachOperand {
    match op {
        MachOperand::PReg(p) => {
            let e = p.encoding();
            let (base, n) = if e >= 32 { (32, e - 32) } else { (0, e) };
            // A different allocatable register of the same width.
            MachOperand::PReg(PReg::new(base + if n == 9 { 10 } else { 9 }))
        }
        other => panic!("not a register: {other:?}"),
    }
}

#[test]
fn pipeline_window_mutations_fail() {
    for (name, opt, machine, lir) in guard_functions() {
        let window = the_window(&machine);
        let (first, skip, brk) = (
            window.first,
            window.skip_id(&machine),
            window.brk_id(&machine),
        );
        let mut mutations: Vec<(&str, MachFunction)> = Vec::new();

        let mut inverted = machine.clone();
        let inst = inverted.inst_mut(skip);
        match inst.opcode {
            Op::BCond => {
                if let MachOperand::Imm(cc) = &mut inst.operands[0] {
                    *cc ^= 1;
                }
            }
            Op::Cbnz => inst.opcode = Op::Cbz,
            other => panic!("{other:?}"),
        }
        mutations.push(("inverted skip condition", inverted));

        let mut wrong = machine.clone();
        let inst = wrong.inst_mut(first);
        let tested = match inst.opcode {
            Op::Cbnz | Op::CmpRI | Op::CmpRR => Some(0),
            Op::AddsRR | Op::SubsRR | Op::MulRR | Op::Umulh => Some(2),
            _ => None,
        };
        if let Some(tested) = tested {
            inst.operands[tested] = other_register(&inst.operands[tested]);
            mutations.push(("a different tested register", wrong));
        }

        let mut displaced = machine.clone();
        if let Some(MachOperand::Imm(d)) = displaced.inst_mut(skip).operands.last_mut() {
            *d = 3;
        }
        mutations.push(("skip displacement 3", displaced));

        let mut dropped = machine.clone();
        for block in &mut dropped.blocks {
            block.insts.retain(|id| *id != brk);
        }
        mutations.push(("BRK dropped", dropped));

        for (what, mutated) in mutations {
            let report = verify_enforced(&mutated, &lir);
            assert!(
                !trap_failures(&report).is_empty(),
                "{name} {opt:?} / {what}: the mutation must fail: {:#?}",
                report.instructions
            );
            // A window that does not hold implements no source guard, so it
            // accounts for none.
            let unaccounted = unaccounted(&report);
            assert!(
                unaccounted.len() == 1 && unaccounted[0].contains("Guard"),
                "{name} {opt:?} / {what}: {:?}",
                report.precondition_failure
            );
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
    }
}

/// The source traps a report's accounting found unaccounted.
fn unaccounted(report: &FunctionVerificationReport) -> Vec<String> {
    accounting(report)
        .map(|failure| failure.unaccounted_sources.clone())
        .unwrap_or_default()
}

/// A window deleted after expansion is a missing trap even though no row is
/// left to carry it: with its record kept the function FAILS
/// (`TrapGuardAccounting`, a recorded window in no block); with the record
/// cleared too, the source guard has no emitted trap and the function is
/// refused. Either way it is never promotable. A source `Trap` whose `BRK` is
/// deleted is refused the same way.
#[test]
fn a_deleted_window_fails_and_an_unaccounted_source_trap_is_refused() {
    for (name, opt, machine, lir) in guard_functions() {
        let window = the_window(&machine);
        let mut deleted = machine.clone();
        deleted.blocks[window.block]
            .insts
            .drain(window.start..=window.skip + 1);
        let report = verify_enforced(&deleted, &lir);
        let failure = accounting(&report)
            .unwrap_or_else(|| panic!("{name} {opt:?}: {:?}", report.precondition_failure));
        assert!(failure.has_missing_window(), "{name} {opt:?}: {failure}");
        assert!(failure.to_string().contains("missing trap"), "{failure}");
        assert!(report.has_failures(), "{name} {opt:?}");
        assert!(!report.emitted_opcode_inventory().is_promotable());

        deleted.trap_expansions.clear();
        let report = verify_enforced(&deleted, &lir);
        let failure = accounting(&report)
            .unwrap_or_else(|| panic!("{name} {opt:?}: {:?}", report.precondition_failure));
        assert!(!failure.has_missing_window(), "{name} {opt:?}: {failure}");
        assert_eq!(
            failure.unaccounted_sources.len(),
            1,
            "{name} {opt:?}: {failure}"
        );
        assert!(
            failure.unaccounted_sources[0].contains("Guard"),
            "{failure}"
        );
        assert!(
            failure.to_string().starts_with(TRAP_GUARD_REFUSED),
            "{failure}"
        );
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
    let source_trap = fixtures::fixtures()
        .into_iter()
        .find(|fixture| fixture.name == "source_trap")
        .expect("the source Trap fixture");
    for opt in fixtures::ALL_LEVELS {
        let mut machine = fixtures::prepare(&source_trap, opt);
        let brks: Vec<InstId> = machine
            .blocks
            .iter()
            .flat_map(|body| body.insts.iter().copied())
            .filter(|id| machine.inst(*id).opcode == Op::Brk)
            .collect();
        assert_eq!(brks.len(), 1, "{opt:?}: one BRK");
        for block in &mut machine.blocks {
            block.insts.retain(|id| !brks.contains(id));
        }
        let report = verify_enforced(&machine, &source_trap.lir);
        let failure = accounting(&report)
            .unwrap_or_else(|| panic!("{opt:?}: {:?}", report.precondition_failure));
        assert!(failure.unaccounted_sources[0].contains("Trap"), "{failure}");
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
}

/// A general-purpose register number in X9-X15 that no instruction of the
/// window and no operand of its record names, in either view.
fn unused_gpr(machine: &MachFunction, window: &Window) -> u16 {
    let carrier = carrier_at(machine, window.first);
    let names = |n: u16, op: &MachOperand| matches!(op, MachOperand::PReg(p) if p.encoding() == n || p.encoding() == 32 + n);
    (9..=15)
        .find(|&n| {
            !carrier.operands.iter().any(|op| names(n, op))
                && machine.blocks[window.block].insts[window.start..=window.skip + 1]
                    .iter()
                    .all(|id| !machine.inst(*id).operands.iter().any(|op| names(n, op)))
        })
        .expect("a free register in X9-X15")
}

/// A window moved past the function's `RET` (dead code no branch targets)
/// never runs: its trap is missing and its rows FAIL. A window moved into a
/// block outside the emitted layout is refused (never encoded), never
/// credited. A window that does not execute accounts for no source guard, so
/// the function is also refused for the guard it lost.
#[test]
fn a_window_that_never_runs_fails_and_one_outside_the_layout_is_refused() {
    for (name, opt, machine, lir) in guard_functions() {
        let window = the_window(&machine);
        let skip = window.skip_id(&machine);
        let brk = window.brk_id(&machine);
        let mut moved = machine.clone();
        let ids: Vec<InstId> = moved.blocks[window.block]
            .insts
            .drain(window.start..=window.skip + 1)
            .collect();
        let ret_block = moved
            .block_order
            .iter()
            .map(|b| b.0 as usize)
            .find(|&b| {
                moved.blocks[b]
                    .insts
                    .last()
                    .is_some_and(|id| moved.inst(*id).opcode == Op::Ret)
            })
            .unwrap_or_else(|| panic!("{name} {opt:?}: a RET block"));
        let mut after_ret = moved.clone();
        after_ret.blocks[ret_block]
            .insts
            .extend(ids.iter().copied());
        let report = verify_enforced(&after_ret, &lir);
        // The stamped first instruction may also carry an enforced TV-2
        // finding; the unstamped skip branch and BRK carry the trap verdict.
        for id in [skip, brk] {
            let detail = failure_of(row_of(&report, id), &format!("{name} {opt:?} after RET"));
            assert!(detail.contains("never executes"), "{detail}");
        }
        assert_eq!(unaccounted(&report).len(), 1, "{name} {opt:?} after RET");
        assert!(report.has_failures());
        assert!(!report.emitted_opcode_inventory().is_promotable());

        let mut shell = moved.clone();
        shell.blocks.push(trust_cg_ir::MachBlock {
            insts: ids.clone(),
            preds: Vec::new(),
            succs: Vec::new(),
            loop_depth: 0,
        });
        let report = verify_enforced(&shell, &lir);
        assert_eq!(
            unaccounted(&report).len(),
            1,
            "{name} {opt:?} shell: {:?}",
            report.precondition_failure
        );
        for id in [skip, brk] {
            let reason = refusal_of(row_of(&report, id), &format!("{name} {opt:?} shell"));
            assert!(reason.contains("not in the emitted layout"), "{reason}");
        }
        assert!(trap_failures(&report).is_empty(), "{name} {opt:?}");
        assert!(!report.emitted_opcode_inventory().is_promotable());

        // The same block laid out, but with no recorded edge into it.
        let shell_block = trust_cg_ir::BlockId((shell.blocks.len() - 1) as u32);
        shell.block_order.push(shell_block);
        let report = verify_enforced(&shell, &lir);
        for id in [skip, brk] {
            let reason = refusal_of(row_of(&report, id), &format!("{name} {opt:?} unreached"));
            assert!(reason.contains("is not reached from the entry"), "{reason}");
        }
        assert_eq!(unaccounted(&report).len(), 1, "{name} {opt:?} unreached");
        assert!(trap_failures(&report).is_empty(), "{name} {opt:?}");
        assert!(!report.emitted_opcode_inventory().is_promotable());

        // Declaring that block the stack-limit overflow block does not make
        // it reached: only a check the stack-limit net certifies enters it.
        shell.stack_limit_overflow_block = Some(shell_block);
        shell.stack_limit = Some(trust_cg_ir::MachStackLimit {
            request: trust_cg_ir::StackLimitRequest {
                param: 0,
                source: trust_cg_ir::StackLimitSource::Value,
                overflow: trust_cg_ir::StackLimitOverflow::Trap,
            },
            limit_reg: PReg::new(0),
            arg_regs: vec![PReg::new(0)],
        });
        let report = verify_enforced(&shell, &lir);
        for id in [skip, brk] {
            let reason = refusal_of(
                row_of(&report, id),
                &format!("{name} {opt:?} declared overflow block"),
            );
            assert!(reason.contains("is not reached from the entry"), "{reason}");
        }
        assert_eq!(
            unaccounted(&report).len(),
            1,
            "{name} {opt:?} declared overflow block"
        );
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
}

/// Delete the function's one recorded window (every instruction its
/// expansion emitted) and its record; return the first instruction's stamp.
fn delete_the_window(machine: &MachFunction) -> (MachFunction, trust_cg_ir::LoweringProvenance) {
    let record = machine.trap_expansions[0].clone();
    let stamp = machine.inst_lowering_provenance(record.insts[0]);
    let mut deleted = machine.clone();
    for block in &mut deleted.blocks {
        block.insts.retain(|id| !record.insts.contains(id));
    }
    deleted.trap_expansions.clear();
    (deleted, stamp)
}

/// A block outside the layout holding `insts`, as a forged role would add it.
fn push_block(
    machine: &mut MachFunction,
    insts: Vec<MachInst>,
) -> (trust_cg_ir::BlockId, Vec<InstId>) {
    let ids: Vec<InstId> = insts
        .into_iter()
        .map(|inst| machine.push_inst(inst))
        .collect();
    machine.blocks.push(trust_cg_ir::MachBlock {
        insts: ids.clone(),
        preds: Vec::new(),
        succs: Vec::new(),
        loop_depth: 0,
    });
    (trust_cg_ir::BlockId((machine.blocks.len() - 1) as u32), ids)
}

/// A window whose skip branch and `BRK` were deleted keeps its stamped first
/// instruction, which is no trap: with or without its record, the guard is
/// unaccounted and the function refused. With the record kept, the window's
/// own rows fail (the trap is missing) or are refused (the scan reaches an
/// instruction outside the window vocabulary).
#[test]
fn a_window_missing_its_trap_tail_accounts_for_nothing() {
    let mut reaches_a_return = 0;
    for (name, opt, machine, lir) in guard_functions() {
        let record = machine.trap_expansions[0].clone();
        // The skip branch and the BRK; a CBNZ window's skip branch is its
        // stamped first instruction, so only its BRK goes.
        let kept_len = record.insts.len().saturating_sub(2).max(1);
        let (head, tail) = record.insts.split_at(kept_len);
        let mut kept = machine.clone();
        for block in &mut kept.blocks {
            block.insts.retain(|id| !tail.contains(id));
        }
        let mut cleared = kept.clone();
        cleared.trap_expansions.clear();
        // Where the kept head is followed by a return or branch, the window
        // scan reaches it before any skip branch: a missing trap, FAILED.
        let last = *head.last().expect("a head");
        let after = kept.blocks.iter().find_map(|body| {
            let at = body.insts.iter().position(|id| *id == last)?;
            body.insts.get(at + 1).copied()
        });
        if record.insts.len() > 2
            && after.is_some_and(|id| matches!(kept.inst(id).opcode, Op::Ret | Op::B | Op::Br))
        {
            reaches_a_return += 1;
            let report = verify_enforced(&kept, &lir);
            assert!(
                trap_failures(&report)
                    .iter()
                    .any(|detail| detail.contains("before any skip branch")),
                "{name} {opt:?}: {:#?}",
                report.instructions
            );
        }
        for (what, mutated) in [("record kept", kept), ("record cleared", cleared)] {
            let report = verify_enforced(&mutated, &lir);
            let unaccounted = unaccounted(&report);
            assert!(
                unaccounted.len() == 1 && unaccounted[0].contains("Guard"),
                "{name} {opt:?} {what}: {:?}",
                report.precondition_failure
            );
            if what == "record kept" {
                // The window's remaining instructions carry its verdict (the
                // stamped first one may carry an enforced TV-2 finding
                // instead).
                assert!(
                    head.iter()
                        .any(|id| is_trap_guard_row(row_of(&report, *id))),
                    "{name} {opt:?}: {:#?}",
                    report.instructions
                );
            }
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
    }
    assert!(
        reaches_a_return > 0,
        "no window head is followed by a return"
    );
}

/// A guard whose window was deleted cannot be accounted for by a `BRK` that
/// merely carries its stamp. The stack-limit trap word in a declared overflow
/// block (with or without the stamp, the function's stack-limit fields
/// forged) is refused because the stack-limit net certifies no such check,
/// the `BRK` after `_Unwind_Resume` is refused because the stamp names a
/// source trap that role does not implement, and a plain `BRK` in the
/// window's place has no modeled role for a guard. None of them accounts for
/// the guard: the function is refused for it, never promotable.
#[test]
fn a_guard_stamp_on_a_role_brk_accounts_for_nothing() {
    use trust_cg_ir::{MachStackLimit, StackLimitOverflow, StackLimitRequest, StackLimitSource};
    let stack_limit_word = || {
        MachInst::new(
            Op::Brk,
            vec![MachOperand::Imm(i64::from(
                trust_cg_ir::STACK_LIMIT_TRAP_IMM,
            ))],
        )
    };
    for (name, opt, machine, lir) in guard_functions() {
        let (deleted, stamp) = delete_the_window(&machine);
        let mut cases: Vec<(&str, MachFunction, InstId, &str)> = Vec::new();
        for stamped in [true, false] {
            let mut forged = deleted.clone();
            let (block, ids) = push_block(&mut forged, vec![stack_limit_word()]);
            if stamped {
                forged.set_inst_lowering_provenance(ids[0], stamp);
            }
            forged.stack_limit_overflow_block = Some(block);
            forged.stack_limit = Some(MachStackLimit {
                request: StackLimitRequest {
                    param: 0,
                    source: StackLimitSource::Value,
                    overflow: StackLimitOverflow::Trap,
                },
                limit_reg: PReg::new(0),
                arg_regs: vec![PReg::new(0)],
            });
            cases.push((
                if stamped {
                    "stamped stack-limit trap"
                } else {
                    "unstamped stack-limit trap"
                },
                forged,
                ids[0],
                if stamped {
                    "carries a source stamp"
                } else {
                    "its role is not certified"
                },
            ));
        }
        let mut noreturn = deleted.clone();
        let (_, ids) = push_block(
            &mut noreturn,
            vec![
                MachInst::new(Op::Bl, vec![MachOperand::Symbol("_Unwind_Resume".into())]),
                MachInst::new(Op::Brk, vec![]),
            ],
        );
        noreturn.set_inst_lowering_provenance(ids[1], stamp);
        cases.push(("noreturn BRK", noreturn, ids[1], "does not implement"));
        let mut plain = machine.clone();
        let window = the_window(&machine);
        let record = plain.trap_expansions[0].clone();
        let brk = plain.push_inst(MachInst::new(Op::Brk, vec![]));
        plain.set_inst_lowering_provenance(brk, stamp);
        let body = &mut plain.blocks[window.block].insts;
        body.retain(|id| !record.insts.contains(id));
        body.insert(window.start, brk);
        plain.trap_expansions.clear();
        cases.push((
            "plain BRK in the window's place",
            plain,
            brk,
            "no modeled trap role",
        ));

        for (what, mutated, brk, why) in cases {
            let report = verify_enforced(&mutated, &lir);
            let reason = refusal_of(row_of(&report, brk), &format!("{name} {opt:?} {what}"));
            assert!(reason.contains(why), "{name} {opt:?} {what}: {reason}");
            let unaccounted = unaccounted(&report);
            assert!(
                unaccounted.len() == 1 && unaccounted[0].contains("Guard"),
                "{name} {opt:?} {what}: {:?}",
                report.precondition_failure
            );
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
    }
}

/// The stack-limit trap of a frame the U10 net certifies keeps its bound
/// role, at O0-O3 through the real pipeline. A source stamp on it, a second
/// instruction in its overflow block, or a check the net no longer certifies
/// (its `B.LO` into the overflow block removed) refuses the role.
#[test]
fn the_stack_limit_trap_keeps_its_role_only_where_certified() {
    let fixture = fixtures::stack_limited();
    for opt in fixtures::ALL_LEVELS {
        let machine = fixtures::prepare(&fixture, opt);
        let overflow = machine
            .stack_limit_overflow_block
            .unwrap_or_else(|| panic!("{opt:?}: an overflow block"));
        let brk = machine.blocks[overflow.0 as usize].insts[0];
        assert_eq!(
            machine.inst(brk).operands,
            vec![MachOperand::Imm(i64::from(
                trust_cg_ir::STACK_LIMIT_TRAP_IMM
            ))],
            "{opt:?}"
        );
        let report = verify_enforced(&machine, &fixture.lir);
        assert!(
            report.precondition_failure.is_none(),
            "{opt:?}: {:?}",
            report.precondition_failure
        );
        assert!(
            matches!(row_of(&report, brk), InstructionVerificationResult::Skipped { reason }
                if reason.starts_with(TRAP_GUARD_BOUND_ROLE) && reason.contains("certifies")),
            "{opt:?}: {:?}",
            row_of(&report, brk)
        );

        let mut stamped = machine.clone();
        let stamp = machine
            .blocks
            .iter()
            .flat_map(|body| body.insts.iter().copied())
            .map(|id| machine.inst_lowering_provenance(id))
            .find(|provenance| provenance.is_source_attributed())
            .expect("a stamped instruction");
        stamped.set_inst_lowering_provenance(brk, stamp);
        let mut crowded = machine.clone();
        let nop = crowded.push_inst(MachInst::new(Op::Nop, vec![]));
        crowded.blocks[overflow.0 as usize].insts.insert(0, nop);
        let mut unchecked = machine.clone();
        let branches: Vec<InstId> = machine
            .blocks
            .iter()
            .flat_map(|body| body.insts.iter().copied())
            .filter(|id| {
                let inst = machine.inst(*id);
                inst.opcode == Op::BCond && inst.operands.first() == Some(&MachOperand::Imm(3))
            })
            .collect();
        assert!(!branches.is_empty(), "{opt:?}: the check's B.LO");
        for body in &mut unchecked.blocks {
            body.insts.retain(|id| !branches.contains(id));
        }
        for (what, mutated) in [
            ("stamped", stamped),
            ("crowded", crowded),
            ("unchecked", unchecked),
        ] {
            let report = verify_enforced(&mutated, &fixture.lir);
            let reason = refusal_of(row_of(&report, brk), &format!("{opt:?} {what}"));
            assert!(reason.contains("stack-limit"), "{opt:?} {what}: {reason}");
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
    }
}

/// A source `Trap` behind a conditional branch (`ctrap`): its `BRK` executes
/// and accounts for the `Trap`, but the branches that reach it are not
/// checked here, so its row is refused, never a promotable role. Inverting
/// those branches or swapping the `BRK` onto the return path keeps it
/// refused; taking its block out of the layout refuses it and, like deleting
/// it, leaves the `Trap` unaccounted. The entry-block `Trap` (`source_trap`)
/// keeps its bound role until a control transfer precedes its `BRK`; a `RET`
/// before it makes it dead code, which FAILS and leaves the `Trap`
/// unaccounted.
#[test]
fn a_source_trap_brk_must_execute_and_binds_only_at_the_entry() {
    let ctrap = fixtures::conditional_trap();
    let brk_of = |machine: &MachFunction| {
        machine
            .blocks
            .iter()
            .enumerate()
            .find_map(|(b, body)| {
                body.insts
                    .iter()
                    .position(|id| machine.inst(*id).opcode == Op::Brk)
                    .map(|p| (b, p, body.insts[p]))
            })
            .expect("the BRK")
    };
    let placement = "reached through branches whose polarity";
    for opt in fixtures::ALL_LEVELS {
        let machine = fixtures::prepare(&ctrap, opt);
        let (bb, bp, brk) = brk_of(&machine);
        let report = verify_enforced(&machine, &ctrap.lir);
        assert!(report.precondition_failure.is_none(), "{opt:?}");
        let reason = refusal_of(row_of(&report, brk), &format!("{opt:?} intact"));
        assert!(reason.contains(placement), "{reason}");

        let mut inverted = machine.clone();
        let mut flipped = 0;
        for body in machine.blocks.iter() {
            for id in &body.insts {
                let inst = inverted.inst_mut(*id);
                match inst.opcode {
                    Op::Cbz => inst.opcode = Op::Cbnz,
                    Op::Cbnz => inst.opcode = Op::Cbz,
                    Op::Tbz => inst.opcode = Op::Tbnz,
                    Op::Tbnz => inst.opcode = Op::Tbz,
                    Op::BCond => {
                        if let MachOperand::Imm(cc) = &mut inst.operands[0] {
                            *cc ^= 1;
                        }
                    }
                    _ => continue,
                }
                flipped += 1;
            }
        }
        assert!(flipped > 0, "{opt:?}: a branch to invert");
        let (rb, rp, _) = machine
            .blocks
            .iter()
            .enumerate()
            .find_map(|(b, body)| {
                body.insts
                    .iter()
                    .position(|id| machine.inst(*id).opcode == Op::Ret)
                    .map(|p| (b, p, body.insts[p]))
            })
            .expect("the RET");
        let mut swapped = machine.clone();
        let ret = swapped.blocks[rb].insts[rp];
        swapped.blocks[bb].insts[bp] = ret;
        swapped.blocks[rb].insts[rp] = brk;
        // The trap hoisted into the entry block with its branches removed:
        // it now traps on every call, where the source traps only for a
        // zero argument. It closes the machine entry block with nothing
        // before it that transfers control, but the `Trap` it names is not
        // the LIR entry block's, so the entry role does not bind it.
        let mut hoisted = machine.clone();
        hoisted.blocks[bb].insts.remove(bp);
        let entry = machine.entry.0 as usize;
        hoisted.blocks[entry].insts.retain(|id| {
            !matches!(
                machine.inst(*id).opcode,
                Op::B | Op::BCond | Op::Cbz | Op::Cbnz | Op::Tbz | Op::Tbnz | Op::Ret
            )
        });
        hoisted.blocks[entry].insts.push(brk);
        for (what, mutated) in [
            ("inverted", inverted),
            ("swapped", swapped),
            ("hoisted", hoisted),
        ] {
            let report = verify_enforced(&mutated, &ctrap.lir);
            let reason = refusal_of(row_of(&report, brk), &format!("{opt:?} {what}"));
            assert!(reason.contains(placement), "{opt:?} {what}: {reason}");
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }

        let mut unlaid = machine.clone();
        unlaid.block_order.retain(|b| b.0 as usize != bb);
        let report_unlaid = verify_enforced(&unlaid, &ctrap.lir);
        let reason = refusal_of(row_of(&report_unlaid, brk), &format!("{opt:?} unlaid"));
        assert!(reason.contains("not shown to execute"), "{reason}");
        let mut deleted = machine.clone();
        deleted.blocks[bb].insts.remove(bp);
        let report_deleted = verify_enforced(&deleted, &ctrap.lir);
        for (what, report) in [("unlaid", &report_unlaid), ("deleted", &report_deleted)] {
            let unaccounted = unaccounted(report);
            assert!(
                unaccounted.len() == 1 && unaccounted[0].contains("Trap"),
                "{opt:?} {what}: {:?}",
                report.precondition_failure
            );
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
    }

    let source_trap = fixtures::fixtures()
        .into_iter()
        .find(|fixture| fixture.name == "source_trap")
        .expect("the source Trap fixture");
    for opt in fixtures::ALL_LEVELS {
        let machine = fixtures::prepare(&source_trap, opt);
        let (bb, bp, brk) = brk_of(&machine);
        assert_eq!(
            bb, machine.entry.0 as usize,
            "{opt:?}: the entry block's BRK"
        );
        let report = verify_enforced(&machine, &source_trap.lir);
        assert!(
            matches!(row_of(&report, brk), InstructionVerificationResult::Skipped { reason }
                if reason.starts_with(TRAP_GUARD_BOUND_ROLE) && reason.contains("entry block")),
            "{opt:?}: {:?}",
            row_of(&report, brk)
        );
        let mut branched = machine.clone();
        let cbz = branched.push_inst(MachInst::new(
            Op::Cbz,
            vec![MachOperand::PReg(PReg::new(0)), MachOperand::Imm(1)],
        ));
        branched.blocks[bb].insts.insert(bp, cbz);
        let report = verify_enforced(&branched, &source_trap.lir);
        let reason = refusal_of(row_of(&report, brk), &format!("{opt:?} branched"));
        assert!(reason.contains(placement), "{reason}");
        // A RET before it, in a function with no branch: the BRK is dead
        // code, its trap missing.
        let mut dead = machine.clone();
        let ret = dead.push_inst(MachInst::new(Op::Ret, vec![]));
        dead.blocks[bb].insts.insert(bp, ret);
        let report = verify_enforced(&dead, &source_trap.lir);
        let detail = failure_of(row_of(&report, brk), &format!("{opt:?} dead"));
        assert!(detail.contains("never executes"), "{detail}");
        let unaccounted = unaccounted(&report);
        assert!(
            unaccounted.len() == 1 && unaccounted[0].contains("Trap"),
            "{opt:?} dead: {:?}",
            report.precondition_failure
        );
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
}

/// A function verified with its exact carrier still un-expanded (the stream
/// before Phase 7.25) accounts its source guard through the carrier, which
/// binds to it: the trap-guard layer leaves the trap-expansion verdict on its
/// stated expansion. The same carrier naming another constant than its
/// stamped source FAILS, and one behind a `RET` never executes: FAILED and
/// unaccounted.
#[test]
fn an_unexpanded_carrier_is_accounted_and_bound() {
    let mut dead_cases = 0;
    for (name, opt, machine, lir) in guard_functions() {
        let window = the_window(&machine);
        let mut unexpanded = machine.clone();
        let carrier = carrier_at(&unexpanded, window.first).clone();
        unexpanded.trap_expansions.clear();
        *unexpanded.inst_mut(window.first) = carrier;
        unexpanded.blocks[window.block]
            .insts
            .drain(window.start + 1..=window.skip + 1);
        let report = verify_enforced(&unexpanded, &lir);
        assert!(
            report.precondition_failure.is_none(),
            "{name} {opt:?}: {:?}",
            report.precondition_failure
        );
        let row = row_of(&report, window.first);
        assert!(!is_trap_guard_row(row), "{name} {opt:?}: {row:?}");
        assert!(trap_failures(&report).is_empty(), "{name} {opt:?}");

        // A RET in front of it, in a function with no other branch: the
        // carrier is dead code, its trap missing, and it accounts for nothing.
        let branch_free = unexpanded
            .blocks
            .iter()
            .flat_map(|body| body.insts.iter())
            .all(|id| {
                !matches!(
                    unexpanded.inst(*id).opcode,
                    Op::B | Op::BCond | Op::Cbz | Op::Cbnz | Op::Tbz | Op::Tbnz | Op::Br
                )
            });
        if branch_free {
            dead_cases += 1;
            let mut dead = unexpanded.clone();
            let ret = dead.push_inst(MachInst::new(Op::Ret, vec![]));
            dead.blocks[window.block].insts.insert(window.start, ret);
            let report = verify_enforced(&dead, &lir);
            let detail = failure_of(
                row_of(&report, window.first),
                &format!("{name} {opt:?} dead"),
            );
            assert!(detail.contains("never executes"), "{detail}");
            assert_eq!(unaccounted(&report).len(), 1, "{name} {opt:?} dead");
        }

        if let Some(MachOperand::Imm(k)) = unexpanded.inst_mut(window.first).operands.last_mut()
            && matches!(
                name.as_str(),
                "bounds_const_10" | "shift_range_ishl_i32" | "shift_range_ushr_i64"
            )
        {
            *k += 1;
            let report = verify_enforced(&unexpanded, &lir);
            let detail = failure_of(row_of(&report, window.first), &format!("{name} {opt:?}"));
            assert!(
                detail.contains("does not implement its stamped source"),
                "{detail}"
            );
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
    }
    assert!(dead_cases > 0, "no branch-free un-expanded fixture");
}

/// Two adjacent bounds guards with the FIRST window's skip branch and `BRK`
/// removed. Each carrier keeps its own verdict: the first, whose scan runs
/// into the second's window, FAILS on its own row; the intact second window
/// still holds on its rows. The function is failed and never promotable.
#[test]
fn adjacent_windows_keep_per_carrier_verdicts() {
    let fixture = fixtures::two_bounds();
    let mut adjacent = 0;
    for opt in fixtures::ALL_LEVELS {
        let machine = fixtures::prepare(&fixture, opt);
        let intact = verify_enforced(&machine, &fixture.lir);
        let mut windows: Vec<Window> = machine
            .trap_expansions
            .iter()
            .map(|record| window_at(&machine, record.insts[0]))
            .collect();
        windows.sort_by_key(|w| (w.block, w.start));
        assert_eq!(windows.len(), 2, "{opt:?}");
        for window in &windows {
            assert!(
                window_holds(&machine, &intact, window.first),
                "{opt:?}: {:#?}",
                intact.instructions
            );
        }
        let (one, two) = (&windows[0], &windows[1]);
        if one.block != two.block || one.skip + 2 != two.start {
            continue;
        }
        adjacent += 1;
        let mut mutated = machine.clone();
        let (skip, brk) = (one.skip_id(&machine), one.brk_id(&machine));
        mutated.blocks[one.block]
            .insts
            .retain(|id| *id != skip && *id != brk);
        let report = verify_enforced(&mutated, &fixture.lir);
        let detail = failure_of(
            row_of(&report, one.first),
            &format!("{opt:?} first carrier"),
        );
        assert!(
            detail.contains("runs into the recorded window of another carrier"),
            "{detail}"
        );
        assert!(
            window_holds(&mutated, &report, two.first),
            "{opt:?}: the second window keeps its own verdict: {:#?}",
            report.instructions
        );
        assert!(report.has_failures());
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
    assert!(adjacent > 0, "no level emitted the two windows adjacently");
}

/// A carrier record and its window changed TOGETHER to another constant: the
/// window holds against the record, and only the binding to the stamped
/// source catches it. It FAILS.
#[test]
fn a_carrier_naming_another_source_guard_fails() {
    for (name, opt, machine, lir) in guard_functions() {
        if !matches!(
            name.as_str(),
            "bounds_const_10" | "shift_range_ishl_i32" | "shift_range_ushr_i64"
        ) {
            continue;
        }
        let window = the_window(&machine);
        let mut mutated = machine.clone();
        let carrier = carrier_at_mut(&mut mutated, window.first);
        let Some(MachOperand::Imm(k)) = carrier.operands.last_mut() else {
            panic!("{name}: constant carrier");
        };
        *k += 1;
        let cmp = mutated.inst_mut(window.first);
        assert_eq!(cmp.opcode, Op::CmpRI, "{name} {opt:?}");
        let Some(MachOperand::Imm(k)) = cmp.operands.last_mut() else {
            panic!("{name}: CMP #imm");
        };
        *k += 1;
        let report = verify_enforced(&mutated, &lir);
        for id in [window.skip_id(&machine), window.brk_id(&machine)] {
            let detail = failure_of(row_of(&report, id), &format!("{name} {opt:?}"));
            assert!(
                detail.contains("does not implement its stamped source"),
                "{detail}"
            );
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
}

/// Only an `I32` in a W register and an `I64` in an X register bind: a
/// narrow (`I16`) divisor in a W register, and an `I64` index whose record
/// and window were both moved to its W view, hold but stay refused.
#[test]
fn an_operand_wider_or_narrower_than_its_source_leaves_the_window_unbound() {
    let narrow = fixtures::div_zero_i16();
    for opt in fixtures::ALL_LEVELS {
        let machine = fixtures::prepare(&narrow, opt);
        let report = verify_enforced(&machine, &narrow.lir);
        let window = the_window(&machine);
        for id in [window.skip_id(&machine), window.brk_id(&machine)] {
            let reason = refusal_of(row_of(&report, id), &format!("I16 divisor {opt:?}"));
            assert!(reason.contains("traps exactly when"), "{reason}");
            assert!(
                reason.contains("only I32 in W and I64 in X bind exactly"),
                "{reason}"
            );
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
    for (name, opt, machine, lir) in guard_functions() {
        if name != "bounds_const_10" {
            continue;
        }
        let window = the_window(&machine);
        let w_view = |op: &mut MachOperand| {
            if let MachOperand::PReg(p) = op
                && p.encoding() <= 30
            {
                *op = MachOperand::PReg(PReg::new(32 + p.encoding()));
            }
        };
        let mut mutated = machine.clone();
        let carrier = carrier_at_mut(&mut mutated, window.first);
        w_view(&mut carrier.operands[1]);
        w_view(&mut mutated.inst_mut(window.first).operands[0]);
        let report = verify_enforced(&mutated, &lir);
        for id in [window.skip_id(&machine), window.brk_id(&machine)] {
            let reason = refusal_of(row_of(&report, id), &format!("{name} {opt:?} W view"));
            assert!(reason.contains("traps exactly when"), "{reason}");
            assert!(
                reason.contains("only I32 in W and I64 in X bind exactly"),
                "{reason}"
            );
        }
    }
}

/// The scratch of a MOVZ (+MOVK) bounds window moved from X16 to X9: the
/// window still traps exactly when the index is out of bounds, but it writes
/// a register outside X16/X17 and is refused.
#[test]
fn a_window_writing_outside_the_ip_scratch_registers_is_refused() {
    let mut seen = 0;
    for (name, opt, machine, lir) in guard_functions() {
        if !matches!(
            name.as_str(),
            "bounds_const_0x1234" | "bounds_const_0x123456"
        ) {
            continue;
        }
        seen += 1;
        let window = the_window(&machine);
        let scratch = MachOperand::PReg(PReg::new(unused_gpr(&machine, &window)));
        let mut mutated = machine.clone();
        for &id in &machine.blocks[window.block].insts[window.start..window.skip] {
            for op in &mut mutated.inst_mut(id).operands {
                if *op == MachOperand::PReg(trust_cg_ir::regs::X16) {
                    *op = scratch.clone();
                }
            }
        }
        let report = verify_enforced(&mutated, &lir);
        let reason = refusal_of(
            row_of(&report, window.skip_id(&machine)),
            &format!("{name} {opt:?}"),
        );
        assert!(
            reason.contains("outside the IP scratch registers X16/X17"),
            "{reason}"
        );
        // The trap-expansion verdict refutes the same window (its words may
        // write only X16/X17); the BRK keeps both findings.
        let brk = row_of(&report, window.brk_id(&machine));
        assert!(
            matches!(brk, InstructionVerificationResult::Failed { detail, .. }
                if detail.contains("outside the IP scratch registers X16/X17")),
            "{name} {opt:?}: {brk:?}"
        );
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
    assert_eq!(seen, 2 * fixtures::ALL_LEVELS.len());
}

/// The bound role of a source `Trap` needs its `BRK` to close its block.
#[test]
fn a_source_trap_brk_that_is_not_last_in_its_block_is_refused() {
    let source_trap = fixtures::fixtures()
        .into_iter()
        .find(|fixture| fixture.name == "source_trap")
        .expect("the source Trap fixture");
    for opt in fixtures::ALL_LEVELS {
        let mut machine = fixtures::prepare(&source_trap, opt);
        let (block, pos) = machine
            .blocks
            .iter()
            .enumerate()
            .find_map(|(b, body)| {
                body.insts
                    .iter()
                    .position(|id| machine.inst(*id).opcode == Op::Brk)
                    .map(|p| (b, p))
            })
            .expect("the BRK");
        let brk = machine.blocks[block].insts[pos];
        let nop = machine.push_inst(MachInst::new(Op::Nop, vec![]));
        machine.blocks[block].insts.insert(pos + 1, nop);
        let report = verify_enforced(&machine, &source_trap.lir);
        let reason = refusal_of(row_of(&report, brk), &format!("{opt:?}"));
        assert!(
            reason.contains("is not the last instruction of its block"),
            "{reason}"
        );
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
}

/// The `BRK` of an `Assert` trap block (its CMP/B.EQ sits in the predecessor
/// block) is refused by name, never a bound role. It accounts for the
/// `Assert`: with it deleted (and with the branch into its block deleted too)
/// the function is refused for the `Assert`.
#[test]
fn an_assert_trap_block_brk_is_refused() {
    for ty in [
        trust_cg_lower::Type::I8,
        trust_cg_lower::Type::I32,
        trust_cg_lower::Type::I64,
    ] {
        let fixture = fixtures::assert_on(ty);
        for opt in fixtures::ALL_LEVELS {
            let machine = fixtures::prepare(&fixture, opt);
            let report = verify_enforced(&machine, &fixture.lir);
            assert!(
                report.precondition_failure.is_none(),
                "{} {opt:?}: {:?}",
                fixture.name,
                report.precondition_failure
            );
            let brks: Vec<InstId> = machine
                .blocks
                .iter()
                .flat_map(|body| body.insts.iter().copied())
                .filter(|id| machine.inst(*id).opcode == Op::Brk)
                .collect();
            assert_eq!(brks.len(), 1, "{} {opt:?}", fixture.name);
            let reason = refusal_of(
                row_of(&report, brks[0]),
                &format!("{} {opt:?}", fixture.name),
            );
            assert!(reason.contains("BRK of an `Assert` trap block"), "{reason}");
            assert!(!report.emitted_opcode_inventory().is_promotable());

            let mut no_brk = machine.clone();
            for body in &mut no_brk.blocks {
                body.insts.retain(|id| *id != brks[0]);
            }
            let mut no_trap = no_brk.clone();
            for body in &mut no_trap.blocks {
                body.insts.retain(|id| {
                    !matches!(
                        machine.inst(*id).opcode,
                        Op::BCond | Op::Cbz | Op::Cbnz | Op::Tbz | Op::Tbnz
                    )
                });
            }
            let brk_block = machine
                .blocks
                .iter()
                .position(|body| body.insts.contains(&brks[0]))
                .expect("the BRK's block");
            let mut unlaid = machine.clone();
            unlaid.block_order.retain(|b| b.0 as usize != brk_block);
            for (what, mutated) in [
                ("BRK deleted", no_brk),
                ("BRK and branch deleted", no_trap),
                ("BRK block out of the layout", unlaid),
            ] {
                let report = verify_enforced(&mutated, &fixture.lir);
                let unaccounted = unaccounted(&report);
                assert!(
                    unaccounted.len() == 1 && unaccounted[0].contains("Assert"),
                    "{} {opt:?} {what}: {:?}",
                    fixture.name,
                    report.precondition_failure
                );
                assert!(!report.emitted_opcode_inventory().is_promotable());
            }
        }
    }
}

/// A `BRK` whose TV-1 stamp names a source that is not a trap (here the
/// division a guard protects, rewritten in place) has no bound role.
#[test]
fn a_brk_stamped_with_a_non_trap_source_is_refused() {
    let mut seen = 0;
    for (name, opt, machine, lir) in guard_functions() {
        if name != "div_zero_udiv_i64" {
            continue;
        }
        let Some(div) = machine
            .blocks
            .iter()
            .flat_map(|body| body.insts.iter().copied())
            .find(|id| machine.inst(*id).opcode == Op::UDiv)
        else {
            panic!("{name} {opt:?}: a UDIV");
        };
        seen += 1;
        let mut mutated = machine.clone();
        let inst = mutated.inst_mut(div);
        inst.opcode = Op::Brk;
        inst.operands.clear();
        inst.flags = Op::Brk.default_flags();
        let report = verify_enforced(&mutated, &lir);
        let reason = refusal_of(row_of(&report, div), &format!("{name} {opt:?}"));
        assert!(reason.contains("has no modeled trap role"), "{reason}");
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
    assert_eq!(seen, fixtures::ALL_LEVELS.len());
}

/// The documented limit: a carrier record and its window re-targeted
/// together to another register still hold and bind (nothing here binds the
/// carrier's registers to source values; the post-allocation value flow
/// judges an expansion as its carrier at the carrier's operands), so the
/// trap-guard layer writes no row and the trap-expansion verdict stands.
#[test]
fn a_retargeted_record_and_window_still_hold() {
    for (name, opt, machine, lir) in guard_functions() {
        let window = the_window(&machine);
        let free = unused_gpr(&machine, &window);
        let mut mutated = machine.clone();
        let carrier = carrier_at_mut(&mut mutated, window.first);
        let tested = match carrier.opcode {
            Op::TrapBoundsCheckExact | Op::TrapOverflowExact => 1,
            _ => 0,
        };
        let original = carrier.operands[tested].clone();
        let MachOperand::PReg(p) = original else {
            panic!("{name}: physical register carrier");
        };
        let retarget = if p.encoding() >= 32 {
            MachOperand::PReg(PReg::new(32 + free))
        } else {
            MachOperand::PReg(PReg::new(free))
        };
        carrier.operands[tested] = retarget.clone();
        for &id in &machine.blocks[window.block].insts[window.start..=window.skip] {
            for op in &mut mutated.inst_mut(id).operands {
                if *op == original {
                    *op = retarget.clone();
                }
            }
        }
        let report = verify_enforced(&mutated, &lir);
        assert!(
            window_holds(&mutated, &report, window.first),
            "{name} {opt:?}: {:#?}",
            report.instructions
        );
    }
}

/// A guard on a constant divisor that is nonzero at its width never traps,
/// and instruction selection emits no carrier for it: the accounting exempts
/// exactly that. A constant that is zero at its width (256 as an `I8`,
/// 0x10000 as an `I16`) keeps its window, and the exemption, which reads the
/// constant at its width, does not cover it: with the window and its record
/// deleted the function is refused for the guard.
#[test]
fn a_nonzero_constant_divisor_needs_no_trap_and_a_zero_one_keeps_it() {
    for (fixture, elided) in [
        (
            fixtures::div_zero_by_constant(trust_cg_lower::Type::I64, 7),
            true,
        ),
        (
            fixtures::div_zero_by_constant(trust_cg_lower::Type::I32, 3),
            true,
        ),
        (
            fixtures::div_zero_by_constant(trust_cg_lower::Type::I8, 1),
            true,
        ),
        (
            fixtures::div_zero_by_constant(trust_cg_lower::Type::I8, 256),
            false,
        ),
        (
            fixtures::div_zero_by_constant(trust_cg_lower::Type::I16, 0x1_0000),
            false,
        ),
    ] {
        for opt in fixtures::ALL_LEVELS {
            let machine = fixtures::prepare(&fixture, opt);
            let report = verify_enforced(&machine, &fixture.lir);
            assert!(
                report.precondition_failure.is_none(),
                "{} {opt:?}: {:?}",
                fixture.name,
                report.precondition_failure
            );
            assert_eq!(
                machine.trap_expansions.is_empty(),
                elided,
                "{} {opt:?}",
                fixture.name
            );
            if !elided {
                let (deleted, _) = delete_the_window(&machine);
                let report = verify_enforced(&deleted, &fixture.lir);
                let unaccounted = unaccounted(&report);
                assert!(
                    unaccounted.len() == 1 && unaccounted[0].contains("GuardDivZero"),
                    "{} {opt:?}: {:?}",
                    fixture.name,
                    report.precondition_failure
                );
            }
        }
    }
}

/// Bounds guards on a 32-bit index: each window the pipeline emits holds and
/// binds (`I32` in a W register), the function compiles to an object, and on
/// a Linux AArch64 host the encoded function returns an in-range index and
/// traps (SIGTRAP) on an out-of-range one.
#[test]
fn i32_index_bounds_windows_hold_compile_and_trap() {
    for fixture in fixtures::i32_index_bounds() {
        for opt in fixtures::ALL_LEVELS {
            let machine = fixtures::prepare(&fixture, opt);
            let report = verify_enforced(&machine, &fixture.lir);
            assert!(
                report.precondition_failure.is_none(),
                "{} {opt:?}",
                fixture.name
            );
            assert!(
                window_holds(&machine, &report, the_window(&machine).first),
                "{} {opt:?}: {:#?}",
                fixture.name,
                report.instructions
            );
            let pipeline = trust_cg_codegen::pipeline::Pipeline::new(
                trust_cg_codegen::pipeline::PipelineConfig {
                    opt_level: opt,
                    verify: false,
                    ..trust_cg_codegen::pipeline::PipelineConfig::for_target(fixtures::TRIPLE)
                },
            );
            pipeline
                .compile_function(&fixture.lir)
                .unwrap_or_else(|e| panic!("{} {opt:?}: compile: {e}", fixture.name));
            let code = trust_cg_codegen::pipeline::encode_function(&machine)
                .unwrap_or_else(|e| panic!("{} {opt:?}: encode: {e}", fixture.name));
            native::check(&fixture.name, opt, &code);
            // Control: the same function with its skip condition inverted
            // must behave as the inverted guard, or the native check above
            // could not tell a wrong window from a right one. ENC-5 refuses
            // to encode the inverted window (its per-compile trap-expansion
            // check), so the control flips the condition in the encoded word.
            let mut inverted = machine.clone();
            let skip = the_window(&machine).skip_id(&machine);
            if let MachOperand::Imm(cc) = &mut inverted.inst_mut(skip).operands[0] {
                *cc ^= 1;
            }
            let refusal = trust_cg_codegen::pipeline::encode_function(&inverted)
                .expect_err("ENC-5 refuses an inverted trap expansion");
            assert!(
                refusal.to_string().contains("ENC-5 trap expansion"),
                "{} {opt:?}: {refusal}",
                fixture.name
            );
            native::check_inverted(&fixture.name, opt, &invert_skip_word(&code));
        }
    }
}

/// `code` with the condition of its one `B.cond +2` that precedes `BRK #1`
/// (the window's skip branch) inverted, as encoded words.
fn invert_skip_word(code: &[u8]) -> Vec<u8> {
    const BRK_1: u32 = 0xD420_0020;
    let (chunks, rest) = code.as_chunks::<4>();
    assert!(rest.is_empty(), "AArch64 code is a whole number of words");
    let mut words: Vec<u32> = chunks.iter().map(|w| u32::from_le_bytes(*w)).collect();
    let skips: Vec<usize> = (0..words.len().saturating_sub(1))
        .filter(|&i| words[i] & 0xFFFF_FFF0 == 0x5400_0040 && words[i + 1] == BRK_1)
        .collect();
    assert_eq!(skips.len(), 1, "one B.cond +2 before BRK #1: {words:08x?}");
    words[skips[0]] ^= 1;
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// A guard on a narrow (`I8`/`I16`) value tests the value, not its 32-bit
/// register. `w = x.wrapping_add(1)` leaves 0x100 (0x10000) in the register
/// at `x = MAX` while the narrow value is 0: the division by it must trap, a
/// shift by it or an index of it (constant or dynamic bound) must not, and
/// a dynamic bound of it admits no index. Run natively at O0-O3. The windows
/// hold but stay unbound (a narrow source value), never credited.
#[test]
fn a_narrow_guard_operand_is_tested_at_its_width() {
    use fixtures::WrappedGuard as G;
    use trust_cg_lower::Type as T;
    for (ty, width, max) in [(T::I8, 8u32, 0xffu32), (T::I16, 16, 0xffff)] {
        for guard in [
            G::DivZero,
            G::ShiftRange,
            G::Bounds,
            G::BoundsDynIndex,
            G::BoundsDynLength,
        ] {
            let fixture = fixtures::wrapped_narrow(ty.clone(), guard);
            // (x, y, Some(returned low bits) or None for SIGTRAP), w = x + 1.
            let cases: Vec<(u32, u32, Option<u32>)> = match guard {
                G::DivZero => vec![
                    (6, 100, Some(14)),
                    (max - 1, 100, Some(100 / max)),
                    (max, 100, None),
                ],
                G::ShiftRange => vec![
                    (max, 3, Some(3)),
                    (width - 2, 3, Some(3 << (width - 1))),
                    (width - 1, 3, None),
                ],
                G::Bounds => vec![(max, 0, Some(0)), (8, 0, Some(9)), (9, 0, None)],
                // Index w, length y: a wrapped index 0 is in range.
                G::BoundsDynIndex => vec![
                    (max, 5, Some(0)),
                    (3, 5, Some(4)),
                    (4, 5, None),
                    (max, 0, None),
                ],
                // Index y, length w: a wrapped length 0 admits no index.
                G::BoundsDynLength => vec![
                    (max, 3, None),
                    (max, 0, None),
                    (3, 3, Some(3)),
                    (3, 4, None),
                ],
            };
            for opt in fixtures::ALL_LEVELS {
                let machine = fixtures::prepare(&fixture, opt);
                let report = verify_enforced(&machine, &fixture.lir);
                assert!(
                    report.precondition_failure.is_none(),
                    "{} {opt:?}: {:?}",
                    fixture.name,
                    report.precondition_failure
                );
                assert!(
                    trap_failures(&report).is_empty(),
                    "{} {opt:?}",
                    fixture.name
                );
                let window = the_window(&machine);
                for id in [window.skip_id(&machine), window.brk_id(&machine)] {
                    let reason =
                        refusal_of(row_of(&report, id), &format!("{} {opt:?}", fixture.name));
                    assert!(reason.contains("traps exactly when"), "{reason}");
                    assert!(
                        reason.contains("only I32 in W and I64 in X bind exactly"),
                        "{reason}"
                    );
                }
                let code = trust_cg_codegen::pipeline::encode_function(&machine)
                    .unwrap_or_else(|e| panic!("{} {opt:?}: encode: {e}", fixture.name));
                native::check_wrapped(&fixture.name, opt, &code, width, &cases);
            }
        }
    }
}

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
mod native {
    use trust_cg_codegen::pipeline::OptLevel;

    unsafe extern "C" {
        fn __clear_cache(start: *mut libc::c_char, end: *mut libc::c_char);
    }

    /// How a forked child running the code ended.
    #[derive(Debug, PartialEq, Eq)]
    enum Outcome {
        /// It returned the expected value.
        Returned,
        /// It returned something else.
        Wrong,
        /// It died of this signal.
        Signal(i32),
    }

    /// `code` mapped read+execute in this process.
    struct Code {
        base: *mut libc::c_void,
        len: usize,
    }

    impl Code {
        fn new(bytes: &[u8]) -> Self {
            let len = bytes.len();
            // SAFETY: a fresh private anonymous mapping of `len` bytes is
            // written once, then made read+execute and its caches
            // synchronized before any call; nothing else aliases it.
            unsafe {
                let base = libc::mmap(
                    std::ptr::null_mut(),
                    len,
                    libc::PROT_READ | libc::PROT_WRITE,
                    libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                    -1,
                    0,
                );
                assert_ne!(base, libc::MAP_FAILED, "map {len} bytes");
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), base.cast::<u8>(), len);
                assert_eq!(
                    libc::mprotect(base, len, libc::PROT_READ | libc::PROT_EXEC),
                    0
                );
                __clear_cache(base.cast(), base.cast::<libc::c_char>().add(len));
                Self { base, len }
            }
        }

        /// Call the code as `fn(u32, u32) -> u32` in a forked child (which
        /// disables core dumps first) and report how the child ended.
        fn run(&self, a: u32, b: u32, expected: u32) -> Outcome {
            self.run_masked(a, b, expected, u32::MAX)
        }

        /// [`Self::run`], comparing only the result bits in `mask` (a narrow
        /// result's register bits above its width are unspecified).
        fn run_masked(&self, a: u32, b: u32, expected: u32, mask: u32) -> Outcome {
            // SAFETY: the mapping holds a complete AArch64 function taking at
            // most two 32-bit integer arguments and returning one; the call
            // happens only in the child.
            let function: extern "C" fn(u32, u32) -> u32 =
                unsafe { std::mem::transmute(self.base) };
            // SAFETY: the child calls only `setrlimit`, the mapped function
            // and `_exit`, none of which takes a lock another thread could
            // hold.
            let pid = unsafe { libc::fork() };
            assert!(pid >= 0, "fork");
            if pid == 0 {
                let no_core = libc::rlimit {
                    rlim_cur: 0,
                    rlim_max: 0,
                };
                // SAFETY: plain system calls in the forked child.
                unsafe {
                    libc::setrlimit(libc::RLIMIT_CORE, &no_core);
                    let got = function(a, b);
                    libc::_exit(if got & mask == expected & mask { 0 } else { 1 });
                }
            }
            let mut status = 0;
            // SAFETY: waits for exactly the child forked above.
            assert_eq!(unsafe { libc::waitpid(pid, &mut status, 0) }, pid);
            if libc::WIFSIGNALED(status) {
                Outcome::Signal(libc::WTERMSIG(status))
            } else if libc::WEXITSTATUS(status) == 0 {
                Outcome::Returned
            } else {
                Outcome::Wrong
            }
        }
    }

    impl Drop for Code {
        fn drop(&mut self) {
            // SAFETY: `base..base+len` is the mapping made in `new`.
            unsafe { libc::munmap(self.base, self.len) };
        }
    }

    /// The fixture's bound and the length argument it is called with.
    fn bound_of(name: &str) -> (u32, u32) {
        match name {
            "bounds_const_10_i32" => (10, 0),
            "bounds_const_0x1234_i32" => (0x1234, 0),
            "bounds_const_0x123456_i32" => (0x12_3456, 0),
            "bounds_dyn_i32" => (777, 777),
            other => panic!("no native expectation for {other}"),
        }
    }

    /// The indices each fixture is called with: both sides of the bound, and
    /// the two indices a signed compare would let through (`0x8000_0000` and
    /// `0xffff_ffff` are negative as `i32`).
    fn indices(bound: u32) -> [u32; 5] {
        [0, bound - 1, bound, 0x8000_0000, 0xffff_ffff]
    }

    /// Run the encoded fixture: the index (`v0`) is returned when it is below
    /// the bound (or the length `v1`) and traps otherwise.
    pub fn check(name: &str, opt: OptLevel, bytes: &[u8]) {
        let code = Code::new(bytes);
        let (bound, len) = bound_of(name);
        for index in indices(bound) {
            let outcome = code.run(index, len, index);
            let expected = if index < bound {
                Outcome::Returned
            } else {
                Outcome::Signal(libc::SIGTRAP)
            };
            assert_eq!(outcome, expected, "{name} {opt:?}: index {index:#x}");
        }
        eprintln!("NATIVE {name} {opt:?}: in-range indices returned, out-of-range ones trapped");
    }

    /// The control: with the skip condition inverted, an in-range index
    /// traps and an out-of-range one is returned.
    pub fn check_inverted(name: &str, opt: OptLevel, bytes: &[u8]) {
        let code = Code::new(bytes);
        let (bound, len) = bound_of(name);
        for index in indices(bound) {
            let outcome = code.run(index, len, index);
            let expected = if index < bound {
                Outcome::Signal(libc::SIGTRAP)
            } else {
                Outcome::Returned
            };
            assert_eq!(
                outcome, expected,
                "{name} {opt:?} inverted: index {index:#x}"
            );
        }
        eprintln!("NATIVE-CONTROL {name} {opt:?}: the inverted window behaves inverted");
    }

    /// Run a wrapped-narrow fixture on `(x, y, expected)` cases: `Some(r)`
    /// expects the low `width` bits of the result to be `r`, `None` expects
    /// SIGTRAP.
    pub fn check_wrapped(
        name: &str,
        opt: OptLevel,
        bytes: &[u8],
        width: u32,
        cases: &[(u32, u32, Option<u32>)],
    ) {
        let code = Code::new(bytes);
        let mask = (1u32 << width) - 1;
        for &(x, y, expected) in cases {
            let outcome = code.run_masked(x, y, expected.unwrap_or(0), mask);
            let wanted = match expected {
                Some(_) => Outcome::Returned,
                None => Outcome::Signal(libc::SIGTRAP),
            };
            assert_eq!(outcome, wanted, "{name} {opt:?}: x={x:#x} y={y:#x}");
        }
        eprintln!(
            "NATIVE {name} {opt:?}: every case returned or trapped as the narrow source says"
        );
    }
}

#[cfg(not(all(target_os = "linux", target_arch = "aarch64")))]
mod native {
    pub fn check_wrapped(
        name: &str,
        opt: trust_cg_codegen::pipeline::OptLevel,
        _bytes: &[u8],
        _width: u32,
        _cases: &[(u32, u32, Option<u32>)],
    ) {
        eprintln!("SKIP native run of {name} {opt:?}: needs a Linux AArch64 host");
    }

    pub fn check(name: &str, opt: trust_cg_codegen::pipeline::OptLevel, _bytes: &[u8]) {
        eprintln!("SKIP native run of {name} {opt:?}: needs a Linux AArch64 host");
    }

    pub fn check_inverted(name: &str, opt: trust_cg_codegen::pipeline::OptLevel, _bytes: &[u8]) {
        eprintln!("SKIP native control of {name} {opt:?}: needs a Linux AArch64 host");
    }
}
