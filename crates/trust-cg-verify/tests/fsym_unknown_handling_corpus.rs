// Symbolic execution: bounded unknown-handling corpus gate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Bounded fsym unknown-handling evidence for #377.
//!
//! This corpus starts from trust_ir scanner-produced unknown obligations, then runs
//! the bounded local solver escalation path. It covers resolved null,
//! arithmetic, and bounds obligations, plus the scanner-side no-free UAF
//! classification that keeps unrelated handoffs out of solver escalation.

use trust_cg_verify::fsym_summary::{FsymSolverEscalationConfig, FsymSolverStatus, FsymSummary};
use trust_cg_verify::fsym_trust_ir::FsymTrustIrDiagnosticKind;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, FuncTyId, Function, ICmpOp, Inst,
    InstrNode, Module, Ty, ValueId,
};

const EXPECTED_FUNCTIONS: usize = 7;
const EXPECTED_SCANNED: usize = 7;
const EXPECTED_INITIAL_UNKNOWNS: usize = 7;
const EXPECTED_PROVEN_SAFE: usize = 4;
const EXPECTED_CONCRETE_UB: usize = 3;
const EXPECTED_REMAINING_UNKNOWN: usize = 0;

#[derive(Debug, Clone, Copy)]
struct ExpectedStatus {
    function: &'static str,
    kind: FsymTrustIrDiagnosticKind,
    status: FsymSolverStatus,
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn bb(index: u32, body: Vec<InstrNode>) -> Block {
    Block {
        id: BlockId::new(index),
        params: vec![],
        body,
    }
}

fn const_int(result: u32, ty: Ty, value: i128) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty,
        value: Constant::Int(value),
    })
    .with_result(v(result))
}

fn assume(cond: u32) -> InstrNode {
    InstrNode::new(Inst::Assume { cond: v(cond) })
}

fn cast(result: u32, op: CastOp, src_ty: Ty, dst_ty: Ty, operand: u32) -> InstrNode {
    InstrNode::new(Inst::Cast {
        op,
        src_ty,
        dst_ty,
        operand: v(operand),
    })
    .with_result(v(result))
}

fn bin(result: u32, op: BinOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
    InstrNode::new(Inst::BinOp {
        op,
        ty,
        lhs: v(lhs),
        rhs: v(rhs),
    })
    .with_result(v(result))
}

fn icmp(result: u32, op: ICmpOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
    InstrNode::new(Inst::ICmp {
        op,
        ty,
        lhs: v(lhs),
        rhs: v(rhs),
    })
    .with_result(v(result))
}

fn alloca(result: u32, ty: Ty, count: Option<u32>) -> InstrNode {
    InstrNode::new(Inst::Alloca {
        ty,
        count: count.map(v),
        align: None,
    })
    .with_result(v(result))
}

fn gep(result: u32, pointee_ty: Ty, base: u32, index: u32) -> InstrNode {
    InstrNode::new(Inst::GEP {
        pointee_ty,
        base: v(base),
        indices: vec![v(index)],
        inbounds: false,
    })
    .with_result(v(result))
}

fn load(result: u32, ty: Ty, ptr: u32) -> InstrNode {
    InstrNode::new(Inst::Load {
        ty,
        ptr: v(ptr),
        volatile: false,
        align: None,
    })
    .with_result(v(result))
}

fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![v(value)],
    })
}

fn add_function(
    module: &mut Module,
    name: &str,
    params: Vec<(ValueId, Ty)>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
) {
    let func_ty = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(FuncTy {
        params: params.iter().map(|(_, ty)| ty.clone()).collect(),
        returns,
        is_vararg: false,
    });

    let mut function = Function::new(
        FuncId::new(module.functions.len() as u32),
        name,
        func_ty,
        BlockId::new(0),
    );
    function.blocks = vec![bb(0, body)];
    function.blocks[0].params = params;
    module.functions.push(function);
}

fn add_guarded_inttoptr_nonnull_load(module: &mut Module) {
    add_function(
        module,
        "guarded_inttoptr_nonnull_load",
        vec![(v(0), Ty::I8)],
        vec![Ty::I8],
        vec![
            const_int(1, Ty::I8, 0),
            icmp(2, ICmpOp::Ne, Ty::I8, 0, 1),
            assume(2),
            cast(3, CastOp::ZExt, Ty::I8, Ty::I64, 0),
            cast(4, CastOp::IntToPtr, Ty::I64, Ty::Ptr, 3),
            load(5, Ty::I8, 4),
            ret(5),
        ],
    );
}

fn add_guarded_inttoptr_null_load(module: &mut Module) {
    add_function(
        module,
        "guarded_inttoptr_null_load",
        vec![(v(0), Ty::I8)],
        vec![Ty::I8],
        vec![
            const_int(1, Ty::I8, 0),
            icmp(2, ICmpOp::Eq, Ty::I8, 0, 1),
            assume(2),
            cast(3, CastOp::ZExt, Ty::I8, Ty::I64, 0),
            cast(4, CastOp::IntToPtr, Ty::I64, Ty::Ptr, 3),
            load(5, Ty::I8, 4),
            ret(5),
        ],
    );
}

fn add_guarded_nonzero_divisor(module: &mut Module) {
    add_function(
        module,
        "guarded_nonzero_divisor",
        vec![(v(0), Ty::I8)],
        vec![Ty::I8],
        vec![
            const_int(1, Ty::I8, 0),
            icmp(2, ICmpOp::Ne, Ty::I8, 0, 1),
            assume(2),
            const_int(3, Ty::I8, 100),
            bin(4, BinOp::SDiv, Ty::I8, 3, 0),
            ret(4),
        ],
    );
}

fn add_guarded_bounded_add(module: &mut Module) {
    add_function(
        module,
        "guarded_bounded_add",
        vec![(v(0), Ty::I8)],
        vec![Ty::I8],
        vec![
            const_int(1, Ty::I8, 0),
            icmp(2, ICmpOp::Sge, Ty::I8, 0, 1),
            assume(2),
            const_int(3, Ty::I8, 10),
            icmp(4, ICmpOp::Sle, Ty::I8, 0, 3),
            assume(4),
            bin(5, BinOp::Add, Ty::I8, 0, 3),
            ret(5),
        ],
    );
}

fn add_guarded_add_overflow(module: &mut Module) {
    add_function(
        module,
        "guarded_add_overflow",
        vec![(v(0), Ty::I8)],
        vec![Ty::I8],
        vec![
            const_int(1, Ty::I8, 127),
            icmp(2, ICmpOp::Eq, Ty::I8, 0, 1),
            assume(2),
            const_int(3, Ty::I8, 1),
            bin(4, BinOp::Add, Ty::I8, 0, 3),
            ret(4),
        ],
    );
}

fn add_guarded_stack_read_in_bounds(module: &mut Module) {
    add_function(
        module,
        "guarded_stack_read_in_bounds",
        vec![(v(0), Ty::I8)],
        vec![Ty::I8],
        vec![
            const_int(1, Ty::I8, 8),
            alloca(2, Ty::I8, Some(1)),
            const_int(3, Ty::I8, 0),
            icmp(4, ICmpOp::Sge, Ty::I8, 0, 3),
            assume(4),
            const_int(5, Ty::I8, 6),
            icmp(6, ICmpOp::Sle, Ty::I8, 0, 5),
            assume(6),
            gep(7, Ty::I8, 2, 0),
            load(8, Ty::I8, 7),
            ret(8),
        ],
    );
}

fn add_guarded_stack_read_oob(module: &mut Module) {
    add_function(
        module,
        "guarded_stack_read_oob",
        vec![(v(0), Ty::I8)],
        vec![Ty::I8],
        vec![
            const_int(1, Ty::I8, 8),
            alloca(2, Ty::I8, Some(1)),
            icmp(3, ICmpOp::Eq, Ty::I8, 0, 1),
            assume(3),
            gep(4, Ty::I8, 2, 0),
            load(5, Ty::I8, 4),
            ret(5),
        ],
    );
}

fn unknown_handling_corpus() -> Module {
    let mut module = Module::new("fsym_unknown_handling_corpus");

    add_guarded_inttoptr_nonnull_load(&mut module);
    add_guarded_inttoptr_null_load(&mut module);
    add_guarded_nonzero_divisor(&mut module);
    add_guarded_bounded_add(&mut module);
    add_guarded_add_overflow(&mut module);
    add_guarded_stack_read_in_bounds(&mut module);
    add_guarded_stack_read_oob(&mut module);

    module
}

fn expected_statuses() -> [ExpectedStatus; EXPECTED_INITIAL_UNKNOWNS] {
    [
        ExpectedStatus {
            function: "guarded_inttoptr_nonnull_load",
            kind: FsymTrustIrDiagnosticKind::NullDeref,
            status: FsymSolverStatus::ProvenSafe,
        },
        ExpectedStatus {
            function: "guarded_inttoptr_null_load",
            kind: FsymTrustIrDiagnosticKind::NullDeref,
            status: FsymSolverStatus::ConcreteUb,
        },
        ExpectedStatus {
            function: "guarded_nonzero_divisor",
            kind: FsymTrustIrDiagnosticKind::Arithmetic,
            status: FsymSolverStatus::ProvenSafe,
        },
        ExpectedStatus {
            function: "guarded_bounded_add",
            kind: FsymTrustIrDiagnosticKind::Arithmetic,
            status: FsymSolverStatus::ProvenSafe,
        },
        ExpectedStatus {
            function: "guarded_add_overflow",
            kind: FsymTrustIrDiagnosticKind::Arithmetic,
            status: FsymSolverStatus::ConcreteUb,
        },
        ExpectedStatus {
            function: "guarded_stack_read_in_bounds",
            kind: FsymTrustIrDiagnosticKind::OutOfBounds,
            status: FsymSolverStatus::ProvenSafe,
        },
        ExpectedStatus {
            function: "guarded_stack_read_oob",
            kind: FsymTrustIrDiagnosticKind::OutOfBounds,
            status: FsymSolverStatus::ConcreteUb,
        },
    ]
}

#[test]
fn fsym_local_solver_resolves_scanner_unknown_obligations() {
    let module = unknown_handling_corpus();
    let summary = FsymSummary::scan_trust_ir_module(&module);
    let before = summary.counters();

    println!(
        "fsym unknown corpus before solver: functions={} scanned={} skipped={} unknown={} concrete_ub={}",
        module.functions.len(),
        before.scanned,
        before.skipped,
        before.unknown,
        before.concrete_ub
    );
    for function in &summary.functions {
        for unknown in &function.unknown_obligations {
            println!(
                "scanner unknown function={} kind={:?} reason={}",
                unknown.function, unknown.kind, unknown.reason
            );
        }
    }

    assert_eq!(module.functions.len(), EXPECTED_FUNCTIONS);
    assert_eq!(before.scanned, EXPECTED_SCANNED);
    assert_eq!(before.skipped, 0);
    assert_eq!(before.unknown, EXPECTED_INITIAL_UNKNOWNS);
    assert_eq!(before.concrete_ub, 0);

    for function in &summary.functions {
        assert!(
            !function.unknown_obligations.is_empty(),
            "expected scanner unknown for {}",
            function.function
        );
        for unknown in &function.unknown_obligations {
            assert!(
                unknown.candidate_expression.is_some(),
                "missing candidate text for {}",
                unknown.function
            );
            assert!(
                unknown.kind != FsymTrustIrDiagnosticKind::UseAfterFree,
                "no-free UAF handoff should be classified safe before solver escalation"
            );
            assert!(
                unknown.solver_candidate.is_some(),
                "missing typed solver candidate for {}",
                unknown.function
            );
        }
    }

    let solver_report =
        summary.escalate_unknown_obligations_locally(&FsymSolverEscalationConfig::enabled());
    let after = summary.counters_after_solver_escalation(&solver_report);

    println!(
        "fsym unknown corpus after solver: results={} proven_safe={} concrete_ub={} remaining_unknown={}",
        solver_report.results.len(),
        solver_report.proven_safe_count(),
        solver_report.concrete_ub_count(),
        solver_report.remaining_unknown_count()
    );
    for result in &solver_report.results {
        println!(
            "solver function={} kind={:?} status={} detail={} witness={:?}",
            result.function,
            result.kind,
            result.status.as_str(),
            result.detail,
            result.witness
        );
    }

    assert!(solver_report.enabled);
    assert_eq!(solver_report.results.len(), EXPECTED_INITIAL_UNKNOWNS);
    assert_eq!(solver_report.proven_safe_count(), EXPECTED_PROVEN_SAFE);
    assert_eq!(solver_report.concrete_ub_count(), EXPECTED_CONCRETE_UB);
    assert_eq!(
        solver_report.remaining_unknown_count(),
        EXPECTED_REMAINING_UNKNOWN
    );
    assert_eq!(after.unknown, EXPECTED_REMAINING_UNKNOWN);
    assert_eq!(after.concrete_ub, EXPECTED_CONCRETE_UB);

    for expected in expected_statuses() {
        let result = solver_report
            .results
            .iter()
            .find(|result| result.function == expected.function && result.kind == expected.kind)
            .unwrap_or_else(|| panic!("missing expected solver result: {expected:?}"));
        assert_eq!(
            result.status, expected.status,
            "unexpected solver status for {}",
            expected.function
        );
        if expected.status == FsymSolverStatus::ConcreteUb {
            assert!(
                !result.witness.is_empty(),
                "expected concrete witness for {}",
                expected.function
            );
        }
    }
}
