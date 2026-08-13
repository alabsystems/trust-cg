// guard_kernel_gate_divzero_behavior_preservation.rs — report-only DivZero authority regression
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Public `DivNonZero`, public proof statuses, and adapter-synthesized `Discharged` statuses are
//! report-only. They cannot authorize removal of a division-by-zero runtime guard.
//!
//! A `UDiv` carrying `DivNonZero` lowers to a self-contained `TrapDivZeroIfZero`. This test proves
//! that carrier survives under both historical env spellings and with either synthesized status or
//! an explicit pending `ProofRef`.

use trust_cg_codegen::env_lock;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::MachOperand;
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;

use trust_ir::inst::BinOp;
use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

const DIVZERO_OBLIGATION_ID: u32 = 31;

/// Which report-only metadata spelling a fixture uses.
#[derive(Clone, Copy)]
enum ProofMode {
    /// The adapter may synthesize a report-only status from `DivNonZero`.
    ReportOnlyAnnotation,
    /// Public `DivNonZero` plus a public pending `ProofRef`.
    PendingProofRef,
}

/// Build a module + function `udiv_guarded(a, b) -> a / b` whose division carries `DivNonZero`.
fn build(mode: ProofMode) -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_divzero_behavior_preservation");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "udiv_guarded", ft, BlockId::new(0));

    // value ids: 0=a (dividend), 1=b (divisor); 2=a/b
    let mut div = InstrNode::new(Inst::BinOp {
        op: BinOp::UDiv,
        ty: Ty::I64,
        lhs: ValueId::new(0),
        rhs: ValueId::new(1),
    })
    .with_result(ValueId::new(2))
    .with_proof(ProofAnnotation::DivNonZero);

    if let ProofMode::PendingProofRef = mode {
        div = div.with_proof(ProofAnnotation::ProofRef(ProofId::new(
            DIVZERO_OBLIGATION_ID,
        )));
    }

    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            div,
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];

    if let ProofMode::PendingProofRef = mode {
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(DIVZERO_OBLIGATION_ID),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "divisor is non-zero",
        ));
    }

    module.add_function(func.clone());
    (module, func)
}

/// The full opcode+operand stream of the prepared function, in block-layout order.
fn opcode_stream(func: &MachFunction) -> Vec<(AArch64Opcode, Vec<MachOperand>)> {
    let mut stream = Vec::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            stream.push((inst.opcode, inst.operands.clone()));
        }
    }
    stream
}

fn brk_count(stream: &[(AArch64Opcode, Vec<MachOperand>)]) -> usize {
    stream
        .iter()
        .filter(|(op, _)| *op == AArch64Opcode::Brk)
        .count()
}

fn prepare_aarch64(module: &Module, func: &TrustIrFunction) -> MachFunction {
    let (lir_func, proof_ctx) =
        trust_cg_lower::translate_function(func, module).expect("adapter translate");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &lir_func,
            Some(&proof_ctx),
            module,
            func,
        )
        .map(|(prepared, _metrics)| prepared)
        .expect("prepare function")
}

/// The historical env flag is process-global, so both spellings run serially in one test.
#[test]
fn divzero_report_only_metadata_always_keeps_runtime_guard_aarch64() {
    let (module, func) = build(ProofMode::ReportOnlyAnnotation);

    let (off, on, control) = env_lock::with_env_edits(|env| {
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "0");
        let off = opcode_stream(&prepare_aarch64(&module, &func));

        env.set("TRUST_CG_GUARD_KERNEL_GATE", "1");
        let on = opcode_stream(&prepare_aarch64(&module, &func));

        let (ctrl_module, ctrl_func) = build(ProofMode::PendingProofRef);
        let control = opcode_stream(&prepare_aarch64(&ctrl_module, &ctrl_func));
        (off, on, control)
    });

    assert_eq!(
        off, on,
        "historical env spellings must be authority-inert and byte-identical"
    );
    assert_eq!(
        brk_count(&off),
        1,
        "env=0 must retain the report-only DivNonZero guard"
    );
    assert_eq!(
        brk_count(&on),
        1,
        "env=1 must retain the report-only DivNonZero guard"
    );
    assert_eq!(
        control, on,
        "a pending public ProofRef and synthesized report-only status must have the same result"
    );
}
