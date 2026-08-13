// guard_kernel_gate_pipeline.rs — fail-closed production guard policy in the real pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Public TrustIR annotations and statuses are report-only until an exact trusted replay establishes
//! authority. The historical `TRUST_CG_GUARD_KERNEL_GATE` env flag is also authority-inert.
//!
//! The decisive observable is a bounds-check carrier flowing through the full prepare pipeline. A
//! retained carrier expands to `CMP + B.LO + BRK`. Both `Pending` and public `Discharged` spellings,
//! with the env flag set to either `0` or `1`, must retain that `Brk`.
//!
//! Because the flag is process-global, this is ONE test that toggles it around two serial sub-runs.

use trust_cg_codegen::env_lock;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;

use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

const OBLIGATION_ID: u32 = 11;
const ARRAY_LEN: u64 = 8;

/// Build a module + function: `array[index]` carrying InBounds + ProofRef(OBLIGATION_ID), with a
/// single module obligation of the given status.
fn build(status: ProofStatus) -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_pipeline");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "guarded_extract", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: ValueId::new(0),
                index: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::InBounds)
            .with_proof(ProofAnnotation::ProofRef(ProofId::new(OBLIGATION_ID))),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.proof_obligations.push(ProofObligation::new(
        ProofId::new(OBLIGATION_ID),
        ObligationKind::MemorySafety,
        status,
        "array index is in bounds",
    ));
    module.add_function(func.clone());
    (module, func)
}

fn brk_count(func: &MachFunction) -> usize {
    func.insts
        .iter()
        .filter(|i| i.opcode == AArch64Opcode::Brk)
        .count()
}

/// Prepare `func` through the full pipeline (O2) with public TrustIR metadata threaded through.
#[allow(clippy::result_large_err)] // Test helper intentionally preserves the production error type.
fn try_prepare(
    module: &Module,
    func: &TrustIrFunction,
) -> Result<MachFunction, trust_cg_codegen::pipeline::PipelineError> {
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
}

fn prepare(module: &Module, func: &TrustIrFunction) -> MachFunction {
    try_prepare(module, func).expect("prepare function")
}

// The flag is a process-global env var; keep all scenarios in ONE test so the test runner's thread
// pool cannot interleave a set/remove from a sibling test.
#[test]
fn public_status_and_env_spellings_never_authorize_guard_elimination() {
    // Pending obligation, historical env spelling "0".
    let (module_pending, func_pending) = build(ProofStatus::Pending);
    env_lock::with_env_edits(|env| {
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "0");
        let off = prepare(&module_pending, &func_pending);
        let off_brks = brk_count(&off);
        assert_eq!(
            off_brks, 1,
            "env=0 must not authorize deletion of a guard backed only by public metadata"
        );

        // Pending obligation, historical env spelling "1".
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "1");
        let on = prepare(&module_pending, &func_pending);
        let on_brks = brk_count(&on);
        assert_eq!(
            on_brks, 1,
            "env=1 must not authorize deletion of a guard backed only by public metadata"
        );
        assert_eq!(off_brks, on_brks, "env spellings must be authority-inert");

        // A public Discharged status remains report-only and must produce the same retained guard.
        let (module_discharged, func_discharged) = build(ProofStatus::Discharged);
        let discharged_result = try_prepare(&module_discharged, &func_discharged);
        let discharged = discharged_result.expect("public Discharged fixture must prepare");
        assert_eq!(
            brk_count(&discharged),
            1,
            "public Discharged status must not authorize runtime-guard deletion"
        );
    });
}
