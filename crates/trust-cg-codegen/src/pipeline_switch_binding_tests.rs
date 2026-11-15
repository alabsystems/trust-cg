// trust-cg-codegen/pipeline_switch_binding_tests.rs - the per-compile switch
// dispatch binding is wired into every AArch64 encode route
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Every AArch64 encode route funnels through
//! `encode_function_with_fixups_and_blocks_impl_with_sites`, which binds each
//! switch dispatch to the final bytes after the layout cross-check
//! (`trust_cg_verify::aarch64_switch_binding`, `[TCG-A64-SWITCH-BIND]`). A
//! bounds compare that covers one index past a two-entry table is consistent
//! between intent and word, so the encoder and the layout cross-check accept
//! it; only the binding can refuse it. Each public or policy-aware route is
//! driven with that function and must fail with
//! [`PipelineError::Aarch64SwitchBinding`], and with the correct bound must
//! encode. Removing the hook turns these refusals into encodes.

use super::*;
use trust_cg_ir::function::{JumpTableData, Signature, Type};
use trust_cg_ir::regs::{X0, X16, X17, X30};
use trust_cg_verify::aarch64_switch_binding::SwitchBindingError;

fn add(func: &mut IrMachFunction, block: BlockId, inst: IrMachInst) {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
}

fn preg(reg: trust_cg_ir::regs::PReg) -> IrOperand {
    IrOperand::PReg(reg)
}

/// entry: `CMP x0, #bound; B.HI default; ADR x16, table; LDRSW x17, [x16,
/// x0, LSL #2]; ADD x16, x16, x17; BR x16`; two table arms and a default,
/// each `MOVZ x0, #k; RET`. The table is `[arm0, arm1]` with `min_val` 0, so
/// the correct bound is 1.
fn dispatch(bound: i64) -> IrMachFunction {
    let mut f = IrMachFunction::new(
        "switch_bind_wiring".into(),
        Signature::new(vec![Type::I64], vec![Type::I64]),
    );
    let entry = f.entry;
    let arm0 = f.create_block();
    let arm1 = f.create_block();
    let default = f.create_block();
    f.jump_tables.push(JumpTableData {
        min_val: 0,
        targets: vec![arm0, arm1],
    });
    for inst in [
        IrMachInst::new(IrOpcode::CmpRI, vec![preg(X0), IrOperand::Imm(bound)]),
        IrMachInst::new(
            IrOpcode::BCond,
            vec![IrOperand::Imm(0b1000), IrOperand::Block(default)],
        ),
        IrMachInst::new(IrOpcode::Adr, vec![preg(X16), IrOperand::JumpTableIndex(0)]),
        IrMachInst::new(IrOpcode::LdrswRO, vec![preg(X17), preg(X16), preg(X0)]),
        IrMachInst::new(IrOpcode::AddRR, vec![preg(X16), preg(X16), preg(X17)]),
        IrMachInst::new(IrOpcode::Br, vec![preg(X16)]),
    ] {
        add(&mut f, entry, inst);
    }
    for (block, value) in [(arm0, 10), (arm1, 11), (default, 99)] {
        add(
            &mut f,
            block,
            IrMachInst::new(IrOpcode::Movz, vec![preg(X0), IrOperand::Imm(value)]),
        );
        add(
            &mut f,
            block,
            IrMachInst::new(IrOpcode::Ret, vec![preg(X30)]).with_implicit_uses(&[X0]),
        );
        f.add_edge(entry, block);
    }
    resolve_branches(&mut f).expect("the fixture's branches resolve");
    f
}

fn refused_by_binding<T>(result: Result<&T, &PipelineError>) -> bool {
    matches!(
        result,
        Err(PipelineError::Aarch64SwitchBinding {
            function,
            error: SwitchBindingError::Bounds { table: 0, .. },
        }) if function == "switch_bind_wiring"
    )
}

#[test]
fn every_encode_route_binds_a_correct_dispatch_and_refuses_a_bound_past_the_table() {
    let good = dispatch(1);
    let bad = dispatch(2);

    encode_function(&good).expect("encode_function binds the correct bound");
    encode_function_with_fixups(&good).expect("encode_function_with_fixups binds");
    encode_function_with_fixups_and_blocks(&good)
        .expect("encode_function_with_fixups_and_blocks binds");
    let result = encode_function(&bad);
    assert!(
        refused_by_binding(result.as_ref()),
        "encode_function: {result:?}"
    );
    let result = encode_function_with_fixups(&bad);
    assert!(
        refused_by_binding(result.as_ref()),
        "encode_function_with_fixups: {result:?}"
    );
    let result = encode_function_with_fixups_and_blocks(&bad);
    assert!(
        refused_by_binding(result.as_ref()),
        "encode_function_with_fixups_and_blocks: {result:?}"
    );

    for pipeline in [
        Pipeline::new(PipelineConfig::for_host_aarch64()),
        Pipeline::new(PipelineConfig::for_host_aarch64()).with_proof_grade_aarch64_publication(),
    ] {
        encode_function_with_fixups_for_pipeline(&pipeline, &good)
            .expect("the policy-aware route binds the correct bound");
        encode_function_with_fixups_and_blocks_for_pipeline(&pipeline, &good)
            .expect("the policy-aware block route binds the correct bound");
        let result = encode_function_with_fixups_for_pipeline(&pipeline, &bad);
        assert!(
            refused_by_binding(result.as_ref()),
            "encode_function_with_fixups_for_pipeline: {result:?}"
        );
        let result = encode_function_with_fixups_and_blocks_for_pipeline(&pipeline, &bad);
        assert!(
            refused_by_binding(result.as_ref()),
            "encode_function_with_fixups_and_blocks_for_pipeline: {result:?}"
        );
    }
}
