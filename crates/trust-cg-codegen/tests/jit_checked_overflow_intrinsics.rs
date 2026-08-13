// jit_checked_overflow_intrinsics.rs
//
// Runtime regression coverage for trust_ir Inst::Overflow -> CheckedS*/CheckedU* lowering.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::AArch64CC;
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, OverflowOp, ProofAnnotation, Ty, ValueId,
};

type CheckedOverflowFn = unsafe extern "C" fn(i64, i64, *mut i64, *mut i64) -> i64;
type CheckedUnsignedOverflowFn = unsafe extern "C" fn(u64, u64, *mut u64, *mut u64) -> u64;

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn f(n: u32) -> FuncId {
    FuncId::new(n)
}

fn build_checked_overflow_module(name: &str, op: OverflowOp, ty: Ty) -> TrustIrModule {
    build_checked_overflow_module_with_proof(name, op, ty, None)
}

fn build_checked_overflow_module_with_proof(
    name: &str,
    op: OverflowOp,
    ty: Ty,
    proof: Option<ProofAnnotation>,
) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let func_ty_id = module.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone(), Ty::Ptr, Ty::Ptr],
        returns: vec![ty.clone()],
        is_vararg: false,
    });

    let entry = b(0);
    let mut func = TrustIrFunction::new(f(0), name, func_ty_id, entry);
    let overflow = InstrNode::new(Inst::Overflow {
        op,
        ty: ty.clone(),
        lhs: v(0),
        rhs: v(1),
    })
    .with_result(v(4))
    .with_result(v(5));
    let overflow = if let Some(proof) = proof {
        overflow.with_proof(proof)
    } else {
        overflow
    };

    func.blocks = vec![TrustIrBlock {
        id: entry,
        params: vec![
            (v(0), ty.clone()),
            (v(1), ty.clone()),
            (v(2), Ty::Ptr),
            (v(3), Ty::Ptr),
        ],
        body: vec![
            overflow,
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Int(1),
            })
            .with_result(v(6)),
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Int(0),
            })
            .with_result(v(7)),
            InstrNode::new(Inst::Select {
                ty: ty.clone(),
                cond: v(5),
                then_val: v(6),
                else_val: v(7),
            })
            .with_result(v(8)),
            InstrNode::new(Inst::Store {
                ty: ty.clone(),
                ptr: v(2),
                value: v(4),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Store {
                ty,
                ptr: v(3),
                value: v(8),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![v(7)] }),
        ],
    }];
    module.add_function(func);
    module
}

fn all_opcodes(func: &MachFunction) -> Vec<AArch64Opcode> {
    func.blocks
        .iter()
        .flat_map(|block| block.insts.iter())
        .map(|id| func.insts[id.0 as usize].opcode)
        .collect()
}

fn all_insts(func: &MachFunction) -> Vec<MachInst> {
    func.blocks
        .iter()
        .flat_map(|block| block.insts.iter())
        .map(|id| func.insts[id.0 as usize].clone())
        .collect()
}

fn has_cset_condition(inst: &MachInst, cc: AArch64CC) -> bool {
    inst.opcode == AArch64Opcode::CSet
        && matches!(
            inst.operands.get(1),
            Some(MachOperand::Imm(raw_cc)) if *raw_cc == i64::from(cc.encoding())
        )
}

/// A materialized consumer of the given condition: either `CSET cc` (the
/// direct isel shape) or `CSEL ..., cc` (the select-fuse pass retargets
/// `CSET cc; CMP bool, #0; CSEL ..., NE` into one `CSEL ..., cc`, which is
/// bit-for-bit the same boolean when the arms are 1/0).
fn is_flag_consumer_with_condition(inst: &MachInst, cc: AArch64CC) -> bool {
    if has_cset_condition(inst, cc) {
        return true;
    }
    inst.opcode == AArch64Opcode::Csel
        && matches!(
            inst.operands.get(3),
            Some(MachOperand::Imm(raw_cc)) if *raw_cc == i64::from(cc.encoding())
        )
}

/// NZCV writers for the adjacency check (the arith op's flags must reach
/// the consumer un-clobbered).
fn writes_nzcv(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::CmpRR
            | AArch64Opcode::CmpRI
            | AArch64Opcode::CMPWrr
            | AArch64Opcode::CMPXrr
            | AArch64Opcode::CMPWri
            | AArch64Opcode::CMPXri
            | AArch64Opcode::Tst
            | AArch64Opcode::Fcmp
            | AArch64Opcode::AddsRR
            | AArch64Opcode::AddsRI
            | AArch64Opcode::SubsRR
            | AArch64Opcode::SubsRI
    )
}

/// The flag-setting arith op must reach a `cc` consumer (CSET or fused
/// CSEL) with no intervening NZCV writer — the load-bearing soundness
/// property behind the original strict-adjacency pin.
fn has_adjacent_cset_condition(
    insts: &[MachInst],
    arith_opcode: AArch64Opcode,
    cc: AArch64CC,
) -> bool {
    for (idx, inst) in insts.iter().enumerate() {
        if inst.opcode != arith_opcode {
            continue;
        }
        for later in &insts[idx + 1..] {
            if is_flag_consumer_with_condition(later, cc) {
                return true;
            }
            if writes_nzcv(later.opcode) {
                break;
            }
        }
    }
    false
}

fn prepare_checked_overflow_module(
    module: &TrustIrModule,
) -> (Vec<AArch64Opcode>, Vec<MachInst>, MachFunction) {
    let lowered =
        trust_cg_lower::translate_module(module).expect("checked-overflow trust_ir lowers");
    assert_eq!(lowered.len(), 1, "expected one lowered function");

    let pipeline_config = PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    let mach = pipeline
        .prepare_function_with_proofs(&lowered[0].0, Some(&lowered[0].1))
        .expect("checked-overflow function prepares");
    let opcodes = all_opcodes(&mach);
    let insts = all_insts(&mach);

    (opcodes, insts, mach)
}

fn compile_checked_overflow_as<F: Copy>(
    name: &str,
    op: OverflowOp,
    ty: Ty,
) -> (
    trust_cg_codegen::ExecutableBuffer,
    F,
    Vec<AArch64Opcode>,
    Vec<MachInst>,
) {
    let module = build_checked_overflow_module(name, op, ty);
    let (opcodes, insts, mach) = prepare_checked_overflow_module(&module);

    let jit = JitCompiler::new(JitConfig {
        opt_level: OptLevel::O2,
        ..JitConfig::default()
    });
    let buffer = jit
        .compile_raw(&[mach], &HashMap::new())
        .expect("checked-overflow raw JIT compile succeeds");
    let f = unsafe {
        buffer
            .get_fn_bound::<F>(name)
            .expect("checked-overflow symbol exists")
    }
    .into_inner();

    (buffer, f, opcodes, insts)
}

fn compile_checked_overflow(
    name: &str,
    op: OverflowOp,
) -> (
    trust_cg_codegen::ExecutableBuffer,
    CheckedOverflowFn,
    Vec<AArch64Opcode>,
    Vec<MachInst>,
) {
    compile_checked_overflow_as(name, op, Ty::I64)
}

fn compile_checked_unsigned_overflow(
    name: &str,
    op: OverflowOp,
) -> (
    trust_cg_codegen::ExecutableBuffer,
    CheckedUnsignedOverflowFn,
    Vec<AArch64Opcode>,
    Vec<MachInst>,
) {
    compile_checked_overflow_as(name, op, Ty::U64)
}

fn run_case(f: CheckedOverflowFn, lhs: i64, rhs: i64, expected_value: i64, expected_flag: i64) {
    let mut value = i64::MIN;
    let mut flag = i64::MIN;
    let ret = unsafe { f(lhs, rhs, &mut value, &mut flag) };

    assert_eq!(ret, 0, "checked-overflow helper should return 0");
    assert_eq!(
        value, expected_value,
        "wrong wrapped value for lhs={lhs}, rhs={rhs}"
    );
    assert_eq!(
        flag, expected_flag,
        "wrong overflow flag for lhs={lhs}, rhs={rhs}"
    );
}

fn run_unsigned_case(
    f: CheckedUnsignedOverflowFn,
    lhs: u64,
    rhs: u64,
    expected_value: u64,
    expected_flag: u64,
) {
    let mut value = u64::MAX;
    let mut flag = u64::MAX;
    let ret = unsafe { f(lhs, rhs, &mut value, &mut flag) };

    assert_eq!(ret, 0, "checked-overflow helper should return 0");
    assert_eq!(
        value, expected_value,
        "wrong wrapped value for lhs={lhs}, rhs={rhs}"
    );
    assert_eq!(
        flag, expected_flag,
        "wrong overflow flag for lhs={lhs}, rhs={rhs}"
    );
}

#[test]
fn no_overflow_proof_does_not_rewrite_flag_setter_before_cset() {
    let module = build_checked_overflow_module_with_proof(
        "checked_sadd_i64_no_overflow_proof_shape",
        OverflowOp::AddOverflow,
        Ty::I64,
        Some(ProofAnnotation::NoOverflow),
    );
    let (opcodes, insts, _) = prepare_checked_overflow_module(&module);

    assert!(
        opcodes.contains(&AArch64Opcode::AddsRR),
        "NoOverflow proof must not erase ADDS while the overflow flag is materialized; opcodes={opcodes:?}"
    );
    assert!(
        has_adjacent_cset_condition(&insts, AArch64Opcode::AddsRR, AArch64CC::VS),
        "checked signed add should keep ADDS adjacent to CSET VS; insts={insts:?}"
    );
    assert!(
        !insts.windows(2).any(|pair| {
            pair[0].opcode == AArch64Opcode::AddRR && has_cset_condition(&pair[1], AArch64CC::VS)
        }),
        "proof opts must not rewrite ADDS to ADD while CSET still consumes V"
    );
}

#[test]
fn checked_signed_overflow_intrinsics_return_wrapped_value_and_flag() {
    let (_add_buffer, checked_add, add_opcodes, _add_insts) =
        compile_checked_overflow("checked_sadd_i64_runtime", OverflowOp::AddOverflow);
    assert!(
        add_opcodes.contains(&AArch64Opcode::AddsRR),
        "CheckedSadd must lower through ADDS; opcodes={add_opcodes:?}"
    );
    assert!(
        _add_insts
            .iter()
            .any(|inst| is_flag_consumer_with_condition(inst, AArch64CC::VS)),
        "CheckedSadd must materialize the overflow flag (CSET VS or fused CSEL VS); opcodes={add_opcodes:?}"
    );
    run_case(checked_add, i64::MAX, 1, i64::MIN, 1);
    run_case(checked_add, 40, 2, 42, 0);

    let (_sub_buffer, checked_sub, sub_opcodes, _sub_insts) =
        compile_checked_overflow("checked_ssub_i64_runtime", OverflowOp::SubOverflow);
    assert!(
        sub_opcodes.contains(&AArch64Opcode::SubsRR),
        "CheckedSsub must lower through SUBS; opcodes={sub_opcodes:?}"
    );
    assert!(
        _sub_insts
            .iter()
            .any(|inst| is_flag_consumer_with_condition(inst, AArch64CC::VS)),
        "CheckedSsub must materialize the overflow flag (CSET VS or fused CSEL VS); opcodes={sub_opcodes:?}"
    );
    run_case(checked_sub, i64::MIN, 1, i64::MAX, 1);
    run_case(checked_sub, 40, 2, 38, 0);

    let (_mul_buffer, checked_mul, mul_opcodes, _mul_insts) =
        compile_checked_overflow("checked_smul_i64_runtime", OverflowOp::MulOverflow);
    assert!(
        mul_opcodes.contains(&AArch64Opcode::MulRR),
        "CheckedSmul must lower through MUL; opcodes={mul_opcodes:?}"
    );
    assert!(
        mul_opcodes.contains(&AArch64Opcode::Smulh),
        "CheckedSmul must lower through SMULH; opcodes={mul_opcodes:?}"
    );
    assert!(
        _mul_insts
            .iter()
            .any(|inst| is_flag_consumer_with_condition(inst, AArch64CC::NE)),
        "CheckedSmul must materialize the overflow flag (CSET NE or fused CSEL NE); opcodes={mul_opcodes:?}"
    );
    run_case(checked_mul, i64::MAX, 2, -2, 1);
    run_case(checked_mul, i64::MIN, -1, i64::MIN, 1);
    run_case(checked_mul, 21, 2, 42, 0);
}

#[test]
fn checked_unsigned_overflow_intrinsics_return_wrapped_value_and_flag() {
    let (_add_buffer, checked_add, add_opcodes, add_insts) =
        compile_checked_unsigned_overflow("checked_uadd_u64_runtime", OverflowOp::AddOverflow);
    assert!(
        add_opcodes.contains(&AArch64Opcode::AddsRR),
        "CheckedUadd must lower through ADDS; opcodes={add_opcodes:?}"
    );
    assert!(
        has_adjacent_cset_condition(&add_insts, AArch64Opcode::AddsRR, AArch64CC::HS),
        "CheckedUadd must materialize the unsigned carry flag with CSET HS; insts={add_insts:#?}"
    );
    run_unsigned_case(checked_add, u64::MAX, 1, 0, 1);
    run_unsigned_case(checked_add, 40, 2, 42, 0);

    let (_sub_buffer, checked_sub, sub_opcodes, sub_insts) =
        compile_checked_unsigned_overflow("checked_usub_u64_runtime", OverflowOp::SubOverflow);
    assert!(
        sub_opcodes.contains(&AArch64Opcode::SubsRR),
        "CheckedUsub must lower through SUBS; opcodes={sub_opcodes:?}"
    );
    assert!(
        has_adjacent_cset_condition(&sub_insts, AArch64Opcode::SubsRR, AArch64CC::LO),
        "CheckedUsub must materialize the unsigned borrow flag with CSET LO; insts={sub_insts:#?}"
    );
    run_unsigned_case(checked_sub, 0, 1, u64::MAX, 1);
    run_unsigned_case(checked_sub, 40, 2, 38, 0);

    let (_mul_buffer, checked_mul, mul_opcodes, mul_insts) =
        compile_checked_unsigned_overflow("checked_umul_u64_runtime", OverflowOp::MulOverflow);
    assert!(
        mul_opcodes.contains(&AArch64Opcode::MulRR),
        "CheckedUmul must lower through MUL; opcodes={mul_opcodes:?}"
    );
    assert!(
        mul_opcodes.contains(&AArch64Opcode::Umulh),
        "CheckedUmul must lower through UMULH; opcodes={mul_opcodes:?}"
    );
    assert!(
        !mul_opcodes.contains(&AArch64Opcode::Smulh),
        "CheckedUmul must not use signed SMULH; opcodes={mul_opcodes:?}"
    );
    assert!(
        mul_insts
            .iter()
            .any(|inst| inst.opcode == AArch64Opcode::CmpRI
                && matches!(inst.operands.get(1), Some(MachOperand::Imm(0)))),
        "CheckedUmul must compare the high half against zero; insts={mul_insts:#?}"
    );
    let umulh_idx = mul_insts
        .iter()
        .position(|inst| inst.opcode == AArch64Opcode::Umulh)
        .expect("CheckedUmul must emit UMULH");
    let cmp_idx = mul_insts
        .iter()
        .position(|inst| {
            inst.opcode == AArch64Opcode::CmpRI
                && matches!(inst.operands.get(1), Some(MachOperand::Imm(0)))
        })
        .expect("CheckedUmul must compare UMULH high half against zero");
    let cset_idx = mul_insts
        .iter()
        .position(|inst| is_flag_consumer_with_condition(inst, AArch64CC::NE))
        .expect("CheckedUmul must materialize overflow with CSET NE (or fused CSEL NE)");
    assert!(umulh_idx < cmp_idx, "UMULH must precede CMP #0");
    assert!(cmp_idx < cset_idx, "CMP #0 must precede CSET NE");
    run_unsigned_case(checked_mul, u64::MAX, 2, u64::MAX.wrapping_mul(2), 1);
    run_unsigned_case(checked_mul, 21, 2, 42, 0);
}
