// trust_ir_integration.rs - End-to-end trust_ir -> adapter -> ISel integration tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_ir::function::{StackSlotAllocationKind, StackSlotSizeSource};
use trust_cg_ir::regs::RegClass;
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::adapter::{
    AdapterError, ProofContext, translate_function, translate_module, translate_type,
};
use trust_cg_lower::bitfield_dialect;
use trust_cg_lower::function::Function;
use trust_cg_lower::instructions::{AtomicOrdering, Block, Instruction, IntCC, Opcode};
use trust_cg_lower::isel::{
    AArch64CC, AArch64Opcode, ISelFunction, ISelOperand, InstructionSelector,
};
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelOperand, X86InstructionSelector};

use trust_ir::dialect::vector as vector_dialect;
use trust_ir::{
    AtomicRMWOp, BinOp, Block as TrustIrBlock, BlockId, CastOp, ClosureTyId, Constant, FieldDef,
    FuncId, FuncTy, FuncTyId, Function as TrustIrFunction, ICmpOp, Inst, InstrNode,
    Module as TrustIrModule, Ordering, OverflowOp, ProofAnnotation, RecordDef, RecordId, SetRepr,
    SwitchCase, Ty, TyId, UnOp, ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn f(n: u32) -> FuncId {
    FuncId::new(n)
}

fn func_ty(params: Vec<Ty>, returns: Vec<Ty>) -> FuncTy {
    FuncTy {
        params,
        returns,
        is_vararg: false,
    }
}

fn single_function_module(
    func_id: u32,
    func_name: &str,
    ty: FuncTy,
    blocks: Vec<TrustIrBlock>,
    proofs: Vec<ProofAnnotation>,
) -> TrustIrModule {
    let entry = blocks.first().expect("module must have a block").id;
    let mut module = TrustIrModule::new(func_name);
    let func_ty_id: FuncTyId = module.add_func_type(ty);

    let mut func = TrustIrFunction::new(f(func_id), func_name, func_ty_id, entry);
    func.blocks = blocks;
    func.proofs = proofs;

    module.add_function(func);
    module
}

fn single_function(module: &TrustIrModule) -> &TrustIrFunction {
    module
        .functions
        .first()
        .expect("expected a single-function module")
}

fn atomic_rmw_module(name: &str, op: AtomicRMWOp, ty: Ty) -> TrustIrModule {
    single_function_module(
        0,
        name,
        func_ty(vec![Ty::Ptr, ty.clone()], vec![ty.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), ty.clone())],
            body: vec![
                InstrNode::new(Inst::AtomicRMW {
                    op,
                    ty,
                    ptr: v(0),
                    value: v(1),
                    ordering: Ordering::SeqCst,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

// ---------------------------------------------------------------------------
// Helper: run a trust_ir function through adapter + ISel
// ---------------------------------------------------------------------------

fn compile_trust_ir_function(module: &TrustIrModule) -> ISelFunction {
    try_compile_trust_ir_function(module).expect("AArch64 lowering failed")
}

fn try_compile_trust_ir_function(module: &TrustIrModule) -> Result<ISelFunction, String> {
    let func = single_function(module);

    let (lir_func, _proof_ctx) = translate_function(func, module)
        .map_err(|err| format!("adapter translation failed: {err}"))?;

    let mut isel = InstructionSelector::new(lir_func.name.clone(), lir_func.signature.clone());

    // Seed Value->Type hints (Call/CallIndirect result types, #381).
    isel.seed_value_types(&lir_func.value_types);

    isel.lower_formal_arguments(&lir_func.signature, lir_func.entry_block)
        .map_err(|err| format!("AArch64 formal argument lowering failed: {err}"))?;

    let mut block_order: Vec<Block> = lir_func.blocks.keys().copied().collect();
    block_order.sort_by_key(|b| {
        if *b == lir_func.entry_block {
            0
        } else {
            b.0 + 1
        }
    });

    for block_id in &block_order {
        let bb = &lir_func.blocks[block_id];
        isel.select_block_with_source_locs(*block_id, &bb.instructions, &bb.source_locs)
            .map_err(|err| format!("AArch64 instruction selection failed: {err}"))?;
    }

    Ok(isel.finalize())
}

fn compile_trust_ir_function_x86_64(module: &TrustIrModule) -> X86ISelFunction {
    try_compile_trust_ir_function_x86_64(module).expect("x86-64 lowering failed")
}

fn try_compile_trust_ir_function_x86_64(module: &TrustIrModule) -> Result<X86ISelFunction, String> {
    let func = single_function(module);

    let (lir_func, _proof_ctx) = translate_function(func, module)
        .map_err(|err| format!("adapter translation failed: {err}"))?;

    let mut isel = X86InstructionSelector::new(lir_func.name.clone(), lir_func.signature.clone());
    isel.seed_value_types(&lir_func.value_types);
    isel.seed_function_value_use_counts(&lir_func);
    isel.lower_formal_arguments(&lir_func.signature, lir_func.entry_block)
        .map_err(|err| format!("x86-64 formal argument lowering failed: {err}"))?;

    let mut block_order: Vec<Block> = lir_func.blocks.keys().copied().collect();
    block_order.sort_by_key(|b| {
        if *b == lir_func.entry_block {
            0
        } else {
            b.0 + 1
        }
    });

    for block_id in &block_order {
        let bb = &lir_func.blocks[block_id];
        isel.select_block(*block_id, &bb.instructions)
            .map_err(|err| format!("x86-64 instruction selection failed: {err}"))?;
    }

    Ok(isel.finalize())
}

fn translate_only(module: &TrustIrModule) -> Result<(Function, ProofContext), AdapterError> {
    translate_function(single_function(module), module)
}

fn count_opcode(mfunc: &ISelFunction, opcode: AArch64Opcode) -> usize {
    mfunc
        .blocks
        .values()
        .flat_map(|b| &b.insts)
        .filter(|inst| inst.opcode == opcode)
        .count()
}

fn has_opcode(mfunc: &ISelFunction, opcode: AArch64Opcode) -> bool {
    count_opcode(mfunc, opcode) > 0
}

fn count_x86_opcode(mfunc: &X86ISelFunction, opcode: X86Opcode) -> usize {
    mfunc
        .blocks
        .values()
        .flat_map(|b| &b.insts)
        .filter(|inst| inst.opcode == opcode)
        .count()
}

fn x86_opcode_imms(mfunc: &X86ISelFunction, opcode: X86Opcode) -> Vec<i64> {
    mfunc
        .blocks
        .values()
        .flat_map(|b| &b.insts)
        .filter(|inst| inst.opcode == opcode)
        .flat_map(|inst| inst.operands.iter())
        .filter_map(|operand| match operand {
            X86ISelOperand::Imm(imm) => Some(*imm),
            _ => None,
        })
        .collect()
}

fn has_x86_opcode(mfunc: &X86ISelFunction, opcode: X86Opcode) -> bool {
    count_x86_opcode(mfunc, opcode) > 0
}

#[test]
fn test_atomic_rmw_min_max_adapter_and_targets() {
    for (op, lir_op, aarch64_opcode, x86_kind) in [
        (
            AtomicRMWOp::Max,
            trust_cg_lower::instructions::AtomicRmwOp::Max,
            AArch64Opcode::Ldsmaxal,
            6,
        ),
        (
            AtomicRMWOp::Min,
            trust_cg_lower::instructions::AtomicRmwOp::Min,
            AArch64Opcode::Ldsminal,
            7,
        ),
        (
            AtomicRMWOp::UMax,
            trust_cg_lower::instructions::AtomicRmwOp::UMax,
            AArch64Opcode::Ldumaxal,
            8,
        ),
        (
            AtomicRMWOp::UMin,
            trust_cg_lower::instructions::AtomicRmwOp::UMin,
            AArch64Opcode::Lduminal,
            9,
        ),
    ] {
        let module = atomic_rmw_module("atomic_rmw_min_max", op, Ty::I64);
        let (lir, _) = translate_only(&module).unwrap();
        assert!(matches!(
            &lir.blocks[&lir.entry_block].instructions[0].opcode,
            Opcode::AtomicRmw { op, .. } if *op == lir_op
        ));

        let aarch64 = compile_trust_ir_function(&module);
        assert!(has_opcode(&aarch64, aarch64_opcode));

        let x86 = compile_trust_ir_function_x86_64(&module);
        assert!(has_x86_opcode(&x86, X86Opcode::AtomicRmwCasLoop));
        assert!(x86_opcode_imms(&x86, X86Opcode::AtomicRmwCasLoop).contains(&x86_kind));
    }
}

fn aarch64_has_call_to(mfunc: &ISelFunction, callee: &str) -> bool {
    mfunc.blocks.values().flat_map(|b| &b.insts).any(|inst| {
        inst.opcode == AArch64Opcode::Bl
            && inst
                .operands
                .iter()
                .any(|op| matches!(op, ISelOperand::Symbol(name) if name == callee))
    })
}

fn x86_64_has_call_to(mfunc: &X86ISelFunction, callee: &str) -> bool {
    mfunc.blocks.values().flat_map(|b| &b.insts).any(|inst| {
        inst.opcode == X86Opcode::Call
            && inst
                .operands
                .iter()
                .any(|op| matches!(op, X86ISelOperand::Symbol(name) if name == callee))
    })
}

fn assert_no_x86_scalarized_vector_cmp_path(mfunc: &X86ISelFunction) {
    assert_eq!(count_x86_opcode(mfunc, X86Opcode::CmpRR), 0);
    assert_eq!(count_x86_opcode(mfunc, X86Opcode::Setcc), 0);
    assert_eq!(count_x86_opcode(mfunc, X86Opcode::Movzx), 0);
    assert_eq!(count_x86_opcode(mfunc, X86Opcode::Neg), 0);
}

fn assert_no_v2i64_icmp_adapter_lane_scalarization(lir_func: &Function) {
    for inst in lir_func
        .blocks
        .values()
        .flat_map(|block| block.instructions.iter())
    {
        assert!(
            !matches!(inst.opcode, Opcode::StackAddr { .. }),
            "v2i64 ICmp adapter path must not allocate stack lane temps: {inst:?}"
        );
        assert!(
            !matches!(inst.opcode, Opcode::ArrayGep { elem_ty: Type::I64 }),
            "v2i64 ICmp adapter path must not compute scalar lane addresses: {inst:?}"
        );
        assert!(
            !matches!(inst.opcode, Opcode::Icmp { .. }),
            "v2i64 ICmp adapter path must not emit scalar lane Icmp: {inst:?}"
        );
        assert!(
            !matches!(
                inst.opcode,
                Opcode::Uextend {
                    from_ty: Type::B1,
                    to_ty: Type::I64
                } | Opcode::Ineg
            ),
            "v2i64 ICmp adapter path must not expand bool lanes into i64 masks: {inst:?}"
        );
        assert!(
            !matches!(
                inst.opcode,
                Opcode::Load {
                    ty: Type::I64,
                    align: None
                } | Opcode::Store {
                    ty: Type::I64,
                    align: None
                }
            ),
            "v2i64 ICmp adapter path must not scalarize lane memory traffic: {inst:?}"
        );
    }
}

fn assert_module(assert_name: &str, constant: i128) -> TrustIrModule {
    single_function_module(
        0,
        assert_name,
        func_ty(vec![], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Int(constant),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Assert { cond: v(0) }),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
        vec![],
    )
}

fn assume_module(assume_name: &str, constant: i128) -> TrustIrModule {
    single_function_module(
        0,
        assume_name,
        func_ty(vec![], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Int(constant),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Assume { cond: v(0) }),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
        vec![],
    )
}

fn dealloc_module(name: &str) -> TrustIrModule {
    single_function_module(
        0,
        name,
        func_ty(vec![Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn assert_trap_block_aarch64(mfunc: &ISelFunction) -> Block {
    let entry = &mfunc.blocks[&Block(0)];
    let trap_block = entry
        .insts
        .iter()
        .find_map(|inst| {
            if inst.opcode != AArch64Opcode::BCond {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    ISelOperand::CondCode(AArch64CC::EQ),
                    ISelOperand::Block(block),
                ] => Some(*block),
                _ => None,
            }
        })
        .expect("assert must branch to a trap block on false");

    assert!(
        entry.successors.contains(&trap_block),
        "assert false edge must be present in the AArch64 CFG"
    );
    let trap = &mfunc.blocks[&trap_block];
    assert!(
        trap.insts
            .iter()
            .any(|inst| inst.opcode == AArch64Opcode::TrapOverflow),
        "AArch64 assert false edge must contain an explicit trap"
    );
    trap_block
}

fn assert_trap_block_x86_64(mfunc: &X86ISelFunction) -> Block {
    let entry = &mfunc.blocks[&Block(0)];
    let trap_block = entry
        .insts
        .iter()
        .find_map(|inst| {
            if inst.opcode != X86Opcode::Jcc {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(block),
                ] => Some(*block),
                _ => None,
            }
        })
        .expect("assert must branch to a trap block on false");

    assert!(
        entry.successors.contains(&trap_block),
        "assert false edge must be present in the x86_64 CFG"
    );
    let trap = &mfunc.blocks[&trap_block];
    assert!(
        trap.insts.iter().any(|inst| inst.opcode == X86Opcode::Ud2),
        "x86_64 assert false edge must contain UD2"
    );
    trap_block
}

#[test]
fn test_dealloc_fails_closed_until_allocator_semantics_are_wired() {
    let module = dealloc_module("dealloc_fail_closed");
    let err = translate_only(&module).expect_err("Dealloc must not be ignored or lowered as free");
    match err {
        AdapterError::UnsupportedInstruction(message) => {
            assert!(
                message.contains("allocator identity"),
                "Dealloc diagnostic must name the missing allocator contract, got: {message}"
            );
            assert!(
                message.contains("layout size/alignment"),
                "Dealloc diagnostic must name the missing layout contract, got: {message}"
            );
            assert!(
                message.contains("GlobalAlloc/Box"),
                "Dealloc diagnostic must name Rust release semantics, got: {message}"
            );
        }
        other => panic!("Dealloc must fail closed as UnsupportedInstruction, got {other:?}"),
    }
}

#[test]
fn test_assert_lowers_to_lir_runtime_guard() {
    let module = assert_module("assert_lir_guard", 1);
    let (lir_func, _) = translate_only(&module).expect("assert must lower to LIR");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Assert)),
        "Inst::Assert must not be ignored or rejected once a trap path exists"
    );
}

#[test]
fn test_assume_lowers_to_lir_runtime_guard() {
    let module = assume_module("assume_lir_guard", 1);
    let (lir_func, _) = translate_only(&module).expect("assume must lower to LIR");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Assert)),
        "Inst::Assume must materialize the checked runtime assertion path"
    );
}

#[test]
fn test_assert_true_and_false_lower_to_aarch64_conditional_trap() {
    for (name, constant) in [("assert_true_aarch64", 1), ("assert_false_aarch64", 0)] {
        let module = assert_module(name, constant);
        let mfunc = compile_trust_ir_function(&module);
        let entry = &mfunc.blocks[&Block(0)];

        assert!(
            entry
                .insts
                .iter()
                .any(|inst| inst.opcode == AArch64Opcode::CmpRI),
            "AArch64 assert must test the condition"
        );
        assert_trap_block_aarch64(&mfunc);
    }
}

#[test]
fn test_assume_true_and_false_lower_to_aarch64_conditional_trap() {
    for (name, constant) in [("assume_true_aarch64", 1), ("assume_false_aarch64", 0)] {
        let module = assume_module(name, constant);
        let mfunc = compile_trust_ir_function(&module);
        let entry = &mfunc.blocks[&Block(0)];

        assert!(
            entry
                .insts
                .iter()
                .any(|inst| inst.opcode == AArch64Opcode::CmpRI),
            "AArch64 assume must test the condition"
        );
        assert_trap_block_aarch64(&mfunc);
    }
}

#[test]
fn test_assert_true_and_false_lower_to_x86_64_conditional_trap() {
    for (name, constant) in [("assert_true_x86_64", 1), ("assert_false_x86_64", 0)] {
        let module = assert_module(name, constant);
        let mfunc = compile_trust_ir_function_x86_64(&module);
        let entry = &mfunc.blocks[&Block(0)];

        assert!(
            entry
                .insts
                .iter()
                .any(|inst| inst.opcode == X86Opcode::CmpRI),
            "x86_64 assert must test the condition"
        );
        assert_trap_block_x86_64(&mfunc);
    }
}

#[test]
fn test_assume_true_and_false_lower_to_x86_64_conditional_trap() {
    for (name, constant) in [("assume_true_x86_64", 1), ("assume_false_x86_64", 0)] {
        let module = assume_module(name, constant);
        let mfunc = compile_trust_ir_function_x86_64(&module);
        let entry = &mfunc.blocks[&Block(0)];

        assert!(
            entry
                .insts
                .iter()
                .any(|inst| inst.opcode == X86Opcode::CmpRI),
            "x86_64 assume must test the condition"
        );
        assert_trap_block_x86_64(&mfunc);
    }
}

fn assert_no_v4i32_icmp_adapter_lane_scalarization(lir_func: &Function) {
    for inst in lir_func
        .blocks
        .values()
        .flat_map(|block| block.instructions.iter())
    {
        assert!(
            !matches!(inst.opcode, Opcode::StackAddr { .. }),
            "v4i32 ICmp adapter path must not allocate stack lane temps: {inst:?}"
        );
        assert!(
            !matches!(inst.opcode, Opcode::ArrayGep { elem_ty: Type::I32 }),
            "v4i32 ICmp adapter path must not compute scalar lane addresses: {inst:?}"
        );
        assert!(
            !matches!(
                inst.opcode,
                Opcode::Uextend {
                    from_ty: Type::B1,
                    to_ty: Type::I32
                } | Opcode::Ineg
            ),
            "v4i32 ICmp adapter path must not expand bool lanes into i32 masks: {inst:?}"
        );
        assert!(
            !matches!(
                inst.opcode,
                Opcode::Load {
                    ty: Type::I32,
                    align: None
                } | Opcode::Store {
                    ty: Type::I32,
                    align: None
                }
            ),
            "v4i32 ICmp adapter path must not scalarize lane memory traffic: {inst:?}"
        );
        if matches!(inst.opcode, Opcode::Icmp { .. }) {
            for value in inst.args.iter().chain(inst.results.iter()) {
                if let Some(ty) = lir_func.value_types.get(value) {
                    assert_eq!(
                        ty,
                        &Type::V128,
                        "v4i32 ICmp must stay on V128 values when typed: {inst:?}"
                    );
                }
            }
        }
    }
}

fn total_insts(mfunc: &ISelFunction) -> usize {
    mfunc.blocks.values().map(|b| b.insts.len()).sum()
}

// ===========================================================================
// Test 1: identity(x: i32) -> i32 { x }
// ===========================================================================

fn build_identity() -> TrustIrModule {
    single_function_module(
        0,
        "identity",
        func_ty(vec![Ty::I32], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I32)],
            body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
        }],
        vec![],
    )
}

#[test]
fn test_identity_adapter() {
    let module = build_identity();
    let (lir_func, proof_ctx) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "identity");
    assert_eq!(lir_func.signature.params, vec![Type::I32]);
    assert_eq!(lir_func.signature.returns, vec![Type::I32]);
    assert_eq!(lir_func.blocks.len(), 1);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.params.len(), 1);
    assert_eq!(entry.instructions.len(), 1);

    assert!(proof_ctx.value_proofs.is_empty());
}

#[test]
fn test_identity_isel() {
    let module = build_identity();
    let mfunc = compile_trust_ir_function(&module);

    assert_eq!(mfunc.name, "identity");
    assert!(!mfunc.blocks.is_empty());
    assert!(has_opcode(&mfunc, AArch64Opcode::Copy));
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Test 2: add(a: i32, b: i32) -> i32 { a + b }
// ===========================================================================

fn build_add() -> TrustIrModule {
    single_function_module(
        1,
        "add",
        func_ty(vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I32), (v(1), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_add_adapter() {
    let module = build_add();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "add");
    assert_eq!(lir_func.signature.params, vec![Type::I32, Type::I32]);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.params.len(), 2);
    assert_eq!(entry.instructions.len(), 2);
}

#[test]
fn test_add_isel() {
    let module = build_add();
    let mfunc = compile_trust_ir_function(&module);

    assert_eq!(mfunc.name, "add");
    assert!(
        has_opcode(&mfunc, AArch64Opcode::AddRR),
        "Expected ADDWrr for i32 addition"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Test 3: negate(x: i32) -> i32 { -x }
// ===========================================================================

fn build_negate() -> TrustIrModule {
    single_function_module(
        2,
        "negate",
        func_ty(vec![Ty::I32], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::UnOp {
                    op: UnOp::Neg,
                    ty: Ty::I32,
                    operand: v(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_negate_adapter() {
    let module = build_negate();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
}

#[test]
fn test_negate_isel() {
    let module = build_negate();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::Neg),
        "Expected NEGWr for negation (-x)"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Test 4: max(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
// ===========================================================================

fn build_max() -> TrustIrModule {
    single_function_module(
        3,
        "max",
        func_ty(vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I32), (v(1), Ty::I32)],
                body: vec![
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Sgt,
                        ty: Ty::I32,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::CondBr {
                        cond: v(2),
                        then_target: b(1),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(1)] })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_max_adapter() {
    let module = build_max();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.blocks.len(), 3);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
}

#[test]
fn test_max_isel() {
    let module = build_max();
    let mfunc = compile_trust_ir_function(&module);

    assert_eq!(mfunc.blocks.len(), 3);
    assert!(
        has_opcode(&mfunc, AArch64Opcode::CmpRR),
        "Expected CMPWrr for signed comparison"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::BCond),
        "Expected Bcc for conditional branch"
    );
    assert!(
        count_opcode(&mfunc, AArch64Opcode::Ret) >= 2,
        "Expected at least 2 RET instructions (then + else)"
    );
}

// ===========================================================================
// Test 5: sum(n: i32) -> i32
// ===========================================================================

fn build_sum() -> TrustIrModule {
    single_function_module(
        4,
        "sum",
        func_ty(vec![Ty::I32], vec![Ty::I32]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I32)],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(0),
                    })
                    .with_result(v(1)),
                    InstrNode::new(Inst::Br {
                        target: b(1),
                        args: vec![v(0), v(1)],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![(v(2), Ty::I32), (v(3), Ty::I32)],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(0),
                    })
                    .with_result(v(4)),
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Sgt,
                        ty: Ty::I32,
                        lhs: v(2),
                        rhs: v(4),
                    })
                    .with_result(v(5)),
                    InstrNode::new(Inst::CondBr {
                        cond: v(5),
                        then_target: b(2),
                        then_args: vec![],
                        else_target: b(3),
                        else_args: vec![],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I32,
                        lhs: v(3),
                        rhs: v(2),
                    })
                    .with_result(v(6)),
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(1),
                    })
                    .with_result(v(7)),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I32,
                        lhs: v(2),
                        rhs: v(7),
                    })
                    .with_result(v(8)),
                    InstrNode::new(Inst::Br {
                        target: b(1),
                        args: vec![v(8), v(6)],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(3),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(3)] })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_sum_adapter() {
    let module = build_sum();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "sum");
    assert_eq!(lir_func.blocks.len(), 4);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry.instructions.len() >= 2,
        "Entry should have at least Iconst + Jump, got {}",
        entry.instructions.len()
    );
}

#[test]
fn test_sum_isel_body_instructions() {
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::{Instruction, Value};

    let sig = Signature {
        params: vec![Type::I32, Type::I32],
        returns: vec![Type::I32],
    };
    let mut isel = InstructionSelector::new("sum_body".to_string(), sig.clone());
    let entry = Block(0);
    isel.lower_formal_arguments(&sig, entry).unwrap();

    isel.select_block(
        entry,
        &[
            Instruction {
                opcode: Opcode::Iadd,
                args: vec![Value(0), Value(1)],
                results: vec![Value(2)],
            },
            Instruction {
                opcode: Opcode::Iconst {
                    ty: Type::I32,
                    imm: 1,
                },
                args: vec![],
                results: vec![Value(3)],
            },
            Instruction {
                opcode: Opcode::Isub,
                args: vec![Value(1), Value(3)],
                results: vec![Value(4)],
            },
            Instruction {
                opcode: Opcode::Iconst {
                    ty: Type::I32,
                    imm: 0,
                },
                args: vec![],
                results: vec![Value(5)],
            },
            Instruction {
                opcode: Opcode::Icmp {
                    cond: trust_cg_lower::instructions::IntCC::SignedGreaterThan,
                },
                args: vec![Value(4), Value(5)],
                results: vec![Value(6)],
            },
            Instruction {
                opcode: Opcode::Return,
                args: vec![Value(2)],
                results: vec![],
            },
        ],
    )
    .unwrap();

    let mfunc = isel.finalize();
    let mblock = &mfunc.blocks[&entry];

    assert!(has_opcode(&mfunc, AArch64Opcode::AddRR));
    assert!(has_opcode(&mfunc, AArch64Opcode::SubRR));
    assert!(has_opcode(&mfunc, AArch64Opcode::CmpRR));
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
    assert!(mblock.insts.len() >= 6, "Expected at least 6 instructions");
}

// ===========================================================================
// Test 6: load_store(p: *mut i32, v: i32) { *p = v; }
// ===========================================================================

fn build_load_store() -> TrustIrModule {
    single_function_module(
        5,
        "load_store",
        func_ty(vec![Ty::Ptr, Ty::I32], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::Store {
                    ty: Ty::I32,
                    ptr: v(0),
                    value: v(1),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_load_store_adapter() {
    let module = build_load_store();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "load_store");
    assert_eq!(lir_func.signature.params, vec![Type::I64, Type::I32]);
    assert_eq!(lir_func.signature.returns, vec![]);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
}

#[test]
fn test_load_store_isel() {
    let module = build_load_store();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::StrRI),
        "Expected STRWui for 32-bit store"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Extended test: load then store
// ===========================================================================

fn build_load_then_store() -> TrustIrModule {
    single_function_module(
        6,
        "load_then_store",
        func_ty(vec![Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I32,
                    ptr: v(0),
                    value: v(1),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_load_then_store_isel() {
    let module = build_load_then_store();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::LdrRI),
        "Expected LDRWui for 32-bit load"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::StrRI),
        "Expected STRWui for 32-bit store"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Volatile memory must survive trust_ir -> adapter -> AArch64 ISel
// ===========================================================================

fn build_volatile_load_store() -> TrustIrModule {
    single_function_module(
        60,
        "volatile_load_store",
        func_ty(vec![Ty::Ptr, Ty::U8], vec![Ty::U8]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::U8)],
            body: vec![
                InstrNode::new(Inst::Store {
                    ty: Ty::U8,
                    ptr: v(0),
                    value: v(1),
                    volatile: true,
                    align: None,
                }),
                InstrNode::new(Inst::Load {
                    ty: Ty::U8,
                    ptr: v(0),
                    volatile: true,
                    align: None,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_volatile_load_store_adapter_lowers_to_barrier_opcodes() {
    let module = build_volatile_load_store();
    let (func, _) = translate_only(&module)
        .expect("volatile memory now lowers to VolatileLoad/VolatileStore barrier opcodes");
    let ops: Vec<_> = func
        .blocks
        .values()
        .flat_map(|bb| bb.instructions.iter())
        .collect();
    assert_eq!(
        ops.iter()
            .filter(|i| matches!(i.opcode, Opcode::VolatileLoad { .. }))
            .count(),
        1,
        "volatile load must lower to VolatileLoad"
    );
    assert_eq!(
        ops.iter()
            .filter(|i| matches!(i.opcode, Opcode::VolatileStore { .. }))
            .count(),
        1,
        "volatile store must lower to VolatileStore"
    );
}

fn build_cmpxchg_with_orderings(success: Ordering, failure: Ordering) -> TrustIrModule {
    single_function_module(
        61,
        "cmpxchg_orderings",
        func_ty(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![Ty::I64, Ty::Bool]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::CmpXchg {
                    ty: Ty::I64,
                    ptr: v(0),
                    expected: v(1),
                    desired: v(2),
                    success,
                    failure,
                })
                .with_results(vec![v(3), v(4)]),
                InstrNode::new(Inst::Return {
                    values: vec![v(3), v(4)],
                }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_cmpxchg_adapter_preserves_success_and_failure_orderings() {
    let module = build_cmpxchg_with_orderings(Ordering::AcqRel, Ordering::Acquire);
    let (lir_func, _) = translate_only(&module).unwrap();
    let entry = &lir_func.blocks[&lir_func.entry_block];

    match &entry.instructions[0].opcode {
        Opcode::CmpXchg {
            ty,
            success,
            failure,
        } => {
            assert_eq!(*ty, Type::I64);
            assert_eq!(*success, AtomicOrdering::AcqRel);
            assert_eq!(*failure, AtomicOrdering::Acquire);
        }
        other => panic!("expected CmpXchg to lower with both orderings, got {other:?}"),
    }
}

#[test]
fn test_cmpxchg_invalid_failure_ordering_fails_in_adapter() {
    // A failure ordering of Release / AcqRel is the ONLY genuinely-invalid
    // cmpxchg failure ordering (C++17 / Rust >= 1.64): the failure path is a
    // load, so a release semantic is meaningless there. The adapter rejects it
    // with an always-on `return Err` (NOT a debug_assert), so this fails closed
    // in release too — a Release/AcqRel failure ordering reaching codegen would
    // be a genuine miscompile. (Item 4: the test previously pinned the pre-1.64
    // "failure must be weaker than success" rule, which the adapter no longer
    // enforces — see the positive lifting test below.)
    for bad in [Ordering::Release, Ordering::AcqRel] {
        let module = build_cmpxchg_with_orderings(Ordering::Acquire, bad);
        let err =
            translate_only(&module).expect_err("Release/AcqRel failure ordering must fail closed");
        assert!(
            matches!(&err, AdapterError::UnsupportedInstruction(message)
                if message.contains(&format!("CmpXchg failure ordering {bad:?}"))
                    && message.contains("must not be Release/AcqRel")),
            "expected invalid cmpxchg ordering diagnostic for {bad:?}, got {err:?}"
        );
    }
}

/// The failure ordering may legally be STRONGER than the success ordering
/// (C++17 / Rust >= 1.64: std's mutex/rwlock use `compare_exchange(.., Acquire,
/// SeqCst)`). The adapter must accept it and LIFT the success ordering to cover
/// the failure path — a strictly stronger single machine ordering that
/// over-satisfies both paths — never fail closed.
#[test]
fn test_cmpxchg_failure_stronger_than_success_lifts_in_adapter() {
    let module = build_cmpxchg_with_orderings(Ordering::Acquire, Ordering::SeqCst);
    let (lir_func, _) = translate_only(&module)
        .expect("failure-stronger-than-success cmpxchg is legal and must lift, not fail");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    match &entry.instructions[0].opcode {
        Opcode::CmpXchg {
            success, failure, ..
        } => {
            // success lifted Acquire -> SeqCst to cover the SeqCst failure path.
            assert_eq!(*success, AtomicOrdering::SeqCst);
            assert_eq!(*failure, AtomicOrdering::SeqCst);
        }
        other => panic!("expected lifted CmpXchg, got {other:?}"),
    }
}

#[test]
fn test_cmpxchg_orderings_reach_aarch64_selection() {
    let module = build_cmpxchg_with_orderings(Ordering::AcqRel, Ordering::Acquire);
    let mfunc = compile_trust_ir_function(&module);
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Casal),
        "AcqRel/Acquire cmpxchg should reach AArch64 CASAL selection"
    );
}

#[test]
fn test_cmpxchg_orderings_reach_x86_64_selection() {
    let module = build_cmpxchg_with_orderings(Ordering::SeqCst, Ordering::Acquire);
    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert!(
        has_x86_opcode(&mfunc, X86Opcode::Cmpxchg),
        "SeqCst/Acquire cmpxchg should reach x86-64 CMPXCHG selection"
    );
}

#[test]
fn test_volatile_load_store_aarch64_isel_compiles() {
    // AArch64 (primary target) lowers volatile via the VolatileLdr*/VolatileStr*
    // barrier opcodes. Verified end-to-end elsewhere (two volatile reads emit
    // two machine loads; a plain read pair CSEs to one).
    let module = build_volatile_load_store();
    try_compile_trust_ir_function(&module)
        .expect("volatile memory now compiles through AArch64 ISel");
}

#[test]
fn test_volatile_load_store_x86_64_isel_compiles() {
    // x86-64 volatile is wired for scalar integer, FP, and V128 widths via
    // distinct VolatileMov* barrier opcodes (byte-identical encoding to the
    // plain MOVs; classified MemoryEffect::Call so the optimizer never
    // elides/CSEs/reorders them). Disassembly-verified: two volatile reads emit
    // two `movq (%rdi)`. I128/U128 fail closed before ISel because the
    // register-pair representation would split one volatile event in two.
    let module = build_volatile_load_store();
    try_compile_trust_ir_function_x86_64(&module)
        .expect("x86-64 volatile now compiles through x86-64 ISel");
}

// ===========================================================================
// End-to-end pipeline test
// ===========================================================================

#[test]
fn test_all_single_block_programs_compile_without_panic() {
    let programs: Vec<(&str, TrustIrModule)> = vec![
        ("identity", build_identity()),
        ("add", build_add()),
        ("negate", build_negate()),
        ("max", build_max()),
        ("load_store", build_load_store()),
    ];

    for (name, module) in &programs {
        let mfunc = compile_trust_ir_function(module);
        assert!(
            !mfunc.blocks.is_empty(),
            "{}: produced empty ISelFunction",
            name
        );
        assert!(
            total_insts(&mfunc) > 0,
            "{}: produced no machine instructions",
            name
        );
        assert!(
            has_opcode(&mfunc, AArch64Opcode::Ret),
            "{}: missing RET instruction",
            name
        );
        assert!(
            has_opcode(&mfunc, AArch64Opcode::Copy),
            "{}: missing COPY for formal arguments",
            name
        );
    }
}

#[test]
fn test_all_programs_adapter_succeeds() {
    let programs: Vec<(&str, TrustIrModule)> = vec![
        ("identity", build_identity()),
        ("add", build_add()),
        ("negate", build_negate()),
        ("max", build_max()),
        ("sum", build_sum()),
        ("load_store", build_load_store()),
    ];

    for (name, module) in &programs {
        let result = translate_only(module);
        assert!(
            result.is_ok(),
            "{}: adapter translation failed: {:?}",
            name,
            result.err()
        );
        let (lir_func, _) = result.unwrap();
        assert_eq!(lir_func.name, *name);
        assert!(!lir_func.blocks.is_empty());
    }
}

// ===========================================================================
// Adapter-level regression: verify type translation preserves semantics
// ===========================================================================

#[test]
fn test_adapter_type_translation_in_context() {
    let module = build_load_store();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.signature.params[0], Type::I64);
    assert_eq!(lir_func.signature.params[1], Type::I32);
}

// ===========================================================================
// Adapter-level: verify block parameter passing
// ===========================================================================

#[test]
fn test_adapter_block_params_for_loop() {
    let module = build_sum();
    let (lir_func, _) = translate_only(&module).unwrap();

    let loop_header_block = lir_func
        .blocks
        .iter()
        .find(|(_, bb)| bb.params.len() == 2)
        .expect("Should have a block with 2 params (loop header)");

    assert_eq!(loop_header_block.1.params.len(), 2);
    assert_eq!(loop_header_block.1.params[0].1, Type::I32);
    assert_eq!(loop_header_block.1.params[1].1, Type::I32);
}

// ===========================================================================
// Test 7: Direct function call
// ===========================================================================

fn build_call_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("call_test");
    // After #381, the adapter propagates the callee signature's return type
    // onto the Call result Value, so I32 end-to-end is type-correct through
    // ISel's #307 Return check. (Historic note: this fixture was forced to
    // I64 in #380 as a workaround for the missing type propagation.)
    let shared_sig: FuncTyId = module.add_func_type(func_ty(vec![Ty::I32], vec![Ty::I32]));

    let mut callee = TrustIrFunction::new(f(0), "callee", shared_sig, b(0));
    callee.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::I32)],
        body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
    });

    let mut caller = TrustIrFunction::new(f(1), "caller", shared_sig, b(0));
    caller.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: f(0),
                args: vec![v(0)],
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });

    module.add_function(callee);
    module.add_function(caller);
    module
}

fn build_direct_call_result_block_arg_merge() -> TrustIrModule {
    let mut module = TrustIrModule::new("direct_call_result_block_arg_merge");
    let callee_ty = module.add_func_type(func_ty(vec![], vec![Ty::I32]));
    let caller_ty = module.add_func_type(func_ty(vec![], vec![Ty::I32]));

    let mut callee = TrustIrFunction::new(f(20), "direct_block_arg_callee", callee_ty, b(0));
    callee.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![v(0)] }),
        ],
    });

    let mut caller =
        TrustIrFunction::new(f(21), "direct_call_result_block_arg_merge", caller_ty, b(0));
    caller.blocks = vec![
        TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Call {
                    callee: f(20),
                    args: vec![],
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Br {
                    target: b(1),
                    args: vec![v(0)],
                }),
            ],
        },
        TrustIrBlock {
            id: b(1),
            params: vec![(v(1), Ty::I32)],
            body: vec![InstrNode::new(Inst::Return { values: vec![v(1)] })],
        },
    ];

    module.add_function(callee);
    module.add_function(caller);
    module
}

#[test]
fn test_call_adapter() {
    let module = build_call_module();
    let results = translate_module(&module).unwrap();
    assert_eq!(results.len(), 2);

    let (callee_func, _) = &results[0];
    assert_eq!(callee_func.name, "callee");

    let (caller_func, _) = &results[1];
    assert_eq!(caller_func.name, "caller");

    let entry = &caller_func.blocks[&caller_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(
        matches!(&entry.instructions[0].opcode, Opcode::Call { name } if name == "callee"),
        "Expected Call to 'callee', got {:?}",
        entry.instructions[0].opcode
    );
}

#[test]
fn test_direct_call_result_can_feed_block_arg_validation() {
    let module = build_direct_call_result_block_arg_merge();
    let results = translate_module(&module).unwrap();
    let (caller_func, _) = results
        .iter()
        .find(|(func, _)| func.name == "direct_call_result_block_arg_merge")
        .expect("caller should translate");
    assert_eq!(caller_func.blocks.len(), 2);

    let entry = &caller_func.blocks[&caller_func.entry_block];
    let call_inst = entry
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Call { .. }))
        .expect("expected direct call before block-arg branch");
    assert_eq!(
        caller_func.value_types.get(&call_inst.results[0]),
        Some(&Type::I32)
    );
    assert!(
        entry.instructions.iter().any(|inst| {
            matches!(inst.opcode, Opcode::Copy) && inst.args == vec![call_inst.results[0]]
        }),
        "expected block-arg copy from direct call result to merge param"
    );
}

#[test]
fn test_empty_closure_const_materializes_function_symbol_pointer_arg() {
    let mut module = TrustIrModule::new("function_pointer_arg");
    let rust_main_sig = module.add_func_type(func_ty(vec![], vec![]));
    let accept_sig = module.add_func_type(func_ty(vec![Ty::Func(rust_main_sig)], vec![Ty::I32]));
    let caller_sig = module.add_func_type(func_ty(vec![], vec![Ty::I32]));

    let mut rust_main = TrustIrFunction::new(f(0), "_rust_main", rust_main_sig, b(0));
    rust_main.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![InstrNode::new(Inst::Unreachable)],
    });

    let mut accept = TrustIrFunction::new(f(1), "_accept_fn_ptr", accept_sig, b(0));
    accept.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Func(rust_main_sig))],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });

    let mut caller = TrustIrFunction::new(f(2), "_caller", caller_sig, b(0));
    caller.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(rust_main_sig),
                value: Constant::Closure {
                    func: f(0),
                    captures: vec![],
                },
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Call {
                callee: f(1),
                args: vec![v(0)],
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });

    module.add_function(rust_main);
    module.add_function(accept);
    module.add_function(caller);

    let results = translate_module(&module).expect("module should translate");
    let (caller_lir, _) = &results[2];
    let entry = &caller_lir.blocks[&caller_lir.entry_block];

    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::GlobalRef { name } if name == "_rust_main"
    ));
    assert!(matches!(
        &entry.instructions[1].opcode,
        Opcode::Call { name } if name == "_accept_fn_ptr"
    ));
    assert_eq!(
        entry.instructions[1].args,
        vec![entry.instructions[0].results[0]]
    );

    let mut isel = InstructionSelector::new(caller_lir.name.clone(), caller_lir.signature.clone());
    isel.seed_value_types(&caller_lir.value_types);
    isel.lower_formal_arguments(&caller_lir.signature, caller_lir.entry_block)
        .unwrap();
    let bb = &caller_lir.blocks[&caller_lir.entry_block];
    isel.select_block(caller_lir.entry_block, &bb.instructions)
        .unwrap();
    let mfunc = isel.finalize();

    assert!(has_opcode(&mfunc, AArch64Opcode::Adrp));
    assert!(has_opcode(&mfunc, AArch64Opcode::AddPCRel));
    assert!(has_opcode(&mfunc, AArch64Opcode::Bl));
}

#[test]
fn test_reify_fn_pointer_from_fndef_materializes_code_pointer_on_both_targets() {
    let mut module = TrustIrModule::new("reify_fn_pointer_fndef");
    let target_sig = module.add_func_type(func_ty(vec![], vec![]));
    let caller_sig = module.add_func_type(func_ty(vec![], vec![Ty::Ptr]));

    let mut target = TrustIrFunction::new(f(0), "_reify_target", target_sig, b(0));
    target.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![InstrNode::new(Inst::Unreachable)],
    });

    let mut caller = TrustIrFunction::new(f(1), "_reify_caller", caller_sig, b(0));
    caller.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(target_sig),
                value: Constant::FnDef(f(0)),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(target_sig),
                dst_ty: Ty::Ptr,
                operand: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });

    module.add_function(target);
    module.add_function(caller);

    let results = translate_module(&module).expect("module should translate");
    let (caller_lir, _) = results
        .iter()
        .find(|(func, _)| func.name == "_reify_caller")
        .expect("caller should translate");
    let entry = &caller_lir.blocks[&caller_lir.entry_block];
    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::GlobalRef { name } if name == "_reify_target"
    ));
    assert!(matches!(entry.instructions[1].opcode, Opcode::Copy));
    assert_eq!(
        entry.instructions[1].args,
        vec![entry.instructions[0].results[0]]
    );

    let mut aarch64 =
        InstructionSelector::new(caller_lir.name.clone(), caller_lir.signature.clone());
    aarch64.seed_value_types(&caller_lir.value_types);
    aarch64
        .lower_formal_arguments(&caller_lir.signature, caller_lir.entry_block)
        .unwrap();
    aarch64
        .select_block(caller_lir.entry_block, &entry.instructions)
        .unwrap();
    let aarch64_func = aarch64.finalize();
    assert!(has_opcode(&aarch64_func, AArch64Opcode::Adrp));
    assert!(has_opcode(&aarch64_func, AArch64Opcode::AddPCRel));

    let mut x86 =
        X86InstructionSelector::new(caller_lir.name.clone(), caller_lir.signature.clone());
    x86.seed_value_types(&caller_lir.value_types);
    x86.seed_function_value_use_counts(caller_lir);
    x86.lower_formal_arguments(&caller_lir.signature, caller_lir.entry_block)
        .unwrap();
    x86.select_block(caller_lir.entry_block, &entry.instructions)
        .unwrap();
    let x86_func = x86.finalize();
    assert!(
        x86_func.blocks[&caller_lir.entry_block]
            .insts
            .iter()
            .any(|inst| inst.opcode == X86Opcode::LeaRip)
    );
}

#[test]
fn test_call_isel() {
    let module = build_call_module();
    let results = translate_module(&module).unwrap();

    let (caller_lir, _) = &results[1];
    let mut isel = InstructionSelector::new(caller_lir.name.clone(), caller_lir.signature.clone());
    // Seed Value->Type hints (Call result types, #381).
    isel.seed_value_types(&caller_lir.value_types);
    isel.lower_formal_arguments(&caller_lir.signature, caller_lir.entry_block)
        .unwrap();

    let mut block_order: Vec<Block> = caller_lir.blocks.keys().copied().collect();
    block_order.sort_by_key(|b| {
        if *b == caller_lir.entry_block {
            0
        } else {
            b.0 + 1
        }
    });

    for block_id in &block_order {
        let bb = &caller_lir.blocks[block_id];
        isel.select_block(*block_id, &bb.instructions).unwrap();
    }

    let mfunc = isel.finalize();
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Bl),
        "Expected BL instruction for direct call"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Test 8: Switch
// ===========================================================================

fn build_switch() -> TrustIrModule {
    single_function_module(
        10,
        "dispatch",
        func_ty(vec![Ty::I32], vec![Ty::I32]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I32)],
                body: vec![InstrNode::new(Inst::Switch {
                    value: v(0),
                    default: b(3),
                    default_args: vec![],
                    cases: vec![
                        SwitchCase {
                            value: Constant::Int(0),
                            target: b(1),
                            args: vec![],
                        },
                        SwitchCase {
                            value: Constant::Int(1),
                            target: b(2),
                            args: vec![],
                        },
                    ],
                    exhaustive_enum_unreachable: false,
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(10),
                    })
                    .with_result(v(1)),
                    InstrNode::new(Inst::Return { values: vec![v(1)] }),
                ],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(20),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Return { values: vec![v(2)] }),
                ],
            },
            TrustIrBlock {
                id: b(3),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(30),
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            },
        ],
        vec![],
    )
}

fn build_sparse_switch_case_materialization(
    func_name: &str,
    selector_ty: Ty,
    cases: Vec<i128>,
) -> TrustIrModule {
    assert_eq!(cases.len(), 3, "test helper expects three sparse cases");
    single_function_module(
        10,
        func_name,
        func_ty(vec![selector_ty.clone()], vec![Ty::I32]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), selector_ty)],
                body: vec![InstrNode::new(Inst::Switch {
                    value: v(0),
                    default: b(4),
                    default_args: vec![],
                    cases: cases
                        .into_iter()
                        .enumerate()
                        .map(|(idx, value)| SwitchCase {
                            value: Constant::Int(value),
                            target: b(idx as u32 + 1),
                            args: vec![],
                        })
                        .collect(),
                    exhaustive_enum_unreachable: false,
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(10),
                    })
                    .with_result(v(1)),
                    InstrNode::new(Inst::Return { values: vec![v(1)] }),
                ],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(20),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Return { values: vec![v(2)] }),
                ],
            },
            TrustIrBlock {
                id: b(3),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(30),
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            },
            TrustIrBlock {
                id: b(4),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(40),
                    })
                    .with_result(v(4)),
                    InstrNode::new(Inst::Return { values: vec![v(4)] }),
                ],
            },
        ],
        vec![],
    )
}

fn invalid_movz_immediates(mfunc: &ISelFunction) -> Vec<i64> {
    mfunc
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .filter(|inst| inst.opcode == AArch64Opcode::Movz)
        .filter_map(|inst| match inst.operands.get(1) {
            Some(trust_cg_lower::isel::ISelOperand::Imm(imm)) => Some(*imm),
            _ => None,
        })
        .filter(|imm| !(0..=0xFFFF).contains(imm))
        .collect()
}

#[test]
fn test_switch_adapter() {
    let module = build_switch();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "dispatch");
    assert_eq!(lir_func.blocks.len(), 4);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 1);
    match &entry.instructions[0].opcode {
        Opcode::Switch { cases, default: _ } => {
            assert_eq!(cases.len(), 2, "Expected 2 switch cases");
            assert_eq!(cases[0].0, 0);
            assert_eq!(cases[1].0, 1);
        }
        other => panic!("Expected Switch opcode, got {:?}", other),
    }
}

#[test]
fn test_switch_isel() {
    let module = build_switch();
    let mfunc = compile_trust_ir_function(&module);

    assert_eq!(mfunc.blocks.len(), 4);
    assert!(
        has_opcode(&mfunc, AArch64Opcode::CmpRR) || has_opcode(&mfunc, AArch64Opcode::CmpRI),
        "Expected CMP instruction for switch case comparison"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::BCond),
        "Expected B.EQ for switch case branch"
    );
    assert!(
        count_opcode(&mfunc, AArch64Opcode::Ret) >= 3,
        "Expected at least 3 RET instructions (case 0, case 1, default)"
    );
}

#[test]
fn test_switch_sparse_large_i32_case_materialization_isel() {
    let module = build_sparse_switch_case_materialization(
        "switch_sparse_large_i32",
        Ty::I32,
        vec![0x1234_5678, 7, 0x1_0000],
    );
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        invalid_movz_immediates(&mfunc).is_empty(),
        "sparse i32 switch case materialization must not emit invalid MOVZ immediates"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::CmpRR),
        "large i32 switch cases should compare against a materialized register"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Movk),
        "large i32 switch cases should use MOVK for full-width materialization"
    );
}

#[test]
fn test_switch_sparse_large_i64_case_materialization_isel() {
    let module = build_sparse_switch_case_materialization(
        "switch_sparse_large_i64",
        Ty::I64,
        vec![0x0001_0002_0003_0004, 7, 0x1_0000_0000],
    );
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        invalid_movz_immediates(&mfunc).is_empty(),
        "sparse i64 switch case materialization must not emit invalid MOVZ immediates"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::CmpRR),
        "large i64 switch cases should compare against a materialized register"
    );
    assert!(
        count_opcode(&mfunc, AArch64Opcode::Movk) >= 3,
        "large i64 switch cases should use MOVK chunks for full-width materialization"
    );
}

#[test]
fn test_switch_sparse_negative_i64_case_materialization_isel() {
    let module = build_sparse_switch_case_materialization(
        "switch_sparse_negative_i64",
        Ty::I64,
        vec![-0x0001_0002_0003_0004, 7, 0x1_0000],
    );
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        invalid_movz_immediates(&mfunc).is_empty(),
        "sparse negative i64 switch case materialization must not emit invalid MOVZ immediates"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::CmpRR),
        "negative i64 switch cases should compare against a materialized register"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Movn) || has_opcode(&mfunc, AArch64Opcode::Movk),
        "negative i64 switch cases should use full-width move-wide materialization"
    );
}

// ===========================================================================
// Test 9: CallIndirect
// ===========================================================================

fn build_call_indirect() -> TrustIrModule {
    let mut module = TrustIrModule::new("call_through_ptr");
    // #381: adapter now propagates the callee signature's return types into
    // ISel's value_types map, so I32 call results are tracked correctly and
    // no longer fall back to I64.
    let callee_sig: FuncTyId = module.add_func_type(func_ty(vec![Ty::I32], vec![Ty::I32]));
    let func_sig: FuncTyId =
        module.add_func_type(func_ty(vec![Ty::Func(callee_sig), Ty::I32], vec![Ty::I32]));

    let mut func = TrustIrFunction::new(f(11), "call_through_ptr", func_sig, b(0));
    func.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Func(callee_sig)), (v(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::CallIndirect {
                callee: v(0),
                sig: callee_sig,
                args: vec![v(1)],
                calling_conv: trust_ir::CallingConv::C,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![v(2)] }),
        ],
    });

    module.add_function(func);
    module
}

#[test]
fn test_call_indirect_adapter() {
    let module = build_call_indirect();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "call_through_ptr");

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(
        matches!(&entry.instructions[0].opcode, Opcode::CallIndirect),
        "Expected CallIndirect opcode, got {:?}",
        entry.instructions[0].opcode
    );
    assert_eq!(
        entry.instructions[0].args.len(),
        2,
        "CallIndirect should have fn_ptr + 1 arg = 2 total args"
    );
}

#[test]
fn test_call_indirect_isel() {
    let module = build_call_indirect();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::Blr),
        "Expected BLR instruction for indirect call"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Test 10: Select
// ===========================================================================

fn build_select() -> TrustIrModule {
    single_function_module(
        12,
        "abs_select",
        func_ty(vec![Ty::I32], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::UnOp {
                    op: UnOp::Neg,
                    ty: Ty::I32,
                    operand: v(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Select {
                    ty: Ty::I32,
                    cond: v(3),
                    then_val: v(1),
                    else_val: v(0),
                })
                .with_result(v(4)),
                InstrNode::new(Inst::Return { values: vec![v(4)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_select_adapter() {
    let module = build_select();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "abs_select");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        entry.instructions.len() >= 4,
        "Expected at least 4 instructions for select pattern, got {}",
        entry.instructions.len()
    );

    let has_select = entry
        .instructions
        .iter()
        .any(|inst| matches!(&inst.opcode, Opcode::Select { .. }));
    assert!(has_select, "Expected Select opcode in instruction stream");
}

#[test]
fn test_select_isel() {
    let module = build_select();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::Csel),
        "Expected CSEL instruction for Select"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Test 11: GEP
// ===========================================================================

fn build_gep() -> TrustIrModule {
    single_function_module(
        13,
        "array_access",
        func_ty(vec![Ty::Ptr, Ty::I64], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I32,
                    base: v(0),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(2),
                    volatile: false,
                    align: None,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_gep_adapter() {
    let module = build_gep();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "array_access");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        entry.instructions.len() >= 4,
        "Expected at least 4 instructions for GEP+Load+Return, got {}",
        entry.instructions.len()
    );

    let has_load = entry
        .instructions
        .iter()
        .any(|inst| matches!(&inst.opcode, Opcode::Load { .. }));
    assert!(has_load, "Expected Load opcode after GEP");
}

#[test]
fn test_gep_isel() {
    let module = build_gep();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::LdrRI) || has_opcode(&mfunc, AArch64Opcode::LdrRO),
        "Expected LDR for load after GEP"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Test 12: GEP with explicit byte offset
// ===========================================================================

fn build_gep_with_offset() -> TrustIrModule {
    single_function_module(
        14,
        "struct_field_in_array",
        func_ty(vec![Ty::Ptr, Ty::I64], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(0),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(4),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::Ptr,
                    lhs: v(2),
                    rhs: v(3),
                })
                .with_result(v(4)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(4),
                    volatile: false,
                    align: None,
                })
                .with_result(v(5)),
                InstrNode::new(Inst::Return { values: vec![v(5)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_gep_with_offset_adapter() {
    let module = build_gep_with_offset();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "struct_field_in_array");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        entry.instructions.len() >= 6,
        "Expected at least 6 instructions for GEP with offset, got {}",
        entry.instructions.len()
    );
}

#[test]
fn test_gep_with_offset_isel() {
    let module = build_gep_with_offset();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::MulRR) || has_opcode(&mfunc, AArch64Opcode::Madd),
        "Expected MUL or MADD for index scaling in GEP"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::LdrRI) || has_opcode(&mfunc, AArch64Opcode::LdrRO),
        "Expected LDR for load after GEP"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ===========================================================================
// Test 13: Type casts
// ===========================================================================

fn build_cast_chain() -> TrustIrModule {
    single_function_module(
        15,
        "widen_and_narrow",
        func_ty(vec![Ty::I8], vec![Ty::I8]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I8)],
            body: vec![
                InstrNode::new(Inst::Cast {
                    op: CastOp::SExt,
                    src_ty: Ty::I8,
                    dst_ty: Ty::I32,
                    operand: v(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I32,
                    dst_ty: Ty::I8,
                    operand: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_cast_chain_adapter() {
    let module = build_cast_chain();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "widen_and_narrow");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 4);
    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::Sextend {
            from_ty: Type::I8,
            to_ty: Type::I32
        }
    ));
    assert!(matches!(
        &entry.instructions[1].opcode,
        Opcode::Trunc { to_ty: Type::I8 }
    ));
    assert!(matches!(
        &entry.instructions[2].opcode,
        Opcode::Sextend {
            from_ty: Type::I8,
            to_ty: Type::I32
        }
    ));
    assert!(matches!(&entry.instructions[3].opcode, Opcode::Return));
    assert_eq!(
        entry.instructions[3].args, entry.instructions[2].results,
        "the Apple arm64 ABI return must use the canonical sign-extended i32 carrier"
    );
}

#[test]
fn test_cast_chain_isel() {
    let module = build_cast_chain();
    let mfunc = compile_trust_ir_function(&module);

    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
    assert!(
        total_insts(&mfunc) >= 3,
        "Expected at least 3 machine instructions (COPY, SXTB, AND/TRUNC, RET)"
    );
}

// ===========================================================================
// Test 14: Float arithmetic + FP cast
// ===========================================================================

fn build_float_to_int() -> TrustIrModule {
    single_function_module(
        16,
        "float_to_int",
        func_ty(vec![Ty::F64, Ty::F64], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::F64), (v(1), Ty::F64)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Cast {
                    op: CastOp::FPToSI,
                    src_ty: Ty::F64,
                    dst_ty: Ty::I32,
                    operand: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_float_to_int_adapter() {
    let module = build_float_to_int();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.name, "float_to_int");
    assert_eq!(lir_func.signature.params, vec![Type::F64, Type::F64]);
    assert_eq!(lir_func.signature.returns, vec![Type::I32]);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 3);
}

#[test]
fn test_float_to_int_isel() {
    let module = build_float_to_int();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::FaddRR),
        "Expected FADD for f64 addition"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

fn build_frem(ty: Ty, name: &str) -> TrustIrModule {
    single_function_module(
        23,
        name,
        func_ty(vec![ty.clone(), ty.clone()], vec![ty.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), ty.clone()), (v(1), ty.clone())],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::FRem,
                    ty,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

fn build_packed_fp_binary(ty: Ty, op: BinOp, name: &str) -> TrustIrModule {
    single_function_module(
        24,
        name,
        func_ty(vec![ty.clone(), ty.clone()], vec![ty.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), ty.clone()), (v(1), ty.clone())],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op,
                    ty,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

fn packed_fp_binary_cases() -> [(Ty, BinOp, &'static str, usize); 6] {
    [
        (
            Ty::Vector(Box::new(Ty::F32), 4),
            BinOp::FMin,
            "v4f32_fmin",
            4,
        ),
        (
            Ty::Vector(Box::new(Ty::F32), 4),
            BinOp::FMax,
            "v4f32_fmax",
            4,
        ),
        (
            Ty::Vector(Box::new(Ty::F32), 4),
            BinOp::FRem,
            "v4f32_frem",
            4,
        ),
        (
            Ty::Vector(Box::new(Ty::F64), 2),
            BinOp::FMin,
            "v2f64_fmin",
            2,
        ),
        (
            Ty::Vector(Box::new(Ty::F64), 2),
            BinOp::FMax,
            "v2f64_fmax",
            2,
        ),
        (
            Ty::Vector(Box::new(Ty::F64), 2),
            BinOp::FRem,
            "v2f64_frem",
            2,
        ),
    ]
}

fn count_aarch64_calls_to(mfunc: &ISelFunction, callee: &str) -> usize {
    mfunc
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .filter(|inst| {
            inst.opcode == AArch64Opcode::Bl
                && inst
                    .operands
                    .iter()
                    .any(|op| matches!(op, ISelOperand::Symbol(name) if name == callee))
        })
        .count()
}

fn count_x86_64_calls_to(mfunc: &X86ISelFunction, callee: &str) -> usize {
    mfunc
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .filter(|inst| {
            inst.opcode == X86Opcode::Call
                && inst
                    .operands
                    .iter()
                    .any(|op| matches!(op, X86ISelOperand::Symbol(name) if name == callee))
        })
        .count()
}

#[test]
fn test_packed_fp_binary_adapter_result_flow_and_lane_semantics() {
    for (vector_ty, op, name, lanes) in packed_fp_binary_cases() {
        let lane_lir_ty = if lanes == 4 { Type::F32 } else { Type::F64 };
        let module = build_packed_fp_binary(vector_ty, op, name);
        let (lir, _) = translate_only(&module).expect("packed FP adapter lowering");
        let insts: Vec<_> = lir
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .collect();

        let lane_results: Vec<_> = insts
            .iter()
            .filter_map(|inst| {
                let is_lane_op = match (&op, &inst.opcode) {
                    (BinOp::FMin, Opcode::Fmin) | (BinOp::FMax, Opcode::Fmax) => true,
                    (BinOp::FRem, Opcode::Call { name }) => {
                        name == if lanes == 4 { "fmodf" } else { "fmod" }
                    }
                    _ => false,
                };
                is_lane_op.then(|| {
                    *inst
                        .results
                        .first()
                        .expect("every packed FP lane operation must define a result")
                })
            })
            .collect();
        assert_eq!(
            lane_results.len(),
            lanes,
            "{name} must perform exactly one scalar operation per lane"
        );

        let lane_stored_results: Vec<_> = insts
            .iter()
            .filter_map(|inst| match &inst.opcode {
                Opcode::Store { ty, .. } if ty == &lane_lir_ty => inst.args.first().copied(),
                _ => None,
            })
            .collect();
        assert_eq!(
            lane_stored_results, lane_results,
            "{name} must store each scalar lane result back in lane order"
        );

        let final_vector_load = insts
            .iter()
            .find(|inst| matches!(&inst.opcode, Opcode::Load { ty: Type::V128, .. }))
            .expect("packed FP lowering must reload the completed V128 result");
        let final_result = *final_vector_load
            .results
            .first()
            .expect("final V128 load must define the packed result");
        let ret = insts
            .iter()
            .find(|inst| matches!(inst.opcode, Opcode::Return))
            .expect("packed FP function must return");
        assert_eq!(
            ret.args,
            vec![final_result],
            "{name} must return the reassembled vector, not an input or lane temporary"
        );
    }
}

#[test]
fn test_packed_fp_binary_aarch64_supported_shapes_and_edge_mechanisms() {
    for (vector_ty, op, name, lanes) in packed_fp_binary_cases() {
        let module = build_packed_fp_binary(vector_ty, op, name);
        let mfunc = compile_trust_ir_function(&module);

        match op {
            BinOp::FMin => assert_eq!(
                count_opcode(&mfunc, AArch64Opcode::FminnmRR),
                lanes * 3,
                "{name} must use two self-FMINNM canonicalizations plus one binary \
                 FMINNM per lane so signaling and quiet sole-NaNs yield the number"
            ),
            BinOp::FMax => assert_eq!(
                count_opcode(&mfunc, AArch64Opcode::FmaxnmRR),
                lanes * 3,
                "{name} must use two self-FMAXNM canonicalizations plus one binary \
                 FMAXNM per lane so signaling and quiet sole-NaNs yield the number"
            ),
            BinOp::FRem => {
                let helper = if lanes == 4 { "fmodf" } else { "fmod" };
                assert_eq!(
                    count_aarch64_calls_to(&mfunc, helper),
                    lanes,
                    "{name} must delegate every lane to {helper}, including zero-divisor, \
                     infinity, NaN, and signed-result cases"
                );
            }
            _ => unreachable!("packed_fp_binary_cases only contains FMin/FMax/FRem"),
        }
        assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
    }
}

#[test]
fn test_packed_fp_binary_x86_64_supported_shapes_and_edge_mechanisms() {
    for (vector_ty, op, name, lanes) in packed_fp_binary_cases() {
        let is_f32 = lanes == 4;
        let module = build_packed_fp_binary(vector_ty, op, name);
        let mfunc = compile_trust_ir_function_x86_64(&module);

        match op {
            BinOp::FMin | BinOp::FMax => {
                let minmax_opcode = match (op, is_f32) {
                    (BinOp::FMin, true) => X86Opcode::Minss,
                    (BinOp::FMin, false) => X86Opcode::Minsd,
                    (BinOp::FMax, true) => X86Opcode::Maxss,
                    (BinOp::FMax, false) => X86Opcode::Maxsd,
                    _ => unreachable!("match is restricted to FMin/FMax"),
                };
                let unordered_cmp = if is_f32 {
                    X86Opcode::Cmpss
                } else {
                    X86Opcode::Cmpsd
                };
                assert_eq!(
                    count_x86_opcode(&mfunc, minmax_opcode),
                    lanes,
                    "{name} must select one scalar min/max instruction per lane"
                );
                assert_eq!(
                    count_x86_opcode(&mfunc, unordered_cmp),
                    lanes,
                    "{name} must retain one unordered comparison per lane for its NaN fixup"
                );
                assert!(
                    x86_opcode_imms(&mfunc, unordered_cmp)
                        .iter()
                        .all(|predicate| *predicate == 3),
                    "{name} NaN fixups must use the CMPUNORD predicate"
                );
            }
            BinOp::FRem => {
                let helper = if is_f32 { "fmodf" } else { "fmod" };
                assert_eq!(
                    count_x86_64_calls_to(&mfunc, helper),
                    lanes,
                    "{name} must delegate every lane to {helper}, including zero-divisor, \
                     infinity, NaN, and signed-result cases"
                );
            }
            _ => unreachable!("packed_fp_binary_cases only contains FMin/FMax/FRem"),
        }
        assert!(has_x86_opcode(&mfunc, X86Opcode::Ret));
    }
}

#[test]
fn test_frem_f64_lowers_to_fmod_on_aarch64() {
    let module = build_frem(Ty::F64, "frem_f64");
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        aarch64_has_call_to(&mfunc, "fmod"),
        "expected scalar f64 FRem to lower to BL fmod"
    );
}

#[test]
fn test_frem_f32_lowers_to_fmodf_on_aarch64() {
    let module = build_frem(Ty::F32, "frem_f32");
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        aarch64_has_call_to(&mfunc, "fmodf"),
        "expected scalar f32 FRem to lower to BL fmodf"
    );
}

#[test]
fn test_frem_f64_lowers_to_fmod_on_x86_64() {
    let module = build_frem(Ty::F64, "frem_f64");
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert!(
        x86_64_has_call_to(&mfunc, "fmod"),
        "expected scalar f64 FRem to lower to CALL fmod"
    );
}

#[test]
fn test_frem_f32_lowers_to_fmodf_on_x86_64() {
    let module = build_frem(Ty::F32, "frem_f32");
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert!(
        x86_64_has_call_to(&mfunc, "fmodf"),
        "expected scalar f32 FRem to lower to CALL fmodf"
    );
}

// ===========================================================================
// Proof annotations survive adapter translation
// ===========================================================================

#[test]
fn test_proof_annotations_survive() {
    let module = single_function_module(
        22,
        "proven_add",
        func_ty(vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I32), (v(1), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2))
                .with_proof(ProofAnnotation::NoOverflow),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![ProofAnnotation::Pure],
    );

    let (_, proof_ctx) = translate_only(&module).unwrap();

    assert!(
        proof_ctx.is_function_pure(),
        "Function-level Pure proof should survive adapter translation"
    );

    let has_no_overflow = proof_ctx.value_proofs.values().any(|proofs| {
        proofs.iter().any(|p| {
            matches!(
                p,
                trust_cg_lower::adapter::Proof::NoOverflow { signed: true }
            )
        })
    });
    assert!(
        has_no_overflow,
        "NoOverflow proof should be attached to the add result"
    );
}

#[test]
fn bare_notnull_annotation_is_reported_but_never_synthesizes_discharge_authority() {
    let module = single_function_module(
        23,
        "forged_notnull",
        func_ty(vec![Ty::Ptr], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1))
                .with_proof(ProofAnnotation::NotNull),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
        vec![],
    );

    let (lir, proof_ctx) =
        translate_only(&module).expect("bare NotNull remains structurally valid");
    assert!(proof_ctx.synthesized_discharged.is_empty());
    assert!(
        lir.blocks
            .values()
            .flat_map(|block| &block.instructions)
            .any(|inst| { matches!(inst.opcode, Opcode::GuardNull { obligation: None }) })
    );
}

#[test]
fn clean_expr_goal_annotation_is_compatible_but_never_treated_as_evidence() {
    let goal = trust_ir::clean_expr_lowering::overflow_obligation(
        OverflowOp::AddOverflow,
        Ty::U8,
        v(0),
        v(1),
        (1, 2),
    )
    .expect("u8 overflow goal is representable");
    let module = single_function_module(
        24,
        "goal_is_not_evidence",
        func_ty(vec![Ty::U8, Ty::U8], vec![Ty::U8]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::U8), (v(1), Ty::U8)],
            body: vec![
                InstrNode::new(Inst::Overflow {
                    op: OverflowOp::AddOverflow,
                    ty: Ty::U8,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2))
                .with_result(v(3))
                .with_proof(ProofAnnotation::Goal(Box::new(goal))),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    );

    let (_lir, proof_ctx) =
        translate_only(&module).expect("Goal annotations must lower compatibly");
    assert!(proof_ctx.value_proofs.is_empty());
    assert!(proof_ctx.synthesized_discharged.is_empty());
}

// ===========================================================================
// #456: ProofAnnotation::Pure propagates through call lowering to the Bl
// ===========================================================================

/// Build a two-function module whose callee carries `ProofAnnotation::Pure`
/// and whose caller invokes it via `Inst::Call`. Returns the module.
fn build_pure_call_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("pure_call_test");
    let sig: FuncTyId = module.add_func_type(func_ty(vec![Ty::I32], vec![Ty::I32]));

    // Pure callee: return arg unchanged.
    let mut callee = TrustIrFunction::new(f(0), "pure_callee", sig, b(0));
    callee.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::I32)],
        body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
    });
    callee.proofs = vec![ProofAnnotation::Pure];

    // Caller: call the pure callee.
    let mut caller = TrustIrFunction::new(f(1), "caller", sig, b(0));
    caller.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: f(0),
                args: vec![v(0)],
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });

    module.add_function(callee);
    module.add_function(caller);
    module
}

#[test]
fn test_pure_callee_surfaces_in_lir_function() {
    let module = build_pure_call_module();
    let results = translate_module(&module).unwrap();
    assert_eq!(results.len(), 2);

    let (caller_lir, _) = results
        .iter()
        .find(|(f, _)| f.name == "caller")
        .expect("caller must be present");

    assert!(
        caller_lir.pure_callees.contains("pure_callee"),
        "adapter should record 'pure_callee' in Function::pure_callees, got {:?}",
        caller_lir.pure_callees
    );
}

#[test]
fn test_pure_callee_bl_carries_proof_pure() {
    use trust_cg_ir::ProofAnnotation as IrProof;

    let module = build_pure_call_module();
    let results = translate_module(&module).unwrap();

    let (caller_lir, _) = results
        .iter()
        .find(|(f, _)| f.name == "caller")
        .expect("caller must be present");

    let mut isel = InstructionSelector::new(caller_lir.name.clone(), caller_lir.signature.clone());
    isel.seed_value_types(&caller_lir.value_types);
    isel.seed_pure_callees(&caller_lir.pure_callees);
    isel.lower_formal_arguments(&caller_lir.signature, caller_lir.entry_block)
        .unwrap();

    let mut block_order: Vec<Block> = caller_lir.blocks.keys().copied().collect();
    block_order.sort_by_key(|b| {
        if *b == caller_lir.entry_block {
            0
        } else {
            b.0 + 1
        }
    });
    for block_id in &block_order {
        let bb = &caller_lir.blocks[block_id];
        isel.select_block_with_source_locs(*block_id, &bb.instructions, &bb.source_locs)
            .unwrap();
    }

    // Convert to canonical MachFunction so we can read MachInst.proof.
    let isel_func = isel.finalize();
    let mfunc = isel_func.to_ir_func();

    // Find the Bl to `pure_callee` and confirm it carries Some(Pure).
    let mut found_pure_bl = false;
    for block in &mfunc.blocks {
        for inst_id in &block.insts {
            let inst = &mfunc.insts[inst_id.0 as usize];
            if inst.opcode == AArch64Opcode::Bl {
                let is_pure_callee = inst.operands.iter().any(
                    |op| matches!(op, trust_cg_ir::MachOperand::Symbol(s) if s == "pure_callee"),
                );
                if is_pure_callee {
                    assert_eq!(
                        inst.proof,
                        Some(IrProof::Pure),
                        "Bl to pure_callee must carry ProofAnnotation::Pure for SROA \
                         partial-escape (#456); got {:?}",
                        inst.proof,
                    );
                    found_pure_bl = true;
                }
            }
        }
    }
    assert!(
        found_pure_bl,
        "expected a Bl to 'pure_callee' in the caller's MachFunction"
    );
}

// ===========================================================================
// Comprehensive: all new programs translate through adapter without errors
// ===========================================================================

#[test]
fn test_all_new_programs_adapter_succeeds() {
    let programs: Vec<(&str, TrustIrModule)> = vec![
        ("dispatch", build_switch()),
        ("call_through_ptr", build_call_indirect()),
        ("abs_select", build_select()),
        ("array_access", build_gep()),
        ("struct_field_in_array", build_gep_with_offset()),
        ("widen_and_narrow", build_cast_chain()),
        ("float_to_int", build_float_to_int()),
    ];

    for (name, module) in &programs {
        let result = translate_only(module);
        assert!(
            result.is_ok(),
            "{}: adapter translation failed: {:?}",
            name,
            result.err()
        );
        let (lir_func, _) = result.unwrap();
        assert_eq!(lir_func.name, *name);
        assert!(!lir_func.blocks.is_empty());
    }
}

// ===========================================================================
// Comprehensive: all new single-function programs compile through ISel
// ===========================================================================

#[test]
fn test_all_new_single_block_programs_compile() {
    let programs: Vec<(&str, TrustIrModule)> = vec![
        ("call_through_ptr", build_call_indirect()),
        ("abs_select", build_select()),
        ("array_access", build_gep()),
        ("struct_field_in_array", build_gep_with_offset()),
        ("widen_and_narrow", build_cast_chain()),
        ("float_to_int", build_float_to_int()),
    ];

    for (name, module) in &programs {
        let mfunc = compile_trust_ir_function(module);
        assert!(
            !mfunc.blocks.is_empty(),
            "{}: produced empty ISelFunction",
            name
        );
        assert!(
            total_insts(&mfunc) > 0,
            "{}: produced no machine instructions",
            name
        );
        assert!(
            has_opcode(&mfunc, AArch64Opcode::Ret),
            "{}: missing RET instruction",
            name
        );
    }
}

// ===========================================================================
// Test: Source location propagation through full pipeline
// ===========================================================================

use trust_ir::SourceSpan;

/// Build a trust_ir function with source spans on instructions, compile through
/// the full pipeline, and verify the spans appear on MachInsts.
#[test]
fn test_source_loc_end_to_end() {
    let module = single_function_module(
        0,
        "add_with_locs",
        func_ty(vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I32), (v(1), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2))
                .with_span(SourceSpan {
                    file: 0,
                    line: 10,
                    col: 5,
                }),
                InstrNode::new(Inst::Return { values: vec![v(2)] }).with_span(SourceSpan {
                    file: 0,
                    line: 11,
                    col: 1,
                }),
            ],
        }],
        vec![],
    );

    let isel_func = compile_trust_ir_function(&module);

    // Verify source_locs are present on the ISelBlock.
    let entry_block = isel_func.blocks.values().next().unwrap();
    let has_line_10 = entry_block.source_locs.iter().any(|loc| {
        *loc == Some(trust_cg_ir::SourceLoc {
            file: 0,
            line: 10,
            col: 5,
        })
    });
    assert!(
        has_line_10,
        "ISel output should carry line 10 source loc from trust_ir span"
    );

    let has_line_11 = entry_block.source_locs.iter().any(|loc| {
        *loc == Some(trust_cg_ir::SourceLoc {
            file: 0,
            line: 11,
            col: 1,
        })
    });
    assert!(
        has_line_11,
        "ISel output should carry line 11 source loc from trust_ir span"
    );

    // Verify propagation through to_ir_func().
    let ir_func = isel_func.to_ir_func();
    let ir_has_line_10 = ir_func.insts.iter().any(|inst| {
        inst.source_loc
            == Some(trust_cg_ir::SourceLoc {
                file: 0,
                line: 10,
                col: 5,
            })
    });
    assert!(
        ir_has_line_10,
        "MachInsts should carry line 10 source loc after to_ir_func()"
    );

    let ir_has_line_11 = ir_func.insts.iter().any(|inst| {
        inst.source_loc
            == Some(trust_cg_ir::SourceLoc {
                file: 0,
                line: 11,
                col: 1,
            })
    });
    assert!(
        ir_has_line_11,
        "MachInsts should carry line 11 source loc after to_ir_func()"
    );
}

/// Verify that instructions without spans get None source_loc.
#[test]
fn test_source_loc_none_for_spanless_instrs() {
    let module = single_function_module(
        0,
        "no_spans",
        func_ty(vec![Ty::I32], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I32)],
            body: vec![
                // No .with_span() — span is None.
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    );

    let isel_func = compile_trust_ir_function(&module);
    let entry_block = isel_func.blocks.values().next().unwrap();

    // All source_locs should be None.
    assert!(
        entry_block.source_locs.iter().all(|loc| loc.is_none()),
        "ISel output should have None source_locs for instructions without spans"
    );
}

// ===========================================================================
// Test: Diamond CFG with merge via block parameters (if-then-else pattern)
//
// This exercises the pattern from ty's BigToSmall/SmallToBig actions:
//   abs_diff(x: i32, y: i32) -> i32 {
//     if x > y { x - y } else { y - x }
//   }
//
// trust_ir form:
//   entry(x: i32, y: i32):
//     cond = icmp sgt x, y
//     condbr cond -> then_block(), else_block()
//   then_block():
//     diff = isub x, y
//     br merge(diff)
//   else_block():
//     diff2 = isub y, x
//     br merge(diff2)
//   merge(result: i32):
//     return result
// ===========================================================================

fn build_diamond_merge() -> TrustIrModule {
    single_function_module(
        50,
        "abs_diff",
        func_ty(vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        vec![
            // entry block: compare and branch
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I32), (v(1), Ty::I32)],
                body: vec![
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Sgt,
                        ty: Ty::I32,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::CondBr {
                        cond: v(2),
                        then_target: b(1),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            },
            // then block: x - y, branch to merge with result
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I32,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Br {
                        target: b(3),
                        args: vec![v(3)],
                    }),
                ],
            },
            // else block: y - x, branch to merge with result
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I32,
                        lhs: v(1),
                        rhs: v(0),
                    })
                    .with_result(v(4)),
                    InstrNode::new(Inst::Br {
                        target: b(3),
                        args: vec![v(4)],
                    }),
                ],
            },
            // merge block: receive result via block parameter, return it
            TrustIrBlock {
                id: b(3),
                params: vec![(v(5), Ty::I32)],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(5)] })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_diamond_merge_adapter() {
    let module = build_diamond_merge();
    let (lir_func, _) = translate_only(&module).unwrap();

    // 4 blocks: entry, then, else, merge
    assert_eq!(lir_func.blocks.len(), 4);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    // entry: ICmp + Brif = 2 instructions
    assert_eq!(entry.instructions.len(), 2);
    assert!(matches!(entry.instructions[0].opcode, Opcode::Icmp { .. }));
    assert!(matches!(entry.instructions[1].opcode, Opcode::Brif { .. }));

    // Verify merge block has exactly 1 parameter.
    // The entry block also has params (function args), so filter it out.
    let merge_block = lir_func
        .blocks
        .iter()
        .filter(|(id, _)| **id != lir_func.entry_block)
        .map(|(_, bb)| bb)
        .find(|bb| !bb.params.is_empty())
        .expect("merge block should have block parameters");
    assert_eq!(
        merge_block.params.len(),
        1,
        "merge block should have exactly 1 param"
    );

    // Verify then and else blocks each have: sub + copy + jump = 3 instructions.
    // Filter out entry (has function params) and merge (has block params).
    let branch_blocks: Vec<_> = lir_func
        .blocks
        .iter()
        .filter(|(id, bb)| **id != lir_func.entry_block && bb.params.is_empty())
        .map(|(_, bb)| bb)
        .collect();
    assert_eq!(branch_blocks.len(), 2, "should have 2 branch blocks");

    for bb in &branch_blocks {
        assert_eq!(
            bb.instructions.len(),
            3,
            "branch block should have sub + copy + jump, got {:?}",
            bb.instructions
                .iter()
                .map(|i| &i.opcode)
                .collect::<Vec<_>>()
        );
        assert!(matches!(bb.instructions[0].opcode, Opcode::Isub));
        // Copy pseudo (block-arg passing; see #417).
        assert!(matches!(bb.instructions[1].opcode, Opcode::Copy));
        assert_eq!(bb.instructions[1].args.len(), 1, "copy should have 1 arg");
        assert!(matches!(bb.instructions[2].opcode, Opcode::Jump { .. }));
    }

    // Both copies should target the same destination (the merge block param)
    let then_copy_dst = branch_blocks[0].instructions[1].results[0];
    let else_copy_dst = branch_blocks[1].instructions[1].results[0];
    assert_eq!(
        then_copy_dst, else_copy_dst,
        "both branch copies should target the same merge block parameter"
    );

    // The copy destinations should be different from the copy sources
    let then_copy_src = branch_blocks[0].instructions[1].args[0];
    let else_copy_src = branch_blocks[1].instructions[1].args[0];
    assert_ne!(
        then_copy_src, else_copy_src,
        "branch copies should use different source values"
    );
}

#[test]
fn test_diamond_merge_isel() {
    let module = build_diamond_merge();
    let mfunc = compile_trust_ir_function(&module);

    // Should have 4 blocks
    assert_eq!(
        mfunc.blocks.len(),
        4,
        "diamond merge should produce 4 ISel blocks"
    );

    // Should have comparison, conditional branch, 2 subs, and return
    assert!(
        has_opcode(&mfunc, AArch64Opcode::CmpRR),
        "Expected CMP for the comparison"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::BCond),
        "Expected B.cond for the conditional branch"
    );
    assert!(
        count_opcode(&mfunc, AArch64Opcode::SubRR) >= 2,
        "Expected at least 2 SUB instructions (then + else branches)"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Ret),
        "Expected RET instruction"
    );
}

fn build_switch_empty_edge_to_param_block() -> TrustIrModule {
    single_function_module(
        154,
        "switch_empty_edge_to_param_block",
        func_ty(vec![Ty::I32, Ty::I64], vec![Ty::I64]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I32), (v(1), Ty::I64)],
                body: vec![InstrNode::new(Inst::Switch {
                    value: v(0),
                    default: b(1),
                    default_args: vec![],
                    cases: vec![SwitchCase {
                        value: Constant::Int(1),
                        target: b(2),
                        args: vec![v(1)],
                    }],
                    exhaustive_enum_unreachable: false,
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![(v(10), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![v(10)],
                })],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![(v(20), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![v(20)],
                })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_switch_empty_edge_to_param_block_rejects_arity_mismatch() {
    let err = translate_only(&build_switch_empty_edge_to_param_block()).unwrap_err();
    assert!(
        matches!(err, AdapterError::BlockArgArityMismatch(block, 0, 1) if block == 1),
        "expected block-arg arity mismatch, got {err:?}"
    );
}

fn build_switch_block_arg_type_mismatch() -> TrustIrModule {
    single_function_module(
        155,
        "switch_block_arg_type_mismatch",
        func_ty(vec![Ty::I32, Ty::Bool], vec![Ty::I64]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I32), (v(1), Ty::Bool)],
                body: vec![InstrNode::new(Inst::Switch {
                    value: v(0),
                    default: b(1),
                    default_args: vec![v(1)],
                    cases: vec![SwitchCase {
                        value: Constant::Int(1),
                        target: b(1),
                        args: vec![v(1)],
                    }],
                    exhaustive_enum_unreachable: false,
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![(v(10), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![v(10)],
                })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_switch_block_arg_type_mismatch_rejects_wrong_arg() {
    let err = translate_only(&build_switch_block_arg_type_mismatch()).unwrap_err();
    assert!(
        matches!(err, AdapterError::BlockArgTypeMismatch(block, 0, Type::B1, Type::I64) if block == 1),
        "expected block-arg type mismatch, got {err:?}"
    );
}

fn build_switch_with_selector_and_cases(
    name: &str,
    selector_ty: Ty,
    cases: Vec<SwitchCase>,
) -> TrustIrModule {
    single_function_module(
        156,
        name,
        func_ty(vec![selector_ty.clone()], vec![]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), selector_ty)],
                body: vec![InstrNode::new(Inst::Switch {
                    value: v(0),
                    default: b(1),
                    default_args: vec![],
                    cases,
                    exhaustive_enum_unreachable: false,
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
            TrustIrBlock {
                id: b(3),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_switch_rejects_non_integer_selector_type() {
    let module = build_switch_with_selector_and_cases(
        "switch_non_integer_selector",
        Ty::F64,
        vec![SwitchCase {
            value: Constant::Int(1),
            target: b(2),
            args: vec![],
        }],
    );
    let err = translate_only(&module).unwrap_err();
    assert!(
        matches!(err, AdapterError::UnsupportedInstruction(ref msg) if msg.contains("non-integer switch selector type")),
        "expected non-integer selector rejection, got {err:?}"
    );
}

#[test]
fn test_switch_rejects_unsupported_selector_width() {
    let module = build_switch_with_selector_and_cases(
        "switch_i128_selector",
        Ty::I128,
        vec![SwitchCase {
            value: Constant::Int(1),
            target: b(2),
            args: vec![],
        }],
    );
    let err = translate_only(&module).unwrap_err();
    assert!(
        matches!(err, AdapterError::UnsupportedInstruction(ref msg) if msg.contains("unsupported switch selector width")),
        "expected unsupported selector-width rejection, got {err:?}"
    );
}

#[test]
fn test_switch_rejects_duplicate_cases_after_selector_width_normalization() {
    let module = build_switch_with_selector_and_cases(
        "switch_duplicate_i8_cases",
        Ty::I8,
        vec![
            SwitchCase {
                value: Constant::Int(-1),
                target: b(2),
                args: vec![],
            },
            SwitchCase {
                value: Constant::Int(255),
                target: b(3),
                args: vec![],
            },
        ],
    );
    let err = translate_only(&module).unwrap_err();
    assert!(
        matches!(err, AdapterError::UnsupportedInstruction(ref msg) if msg.contains("duplicate switch case value after 8-bit selector normalization")),
        "expected duplicate normalized case rejection, got {err:?}"
    );
}

#[test]
fn test_switch_rejects_non_integer_case_value() {
    let module = build_switch_with_selector_and_cases(
        "switch_float_case",
        Ty::I32,
        vec![SwitchCase {
            value: Constant::Float(1.0),
            target: b(2),
            args: vec![],
        }],
    );
    let err = translate_only(&module).unwrap_err();
    assert!(
        matches!(err, AdapterError::UnsupportedInstruction(ref msg) if msg.contains("non-integer switch case value")),
        "expected non-integer case rejection, got {err:?}"
    );
}

// ===========================================================================
// Test: Diamond CFG with CondBr block args (direct arg passing on branch)
//
// This tests the pattern where CondBr passes different values to the SAME
// merge block parameter on each edge, going through the full ISel pipeline.
// Exercises the #302 copy-block fix end-to-end.
//
// trust_ir form:
//   entry(cond: bool, x: i32, y: i32):
//     condbr cond -> merge(x), merge(y)
//   merge(result: i32):
//     return result
// ===========================================================================

fn build_condbr_merge() -> TrustIrModule {
    let mut module = TrustIrModule::new("condbr_merge");
    let ft_id = module.add_func_type(func_ty(vec![Ty::Bool, Ty::I32, Ty::I32], vec![Ty::I32]));

    let mut func = TrustIrFunction::new(f(51), "select_via_branch", ft_id, b(0));
    func.blocks = vec![
        // entry: condbr with args to same merge block
        TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), Ty::Bool), // cond
                (v(1), Ty::I32),  // x
                (v(2), Ty::I32),  // y
            ],
            body: vec![InstrNode::new(Inst::CondBr {
                cond: v(0),
                then_target: b(1),
                then_args: vec![v(1)], // pass x to merge
                else_target: b(1),
                else_args: vec![v(2)], // pass y to merge
            })],
        },
        // merge block: receives result, returns it
        TrustIrBlock {
            id: b(1),
            params: vec![(v(3), Ty::I32)],
            body: vec![InstrNode::new(Inst::Return { values: vec![v(3)] })],
        },
    ];

    module.add_function(func);
    module
}

#[test]
fn test_condbr_merge_adapter() {
    let module = build_condbr_merge();
    let (lir_func, _) = translate_only(&module).unwrap();

    // 4 blocks: entry + merge + 2 copy blocks
    assert_eq!(
        lir_func.blocks.len(),
        4,
        "expected 4 blocks (entry + merge + 2 copy blocks), got {}",
        lir_func.blocks.len()
    );
}

#[test]
fn test_condbr_merge_isel() {
    let module = build_condbr_merge();
    let mfunc = compile_trust_ir_function(&module);

    // Should have 4 blocks: entry, merge, 2 copy blocks
    assert_eq!(
        mfunc.blocks.len(),
        4,
        "condbr merge should produce 4 ISel blocks, got {}",
        mfunc.blocks.len()
    );

    assert!(
        has_opcode(&mfunc, AArch64Opcode::BCond),
        "Expected conditional branch"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Ret),
        "Expected RET instruction"
    );
    // Copy blocks should have MOV instructions for the phi copies
    assert!(
        count_opcode(&mfunc, AArch64Opcode::MovR) >= 2,
        "Expected at least 2 MOV instructions for copy blocks"
    );
}

fn build_empty_br_to_param_block() -> TrustIrModule {
    single_function_module(
        151,
        "empty_br_to_param_block",
        func_ty(vec![], vec![Ty::I64]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![],
                body: vec![InstrNode::new(Inst::Br {
                    target: b(1),
                    args: vec![],
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![(v(10), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![v(10)],
                })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_empty_br_to_param_block_rejects_arity_mismatch() {
    let err = translate_only(&build_empty_br_to_param_block()).unwrap_err();
    assert!(
        matches!(err, AdapterError::BlockArgArityMismatch(block, 0, 1) if block == 1),
        "expected block-arg arity mismatch, got {err:?}"
    );
}

fn build_empty_condbr_edge_to_param_block() -> TrustIrModule {
    single_function_module(
        152,
        "empty_condbr_edge_to_param_block",
        func_ty(vec![Ty::Bool, Ty::I64], vec![Ty::I64]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::Bool), (v(1), Ty::I64)],
                body: vec![InstrNode::new(Inst::CondBr {
                    cond: v(0),
                    then_target: b(1),
                    then_args: vec![],
                    else_target: b(2),
                    else_args: vec![v(1)],
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![(v(10), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![v(10)],
                })],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![(v(20), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![v(20)],
                })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_empty_condbr_edge_to_param_block_rejects_arity_mismatch() {
    let err = translate_only(&build_empty_condbr_edge_to_param_block()).unwrap_err();
    assert!(
        matches!(err, AdapterError::BlockArgArityMismatch(block, 0, 1) if block == 1),
        "expected block-arg arity mismatch, got {err:?}"
    );
}

fn build_ptr_bool_ptr_condbr_merge(third_arg_ty: Ty) -> TrustIrModule {
    single_function_module(
        153,
        "ptr_bool_ptr_condbr_merge",
        func_ty(
            vec![Ty::Bool, Ty::Ptr, Ty::Bool, third_arg_ty.clone(), Ty::Ptr],
            vec![Ty::Ptr],
        ),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![
                    (v(0), Ty::Bool),
                    (v(1), Ty::Ptr),
                    (v(2), Ty::Bool),
                    (v(3), third_arg_ty),
                    (v(4), Ty::Ptr),
                ],
                body: vec![InstrNode::new(Inst::CondBr {
                    cond: v(0),
                    then_target: b(1),
                    then_args: vec![v(1), v(2), v(3)],
                    else_target: b(1),
                    else_args: vec![v(4), v(2), v(4)],
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![(v(10), Ty::Ptr), (v(11), Ty::Bool), (v(12), Ty::Ptr)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![v(12)],
                })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_condbr_ptr_bool_ptr_block_args_translate_and_isel() {
    let module = build_ptr_bool_ptr_condbr_merge(Ty::Ptr);
    let (lir_func, _) = translate_only(&module).unwrap();
    assert_eq!(
        lir_func.blocks.len(),
        4,
        "expected entry, merge, and two copy blocks"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    let (then_dest, else_dest) = match &entry.instructions[0].opcode {
        Opcode::Brif {
            then_dest,
            else_dest,
            ..
        } => (*then_dest, *else_dest),
        other => panic!("expected Brif, got {other:?}"),
    };
    assert_eq!(
        lir_func.blocks[&then_dest]
            .instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::Copy))
            .count(),
        3
    );
    assert_eq!(
        lir_func.blocks[&else_dest]
            .instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::Copy))
            .count(),
        3
    );

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(mfunc.blocks.len(), 4);
    assert!(has_opcode(&mfunc, AArch64Opcode::BCond));
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

#[test]
fn test_condbr_block_arg_type_mismatch_rejects_wrong_ptr_arg() {
    let err = translate_only(&build_ptr_bool_ptr_condbr_merge(Ty::Bool)).unwrap_err();
    assert!(
        matches!(err, AdapterError::BlockArgTrustIrTypeMismatch(block, 2, Ty::Bool, Ty::Ptr) if block == 1),
        "expected trust_ir block-arg type mismatch, got {err:?}"
    );
}

fn build_call_indirect_result_block_arg_merge() -> TrustIrModule {
    let mut module = TrustIrModule::new("call_indirect_result_block_arg_merge");
    let callee_ty = module.add_func_type(func_ty(vec![], vec![Ty::I32, Ty::I64]));
    let wrapper_ty = module.add_func_type(func_ty(vec![Ty::Func(callee_ty)], vec![Ty::I64]));

    let mut func = TrustIrFunction::new(
        f(156),
        "call_indirect_result_block_arg_merge",
        wrapper_ty,
        b(0),
    );
    func.blocks = vec![
        TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Func(callee_ty))],
            body: vec![
                InstrNode::new(Inst::CallIndirect {
                    callee: v(0),
                    sig: callee_ty,
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                })
                .with_result(v(1))
                .with_result(v(2)),
                InstrNode::new(Inst::Br {
                    target: b(1),
                    args: vec![v(2)],
                }),
            ],
        },
        TrustIrBlock {
            id: b(1),
            params: vec![(v(3), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return { values: vec![v(3)] })],
        },
    ];

    module.add_function(func);
    module
}

#[test]
fn test_call_indirect_result_can_feed_block_arg_validation() {
    let module = build_call_indirect_result_block_arg_merge();
    let (lir_func, _) = translate_only(&module).unwrap();
    assert_eq!(lir_func.blocks.len(), 2);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    let call_inst = entry
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::CallIndirect))
        .expect("expected indirect call before block-arg branch");
    assert_eq!(call_inst.results.len(), 2);
    assert_eq!(
        lir_func.value_types.get(&call_inst.results[0]),
        Some(&Type::I32)
    );
    assert_eq!(
        lir_func.value_types.get(&call_inst.results[1]),
        Some(&Type::I64)
    );
    assert!(
        entry.instructions.iter().any(|inst| {
            matches!(inst.opcode, Opcode::Copy) && inst.args == vec![call_inst.results[1]]
        }),
        "expected block-arg copy from second indirect call result to merge param"
    );
}

// ===========================================================================
// tla-trust_ir integration tests (issue #339)
//
// These tests verify that trust-cg-lower handles all trust_ir instruction types
// emitted by tla-trust_ir (the TLA+ bytecode -> trust_ir lowering crate).
// ty uses i64 as its primary integer type throughout.
// ===========================================================================

// ---------------------------------------------------------------------------
// Category 1: Scalar arithmetic on i64 (Mul, SDiv, SRem)
// Add and Sub already tested above; these cover the remaining ops ty uses.
// ---------------------------------------------------------------------------

fn build_i64_mul() -> TrustIrModule {
    single_function_module(
        100,
        "i64_mul",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_i64_mul_adapter() {
    let module = build_i64_mul();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.signature.params, vec![Type::I64, Type::I64]);
    assert_eq!(lir_func.signature.returns, vec![Type::I64]);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(matches!(entry.instructions[0].opcode, Opcode::Imul));
}

#[test]
fn test_i64_mul_isel() {
    let module = build_i64_mul();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::MulRR),
        "Expected MUL instruction for i64 multiplication"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

fn build_i64_sdiv() -> TrustIrModule {
    single_function_module(
        101,
        "i64_sdiv",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_i64_sdiv_adapter() {
    let module = build_i64_sdiv();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(matches!(entry.instructions[0].opcode, Opcode::Sdiv));
}

#[test]
fn test_i64_sdiv_isel() {
    let module = build_i64_sdiv();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::SDiv),
        "Expected SDIV instruction for signed i64 division"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

fn build_i64_srem() -> TrustIrModule {
    single_function_module(
        102,
        "i64_srem",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SRem,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_i64_srem_adapter() {
    let module = build_i64_srem();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(matches!(entry.instructions[0].opcode, Opcode::Srem));
}

#[test]
fn test_i64_srem_isel() {
    let module = build_i64_srem();
    let mfunc = compile_trust_ir_function(&module);

    // SREM is lowered as: SDIV tmp, a, b; MSUB result, tmp, b, a
    assert!(
        has_opcode(&mfunc, AArch64Opcode::SDiv),
        "Expected SDIV as part of SREM lowering"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Msub),
        "Expected MSUB as part of SREM lowering (result = a - (a/b)*b)"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ---------------------------------------------------------------------------
// Category 2: ICmp with all comparison operators used by ty
// ---------------------------------------------------------------------------

fn build_icmp_variant(op: ICmpOp, name: &str, func_id: u32) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                // ZExt i1->i64 to return the boolean as an integer (ty pattern)
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: Ty::I64,
                    operand: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

fn build_pointer_icmp_variant(op: ICmpOp, name: &str, func_id: u32) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: Ty::Ptr,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: Ty::I64,
                    operand: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_icmp_eq_adapter_and_isel() {
    let module = build_icmp_variant(ICmpOp::Eq, "icmp_eq", 110);
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(&i.opcode, Opcode::Icmp { cond: IntCC::Equal }))
    );

    let mfunc = compile_trust_ir_function(&module);
    assert!(has_opcode(&mfunc, AArch64Opcode::CmpRR));
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

#[test]
fn test_icmp_ne_adapter_and_isel() {
    let module = build_icmp_variant(ICmpOp::Ne, "icmp_ne", 111);
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(entry.instructions.iter().any(|i| matches!(
        &i.opcode,
        Opcode::Icmp {
            cond: IntCC::NotEqual
        }
    )));

    let mfunc = compile_trust_ir_function(&module);
    assert!(has_opcode(&mfunc, AArch64Opcode::CmpRR));
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

#[test]
fn test_pointer_icmp_eq_ne_adapter_and_targets() {
    for (op, cond, name, func_id) in [
        (ICmpOp::Eq, IntCC::Equal, "ptr_icmp_eq", 700),
        (ICmpOp::Ne, IntCC::NotEqual, "ptr_icmp_ne", 701),
        // Unsigned pointer orderings lower as raw address comparisons too.
        (ICmpOp::Ult, IntCC::UnsignedLessThan, "ptr_icmp_ult", 703),
        (
            ICmpOp::Ule,
            IntCC::UnsignedLessThanOrEqual,
            "ptr_icmp_ule",
            704,
        ),
        (ICmpOp::Ugt, IntCC::UnsignedGreaterThan, "ptr_icmp_ugt", 705),
        (
            ICmpOp::Uge,
            IntCC::UnsignedGreaterThanOrEqual,
            "ptr_icmp_uge",
            706,
        ),
    ] {
        let module = build_pointer_icmp_variant(op, name, func_id);
        let (lir_func, _) = translate_only(&module).unwrap();

        let entry = &lir_func.blocks[&lir_func.entry_block];
        assert!(
            entry
                .instructions
                .iter()
                .any(|i| matches!(&i.opcode, Opcode::Icmp { cond: actual } if *actual == cond)),
            "pointer ICmp::{op:?} must lower as raw address Eq/Ne"
        );

        let aarch64 = compile_trust_ir_function(&module);
        assert!(has_opcode(&aarch64, AArch64Opcode::CmpRR));
        assert!(has_opcode(&aarch64, AArch64Opcode::Ret));

        let x86_64 = compile_trust_ir_function_x86_64(&module);
        assert!(
            has_x86_opcode(&x86_64, X86Opcode::CmpRR) || has_x86_opcode(&x86_64, X86Opcode::CmpRI)
        );
        assert!(has_x86_opcode(&x86_64, X86Opcode::Ret));
    }
}

#[test]
fn test_pointer_icmp_signed_relational_fails_closed() {
    // Unsigned pointer orderings are now supported (address comparison), but a
    // SIGNED ordering over pointers stays fail-closed: an address is unsigned.
    let module = build_pointer_icmp_variant(ICmpOp::Slt, "ptr_icmp_slt_fail_closed", 702);
    let err = translate_only(&module).expect_err("signed relational pointer ICmp must fail closed");
    assert!(
        err.to_string().contains("pointer-like"),
        "unexpected pointer relational ICmp diagnostic: {err}"
    );
}

#[test]
fn test_icmp_slt_adapter_and_isel() {
    let module = build_icmp_variant(ICmpOp::Slt, "icmp_slt", 112);
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(entry.instructions.iter().any(|i| matches!(
        &i.opcode,
        Opcode::Icmp {
            cond: IntCC::SignedLessThan
        }
    )));

    let mfunc = compile_trust_ir_function(&module);
    assert!(has_opcode(&mfunc, AArch64Opcode::CmpRR));
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

#[test]
fn test_icmp_sle_adapter_and_isel() {
    let module = build_icmp_variant(ICmpOp::Sle, "icmp_sle", 113);
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(entry.instructions.iter().any(|i| matches!(
        &i.opcode,
        Opcode::Icmp {
            cond: IntCC::SignedLessThanOrEqual
        }
    )));

    let mfunc = compile_trust_ir_function(&module);
    assert!(has_opcode(&mfunc, AArch64Opcode::CmpRR));
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

#[test]
fn test_icmp_sge_adapter_and_isel() {
    let module = build_icmp_variant(ICmpOp::Sge, "icmp_sge", 114);
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(entry.instructions.iter().any(|i| matches!(
        &i.opcode,
        Opcode::Icmp {
            cond: IntCC::SignedGreaterThanOrEqual
        }
    )));

    let mfunc = compile_trust_ir_function(&module);
    assert!(has_opcode(&mfunc, AArch64Opcode::CmpRR));
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ---------------------------------------------------------------------------
// Category 3: Boolean logic (And, Or, Xor, Not)
// ty uses these for TLA+ logical operators: /\, \/, ~
// ---------------------------------------------------------------------------

fn build_bool_and() -> TrustIrModule {
    single_function_module(
        120,
        "bool_and",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_bool_and_adapter() {
    let module = build_bool_and();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(matches!(entry.instructions[0].opcode, Opcode::Band));
}

#[test]
fn test_bool_and_isel() {
    let module = build_bool_and();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::AndRR),
        "Expected AND instruction for bitwise AND"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

fn build_bool_or() -> TrustIrModule {
    single_function_module(
        121,
        "bool_or",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_bool_or_adapter() {
    let module = build_bool_or();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(matches!(entry.instructions[0].opcode, Opcode::Bor));
}

#[test]
fn test_bool_or_isel() {
    let module = build_bool_or();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::OrrRR),
        "Expected ORR instruction for bitwise OR"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

fn build_bool_xor() -> TrustIrModule {
    single_function_module(
        122,
        "bool_xor",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_bool_xor_adapter() {
    let module = build_bool_xor();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(matches!(entry.instructions[0].opcode, Opcode::Bxor));
}

#[test]
fn test_bool_xor_isel() {
    let module = build_bool_xor();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::EorRR),
        "Expected EOR instruction for bitwise XOR"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

/// TLA+ negation (~) is lowered as UnOp::Not which maps to Bnot (MVN on AArch64)
fn build_bool_not() -> TrustIrModule {
    single_function_module(
        123,
        "bool_not",
        func_ty(vec![Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::UnOp {
                    op: UnOp::Not,
                    ty: Ty::I64,
                    operand: v(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_bool_not_adapter() {
    let module = build_bool_not();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    assert!(matches!(entry.instructions[0].opcode, Opcode::Bnot));
}

#[test]
fn test_bool_not_isel() {
    let module = build_bool_not();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::OrnRR),
        "Expected ORN (MVN) instruction for bitwise NOT"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ---------------------------------------------------------------------------
// Category 4: Casts - ZExt (i1->i64) for boolean promotion
// ty compares i64 values producing i1, then ZExts back to i64
// ---------------------------------------------------------------------------

fn build_zext_i1_to_i64() -> TrustIrModule {
    single_function_module(
        130,
        "zext_bool_to_i64",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                // Compare: result is i1
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                // ZExt i1 -> i64 (boolean to integer promotion)
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: Ty::I64,
                    operand: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_zext_i1_to_i64_adapter() {
    let module = build_zext_i1_to_i64();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(entry.instructions.len() >= 3);
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(&i.opcode, Opcode::Icmp { cond: IntCC::Equal }))
    );
    assert!(entry.instructions.iter().any(|i| matches!(
        &i.opcode,
        Opcode::Uextend {
            from_ty: Type::B1,
            to_ty: Type::I64
        }
    )));
}

#[test]
fn test_zext_i1_to_i64_isel() {
    let module = build_zext_i1_to_i64();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::CmpRR),
        "Expected CMP for comparison"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

/// Trunc i64 -> i1 (integer to boolean demotion, for feeding CondBr)
fn build_trunc_i64_to_i1() -> TrustIrModule {
    single_function_module(
        131,
        "trunc_i64_to_bool",
        func_ty(vec![Ty::I64], vec![Ty::I64]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I64)],
                body: vec![
                    // Trunc i64 -> Bool (take low bit)
                    InstrNode::new(Inst::Cast {
                        op: CastOp::Trunc,
                        src_ty: Ty::I64,
                        dst_ty: Ty::Bool,
                        operand: v(0),
                    })
                    .with_result(v(1)),
                    // Use the bool in a CondBr
                    InstrNode::new(Inst::CondBr {
                        cond: v(1),
                        then_target: b(1),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(1),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Return { values: vec![v(2)] }),
                ],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            },
        ],
        vec![],
    )
}

#[test]
fn test_trunc_i64_to_i1_adapter() {
    let module = build_trunc_i64_to_i1();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.blocks.len(), 3);
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(&i.opcode, Opcode::Trunc { to_ty: Type::B1 }))
    );
}

#[test]
fn test_trunc_i64_to_i1_isel() {
    let module = build_trunc_i64_to_i1();
    let mfunc = compile_trust_ir_function(&module);

    assert!(has_opcode(&mfunc, AArch64Opcode::BCond));
    assert!(
        count_opcode(&mfunc, AArch64Opcode::Ret) >= 2,
        "Expected 2 RET instructions (then + else)"
    );
}

// ---------------------------------------------------------------------------
// Category 5: Large i64 constants
// ty needs large constants for set cardinalities, model checking bounds, etc.
// ---------------------------------------------------------------------------

fn build_large_i64_const() -> TrustIrModule {
    single_function_module(
        140,
        "large_const",
        func_ty(vec![], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0x7FFF_FFFF_FFFF_FFFF), // i64::MAX
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_large_i64_const_adapter() {
    let module = build_large_i64_const();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions.len(), 2);
    match &entry.instructions[0].opcode {
        Opcode::Iconst { ty, imm } => {
            assert_eq!(*ty, Type::I64);
            assert_eq!(*imm, 0x7FFF_FFFF_FFFF_FFFF_i64);
        }
        other => panic!("Expected Iconst, got {:?}", other),
    }
}

#[test]
fn test_large_i64_const_isel() {
    let module = build_large_i64_const();
    let mfunc = compile_trust_ir_function(&module);

    // Large constants may use MOVZ+MOVK, or an hw0 MOVN seed followed by MOVK
    // repairs when the complement is cheaper.
    assert!(
        invalid_movz_immediates(&mfunc).is_empty(),
        "large constant materialization must not emit invalid MOVZ immediates"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Movz)
            || has_opcode(&mfunc, AArch64Opcode::Movn)
            || has_opcode(&mfunc, AArch64Opcode::Movk),
        "Expected move-wide materialization for large constant"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

fn build_negative_i64_const() -> TrustIrModule {
    single_function_module(
        141,
        "neg_const",
        func_ty(vec![], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(-1),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_negative_i64_const_adapter() {
    let module = build_negative_i64_const();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    match &entry.instructions[0].opcode {
        Opcode::Iconst { ty, imm } => {
            assert_eq!(*ty, Type::I64);
            assert_eq!(*imm, -1_i64);
        }
        other => panic!("Expected Iconst, got {:?}", other),
    }
}

#[test]
fn test_negative_i64_const_isel() {
    let module = build_negative_i64_const();
    let mfunc = compile_trust_ir_function(&module);

    // -1 can be materialized via MOVN
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Movn)
            || has_opcode(&mfunc, AArch64Opcode::MovI)
            || has_opcode(&mfunc, AArch64Opcode::Movz),
        "Expected MOV variant for negative constant"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ---------------------------------------------------------------------------
// Category 6: Memory operations on i64 arrays (ty's primary data structure)
// TLA+ functions/sequences are typically i64 arrays accessed via GEP
// ---------------------------------------------------------------------------

/// Load an i64 element from an array: arr[idx]
fn build_i64_array_load() -> TrustIrModule {
    single_function_module(
        150,
        "i64_array_load",
        func_ty(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(0),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(2),
                    volatile: false,
                    align: None,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_i64_array_load_adapter() {
    let module = build_i64_array_load();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(lir_func.signature.params, vec![Type::I64, Type::I64]);
    assert_eq!(lir_func.signature.returns, vec![Type::I64]);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    // GEP expands to: Iconst(8) + Imul(idx, 8) + Iadd(base, offset)
    // Then: Load + Return
    let has_load = entry.instructions.iter().any(|i| {
        matches!(
            &i.opcode,
            Opcode::Load {
                ty: Type::I64,
                align: None
            }
        )
    });
    assert!(has_load, "Expected Load of type I64 after GEP");
}

#[test]
fn test_i64_array_load_isel() {
    let module = build_i64_array_load();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::LdrRI) || has_opcode(&mfunc, AArch64Opcode::LdrRO),
        "Expected LDR for i64 array load"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

/// Store an i64 element into an array: arr[idx] = val
fn build_i64_array_store() -> TrustIrModule {
    single_function_module(
        151,
        "i64_array_store",
        func_ty(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(0),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(3),
                    value: v(2),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_i64_array_store_adapter() {
    let module = build_i64_array_store();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    let has_store = entry
        .instructions
        .iter()
        .any(|i| matches!(&i.opcode, Opcode::Store { .. }));
    assert!(has_store, "Expected Store opcode for array write");
}

#[test]
fn test_i64_array_store_isel() {
    let module = build_i64_array_store();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::StrRI) || has_opcode(&mfunc, AArch64Opcode::StrRO),
        "Expected STR for i64 array store"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ---------------------------------------------------------------------------
// Category 7: Function calls to extern "C" runtime helpers
// ty calls into runtime helpers for set operations, string handling, etc.
// ---------------------------------------------------------------------------

fn build_extern_call() -> TrustIrModule {
    let mut module = TrustIrModule::new("extern_call_test");
    let helper_sig = module.add_func_type(func_ty(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]));
    let main_sig = module.add_func_type(func_ty(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]));

    // External function (minimal stub -- just returns its second argument)
    let mut helper = TrustIrFunction::new(f(0), "ty_runtime_set_card", helper_sig, b(0));
    helper.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        body: vec![InstrNode::new(Inst::Return { values: vec![v(1)] })],
    });

    // Main function that calls the helper
    let mut main_func = TrustIrFunction::new(f(1), "count_elements", main_sig, b(0));
    main_func.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: f(0),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![v(2)] }),
        ],
    });

    module.add_function(helper);
    module.add_function(main_func);
    module
}

#[test]
fn test_extern_call_adapter() {
    let module = build_extern_call();
    let results = translate_module(&module).unwrap();

    // Should have 2 functions (helper declaration + caller)
    assert!(!results.is_empty(), "Should translate at least the caller");

    // Find the caller function
    let caller = results.iter().find(|(f, _)| f.name == "count_elements");
    assert!(caller.is_some(), "Should have translated count_elements");

    let (caller_func, _) = caller.unwrap();
    let entry = &caller_func.blocks[&caller_func.entry_block];
    let has_call = entry.instructions.iter().any(|i| {
        matches!(
            &i.opcode,
            Opcode::Call { name } if name == "ty_runtime_set_card"
        )
    });
    assert!(has_call, "Expected Call to ty_runtime_set_card");
}

// ---------------------------------------------------------------------------
// Category 8: Select (conditional value without branching)
// Already tested above (test_select), but add i64 variant for ty
// ---------------------------------------------------------------------------

fn build_i64_select() -> TrustIrModule {
    single_function_module(
        160,
        "i64_select",
        func_ty(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64), (v(2), Ty::I64)],
            body: vec![
                // Compare first two args
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(3)),
                // Select between them based on comparison
                InstrNode::new(Inst::Select {
                    ty: Ty::I64,
                    cond: v(3),
                    then_val: v(0),
                    else_val: v(1),
                })
                .with_result(v(4)),
                InstrNode::new(Inst::Return { values: vec![v(4)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_i64_select_adapter() {
    let module = build_i64_select();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];
    let has_select = entry
        .instructions
        .iter()
        .any(|i| matches!(&i.opcode, Opcode::Select { .. }));
    assert!(
        has_select,
        "Expected Select opcode for i64 conditional select"
    );
}

#[test]
fn test_i64_select_isel() {
    let module = build_i64_select();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::CmpRR),
        "Expected CMP for the comparison"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::Csel),
        "Expected CSEL for i64 conditional select"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ---------------------------------------------------------------------------
// Category 9: Alloca for local stack variables
// ty uses stack allocation for local variables in action functions
// ---------------------------------------------------------------------------

fn build_alloca_usage() -> TrustIrModule {
    single_function_module(
        170,
        "alloca_local",
        func_ty(vec![Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                // Alloca for an i64 local
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(v(1)),
                // Store into it
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(1),
                    value: v(0),
                    volatile: false,
                    align: None,
                }),
                // Load back
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(1),
                    volatile: false,
                    align: None,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_alloca_adapter() {
    let module = build_alloca_usage();
    let (lir_func, _) = translate_only(&module).unwrap();

    // Alloca should create a stack slot
    assert!(
        !lir_func.stack_slots.is_empty(),
        "Expected at least one stack slot from Alloca"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    // Should have: StackAddr + Store + Load + Return
    let has_stack_addr = entry
        .instructions
        .iter()
        .any(|i| matches!(&i.opcode, Opcode::StackAddr { .. }));
    assert!(has_stack_addr, "Expected StackAddr for alloca result");
}

#[test]
fn test_alloca_isel() {
    let module = build_alloca_usage();
    let mfunc = compile_trust_ir_function(&module);

    assert!(
        has_opcode(&mfunc, AArch64Opcode::LdrRI) || has_opcode(&mfunc, AArch64Opcode::LdrRO),
        "Expected LDR for loading from alloca"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::StrRI) || has_opcode(&mfunc, AArch64Opcode::StrRO),
        "Expected STR for storing to alloca"
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

// ---------------------------------------------------------------------------
// Comprehensive: all tla-trust_ir test programs compile through full pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_all_tla_trust_ir_programs_adapter_succeeds() {
    let programs: Vec<(&str, TrustIrModule)> = vec![
        ("i64_mul", build_i64_mul()),
        ("i64_sdiv", build_i64_sdiv()),
        ("i64_srem", build_i64_srem()),
        ("bool_and", build_bool_and()),
        ("bool_or", build_bool_or()),
        ("bool_xor", build_bool_xor()),
        ("bool_not", build_bool_not()),
        ("zext_bool_to_i64", build_zext_i1_to_i64()),
        ("trunc_i64_to_bool", build_trunc_i64_to_i1()),
        ("large_const", build_large_i64_const()),
        ("neg_const", build_negative_i64_const()),
        ("i64_array_load", build_i64_array_load()),
        ("i64_array_store", build_i64_array_store()),
        ("i64_select", build_i64_select()),
        ("alloca_local", build_alloca_usage()),
    ];

    for (name, module) in &programs {
        let result = translate_only(module);
        assert!(
            result.is_ok(),
            "{}: adapter translation failed: {:?}",
            name,
            result.err()
        );
        let (lir_func, _) = result.unwrap();
        assert_eq!(lir_func.name, *name);
        assert!(!lir_func.blocks.is_empty());
    }
}

#[test]
fn test_all_tla_trust_ir_programs_isel_succeeds() {
    let programs: Vec<(&str, TrustIrModule)> = vec![
        ("i64_mul", build_i64_mul()),
        ("i64_sdiv", build_i64_sdiv()),
        ("i64_srem", build_i64_srem()),
        ("bool_and", build_bool_and()),
        ("bool_or", build_bool_or()),
        ("bool_xor", build_bool_xor()),
        ("bool_not", build_bool_not()),
        ("zext_bool_to_i64", build_zext_i1_to_i64()),
        ("trunc_i64_to_bool", build_trunc_i64_to_i1()),
        ("large_const", build_large_i64_const()),
        ("neg_const", build_negative_i64_const()),
        ("i64_array_load", build_i64_array_load()),
        ("i64_array_store", build_i64_array_store()),
        ("i64_select", build_i64_select()),
        ("alloca_local", build_alloca_usage()),
    ];

    for (name, module) in &programs {
        let mfunc = compile_trust_ir_function(module);
        assert!(
            !mfunc.blocks.is_empty(),
            "{}: produced empty ISelFunction",
            name
        );
        assert!(
            total_insts(&mfunc) > 0,
            "{}: produced no machine instructions",
            name
        );
        assert!(
            has_opcode(&mfunc, AArch64Opcode::Ret),
            "{}: missing RET instruction",
            name
        );
    }
}

// ===========================================================================
// Test: Multi-value diamond merge (ty DieHard-like pattern)
//
// Exercises the pattern where MULTIPLE output values flow through a diamond
// CFG and merge via MULTIPLE block parameters. This is the pattern ty's
// DieHard actions produce when an IF-THEN-ELSE updates several state
// variables at once.
//
// trust_ir form:
//   entry(x: i32, y: i32, cond: bool):
//     condbr cond -> then_block(), else_block()
//   then_block():
//     a = iadd x, y
//     b = isub x, y
//     br merge(a, b)
//   else_block():
//     c = isub y, x
//     d = iadd y, x
//     br merge(c, d)
//   merge(p1: i32, p2: i32):
//     result = iadd p1, p2
//     return result
// ===========================================================================

fn build_multi_value_diamond() -> TrustIrModule {
    single_function_module(
        60,
        "multi_val_diamond",
        func_ty(vec![Ty::I32, Ty::I32, Ty::Bool], vec![Ty::I32]),
        vec![
            // entry block: compare and branch
            TrustIrBlock {
                id: b(0),
                params: vec![
                    (v(0), Ty::I32),  // x
                    (v(1), Ty::I32),  // y
                    (v(2), Ty::Bool), // cond
                ],
                body: vec![InstrNode::new(Inst::CondBr {
                    cond: v(2),
                    then_target: b(1),
                    then_args: vec![],
                    else_target: b(2),
                    else_args: vec![],
                })],
            },
            // then block: compute two values, branch to merge
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I32,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(10)),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I32,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(11)),
                    InstrNode::new(Inst::Br {
                        target: b(3),
                        args: vec![v(10), v(11)],
                    }),
                ],
            },
            // else block: compute two different values, branch to merge
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I32,
                        lhs: v(1),
                        rhs: v(0),
                    })
                    .with_result(v(20)),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I32,
                        lhs: v(1),
                        rhs: v(0),
                    })
                    .with_result(v(21)),
                    InstrNode::new(Inst::Br {
                        target: b(3),
                        args: vec![v(20), v(21)],
                    }),
                ],
            },
            // merge block: use both merged values
            TrustIrBlock {
                id: b(3),
                params: vec![(v(30), Ty::I32), (v(31), Ty::I32)],
                body: vec![
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I32,
                        lhs: v(30),
                        rhs: v(31),
                    })
                    .with_result(v(32)),
                    InstrNode::new(Inst::Return {
                        values: vec![v(32)],
                    }),
                ],
            },
        ],
        vec![],
    )
}

#[test]
fn test_multi_value_diamond_adapter() {
    let module = build_multi_value_diamond();
    let (lir_func, _) = translate_only(&module).unwrap();

    // 4 blocks: entry, then, else, merge (Br copies are inline)
    assert_eq!(
        lir_func.blocks.len(),
        4,
        "expected 4 blocks, got {}",
        lir_func.blocks.len()
    );

    // Verify merge block has exactly 2 parameters
    let merge_block = lir_func
        .blocks
        .iter()
        .filter(|(id, _)| **id != lir_func.entry_block)
        .map(|(_, bb)| bb)
        .find(|bb| bb.params.len() == 2)
        .expect("merge block should have 2 block parameters");
    assert_eq!(merge_block.params.len(), 2);

    // Each branch block: 2 ops + 2 copies + 1 jump = 5 instructions
    let branch_blocks: Vec<_> = lir_func
        .blocks
        .iter()
        .filter(|(id, bb)| **id != lir_func.entry_block && bb.params.is_empty())
        .map(|(_, bb)| bb)
        .collect();
    assert_eq!(branch_blocks.len(), 2, "should have 2 branch blocks");

    for bb in &branch_blocks {
        assert_eq!(
            bb.instructions.len(),
            5,
            "branch block should have 2 ops + 2 copies + jump, got {:?}",
            bb.instructions
                .iter()
                .map(|i| &i.opcode)
                .collect::<Vec<_>>()
        );
        // First two are BinOps (Iadd or Isub)
        // Next two are copies (single-arg Iadd)
        assert_eq!(bb.instructions[2].args.len(), 1, "copy should have 1 arg");
        assert_eq!(bb.instructions[3].args.len(), 1, "copy should have 1 arg");
        // Last is Jump
        assert!(matches!(bb.instructions[4].opcode, Opcode::Jump { .. }));
    }

    // Both branch blocks' copies should target the same merge block params
    let then_dst0 = branch_blocks[0].instructions[2].results[0];
    let then_dst1 = branch_blocks[0].instructions[3].results[0];
    let else_dst0 = branch_blocks[1].instructions[2].results[0];
    let else_dst1 = branch_blocks[1].instructions[3].results[0];
    assert_eq!(
        then_dst0, else_dst0,
        "first param copies should target same Value"
    );
    assert_eq!(
        then_dst1, else_dst1,
        "second param copies should target same Value"
    );
    assert_ne!(
        then_dst0, then_dst1,
        "the two params should be different Values"
    );
}

#[test]
fn test_multi_value_diamond_isel() {
    let module = build_multi_value_diamond();
    let mfunc = compile_trust_ir_function(&module);

    // Should have 4 blocks
    assert_eq!(
        mfunc.blocks.len(),
        4,
        "multi-value diamond should produce 4 ISel blocks"
    );

    // Should have conditional branch, arithmetic, and return
    assert!(has_opcode(&mfunc, AArch64Opcode::BCond), "Expected B.cond");
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret), "Expected RET");
    assert!(
        count_opcode(&mfunc, AArch64Opcode::AddRR) >= 2,
        "Expected at least 2 ADD instructions"
    );
    assert!(
        count_opcode(&mfunc, AArch64Opcode::SubRR) >= 2,
        "Expected at least 2 SUB instructions"
    );
    // Copy instructions for block params
    assert!(
        count_opcode(&mfunc, AArch64Opcode::MovR) >= 4,
        "Expected at least 4 MOV instructions for 2 params x 2 branches"
    );
}

// ===========================================================================
// Test: CondBr with multi-value args to same merge block
//
// Like the #302 test but with MULTIPLE block parameters, exercising the
// pattern where CondBr directly passes multiple different values to the
// same merge block from each edge.
//
// trust_ir form:
//   entry(cond: bool, a: i32, b: i32, c: i32, d: i32):
//     condbr cond -> merge(a, b), merge(c, d)
//   merge(p1: i32, p2: i32):
//     result = iadd p1, p2
//     return result
// ===========================================================================

fn build_condbr_multi_value_merge() -> TrustIrModule {
    let mut module = TrustIrModule::new("condbr_multi_val");
    let ft_id = module.add_func_type(func_ty(
        vec![Ty::Bool, Ty::I32, Ty::I32, Ty::I32, Ty::I32],
        vec![Ty::I32],
    ));

    let mut func = TrustIrFunction::new(f(61), "select_pair", ft_id, b(0));
    func.blocks = vec![
        // entry: condbr with multi-value args to same merge block
        TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), Ty::Bool), // cond
                (v(1), Ty::I32),  // a
                (v(2), Ty::I32),  // b
                (v(3), Ty::I32),  // c
                (v(4), Ty::I32),  // d
            ],
            body: vec![InstrNode::new(Inst::CondBr {
                cond: v(0),
                then_target: b(1),
                then_args: vec![v(1), v(2)], // pass (a, b) to merge
                else_target: b(1),
                else_args: vec![v(3), v(4)], // pass (c, d) to merge
            })],
        },
        // merge block: receives two params, combines them
        TrustIrBlock {
            id: b(1),
            params: vec![(v(10), Ty::I32), (v(11), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Return {
                    values: vec![v(12)],
                }),
            ],
        },
    ];

    module.add_function(func);
    module
}

#[test]
fn test_condbr_multi_value_merge_adapter() {
    let module = build_condbr_multi_value_merge();
    let (lir_func, _) = translate_only(&module).unwrap();

    // 4 blocks: entry + merge + 2 copy blocks
    assert_eq!(
        lir_func.blocks.len(),
        4,
        "expected 4 blocks (entry + merge + 2 copy blocks), got {}",
        lir_func.blocks.len()
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    // Entry should have only the Brif
    assert_eq!(entry.instructions.len(), 1);
    match &entry.instructions[0].opcode {
        Opcode::Brif {
            then_dest,
            else_dest,
            ..
        } => {
            assert_ne!(then_dest, else_dest, "copy blocks should be different");

            let then_block = &lir_func.blocks[then_dest];
            // 2 copies + 1 jump = 3 instructions
            assert_eq!(
                then_block.instructions.len(),
                3,
                "then-copy block should have 2 copies + jump"
            );

            let else_block = &lir_func.blocks[else_dest];
            assert_eq!(
                else_block.instructions.len(),
                3,
                "else-copy block should have 2 copies + jump"
            );

            // Both copy blocks jump to the same merge block
            let then_jump = match &then_block.instructions[2].opcode {
                Opcode::Jump { dest } => *dest,
                _ => panic!("expected Jump"),
            };
            let else_jump = match &else_block.instructions[2].opcode {
                Opcode::Jump { dest } => *dest,
                _ => panic!("expected Jump"),
            };
            assert_eq!(then_jump, else_jump, "both should jump to merge");

            // Copy destinations should match: then[0].dst == else[0].dst (param p1)
            // and then[1].dst == else[1].dst (param p2)
            assert_eq!(
                then_block.instructions[0].results[0], else_block.instructions[0].results[0],
                "first param copies should target same Value (p1)"
            );
            assert_eq!(
                then_block.instructions[1].results[0], else_block.instructions[1].results[0],
                "second param copies should target same Value (p2)"
            );

            // Copy sources should differ (a,b vs c,d)
            assert_ne!(
                then_block.instructions[0].args[0], else_block.instructions[0].args[0],
                "first copies should use different sources"
            );
            assert_ne!(
                then_block.instructions[1].args[0], else_block.instructions[1].args[0],
                "second copies should use different sources"
            );
        }
        other => panic!("expected Brif, got {:?}", other),
    }
}

#[test]
fn test_condbr_multi_value_merge_isel() {
    let module = build_condbr_multi_value_merge();
    let mfunc = compile_trust_ir_function(&module);

    // Should have 4 blocks
    assert_eq!(
        mfunc.blocks.len(),
        4,
        "condbr multi-value merge should produce 4 ISel blocks, got {}",
        mfunc.blocks.len()
    );

    assert!(has_opcode(&mfunc, AArch64Opcode::BCond), "Expected B.cond");
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret), "Expected RET");
    // 4 MOV instructions total: 2 per copy block
    assert!(
        count_opcode(&mfunc, AArch64Opcode::MovR) >= 4,
        "Expected at least 4 MOV for 2 params x 2 edges, got {}",
        count_opcode(&mfunc, AArch64Opcode::MovR)
    );
}

// ===========================================================================
// Test: ty DieHard-style i64 IF-THEN-ELSE with multi-variable state writes
//
// This exercises the EXACT pattern ty's BigToSmall / SmallToBig actions
// produce: an i64 IF-THEN-ELSE where BOTH branches write MULTIPLE state
// variables, and the merge block consumes all of them (via block parameters).
//
// Pattern:
//   pour_big_to_small(big: i64, small: i64, big_cap: i64, small_cap: i64)
//                                               -> (new_big, new_small)
//
//   IF big >= (small_cap - small) THEN
//     -- pouring saturates small jug
//     new_big   = big - (small_cap - small)
//     new_small = small_cap
//   ELSE
//     -- all of big fits in small
//     new_big   = 0
//     new_small = small + big
//
// We return new_big + new_small as a proxy for successful multi-value merge.
//
// trust_ir form (i64 everywhere, mirrors ty usage):
//   entry(big, small, big_cap, small_cap: i64):
//     room     = isub small_cap, small
//     cond     = icmp sge big, room
//     condbr cond -> saturate(...), fits(...)
//   saturate():
//     new_big   = isub big, room
//     new_small = small_cap
//     br merge(new_big, new_small)
//   fits():
//     new_big   = 0
//     new_small = iadd small, big
//     br merge(new_big, new_small)
//   merge(final_big: i64, final_small: i64):
//     result = iadd final_big, final_small
//     return result
// ===========================================================================

fn build_diehard_big_to_small() -> TrustIrModule {
    single_function_module(
        70,
        "pour_big_to_small",
        func_ty(vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![
            // entry: compute room, compare, branch
            TrustIrBlock {
                id: b(0),
                params: vec![
                    (v(0), Ty::I64), // big
                    (v(1), Ty::I64), // small
                    (v(2), Ty::I64), // big_cap (unused, mirrors ty signature)
                    (v(3), Ty::I64), // small_cap
                ],
                body: vec![
                    // room = small_cap - small
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I64,
                        lhs: v(3),
                        rhs: v(1),
                    })
                    .with_result(v(4)),
                    // cond = big >= room
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Sge,
                        ty: Ty::I64,
                        lhs: v(0),
                        rhs: v(4),
                    })
                    .with_result(v(5)),
                    // branch
                    InstrNode::new(Inst::CondBr {
                        cond: v(5),
                        then_target: b(1),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            },
            // saturate: new_big = big - room; new_small = small_cap
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I64,
                        lhs: v(0),
                        rhs: v(4),
                    })
                    .with_result(v(10)),
                    // new_small = small_cap -> use a MoveValue proxy via
                    // Const(small_cap) is not possible; pass small_cap value
                    // directly as merge arg since no additional computation.
                    InstrNode::new(Inst::Br {
                        target: b(3),
                        args: vec![v(10), v(3)], // (new_big, small_cap)
                    }),
                ],
            },
            // fits: new_big = 0; new_small = small + big
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(v(20)),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: v(1),
                        rhs: v(0),
                    })
                    .with_result(v(21)),
                    InstrNode::new(Inst::Br {
                        target: b(3),
                        args: vec![v(20), v(21)], // (0, small+big)
                    }),
                ],
            },
            // merge: sum the two new state values and return
            TrustIrBlock {
                id: b(3),
                params: vec![(v(30), Ty::I64), (v(31), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: v(30),
                        rhs: v(31),
                    })
                    .with_result(v(32)),
                    InstrNode::new(Inst::Return {
                        values: vec![v(32)],
                    }),
                ],
            },
        ],
        vec![],
    )
}

#[test]
fn test_diehard_big_to_small_adapter() {
    let module = build_diehard_big_to_small();
    let (lir_func, _) = translate_only(&module).unwrap();

    // 4 blocks: entry, saturate, fits, merge
    assert_eq!(
        lir_func.blocks.len(),
        4,
        "DieHard i64 IF-THEN-ELSE should produce 4 LIR blocks, got {}",
        lir_func.blocks.len()
    );

    // Signature should propagate i64 parameters and return
    assert_eq!(
        lir_func.signature.params,
        vec![Type::I64, Type::I64, Type::I64, Type::I64]
    );
    assert_eq!(lir_func.signature.returns, vec![Type::I64]);

    // Each branch arm must have its own copy sequence (no unified copies
    // hoisted out to the entry block). Verify by looking at the non-entry,
    // non-merge blocks' instruction layout.
    let merge_block = lir_func
        .blocks
        .iter()
        .filter(|(id, _)| **id != lir_func.entry_block)
        .map(|(_, bb)| bb)
        .find(|bb| bb.params.len() == 2)
        .expect("merge block should have 2 i64 block parameters");
    assert_eq!(merge_block.params[0].1, Type::I64);
    assert_eq!(merge_block.params[1].1, Type::I64);

    // Post-SSA (block-parameter-form) correctness invariants:
    //
    // 1. Every non-block-parameter Value is defined at most once across the
    //    function. Block parameters may be the destination of COPY
    //    instructions in multiple predecessor blocks — that is the standard
    //    block-parameter SSA deconstruction form and is NOT an SSA violation.
    // 2. A merge-block parameter Value must never be the result of an
    //    instruction INSIDE the merge block itself (block params can only be
    //    written by predecessor copies).
    // 3. Within each single predecessor edge's copy sequence, each block
    //    parameter must be written at most ONCE. Writing the same merge-param
    //    twice from one edge is the bug reported in #365 ("invalid SSA
    //    references when both branches write to the same output variable").

    let merge_param_values: std::collections::HashSet<_> =
        merge_block.params.iter().map(|(v, _)| *v).collect();

    // Invariant 1: non-param defs unique across the function.
    let mut non_param_defs: std::collections::HashMap<trust_cg_lower::instructions::Value, usize> =
        std::collections::HashMap::new();
    for bb in lir_func.blocks.values() {
        for inst in &bb.instructions {
            for r in &inst.results {
                if !merge_param_values.contains(r) {
                    let n = non_param_defs.entry(*r).or_insert(0);
                    *n += 1;
                    assert!(
                        *n == 1,
                        "SSA violation: non-param Value {:?} defined {} times (opcode {:?})",
                        r,
                        n,
                        inst.opcode
                    );
                }
            }
        }
    }

    // Invariant 2: merge-block body does not write merge-param Values.
    for inst in &merge_block.instructions {
        for r in &inst.results {
            assert!(
                !merge_param_values.contains(r),
                "merge block param {:?} written by instruction in merge block (opcode {:?})",
                r,
                inst.opcode
            );
        }
    }

    // Invariant 3: each predecessor edge writes each merge-param at most once.
    for (bid, bb) in &lir_func.blocks {
        let mut per_edge_writes: std::collections::HashMap<
            trust_cg_lower::instructions::Value,
            usize,
        > = std::collections::HashMap::new();
        for inst in &bb.instructions {
            for r in &inst.results {
                if merge_param_values.contains(r) {
                    *per_edge_writes.entry(*r).or_insert(0) += 1;
                }
            }
        }
        for (v, n) in per_edge_writes {
            assert!(
                n == 1,
                "merge param {:?} written {} times on edge from block {:?} (expected <=1)",
                v,
                n,
                bid
            );
        }
    }
}

#[test]
fn test_diehard_big_to_small_isel() {
    let module = build_diehard_big_to_small();
    let mfunc = compile_trust_ir_function(&module);

    assert_eq!(
        mfunc.blocks.len(),
        4,
        "DieHard ISel should produce 4 machine blocks, got {}",
        mfunc.blocks.len()
    );

    assert!(has_opcode(&mfunc, AArch64Opcode::BCond), "Expected B.cond");
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret), "Expected RET");
    // At least one SUB (room, new_big in saturate) and one ADD (small+big in fits)
    assert!(
        count_opcode(&mfunc, AArch64Opcode::SubRR) >= 2,
        "Expected at least 2 SUB instructions"
    );
    assert!(
        count_opcode(&mfunc, AArch64Opcode::AddRR) >= 2,
        "Expected at least 2 ADD instructions (final merge + fits)"
    );
    // Copies for the 2 params x 2 edges
    assert!(
        count_opcode(&mfunc, AArch64Opcode::MovR) >= 4,
        "Expected at least 4 MOV for 2 params x 2 edges, got {}",
        count_opcode(&mfunc, AArch64Opcode::MovR)
    );
}

// ===========================================================================
// Test: Parallel-copy swap detection via back-edge argument permutation
//
// This is the classic parallel-copy correctness test. A loop back-edge
// passes its own header's parameters in SWAPPED order:
//
//   header(a, b):
//     ... use a, b ...
//     cond = ...
//     condbr cond -> header(b, a) {back}, exit(a, b)
//
// Under SEQUENTIAL copies (a = b; b = a), the second copy reads `a` AFTER
// it has been overwritten to the old `b`, yielding b = b instead of b = a.
//
// The correct lowering is a parallel copy: detect the cycle and insert a
// temp, e.g.:
//     tmp = a; a = b; b = tmp;
//
// This test asserts the structural property that the emitted copy sequence
// for a swap edge does NOT expose the sequential-overwrite miscompile. We
// check that either:
//   (a) a fresh temporary Value is introduced (cycle-break insertion), or
//   (b) the copy order is such that no destination of an earlier copy is
//       read as source by a later copy in the SAME edge.
// ===========================================================================

fn build_back_edge_swap() -> TrustIrModule {
    single_function_module(
        71,
        "swap_back_edge",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![
            // entry: br header(x, y)
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
                body: vec![InstrNode::new(Inst::Br {
                    target: b(1),
                    args: vec![v(0), v(1)],
                })],
            },
            // header(a, b): compute cond, condbr header(b, a) | exit
            TrustIrBlock {
                id: b(1),
                params: vec![(v(2), Ty::I64), (v(3), Ty::I64)],
                body: vec![
                    // cond = a > 0  (to ensure loop eventually terminates
                    // in an abstract sense — we only care about structure)
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(v(4)),
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Sgt,
                        ty: Ty::I64,
                        lhs: v(2),
                        rhs: v(4),
                    })
                    .with_result(v(5)),
                    InstrNode::new(Inst::CondBr {
                        cond: v(5),
                        then_target: b(1),           // back-edge
                        then_args: vec![v(3), v(2)], // SWAP: pass (b, a)
                        else_target: b(2),
                        else_args: vec![v(2)],
                    }),
                ],
            },
            // exit(result): return result
            TrustIrBlock {
                id: b(2),
                params: vec![(v(6), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(6)] })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_back_edge_swap_parallel_copy_correctness() {
    let module = build_back_edge_swap();
    let (lir_func, _) = translate_only(&module).unwrap();

    // Find the back-edge copy block (jumps back to header, which is the only
    // non-entry block with 2 params).
    let header_block_id_and_params: Vec<_> = lir_func
        .blocks
        .iter()
        .filter(|(id, bb)| **id != lir_func.entry_block && bb.params.len() == 2)
        .map(|(id, bb)| (*id, bb.params.iter().map(|(v, _)| *v).collect::<Vec<_>>()))
        .collect();
    assert_eq!(
        header_block_id_and_params.len(),
        1,
        "expected exactly one loop header"
    );
    let (header_id, header_params) = &header_block_id_and_params[0];
    let header_param_a = header_params[0];
    let header_param_b = header_params[1];

    // The back-edge copy block is the one that:
    //   - has no block params
    //   - ends in Jump { dest: header_id }
    //   - contains copies whose DESTINATIONS are the header's parameters
    let back_edge_copy_block = lir_func
        .blocks
        .values()
        .find(|bb| {
            bb.params.is_empty()
                && bb
                    .instructions
                    .iter()
                    .any(|i| matches!(i.opcode, Opcode::Jump { dest } if dest == *header_id))
                && bb.instructions.iter().any(|i| {
                    !i.results.is_empty()
                        && (i.results[0] == header_param_a || i.results[0] == header_param_b)
                })
        })
        .expect("should find a back-edge copy block that jumps to header");

    // Collect the in-order (source, dest) copy pairs before the terminator.
    let copies: Vec<(
        trust_cg_lower::instructions::Value,
        trust_cg_lower::instructions::Value,
    )> = back_edge_copy_block
        .instructions
        .iter()
        .filter(|i| !matches!(i.opcode, Opcode::Jump { .. }))
        .map(|i| (i.args[0], i.results[0]))
        .collect();

    assert!(
        copies.len() >= 2,
        "expected at least 2 copies on the swap back-edge, got {}",
        copies.len()
    );

    // Parallel-copy correctness invariant (semantic):
    //
    // A correct lowering of `br header(b, a)` from `header(a, b)` must
    // ensure that, AFTER the full copy sequence, the header's first
    // parameter holds the ORIGINAL value of `b` and the second parameter
    // holds the ORIGINAL value of `a`. Under the previous naive sequential
    // emission, the swap was silently miscompiled (both params ended up
    // holding the same value).
    //
    // We simulate the copy sequence with a symbolic register file:
    //   - Each original Value starts holding its own symbolic value.
    //   - Each copy (src, dst) sets the file's "contents at dst" to the
    //     CURRENT contents at src.
    //   - After all copies, read the merge-param Values and check they
    //     contain the correct swapped originals.
    use std::collections::HashMap;
    let mut reg_file: HashMap<
        trust_cg_lower::instructions::Value,
        trust_cg_lower::instructions::Value,
    > = HashMap::new();
    for (src, dst) in &copies {
        // Ensure src and dst have an entry (initialised to their own Value
        // if not yet seen — that represents the "original" symbolic value).
        reg_file.entry(*src).or_insert(*src);
        reg_file.entry(*dst).or_insert(*dst);
        let val = *reg_file.get(src).unwrap();
        reg_file.insert(*dst, val);
    }

    // Expected post-state: header_param_a holds the ORIGINAL source that the
    // trust_ir back-edge passed as the first arg, which is the entry block's
    // second param (header_param_b is the ORIGINAL second param mapped from
    // v(3), i.e. Value(3)). But map_value may produce arbitrary Values, so
    // we deduce the expectation from the trust_ir: the first arg of the back
    // edge's CondBr.then_args is ValueId(3), which is header's second
    // parameter. So after the copies, header_param_a (the first merge param)
    // must hold the value that was originally at header_param_b.
    assert_eq!(
        reg_file.get(&header_param_a).copied(),
        Some(header_param_b),
        "swap miscompile: header's first param should hold the original second param's value, got {:?}",
        reg_file.get(&header_param_a)
    );
    assert_eq!(
        reg_file.get(&header_param_b).copied(),
        Some(header_param_a),
        "swap miscompile: header's second param should hold the original first param's value, got {:?}",
        reg_file.get(&header_param_b)
    );
}

// ===========================================================================
// Test: 3-way rotation parallel copy (a<-b, b<-c, c<-a)
//
// This is the generalised version of the back-edge swap test. A loop
// back-edge passes (b, c, a) to header(a, b, c), forcing a 3-cycle in the
// parallel-copy graph. The scheduler must insert exactly one temp to break
// the cycle, then emit the remaining copies in a safe order.
//
// trust_ir form:
//   entry(x, y, z: i64):
//     br header(x, y, z)
//   header(a, b, c: i64):
//     cond = a > 0
//     condbr cond -> header(b, c, a), exit(a)
//   exit(result):
//     return result
// ===========================================================================

fn build_three_way_rotation() -> TrustIrModule {
    single_function_module(
        72,
        "rotate_back_edge",
        func_ty(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![
            // entry: br header(x, y, z)
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I64), (v(1), Ty::I64), (v(2), Ty::I64)],
                body: vec![InstrNode::new(Inst::Br {
                    target: b(1),
                    args: vec![v(0), v(1), v(2)],
                })],
            },
            // header(a, b, c): condbr back with rotation or exit
            TrustIrBlock {
                id: b(1),
                params: vec![(v(3), Ty::I64), (v(4), Ty::I64), (v(5), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(v(6)),
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Sgt,
                        ty: Ty::I64,
                        lhs: v(3),
                        rhs: v(6),
                    })
                    .with_result(v(7)),
                    InstrNode::new(Inst::CondBr {
                        cond: v(7),
                        then_target: b(1),
                        then_args: vec![v(4), v(5), v(3)], // ROTATE: (b, c, a)
                        else_target: b(2),
                        else_args: vec![v(3)],
                    }),
                ],
            },
            // exit(result)
            TrustIrBlock {
                id: b(2),
                params: vec![(v(8), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(8)] })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_three_way_rotation_parallel_copy_correctness() {
    let module = build_three_way_rotation();
    let (lir_func, _) = translate_only(&module).unwrap();

    // Find the header block (non-entry, 3 params).
    let header_info: Vec<_> = lir_func
        .blocks
        .iter()
        .filter(|(id, bb)| **id != lir_func.entry_block && bb.params.len() == 3)
        .map(|(id, bb)| (*id, bb.params.iter().map(|(v, _)| *v).collect::<Vec<_>>()))
        .collect();
    assert_eq!(header_info.len(), 1);
    let (header_id, header_params) = &header_info[0];
    let pa = header_params[0];
    let pb = header_params[1];
    let pc = header_params[2];

    // Find the back-edge copy block: jumps to header AND writes at least
    // one of the header params.
    let back_edge_copy_block = lir_func
        .blocks
        .values()
        .find(|bb| {
            bb.params.is_empty()
                && bb
                    .instructions
                    .iter()
                    .any(|i| matches!(i.opcode, Opcode::Jump { dest } if dest == *header_id))
                && bb.instructions.iter().any(|i| {
                    !i.results.is_empty()
                        && (i.results[0] == pa || i.results[0] == pb || i.results[0] == pc)
                })
        })
        .expect("should find back-edge copy block");

    let copies: Vec<(
        trust_cg_lower::instructions::Value,
        trust_cg_lower::instructions::Value,
    )> = back_edge_copy_block
        .instructions
        .iter()
        .filter(|i| !matches!(i.opcode, Opcode::Jump { .. }))
        .map(|i| (i.args[0], i.results[0]))
        .collect();

    // Symbolically execute the copy sequence and verify the post-state
    // matches the intended rotation.
    use std::collections::HashMap;
    let mut reg_file: HashMap<
        trust_cg_lower::instructions::Value,
        trust_cg_lower::instructions::Value,
    > = HashMap::new();
    for (src, dst) in &copies {
        reg_file.entry(*src).or_insert(*src);
        reg_file.entry(*dst).or_insert(*dst);
        let val = *reg_file.get(src).unwrap();
        reg_file.insert(*dst, val);
    }

    // Expected: pa <- original pb, pb <- original pc, pc <- original pa.
    assert_eq!(
        reg_file.get(&pa).copied(),
        Some(pb),
        "rotation miscompile: pa should hold original pb, got {:?}",
        reg_file.get(&pa)
    );
    assert_eq!(
        reg_file.get(&pb).copied(),
        Some(pc),
        "rotation miscompile: pb should hold original pc, got {:?}",
        reg_file.get(&pb)
    );
    assert_eq!(
        reg_file.get(&pc).copied(),
        Some(pa),
        "rotation miscompile: pc should hold original pa, got {:?}",
        reg_file.get(&pc)
    );
}

// ===========================================================================
// Test: Non-cyclic dependent copies require topological reordering
//
// This is distinct from the full 3-cycle rotation test above because it
// stresses ONLY the scheduler's ready-list ordering logic (no cycle, so
// no temp-variable insertion). A naive sequential emitter would miscompile
// this — the scheduler must reorder the copies.
//
// Pattern: loop back-edge carrying `(a, a, b)` into `header(a, b, c)`.
// This produces copy pairs:
//   (map_value(a_src) -> map_value(a_param))    -- self-copy of `a`, dropped
//   (map_value(a_src) -> map_value(b_param))    -- b <- a
//   (map_value(b_src) -> map_value(c_param))    -- c <- b
// After the self-copy drop, we have pending pairs [(a, b), (b, c)].
//   * Naive sequential order would emit `b = a` first, destroying the
//     original `b` value, then emit `c = b` which reads the NEW b (=a).
//     WRONG: c should receive the ORIGINAL b.
//   * Correct parallel scheduler detects that `b` is a source of another
//     pending copy, defers (a -> b), emits `c = b` first, then `b = a`.
//
// No cycle exists (the dependency graph is a DAG: a depends on nothing,
// b depends on a, c depends on b). So this test fails before any
// cycle-breaking code runs — it exercises the ready-list reordering.
//
// trust_ir form:
//   entry(x, y, z):
//     br header(x, y, z)
//   header(a, b, c):
//     if a > 0 {
//       br header(a, a, b)     -- chain copies: (a, a, b) into (a, b, c)
//     } else {
//       br exit(a)
//     }
//   exit(r):
//     return r
// ===========================================================================

fn build_chain_reorder() -> TrustIrModule {
    single_function_module(
        73,
        "chain_reorder",
        func_ty(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I64), (v(1), Ty::I64), (v(2), Ty::I64)],
                body: vec![InstrNode::new(Inst::Br {
                    target: b(1),
                    args: vec![v(0), v(1), v(2)],
                })],
            },
            // header(a, b, c): cond-branch back with chain-copy, or exit
            TrustIrBlock {
                id: b(1),
                params: vec![
                    (v(3), Ty::I64), // a
                    (v(4), Ty::I64), // b
                    (v(5), Ty::I64), // c
                ],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(v(6)),
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Sgt,
                        ty: Ty::I64,
                        lhs: v(3),
                        rhs: v(6),
                    })
                    .with_result(v(7)),
                    InstrNode::new(Inst::CondBr {
                        cond: v(7),
                        then_target: b(1),
                        then_args: vec![v(3), v(3), v(4)], // CHAIN: (a, a, b)
                        else_target: b(2),
                        else_args: vec![v(3)],
                    }),
                ],
            },
            // exit(r)
            TrustIrBlock {
                id: b(2),
                params: vec![(v(8), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(8)] })],
            },
        ],
        vec![],
    )
}

#[test]
fn test_chain_reorder_parallel_copy() {
    let module = build_chain_reorder();
    let (lir_func, _) = translate_only(&module).unwrap();

    // Find the header block (non-entry, 3 params).
    let header_info: Vec<_> = lir_func
        .blocks
        .iter()
        .filter(|(id, bb)| **id != lir_func.entry_block && bb.params.len() == 3)
        .map(|(id, bb)| (*id, bb.params.iter().map(|(v, _)| *v).collect::<Vec<_>>()))
        .collect();
    assert_eq!(header_info.len(), 1);
    let (header_id, header_params) = &header_info[0];
    let pa = header_params[0];
    let pb = header_params[1];
    let pc = header_params[2];

    // Find the back-edge copy block (jumps to header AND writes at least
    // one header param).
    let back_edge_copy_block = lir_func
        .blocks
        .values()
        .find(|bb| {
            bb.params.is_empty()
                && bb
                    .instructions
                    .iter()
                    .any(|i| matches!(i.opcode, Opcode::Jump { dest } if dest == *header_id))
                && bb.instructions.iter().any(|i| {
                    !i.results.is_empty()
                        && (i.results[0] == pa || i.results[0] == pb || i.results[0] == pc)
                })
        })
        .expect("should find back-edge copy block");

    let copies: Vec<(
        trust_cg_lower::instructions::Value,
        trust_cg_lower::instructions::Value,
    )> = back_edge_copy_block
        .instructions
        .iter()
        .filter(|i| !matches!(i.opcode, Opcode::Jump { .. }))
        .map(|i| (i.args[0], i.results[0]))
        .collect();

    // Non-triviality guard: at least one emitted copy's dst must equal
    // another emitted copy's src. Otherwise the test is vacuous (a naive
    // sequential emitter would also pass) and should not be trusted.
    let srcs: std::collections::HashSet<_> = copies.iter().map(|(s, _)| *s).collect();
    let has_overlap = copies.iter().any(|(_, d)| srcs.contains(d));
    assert!(
        has_overlap,
        "test is vacuous — no copy dst appears as another copy's src. \
         copies = {:?}",
        copies
    );

    // Symbolically execute the copy sequence and verify the post-state
    // matches the intended chain: (a, b, c) <- (a, a, b), i.e.
    //   new_pa = orig_pa (self-copy elided)
    //   new_pb = orig_pa
    //   new_pc = orig_pb
    use std::collections::HashMap;
    let mut reg_file: HashMap<
        trust_cg_lower::instructions::Value,
        trust_cg_lower::instructions::Value,
    > = HashMap::new();
    for (src, dst) in &copies {
        reg_file.entry(*src).or_insert(*src);
        reg_file.entry(*dst).or_insert(*dst);
        let val = *reg_file.get(src).unwrap();
        reg_file.insert(*dst, val);
    }

    assert_eq!(
        reg_file.get(&pa).copied().unwrap_or(pa),
        pa,
        "chain miscompile: pa (self-copy) should preserve original pa"
    );
    assert_eq!(
        reg_file.get(&pb).copied(),
        Some(pa),
        "chain miscompile: pb should hold original pa, got {:?}",
        reg_file.get(&pb)
    );
    assert_eq!(
        reg_file.get(&pc).copied(),
        Some(pb),
        "chain miscompile: pc should hold original pb (NOT the new pb=pa), \
         got {:?}",
        reg_file.get(&pc)
    );
}

// ===========================================================================
// Category 10: tla-trust_ir coverage — Inst::Overflow with checked-arithmetic idiom
//
// tla-trust_ir (see ~/ty/crates/tla-trust_ir/src/lower/arithmetic.rs:16-117) lowers
// every TLA+ integer Add/Sub/Mul/Neg as:
//     (value, overflow_flag) = Inst::Overflow { op, ty, lhs, rhs }
//     CondBr overflow_flag -> overflow_error_block, continue_block
// The correctness of TLA+ runtime overflow detection depends on the adapter
// producing a real overflow flag from the hardware.
//
// Issue #339 and reports/2026-04-18-tla-trust_ir-coverage.md document that the
// current adapter hardcodes the flag to Iconst { imm: 0 } (silent miscompile).
// The tests below are PINNING TESTS — they assert current adapter behavior
// verbatim so that any future fix to the overflow flag requires updating the
// assertion in the same diff, preventing a silent regression and making the
// fix visible.
//
// When the overflow-flag bug is fixed, these tests will fail by design and
// must be updated alongside the fix.
// ===========================================================================

fn build_tla_checked_add() -> TrustIrModule {
    // Mirror lower_checked_binary_overflow from tla-trust_ir:
    //   entry(lhs: i64, rhs: i64):
    //     (result, flag) = Inst::Overflow { AddOverflow, lhs, rhs }
    //     CondBr flag -> overflow_block, continue_block
    //   overflow_block: Return 0
    //   continue_block: Return result
    single_function_module(
        200,
        "tla_checked_add",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::Overflow {
                        op: OverflowOp::AddOverflow,
                        ty: Ty::I64,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(2)) // value
                    .with_result(v(3)), // overflow flag
                    InstrNode::new(Inst::CondBr {
                        cond: v(3),
                        then_target: b(1),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(v(4)),
                    InstrNode::new(Inst::Return { values: vec![v(4)] }),
                ],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(2)] })],
            },
        ],
        vec![],
    )
}

fn build_checked_overflow_module(op: OverflowOp, ty: Ty, name: &str) -> TrustIrModule {
    single_function_module(
        201,
        name,
        func_ty(vec![ty.clone(), ty.clone()], vec![ty.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), ty.clone()), (v(1), ty.clone())],
            body: vec![
                InstrNode::new(Inst::Overflow {
                    op,
                    ty,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2))
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_tla_checked_add_adapter_translates() {
    // Documents that the adapter at least translates the Inst::Overflow
    // instruction without raising UnsupportedInstruction.
    let module = build_tla_checked_add();
    let (lir_func, _) = translate_only(&module).expect("adapter must translate Inst::Overflow");
    assert_eq!(lir_func.name, "tla_checked_add");
    assert!(
        lir_func.blocks.len() >= 3,
        "expected at least 3 blocks (entry, overflow, continue), got {}",
        lir_func.blocks.len()
    );
}

#[test]
fn test_u64_overflow_adapter_emits_unsigned_checked_opcodes() {
    let cases = [
        (
            OverflowOp::AddOverflow,
            Opcode::CheckedUadd,
            Opcode::CheckedSadd,
            "u64_checked_add",
        ),
        (
            OverflowOp::SubOverflow,
            Opcode::CheckedUsub,
            Opcode::CheckedSsub,
            "u64_checked_sub",
        ),
        (
            OverflowOp::MulOverflow,
            Opcode::CheckedUmul,
            Opcode::CheckedSmul,
            "u64_checked_mul",
        ),
    ];

    for (op, expected_unsigned, unexpected_signed, name) in cases {
        let module = build_checked_overflow_module(op, Ty::U64, name);
        let (lir_func, _) = translate_only(&module).unwrap();
        let entry = &lir_func.blocks[&lir_func.entry_block];

        let unsigned_count = entry
            .instructions
            .iter()
            .filter(|i| {
                std::mem::discriminant(&i.opcode) == std::mem::discriminant(&expected_unsigned)
            })
            .count();
        assert_eq!(
            unsigned_count, 1,
            "{name} must emit exactly one unsigned checked opcode; entry: {:#?}",
            entry.instructions
        );
        assert!(
            !entry.instructions.iter().any(|i| {
                std::mem::discriminant(&i.opcode) == std::mem::discriminant(&unexpected_signed)
            }),
            "{name} must not route Ty::U64 through the signed checked opcode"
        );
    }
}

#[test]
fn test_tla_checked_add_overflow_flag_is_real() {
    // Regression test for issue #339 Finding 1 and #474.
    //
    // History:
    //   * Originally (#339 Finding 1): adapter emitted `Iconst B1 imm 0` as
    //     the overflow flag — a silent miscompile.
    //   * First fix: adapter expanded `Inst::Overflow { AddOverflow }` to
    //     a bit-pattern overflow check using Bxor/Bnot/Band + Icmp Slt.
    //   * Second fix (#474): for I64, the adapter now emits a single
    //     `Opcode::CheckedSadd` LIR op that ISel lowers directly to the
    //     canonical AArch64 ADDS+CSET VS idiom. The bit-pattern path is
    //     retained only for I8/I16/I32 where the flag-setting idiom is
    //     not yet wired up.
    //
    // This test asserts the post-#474 I64 behavior:
    //   * Exactly one `Opcode::CheckedSadd` instruction is emitted.
    //   * It has two args (lhs, rhs) and two results (value, overflow_b1).
    //   * No `Iadd`, `Bxor`, or `Icmp { cond: SignedLessThan }` remains —
    //     those would indicate regression back to the bit-pattern lowering.
    //   * The bogus `Iconst B1 imm 0` is still absent (guards against the
    //     original #339 miscompile pattern).
    let module = build_tla_checked_add();
    let (lir_func, _) = translate_only(&module).unwrap();

    let entry = &lir_func.blocks[&lir_func.entry_block];

    // Exactly one CheckedSadd must appear for this I64 fixture.
    let checked_sadds: Vec<&Instruction> = entry
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::CheckedSadd))
        .collect();
    assert_eq!(
        checked_sadds.len(),
        1,
        "expected exactly one CheckedSadd for an I64 overflow add, got {}. \
         Entry instructions: {:#?}",
        checked_sadds.len(),
        entry.instructions,
    );
    let checked = checked_sadds[0];
    assert_eq!(
        checked.args.len(),
        2,
        "CheckedSadd must take [lhs, rhs] args; got {} args",
        checked.args.len()
    );
    assert_eq!(
        checked.results.len(),
        2,
        "CheckedSadd must produce [value, overflow_b1] results; got {} results",
        checked.results.len()
    );

    // Bit-pattern leftovers from the pre-#474 lowering must NOT be present.
    let has_iadd = entry
        .instructions
        .iter()
        .any(|i| matches!(i.opcode, Opcode::Iadd));
    assert!(
        !has_iadd,
        "I64 overflow add must not produce a bare Iadd after #474 — \
         the native CheckedSadd op subsumes it. Regression to bit-pattern lowering?"
    );
    let has_bxor = entry
        .instructions
        .iter()
        .any(|i| matches!(i.opcode, Opcode::Bxor));
    assert!(
        !has_bxor,
        "I64 overflow add must not produce Bxor after #474 — native flag \
         idiom doesn't need the XOR chain. Regression to bit-pattern lowering?"
    );
    let has_icmp_slt = entry.instructions.iter().any(|i| {
        matches!(
            &i.opcode,
            Opcode::Icmp {
                cond: IntCC::SignedLessThan
            }
        )
    });
    assert!(
        !has_icmp_slt,
        "I64 overflow add must not produce Icmp SignedLessThan after #474 — \
         overflow is derived from NZCV.V via CSET VS, not a signed compare."
    );

    // The bogus Iconst { ty: B1, imm: 0 } from the original #339 miscompile
    // must remain absent. CheckedSadd is a single op that can't be constant-
    // folded away at adapter time, so this is a belt-and-suspenders check.
    let has_bogus_zero_flag = entry.instructions.iter().any(|i| {
        matches!(
            &i.opcode,
            Opcode::Iconst {
                ty: Type::B1,
                imm: 0
            }
        )
    });
    assert!(
        !has_bogus_zero_flag,
        "Regression: adapter re-introduced Iconst B1 imm 0 as the overflow flag."
    );
}

// ===========================================================================
// Category 11: tla-trust_ir coverage — Alloca { count: Some(..) } for aggregates
//
// tla-trust_ir allocates sets/sequences/tuples/records via
//     let n = Const { ty: I32, value: Constant::Int(count) };
//     alloc = Alloca { ty: I64, count: Some(n), align: None }
// (see ~/ty/crates/tla-trust_ir/src/lower/mod.rs:920-936 and set_ops.rs).
//
// Issue #339 and reports/2026-04-18-tla-trust_ir-coverage.md document that the
// current adapter ignores `count` and always produces an 8-byte stack slot.
// For a 10-element set literal this produces silent buffer overrun when the
// 2nd+ elements are stored.
//
// The test below is a PINNING TEST — it captures the current slot size so
// any future fix that honors `count` will require updating the assertion.
// ===========================================================================

fn build_tla_aggregate_alloca() -> TrustIrModule {
    // Allocate 10 i64 slots, store the parameter into slot 5, load it back.
    // Mirrors the set/sequence/tuple literal pattern in tla-trust_ir.
    single_function_module(
        210,
        "tla_aggregate_alloca",
        func_ty(vec![Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                // count = 10
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(10),
                })
                .with_result(v(1)),
                // alloca 10 * i64
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(v(1)),
                    align: None,
                })
                .with_result(v(2)),
                // idx = 5
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(5),
                })
                .with_result(v(3)),
                // ptr = GEP v2[5]
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(2),
                    indices: vec![v(3)],
                    inbounds: false,
                })
                .with_result(v(4)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(4),
                    value: v(0),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(4),
                    align: None,
                    volatile: false,
                })
                .with_result(v(5)),
                InstrNode::new(Inst::Return { values: vec![v(5)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_tla_aggregate_alloca_adapter_translates() {
    let module = build_tla_aggregate_alloca();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate Alloca { count: Some(..) }");
    assert!(
        !lir_func.stack_slots.is_empty(),
        "expected at least one stack slot from Alloca"
    );
}

#[test]
fn test_tla_aggregate_alloca_slot_size_is_count_times_element_bytes() {
    // Regression test for issue #339 Finding 2 — formerly a PINNING test
    // that asserted the adapter ignored the `count` field and allocated
    // only 8 bytes. The fix constant-folds a `Some(vid)` count whose
    // producer is an `Inst::Const`, multiplies by element size, and
    // requests that many bytes from the stack slot allocator.
    //
    // The trust_ir fixture allocates `count = 10` I64 elements, so the slot
    // must be 10 * 8 = 80 bytes, with 8-byte alignment.
    let module = build_tla_aggregate_alloca();
    let (lir_func, _) = translate_only(&module).unwrap();

    assert_eq!(
        lir_func.stack_slots.len(),
        1,
        "expected exactly one stack slot from the Alloca"
    );
    let slot = &lir_func.stack_slots[0];
    assert_eq!(
        slot.size, 80,
        "expected size = 10 (count) * 8 (sizeof I64) = 80 bytes. \
         If this assertion fails, the `count` folding regressed."
    );
    assert_eq!(
        slot.align, 8,
        "I64 alloca must retain 8-byte alignment regardless of count"
    );
}

fn build_tla_bounded_dynamic_alloca_from_loaded_count() -> TrustIrModule {
    // Dynamic-looking count path for the #520 escape hatch:
    //   count_slot = alloca i64
    //   store 4 -> count_slot
    //   count = load count_slot
    //   agg = alloca i64, count
    //   store 4 aggregate fields at constant indices [0,1,2,3]
    //
    // The count is not a direct Inst::Const producer anymore, but the actual
    // aggregate footprint is still statically visible from the bounded GEP
    // pattern. That is the narrow TY unblocker we want.
    single_function_module(
        211,
        "tla_bounded_dynamic_alloca_from_loaded_count",
        func_ty(vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), Ty::I64),
                (v(1), Ty::I64),
                (v(2), Ty::I64),
                (v(3), Ty::I64),
            ],
            body: vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(4),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(10),
                    value: v(11),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(10),
                    align: None,
                    volatile: false,
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(v(12)),
                    align: None,
                })
                .with_result(v(20)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                })
                .with_result(v(30)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(1),
                })
                .with_result(v(31)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(2),
                })
                .with_result(v(32)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(3),
                })
                .with_result(v(33)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(30)],
                    inbounds: false,
                })
                .with_result(v(40)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(40),
                    value: v(0),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(31)],
                    inbounds: false,
                })
                .with_result(v(41)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(41),
                    value: v(1),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(32)],
                    inbounds: false,
                })
                .with_result(v(42)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(42),
                    value: v(2),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(33)],
                    inbounds: false,
                })
                .with_result(v(43)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(43),
                    value: v(3),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(41),
                    align: None,
                    volatile: false,
                })
                .with_result(v(50)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(43),
                    align: None,
                    volatile: false,
                })
                .with_result(v(51)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(50),
                    rhs: v(51),
                })
                .with_result(v(52)),
                InstrNode::new(Inst::Return {
                    values: vec![v(52)],
                }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_tla_bounded_dynamic_alloca_from_loaded_count_adapter() {
    let module = build_tla_bounded_dynamic_alloca_from_loaded_count();
    let (lir_func, _) = translate_only(&module)
        .expect("bounded-use inference should translate the loaded-count alloca");

    assert_eq!(
        lir_func.stack_slots.len(),
        2,
        "expected count-slot + aggregate-slot"
    );
    assert_eq!(
        lir_func.stack_slots[1].size, 32,
        "bounded-use inference should size the aggregate slot from 4 observed i64 elements"
    );
    assert_eq!(
        lir_func.stack_slots[1].allocation,
        StackSlotAllocationKind::Fixed,
        "bounded-use inference must keep using fixed stack-slot metadata"
    );
    assert_eq!(
        lir_func.stack_slots[1].align, 8,
        "bounded-use inference must preserve i64 alignment"
    );
}

#[test]
fn test_tla_bounded_dynamic_alloca_from_loaded_count_isel() {
    let module = build_tla_bounded_dynamic_alloca_from_loaded_count();
    let mfunc = compile_trust_ir_function_with_stack_slots(&module);

    assert_eq!(
        mfunc.stack_slots.len(),
        2,
        "expected count-slot + aggregate-slot to survive ISel"
    );
    assert_eq!(
        mfunc.stack_slots[1].size, 32,
        "bounded-use inference should preserve the 4-element aggregate slot through ISel"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::StrRI) || has_opcode(&mfunc, AArch64Opcode::StrRO),
        "expected STR for bounded aggregate stores"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::LdrRI) || has_opcode(&mfunc, AArch64Opcode::LdrRO),
        "expected LDR for bounded aggregate readbacks"
    );
}

fn build_tla_bounded_dynamic_alloca_via_direct_callee() -> TrustIrModule {
    let mut module = TrustIrModule::new("tla_bounded_dynamic_alloca_via_direct_callee");
    let callee_ty = module.add_func_type(func_ty(vec![Ty::Ptr], vec![Ty::I64]));
    let mut callee = TrustIrFunction::new(f(300), "tla_record_sum2", callee_ty, b(0));
    callee.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(3),
                align: None,
                volatile: false,
            })
            .with_result(v(4)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(0),
                indices: vec![v(2)],
                inbounds: false,
            })
            .with_result(v(5)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(5),
                align: None,
                volatile: false,
            })
            .with_result(v(6)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(4),
                rhs: v(6),
            })
            .with_result(v(7)),
            InstrNode::new(Inst::Return { values: vec![v(7)] }),
        ],
    }];

    let caller_ty = module.add_func_type(func_ty(
        vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        vec![Ty::I64],
    ));
    let mut caller = TrustIrFunction::new(f(301), "tla_record_build_then_sum2", caller_ty, b(0));
    caller.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![
            (v(0), Ty::I64),
            (v(1), Ty::I64),
            (v(2), Ty::I64),
            (v(3), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(4),
            })
            .with_result(v(11)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: v(10),
                value: v(11),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(10),
                align: None,
                volatile: false,
            })
            .with_result(v(12)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(12)),
                align: None,
            })
            .with_result(v(20)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(30)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(31)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(2),
            })
            .with_result(v(32)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(3),
            })
            .with_result(v(33)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(20),
                indices: vec![v(30)],
                inbounds: false,
            })
            .with_result(v(40)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: v(40),
                value: v(0),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(20),
                indices: vec![v(31)],
                inbounds: false,
            })
            .with_result(v(41)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: v(41),
                value: v(1),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(20),
                indices: vec![v(32)],
                inbounds: false,
            })
            .with_result(v(42)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: v(42),
                value: v(2),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(20),
                indices: vec![v(33)],
                inbounds: false,
            })
            .with_result(v(43)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: v(43),
                value: v(3),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::Call {
                callee: f(300),
                args: vec![v(20)],
            })
            .with_result(v(50)),
            InstrNode::new(Inst::Return {
                values: vec![v(50)],
            }),
        ],
    }];

    module.add_function(callee);
    module.add_function(caller);
    module
}

#[test]
fn test_tla_bounded_dynamic_alloca_via_direct_callee_adapter() {
    let module = build_tla_bounded_dynamic_alloca_via_direct_callee();
    let results = translate_module(&module)
        .expect("direct-callee bounded-use inference should translate the loaded-count alloca");

    assert_eq!(results.len(), 2, "expected callee + caller translation");
    let (caller_func, _) = &results[1];
    assert_eq!(caller_func.name, "tla_record_build_then_sum2");
    assert_eq!(
        caller_func.stack_slots.len(),
        2,
        "expected count-slot + aggregate-slot in caller"
    );
    assert_eq!(
        caller_func.stack_slots[1].size, 32,
        "direct-callee bounded-use inference should size the aggregate slot from 4 observed i64 elements"
    );
    assert_eq!(
        caller_func.stack_slots[1].align, 8,
        "direct-callee bounded-use inference must preserve i64 alignment"
    );

    let entry = &caller_func.blocks[&caller_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(&inst.opcode, Opcode::Call { name } if name == "tla_record_sum2")),
        "expected direct call to tla_record_sum2 in caller entry block"
    );
}

fn build_tla_unbounded_dynamic_alloca_with_dynamic_gep() -> TrustIrModule {
    single_function_module(
        212,
        "tla_unbounded_dynamic_alloca_with_dynamic_gep",
        func_ty(vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(v(0)),
                    align: None,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(10),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(11),
                    value: v(1),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(11),
                    align: None,
                    volatile: false,
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Return {
                    values: vec![v(12)],
                }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_tla_unbounded_dynamic_alloca_with_dynamic_gep_records_runtime_metadata() {
    let module = build_tla_unbounded_dynamic_alloca_with_dynamic_gep();
    let (lir_func, _) =
        translate_only(&module).expect("dynamic alloca should record runtime-size metadata");

    assert_eq!(
        lir_func.stack_slots.len(),
        1,
        "expected one runtime-sized aggregate slot"
    );
    assert_eq!(lir_func.stack_slots[0].size, 8);
    assert_eq!(lir_func.stack_slots[0].align, 8);
    assert_eq!(
        lir_func.stack_slots[0].allocation,
        StackSlotAllocationKind::RuntimeSized {
            size_source: StackSlotSizeSource::Value(0)
        },
        "dynamic alloca metadata should point at the trust_ir count ValueId"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StackAddr { slot: 0 })),
        "expected the dynamic alloca result to materialize as StackAddr slot 0"
    );
}

/// Reducer for #521: `FuncExcept` lowers a runtime pair count through
/// `Load -> Mul -> Add -> Trunc -> Alloca(count=Some(...))`.
///
/// This is the smallest shape that matches the failing ty-side record /
/// EXCEPT aggregate path without pulling in the rest of the lowering stack.
fn build_tla_func_except_dynamic_alloca_reducer() -> TrustIrModule {
    single_function_module(
        321,
        "tla_func_except_dynamic_alloca_reducer",
        func_ty(vec![Ty::I64], vec![Ty::Ptr]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                // pair_count = load [func_ptr]
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(1)),
                // total_slots = 1 + 2 * pair_count
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: v(1),
                    rhs: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(4)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(3),
                    rhs: v(4),
                })
                .with_result(v(5)),
                // FuncExcept truncates the slot count to i32 before Alloca.
                InstrNode::new(Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I64,
                    dst_ty: Ty::I32,
                    operand: v(5),
                })
                .with_result(v(6)),
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(v(6)),
                    align: None,
                })
                .with_result(v(7)),
                InstrNode::new(Inst::Return { values: vec![v(7)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_tla_func_except_dynamic_alloca_reducer_records_runtime_metadata() {
    let module = build_tla_func_except_dynamic_alloca_reducer();
    let (lir_func, _) = translate_only(&module)
        .expect("FuncExcept-style dynamic alloca should record runtime-size metadata");

    assert_eq!(
        lir_func.stack_slots.len(),
        1,
        "expected one runtime-sized FuncExcept aggregate slot"
    );
    assert_eq!(lir_func.stack_slots[0].size, 8);
    assert_eq!(lir_func.stack_slots[0].align, 8);
    assert_eq!(
        lir_func.stack_slots[0].allocation,
        StackSlotAllocationKind::RuntimeSized {
            size_source: StackSlotSizeSource::Value(6)
        },
        "runtime metadata should identify the truncated alloca-count ValueId"
    );
}

// ===========================================================================
// Category 12: tla-trust_ir coverage — Constant::Int i128 range checks
//
// Issue #339 Finding 3: the adapter previously did `*v as i64` on a
// Constant::Int(i128) value, silently truncating any constant whose value
// did not fit in i64. Latent bug because current tla-trust_ir only emits
// i64-sourced literals, but explicit in the issue body ("large constants
// for set membership encoding"). Fix rejects out-of-range integer literals
// with a clear AdapterError::UnsupportedInstruction.
// ===========================================================================

fn build_i64_constant_module(value: i128) -> TrustIrModule {
    single_function_module(
        220,
        "i64_const",
        func_ty(vec![], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(value),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_i64_constant_in_range_is_accepted() {
    // Values inside i64 range must still translate successfully — do not
    // regress on normal integer literals while closing the silent-truncation
    // hole.
    for value in [0i128, 1, -1, i64::MIN as i128, i64::MAX as i128] {
        let module = build_i64_constant_module(value);
        translate_only(&module).unwrap_or_else(|e| {
            panic!(
                "in-range i64 constant {} must translate, got {:?}",
                value, e
            )
        });
    }
}

#[test]
fn test_i64_constant_above_range_is_rejected() {
    // A Constant::Int beyond the 64-bit bit-pattern range (above u64::MAX)
    // must NOT be silently truncated. The adapter accepts values in
    // [i64::MIN, u64::MAX] for Ty::I64 (unsigned bit-patterns like hash
    // primes are common in trust_ir frontends), but anything wider must
    // produce an explicit UnsupportedInstruction error.
    let module = build_i64_constant_module(u64::MAX as i128 + 1);
    let err = translate_only(&module)
        .expect_err("Constant::Int above u64::MAX must be rejected, not silently truncated");
    let msg = format!("{:?}", err);
    assert!(
        msg.contains("Constant::Int") && msg.contains("does not fit"),
        "expected UnsupportedInstruction about Constant::Int not fitting, got: {:?}",
        err
    );
}

#[test]
fn test_i64_constant_below_range_is_rejected() {
    // Symmetric check for the negative bound.
    let module = build_i64_constant_module(i64::MIN as i128 - 1);
    let err = translate_only(&module).expect_err("Constant::Int below i64::MIN must be rejected");
    let msg = format!("{:?}", err);
    assert!(
        msg.contains("Constant::Int") && msg.contains("does not fit"),
        "expected UnsupportedInstruction about Constant::Int not fitting, got: {:?}",
        err
    );
}

#[test]
fn test_i32_constant_overflow_is_rejected() {
    // Narrower target types must also reject out-of-range literals. A
    // Constant::Int with value 1 << 33 cannot fit in I32 and must error.
    let module = single_function_module(
        221,
        "i32_overflow",
        func_ty(vec![], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(1i128 << 33),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    );
    let err =
        translate_only(&module).expect_err("Constant::Int(1<<33) in I32 context must be rejected");
    let msg = format!("{:?}", err);
    assert!(
        msg.contains("does not fit"),
        "expected range-check error message, got: {:?}",
        err
    );
}

// ===========================================================================
// Category 13: End-to-end pinning tests for the #339 adapter fixes (#384).
//
// Issue #384 is the end-to-end follow-up to #339 and asks for integration
// tests that exercise the 3 silent-miscompile fixes (e00554a, 67292df,
// b2e2705 + 19455a8) against the full Trust Codegen pipeline (adapter -> ISel ->
// MachFunction) rather than just the adapter. The pre-existing pinning
// tests earlier in this file assert adapter-level correctness
// (`translate_only`); these tests run the same canonical trust_ir fixtures
// through `compile_trust_ir_function` and assert that the post-fix behavior
// survives the ISel lowering that a TLA+ spec would hit in tla-trust-cg.
//
// Cross-repo (ty) validation against tla-jit state graphs remains open
// on #384; those tests live in ~/ty/crates/tla-check/tests/.
// ===========================================================================

#[test]
fn test_tla_checked_add_overflow_flag_e2e() {
    // Finding 1 regression (e00554a) + #474 native-idiom lowering:
    //
    // The adapter must emit a real overflow check for
    // `Inst::Overflow { AddOverflow }`, not `Iconst B1 imm=0`.
    //
    // After #474, for I64 fixtures the end-to-end lowering produces the
    // canonical AArch64 flag-setting idiom:
    //     ADDS  Xd, Xa, Xb       ; flag-setting add (V = signed overflow)
    //     CSET  Xov, VS          ; materialize V into a bool register
    //
    // Pre-#474 this path went through the bit-pattern expansion
    // (`~(lhs ^ rhs) & (lhs ^ sum)`, MSB=1 iff overflow) which surfaced as
    // AArch64 EOR family opcodes in the MachFunction. That idiom is now
    // gone for I64 and has been replaced by ADDS+CSET VS.
    //
    // This test pins the NEW post-#474 shape: ADDS must appear, CSET must
    // appear, and the bit-pattern EOR chain must be absent.
    let module = build_tla_checked_add();
    let mfunc = compile_trust_ir_function(&module);

    // ADDS must be present — it is both the wrapping value result AND the
    // NZCV.V flag source. The plain AddRR/AddRI path is no longer emitted
    // for I64 overflow adds (the adapter emits `Opcode::CheckedSadd` which
    // ISel lowers to `AArch64Opcode::AddsRR`).
    let adds_flag = count_opcode(&mfunc, AArch64Opcode::AddsRR);
    assert!(
        adds_flag >= 1,
        "expected at least one AArch64 ADDS (flag-setting add) from #474 \
         CheckedSadd lowering, got 0. MachFunction: {:#?}",
        mfunc.blocks,
    );

    // CSET must be present — materialises NZCV.V into a register. The
    // condition-code operand (VS) rides on the instruction operand list,
    // not on the opcode, so we assert the opcode count here.
    let csets = count_opcode(&mfunc, AArch64Opcode::CSet);
    assert!(
        csets >= 1,
        "expected at least one AArch64 CSET (VS) to materialise the V flag \
         produced by ADDS. Regression would mean the overflow bool is \
         unreachable or constant-folded. MachFunction: {:#?}",
        mfunc.blocks,
    );

    // The bit-pattern XOR chain must be gone for I64 — presence would mean
    // the adapter fell back to `Iadd + Bxor + Bnot + Band + Icmp` instead
    // of emitting the native CheckedSadd op.
    let xors =
        count_opcode(&mfunc, AArch64Opcode::EorRR) + count_opcode(&mfunc, AArch64Opcode::EorRI);
    assert_eq!(
        xors, 0,
        "I64 overflow add must not emit EOR after #474 — the native ADDS+CSET \
         idiom does not need a bit-pattern check. Regression to bit-pattern \
         lowering? MachFunction: {:#?}",
        mfunc.blocks,
    );

    assert!(
        has_opcode(&mfunc, AArch64Opcode::Ret),
        "expected terminating RET in the overflow-add function"
    );
}

/// Local variant of `compile_trust_ir_function` that also propagates
/// adapter-produced `stack_slots` onto the resulting `ISelFunction` via
/// `set_stack_slots`. Used by the #384 e2e tests that assert the slot
/// metadata survives ISel. The shared helper above deliberately omits
/// slot propagation; replicating it here keeps existing tests unchanged.
fn compile_trust_ir_function_with_stack_slots(module: &TrustIrModule) -> ISelFunction {
    let func = single_function(module);
    let (lir_func, _proof_ctx) =
        translate_function(func, module).expect("adapter translation failed");

    let mut isel = InstructionSelector::new(lir_func.name.clone(), lir_func.signature.clone());
    isel.seed_value_types(&lir_func.value_types);
    isel.set_stack_slots(lir_func.stack_slots.clone());
    isel.lower_formal_arguments(&lir_func.signature, lir_func.entry_block)
        .unwrap();

    let mut block_order: Vec<Block> = lir_func.blocks.keys().copied().collect();
    block_order.sort_by_key(|b| {
        if *b == lir_func.entry_block {
            0
        } else {
            b.0 + 1
        }
    });
    for block_id in &block_order {
        let bb = &lir_func.blocks[block_id];
        isel.select_block_with_source_locs(*block_id, &bb.instructions, &bb.source_locs)
            .unwrap();
    }
    isel.finalize()
}

fn compile_trust_ir_function_x86_64_with_stack_slots(module: &TrustIrModule) -> X86ISelFunction {
    let func = single_function(module);
    let (lir_func, _proof_ctx) =
        translate_function(func, module).expect("adapter translation failed");

    let mut isel = X86InstructionSelector::new(lir_func.name.clone(), lir_func.signature.clone());
    isel.seed_value_types(&lir_func.value_types);
    isel.seed_function_value_use_counts(&lir_func);
    isel.set_stack_slots(lir_func.stack_slots.clone());
    isel.lower_formal_arguments(&lir_func.signature, lir_func.entry_block)
        .unwrap();

    let mut block_order: Vec<Block> = lir_func.blocks.keys().copied().collect();
    block_order.sort_by_key(|b| {
        if *b == lir_func.entry_block {
            0
        } else {
            b.0 + 1
        }
    });
    for block_id in &block_order {
        let bb = &lir_func.blocks[block_id];
        isel.select_block(*block_id, &bb.instructions).unwrap();
    }
    isel.finalize()
}

#[test]
fn test_tla_aggregate_alloca_slot_size_e2e() {
    // Finding 2 regression (67292df): Alloca { count: Some(const(10)) } on
    // an I64 element type must allocate 10 * 8 = 80 bytes of stack. End-to-
    // end this is visible on the MachFunction's stack_slots — ISel carries
    // the adapter's slot size through unchanged (via `set_stack_slots`), so
    // the post-fix value must appear in `mfunc.stack_slots`. A regression
    // that silently drops the count would show size=8 here.
    let module = build_tla_aggregate_alloca();
    let mfunc = compile_trust_ir_function_with_stack_slots(&module);

    assert_eq!(
        mfunc.stack_slots.len(),
        1,
        "expected exactly one stack slot from the Alloca, got {}",
        mfunc.stack_slots.len()
    );
    assert_eq!(
        mfunc.stack_slots[0].size, 80,
        "expected 10 * sizeof(I64) = 80 bytes post-fix; a size of 8 means \
         the adapter silently dropped the `count` field again."
    );
    assert_eq!(
        mfunc.stack_slots[0].align, 8,
        "I64 alloca must retain 8-byte alignment end-to-end"
    );

    // A store+load round-trip must survive ISel.
    assert!(
        has_opcode(&mfunc, AArch64Opcode::StrRI) || has_opcode(&mfunc, AArch64Opcode::StrRO),
        "expected STR for the aggregate store"
    );
    assert!(
        has_opcode(&mfunc, AArch64Opcode::LdrRI) || has_opcode(&mfunc, AArch64Opcode::LdrRO),
        "expected LDR for the aggregate load"
    );
}

#[test]
fn test_alloca_explicit_align_preserved_aarch64_and_x86_64() {
    let module = single_function_module(
        318,
        "alloca_explicit_align_32",
        func_ty(vec![], vec![Ty::Ptr]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I8,
                    count: None,
                    align: Some(32),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    );

    let (lir_func, _) = translate_only(&module).expect("explicit Alloca align must lower");
    assert_eq!(lir_func.stack_slots.len(), 1);
    assert_eq!(lir_func.stack_slots[0].size, 1);
    assert_eq!(lir_func.stack_slots[0].align, 32);

    let aarch64 = compile_trust_ir_function_with_stack_slots(&module);
    assert_eq!(aarch64.stack_slots[0].align, 32);
    assert!(has_opcode(&aarch64, AArch64Opcode::Ret));

    let x86_64 = compile_trust_ir_function_x86_64_with_stack_slots(&module);
    assert_eq!(x86_64.stack_slots[0].align, 32);
    assert!(has_x86_opcode(&x86_64, X86Opcode::Ret));
}

#[test]
fn test_alloca_invalid_explicit_align_fails_closed() {
    let module = single_function_module(
        319,
        "alloca_invalid_explicit_align",
        func_ty(vec![], vec![Ty::Ptr]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I8,
                    count: None,
                    align: Some(3),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    );

    let err = translate_only(&module).expect_err("non-power-of-two Alloca align must fail");
    assert!(
        err.to_string().contains("explicit align 3") && err.to_string().contains("invalid"),
        "unexpected invalid Alloca align diagnostic: {err}"
    );
}

fn explicit_v128_load_store_module(name: &str, align: Option<u64>) -> TrustIrModule {
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    single_function_module(
        320,
        name,
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    volatile: false,
                    align,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Store {
                    ty: v4i32,
                    ptr: v(1),
                    value: v(2),
                    volatile: false,
                    align,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_explicit_v128_memory_align_selects_x86_aligned_moves() {
    let aligned = explicit_v128_load_store_module("explicit_v128_align_16", Some(16));
    let (lir_func, _) = translate_only(&aligned).expect("explicit v128 align must lower");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::Load {
            ty: Type::V128,
            align: Some(16)
        }
    ));
    assert!(matches!(
        &entry.instructions[1].opcode,
        Opcode::Store {
            ty: Type::V128,
            align: Some(16)
        }
    ));

    let x86_64 = compile_trust_ir_function_x86_64(&aligned);
    assert_eq!(count_x86_opcode(&x86_64, X86Opcode::MovdqaRM), 1);
    assert_eq!(count_x86_opcode(&x86_64, X86Opcode::MovdqaMR), 1);
    assert_eq!(count_x86_opcode(&x86_64, X86Opcode::MovdquRM), 0);
    assert_eq!(count_x86_opcode(&x86_64, X86Opcode::MovdquMR), 0);
}

#[test]
fn test_missing_or_weak_v128_memory_align_keeps_x86_unaligned_moves() {
    for (name, align) in [
        ("explicit_v128_no_align", None),
        ("explicit_v128_align_8", Some(8)),
    ] {
        let module = explicit_v128_load_store_module(name, align);
        let x86_64 = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&x86_64, X86Opcode::MovdqaRM), 0, "{name}");
        assert_eq!(count_x86_opcode(&x86_64, X86Opcode::MovdqaMR), 0, "{name}");
        assert_eq!(count_x86_opcode(&x86_64, X86Opcode::MovdquRM), 1, "{name}");
        assert_eq!(count_x86_opcode(&x86_64, X86Opcode::MovdquMR), 1, "{name}");
    }
}

#[test]
fn test_tla_i64_constant_range_e2e() {
    // Finding 3 regression (b2e2705 + 19455a8): Constant::Int(i128) must
    // be range-checked against the target type, NOT silently truncated via
    // `*v as i64`. End-to-end the post-fix contract is two-sided:
    //
    // 1. An in-range I64 constant compiles cleanly through ISel (we use
    //    i64::MAX as the canonical representative) and reaches a MOV family
    //    opcode in the MachFunction.
    // 2. An out-of-range wide-imm (u64::MAX + 1, which exceeds both the
    //    signed and u64 bit-pattern windows) is rejected at the adapter
    //    layer — no MachFunction is produced. A regression to
    //    truncation-by-cast would allow the wide-imm to silently pass and
    //    produce a bogus MachFunction with a truncated `imm`.
    let ok_module = build_i64_constant_module(i64::MAX as i128);
    let ok_mfunc = compile_trust_ir_function(&ok_module);
    let has_mov = has_opcode(&ok_mfunc, AArch64Opcode::Movz)
        || has_opcode(&ok_mfunc, AArch64Opcode::MovI)
        || has_opcode(&ok_mfunc, AArch64Opcode::MovR)
        || has_opcode(&ok_mfunc, AArch64Opcode::Movn)
        || has_opcode(&ok_mfunc, AArch64Opcode::Movk)
        || has_opcode(&ok_mfunc, AArch64Opcode::LdrLiteral);
    assert!(
        has_mov,
        "expected a MOV-family or LDR-literal opcode for the i64 constant \
         materialization; got MachFunction: {:#?}",
        ok_mfunc.blocks,
    );
    assert!(
        has_opcode(&ok_mfunc, AArch64Opcode::Ret),
        "expected RET in the i64 constant function"
    );

    // Out-of-range wide immediate must error at the adapter — ISel never
    // runs because translate_only returns Err. u64::MAX as i128 + 1 is
    // above the u64-bit-pattern acceptance window, so it still fails even
    // after the 19455a8 u64-bit-pattern widening.
    let too_wide = (u64::MAX as i128) + 1;
    let bad_module = build_i64_constant_module(too_wide);
    let err = translate_only(&bad_module)
        .expect_err("Constant::Int above u64::MAX must be rejected end-to-end");
    let msg = format!("{:?}", err);
    assert!(
        msg.contains("does not fit"),
        "expected adapter range-check error, got: {:?}",
        err
    );
}

// ===========================================================================
// GEP stride contract (#475)
//
// Pins the ABI-critical stride convention: GEP { pointee_ty: I64, base, [idx] }
// must lower to `base + idx * 8`. External consumers (ay, ty) rely on
// `stride = sizeof(pointee_ty)`; see the `trust-cg-ir` crate docs.
// ===========================================================================

fn build_gep_stride_contract_i64() -> TrustIrModule {
    single_function_module(
        9999,
        "gep_stride_contract_i64",
        func_ty(vec![Ty::Ptr, Ty::I64], vec![Ty::Ptr]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(0),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

fn build_gep_stride_contract_i32_index() -> TrustIrModule {
    single_function_module(
        10000,
        "gep_stride_contract_i32_index",
        func_ty(vec![Ty::Ptr, Ty::I32], vec![Ty::Ptr]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(0),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_gep_stride_contract_i64() {
    // Contract (#475): for pointee_ty = I64 (sizeof = 8), a single-index GEP
    // must lower to `base + index * 8`, implemented as:
    //   Iconst { ty: I64, imm: 8 }  (stride materialization)
    //   Imul                         (scaled index)
    //   Iadd                         (base + scaled)
    let module = build_gep_stride_contract_i64();
    let (lir_func, _) = translate_only(&module).expect("adapter translation failed");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    let has_stride_8 = entry.instructions.iter().any(|inst| {
        matches!(
            inst.opcode,
            Opcode::Iconst {
                ty: Type::I64,
                imm: 8,
            }
        )
    });
    assert!(
        has_stride_8,
        "GEP stride contract (#475): expected Iconst {{ ty: I64, imm: 8 }} \
         (sizeof(I64) stride) but got {:?}",
        entry
            .instructions
            .iter()
            .map(|i| &i.opcode)
            .collect::<Vec<_>>()
    );

    let has_imul = entry
        .instructions
        .iter()
        .any(|inst| matches!(inst.opcode, Opcode::Imul));
    assert!(
        has_imul,
        "GEP stride contract (#475): expected Imul for index * stride"
    );

    let has_iadd = entry
        .instructions
        .iter()
        .any(|inst| matches!(inst.opcode, Opcode::Iadd));
    assert!(
        has_iadd,
        "GEP stride contract (#475): expected Iadd for base + scaled_index"
    );
}

#[test]
fn test_gep_stride_contract_i32_index_extends_before_scaling() {
    let module = build_gep_stride_contract_i32_index();
    let (lir_func, _) = translate_only(&module).expect("adapter translation failed");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    let sext_pos = entry
        .instructions
        .iter()
        .position(|inst| {
            matches!(
                inst.opcode,
                Opcode::Sextend {
                    from_ty: Type::I32,
                    to_ty: Type::I64,
                }
            )
        })
        .expect("GEP i32 index must sign-extend to i64 before stride scaling");
    let mul_pos = entry
        .instructions
        .iter()
        .position(|inst| matches!(inst.opcode, Opcode::Imul))
        .expect("GEP stride contract expected Imul for index * stride");
    assert!(
        sext_pos < mul_pos,
        "GEP index extension must precede stride scaling"
    );

    let mfunc = compile_trust_ir_function(&module);
    let entry = &mfunc.blocks[&Block(0)];
    let sxtw_pos = entry
        .insts
        .iter()
        .position(|inst| inst.opcode == AArch64Opcode::Sxtw)
        .expect("ISel must emit SXTW for signed i32 GEP index");
    let scale_pos = entry
        .insts
        .iter()
        .position(|inst| matches!(inst.opcode, AArch64Opcode::MulRR | AArch64Opcode::Madd))
        .expect("ISel must emit a 64-bit multiply or fused multiply-add for GEP scaling");
    assert!(sxtw_pos < scale_pos, "SXTW must feed the stride multiply");
    match entry.insts[scale_pos].operands[0] {
        trust_cg_lower::isel::ISelOperand::VReg(vreg) => assert_eq!(vreg.class, RegClass::Gpr64),
        ref other => panic!("expected Gpr64 scaling destination, got {other:?}"),
    }
}

// ===========================================================================
// Category 14: EWD998Small-shaped tla-trust_ir Record/Sequence aggregates (#384)
//
// Issue #384 tracks end-to-end validation for the #339 adapter fixes. A real
// cross-repo tla-check harness (AddTwoTest / DieHardTLA / bcastFolklore_small
// vs tla-jit) is filed as a separate ty-side tracker so ty owns the
// driver; see `reports/2026-04-20-384-ewd998-status.md`.
//
// The Trust Codegen-side deliverable is a pinning regression that captures the exact
// nested Record / Sequence aggregate shape a TLA+ spec emits through
// tla-trust_ir. The canonical pattern (from
// `~/ty/crates/tla-trust_ir/src/lower/mod.rs:1322-1431`,
// `~/ty/crates/tla-trust_ir/src/lower/sequences.rs:70-108`,
// `~/ty/crates/tla-trust_ir/src/lower/set_ops.rs:25-60`) is:
//
//     %cnt  = Const I32 N
//     %agg  = Alloca I64, count: Some(%cnt)                 ; N-slot aggregate
//     for i in 0..N {
//         %idx = Const I32 i
//         %ptr = GEP i64, %agg, [%idx]
//         Store i64, %ptr, %vi                              ; or Load
//     }
//
// That is the shape EWD998Small would hit at every `RecordNew`/`SetEnum`/
// `Append` operation. The pre-existing `test_tla_aggregate_alloca_*` tests
// exercise *one* offset (slot 5); the EWD998-shaped regressions below stress
// the full multi-offset store+load pattern, which is what tla-check actually
// observes between states. If the adapter or ISel ever regresses on any
// single slot, these tests fail loudly.
//
// Substitute specs (per #384 body and `reports/2026-04-18-339-ewd998-plan.md`):
//   - Record: 4-field record, like a `DieHard` state `[big |-> i, small |-> j]`
//   - Sequence: length-header + 3 elements, like a small `Append` step
//
// The cross-repo tla-jit diff work tracked by the ty-side tracker remains
// the closure gate for #384; these pins are the Trust Codegen half.
// ===========================================================================

fn build_record_constant_extract_right() -> TrustIrModule {
    let record_id = RecordId::new(0);
    let record_ty = Ty::Record(record_id);
    let func_ty = func_ty(vec![], vec![Ty::I64]);
    let mut module = TrustIrModule::new("record_constant_extract_right");
    module.add_record(RecordDef {
        id: record_id,
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "left".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "right".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
    });
    let func_ty_id = module.add_func_type(func_ty);
    let mut func = TrustIrFunction::new(f(309), "record_constant_extract_right", func_ty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: record_ty.clone(),
                value: Constant::Record(vec![
                    ("right".to_string(), Constant::Int(22)),
                    ("left".to_string(), Constant::Int(11)),
                ]),
            })
            .with_result(v(10)),
            InstrNode::new(Inst::ExtractField {
                ty: record_ty,
                aggregate: v(10),
                field: 1,
            })
            .with_result(v(11)),
            InstrNode::new(Inst::Return {
                values: vec![v(11)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

#[test]
fn test_record_slice_keeps_other_trust_ir30_types_fail_closed() {
    for ty in [
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
    ] {
        let err = translate_type(&ty).expect_err("non-record trust_ir#30 type must fail closed");
        assert!(
            err.to_string().contains("not yet lowered"),
            "unexpected fail-closed diagnostic for {ty:?}: {err}"
        );
    }

    let rc = Ty::Rc(Box::new(Ty::I64));
    let err = translate_type(&rc).expect_err("Rc must not lower as a raw pointer");
    assert!(
        err.to_string().contains("Ty::Rc") && err.to_string().contains("refcount ownership"),
        "unexpected Rc fail-closed diagnostic: {err}"
    );
}

#[test]
fn test_captured_closure_constant_stays_fail_closed() {
    let module = single_function_module(
        308,
        "captured_closure_const_fail_closed",
        func_ty(vec![], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Closure {
                        func: f(0),
                        captures: vec![Constant::Int(1)],
                    },
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    );
    let err = translate_only(&module).expect_err("captured closure constants must fail closed");
    assert!(
        err.to_string().contains("aggregate/closure constant"),
        "unexpected captured closure diagnostic: {err}"
    );
}

#[test]
fn test_record_constant_materializes_struct_gep_store_load() {
    let module = build_record_constant_extract_right();
    let (lir_func, _) = translate_only(&module).expect("record constant should lower");

    assert_eq!(lir_func.stack_slots.len(), 1);
    assert_eq!(lir_func.stack_slots[0].size, 16);
    assert_eq!(lir_func.stack_slots[0].align, 8);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::StructGep { .. }))
            .count(),
        3
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(
                inst.opcode,
                Opcode::Store {
                    ty: Type::I64,
                    align: None
                }
            ))
            .count(),
        2
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(
                inst.opcode,
                Opcode::Load {
                    ty: Type::I64,
                    align: None
                }
            ))
            .count(),
        1
    );
}

#[test]
fn test_record_constant_materializes_aarch64() {
    let module = build_record_constant_extract_right();
    let mfunc = compile_trust_ir_function_with_stack_slots(&module);

    assert!(
        count_opcode(&mfunc, AArch64Opcode::StrRI) + count_opcode(&mfunc, AArch64Opcode::StrRO)
            >= 2,
        "record constant should store both fields: {:#?}",
        mfunc.blocks
    );
    assert!(
        count_opcode(&mfunc, AArch64Opcode::LdrRI) + count_opcode(&mfunc, AArch64Opcode::LdrRO)
            >= 1,
        "record extract should load the selected field: {:#?}",
        mfunc.blocks
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

#[test]
fn test_record_constant_materializes_x86_64() {
    let module = build_record_constant_extract_right();
    let mfunc = compile_trust_ir_function_x86_64_with_stack_slots(&module);

    assert!(
        count_x86_opcode(&mfunc, X86Opcode::MovMR) >= 2,
        "record constant should store both fields: {:#?}",
        mfunc.blocks
    );
    assert!(
        count_x86_opcode(&mfunc, X86Opcode::MovRM) >= 1,
        "record extract should load the selected field: {:#?}",
        mfunc.blocks
    );
    assert!(has_x86_opcode(&mfunc, X86Opcode::Ret));
}

/// EWD998-shape: a 4-field Record — `Alloca(count=4)` + 4 × `Const+GEP+Store`
/// then 4 × `Const+GEP+Load`, finally summing the first two loaded fields.
///
/// Mirrors `tla-trust_ir::lower_record_new`
/// (`~/ty/crates/tla-trust_ir/src/lower/sequences.rs:77-93`), which is what a
/// `[a |-> x, b |-> y, c |-> z, d |-> w]` record literal expands to. The
/// summed-fields return keeps the aggregate observably live so DCE can't
/// erase the stores.
fn build_tla_record_new_4fields() -> TrustIrModule {
    // (v0, v1, v2, v3) are the 4 incoming i64 field values.
    // Locals:
    //   v10..v13 = Const I32 {0,1,2,3} for field indices
    //   v20      = Const I32 4           (aggregate slot count)
    //   v21      = Alloca I64, count v20
    //   v30..v33 = GEP v21 [v10..v13]    (per-field slot pointers)
    //   v40..v43 = Load from v30..v33    (read back for verification)
    //   v50      = Iadd v40, v41         (observably uses the loads)
    single_function_module(
        310,
        "tla_record_new_4fields",
        func_ty(vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), Ty::I64),
                (v(1), Ty::I64),
                (v(2), Ty::I64),
                (v(3), Ty::I64),
            ],
            body: vec![
                // Field indices (tla-trust_ir uses I32 constants for offsets)
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(1),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(2),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(3),
                })
                .with_result(v(13)),
                // Aggregate count + allocation (canonical alloc_aggregate pattern)
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(4),
                })
                .with_result(v(20)),
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(v(20)),
                    align: None,
                })
                .with_result(v(21)),
                // Per-field stores: store_at_offset(agg, i, v_i)
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(21),
                    indices: vec![v(10)],
                    inbounds: false,
                })
                .with_result(v(30)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(30),
                    value: v(0),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(21),
                    indices: vec![v(11)],
                    inbounds: false,
                })
                .with_result(v(31)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(31),
                    value: v(1),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(21),
                    indices: vec![v(12)],
                    inbounds: false,
                })
                .with_result(v(32)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(32),
                    value: v(2),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(21),
                    indices: vec![v(13)],
                    inbounds: false,
                })
                .with_result(v(33)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(33),
                    value: v(3),
                    align: None,
                    volatile: false,
                }),
                // Read slot[0] and slot[1] back for observability
                // (fresh GEPs — tla-trust_ir always re-emits the GEP per load/store)
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(21),
                    indices: vec![v(10)],
                    inbounds: false,
                })
                .with_result(v(40)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(40),
                    align: None,
                    volatile: false,
                })
                .with_result(v(41)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(21),
                    indices: vec![v(11)],
                    inbounds: false,
                })
                .with_result(v(42)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(42),
                    align: None,
                    volatile: false,
                })
                .with_result(v(43)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(41),
                    rhs: v(43),
                })
                .with_result(v(50)),
                InstrNode::new(Inst::Return {
                    values: vec![v(50)],
                }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_tla_record_new_4fields_adapter() {
    // Adapter layer must translate the full record-new pattern:
    // Alloca(count=4) must fold into a single 32-byte slot, and all 4 stores
    // plus 2 loads must reach the LIR entry block.
    let module = build_tla_record_new_4fields();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate 4-field record pattern");

    assert_eq!(
        lir_func.stack_slots.len(),
        1,
        "4-field record must produce exactly one Alloca-backed slot, got {}",
        lir_func.stack_slots.len()
    );
    assert_eq!(
        lir_func.stack_slots[0].size, 32,
        "4 * sizeof(I64) = 32 bytes expected; got {}. A size of 8 would mean \
         the adapter regressed on the #339 Finding 2 `count` fold.",
        lir_func.stack_slots[0].size
    );
    assert_eq!(
        lir_func.stack_slots[0].align, 8,
        "I64 record aggregate must retain 8-byte alignment"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    let store_count = entry
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();
    assert_eq!(
        store_count, 4,
        "expected exactly 4 Store opcodes (one per record field), got {}",
        store_count
    );
    let load_count = entry
        .instructions
        .iter()
        .filter(|i| {
            matches!(
                i.opcode,
                Opcode::Load {
                    ty: Type::I64,
                    align: None
                }
            )
        })
        .count();
    assert_eq!(
        load_count, 2,
        "expected exactly 2 Load opcodes (for the summed-back field reads), got {}",
        load_count
    );
}

#[test]
fn test_tla_record_new_4fields_isel() {
    // End-to-end: after adapter + ISel, the AArch64 MachFunction must contain
    // 4 STR (per-field store) and 2 LDR (summed-back reads). The parallel
    // field operations also stress register allocation — a regression where
    // GEP+Store gets folded into a single base-only STR would drop per-field
    // offset correctness (the DieHardTLA test would diverge immediately).
    let module = build_tla_record_new_4fields();
    let mfunc = compile_trust_ir_function_with_stack_slots(&module);

    let strs =
        count_opcode(&mfunc, AArch64Opcode::StrRI) + count_opcode(&mfunc, AArch64Opcode::StrRO);
    assert!(
        strs >= 4,
        "expected >=4 STR opcodes for the 4 record-field stores, got {}. \
         MachFunction blocks: {:#?}",
        strs,
        mfunc.blocks,
    );

    let ldrs =
        count_opcode(&mfunc, AArch64Opcode::LdrRI) + count_opcode(&mfunc, AArch64Opcode::LdrRO);
    assert!(
        ldrs >= 2,
        "expected >=2 LDR opcodes for the slot-0 + slot-1 read-back, got {}. \
         MachFunction blocks: {:#?}",
        ldrs,
        mfunc.blocks,
    );

    assert_eq!(
        mfunc.stack_slots.len(),
        1,
        "ISel must carry the single 32-byte slot through unchanged"
    );
    assert_eq!(
        mfunc.stack_slots[0].size, 32,
        "record slot must remain 32 bytes end-to-end"
    );

    assert!(
        has_opcode(&mfunc, AArch64Opcode::Ret),
        "record return must terminate with RET"
    );
}

/// EWD998-shape: a length-prefixed Sequence aggregate with 3 elements —
/// `Alloca(count=4)` (1 header + 3 data), store length at slot[0], stores
/// at slot[1..4], then `Len(seq)` reads slot[0] and `Head(seq)` reads
/// slot[1]. Mirrors `tla-trust_ir::lower_seq_len`/`lower_seq_head` calls on a
/// sequence built by `lower_seq_enum` (`~/ty/crates/tla-trust_ir/src/lower/
/// constants.rs:91-125` and `sequences.rs:127-152`).
///
/// The returned value is `Len(seq) + Head(seq)`, which keeps both loads
/// observably live.
fn build_tla_sequence_len_plus_head() -> TrustIrModule {
    single_function_module(
        311,
        "tla_sequence_len_plus_head",
        func_ty(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64), (v(2), Ty::I64)],
            body: vec![
                // Offset constants: 0 (length header), 1/2/3 (elements)
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(1),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(2),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(3),
                })
                .with_result(v(13)),
                // Aggregate total slot count: 1 (length) + 3 (elements) = 4
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(4),
                })
                .with_result(v(14)),
                // Length value (number of elements, stored at slot[0])
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(3),
                })
                .with_result(v(15)),
                // Alloca: total slot count (1 header + 3 data)
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(v(14)),
                    align: None,
                })
                .with_result(v(20)),
                // Store length at slot[0]
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(10)],
                    inbounds: false,
                })
                .with_result(v(30)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(30),
                    value: v(15),
                    align: None,
                    volatile: false,
                }),
                // Store elements at slots [1], [2], [3]
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(11)],
                    inbounds: false,
                })
                .with_result(v(31)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(31),
                    value: v(0),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(12)],
                    inbounds: false,
                })
                .with_result(v(32)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(32),
                    value: v(1),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(13)],
                    inbounds: false,
                })
                .with_result(v(33)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(33),
                    value: v(2),
                    align: None,
                    volatile: false,
                }),
                // Len(seq): reload slot[0]
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(10)],
                    inbounds: false,
                })
                .with_result(v(40)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(40),
                    align: None,
                    volatile: false,
                })
                .with_result(v(41)),
                // Head(seq): reload slot[1]
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(20),
                    indices: vec![v(11)],
                    inbounds: false,
                })
                .with_result(v(42)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(42),
                    align: None,
                    volatile: false,
                })
                .with_result(v(43)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(41),
                    rhs: v(43),
                })
                .with_result(v(50)),
                InstrNode::new(Inst::Return {
                    values: vec![v(50)],
                }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_tla_sequence_len_plus_head_adapter() {
    // Adapter must allocate 4 * 8 = 32 bytes for the 1-header + 3-data layout
    // and lower all 4 stores (length + 3 elements) plus 2 loads (Len + Head).
    let module = build_tla_sequence_len_plus_head();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate length-prefixed sequence pattern");

    assert_eq!(
        lir_func.stack_slots.len(),
        1,
        "sequence aggregate must produce exactly one Alloca-backed slot"
    );
    assert_eq!(
        lir_func.stack_slots[0].size, 32,
        "expected 4 * 8 = 32 bytes (1 length + 3 elements); \
         got {}. A size of 8 means the adapter regressed on Alloca `count` fold.",
        lir_func.stack_slots[0].size
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    let store_count = entry
        .instructions
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
        .count();
    assert_eq!(
        store_count, 4,
        "expected 4 Stores (length + 3 elements); got {}",
        store_count
    );
    let load_count = entry
        .instructions
        .iter()
        .filter(|i| {
            matches!(
                i.opcode,
                Opcode::Load {
                    ty: Type::I64,
                    align: None
                }
            )
        })
        .count();
    assert_eq!(
        load_count, 2,
        "expected 2 Loads (Len + Head readbacks); got {}",
        load_count
    );
}

#[test]
fn test_tla_sequence_len_plus_head_isel() {
    // End-to-end ISel pin: ensure the length-prefixed sequence shape survives
    // register allocation and produces the expected STR/LDR counts. Stride
    // must be 8 (i64 contract, #475): a GEP-miscompile would put slot[1]'s
    // store at the wrong byte offset, which EWD998Small-style state hashing
    // would surface as state-graph divergence vs tla-jit.
    let module = build_tla_sequence_len_plus_head();
    let mfunc = compile_trust_ir_function_with_stack_slots(&module);

    let strs =
        count_opcode(&mfunc, AArch64Opcode::StrRI) + count_opcode(&mfunc, AArch64Opcode::StrRO);
    assert!(
        strs >= 4,
        "expected >=4 STR opcodes for header + 3 elements, got {}. \
         MachFunction: {:#?}",
        strs,
        mfunc.blocks,
    );

    let ldrs =
        count_opcode(&mfunc, AArch64Opcode::LdrRI) + count_opcode(&mfunc, AArch64Opcode::LdrRO);
    assert!(
        ldrs >= 2,
        "expected >=2 LDR opcodes for Len + Head readbacks, got {}. \
         MachFunction: {:#?}",
        ldrs,
        mfunc.blocks,
    );

    assert_eq!(
        mfunc.stack_slots.len(),
        1,
        "ISel must carry the 32-byte slot through unchanged"
    );
    assert_eq!(
        mfunc.stack_slots[0].size, 32,
        "sequence slot must remain 32 bytes end-to-end"
    );

    assert!(
        has_opcode(&mfunc, AArch64Opcode::Ret),
        "sequence-return function must terminate with RET"
    );
}

fn build_sequence_constant_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("sequence_constant_i64");
    let elem_tyid = module.add_type(Ty::I64);
    let func_ty_id = module.add_func_type(func_ty(vec![], vec![]));

    let mut func = TrustIrFunction::new(f(312), "sequence_constant_i64", func_ty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Sequence(elem_tyid),
                value: Constant::Sequence(vec![
                    Constant::Int(10),
                    Constant::Int(20),
                    Constant::Int(30),
                ]),
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);
    module
}

fn build_sequence_extract_element_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("sequence_extract_element_i64");
    let elem_tyid = module.add_type(Ty::I64);
    let func_ty_id = module.add_func_type(func_ty(vec![], vec![Ty::I64]));

    let mut func = TrustIrFunction::new(f(316), "sequence_extract_element_i64", func_ty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Sequence(elem_tyid),
                value: Constant::Sequence(vec![
                    Constant::Int(10),
                    Constant::Int(20),
                    Constant::Int(30),
                ]),
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(v(11)),
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: v(10),
                index: v(11),
            })
            .with_result(v(12)),
            InstrNode::new(Inst::Return {
                values: vec![v(12)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

fn build_sequence_insert_element_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("sequence_insert_element_i64");
    let elem_tyid = module.add_type(Ty::I64);
    let func_ty_id = module.add_func_type(func_ty(vec![], vec![]));

    let mut func = TrustIrFunction::new(f(317), "sequence_insert_element_i64", func_ty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Sequence(elem_tyid),
                value: Constant::Sequence(vec![
                    Constant::Int(10),
                    Constant::Int(20),
                    Constant::Int(30),
                ]),
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(v(11)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(99),
            })
            .with_result(v(12)),
            InstrNode::new(Inst::InsertElement {
                ty: Ty::Sequence(elem_tyid),
                array: v(10),
                index: v(11),
                value: v(12),
            })
            .with_result(v(13)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);
    module
}

#[test]
fn test_sequence_constant_materializes_length_prefixed_stack_buffer() {
    let module = build_sequence_constant_module();
    let (lir_func, _) =
        translate_only(&module).expect("typed i64 Sequence constant must materialize");

    assert_eq!(lir_func.stack_slots.len(), 1);
    assert_eq!(lir_func.stack_slots[0].size, 32);
    assert_eq!(lir_func.stack_slots[0].align, 8);

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::ArrayGep { elem_ty: Type::I64 }))
            .count(),
        4,
        "expected one i64 GEP for the length header plus three i64 element GEPs"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|i| matches!(
                i.opcode,
                Opcode::Store {
                    ty: Type::I64,
                    align: None
                }
            ))
            .count(),
        4,
        "expected one i64 length store plus three i64 element stores"
    );
}

#[test]
fn test_sequence_constant_materializes_aarch64() {
    let module = build_sequence_constant_module();
    let mfunc = compile_trust_ir_function_with_stack_slots(&module);

    assert_eq!(mfunc.stack_slots.len(), 1);
    assert_eq!(mfunc.stack_slots[0].size, 32);

    let strs =
        count_opcode(&mfunc, AArch64Opcode::StrRI) + count_opcode(&mfunc, AArch64Opcode::StrRO);
    assert!(
        strs >= 4,
        "expected >=4 STR opcodes for length-prefixed sequence constant, got {}. \
         MachFunction: {:#?}",
        strs,
        mfunc.blocks,
    );
    assert!(has_opcode(&mfunc, AArch64Opcode::Ret));
}

#[test]
fn test_sequence_constant_materializes_x86_64() {
    let module = build_sequence_constant_module();
    let mfunc = compile_trust_ir_function_x86_64_with_stack_slots(&module);

    assert_eq!(mfunc.stack_slots.len(), 1);
    assert_eq!(mfunc.stack_slots[0].size, 32);
    assert!(
        count_x86_opcode(&mfunc, X86Opcode::MovMR) >= 4,
        "expected >=4 memory stores for length-prefixed sequence constant, got {:#?}",
        mfunc.blocks,
    );
    assert!(has_x86_opcode(&mfunc, X86Opcode::Ret));
}

#[test]
fn test_sequence_extract_element_materializes_load_path() {
    let module = build_sequence_extract_element_module();
    let (lir_func, _) =
        translate_only(&module).expect("Sequence ExtractElement over materialized buffer lowers");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        entry
            .instructions
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::ArrayGep { elem_ty: Type::I64 }))
            .count()
            >= 5,
        "expected length/element stores plus extraction element address"
    );
    assert!(
        entry.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Load {
                ty: Type::I64,
                align: None
            }
        )),
        "Sequence ExtractElement must load the selected element"
    );
}

#[test]
fn test_sequence_extract_element_materializes_aarch64_and_x86_64() {
    let module = build_sequence_extract_element_module();
    let aarch64 = compile_trust_ir_function_with_stack_slots(&module);
    assert!(
        count_opcode(&aarch64, AArch64Opcode::LdrRI) + count_opcode(&aarch64, AArch64Opcode::LdrRO)
            >= 1,
        "AArch64 sequence extraction must emit a load: {:#?}",
        aarch64.blocks
    );
    assert!(has_opcode(&aarch64, AArch64Opcode::Ret));

    let x86_64 = compile_trust_ir_function_x86_64_with_stack_slots(&module);
    assert!(
        count_x86_opcode(&x86_64, X86Opcode::MovRM) >= 1,
        "x86_64 sequence extraction must emit a load: {:#?}",
        x86_64.blocks
    );
    assert!(has_x86_opcode(&x86_64, X86Opcode::Ret));
}

#[test]
fn test_sequence_insert_element_materializes_store_path() {
    let module = build_sequence_insert_element_module();
    let (lir_func, _) =
        translate_only(&module).expect("Sequence InsertElement over materialized buffer lowers");
    let entry = &lir_func.blocks[&lir_func.entry_block];

    assert!(
        entry
            .instructions
            .iter()
            .filter(|i| matches!(
                i.opcode,
                Opcode::Store {
                    ty: Type::I64,
                    align: None
                }
            ))
            .count()
            >= 5,
        "expected length/element stores plus replacement element store"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Copy)),
        "Sequence InsertElement must return the sequence pointer carrier"
    );
}

#[test]
fn test_sequence_insert_element_materializes_aarch64_and_x86_64() {
    let module = build_sequence_insert_element_module();
    let aarch64 = compile_trust_ir_function_with_stack_slots(&module);
    assert!(
        count_opcode(&aarch64, AArch64Opcode::StrRI) + count_opcode(&aarch64, AArch64Opcode::StrRO)
            >= 5,
        "AArch64 sequence insertion must emit stores: {:#?}",
        aarch64.blocks
    );
    assert!(has_opcode(&aarch64, AArch64Opcode::Ret));

    let x86_64 = compile_trust_ir_function_x86_64_with_stack_slots(&module);
    assert!(
        count_x86_opcode(&x86_64, X86Opcode::MovMR) >= 5,
        "x86_64 sequence insertion must emit stores: {:#?}",
        x86_64.blocks
    );
    assert!(has_x86_opcode(&x86_64, X86Opcode::Ret));
}

#[test]
fn test_sequence_constant_rejects_missing_or_non_scalar_element_type() {
    let missing = single_function_module(
        313,
        "sequence_constant_missing_type",
        func_ty(vec![], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Sequence(TyId::new(99)),
                    value: Constant::Sequence(vec![Constant::Int(1)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    );
    let err = translate_only(&missing).expect_err("missing Sequence element TyId must fail");
    assert!(
        err.to_string().contains("element TyId"),
        "expected missing TyId diagnostic, got {err:?}"
    );

    let mut non_scalar = TrustIrModule::new("sequence_constant_non_scalar_type");
    let tuple_tyid = non_scalar.add_type(Ty::Tuple(vec![Ty::I64]));
    let func_ty_id = non_scalar.add_func_type(func_ty(vec![], vec![]));
    let mut func = TrustIrFunction::new(
        f(314),
        "sequence_constant_non_scalar_type",
        func_ty_id,
        b(0),
    );
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Sequence(tuple_tyid),
                value: Constant::Sequence(vec![Constant::Aggregate(vec![Constant::Int(1)])]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    non_scalar.add_function(func);

    let err = translate_only(&non_scalar).expect_err("non-scalar Sequence element type must fail");
    assert!(
        err.to_string().contains("not a fixed scalar element type"),
        "expected non-scalar element type diagnostic, got {err:?}"
    );
}

#[test]
fn test_sequence_constant_rejects_non_sequence_type() {
    let module = single_function_module(
        315,
        "sequence_constant_wrong_type",
        func_ty(vec![], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Sequence(vec![Constant::Int(1)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    );
    let err = translate_only(&module).expect_err("Sequence constant with scalar ty must fail");
    assert!(
        err.to_string().contains("requires Ty::Sequence"),
        "expected type mismatch diagnostic, got {err:?}"
    );
}

fn ty_v4i32() -> Ty {
    Ty::Vector(Box::new(Ty::I32), 4)
}

fn ty_v2i64() -> Ty {
    Ty::Vector(Box::new(Ty::I64), 2)
}

fn ty_v16i8() -> Ty {
    Ty::Vector(Box::new(Ty::I8), 16)
}

fn ty_v8i16() -> Ty {
    Ty::Vector(Box::new(Ty::I16), 8)
}

fn ty_v16_bool() -> Ty {
    Ty::Vector(Box::new(Ty::Bool), 16)
}

fn ty_v8_bool() -> Ty {
    Ty::Vector(Box::new(Ty::Bool), 8)
}

fn ty_v4_bool() -> Ty {
    Ty::Vector(Box::new(Ty::Bool), 4)
}

fn ty_v2_bool() -> Ty {
    Ty::Vector(Box::new(Ty::Bool), 2)
}

fn vector_zero_const_module(func_id: u32, name: &str, ty: Ty, lanes: usize) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![], vec![ty.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty,
                    value: Constant::Vector(vec![Constant::Int(0); lanes]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
        vec![],
    )
}

fn chc_lane_mask_array_const() -> Constant {
    Constant::Array(vec![
        Constant::Int(-1),
        Constant::Int(0),
        Constant::Int(-1),
        Constant::Int(0),
    ])
}

fn chc_lane_mask_aggregate_const() -> Constant {
    Constant::Aggregate(vec![
        Constant::Int(-1),
        Constant::Int(0),
        Constant::Int(-1),
        Constant::Int(0),
    ])
}

fn chc_lane_mask_vector_const() -> Constant {
    Constant::Vector(vec![
        Constant::Int(-1),
        Constant::Int(0),
        Constant::Int(-1),
        Constant::Int(0),
    ])
}

fn x86_v4i32_mask_shuffle_imm(bits: u8) -> i64 {
    (0..4).fold(0_i64, |imm, lane| {
        let selector = if bits & (1_u8 << lane) != 0 { 0 } else { 1 };
        imm | (selector << (lane * 2))
    })
}

fn x86_v4i32_mixed_mask_vector_const(bits: u8) -> Constant {
    Constant::Vector(
        (0..4)
            .map(|lane| {
                if bits & (1_u8 << lane) != 0 {
                    if bits & 1 == 0 {
                        Constant::Int(i128::from(u32::MAX))
                    } else {
                        Constant::Int(-1)
                    }
                } else {
                    Constant::Int(0)
                }
            })
            .collect(),
    )
}

fn build_x86_v4i32_const_mask_select(
    func_id: u32,
    name: &str,
    mask_ty: Ty,
    mask: Constant,
) -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: mask_ty,
                    value: mask,
                })
                .with_result(v(9)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Select {
                    ty: v4i32,
                    cond: v(9),
                    then_val: v(10),
                    else_val: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v4i32_const_store(func_id: u32, name: &str, value: Constant) -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v4i32.clone(),
                    value,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Store {
                    ty: v4i32,
                    ptr: v(0),
                    value: v(1),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn assert_vector_const_uses_pack_lanes_without_stack(
    lir_func: &Function,
    lane_ty: Type,
    pack_opcode: Opcode,
    context: &str,
) {
    assert!(
        lir_func.stack_slots.is_empty(),
        "{context} must not allocate adapter vector materialization slots"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| inst.opcode == pack_opcode)
            .count(),
        1,
        "{context} must lower through exactly one pack-lanes opcode"
    );

    for inst in &entry.instructions {
        assert!(
            !matches!(inst.opcode, Opcode::StackAddr { .. }),
            "{context} must not take an adapter stack address: {inst:?}"
        );
        assert!(
            !matches!(inst.opcode, Opcode::ArrayGep { .. }),
            "{context} must not compute per-lane addresses: {inst:?}"
        );
        assert!(
            !matches!(inst.opcode, Opcode::Store { ref ty, .. } if ty == &lane_ty),
            "{context} must not store scalar lanes: {inst:?}"
        );
        assert!(
            !matches!(
                inst.opcode,
                Opcode::Load {
                    ty: Type::V128,
                    align: None
                }
            ),
            "{context} must not reload a vector constant from memory: {inst:?}"
        );
    }
}

#[test]
fn test_v4i32_physical_mask_array_aggregate_and_vector_constants_keep_mask_stack_path() {
    for (name, mask) in [
        ("array", chc_lane_mask_array_const()),
        ("aggregate", chc_lane_mask_aggregate_const()),
        ("vector", chc_lane_mask_vector_const()),
    ] {
        let module = build_x86_v4i32_const_mask_select(
            9103,
            &format!("x86_v4i32_{name}_const_mask_select"),
            ty_v4i32(),
            mask,
        );
        let err =
            translate_only(&module).expect_err("physical v4i32 select masks must fail closed");
        assert!(
            err.to_string().contains("Select over <4 x i32>")
                && err.to_string().contains("<4 x bool>")
                && err.to_string().contains("Vector(I32, 4)"),
            "unexpected physical mask diagnostic for {name}: {err}"
        );
    }
}

#[test]
fn test_v4i32_array_aggregate_and_vector_constants_lower_to_pack_lanes_without_stack() {
    for (name, value) in [
        (
            "array",
            Constant::Array(vec![
                Constant::Int(7),
                Constant::Int(-20),
                Constant::Int(0),
                Constant::Int(5),
            ]),
        ),
        (
            "aggregate",
            Constant::Aggregate(vec![
                Constant::Int(i32::MIN as i128),
                Constant::Int(1),
                Constant::Int(i32::MAX as i128),
                Constant::Int(42),
            ]),
        ),
        (
            "vector",
            Constant::Vector(vec![
                Constant::Int(-1),
                Constant::Int(1),
                Constant::Int(0),
                Constant::Int(0),
            ]),
        ),
    ] {
        let module = build_x86_v4i32_const_store(
            9215,
            &format!("x86_v4i32_non_mask_{name}_const_store"),
            value,
        );
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate v4i32 non-mask constant");

        assert_vector_const_uses_pack_lanes_without_stack(
            &lir_func,
            Type::I32,
            Opcode::V4I32PackLanes,
            name,
        );
    }
}

#[test]
fn test_x86_v4i32_all_zero_and_all_ones_constants_materialize_directly() {
    for (name, value, expected_opcode, unexpected_opcode) in [
        (
            "zero",
            Constant::Vector(vec![
                Constant::Int(0),
                Constant::Int(0),
                Constant::Int(0),
                Constant::Int(0),
            ]),
            X86Opcode::Pxor,
            X86Opcode::Pcmpeqd,
        ),
        (
            "all_ones",
            Constant::Vector(vec![
                Constant::Int(-1),
                Constant::Int(-1),
                Constant::Int(-1),
                Constant::Int(-1),
            ]),
            X86Opcode::Pcmpeqd,
            X86Opcode::Pxor,
        ),
    ] {
        let module =
            build_x86_v4i32_const_store(9104, &format!("x86_v4i32_{name}_const_store"), value);
        let mfunc = compile_trust_ir_function_x86_64(&module);

        assert_eq!(count_x86_opcode(&mfunc, expected_opcode), 1, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, unexpected_opcode), 0, "{name}");
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::MovdquRM),
            0,
            "{name} must not reload a vector constant from a stack slot"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::MovdquMR),
            1,
            "{name} should only store the final vector to the destination pointer"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::MovMR32),
            0,
            "{name} must not emit lane-by-lane stack stores"
        );
    }
}

#[test]
fn test_aarch64_v4i32_and_v2i64_zero_constants_materialize_with_neon_movi() {
    for (name, ty, lanes, expected_lir_opcode) in [
        ("v4i32", ty_v4i32(), 4, Opcode::V4I32Zero),
        ("v2i64", ty_v2i64(), 2, Opcode::V2I64Zero),
    ] {
        let module = vector_zero_const_module(
            9240 + lanes as u32,
            &format!("aarch64_{name}_zero"),
            ty,
            lanes,
        );
        let (lir_func, _) = translate_only(&module).expect("adapter must lower zero vector const");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        assert!(
            entry
                .instructions
                .iter()
                .any(|i| i.opcode == expected_lir_opcode),
            "{name} zero constant should use direct vector-zero LIR"
        );

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonMovi), 1, "{name}");
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonLd1Post),
            0,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonSt1Post),
            0,
            "{name}"
        );
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0, "{name}");
    }
}

#[test]
fn test_x86_v4i32_mixed_mask_constants_materialize_with_movd_pshufd() {
    for bits in 1_u8..15 {
        let module = build_x86_v4i32_const_store(
            9200 + u32::from(bits),
            &format!("x86_v4i32_mixed_mask_{bits:04b}_const_store"),
            x86_v4i32_mixed_mask_vector_const(bits),
        );
        let mfunc = compile_trust_ir_function_x86_64(&module);

        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRI), 1, "{bits:04b}");
        assert_eq!(
            x86_opcode_imms(&mfunc, X86Opcode::MovRI),
            vec![-1],
            "{bits:04b}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::MovdToXmm),
            1,
            "{bits:04b}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 1, "{bits:04b}");
        assert_eq!(
            x86_opcode_imms(&mfunc, X86Opcode::Pshufd),
            vec![x86_v4i32_mask_shuffle_imm(bits)],
            "{bits:04b}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 0, "{bits:04b}");
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd),
            0,
            "{bits:04b}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::MovdquRM),
            0,
            "{bits:04b} must not reload a vector constant from a stack slot"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::MovdquMR),
            1,
            "{bits:04b} should only store the final vector to the destination pointer"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::MovMR32),
            0,
            "{bits:04b} must not emit lane-by-lane stack stores"
        );
    }
}

#[test]
fn test_x86_v4i32_non_mask_constant_lowers_to_pack_lanes_without_stack() {
    let module = build_x86_v4i32_const_store(
        9215,
        "x86_v4i32_non_mask_const_store",
        Constant::Vector(vec![
            Constant::Int(-1),
            Constant::Int(1),
            Constant::Int(0),
            Constant::Int(0),
        ]),
    );
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate v4i32 non-mask constant");
    assert_vector_const_uses_pack_lanes_without_stack(
        &lir_func,
        Type::I32,
        Opcode::V4I32PackLanes,
        "v4i32 non-mask vector constant",
    );

    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 4);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpckldq), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1);
}

fn build_x86_bool_mask_to_bits_const(
    func_id: u32,
    name: &str,
    mask_ty: Ty,
    value: Constant,
    result_ty: Ty,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![], vec![result_ty.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: mask_ty.clone(),
                    value,
                })
                .with_result(v(0)),
                InstrNode::new(Inst::DialectOp(Box::new(vector_dialect::mask_to_bits(
                    mask_ty,
                    v(0),
                    result_ty,
                ))))
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
        vec![],
    )
}

fn bool_mask_vector_const(bits: u8, lanes: u8) -> Constant {
    Constant::Vector(
        (0..lanes)
            .map(|lane| Constant::Bool(bits & (1_u8 << lane) != 0))
            .collect(),
    )
}

#[test]
fn test_x86_v4_bool_mask_to_bits_constants_lower_to_mask_extract() {
    for (bits, expected_opcode, unexpected_opcode, expected_shuffle) in [
        (0_u8, X86Opcode::Pxor, X86Opcode::Pcmpeqd, None),
        (
            0b1010,
            X86Opcode::Pshufd,
            X86Opcode::Pxor,
            Some(x86_v4i32_mask_shuffle_imm(0b1010)),
        ),
        (0b1111, X86Opcode::Pcmpeqd, X86Opcode::Pxor, None),
    ] {
        let module = build_x86_bool_mask_to_bits_const(
            9220 + u32::from(bits),
            &format!("x86_v4_bool_mask_to_bits_const_{bits:04b}"),
            ty_v4_bool(),
            bool_mask_vector_const(bits, 4),
            Ty::I32,
        );
        let mfunc = compile_trust_ir_function_x86_64(&module);

        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::V4I32MaskExtract), 1);
        assert_eq!(count_x86_opcode(&mfunc, expected_opcode), 1, "{bits:04b}");
        assert_eq!(count_x86_opcode(&mfunc, unexpected_opcode), 0, "{bits:04b}");
        if let Some(expected_shuffle) = expected_shuffle {
            assert_eq!(
                x86_opcode_imms(&mfunc, X86Opcode::MovRI),
                vec![-1],
                "{bits:04b}"
            );
            assert_eq!(
                x86_opcode_imms(&mfunc, X86Opcode::Pshufd),
                vec![expected_shuffle],
                "{bits:04b}"
            );
        } else {
            assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 0, "{bits:04b}");
        }
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
    }
}

#[test]
fn test_x86_v2_bool_mask_to_bits_constants_lower_to_mask_extract() {
    for (bits, expected_movri_imms, expected_pxor, expected_unpack) in [
        (0_u8, vec![], 1, 0),
        (0b01, vec![-1], 0, 0),
        (0b10, vec![-1], 1, 1),
        (0b11, vec![], 0, 0),
    ] {
        let module = build_x86_bool_mask_to_bits_const(
            9240 + u32::from(bits),
            &format!("x86_v2_bool_mask_to_bits_const_{bits:02b}"),
            ty_v2_bool(),
            bool_mask_vector_const(bits, 2),
            Ty::I64,
        );
        let mfunc = compile_trust_ir_function_x86_64(&module);

        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::V2I64MaskExtract), 1);
        assert_eq!(
            x86_opcode_imms(&mfunc, X86Opcode::MovRI),
            expected_movri_imms,
            "{bits:02b}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pxor),
            expected_pxor,
            "{bits:02b}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq),
            expected_unpack,
            "{bits:02b}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd),
            if bits == 0b11 { 1 } else { 0 },
            "{bits:02b}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    }
}

fn build_x86_v4i32_logic_cmp_copy_store() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9100,
        "x86_v4i32_logic_cmp_copy_store",
        func_ty(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr), (v(2), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::And,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Or,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Xor,
                    ty: v4i32.clone(),
                    lhs: v(12),
                    rhs: v(13),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: v4i32.clone(),
                    lhs: v(14),
                    rhs: v(11),
                })
                .with_result(v(17)),
                InstrNode::new(Inst::Copy {
                    ty: v4i32.clone(),
                    operand: v(17),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(16)),
                InstrNode::new(Inst::Store {
                    ty: v4i32,
                    ptr: v(2),
                    value: v(15),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_narrow_vector_binop_store(ty: Ty, op: BinOp, func_id: u32, name: &str) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr), (v(2), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty,
                    ptr: v(2),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_narrow_vector_icmp_store(
    ty: Ty,
    op: ICmpOp,
    func_id: u32,
    name: &str,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr), (v(2), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty,
                    ptr: v(2),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_narrow_vector_icmp_mask_to_bits(
    ty: Ty,
    mask_ty: Ty,
    op: ICmpOp,
    func_id: u32,
    name: &str,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::DialectOp(Box::new(vector_dialect::mask_to_bits(
                    mask_ty,
                    v(12),
                    Ty::I32,
                ))))
                .with_result(v(13)),
                InstrNode::new(Inst::Return {
                    values: vec![v(13)],
                }),
            ],
        }],
        vec![],
    )
}

fn build_x86_narrow_vector_cmp_select_store(
    ty: Ty,
    op: ICmpOp,
    func_id: u32,
    name: &str,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), Ty::Ptr),
                (v(1), Ty::Ptr),
                (v(2), Ty::Ptr),
                (v(3), Ty::Ptr),
                (v(4), Ty::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(2),
                    align: None,
                    volatile: false,
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: v(3),
                    align: None,
                    volatile: false,
                })
                .with_result(v(13)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Select {
                    ty: ty.clone(),
                    cond: v(14),
                    then_val: v(12),
                    else_val: v(13),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::Store {
                    ty,
                    ptr: v(4),
                    value: v(15),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn assert_no_narrow_i8_i16_adapter_lane_memory(lir_func: &Function, name: &str) {
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(
                inst.opcode,
                Opcode::Store {
                    ty: Type::I8 | Type::I16,
                    ..
                }
            ))
            .count(),
        0,
        "{name} must not lower through scalar lane stores"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(
                inst.opcode,
                Opcode::Load {
                    ty: Type::I8 | Type::I16,
                    ..
                }
            ))
            .count(),
        0,
        "{name} must not lower through scalar lane loads"
    );
    assert!(
        entry.instructions.iter().all(|inst| !matches!(
            inst.opcode,
            Opcode::ArrayGep {
                elem_ty: Type::I8 | Type::I16
            }
        )),
        "{name} must not compute scalar lane addresses"
    );
}

#[test]
fn test_x86_v_narrow_i8_i16_cmp_select_lowers_to_v128_bool_select_without_lane_memory() {
    for (
        ty,
        op,
        expected_lir,
        expected_x86_eq,
        expected_x86_gt,
        expected_eq_count,
        expected_gt_count,
        expected_pxor_count,
        expected_pcmpeqd_count,
        name,
        func_id,
    ) in [
        (
            ty_v16i8(),
            ICmpOp::Eq,
            Opcode::V16I8Icmp { cond: IntCC::Equal },
            X86Opcode::Pcmpeqb,
            X86Opcode::Pcmpgtb,
            1,
            0,
            0,
            0,
            "x86_v16i8_eq_select",
            9290,
        ),
        (
            ty_v16i8(),
            ICmpOp::Ne,
            Opcode::V16I8Icmp {
                cond: IntCC::NotEqual,
            },
            X86Opcode::Pcmpeqb,
            X86Opcode::Pcmpgtb,
            1,
            0,
            1,
            1,
            "x86_v16i8_ne_select",
            9291,
        ),
        (
            ty_v16i8(),
            ICmpOp::Sgt,
            Opcode::V16I8Icmp {
                cond: IntCC::SignedGreaterThan,
            },
            X86Opcode::Pcmpeqb,
            X86Opcode::Pcmpgtb,
            0,
            1,
            0,
            0,
            "x86_v16i8_sgt_select",
            9292,
        ),
        (
            ty_v8i16(),
            ICmpOp::Eq,
            Opcode::V8I16Icmp { cond: IntCC::Equal },
            X86Opcode::Pcmpeqw,
            X86Opcode::Pcmpgtw,
            1,
            0,
            0,
            0,
            "x86_v8i16_eq_select",
            9293,
        ),
        (
            ty_v8i16(),
            ICmpOp::Ne,
            Opcode::V8I16Icmp {
                cond: IntCC::NotEqual,
            },
            X86Opcode::Pcmpeqw,
            X86Opcode::Pcmpgtw,
            1,
            0,
            1,
            1,
            "x86_v8i16_ne_select",
            9294,
        ),
        (
            ty_v8i16(),
            ICmpOp::Slt,
            Opcode::V8I16Icmp {
                cond: IntCC::SignedLessThan,
            },
            X86Opcode::Pcmpeqw,
            X86Opcode::Pcmpgtw,
            0,
            1,
            0,
            0,
            "x86_v8i16_slt_select",
            9295,
        ),
    ] {
        let module = build_x86_narrow_vector_cmp_select_store(ty, op, func_id, name);
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate narrow compare select");
        let entry = &lir_func.blocks[&lir_func.entry_block];

        let cmp = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed narrow compare LIR opcode"));
        assert_eq!(lir_func.value_types.get(&cmp.results[0]), Some(&Type::V128));

        let select = entry
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    inst.opcode,
                    Opcode::Select {
                        cond: IntCC::NotEqual
                    }
                )
            })
            .unwrap_or_else(|| panic!("{name} should reach typed LIR Select"));
        assert_eq!(select.args[0], cmp.results[0]);
        assert_eq!(
            lir_func.value_types.get(&select.results[0]),
            Some(&Type::V128)
        );
        assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::V128BoolSelect),
            1,
            "{name}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, expected_x86_eq),
            expected_eq_count,
            "{name}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, expected_x86_gt),
            expected_gt_count,
            "{name}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pxor),
            expected_pxor_count,
            "{name}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd),
            expected_pcmpeqd_count,
            "{name}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pand), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pandn), 0, "{name}");
        assert_no_x86_scalarized_vector_cmp_path(&mfunc);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 4, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1, "{name}");
    }
}

#[test]
fn test_x86_v_narrow_i8_i16_add_sub_lower_to_packed_sse2_without_scalar_lanes() {
    for (ty, op, expected_lir, expected_x86, name, func_id) in [
        (
            ty_v16i8(),
            BinOp::Add,
            Opcode::V16I8Add,
            X86Opcode::Paddb,
            "x86_v16i8_add",
            9250,
        ),
        (
            ty_v16i8(),
            BinOp::Sub,
            Opcode::V16I8Sub,
            X86Opcode::Psubb,
            "x86_v16i8_sub",
            9251,
        ),
        (
            ty_v16i8(),
            BinOp::Mul,
            Opcode::V16I8Mul,
            X86Opcode::Packuswb,
            "x86_v16i8_mul",
            9255,
        ),
        (
            ty_v8i16(),
            BinOp::Add,
            Opcode::V8I16Add,
            X86Opcode::Paddw,
            "x86_v8i16_add",
            9252,
        ),
        (
            ty_v8i16(),
            BinOp::Sub,
            Opcode::V8I16Sub,
            X86Opcode::Psubw,
            "x86_v8i16_sub",
            9253,
        ),
        (
            ty_v8i16(),
            BinOp::Mul,
            Opcode::V8I16Mul,
            X86Opcode::Pmullw,
            "x86_v8i16_mul",
            9254,
        ),
    ] {
        let module = build_narrow_vector_binop_store(ty, op, func_id, name);
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate narrow add/sub/mul");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let packed_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed narrow LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&packed_inst.results[0]),
            Some(&Type::V128)
        );
        assert_eq!(
            entry
                .instructions
                .iter()
                .filter(|inst| matches!(
                    inst.opcode,
                    Opcode::Store {
                        ty: Type::I8 | Type::I16,
                        ..
                    }
                ))
                .count(),
            0,
            "{name} must not lower through scalar lane stores"
        );
        assert_eq!(
            entry
                .instructions
                .iter()
                .filter(|inst| matches!(
                    inst.opcode,
                    Opcode::Load {
                        ty: Type::I8 | Type::I16,
                        ..
                    }
                ))
                .count(),
            0,
            "{name} must not lower through scalar lane loads"
        );

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&mfunc, expected_x86), 1, "{name}");
        if expected_lir == Opcode::V16I8Mul {
            assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklbw), 2, "{name}");
            assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpckhbw), 2, "{name}");
            assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pmullw), 2, "{name}");
        }
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1, "{name}");
    }
}

#[test]
fn test_x86_v4i32_add_sub_mul_lowers_to_packed_sse_without_scalar_lanes() {
    for (op, expected_lir, expected_x86, name, func_id) in [
        (
            BinOp::Add,
            Opcode::V4I32Add,
            X86Opcode::Paddd,
            "x86_v4i32_add",
            9255,
        ),
        (
            BinOp::Sub,
            Opcode::V4I32Sub,
            X86Opcode::Psubd,
            "x86_v4i32_sub",
            9256,
        ),
        (
            BinOp::Mul,
            Opcode::V4I32Mul,
            X86Opcode::Pmuludq,
            "x86_v4i32_mul",
            9257,
        ),
    ] {
        let module = build_narrow_vector_binop_store(ty_v4i32(), op, func_id, name);
        let (lir_func, _) = translate_only(&module).expect("adapter must translate v4i32 binop");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let packed_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed V4I32 LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&packed_inst.results[0]),
            Some(&Type::V128)
        );
        assert_eq!(
            entry
                .instructions
                .iter()
                .filter(|inst| matches!(
                    inst.opcode,
                    Opcode::Load { ty: Type::I32, .. } | Opcode::Store { ty: Type::I32, .. }
                ))
                .count(),
            0,
            "{name} must not lower through scalar i32 lane memory"
        );

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(
            count_x86_opcode(&mfunc, expected_x86),
            1 + usize::from(op == BinOp::Mul),
            "{name}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM32), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pmulld), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1, "{name}");
    }
}

#[test]
fn test_x86_narrow_i8_i16_bitwise_lower_to_packed_sse2_without_scalar_lanes() {
    for (ty, op, expected_lir, expected_x86, name, func_id) in [
        (
            ty_v16i8(),
            BinOp::And,
            Opcode::Band,
            X86Opcode::Pand,
            "x86_v16i8_and",
            9300,
        ),
        (
            ty_v16i8(),
            BinOp::Or,
            Opcode::Bor,
            X86Opcode::Por,
            "x86_v16i8_or",
            9301,
        ),
        (
            ty_v16i8(),
            BinOp::Xor,
            Opcode::Bxor,
            X86Opcode::Pxor,
            "x86_v16i8_xor",
            9302,
        ),
        (
            ty_v8i16(),
            BinOp::And,
            Opcode::Band,
            X86Opcode::Pand,
            "x86_v8i16_and",
            9303,
        ),
        (
            ty_v8i16(),
            BinOp::Or,
            Opcode::Bor,
            X86Opcode::Por,
            "x86_v8i16_or",
            9304,
        ),
        (
            ty_v8i16(),
            BinOp::Xor,
            Opcode::Bxor,
            X86Opcode::Pxor,
            "x86_v8i16_xor",
            9305,
        ),
    ] {
        let module = build_narrow_vector_binop_store(ty, op, func_id, name);
        let (lir_func, _) = translate_only(&module).expect("adapter must translate narrow bitwise");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let logical_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed V128 logical LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&logical_inst.results[0]),
            Some(&Type::V128)
        );
        assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&mfunc, expected_x86), 1, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrd), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrq), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1, "{name}");
    }
}

#[test]
fn test_aarch64_narrow_i8_i16_bitwise_lowers_to_neon() {
    for (ty, op, expected_aarch64, name, func_id) in [
        (
            ty_v16i8(),
            BinOp::And,
            AArch64Opcode::NeonAndV,
            "aarch64_v16i8_and",
            9306,
        ),
        (
            ty_v16i8(),
            BinOp::Or,
            AArch64Opcode::NeonOrrV,
            "aarch64_v16i8_or",
            9307,
        ),
        (
            ty_v16i8(),
            BinOp::Xor,
            AArch64Opcode::NeonEorV,
            "aarch64_v16i8_xor",
            9308,
        ),
        (
            ty_v8i16(),
            BinOp::And,
            AArch64Opcode::NeonAndV,
            "aarch64_v8i16_and",
            9309,
        ),
        (
            ty_v8i16(),
            BinOp::Or,
            AArch64Opcode::NeonOrrV,
            "aarch64_v8i16_or",
            9310,
        ),
        (
            ty_v8i16(),
            BinOp::Xor,
            AArch64Opcode::NeonEorV,
            "aarch64_v8i16_xor",
            9311,
        ),
    ] {
        let module = build_narrow_vector_binop_store(ty, op, func_id, name);
        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, expected_aarch64), 1, "{name}");
    }
}

#[test]
fn test_aarch64_narrow_i8_i16_add_sub_lower_to_neon_without_scalar_lanes() {
    for (ty, op, expected_lir, expected_aarch64, name, func_id) in [
        (
            ty_v16i8(),
            BinOp::Add,
            Opcode::V16I8Add,
            AArch64Opcode::NeonAddV,
            "aarch64_v16i8_add",
            9314,
        ),
        (
            ty_v16i8(),
            BinOp::Sub,
            Opcode::V16I8Sub,
            AArch64Opcode::NeonSubV,
            "aarch64_v16i8_sub",
            9315,
        ),
        (
            ty_v16i8(),
            BinOp::Mul,
            Opcode::V16I8Mul,
            AArch64Opcode::NeonMulV,
            "aarch64_v16i8_mul",
            9319,
        ),
        (
            ty_v8i16(),
            BinOp::Add,
            Opcode::V8I16Add,
            AArch64Opcode::NeonAddV,
            "aarch64_v8i16_add",
            9316,
        ),
        (
            ty_v8i16(),
            BinOp::Sub,
            Opcode::V8I16Sub,
            AArch64Opcode::NeonSubV,
            "aarch64_v8i16_sub",
            9317,
        ),
        (
            ty_v8i16(),
            BinOp::Mul,
            Opcode::V8I16Mul,
            AArch64Opcode::NeonMulV,
            "aarch64_v8i16_mul",
            9318,
        ),
    ] {
        let module = build_narrow_vector_binop_store(ty, op, func_id, name);
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate narrow add/sub/mul");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let arith_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed narrow arithmetic LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&arith_inst.results[0]),
            Some(&Type::V128)
        );
        assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, expected_aarch64), 1, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrbRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrhRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrbRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrhRI), 0, "{name}");
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonLd1Post),
            0,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonSt1Post),
            0,
            "{name}"
        );
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0, "{name}");
    }
}

#[test]
fn test_aarch64_v4i32_add_sub_mul_lower_to_neon_without_scalar_lanes() {
    for (op, expected_lir, expected_aarch64, name, func_id) in [
        (
            BinOp::Add,
            Opcode::V4I32Add,
            AArch64Opcode::NeonAddV,
            "aarch64_v4i32_add",
            9340,
        ),
        (
            BinOp::Sub,
            Opcode::V4I32Sub,
            AArch64Opcode::NeonSubV,
            "aarch64_v4i32_sub",
            9341,
        ),
        (
            BinOp::Mul,
            Opcode::V4I32Mul,
            AArch64Opcode::NeonMulV,
            "aarch64_v4i32_mul",
            9342,
        ),
    ] {
        let module = build_narrow_vector_binop_store(ty_v4i32(), op, func_id, name);
        let (lir_func, _) = translate_only(&module).expect("adapter must translate v4i32 binop");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let arith_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed V4I32 LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&arith_inst.results[0]),
            Some(&Type::V128)
        );
        assert_eq!(
            entry
                .instructions
                .iter()
                .filter(|inst| matches!(
                    inst.opcode,
                    Opcode::Load { ty: Type::I32, .. } | Opcode::Store { ty: Type::I32, .. }
                ))
                .count(),
            0,
            "{name} must not lower through scalar i32 lane memory"
        );

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, expected_aarch64), 1, "{name}");
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonLd1Post),
            0,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonSt1Post),
            0,
            "{name}"
        );
    }
}

#[test]
fn test_aarch64_typed_vector_icmp_lower_to_neon_without_scalar_lanes() {
    for (ty, op, expected_lir, expected_aarch64, name, func_id) in [
        (
            ty_v16i8(),
            ICmpOp::Eq,
            Opcode::V16I8Icmp { cond: IntCC::Equal },
            AArch64Opcode::NeonCmeqV,
            "aarch64_v16i8_eq",
            9318,
        ),
        (
            ty_v16i8(),
            ICmpOp::Sgt,
            Opcode::V16I8Icmp {
                cond: IntCC::SignedGreaterThan,
            },
            AArch64Opcode::NeonCmgtV,
            "aarch64_v16i8_sgt",
            9319,
        ),
        (
            ty_v16i8(),
            ICmpOp::Sge,
            Opcode::V16I8Icmp {
                cond: IntCC::SignedGreaterThanOrEqual,
            },
            AArch64Opcode::NeonCmgeV,
            "aarch64_v16i8_sge",
            9320,
        ),
        (
            ty_v16i8(),
            ICmpOp::Ugt,
            Opcode::V16I8Icmp {
                cond: IntCC::UnsignedGreaterThan,
            },
            AArch64Opcode::NeonCmhiV,
            "aarch64_v16i8_ugt",
            9349,
        ),
        (
            ty_v16i8(),
            ICmpOp::Ule,
            Opcode::V16I8Icmp {
                cond: IntCC::UnsignedLessThanOrEqual,
            },
            AArch64Opcode::NeonCmhsV,
            "aarch64_v16i8_ule",
            9350,
        ),
        (
            ty_v8i16(),
            ICmpOp::Eq,
            Opcode::V8I16Icmp { cond: IntCC::Equal },
            AArch64Opcode::NeonCmeqV,
            "aarch64_v8i16_eq",
            9321,
        ),
        (
            ty_v8i16(),
            ICmpOp::Sgt,
            Opcode::V8I16Icmp {
                cond: IntCC::SignedGreaterThan,
            },
            AArch64Opcode::NeonCmgtV,
            "aarch64_v8i16_sgt",
            9322,
        ),
        (
            ty_v8i16(),
            ICmpOp::Sge,
            Opcode::V8I16Icmp {
                cond: IntCC::SignedGreaterThanOrEqual,
            },
            AArch64Opcode::NeonCmgeV,
            "aarch64_v8i16_sge",
            9323,
        ),
        (
            ty_v8i16(),
            ICmpOp::Ugt,
            Opcode::V8I16Icmp {
                cond: IntCC::UnsignedGreaterThan,
            },
            AArch64Opcode::NeonCmhiV,
            "aarch64_v8i16_ugt",
            9351,
        ),
        (
            ty_v8i16(),
            ICmpOp::Ule,
            Opcode::V8I16Icmp {
                cond: IntCC::UnsignedLessThanOrEqual,
            },
            AArch64Opcode::NeonCmhsV,
            "aarch64_v8i16_ule",
            9352,
        ),
        (
            ty_v4i32(),
            ICmpOp::Eq,
            Opcode::V4I32Icmp { cond: IntCC::Equal },
            AArch64Opcode::NeonCmeqV,
            "aarch64_v4i32_eq",
            9343,
        ),
        (
            ty_v4i32(),
            ICmpOp::Sgt,
            Opcode::V4I32Icmp {
                cond: IntCC::SignedGreaterThan,
            },
            AArch64Opcode::NeonCmgtV,
            "aarch64_v4i32_sgt",
            9344,
        ),
        (
            ty_v4i32(),
            ICmpOp::Sge,
            Opcode::V4I32Icmp {
                cond: IntCC::SignedGreaterThanOrEqual,
            },
            AArch64Opcode::NeonCmgeV,
            "aarch64_v4i32_sge",
            9345,
        ),
        (
            ty_v4i32(),
            ICmpOp::Ugt,
            Opcode::V4I32Icmp {
                cond: IntCC::UnsignedGreaterThan,
            },
            AArch64Opcode::NeonCmhiV,
            "aarch64_v4i32_ugt",
            9347,
        ),
        (
            ty_v4i32(),
            ICmpOp::Uge,
            Opcode::V4I32Icmp {
                cond: IntCC::UnsignedGreaterThanOrEqual,
            },
            AArch64Opcode::NeonCmhsV,
            "aarch64_v4i32_uge",
            9348,
        ),
        (
            ty_v2i64(),
            ICmpOp::Eq,
            Opcode::V2I64Icmp { cond: IntCC::Equal },
            AArch64Opcode::NeonCmeqV,
            "aarch64_v2i64_eq",
            9324,
        ),
        (
            ty_v2i64(),
            ICmpOp::Sgt,
            Opcode::V2I64Icmp {
                cond: IntCC::SignedGreaterThan,
            },
            AArch64Opcode::NeonCmgtV,
            "aarch64_v2i64_sgt",
            9325,
        ),
        (
            ty_v2i64(),
            ICmpOp::Sge,
            Opcode::V2I64Icmp {
                cond: IntCC::SignedGreaterThanOrEqual,
            },
            AArch64Opcode::NeonCmgeV,
            "aarch64_v2i64_sge",
            9326,
        ),
        (
            ty_v2i64(),
            ICmpOp::Ugt,
            Opcode::V2I64Icmp {
                cond: IntCC::UnsignedGreaterThan,
            },
            AArch64Opcode::NeonCmhiV,
            "aarch64_v2i64_ugt",
            9355,
        ),
        (
            ty_v2i64(),
            ICmpOp::Ule,
            Opcode::V2I64Icmp {
                cond: IntCC::UnsignedLessThanOrEqual,
            },
            AArch64Opcode::NeonCmhsV,
            "aarch64_v2i64_ule",
            9356,
        ),
    ] {
        let module = build_x86_narrow_vector_icmp_store(ty.clone(), op, func_id, name);
        let (lir_func, _) = translate_only(&module).expect("adapter must translate vector ICmp");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let cmp_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed vector compare LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&cmp_inst.results[0]),
            Some(&Type::V128)
        );

        if ty == ty_v2i64() {
            assert_no_v2i64_icmp_adapter_lane_scalarization(&lir_func);
        } else if ty == ty_v4i32() {
            assert_no_v4i32_icmp_adapter_lane_scalarization(&lir_func);
        } else {
            assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);
        }

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, expected_aarch64), 1, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrbRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrhRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrbRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrhRI), 0, "{name}");
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonLd1Post),
            0,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonSt1Post),
            0,
            "{name}"
        );
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0, "{name}");
    }
}

#[test]
fn test_aarch64_vector_mask_to_bits_lowers_without_scalar_lanes() {
    for (ty, mask_ty, expected_cmp, expected_extract, expected_lanes, name, func_id) in [
        (
            ty_v16i8(),
            ty_v16_bool(),
            Opcode::V16I8Icmp { cond: IntCC::Equal },
            Opcode::V16I8MaskExtract,
            16,
            "aarch64_v16i8_eq_mask_to_bits",
            9328,
        ),
        (
            ty_v8i16(),
            ty_v8_bool(),
            Opcode::V8I16Icmp { cond: IntCC::Equal },
            Opcode::V8I16MaskExtract,
            8,
            "aarch64_v8i16_eq_mask_to_bits",
            9329,
        ),
        (
            ty_v4i32(),
            ty_v4_bool(),
            Opcode::V4I32Icmp { cond: IntCC::Equal },
            Opcode::V4I32MaskExtract,
            4,
            "aarch64_v4i32_eq_mask_to_bits",
            9346,
        ),
    ] {
        let module = build_x86_narrow_vector_icmp_mask_to_bits(
            ty.clone(),
            mask_ty,
            ICmpOp::Eq,
            func_id,
            name,
        );
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate vector mask_to_bits");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let cmp = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_cmp)
            .unwrap_or_else(|| panic!("{name} should reach typed compare LIR opcode"));
        let extract = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_extract)
            .unwrap_or_else(|| panic!("{name} should reach typed mask extract LIR opcode"));
        assert_eq!(extract.args, vec![cmp.results[0]]);
        assert_eq!(
            lir_func.value_types.get(&extract.results[0]),
            Some(&Type::I32)
        );
        if ty == ty_v4i32() {
            assert_no_v4i32_icmp_adapter_lane_scalarization(&lir_func);
        } else {
            assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);
        }

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonCmeqV), 1, "{name}");
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonUmovGen),
            expected_lanes,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::LsrRI),
            expected_lanes,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::AndRI),
            expected_lanes,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::LslRI),
            expected_lanes - 1,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::OrrRR),
            expected_lanes - 1,
            "{name}"
        );
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrbRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrhRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrbRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrhRI), 0, "{name}");
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonLd1Post),
            0,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonSt1Post),
            0,
            "{name}"
        );
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0, "{name}");
    }
}

#[test]
fn test_aarch64_v4i32_mask_extract_lowers_without_scalar_lanes() {
    let module = single_function_module(
        9327,
        "aarch64_v4i32_mask_extract",
        func_ty(vec![Ty::Ptr], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: ty_v4i32(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    bitfield_dialect::v4i32_mask_extract(v(1)),
                )))
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    );

    let (lir_func, _) = translate_only(&module).expect("adapter must translate v4i32 mask extract");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    let extract = entry
        .instructions
        .iter()
        .find(|inst| inst.opcode == Opcode::V4I32MaskExtract)
        .expect("v4i32 mask extract should reach typed mask extract LIR opcode");
    assert_eq!(
        lir_func.value_types.get(&extract.results[0]),
        Some(&Type::I32)
    );
    assert_no_v4i32_icmp_adapter_lane_scalarization(&lir_func);

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 4);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LsrRI), 4);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::AndRI), 4);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LslRI), 3);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::OrrRR), 3);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
}

#[test]
fn test_aarch64_v2i64_cmp_bool_mask_extract_lowers_without_scalar_lanes() {
    let module = build_x86_v2i64_cmp_bool_mask_extract();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate v2i64 bool mask extract");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    let cmp = entry
        .instructions
        .iter()
        .find(|inst| {
            matches!(
                inst.opcode,
                Opcode::V2I64Icmp {
                    cond: IntCC::SignedLessThan
                }
            )
        })
        .expect("v2i64 bool mask extract should reach typed compare LIR opcode");
    let extract = entry
        .instructions
        .iter()
        .find(|inst| {
            matches!(
                inst.opcode,
                Opcode::V2I64MaskExtract {
                    result_ty: Type::I32
                }
            )
        })
        .expect("v2i64 bool mask extract should reach typed mask extract LIR opcode");
    assert_eq!(extract.args, vec![cmp.results[0]]);
    assert_eq!(
        lir_func.value_types.get(&extract.results[0]),
        Some(&Type::I32)
    );
    assert_no_v2i64_icmp_adapter_lane_scalarization(&lir_func);

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonCmgtV), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 2);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LsrRI), 2);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::AndRI), 2);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LslRI), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::OrrRR), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::Csel), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
}

#[test]
fn test_aarch64_v2i64_add_sub_lower_to_neon_d2_without_scalar_lanes() {
    for (op, expected_lir, expected_aarch64, name, func_id) in [
        (
            BinOp::Add,
            Opcode::V2I64Add,
            AArch64Opcode::NeonAddV,
            "aarch64_v2i64_add",
            9312,
        ),
        (
            BinOp::Sub,
            Opcode::V2I64Sub,
            AArch64Opcode::NeonSubV,
            "aarch64_v2i64_sub",
            9313,
        ),
    ] {
        let module = build_narrow_vector_binop_store(ty_v2i64(), op, func_id, name);
        let (lir_func, _) = translate_only(&module).expect("adapter must translate v2i64 add/sub");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let arith_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed V2I64 arithmetic LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&arith_inst.results[0]),
            Some(&Type::V128)
        );
        assert!(
            entry
                .instructions
                .iter()
                .all(|inst| !matches!(inst.opcode, Opcode::ArrayGep { elem_ty: Type::I64 })),
            "{name} must not compute scalar i64 lane addresses"
        );

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, expected_aarch64), 1, "{name}");
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonLd1Post),
            0,
            "{name}"
        );
        assert_eq!(
            count_opcode(&mfunc, AArch64Opcode::NeonSt1Post),
            0,
            "{name}"
        );
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0, "{name}");
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0, "{name}");
    }
}

#[test]
fn test_aarch64_v2i64_mul_lowers_with_scalar_lane_multiply_and_repack() {
    let module = build_narrow_vector_binop_store(ty_v2i64(), BinOp::Mul, 9320, "aarch64_v2i64_mul");
    let (lir_func, _) = translate_only(&module).expect("adapter must translate v2i64 mul");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    let arith_inst = entry
        .instructions
        .iter()
        .find(|inst| inst.opcode == Opcode::V2I64Mul)
        .expect("v2i64 mul should reach typed arithmetic LIR opcode");
    assert_eq!(
        lir_func.value_types.get(&arith_inst.results[0]),
        Some(&Type::V128)
    );

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 4);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::MulRR), 2);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonDupGen), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonInsGen), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonMulV), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
}

#[test]
fn test_x86_v2i64_mul_lowers_with_scalar_lane_multiply_and_repack() {
    let module = build_narrow_vector_binop_store(ty_v2i64(), BinOp::Mul, 9256, "x86_v2i64_mul");
    let (lir_func, _) = translate_only(&module).expect("adapter must translate v2i64 mul");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    let arith_inst = entry
        .instructions
        .iter()
        .find(|inst| inst.opcode == Opcode::V2I64Mul)
        .expect("v2i64 mul should reach typed arithmetic LIR opcode");
    assert_eq!(
        lir_func.value_types.get(&arith_inst.results[0]),
        Some(&Type::V128)
    );

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovqFromXmm), 4);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::ImulRR), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovqToXmm), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pmuludq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pmulld), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM), 0);
}

#[test]
fn test_x86_v_narrow_i8_i16_eq_ne_cmp_lower_to_pcmpeq_without_lane_memory() {
    for (ty, op, expected_cond, expected_lir, expected_x86, name, func_id) in [
        (
            ty_v16i8(),
            ICmpOp::Eq,
            IntCC::Equal,
            Opcode::V16I8Icmp { cond: IntCC::Equal },
            X86Opcode::Pcmpeqb,
            "x86_v16i8_eq",
            9254,
        ),
        (
            ty_v16i8(),
            ICmpOp::Ne,
            IntCC::NotEqual,
            Opcode::V16I8Icmp {
                cond: IntCC::NotEqual,
            },
            X86Opcode::Pcmpeqb,
            "x86_v16i8_ne",
            9255,
        ),
        (
            ty_v8i16(),
            ICmpOp::Eq,
            IntCC::Equal,
            Opcode::V8I16Icmp { cond: IntCC::Equal },
            X86Opcode::Pcmpeqw,
            "x86_v8i16_eq",
            9256,
        ),
        (
            ty_v8i16(),
            ICmpOp::Ne,
            IntCC::NotEqual,
            Opcode::V8I16Icmp {
                cond: IntCC::NotEqual,
            },
            X86Opcode::Pcmpeqw,
            "x86_v8i16_ne",
            9257,
        ),
    ] {
        let module = build_x86_narrow_vector_icmp_store(ty, op, func_id, name);
        let (lir_func, _) = translate_only(&module).expect("adapter must translate narrow eq/ne");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let packed_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed narrow compare LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&packed_inst.results[0]),
            Some(&Type::V128)
        );
        assert!(matches!(
            packed_inst.opcode,
            Opcode::V16I8Icmp { cond } | Opcode::V8I16Icmp { cond } if cond == expected_cond
        ));
        assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&mfunc, expected_x86), 1, "{name}");
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd),
            if op == ICmpOp::Ne { 1 } else { 0 },
            "{name}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pxor),
            if op == ICmpOp::Ne { 1 } else { 0 },
            "{name}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrd), 0, "{name}");
        assert_no_x86_scalarized_vector_cmp_path(&mfunc);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1, "{name}");
    }
}

#[test]
fn test_x86_v_narrow_i8_i16_eq_ne_mask_to_bits_reaches_typed_lir_without_lane_memory() {
    for (ty, mask_ty, op, expected_cmp, expected_extract, name, func_id) in [
        (
            ty_v16i8(),
            ty_v16_bool(),
            ICmpOp::Eq,
            Opcode::V16I8Icmp { cond: IntCC::Equal },
            Opcode::V16I8MaskExtract,
            "x86_v16i8_eq_mask_to_bits",
            9270,
        ),
        (
            ty_v16i8(),
            ty_v16_bool(),
            ICmpOp::Ne,
            Opcode::V16I8Icmp {
                cond: IntCC::NotEqual,
            },
            Opcode::V16I8MaskExtract,
            "x86_v16i8_ne_mask_to_bits",
            9271,
        ),
        (
            ty_v8i16(),
            ty_v8_bool(),
            ICmpOp::Eq,
            Opcode::V8I16Icmp { cond: IntCC::Equal },
            Opcode::V8I16MaskExtract,
            "x86_v8i16_eq_mask_to_bits",
            9272,
        ),
        (
            ty_v8i16(),
            ty_v8_bool(),
            ICmpOp::Ne,
            Opcode::V8I16Icmp {
                cond: IntCC::NotEqual,
            },
            Opcode::V8I16MaskExtract,
            "x86_v8i16_ne_mask_to_bits",
            9273,
        ),
    ] {
        let module = build_x86_narrow_vector_icmp_mask_to_bits(ty, mask_ty, op, func_id, name);
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate narrow mask_to_bits");
        let entry = &lir_func.blocks[&lir_func.entry_block];

        let cmp = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_cmp)
            .unwrap_or_else(|| panic!("{name} should reach typed narrow compare LIR opcode"));
        assert_eq!(lir_func.value_types.get(&cmp.results[0]), Some(&Type::V128));

        let extract = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_extract)
            .unwrap_or_else(|| panic!("{name} should reach typed narrow mask extract LIR opcode"));
        assert_eq!(extract.args, vec![cmp.results[0]]);
        assert_eq!(
            lir_func.value_types.get(&extract.results[0]),
            Some(&Type::I32)
        );
        assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);
    }
}

#[test]
fn test_x86_v_narrow_i8_i16_signed_cmp_lower_to_pcmpgt_without_lane_memory() {
    for (
        ty,
        op,
        expected_cond,
        expected_lir,
        expected_gt,
        expected_eq,
        expected_gt_count,
        expected_eq_count,
        expected_por_count,
        name,
        func_id,
    ) in [
        (
            ty_v16i8(),
            ICmpOp::Sgt,
            IntCC::SignedGreaterThan,
            Opcode::V16I8Icmp {
                cond: IntCC::SignedGreaterThan,
            },
            X86Opcode::Pcmpgtb,
            X86Opcode::Pcmpeqb,
            1,
            0,
            0,
            "x86_v16i8_sgt",
            9258,
        ),
        (
            ty_v16i8(),
            ICmpOp::Slt,
            IntCC::SignedLessThan,
            Opcode::V16I8Icmp {
                cond: IntCC::SignedLessThan,
            },
            X86Opcode::Pcmpgtb,
            X86Opcode::Pcmpeqb,
            1,
            0,
            0,
            "x86_v16i8_slt",
            9259,
        ),
        (
            ty_v16i8(),
            ICmpOp::Sge,
            IntCC::SignedGreaterThanOrEqual,
            Opcode::V16I8Icmp {
                cond: IntCC::SignedGreaterThanOrEqual,
            },
            X86Opcode::Pcmpgtb,
            X86Opcode::Pcmpeqb,
            1,
            1,
            1,
            "x86_v16i8_sge",
            9260,
        ),
        (
            ty_v16i8(),
            ICmpOp::Sle,
            IntCC::SignedLessThanOrEqual,
            Opcode::V16I8Icmp {
                cond: IntCC::SignedLessThanOrEqual,
            },
            X86Opcode::Pcmpgtb,
            X86Opcode::Pcmpeqb,
            1,
            1,
            1,
            "x86_v16i8_sle",
            9261,
        ),
        (
            ty_v8i16(),
            ICmpOp::Sgt,
            IntCC::SignedGreaterThan,
            Opcode::V8I16Icmp {
                cond: IntCC::SignedGreaterThan,
            },
            X86Opcode::Pcmpgtw,
            X86Opcode::Pcmpeqw,
            1,
            0,
            0,
            "x86_v8i16_sgt",
            9262,
        ),
        (
            ty_v8i16(),
            ICmpOp::Slt,
            IntCC::SignedLessThan,
            Opcode::V8I16Icmp {
                cond: IntCC::SignedLessThan,
            },
            X86Opcode::Pcmpgtw,
            X86Opcode::Pcmpeqw,
            1,
            0,
            0,
            "x86_v8i16_slt",
            9263,
        ),
        (
            ty_v8i16(),
            ICmpOp::Sge,
            IntCC::SignedGreaterThanOrEqual,
            Opcode::V8I16Icmp {
                cond: IntCC::SignedGreaterThanOrEqual,
            },
            X86Opcode::Pcmpgtw,
            X86Opcode::Pcmpeqw,
            1,
            1,
            1,
            "x86_v8i16_sge",
            9264,
        ),
        (
            ty_v8i16(),
            ICmpOp::Sle,
            IntCC::SignedLessThanOrEqual,
            Opcode::V8I16Icmp {
                cond: IntCC::SignedLessThanOrEqual,
            },
            X86Opcode::Pcmpgtw,
            X86Opcode::Pcmpeqw,
            1,
            1,
            1,
            "x86_v8i16_sle",
            9265,
        ),
    ] {
        let module = build_x86_narrow_vector_icmp_store(ty, op, func_id, name);
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate signed narrow icmp");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let packed_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed narrow compare LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&packed_inst.results[0]),
            Some(&Type::V128)
        );
        assert!(matches!(
            packed_inst.opcode,
            Opcode::V16I8Icmp { cond } | Opcode::V8I16Icmp { cond } if cond == expected_cond
        ));
        assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(
            count_x86_opcode(&mfunc, expected_gt),
            expected_gt_count,
            "{name}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, expected_eq),
            expected_eq_count,
            "{name}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Por),
            expected_por_count,
            "{name}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrd), 0, "{name}");
        assert_no_x86_scalarized_vector_cmp_path(&mfunc);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM8), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM16), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1, "{name}");
    }
}

#[test]
fn test_x86_v_narrow_i8_i16_unsigned_cmp_lower_with_sse2_sign_bias() {
    for (
        ty,
        op,
        expected_cond,
        expected_lir,
        expected_gt,
        expected_eq,
        expected_eq_count,
        expected_por_count,
        expected_bias,
        name,
        func_id,
    ) in [
        (
            ty_v16i8(),
            ICmpOp::Ugt,
            IntCC::UnsignedGreaterThan,
            Opcode::V16I8Icmp {
                cond: IntCC::UnsignedGreaterThan,
            },
            X86Opcode::Pcmpgtb,
            X86Opcode::Pcmpeqb,
            0,
            0,
            0x8080_8080_u32 as i32 as i64,
            "x86_v16i8_ugt",
            9353,
        ),
        (
            ty_v8i16(),
            ICmpOp::Ule,
            IntCC::UnsignedLessThanOrEqual,
            Opcode::V8I16Icmp {
                cond: IntCC::UnsignedLessThanOrEqual,
            },
            X86Opcode::Pcmpgtw,
            X86Opcode::Pcmpeqw,
            1,
            1,
            0x8000_8000_u32 as i32 as i64,
            "x86_v8i16_ule",
            9354,
        ),
    ] {
        let module = build_x86_narrow_vector_icmp_store(ty, op, func_id, name);
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate unsigned narrow icmp");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let packed_inst = entry
            .instructions
            .iter()
            .find(|inst| inst.opcode == expected_lir)
            .unwrap_or_else(|| panic!("{name} should reach typed narrow compare LIR opcode"));
        assert_eq!(
            lir_func.value_types.get(&packed_inst.results[0]),
            Some(&Type::V128)
        );
        assert!(matches!(
            packed_inst.opcode,
            Opcode::V16I8Icmp { cond } | Opcode::V8I16Icmp { cond } if cond == expected_cond
        ));
        assert_no_narrow_i8_i16_adapter_lane_memory(&lir_func, name);

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(
            x86_opcode_imms(&mfunc, X86Opcode::MovRI),
            vec![expected_bias]
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 1, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 1, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 2, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, expected_gt), 1, "{name}");
        assert_eq!(
            count_x86_opcode(&mfunc, expected_eq),
            expected_eq_count,
            "{name}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Por),
            expected_por_count,
            "{name}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0, "{name}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrd), 0, "{name}");
        assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    }
}

#[test]
fn test_x86_v_narrow_i8_i16_unsupported_ops_fail_closed() {
    {
        let (ty, inst, message) = (
            ty_v16i8(),
            Inst::BinOp {
                op: BinOp::UDiv,
                ty: ty_v16i8(),
                lhs: v(0),
                rhs: v(1),
            },
            "<16 x i8> BinOp::UDiv",
        );
        let param_ty = ty.clone();
        let module = single_function_module(
            9254,
            "x86_narrow_reject",
            func_ty(vec![param_ty.clone(), param_ty.clone()], vec![]),
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), param_ty.clone()), (v(1), param_ty)],
                body: vec![InstrNode::new(inst).with_result(v(2))],
            }],
            vec![],
        );
        let err = translate_only(&module).expect_err("unsupported narrow vector op must fail");
        assert!(
            matches!(err, AdapterError::UnsupportedInstruction(ref text) if text.contains(message)),
            "unexpected fail-closed diagnostic: {err:?}"
        );
    }
}

#[test]
fn test_x86_v4i32_logic_cmp_copy_and_memory_lower_to_sse2() {
    let module = build_x86_v4i32_logic_cmp_copy_store();
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pand), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Por), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pmulld), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 1);
    assert!(
        has_x86_opcode(&mfunc, X86Opcode::MovdqaRR),
        "expected vector Copy to lower to MovdqaRR"
    );
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1);
}

fn build_x86_v4i32_signed_cmp_masks() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9102,
        "x86_v4i32_signed_cmp_masks",
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: v4i32,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v4i32_unsigned_cmp_masks() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9128,
        "x86_v4i32_unsigned_cmp_masks",
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ult,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ule,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ugt,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Uge,
                    ty: v4i32,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v4i32_ne_cmp_mask_store() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9106,
        "x86_v4i32_ne_cmp_mask_store",
        func_ty(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr), (v(2), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: v4i32,
                    ptr: v(2),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v4i32_repeated_ne_cmp_masks() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9109,
        "x86_v4i32_repeated_ne_cmp_masks",
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: v4i32,
                    lhs: v(11),
                    rhs: v(10),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v4i32_signed_cmp_masks_lower_to_sse2() {
    let module = build_x86_v4i32_signed_cmp_masks();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate signed v4i32 compares");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    let direct_conds: Vec<IntCC> = entry
        .instructions
        .iter()
        .filter_map(|inst| match inst.opcode {
            Opcode::V4I32Icmp { cond } => Some(cond),
            _ => None,
        })
        .collect();
    assert_eq!(
        direct_conds,
        vec![
            IntCC::SignedLessThan,
            IntCC::SignedLessThanOrEqual,
            IntCC::SignedGreaterThan,
            IntCC::SignedGreaterThanOrEqual,
        ]
    );
    assert_no_v4i32_icmp_adapter_lane_scalarization(&lir_func);

    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 4);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Por), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
}

#[test]
fn test_v4i32_unsigned_cmp_masks_lower_with_aarch64_x86_parity() {
    let module = build_x86_v4i32_unsigned_cmp_masks();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate v4i32 unsigned compares");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    let direct_conds: Vec<IntCC> = entry
        .instructions
        .iter()
        .filter_map(|inst| match inst.opcode {
            Opcode::V4I32Icmp { cond } => Some(cond),
            _ => None,
        })
        .collect();
    assert_eq!(
        direct_conds,
        vec![
            IntCC::UnsignedLessThan,
            IntCC::UnsignedLessThanOrEqual,
            IntCC::UnsignedGreaterThan,
            IntCC::UnsignedGreaterThanOrEqual,
        ]
    );
    assert_no_v4i32_icmp_adapter_lane_scalarization(&lir_func);

    let aarch64 = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&aarch64, AArch64Opcode::NeonCmhiV), 2);
    assert_eq!(count_opcode(&aarch64, AArch64Opcode::NeonCmhsV), 2);
    assert_eq!(count_opcode(&aarch64, AArch64Opcode::CmpRR), 0);
    assert_eq!(count_opcode(&aarch64, AArch64Opcode::CSet), 0);

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRI), 1);
    assert_eq!(
        x86_opcode_imms(&mfunc, X86Opcode::MovRI),
        vec![i32::MIN as i64]
    );
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 1);
    assert_eq!(x86_opcode_imms(&mfunc, X86Opcode::Pshufd), vec![0]);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 8);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 4);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Por), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Cmovcc), 0);
    assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
}

#[test]
fn test_x86_v4i32_ne_cmp_mask_lowers_direct_without_scalar_lane_fallback() {
    let module = build_x86_v4i32_ne_cmp_mask_store();
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Cmovcc), 0);
    assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1);
}

#[test]
fn test_x86_v4i32_repeated_ne_cmp_masks_reuse_one_all_ones_materialization() {
    let module = build_x86_v4i32_repeated_ne_cmp_masks();
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 3);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 0);
    assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
}

fn build_x86_v2i64_signed_cmp_masks() -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9110,
        "x86_v2i64_signed_cmp_masks",
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: v2i64.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: v2i64.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: v2i64.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: v2i64,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v2i64_cmp_bool_mask_extract() -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9114,
        "x86_v2i64_cmp_bool_mask_extract",
        func_ty(vec![v2i64.clone(), v2i64.clone()], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), v2i64.clone()), (v(1), v2i64.clone())],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: v2i64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    bitfield_dialect::v2i64_bool_mask_extract(v(2), Ty::I32),
                )))
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v2i64_boundary_cmp_masks() -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9112,
        "x86_v2i64_boundary_cmp_masks",
        func_ty(vec![], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(vec![
                        Constant::Int(i64::MIN as i128),
                        Constant::Int(i64::MAX as i128),
                    ]),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(vec![
                        Constant::Int(i64::MIN as i128),
                        Constant::Int(0),
                    ]),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: v2i64.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(20)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: v2i64.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(21)),
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(vec![Constant::Int(-1), Constant::Int(0)]),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(vec![Constant::Int(0), Constant::Int(1)]),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: v2i64.clone(),
                    lhs: v(12),
                    rhs: v(13),
                })
                .with_result(v(22)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: v2i64.clone(),
                    lhs: v(12),
                    rhs: v(13),
                })
                .with_result(v(23)),
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(vec![
                        Constant::Int(1),
                        Constant::Int(i64::MAX as i128),
                    ]),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(vec![Constant::Int(0), Constant::Int(-1)]),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: v2i64.clone(),
                    lhs: v(14),
                    rhs: v(15),
                })
                .with_result(v(24)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: v2i64,
                    lhs: v(14),
                    rhs: v(15),
                })
                .with_result(v(25)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v2i64_signed_cmp_masks_lower_to_packed_qword_ops() {
    let module = build_x86_v2i64_signed_cmp_masks();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate v2i64 signed compares");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    let direct_conds: Vec<IntCC> = entry
        .instructions
        .iter()
        .filter_map(|inst| match inst.opcode {
            Opcode::V2I64Icmp { cond } => Some(cond),
            _ => None,
        })
        .collect();
    assert_eq!(
        direct_conds,
        vec![
            IntCC::SignedLessThan,
            IntCC::SignedLessThanOrEqual,
            IntCC::SignedGreaterThan,
            IntCC::SignedGreaterThanOrEqual,
        ]
    );
    assert_no_v2i64_icmp_adapter_lane_scalarization(&lir_func);

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtq), 4);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqq), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Por), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 0);
    assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Cmovcc), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM), 0);
}

#[test]
fn test_x86_v2i64_cmp_bool_mask_extract_lowers_without_select_bridge() {
    let module = build_x86_v2i64_cmp_bool_mask_extract();
    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtq), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::V2I64MaskExtract), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM), 0);
}

#[test]
fn test_x86_v2i64_boundary_cmp_masks_lower_to_packed_qword_ops() {
    let module = build_x86_v2i64_boundary_cmp_masks();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate v2i64 boundary compares");

    let i64_imms: Vec<i64> = lir_func
        .blocks
        .values()
        .flat_map(|block| block.instructions.iter())
        .filter_map(|inst| match inst.opcode {
            Opcode::Iconst { ty: Type::I64, imm } => Some(imm),
            _ => None,
        })
        .collect();
    for imm in [i64::MIN, i64::MAX, -1, 0, 1] {
        assert!(
            i64_imms.contains(&imm),
            "v2i64 boundary constant {imm} must remain an i64 lane immediate"
        );
    }

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtq), 4);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqq), 4);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Por), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 5);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 0);
    assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Cmovcc), 0);
}

fn build_x86_v2i64_eq_ne_cmp_masks() -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9111,
        "x86_v2i64_eq_ne_cmp_masks",
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: v2i64.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: v2i64,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v2i64_repeated_ne_cmp_masks() -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9113,
        "x86_v2i64_repeated_ne_cmp_masks",
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: v2i64.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: v2i64,
                    lhs: v(11),
                    rhs: v(10),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v2i64_unsigned_cmp(op: ICmpOp) -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9115,
        "x86_v2i64_unsigned_cmp",
        func_ty(vec![v2i64.clone(), v2i64.clone()], vec![ty_v2_bool()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), v2i64.clone()), (v(1), v2i64.clone())],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: v2i64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v2i64_eq_ne_cmp_masks_lower_to_packed_qword_ops() {
    let module = build_x86_v2i64_eq_ne_cmp_masks();
    let (lir_func, _) =
        translate_only(&module).expect("adapter must translate v2i64 eq/ne compares");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    let direct_conds: Vec<IntCC> = entry
        .instructions
        .iter()
        .filter_map(|inst| match inst.opcode {
            Opcode::V2I64Icmp { cond } => Some(cond),
            _ => None,
        })
        .collect();
    assert_eq!(direct_conds, vec![IntCC::Equal, IntCC::NotEqual]);
    assert_no_v2i64_icmp_adapter_lane_scalarization(&lir_func);

    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqq), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 1);
    assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Cmovcc), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM), 0);
}

#[test]
fn test_x86_v2i64_repeated_ne_cmp_masks_reuse_one_all_ones_materialization() {
    let module = build_x86_v2i64_repeated_ne_cmp_masks();
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqq), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtq), 0);
    assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
}

#[test]
fn test_x86_v2i64_unsigned_cmp_masks_lower_to_sse2_dword_halves() {
    for (op, expected_cond, inclusive) in [
        (ICmpOp::Ult, IntCC::UnsignedLessThan, false),
        (ICmpOp::Ule, IntCC::UnsignedLessThanOrEqual, true),
        (ICmpOp::Ugt, IntCC::UnsignedGreaterThan, false),
        (ICmpOp::Uge, IntCC::UnsignedGreaterThanOrEqual, true),
    ] {
        let module = build_x86_v2i64_unsigned_cmp(op);
        let (lir_func, _) =
            translate_only(&module).expect("adapter must translate v2i64 unsigned compares");
        let entry = &lir_func.blocks[&lir_func.entry_block];
        let direct_conds: Vec<IntCC> = entry
            .instructions
            .iter()
            .filter_map(|inst| match inst.opcode {
                Opcode::V2I64Icmp { cond } => Some(cond),
                _ => None,
            })
            .collect();
        assert_eq!(direct_conds, vec![expected_cond], "ICmp::{op:?}");
        assert_no_v2i64_icmp_adapter_lane_scalarization(&lir_func);

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRI), 1, "{op:?}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 1, "{op:?}");
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pshufd),
            if inclusive { 5 } else { 4 },
            "{op:?}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 2, "{op:?}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtd), 1, "{op:?}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 1, "{op:?}");
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Pand),
            if inclusive { 2 } else { 1 },
            "{op:?}"
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Por),
            if inclusive { 2 } else { 1 },
            "{op:?}"
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpgtq), 0, "{op:?}");
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqq), 0, "{op:?}");
        assert_no_x86_scalarized_vector_cmp_path(&mfunc);
    }
}

fn build_x86_v4i32_select_bitselect() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9101,
        "x86_v4i32_select_bitselect",
        func_ty(vec![Ty::Ptr, Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Select {
                    ty: v4i32,
                    cond: v(12),
                    then_val: v(10),
                    else_val: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v4i32_select_with_vector_mask_lowers_to_bool_select_pseudo() {
    let module = build_x86_v4i32_select_bitselect();
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pcmpeqd), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::V128BoolSelect), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pand), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pandn), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Por), 0);
}

fn build_x86_v4i32_extract_element_const_index(lane: i128) -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9105,
        "x86_v4i32_extract_element_const_index",
        func_ty(vec![v4i32.clone()], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), v4i32)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(lane),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::I32,
                    array: v(0),
                    index: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v4i32_extract_element_const_lane_lowers_to_sse2_shuffle_movd() {
    let module = build_x86_v4i32_extract_element_const_index(2);
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v4i32 extract lane");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v4i32 extract lane should avoid adapter stack materialization"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V4I32ExtractLane { lane: 2 }))
    );

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdFromXmm), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
}

#[test]
fn test_aarch64_v4i32_extract_element_const_lane_lowers_to_neon_umov_without_stack_or_memory() {
    let module = build_x86_v4i32_extract_element_const_index(2);
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v4i32 extract lane");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v4i32 extract lane should avoid adapter stack materialization"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V4I32ExtractLane { lane: 2 }))
    );

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
}

fn build_x86_v4i32_extract_element_dynamic_index() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9108,
        "x86_v4i32_extract_element_dynamic_index",
        func_ty(vec![v4i32.clone(), Ty::I64], vec![Ty::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), v4i32), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::I32,
                    array: v(0),
                    index: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v4i32_extract_element_dynamic_lane_fails_closed() {
    let err =
        try_compile_trust_ir_function_x86_64(&build_x86_v4i32_extract_element_dynamic_index())
            .expect_err("dynamic vector ExtractElement lane must fail closed");

    assert!(
        err.contains("vector ExtractElement requires i64 constant lane index 0..3"),
        "unexpected vector ExtractElement dynamic-lane diagnostic: {err}"
    );
}

fn build_x86_v4i32_insert_element_const_index(lane: i128) -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9106,
        "x86_v4i32_insert_element_const_index",
        func_ty(vec![v4i32.clone(), Ty::I32], vec![v4i32.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), v4i32.clone()), (v(2), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(lane),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::InsertElement {
                    ty: v4i32,
                    array: v(0),
                    index: v(1),
                    value: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v4i32_zero_insert_element_const_index(lane: i128) -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9159,
        "x86_v4i32_zero_insert_element_const_index",
        func_ty(vec![Ty::I32], vec![v4i32.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(lane),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: v4i32.clone(),
                    value: Constant::Vector(vec![
                        Constant::Int(0),
                        Constant::Int(0),
                        Constant::Int(0),
                        Constant::Int(0),
                    ]),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::InsertElement {
                    ty: v4i32,
                    array: v(2),
                    index: v(1),
                    value: v(0),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v4i32_full_lane_pack() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9112,
        "x86_v4i32_full_lane_pack",
        func_ty(
            vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32],
            vec![v4i32.clone()],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), Ty::I32),
                (v(1), Ty::I32),
                (v(2), Ty::I32),
                (v(3), Ty::I32),
            ],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(3),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Const {
                    ty: v4i32.clone(),
                    value: Constant::Vector(vec![
                        Constant::Int(0),
                        Constant::Int(0),
                        Constant::Int(0),
                        Constant::Int(0),
                    ]),
                })
                .with_result(v(20)),
                InstrNode::new(Inst::InsertElement {
                    ty: v4i32.clone(),
                    array: v(20),
                    index: v(10),
                    value: v(0),
                })
                .with_result(v(21)),
                InstrNode::new(Inst::InsertElement {
                    ty: v4i32.clone(),
                    array: v(21),
                    index: v(11),
                    value: v(1),
                })
                .with_result(v(22)),
                InstrNode::new(Inst::InsertElement {
                    ty: v4i32.clone(),
                    array: v(22),
                    index: v(12),
                    value: v(2),
                })
                .with_result(v(23)),
                InstrNode::new(Inst::InsertElement {
                    ty: v4i32,
                    array: v(23),
                    index: v(13),
                    value: v(3),
                })
                .with_result(v(24)),
                InstrNode::new(Inst::Return {
                    values: vec![v(24)],
                }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v4i32_insert_element_const_lane_nonzero_base_lowers_to_sse2() {
    for (lane, pshufd_count) in [(0_i128, 3), (1, 2), (2, 2), (3, 2)] {
        let module = build_x86_v4i32_insert_element_const_index(lane);
        let (lir_func, _) = translate_only(&module).expect("adapter must lower v4i32 insert lane");
        assert!(
            lir_func.stack_slots.is_empty(),
            "v4i32 insert lane should avoid adapter stack materialization"
        );

        let entry = &lir_func.blocks[&lir_func.entry_block];
        assert!(entry.instructions.iter().any(
            |i| matches!(i.opcode, Opcode::V4I32InsertLane { lane: actual } if actual == lane as u8)
        ));

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdFromXmm), 3);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), pshufd_count);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 4);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpckldq), 2);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
    }
}

#[test]
fn test_aarch64_v4i32_insert_element_const_lane_nonzero_base_lowers_to_neon_ins_without_memory() {
    for lane in 0_i128..=3 {
        let module = build_x86_v4i32_insert_element_const_index(lane);
        let (lir_func, _) = translate_only(&module).expect("adapter must lower v4i32 insert lane");
        assert!(
            lir_func.stack_slots.is_empty(),
            "v4i32 insert lane should avoid adapter stack materialization"
        );

        let entry = &lir_func.blocks[&lir_func.entry_block];
        assert!(entry.instructions.iter().any(
            |i| matches!(i.opcode, Opcode::V4I32InsertLane { lane: actual } if actual == lane as u8)
        ));

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonInsGen), 1);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
    }
}

#[test]
fn test_x86_v4i32_insert_element_const_lane_zero_base_lowers_to_sse2() {
    for (lane, punpckldq_count, punpcklqdq_count, pshufd_count) in
        [(1_u8, 1, 0, 0), (2, 0, 1, 0), (3, 1, 0, 1)]
    {
        let module = build_x86_v4i32_zero_insert_element_const_index(i128::from(lane));
        let (lir_func, _) =
            translate_only(&module).expect("adapter must lower zero-base v4i32 insert lane");
        assert!(
            lir_func.stack_slots.is_empty(),
            "zero-base v4i32 insert lane should avoid adapter stack materialization"
        );
        let entry = &lir_func.blocks[&lir_func.entry_block];
        assert!(
            entry
                .instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::V4I32Zero)),
            "zero-base v4i32 insert lane should materialize a direct zero vector"
        );
        assert!(entry.instructions.iter().any(
            |i| matches!(i.opcode, Opcode::V4I32InsertLane { lane: actual } if actual == lane)
        ));

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 1);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 1);
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Punpckldq),
            punpckldq_count
        );
        assert_eq!(
            count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq),
            punpcklqdq_count
        );
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), pshufd_count);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM32), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
    }
}

#[test]
fn test_aarch64_v4i32_insert_element_const_lane_zero_base_lowers_to_neon_movi_ins_without_memory() {
    for lane in 1_u8..=3 {
        let module = build_x86_v4i32_zero_insert_element_const_index(i128::from(lane));
        let (lir_func, _) =
            translate_only(&module).expect("adapter must lower zero-base v4i32 insert lane");
        assert!(
            lir_func.stack_slots.is_empty(),
            "zero-base v4i32 insert lane should avoid adapter stack materialization"
        );
        let entry = &lir_func.blocks[&lir_func.entry_block];
        assert!(
            entry
                .instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::V4I32Zero)),
            "zero-base v4i32 insert lane should materialize a direct zero vector"
        );
        assert!(entry.instructions.iter().any(
            |i| matches!(i.opcode, Opcode::V4I32InsertLane { lane: actual } if actual == lane)
        ));

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonMovi), 1);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonInsGen), 1);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
    }
}

#[test]
fn test_x86_v4i32_full_insert_chain_lowers_through_sse2_packs() {
    let module = build_x86_v4i32_full_lane_pack();
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v4i32 lane pack");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v4i32 insert chain should avoid adapter stack materialization"
    );
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V4I32Zero)),
        "v4i32 insert chain should materialize a direct zero vector"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::V4I32InsertLane { .. }))
            .count(),
        4
    );

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 13);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdFromXmm), 9);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 6);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpckldq), 6);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 3);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovqToXmm), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
}

#[test]
fn test_x86_v4i32_insert_element_out_of_range_lane_fails_closed() {
    let err = try_compile_trust_ir_function_x86_64(&build_x86_v4i32_insert_element_const_index(4))
        .expect_err("out-of-range vector InsertElement lane must fail closed");

    assert!(
        err.contains("vector InsertElement requires i64 constant lane index 0..3")
            && err.contains("got 4"),
        "unexpected vector InsertElement out-of-range diagnostic: {err}"
    );
}

fn build_x86_v4i32_pack_lanes_dialect() -> TrustIrModule {
    let v4i32 = ty_v4i32();
    single_function_module(
        9137,
        "x86_v4i32_pack_lanes_dialect",
        func_ty(
            vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32],
            vec![v4i32.clone()],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), Ty::I32),
                (v(1), Ty::I32),
                (v(2), Ty::I32),
                (v(3), Ty::I32),
            ],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(v4i32, [v(0), v(1), v(2), v(3)]),
                )))
                .with_result(v(4)),
                InstrNode::new(Inst::Return { values: vec![v(4)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v4i32_pack_lanes_dialect_lowers_to_sse2_movd_unpacks_without_stack() {
    let module = build_x86_v4i32_pack_lanes_dialect();
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v4i32 pack_lanes");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v4i32 pack_lanes should avoid adapter stack slots"
    );
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions[0].opcode, Opcode::V4I32PackLanes);

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 4);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpckldq), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
}

#[test]
fn test_aarch64_v4i32_pack_lanes_dialect_lowers_to_neon_dup_ins_without_stack() {
    let module = build_x86_v4i32_pack_lanes_dialect();
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v4i32 pack_lanes");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v4i32 pack_lanes should avoid adapter stack slots"
    );
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions[0].opcode, Opcode::V4I32PackLanes);

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonDupGen), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonInsGen), 3);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonMovi), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
}

fn build_x86_v2i64_pack_lanes_dialect() -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9138,
        "x86_v2i64_pack_lanes_dialect",
        func_ty(vec![Ty::I64, Ty::I64], vec![v2i64.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(v2i64, [v(0), v(1)]),
                )))
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v2i64_pack_lanes_dialect_lowers_to_sse2_movq_unpack_without_stack() {
    let module = build_x86_v2i64_pack_lanes_dialect();
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v2i64 pack_lanes");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v2i64 pack_lanes should avoid adapter stack slots"
    );
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions[0].opcode, Opcode::V2I64PackLanes);

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovqToXmm), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
}

#[test]
fn test_aarch64_v2i64_pack_lanes_dialect_lowers_to_neon_dup_ins_without_stack() {
    let module = build_x86_v2i64_pack_lanes_dialect();
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v2i64 pack_lanes");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v2i64 pack_lanes should avoid adapter stack slots"
    );
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert_eq!(entry.instructions[0].opcode, Opcode::V2I64PackLanes);

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonDupGen), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonInsGen), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonMovi), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
}

fn build_narrow_pack_lanes_dialect(ty: Ty, lane_ty: Ty, lanes: u32, name: &str) -> TrustIrModule {
    let lane_values = (0..lanes).map(v).collect::<Vec<_>>();
    single_function_module(
        9167,
        name,
        func_ty(vec![lane_ty.clone(); lanes as usize], vec![ty.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: lane_values
                .iter()
                .copied()
                .map(|value| (value, lane_ty.clone()))
                .collect(),
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(vector_dialect::pack_lanes(
                    ty,
                    lane_values.clone(),
                ))))
                .with_result(v(100)),
                InstrNode::new(Inst::Return {
                    values: vec![v(100)],
                }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_narrow_pack_lanes_dialect_lowers_to_scalar_bitfields_sse2_without_stack() {
    for (module, expected_opcode, lane_ty, lanes, shl_count) in [
        (
            build_narrow_pack_lanes_dialect(ty_v16i8(), Ty::I8, 16, "x86_v16i8_pack_lanes_dialect"),
            Opcode::V16I8PackLanes,
            Type::I8,
            16,
            12,
        ),
        (
            build_narrow_pack_lanes_dialect(ty_v8i16(), Ty::I16, 8, "x86_v8i16_pack_lanes_dialect"),
            Opcode::V8I16PackLanes,
            Type::I16,
            8,
            4,
        ),
    ] {
        let (lir_func, _) = translate_only(&module).expect("adapter must lower narrow pack_lanes");
        assert_vector_const_uses_pack_lanes_without_stack(
            &lir_func,
            lane_ty,
            expected_opcode,
            "narrow pack_lanes dialect",
        );

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 4);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpckldq), 2);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::ShlRI), shl_count);
        assert!(count_x86_opcode(&mfunc, X86Opcode::AndRR) >= lanes);
        assert!(count_x86_opcode(&mfunc, X86Opcode::OrRR) >= lanes - 4);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrd), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM32), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
    }
}

#[test]
fn test_aarch64_narrow_pack_lanes_dialect_lowers_to_neon_dup_ins_without_stack() {
    for (module, expected_opcode, lane_ty, ins_count) in [
        (
            build_narrow_pack_lanes_dialect(
                ty_v16i8(),
                Ty::I8,
                16,
                "aarch64_v16i8_pack_lanes_dialect",
            ),
            Opcode::V16I8PackLanes,
            Type::I8,
            15,
        ),
        (
            build_narrow_pack_lanes_dialect(
                ty_v8i16(),
                Ty::I16,
                8,
                "aarch64_v8i16_pack_lanes_dialect",
            ),
            Opcode::V8I16PackLanes,
            Type::I16,
            7,
        ),
    ] {
        let (lir_func, _) = translate_only(&module).expect("adapter must lower narrow pack_lanes");
        assert_vector_const_uses_pack_lanes_without_stack(
            &lir_func,
            lane_ty,
            expected_opcode,
            "narrow pack_lanes dialect",
        );

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonDupGen), 1);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonInsGen), ins_count);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonMovi), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
    }
}

fn build_x86_v2i64_const_store(func_id: u32, name: &str, value: Constant) -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        func_id,
        name,
        func_ty(vec![Ty::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: v2i64,
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v2i64_vector_constant_forms_lower_to_pack_lanes_without_stack() {
    for (name, value) in [
        (
            "array",
            Constant::Array(vec![Constant::Int(i64::MIN as i128), Constant::Int(42)]),
        ),
        (
            "aggregate",
            Constant::Aggregate(vec![Constant::Int(17), Constant::Int(i64::MAX as i128)]),
        ),
        (
            "vector",
            Constant::Vector(vec![Constant::Int(i64::MIN as i128), Constant::Int(42)]),
        ),
    ] {
        let module =
            build_x86_v2i64_const_store(9113, &format!("x86_v2i64_{name}_const_store"), value);
        let (lir_func, _) = translate_only(&module).expect("adapter must translate v2i64 constant");
        assert_vector_const_uses_pack_lanes_without_stack(
            &lir_func,
            Type::I64,
            Opcode::V2I64PackLanes,
            name,
        );
    }

    let module = build_x86_v2i64_const_store(
        9113,
        "x86_v2i64_const_store",
        Constant::Vector(vec![Constant::Int(i64::MIN as i128), Constant::Int(42)]),
    );

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRI), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovqToXmm), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
}

fn build_x86_v2i64_extract_element_const_index(lane: i128) -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9114,
        "x86_v2i64_extract_element_const_index",
        func_ty(vec![v2i64.clone()], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), v2i64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(lane),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::I64,
                    array: v(0),
                    index: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v2i64_extract_element_const_lane_lowers_to_sse2_shuffle_movq() {
    let module = build_x86_v2i64_extract_element_const_index(1);
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v2i64 extract lane");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v2i64 extract lane should avoid adapter stack materialization"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V2I64ExtractLane { lane: 1 }))
    );

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovqFromXmm), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pextrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
}

#[test]
fn test_aarch64_v2i64_extract_element_const_lane_lowers_to_neon_umov_without_stack_or_memory() {
    let module = build_x86_v2i64_extract_element_const_index(1);
    let (lir_func, _) = translate_only(&module).expect("adapter must lower v2i64 extract lane");
    assert!(
        lir_func.stack_slots.is_empty(),
        "v2i64 extract lane should avoid adapter stack materialization"
    );

    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V2I64ExtractLane { lane: 1 }))
    );

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
}

fn build_x86_v2i64_extract_element_dynamic_index() -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9115,
        "x86_v2i64_extract_element_dynamic_index",
        func_ty(vec![v2i64.clone(), Ty::I64], vec![Ty::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), v2i64), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::I64,
                    array: v(0),
                    index: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v2i64_extract_element_dynamic_lane_fails_closed() {
    let err =
        try_compile_trust_ir_function_x86_64(&build_x86_v2i64_extract_element_dynamic_index())
            .expect_err("dynamic v2i64 ExtractElement lane must fail closed");

    assert!(
        err.contains("vector ExtractElement requires i64 constant lane index 0..1"),
        "unexpected v2i64 ExtractElement dynamic-lane diagnostic: {err}"
    );
}

fn build_x86_v2i64_insert_element_const_index(lane: i128) -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9116,
        "x86_v2i64_insert_element_const_index",
        func_ty(vec![v2i64.clone(), Ty::I64], vec![v2i64.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), v2i64.clone()), (v(2), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(lane),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::InsertElement {
                    ty: v2i64,
                    array: v(0),
                    index: v(1),
                    value: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

fn build_x86_v2i64_zero_insert_element_const_index(lane: i128) -> TrustIrModule {
    let v2i64 = ty_v2i64();
    single_function_module(
        9160,
        "x86_v2i64_zero_insert_element_const_index",
        func_ty(vec![Ty::I64], vec![v2i64.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(lane),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(vec![Constant::Int(0), Constant::Int(0)]),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::InsertElement {
                    ty: v2i64,
                    array: v(2),
                    index: v(1),
                    value: v(0),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
        vec![],
    )
}

#[test]
fn test_x86_v2i64_insert_element_const_lane_nonzero_base_lowers_to_sse2() {
    for (lane, pshufd_count) in [(0_u8, 1), (1, 0)] {
        let module = build_x86_v2i64_insert_element_const_index(i128::from(lane));
        let (lir_func, _) = translate_only(&module).expect("adapter must lower v2i64 insert lane");
        assert!(
            lir_func.stack_slots.is_empty(),
            "v2i64 insert lane should avoid adapter stack materialization"
        );

        let entry = &lir_func.blocks[&lir_func.entry_block];
        assert!(entry.instructions.iter().any(
            |i| matches!(i.opcode, Opcode::V2I64InsertLane { lane: actual } if actual == lane)
        ));

        let mfunc = compile_trust_ir_function_x86_64(&module);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovqToXmm), 1);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), pshufd_count);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
        assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
    }
}

#[test]
fn test_aarch64_v2i64_insert_element_const_lane_nonzero_base_lowers_to_neon_ins_without_memory() {
    for lane in 0_u8..=1 {
        let module = build_x86_v2i64_insert_element_const_index(i128::from(lane));
        let (lir_func, _) = translate_only(&module).expect("adapter must lower v2i64 insert lane");
        assert!(
            lir_func.stack_slots.is_empty(),
            "v2i64 insert lane should avoid adapter stack materialization"
        );

        let entry = &lir_func.blocks[&lir_func.entry_block];
        assert!(entry.instructions.iter().any(
            |i| matches!(i.opcode, Opcode::V2I64InsertLane { lane: actual } if actual == lane)
        ));

        let mfunc = compile_trust_ir_function(&module);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonInsGen), 1);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonMovi), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
        assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
    }
}

#[test]
fn test_x86_v2i64_insert_element_const_lane_zero_base_lowers_to_sse2() {
    let module = build_x86_v2i64_zero_insert_element_const_index(1);
    let (lir_func, _) =
        translate_only(&module).expect("adapter must lower zero-base v2i64 insert lane");
    assert!(
        lir_func.stack_slots.is_empty(),
        "zero-base v2i64 insert lane should avoid adapter stack materialization"
    );
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V2I64Zero)),
        "zero-base v2i64 insert lane should materialize a direct zero vector"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V2I64InsertLane { lane: 1 }))
    );

    let mfunc = compile_trust_ir_function_x86_64(&module);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pinsrq), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovqToXmm), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pxor), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Punpcklqdq), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::LeaSib), 0);
}

#[test]
fn test_aarch64_v2i64_insert_element_const_lane_zero_base_lowers_to_neon_movi_ins_without_memory() {
    let module = build_x86_v2i64_zero_insert_element_const_index(1);
    let (lir_func, _) =
        translate_only(&module).expect("adapter must lower zero-base v2i64 insert lane");
    assert!(
        lir_func.stack_slots.is_empty(),
        "zero-base v2i64 insert lane should avoid adapter stack materialization"
    );
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V2I64Zero)),
        "zero-base v2i64 insert lane should materialize a direct zero vector"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::V2I64InsertLane { lane: 1 }))
    );

    let mfunc = compile_trust_ir_function(&module);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonMovi), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonInsGen), 1);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonUmovGen), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonLd1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::NeonSt1Post), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StrRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::LdpRI), 0);
    assert_eq!(count_opcode(&mfunc, AArch64Opcode::StpRI), 0);
}

#[test]
fn test_x86_v2i64_insert_element_out_of_range_lane_fails_closed() {
    let err = try_compile_trust_ir_function_x86_64(&build_x86_v2i64_insert_element_const_index(2))
        .expect_err("out-of-range v2i64 InsertElement lane must fail closed");

    assert!(
        err.contains("vector InsertElement requires i64 constant lane index 0..1")
            && err.contains("got 2"),
        "unexpected v2i64 InsertElement out-of-range diagnostic: {err}"
    );
}

#[test]
fn test_x86_v4i32_vector_constant_mask_select_lowers_to_sse2() {
    let module = build_x86_v4i32_const_mask_select(
        9107,
        "x86_chc_lane_packed_v4i32_vector_const_mask_select",
        ty_v4_bool(),
        bool_mask_vector_const(0b0101, 4),
    );
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRI), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 1);
    assert_eq!(
        x86_opcode_imms(&mfunc, X86Opcode::Pshufd),
        vec![x86_v4i32_mask_shuffle_imm(0b0101)]
    );
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pand), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pandn), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Por), 1);
}

#[test]
fn test_x86_v4i32_array_constant_mask_select_lowers_to_sse2() {
    let module = build_x86_v4i32_const_mask_select(
        9104,
        "x86_chc_lane_packed_v4i32_array_const_mask_select",
        ty_v4_bool(),
        Constant::Array(vec![
            Constant::Bool(true),
            Constant::Bool(false),
            Constant::Bool(true),
            Constant::Bool(false),
        ]),
    );
    let mfunc = compile_trust_ir_function_x86_64(&module);

    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovMR32), 0);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdquRM), 2);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovRI), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::MovdToXmm), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pshufd), 1);
    assert_eq!(
        x86_opcode_imms(&mfunc, X86Opcode::Pshufd),
        vec![x86_v4i32_mask_shuffle_imm(0b0101)]
    );
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pand), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Pandn), 1);
    assert_eq!(count_x86_opcode(&mfunc, X86Opcode::Por), 1);
}

#[test]
fn test_v4i32_vector_constant_in_tuple_field_translates_as_v128_store() {
    let v4i32 = ty_v4i32();
    let tuple_ty = Ty::Tuple(vec![v4i32]);
    let module = single_function_module(
        9108,
        "x86_v4i32_vector_const_tuple_field",
        func_ty(vec![], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: tuple_ty,
                    value: Constant::Aggregate(vec![chc_lane_mask_vector_const()]),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
        vec![],
    );

    let (lir_func, _) = translate_only(&module)
        .expect("adapter must translate vector constants in aggregate fields");
    let entry = &lir_func.blocks[&lir_func.entry_block];
    assert!(
        entry.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Store {
                ty: Type::V128,
                align: None
            }
        )),
        "tuple field must receive a V128 store for the vector constant"
    );
}
