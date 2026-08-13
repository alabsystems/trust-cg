// trust-cg-codegen/tests/e2e_x86_64_i128_stack_abi.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! SysV AMD64 stack-passed `i128` ABI coverage.
//!
//! Two layouts matter:
//! * after five integer arguments, an `i128` cannot fit in the lone remaining
//!   GPR, so the whole pair rolls back to the stack and a following scalar must
//!   still use `R9`;
//! * after seven integer arguments, the first stack scalar occupies offset 0
//!   and the `i128` must skip offset 8 to start at a 16-byte boundary.
//!
//! The structural test pins both layouts after Trust IR adaptation. The
//! differential test crosses the real C ABI in both directions: C calls
//! trust-cg formals, and trust-cg callers invoke C callees. It runs natively on
//! x86-64 macOS and under the repository's opt-in Rosetta harness on Apple
//! silicon.

mod common;

use common::rosetta::has_cc_x86_64_link_run;
use common::x86_64_corpus::x86_64_differential_test;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{R9, RBP, RSP, X86PReg};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelOperand, X86InstructionSelector};
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

fn add_external(module: &mut TrustIrModule, id: u32, name: &str, params: Vec<Ty>) -> FuncId {
    let ty = module.add_func_type(FuncTy {
        params,
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut function = TrustIrFunction::new(FuncId::new(id), name, ty, BlockId::new(0));
    function.blocks.clear();
    function.linkage = Linkage::External;
    let id = function.id;
    module.add_function(function);
    id
}

/// Add a function that returns `wide ^ zext(mix)`.
fn add_formal_probe(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    params: Vec<Ty>,
    wide_index: u32,
    mix_index: u32,
) {
    let ty = module.add_func_type(FuncTy {
        params: params.clone(),
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut function = TrustIrFunction::new(FuncId::new(id), name, ty, BlockId::new(0));
    function.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (v(index as u32), ty))
            .collect(),
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I64,
                dst_ty: Ty::I128,
                operand: v(mix_index),
            })
            .with_result(v(100)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Xor,
                ty: Ty::I128,
                lhs: v(wide_index),
                rhs: v(100),
            })
            .with_result(v(101)),
            InstrNode::new(Inst::Return {
                values: vec![v(101)],
            }),
        ],
    }];
    module.add_function(function);
}

fn add_i64_const(body: &mut Vec<InstrNode>, id: u32, value: i128) -> ValueId {
    let result = v(id);
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value),
        })
        .with_result(result),
    );
    result
}

fn add_rollback_caller(module: &mut TrustIrModule, id: u32, callee: FuncId) {
    let ty = module.add_func_type(FuncTy {
        params: vec![Ty::I128, Ty::I64],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut body = Vec::new();
    let mut args = Vec::new();
    for (index, value) in [11, 22, 33, 44, 55].into_iter().enumerate() {
        args.push(add_i64_const(&mut body, 10 + index as u32, value));
    }
    args.extend([v(0), v(1)]);
    body.push(InstrNode::new(Inst::Call { callee, args }).with_result(v(30)));
    body.push(InstrNode::new(Inst::Return {
        values: vec![v(30)],
    }));

    let mut function =
        TrustIrFunction::new(FuncId::new(id), "_call_i128_rollback", ty, BlockId::new(0));
    function.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::I128), (v(1), Ty::I64)],
        body,
    }];
    module.add_function(function);
}

fn add_aligned_caller(module: &mut TrustIrModule, id: u32, callee: FuncId) {
    let ty = module.add_func_type(FuncTy {
        params: vec![Ty::I128],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut body = Vec::new();
    let mut args = Vec::new();
    for (index, value) in [11, 22, 33, 44, 55, 66, 77].into_iter().enumerate() {
        args.push(add_i64_const(&mut body, 10 + index as u32, value));
    }
    args.push(v(0));
    body.push(InstrNode::new(Inst::Call { callee, args }).with_result(v(30)));
    body.push(InstrNode::new(Inst::Return {
        values: vec![v(30)],
    }));

    let mut function =
        TrustIrFunction::new(FuncId::new(id), "_call_i128_aligned", ty, BlockId::new(0));
    function.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::I128)],
        body,
    }];
    module.add_function(function);
}

fn build_module() -> TrustIrModule {
    let rollback_params = {
        let mut params = vec![Ty::I64; 5];
        params.extend([Ty::I128, Ty::I64]);
        params
    };
    let aligned_params = {
        let mut params = vec![Ty::I64; 7];
        params.push(Ty::I128);
        params
    };

    let mut module = TrustIrModule::new("sysv_stack_i128_abi");
    let native_rollback = add_external(
        &mut module,
        0,
        "_native_i128_rollback",
        rollback_params.clone(),
    );
    let native_aligned = add_external(
        &mut module,
        1,
        "_native_i128_aligned",
        aligned_params.clone(),
    );
    add_formal_probe(
        &mut module,
        2,
        "_formal_i128_rollback",
        rollback_params,
        5,
        6,
    );
    add_formal_probe(&mut module, 3, "_formal_i128_aligned", aligned_params, 7, 6);
    add_rollback_caller(&mut module, 4, native_rollback);
    add_aligned_caller(&mut module, 5, native_aligned);
    module
}

fn select_function(module: &TrustIrModule, name: &str) -> X86ISelFunction {
    let function = module
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function {name}"));
    let (lir, _) =
        trust_cg_lower::translate_function(function, module).expect("adapter must lower ABI probe");
    let mut isel = X86InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    isel.seed_value_types(&lir.value_types);
    isel.seed_function_value_use_counts(&lir);
    isel.lower_formal_arguments(&lir.signature, lir.entry_block)
        .expect("formal arguments must lower");

    let mut blocks: Vec<Block> = lir.blocks.keys().copied().collect();
    blocks.sort_by_key(|block| {
        if *block == lir.entry_block {
            0
        } else {
            block.0 + 1
        }
    });
    for block in blocks {
        let lir_block = &lir.blocks[&block];
        isel.select_block(block, &lir_block.instructions)
            .expect("ABI probe must select");
    }
    isel.finalize()
}

fn memory_displacements(function: &X86ISelFunction, opcode: X86Opcode, base: X86PReg) -> Vec<i32> {
    function
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .filter(|inst| inst.opcode == opcode)
        .flat_map(|inst| &inst.operands)
        .filter_map(|operand| match operand {
            X86ISelOperand::MemAddr {
                base: address_base,
                disp,
            } if **address_base == X86ISelOperand::PReg(base) => Some(*disp),
            _ => None,
        })
        .collect()
}

fn has_move_from(function: &X86ISelFunction, register: X86PReg) -> bool {
    function
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .any(|inst| {
            inst.opcode == X86Opcode::MovRR
                && matches!(
                    inst.operands.get(1),
                    Some(X86ISelOperand::PReg(source)) if *source == register
                )
        })
}

fn has_move_to(function: &X86ISelFunction, register: X86PReg) -> bool {
    function
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .any(|inst| {
            inst.opcode == X86Opcode::MovRR
                && matches!(
                    inst.operands.first(),
                    Some(X86ISelOperand::PReg(destination)) if *destination == register
                )
        })
}

#[test]
fn sysv_stack_i128_layout_survives_trust_ir_adaptation() {
    let module = build_module();

    let formal_rollback = select_function(&module, "_formal_i128_rollback");
    assert_eq!(
        memory_displacements(&formal_rollback, X86Opcode::MovRM, RBP),
        vec![16, 24]
    );
    assert!(
        has_move_from(&formal_rollback, R9),
        "tail scalar must retain the final argument GPR"
    );

    let formal_aligned = select_function(&module, "_formal_i128_aligned");
    assert_eq!(
        memory_displacements(&formal_aligned, X86Opcode::MovRM, RBP),
        vec![16, 32, 40],
        "stack scalar at +16 must be followed by padding and i128 at +32"
    );

    let call_rollback = select_function(&module, "_call_i128_rollback");
    assert_eq!(
        memory_displacements(&call_rollback, X86Opcode::MovMR, RSP),
        vec![0, 8]
    );
    assert!(
        has_move_to(&call_rollback, R9),
        "tail scalar must use R9 after the i128 rolls back"
    );

    let call_aligned = select_function(&module, "_call_i128_aligned");
    assert_eq!(
        memory_displacements(&call_aligned, X86Opcode::MovMR, RSP),
        vec![0, 16, 24],
        "outgoing scalar at +0 must be followed by padding and i128 at +16"
    );
}

const C_REFERENCE: &str = r#"
#include <stdint.h>
typedef unsigned __int128 u128;

extern u128 _native_i128_rollback(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, u128, uint64_t);
extern u128 _native_i128_aligned(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, u128);

u128 _formal_i128_rollback(
    uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4,
    u128 wide, uint64_t tail) {
    (void)a0; (void)a1; (void)a2; (void)a3; (void)a4;
    return wide ^ (u128)tail;
}

u128 _formal_i128_aligned(
    uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4,
    uint64_t a5, uint64_t a6, u128 wide) {
    (void)a0; (void)a1; (void)a2; (void)a3; (void)a4; (void)a5;
    return wide ^ (u128)a6;
}

u128 _call_i128_rollback(u128 wide, uint64_t tail) {
    return _native_i128_rollback(11, 22, 33, 44, 55, wide, tail);
}

u128 _call_i128_aligned(u128 wide) {
    return _native_i128_aligned(11, 22, 33, 44, 55, 66, 77, wide);
}
"#;

const C_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
typedef unsigned __int128 u128;

extern u128 _formal_i128_rollback(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, u128, uint64_t);
extern u128 _formal_i128_aligned(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, u128);
extern u128 _call_i128_rollback(u128, uint64_t);
extern u128 _call_i128_aligned(u128);

static u128 bad(void) {
    return ((u128)UINT64_MAX << 64) | UINT64_C(0xbad0bad0bad0bad0);
}

u128 _native_i128_rollback(
    uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4,
    u128 wide, uint64_t tail) {
    if (a0 != 11 || a1 != 22 || a2 != 33 || a3 != 44 || a4 != 55) return bad();
    return wide ^ (u128)tail;
}

u128 _native_i128_aligned(
    uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4,
    uint64_t a5, uint64_t a6, u128 wide) {
    if (a0 != 11 || a1 != 22 || a2 != 33 || a3 != 44 ||
        a4 != 55 || a5 != 66 || a6 != 77) return bad();
    return wide ^ (u128)a6;
}

static int check(const char *name, u128 got, u128 expected, int code) {
    printf("%s=%016llx:%016llx\n", name,
           (unsigned long long)(got >> 64), (unsigned long long)got);
    if (got == expected) return 0;
    fprintf(stderr, "%s mismatch: expected %016llx:%016llx\n", name,
            (unsigned long long)(expected >> 64), (unsigned long long)expected);
    return code;
}

int main(void) {
    const u128 x0 = ((u128)UINT64_C(0x1122334455667788) << 64) |
                    UINT64_C(0x99aabbccddeeff00);
    const u128 x1 = ((u128)UINT64_C(0xfedcba9876543210) << 64) |
                    UINT64_C(0x0123456789abcdef);
    const uint64_t tail = UINT64_C(0x8877665544332211);
    int code;

    code = check("formal_rollback",
        _formal_i128_rollback(11, 22, 33, 44, 55, x0, tail), x0 ^ (u128)tail, 1);
    if (code) return code;
    code = check("formal_aligned",
        _formal_i128_aligned(11, 22, 33, 44, 55, 66, 77, x1), x1 ^ (u128)77, 2);
    if (code) return code;
    code = check("call_rollback",
        _call_i128_rollback(x1, tail), x1 ^ (u128)tail, 3);
    if (code) return code;
    code = check("call_aligned", _call_i128_aligned(x0), x0 ^ (u128)77, 4);
    return code;
}
"#;

#[test]
fn sysv_stack_i128_crosses_c_abi_in_both_directions() {
    if !has_cc_x86_64_link_run() {
        eprintln!("SKIP: x86-64 native/Rosetta C link-run is unavailable");
        return;
    }
    let module = build_module();
    x86_64_differential_test("sysv_stack_i128_abi", &module, C_REFERENCE, C_DRIVER)
        .unwrap_or_else(|error| panic!("SysV stack i128 differential failed: {error}"));
}
