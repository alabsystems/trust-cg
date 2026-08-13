// Regression for TY-style materialized helper returns surviving a later call.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, ExecutableBuffer, Target};
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode,
    Module, Ty, ValueId,
};

#[path = "common/ty_contract.rs"]
mod ty_contract;

use ty_contract::{abi_i64, bind_ty_reducer_entry, extern_c_signature};

const ENTRY_NAME: &str = "o3_ty_materialized_return";

type EntryFn = extern "C" fn() -> i64;

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn push_result(block: &mut Block, next: &mut u32, inst: Inst) -> ValueId {
    let result = v(*next);
    *next += 1;
    block.body.push(InstrNode::new(inst).with_result(result));
    result
}

fn push_void(block: &mut Block, inst: Inst) {
    block.body.push(InstrNode::new(inst));
}

fn iconst(block: &mut Block, next: &mut u32, ty: Ty, value: i128) -> ValueId {
    push_result(
        block,
        next,
        Inst::Const {
            ty,
            value: Constant::Int(value),
        },
    )
}

fn alloca_ty(block: &mut Block, next: &mut u32, ty: Ty, count: ValueId) -> ValueId {
    push_result(
        block,
        next,
        Inst::Alloca {
            ty,
            count: Some(count),
            align: None,
        },
    )
}

fn alloca_i64(block: &mut Block, next: &mut u32, count: ValueId) -> ValueId {
    alloca_ty(block, next, Ty::I64, count)
}

fn alloca_u8(block: &mut Block, next: &mut u32, count: ValueId) -> ValueId {
    alloca_ty(block, next, Ty::U8, count)
}

fn alloca_ptr(block: &mut Block, next: &mut u32, count: ValueId) -> ValueId {
    alloca_ty(block, next, Ty::Ptr, count)
}

fn gep_i64(block: &mut Block, next: &mut u32, base: ValueId, slot: i64) -> ValueId {
    let index = iconst(block, next, Ty::U64, i128::from(slot));
    push_result(
        block,
        next,
        Inst::GEP {
            pointee_ty: Ty::I64,
            base,
            indices: vec![index],
            inbounds: false,
        },
    )
}

fn gep_ptr(block: &mut Block, next: &mut u32, base: ValueId, slot: i64) -> ValueId {
    let index = iconst(block, next, Ty::U64, i128::from(slot));
    push_result(
        block,
        next,
        Inst::GEP {
            pointee_ty: Ty::Ptr,
            base,
            indices: vec![index],
            inbounds: false,
        },
    )
}

fn store_ty(block: &mut Block, ty: Ty, ptr: ValueId, value: ValueId, volatile: bool) {
    push_void(
        block,
        Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align: None,
        },
    );
}

fn store_i64(block: &mut Block, ptr: ValueId, value: ValueId) {
    store_ty(block, Ty::I64, ptr, value, false);
}

fn store_u8_volatile(block: &mut Block, ptr: ValueId, value: ValueId) {
    store_ty(block, Ty::U8, ptr, value, false);
}

fn store_ptr(block: &mut Block, ptr: ValueId, value: ValueId) {
    store_ty(block, Ty::Ptr, ptr, value, false);
}

fn load_ty(block: &mut Block, next: &mut u32, ty: Ty, ptr: ValueId, volatile: bool) -> ValueId {
    push_result(
        block,
        next,
        Inst::Load {
            ty,
            ptr,
            volatile,
            align: None,
        },
    )
}

fn load_i64(block: &mut Block, next: &mut u32, ptr: ValueId) -> ValueId {
    load_ty(block, next, Ty::I64, ptr, false)
}

fn load_u8_volatile(block: &mut Block, next: &mut u32, ptr: ValueId) -> ValueId {
    load_ty(block, next, Ty::U8, ptr, false)
}

fn load_ptr(block: &mut Block, next: &mut u32, ptr: ValueId) -> ValueId {
    load_ty(block, next, Ty::Ptr, ptr, false)
}

fn binop_i64(block: &mut Block, next: &mut u32, op: BinOp, lhs: ValueId, rhs: ValueId) -> ValueId {
    push_result(
        block,
        next,
        Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs,
            rhs,
        },
    )
}

fn call_i64(block: &mut Block, next: &mut u32, callee: FuncId, args: Vec<ValueId>) -> ValueId {
    push_result(block, next, Inst::Call { callee, args })
}

fn cast_ptr_to_i64(block: &mut Block, next: &mut u32, ptr: ValueId) -> ValueId {
    push_result(
        block,
        next,
        Inst::Cast {
            op: CastOp::PtrToInt,
            src_ty: Ty::Ptr,
            dst_ty: Ty::I64,
            operand: ptr,
        },
    )
}

fn cast_i64_to_ptr(block: &mut Block, next: &mut u32, raw: ValueId) -> ValueId {
    push_result(
        block,
        next,
        Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty: Ty::I64,
            dst_ty: Ty::Ptr,
            operand: raw,
        },
    )
}

fn zext_u8_to_i64(block: &mut Block, next: &mut u32, value: ValueId) -> ValueId {
    push_result(
        block,
        next,
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::I64,
            operand: value,
        },
    )
}

fn load_retbuf_slot(block: &mut Block, next: &mut u32, base: ValueId, slot: i64) -> ValueId {
    let ptr = gep_i64(block, next, base, slot);
    load_i64(block, next, ptr)
}

fn add_weighted(
    block: &mut Block,
    next: &mut u32,
    acc: ValueId,
    flag: ValueId,
    weight: i64,
) -> ValueId {
    if weight == 1 {
        binop_i64(block, next, BinOp::Add, acc, flag)
    } else {
        let weight = iconst(block, next, Ty::I64, i128::from(weight));
        let term = binop_i64(block, next, BinOp::Mul, flag, weight);
        binop_i64(block, next, BinOp::Add, acc, term)
    }
}

fn one_minus(block: &mut Block, next: &mut u32, value: ValueId) -> ValueId {
    let one = iconst(block, next, Ty::I64, 1);
    binop_i64(block, next, BinOp::Sub, one, value)
}

fn build_retbuf_helper(id: FuncId, name: &str, ty: FuncTyId, slots: &[i64]) -> Function {
    let entry = BlockId::new(0);
    let retbuf = v(0);
    let mut block = Block::new(entry).with_param(retbuf, Ty::Ptr);
    let mut next = 1;

    for (slot, value) in slots.iter().enumerate() {
        let value = iconst(&mut block, &mut next, Ty::I64, i128::from(*value));
        let ptr = gep_i64(&mut block, &mut next, retbuf, slot as i64);
        store_i64(&mut block, ptr, value);
    }

    let raw_retbuf = cast_ptr_to_i64(&mut block, &mut next, retbuf);
    push_void(
        &mut block,
        Inst::Return {
            values: vec![raw_retbuf],
        },
    );

    let mut func = Function::new(id, name, ty, entry);
    func.blocks.push(block);
    func
}

fn build_clobber(id: FuncId, ty: FuncTyId) -> Function {
    let entry = BlockId::new(0);
    let mut block = Block::new(entry);
    for param in 0..8 {
        block = block.with_param(v(param), Ty::I64);
    }

    let mut next = 8;
    let mut acc = v(0);
    for param in 1..8 {
        acc = binop_i64(&mut block, &mut next, BinOp::Add, acc, v(param));
    }
    push_void(&mut block, Inst::Return { values: vec![acc] });

    let mut func = Function::new(id, "retbuf_later_clobber", ty, entry);
    func.blocks.push(block);
    func
}

fn build_entry(ty: FuncTyId) -> Function {
    let entry = BlockId::new(0);
    let mut block = Block::new(entry);
    let mut next = 0;

    let exact_count = iconst(&mut block, &mut next, Ty::U64, 4);
    let exact_retbuf = alloca_i64(&mut block, &mut next, exact_count);
    let diff_count = iconst(&mut block, &mut next, Ty::U64, 5);
    let diff_retbuf = alloca_i64(&mut block, &mut next, diff_count);
    let later_count = iconst(&mut block, &mut next, Ty::U64, 3);
    let later_retbuf = alloca_i64(&mut block, &mut next, later_count);
    let status_count = iconst(&mut block, &mut next, Ty::U64, 1);
    let status_ptr = alloca_u8(&mut block, &mut next, status_count);
    let ptr_spill_count = iconst(&mut block, &mut next, Ty::U64, 2);
    let ptr_spill = alloca_ptr(&mut block, &mut next, ptr_spill_count);

    let status_busy = iconst(&mut block, &mut next, Ty::U8, 1);
    store_u8_volatile(&mut block, status_ptr, status_busy);
    let status_clear = iconst(&mut block, &mut next, Ty::U8, 0);
    store_u8_volatile(&mut block, status_ptr, status_clear);

    let exact_raw = call_i64(&mut block, &mut next, FuncId::new(1), vec![exact_retbuf]);
    let diff_raw = call_i64(&mut block, &mut next, FuncId::new(2), vec![diff_retbuf]);

    let clobber_args = (0..8)
        .map(|i| iconst(&mut block, &mut next, Ty::I64, 100 + i))
        .collect();
    let _clobber = call_i64(&mut block, &mut next, FuncId::new(3), clobber_args);
    let _unused_later_raw = call_i64(&mut block, &mut next, FuncId::new(4), vec![later_retbuf]);

    let status_after_calls = load_u8_volatile(&mut block, &mut next, status_ptr);
    let status_after_calls = zext_u8_to_i64(&mut block, &mut next, status_after_calls);
    let status_is_clear = one_minus(&mut block, &mut next, status_after_calls);

    let exact_ptr = cast_i64_to_ptr(&mut block, &mut next, exact_raw);
    let diff_ptr = cast_i64_to_ptr(&mut block, &mut next, diff_raw);
    let exact_ptr_slot = gep_ptr(&mut block, &mut next, ptr_spill, 0);
    store_ptr(&mut block, exact_ptr_slot, exact_ptr);
    let diff_ptr_slot = gep_ptr(&mut block, &mut next, ptr_spill, 1);
    store_ptr(&mut block, diff_ptr_slot, diff_ptr);
    let exact_ptr = load_ptr(&mut block, &mut next, exact_ptr_slot);
    let diff_ptr = load_ptr(&mut block, &mut next, diff_ptr_slot);

    let exact_has_2 = load_retbuf_slot(&mut block, &mut next, exact_ptr, 0);
    let exact_has_4 = load_retbuf_slot(&mut block, &mut next, exact_ptr, 1);
    let exact_has_3 = load_retbuf_slot(&mut block, &mut next, exact_ptr, 2);
    let exact_has_10 = load_retbuf_slot(&mut block, &mut next, exact_ptr, 3);

    let diff_has_1 = load_retbuf_slot(&mut block, &mut next, diff_ptr, 0);
    let diff_has_3 = load_retbuf_slot(&mut block, &mut next, diff_ptr, 1);
    let diff_has_4 = load_retbuf_slot(&mut block, &mut next, diff_ptr, 2);
    let diff_has_2 = load_retbuf_slot(&mut block, &mut next, diff_ptr, 3);
    let diff_has_10 = load_retbuf_slot(&mut block, &mut next, diff_ptr, 4);

    let exact_lacks_3 = one_minus(&mut block, &mut next, exact_has_3);
    let exact_lacks_10 = one_minus(&mut block, &mut next, exact_has_10);
    let diff_lacks_2 = one_minus(&mut block, &mut next, diff_has_2);
    let diff_lacks_10 = one_minus(&mut block, &mut next, diff_has_10);
    let exact_has_2_after_status_clear = binop_i64(
        &mut block,
        &mut next,
        BinOp::Mul,
        exact_has_2,
        status_is_clear,
    );

    let mut acc = iconst(&mut block, &mut next, Ty::I64, 0);
    for (flag, weight) in [
        (exact_has_2_after_status_clear, 1),
        (exact_has_4, 2),
        (exact_lacks_3, 4),
        (exact_lacks_10, 8),
        (diff_has_1, 16),
        (diff_has_3, 32),
        (diff_has_4, 64),
        (diff_lacks_2, 128),
        (diff_lacks_10, 256),
    ] {
        acc = add_weighted(&mut block, &mut next, acc, flag, weight);
    }
    push_void(&mut block, Inst::Return { values: vec![acc] });

    let mut func = Function::new(FuncId::new(0), ENTRY_NAME, ty, entry);
    func.blocks.push(block);
    func
}

fn build_module() -> Module {
    let mut module = Module::new("o3_ty_materialized_return");
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let retbuf_helper_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let clobber_ty = module.add_func_type(FuncTy {
        params: vec![
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
        ],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    module.add_function(build_entry(entry_ty));
    module.add_function(build_retbuf_helper(
        FuncId::new(1),
        "exact_set_return_retbuf",
        retbuf_helper_ty,
        &[1, 1, 0, 0],
    ));
    module.add_function(build_retbuf_helper(
        FuncId::new(2),
        "materialized_set_diff_return_retbuf",
        retbuf_helper_ty,
        &[1, 1, 1, 0, 0],
    ));
    module.add_function(build_clobber(FuncId::new(3), clobber_ty));
    module.add_function(build_retbuf_helper(
        FuncId::new(4),
        "unused_later_materialized_return_retbuf",
        retbuf_helper_ty,
        &[7, 8, 9],
    ));
    module
}

fn compile_to_jit(module: &Module, opt_level: OptLevel) -> ExecutableBuffer {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|err| panic!("{opt_level:?} compile failed: {err}"))
        .buffer
}

fn entry_signature() -> trust_cg_codegen::jit_contract::SymbolSignature {
    extern_c_signature(vec![], vec![abi_i64()])
}

fn run_at(opt_level: OptLevel) -> i64 {
    let module = build_module();
    let buffer = compile_to_jit(&module, opt_level);
    let entry: EntryFn = bind_ty_reducer_entry(&buffer, opt_level, ENTRY_NAME, entry_signature());
    entry()
}

#[test]
fn ty_materialized_retbuf_returns_survive_later_clobber_o1_o3() {
    for opt_level in [OptLevel::O1, OptLevel::O3] {
        assert_eq!(
            run_at(opt_level),
            511,
            "{opt_level:?} should preserve both materialized retbuf helper returns across the later call"
        );
    }
}
