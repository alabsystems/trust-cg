// fuzz/fuzz_targets/fuzz_translate_function.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// libFuzzer target shadowing `panic_fuzz_lower.rs`. Derives a minimal
// well-formed trust-ir function from the fuzzer's byte stream (any shape
// survives because the trust-ir types do not implement `Arbitrary` directly;
// we use byte bits to pick instruction variants). Feeds the result to
// `trust_cg_lower::translate_function`. The contract is identical to the
// proptest harness: translate must return `Ok((Function, ProofContext))`
// or `Err(AdapterError)` — never panic.

#![no_main]

use libfuzzer_sys::fuzz_target;

use trust_cg_lower::trust_ir_compat::{
    BinOp, Block as TmirBlock, BlockId, Constant, FuncId, FuncTy, Function as TmirFunction, ICmpOp,
    Inst, InstrNode, Module as TmirModule, Ty, ValueId,
};

fn pick_binop(byte: u8) -> BinOp {
    match byte % 9 {
        0 => BinOp::Add,
        1 => BinOp::Sub,
        2 => BinOp::Mul,
        3 => BinOp::And,
        4 => BinOp::Or,
        5 => BinOp::Xor,
        6 => BinOp::Shl,
        7 => BinOp::LShr,
        _ => BinOp::AShr,
    }
}

fn pick_icmp(byte: u8) -> ICmpOp {
    match byte % 6 {
        0 => ICmpOp::Eq,
        1 => ICmpOp::Ne,
        2 => ICmpOp::Slt,
        3 => ICmpOp::Sle,
        4 => ICmpOp::Ult,
        _ => ICmpOp::Ule,
    }
}

fn v2i64_ty() -> Ty {
    Ty::Vector(Box::new(Ty::I64), 2)
}

fn v4i32_ty() -> Ty {
    Ty::Vector(Box::new(Ty::I32), 4)
}

fn vector_const(values: impl IntoIterator<Item = i128>) -> Constant {
    Constant::Vector(values.into_iter().map(Constant::Int).collect())
}

fn byte_at(data: &[u8], index: usize) -> u8 {
    data.get(index).copied().unwrap_or(0)
}

fn signed_lane(byte: u8) -> i128 {
    i128::from(byte as i8)
}

fn build_vector_function(data: &[u8], ty: Ty, ops: &[BinOp]) -> (TmirFunction, TmirModule) {
    let mut module = TmirModule::new("_fuzz_lower_vector");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![ty.clone()],
        is_vararg: false,
    });

    let mut func = TmirFunction::new(FuncId::new(0), "_fuzz_vector_fn", ft_id, BlockId::new(0));
    let mut next_vid: u32 = 1000;
    let mut alloc_vid = || {
        let v = ValueId::new(next_vid);
        next_vid += 1;
        v
    };

    let lanes = match &ty {
        Ty::Vector(_, lanes) => *lanes as usize,
        _ => 0,
    };
    let mut body: Vec<InstrNode> = Vec::new();

    let lhs = alloc_vid();
    let lhs_lanes = (0..lanes).map(|lane| signed_lane(byte_at(data, lane + 1)));
    body.push(
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: vector_const(lhs_lanes),
        })
        .with_result(lhs),
    );

    let rhs = alloc_vid();
    let rhs_lanes = (0..lanes).map(|lane| {
        let raw = byte_at(data, lanes + lane + 1);
        if matches!(ops, [BinOp::Shl | BinOp::LShr | BinOp::AShr, ..]) {
            i128::from(raw % 32)
        } else {
            signed_lane(raw)
        }
    });
    body.push(
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: vector_const(rhs_lanes),
        })
        .with_result(rhs),
    );

    let result = alloc_vid();
    let op = ops[(byte_at(data, 0) as usize) % ops.len()];
    body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty: ty.clone(),
            lhs,
            rhs,
        })
        .with_result(result),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));

    func.blocks.push(TmirBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    });

    (func, module)
}

fuzz_target!(|data: &[u8]| {
    match data.first().copied().unwrap_or(0) % 4 {
        1 => {
            let (func, module) = build_vector_function(data, v2i64_ty(), &[BinOp::Add, BinOp::Sub]);
            let _ = trust_cg_lower::translate_function(&func, &module);
            return;
        }
        2 => {
            let (func, module) =
                build_vector_function(data, v4i32_ty(), &[BinOp::Shl, BinOp::LShr, BinOp::AShr]);
            let _ = trust_cg_lower::translate_function(&func, &module);
            return;
        }
        _ => {}
    }

    // Build a trust-ir function whose shape is driven by `data`. We deliberately
    // stay on the well-formed side: a single block, 0..=2 params, a handful
    // of insts drawn from `data`. The "malformed" axis is already covered
    // by the proptest harness; here we want corpus-driven coverage of the
    // lowering passes, so `Err(..)` from the adapter short-circuits the
    // interesting signal anyway.
    let mut module = TmirModule::new("_fuzz_lower");
    let num_params = (data.first().copied().unwrap_or(0) % 3) as usize;
    let params = vec![Ty::I64; num_params];
    let ft_id = module.add_func_type(FuncTy {
        params: params.clone(),
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut func = TmirFunction::new(FuncId::new(0), "_fuzz_fn", ft_id, BlockId::new(0));
    let mut next_vid: u32 = 1000;
    let mut alloc_vid = || {
        let v = ValueId::new(next_vid);
        next_vid += 1;
        v
    };

    // Entry block params.
    let mut defined: Vec<ValueId> = Vec::new();
    let mut body: Vec<InstrNode> = Vec::new();
    let mut block_params: Vec<(ValueId, Ty)> = Vec::new();
    for _ in 0..num_params {
        let v = alloc_vid();
        block_params.push((v, Ty::I64));
        defined.push(v);
    }

    // Seed a constant so every ValueId is eventually defined.
    let zero = alloc_vid();
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        })
        .with_result(zero),
    );
    defined.push(zero);

    let nsteps = data.len().min(6);
    for i in 0..nsteps {
        let b = data[i];
        let kind = b % 4;
        match kind {
            0 => {
                // Constant
                let val = i as i64 - (b as i64);
                let v = alloc_vid();
                body.push(
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(val as i128),
                    })
                    .with_result(v),
                );
                defined.push(v);
            }
            1 => {
                let lhs = *defined.last().unwrap();
                let rhs = defined[defined.len().saturating_sub(2).max(0)];
                let v = alloc_vid();
                body.push(
                    InstrNode::new(Inst::BinOp {
                        op: pick_binop(b),
                        ty: Ty::I64,
                        lhs,
                        rhs,
                    })
                    .with_result(v),
                );
                defined.push(v);
            }
            2 => {
                let lhs = *defined.last().unwrap();
                let rhs = defined[defined.len().saturating_sub(2).max(0)];
                let v = alloc_vid();
                body.push(
                    InstrNode::new(Inst::ICmp {
                        op: pick_icmp(b),
                        ty: Ty::I64,
                        lhs,
                        rhs,
                    })
                    .with_result(v),
                );
            }
            _ => {}
        }
    }

    let ret = *defined.last().unwrap_or(&zero);
    body.push(InstrNode::new(Inst::Return { values: vec![ret] }));
    func.blocks.push(TmirBlock {
        id: BlockId::new(0),
        params: block_params,
        body,
    });

    let _ = trust_cg_lower::translate_function(&func, &module);
});
