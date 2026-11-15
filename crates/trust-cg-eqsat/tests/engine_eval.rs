// crates/trust-cg-eqsat/tests/engine_eval.rs - section 3 evaluation agrees with trust-ir's reference interpreter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Every graph operator of section 2.2, at boundary values, for i8, u8, i32,
//! u64, i128, u128 and usize (and Bool where admitted): the crate's `eval`
//! (used for `eval` in rule rhs and for side conditions) gives the residue
//! trust-ir's interpreter computes. Evidence boundary: this compares two
//! implementations at sampled points; it is a test, not a proof.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod engine_common;

use engine_common::{boundaries, residue, value};
use trust_cg_eqsat::derivation::{BinOpCode, CastOpCode, CmpPred, OpDesc, ScalarTy, UnOpCode};
use trust_cg_eqsat::eval;
use trust_cg_eqsat::vocab::GraphWidths;
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Interpreter, Module, Ty, ValueId,
};

const TYPES: [ScalarTy; 7] = [
    ScalarTy::I8,
    ScalarTy::U8,
    ScalarTy::I32,
    ScalarTy::U64,
    ScalarTy::I128,
    ScalarTy::U128,
    ScalarTy::Usize,
];

/// A one-function module computing `desc` over its parameters.
fn module_for(desc: OpDesc) -> Module {
    let mut module = Module::new("eval");
    let params: Vec<Ty> = (0..desc.arity())
        .map(|i| desc.operand_ty(i).unwrap().to_ty())
        .collect();
    let ret = desc.result_ty().to_ty();
    let fty = module
        .add_func_type(FuncTy::unrecorded(params.clone(), vec![ret], false))
        .unwrap();
    let mut function = Function::new(FuncId(0), "f", fty, BlockId(0));
    let mut block = Block::new(BlockId(0));
    for (i, ty) in params.iter().enumerate() {
        block = block.with_param(ValueId(i as u32), ty.clone());
    }
    let arg = |i: usize| ValueId(i as u32);
    let inst = match desc {
        OpDesc::Bin(op, ty) => Inst::BinOp {
            op: op.to_ir(),
            ty: ty.to_ty(),
            lhs: arg(0),
            rhs: arg(1),
        },
        OpDesc::Un(op, ty) => Inst::UnOp {
            op: op.to_ir(),
            ty: ty.to_ty(),
            operand: arg(0),
        },
        OpDesc::Cmp(pred, ty) => Inst::ICmp {
            op: pred.to_ir(),
            ty: ty.to_ty(),
            lhs: arg(0),
            rhs: arg(1),
        },
        OpDesc::Cast(op, src, dst) => Inst::Cast {
            op: op.to_ir(),
            src_ty: src.to_ty(),
            dst_ty: dst.to_ty(),
            operand: arg(0),
        },
        OpDesc::Select(ty) => Inst::Select {
            ty: ty.to_ty(),
            cond: arg(0),
            then_val: arg(1),
            else_val: arg(2),
        },
    };
    let result = ValueId(desc.arity() as u32);
    block.body.push(InstrNode::new(inst).with_result(result));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{desc:?}: {errors:?}");
    module
}

/// Compare `eval::op` with the interpreter on every combination of boundary
/// operands; returns the number of comparisons.
fn compare(desc: OpDesc) -> usize {
    let widths = GraphWidths::new(64);
    let module = module_for(desc);
    let interpreter = Interpreter::with_module(&module);
    let operand_values: Vec<Vec<u128>> = (0..desc.arity())
        .map(|i| boundaries(widths.width(desc.operand_ty(i).unwrap()).unwrap()))
        .collect();
    let mut combos: Vec<Vec<u128>> = vec![Vec::new()];
    for values in &operand_values {
        combos = combos
            .into_iter()
            .flat_map(|prefix| {
                values.iter().map(move |v| {
                    let mut next = prefix.clone();
                    next.push(*v);
                    next
                })
            })
            .collect();
    }
    let mut count = 0;
    for combo in combos {
        let args: Vec<_> = combo
            .iter()
            .enumerate()
            .map(|(i, r)| value(&desc.operand_ty(i).unwrap().to_ty(), *r))
            .collect();
        let outcome = interpreter
            .execute_func(FuncId(0), args)
            .unwrap_or_else(|e| panic!("{desc:?} {combo:?}: {e:?}"));
        let expected = residue(&outcome.returns[0]);
        let actual = eval::op(widths, desc, &combo);
        assert_eq!(actual, Some(expected), "{desc:?} on {combo:x?}");
        count += 1;
    }
    count
}

#[test]
fn binary_operators_match_the_interpreter() {
    let mut count = 0;
    for ty in TYPES {
        for op in BinOpCode::ALL {
            let desc = OpDesc::Bin(op, ty);
            if desc.admitted() {
                count += compare(desc);
            }
        }
    }
    for op in [
        BinOpCode::And,
        BinOpCode::Or,
        BinOpCode::Xor,
        BinOpCode::BAnd,
        BinOpCode::BOr,
        BinOpCode::BXor,
    ] {
        count += compare(OpDesc::Bin(op, ScalarTy::Bool));
    }
    assert!(count > 5000, "{count}");
}

#[test]
fn unary_operators_match_the_interpreter() {
    let mut count = 0;
    for ty in TYPES {
        for op in UnOpCode::ALL {
            count += compare(OpDesc::Un(op, ty));
        }
    }
    assert!(count > 500, "{count}");
}

#[test]
fn comparisons_match_the_interpreter() {
    let mut count = 0;
    for ty in TYPES {
        for pred in CmpPred::ALL {
            count += compare(OpDesc::Cmp(pred, ty));
        }
    }
    count += compare(OpDesc::Cmp(CmpPred::Eq, ScalarTy::Bool));
    count += compare(OpDesc::Cmp(CmpPred::Ne, ScalarTy::Bool));
    assert!(count > 10_000, "{count}");
}

#[test]
fn casts_match_the_interpreter() {
    let widths = GraphWidths::new(64);
    let mut count = 0;
    for src in TYPES {
        for dst in TYPES {
            let (ws, wd) = (widths.width(src).unwrap(), widths.width(dst).unwrap());
            // The validator's direction rule: trunc narrows, zext/sext widen
            // (pointer-width pairs are exempt from the check).
            let pointer = src == ScalarTy::Usize || dst == ScalarTy::Usize;
            for op in CastOpCode::ALL {
                let ok = pointer
                    || match op {
                        CastOpCode::Trunc => wd < ws,
                        CastOpCode::ZExt | CastOpCode::SExt => wd > ws,
                    };
                if ok {
                    count += compare(OpDesc::Cast(op, src, dst));
                }
            }
        }
    }
    assert!(count > 1000, "{count}");
}

#[test]
fn selects_match_the_interpreter() {
    let mut count = 0;
    for ty in TYPES {
        count += compare(OpDesc::Select(ty));
    }
    count += compare(OpDesc::Select(ScalarTy::Bool));
    assert!(count > 1000, "{count}");
}
