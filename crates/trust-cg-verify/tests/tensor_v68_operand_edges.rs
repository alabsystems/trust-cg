// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Loop liveness agrees with the source owner's SSA edge contract.
use trust_cg_verify::ssa_loop_complete::non_terminator_value_uses;
use trust_ir::inst::{TensorMapNode, TensorReduceOp, TensorReduceOrder};
use trust_ir::{Inst, Ty, ValueId};
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
#[test]
fn tensor_lanes_and_indices_are_not_ssa_edges_but_repeated_real_edges_survive() {
    let ty = Ty::Tensor(Box::new(Ty::I32), 0);
    let cases = [
        Inst::TensorMap {
            ty: ty.clone(),
            args: vec![v(4), v(2), v(4)],
            body: vec![TensorMapNode::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::I32,
                lhs: 77,
                rhs: 88,
            }],
        },
        Inst::TensorReduce {
            ty: ty.clone(),
            src: v(4),
            op: TensorReduceOp::Add,
            axes: vec![55],
            order: TensorReduceOrder::RowMajor,
        },
        Inst::TensorGather {
            ty: ty.clone(),
            data: v(4),
            coords: vec![v(2), v(4), v(2)],
        },
        Inst::TensorScatter {
            ty: ty.clone(),
            init: v(4),
            src: v(2),
            coords: vec![v(4), v(4)],
        },
        Inst::TensorView {
            ty,
            src: v(4),
            params: vec![v(2), v(4)],
            exprs: vec![],
            shape: vec![77],
            index: vec![88],
            fill: Some(v(2)),
        },
    ];
    for inst in cases {
        let mut canonical = Vec::new();
        inst.visit_value_operands(|id| canonical.push(id));
        let actual = non_terminator_value_uses(&inst);
        assert_eq!(actual, canonical, "{inst:?}");
        assert!(!actual.contains(&v(77)) && !actual.contains(&v(88)));
    }
}
