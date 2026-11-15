//! Unconditional threading across read-dependent nested branches. Mutations
//! exercise the path union, every edge's arguments, and opaque-value rejection.
use trust_cg_lower::Type;
use trust_cg_verify::ay_bridge::AYConfig;
use trust_cg_verify::loop_backedge_symexec::model_back_edge_args_all_paths;
use trust_cg_verify::mir_semantics::{
    BridgeEdgeArgs, EdgeKind, MirBlock, MirOperand, MirScalarTy, MirTerminator, RefinementOutcome,
    check_back_edge_threading,
};
use trust_cg_verify::smt::SmtExpr;
use trust_ir::{Block, BlockId, FuncId, FuncTyId, Function, Inst, InstrNode, Ty, ValueId};
fn b(i: u32) -> BlockId {
    BlockId::new(i)
}
fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
fn branch(t: u32, e: u32) -> InstrNode {
    InstrNode::new(Inst::CondBr {
        cond: v(10),
        then_target: b(t),
        then_args: vec![],
        else_target: b(e),
        else_args: vec![],
    })
}
fn fixture(mutation: u8) -> Function {
    let mut f = Function::new(FuncId::new(0), "read_funnel", FuncTyId::new(0), b(0));
    let mut header = Block::new(b(0))
        .with_param(v(0), Ty::I8)
        .with_param(v(1), Ty::I8);
    // A branch predicate intentionally has no source/implementation correlation.
    header
        .body
        .push(InstrNode::new(Inst::Undef { ty: Ty::Bool }).with_result(v(10)));
    header.body.push(branch(1, 2));
    let mut nested = Block::new(b(1));
    nested.body.push(branch(2, 3));
    let mut left = Block::new(b(2));
    let first = if mutation == 1 || mutation == 2 {
        v(0)
    } else {
        v(1)
    };
    left.body.push(InstrNode::new(Inst::Br {
        target: if mutation == 4 { b(1) } else { b(4) },
        args: if mutation == 4 {
            vec![]
        } else {
            vec![first, v(0)]
        },
    }));
    let mut right = Block::new(b(3));
    right.body.push(InstrNode::new(Inst::Br {
        target: b(4),
        args: vec![if mutation == 2 { v(0) } else { v(1) }, v(0)],
    }));
    let mut latch = Block::new(b(4))
        .with_param(v(20), Ty::I8)
        .with_param(v(21), Ty::I8);
    if mutation == 3 {
        latch
            .body
            .push(InstrNode::new(Inst::Undef { ty: Ty::I8 }).with_result(v(22)));
    }
    latch.body.push(InstrNode::new(Inst::Br {
        target: b(0),
        args: vec![if mutation == 3 { v(22) } else { v(20) }, v(21)],
    }));
    f.blocks = vec![header, nested, left, right, latch];
    f
}
fn bindings() -> Vec<(ValueId, String, u32)> {
    vec![(v(0), "a".into(), 8), (v(1), "b".into(), 8)]
}
fn specification() -> MirBlock {
    MirBlock {
        stmts: vec![],
        terminator: MirTerminator::Goto {
            target: 0,
            args: ["b", "a"]
                .map(|name| MirOperand::Var {
                    name: name.into(),
                    ty: MirScalarTy::UInt(Type::I8),
                })
                .to_vec(),
        },
    }
}
#[test]
fn every_path_agrees_and_wrong_common_value_refutes() {
    for mutation in [0, 2] {
        let model =
            model_back_edge_args_all_paths(&fixture(mutation), b(0), b(4), &bindings()).unwrap();
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model.args,
        };
        let result = check_back_edge_threading(
            "paths",
            &specification(),
            &bridge,
            &[],
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap();
        if mutation == 0 {
            assert!(matches!(result, RefinementOutcome::Refined));
        } else {
            assert!(
                matches!(result, RefinementOutcome::Refuted { .. }),
                "{result:?}"
            );
        }
    }
}
#[test]
fn one_wrong_edge_is_not_hidden_by_the_other_paths() {
    let error = model_back_edge_args_all_paths(&fixture(1), b(0), b(4), &bindings()).unwrap_err();
    assert!(error.contains("disagree"), "{error}");
}
#[test]
fn opaque_result_and_nested_cycle_are_rejected() {
    for (mutation, message) in [(3, "unmodeled"), (4, "nested cycle")] {
        let error = model_back_edge_args_all_paths(&fixture(mutation), b(0), b(4), &bindings())
            .unwrap_err();
        assert!(error.contains(message), "{error}");
    }
}
#[test]
fn missing_header_binding_cannot_become_an_invariant() {
    let error =
        model_back_edge_args_all_paths(&fixture(0), b(0), b(4), &bindings()[..1]).unwrap_err();
    assert!(error.contains("non-header"), "{error}");
}
#[test]
fn path_budget_fails_closed() {
    let mut f = fixture(0);
    // Nine equal-target conditional branches still denote 512 distinct edges.
    // Enumeration must decline instead of proving only a convenient prefix.
    f.blocks.clear();
    for index in 0..10 {
        let mut block = Block::new(b(index));
        if index == 0 {
            block.params = vec![(v(0), Ty::I8), (v(1), Ty::I8)];
        }
        block.body.push(if index == 9 {
            InstrNode::new(Inst::Br {
                target: b(0),
                args: vec![v(1), v(0)],
            })
        } else {
            branch(index + 1, index + 1)
        });
        f.blocks.push(block);
    }
    let error = model_back_edge_args_all_paths(&f, b(0), b(9), &bindings()).unwrap_err();
    assert!(error.contains("budget"), "{error}");
}
#[test]
fn parallel_phi_transfer_preserves_both_old_values() {
    let model = model_back_edge_args_all_paths(&fixture(0), b(0), b(4), &bindings()).unwrap();
    assert_eq!(model.args, vec![SmtExpr::var("b", 8), SmtExpr::var("a", 8)]);
}

#[test]
fn typed_use_of_unknown_producer_stays_opaque() {
    let mut f = fixture(0);
    f.blocks[0].body[0] = InstrNode::new(Inst::Call {
        callee: FuncId::new(7),
        args: vec![],
    })
    .with_result(v(11));
    f.blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::Bool,
            operand: v(11),
        })
        .with_result(v(10)),
    );
    let model = model_back_edge_args_all_paths(&f, b(0), b(4), &bindings()).unwrap();
    assert_eq!(model.args, vec![SmtExpr::var("b", 8), SmtExpr::var("a", 8)]);
    f.blocks[4].body.insert(
        0,
        InstrNode::new(Inst::Cast {
            op: trust_ir::CastOp::ZExt,
            src_ty: Ty::Bool,
            dst_ty: Ty::I8,
            operand: v(10),
        })
        .with_result(v(30)),
    );
    let Inst::Br { args, .. } = &mut f.blocks[4].body.last_mut().unwrap().inst else {
        unreachable!()
    };
    args[0] = v(30);
    let error = model_back_edge_args_all_paths(&f, b(0), b(4), &bindings()).unwrap_err();
    assert!(error.contains("unmodeled"), "{error}");
}

#[test]
fn aliased_or_non_header_bindings_are_rejected() {
    for bound in [
        vec![(v(0), "same".into(), 8), (v(1), "same".into(), 8)],
        vec![(v(0), "a".into(), 8), (v(99), "b".into(), 8)],
        vec![(v(0), "a".into(), 16), (v(1), "b".into(), 8)],
    ] {
        let error = model_back_edge_args_all_paths(&fixture(0), b(0), b(4), &bound).unwrap_err();
        assert!(error.contains("bindings"), "{error}");
    }
}
