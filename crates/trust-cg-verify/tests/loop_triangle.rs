//! Compare a conditional loop update with its source semantics, including
//! mutations of each edge. No solver result is assumed by the concrete checks.
use std::collections::{HashMap, HashSet};
use trust_cg_lower::Type;
use trust_cg_verify::ay_bridge::AYConfig;
use trust_cg_verify::loop_backedge_symexec::model_back_edge_args;
use trust_cg_verify::mir_semantics::{
    BridgeEdgeArgs, EdgeKind, MirBinOp, MirBlock, MirOperand, MirRvalue, MirScalarTy, MirStmt,
    MirTerminator, RefinementOutcome, check_back_edge_threading, encode_block_store,
    overflow_flag_uf,
};
use trust_cg_verify::smt::SmtExpr;
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTyId, Function, ICmpOp, Inst, InstrNode,
    SwitchCase, Ty, ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
fn var(name: &str) -> MirOperand {
    MirOperand::Var {
        name: name.into(),
        ty: MirScalarTy::SInt(Type::I32),
    }
}

fn triangle(work_on_true: bool, mutation: u8) -> Function {
    let mut f = Function::new(FuncId::new(0), "triangle", FuncTyId::new(0), b(0));
    let mut entry = Block::new(b(0))
        .with_param(v(0), Ty::I32)
        .with_param(v(1), Ty::I32);
    entry.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(0), v(1)],
    }));
    let mut header = Block::new(b(1))
        .with_param(v(10), Ty::I32)
        .with_param(v(11), Ty::I32);
    header.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(v(2)),
    );
    header.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ne,
            ty: Ty::I32,
            lhs: v(11),
            rhs: v(2),
        })
        .with_result(v(3)),
    );
    header.body.push(InstrNode::new(Inst::CondBr {
        cond: v(3),
        then_target: b(2),
        then_args: vec![],
        else_target: b(5),
        else_args: vec![],
    }));
    let mut branch = Block::new(b(2));
    branch.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sgt,
            ty: Ty::I32,
            lhs: v(10),
            rhs: v(11),
        })
        .with_result(v(4)),
    );
    let empty_args = vec![if mutation == 1 { v(11) } else { v(10) }];
    branch.body.push(InstrNode::new(Inst::CondBr {
        cond: v(4),
        then_target: if work_on_true { b(3) } else { b(4) },
        then_args: if work_on_true {
            vec![]
        } else {
            empty_args.clone()
        },
        else_target: if work_on_true { b(4) } else { b(3) },
        else_args: if work_on_true { empty_args } else { vec![] },
    }));
    let mut work = Block::new(b(3));
    work.body.push(
        InstrNode::new(Inst::BinOp {
            op: if mutation == 2 {
                BinOp::Add
            } else {
                BinOp::Sub
            },
            ty: Ty::I32,
            lhs: v(10),
            rhs: v(11),
        })
        .with_result(v(5)),
    );
    work.body.push(InstrNode::new(Inst::Br {
        target: b(4),
        args: vec![v(5)],
    }));
    let mut join = Block::new(b(4)).with_param(v(6), Ty::I32);
    join.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(11), v(6)],
    }));
    let mut exit = Block::new(b(5));
    exit.body.push(InstrNode::new(Inst::Return {
        values: vec![v(10)],
    }));
    f.blocks = vec![entry, header, branch, work, join, exit];
    f
}

fn spec(work_on_true: bool) -> MirBlock {
    MirBlock {
        stmts: vec![
            MirStmt {
                dst: "cond".into(),
                rvalue: MirRvalue::BinaryOp {
                    op: MirBinOp::Gt,
                    ty: MirScalarTy::SInt(Type::I32),
                    lhs: var("x"),
                    rhs: var("y"),
                },
            },
            MirStmt {
                dst: "work".into(),
                rvalue: MirRvalue::BinaryOp {
                    op: MirBinOp::Sub,
                    ty: MirScalarTy::SInt(Type::I32),
                    lhs: var("x"),
                    rhs: var("y"),
                },
            },
            MirStmt {
                dst: "next".into(),
                rvalue: MirRvalue::Select {
                    cond: MirOperand::Var {
                        name: "cond".into(),
                        ty: MirScalarTy::Bool,
                    },
                    ty: MirScalarTy::SInt(Type::I32),
                    then_val: var(if work_on_true { "work" } else { "x" }),
                    else_val: var(if work_on_true { "x" } else { "work" }),
                },
            },
        ],
        terminator: MirTerminator::Goto {
            target: 0,
            args: vec![var("y"), var("next")],
        },
    }
}

#[test]
fn latch_triangle_rejects_a_third_join_predecessor() {
    for work_on_true in [false, true] {
        let mut f = triangle(work_on_true, 0);
        // Even an otherwise unreachable third predecessor prevents
        // the exact two-edge triangle classification.
        let mut extra = Block::new(b(6));
        extra.body.push(InstrNode::new(Inst::Br {
            target: b(4),
            args: vec![v(10)],
        }));
        f.blocks.push(extra);
        assert!(
            model_back_edge_args(
                &f,
                b(1),
                b(4),
                &[(v(10), "x".into(), 32), (v(11), "y".into(), 32)],
                &HashSet::new(),
            )
            .is_err()
        );
    }
}

#[test]
fn triangle_preserves_empty_edge_values_and_rejects_mutations() {
    for work_on_true in [false, true] {
        for mutation in 0..3 {
            let wrong = mutation != 0;
            let model = model_back_edge_args(
                &triangle(work_on_true, mutation),
                b(1),
                b(4),
                &[(v(10), "x".into(), 32), (v(11), "y".into(), 32)],
                &HashSet::new(),
            )
            .unwrap();
            let mut mismatches = 0;
            let inputs = [i32::MIN, -100, -1, 0, 1, 100, i32::MAX];
            for x in inputs {
                for y in inputs {
                    let env = HashMap::from([
                        ("x".to_owned(), x as u32 as u64),
                        ("y".to_owned(), y as u32 as u64),
                    ]);
                    let expected = if (x > y) == work_on_true {
                        x.wrapping_sub(y)
                    } else {
                        x
                    };
                    assert_eq!(
                        model.args[0].try_eval(&env).unwrap().as_u64(),
                        y as u32 as u64
                    );
                    mismatches += usize::from(
                        model.args[1].try_eval(&env).unwrap().as_u64() != expected as u32 as u64,
                    );
                }
            }
            assert_eq!(mismatches != 0, wrong);
            let outcome = check_back_edge_threading(
                "triangle",
                &spec(work_on_true),
                &BridgeEdgeArgs {
                    edge: EdgeKind::Goto,
                    args: model.args,
                },
                &[],
                &model.extra_inputs,
                &AYConfig::default(),
            )
            .unwrap();
            if wrong {
                assert!(
                    !matches!(outcome, RefinementOutcome::Refined),
                    "{outcome:?}"
                );
            } else {
                assert!(matches!(outcome, RefinementOutcome::Refined), "{outcome:?}");
            }
        }
    }
}

#[test]
fn triangle_conditional_exit_preserves_the_continuing_edge() {
    for integer_switch in [false, true] {
        let mut function = triangle(true, 0);
        let work = function
            .blocks
            .iter_mut()
            .find(|block| block.id == b(3))
            .unwrap();
        work.body.pop();
        work.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(2),
            })
            .with_result(v(7)),
        );
        work.body.push(InstrNode::new(Inst::CondBr {
            cond: v(7),
            then_target: b(5),
            then_args: vec![],
            else_target: b(4),
            else_args: vec![v(5)],
        }));
        if integer_switch {
            work.body.last_mut().unwrap().inst = Inst::Switch {
                value: v(10),
                cases: vec![SwitchCase {
                    value: Constant::Int(0),
                    target: b(5),
                    args: vec![],
                }],
                default: b(4),
                default_args: vec![v(5)],
                exhaustive_enum_unreachable: false,
            };
        }
        let bindings = [(v(10), "x".into(), 32), (v(11), "y".into(), 32)];
        let model =
            model_back_edge_args(&function, b(1), b(4), &bindings, &HashSet::new()).unwrap();
        let outcome = check_back_edge_threading(
            "conditional_exit",
            &spec(true),
            &BridgeEdgeArgs {
                edge: EdgeKind::Goto,
                args: model.args,
            },
            &[],
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap();
        assert!(matches!(outcome, RefinementOutcome::Refined), "{outcome:?}");
        let work = function
            .blocks
            .iter_mut()
            .find(|block| block.id == b(3))
            .unwrap();
        match &mut work.body.last_mut().unwrap().inst {
            Inst::CondBr { else_args, .. } => *else_args = vec![v(10)],
            Inst::Switch { default_args, .. } => *default_args = vec![v(10)],
            _ => unreachable!(),
        }
        let model =
            model_back_edge_args(&function, b(1), b(4), &bindings, &HashSet::new()).unwrap();
        let outcome = check_back_edge_threading(
            "conditional_exit_wrong",
            &spec(true),
            &BridgeEdgeArgs {
                edge: EdgeKind::Goto,
                args: model.args,
            },
            &[],
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap();
        assert!(
            !matches!(outcome, RefinementOutcome::Refined),
            "{outcome:?}"
        );
    }
}

#[test]
fn overflow_tuple_fields_keep_the_exact_arithmetic_and_flag() {
    for (width, ty) in [
        (8, Type::I8),
        (16, Type::I16),
        (32, Type::I32),
        (64, Type::I64),
    ] {
        for (op, tag) in [
            (MirBinOp::Add, "add"),
            (MirBinOp::Sub, "sub"),
            (MirBinOp::Mul, "mul"),
        ] {
            let scalar = MirScalarTy::UInt(ty.clone());
            let block = MirBlock::straight_line(vec![
                MirStmt {
                    dst: "pair".into(),
                    rvalue: MirRvalue::CheckedOverflowPacked {
                        op,
                        ty: scalar.clone(),
                        lhs: MirOperand::Var {
                            name: "a".into(),
                            ty: scalar.clone(),
                        },
                        rhs: MirOperand::Var {
                            name: "b".into(),
                            ty: scalar.clone(),
                        },
                    },
                },
                MirStmt {
                    dst: "value".into(),
                    rvalue: MirRvalue::PackedOverflowField {
                        src: "pair".into(),
                        field: 0,
                        value_width: width,
                    },
                },
                MirStmt {
                    dst: "flag".into(),
                    rvalue: MirRvalue::PackedOverflowField {
                        src: "pair".into(),
                        field: 1,
                        value_width: width,
                    },
                },
            ]);
            let mut store = encode_block_store(&block).unwrap();
            let a = SmtExpr::var("a", width);
            let b = SmtExpr::var("b", width);
            let value = match op {
                MirBinOp::Add => a.clone().bvadd(b.clone()),
                MirBinOp::Sub => a.clone().bvsub(b.clone()),
                MirBinOp::Mul => a.clone().bvmul(b.clone()),
                _ => unreachable!(),
            };
            assert_eq!(
                store.resolve(&MirOperand::Var {
                    name: "value".into(),
                    ty: scalar
                }),
                value
            );
            assert_eq!(
                store.resolve(&MirOperand::Var {
                    name: "flag".into(),
                    ty: MirScalarTy::Bool
                }),
                overflow_flag_uf(tag, width, a, b)
            );
        }
    }
}
