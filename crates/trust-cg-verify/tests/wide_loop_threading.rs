//! Wide loop semantics: full constants, arithmetic flags and switch mutations.
use std::collections::{HashMap, HashSet};
use trust_cg_lower::Type;
use trust_cg_verify::ay_bridge::AYConfig;
use trust_cg_verify::loop_backedge_symexec::model_back_edge_args;
use trust_cg_verify::mir_semantics::{
    BridgeEdgeArgs, EdgeKind, MirBinOp, MirBlock, MirOperand, MirRvalue, MirScalarTy, MirStmt,
    MirTerminator, MirUnOp, RefinementOutcome, check_back_edge_threading, encode_block_store,
};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTyId, Function, Inst, InstrNode, SwitchCase, Ty, ValueId,
};

fn wide(value: u128, signed: bool) -> MirOperand {
    MirOperand::ConstInt128 { value, signed }
}
fn scalar(signed: bool) -> MirScalarTy {
    if signed {
        MirScalarTy::SInt(Type::I128)
    } else {
        MirScalarTy::UInt(Type::I128)
    }
}
fn fields(op: MirBinOp, signed: bool, a: u128, b: u128) -> (u128, bool) {
    let block = MirBlock::straight_line(vec![
        MirStmt {
            dst: "pair".into(),
            rvalue: MirRvalue::CheckedOverflowPacked {
                op,
                ty: scalar(signed),
                lhs: wide(a, signed),
                rhs: wide(b, signed),
            },
        },
        MirStmt {
            dst: "value".into(),
            rvalue: MirRvalue::PackedOverflowField {
                src: "pair".into(),
                field: 0,
                value_width: 128,
            },
        },
        MirStmt {
            dst: "flag".into(),
            rvalue: MirRvalue::PackedOverflowField {
                src: "pair".into(),
                field: 1,
                value_width: 128,
            },
        },
    ]);
    let mut store = encode_block_store(&block).unwrap();
    let value = store.resolve(&MirOperand::Var {
        name: "value".into(),
        ty: scalar(signed),
    });
    let flag = store.resolve(&MirOperand::Var {
        name: "flag".into(),
        ty: MirScalarTy::Bool,
    });
    let env = HashMap::new();
    (
        value.try_eval(&env).unwrap().as_u128(),
        flag.try_eval(&env).unwrap().as_u64() != 0,
    )
}

#[test]
fn wide_composed_addsub_matches_integer_oracle_at_both_limbs_and_sign_boundaries() {
    let edges = [
        0,
        1,
        2,
        3,
        (1 << 32) - 1,
        1 << 32,
        (1 << 64) - 1,
        1 << 64,
        (1 << 64) + 1,
        (1 << 127) - 1,
        1 << 127,
        (1 << 127) + 1,
        u128::MAX - 1,
        u128::MAX,
    ];
    let mut cases: Vec<_> = edges
        .into_iter()
        .flat_map(|a| edges.into_iter().map(move |b| (a, b)))
        .collect();
    let mut state = 0xa781_d803_237b_43af_7192_3791_124f_e159u128;
    for _ in 0..1024 {
        state ^= state << 23;
        state ^= state >> 17;
        state ^= state << 26;
        let a = state;
        state ^= state << 23;
        state ^= state >> 17;
        state ^= state << 26;
        cases.push((a, state));
    }
    for (a, b) in cases {
        for op in [MirBinOp::Add, MirBinOp::Sub] {
            let expected = match op {
                MirBinOp::Add => a.overflowing_add(b),
                MirBinOp::Sub => a.overflowing_sub(b),
                _ => unreachable!(),
            };
            assert_eq!(
                fields(op, false, a, b),
                expected,
                "unsigned {op:?} {a:x} {b:x}"
            );
            let expected = match op {
                MirBinOp::Add => (a as i128).overflowing_add(b as i128),
                MirBinOp::Sub => (a as i128).overflowing_sub(b as i128),
                _ => unreachable!(),
            };
            assert_eq!(
                fields(op, true, a, b),
                (expected.0 as u128, expected.1),
                "signed {op:?} {a:x} {b:x}"
            );
        }
    }
}

#[test]
fn wide_constants_and_complements_preserve_all_128_bits() {
    for value in [0, 1, u64::MAX as u128, 1 << 64, (1 << 127) + 7, u128::MAX] {
        for signed in [false, true] {
            let block = MirBlock::straight_line(vec![
                MirStmt {
                    dst: "x".into(),
                    rvalue: MirRvalue::Use {
                        src: wide(value, signed),
                    },
                },
                MirStmt {
                    dst: "not".into(),
                    rvalue: MirRvalue::UnaryOp {
                        op: MirUnOp::Not,
                        ty: scalar(signed),
                        operand: wide(value, signed),
                    },
                },
            ]);
            let mut store = encode_block_store(&block).unwrap();
            for (name, expected) in [("x", value), ("not", !value)] {
                let expr = store.resolve(&MirOperand::Var {
                    name: name.into(),
                    ty: scalar(signed),
                });
                assert_eq!(expr.try_bv_width().unwrap(), 128);
                assert_eq!(expr.try_eval(&HashMap::new()).unwrap().as_u128(), expected);
            }
            let lowered = trust_cg_verify::trust_ir_semantics::encode_trust_ir_bnot(
                Type::I128,
                trust_cg_verify::mir_semantics::encode_u128_constant(value),
            );
            assert_eq!(lowered.try_eval(&HashMap::new()).unwrap().as_u128(), !value);
        }
    }
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn constant(block: &mut Block, id: u32, value: u128) {
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U128,
            value: Constant::u128(value),
        })
        .with_result(v(id)),
    );
}
const CASE: u128 = (1 << 127) + 7;
const THEN: u128 = (1 << 127) + 5;
const ELSE: u128 = (1 << 80) + 9;
fn switch_loop(input: u128, case: u128, complement: bool) -> Function {
    let mut f = Function::new(FuncId::new(0), "wide_switch", FuncTyId::new(0), b(0));
    let mut entry = Block::new(b(0));
    constant(&mut entry, 0, 0);
    entry.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(0)],
    }));
    let mut header = Block::new(b(1)).with_param(v(10), Ty::U128);
    constant(&mut header, 1, input);
    header.body.push(InstrNode::new(Inst::Switch {
        value: v(1),
        cases: vec![SwitchCase {
            value: Constant::u128(case),
            target: b(2),
            args: vec![],
        }],
        default: b(3),
        default_args: vec![],
        exhaustive_enum_unreachable: false,
    }));
    let mut yes = Block::new(b(2));
    constant(&mut yes, 2, THEN);
    yes.body.push(InstrNode::new(Inst::Br {
        target: b(4),
        args: vec![v(2)],
    }));
    let mut no = Block::new(b(3));
    constant(&mut no, 3, ELSE);
    no.body.push(InstrNode::new(Inst::Br {
        target: b(4),
        args: vec![v(3)],
    }));
    let mut join = Block::new(b(4)).with_param(v(4), Ty::U128);
    if complement {
        join.body.push(
            InstrNode::new(Inst::UnOp {
                op: trust_ir::UnOp::Not,
                ty: Ty::U128,
                operand: v(4),
            })
            .with_result(v(5)),
        );
    }
    join.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(if complement { 5 } else { 4 })],
    }));
    f.blocks = vec![entry, header, yes, no, join];
    f
}
fn spec(input: u128, complement: bool) -> MirBlock {
    let mut stmts = vec![
        MirStmt {
            dst: "cond".into(),
            rvalue: MirRvalue::BinaryOp {
                op: MirBinOp::Eq,
                ty: scalar(false),
                lhs: wide(input, false),
                rhs: wide(CASE, false),
            },
        },
        MirStmt {
            dst: "next".into(),
            rvalue: MirRvalue::Select {
                cond: MirOperand::Var {
                    name: "cond".into(),
                    ty: MirScalarTy::Bool,
                },
                ty: scalar(false),
                then_val: wide(THEN, false),
                else_val: wide(ELSE, false),
            },
        },
    ];
    if complement {
        stmts.push(MirStmt {
            dst: "next".into(),
            rvalue: MirRvalue::UnaryOp {
                op: MirUnOp::Not,
                ty: scalar(false),
                operand: MirOperand::Var {
                    name: "next".into(),
                    ty: scalar(false),
                },
            },
        });
    }
    MirBlock {
        stmts,
        terminator: MirTerminator::Goto {
            target: 0,
            args: vec![MirOperand::Var {
                name: "next".into(),
                ty: scalar(false),
            }],
        },
    }
}

#[test]
fn wide_switch_and_complement_model_rejects_dropped_high_case_bits() {
    for input in [CASE, CASE as u64 as u128] {
        for complement in [false, true] {
            for mutation in [false, true] {
                let case = if mutation { CASE as u64 as u128 } else { CASE };
                let model = model_back_edge_args(
                    &switch_loop(input, case, complement),
                    b(1),
                    b(4),
                    &[(v(10), "seed".into(), 128)],
                    &HashSet::new(),
                )
                .unwrap();
                let mut expected = if input == CASE { THEN } else { ELSE };
                if complement {
                    expected = !expected;
                }
                let actual = model.args[0].try_eval(&HashMap::new()).unwrap().as_u128();
                assert_eq!(actual != expected, mutation);
                let outcome = check_back_edge_threading(
                    "wide_switch",
                    &spec(input, complement),
                    &BridgeEdgeArgs {
                        edge: EdgeKind::Goto,
                        args: model.args,
                    },
                    &[],
                    &model.extra_inputs,
                    &AYConfig::default(),
                )
                .unwrap();
                assert_eq!(
                    matches!(outcome, RefinementOutcome::Refined),
                    !mutation,
                    "{outcome:?}"
                );
            }
        }
    }
}

/// A wide multiply is a canonical overflow instruction. Its loop obligation
/// checks operand/flag threading; the instruction certificate checks flag value.
#[test]
fn wide_canonical_multiply_threads_its_own_flag_and_rejects_mutations() {
    for signed in [false, true] {
        let var = |name: &str| MirOperand::Var {
            name: name.into(),
            ty: scalar(signed),
        };
        let spec = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "pair".into(),
                    rvalue: MirRvalue::CheckedOverflowPacked {
                        op: MirBinOp::Mul,
                        ty: scalar(signed),
                        lhs: var("lhs"),
                        rhs: var("rhs"),
                    },
                },
                MirStmt {
                    dst: "value".into(),
                    rvalue: MirRvalue::PackedOverflowField {
                        src: "pair".into(),
                        field: 0,
                        value_width: 128,
                    },
                },
                MirStmt {
                    dst: "flag".into(),
                    rvalue: MirRvalue::PackedOverflowField {
                        src: "pair".into(),
                        field: 1,
                        value_width: 128,
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 1,
                args: vec![
                    var("value"),
                    var("rhs"),
                    MirOperand::Var {
                        name: "flag".into(),
                        ty: MirScalarTy::Bool,
                    },
                ],
            },
        };
        for mutation in ["none", "wrong_op", "wrong_rhs", "stale_flag"] {
            let ty = if signed { Ty::I128 } else { Ty::U128 };
            let mut f = Function::new(FuncId::new(0), "wide_mul", FuncTyId::new(0), b(0));
            let mut entry = Block::new(b(0))
                .with_param(v(0), ty.clone())
                .with_param(v(1), ty.clone())
                .with_param(v(2), Ty::Bool);
            entry.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(0), v(1), v(2)],
            }));
            let mut header = Block::new(b(1))
                .with_param(v(10), ty.clone())
                .with_param(v(11), ty.clone())
                .with_param(v(12), Ty::Bool);
            header.body.push(InstrNode::new(Inst::Br {
                target: b(2),
                args: vec![],
            }));
            let mut latch = Block::new(b(2));
            latch.body.push(
                InstrNode::new(Inst::Overflow {
                    op: if mutation == "wrong_op" {
                        trust_ir::OverflowOp::AddOverflow
                    } else {
                        trust_ir::OverflowOp::MulOverflow
                    },
                    ty,
                    lhs: v(10),
                    rhs: v(if mutation == "wrong_rhs" { 10 } else { 11 }),
                })
                .with_results([v(20), v(21)]),
            );
            latch.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![
                    v(20),
                    v(11),
                    v(if mutation == "stale_flag" { 12 } else { 21 }),
                ],
            }));
            f.blocks = vec![entry, header, latch];
            let model = model_back_edge_args(
                &f,
                b(1),
                b(2),
                &[
                    (v(10), "lhs".into(), 128),
                    (v(11), "rhs".into(), 128),
                    (v(12), "old_flag".into(), 1),
                ],
                &HashSet::new(),
            )
            .unwrap();
            let outcome = check_back_edge_threading(
                "wide_mul",
                &spec,
                &BridgeEdgeArgs {
                    edge: EdgeKind::Goto,
                    args: model.args,
                },
                &[],
                &model.extra_inputs,
                &AYConfig::default(),
            )
            .unwrap();
            if mutation == "none" {
                assert!(
                    matches!(outcome, RefinementOutcome::Refined),
                    "signed={signed}: {outcome:?}"
                );
            } else {
                assert!(
                    matches!(outcome, RefinementOutcome::Refuted { .. }),
                    "signed={signed} {mutation}: {outcome:?}"
                );
            }
        }
    }
}
