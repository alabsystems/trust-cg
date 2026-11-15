// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded value/capture evidence, not a closure-call or native-code proof.
use trust_cg_verify::fsym_trust_ir::{
    FsymTrustIrDiagnosticKind as K, FsymTrustIrReport, scan_function_in_module,
};
use trust_ir::{
    BinOp, Block, BlockId, ClosureTy, ClosureTyId, Constant, FuncId, FuncTy, Function, Inst,
    InstrNode, InterpretErrorCode, Interpreter, Module, Ty, ValueId,
};

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
fn val(i: u32, inst: Inst) -> InstrNode {
    InstrNode::new(inst).with_result(v(i))
}
fn integer(i: u32, n: i128) -> InstrNode {
    val(
        i,
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(n),
        },
    )
}
fn frame(i: u32, p: u32, n: u32) -> InstrNode {
    val(
        i,
        Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: FuncId::new(1),
            captures: vec![v(p), v(n)],
        },
    )
}
fn field(i: u32, env: u32, lane: u32, ty: Ty) -> InstrNode {
    val(
        i,
        Inst::ExtractField {
            ty,
            aggregate: v(env),
            field: lane,
        },
    )
}
fn load(i: u32, p: u32) -> InstrNode {
    val(
        i,
        Inst::Load {
            ty: Ty::I32,
            ptr: v(p),
            volatile: false,
            align: None,
        },
    )
}
fn ret(i: u32) -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![v(i)] })
}
fn fixture(body: Vec<InstrNode>) -> Module {
    let mut m = Module::new("fsym_runtime_closure");
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    });
    let source = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let apparent = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let physical = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    m.closure_types.push(ClosureTy {
        func: apparent,
        captures: vec![Ty::Ptr, Ty::I32],
    });
    let mut f = Function::new(FuncId::new(0), "subject", source, BlockId::new(0));
    f.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![],
        body,
    });
    m.functions.push(f);
    let mut target = Function::new(FuncId::new(1), "target", physical, BlockId::new(0));
    target.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::Ptr), (v(1), Ty::I32)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    });
    m.functions.push(target);
    m
}
fn scan(m: &Module) -> FsymTrustIrReport {
    scan_function_in_module(m, &m.functions[0])
}
fn assert_clean(m: &Module, expected: i128) {
    let report = scan(m);
    assert_eq!(report.scanned_functions, 1, "{report:?}");
    assert!(report.skipped_functions.is_empty(), "{report:?}");
    assert!(report.diagnostics.is_empty(), "{report:?}");
    assert!(report.unknown_obligations.is_empty(), "{report:?}");
    assert!(report.coverage_errors.is_empty(), "{report:?}");
    let result = Interpreter::with_module(m)
        .execute_func(FuncId::new(0), vec![])
        .unwrap();
    assert_eq!(result.returns[0].as_int().unwrap().as_signed(), expected);
}
fn assert_ub(m: &Module, kind: K) {
    let error = Interpreter::with_module(m)
        .execute_func(FuncId::new(0), vec![])
        .unwrap_err();
    assert_eq!(
        error.code,
        InterpretErrorCode::UndefinedBehavior,
        "{error:?}"
    );
    let report = scan(m);
    assert_eq!(report.scanned_functions, 1, "{report:?}");
    assert!(report.coverage_errors.is_empty(), "{report:?}");
    assert!(
        report.diagnostics.iter().any(|d| d.kind == kind),
        "{report:?}"
    );
}
fn live_prefix() -> Vec<InstrNode> {
    vec![
        val(
            0,
            Inst::HeapAlloc {
                ty: Ty::I32,
                count: None,
                align: None,
                origin: trust_ir::inst::AllocOrigin::CMalloc,
            },
        ),
        integer(1, 77),
        InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }),
        frame(2, 0, 1),
        val(
            3,
            Inst::Copy {
                ty: Ty::Closure(ClosureTyId::new(0)),
                operand: v(2),
            },
        ),
    ]
}

#[test]
fn copied_capture_preserves_live_pointer_identity() {
    let mut body = live_prefix();
    // Alloca is non-null in the scanner's model. CMalloc may fail, so its
    // dereferences correctly retain null Unknowns without a source guard.
    body[0] = val(
        0,
        Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: None,
        },
    );
    body.extend([field(4, 3, 0, Ty::Ptr), load(5, 4), ret(5)]);
    assert_clean(&fixture(body), 77);
}

#[test]
fn capture_update_copies_values_without_modifying_the_original() {
    let m = fixture(vec![
        val(0, Inst::NullPtr),
        integer(1, 3),
        frame(2, 0, 1),
        val(
            3,
            Inst::Copy {
                ty: Ty::Closure(ClosureTyId::new(0)),
                operand: v(2),
            },
        ),
        integer(4, 9),
        val(
            5,
            Inst::InsertField {
                ty: Ty::Closure(ClosureTyId::new(0)),
                aggregate: v(3),
                field: 1,
                value: v(4),
            },
        ),
        field(6, 2, 1, Ty::I32),
        field(7, 5, 1, Ty::I32),
        val(
            8,
            Inst::BinOp {
                op: BinOp::SDiv,
                ty: Ty::I32,
                lhs: v(7),
                rhs: v(6),
            },
        ),
        ret(8),
    ]);
    assert_clean(&m, 3);
}

#[test]
fn null_capture_is_still_null_after_copy_and_extract() {
    assert_ub(
        &fixture(vec![
            val(0, Inst::NullPtr),
            integer(1, 7),
            frame(2, 0, 1),
            val(
                3,
                Inst::Copy {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    operand: v(2),
                },
            ),
            field(4, 3, 0, Ty::Ptr),
            load(5, 4),
            ret(5),
        ]),
        K::NullDeref,
    );
}

#[test]
fn updating_one_frame_does_not_lose_the_null_in_the_new_value() {
    let mut body = live_prefix();
    body.extend([
        val(4, Inst::NullPtr),
        val(
            5,
            Inst::InsertField {
                ty: Ty::Closure(ClosureTyId::new(0)),
                aggregate: v(3),
                field: 0,
                value: v(4),
            },
        ),
        field(6, 2, 0, Ty::Ptr),
        load(7, 6),
        field(8, 5, 0, Ty::Ptr),
        load(9, 8),
        ret(9),
    ]);
    let m = fixture(body);
    assert_ub(&m, K::NullDeref);
    let report = scan(&m);
    assert_eq!(
        report
            .diagnostics
            .iter()
            .filter(|d| d.kind == K::NullDeref)
            .count(),
        1,
        "{report:?}"
    );
}

#[test]
fn capture_does_not_extend_an_allocations_lifetime() {
    let mut body = live_prefix();
    body.extend([
        InstrNode::new(Inst::Dealloc { ptr: v(0) }),
        field(4, 3, 0, Ty::Ptr),
        load(5, 4),
        ret(5),
    ]);
    assert_ub(&fixture(body), K::UseAfterFree);
}

#[test]
fn capture_lane_out_of_bounds_is_not_clean() {
    assert_ub(
        &fixture(vec![
            val(0, Inst::NullPtr),
            integer(1, 7),
            frame(2, 0, 1),
            field(3, 2, 2, Ty::I32),
            ret(3),
        ]),
        K::OutOfBounds,
    );
}

#[test]
fn an_escaped_capture_is_havocked_by_an_unsummarized_call() {
    let mut body = live_prefix();
    body.extend([
        InstrNode::new(Inst::Call {
            callee: FuncId::new(2),
            args: vec![],
        }),
        field(4, 3, 0, Ty::Ptr),
        load(5, 4),
        ret(5),
    ]);
    let mut m = fixture(body);
    let ty = m.closure_types[0].func;
    m.functions.push(Function::new(
        FuncId::new(2),
        "unknown_external",
        ty,
        BlockId::new(0),
    ));
    let report = scan(&m);
    assert_eq!(report.scanned_functions, 1, "{report:?}");
    assert!(
        report
            .unknown_obligations
            .iter()
            .any(|u| u.kind == K::UseAfterFree),
        "{report:?}"
    );
    assert!(report.coverage_errors.is_empty(), "{report:?}");
}

#[test]
fn construction_does_not_hide_a_poison_capture_source() {
    let m = fixture(vec![
        val(
            0,
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            },
        ),
        load(1, 0),
        frame(2, 0, 1),
        integer(3, 0),
        ret(3),
    ]);
    let error = Interpreter::with_module(&m)
        .execute_func(FuncId::new(0), vec![])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    let report = scan(&m);
    assert_eq!(report.scanned_functions, 1, "{report:?}");
    assert!(
        report
            .unknown_obligations
            .iter()
            .any(|u| u.kind == K::Uninitialized),
        "{report:?}"
    );
    assert!(report.coverage_errors.is_empty(), "{report:?}");
}

#[test]
fn malformed_or_unmodeled_constructions_stay_named_refusals() {
    let base = fixture(vec![
        val(0, Inst::NullPtr),
        integer(1, 7),
        frame(2, 0, 1),
        ret(1),
    ]);
    for (mut m, needle) in [
        (base.clone(), "target signature"),
        (base.clone(), "capture count"),
        (base, "flat scalar"),
    ] {
        match needle {
            "target signature" => m.func_types[m.functions[1].ty.as_usize()].params.reverse(),
            "capture count" => {
                let Inst::MakeClosure { captures, .. } = &mut m.functions[0].blocks[0].body[2].inst
                else {
                    unreachable!()
                };
                captures.pop();
            }
            _ => m.closure_types[0].captures[0] = Ty::Tuple(vec![Ty::Ptr]),
        }
        let report = scan(&m);
        assert_eq!(report.scanned_functions, 0, "{report:?}");
        assert!(
            report.skipped_functions[0].detail.contains(needle),
            "{report:?}"
        );
    }
}

#[test]
fn closure_invocation_still_requires_a_call_summary() {
    let mut m = fixture(vec![
        val(0, Inst::NullPtr),
        integer(1, 7),
        frame(2, 0, 1),
        InstrNode::new(Inst::CallIndirect {
            callee: v(2),
            sig: trust_ir::FuncTyId::new(1),
            args: vec![],
            calling_conv: trust_ir::CallingConv::Rust,
        }),
        ret(1),
    ]);
    // Keep the constructor itself supported; only the invocation is refused.
    m.functions[0].calling_conv = trust_ir::CallingConv::Rust;
    let report = scan(&m);
    assert_eq!(report.scanned_functions, 0, "{report:?}");
    assert!(
        report.skipped_functions[0]
            .detail
            .contains("CallIndirect requires callee/call-effect summaries"),
        "{report:?}"
    );
}

#[test]
fn closure_block_parameters_preserve_capture_provenance() {
    let mut body = live_prefix();
    body[0] = val(
        0,
        Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: None,
        },
    );
    body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![v(3)],
    }));
    let mut m = fixture(body);
    m.functions[0].blocks.push(Block {
        id: BlockId::new(1),
        params: vec![(v(10), Ty::Closure(ClosureTyId::new(0)))],
        body: vec![field(11, 10, 0, Ty::Ptr), load(12, 11), ret(12)],
    });
    assert_clean(&m, 77);
}
