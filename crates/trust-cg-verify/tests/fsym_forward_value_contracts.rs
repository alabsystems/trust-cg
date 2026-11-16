// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Forward source contracts: initialized storage is not a typed validity proof.
use trust_cg_verify::fsym_trust_ir::scan_function_in_module;
use trust_ir::*;

fn image_case(ty: Ty, byte: u8) -> Module {
    let mut m = Module::new("forward_memory_image");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::default(),
    });
    let mut e = EnumDef::new(
        EnumId::new(0),
        "Two",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    );
    e.discriminants = vec![Some(0), Some(1)];
    e.repr = Some(EnumTagRepr::U8);
    e.layout = Some(EnumLayoutDescriptor {
        size: 1,
        align: 1,
        variant_field_offsets: vec![vec![], vec![]],
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
    });
    m.enums.push(e);
    m.func_types
        .push(FuncTy::unrecorded(vec![], vec![Ty::U64], false));
    let mut f = Function::new(
        FuncId::new(0),
        "read_image",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    let mut value = |id, inst| {
        let mut node = InstrNode::new(inst);
        node.results.push(ValueId::new(id));
        b.body.push(node);
    };
    value(
        0,
        Inst::Alloca {
            ty: ty.clone(),
            count: None,
            align: Some(1),
        },
    );
    value(
        1,
        Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(byte.into()),
        },
    );
    value(
        2,
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1),
        },
    );
    b.body.push(InstrNode::new(Inst::MemSet {
        dst: ValueId::new(0),
        byte: ValueId::new(1),
        bytes: ValueId::new(2),
    }));
    let mut load = InstrNode::new(Inst::Load {
        ty,
        ptr: ValueId::new(0),
        align: Some(1),
        volatile: false,
    });
    load.results.push(ValueId::new(3));
    b.body.push(load);
    let mut result = InstrNode::new(Inst::Const {
        ty: Ty::U64,
        value: Constant::Int(9),
    });
    result.results.push(ValueId::new(4));
    b.body.push(result);
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    f.blocks.push(b);
    m.functions.push(f);
    m
}

#[test]
fn initialized_invalid_enum_bytes_are_observed_ub_and_a_named_refusal() {
    for byte in [0, 1, 2, 255] {
        let m = image_case(Ty::Enum(EnumId::new(0)), byte);
        let observed = Interpreter::with_module(&m).execute_func(FuncId::new(0), vec![]);
        if byte < 2 {
            assert!(observed.is_ok(), "valid tag control: {observed:?}");
        } else {
            assert_eq!(
                observed.unwrap_err().code,
                InterpretErrorCode::UndefinedBehavior
            );
        }
        let report = scan_function_in_module(&m, &m.functions[0]);
        assert_eq!(report.scanned_functions, 0, "{report:?}");
        assert!(report.coverage_errors.is_empty(), "{report:?}");
        assert!(
            report
                .skipped_functions
                .iter()
                .any(|skip| skip.detail.contains("enum-containing")),
            "{report:?}"
        );
        assert!(
            report.unknown_obligations.is_empty(),
            "an unsupported image earns no verdict: {report:?}"
        );
    }
}

#[test]
fn scalar_image_retains_ordinary_admission_and_no_enum_validity_unknown() {
    let m = image_case(Ty::U8, 255);
    assert!(
        Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), vec![])
            .is_ok()
    );
    let report = scan_function_in_module(&m, &m.functions[0]);
    assert_eq!(report.scanned_functions, 1, "{report:?}");
    assert!(report.coverage_errors.is_empty(), "{report:?}");
    assert!(report.skipped_functions.is_empty(), "{report:?}");
}

#[test]
fn unused_recorded_abi_cannot_borrow_an_unrecorded_functions_bounded_verdict() {
    use trust_ir::signature_abi::*;
    let mut m = image_case(Ty::U8, 0);
    let target = m.target_info.as_ref().unwrap();
    let mut sig = FuncTy::unrecorded(vec![], vec![], false);
    sig.abi = Some(SignatureAbi {
        target: AbiTarget {
            triple: target.triple.clone(),
            data_layout: "e-m:e-i64:64-i128:128-n32:64-S128".into(),
            abi: "aapcs".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "bounded-negative-control".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "bounded-negative-control".into(),
            revision: "1".into(),
        },
        convention: "aapcs".into(),
        lowered_convention: CallingConv::C,
        source_abi: "C".into(),
        can_unwind: true,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: AbiArgument {
            size: 0,
            align: 1,
            mode: AbiPassMode::Ignore,
            bindings: vec![],
        },
    });
    sig.abi.as_ref().unwrap().validate(&sig).unwrap();
    sig.abi
        .as_ref()
        .unwrap()
        .validate_target(m.target_info.as_ref())
        .unwrap();
    m.func_types.push(sig);
    let report = scan_function_in_module(&m, &m.functions[0]);
    assert_eq!(report.scanned_functions, 0, "{report:?}");
    assert!(
        report
            .skipped_functions
            .iter()
            .any(|s| s.detail.contains("signature ABI")),
        "{report:?}"
    );
    m.func_types.pop();
    assert_eq!(
        scan_function_in_module(&m, &m.functions[0]).scanned_functions,
        1
    );
}

#[test]
fn ordinary_zero_sized_cast_is_a_type_refusal_before_image_decoding() {
    let mut m = image_case(Ty::U8, 0);
    m.enums[0].variants.truncate(1);
    m.enums[0].discriminants.clear();
    m.enums[0].layout = Some(EnumLayoutDescriptor {
        size: 0,
        align: 1,
        variant_field_offsets: vec![vec![]],
        encoding: EnumTagEncoding::SingleInhabited { variant: 0 },
    });
    m.func_types[0] = FuncTy::unrecorded(vec![], vec![Ty::Enum(EnumId::new(0))], false);
    let mut constant = InstrNode::new(Inst::Const {
        ty: Ty::Unit,
        value: Constant::PhantomData,
    });
    constant.results.push(ValueId::new(0));
    let mut cast = InstrNode::new(Inst::Cast {
        op: CastOp::Bitcast,
        src_ty: Ty::Unit,
        dst_ty: Ty::Enum(EnumId::new(0)),
        operand: ValueId::new(0),
    });
    cast.results.push(ValueId::new(1));
    m.functions[0].blocks[0].body = vec![
        constant,
        cast,
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    assert_eq!(
        Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), vec![])
            .unwrap_err()
            .code,
        InterpretErrorCode::TypeError
    );
    let report = scan_function_in_module(&m, &m.functions[0]);
    assert_eq!(report.scanned_functions, 0, "{report:?}");
    assert!(
        report
            .skipped_functions
            .iter()
            .any(|skip| skip.detail.contains("enum-containing")),
        "{report:?}"
    );
}

#[test]
fn genuine_nominal_zero_image_codec_executes_but_has_no_bounded_identity_model() {
    let mut m = image_case(Ty::U8, 0);
    m.func_types[0] = FuncTy::unrecorded(vec![], vec![Ty::FnItem(FuncId::new(1))], false);
    m.func_types.push(FuncTy::unrecorded(vec![], vec![], false));
    m.functions.push(Function::new(
        FuncId::new(1),
        "nominal_target",
        FuncTyId::new(1),
        BlockId::new(0),
    ));
    let mut constant = InstrNode::new(Inst::Const {
        ty: Ty::Unit,
        value: Constant::PhantomData,
    });
    constant.results.push(ValueId::new(0));
    let mut cast = InstrNode::new(Inst::Cast {
        op: CastOp::Bitcast,
        src_ty: Ty::Unit,
        dst_ty: Ty::FnItem(FuncId::new(1)),
        operand: ValueId::new(0),
    });
    cast.results.push(ValueId::new(1));
    m.functions[0].blocks[0].body = vec![
        constant,
        cast,
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    let observed = Interpreter::with_module(&m)
        .execute_func(FuncId::new(0), vec![])
        .unwrap();
    assert!(
        matches!(observed.returns.as_slice(), [InterpretValue { kind: InterpretValueKind::FnItem(id), .. }] if *id == FuncId::new(1))
    );
    let report = scan_function_in_module(&m, &m.functions[0]);
    assert_eq!(report.scanned_functions, 0, "{report:?}");
    assert!(
        report
            .skipped_functions
            .iter()
            .any(|skip| skip.detail.contains("FnItem nominal identity")),
        "{report:?}"
    );
    // An unreferenced nominal type cannot borrow a clean neighbor's verdict.
    let mut unused = image_case(Ty::U8, 255);
    unused.types.push(Ty::FnItem(FuncId::new(0)));
    assert_eq!(
        scan_function_in_module(&unused, &unused.functions[0]).scanned_functions,
        0
    );
    unused.types.pop();
    assert_eq!(
        scan_function_in_module(&unused, &unused.functions[0]).scanned_functions,
        1
    );
    let mut supplied = unused.functions[0].clone();
    assert_eq!(
        scan_function_in_module(&unused, &supplied).scanned_functions,
        1
    );
    let mut unit = InstrNode::new(Inst::Const {
        ty: Ty::Unit,
        value: Constant::PhantomData,
    });
    unit.results.push(ValueId::new(90));
    let mut nominal = InstrNode::new(Inst::Cast {
        op: CastOp::Bitcast,
        src_ty: Ty::Unit,
        dst_ty: Ty::FnItem(FuncId::new(0)),
        operand: ValueId::new(90),
    });
    nominal.results.push(ValueId::new(91));
    supplied.blocks[0].body.splice(0..0, [unit, nominal]);
    let outside = scan_function_in_module(&unused, &supplied);
    assert_eq!(outside.scanned_functions, 0, "{outside:?}");
    assert!(
        outside
            .skipped_functions
            .iter()
            .any(|skip| skip.detail.contains("FnItem nominal identity")),
        "{outside:?}"
    );
    assert_eq!(
        scan_function_in_module(&unused, &unused.functions[0]).scanned_functions,
        1
    );
}
