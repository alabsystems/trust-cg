// trust_ir_conformance_manifest.rs - executable TrustIr coverage ledger
//
// This is a deliberately small foothold: every row is a live adapter check,
// so moving a surface from fail_closed to supported requires updating both
// the implementation and this manifest.

use std::collections::HashSet;

use trust_cg_lower::adapter::{AdapterError, translate_function, translate_module, translate_type};
use trust_cg_lower::instructions::{AtomicRmwOp as LirAtomicRmwOp, Instruction, IntCC, Opcode};
use trust_cg_lower::types::Type;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::value::{BindingFrameId, SourceSpan};
use trust_ir::{
    AtomicRMWOp, BinOp, Block as TrustIrBlock, BlockId, CallingConv, CastOp, ClosureTy,
    ClosureTyId, Constant, EnumId, FCmpOp, FatPtrKind, FieldDef, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ordering,
    OverflowOp, Pred, PredId, RecordDef, RecordId, SetRepr, StructId, SwitchCase, Ty, TyId,
    ValueId,
};
use trust_ir::{
    ProofDigest, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
    ProofReplayIdentity, ProofTransform, ProofTransformStage,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CoverageStatus {
    Supported,
    FailClosed,
}

#[derive(Debug, Clone, Copy)]
enum DiagnosticClass {
    UnsupportedInstruction,
    UnsupportedType,
}

struct CoverageRow {
    category: &'static str,
    surface: &'static str,
    status: CoverageStatus,
    check: fn(),
}

struct InventoryRow {
    enum_name: &'static str,
    variant: &'static str,
    status: CoverageStatus,
    evidence: &'static str,
}

#[allow(dead_code)]
struct EnumVariantInventory {
    enum_name: &'static str,
    expected_variants: &'static [&'static str],
    actual_variants: fn() -> Vec<&'static str>,
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn f(n: u32) -> FuncId {
    FuncId::new(n)
}

fn module_with_blocks(
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    blocks: Vec<TrustIrBlock>,
) -> TrustIrModule {
    let entry = blocks.first().expect("test module must have an entry").id;
    let mut module = TrustIrModule::new(name);
    let ty = module.add_func_type(FuncTy {
        params,
        returns,
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(f(0), name, ty, entry);
    func.blocks = blocks;
    module.add_function(func);
    module
}

fn translate_single(
    module: &TrustIrModule,
) -> Result<trust_cg_lower::function::Function, AdapterError> {
    let func = module
        .functions
        .first()
        .expect("test module must have one function");
    translate_function(func, module).map(|(func, _proofs)| func)
}

fn expect_fail_closed(err: AdapterError, class: DiagnosticClass, needle: &str) {
    match (class, err) {
        (
            DiagnosticClass::UnsupportedInstruction,
            AdapterError::UnsupportedInstruction(message),
        ) => {
            assert!(
                message.contains(needle),
                "expected UnsupportedInstruction containing `{needle}`, got `{message}`"
            );
        }
        (DiagnosticClass::UnsupportedType, AdapterError::UnsupportedType(message)) => {
            assert!(
                message.contains(needle),
                "expected UnsupportedType containing `{needle}`, got `{message}`"
            );
        }
        (expected, other) => panic!("expected {expected:?}, got {other:?}"),
    }
}

fn expect_fail_closed_all(err: AdapterError, class: DiagnosticClass, needles: &[&str]) {
    match (class, err) {
        (
            DiagnosticClass::UnsupportedInstruction,
            AdapterError::UnsupportedInstruction(message),
        ) => {
            for needle in needles {
                assert!(
                    message.contains(needle),
                    "expected UnsupportedInstruction containing `{needle}`, got `{message}`"
                );
            }
        }
        (DiagnosticClass::UnsupportedType, AdapterError::UnsupportedType(message)) => {
            for needle in needles {
                assert!(
                    message.contains(needle),
                    "expected UnsupportedType containing `{needle}`, got `{message}`"
                );
            }
        }
        (expected, other) => panic!("expected {expected:?}, got {other:?}"),
    }
}

fn binop_module(name: &str, op: BinOp, ty: Ty) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![ty.clone(), ty.clone()],
        vec![ty.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), ty.clone()), (v(1), ty.clone())],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op,
                    ty,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    )
}

fn binop_module_typed(
    name: &str,
    op: BinOp,
    declared_ty: Ty,
    lhs_ty: Ty,
    rhs_ty: Ty,
) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![lhs_ty.clone(), rhs_ty.clone()],
        vec![declared_ty.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), lhs_ty), (v(1), rhs_ty)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: declared_ty,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    )
}

fn atomic_rmw_module(name: &str, op: AtomicRMWOp) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![Ty::Ptr, Ty::I64],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::AtomicRMW {
                    op,
                    ty: Ty::I64,
                    ptr: v(0),
                    value: v(1),
                    ordering: Ordering::SeqCst,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    )
}

fn cast_module_typed(name: &str, op: CastOp, src_ty: Ty, dst_ty: Ty) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![src_ty.clone()],
        vec![dst_ty.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), src_ty.clone())],
            body: vec![
                InstrNode::new(Inst::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand: v(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
    )
}

fn unop_module(name: &str, op: trust_ir::UnOp, ty: Ty) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![ty.clone()],
        vec![ty.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), ty.clone())],
            body: vec![
                InstrNode::new(Inst::UnOp {
                    op,
                    ty,
                    operand: v(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
    )
}

fn const_module(name: &str, ty: Ty, value: Constant) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![],
        vec![ty.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const { ty, value }).with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    )
}

fn reify_materialized_fndef_module(name: &str) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let callee_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let caller_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::Ptr],
        is_vararg: false,
    });

    let mut callee = TrustIrFunction::new(f(0), "manifest_reify_target", callee_ty, b(0));
    callee.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![InstrNode::new(Inst::Unreachable)],
    });

    let mut caller = TrustIrFunction::new(f(1), name, caller_ty, b(0));
    caller.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(callee_ty),
                value: Constant::FnDef(f(0)),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(callee_ty),
                dst_ty: Ty::Ptr,
                operand: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });

    module.add_function(callee);
    module.add_function(caller);
    module
}

fn sequence_const_module(name: &str, values: Vec<Constant>) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let elem_tyid = module.add_type(Ty::I64);
    let func_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(f(0), name, func_ty, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Sequence(elem_tyid),
                value: Constant::Sequence(values),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);
    module
}

fn record_const_module(name: &str) -> TrustIrModule {
    let record_id = RecordId::new(0);
    let mut module = TrustIrModule::new(name);
    module.add_record(RecordDef {
        id: record_id,
        name: "ManifestRecord".to_string(),
        fields: vec![
            FieldDef {
                name: "left".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "right".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
    });
    let func_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(f(0), name, func_ty, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Record(record_id),
                value: Constant::Record(vec![
                    ("right".to_string(), Constant::Int(2)),
                    ("left".to_string(), Constant::Int(1)),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);
    module
}

fn record_extract_module(name: &str) -> TrustIrModule {
    let record_id = RecordId::new(0);
    let mut module = TrustIrModule::new(name);
    module.add_record(RecordDef {
        id: record_id,
        name: "ManifestRecord".to_string(),
        fields: vec![
            FieldDef {
                name: "left".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "right".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
    });
    let func_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(f(0), name, func_ty, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Record(record_id),
                value: Constant::Record(vec![
                    ("right".to_string(), Constant::Int(2)),
                    ("left".to_string(), Constant::Int(1)),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Record(record_id),
                aggregate: v(0),
                field: 1,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    }];
    module.add_function(func);
    module
}

fn record_insert_module(name: &str) -> TrustIrModule {
    let mut module = record_const_module(name);
    let func = module
        .functions
        .first_mut()
        .expect("record fixture must contain one function");
    func.blocks[0].body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Record(RecordId::new(0)),
            value: Constant::Record(vec![
                ("right".to_string(), Constant::Int(2)),
                ("left".to_string(), Constant::Int(1)),
            ]),
        })
        .with_result(v(0)),
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(3),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::InsertField {
            ty: Ty::Record(RecordId::new(0)),
            aggregate: v(0),
            field: 1,
            value: v(1),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    module
}

fn single_inst_module(
    name: &str,
    params: Vec<(ValueId, Ty)>,
    returns: Vec<Ty>,
    inst: InstrNode,
    return_values: Vec<ValueId>,
) -> TrustIrModule {
    module_with_blocks(
        name,
        params.iter().map(|(_, ty)| ty.clone()).collect(),
        returns,
        vec![TrustIrBlock {
            id: b(0),
            params,
            body: vec![
                inst,
                InstrNode::new(Inst::Return {
                    values: return_values,
                }),
            ],
        }],
    )
}

fn expect_supported(module: &TrustIrModule, surface: &str) -> trust_cg_lower::function::Function {
    translate_single(module)
        .unwrap_or_else(|err| panic!("{surface} must remain supported: {err:?}"))
}

fn check_scalar_binops_supported() {
    for (op, ty) in [
        (BinOp::Add, Ty::I64),
        (BinOp::Sub, Ty::I64),
        (BinOp::Mul, Ty::I64),
        (BinOp::UDiv, Ty::I64),
        (BinOp::SDiv, Ty::I64),
        (BinOp::URem, Ty::I64),
        (BinOp::SRem, Ty::I64),
        (BinOp::And, Ty::I64),
        (BinOp::Or, Ty::I64),
        (BinOp::Xor, Ty::I64),
        (BinOp::Shl, Ty::I64),
        (BinOp::LShr, Ty::I64),
        (BinOp::AShr, Ty::I64),
        (BinOp::FAdd, Ty::F64),
        (BinOp::FSub, Ty::F64),
        (BinOp::FMul, Ty::F64),
        (BinOp::FDiv, Ty::F64),
    ] {
        expect_supported(
            &binop_module("manifest_scalar_binop", op, ty),
            "scalar BinOp",
        );
    }
}

fn check_vector_binops_supported() {
    for (surface, ty, cases) in [
        (
            "<4 x i32>",
            Ty::Vector(Box::new(Ty::I32), 4),
            &[
                (BinOp::Add, Opcode::V4I32Add),
                (BinOp::Sub, Opcode::V4I32Sub),
                (BinOp::Mul, Opcode::V4I32Mul),
            ][..],
        ),
        // <16 x i8>/<8 x i16> Mul lower through the typed V16I8Mul/V8I16Mul ops:
        // x86-64 lowers them through an SSE2 unpack/PMULLW/pack sequence and
        // AArch64 has direct NEON MUL.16B/MUL.8H.
        (
            "<16 x i8>",
            Ty::Vector(Box::new(Ty::I8), 16),
            &[
                (BinOp::Add, Opcode::V16I8Add),
                (BinOp::Sub, Opcode::V16I8Sub),
                (BinOp::Mul, Opcode::V16I8Mul),
            ][..],
        ),
        (
            "<8 x i16>",
            Ty::Vector(Box::new(Ty::I16), 8),
            &[
                (BinOp::Add, Opcode::V8I16Add),
                (BinOp::Sub, Opcode::V8I16Sub),
                (BinOp::Mul, Opcode::V8I16Mul),
            ][..],
        ),
        // <2 x i64> Mul lowers through the typed V2I64Mul op: neither SSE2 nor
        // baseline NEON has a single-instruction packed i64 multiply, so both
        // ISels lower it through scalar lane extraction, two 64-bit scalar
        // multiplies, and a vector repack (no adapter lane-memory).
        (
            "<2 x i64>",
            Ty::Vector(Box::new(Ty::I64), 2),
            &[
                (BinOp::Add, Opcode::V2I64Add),
                (BinOp::Sub, Opcode::V2I64Sub),
                (BinOp::Mul, Opcode::V2I64Mul),
            ][..],
        ),
    ] {
        for (op, expected) in cases.iter().cloned() {
            let func = expect_supported(
                &binop_module("manifest_vector_binop", op, ty.clone()),
                surface,
            );
            let entry = &func.blocks[&func.entry_block];
            assert_eq!(entry.instructions[0].opcode, expected, "{surface} {op:?}");
            assert_eq!(
                func.value_types.get(&entry.instructions[0].results[0]),
                Some(&Type::V128),
                "{surface} {op:?} must produce V128 LIR"
            );
        }
    }
}

fn check_frem_f64_lowers_to_fmod_libcall() {
    // Scalar FRem has no native machine instruction: the adapter lowers it to a
    // call to the libm `fmod` symbol (resolved by the linker), exactly as
    // C/Rust define floating-point remainder. This is bit-exact, not an Fdiv
    // approximation.
    let func = expect_supported(
        &binop_module("manifest_frem_f64", BinOp::FRem, Ty::F64),
        "FRem f64",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(&inst.opcode, Opcode::Call { name } if name == "fmod")),
        "FRem f64 must lower to a call to fmod, got {:?}",
        entry.instructions
    );
}

fn check_frem_f32_lowers_to_fmodf_libcall() {
    let func = expect_supported(
        &binop_module("manifest_frem_f32", BinOp::FRem, Ty::F32),
        "FRem f32",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(&inst.opcode, Opcode::Call { name } if name == "fmodf")),
        "FRem f32 must lower to a call to fmodf, got {:?}",
        entry.instructions
    );
}

fn check_frem_f16_lowers_via_promoted_fmodf() {
    let func = expect_supported(
        &binop_module("manifest_frem_f16", BinOp::FRem, Ty::F16),
        "FRem f16",
    );
    let entry = &func.blocks[&func.entry_block];
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::FPExt))
            .count(),
        2,
        "FRem f16 must promote both operands to f32"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(&inst.opcode, Opcode::Call { name } if name == "fmodf")),
        "FRem f16 must call fmodf on the promoted operands"
    );
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::FPTrunc)),
        "FRem f16 must demote the f32 remainder back to f16"
    );
}

fn check_integer_binop_float_declared_fail_closed() {
    let err = translate_single(&binop_module("manifest_add_f64", BinOp::Add, Ty::F64))
        .expect_err("integer BinOp over a float declared type must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["BinOp::Add", "scalar lowering", "F64"],
    );
}

fn check_float_binop_integer_declared_fail_closed() {
    let err = translate_single(&binop_module("manifest_fadd_i64", BinOp::FAdd, Ty::I64))
        .expect_err("float BinOp over an integer declared type must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["BinOp::FAdd", "scalar lowering", "I64"],
    );
}

fn check_binop_operand_type_mismatch_fail_closed() {
    let err = translate_single(&binop_module_typed(
        "manifest_binop_operand_mismatch",
        BinOp::Add,
        Ty::I64,
        Ty::I64,
        Ty::I32,
    ))
    .expect_err("BinOp operands must match the declared scalar type");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "BinOp::Add",
            "operand type mismatch",
            "declared ty=I64",
            "I32",
        ],
    );
}

fn check_shift_float_declared_fail_closed() {
    let err = translate_single(&binop_module("manifest_shl_f64", BinOp::Shl, Ty::F64))
        .expect_err("integer shift over a float declared type must fail closed");
    // `binop_module` gives both operands the declared type, so the shift COUNT is
    // F64 — the adapter rejects it at the shift-count-type check (which runs
    // before the declared-type "scalar lowering" check). Either way it fails
    // closed; assert the message it actually produces.
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["BinOp::Shl", "must be an integer scalar", "F64"],
    );
}

fn fcmp_module(name: &str, declared_ty: Ty, lhs_ty: Ty, rhs_ty: Ty) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![lhs_ty.clone(), rhs_ty.clone()],
        vec![Ty::Bool],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), lhs_ty), (v(1), rhs_ty)],
            body: vec![
                InstrNode::new(Inst::FCmp {
                    op: FCmpOp::OEq,
                    ty: declared_ty,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    )
}

fn icmp_module(name: &str, op: ICmpOp, declared_ty: Ty, lhs_ty: Ty, rhs_ty: Ty) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![lhs_ty.clone(), rhs_ty.clone()],
        vec![Ty::Bool],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), lhs_ty), (v(1), rhs_ty)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: declared_ty,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    )
}

fn vector_icmp_module(name: &str, op: ICmpOp, ty: Ty, mask_ty: Ty) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![ty.clone(), ty.clone()],
        vec![mask_ty],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), ty.clone()), (v(1), ty.clone())],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op,
                    ty,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    )
}

fn check_icmp_scalar_integer_supported() {
    let func = expect_supported(
        &icmp_module(
            "manifest_icmp_scalar_integer",
            ICmpOp::Slt,
            Ty::I64,
            Ty::I64,
            Ty::I64,
        ),
        "ICmp scalar integer",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(matches!(entry.instructions[0].opcode, Opcode::Icmp { .. }));
}

fn check_icmp_v4i32_signed_vector_supported() {
    let ty = Ty::Vector(Box::new(Ty::I32), 4);
    let mask_ty = Ty::Vector(Box::new(Ty::Bool), 4);
    for (op, expected) in [
        (ICmpOp::Eq, Opcode::V4I32Icmp { cond: IntCC::Equal }),
        (
            ICmpOp::Ne,
            Opcode::V4I32Icmp {
                cond: IntCC::NotEqual,
            },
        ),
        (
            ICmpOp::Slt,
            Opcode::V4I32Icmp {
                cond: IntCC::SignedLessThan,
            },
        ),
        (
            ICmpOp::Sle,
            Opcode::V4I32Icmp {
                cond: IntCC::SignedLessThanOrEqual,
            },
        ),
        (
            ICmpOp::Sgt,
            Opcode::V4I32Icmp {
                cond: IntCC::SignedGreaterThan,
            },
        ),
        (
            ICmpOp::Sge,
            Opcode::V4I32Icmp {
                cond: IntCC::SignedGreaterThanOrEqual,
            },
        ),
    ] {
        let func = expect_supported(
            &vector_icmp_module(
                "manifest_icmp_v4i32_signed_vector",
                op,
                ty.clone(),
                mask_ty.clone(),
            ),
            "ICmp <4 x i32> signed vector",
        );
        let entry = &func.blocks[&func.entry_block];
        assert_eq!(entry.instructions[0].opcode, expected, "ICmp::{op:?}");
        assert_eq!(
            func.value_types.get(&entry.instructions[0].results[0]),
            Some(&Type::V128),
            "ICmp::{op:?} must produce a V128 lane mask"
        );
    }
}

fn check_icmp_v4i32_unsigned_vector_supported() {
    let ty = Ty::Vector(Box::new(Ty::I32), 4);
    let mask_ty = Ty::Vector(Box::new(Ty::Bool), 4);
    for (op, expected) in [
        (
            ICmpOp::Ult,
            Opcode::V4I32Icmp {
                cond: IntCC::UnsignedLessThan,
            },
        ),
        (
            ICmpOp::Ule,
            Opcode::V4I32Icmp {
                cond: IntCC::UnsignedLessThanOrEqual,
            },
        ),
        (
            ICmpOp::Ugt,
            Opcode::V4I32Icmp {
                cond: IntCC::UnsignedGreaterThan,
            },
        ),
        (
            ICmpOp::Uge,
            Opcode::V4I32Icmp {
                cond: IntCC::UnsignedGreaterThanOrEqual,
            },
        ),
    ] {
        let func = expect_supported(
            &vector_icmp_module(
                "manifest_icmp_v4i32_unsigned_vector",
                op,
                ty.clone(),
                mask_ty.clone(),
            ),
            "ICmp <4 x i32> unsigned vector",
        );
        let entry = &func.blocks[&func.entry_block];
        assert_eq!(entry.instructions[0].opcode, expected, "ICmp::{op:?}");
        assert_eq!(
            func.value_types.get(&entry.instructions[0].results[0]),
            Some(&Type::V128),
            "ICmp::{op:?} must produce a V128 lane mask"
        );
    }
}

fn check_icmp_narrow_unsigned_vector_supported() {
    // Unsigned narrow-vector compares lower through the typed `V16I8Icmp`/
    // `V8I16Icmp` ops: x86-64 lowers unsigned predicates with a sign-bit bias
    // before PCMPGTB/PCMPGTW and AArch64 has direct NEON CMHI/CMHS. The adapter
    // emits the typed compare op rather than scalarizing the lanes.
    for (name, ty, mask_ty, op, cond) in [
        (
            "manifest_icmp_v16i8_ult_vector",
            Ty::Vector(Box::new(Ty::I8), 16),
            Ty::Vector(Box::new(Ty::Bool), 16),
            ICmpOp::Ult,
            IntCC::UnsignedLessThan,
        ),
        (
            "manifest_icmp_v16i8_ule_vector",
            Ty::Vector(Box::new(Ty::I8), 16),
            Ty::Vector(Box::new(Ty::Bool), 16),
            ICmpOp::Ule,
            IntCC::UnsignedLessThanOrEqual,
        ),
        (
            "manifest_icmp_v16i8_ugt_vector",
            Ty::Vector(Box::new(Ty::I8), 16),
            Ty::Vector(Box::new(Ty::Bool), 16),
            ICmpOp::Ugt,
            IntCC::UnsignedGreaterThan,
        ),
        (
            "manifest_icmp_v16i8_uge_vector",
            Ty::Vector(Box::new(Ty::I8), 16),
            Ty::Vector(Box::new(Ty::Bool), 16),
            ICmpOp::Uge,
            IntCC::UnsignedGreaterThanOrEqual,
        ),
        (
            "manifest_icmp_v8i16_ult_vector",
            Ty::Vector(Box::new(Ty::I16), 8),
            Ty::Vector(Box::new(Ty::Bool), 8),
            ICmpOp::Ult,
            IntCC::UnsignedLessThan,
        ),
        (
            "manifest_icmp_v8i16_ule_vector",
            Ty::Vector(Box::new(Ty::I16), 8),
            Ty::Vector(Box::new(Ty::Bool), 8),
            ICmpOp::Ule,
            IntCC::UnsignedLessThanOrEqual,
        ),
        (
            "manifest_icmp_v8i16_ugt_vector",
            Ty::Vector(Box::new(Ty::I16), 8),
            Ty::Vector(Box::new(Ty::Bool), 8),
            ICmpOp::Ugt,
            IntCC::UnsignedGreaterThan,
        ),
        (
            "manifest_icmp_v8i16_uge_vector",
            Ty::Vector(Box::new(Ty::I16), 8),
            Ty::Vector(Box::new(Ty::Bool), 8),
            ICmpOp::Uge,
            IntCC::UnsignedGreaterThanOrEqual,
        ),
    ] {
        let is_v16i8 = matches!(&ty, Ty::Vector(elem, 16) if **elem == Ty::I8);
        let expected = if is_v16i8 {
            Opcode::V16I8Icmp { cond }
        } else {
            Opcode::V8I16Icmp { cond }
        };
        let func = expect_supported(
            &vector_icmp_module(name, op, ty, mask_ty),
            "ICmp narrow unsigned vector",
        );
        let entry = &func.blocks[&func.entry_block];
        assert_eq!(entry.instructions[0].opcode, expected, "ICmp::{op:?}");
        assert_eq!(
            func.value_types.get(&entry.instructions[0].results[0]),
            Some(&Type::V128),
            "ICmp::{op:?} must produce a V128 lane mask"
        );
    }
}

fn check_icmp_v2i64_unsigned_vector_supported() {
    // Unsigned <2 x i64> compares lower through the typed `V2I64Icmp` op:
    // baseline x86-64 lowers them through dword-half PCMPGTD/PCMPEQD sequences
    // with a sign-bit bias, and AArch64 lowers them directly through NEON.
    let ty = Ty::Vector(Box::new(Ty::I64), 2);
    let mask_ty = Ty::Vector(Box::new(Ty::Bool), 2);
    for (op, cond) in [
        (ICmpOp::Ult, IntCC::UnsignedLessThan),
        (ICmpOp::Ule, IntCC::UnsignedLessThanOrEqual),
        (ICmpOp::Ugt, IntCC::UnsignedGreaterThan),
        (ICmpOp::Uge, IntCC::UnsignedGreaterThanOrEqual),
    ] {
        let func = expect_supported(
            &vector_icmp_module(
                "manifest_icmp_v2i64_unsigned_vector",
                op,
                ty.clone(),
                mask_ty.clone(),
            ),
            "ICmp <2 x i64> unsigned vector",
        );
        let entry = &func.blocks[&func.entry_block];
        assert_eq!(
            entry.instructions[0].opcode,
            Opcode::V2I64Icmp { cond },
            "ICmp::{op:?}"
        );
        assert_eq!(
            func.value_types.get(&entry.instructions[0].results[0]),
            Some(&Type::V128),
            "ICmp::{op:?} must produce a V128 lane mask"
        );
    }
}

fn check_icmp_declared_non_integer_fail_closed() {
    let err = translate_single(&icmp_module(
        "manifest_icmp_declared_non_integer",
        ICmpOp::Eq,
        Ty::F64,
        Ty::F64,
        Ty::F64,
    ))
    .expect_err("ICmp over a non-integer declared type must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["ICmp::Eq", "integer scalar", "F64"],
    );
}

fn check_icmp_operand_type_mismatch_fail_closed() {
    let err = translate_single(&icmp_module(
        "manifest_icmp_operand_type_mismatch",
        ICmpOp::Eq,
        Ty::I64,
        Ty::I64,
        Ty::I32,
    ))
    .expect_err("ICmp operands must match the declared scalar type");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["ICmp", "operand type mismatch", "declared ty=I64", "I32"],
    );
}

fn check_icmp_pointer_eq_ne_supported() {
    // Eq/Ne and the UNSIGNED orderings all lower as a raw address comparison:
    // a pointer carries its address in a pointer-width integer register, so an
    // unsigned-condition `Icmp` over the two pointer operands IS the address
    // comparison the frontend intends (e.g. hashbrown `current >= end`).
    for (op, cond) in [
        (ICmpOp::Eq, IntCC::Equal),
        (ICmpOp::Ne, IntCC::NotEqual),
        (ICmpOp::Ult, IntCC::UnsignedLessThan),
        (ICmpOp::Ule, IntCC::UnsignedLessThanOrEqual),
        (ICmpOp::Ugt, IntCC::UnsignedGreaterThan),
        (ICmpOp::Uge, IntCC::UnsignedGreaterThanOrEqual),
    ] {
        let func = expect_supported(
            &icmp_module("manifest_icmp_pointer_eq_ne", op, Ty::Ptr, Ty::Ptr, Ty::Ptr),
            "ICmp pointer Eq/Ne/unsigned-ordering",
        );
        let entry = &func.blocks[&func.entry_block];
        assert!(
            entry
                .instructions
                .iter()
                .any(|inst| matches!(inst.opcode, Opcode::Icmp { cond: actual } if actual == cond)),
            "pointer ICmp::{op:?} must lower as raw address comparison"
        );
    }
}

fn check_icmp_pointer_relational_fail_closed() {
    // SIGNED pointer orderings remain fail-closed: an address is unsigned, so a
    // signed ordering over pointers is never a well-formed frontend emission.
    let err = translate_single(&icmp_module(
        "manifest_icmp_pointer",
        ICmpOp::Slt,
        Ty::Ptr,
        Ty::Ptr,
        Ty::Ptr,
    ))
    .expect_err("signed relational ICmp over pointers must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["ICmp::Slt", "pointer-like", "Ptr"],
    );
}

fn check_fcmp_scalar_float_supported() {
    for ty in [Ty::F16, Ty::F32, Ty::F64] {
        let func = expect_supported(
            &fcmp_module("manifest_fcmp_scalar_float", ty.clone(), ty.clone(), ty),
            "FCmp scalar float",
        );
        let entry = &func.blocks[&func.entry_block];
        assert!(matches!(entry.instructions[0].opcode, Opcode::Fcmp { .. }));
    }
}

fn check_fcmp_declared_non_float_fail_closed() {
    let err = translate_single(&fcmp_module(
        "manifest_fcmp_declared_non_float",
        Ty::I64,
        Ty::I64,
        Ty::I64,
    ))
    .expect_err("FCmp over a non-float declared type must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["FCmp", "scalar float", "I64"],
    );
}

fn check_fcmp_operand_type_mismatch_fail_closed() {
    let err = translate_single(&fcmp_module(
        "manifest_fcmp_operand_type_mismatch",
        Ty::F64,
        Ty::F64,
        Ty::F32,
    ))
    .expect_err("FCmp operands must match the declared float type");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["FCmp", "operand type mismatch", "declared ty=F64", "F32"],
    );
}

fn check_unops_supported() {
    for (op, ty) in [
        (trust_ir::UnOp::Neg, Ty::I64),
        (trust_ir::UnOp::FNeg, Ty::F64),
        (trust_ir::UnOp::Not, Ty::I64),
        (trust_ir::UnOp::CtPop, Ty::I64),
    ] {
        expect_supported(&unop_module("manifest_unop", op, ty), "UnOp");
    }
}

fn check_unop_wrong_type_fail_closed() {
    for (op, ty, expected) in [
        (trust_ir::UnOp::FNeg, Ty::I64, "UnOp::FNeg"),
        (trust_ir::UnOp::Neg, Ty::F64, "UnOp::Neg"),
        (trust_ir::UnOp::CtPop, Ty::F64, "UnOp::CtPop"),
    ] {
        let err = translate_single(&unop_module("manifest_unop_wrong_type", op, ty.clone()))
            .expect_err("UnOp over an unsupported scalar type must fail closed");
        expect_fail_closed_all(
            err,
            DiagnosticClass::UnsupportedInstruction,
            &[expected, "scalar lowering"],
        );
    }
}

fn check_atomic_supported_ops() {
    for (op, expected) in [
        (AtomicRMWOp::Xchg, LirAtomicRmwOp::Xchg),
        (AtomicRMWOp::Add, LirAtomicRmwOp::Add),
        (AtomicRMWOp::Sub, LirAtomicRmwOp::Sub),
        (AtomicRMWOp::And, LirAtomicRmwOp::And),
        (AtomicRMWOp::Or, LirAtomicRmwOp::Or),
        (AtomicRMWOp::Xor, LirAtomicRmwOp::Xor),
        (AtomicRMWOp::Max, LirAtomicRmwOp::Max),
        (AtomicRMWOp::Min, LirAtomicRmwOp::Min),
        (AtomicRMWOp::UMax, LirAtomicRmwOp::UMax),
        (AtomicRMWOp::UMin, LirAtomicRmwOp::UMin),
    ] {
        let func = expect_supported(
            &atomic_rmw_module("manifest_atomic_supported", op),
            "supported AtomicRMW",
        );
        let entry = &func.blocks[&func.entry_block];
        assert!(matches!(
            &entry.instructions[0].opcode,
            Opcode::AtomicRmw { op: actual, .. } if actual == &expected
        ));
    }
}

fn atomic_load_module(name: &str, ordering: Ordering) -> TrustIrModule {
    single_inst_module(
        name,
        vec![(v(0), Ty::Ptr)],
        vec![Ty::I64],
        InstrNode::new(Inst::AtomicLoad {
            ty: Ty::I64,
            ptr: v(0),
            ordering,
        })
        .with_result(v(1)),
        vec![v(1)],
    )
}

fn atomic_store_module(name: &str, ordering: Ordering) -> TrustIrModule {
    single_inst_module(
        name,
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![],
        InstrNode::new(Inst::AtomicStore {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering,
        }),
        vec![],
    )
}

fn check_atomic_load_store_supported_orderings() {
    for ordering in [Ordering::Relaxed, Ordering::Acquire, Ordering::SeqCst] {
        expect_supported(
            &atomic_load_module("manifest_atomic_load_supported", ordering),
            "AtomicLoad supported ordering",
        );
    }

    for ordering in [Ordering::Relaxed, Ordering::Release, Ordering::SeqCst] {
        expect_supported(
            &atomic_store_module("manifest_atomic_store_supported", ordering),
            "AtomicStore supported ordering",
        );
    }
}

fn check_atomic_load_release_fail_closed() {
    let err = translate_single(&atomic_load_module(
        "manifest_atomic_load_release",
        Ordering::Release,
    ))
    .expect_err("AtomicLoad Release ordering must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["AtomicLoad", "invalid ordering", "Release"],
    );
}

fn check_atomic_load_acqrel_fail_closed() {
    let err = translate_single(&atomic_load_module(
        "manifest_atomic_load_acqrel",
        Ordering::AcqRel,
    ))
    .expect_err("AtomicLoad AcqRel ordering must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["AtomicLoad", "invalid ordering", "AcqRel"],
    );
}

fn check_atomic_store_acquire_fail_closed() {
    let err = translate_single(&atomic_store_module(
        "manifest_atomic_store_acquire",
        Ordering::Acquire,
    ))
    .expect_err("AtomicStore Acquire ordering must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["AtomicStore", "invalid ordering", "Acquire"],
    );
}

fn check_atomic_store_acqrel_fail_closed() {
    let err = translate_single(&atomic_store_module(
        "manifest_atomic_store_acqrel",
        Ordering::AcqRel,
    ))
    .expect_err("AtomicStore AcqRel ordering must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["AtomicStore", "invalid ordering", "AcqRel"],
    );
}

fn volatile_load_module(name: &str) -> TrustIrModule {
    single_inst_module(
        name,
        vec![(v(0), Ty::Ptr)],
        vec![Ty::I64],
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: v(0),
            volatile: true,
            align: None,
        })
        .with_result(v(1)),
        vec![v(1)],
    )
}

fn volatile_store_module(name: &str) -> TrustIrModule {
    single_inst_module(
        name,
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![],
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: true,
            align: None,
        }),
        vec![],
    )
}

fn check_volatile_load_supported() {
    // Volatile load lowers to the distinct `VolatileLoad` opcode -> a byte-
    // identical machine load classified as a memory barrier, so the optimizer
    // never elides/CSEs/hoists it. Verified end-to-end (two volatile reads emit
    // two machine loads; a plain read pair CSEs to one).
    expect_supported(
        &volatile_load_module("manifest_volatile_load"),
        "volatile Load",
    );
}

fn check_volatile_store_supported() {
    expect_supported(
        &volatile_store_module("manifest_volatile_store"),
        "volatile Store",
    );
}

fn aligned_load_module(name: &str, align: u64) -> TrustIrModule {
    single_inst_module(
        name,
        vec![(v(0), Ty::Ptr)],
        vec![Ty::I64],
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: v(0),
            volatile: false,
            align: Some(align),
        })
        .with_result(v(1)),
        vec![v(1)],
    )
}

fn aligned_store_module(name: &str, align: u64) -> TrustIrModule {
    single_inst_module(
        name,
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![],
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(align),
        }),
        vec![],
    )
}

fn aligned_alloca_module(name: &str) -> TrustIrModule {
    single_inst_module(
        name,
        vec![],
        vec![Ty::Ptr],
        InstrNode::new(Inst::Alloca {
            ty: Ty::I8,
            count: None,
            align: Some(16),
        })
        .with_result(v(0)),
        vec![v(0)],
    )
}

fn invalid_aligned_alloca_module(name: &str, align: u64) -> TrustIrModule {
    single_inst_module(
        name,
        vec![],
        vec![Ty::Ptr],
        InstrNode::new(Inst::Alloca {
            ty: Ty::I8,
            count: None,
            align: Some(align),
        })
        .with_result(v(0)),
        vec![v(0)],
    )
}

fn check_load_natural_explicit_align_supported() {
    let func = expect_supported(
        &aligned_load_module("manifest_load_natural_explicit_align", 8),
        "Load natural explicit align",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::Load {
            ty: Type::I64,
            align: Some(8)
        }
    ));
}

fn check_store_natural_explicit_align_supported() {
    let func = expect_supported(
        &aligned_store_module("manifest_store_natural_explicit_align", 8),
        "Store natural explicit align",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::Store {
            ty: Type::I64,
            align: Some(8)
        }
    ));
}

fn check_load_stronger_explicit_align_supported() {
    let func = expect_supported(
        &aligned_load_module("manifest_load_stronger_explicit_align", 16),
        "Load stronger-than-natural explicit align",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::Load {
            ty: Type::I64,
            align: Some(16)
        }
    ));
}

fn check_store_stronger_explicit_align_supported() {
    let func = expect_supported(
        &aligned_store_module("manifest_store_stronger_explicit_align", 16),
        "Store stronger-than-natural explicit align",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::Store {
            ty: Type::I64,
            align: Some(16)
        }
    ));
}

fn check_alloca_explicit_align_supported() {
    let func = expect_supported(
        &aligned_alloca_module("manifest_alloca_explicit_align"),
        "Alloca explicit align",
    );
    assert_eq!(
        func.stack_slots[0].align, 16,
        "Alloca explicit align must be preserved in StackSlotInfo"
    );
}

fn check_alloca_invalid_explicit_align_fail_closed() {
    let err = translate_single(&invalid_aligned_alloca_module(
        "manifest_alloca_invalid_explicit_align",
        3,
    ))
    .expect_err("Alloca invalid explicit align must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Alloca", "explicit align 3", "invalid"],
    );
}

fn scalar_select_module(name: &str, cond_ty: Ty, then_ty: Ty, else_ty: Ty) -> TrustIrModule {
    single_inst_module(
        name,
        vec![(v(0), cond_ty), (v(1), then_ty), (v(2), else_ty)],
        vec![Ty::I64],
        InstrNode::new(Inst::Select {
            ty: Ty::I64,
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        })
        .with_result(v(3)),
        vec![v(3)],
    )
}

fn vector_select_bad_cond_module(name: &str) -> TrustIrModule {
    let vec_ty = Ty::Vector(Box::new(Ty::I32), 4);
    single_inst_module(
        name,
        vec![
            (v(0), Ty::Bool),
            (v(1), vec_ty.clone()),
            (v(2), vec_ty.clone()),
        ],
        vec![vec_ty.clone()],
        InstrNode::new(Inst::Select {
            ty: vec_ty,
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        })
        .with_result(v(3)),
        vec![v(3)],
    )
}

fn check_select_scalar_bool_condition_supported() {
    expect_supported(
        &scalar_select_module("manifest_select_scalar_bool", Ty::Bool, Ty::I64, Ty::I64),
        "scalar Select with Bool condition",
    );
}

fn check_select_scalar_non_bool_condition_fail_closed() {
    let err = translate_single(&scalar_select_module(
        "manifest_select_scalar_non_bool",
        Ty::I64,
        Ty::I64,
        Ty::I64,
    ))
    .expect_err("scalar Select condition must be Bool");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Select scalar condition", "Bool", "I64"],
    );
}

fn check_select_operand_type_mismatch_fail_closed() {
    let err = translate_single(&scalar_select_module(
        "manifest_select_operand_mismatch",
        Ty::Bool,
        Ty::I64,
        Ty::I32,
    ))
    .expect_err("Select operands must match the declared result type");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Select else operand type", "I32", "I64"],
    );
}

fn check_select_vector_condition_mask_mismatch_fail_closed() {
    let err = translate_single(&vector_select_bad_cond_module(
        "manifest_select_vector_condition_mismatch",
    ))
    .expect_err("vector Select condition must be matching bool mask");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Select over <4 x i32>", "<4 x bool>", "Bool"],
    );
}

fn check_standard_casts_supported() {
    for (op, src_ty, dst_ty) in [
        (CastOp::Trunc, Ty::I64, Ty::I32),
        (CastOp::ZExt, Ty::U32, Ty::U64),
        (CastOp::SExt, Ty::I32, Ty::I64),
        (CastOp::FPTrunc, Ty::F64, Ty::F32),
        (CastOp::FPExt, Ty::F32, Ty::F64),
        (CastOp::FPToUI, Ty::F64, Ty::U64),
        (CastOp::FPToSI, Ty::F64, Ty::I64),
        (CastOp::UIToFP, Ty::U64, Ty::F64),
        (CastOp::SIToFP, Ty::I64, Ty::F64),
        (CastOp::PtrToInt, Ty::Ptr, Ty::I64),
        (CastOp::IntToPtr, Ty::I64, Ty::Ptr),
        (CastOp::PtrToPtr, Ty::Ptr, Ty::Ptr),
        (CastOp::Bitcast, Ty::I64, Ty::F64),
    ] {
        let module = module_with_blocks(
            "manifest_standard_cast",
            vec![src_ty.clone()],
            vec![dst_ty.clone()],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), src_ty.clone())],
                body: vec![
                    InstrNode::new(Inst::Cast {
                        op,
                        src_ty,
                        dst_ty,
                        operand: v(0),
                    })
                    .with_result(v(1)),
                    InstrNode::new(Inst::Return { values: vec![v(1)] }),
                ],
            }],
        );
        expect_supported(&module, "standard CastOp");
    }
}

fn check_transmute_equal_size_fail_closed() {
    let err = translate_single(&cast_module_typed(
        "manifest_transmute_equal_size",
        CastOp::Transmute,
        Ty::I64,
        Ty::F64,
    ))
    .expect_err("equal-size Transmute must fail closed until validity/provenance checks exist");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "CastOp::Transmute",
            "equal-size bit reinterpretation",
            "src_size=8",
            "dst_size=8",
            "validity",
            "pointer-provenance",
        ],
    );
}

fn check_malformed_pointer_casts_fail_closed() {
    for (name, op, src_ty, dst_ty) in [
        (
            "manifest_bad_ptr_to_int",
            CastOp::PtrToInt,
            Ty::I64,
            Ty::I64,
        ),
        (
            "manifest_bad_int_to_ptr",
            CastOp::IntToPtr,
            Ty::I32,
            Ty::Ptr,
        ),
        (
            "manifest_bad_ptr_to_ptr",
            CastOp::PtrToPtr,
            Ty::I64,
            Ty::Ptr,
        ),
    ] {
        let err = translate_single(&cast_module_typed(name, op, src_ty, dst_ty))
            .expect_err("malformed pointer cast must fail closed before LIR copy emission");
        expect_fail_closed_all(
            err,
            DiagnosticClass::UnsupportedInstruction,
            &[
                "CastOp::",
                "source/destination shape",
                "provenance-compatible",
            ],
        );
    }
}

fn check_wrong_direction_integer_casts_fail_closed() {
    for (name, op, src_ty, dst_ty) in [
        ("manifest_bad_zext", CastOp::ZExt, Ty::U64, Ty::U32),
        ("manifest_bad_sext", CastOp::SExt, Ty::I64, Ty::I32),
        ("manifest_bad_trunc", CastOp::Trunc, Ty::I32, Ty::I64),
    ] {
        let err = translate_single(&cast_module_typed(name, op, src_ty, dst_ty))
            .expect_err("wrong-direction integer cast must fail closed before LIR emission");
        expect_fail_closed_all(
            err,
            DiagnosticClass::UnsupportedInstruction,
            &[
                "CastOp::",
                "source/destination shape",
                "integer/float width",
            ],
        );
    }
}

fn check_transmute_size_mismatch_fail_closed() {
    let err = translate_single(&cast_module_typed(
        "manifest_transmute_size_mismatch",
        CastOp::Transmute,
        Ty::I64,
        Ty::I32,
    ))
    .expect_err("size-mismatched Transmute must fail closed before any truncating lowering");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "CastOp::Transmute",
            "layout sizes differ",
            "src_size=8",
            "dst_size=4",
            "layout",
        ],
    );
}

fn check_reify_fn_pointer_materialized_fndef_supported() {
    let funcs = translate_module(&reify_materialized_fndef_module(
        "manifest_reify_materialized_fndef",
    ))
    .expect("ReifyFnPointer should lower for materialized function-symbol values");
    let caller = funcs
        .iter()
        .find(|(func, _)| func.name == "manifest_reify_materialized_fndef")
        .expect("caller should translate")
        .0
        .clone();
    let entry = &caller.blocks[&caller.entry_block];

    assert!(matches!(
        &entry.instructions[0].opcode,
        Opcode::GlobalRef { name } if name == "manifest_reify_target"
    ));
    assert!(matches!(entry.instructions[1].opcode, Opcode::Copy));
    assert_eq!(
        entry.instructions[1].args,
        vec![entry.instructions[0].results[0]]
    );
    assert_eq!(
        caller.value_types.get(&entry.instructions[1].results[0]),
        Some(&Type::I64)
    );
}

fn check_reify_fn_pointer_without_provenance_fail_closed() {
    let err = translate_single(&cast_module_typed(
        "manifest_reify_fn_pointer_without_provenance",
        CastOp::ReifyFnPointer,
        Ty::Func(FuncTyId::new(1)),
        Ty::Ptr,
    ))
    .expect_err("ReifyFnPointer must fail closed without materialized function-symbol provenance");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "CastOp::ReifyFnPointer",
            "materialized function-symbol/code-pointer provenance",
            "code-pointer ABI",
            "symbol relocation",
            "proof provenance",
        ],
    );
}

fn check_scalar_constants_supported() {
    for (ty, value) in [
        (Ty::I64, Constant::Int(42)),
        (Ty::F64, Constant::Float(3.5)),
        (Ty::Bool, Constant::Bool(true)),
    ] {
        expect_supported(
            &const_module("manifest_scalar_constant", ty, value),
            "scalar Constant",
        );
    }
}

fn check_vector_constant_supported() {
    expect_supported(
        &const_module(
            "manifest_vector_constant",
            Ty::Vector(Box::new(Ty::I32), 4),
            Constant::Vector(vec![
                Constant::Int(1),
                Constant::Int(2),
                Constant::Int(3),
                Constant::Int(4),
            ]),
        ),
        "Constant::Vector",
    );
}

fn check_phantom_constant_fail_closed() {
    let err = translate_single(&const_module(
        "manifest_phantom_const",
        Ty::I64,
        Constant::PhantomData,
    ))
    .expect_err("PhantomData constants must fail closed until ZST materialization is explicit");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "aggregate/closure constant",
    );
}

fn check_fndef_unregistered_fail_closed() {
    let err = translate_single(&const_module(
        "manifest_fndef_unregistered",
        Ty::Func(FuncTyId::new(0)),
        Constant::FnDef(f(99)),
    ))
    .expect_err("unregistered function-symbol constants must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["function symbol constant", "unregistered FuncId(99)"],
    );
}

fn check_control_and_pseudo_insts_supported() {
    let copy = single_inst_module(
        "manifest_copy",
        vec![(v(0), Ty::I64)],
        vec![Ty::I64],
        InstrNode::new(Inst::Copy {
            ty: Ty::I64,
            operand: v(0),
        })
        .with_result(v(1)),
        vec![v(1)],
    );
    expect_supported(&copy, "Inst::Copy");

    let unreachable = module_with_blocks(
        "manifest_unreachable",
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Unreachable)],
        }],
    );
    expect_supported(&unreachable, "Inst::Unreachable");
}

fn check_assume_supported() {
    let module = single_inst_module(
        "manifest_assume",
        vec![(v(0), Ty::Bool)],
        vec![],
        InstrNode::new(Inst::Assume { cond: v(0) }),
        vec![],
    );
    let func = translate_single(&module).expect("Inst::Assume should lower as a checked assert");
    assert!(
        func.blocks
            .values()
            .flat_map(|block| block.instructions.iter())
            .any(|inst| matches!(inst.opcode, Opcode::Assert)),
        "Inst::Assume must materialize a checked runtime assertion"
    );
}

fn check_assume_non_bool_condition_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_assume_non_bool",
        vec![(v(0), Ty::I32)],
        vec![],
        InstrNode::new(Inst::Assume { cond: v(0) }),
        vec![],
    ))
    .expect_err("Inst::Assume with non-Bool condition must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Inst::Assume", "condition", "Bool"],
    );
}

fn switch_module(name: &str, selector_ty: Ty, cases: Vec<SwitchCase>) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![selector_ty.clone()],
        vec![],
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), selector_ty)],
                body: vec![InstrNode::new(Inst::Switch {
                    value: v(0),
                    default: b(1),
                    default_args: vec![],
                    cases,
                    exhaustive_enum_unreachable: false,
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
            TrustIrBlock {
                id: b(3),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
        ],
    )
}

fn check_switch_supported() {
    let module = switch_module(
        "manifest_switch_supported",
        Ty::U8,
        vec![
            SwitchCase {
                value: Constant::Int(255),
                target: b(2),
                args: vec![],
            },
            SwitchCase {
                value: Constant::Int(1),
                target: b(3),
                args: vec![],
            },
        ],
    );
    let func = expect_supported(&module, "Inst::Switch");
    let entry = &func.blocks[&func.entry_block];
    let Opcode::Switch { cases, .. } = &entry.instructions[0].opcode else {
        panic!(
            "expected Switch opcode, got {:?}",
            entry.instructions[0].opcode
        );
    };
    // A U8 selector is ZERO-extended before the per-case equality compare, so a
    // high-bit case constant (255) must normalize to its zero-extended value 255,
    // NOT sign-extended to -1 (MISCOMPILE #62 — sign-extending it produced a
    // `cmp r64, -1` that never matched the zero-extended selector).
    assert_eq!(
        cases.iter().map(|(value, _)| *value).collect::<Vec<_>>(),
        vec![255, 1]
    );
}

fn check_switch_non_integer_selector_fail_closed() {
    let err = translate_single(&switch_module(
        "manifest_switch_non_integer_selector",
        Ty::F64,
        vec![SwitchCase {
            value: Constant::Int(1),
            target: b(2),
            args: vec![],
        }],
    ))
    .expect_err("non-integer switch selectors must fail closed");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "non-integer switch selector type",
    );
}

fn check_switch_unsupported_selector_width_fail_closed() {
    let err = translate_single(&switch_module(
        "manifest_switch_i128_selector",
        Ty::I128,
        vec![SwitchCase {
            value: Constant::Int(1),
            target: b(2),
            args: vec![],
        }],
    ))
    .expect_err("128-bit switch selectors must fail closed until target lowering supports them");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "unsupported switch selector width",
    );
}

fn check_switch_duplicate_normalized_case_fail_closed() {
    let err = translate_single(&switch_module(
        "manifest_switch_duplicate_normalized_case",
        Ty::I8,
        vec![
            SwitchCase {
                value: Constant::Int(-1),
                target: b(2),
                args: vec![],
            },
            SwitchCase {
                value: Constant::Int(255),
                target: b(3),
                args: vec![],
            },
        ],
    ))
    .expect_err("duplicate normalized switch cases must fail closed");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "duplicate switch case value after 8-bit selector normalization",
    );
}

fn check_switch_non_integer_case_fail_closed() {
    let err = translate_single(&switch_module(
        "manifest_switch_non_integer_case",
        Ty::I32,
        vec![SwitchCase {
            value: Constant::Float(1.0),
            target: b(2),
            args: vec![],
        }],
    ))
    .expect_err("non-integer switch case constants must fail closed");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "non-integer switch case value",
    );
}

fn check_switch_block_arg_mismatch_fail_closed() {
    let module = module_with_blocks(
        "manifest_switch_block_arg_mismatch",
        vec![Ty::I32],
        vec![],
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I32)],
                body: vec![InstrNode::new(Inst::Switch {
                    value: v(0),
                    default: b(1),
                    default_args: vec![],
                    cases: vec![SwitchCase {
                        value: Constant::Int(1),
                        target: b(2),
                        args: vec![],
                    }],
                    exhaustive_enum_unreachable: false,
                })],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![(v(10), Ty::I64)],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
        ],
    );
    let err = translate_single(&module).expect_err("switch block-arg mismatch must fail closed");
    assert!(
        matches!(err, AdapterError::BlockArgArityMismatch(block, 0, 1) if block == 1),
        "expected switch block-arg arity mismatch, got {err:?}"
    );
}

fn direct_call_module(
    name: &str,
    caller_arg_tys: Vec<Ty>,
    callee_params: Vec<Ty>,
    callee_returns: Vec<Ty>,
    call_args: Vec<ValueId>,
    call_results: Vec<(ValueId, Ty)>,
    return_values: Vec<ValueId>,
) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let caller_ty = module.add_func_type(FuncTy {
        params: caller_arg_tys.clone(),
        returns: return_values
            .iter()
            .filter_map(|value| {
                call_results
                    .iter()
                    .find(|(result, _)| result == value)
                    .map(|(_, ty)| ty.clone())
            })
            .collect(),
        is_vararg: false,
    });
    let callee_ty = module.add_func_type(FuncTy {
        params: callee_params,
        returns: callee_returns,
        is_vararg: false,
    });

    let mut caller = TrustIrFunction::new(f(0), name, caller_ty, b(0));
    caller.blocks = vec![TrustIrBlock {
        id: b(0),
        params: caller_arg_tys
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (v(index as u32), ty))
            .collect(),
        body: vec![
            InstrNode::new(Inst::Call {
                callee: f(1),
                args: call_args,
            })
            .with_results(
                call_results
                    .iter()
                    .map(|(value, _)| *value)
                    .collect::<Vec<_>>(),
            ),
            InstrNode::new(Inst::Return {
                values: return_values,
            }),
        ],
    }];

    let mut callee = TrustIrFunction::new(f(1), "manifest_callee", callee_ty, b(1));
    callee.blocks = vec![TrustIrBlock {
        id: b(1),
        params: vec![(v(10), Ty::I64)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![v(10)],
        })],
    }];

    module.add_function(caller);
    module.add_function(callee);
    module
}

fn check_call_signature_supported() {
    let module = direct_call_module(
        "manifest_call_supported",
        vec![Ty::I64],
        vec![Ty::I64],
        vec![Ty::I64],
        vec![v(0)],
        vec![(v(1), Ty::I64)],
        vec![v(1)],
    );
    expect_supported(&module, "Inst::Call");
    translate_module(&module).expect("registered direct-call module must be type-valid end to end");
}

fn return_module(
    name: &str,
    signature_returns: Vec<Ty>,
    returned: Vec<(ValueId, Ty)>,
) -> TrustIrModule {
    let params = returned.iter().map(|(_, ty)| ty.clone()).collect();
    module_with_blocks(
        name,
        params,
        signature_returns,
        vec![TrustIrBlock {
            id: b(0),
            params: returned,
            body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
        }],
    )
}

fn check_return_signature_supported() {
    expect_supported(
        &return_module(
            "manifest_return_supported",
            vec![Ty::I64],
            vec![(v(0), Ty::I64)],
        ),
        "Inst::Return signature",
    );
}

fn check_return_arity_mismatch_fail_closed() {
    let err = translate_single(&module_with_blocks(
        "manifest_return_arity_mismatch",
        vec![],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }],
    ))
    .expect_err("return arity mismatch must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Inst::Return", "arity mismatch"],
    );
}

fn check_return_type_mismatch_fail_closed() {
    let err = translate_single(&return_module(
        "manifest_return_type_mismatch",
        vec![Ty::I64],
        vec![(v(0), Ty::F64)],
    ))
    .expect_err("return type mismatch must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Inst::Return", "type mismatch", "I64", "F64"],
    );
}

fn check_direct_call_supported_calling_conventions() {
    for convention in [
        CallingConv::C,
        CallingConv::Fast,
        CallingConv::Cold,
        CallingConv::Rust,
        CallingConv::Swift,
    ] {
        let mut module = direct_call_module(
            "manifest_call_supported_convention",
            vec![Ty::I64],
            vec![Ty::I64],
            vec![Ty::I64],
            vec![v(0)],
            vec![(v(1), Ty::I64)],
            vec![v(1)],
        );
        module.functions[0].calling_conv = convention;
        module.functions[1].calling_conv = convention;
        expect_supported(
            &module,
            "direct call using a proven C-register-compatible convention",
        );
    }
}

fn check_call_unregistered_callee_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_call_unregistered_callee",
        vec![(v(0), Ty::I64)],
        vec![Ty::I64],
        InstrNode::new(Inst::Call {
            callee: f(99),
            args: vec![v(0)],
        })
        .with_result(v(1)),
        vec![v(1)],
    ))
    .expect_err("Call must fail closed for unregistered callees");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Call", "unregistered FuncId(99)"],
    );
}

fn check_call_arg_arity_mismatch_fail_closed() {
    let err = translate_single(&direct_call_module(
        "manifest_call_arg_arity_mismatch",
        vec![Ty::I64],
        vec![Ty::I64, Ty::I64],
        vec![Ty::I64],
        vec![v(0)],
        vec![(v(1), Ty::I64)],
        vec![v(1)],
    ))
    .expect_err("Call must fail closed for argument arity mismatches");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Call", "argument arity mismatch", "got 1, expected 2"],
    );
}

fn check_call_arg_type_mismatch_fail_closed() {
    let err = translate_single(&direct_call_module(
        "manifest_call_arg_type_mismatch",
        vec![Ty::I32],
        vec![Ty::I64],
        vec![Ty::I64],
        vec![v(0)],
        vec![(v(1), Ty::I64)],
        vec![v(1)],
    ))
    .expect_err("Call must fail closed for argument type mismatches");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Call", "argument 0 type mismatch"],
    );
}

fn check_call_result_arity_mismatch_fail_closed() {
    let err = translate_single(&direct_call_module(
        "manifest_call_result_arity_mismatch",
        vec![Ty::I64],
        vec![Ty::I64],
        vec![Ty::I64, Ty::I64],
        vec![v(0)],
        vec![(v(1), Ty::I64)],
        vec![v(1)],
    ))
    .expect_err("Call must fail closed for result arity mismatches");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Call", "result arity mismatch", "got 1, expected 2"],
    );
}

fn call_indirect_module(
    name: &str,
    callee_ty: Ty,
    arg_ty: Ty,
    sig_params: Vec<Ty>,
    sig_returns: Vec<Ty>,
    inst_returns: Vec<Ty>,
    return_values: Vec<ValueId>,
) -> TrustIrModule {
    let mut module = single_inst_module(
        name,
        vec![(v(0), callee_ty), (v(1), arg_ty)],
        inst_returns,
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(1),
            args: vec![v(1)],
            calling_conv: CallingConv::C,
        })
        .with_result(v(2)),
        return_values,
    );
    let sig = module.add_func_type(FuncTy {
        params: sig_params,
        returns: sig_returns,
        is_vararg: false,
    });
    assert_eq!(sig, FuncTyId::new(1));
    module
}

fn call_indirect_vararg_module() -> TrustIrModule {
    let mut module = single_inst_module(
        "manifest_call_indirect_vararg",
        vec![(v(0), Ty::Func(FuncTyId::new(1))), (v(1), Ty::I64)],
        vec![Ty::I64],
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(1),
            args: vec![v(1)],
            calling_conv: CallingConv::C,
        })
        .with_result(v(2)),
        vec![v(2)],
    );
    let sig = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: true,
    });
    assert_eq!(sig, FuncTyId::new(1));
    module
}

fn check_call_indirect_signature_supported() {
    for convention in [
        CallingConv::C,
        CallingConv::Fast,
        CallingConv::Cold,
        CallingConv::Rust,
        CallingConv::Swift,
    ] {
        let mut module = call_indirect_module(
            "manifest_call_indirect_supported",
            Ty::Func(FuncTyId::new(1)),
            Ty::I64,
            vec![Ty::I64],
            vec![Ty::I64],
            vec![Ty::I64],
            vec![v(2)],
        );
        let Inst::CallIndirect { calling_conv, .. } =
            &mut module.functions[0].blocks[0].body[0].inst
        else {
            panic!("indirect-call fixture must contain Inst::CallIndirect");
        };
        *calling_conv = convention;
        expect_supported(
            &module,
            "indirect call using a proven C-register-compatible convention",
        );
    }
}

fn check_call_indirect_unregistered_sig_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_call_indirect_bad_sig",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![Ty::I64],
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(99),
            args: vec![v(1)],
            calling_conv: CallingConv::C,
        })
        .with_result(v(2)),
        vec![v(2)],
    ))
    .expect_err("CallIndirect must fail closed for unregistered function signatures");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["CallIndirect", "unregistered FuncTyId"],
    );
}

fn check_call_indirect_non_pointer_callee_fail_closed() {
    // A `Ty::Ptr` callee is intentionally ACCEPTED (it carries &dyn-dispatch /
    // FnPtr code pointers). A pointer-width integer callee (`Ty::I64` / `Ty::U64`)
    // is ALSO accepted: a function address loaded out of a vtable / fn-pointer
    // table slot is materialized as a pointer-width integer, and a Func, a Ptr,
    // and a 64-bit integer callee all lower to byte-identical machine code (the
    // call ABI is constrained by the explicit `sig`, not the callee carrier
    // type). See `validate_call_indirect_signature` in the adapter. So the real
    // non-pointer case that must fail closed is a *sub*-pointer-width integer
    // (`Ty::I32`), which cannot hold a full 64-bit code address.
    for accepted in [Ty::I64, Ty::U64] {
        let module = call_indirect_module(
            "manifest_call_indirect_intaddr_callee",
            accepted,
            Ty::I64,
            vec![Ty::I64],
            vec![Ty::I64],
            vec![Ty::I64],
            vec![v(2)],
        );
        expect_supported(&module, "Inst::CallIndirect");
    }

    let err = translate_single(&call_indirect_module(
        "manifest_call_indirect_non_pointer_callee",
        Ty::I32,
        Ty::I64,
        vec![Ty::I64],
        vec![Ty::I64],
        vec![Ty::I64],
        vec![v(2)],
    ))
    .expect_err("CallIndirect must fail closed for sub-pointer-width integer callees");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["CallIndirect", "callee", "code pointer", "I32"],
    );
}

fn check_call_indirect_arg_type_mismatch_fail_closed() {
    let err = translate_single(&call_indirect_module(
        "manifest_call_indirect_arg_mismatch",
        Ty::Func(FuncTyId::new(1)),
        Ty::I32,
        vec![Ty::I64],
        vec![Ty::I64],
        vec![Ty::I64],
        vec![v(2)],
    ))
    .expect_err("CallIndirect must fail closed when argument types do not match signature");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["CallIndirect", "argument 0 type mismatch"],
    );
}

fn check_call_indirect_result_arity_mismatch_fail_closed() {
    let err = translate_single(&call_indirect_module(
        "manifest_call_indirect_result_arity_mismatch",
        Ty::Func(FuncTyId::new(1)),
        Ty::I64,
        vec![Ty::I64],
        vec![Ty::I64, Ty::I64],
        vec![Ty::I64],
        vec![v(2)],
    ))
    .expect_err("CallIndirect must fail closed when result arity does not match signature");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["CallIndirect", "result arity mismatch"],
    );
}

fn check_call_indirect_vararg_fail_closed() {
    let err = translate_single(&call_indirect_vararg_module())
        .expect_err("CallIndirect must fail closed for variadic signatures");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["CallIndirect", "variadic", "ABI"],
    );
}

fn check_call_indirect_swift_aggregate_signature_fail_closed() {
    // NOTE: the SCALAR subset of Swift -- INCLUDING i128/u128 -- is now SUPPORTED
    // (it lowers identically to the C register ABI; see
    // adapter::swift_signature_is_c_abi_equivalent and
    // tests/e2e_aarch64_swift_scalar.rs). The remaining GENUINE divergence is an
    // AGGREGATE signature (Swift direct-returns a >16-byte value in x0-x3 vs C
    // sret), so this uses a `[i64; 4]` (32-byte) signature, which must still fail
    // closed rather than silently lower with the C ABI.
    let agg = Ty::Array(TyId::new(0), 4);
    let mut module = single_inst_module(
        "manifest_call_indirect_non_c",
        vec![(v(0), Ty::Func(FuncTyId::new(1))), (v(1), agg.clone())],
        vec![agg.clone()],
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(1),
            args: vec![v(1)],
            calling_conv: CallingConv::Swift,
        })
        .with_result(v(2)),
        vec![v(2)],
    );
    module.types.push(Ty::I64); // element type for TyId(0)
    let sig = module.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![agg],
        is_vararg: false,
    });
    assert_eq!(sig, FuncTyId::new(1));
    let err = translate_single(&module)
        .expect_err("Swift aggregate indirect-call signatures must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "CallIndirect",
            "unsupported calling convention",
            "Swift",
            "aggregate",
        ],
    );
}

fn check_borrow_insts_fail_closed() {
    let borrow = single_inst_module(
        "manifest_borrow",
        vec![(v(0), Ty::Ptr)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
        vec![v(1)],
    );
    let err = translate_single(&borrow)
        .expect_err("Borrow must fail closed until provenance semantics are modeled");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Borrow", "not lowered", "provenance"],
    );

    let borrow_mut = single_inst_module(
        "manifest_borrow_mut",
        vec![(v(0), Ty::Ptr)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)),
        vec![v(1)],
    );
    let err = translate_single(&borrow_mut)
        .expect_err("BorrowMut must fail closed until unique borrow semantics are modeled");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["BorrowMut", "not lowered", "unique-borrow"],
    );

    let end_borrow = single_inst_module(
        "manifest_end_borrow",
        vec![(v(0), Ty::Ptr)],
        vec![],
        InstrNode::new(Inst::EndBorrow { borrow_ptr: v(0) }),
        vec![],
    );
    let err = translate_single(&end_borrow)
        .expect_err("EndBorrow must fail closed until borrow-scope semantics are modeled");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["EndBorrow", "not lowered", "borrow scope"],
    );
}

/// ARC ops in a module that declares NO RC runtime must fail closed: the
/// lowering routes by the module-declared Clean RC-runtime import triple
/// (see [`clean_rc_triple_module`]); with no triple there is no sound call
/// target — routing refcount ops to a guessed runtime would corrupt its
/// refcount discipline.
fn expect_arc_fail_closed(surface: &str, inst: InstrNode, returns: Vec<Ty>, values: Vec<ValueId>) {
    let err = translate_single(&single_inst_module(
        "manifest_arc",
        vec![(v(0), Ty::Ptr)],
        returns,
        inst,
        values,
    ))
    .unwrap_err_or_else(surface);
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "declares no RC runtime",
    );
}

fn check_retain_fail_closed() {
    expect_arc_fail_closed(
        "Inst::Retain",
        InstrNode::new(Inst::Retain { ptr: v(0) }),
        vec![],
        vec![],
    );
}

fn check_release_fail_closed() {
    expect_arc_fail_closed(
        "Inst::Release",
        InstrNode::new(Inst::Release { ptr: v(0) }),
        vec![],
        vec![],
    );
}

fn check_is_unique_fail_closed() {
    expect_arc_fail_closed(
        "Inst::IsUnique",
        InstrNode::new(Inst::IsUnique { ptr: v(0) }).with_result(v(1)),
        vec![Ty::Bool],
        vec![v(1)],
    );
}

/// A module declaring the Clean RC-runtime import triple (bodyless externals
/// with the contract signatures: `clean_inc(ptr)`, `clean_dec(ptr)`,
/// `clean_is_exclusive(ptr) -> u8`) plus one body function holding `inst` —
/// the shape a Clean-produced (P1 native ARC) module hands to trust-cg.
fn clean_rc_triple_module(
    name: &str,
    returns: Vec<Ty>,
    inst: InstrNode,
    return_values: Vec<ValueId>,
) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let rc_void = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    let rc_flag = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::U8],
        is_vararg: false,
    });
    module.add_function(TrustIrFunction::new(f(0), "clean_inc", rc_void, b(0)));
    module.add_function(TrustIrFunction::new(f(1), "clean_dec", rc_void, b(0)));
    module.add_function(TrustIrFunction::new(
        f(2),
        "clean_is_exclusive",
        rc_flag,
        b(0),
    ));
    let body_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns,
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(f(3), name, body_ty, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr)],
        body: vec![
            inst,
            InstrNode::new(Inst::Return {
                values: return_values,
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// Translate the (single) body function of a module that also carries
/// bodyless external declarations.
fn translate_body_function(
    module: &TrustIrModule,
) -> Result<trust_cg_lower::function::Function, AdapterError> {
    let func = module
        .functions
        .iter()
        .find(|func| !func.blocks.is_empty())
        .expect("fixture must contain one body function");
    translate_function(func, module).map(|(func, _proofs)| func)
}

/// The lowered instructions of the (single) entry block of a translated body.
fn entry_instructions(func: &trust_cg_lower::function::Function) -> &[Instruction] {
    &func.blocks[&func.entry_block].instructions
}

/// Count entry-block calls to the runtime symbol `name`.
fn count_calls(insns: &[Instruction], name: &str) -> usize {
    insns
        .iter()
        .filter(|inst| matches!(&inst.opcode, Opcode::Call { name: n } if n == name))
        .count()
}

/// The three Clean RC-runtime symbols, keyed for routing-exclusivity checks.
const RC_TRIPLE: [&str; 3] = ["clean_inc", "clean_dec", "clean_is_exclusive"];

/// Full-shape checked property for a *void* ARC op (`Retain`/`Release`): the
/// body must lower to EXACTLY ONE call of `symbol`, that call takes exactly one
/// argument (the mapped pointer operand — arity 1) and produces NO result (a
/// void runtime call), and the OTHER two RC-triple symbols are never called
/// (routing/polarity: a `Retain` reaches `clean_inc`, never `clean_dec` /
/// `clean_is_exclusive`). This is strictly stronger than "a call with the right
/// name exists somewhere": it pins arity, void-ness, single-call count, and
/// exclusive routing as a differential contract over the emitted shape.
fn assert_arc_void_call(func: &trust_cg_lower::function::Function, op: &str, symbol: &str) {
    let insns = entry_instructions(func);
    let calls: Vec<&Instruction> = insns
        .iter()
        .filter(|inst| matches!(&inst.opcode, Opcode::Call { name } if name == symbol))
        .collect();
    assert_eq!(
        calls.len(),
        1,
        "{op} must lower to EXACTLY ONE {symbol} call, got {insns:?}"
    );
    let call = calls[0];
    assert_eq!(
        call.args.len(),
        1,
        "{op}->{symbol} must be a single-pointer-arg call (arity 1, the mapped ptr operand), got {call:?}"
    );
    assert!(
        call.results.is_empty(),
        "{op}->{symbol} is a VOID runtime call (produces no result), got {call:?}"
    );
    for forbidden in RC_TRIPLE.iter().filter(|s| **s != symbol) {
        assert_eq!(
            count_calls(insns, forbidden),
            0,
            "{op} must route ONLY to {symbol}, never {forbidden}, got {insns:?}"
        );
    }
}

fn check_retain_lowered_via_clean_rc_triple() {
    let func = translate_body_function(&clean_rc_triple_module(
        "manifest_arc_retain_clean",
        vec![],
        InstrNode::new(Inst::Retain { ptr: v(0) }),
        vec![],
    ))
    .expect("Retain must lower in a module declaring the Clean RC triple");
    assert_arc_void_call(&func, "Retain", "clean_inc");
}

fn check_release_lowered_via_clean_rc_triple() {
    let func = translate_body_function(&clean_rc_triple_module(
        "manifest_arc_release_clean",
        vec![],
        InstrNode::new(Inst::Release { ptr: v(0) }),
        vec![],
    ))
    .expect("Release must lower in a module declaring the Clean RC triple");
    assert_arc_void_call(&func, "Release", "clean_dec");
}

fn check_is_unique_lowered_via_clean_rc_triple() {
    // POLARITY + DATA-FLOW PIN: `IsUnique` (refcount == 1) and `clean_is_exclusive`
    // answer the SAME predicate, so the lowering calls clean_is_exclusive with NO
    // negation (Clean's frontend expresses `IsShared` as `!IsUnique` itself — a
    // silent flip here would invert every Perceus reuse decision). The C `bool`
    // return is normalized to a canonical 0/1 via an explicit `!= 0`. This pins
    // the WHOLE dataflow chain as a checked property — call result -> `!= 0` ->
    // returned Bool — not merely "a NotEqual exists somewhere after the call":
    //   %raw  = call clean_is_exclusive(%ptr)   (arity 1, one i8 result)
    //   %zero = iconst.i8 0
    //   %dst  = icmp ne %raw, %zero              (EXACT operands, in order)
    //   return %dst
    // plus the negative pins: no `== 0` (polarity flip) and no clean_inc/clean_dec.
    let func = translate_body_function(&clean_rc_triple_module(
        "manifest_arc_is_unique_clean",
        vec![Ty::Bool],
        InstrNode::new(Inst::IsUnique { ptr: v(0) }).with_result(v(1)),
        vec![v(1)],
    ))
    .expect("IsUnique must lower in a module declaring the Clean RC triple");
    let insns = entry_instructions(&func);

    // Exactly one clean_is_exclusive call: arity 1, exactly one (i8) result.
    let calls: Vec<&Instruction> = insns
        .iter()
        .filter(
            |inst| matches!(&inst.opcode, Opcode::Call { name } if name == "clean_is_exclusive"),
        )
        .collect();
    assert_eq!(
        calls.len(),
        1,
        "IsUnique must lower to EXACTLY ONE clean_is_exclusive call (same polarity), got {insns:?}"
    );
    let call = calls[0];
    assert_eq!(
        call.args.len(),
        1,
        "IsUnique->clean_is_exclusive must be a single-pointer-arg call (arity 1), got {call:?}"
    );
    assert_eq!(
        call.results.len(),
        1,
        "IsUnique->clean_is_exclusive yields exactly the raw C-bool byte, got {call:?}"
    );
    let raw = call.results[0];

    // The `!= 0` normalization compares the call result against an i8 zero.
    let zero = insns
        .iter()
        .find(|inst| {
            matches!(
                &inst.opcode,
                Opcode::Iconst {
                    ty: Type::I8,
                    imm: 0
                }
            )
        })
        .and_then(|inst| inst.results.first().copied())
        .unwrap_or_else(|| panic!("IsUnique must normalize via an i8 `0` constant, got {insns:?}"));
    let icmp = insns
        .iter()
        .find(|inst| {
            matches!(
                &inst.opcode,
                Opcode::Icmp {
                    cond: IntCC::NotEqual
                }
            )
        })
        .unwrap_or_else(|| panic!("IsUnique must normalize the C bool via `!= 0`, got {insns:?}"));
    assert_eq!(
        icmp.args,
        vec![raw, zero],
        "IsUnique must normalize as `clean_is_exclusive(p) != 0` over EXACTLY the call \
         result and the i8 zero, in order (no polarity flip), got {icmp:?}"
    );
    let dst = icmp.results[0];

    // The normalized Bool is what the body returns (the result flows through).
    let ret = insns
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Return))
        .unwrap_or_else(|| panic!("IsUnique body must return, got {insns:?}"));
    assert!(
        ret.args.contains(&dst),
        "IsUnique's normalized `!= 0` Bool must be the returned value, got return {ret:?}, dst {dst:?}"
    );

    // Negative pins: an `== 0` would invert the polarity, and touching
    // clean_inc/clean_dec would be a routing bug.
    assert!(
        !insns
            .iter()
            .any(|inst| matches!(&inst.opcode, Opcode::Icmp { cond: IntCC::Equal })),
        "IsUnique must not emit an `== 0` (that inverts the Perceus polarity), got {insns:?}"
    );
    assert_eq!(
        count_calls(insns, "clean_inc"),
        0,
        "IsUnique must not retain"
    );
    assert_eq!(
        count_calls(insns, "clean_dec"),
        0,
        "IsUnique must not release"
    );
}

fn check_arc_partial_rc_triple_fail_closed() {
    // The triple is all-or-nothing: drop `clean_is_exclusive` and every ARC op
    // must keep failing closed (a partial match is not an RC runtime).
    let mut module = clean_rc_triple_module(
        "manifest_arc_partial_triple",
        vec![],
        InstrNode::new(Inst::Retain { ptr: v(0) }),
        vec![],
    );
    module
        .functions
        .retain(|func| func.name != "clean_is_exclusive");
    let err = translate_body_function(&module)
        .expect_err("a partial RC-runtime triple must not claim the ARC contract");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "declares no RC runtime",
    );
}

fn check_dealloc_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_dealloc",
        vec![(v(0), Ty::Ptr)],
        vec![],
        InstrNode::new(Inst::Dealloc { ptr: v(0) }),
        vec![],
    ))
    .expect_err(
        "Inst::Dealloc must fail closed until allocator identity and layout semantics are wired",
    );
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "allocator identity",
    );
}

fn manifest_frame_def() -> BindingFrameDef {
    BindingFrameDef::new(
        BindingFrameId::new(0),
        "manifest_frame",
        vec![BindingSlot::new("slot", Ty::I64)],
    )
}

fn expect_binding_frame_fail_closed(
    surface: &str,
    params: Vec<(ValueId, Ty)>,
    returns: Vec<Ty>,
    inst: InstrNode,
    values: Vec<ValueId>,
) {
    let err = translate_single(&single_inst_module(
        "manifest_binding_frame",
        params,
        returns,
        inst,
        values,
    ))
    .unwrap_err_or_else(surface);
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "binding-frame storage ops",
    );
}

fn check_open_frame_fail_closed() {
    expect_binding_frame_fail_closed(
        "Inst::OpenFrame",
        vec![],
        vec![Ty::Ptr],
        InstrNode::new(Inst::OpenFrame {
            def: manifest_frame_def(),
        })
        .with_result(v(0)),
        vec![v(0)],
    );
}

fn check_bind_slot_fail_closed() {
    expect_binding_frame_fail_closed(
        "Inst::BindSlot",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::BindSlot {
            frame: v(0),
            slot: 0,
            value: v(1),
        })
        .with_result(v(2)),
        vec![v(2)],
    );
}

fn check_load_slot_fail_closed() {
    expect_binding_frame_fail_closed(
        "Inst::LoadSlot",
        vec![(v(0), Ty::Ptr)],
        vec![Ty::I64],
        InstrNode::new(Inst::LoadSlot {
            frame: v(0),
            slot: 0,
            ty: Ty::I64,
        })
        .with_result(v(1)),
        vec![v(1)],
    );
}

fn check_close_frame_supported() {
    let func = expect_supported(
        &single_inst_module(
            "manifest_close_frame",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::CloseFrame { frame: v(0) }),
            vec![],
        ),
        "Inst::CloseFrame",
    );
    assert!(
        func.blocks[&func.entry_block]
            .instructions
            .iter()
            .all(|inst| matches!(inst.opcode, Opcode::Return)),
        "CloseFrame is a lifetime marker and must not emit runtime instructions beyond the terminator"
    );
}

fn check_close_frame_non_pointer_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_close_frame_non_pointer",
        vec![(v(0), Ty::I64)],
        vec![],
        InstrNode::new(Inst::CloseFrame { frame: v(0) }),
        vec![],
    ))
    .expect_err("CloseFrame with a non-pointer frame handle must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["CloseFrame", "pointer-like type"],
    );
}

trait ExpectErrOrElse<T> {
    fn unwrap_err_or_else(self, surface: &str) -> AdapterError;
}

impl<T> ExpectErrOrElse<T> for Result<T, AdapterError> {
    fn unwrap_err_or_else(self, surface: &str) -> AdapterError {
        match self {
            Ok(_) => panic!("{surface} must fail closed"),
            Err(err) => err,
        }
    }
}

fn check_assert_supported() {
    let module = module_with_blocks(
        "manifest_assert",
        vec![Ty::Bool],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Bool)],
            body: vec![
                InstrNode::new(Inst::Assert { cond: v(0) }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );
    expect_supported(&module, "Inst::Assert");
}

fn check_undef_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_undef",
        vec![],
        vec![Ty::I64],
        InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(0)),
        vec![v(0)],
    ))
    .expect_err("Inst::Undef must fail closed until poison/undef semantics are modeled");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Inst::Undef", "poison/undef", "NoUndef"],
    );
}

fn check_unknown_dialect_fail_closed() {
    let module = module_with_blocks(
        "manifest_unknown_dialect",
        vec![],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    DialectInst::new("manifest_unknown", "opaque").with_result_ty(Ty::I64),
                )))
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    let err = translate_single(&module)
        .expect_err("unknown dialect ops must fail closed before native lowering");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "DialectOp reached",
    );
}

fn check_set_type_fail_closed() {
    let element = TyId::new(0);
    let err = translate_type(&Ty::Set(element, SetRepr::Boxed))
        .expect_err("Set type must fail closed until a CPU layout ABI exists");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_sequence_type_fail_closed() {
    let err = translate_type(&Ty::Sequence(TyId::new(0)))
        .expect_err("Sequence type must fail closed until a CPU layout ABI exists");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_record_type_fail_closed() {
    let err = translate_type(&Ty::Record(RecordId::new(0)))
        .expect_err("Record type must fail closed until a CPU layout ABI exists");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_closure_type_fail_closed() {
    let err = translate_type(&Ty::Closure(ClosureTyId::new(0)))
        .expect_err("Closure type must fail closed until a CPU layout ABI exists");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_v25_scalar_types_supported() {
    // B1 pointer-width / char scalars now lower: isize/usize are 64-bit
    // (target pointer width), char is a 32-bit Unicode scalar. Verified
    // end-to-end (const/add/id/overflow/saturating-cast) against native.
    assert_eq!(
        translate_type(&Ty::Isize).expect("isize lowers to I64"),
        Type::I64,
        "isize must lower to the 64-bit pointer-width carrier",
    );
    assert_eq!(
        translate_type(&Ty::Usize).expect("usize lowers to I64"),
        Type::I64,
        "usize must lower to the 64-bit pointer-width carrier",
    );
    assert_eq!(
        translate_type(&Ty::Char).expect("char lowers to I32"),
        Type::I32,
        "char must lower to the 32-bit Unicode-scalar carrier",
    );

    // `usize` spans the full unsigned pointer-width range. Values above
    // i64::MAX must retain their raw 64-bit pattern instead of failing the
    // signed-immediate conversion path.
    expect_supported(
        &const_module(
            "manifest_usize_high_bit",
            Ty::Usize,
            Constant::Int((i64::MAX as i128) + 1),
        ),
        "usize constant with bit 63 set",
    );
    expect_supported(
        &const_module(
            "manifest_usize_max",
            Ty::Usize,
            Constant::Int(u64::MAX as i128),
        ),
        "usize::MAX constant",
    );

    let err = translate_single(&const_module(
        "manifest_isize_positive_overflow",
        Ty::Isize,
        Constant::Int((i64::MAX as i128) + 1),
    ))
    .expect_err("an isize constant above i64::MAX must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["does not fit", "Isize"],
    );

    expect_supported(
        &const_module("manifest_char_max", Ty::Char, Constant::Int(0x10FFFF)),
        "maximum Unicode scalar Char constant",
    );
    for (name, value, detail) in [
        ("manifest_char_surrogate", 0xD800, "Unicode scalar"),
        ("manifest_char_out_of_range", 0x11_0000, "does not fit"),
    ] {
        let err = translate_single(&const_module(name, Ty::Char, Constant::Int(value)))
            .expect_err("a non-scalar Char constant must fail closed");
        expect_fail_closed_all(
            err,
            DiagnosticClass::UnsupportedInstruction,
            &[detail, "Char"],
        );
    }
}

fn check_char_arithmetic_supported() {
    expect_supported(
        &binop_module("manifest_char_add", BinOp::Add, Ty::Char),
        "Char 32-bit arithmetic carrier",
    );
    expect_supported(
        &binop_module_typed(
            "manifest_char_u32_add",
            BinOp::Add,
            Ty::Char,
            Ty::Char,
            Ty::U32,
        ),
        "Char/U32 same-width arithmetic carriers",
    );

    let switch = switch_module(
        "manifest_char_switch",
        Ty::Char,
        vec![SwitchCase {
            value: Constant::Int(0x10FFFF),
            target: b(2),
            args: vec![],
        }],
    );
    let lowered = expect_supported(&switch, "Char switch selector");
    let entry = &lowered.blocks[&lowered.entry_block];
    let Opcode::Switch { cases, .. } = &entry.instructions[0].opcode else {
        panic!("Char switch must lower to Opcode::Switch")
    };
    assert_eq!(cases[0].0, 0x10FFFF);

    for (name, op, src_ty, dst_ty) in [
        ("manifest_char_zext", CastOp::ZExt, Ty::Char, Ty::U64),
        ("manifest_char_trunc", CastOp::Trunc, Ty::U64, Ty::Char),
        ("manifest_char_to_fp", CastOp::UIToFP, Ty::Char, Ty::F64),
        (
            "manifest_char_u32_bitcast",
            CastOp::Bitcast,
            Ty::Char,
            Ty::U32,
        ),
    ] {
        expect_supported(
            &cast_module_typed(name, op, src_ty, dst_ty),
            "Char numeric cast carrier",
        );
    }

    let overflow = module_with_blocks(
        "manifest_char_add_overflow",
        vec![Ty::Char, Ty::Char],
        vec![Ty::Char, Ty::Bool],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Char), (v(1), Ty::Char)],
            body: vec![
                InstrNode::new(Inst::Overflow {
                    op: OverflowOp::AddOverflow,
                    ty: Ty::Char,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_results(vec![v(2), v(3)]),
                InstrNode::new(Inst::Return {
                    values: vec![v(2), v(3)],
                }),
            ],
        }],
    );
    expect_supported(&overflow, "Char unsigned overflow carrier");
}

fn check_refine_type_supported() {
    let refined = Ty::Refine(TyId::new(0), PredId::new(0));
    let mut module = module_with_blocks(
        "manifest_refine_type",
        vec![refined.clone()],
        vec![refined.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), refined)],
            body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
        }],
    );
    assert_eq!(module.add_type(Ty::I64), TyId::new(0));
    assert_eq!(module.intern_pred(Pred::NonZero), Some(PredId::new(0)));

    let lowered = translate_module(&module)
        .expect("a validated Refine<i64, NonZero> must lower to its base carrier");
    assert_eq!(lowered.len(), 1);
    assert_eq!(lowered[0].0.signature.params, vec![Type::I64]);
    assert_eq!(lowered[0].0.signature.returns, vec![Type::I64]);
}

fn check_refine_operation_operands_fail_closed() {
    let refined = Ty::Refine(TyId::new(0), PredId::new(0));
    let mut module = module_with_blocks(
        "manifest_refine_binop_operand",
        vec![refined.clone(), refined.clone()],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), refined.clone()), (v(1), refined)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );
    assert_eq!(module.add_type(Ty::I64), TyId::new(0));
    assert_eq!(module.intern_pred(Pred::Top), Some(PredId::new(0)));

    let err = translate_single(&module)
        .expect_err("ordinary operations over refined operands are not lowered in v0.1.0");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["BinOp::Add", "operand type mismatch", "Refine"],
    );
}

fn check_error_type_fail_closed() {
    let err = translate_type(&Ty::Error)
        .expect_err("producer-internal Ty::Error must never reach trust-cg lowering");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedType,
        &["Ty::Error", "producer-internal", "fail-closed"],
    );
}

fn check_rc_type_fail_closed() {
    // `Ty::Rc(_)` is NOT a raw pointer: lowering it to a bare I64 carrier would
    // silently drop the reference-count ownership semantics (the retain on clone
    // and the release/drop on the last owner). Until a refcounted Rc ABI is
    // modelled, the adapter fails closed — the sound stance, identical to
    // volatile memory and other unmodelled ownership.
    let err = translate_type(&Ty::Rc(Box::new(Ty::I64)))
        .expect_err("Rc must fail closed instead of lowering as a raw pointer");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedType,
        &["Ty::Rc", "refcount ownership"],
    );
}

fn check_rc_function_boundary_fail_closed() {
    let module = module_with_blocks(
        "manifest_rc_function_boundary",
        vec![Ty::Rc(Box::new(Ty::I64))],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Rc(Box::new(Ty::I64)))],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
    );

    // An `Rc(_)` parameter cannot cross the function boundary as a bare pointer:
    // dropping its refcount ownership at the ABI would miscompile retain/release.
    // The adapter rejects the signature instead of synthesizing an unsound
    // pointer-carrier lowering.
    let err = translate_single(&module).expect_err(
        "Rc function boundary must fail closed instead of using an I64 pointer carrier",
    );
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedType,
        &["Ty::Rc", "refcount ownership"],
    );
}

fn check_sequence_constant_supported() {
    let func = expect_supported(
        &sequence_const_module(
            "manifest_sequence_const",
            vec![Constant::Int(1), Constant::Int(2)],
        ),
        "typed Constant::Sequence",
    );
    assert_eq!(func.stack_slots.len(), 1);
    assert_eq!(func.stack_slots[0].size, 24);
    let entry = &func.blocks[&func.entry_block];
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(
                inst.opcode,
                Opcode::Store {
                    ty: Type::I64,
                    align: None
                }
            ))
            .count(),
        3,
        "Sequence constant must store one i64 length header plus two i64 elements"
    );
}

fn check_set_constant_fail_closed() {
    let err = translate_single(&const_module(
        "manifest_set_const",
        Ty::I64,
        Constant::Set(vec![Constant::Int(1)]),
    ))
    .expect_err("Set constants must fail closed until layout materialization exists");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "aggregate/closure constant",
    );
}

fn check_u128_constant_supported() {
    // v24 U128 carrier (canonical iff value > i128::MAX): materialized via a
    // bit-pattern-preserving reinterpret into the shared integer-const path,
    // which splits it into two physical u64 halves (Iconst128). Verified
    // end-to-end: 2^127, u128::MAX, and i128::MAX all round-trip bit-exactly.
    let above_i128_max = (i128::MAX as u128) + 1; // 2^127
    expect_supported(
        &const_module(
            "manifest_u128_const_hi",
            Ty::U128,
            Constant::U128(above_i128_max),
        ),
        "Constant::U128",
    );
    // The one-spelling rule is part of the wire contract: values that fit
    // i128 must use Constant::Int, even when the destination type is U128.
    let err = translate_single(&const_module(
        "manifest_u128_const_noncanonical",
        Ty::U128,
        Constant::U128(7),
    ))
    .expect_err("non-canonical Constant::U128 must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Constant::U128", "non-canonical"],
    );
    // u128::MAX (all-ones) — the extreme bit pattern.
    expect_supported(
        &const_module(
            "manifest_u128_const_max",
            Ty::U128,
            Constant::U128(u128::MAX),
        ),
        "Constant::U128",
    );
}

fn check_bytes_constant_supported() {
    // v25 Bytes carrier (string/byte-string literals): a `[u8; N]` bytes
    // constant lowers via the proven aggregate stack-materialization path,
    // exactly as the reference interpreter executes it (an Array of U8 ints).
    // Verified end-to-end: a bytes<414243> buffer reads back as 'A','B','C'.
    let array_ty = Ty::Array(TyId::new(0), 3);
    let mut module = module_with_blocks(
        "manifest_bytes_const",
        vec![],
        vec![array_ty.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: array_ty.clone(),
                    value: Constant::Bytes {
                        data: vec![0x54, 0x49, 0x52],
                        utf8: false,
                    },
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    module.types.push(Ty::U8); // element type for TyId(0) = [u8; 3]
    expect_supported(&module, "Constant::Bytes");

    let mut utf8_module = module.clone();
    let Inst::Const { value, .. } = &mut utf8_module.functions[0].blocks[0].body[0].inst else {
        panic!("bytes fixture must begin with a constant")
    };
    *value = Constant::Bytes {
        data: "TIR".as_bytes().to_vec(),
        utf8: true,
    };
    expect_supported(&utf8_module, "valid UTF-8 Constant::Bytes");

    let mut invalid_utf8_module = module.clone();
    let Inst::Const { value, .. } = &mut invalid_utf8_module.functions[0].blocks[0].body[0].inst
    else {
        panic!("bytes fixture must begin with a constant")
    };
    *value = Constant::Bytes {
        data: vec![0xff, 0xfe, 0xfd],
        utf8: true,
    };
    let err = translate_single(&invalid_utf8_module)
        .expect_err("an invalid UTF-8 claim must fail closed before metadata is erased");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Constant::Bytes", "UTF-8"],
    );

    // A non-`[u8; N]` bytes constant is malformed and must still fail closed.
    let err = translate_single(&const_module(
        "manifest_bytes_scalar",
        Ty::U8,
        Constant::Bytes {
            data: vec![0x54, 0x49, 0x52],
            utf8: false,
        },
    ))
    .expect_err("a scalar-typed bytes constant is malformed and must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Constant::Bytes", "[u8; N]"],
    );
}

fn check_symbol_addr_instruction_constant_supported() {
    // A ZERO-addend `SymbolAddr` function-body constant materializes the named
    // symbol's address via a GlobalRef (defined) / ExternRef (external)
    // relocation — the raw-name counterpart of `FnDef`/`GlobalAddr`. Here the
    // target `manifest_target` is not defined in the module, so it lowers to a
    // GOT-indirect `ExternRef` the linker resolves.
    let func = expect_supported(
        &const_module(
            "manifest_symbol_addr_instruction_const",
            Ty::Ptr,
            Constant::SymbolAddr {
                symbol: "manifest_target".to_string(),
                addend: 0,
            },
        ),
        "zero-addend Constant::SymbolAddr function-body constant",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry.instructions.iter().any(|inst| matches!(
            &inst.opcode,
            Opcode::ExternRef { name } | Opcode::GlobalRef { name } if name == "manifest_target"
        )),
        "SymbolAddr must lower to a GlobalRef/ExternRef of the target symbol"
    );

    // A NON-ZERO addend has no relocation-carried form here and still fails
    // closed rather than synthesizing an unverified `base + k` sequence.
    let err = translate_single(&const_module(
        "manifest_symbol_addr_instruction_const_addend",
        Ty::Ptr,
        Constant::SymbolAddr {
            symbol: "manifest_target".to_string(),
            addend: 8,
        },
    ))
    .expect_err("a non-zero-addend SymbolAddr function-body constant must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "Constant::SymbolAddr",
            "manifest_target",
            "addend: 8",
            "non-zero addend",
        ],
    );
}

fn check_record_constant_supported() {
    let func = expect_supported(
        &record_const_module("manifest_record_const"),
        "typed Constant::Record",
    );
    assert_eq!(func.stack_slots.len(), 1);
    assert_eq!(func.stack_slots[0].size, 16);
    let entry = &func.blocks[&func.entry_block];
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::StructGep { .. }))
            .count(),
        2,
        "Record constant must materialize both declared fields"
    );
}

fn check_closure_constant_with_capture_fail_closed() {
    let err = translate_single(&const_module(
        "manifest_closure_const",
        Ty::I64,
        Constant::Closure {
            func: f(0),
            captures: vec![Constant::Int(1)],
        },
    ))
    .expect_err("captured closure constants must fail closed until closure layout exists");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "aggregate/closure constant",
    );
}

fn parser_roundtrip_modules() -> Vec<TrustIrModule> {
    vec![
        const_module("manifest_parser_const", Ty::I64, Constant::Int(7)),
        binop_module("manifest_parser_add", BinOp::Add, Ty::I64),
        single_inst_module(
            "manifest_parser_copy",
            vec![(v(0), Ty::I64)],
            vec![Ty::I64],
            InstrNode::new(Inst::Copy {
                ty: Ty::I64,
                operand: v(0),
            })
            .with_result(v(1)),
            vec![v(1)],
        ),
    ]
}

fn check_text_parser_roundtrips_supported_forms() {
    for module in parser_roundtrip_modules() {
        let text = format!("{module}");
        let parsed = trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|err| panic!("TrustIr parser rejected accepted fixture: {err}"));
        assert_eq!(
            format!("{parsed}"),
            text,
            "TrustIr parser/display must remain a canonical roundtrip"
        );
    }
}

fn module_with_source_span_provenance() -> TrustIrModule {
    module_with_blocks(
        "manifest_binary_source_span",
        vec![],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(11),
                })
                .with_result(v(0))
                .with_span(SourceSpan {
                    file: 1,
                    line: 2,
                    col: 3,
                }),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    )
}

fn check_binary_module_roundtrips_supported_forms() {
    for module in parser_roundtrip_modules()
        .into_iter()
        .chain([module_with_source_span_provenance()])
    {
        let bytes = trust_ir::binary::serialize_module(&module);
        let decoded = trust_ir::binary::deserialize_module(&bytes)
            .unwrap_or_else(|err| panic!("TrustIr binary reader rejected fixture: {err}"));
        assert_eq!(
            format!("{decoded}"),
            format!("{module}"),
            "TrustIr binary module roundtrip must preserve canonical text"
        );
    }
}

fn check_source_span_provenance_roundtrips_through_binary() {
    let module = module_with_source_span_provenance();
    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded = trust_ir::binary::deserialize_module(&bytes)
        .expect("TrustIr binary reader must accept SourceSpan provenance fixture");
    let span = decoded.functions[0].blocks[0].body[0]
        .span
        .expect("SourceSpan provenance must survive binary roundtrip");
    assert_eq!(
        span,
        SourceSpan {
            file: 1,
            line: 2,
            col: 3
        }
    );
}

fn check_proof_lineage_provenance_sidecar_roundtrips() {
    let source = ProofDigest::sha256_domain("trust-cg.manifest.source", b"source");
    let target = ProofDigest::sha256_domain("trust-cg.manifest.target", b"target");
    let replay = ProofReplayIdentity::new("trust-cg-conformance", "trust-ir-provenance-roundtrip")
        .with_transcript_digest(ProofDigest::sha256_domain(
            "trust-cg.manifest.transcript",
            b"ok",
        ));
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::TrustIrLowering,
            "trust-cg-lower-conformance",
            "trust-cg",
            "manifest",
        ),
        source,
        target,
    );
    node.replay = Some(replay);
    node.obligations.push(ProofId::new(0));

    let mut manifest = ProofLineageManifest::new();
    manifest.nodes.push(node);
    manifest.roots.push(ProofLineageId::new(0));
    manifest
        .validate()
        .expect("proof lineage provenance fixture must be valid");

    let bytes = trust_ir::binary::serialize_proof_lineage_manifest(&manifest);
    let decoded = trust_ir::binary::deserialize_proof_lineage_manifest(&bytes)
        .expect("proof lineage provenance sidecar must decode");
    assert_eq!(decoded, manifest);
    assert_eq!(
        trust_ir::binary::serialize_proof_lineage_manifest(&decoded),
        bytes,
        "proof lineage provenance sidecar must be canonical"
    );
}

fn check_unknown_dialect_has_no_target_execution_path() {
    let module = module_with_blocks(
        "manifest_unknown_dialect_target_execution",
        vec![],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    DialectInst::new("manifest_unknown_target", "opaque").with_result_ty(Ty::I64),
                )))
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    let err = translate_single(&module)
        .expect_err("unknown dialect ops must fail closed before target execution");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "DialectOp reached",
    );
}

fn check_logical_aggregates_have_no_target_execution_path() {
    for (name, ty) in [
        (
            "manifest_target_set_bitset",
            Ty::Set(TyId::new(0), SetRepr::Bitset),
        ),
        (
            "manifest_target_set_boxed",
            Ty::Set(TyId::new(0), SetRepr::Boxed),
        ),
        ("manifest_target_sequence", Ty::Sequence(TyId::new(0))),
        ("manifest_target_record", Ty::Record(RecordId::new(0))),
        ("manifest_target_closure", Ty::Closure(ClosureTyId::new(0))),
    ] {
        let module = module_with_blocks(
            name,
            vec![ty.clone()],
            vec![ty.clone()],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), ty)],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
            }],
        );
        let err = translate_single(&module)
            .expect_err("logical aggregate target-execution fixtures must fail closed");
        expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
    }
}

fn check_sequence_constant_has_target_materialization_path() {
    let func = expect_supported(
        &sequence_const_module(
            "manifest_target_sequence_const",
            vec![Constant::Int(1), Constant::Int(2)],
        ),
        "typed Constant::Sequence target materialization",
    );
    assert!(
        func.blocks[&func.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::ArrayGep { elem_ty: Type::I64 })),
        "Sequence constant materialization must compute length/element addresses"
    );
}

fn check_set_constant_has_no_target_execution_path() {
    let err = translate_single(&const_module(
        "manifest_target_set_const",
        Ty::I64,
        Constant::Set(vec![Constant::Int(1), Constant::Int(2)]),
    ))
    .expect_err("Set target materialization must fail closed until layout exists");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "aggregate/closure constant",
    );
}

fn check_record_constant_has_target_materialization_path() {
    let func = expect_supported(
        &record_const_module("manifest_target_record_const"),
        "typed Constant::Record target materialization",
    );
    assert!(
        func.blocks[&func.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { .. })),
        "Record constant materialization must compute declared field addresses"
    );
}

fn check_record_extract_field_has_target_execution_path() {
    let func = expect_supported(
        &record_extract_module("manifest_target_record_extract_field_supported"),
        "typed Record ExtractField target materialization",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { field_index: 1, .. })),
        "Record ExtractField must compute the selected declared field address"
    );
    assert!(
        entry.instructions.iter().any(|inst| matches!(
            inst.opcode,
            Opcode::Load {
                ty: Type::I64,
                align: None
            }
        )),
        "Record ExtractField must load the selected field"
    );
}

fn check_record_insert_field_has_target_execution_path() {
    let func = expect_supported(
        &record_insert_module("manifest_target_record_insert_field_supported"),
        "typed Record InsertField target materialization",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { field_index: 1, .. })),
        "Record InsertField must compute the selected declared field address"
    );
    assert!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(
                inst.opcode,
                Opcode::Store {
                    ty: Type::I64,
                    align: None
                }
            ))
            .count()
            >= 3,
        "Record InsertField fixture must store two constant fields plus the replacement field"
    );
}

fn check_closure_constant_has_no_target_execution_path() {
    let err = translate_single(&const_module(
        "manifest_target_closure_const",
        Ty::I64,
        Constant::Closure {
            func: f(0),
            captures: vec![Constant::Int(1)],
        },
    ))
    .expect_err("Captured closure target materialization must fail closed until layout exists");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "aggregate/closure constant",
    );
}

fn check_record_extract_field_missing_def_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_target_record_extract_field",
        vec![(v(0), Ty::Ptr)],
        vec![Ty::I64],
        InstrNode::new(Inst::ExtractField {
            ty: Ty::Record(RecordId::new(0)),
            aggregate: v(0),
            field: 0,
        })
        .with_result(v(1)),
        vec![v(1)],
    ))
    .expect_err("Record field extraction must fail closed without a record definition");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_record_insert_field_missing_def_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_target_record_insert_field",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::InsertField {
            ty: Ty::Record(RecordId::new(0)),
            aggregate: v(0),
            field: 0,
            value: v(1),
        })
        .with_result(v(2)),
        vec![v(2)],
    ))
    .expect_err("Record field insertion must fail closed without a record definition");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_sequence_insert_element_has_no_target_execution_path() {
    let err = translate_single(&single_inst_module(
        "manifest_target_sequence_insert_element_unknown_source",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::InsertElement {
            ty: Ty::Sequence(TyId::new(0)),
            array: v(0),
            index: v(1),
            value: v(2),
        })
        .with_result(v(3)),
        vec![v(3)],
    ))
    .expect_err("Sequence insertion with an unknown pointer source layout must fail closed");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "InsertElement requires array or vector source type",
    );
}

fn check_sequence_extract_element_without_layout_provenance_fail_closed() {
    let elem_tyid = TyId::new(0);
    let mut module = module_with_blocks(
        "manifest_target_sequence_extract_without_layout",
        vec![Ty::Ptr],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Copy {
                    ty: Ty::Sequence(elem_tyid),
                    operand: v(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::I64,
                    array: v(1),
                    index: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    );
    module.types.push(Ty::I64);

    let err = translate_single(&module)
        .expect_err("Sequence extraction without materialized layout provenance must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Ty::Sequence", "no materialized", "layout provenance"],
    );
}

fn check_sequence_extract_element_supported_for_materialized_sequence() {
    let elem_tyid = TyId::new(0);
    let module = module_with_blocks(
        "manifest_target_sequence_extract_element",
        vec![],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Sequence(elem_tyid),
                    value: Constant::Sequence(vec![Constant::Int(5), Constant::Int(8)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::I64,
                    array: v(0),
                    index: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );
    let mut module = module;
    module.types.push(Ty::I64);

    let func = expect_supported(&module, "materialized Sequence ExtractElement");
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry.instructions.iter().any(|inst| matches!(
            inst.opcode,
            Opcode::Load {
                ty: Type::I64,
                align: None
            }
        )),
        "Sequence ExtractElement must load the selected element"
    );
}

fn check_sequence_insert_element_supported_for_materialized_sequence() {
    let elem_tyid = TyId::new(0);
    let module = module_with_blocks(
        "manifest_target_sequence_insert_element",
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Sequence(elem_tyid),
                    value: Constant::Sequence(vec![Constant::Int(5), Constant::Int(8)]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(13),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::InsertElement {
                    ty: Ty::Sequence(elem_tyid),
                    array: v(0),
                    index: v(1),
                    value: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );
    let mut module = module;
    module.types.push(Ty::I64);

    let func = expect_supported(&module, "materialized Sequence InsertElement");
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .filter(|inst| matches!(
                inst.opcode,
                Opcode::Store {
                    ty: Type::I64,
                    align: None
                }
            ))
            .count()
            >= 4,
        "Sequence InsertElement must store the length, initial elements, and replacement element"
    );
}

fn check_array_insert_element_supported() {
    let array_ty = Ty::Array(TyId::new(0), 2);
    let mut module = single_inst_module(
        "manifest_target_array_insert_element",
        vec![(v(0), array_ty.clone()), (v(1), Ty::I64), (v(2), Ty::I64)],
        vec![array_ty.clone()],
        InstrNode::new(Inst::InsertElement {
            ty: array_ty,
            array: v(0),
            index: v(1),
            value: v(2),
        })
        .with_result(v(3)),
        vec![v(3)],
    );
    module.types.push(Ty::I64);

    let func = expect_supported(&module, "array InsertElement");
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::ArrayGep { elem_ty: Type::I64 })),
        "array InsertElement must compute the selected element address"
    );
    assert!(
        entry.instructions.iter().any(|inst| matches!(
            inst.opcode,
            Opcode::Store {
                ty: Type::I64,
                align: None
            }
        )),
        "array InsertElement must store the replacement value"
    );
}

fn check_insert_element_rejects_non_array_source() {
    let err = translate_single(&single_inst_module(
        "manifest_target_insert_element_non_array_source",
        vec![(v(0), Ty::I64), (v(1), Ty::I64), (v(2), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::InsertElement {
            ty: Ty::Array(TyId::new(0), 2),
            array: v(0),
            index: v(1),
            value: v(2),
        })
        .with_result(v(3)),
        vec![v(3)],
    ))
    .expect_err("InsertElement over a scalar source must not lower as pointer arithmetic");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "InsertElement requires array or vector source type",
    );
}

fn check_insert_element_rejects_array_source_result_mismatch() {
    let source_ty = Ty::Array(TyId::new(0), 2);
    let result_ty = Ty::Array(TyId::new(0), 3);
    let mut module = single_inst_module(
        "manifest_target_insert_element_source_result_mismatch",
        vec![(v(0), source_ty), (v(1), Ty::I64), (v(2), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::InsertElement {
            ty: result_ty,
            array: v(0),
            index: v(1),
            value: v(2),
        })
        .with_result(v(3)),
        vec![v(3)],
    );
    module.types.push(Ty::I64);

    let err = translate_single(&module)
        .expect_err("InsertElement must reject declared result/source aggregate mismatches");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "does not match source aggregate type",
    );
}

fn check_insert_element_rejects_array_value_type_mismatch() {
    let array_ty = Ty::Array(TyId::new(0), 2);
    let mut module = single_inst_module(
        "manifest_target_insert_element_value_type_mismatch",
        vec![(v(0), array_ty.clone()), (v(1), Ty::I64), (v(2), Ty::I32)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::InsertElement {
            ty: array_ty,
            array: v(0),
            index: v(1),
            value: v(2),
        })
        .with_result(v(3)),
        vec![v(3)],
    );
    module.types.push(Ty::I64);

    let err =
        translate_single(&module).expect_err("InsertElement must reject element value mismatch");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "does not match array element type",
    );
}

fn check_extract_element_rejects_non_array_source() {
    let err = translate_single(&single_inst_module(
        "manifest_target_extract_element_non_array_source",
        vec![(v(0), Ty::I64), (v(1), Ty::I64)],
        vec![Ty::I64],
        InstrNode::new(Inst::ExtractElement {
            ty: Ty::I64,
            array: v(0),
            index: v(1),
        })
        .with_result(v(2)),
        vec![v(2)],
    ))
    .expect_err("ExtractElement over a scalar source must not lower as pointer arithmetic");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "ExtractElement requires array or vector source type",
    );
}

fn check_extract_element_rejects_array_element_type_mismatch() {
    let array_ty = Ty::Array(TyId::new(0), 2);
    let mut module = single_inst_module(
        "manifest_target_extract_element_type_mismatch",
        vec![(v(0), array_ty), (v(1), Ty::I64)],
        vec![Ty::I32],
        InstrNode::new(Inst::ExtractElement {
            ty: Ty::I32,
            array: v(0),
            index: v(1),
        })
        .with_result(v(2)),
        vec![v(2)],
    );
    module.types.push(Ty::I64);

    let err = translate_single(&module)
        .expect_err("ExtractElement must reject declared type/array element mismatches");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "does not match array element type",
    );
}

fn check_record_multi_index_gep_supported() {
    let record_id = RecordId::new(0);
    let mut module = module_with_blocks(
        "manifest_target_record_multi_index_gep",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::Record(record_id),
                    base: v(0),
                    indices: vec![v(1), v(2)],
                    inbounds: false,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    );
    module.add_record(RecordDef {
        id: record_id,
        name: "ManifestRecord".to_string(),
        fields: vec![
            FieldDef {
                name: "left".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "right".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
    });

    let func = expect_supported(&module, "record multi-index GEP");
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { field_index: 1, .. })),
        "record multi-index GEP must compute the selected record field address"
    );
}

fn check_set_gep_has_no_target_execution_path() {
    let err = translate_single(&single_inst_module(
        "manifest_target_set_gep",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::Set(TyId::new(0), SetRepr::Boxed),
            base: v(0),
            indices: vec![v(1), v(2)],
            inbounds: false,
        })
        .with_result(v(3)),
        vec![v(3)],
    ))
    .expect_err("Set GEP must fail closed until set layout exists");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_sequence_gep_has_no_target_execution_path() {
    let err = translate_single(&single_inst_module(
        "manifest_target_sequence_gep",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::Sequence(TyId::new(0)),
            base: v(0),
            indices: vec![v(1), v(2)],
            inbounds: false,
        })
        .with_result(v(3)),
        vec![v(3)],
    ))
    .expect_err("Sequence GEP must fail closed until sequence layout exists");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_single_index_set_gep_has_no_byte_stride_fallback() {
    let err = translate_single(&single_inst_module(
        "manifest_target_single_index_set_gep",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::Set(TyId::new(0), SetRepr::Boxed),
            base: v(0),
            indices: vec![v(1)],
            inbounds: false,
        })
        .with_result(v(2)),
        vec![v(2)],
    ))
    .expect_err("single-index Set GEP must fail closed until set layout exists");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_single_index_sequence_gep_has_no_byte_stride_fallback() {
    let err = translate_single(&single_inst_module(
        "manifest_target_single_index_sequence_gep",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![Ty::Ptr],
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::Sequence(TyId::new(0)),
            base: v(0),
            indices: vec![v(1)],
            inbounds: false,
        })
        .with_result(v(2)),
        vec![v(2)],
    ))
    .expect_err("single-index Sequence GEP must fail closed until sequence layout exists");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn coverage_rows() -> Vec<CoverageRow> {
    vec![
        CoverageRow {
            category: "binops",
            surface: "scalar BinOp except FRem",
            status: CoverageStatus::Supported,
            check: check_scalar_binops_supported,
        },
        CoverageRow {
            category: "binops",
            surface: "vector BinOp typed V128 Add/Sub/Mul subset",
            status: CoverageStatus::Supported,
            check: check_vector_binops_supported,
        },
        CoverageRow {
            category: "binops",
            surface: "BinOp::FRem f64",
            status: CoverageStatus::Supported,
            check: check_frem_f64_lowers_to_fmod_libcall,
        },
        CoverageRow {
            category: "binops",
            surface: "BinOp::FRem f32",
            status: CoverageStatus::Supported,
            check: check_frem_f32_lowers_to_fmodf_libcall,
        },
        CoverageRow {
            category: "binops",
            surface: "BinOp::FRem f16",
            status: CoverageStatus::Supported,
            check: check_frem_f16_lowers_via_promoted_fmodf,
        },
        CoverageRow {
            category: "binops",
            surface: "integer BinOp declared float",
            status: CoverageStatus::FailClosed,
            check: check_integer_binop_float_declared_fail_closed,
        },
        CoverageRow {
            category: "binops",
            surface: "float BinOp declared integer",
            status: CoverageStatus::FailClosed,
            check: check_float_binop_integer_declared_fail_closed,
        },
        CoverageRow {
            category: "binops",
            surface: "BinOp operand type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_binop_operand_type_mismatch_fail_closed,
        },
        CoverageRow {
            category: "binops",
            surface: "shift BinOp declared float",
            status: CoverageStatus::FailClosed,
            check: check_shift_float_declared_fail_closed,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp scalar integer operands",
            status: CoverageStatus::Supported,
            check: check_icmp_scalar_integer_supported,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp <4 x i32> eq/ne/signed vector operands",
            status: CoverageStatus::Supported,
            check: check_icmp_v4i32_signed_vector_supported,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp <4 x i32> unsigned vector operands",
            status: CoverageStatus::Supported,
            check: check_icmp_v4i32_unsigned_vector_supported,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp <16 x i8>/<8 x i16> unsigned vector operands",
            status: CoverageStatus::Supported,
            check: check_icmp_narrow_unsigned_vector_supported,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp <2 x i64> unsigned vector operands",
            status: CoverageStatus::Supported,
            check: check_icmp_v2i64_unsigned_vector_supported,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp declared non-integer type",
            status: CoverageStatus::FailClosed,
            check: check_icmp_declared_non_integer_fail_closed,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp operand type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_icmp_operand_type_mismatch_fail_closed,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp pointer Eq/Ne operands",
            status: CoverageStatus::Supported,
            check: check_icmp_pointer_eq_ne_supported,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::ICmp pointer relational operands",
            status: CoverageStatus::FailClosed,
            check: check_icmp_pointer_relational_fail_closed,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::FCmp scalar float operands",
            status: CoverageStatus::Supported,
            check: check_fcmp_scalar_float_supported,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::FCmp declared non-float type",
            status: CoverageStatus::FailClosed,
            check: check_fcmp_declared_non_float_fail_closed,
        },
        CoverageRow {
            category: "comparisons",
            surface: "Inst::FCmp operand type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_fcmp_operand_type_mismatch_fail_closed,
        },
        CoverageRow {
            category: "unops",
            surface: "UnOp scalar core",
            status: CoverageStatus::Supported,
            check: check_unops_supported,
        },
        CoverageRow {
            category: "unops",
            surface: "UnOp wrong scalar type",
            status: CoverageStatus::FailClosed,
            check: check_unop_wrong_type_fail_closed,
        },
        CoverageRow {
            category: "atomics",
            surface: "AtomicRMW::Xchg/Add/Sub/And/Or/Xor/Max/Min/UMax/UMin",
            status: CoverageStatus::Supported,
            check: check_atomic_supported_ops,
        },
        CoverageRow {
            category: "atomics",
            surface: "AtomicLoad/AtomicStore legal orderings",
            status: CoverageStatus::Supported,
            check: check_atomic_load_store_supported_orderings,
        },
        CoverageRow {
            category: "atomics",
            surface: "AtomicLoad::Release ordering",
            status: CoverageStatus::FailClosed,
            check: check_atomic_load_release_fail_closed,
        },
        CoverageRow {
            category: "atomics",
            surface: "AtomicLoad::AcqRel ordering",
            status: CoverageStatus::FailClosed,
            check: check_atomic_load_acqrel_fail_closed,
        },
        CoverageRow {
            category: "atomics",
            surface: "AtomicStore::Acquire ordering",
            status: CoverageStatus::FailClosed,
            check: check_atomic_store_acquire_fail_closed,
        },
        CoverageRow {
            category: "atomics",
            surface: "AtomicStore::AcqRel ordering",
            status: CoverageStatus::FailClosed,
            check: check_atomic_store_acqrel_fail_closed,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Load volatile",
            status: CoverageStatus::Supported,
            check: check_volatile_load_supported,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Store volatile",
            status: CoverageStatus::Supported,
            check: check_volatile_store_supported,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Load natural-or-weaker explicit align",
            status: CoverageStatus::Supported,
            check: check_load_natural_explicit_align_supported,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Store natural-or-weaker explicit align",
            status: CoverageStatus::Supported,
            check: check_store_natural_explicit_align_supported,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Load stronger-than-natural explicit align",
            status: CoverageStatus::Supported,
            check: check_load_stronger_explicit_align_supported,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Store stronger-than-natural explicit align",
            status: CoverageStatus::Supported,
            check: check_store_stronger_explicit_align_supported,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Alloca explicit align",
            status: CoverageStatus::Supported,
            check: check_alloca_explicit_align_supported,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Alloca invalid explicit align",
            status: CoverageStatus::FailClosed,
            check: check_alloca_invalid_explicit_align_fail_closed,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp standard scalar/pointer casts",
            status: CoverageStatus::Supported,
            check: check_standard_casts_supported,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp malformed pointer casts",
            status: CoverageStatus::FailClosed,
            check: check_malformed_pointer_casts_fail_closed,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp wrong-direction integer resize",
            status: CoverageStatus::FailClosed,
            check: check_wrong_direction_integer_casts_fail_closed,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp::Transmute equal-size",
            status: CoverageStatus::FailClosed,
            check: check_transmute_equal_size_fail_closed,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp::Transmute size-mismatch",
            status: CoverageStatus::FailClosed,
            check: check_transmute_size_mismatch_fail_closed,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp::ReifyFnPointer materialized function symbol",
            status: CoverageStatus::Supported,
            check: check_reify_fn_pointer_materialized_fndef_supported,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp::ReifyFnPointer without materialized provenance",
            status: CoverageStatus::FailClosed,
            check: check_reify_fn_pointer_without_provenance_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Copy/Unreachable",
            status: CoverageStatus::Supported,
            check: check_control_and_pseudo_insts_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Assume",
            status: CoverageStatus::Supported,
            check: check_assume_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Assume non-Bool condition",
            status: CoverageStatus::FailClosed,
            check: check_assume_non_bool_condition_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Switch integer selector",
            status: CoverageStatus::Supported,
            check: check_switch_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Switch non-integer selector",
            status: CoverageStatus::FailClosed,
            check: check_switch_non_integer_selector_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Switch unsupported selector width",
            status: CoverageStatus::FailClosed,
            check: check_switch_unsupported_selector_width_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Switch duplicate normalized case",
            status: CoverageStatus::FailClosed,
            check: check_switch_duplicate_normalized_case_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Switch non-integer case",
            status: CoverageStatus::FailClosed,
            check: check_switch_non_integer_case_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Switch block-arg mismatch",
            status: CoverageStatus::FailClosed,
            check: check_switch_block_arg_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Call signature-checked",
            status: CoverageStatus::Supported,
            check: check_call_signature_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Return signature-checked",
            status: CoverageStatus::Supported,
            check: check_return_signature_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Return arity mismatch",
            status: CoverageStatus::FailClosed,
            check: check_return_arity_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Return type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_return_type_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Call unregistered callee",
            status: CoverageStatus::FailClosed,
            check: check_call_unregistered_callee_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Call C/Fast/Cold/Rust/scalar-Swift ABI matrix",
            status: CoverageStatus::Supported,
            check: check_direct_call_supported_calling_conventions,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Call argument arity mismatch",
            status: CoverageStatus::FailClosed,
            check: check_call_arg_arity_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Call argument type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_call_arg_type_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Call result arity mismatch",
            status: CoverageStatus::FailClosed,
            check: check_call_result_arity_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect C/Fast/Cold/Rust/scalar-Swift ABI matrix",
            status: CoverageStatus::Supported,
            check: check_call_indirect_signature_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect unregistered signature",
            status: CoverageStatus::FailClosed,
            check: check_call_indirect_unregistered_sig_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect non-pointer callee",
            status: CoverageStatus::FailClosed,
            check: check_call_indirect_non_pointer_callee_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect argument type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_call_indirect_arg_type_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect result arity mismatch",
            status: CoverageStatus::FailClosed,
            check: check_call_indirect_result_arity_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect variadic signature",
            status: CoverageStatus::FailClosed,
            check: check_call_indirect_vararg_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect Swift aggregate signature",
            status: CoverageStatus::FailClosed,
            check: check_call_indirect_swift_aggregate_signature_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Borrow/BorrowMut/EndBorrow",
            status: CoverageStatus::FailClosed,
            check: check_borrow_insts_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Select scalar Bool condition",
            status: CoverageStatus::Supported,
            check: check_select_scalar_bool_condition_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Select scalar non-Bool condition",
            status: CoverageStatus::FailClosed,
            check: check_select_scalar_non_bool_condition_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Select operand type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_select_operand_type_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Select vector mask mismatch",
            status: CoverageStatus::FailClosed,
            check: check_select_vector_condition_mask_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Assert",
            status: CoverageStatus::Supported,
            check: check_assert_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Undef",
            status: CoverageStatus::FailClosed,
            check: check_undef_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Retain without RC runtime",
            status: CoverageStatus::FailClosed,
            check: check_retain_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Release without RC runtime",
            status: CoverageStatus::FailClosed,
            check: check_release_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::IsUnique without RC runtime",
            status: CoverageStatus::FailClosed,
            check: check_is_unique_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Retain via Clean RC runtime",
            status: CoverageStatus::Supported,
            check: check_retain_lowered_via_clean_rc_triple,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Release via Clean RC runtime",
            status: CoverageStatus::Supported,
            check: check_release_lowered_via_clean_rc_triple,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::IsUnique via Clean RC runtime",
            status: CoverageStatus::Supported,
            check: check_is_unique_lowered_via_clean_rc_triple,
        },
        CoverageRow {
            category: "instructions",
            surface: "ARC partial RC-runtime triple",
            status: CoverageStatus::FailClosed,
            check: check_arc_partial_rc_triple_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Dealloc",
            status: CoverageStatus::FailClosed,
            check: check_dealloc_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::OpenFrame",
            status: CoverageStatus::FailClosed,
            check: check_open_frame_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::BindSlot",
            status: CoverageStatus::FailClosed,
            check: check_bind_slot_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::LoadSlot",
            status: CoverageStatus::FailClosed,
            check: check_load_slot_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CloseFrame",
            status: CoverageStatus::Supported,
            check: check_close_frame_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CloseFrame non-pointer frame",
            status: CoverageStatus::FailClosed,
            check: check_close_frame_non_pointer_fail_closed,
        },
        CoverageRow {
            category: "dialect_ops",
            surface: "Inst::DialectOp unknown namespace",
            status: CoverageStatus::FailClosed,
            check: check_unknown_dialect_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Set",
            status: CoverageStatus::FailClosed,
            check: check_set_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Sequence",
            status: CoverageStatus::FailClosed,
            check: check_sequence_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Record",
            status: CoverageStatus::FailClosed,
            check: check_record_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Closure",
            status: CoverageStatus::FailClosed,
            check: check_closure_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Isize/Usize arithmetic and Char carrier/constants",
            status: CoverageStatus::Supported,
            check: check_v25_scalar_types_supported,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Char arithmetic/switch/casts/overflow",
            status: CoverageStatus::Supported,
            check: check_char_arithmetic_supported,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Refine validated identity/signature carrier",
            status: CoverageStatus::Supported,
            check: check_refine_type_supported,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Refine ordinary operation operands",
            status: CoverageStatus::FailClosed,
            check: check_refine_operation_operands_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Error",
            status: CoverageStatus::FailClosed,
            check: check_error_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Rc",
            status: CoverageStatus::FailClosed,
            check: check_rc_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Rc function boundary",
            status: CoverageStatus::FailClosed,
            check: check_rc_function_boundary_fail_closed,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Int/Float/Bool",
            status: CoverageStatus::Supported,
            check: check_scalar_constants_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Vector",
            status: CoverageStatus::Supported,
            check: check_vector_constant_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Sequence",
            status: CoverageStatus::Supported,
            check: check_sequence_constant_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Set",
            status: CoverageStatus::FailClosed,
            check: check_set_constant_fail_closed,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::U128",
            status: CoverageStatus::Supported,
            check: check_u128_constant_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Bytes",
            status: CoverageStatus::Supported,
            check: check_bytes_constant_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::SymbolAddr function-body instruction",
            status: CoverageStatus::Supported,
            check: check_symbol_addr_instruction_constant_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Record",
            status: CoverageStatus::Supported,
            check: check_record_constant_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Closure with captures",
            status: CoverageStatus::FailClosed,
            check: check_closure_constant_with_capture_fail_closed,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::PhantomData",
            status: CoverageStatus::FailClosed,
            check: check_phantom_constant_fail_closed,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::FnDef unregistered function",
            status: CoverageStatus::FailClosed,
            check: check_fndef_unregistered_fail_closed,
        },
        CoverageRow {
            category: "parser",
            surface: "TrustIr text parser/display accepted fixtures",
            status: CoverageStatus::Supported,
            check: check_text_parser_roundtrips_supported_forms,
        },
        CoverageRow {
            category: "binary",
            surface: "TrustIr binary module accepted fixtures",
            status: CoverageStatus::Supported,
            check: check_binary_module_roundtrips_supported_forms,
        },
        CoverageRow {
            category: "provenance",
            surface: "InstrNode::SourceSpan binary provenance",
            status: CoverageStatus::Supported,
            check: check_source_span_provenance_roundtrips_through_binary,
        },
        CoverageRow {
            category: "provenance",
            surface: "ProofLineageManifest binary provenance sidecar",
            status: CoverageStatus::Supported,
            check: check_proof_lineage_provenance_sidecar_roundtrips,
        },
        CoverageRow {
            category: "dialect_target_execution",
            surface: "unknown DialectOp fails closed before target execution",
            status: CoverageStatus::FailClosed,
            check: check_unknown_dialect_has_no_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Ty::Set/Sequence/Record/Closure target fixtures fail closed",
            status: CoverageStatus::FailClosed,
            check: check_logical_aggregates_have_no_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Constant::Sequence target materialization",
            status: CoverageStatus::Supported,
            check: check_sequence_constant_has_target_materialization_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Constant::Set target materialization",
            status: CoverageStatus::FailClosed,
            check: check_set_constant_has_no_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Constant::Record target materialization",
            status: CoverageStatus::Supported,
            check: check_record_constant_has_target_materialization_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Constant::Closure with captures target materialization",
            status: CoverageStatus::FailClosed,
            check: check_closure_constant_has_no_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractField over Ty::Record with RecordDef",
            status: CoverageStatus::Supported,
            check: check_record_extract_field_has_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractField over Ty::Record without RecordDef",
            status: CoverageStatus::FailClosed,
            check: check_record_extract_field_missing_def_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertField over Ty::Record with RecordDef",
            status: CoverageStatus::Supported,
            check: check_record_insert_field_has_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertField over Ty::Record without RecordDef",
            status: CoverageStatus::FailClosed,
            check: check_record_insert_field_missing_def_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractElement over materialized Ty::Sequence",
            status: CoverageStatus::Supported,
            check: check_sequence_extract_element_supported_for_materialized_sequence,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractElement over Ty::Sequence without materialized layout provenance",
            status: CoverageStatus::FailClosed,
            check: check_sequence_extract_element_without_layout_provenance_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertElement over materialized Ty::Sequence",
            status: CoverageStatus::Supported,
            check: check_sequence_insert_element_supported_for_materialized_sequence,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertElement over Ty::Sequence with unknown source layout",
            status: CoverageStatus::FailClosed,
            check: check_sequence_insert_element_has_no_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertElement over Ty::Array",
            status: CoverageStatus::Supported,
            check: check_array_insert_element_supported,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertElement rejects non-array source",
            status: CoverageStatus::FailClosed,
            check: check_insert_element_rejects_non_array_source,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertElement rejects source/result aggregate mismatch",
            status: CoverageStatus::FailClosed,
            check: check_insert_element_rejects_array_source_result_mismatch,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertElement rejects array value type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_insert_element_rejects_array_value_type_mismatch,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractElement rejects non-array source",
            status: CoverageStatus::FailClosed,
            check: check_extract_element_rejects_non_array_source,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractElement rejects array element type mismatch",
            status: CoverageStatus::FailClosed,
            check: check_extract_element_rejects_array_element_type_mismatch,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "multi-index Inst::GEP over Ty::Record with RecordDef",
            status: CoverageStatus::Supported,
            check: check_record_multi_index_gep_supported,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::GEP over Ty::Set",
            status: CoverageStatus::FailClosed,
            check: check_set_gep_has_no_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::GEP over Ty::Sequence",
            status: CoverageStatus::FailClosed,
            check: check_sequence_gep_has_no_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "single-index Inst::GEP over Ty::Set",
            status: CoverageStatus::FailClosed,
            check: check_single_index_set_gep_has_no_byte_stride_fallback,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "single-index Inst::GEP over Ty::Sequence",
            status: CoverageStatus::FailClosed,
            check: check_single_index_sequence_gep_has_no_byte_stride_fallback,
        },
    ]
}

#[allow(dead_code)]
fn binop_variant_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::UDiv => "UDiv",
        BinOp::SDiv => "SDiv",
        BinOp::URem => "URem",
        BinOp::SRem => "SRem",
        BinOp::FAdd => "FAdd",
        BinOp::FSub => "FSub",
        BinOp::FMul => "FMul",
        BinOp::FDiv => "FDiv",
        BinOp::FRem => "FRem",
        BinOp::And => "And",
        BinOp::Or => "Or",
        BinOp::Xor => "Xor",
        BinOp::Shl => "Shl",
        BinOp::LShr => "LShr",
        BinOp::AShr => "AShr",
        BinOp::FMin => "FMin",
        BinOp::FMax => "FMax",
        // Trust: the BOOLEAN connectives (trust-ir 4b06918).
        BinOp::BAnd => "BAnd",
        BinOp::BOr => "BOr",
        BinOp::BXor => "BXor",
    }
}

#[allow(dead_code)]
fn castop_variant_name(op: CastOp) -> &'static str {
    match op {
        CastOp::Trunc => "Trunc",
        CastOp::ZExt => "ZExt",
        CastOp::SExt => "SExt",
        CastOp::FPTrunc => "FPTrunc",
        CastOp::FPExt => "FPExt",
        CastOp::FPToUI => "FPToUI",
        CastOp::FPToSI => "FPToSI",
        CastOp::UIToFP => "UIToFP",
        CastOp::SIToFP => "SIToFP",
        CastOp::PtrToInt => "PtrToInt",
        CastOp::IntToPtr => "IntToPtr",
        CastOp::PtrToPtr => "PtrToPtr",
        CastOp::Bitcast => "Bitcast",
        CastOp::Transmute => "Transmute",
        CastOp::ReifyFnPointer => "ReifyFnPointer",
        CastOp::FPToSISat => "FPToSISat",
        CastOp::FPToUISat => "FPToUISat",
    }
}

#[allow(dead_code)]
fn ty_variant_name(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "I8",
        Ty::I16 => "I16",
        Ty::I32 => "I32",
        Ty::I64 => "I64",
        Ty::I128 => "I128",
        Ty::U8 => "U8",
        Ty::U16 => "U16",
        Ty::U32 => "U32",
        Ty::U64 => "U64",
        Ty::U128 => "U128",
        Ty::Isize => "Isize",
        Ty::Usize => "Usize",
        Ty::Char => "Char",
        Ty::Error => "Error",
        Ty::F16 => "F16",
        Ty::F32 => "F32",
        Ty::F64 => "F64",
        Ty::Bool => "Bool",
        Ty::Vector(_, _) => "Vector",
        Ty::Ptr => "Ptr",
        Ty::FatPtr(_) => "FatPtr",
        Ty::Unit => "Unit",
        Ty::Never => "Never",
        Ty::Struct(_) => "Struct",
        Ty::Array(_, _) => "Array",
        Ty::Tuple(_) => "Tuple",
        Ty::Enum(_) => "Enum",
        Ty::Func(_) => "Func",
        Ty::Ref(_) => "Ref",
        Ty::RefMut(_) => "RefMut",
        Ty::PtrConst(_) => "PtrConst",
        Ty::PtrMut(_) => "PtrMut",
        Ty::Rc(_) => "Rc",
        Ty::Set(_, _) => "Set",
        Ty::Sequence(_) => "Sequence",
        Ty::Record(_) => "Record",
        Ty::Closure(_) => "Closure",
        Ty::Refine(_, _) => "Refine",
    }
}

#[allow(dead_code)]
fn constant_variant_name(value: &Constant) -> &'static str {
    match value {
        Constant::Int(_) => "Int",
        Constant::U128(_) => "U128",
        Constant::Bytes { .. } => "Bytes",
        Constant::Float(_) => "Float",
        Constant::Bool(_) => "Bool",
        Constant::Aggregate(_) => "Aggregate",
        Constant::Array(_) => "Array",
        Constant::Vector(_) => "Vector",
        Constant::Sequence(_) => "Sequence",
        Constant::Set(_) => "Set",
        Constant::Record(_) => "Record",
        Constant::Closure { .. } => "Closure",
        Constant::FnDef(_) => "FnDef",
        Constant::SymbolAddr { .. } => "SymbolAddr",
        Constant::PhantomData => "PhantomData",
    }
}

#[allow(dead_code)]
fn inst_variant_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::GEP { .. } => "GEP",
        Inst::PtrData { .. } => "PtrData",
        Inst::PtrMetadata { .. } => "PtrMetadata",
        Inst::PtrFromParts { .. } => "PtrFromParts",
        Inst::AtomicLoad { .. } => "AtomicLoad",
        Inst::AtomicStore { .. } => "AtomicStore",
        Inst::AtomicRMW { .. } => "AtomicRMW",
        Inst::CmpXchg { .. } => "CmpXchg",
        Inst::Fence { .. } => "Fence",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::CoroSuspend { .. } => "CoroSuspend",
        Inst::Invoke { .. } => "Invoke",
        Inst::LandingPad { .. } => "LandingPad",
        Inst::Resume { .. } => "Resume",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::Const { .. } => "Const",
        Inst::NullPtr => "NullPtr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        Inst::SeqMapAddK { .. } => "SeqMapAddK",
        Inst::SeqMapNot { .. } => "SeqMapNot",
        Inst::SeqMap { .. } => "SeqMap",
        Inst::Borrow { .. } => "Borrow",
        Inst::BorrowMut { .. } => "BorrowMut",
        Inst::EndBorrow { .. } => "EndBorrow",
        Inst::Retain { .. } => "Retain",
        Inst::Release { .. } => "Release",
        Inst::IsUnique { .. } => "IsUnique",
        Inst::Dealloc { .. } => "Dealloc",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::OpenFrame { .. } => "OpenFrame",
        Inst::BindSlot { .. } => "BindSlot",
        Inst::LoadSlot { .. } => "LoadSlot",
        Inst::CloseFrame { .. } => "CloseFrame",
        Inst::DialectOp(_) => "DialectOp",
    }
}

fn all_binop_variant_names() -> Vec<&'static str> {
    [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::UDiv,
        BinOp::SDiv,
        BinOp::URem,
        BinOp::SRem,
        BinOp::FAdd,
        BinOp::FSub,
        BinOp::FMul,
        BinOp::FDiv,
        BinOp::FRem,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
    ]
    .into_iter()
    .map(binop_variant_name)
    .collect()
}

fn all_castop_variant_names() -> Vec<&'static str> {
    [
        CastOp::Trunc,
        CastOp::ZExt,
        CastOp::SExt,
        CastOp::FPTrunc,
        CastOp::FPExt,
        CastOp::FPToUI,
        CastOp::FPToSI,
        CastOp::UIToFP,
        CastOp::SIToFP,
        CastOp::PtrToInt,
        CastOp::IntToPtr,
        CastOp::PtrToPtr,
        CastOp::Bitcast,
        CastOp::Transmute,
        CastOp::ReifyFnPointer,
    ]
    .into_iter()
    .map(castop_variant_name)
    .collect()
}

fn all_ty_variant_names() -> Vec<&'static str> {
    [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::Error,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Vector(Box::new(Ty::I32), 4),
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Unit,
        Ty::Never,
        Ty::Struct(StructId::new(0)),
        Ty::Array(TyId::new(0), 4),
        Ty::Tuple(vec![Ty::I64]),
        Ty::Enum(EnumId::new(0)),
        Ty::Func(trust_ir::value::FuncTyId::new(0)),
        Ty::Ref(Box::new(Ty::I64)),
        Ty::RefMut(Box::new(Ty::I64)),
        Ty::PtrConst(Box::new(Ty::I64)),
        Ty::PtrMut(Box::new(Ty::I64)),
        Ty::Rc(Box::new(Ty::I64)),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Refine(TyId::new(0), PredId::new(0)),
    ]
    .iter()
    .map(ty_variant_name)
    .collect()
}

fn all_constant_variant_names() -> Vec<&'static str> {
    [
        Constant::Int(0),
        Constant::U128((i128::MAX as u128) + 1),
        Constant::Bytes {
            data: vec![0x54, 0x49, 0x52],
            utf8: false,
        },
        Constant::Float(0.0),
        Constant::Bool(false),
        Constant::Aggregate(vec![Constant::Int(0)]),
        Constant::Array(vec![Constant::Int(0)]),
        Constant::Vector(vec![Constant::Int(0)]),
        Constant::Sequence(vec![Constant::Int(0)]),
        Constant::Set(vec![Constant::Int(0)]),
        Constant::Record(vec![("field".to_string(), Constant::Int(0))]),
        Constant::Closure {
            func: f(0),
            captures: vec![],
        },
        Constant::FnDef(f(0)),
        Constant::SymbolAddr {
            symbol: "manifest_symbol".to_string(),
            addend: 0,
        },
        Constant::PhantomData,
    ]
    .iter()
    .map(constant_variant_name)
    .collect()
}

fn all_inst_variant_names() -> Vec<&'static str> {
    let frame_def = BindingFrameDef::new(
        BindingFrameId::new(0),
        "manifest_frame",
        vec![BindingSlot::new("slot", Ty::I64)],
    );
    vec![
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::UnOp {
            op: trust_ir::UnOp::Not,
            ty: Ty::I64,
            operand: v(0),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::I64,
            dst_ty: Ty::F64,
            operand: v(0),
        },
        Inst::Load {
            ty: Ty::I64,
            ptr: v(0),
            volatile: false,
            align: None,
        },
        Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        },
        Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        },
        Inst::GEP {
            pointee_ty: Ty::I64,
            base: v(0),
            indices: vec![v(1)],
            inbounds: false,
        },
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(0),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Unit,
            ptr: v(0),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Unit,
            data: v(0),
            metadata: v(1),
        },
        Inst::AtomicLoad {
            ty: Ty::I64,
            ptr: v(0),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicStore {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::CmpXchg {
            ty: Ty::I64,
            ptr: v(0),
            expected: v(1),
            desired: v(2),
            success: Ordering::SeqCst,
            failure: Ordering::Acquire,
        },
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        Inst::Br {
            target: b(0),
            args: vec![],
        },
        Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        },
        Inst::Switch {
            value: v(0),
            default: b(1),
            default_args: vec![],
            cases: vec![SwitchCase {
                value: Constant::Int(0),
                target: b(2),
                args: vec![],
            }],
            exhaustive_enum_unreachable: false,
        },
        Inst::Call {
            callee: f(0),
            args: vec![v(0)],
        },
        Inst::CallIndirect {
            callee: v(0),
            sig: trust_ir::value::FuncTyId::new(0),
            args: vec![v(1)],
            calling_conv: CallingConv::C,
        },
        Inst::Return { values: vec![v(0)] },
        Inst::ExtractField {
            ty: Ty::Tuple(vec![Ty::I64]),
            aggregate: v(0),
            field: 0,
        },
        Inst::InsertField {
            ty: Ty::Tuple(vec![Ty::I64]),
            aggregate: v(0),
            field: 0,
            value: v(1),
        },
        Inst::ExtractElement {
            ty: Ty::Array(TyId::new(0), 1),
            array: v(0),
            index: v(1),
        },
        Inst::InsertElement {
            ty: Ty::Array(TyId::new(0), 1),
            array: v(0),
            index: v(1),
            value: v(2),
        },
        Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        },
        Inst::NullPtr,
        Inst::Undef { ty: Ty::I64 },
        Inst::Assume { cond: v(0) },
        Inst::Assert { cond: v(0) },
        Inst::Unreachable,
        Inst::Copy {
            ty: Ty::I64,
            operand: v(0),
        },
        Inst::Select {
            ty: Ty::I64,
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        },
        Inst::SeqMapAddK {
            ty: Ty::Sequence(TyId::new(0)),
            seq: v(0),
            k: 1,
        },
        Inst::SeqMapNot {
            ty: Ty::Sequence(TyId::new(0)),
            seq: v(0),
        },
        Inst::Borrow { ptr: v(0) },
        Inst::BorrowMut { ptr: v(0) },
        Inst::EndBorrow { borrow_ptr: v(0) },
        Inst::Retain { ptr: v(0) },
        Inst::Release { ptr: v(0) },
        Inst::IsUnique { ptr: v(0) },
        Inst::Dealloc { ptr: v(0) },
        Inst::OpenFrame { def: frame_def },
        Inst::BindSlot {
            frame: v(0),
            slot: 0,
            value: v(1),
        },
        Inst::LoadSlot {
            frame: v(0),
            slot: 0,
            ty: Ty::I64,
        },
        Inst::CloseFrame { frame: v(0) },
        Inst::DialectOp(Box::new(DialectInst::new("manifest_unknown", "opaque"))),
    ]
    .iter()
    .map(inst_variant_name)
    .collect()
}

fn generated_enum_inventories() -> Vec<EnumVariantInventory> {
    vec![
        EnumVariantInventory {
            enum_name: "BinOp",
            expected_variants: &[
                "Add", "Sub", "Mul", "UDiv", "SDiv", "URem", "SRem", "FAdd", "FSub", "FMul",
                "FDiv", "FRem", "And", "Or", "Xor", "Shl", "LShr", "AShr",
            ],
            actual_variants: all_binop_variant_names,
        },
        EnumVariantInventory {
            enum_name: "CastOp",
            expected_variants: &[
                "Trunc",
                "ZExt",
                "SExt",
                "FPTrunc",
                "FPExt",
                "FPToUI",
                "FPToSI",
                "UIToFP",
                "SIToFP",
                "PtrToInt",
                "IntToPtr",
                "PtrToPtr",
                "Bitcast",
                "Transmute",
                "ReifyFnPointer",
            ],
            actual_variants: all_castop_variant_names,
        },
        EnumVariantInventory {
            enum_name: "Ty",
            expected_variants: &[
                "I8", "I16", "I32", "I64", "I128", "U8", "U16", "U32", "U64", "U128", "Isize",
                "Usize", "Char", "Error", "F16", "F32", "F64", "Bool", "Vector", "Ptr", "FatPtr",
                "Unit", "Never", "Struct", "Array", "Tuple", "Enum", "Func", "Ref", "RefMut",
                "PtrConst", "PtrMut", "Rc", "Set", "Sequence", "Record", "Closure", "Refine",
            ],
            actual_variants: all_ty_variant_names,
        },
        EnumVariantInventory {
            enum_name: "Constant",
            expected_variants: &[
                "Int",
                "U128",
                "Bytes",
                "Float",
                "Bool",
                "Aggregate",
                "Array",
                "Vector",
                "Sequence",
                "Set",
                "Record",
                "Closure",
                "FnDef",
                "SymbolAddr",
                "PhantomData",
            ],
            actual_variants: all_constant_variant_names,
        },
        EnumVariantInventory {
            enum_name: "Inst",
            expected_variants: &[
                "BinOp",
                "UnOp",
                "Overflow",
                "ICmp",
                "FCmp",
                "Cast",
                "Load",
                "Store",
                "Alloca",
                "GEP",
                "PtrData",
                "PtrMetadata",
                "PtrFromParts",
                "AtomicLoad",
                "AtomicStore",
                "AtomicRMW",
                "CmpXchg",
                "Fence",
                "Br",
                "CondBr",
                "Switch",
                "Call",
                "CallIndirect",
                "Return",
                "ExtractField",
                "InsertField",
                "ExtractElement",
                "InsertElement",
                "Const",
                "NullPtr",
                "Undef",
                "Assume",
                "Assert",
                "Unreachable",
                "Copy",
                "Select",
                "SeqMapAddK",
                "SeqMapNot",
                "Borrow",
                "BorrowMut",
                "EndBorrow",
                "Retain",
                "Release",
                "IsUnique",
                "Dealloc",
                "OpenFrame",
                "BindSlot",
                "LoadSlot",
                "CloseFrame",
                "DialectOp",
            ],
            actual_variants: all_inst_variant_names,
        },
    ]
}

fn inventory_rows() -> Vec<InventoryRow> {
    use CoverageStatus::{FailClosed, Supported};

    vec![
        InventoryRow {
            enum_name: "Ty",
            variant: "Bool/I*/U*/F*/Ptr/ref/raw/Func/FatPtr",
            status: Supported,
            evidence: "translate_type direct scalar/pointer rows excluding Rc",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Rc",
            status: FailClosed,
            evidence: "coverage_rows Rc type and function-boundary fail closed: refcount ownership has no modelled CPU ABI",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Vector/Struct/Array/Tuple/Enum",
            status: Supported,
            evidence: "supported with shape/table constraints",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Unit/Never",
            status: FailClosed,
            evidence: "void-value type path",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Isize/Usize arithmetic and Char carrier/constants",
            status: Supported,
            evidence: "coverage_rows v25 pointer-width arithmetic plus Unicode-scalar Char carrier/constant checks",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Char arithmetic/switch/casts/overflow",
            status: Supported,
            evidence: "coverage_rows Char uses TrustIr's 32-bit unsigned arithmetic carrier while constants retain Unicode-scalar validation",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Error",
            status: FailClosed,
            evidence: "coverage_rows producer-internal error type row",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Refine identity/signature carrier",
            status: Supported,
            evidence: "coverage_rows validated representation-preserving pass-through lowering",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Refine ordinary operation operands",
            status: FailClosed,
            evidence: "coverage_rows refined arithmetic operands fail closed until consumer-wide representation peeling exists",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Set/Sequence/Record/Closure",
            status: FailClosed,
            evidence: "coverage_rows logical aggregate type rows",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "Int/Float/Bool/Vector",
            status: Supported,
            evidence: "coverage_rows scalar/vector constants",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "Aggregate/Array",
            status: Supported,
            evidence: "adapter aggregate materialization with type constraints",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "FnDef/empty Closure",
            status: Supported,
            evidence: "adapter function-symbol constant path",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "Sequence/Record",
            status: Supported,
            evidence: "coverage_rows typed logical constant materialization",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "Set/captured Closure/PhantomData",
            status: FailClosed,
            evidence: "coverage_rows trust_ir#30 constant rows",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "U128/Bytes",
            status: Supported,
            evidence: "coverage_rows v24/v25 faithful target materialization with canonicality and UTF-8 checks",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "SymbolAddr function-body instruction",
            status: Supported,
            evidence: "coverage_rows zero-addend SymbolAddr lowers to GlobalRef/ExternRef (raw-name FnDef/GlobalAddr counterpart); non-zero addend fails closed",
        },
        InventoryRow {
            enum_name: "BinOp",
            variant: "Add/Sub/Mul/Div/Rem/bit/shift/FAdd/FSub/FMul/FDiv",
            status: Supported,
            evidence: "coverage_rows scalar BinOp with operand/type validators",
        },
        InventoryRow {
            enum_name: "BinOp",
            variant: "FRem f32/f64",
            status: Supported,
            evidence: "coverage_rows FRem f32/f64 rows lower to fmodf/fmod libcalls",
        },
        InventoryRow {
            enum_name: "BinOp",
            variant: "FRem f16",
            status: Supported,
            evidence: "coverage_rows promoted-fmodf FRem f16 row",
        },
        InventoryRow {
            enum_name: "BinOp",
            variant: "FRem vector/non-float",
            status: FailClosed,
            evidence: "coverage_rows BinOp operand/type validators",
        },
        InventoryRow {
            enum_name: "UnOp",
            variant: "Neg/FNeg/Not/CtPop",
            status: Supported,
            evidence: "coverage_rows UnOp scalar core with type validators",
        },
        InventoryRow {
            enum_name: "CastOp",
            variant: "Trunc/ZExt/SExt/FP*/Ptr*/Bitcast",
            status: Supported,
            evidence: "coverage_rows standard casts",
        },
        InventoryRow {
            enum_name: "CastOp",
            variant: "Transmute equal-size/size-mismatch",
            status: FailClosed,
            evidence: "coverage_rows Transmute equal-size and size-mismatch rows",
        },
        InventoryRow {
            enum_name: "CastOp",
            variant: "ReifyFnPointer",
            status: Supported,
            evidence: "coverage_rows ReifyFnPointer materialized function symbol row plus fail-closed unprovenanced row",
        },
        InventoryRow {
            enum_name: "AtomicRMWOp",
            variant: "Xchg/Add/Sub/And/Or/Xor/Max/Min/UMax/UMin",
            status: Supported,
            evidence: "coverage_rows supported AtomicRMW row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "BinOp/UnOp/ICmp/FCmp/Cast/Load/Store/Alloca/GEP",
            status: Supported,
            evidence: "adapter core instruction arms and focused operand/type validation rows",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "PtrData/PtrMetadata/PtrFromParts",
            status: Supported,
            evidence: "adapter pointer-lane arms",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "AtomicLoad/AtomicStore/AtomicRMW/CmpXchg/Fence",
            status: Supported,
            evidence: "coverage_rows atomic rows with legal-ordering support and illegal-ordering fail-closed checks",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Br/CondBr/Switch/Call/CallIndirect/Return",
            status: Supported,
            evidence: "adapter control/call arms with direct, indirect, and return signature checks",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "ExtractField/InsertField/ExtractElement/InsertElement",
            status: Supported,
            evidence: "adapter aggregate/vector arms with type constraints",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Const/NullPtr/Unreachable/Copy/Select",
            status: Supported,
            evidence: "coverage_rows constants/control/pseudo rows plus Select operand/mask validation",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Assume",
            status: Supported,
            evidence: "coverage_rows Assume checked runtime assertion row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Undef",
            status: FailClosed,
            evidence: "coverage_rows Undef row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Borrow/BorrowMut/EndBorrow",
            status: FailClosed,
            evidence: "coverage_rows borrow provenance fail-closed row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Assert",
            status: Supported,
            evidence: "coverage_rows assert row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Retain",
            status: FailClosed,
            evidence: "coverage_rows Retain row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Release",
            status: FailClosed,
            evidence: "coverage_rows Release row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "IsUnique",
            status: FailClosed,
            evidence: "coverage_rows IsUnique row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Dealloc",
            status: FailClosed,
            evidence: "coverage_rows dealloc row with allocator/layout diagnostic",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "OpenFrame",
            status: FailClosed,
            evidence: "coverage_rows OpenFrame row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "BindSlot",
            status: FailClosed,
            evidence: "coverage_rows BindSlot row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "LoadSlot",
            status: FailClosed,
            evidence: "coverage_rows LoadSlot row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "CloseFrame",
            status: Supported,
            evidence: "coverage_rows CloseFrame row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "DialectOp known vector/bitfield",
            status: Supported,
            evidence: "adapter dialect allowlist arms",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "DialectOp unknown namespace",
            status: FailClosed,
            evidence: "coverage_rows unknown dialect row",
        },
        InventoryRow {
            enum_name: "Ordering",
            variant: "Relaxed/Acquire/Release/AcqRel/SeqCst",
            status: Supported,
            evidence: "adapter ordering translation; CmpXchg validates invalid pairs",
        },
        InventoryRow {
            enum_name: "SetRepr",
            variant: "Bitset/Boxed",
            status: FailClosed,
            evidence: "Ty::Set fails closed independent of repr",
        },
        InventoryRow {
            enum_name: "TrustIrTransport",
            variant: "parser::parse_module text/display roundtrip",
            status: Supported,
            evidence: "coverage_rows parser accepted fixtures",
        },
        InventoryRow {
            enum_name: "TrustIrTransport",
            variant: "binary::serialize_module/deserialize_module",
            status: Supported,
            evidence: "coverage_rows binary accepted fixtures",
        },
        InventoryRow {
            enum_name: "TrustIrProvenance",
            variant: "InstrNode::SourceSpan",
            status: Supported,
            evidence: "coverage_rows SourceSpan binary provenance row",
        },
        InventoryRow {
            enum_name: "TrustIrProvenance",
            variant: "ProofLineageManifest sidecar",
            status: Supported,
            evidence: "coverage_rows proof-lineage provenance sidecar row",
        },
    ]
}

#[test]
fn trust_ir_coverage_manifest_rows_are_unique_and_categorized() {
    let rows = coverage_rows();
    let mut seen = HashSet::new();
    for row in &rows {
        assert!(
            seen.insert((row.category, row.surface)),
            "duplicate manifest row: {} / {}",
            row.category,
            row.surface
        );
    }

    for required in [
        "types",
        "constants",
        "instructions",
        "binops",
        "comparisons",
        "casts",
        "atomics",
        "dialect_ops",
        "unops",
        "parser",
        "binary",
        "provenance",
        "dialect_target_execution",
        "aggregate_target_execution",
    ] {
        assert!(
            rows.iter().any(|row| row.category == required),
            "manifest must include category `{required}`"
        );
    }

    assert!(
        rows.iter()
            .any(|row| row.status == CoverageStatus::Supported),
        "manifest must track at least one supported surface"
    );
    assert!(
        rows.iter()
            .any(|row| row.status == CoverageStatus::FailClosed),
        "manifest must track fail-closed surfaces"
    );
    assert!(
        rows.iter().any(|row| row.category == "binops"
            && row.surface == "vector BinOp typed V128 Add/Sub/Mul subset"
            && row.status == CoverageStatus::Supported),
        "manifest must pin supported vector BinOp rows"
    );
    assert!(
        rows.iter()
            .any(|row| row.category == "instructions" && row.surface == "Inst::Dealloc"),
        "manifest must pin Dealloc separately from ARC so it cannot silently disappear"
    );
    assert!(
        rows.iter().any(|row| row.category == "instructions"
            && row.surface == "Inst::Undef"
            && row.status == CoverageStatus::FailClosed),
        "manifest must pin Undef as fail-closed until poison/undef semantics are modeled"
    );
    for required_surface in [
        "integer BinOp declared float",
        "float BinOp declared integer",
        "BinOp operand type mismatch",
        "shift BinOp declared float",
    ] {
        assert!(
            rows.iter().any(|row| row.category == "binops"
                && row.surface == required_surface
                && row.status == CoverageStatus::FailClosed),
            "manifest must pin `{required_surface}` as an executable fail-closed binop row"
        );
    }

    for required_surface in [
        "Inst::ICmp declared non-integer type",
        "Inst::ICmp operand type mismatch",
        "Inst::ICmp pointer relational operands",
        "Inst::FCmp declared non-float type",
        "Inst::FCmp operand type mismatch",
    ] {
        assert!(
            rows.iter().any(|row| row.category == "comparisons"
                && row.surface == required_surface
                && row.status == CoverageStatus::FailClosed),
            "manifest must pin `{required_surface}` as an executable fail-closed comparison row"
        );
    }

    {
        let required_surface = "UnOp wrong scalar type";
        assert!(
            rows.iter().any(|row| row.category == "unops"
                && row.surface == required_surface
                && row.status == CoverageStatus::FailClosed),
            "manifest must pin `{required_surface}` as an executable fail-closed unop row"
        );
    }

    for required_surface in ["Ty::Rc", "Ty::Rc function boundary"] {
        assert!(
            rows.iter().any(|row| row.category == "types"
                && row.surface == required_surface
                && row.status == CoverageStatus::FailClosed),
            "manifest must pin `{required_surface}` as an executable fail-closed type row"
        );
    }
    for required_surface in [
        "CastOp malformed pointer casts",
        "CastOp wrong-direction integer resize",
        "CastOp::Transmute equal-size",
        "CastOp::Transmute size-mismatch",
        "CastOp::ReifyFnPointer without materialized provenance",
    ] {
        assert!(
            rows.iter().any(|row| row.category == "casts"
                && row.surface == required_surface
                && row.status == CoverageStatus::FailClosed),
            "manifest must pin `{required_surface}` as an executable fail-closed cast row"
        );
    }

    for required_surface in [
        "AtomicLoad::Release ordering",
        "AtomicLoad::AcqRel ordering",
        "AtomicStore::Acquire ordering",
        "AtomicStore::AcqRel ordering",
    ] {
        assert!(
            rows.iter().any(|row| row.category == "atomics"
                && row.surface == required_surface
                && row.status == CoverageStatus::FailClosed),
            "manifest must pin `{required_surface}` as an executable fail-closed atomic row"
        );
    }

    // Volatile Load/Store are now SUPPORTED (they lower to the distinct
    // VolatileLoad/VolatileStore barrier opcodes), so they are no longer pinned
    // as fail-closed here — their Supported coverage rows carry the assertion.
    {
        let required_surface = "Inst::Alloca invalid explicit align";
        assert!(
            rows.iter().any(|row| row.category == "memory"
                && row.surface == required_surface
                && row.status == CoverageStatus::FailClosed),
            "manifest must pin `{required_surface}` as an executable fail-closed memory row"
        );
    }

    for required_surface in [
        "Inst::Call unregistered callee",
        "Inst::Call argument arity mismatch",
        "Inst::Call argument type mismatch",
        "Inst::Call result arity mismatch",
        "Inst::Return arity mismatch",
        "Inst::Return type mismatch",
        "Inst::CallIndirect unregistered signature",
        "Inst::CallIndirect non-pointer callee",
        "Inst::CallIndirect argument type mismatch",
        "Inst::CallIndirect result arity mismatch",
        "Inst::CallIndirect variadic signature",
        "Inst::CallIndirect Swift aggregate signature",
        "Inst::Assume non-Bool condition",
        "Inst::Borrow/BorrowMut/EndBorrow",
        "Inst::Select scalar non-Bool condition",
        "Inst::Select operand type mismatch",
        "Inst::Select vector mask mismatch",
        "Inst::Switch non-integer selector",
        "Inst::Switch unsupported selector width",
        "Inst::Switch duplicate normalized case",
        "Inst::Switch non-integer case",
        "Inst::Switch block-arg mismatch",
        "Inst::Retain without RC runtime",
        "Inst::Release without RC runtime",
        "Inst::IsUnique without RC runtime",
        "ARC partial RC-runtime triple",
        "Inst::OpenFrame",
        "Inst::BindSlot",
        "Inst::LoadSlot",
    ] {
        assert!(
            rows.iter().any(|row| row.category == "instructions"
                && row.surface == required_surface
                && row.status == CoverageStatus::FailClosed),
            "manifest must pin `{required_surface}` as an executable fail-closed row"
        );
    }

    for required_surface in [
        "Inst::Call C/Fast/Cold/Rust/scalar-Swift ABI matrix",
        "Inst::CallIndirect C/Fast/Cold/Rust/scalar-Swift ABI matrix",
    ] {
        assert!(
            rows.iter().any(|row| row.category == "instructions"
                && row.surface == required_surface
                && row.status == CoverageStatus::Supported),
            "manifest must pin `{required_surface}` as an executable supported call row"
        );
    }

    for required_surface in [
        "Constant::Set target materialization",
        "Constant::Closure with captures target materialization",
        "Inst::ExtractField over Ty::Record without RecordDef",
        "Inst::InsertField over Ty::Record without RecordDef",
        "Inst::InsertElement over Ty::Sequence with unknown source layout",
        "Inst::InsertElement rejects non-array source",
        "Inst::InsertElement rejects source/result aggregate mismatch",
        "Inst::InsertElement rejects array value type mismatch",
        "Inst::ExtractElement rejects non-array source",
        "Inst::ExtractElement rejects array element type mismatch",
        "Inst::GEP over Ty::Set",
        "Inst::GEP over Ty::Sequence",
        "single-index Inst::GEP over Ty::Set",
        "single-index Inst::GEP over Ty::Sequence",
    ] {
        assert!(
            rows.iter()
                .any(|row| row.category == "aggregate_target_execution"
                    && row.surface == required_surface
                    && row.status == CoverageStatus::FailClosed),
            "manifest must pin aggregate target-execution surface `{required_surface}`"
        );
    }
}

#[test]
fn trust_ir_enum_inventory_is_structured_and_has_evidence() {
    let rows = inventory_rows();
    let mut seen = HashSet::new();
    for row in &rows {
        assert!(
            seen.insert((row.enum_name, row.variant)),
            "duplicate inventory row: {} / {}",
            row.enum_name,
            row.variant
        );
        assert!(!row.evidence.is_empty(), "inventory row needs evidence");
    }

    for required in [
        "Ty",
        "Constant",
        "BinOp",
        "UnOp",
        "CastOp",
        "AtomicRMWOp",
        "Inst",
        "Ordering",
        "SetRepr",
        "TrustIrTransport",
        "TrustIrProvenance",
    ] {
        assert!(
            rows.iter().any(|row| row.enum_name == required),
            "inventory must include TrustIr enum `{required}`"
        );
        assert!(
            rows.iter()
                .any(|row| row.enum_name == required && row.status == CoverageStatus::Supported)
                || required == "SetRepr",
            "inventory enum `{required}` must include supported rows"
        );
    }

    assert!(
        rows.iter()
            .any(|row| row.status == CoverageStatus::FailClosed),
        "inventory must preserve fail-closed rows"
    );

    for required_variant in [
        "Retain",
        "Release",
        "IsUnique",
        "OpenFrame",
        "BindSlot",
        "LoadSlot",
    ] {
        assert!(
            rows.iter().any(|row| row.enum_name == "Inst"
                && row.variant == required_variant
                && row.status == CoverageStatus::FailClosed),
            "Inst inventory must pin `{required_variant}` individually"
        );
    }
}

#[test]
fn trust_ir_generated_variant_inventory_matches_current_enums() {
    for inventory in generated_enum_inventories() {
        let actual = (inventory.actual_variants)();
        assert_eq!(
            actual.len(),
            inventory.expected_variants.len(),
            "{} variant count drifted: expected {:?}, got {:?}",
            inventory.enum_name,
            inventory.expected_variants,
            actual
        );
        assert_eq!(
            actual, inventory.expected_variants,
            "{} variant names/order drifted",
            inventory.enum_name
        );
    }
}

#[test]
fn trust_ir_coverage_manifest_matches_adapter_behavior() {
    for row in coverage_rows() {
        (row.check)();
    }
}

#[test]
fn trust_ir_rc_manifest_rows_fail_closed() {
    // `Ty::Rc(_)` carries reference-count ownership (retain/release/drop) that
    // has no modelled CPU ABI. Lowering it to a bare pointer-sized I64 carrier
    // would silently drop those semantics, so both the standalone type row and
    // the function-boundary row must fail closed — the sound stance.
    check_rc_type_fail_closed();
    check_rc_function_boundary_fail_closed();
}

#[test]
fn trust_ir_logical_type_definitions_are_present_but_not_lowered() {
    let mut module = TrustIrModule::new("logical_type_tables");
    module.types.push(Ty::I64);
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "ManifestRecord".to_string(),
        fields: vec![FieldDef {
            name: "field".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
    });
    let func_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    module.closure_types.push(ClosureTy {
        func: func_ty,
        captures: vec![Ty::I64],
    });

    for ty in [
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
    ] {
        let err = translate_type(&ty)
            .expect_err("logical trust-ir aggregate types must currently fail closed");
        expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
    }
}
