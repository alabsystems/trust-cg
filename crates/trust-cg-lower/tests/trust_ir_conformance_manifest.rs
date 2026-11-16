// trust_ir_conformance_manifest.rs - executable TrustIr coverage ledger
//
// This is a deliberately small foothold: every row is a live adapter check,
// so moving a surface from fail_closed to supported requires updating both
// the implementation and this manifest.

use std::collections::HashSet;

#[path = "common/canonical_constant_inventory.rs"]
mod canonical_constants;
#[path = "common/conformance_record_constants.rs"]
mod record_constants;
#[path = "common/runtime_closure.rs"]
mod runtime_closure;

use trust_cg_lower::adapter::{
    AdapterError, reject_unconsumed_v41_target_neutral_surface, translate_type,
    translate_type_with_tables,
};
use trust_cg_lower::instructions::{AtomicRmwOp as LirAtomicRmwOp, Instruction, IntCC, Opcode};
use trust_cg_lower::types::Type;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{AllocOrigin, BindingFrameDef, BindingSlot};
use trust_ir::value::{BindingFrameId, SourceSpan};
use trust_ir::{
    AtomicRMWOp, BinOp, Block as TrustIrBlock, BlockId, CallingConv, CastOp, ClosureTy,
    ClosureTyId, Constant, Endianness, EnumId, FCmpOp, FatPtrKind, FieldDef, FuncId, FuncTy,
    FuncTyId, Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule,
    Ordering, OverflowOp, Pred, PredId, RecordDef, RecordId, SetRepr, StructDef, StructId,
    StructPassingPolicy, StructRepr, SwitchCase, TargetInfo, Ty, TyId, ValueId,
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
    /// `AdapterError::LegalizationRefused`: the borrow / binding-frame /
    /// `Undef` legalization stage refused the shape by name.
    Legalization,
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
    let ty = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), name, ty, entry);
    func.blocks = blocks;
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn translate_single(
    module: &TrustIrModule,
) -> Result<trust_cg_lower::function::Function, AdapterError> {
    let func = module
        .functions
        .first()
        .expect("test module must have one function");
    trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
        .map(|(func, _proofs)| func)
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
        (DiagnosticClass::Legalization, err @ AdapterError::LegalizationRefused { .. }) => {
            let message = err.to_string();
            assert!(
                message.contains(needle),
                "expected LegalizationRefused containing `{needle}`, got `{message}`"
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
        (DiagnosticClass::Legalization, err @ AdapterError::LegalizationRefused { .. }) => {
            let message = err.to_string();
            for needle in needles {
                assert!(
                    message.contains(needle),
                    "expected LegalizationRefused containing `{needle}`, got `{message}`"
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
    let callee_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

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

    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

fn sequence_const_module(name: &str, values: Vec<Constant>) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let elem_tyid = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let func_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
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
    let func_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    record_constants::canonical_fixture(module, name, false)
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
    let func_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    record_constants::canonical_fixture(module, name, true)
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
    record_constants::canonical_fixture(module, name, false)
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
        // trust-ir WS3.20: expanded into covered shift/mask/bitcast opcodes.
        (BinOp::RotL, Ty::I64),
        (BinOp::RotR, Ty::U8),
        (BinOp::FCopySign, Ty::F64),
        (BinOp::FCopySign, Ty::F32),
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
            .any(|inst| matches!(&inst.opcode, Opcode::Call { name, .. } if name == "fmod")),
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
            .any(|inst| matches!(&inst.opcode, Opcode::Call { name, .. } if name == "fmodf")),
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
            .any(|inst| matches!(&inst.opcode, Opcode::Call { name, .. } if name == "fmodf")),
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
    // emits the typed compare op rather than scalarizing the lanes. This is
    // the function-level entry, which is not an x86-64 MODULE entry: there
    // trust-ir's per-cell rule decides admission (`tests/x86_vector_icmp_admission.rs`;
    // at the pinned trust-ir every covered cell, the unsigned `chc_x86.v16_i8`
    // ones included, is available).
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
        // trust-ir WS3.20 bit intrinsics.
        (trust_ir::UnOp::CtLz, Ty::I64),
        (trust_ir::UnOp::CtTz, Ty::U32),
        (trust_ir::UnOp::BSwap, Ty::I16),
        (trust_ir::UnOp::BitReverse, Ty::U8),
    ] {
        expect_supported(&unop_module("manifest_unop", op, ty), "UnOp");
    }
}

fn check_unop_wrong_type_fail_closed() {
    for (op, ty, expected) in [
        (trust_ir::UnOp::FNeg, Ty::I64, "UnOp::FNeg"),
        (trust_ir::UnOp::Neg, Ty::F64, "UnOp::Neg"),
        (trust_ir::UnOp::CtPop, Ty::F64, "UnOp::CtPop"),
        (trust_ir::UnOp::CtLz, Ty::F64, "UnOp::CtLz"),
        // `Char` is not an integer to trust-ir, so the bit intrinsics refuse
        // its arithmetic carrier.
        (trust_ir::UnOp::BSwap, Ty::Char, "UnOp::BSwap"),
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

/// A `<N x bool>` logical mask never reaches a memory layout: trust-ir's
/// normative interpreter stores one `0xFF`/`0x00` byte per lane, while this
/// backend's carrier is the producer's register class (V128 of 16-bit lanes
/// for an `<8 x i16>` compare), so the boundary is refused BY NAME rather
/// than emitting either image. The full boundary matrix and the referee's
/// quoted bytes are in `tests/bool_lane_layout_refusal.rs`.
fn expect_bool_lane_layout_refusal(module: &TrustIrModule, surface: &str, location: &str) {
    match translate_single(module) {
        Err(AdapterError::BoolLaneLayoutNotAdmitted {
            ty, location: got, ..
        }) => {
            assert_eq!(
                ty,
                Ty::Vector(Box::new(Ty::Bool), 8),
                "{surface}: refused type"
            );
            assert_eq!(got, location, "{surface}: location");
        }
        other => panic!("{surface} must fail closed by name: {other:?}"),
    }
}

/// `mask = <8 x i16> sge (load p0), (load p1)` followed by `tail(mask)`.
fn bool_mask_memory_module(name: &str, returns: Vec<Ty>, tail: Vec<InstrNode>) -> TrustIrModule {
    let v8i16 = Ty::Vector(Box::new(Ty::I16), 8);
    let mut body = vec![
        InstrNode::new(Inst::Load {
            ty: v8i16.clone(),
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(v(3)),
        InstrNode::new(Inst::Load {
            ty: v8i16.clone(),
            ptr: v(1),
            volatile: false,
            align: None,
        })
        .with_result(v(4)),
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sge,
            ty: v8i16,
            lhs: v(3),
            rhs: v(4),
        })
        .with_result(v(5)),
    ];
    body.extend(tail);
    module_with_blocks(
        name,
        vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
        returns,
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr), (v(2), Ty::Ptr)],
            body,
        }],
    )
}

fn check_store_bool_mask_fail_closed() {
    expect_bool_lane_layout_refusal(
        &bool_mask_memory_module(
            "manifest_store_bool_mask",
            vec![],
            vec![
                InstrNode::new(Inst::Store {
                    ty: Ty::Vector(Box::new(Ty::Bool), 8),
                    ptr: v(2),
                    value: v(5),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        ),
        "Inst::Store of a <N x bool> logical mask",
        "Store",
    );
}

fn check_load_bool_mask_fail_closed() {
    let mask_ty = Ty::Vector(Box::new(Ty::Bool), 8);
    expect_bool_lane_layout_refusal(
        &single_inst_module(
            "manifest_load_bool_mask",
            vec![(v(0), Ty::Ptr)],
            vec![mask_ty.clone()],
            InstrNode::new(Inst::Load {
                ty: mask_ty,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
            vec![v(1)],
        ),
        "Inst::Load of a <N x bool> logical mask",
        "Load",
    );
}

fn check_alloca_bool_mask_fail_closed() {
    expect_bool_lane_layout_refusal(
        &single_inst_module(
            "manifest_alloca_bool_mask",
            vec![],
            vec![Ty::Ptr],
            InstrNode::new(Inst::Alloca {
                ty: Ty::Vector(Box::new(Ty::Bool), 8),
                count: None,
                align: None,
            })
            .with_result(v(0)),
            vec![v(0)],
        ),
        "Inst::Alloca of a <N x bool> logical mask",
        "Alloca",
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

fn check_transmute_equal_size_supported() {
    // An equal-size scalar pair stays in registers: one carrier is a `Copy`,
    // an integer/float pair a `Bitcast`.
    for (name, src_ty, dst_ty, bitcast) in [
        ("manifest_transmute_i64_u64", Ty::I64, Ty::U64, false),
        ("manifest_transmute_u64_ptr", Ty::U64, Ty::Ptr, false),
        ("manifest_transmute_i64_f64", Ty::I64, Ty::F64, true),
        ("manifest_transmute_f32_u32", Ty::F32, Ty::U32, true),
    ] {
        let func = expect_supported(
            &cast_module_typed(name, CastOp::Transmute, src_ty, dst_ty),
            "equal-size scalar Transmute",
        );
        let entry = &func.blocks[&func.entry_block];
        let expected = entry.instructions.iter().any(|inst| {
            if bitcast {
                matches!(inst.opcode, Opcode::Bitcast { .. })
            } else {
                matches!(inst.opcode, Opcode::Copy)
            }
        });
        assert!(
            expected,
            "{name}: unexpected lowering {:?}",
            entry.instructions
        );
    }
    // A vector or an aggregate goes through the memory lane: the source image
    // is stored (or copied) into a slot and the destination read back.
    let module = cast_module_typed(
        "manifest_transmute_u128_vector",
        CastOp::Transmute,
        Ty::U128,
        Ty::Vector(Box::new(Ty::I32), 4),
    );
    let func = expect_supported(&module, "u128 -> <4 x i32> Transmute");
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Store { .. }))
            && entry
                .instructions
                .iter()
                .any(|inst| matches!(inst.opcode, Opcode::Load { .. })),
        "a vector Transmute must lower as a store/load pair: {:?}",
        entry.instructions
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

fn check_transmute_validity_leaf_fail_closed() {
    for (name, src_ty, dst_ty, leaf) in [
        (
            "manifest_transmute_u32_char",
            Ty::U32,
            Ty::Char,
            "reaches Char",
        ),
        (
            "manifest_transmute_u64_ref",
            Ty::U64,
            Ty::Ref(Box::new(Ty::U64)),
            "reaches Ref",
        ),
    ] {
        let err = translate_single(&cast_module_typed(name, CastOp::Transmute, src_ty, dst_ty))
            .expect_err("a Transmute into a validity-carrying leaf must fail closed");
        expect_fail_closed_all(
            err,
            DiagnosticClass::UnsupportedInstruction,
            &["CastOp::Transmute fail-closed", leaf, "validity invariant"],
        );
    }
}

fn check_transmute_source_padding_fail_closed() {
    let mut module = cast_module_typed(
        "manifest_transmute_padded_source",
        CastOp::Transmute,
        Ty::Struct(StructId::new(0)),
        Ty::U64,
    );
    module.add_struct(trust_ir::StructDef {
        origin: None,
        id: StructId::new(0),
        name: "ManifestPadded".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::U8,
                offset: Some(0),
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::U32,
                offset: Some(4),
            },
        ],
        size: Some(8),
        align: Some(4),
        repr: trust_ir::StructRepr::C,
    });
    let err =
        translate_single(&module).expect_err("a Transmute of a padded source must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["CastOp::Transmute fail-closed", "3 padding byte(s)"],
    );
}

fn make_aggregate_module(
    name: &str,
    ty: Ty,
    variant: Option<u32>,
    lanes: Vec<Ty>,
) -> TrustIrModule {
    let params: Vec<(ValueId, Ty)> = lanes
        .iter()
        .enumerate()
        .map(|(index, lane)| (v(index as u32), lane.clone()))
        .collect();
    let result = v(lanes.len() as u32);
    single_inst_module(
        name,
        params.clone(),
        vec![ty.clone()],
        InstrNode::new(Inst::MakeAggregate {
            ty,
            variant,
            fields: params.iter().map(|(value, _)| *value).collect(),
        })
        .with_result(result),
        vec![result],
    )
}

/// `f(x: u32, i: u64) -> u32 { [x; n][i] }`.
fn array_splat_module(ty: Ty) -> TrustIrModule {
    let mut module = module_with_blocks(
        "manifest_array_splat",
        vec![Ty::U32, Ty::U64],
        vec![Ty::U32],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::U32), (v(1), Ty::U64)],
            body: vec![
                InstrNode::new(Inst::ArraySplat { ty, value: v(0) }).with_result(v(2)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::U32,
                    array: v(2),
                    index: v(1),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    );
    module
        .add_type(Ty::U32)
        .expect("Module::add_type: test fixture");
    module
}

fn bulk_op_count(func: &trust_cg_lower::function::Function) -> (usize, usize, usize) {
    let insts = func.blocks.values().flat_map(|block| &block.instructions);
    insts.fold((0, 0, 0), |(stores, sets, copies), inst| {
        match inst.opcode {
            Opcode::Store { .. } => (stores + 1, sets, copies),
            Opcode::Memset => (stores, sets + 1, copies),
            Opcode::Memcpy => (stores, sets, copies + 1),
            _ => (stores, sets, copies),
        }
    })
}

fn check_array_splat_supported() {
    // One store and ceil(log2 n) doubling copies, never a store per lane.
    for (n, copies) in [(2u64, 1usize), (1000, 10), ((1 << 30) - 1, 30)] {
        let func = expect_supported(
            &array_splat_module(Ty::Array(TyId::new(0), n)),
            "Inst::ArraySplat",
        );
        assert_eq!(bulk_op_count(&func), (1, 0, copies), "[u32; {n}]");
    }
}

fn check_array_splat_non_array_fail_closed() {
    let err = translate_single(&array_splat_module(Ty::U32))
        .expect_err("Inst::ArraySplat at u32 must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Inst::ArraySplat", "not an array"],
    );
}

fn check_splat_constant_supported() {
    let splat_module = |value: Constant, n: u64| {
        let mut module = module_with_blocks(
            "manifest_splat_constant",
            vec![Ty::U64],
            vec![Ty::U32],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::U64)],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::Array(TyId::new(0), n),
                        value: Constant::Splat {
                            elem: Box::new(value),
                            len: n,
                        },
                    })
                    .with_result(v(1)),
                    InstrNode::new(Inst::ExtractElement {
                        ty: Ty::U32,
                        array: v(1),
                        index: v(0),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Return { values: vec![v(2)] }),
                ],
            }],
        );
        module
            .add_type(Ty::U32)
            .expect("Module::add_type: test fixture");
        module
    };
    for n in [2u64, (1 << 30) - 1] {
        // A byte-uniform element is one memset; any other one lane write and
        // the doubling copy.
        let zero = expect_supported(&splat_module(Constant::Int(0), n), "Constant::Splat zero");
        assert_eq!(bulk_op_count(&zero), (0, 1, 0), "[0u32; {n}]");
        let one = expect_supported(&splat_module(Constant::Int(1), n), "Constant::Splat one");
        let copies = (64 - (n - 1).leading_zeros()) as usize;
        assert_eq!(bulk_op_count(&one), (1, 0, copies), "[1u32; {n}]");
    }
}

fn check_make_aggregate_supported() {
    let mut module = make_aggregate_module(
        "manifest_make_struct",
        Ty::Struct(StructId::new(0)),
        None,
        vec![Ty::U8, Ty::U64],
    );
    module.add_struct(trust_ir::StructDef {
        origin: None,
        id: StructId::new(0),
        name: "ManifestPair".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::U8,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: trust_ir::StructRepr::C,
    });
    let func = expect_supported(&module, "Inst::MakeAggregate struct");
    let stores = func.blocks[&func.entry_block]
        .instructions
        .iter()
        .filter(|inst| matches!(inst.opcode, Opcode::Store { .. }))
        .count();
    assert_eq!(stores, 2, "one Store per scalar lane");
    expect_supported(
        &make_aggregate_module(
            "manifest_make_tuple",
            Ty::Tuple(vec![Ty::I32, Ty::F64]),
            None,
            vec![Ty::I32, Ty::F64],
        ),
        "Inst::MakeAggregate tuple",
    );
    let mut array = make_aggregate_module(
        "manifest_make_array",
        Ty::Array(TyId::new(0), 3),
        None,
        vec![Ty::I16, Ty::I16, Ty::I16],
    );
    array
        .add_type(Ty::I16)
        .expect("Module::add_type: test fixture");
    expect_supported(&array, "Inst::MakeAggregate array");
    let mut record = make_aggregate_module(
        "manifest_make_record",
        Ty::Record(RecordId::new(0)),
        None,
        vec![Ty::I64, Ty::I32],
    );
    record.add_record(RecordDef {
        id: RecordId::new(0),
        name: "ManifestPoint".to_string(),
        fields: vec![
            FieldDef {
                name: "x".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "y".to_string(),
                ty: Ty::I32,
                offset: None,
            },
        ],
    });
    expect_supported(&record, "Inst::MakeAggregate record");
}

fn check_make_aggregate_enum_supported() {
    let mut module = make_aggregate_module(
        "manifest_make_enum",
        Ty::Enum(EnumId::new(0)),
        Some(1),
        vec![Ty::U32],
    );
    module.add_enum(trust_ir::EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "ManifestChoice".to_string(),
        variants: vec![
            trust_ir::EnumVariant {
                name: "Empty".to_string(),
                fields: vec![],
                field_names: vec![],
            },
            trust_ir::EnumVariant {
                name: "Full".to_string(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
        ],
        discriminants: vec![],
        repr: None,
        layout: None,
    });
    expect_supported(&module, "Inst::MakeAggregate direct-tag enum variant");
    // Runtime raw integers/pointers state no nonreserved niche domain.
    let mut unknown = make_aggregate_module(
        "manifest_make_unknown_niche",
        Ty::Enum(EnumId::new(0)),
        Some(1),
        vec![Ty::Ptr],
    );
    let mut def = module.enums[0].clone();
    def.variants[1].fields = vec![Ty::Ptr];
    def.layout = Some(trust_ir::ty::EnumLayoutDescriptor {
        encoding: trust_ir::ty::EnumTagEncoding::Niche {
            untagged_variant: 1,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: trust_ir::ty::EnumTagRepr::U64,
        },
        size: 8,
        align: 8,
        variant_field_offsets: vec![vec![], vec![0]],
    });
    unknown.add_enum(def);
    let err = translate_single(&unknown).expect_err("raw niche domain must stay refused");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["Inst::MakeAggregate", "no typed nonreserved"],
    );
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
    let funcs = permit_translate_module(&reify_materialized_fndef_module(
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

/// `phantomdata` is trust-ir's one spelling of `()`'s value. Typed admission
/// refuses the empty aggregate at `()`, so the adapter lowers `phantomdata`
/// there as the zero-sized value `{ }` lowered to; at any other type it is no
/// constant of that type and is refused by TrustIR's typed admission
/// (`canonical_constants::phantom_subject` pins that negative exactly).
fn check_phantom_unit_constant_supported() {
    expect_supported(
        &canonical_constants::phantom_subject("manifest_phantom_const"),
        "Constant::PhantomData at Ty::Unit",
    );
}

/// trust-ir v47-v49: every entry refuses these by the construct's own name
/// (`AdapterError::UnmodeledTrustIrConstruct`), on the shared floor.
fn expect_unmodeled(err: AdapterError, expected: &str) {
    match err {
        AdapterError::UnmodeledTrustIrConstruct { construct, .. } => {
            assert_eq!(
                construct, expected,
                "refused under another construct's name"
            )
        }
        other => panic!("expected UnmodeledTrustIrConstruct {{ {expected} }}, got {other:?}"),
    }
}

fn check_runtime_closure_fail_closed() {
    let module = runtime_closure::runtime_closure_module(true);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let error = reject_unconsumed_v41_target_neutral_surface(&module).unwrap_err();
    assert!(matches!(
        error,
        AdapterError::UnmodeledTrustIrConstruct {
            construct: "Inst::MakeClosure",
            ..
        }
    ));
    assert!(error.to_string().contains("runtime closure ABI"));
}

fn check_drop_fail_closed() {
    // Since trust-ir v55 a drop of a trivially droppable type is not the one
    // spelling of a drop (trust-ir's own verdict refuses it first): drop a
    // struct, unresolved (no drop-glue row) and then resolved.
    let mut module = single_inst_module(
        "manifest_drop",
        vec![(v(0), Ty::Ptr)],
        vec![],
        InstrNode::new(Inst::Drop {
            ty: Ty::Struct(StructId::new(0)),
            ptr: v(0),
        }),
        vec![],
    );
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "ManifestOwner".to_string(),
        fields: vec![FieldDef {
            name: "handle".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::default(),
    });
    let err = translate_single(&module)
        .expect_err("a drop runs a destructor this backend does not model");
    expect_unmodeled(err, "Inst::Drop");
    let glue_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut glue = TrustIrFunction::new(FuncId::new(1), "manifest_owner_drop", glue_ty, b(0));
    glue.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    module
        .try_add_function(glue)
        .expect("Module::try_add_function: test fixture");
    module
        .set_drop_glue(Ty::Struct(StructId::new(0)), FuncId::new(1))
        .expect("one row for one type and one glue");
    let err = translate_single(&module).expect_err("a RESOLVED drop is refused too");
    expect_unmodeled(err, "Inst::Drop");
}

/// v53: a non-propagating call boundary, direct and indirect. Refused by name
/// on the shared floor (every lane, before any transform) and again at the
/// lowering arm, so no entry lowers it as an ordinary call.
fn call_unwind_boundary_modules() -> [(&'static str, TrustIrModule); 2] {
    [
        (
            "Inst::CallCannotUnwind",
            single_inst_module(
                "manifest_call_cannot_unwind",
                vec![(v(0), Ty::Ptr)],
                vec![],
                InstrNode::new(Inst::CallCannotUnwind {
                    callee: FuncId::new(0),
                    args: vec![v(0)],
                }),
                vec![],
            ),
        ),
        (
            "Inst::CallIndirectCannotUnwind",
            single_inst_module(
                "manifest_call_indirect_cannot_unwind",
                vec![(v(0), Ty::Ptr)],
                vec![],
                InstrNode::new(Inst::CallIndirectCannotUnwind {
                    callee: v(0),
                    sig: FuncTyId::new(0),
                    args: vec![v(0)],
                    calling_conv: CallingConv::default(),
                }),
                vec![],
            ),
        ),
    ]
}

fn check_call_unwind_boundary_fail_closed(construct: &str) {
    let (_, module) = call_unwind_boundary_modules()
        .into_iter()
        .find(|(name, _)| *name == construct)
        .expect("a v53 boundary construct");
    match reject_unconsumed_v41_target_neutral_surface(&module)
        .expect_err("the shared floor refuses a non-propagating call boundary")
    {
        AdapterError::UnmodeledTrustIrConstruct {
            location,
            construct: refused,
            reason,
        } => {
            assert_eq!(refused, construct, "refused under another construct's name");
            assert!(
                location.contains("bb0"),
                "not the floor's refusal: {location}"
            );
            assert!(reason.contains("unwind"), "{reason}");
        }
        other => panic!("expected the floor's UnmodeledTrustIrConstruct, got {other:?}"),
    }
    let err = translate_single(&module)
        .expect_err("the lowering arm refuses a non-propagating call boundary");
    expect_unmodeled(err, construct);
}

fn check_call_cannot_unwind_fail_closed() {
    check_call_unwind_boundary_fail_closed("Inst::CallCannotUnwind");
}

fn check_call_indirect_cannot_unwind_fail_closed() {
    check_call_unwind_boundary_fail_closed("Inst::CallIndirectCannotUnwind");
}

/// v54 (amendment P): `blocks` as function `f(0)` taking `(bool, ptr)`, plus
/// the panic entry `f(1)`, a `(ptr) -> ()` definition that never returns.
fn panic_site_module(name: &str, blocks: Vec<TrustIrBlock>) -> TrustIrModule {
    let mut module = module_with_blocks(name, vec![Ty::Bool, Ty::Ptr], vec![], blocks);
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = TrustIrFunction::new(f(1), "panic_const_div_by_zero", ty, b(0));
    entry.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr)],
        body: vec![InstrNode::new(Inst::Unreachable)],
    }];
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");
    module
}

fn manifest_panic_site() -> trust_ir::PanicSite {
    trust_ir::PanicSite {
        entry: f(1),
        location: trust_ir::PanicLocation::Value(v(1)),
    }
}

fn sited_assert_module(kind: trust_ir::AssertKind, sited: bool) -> TrustIrModule {
    panic_site_module(
        "manifest_sited_assert",
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Bool), (v(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Assert {
                    cond: v(0),
                    kind,
                    site: sited.then(manifest_panic_site),
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    )
}

fn assert_invoke_module() -> TrustIrModule {
    panic_site_module(
        "manifest_assert_invoke",
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::Bool), (v(1), Ty::Ptr)],
                body: vec![InstrNode::new(Inst::AssertInvoke {
                    cond: v(0),
                    kind: trust_ir::AssertKind::DivByZero,
                    site: manifest_panic_site(),
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
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
                body: vec![
                    InstrNode::new(Inst::LandingPad {
                        is_cleanup: true,
                        catch_type_indices: vec![],
                    })
                    .with_results([v(2), v(3)]),
                    InstrNode::new(Inst::Resume { exn: v(2) }),
                ],
            },
        ],
    )
}

/// Precision migration of the unchanged v54 fixtures: native delivery gains a
/// real failure call; missing sites and invalid entries still fail closed.
fn check_panic_site_fail_closed(module: &TrustIrModule, construct: &str) {
    let original = module.clone();
    reject_unconsumed_v41_target_neutral_surface(module).expect("sited native floor");
    let lir = translate_single(module).expect("actual entry/location call lowering");
    use trust_cg_lower::instructions::Opcode;
    assert_eq!(
        lir.blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Call { .. } | Opcode::Invoke { .. }))
            .count(),
        1
    );
    assert!(
        lir.blocks
            .values()
            .flat_map(|b| &b.instructions)
            .any(|i| matches!(i.opcode, Opcode::Brif { .. })),
        "{construct}"
    );
    assert!(
        lir.blocks
            .values()
            .flat_map(|b| &b.instructions)
            .any(|i| matches!(i.opcode, Opcode::Trap)),
        "returning entry remains terminal"
    );
    assert_eq!(module, &original);
    let mut invalid = module.clone();
    invalid.functions[1].name = invalid.functions[0].name.clone();
    assert!(
        translate_single(&invalid).is_err(),
        "ambiguous entry must refuse"
    );
}

fn check_sited_assert_fail_closed() {
    check_panic_site_fail_closed(
        &sited_assert_module(trust_ir::AssertKind::DivByZero, true),
        "Inst::Assert { site: Some(_) }",
    );
    // The neighbour: the SAME check without its site is refused by its kind
    // (the v52 runtime refusal), never under the site's name.
    match translate_single(&sited_assert_module(trust_ir::AssertKind::DivByZero, false))
        .expect_err("an unsited stated-kind check still refuses")
    {
        AdapterError::AssertPanicUnsupported { kind, .. } => {
            assert_eq!(kind, trust_ir::AssertKind::DivByZero)
        }
        other => panic!("expected AssertPanicUnsupported, got {other:?}"),
    }
}

fn check_assert_invoke_fail_closed() {
    check_panic_site_fail_closed(&assert_invoke_module(), "Inst::AssertInvoke");
}

/// v55 / v56 (amendment D): a one-terminator entry block whose unwind edge
/// enters a cleanup pad that re-raises.
fn unwinding_twin_module(name: &str, terminator: Inst) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let entry_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(FuncId::new(0), name, entry_ty, b(0));
    function.blocks = vec![
        TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![InstrNode::new(terminator)],
        },
        TrustIrBlock {
            id: b(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        },
        TrustIrBlock {
            id: b(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results([v(1), v(2)]),
                InstrNode::new(Inst::Resume { exn: v(1) }),
            ],
        },
    ];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

/// v55: a drop with an unwind edge, at a type the module's drop-glue table
/// RESOLVES (struct.0, glue @func.1): the resolved drop is still refused.
fn drop_invoke_module() -> TrustIrModule {
    let mut module = unwinding_twin_module(
        "manifest_drop_invoke",
        Inst::DropInvoke {
            ty: Ty::Struct(StructId::new(0)),
            ptr: v(0),
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
    );
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "ManifestOwner".to_string(),
        fields: vec![FieldDef {
            name: "handle".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::default(),
    });
    let glue_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut glue = TrustIrFunction::new(FuncId::new(1), "manifest_owner_drop_glue", glue_ty, b(0));
    glue.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    module
        .try_add_function(glue)
        .expect("Module::try_add_function: test fixture");
    module
        .set_drop_glue(Ty::Struct(StructId::new(0)), FuncId::new(1))
        .expect("one row for one type and one glue");
    module
}

fn invoke_indirect_module() -> TrustIrModule {
    unwinding_twin_module(
        "manifest_invoke_indirect",
        Inst::InvokeIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![v(0)],
            calling_conv: CallingConv::default(),
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
    )
}

/// v55 / v56: refused BY NAME on the shared floor (every lane, before any
/// transform) and again at the lowering arm, so no entry lowers a drop as a
/// branch or an unwinding indirect call as an ordinary one.
fn check_unwinding_twin_fail_closed(module: &TrustIrModule, construct: &str, needle: &str) {
    match reject_unconsumed_v41_target_neutral_surface(module)
        .expect_err("the shared floor refuses a v55 / v56 unwinding twin")
    {
        AdapterError::UnmodeledTrustIrConstruct {
            location,
            construct: refused,
            reason,
        } => {
            assert_eq!(refused, construct, "refused under another construct's name");
            assert!(
                location.contains("bb0"),
                "not the floor's refusal: {location}"
            );
            assert!(reason.contains(needle), "{reason}");
        }
        other => panic!("expected the floor's UnmodeledTrustIrConstruct, got {other:?}"),
    }
    let err = translate_single(module).expect_err("the lowering arm refuses it too");
    expect_unmodeled(err, construct);
}

fn check_drop_invoke_fail_closed() {
    check_unwinding_twin_fail_closed(&drop_invoke_module(), "Inst::DropInvoke", "drop glue");
}

fn check_invoke_indirect_fail_closed() {
    check_unwinding_twin_fail_closed(
        &invoke_indirect_module(),
        "Inst::InvokeIndirect",
        "landing pad",
    );
}

fn check_weak_cmpxchg_fail_closed() {
    let err = translate_single(&single_inst_module(
        "manifest_weak_cmpxchg",
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![Ty::I64],
        InstrNode::new(Inst::CmpXchg {
            ty: Ty::I64,
            ptr: v(0),
            expected: v(1),
            desired: v(1),
            success: Ordering::SeqCst,
            failure: Ordering::SeqCst,
            weak: true,
        })
        .with_results([v(2), v(3)]),
        vec![v(2)],
    ))
    .expect_err("a weak compare-exchange may fail spuriously; no lane models that");
    expect_unmodeled(err, "Inst::CmpXchg { weak: true }");
}

fn check_uninit_lane_fail_closed() {
    let err = translate_single(&const_module(
        "manifest_uninit_lane",
        Ty::Tuple(vec![Ty::I64, Ty::I64]),
        Constant::Aggregate(vec![Constant::Int(1), Constant::Uninit]),
    ))
    .expect_err("an unwritten aggregate lane holds no value to materialize");
    expect_unmodeled(err, "Constant::Uninit");
}

fn check_fndef_unregistered_fail_closed() {
    canonical_constants::fndef_unregistered("manifest_fndef_unregistered");
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

fn check_switch_i128_selector_supported() {
    // L04-P10: a 128-bit selector is split into its 64-bit halves and
    // dispatched on both, so the lowered function keeps a 64-bit `Switch`
    // leaf and no 128-bit selector survives.
    let module = switch_module(
        "manifest_switch_i128_selector",
        Ty::I128,
        vec![SwitchCase {
            value: Constant::Int(1),
            target: b(2),
            args: vec![],
        }],
    );
    let func = expect_supported(&module, "Inst::Switch (I128 selector)");
    let switches: Vec<&Opcode> = func
        .blocks
        .values()
        .flat_map(|block| block.instructions.iter().map(|inst| &inst.opcode))
        .filter(|opcode| matches!(opcode, Opcode::Switch { .. }))
        .collect();
    assert!(
        !switches.is_empty(),
        "the split dispatch keeps a 64-bit Switch leaf: {:?}",
        func.blocks
    );
}

fn check_switch_duplicate_normalized_case_fail_closed() {
    let malformed = switch_module(
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
    );
    canonical_constants::assert_refused(
        &malformed,
        &[(
            "function 'manifest_switch_duplicate_normalized_case' bb0 switch case 1",
            "i8",
            "int",
        )],
    );
    // I8 cannot spell 255. Keep that negative above; a genuine duplicate
    // normalized case uses two valid -1 source constants, not a byte alias.
    let mut duplicate = malformed;
    let Inst::Switch { cases, .. } = &mut duplicate.functions[0].blocks[0].body[0].inst else {
        panic!("the retained source is a Switch");
    };
    cases[1].value = Constant::Int(-1);
    let err = translate_single(&duplicate)
        .expect_err("duplicate normalized switch cases must fail closed");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedInstruction,
        "duplicate switch case value after 8-bit selector normalization",
    );
}

fn check_switch_non_integer_case_fail_closed() {
    let malformed = switch_module(
        "manifest_switch_non_integer_case",
        Ty::I32,
        vec![SwitchCase {
            value: Constant::Float(1.0),
            target: b(2),
            args: vec![],
        }],
    );
    canonical_constants::assert_refused(
        &malformed,
        &[(
            "function 'manifest_switch_non_integer_case' bb0 switch case 0",
            "i32",
            "float",
        )],
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
    let caller_ty = module
        .add_func_type(FuncTy {
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
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let callee_ty = module
        .add_func_type(FuncTy {
            params: callee_params,
            returns: callee_returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

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

    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
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
    permit_translate_module(&module)
        .expect("registered direct-call module must be type-valid end to end");
}

/// Actual zero-result call shapes with no EH metadata. Every operand and target
/// signature is declared; the indirect callee is a dynamic function parameter.
/// The constant-false branch threads real operands into a CFG-reachable,
/// statically nonexecuted call block rather than an invalid disconnected block.
/// This validation fixture establishes typing, not host-unwind enforcement.
fn call_boundary_module(indirect: bool, nonexecuted: bool) -> TrustIrModule {
    let mut module = TrustIrModule::new("manifest_call_boundary");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let signature = FuncTyId::new(1);
    let parameters = if indirect {
        vec![Ty::Func(signature), Ty::I64]
    } else {
        vec![Ty::I64]
    };
    let caller_signature = module
        .add_func_type(FuncTy {
            params: parameters.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert_eq!(
        module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture"),
        signature
    );
    let parameters_for = |base| {
        parameters
            .iter()
            .enumerate()
            .map(|(index, ty)| (v(base + index as u32), ty.clone()))
            .collect()
    };
    let call_for = |base| {
        if indirect {
            Inst::CallIndirectCannotUnwind {
                callee: v(base),
                sig: signature,
                args: vec![v(base + 1)],
                calling_conv: CallingConv::C,
            }
        } else {
            Inst::CallCannotUnwind {
                callee: f(1),
                args: vec![v(base)],
            }
        }
    };
    let mut caller = TrustIrFunction::new(f(0), "manifest_call_boundary", caller_signature, b(0));
    caller.calling_conv = CallingConv::C;
    let mut entry = TrustIrBlock {
        id: b(0),
        params: parameters_for(0),
        body: vec![],
    };
    if nonexecuted {
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            })
            .with_result(v(2)),
        );
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: v(2),
            then_target: b(1),
            then_args: (0..parameters.len()).map(|index| v(index as u32)).collect(),
            else_target: b(2),
            else_args: vec![],
        }));
    } else {
        entry.body.push(InstrNode::new(call_for(0)));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
    }
    caller.blocks.push(entry);
    if nonexecuted {
        caller.blocks.push(TrustIrBlock {
            id: b(1),
            params: parameters_for(4),
            body: vec![
                InstrNode::new(call_for(4)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        });
        caller.blocks.push(TrustIrBlock {
            id: b(2),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        });
    }
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    let mut callee = TrustIrFunction::new(f(1), "boundary_target", signature, b(0));
    callee.calling_conv = CallingConv::C;
    callee.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    });
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "boundary fixture is invalid: {errors:?}");
    module
}

fn check_validated_call_boundary_fail_closed(indirect: bool) {
    let expected = if indirect {
        "Inst::CallIndirectCannotUnwind"
    } else {
        "Inst::CallCannotUnwind"
    };
    for nonexecuted in [false, true] {
        let module = call_boundary_module(indirect, nonexecuted);
        for result in [
            translate_single(&module).map(|_| ()),
            permit_translate_module(&module).map(|_| ()),
        ] {
            let error =
                result.expect_err("a boundary with no EH must still be enforced or refused");
            match error {
                AdapterError::UnmodeledTrustIrConstruct {
                    construct, reason, ..
                } => {
                    assert_eq!(construct, expected, "refused under the wrong constructor");
                    assert!(reason.contains("non-propagating call boundary"), "{reason}");
                }
                other => panic!("expected the actual boundary floor for {expected}, got {other:?}"),
            }
        }
    }
}

fn check_validated_call_cannot_unwind_fail_closed() {
    check_validated_call_boundary_fail_closed(false);
}

fn check_validated_call_indirect_cannot_unwind_fail_closed() {
    check_validated_call_boundary_fail_closed(true);
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
    let sig = module
        .add_func_type(FuncTy {
            params: sig_params,
            returns: sig_returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
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
    let sig = module
        .add_func_type(FuncTy {
            params: vec![agg.clone()],
            returns: vec![agg],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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

/// Borrows lower as value-preserving copies of the borrowed address
/// (trust-ir `interpret.rs`: the result IS the operand pointer), with each
/// borrow's root and kind and each `EndBorrow` recorded in the function's
/// legalization receipt. A unique borrow, a shared reborrow of it and a
/// shared borrow of the root all record the parameter as their root.
fn check_borrow_insts_supported() {
    let module = module_with_blocks(
        "manifest_borrows",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
                InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }),
                InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(2)),
                InstrNode::new(Inst::Borrow { ptr: v(2) }).with_result(v(3)),
                InstrNode::new(Inst::EndBorrow { borrow_ptr: v(3) }),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );
    let (func, proofs) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap_or_else(|err| panic!("borrows must lower: {err:?}"));
    let copies = func.blocks[&func.entry_block]
        .instructions
        .iter()
        .filter(|inst| matches!(inst.opcode, Opcode::Copy))
        .count();
    assert_eq!(copies, 3, "each borrow is one value-preserving LIR copy");
    let receipt = &proofs.borrow_frame_undef;
    assert_eq!(receipt.borrows.len(), 3);
    assert_eq!(receipt.retired_borrows.len(), 2);
    assert!(
        receipt.borrows.iter().all(|borrow| borrow.root == v(0)),
        "every borrow records the parameter as its root: {receipt:?}"
    );
}

fn expect_legalization_refused(surface: &str, module: &TrustIrModule, needles: &[&str]) {
    let err = translate_single(module).unwrap_err_or_else(surface);
    expect_fail_closed_all(err, DiagnosticClass::Legalization, needles);
}

fn check_borrow_mut_through_shared_borrow_fail_closed() {
    let module = module_with_blocks(
        "manifest_borrow_mut_of_shared",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
                InstrNode::new(Inst::BorrowMut { ptr: v(1) }).with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );
    expect_legalization_refused(
        "BorrowMut through a shared Borrow",
        &module,
        &["Inst::BorrowMut", "BorrowMutThroughSharedRef"],
    );
}

fn check_borrow_of_non_pointer_fail_closed() {
    expect_legalization_refused(
        "Borrow of a non-pointer",
        &single_inst_module(
            "manifest_borrow_non_pointer",
            vec![(v(0), Ty::I64)],
            vec![Ty::Ptr],
            InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
            vec![v(1)],
        ),
        &["Inst::Borrow", "non-addressable"],
    );
}

fn check_end_borrow_of_non_borrow_fail_closed() {
    expect_legalization_refused(
        "EndBorrow of a non-borrow",
        &single_inst_module(
            "manifest_end_borrow_non_borrow",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::EndBorrow { borrow_ptr: v(0) }),
            vec![],
        ),
        &["Inst::EndBorrow", "EndBorrowOfNonBorrow"],
    );
}

/// A borrow of a FAT pointer is the same value-preserving copy as a thin
/// one (trust-ir `interpret.rs`: a fat pointee is passed through verbatim,
/// both lanes untouched): one LIR `Copy` of the whole fat carrier, typed as
/// the fat pointer's carrier, recorded with the parameter as its root.
fn check_borrow_fat_pointer_supported() {
    let fat = Ty::FatPtr(FatPtrKind::Str);
    let module = module_with_blocks(
        "manifest_borrow_fat",
        vec![fat.clone()],
        vec![Ty::Ptr],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), fat.clone())],
            body: vec![
                InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
                InstrNode::new(Inst::PtrData {
                    ptr_ty: fat.clone(),
                    ptr: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );
    let (func, proofs) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap_or_else(|err| panic!("a fat-pointer borrow must lower: {err:?}"));
    let receipt = &proofs.borrow_frame_undef;
    let [borrow] = receipt.borrows.as_slice() else {
        panic!("one borrow record expected: {receipt:?}")
    };
    assert_eq!(borrow.root, v(0));
    assert_eq!(receipt.retired_borrows.len(), 1);
    assert!(
        func.blocks[&func.entry_block]
            .instructions
            .iter()
            .any(|inst| {
                matches!(inst.opcode, Opcode::Copy)
                    && inst.args == [borrow.operand]
                    && inst.results == [borrow.result]
            }),
        "the fat borrow is one Copy of the operand"
    );
    assert_eq!(
        func.value_types.get(&borrow.result),
        Some(&translate_type(&fat).expect("fat carrier")),
        "the borrow result keeps the fat pointer's carrier"
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
    let rc_void = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let rc_flag = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::U8],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(TrustIrFunction::new(f(0), "clean_inc", rc_void, b(0)))
        .expect("Module::try_add_function: test fixture");
    module
        .try_add_function(TrustIrFunction::new(f(1), "clean_dec", rc_void, b(0)))
        .expect("Module::try_add_function: test fixture");
    module
        .try_add_function(TrustIrFunction::new(
            f(2),
            "clean_is_exclusive",
            rc_flag,
            b(0),
        ))
        .expect("Module::try_add_function: test fixture");
    let body_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
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
    trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
        .map(|(func, _proofs)| func)
}

/// The lowered instructions of the (single) entry block of a translated body.
fn entry_instructions(func: &trust_cg_lower::function::Function) -> &[Instruction] {
    &func.blocks[&func.entry_block].instructions
}

/// Count entry-block calls to the runtime symbol `name`.
fn count_calls(insns: &[Instruction], name: &str) -> usize {
    insns
        .iter()
        .filter(|inst| matches!(&inst.opcode, Opcode::Call { name: n, .. } if n == name))
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
        .filter(|inst| matches!(&inst.opcode, Opcode::Call { name, .. } if name == symbol))
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
            |inst| matches!(&inst.opcode, Opcode::Call { name, .. } if name == "clean_is_exclusive"),
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

/// The refusal every `Inst::Dealloc` gets (G18-1, re-decided 2026-09-27):
/// the named `[TCG-DEALLOC]` diagnostic citing trust-ir's own verdict.
const DEALLOC_REFUSAL: &[&str] = &["[TCG-DEALLOC]", "UnlowerableForCodegen"];

fn check_dealloc_fail_closed() {
    // TrustIR `Dealloc` carries no allocator origin or layout. trust-ir
    // refuses every one for codegen in every body, and so does this backend.
    let err = translate_single(&single_inst_module(
        "manifest_dealloc",
        vec![(v(0), Ty::Ptr)],
        vec![],
        InstrNode::new(Inst::Dealloc { ptr: v(0) }),
        vec![],
    ))
    .expect_err("Inst::Dealloc must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        DEALLOC_REFUSAL,
    );
}

/// `HeapAlloc { U64, origin }` immediately freed by `Dealloc`.
fn heap_alloc_dealloc_module(
    name: &str,
    first: AllocOrigin,
    second: Option<AllocOrigin>,
) -> TrustIrModule {
    heap_alloc_module(name, first, second, true)
}

/// `HeapAlloc { U64, origin }` (a second origin behind a `Select`), freed by
/// `Dealloc` when `dealloc`.
fn heap_alloc_module(
    name: &str,
    first: AllocOrigin,
    second: Option<AllocOrigin>,
    dealloc: bool,
) -> TrustIrModule {
    let mut body = vec![
        InstrNode::new(Inst::HeapAlloc {
            ty: Ty::U64,
            count: None,
            align: None,
            origin: first,
        })
        .with_result(v(1)),
    ];
    let mut freed = v(1);
    if let Some(second) = second {
        body.push(
            InstrNode::new(Inst::HeapAlloc {
                ty: Ty::U64,
                count: None,
                align: None,
                origin: second,
            })
            .with_result(v(2)),
        );
        body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::Ptr,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(3)),
        );
        freed = v(3);
    }
    if dealloc {
        body.push(InstrNode::new(Inst::Dealloc { ptr: freed }));
    }
    body.push(InstrNode::new(Inst::Return { values: vec![] }));
    module_with_blocks(
        name,
        vec![Ty::Bool],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Bool)],
            body,
        }],
    )
}

/// The most resolvable shape there is — a `Dealloc` of the result of a
/// same-function `HeapAlloc` of one origin and one static layout, the shape
/// the retired provenance lowering (2887cbf01) emitted `__rust_dealloc` /
/// `free` for — is refused like every other (trust-ir SPEC "Deallocation is
/// refused for codegen, whatever its provenance").
fn check_dealloc_provenance_resolvable_fail_closed() {
    for (name, origin) in [
        ("manifest_dealloc_rust", AllocOrigin::RustHeap),
        ("manifest_dealloc_malloc", AllocOrigin::CMalloc),
    ] {
        let err = translate_single(&heap_alloc_dealloc_module(name, origin, None))
            .expect_err("a provenance-resolvable Dealloc must fail closed");
        expect_fail_closed_all(
            err,
            DiagnosticClass::UnsupportedInstruction,
            DEALLOC_REFUSAL,
        );
    }
}

fn check_dealloc_mixed_origins_fail_closed() {
    let err = translate_single(&heap_alloc_dealloc_module(
        "manifest_dealloc_mixed",
        AllocOrigin::RustHeap,
        Some(AllocOrigin::CMalloc),
    ))
    .expect_err("a Dealloc that may free memory of two allocators must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        DEALLOC_REFUSAL,
    );
}

fn check_dealloc_rc_heap_origins_fail_closed() {
    for (origin, needle) in [
        (AllocOrigin::SwiftHeap, "SwiftHeap"),
        (AllocOrigin::CleanHeap, "CleanHeap"),
    ] {
        // The HeapAlloc alone: a Dealloc beside it is refused first, by
        // trust-ir's verdict, whatever the origin.
        let err = translate_single(&heap_alloc_module(
            "manifest_heap_alloc_rc_heap",
            origin,
            None,
            false,
        ))
        .expect_err("Swift/Clean heap allocations have no modelled allocation path");
        expect_fail_closed(err, DiagnosticClass::UnsupportedInstruction, needle);
        let err = translate_single(&heap_alloc_dealloc_module(
            "manifest_dealloc_rc_heap",
            origin,
            None,
        ))
        .expect_err("a Dealloc of a Swift/Clean heap cell must fail closed");
        expect_fail_closed_all(
            err,
            DiagnosticClass::UnsupportedInstruction,
            DEALLOC_REFUSAL,
        );
    }
}

fn manifest_frame_def() -> BindingFrameDef {
    BindingFrameDef::new(
        BindingFrameId::new(0),
        "manifest_frame",
        vec![BindingSlot::new("slot", Ty::I64)],
    )
}

/// `(x: i64) -> i64 { f = open_frame {slot: I64}; f' = bind_slot f, 0, x;
/// r = load_slot f', 0; close_frame f'; ret r }`.
fn frame_program_module(name: &str) -> TrustIrModule {
    module_with_blocks(
        name,
        vec![Ty::I64],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::OpenFrame {
                    def: manifest_frame_def(),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::BindSlot {
                    frame: v(1),
                    slot: 0,
                    value: v(0),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::LoadSlot {
                    frame: v(2),
                    slot: 0,
                    ty: Ty::I64,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::CloseFrame { frame: v(2) }),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    )
}

fn frame_program_opcodes() -> Vec<Opcode> {
    let func = expect_supported(&frame_program_module("manifest_frame"), "binding frames");
    func.blocks[&func.entry_block]
        .instructions
        .iter()
        .map(|inst| inst.opcode.clone())
        .collect()
}

/// `OpenFrame` is one zero-filled stack slot laid out from the slot
/// carriers, recorded in the legalization receipt.
fn check_open_frame_supported() {
    let module = frame_program_module("manifest_open_frame");
    let (_, proofs) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap_or_else(|err| panic!("OpenFrame must lower: {err:?}"));
    let [frame] = proofs.borrow_frame_undef.frames.as_slice() else {
        panic!("one frame record expected: {:?}", proofs.borrow_frame_undef)
    };
    assert_eq!((frame.bytes, frame.align, frame.slots.len()), (8, 8, 1));
    assert!(
        frame_program_opcodes()
            .iter()
            .any(|opcode| matches!(opcode, Opcode::StackAddr { .. })),
        "OpenFrame materializes its stack slot"
    );
}

/// `BindSlot` stores in place (after the zero-fill store of `OpenFrame`).
fn check_bind_slot_supported() {
    let stores = frame_program_opcodes()
        .iter()
        .filter(|opcode| matches!(opcode, Opcode::Store { ty: Type::I64, .. }))
        .count();
    assert_eq!(stores, 2, "one zero-fill store and one bind store");
}

/// `LoadSlot` loads the slot's carrier.
fn check_load_slot_supported() {
    assert!(
        frame_program_opcodes()
            .iter()
            .any(|opcode| matches!(opcode, Opcode::Load { ty: Type::I64, .. })),
        "LoadSlot lowers to a typed load"
    );
}

fn check_bind_slot_of_non_frame_fail_closed() {
    expect_legalization_refused(
        "Inst::BindSlot of a value no OpenFrame produced",
        &single_inst_module(
            "manifest_bind_slot_non_frame",
            vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            vec![Ty::Ptr],
            InstrNode::new(Inst::BindSlot {
                frame: v(0),
                slot: 0,
                value: v(1),
            })
            .with_result(v(2)),
            vec![v(2)],
        ),
        &["Inst::BindSlot", "BindingFrameNotOpen"],
    );
}

fn check_load_slot_of_non_frame_fail_closed() {
    expect_legalization_refused(
        "Inst::LoadSlot of a value no OpenFrame produced",
        &single_inst_module(
            "manifest_load_slot_non_frame",
            vec![(v(0), Ty::Ptr)],
            vec![Ty::I64],
            InstrNode::new(Inst::LoadSlot {
                frame: v(0),
                slot: 0,
                ty: Ty::I64,
            })
            .with_result(v(1)),
            vec![v(1)],
        ),
        &["Inst::LoadSlot", "BindingFrameNotOpen"],
    );
}

/// In-place slot storage cannot honour trust-ir's functional `BindSlot` when
/// a superseded handle is read after the rebind: refused by name.
fn check_binding_frame_superseded_handle_fail_closed() {
    let module = module_with_blocks(
        "manifest_frame_superseded",
        vec![Ty::I64],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::OpenFrame {
                    def: manifest_frame_def(),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::BindSlot {
                    frame: v(1),
                    slot: 0,
                    value: v(0),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::BindSlot {
                    frame: v(2),
                    slot: 0,
                    value: v(0),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::LoadSlot {
                    frame: v(2),
                    slot: 0,
                    ty: Ty::I64,
                })
                .with_result(v(4)),
                InstrNode::new(Inst::CloseFrame { frame: v(3) }),
                InstrNode::new(Inst::Return { values: vec![v(4)] }),
            ],
        }],
    );
    expect_legalization_refused(
        "binding-frame handle live after a rebind",
        &module,
        &["Inst::BindSlot", "still live after"],
    );
}

fn check_binding_frame_escape_fail_closed() {
    let module = module_with_blocks(
        "manifest_frame_escape",
        vec![],
        vec![Ty::Ptr],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::OpenFrame {
                    def: manifest_frame_def(),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::CloseFrame { frame: v(0) }),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    expect_legalization_refused(
        "binding-frame handle escape",
        &module,
        &["Inst::OpenFrame", "escapes into Inst::Return"],
    );
}

fn check_binding_frame_non_scalar_slot_fail_closed() {
    let module = module_with_blocks(
        "manifest_frame_tuple_slot",
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::OpenFrame {
                    def: BindingFrameDef::new(
                        BindingFrameId::new(0),
                        "manifest_frame",
                        vec![BindingSlot::new("pair", Ty::Tuple(vec![Ty::I64, Ty::I64]))],
                    ),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::CloseFrame { frame: v(0) }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );
    expect_legalization_refused(
        "binding-frame non-scalar slot",
        &module,
        &["Inst::OpenFrame", "only scalar"],
    );
}

fn check_binding_frame_unclosed_fail_closed() {
    expect_legalization_refused(
        "binding frame never closed",
        &single_inst_module(
            "manifest_frame_unclosed",
            vec![],
            vec![],
            InstrNode::new(Inst::OpenFrame {
                def: manifest_frame_def(),
            })
            .with_result(v(0)),
            vec![],
        ),
        &["Inst::OpenFrame", "never closed"],
    );
}

/// The superseded handle is read in a SUCCESSOR block, so only liveness
/// seeded across the block edge sees it (trust-ir: `%4` reads `%0`, the
/// in-place slot would hold `%0 + %0`). Refused by name.
fn check_binding_frame_superseded_handle_across_blocks_fail_closed() {
    let module = module_with_blocks(
        "manifest_frame_superseded_across_blocks",
        vec![Ty::I64],
        vec![Ty::I64],
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::OpenFrame {
                        def: manifest_frame_def(),
                    })
                    .with_result(v(1)),
                    InstrNode::new(Inst::BindSlot {
                        frame: v(1),
                        slot: 0,
                        value: v(0),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: v(0),
                        rhs: v(0),
                    })
                    .with_result(v(5)),
                    InstrNode::new(Inst::BindSlot {
                        frame: v(2),
                        slot: 0,
                        value: v(5),
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Br {
                        target: b(1),
                        args: vec![],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::LoadSlot {
                        frame: v(2),
                        slot: 0,
                        ty: Ty::I64,
                    })
                    .with_result(v(4)),
                    InstrNode::new(Inst::CloseFrame { frame: v(3) }),
                    InstrNode::new(Inst::Return { values: vec![v(4)] }),
                ],
            },
        ],
    );
    expect_legalization_refused(
        "binding-frame handle live across a block edge after a rebind",
        &module,
        &["Inst::BindSlot", "still live after"],
    );
}

/// A slot bound on one `CondBr` arm only: after the merge it may be
/// unbound (poison in trust-ir), and returning it inspects it. Refused by
/// name, never compiled to the zero-filled slot.
fn check_binding_frame_partially_bound_slot_fail_closed() {
    let module = module_with_blocks(
        "manifest_frame_partially_bound",
        vec![Ty::Bool, Ty::I64],
        vec![Ty::I64],
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::Bool), (v(1), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::OpenFrame {
                        def: manifest_frame_def(),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::CondBr {
                        cond: v(0),
                        then_target: b(1),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::BindSlot {
                        frame: v(2),
                        slot: 0,
                        value: v(1),
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Br {
                        target: b(3),
                        args: vec![v(3)],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(2),
                params: vec![],
                body: vec![InstrNode::new(Inst::Br {
                    target: b(3),
                    args: vec![v(2)],
                })],
            },
            TrustIrBlock {
                id: b(3),
                params: vec![(v(4), Ty::Ptr)],
                body: vec![
                    InstrNode::new(Inst::LoadSlot {
                        frame: v(4),
                        slot: 0,
                        ty: Ty::I64,
                    })
                    .with_result(v(5)),
                    InstrNode::new(Inst::CloseFrame { frame: v(4) }),
                    InstrNode::new(Inst::Return { values: vec![v(5)] }),
                ],
            },
        ],
    );
    expect_legalization_refused(
        "binding-frame slot bound on one path only",
        &module,
        &["Inst::Undef", "may be unbound", "Inst::Return"],
    );
}

/// A back edge into the entry block that carries a frame handle: on
/// function entry the same parameter holds the caller's pointer, which no
/// `OpenFrame` produced. Refused by name.
fn check_binding_frame_entry_param_fail_closed() {
    let module = module_with_blocks(
        "manifest_frame_entry_param",
        vec![Ty::Bool, Ty::Ptr, Ty::I64],
        vec![Ty::I64],
        vec![
            TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::Bool), (v(1), Ty::Ptr), (v(2), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::LoadSlot {
                        frame: v(1),
                        slot: 0,
                        ty: Ty::I64,
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::OpenFrame {
                        def: manifest_frame_def(),
                    })
                    .with_result(v(4)),
                    InstrNode::new(Inst::BindSlot {
                        frame: v(4),
                        slot: 0,
                        value: v(2),
                    })
                    .with_result(v(5)),
                    InstrNode::new(Inst::CondBr {
                        cond: v(0),
                        then_target: b(0),
                        then_args: vec![v(0), v(5), v(3)],
                        else_target: b(1),
                        else_args: vec![],
                    }),
                ],
            },
            TrustIrBlock {
                id: b(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::CloseFrame { frame: v(5) }),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            },
        ],
    );
    expect_legalization_refused(
        "binding-frame handle in an entry-block parameter",
        &module,
        &["Inst::OpenFrame", "entry-block parameter"],
    );
}

/// `CloseFrame` has no runtime effect (trust-ir `interpret.rs`): nothing is
/// emitted between the slot load and the return.
fn check_close_frame_supported() {
    let opcodes = frame_program_opcodes();
    let tail = &opcodes[opcodes.len() - 2..];
    assert!(
        matches!(tail, [Opcode::Load { .. }, Opcode::Return]),
        "CloseFrame is a lifetime marker and must not emit runtime instructions: {opcodes:?}"
    );
}

fn check_close_frame_non_frame_fail_closed() {
    expect_legalization_refused(
        "CloseFrame of a value no OpenFrame produced",
        &single_inst_module(
            "manifest_close_frame_non_frame",
            vec![(v(0), Ty::I64)],
            vec![],
            InstrNode::new(Inst::CloseFrame { frame: v(0) }),
            vec![],
        ),
        &["Inst::CloseFrame", "BindingFrameUnopened"],
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

fn check_assert_panic_unspecified_fail_closed() {
    let module = module_with_blocks(
        "manifest_assert",
        vec![Ty::Bool],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Bool)],
            body: vec![
                InstrNode::new(Inst::Assert {
                    cond: v(0),
                    kind: trust_ir::AssertKind::Unspecified,
                    site: None,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );
    assert!(matches!(translate_single(&module),
        Err(AdapterError::TrustIrAdmissionRefused { error })
            if error.contains("unspecified panic kind") && error.contains("require_assert_panic_kinds")));
}

/// A scalar `Undef` whose poison is only transported (here: stored plainly)
/// materializes as the all-zero bit pattern (the NoUndef model), recorded in
/// the legalization receipt.
fn check_undef_transported_supported() {
    let module = module_with_blocks(
        "manifest_undef_transported",
        vec![Ty::I64],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(1)),
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(2),
                    value: v(1),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    let (func, proofs) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap_or_else(|err| panic!("a transported undef must lower: {err:?}"));
    assert!(
        func.blocks[&func.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(
                inst.opcode,
                Opcode::Iconst {
                    ty: Type::I64,
                    imm: 0
                }
            )),
        "the undef materializes as zero"
    );
    assert_eq!(proofs.borrow_frame_undef.undefs.len(), 1);
}

/// Inspecting poison is undefined behaviour in trust-ir (ub-numerics-policy
/// §4): an undef that reaches a return is refused, never compiled to zero.
fn check_undef_inspected_fail_closed() {
    expect_legalization_refused(
        "Inst::Undef inspected poison",
        &single_inst_module(
            "manifest_undef",
            vec![],
            vec![Ty::I64],
            InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(0)),
            vec![v(0)],
        ),
        &[
            "Inst::Undef",
            "reaches an inspecting use in Inst::Return",
            "NoUndef",
        ],
    );
}

/// Aggregate poison is unmodelled by the pinned reference semantics.
fn check_undef_aggregate_fail_closed() {
    let pair = Ty::Tuple(vec![Ty::I64, Ty::I64]);
    let module = module_with_blocks(
        "manifest_undef_aggregate",
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Undef { ty: pair.clone() }).with_result(v(0)),
                InstrNode::new(Inst::Alloca {
                    ty: pair.clone(),
                    count: None,
                    align: None,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Store {
                    ty: pair,
                    ptr: v(1),
                    value: v(0),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );
    expect_legalization_refused(
        "Inst::Undef aggregate",
        &module,
        &["Inst::Undef", "aggregate/vector poison is unmodelled"],
    );
}

/// Only a PLAIN store transports poison (ub-numerics-policy §4); a volatile
/// store inspects it, and the reference interpreter faults on it. Refused.
fn check_undef_volatile_store_fail_closed() {
    let module = module_with_blocks(
        "manifest_undef_volatile_store",
        vec![Ty::I64],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(1)),
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(2),
                    value: v(1),
                    volatile: true,
                    align: None,
                }),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    );
    expect_legalization_refused(
        "Inst::Undef stored volatilely",
        &module,
        &["Inst::Undef", "reaches an inspecting use in Inst::Store"],
    );
}

/// The NoUndef model for EVERY admitted scalar carrier: the LIR value an
/// `Undef` materializes as is defined by a zero constant of the carrier the
/// adapter translates its type to (`Iconst 0` for integers, `Bool` and
/// pointers, `Fconst +0.0` for `F32`/`F64`). Native code cannot observe
/// this zero in an admitted program (poison is only transported), so this
/// row is where the zero itself is pinned.
fn check_undef_zero_of_every_carrier_supported() {
    for ty in [
        Ty::Bool,
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
        Ty::F32,
        Ty::F64,
        Ty::Ptr,
    ] {
        let module = module_with_blocks(
            "manifest_undef_zero",
            vec![],
            vec![],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Undef { ty: ty.clone() }).with_result(v(0)),
                    InstrNode::new(Inst::Alloca {
                        ty: ty.clone(),
                        count: None,
                        align: None,
                    })
                    .with_result(v(1)),
                    InstrNode::new(Inst::Store {
                        ty: ty.clone(),
                        ptr: v(1),
                        value: v(0),
                        volatile: false,
                        align: None,
                    }),
                    InstrNode::new(Inst::Return { values: vec![] }),
                ],
            }],
        );
        let (func, proofs) = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap_or_else(|err| panic!("a transported {ty} undef must lower: {err:?}"));
        let [record] = proofs.borrow_frame_undef.undefs.as_slice() else {
            panic!(
                "{ty}: one undef record expected: {:?}",
                proofs.borrow_frame_undef
            )
        };
        let carrier = translate_type(&ty).expect("scalar carrier");
        assert_eq!(record.carrier, carrier, "{ty}: recorded carrier");
        let definitions: Vec<&Opcode> = func.blocks[&func.entry_block]
            .instructions
            .iter()
            .filter(|inst| inst.results.contains(&record.result))
            .map(|inst| &inst.opcode)
            .collect();
        let [definition] = definitions.as_slice() else {
            panic!("{ty}: one definition of the undef value expected: {definitions:?}")
        };
        let zero = match definition {
            Opcode::Iconst { ty, imm } => *ty == carrier && *imm == 0,
            Opcode::Fconst { ty, imm } => *ty == carrier && imm.to_bits() == 0,
            _ => false,
        };
        assert!(
            zero,
            "{ty}: the undef must materialize as the +0 bit pattern of {carrier:?}, got {definition:?}"
        );
    }
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

fn check_set_bitset_type_fail_closed() {
    // trust-ir states no universe for a bitset, so no bit image exists.
    let err = translate_type_with_tables(&Ty::Set(TyId::new(0), SetRepr::Bitset), &[], &[Ty::U8])
        .expect_err("a bitset Set must fail closed: trust-ir states no universe");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "SetRepr::Bitset");
}

fn check_set_boxed_type_value_slot_supported() {
    // `trust_cg_lower::sequence_layout`: a value slot carries the image pointer.
    assert_eq!(
        translate_type_with_tables(&Ty::Set(TyId::new(0), SetRepr::Boxed), &[], &[Ty::U16])
            .expect("a boxed set of an admitted element lowers in a value slot"),
        Type::I64
    );
}

fn check_sequence_type_value_slot_supported() {
    assert_eq!(
        translate_type_with_tables(&Ty::Sequence(TyId::new(0)), &[], &[Ty::F64])
            .expect("a sequence of an admitted element lowers in a value slot"),
        Type::I64
    );
    let err = translate_type_with_tables(&Ty::Sequence(TyId::new(0)), &[], &[Ty::I128])
        .expect_err("an unadmitted element must fail closed");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "is not admitted");
}

fn check_nested_collection_type_fail_closed() {
    for ty in [
        Ty::Tuple(vec![Ty::Sequence(TyId::new(0))]),
        Ty::Tuple(vec![Ty::I64, Ty::Set(TyId::new(0), SetRepr::Boxed)]),
    ] {
        let err = translate_type_with_tables(&ty, &[], &[Ty::I32])
            .expect_err("a collection nested in an aggregate has no in-memory layout");
        expect_fail_closed(
            err,
            DiagnosticClass::UnsupportedType,
            "nested inside another type",
        );
    }
    // A table-free lookup cannot resolve the element size.
    let err = translate_type(&Ty::Sequence(TyId::new(0)))
        .expect_err("an unresolvable element must fail closed");
    expect_fail_closed(
        err,
        DiagnosticClass::UnsupportedType,
        "not in the module types table",
    );
}

fn check_record_type_fail_closed() {
    // The table-only type helper has no record table to resolve the fields
    // from, so it cannot name a layout.
    let err = translate_type(&Ty::Record(RecordId::new(0)))
        .expect_err("Record type must fail closed without a module record table");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_record_type_with_table_supported() {
    // With the module's record table a record-typed value is the struct of
    // its declared fields: a record-typed parameter is projected like any
    // aggregate (the aggregate_target_execution rows cover the constant and
    // field-update paths).
    let mut module = TrustIrModule::new("manifest_record_type_param");
    let record = RecordId::new(0);
    module.add_record(RecordDef {
        id: record,
        name: "ManifestRecord".to_string(),
        fields: vec![FieldDef {
            name: "field".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
    });
    let takes_record = module
        .add_func_type(FuncTy {
            params: vec![Ty::Record(record)],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut program = TrustIrFunction::new(f(0), "manifest_record_type_param", takes_record, b(0));
    program.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Record(record))],
        body: vec![
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Record(record),
                aggregate: v(0),
                field: 0,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });
    module
        .try_add_function(program)
        .expect("Module::try_add_function: test fixture");
    let func = expect_supported(&module, "Ty::Record with module record table");
    assert!(
        func.blocks[&func.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Load { .. })),
        "field projection out of a record-typed parameter loads the field"
    );
}

fn check_closure_type_fail_closed() {
    // The table-only type helper has no closure-type table to resolve the
    // captures from, so it cannot name a layout.
    let err = translate_type(&Ty::Closure(ClosureTyId::new(0)))
        .expect_err("Closure type must fail closed without a module closure-type table");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
}

fn check_closure_type_with_table_supported() {
    // With the module's closure-type table a closure value is the struct of
    // its captures: a closure-typed parameter is projected like any aggregate.
    let mut module = TrustIrModule::new("manifest_closure_type_param");
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.closure_types.push(ClosureTy {
        func: apparent,
        captures: vec![Ty::I64],
    });
    let takes_closure = module
        .add_func_type(FuncTy {
            params: vec![Ty::Closure(ClosureTyId::new(0))],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut program =
        TrustIrFunction::new(f(0), "manifest_closure_type_param", takes_closure, b(0));
    program.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Closure(ClosureTyId::new(0)))],
        body: vec![
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I64,
                aggregate: v(0),
                field: 0,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });
    module
        .try_add_function(program)
        .expect("Module::try_add_function: test fixture");
    let func = expect_supported(&module, "Ty::Closure with module closure table");
    assert!(
        func.blocks[&func.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Load { .. })),
        "capture projection out of a closure-typed parameter loads the capture"
    );
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

    canonical_constants::body_refused(
        &const_module(
            "manifest_isize_positive_overflow",
            Ty::Isize,
            Constant::Int((i64::MAX as i128) + 1),
        ),
        "manifest_isize_positive_overflow",
        "isize",
        "int",
    );

    expect_supported(
        &const_module("manifest_char_max", Ty::Char, Constant::Int(0x10FFFF)),
        "maximum Unicode scalar Char constant",
    );
    for (name, value) in [
        ("manifest_char_surrogate", 0xD800),
        ("manifest_char_out_of_range", 0x11_0000),
    ] {
        let location = format!("function '{name}' bb0");
        canonical_constants::assert_refused(
            &const_module(name, Ty::Char, Constant::Int(value)),
            &[
                (
                    &location,
                    "a Unicode scalar value (0..=0x10FFFF minus 0xD800..=0xDFFF)",
                    &format!("char constant {value}"),
                ),
                (&location, "char", "int"),
            ],
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
    assert_eq!(
        module
            .add_type(Ty::I64)
            .expect("Module::add_type: test fixture"),
        TyId::new(0)
    );
    assert_eq!(
        module
            .intern_pred(Pred::NonZero)
            .expect("Module::intern_pred: test fixture"),
        Some(PredId::new(0))
    );

    let lowered = permit_translate_module(&module)
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
    assert_eq!(
        module
            .add_type(Ty::I64)
            .expect("Module::add_type: test fixture"),
        TyId::new(0)
    );
    assert_eq!(
        module
            .intern_pred(Pred::Top)
            .expect("Module::intern_pred: test fixture"),
        Some(PredId::new(0))
    );

    let err = translate_single(&module)
        .expect_err("ordinary operations over refined operands are not lowered in v0.1.0");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["BinOp::Add", "operand type mismatch", "Refine"],
    );
}

fn check_storage_type_fail_closed() {
    let err = translate_type(&Ty::Storage(trust_ir::StorageLayout::new(80, 8)))
        .expect_err("Storage has no initialized LIR value representation");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedType,
        &["Ty::Storage", "no LIR value representation"],
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

fn check_dialect_type_fail_closed() {
    let ty = Ty::Dialect(Box::new(trust_ir::DialectTy::new("tla", "Value", 1)));
    let err = translate_type(&ty)
        .expect_err("nominal semantic types require legalization before lowering");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedType,
        &["tla.Value@1", "semantic legalization"],
    );
}

/// A v43 opaque runtime handle in a VALUE slot is the one pointer-word
/// carrier: that is what makes a pinned-runtime call edge emittable at all.
/// Nothing beyond that word is promised — see the interior row below.
fn check_handle_value_slot_supported() {
    assert_eq!(
        translate_type(&Ty::handle("Nat", "trust_bignum::Nat"))
            .expect("a handle in a value slot is one pointer word"),
        Type::I64
    );
}

/// Every INTERIOR occurrence fails closed, because an interior has an address:
/// a handle given a layout can be stored and re-read as an ordinary pointer,
/// which is the forgery the type exists to prevent. The module-wide admission
/// (`trust_cg_lower::handle_transport`) decides the rest; this row pins the
/// type funnel's own half.
fn check_handle_interior_fail_closed() {
    let handle = Ty::handle("Nat", "trust_bignum::Nat");
    for interior in [
        Ty::Tuple(vec![Ty::I64, handle.clone()]),
        Ty::Ref(Box::new(handle.clone())),
        Ty::Vector(Box::new(handle), 2),
    ] {
        let err = translate_type(&interior)
            .expect_err("an interior opaque runtime handle has no representation");
        assert!(
            matches!(
                err,
                AdapterError::OpaqueHandleNotAdmitted { ref name, ref runtime, .. }
                    if name == "Nat" && runtime == "trust_bignum::Nat"
            ),
            "{interior:?} must be refused by handle identity, got {err}"
        );
    }
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

fn set_const_module(name: &str, values: Vec<Constant>) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let elem_tyid = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let func_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), name, func_ty, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Set(elem_tyid, SetRepr::Boxed),
                value: Constant::Set(values),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn check_set_constant_supported() {
    // A boxed set constant is the sequence image of its constructor-ordered
    // elements (`trust_cg_lower::sequence_layout`).
    let func = expect_supported(
        &set_const_module(
            "manifest_set_const",
            vec![Constant::Int(3), Constant::Int(1)],
        ),
        "typed Constant::Set",
    );
    assert_eq!(func.stack_slots.len(), 1);
    assert_eq!(func.stack_slots[0].size, 24);
}

fn check_set_constant_repeated_element_fail_closed() {
    let err = translate_single(&set_const_module(
        "manifest_set_repeat",
        vec![Constant::Int(3), Constant::Int(3)],
    ))
    .expect_err("a set constant repeating an element must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "repeats an element"],
    );
    // Retain the original physical-alias fixture, but 2^64 - 1 is not an I64
    // value. Its canonical type error precedes duplicate-image lowering;
    // the genuine repeated-element control above remains unchanged.
    canonical_constants::assert_refused(
        &set_const_module(
            "manifest_set_alias",
            vec![Constant::Int(-1), Constant::Int(i128::from(u64::MAX))],
        ),
        &[("function 'manifest_set_alias' bb0[1]", "i64", "int")],
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
    canonical_constants::body_refused(
        &const_module(
            "manifest_u128_const_noncanonical",
            Ty::U128,
            Constant::U128(7),
        ),
        "manifest_u128_const_noncanonical",
        "canonical integer spelling (values <= i128::MAX are Constant::Int;                        Constant::U128 only above)",
        "int",
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
    canonical_constants::body_refused(
        &invalid_utf8_module,
        "manifest_bytes_const",
        "valid UTF-8 under the utf8 claim",
        "invalid UTF-8 byte sequence",
    );

    // A non-`[u8; N]` bytes constant is malformed and must still fail closed.
    canonical_constants::body_refused(
        &const_module(
            "manifest_bytes_scalar",
            Ty::U8,
            Constant::Bytes {
                data: vec![0x54, 0x49, 0x52],
                utf8: false,
            },
        ),
        "manifest_bytes_scalar",
        "u8",
        "bytes[3]",
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

    // A NON-ZERO addend (`&symbol + 8`, an interior address) lowers to the
    // same bare symbol reference followed by an EXPLICIT `Iconst 8; Iadd`:
    // the relocation stays the plain symbol reference and the displacement
    // is an ordinary integer add, never an addend-carrying relocation.
    let func = expect_supported(
        &const_module(
            "manifest_symbol_addr_instruction_const_addend",
            Ty::Ptr,
            Constant::SymbolAddr {
                symbol: "manifest_target".to_string(),
                addend: 8,
            },
        ),
        "non-zero-addend Constant::SymbolAddr function-body constant",
    );
    let entry = &func.blocks[&func.entry_block];
    let base = entry
        .instructions
        .iter()
        .position(|inst| {
            matches!(
                &inst.opcode,
                Opcode::ExternRef { name } | Opcode::GlobalRef { name } if name == "manifest_target"
            )
        })
        .expect("SymbolAddr with an addend still materializes the bare symbol address");
    let base_value = entry.instructions[base].results[0];
    let offset = entry
        .instructions
        .iter()
        .position(|inst| matches!(&inst.opcode, Opcode::Iconst { imm: 8, .. }))
        .expect("the addend is an explicit I64 constant");
    let offset_value = entry.instructions[offset].results[0];
    assert!(
        entry.instructions.iter().any(|inst| {
            matches!(inst.opcode, Opcode::Iadd)
                && inst.args.contains(&base_value)
                && inst.args.contains(&offset_value)
        }),
        "the interior address is `base + addend` through an explicit Iadd"
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

fn check_closure_constant_with_capture_at_non_closure_type_fail_closed() {
    // A captured closure literal is a `Ty::Closure` value; at any other type
    // there is no environment layout to materialize it into.
    canonical_constants::body_refused(
        &const_module(
            "manifest_closure_const",
            Ty::I64,
            Constant::Closure {
                func: f(0),
                captures: vec![Constant::Int(1)],
            },
        ),
        "manifest_closure_const",
        "i64",
        "closure<func.0>[1]",
    );
}

/// A module with `closure.0 = { func: functy.0 (i64) -> (i64), captures: [i64] }`,
/// its code target `manifest_closure_body` (`FuncId(1)`, physical signature
/// `(i64, i64) -> (i64)`), and `program` (`FuncId(0)`, `(i64) -> (i64)`) whose
/// entry block is `body` over parameter `v0` and returns `ret`.
fn closure_module(name: &str, body: Vec<InstrNode>, ret: ValueId) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let physical = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.closure_types.push(ClosureTy {
        func: apparent,
        captures: vec![Ty::I64],
    });
    let mut program = TrustIrFunction::new(f(0), name, apparent, b(0));
    let mut entry = TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::I64)],
        body,
    };
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![ret] }));
    program.blocks.push(entry);
    module
        .try_add_function(program)
        .expect("Module::try_add_function: test fixture");

    let mut target = TrustIrFunction::new(f(1), "manifest_closure_body", physical, b(0));
    target.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::I64), (v(1), Ty::I64)],
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
    });
    module
        .try_add_function(target)
        .expect("Module::try_add_function: test fixture");
    module
}

fn closure_literal(func: FuncId, capture: i128) -> Constant {
    Constant::Closure {
        func,
        captures: vec![Constant::Int(capture)],
    }
}

fn check_closure_constant_with_captures_supported() {
    // `Const closure.0 { manifest_closure_body, [7] }` materializes its
    // environment (one stack slot, capture 0 stored), and `ExtractField`
    // projects the capture back.
    let func = expect_supported(
        &closure_module(
            "manifest_closure_const_supported",
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    value: closure_literal(f(1), 7),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::I64,
                    aggregate: v(1),
                    field: 0,
                })
                .with_result(v(2)),
            ],
            v(2),
        ),
        "Constant::Closure with captures at Ty::Closure",
    );
    let instructions = &func.blocks[&func.entry_block].instructions;
    assert!(
        instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StackAddr { .. })),
        "closure literal must materialize its environment in a stack slot"
    );
    assert!(
        instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Store { .. })),
        "closure literal must store its capture into the environment"
    );
    assert!(
        instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Load { .. })),
        "capture projection must load the capture back out of the environment"
    );
}

fn check_closure_application_with_static_identity_supported() {
    // `CallIndirect closure.0 (v0)` over the literal lowers as ONE direct call
    // to `manifest_closure_body` with the capture spread ahead of the apparent
    // argument: `(capture_0, v0)`.
    let func = expect_supported(
        &closure_module(
            "manifest_closure_apply_supported",
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    value: closure_literal(f(1), 7),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Copy {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    operand: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::CallIndirect {
                    callee: v(2),
                    sig: FuncTyId::new(0),
                    args: vec![v(0)],
                    calling_conv: CallingConv::C,
                })
                .with_result(v(3)),
            ],
            v(3),
        ),
        "Inst::CallIndirect over Ty::Closure callee with static code identity",
    );
    let calls: Vec<&Instruction> = func.blocks[&func.entry_block]
        .instructions
        .iter()
        .filter(|inst| matches!(inst.opcode, Opcode::Call { .. } | Opcode::CallIndirect))
        .collect();
    assert_eq!(
        calls.len(),
        1,
        "closure application lowers to exactly one call carrier"
    );
    let Opcode::Call { name, .. } = &calls[0].opcode else {
        panic!(
            "closure application must be a DIRECT call, got {:?}",
            calls[0].opcode
        )
    };
    assert_eq!(name, "manifest_closure_body");
    assert_eq!(
        calls[0].args.len(),
        2,
        "the capture is spread ahead of the apparent argument"
    );
}

fn check_closure_application_from_parameter_fail_closed() {
    let mut module = TrustIrModule::new("manifest_closure_param_callee");
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.closure_types.push(ClosureTy {
        func: apparent,
        captures: vec![Ty::I64],
    });
    let takes_closure = module
        .add_func_type(FuncTy {
            params: vec![Ty::Closure(ClosureTyId::new(0)), Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut program =
        TrustIrFunction::new(f(0), "manifest_closure_param_callee", takes_closure, b(0));
    program.blocks.push(TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Closure(ClosureTyId::new(0))), (v(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::CallIndirect {
                callee: v(0),
                sig: apparent,
                args: vec![v(1)],
                calling_conv: CallingConv::C,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![v(2)] }),
        ],
    });
    module
        .try_add_function(program)
        .expect("Module::try_add_function: test fixture");
    let err = translate_single(&module)
        .expect_err("a closure arriving as a parameter has no statically visible code");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "[TCG-CLOSURE]",
            "function or block parameter",
            "not statically visible",
        ],
    );
}

fn check_closure_application_from_same_code_select_supported() {
    let func = expect_supported(
        &closure_module(
            "manifest_closure_select_callee",
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    value: closure_literal(f(1), 1),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    value: closure_literal(f(1), 2),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Select {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    cond: v(3),
                    then_val: v(1),
                    else_val: v(2),
                })
                .with_result(v(4)),
                InstrNode::new(Inst::CallIndirect {
                    callee: v(4),
                    sig: FuncTyId::new(0),
                    args: vec![v(0)],
                    calling_conv: CallingConv::C,
                })
                .with_result(v(5)),
            ],
            v(5),
        ),
        "same-code closure selection",
    );
    let instructions = &func.blocks[&func.entry_block].instructions;
    assert!(
        instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Select { .. }))
    );
    let calls: Vec<_> = instructions
        .iter()
        .filter(|inst| matches!(inst.opcode, Opcode::Call { .. } | Opcode::CallIndirect))
        .collect();
    assert_eq!(calls.len(), 1);
    assert!(matches!(&calls[0].opcode, Opcode::Call { name, .. }
        if name == "manifest_closure_body"));
    assert_eq!(calls[0].args.len(), 2);
}

fn check_closure_application_from_select_fail_closed() {
    let mut module = closure_module(
        "manifest_closure_select_callee",
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Closure(ClosureTyId::new(0)),
                value: closure_literal(f(1), 1),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::Closure(ClosureTyId::new(0)),
                value: closure_literal(f(2), 2),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Select {
                ty: Ty::Closure(ClosureTyId::new(0)),
                cond: v(3),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(4)),
            InstrNode::new(Inst::CallIndirect {
                callee: v(4),
                sig: FuncTyId::new(0),
                args: vec![v(0)],
                calling_conv: CallingConv::C,
            })
            .with_result(v(5)),
        ],
        v(5),
    );
    // Both constructors must be valid physical code targets so the refusal
    // reaches Select itself rather than a malformed closure introduction.
    let mut other_target = module.functions[1].clone();
    other_target.id = f(2);
    other_target.name = "manifest_other_closure_body".to_string();
    module.functions.push(other_target);
    let err = translate_single(&module)
        .expect_err("a differing-code selected closure has no statically visible code");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "[TCG-CLOSURE]",
            "produced by Inst::Select",
            "not statically visible",
        ],
    );
}

fn check_closure_application_apparent_signature_mismatch_fail_closed() {
    // The edge declares the PHYSICAL signature (functy.1) instead of the
    // closure's apparent one (functy.0).
    let err = translate_single(&closure_module(
        "manifest_closure_apparent_sig",
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Closure(ClosureTyId::new(0)),
                value: closure_literal(f(1), 7),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::CallIndirect {
                callee: v(1),
                sig: FuncTyId::new(1),
                args: vec![v(0), v(0)],
                calling_conv: CallingConv::C,
            })
            .with_result(v(2)),
        ],
        v(2),
    ))
    .expect_err("the edge must declare the closure's apparent signature");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-CLOSURE]", "apparent signature is functy.0"],
    );
}

fn check_closure_application_physical_signature_mismatch_fail_closed() {
    // The literal names `program` itself (`(i64) -> (i64)`), whose signature
    // lacks the leading capture the closure type requires.
    let err = translate_single(&closure_module(
        "manifest_closure_physical_sig",
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Closure(ClosureTyId::new(0)),
                value: closure_literal(f(0), 7),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::CallIndirect {
                callee: v(1),
                sig: FuncTyId::new(0),
                args: vec![v(0)],
                calling_conv: CallingConv::C,
            })
            .with_result(v(2)),
        ],
        v(2),
    ))
    .expect_err("the code target must carry the physical closure signature");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &[
            "[TCG-CLOSURE]",
            "physical signature",
            "1 capture(s) then 1 apparent parameter(s)",
        ],
    );
}

fn check_nested_closure_fndef_symbol_addr_constants_supported() {
    // `(5, closure.0 { manifest_closure_body, [2] }, manifest_closure_body as
    // fn(i64, i64) -> i64, &manifest_closure_body)` as one in-body literal.
    let mut module = closure_module("manifest_nested_closure_fndef_symbol", vec![], v(0));
    let tuple_ty = Ty::Tuple(vec![
        Ty::I64,
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Func(FuncTyId::new(1)),
        Ty::Ptr,
    ]);
    let program = &mut module.functions[0];
    let entry = &mut program.blocks[0];
    entry.body = vec![
        InstrNode::new(Inst::Const {
            ty: tuple_ty,
            value: Constant::Aggregate(vec![
                Constant::Int(5),
                closure_literal(f(1), 2),
                Constant::FnDef(f(1)),
                Constant::SymbolAddr {
                    symbol: "manifest_closure_body".to_string(),
                    addend: 0,
                },
            ]),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::Closure(ClosureTyId::new(0)),
            aggregate: v(1),
            field: 1,
        })
        .with_result(v(2)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::I64,
            aggregate: v(2),
            field: 0,
        })
        .with_result(v(3)),
        InstrNode::new(Inst::Return { values: vec![v(3)] }),
    ];
    let func = expect_supported(
        &module,
        "Constant::Closure/FnDef/SymbolAddr nested as aggregate fields",
    );
    let instructions = &func.blocks[&func.entry_block].instructions;
    let symbol_materializations = instructions
        .iter()
        .filter(|inst| {
            matches!(
                inst.opcode,
                Opcode::GlobalRef { .. } | Opcode::ExternRef { .. } | Opcode::FunctionAddr { .. }
            )
        })
        .count();
    assert_eq!(
        symbol_materializations, 2,
        "the FnDef and SymbolAddr fields each materialize one symbol address"
    );
    assert!(
        instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::Store { .. }))
            .count()
            >= 4,
        "every scalar field (5, capture 2, fn address, symbol address) is stored"
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
        let bytes =
            trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
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
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
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
    for (name, ty, needle) in [
        (
            "manifest_target_set_bitset",
            Ty::Set(TyId::new(0), SetRepr::Bitset),
            "SetRepr::Bitset",
        ),
        (
            "manifest_target_record",
            Ty::Record(RecordId::new(0)),
            "not yet lowered",
        ),
        (
            "manifest_target_closure",
            Ty::Closure(ClosureTyId::new(0)),
            "not yet lowered",
        ),
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
        expect_fail_closed(err, DiagnosticClass::UnsupportedType, needle);
    }
}

fn check_collection_value_slots_have_target_execution_path() {
    // `f(s) -> s` for a sequence and a boxed set: the parameter is the image
    // pointer and the result travels through the trailing result buffer.
    for (name, ty) in [
        ("manifest_target_sequence_slot", Ty::Sequence(TyId::new(0))),
        (
            "manifest_target_set_slot",
            Ty::Set(TyId::new(0), SetRepr::Boxed),
        ),
    ] {
        let mut module = module_with_blocks(
            name,
            vec![ty.clone()],
            vec![ty.clone()],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), ty)],
                body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
            }],
        );
        module.types.push(Ty::I32);
        let func = expect_supported(&module, "collection value slots");
        assert_eq!(
            func.signature.params,
            vec![Type::I64, Type::I64],
            "the image pointer plus the trailing result buffer"
        );
        assert_eq!(func.signature.returns, vec![Type::I64]);
        assert!(
            func.blocks[&func.entry_block]
                .instructions
                .iter()
                .any(|inst| matches!(inst.opcode, Opcode::Memmove)),
            "the result image is copied into the caller's buffer"
        );
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
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Iadd))
            && entry
                .instructions
                .iter()
                .any(|inst| matches!(inst.opcode, Opcode::Store { ty: Type::I64, .. })),
        "Sequence constant materialization must compute element addresses and store the image"
    );
}

fn check_set_constant_has_target_materialization_path() {
    let func = expect_supported(
        &set_const_module(
            "manifest_target_set_const",
            vec![Constant::Int(1), Constant::Int(2)],
        ),
        "typed Constant::Set target materialization",
    );
    assert_eq!(
        func.blocks[&func.entry_block]
            .instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::Store { ty: Type::I64, .. }))
            .count(),
        3,
        "one length header plus two element stores"
    );
    // A constant under a non-collection type stays refused.
    canonical_constants::body_refused(
        &const_module(
            "manifest_target_set_const_scalar",
            Ty::I64,
            Constant::Set(vec![Constant::Int(1), Constant::Int(2)]),
        ),
        "manifest_target_set_const_scalar",
        "i64",
        "set[2]",
    );
}

fn seq_map_family_module(inst: Inst) -> TrustIrModule {
    let seq = Ty::Sequence(TyId::new(0));
    let mut module = module_with_blocks(
        "manifest_seq_map",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), seq)],
            body: vec![
                InstrNode::new(inst).with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
    );
    module.types.push(Ty::I32);
    module
}

fn check_seq_map_family_supported() {
    let seq = Ty::Sequence(TyId::new(0));
    for inst in [
        Inst::SeqMapAddK {
            ty: seq.clone(),
            seq: v(0),
            k: 7,
        },
        Inst::SeqMapNot {
            ty: seq.clone(),
            seq: v(0),
        },
    ] {
        let not = matches!(inst, Inst::SeqMapNot { .. });
        let mut module = seq_map_family_module(inst);
        if not {
            module.types[0] = Ty::Bool;
        }
        let func = expect_supported(&module, "SeqMap family counted loop");
        // The entry, the loop header and body, and the continuation.
        assert_eq!(func.blocks.len(), 4, "a counted loop in blocks of its own");
        assert!(
            func.blocks.values().any(|block| block
                .instructions
                .iter()
                .any(|inst| matches!(inst.opcode, Opcode::Brif { .. }))),
            "the loop exit is a conditional branch"
        );
    }
}

fn check_seq_map_family_outside_semantics_fail_closed() {
    let seq = Ty::Sequence(TyId::new(0));
    let mut add_k_float = seq_map_family_module(Inst::SeqMapAddK {
        ty: seq.clone(),
        seq: v(0),
        k: 1,
    });
    add_k_float.types[0] = Ty::F32;
    let err = translate_single(&add_k_float).expect_err("SeqMapAddK over f32 must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "integer elements"],
    );
    let err = translate_single(&seq_map_family_module(Inst::SeqMapNot {
        ty: seq,
        seq: v(0),
    }))
    .expect_err("SeqMapNot over i32 must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "Bool elements"],
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

fn check_closure_constant_has_target_materialization_path() {
    // The captured closure literal's environment is a stack image of its
    // captures (declaration order, natural-C layout), the same image
    // `ExtractField`/`InsertField` address; `e2e_aarch64_closures.rs`
    // executes it natively.
    let func = expect_supported(
        &closure_module(
            "manifest_target_closure_const",
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    value: closure_literal(f(1), 1),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::I64,
                    aggregate: v(1),
                    field: 0,
                })
                .with_result(v(2)),
            ],
            v(2),
        ),
        "Constant::Closure with captures target materialization",
    );
    let instructions = &func.blocks[&func.entry_block].instructions;
    assert!(
        instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StackAddr { .. }))
            && instructions
                .iter()
                .any(|inst| matches!(inst.opcode, Opcode::Store { .. })),
        "captured closure literal must materialize its environment"
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

/// `fn project(e: enum.0) -> ty { ret extractfield ty e, field }` over a
/// descriptor-less enum with the given variants (WS7.6).
fn direct_enum_extract_module(
    name: &str,
    variants: Vec<Vec<Ty>>,
    ty: Ty,
    field: u32,
) -> TrustIrModule {
    let mut module = single_inst_module(
        name,
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![ty.clone()],
        InstrNode::new(Inst::ExtractField {
            ty,
            aggregate: v(0),
            field,
        })
        .with_result(v(1)),
        vec![v(1)],
    );
    module.add_enum(trust_ir::EnumDef::new(
        EnumId::new(0),
        "ManifestEnum",
        variants
            .into_iter()
            .enumerate()
            .map(|(i, fields)| trust_ir::EnumVariant {
                name: format!("v{i}"),
                fields,
                field_names: Vec::new(),
            })
            .collect(),
    ));
    module
}

fn check_direct_enum_extract_field_supported() {
    // `enum { v0(u64), v1(u64, u64) }`: the u8 tag at byte 0, both variants'
    // first field at payload byte 8, `v1`'s second at 16.
    let shape = || vec![vec![Ty::U64], vec![Ty::U64, Ty::U64]];
    for (ty, field, load_ty, offset) in [
        (Ty::U8, 0, Type::I8, None),
        (Ty::U64, 1, Type::I64, Some(8)),
        (Ty::U64, 2, Type::I64, Some(16)),
    ] {
        let func = expect_supported(
            &direct_enum_extract_module("manifest_direct_enum_extract", shape(), ty, field),
            "direct-tag enum ExtractField",
        );
        let entry = &func.blocks[&func.entry_block];
        assert!(
            entry.instructions.iter().any(|inst| matches!(
                &inst.opcode,
                Opcode::Load { ty, .. } if *ty == load_ty
            )),
            "element {field} must load {load_ty:?}"
        );
        assert_eq!(
            entry
                .instructions
                .iter()
                .find_map(|inst| match inst.opcode {
                    Opcode::Iconst { imm, .. } => Some(imm),
                    _ => None,
                }),
            offset,
            "element {field} must be read at its static offset"
        );
    }
}

fn check_direct_enum_ambiguous_extract_field_fail_closed() {
    // `u8` element 2 sits at payload byte 1 in `v0(u8, u8)` and 2 in
    // `v1(u16, u8)`; the lane does not say which variant is active.
    let err = translate_single(&direct_enum_extract_module(
        "manifest_direct_enum_ambiguous",
        vec![vec![Ty::U8, Ty::U8], vec![Ty::U16, Ty::U8]],
        Ty::U8,
        2,
    ))
    .expect_err("an ambiguous enum payload offset must fail closed");
    assert!(
        matches!(
            err,
            AdapterError::EnumProjectionOffsetAmbiguous { lane: 2, .. }
        ),
        "{err:?}"
    );
}

fn check_direct_enum_insert_field_tag_refused_payload_lowers() {
    for (field, value_ty) in [(0, Ty::U8), (1, Ty::U64)] {
        let mut module = single_inst_module(
            "manifest_direct_enum_insert",
            vec![(v(0), Ty::Enum(EnumId::new(0))), (v(1), value_ty)],
            vec![],
            InstrNode::new(Inst::InsertField {
                ty: Ty::Enum(EnumId::new(0)),
                aggregate: v(0),
                field,
                value: v(1),
            })
            .with_result(v(2)),
            vec![],
        );
        module.add_enum(trust_ir::EnumDef::new(
            EnumId::new(0),
            "ManifestEnum",
            vec![trust_ir::EnumVariant {
                name: "v0".to_string(),
                fields: vec![Ty::U64],
                field_names: Vec::new(),
            }],
        ));
        // Element 0 re-tags, which trust-ir makes undefined behaviour, so it stays
        // refused. A PAYLOAD element lowers since WS7.1(c) wired the fresh-slot
        // value-semantic insert to this carrier's field walk, so the manifest row for it
        // is now "lowers", not "fails closed".
        match field {
            0 => {
                let err =
                    translate_single(&module).expect_err("element 0 re-tags and must fail closed");
                assert!(
                    matches!(&err, AdapterError::EnumTagWriteUnsupported { .. }),
                    "element 0: {err:?}"
                );
            }
            _ => {
                translate_single(&module)
                    .expect("WS7.1(c): a direct-tag payload element must lower");
            }
        }
    }
}

/// `enum { v0(u8, u32), v1(u64), v2 }` at rustc's layout — tag at 0, `v0` at
/// bytes 1 and 4, `v1` at 8, 16 bytes — with the given discriminants and repr.
fn direct_enum_def_with(
    discriminants: Vec<Option<i128>>,
    repr: Option<trust_ir::ty::EnumTagRepr>,
    layout: Option<trust_ir::ty::EnumLayoutDescriptor>,
) -> trust_ir::EnumDef {
    let variant = |name: &str, fields: Vec<Ty>| trust_ir::EnumVariant {
        name: name.to_string(),
        fields,
        field_names: Vec::new(),
    };
    trust_ir::EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "ManifestEnum".to_string(),
        variants: vec![
            variant("v0", vec![Ty::U8, Ty::U32]),
            variant("v1", vec![Ty::U64]),
            variant("v2", vec![]),
        ],
        discriminants,
        repr,
        layout,
    }
}

fn rustc_like_layout() -> trust_ir::ty::EnumLayoutDescriptor {
    trust_ir::ty::EnumLayoutDescriptor {
        encoding: trust_ir::ty::EnumTagEncoding::Direct { tag_offset: 0 },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![1, 4], vec![8], vec![]],
    }
}

fn direct_enum_extract_module_with(
    name: &str,
    edef: trust_ir::EnumDef,
    ty: Ty,
    field: u32,
) -> TrustIrModule {
    let mut module = single_inst_module(
        name,
        vec![(v(0), Ty::Enum(EnumId::new(0)))],
        vec![ty.clone()],
        InstrNode::new(Inst::ExtractField {
            ty,
            aggregate: v(0),
            field,
        })
        .with_result(v(1)),
        vec![v(1)],
    );
    module.add_enum(edef);
    module
}

fn check_direct_enum_signed_explicit_discriminants_supported() {
    // `Ordering { Less = -1, Equal = 0, Greater = 1 }` with an `i8` repr: the
    // tag lane is a one-byte load whose signedness belongs to the consumer.
    let ordering = trust_ir::EnumDef::new(
        EnumId::new(0),
        "ManifestOrdering",
        ["Less", "Equal", "Greater"]
            .into_iter()
            .map(|name| trust_ir::EnumVariant {
                name: name.to_string(),
                fields: vec![],
                field_names: Vec::new(),
            })
            .collect(),
    )
    .with_discriminants(vec![Some(-1), Some(0), Some(1)])
    .with_repr(trust_ir::ty::EnumTagRepr::I8);
    let func = expect_supported(
        &direct_enum_extract_module_with("manifest_direct_enum_signed", ordering, Ty::I8, 0),
        "direct-tag enum with a signed repr and explicit discriminants",
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry.instructions.iter().any(|inst| matches!(
            &inst.opcode,
            Opcode::Load { ty, .. } if *ty == Type::I8
        )),
        "the tag must be loaded at its i8 lane"
    );
}

fn check_direct_enum_producer_layout_supported() {
    // `v0.1` sits at byte 4 by the producer's layout, where the canonical
    // shape would put it at 12; the carrier is the declared 16/8 image.
    let edef = direct_enum_def_with(
        vec![Some(10), Some(20), Some(30)],
        Some(trust_ir::ty::EnumTagRepr::U8),
        Some(rustc_like_layout()),
    );
    let func = expect_supported(
        &direct_enum_extract_module_with("manifest_direct_enum_layout", edef, Ty::U32, 2),
        "direct-tag enum with a producer layout",
    );
    assert_eq!(
        func.signature.params[0],
        Type::Struct(vec![Type::Array(Box::new(Type::I64), 2)]),
        "the byte-image carrier of the declared 16/8"
    );
    let entry = &func.blocks[&func.entry_block];
    assert!(
        entry.instructions.iter().any(|inst| matches!(
            &inst.opcode,
            Opcode::Load { ty, .. } if *ty == Type::I32
        )),
        "element 2 must load a u32"
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .find_map(|inst| match inst.opcode {
                Opcode::Iconst { imm, .. } => Some(imm),
                _ => None,
            }),
        Some(4),
        "element 2 must be read at the descriptor's byte 4"
    );
}

fn check_direct_enum_constant_writes_discriminant_value() {
    // `Const v0 = 10 { 7, 9 }`: the stored tag is the VALUE 10, and the u32
    // field lands at the descriptor's byte 4.
    let edef = direct_enum_def_with(
        vec![Some(10), Some(20), Some(30)],
        Some(trust_ir::ty::EnumTagRepr::U8),
        Some(rustc_like_layout()),
    );
    let mut module = single_inst_module(
        "manifest_direct_enum_const",
        vec![],
        vec![],
        InstrNode::new(Inst::Const {
            ty: Ty::Enum(EnumId::new(0)),
            value: Constant::Aggregate(vec![Constant::Int(10), Constant::Int(7), Constant::Int(9)]),
        })
        .with_result(v(0)),
        vec![],
    );
    module.add_enum(edef);
    let func = expect_supported(&module, "direct-tag enum constant at a producer layout");
    let entry = &func.blocks[&func.entry_block];
    let iconsts: Vec<(Type, i64)> = entry
        .instructions
        .iter()
        .filter_map(|inst| match &inst.opcode {
            Opcode::Iconst { ty, imm } => Some((ty.clone(), *imm)),
            _ => None,
        })
        .collect();
    assert!(
        iconsts.contains(&(Type::I8, 10)),
        "the tag word must carry the discriminant VALUE 10: {iconsts:?}"
    );
    assert!(
        iconsts.contains(&(Type::I64, 4)),
        "the u32 field must be addressed at the descriptor's byte 4: {iconsts:?}"
    );
    assert!(
        !iconsts.contains(&(Type::I8, 0)),
        "nothing writes the variant INDEX as a tag: {iconsts:?}"
    );
}

fn check_direct_enum_duplicate_discriminants_fail_closed() {
    let edef = direct_enum_def_with(vec![Some(4), Some(4), None], None, None);
    canonical_constants::assert_refused(
        &direct_enum_extract_module_with("manifest_direct_enum_duplicate", edef, Ty::U8, 0),
        &[(
            "enum.0 (ManifestEnum)",
            "resolvable, duplicate-free discriminant assignment",
            "ill-formed discriminants",
        )],
    );
}

fn check_direct_enum_128_bit_repr_fail_closed() {
    let edef = direct_enum_def_with(vec![], Some(trust_ir::ty::EnumTagRepr::I128), None);
    let err = translate_single(&direct_enum_extract_module_with(
        "manifest_direct_enum_i128",
        edef,
        Ty::I128,
        0,
    ))
    .expect_err("a 128-bit tag lane must fail closed");
    expect_fail_closed(err, DiagnosticClass::UnsupportedType, "128-bit");
}

fn check_direct_enum_descriptor_overlapping_tag_fail_closed() {
    let mut layout = rustc_like_layout();
    layout.encoding = trust_ir::ty::EnumTagEncoding::Direct { tag_offset: 8 };
    let edef = direct_enum_def_with(vec![], Some(trust_ir::ty::EnumTagRepr::U8), Some(layout));
    canonical_constants::assert_refused(
        &direct_enum_extract_module_with("manifest_direct_enum_overlap", edef, Ty::U8, 0),
        &[(
            "enum.0 (ManifestEnum) layout",
            "a direct tag disjoint from every non-ZST field",
            "tag overlaps variant 1 field 0",
        )],
    );
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
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "InsertElement", "UnlowerableForCodegen"],
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

    // A `Copy` cannot launder a raw pointer into a sequence value.
    let err = translate_single(&module)
        .expect_err("a Copy of a Ptr at a Ty::Sequence type must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "moves only at its own type"],
    );
}

fn check_sequence_extract_element_over_materialized_sequence_fail_closed() {
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

    // trust-ir's codegen gate: no element of a sequence is addressable,
    // whatever the operand's provenance (must-refuse row sequence_element_op).
    let err = translate_single(&module)
        .expect_err("ExtractElement over a materialized sequence must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "ExtractElement", "UnlowerableForCodegen"],
    );
}

fn check_sequence_insert_element_over_materialized_sequence_fail_closed() {
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

    let err = translate_single(&module)
        .expect_err("InsertElement over a materialized sequence must fail closed");
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "InsertElement", "UnlowerableForCodegen"],
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
    let strides: Vec<_> = entry
        .instructions
        .iter()
        .filter_map(|inst| match &inst.opcode {
            Opcode::ArrayGep { elem_ty } => Some(elem_ty.bytes()),
            _ => None,
        })
        .collect();
    assert_eq!(
        strides,
        vec![16, 16],
        "each index must stride a whole record"
    );
    assert!(
        !entry
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::StructGep { .. }))
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
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "Inst::GEP spells", "no byte layout"],
    );
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
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "Inst::GEP spells", "no byte layout"],
    );
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
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "Inst::GEP spells", "no byte layout"],
    );
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
    expect_fail_closed_all(
        err,
        DiagnosticClass::UnsupportedInstruction,
        &["[TCG-SEQ]", "Inst::GEP spells", "no byte layout"],
    );
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
            surface: "Inst::Store of a <N x bool> logical mask",
            status: CoverageStatus::FailClosed,
            check: check_store_bool_mask_fail_closed,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Load of a <N x bool> logical mask",
            status: CoverageStatus::FailClosed,
            check: check_load_bool_mask_fail_closed,
        },
        CoverageRow {
            category: "memory",
            surface: "Inst::Alloca of a <N x bool> logical mask",
            status: CoverageStatus::FailClosed,
            check: check_alloca_bool_mask_fail_closed,
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
            status: CoverageStatus::Supported,
            check: check_transmute_equal_size_supported,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp::Transmute size-mismatch",
            status: CoverageStatus::FailClosed,
            check: check_transmute_size_mismatch_fail_closed,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp::Transmute validity-carrying leaf",
            status: CoverageStatus::FailClosed,
            check: check_transmute_validity_leaf_fail_closed,
        },
        CoverageRow {
            category: "casts",
            surface: "CastOp::Transmute source padding",
            status: CoverageStatus::FailClosed,
            check: check_transmute_source_padding_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::MakeAggregate struct/tuple/record/array",
            status: CoverageStatus::Supported,
            check: check_make_aggregate_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::MakeAggregate enum variant",
            status: CoverageStatus::Supported,
            check: check_make_aggregate_enum_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::ArraySplat (v50)",
            status: CoverageStatus::Supported,
            check: check_array_splat_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::ArraySplat at a non-array type",
            status: CoverageStatus::FailClosed,
            check: check_array_splat_non_array_fail_closed,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Splat (v50)",
            status: CoverageStatus::Supported,
            check: check_splat_constant_supported,
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
            surface: "Inst::Switch I128/U128 selector (split halves dispatch)",
            status: CoverageStatus::Supported,
            check: check_switch_i128_selector_supported,
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
            surface: "Inst::CallCannotUnwind normative boundary without EH",
            status: CoverageStatus::FailClosed,
            check: check_validated_call_cannot_unwind_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirectCannotUnwind dynamic normative boundary without EH",
            status: CoverageStatus::FailClosed,
            check: check_validated_call_indirect_cannot_unwind_fail_closed,
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
            status: CoverageStatus::Supported,
            check: check_borrow_insts_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::BorrowMut through a shared borrow",
            status: CoverageStatus::FailClosed,
            check: check_borrow_mut_through_shared_borrow_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Borrow of a non-pointer",
            status: CoverageStatus::FailClosed,
            check: check_borrow_of_non_pointer_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Borrow of a fat pointer",
            status: CoverageStatus::Supported,
            check: check_borrow_fat_pointer_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::EndBorrow of a non-borrow",
            status: CoverageStatus::FailClosed,
            check: check_end_borrow_of_non_borrow_fail_closed,
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
            status: CoverageStatus::FailClosed,
            check: check_assert_panic_unspecified_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Undef scalar transported (NoUndef zero model)",
            status: CoverageStatus::Supported,
            check: check_undef_transported_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Undef inspected poison",
            status: CoverageStatus::FailClosed,
            check: check_undef_inspected_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Undef aggregate",
            status: CoverageStatus::FailClosed,
            check: check_undef_aggregate_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Undef stored volatilely",
            status: CoverageStatus::FailClosed,
            check: check_undef_volatile_store_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Undef zero pattern of every scalar carrier (NoUndef model)",
            status: CoverageStatus::Supported,
            check: check_undef_zero_of_every_carrier_supported,
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
            surface: "Inst::Dealloc of a same-function RustHeap/CMalloc HeapAlloc (G18-1)",
            status: CoverageStatus::FailClosed,
            check: check_dealloc_provenance_resolvable_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Dealloc with mixed allocator origins",
            status: CoverageStatus::FailClosed,
            check: check_dealloc_mixed_origins_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "HeapAlloc/Dealloc with SwiftHeap or CleanHeap origin",
            status: CoverageStatus::FailClosed,
            check: check_dealloc_rc_heap_origins_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::OpenFrame",
            status: CoverageStatus::Supported,
            check: check_open_frame_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::BindSlot",
            status: CoverageStatus::Supported,
            check: check_bind_slot_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::LoadSlot",
            status: CoverageStatus::Supported,
            check: check_load_slot_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CloseFrame",
            status: CoverageStatus::Supported,
            check: check_close_frame_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::BindSlot of a value no OpenFrame produced",
            status: CoverageStatus::FailClosed,
            check: check_bind_slot_of_non_frame_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::LoadSlot of a value no OpenFrame produced",
            status: CoverageStatus::FailClosed,
            check: check_load_slot_of_non_frame_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CloseFrame of a value no OpenFrame produced",
            status: CoverageStatus::FailClosed,
            check: check_close_frame_non_frame_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "binding-frame handle live after a rebind",
            status: CoverageStatus::FailClosed,
            check: check_binding_frame_superseded_handle_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "binding-frame handle escape",
            status: CoverageStatus::FailClosed,
            check: check_binding_frame_escape_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "binding-frame non-scalar slot",
            status: CoverageStatus::FailClosed,
            check: check_binding_frame_non_scalar_slot_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "binding frame never closed",
            status: CoverageStatus::FailClosed,
            check: check_binding_frame_unclosed_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "binding-frame handle live across a block edge after a rebind",
            status: CoverageStatus::FailClosed,
            check: check_binding_frame_superseded_handle_across_blocks_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "binding-frame slot bound on one path only",
            status: CoverageStatus::FailClosed,
            check: check_binding_frame_partially_bound_slot_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "binding-frame handle in an entry-block parameter",
            status: CoverageStatus::FailClosed,
            check: check_binding_frame_entry_param_fail_closed,
        },
        CoverageRow {
            category: "dialect_ops",
            surface: "Inst::DialectOp unknown namespace",
            status: CoverageStatus::FailClosed,
            check: check_unknown_dialect_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Set bitset",
            status: CoverageStatus::FailClosed,
            check: check_set_bitset_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Set boxed value slot",
            status: CoverageStatus::Supported,
            check: check_set_boxed_type_value_slot_supported,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Sequence value slot",
            status: CoverageStatus::Supported,
            check: check_sequence_type_value_slot_supported,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Sequence/Ty::Set nested in another type",
            status: CoverageStatus::FailClosed,
            check: check_nested_collection_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Record without module record table",
            status: CoverageStatus::FailClosed,
            check: check_record_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Record with module record table",
            status: CoverageStatus::Supported,
            check: check_record_type_with_table_supported,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Closure without module closure table",
            status: CoverageStatus::FailClosed,
            check: check_closure_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Closure with module closure table",
            status: CoverageStatus::Supported,
            check: check_closure_type_with_table_supported,
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
            surface: "Ty::Dialect",
            status: CoverageStatus::FailClosed,
            check: check_dialect_type_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Handle value slot (v43 pinned-runtime transport)",
            status: CoverageStatus::Supported,
            check: check_handle_value_slot_supported,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Handle interior/representation",
            status: CoverageStatus::FailClosed,
            check: check_handle_interior_fail_closed,
        },
        CoverageRow {
            category: "types",
            surface: "Ty::Storage by-value representation",
            status: CoverageStatus::FailClosed,
            check: check_storage_type_fail_closed,
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
            status: CoverageStatus::Supported,
            check: check_set_constant_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Set with a repeated element",
            status: CoverageStatus::FailClosed,
            check: check_set_constant_repeated_element_fail_closed,
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
            surface: "Constant::Closure with captures at non-closure type",
            status: CoverageStatus::FailClosed,
            check: check_closure_constant_with_capture_at_non_closure_type_fail_closed,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Closure with captures at Ty::Closure",
            status: CoverageStatus::Supported,
            check: check_closure_constant_with_captures_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Closure/FnDef/SymbolAddr nested as aggregate fields",
            status: CoverageStatus::Supported,
            check: check_nested_closure_fndef_symbol_addr_constants_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect over Ty::Closure callee with static code identity",
            status: CoverageStatus::Supported,
            check: check_closure_application_with_static_identity_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect over Ty::Closure parameter callee",
            status: CoverageStatus::FailClosed,
            check: check_closure_application_from_parameter_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect over Ty::Closure same-code Select callee",
            status: CoverageStatus::Supported,
            check: check_closure_application_from_same_code_select_supported,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect over Ty::Closure differing-code Select callee",
            status: CoverageStatus::FailClosed,
            check: check_closure_application_from_select_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect over Ty::Closure apparent signature mismatch",
            status: CoverageStatus::FailClosed,
            check: check_closure_application_apparent_signature_mismatch_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirect over Ty::Closure physical signature mismatch",
            status: CoverageStatus::FailClosed,
            check: check_closure_application_physical_signature_mismatch_fail_closed,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::PhantomData",
            status: CoverageStatus::Supported,
            check: check_phantom_unit_constant_supported,
        },
        CoverageRow {
            category: "constants",
            surface: "Constant::Uninit (v49 unwritten aggregate lane)",
            status: CoverageStatus::FailClosed,
            check: check_uninit_lane_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Drop (v47)",
            status: CoverageStatus::FailClosed,
            check: check_drop_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::MakeClosure (v63 runtime captures)",
            status: CoverageStatus::FailClosed,
            check: check_runtime_closure_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallCannotUnwind (v53 non-propagating call boundary)",
            status: CoverageStatus::FailClosed,
            check: check_call_cannot_unwind_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CallIndirectCannotUnwind (v53 non-propagating call boundary)",
            status: CoverageStatus::FailClosed,
            check: check_call_indirect_cannot_unwind_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::Assert { site: Some(_) } (v54 panic site)",
            status: CoverageStatus::Supported,
            check: check_sited_assert_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::AssertInvoke (v54 sited check with an unwind edge)",
            status: CoverageStatus::Supported,
            check: check_assert_invoke_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::DropInvoke (v55 drop with an unwind edge)",
            status: CoverageStatus::FailClosed,
            check: check_drop_invoke_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::InvokeIndirect (v56 indirect call with an unwind edge)",
            status: CoverageStatus::FailClosed,
            check: check_invoke_indirect_fail_closed,
        },
        CoverageRow {
            category: "instructions",
            surface: "Inst::CmpXchg { weak: true } (v48)",
            status: CoverageStatus::FailClosed,
            check: check_weak_cmpxchg_fail_closed,
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
            surface: "Ty::Set bitset/Record/Closure target fixtures fail closed",
            status: CoverageStatus::FailClosed,
            check: check_logical_aggregates_have_no_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Ty::Sequence/boxed Ty::Set parameter and result",
            status: CoverageStatus::Supported,
            check: check_collection_value_slots_have_target_execution_path,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::SeqMapAddK/SeqMapNot counted loop",
            status: CoverageStatus::Supported,
            check: check_seq_map_family_supported,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::SeqMap family outside trust-ir element semantics",
            status: CoverageStatus::FailClosed,
            check: check_seq_map_family_outside_semantics_fail_closed,
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
            status: CoverageStatus::Supported,
            check: check_set_constant_has_target_materialization_path,
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
            status: CoverageStatus::Supported,
            check: check_closure_constant_has_target_materialization_path,
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
            surface: "Inst::ExtractField over direct-tag Ty::Enum (tag and payload lanes)",
            status: CoverageStatus::Supported,
            check: check_direct_enum_extract_field_supported,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractField over direct-tag Ty::Enum with an ambiguous payload offset",
            status: CoverageStatus::FailClosed,
            check: check_direct_enum_ambiguous_extract_field_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertField over direct-tag Ty::Enum",
            status: CoverageStatus::FailClosed,
            check: check_direct_enum_insert_field_tag_refused_payload_lowers,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractField over direct-tag Ty::Enum with explicit discriminants and a signed repr (L05-P5)",
            status: CoverageStatus::Supported,
            check: check_direct_enum_signed_explicit_discriminants_supported,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractField over direct-tag Ty::Enum with a producer layout the canonical shape does not reproduce (L05-P5)",
            status: CoverageStatus::Supported,
            check: check_direct_enum_producer_layout_supported,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Constant::Aggregate of a direct-tag Ty::Enum writes the discriminant value at the producer layout (L05-P5)",
            status: CoverageStatus::Supported,
            check: check_direct_enum_constant_writes_discriminant_value,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Ty::Enum with duplicate effective discriminants",
            status: CoverageStatus::FailClosed,
            check: check_direct_enum_duplicate_discriminants_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Ty::Enum with a 128-bit EnumDef.repr",
            status: CoverageStatus::FailClosed,
            check: check_direct_enum_128_bit_repr_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Ty::Enum with a Direct descriptor whose field overlaps the tag word",
            status: CoverageStatus::FailClosed,
            check: check_direct_enum_descriptor_overlapping_tag_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::ExtractElement over a materialized Ty::Sequence",
            status: CoverageStatus::FailClosed,
            check: check_sequence_extract_element_over_materialized_sequence_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::Copy of a Ptr at a Ty::Sequence type",
            status: CoverageStatus::FailClosed,
            check: check_sequence_extract_element_without_layout_provenance_fail_closed,
        },
        CoverageRow {
            category: "aggregate_target_execution",
            surface: "Inst::InsertElement over a materialized Ty::Sequence",
            status: CoverageStatus::FailClosed,
            check: check_sequence_insert_element_over_materialized_sequence_fail_closed,
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
        // trust-ir WS3.20 (F-057).
        BinOp::RotL => "RotL",
        BinOp::RotR => "RotR",
        BinOp::FCopySign => "FCopySign",
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
        Ty::Ext(e) => e.unreachable(),
        Ty::Tensor(_, _) => "Tensor",
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
        Ty::Storage(_) => "Storage",
        Ty::Never => "Never",
        Ty::Struct(_) => "Struct",
        Ty::Array(_, _) => "Array",
        Ty::Tuple(_) => "Tuple",
        Ty::Enum(_) => "Enum",
        Ty::Func(_) => "Func",
        Ty::FnItem(_) => "FnItem",
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
        Ty::Dialect(_) => "Dialect",
        Ty::Handle(_) => "Handle",
    }
}

#[allow(dead_code)]
fn constant_variant_name(value: &Constant) -> &'static str {
    match value {
        Constant::Ext(e) => e.unreachable(),
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
        Constant::FnItem(_) => "FnItem",
        Constant::SymbolAddr { .. } => "SymbolAddr",
        Constant::PhantomData => "PhantomData",
        Constant::Uninit => "Uninit",
        Constant::Splat { .. } => "Splat",
        Constant::TensorBlob { .. } => "TensorBlob",
    }
}

#[allow(dead_code)]
fn inst_variant_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::TensorContract { .. } => "TensorContract",
        Inst::TensorMap { .. } => "TensorMap",
        Inst::TensorReduce { .. } => "TensorReduce",
        Inst::TensorView { .. } => "TensorView",
        Inst::TensorGather { .. } => "TensorGather",
        Inst::TensorScatter { .. } => "TensorScatter",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::MemCopy { .. } => "MemCopy",
        Inst::MemSet { .. } => "MemSet",
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
        Inst::CallCannotUnwind { .. } => "CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
        Inst::AssertInvoke { .. } => "AssertInvoke",
        Inst::DropInvoke { .. } => "DropInvoke",
        Inst::InvokeIndirect { .. } => "InvokeIndirect",
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
        Inst::BoxDeref { .. } => "BoxDeref",
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
        Inst::MakeAggregate { .. } => "MakeAggregate",
        Inst::MakeClosure { .. } => "MakeClosure",
        Inst::Drop { .. } => "Drop",
        Inst::ArraySplat { .. } => "ArraySplat",
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
        Ty::FnItem(FuncId::new(0)),
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
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("tla", "Value", 1))),
        Ty::handle("Nat", "trust_bignum::Nat"),
        Ty::Storage(trust_ir::StorageLayout::new(80, 8)),
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
        Constant::FnItem(f(0)),
        Constant::SymbolAddr {
            symbol: "manifest_symbol".to_string(),
            addend: 0,
        },
        Constant::PhantomData,
        Constant::Uninit,
        Constant::Splat {
            elem: Box::new(Constant::Int(0)),
            len: 2,
        },
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
            weak: false,
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
        Inst::Assert {
            cond: v(0),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        },
        Inst::Unreachable,
        Inst::Copy {
            ty: Ty::I64,
            operand: v(0),
        },
        Inst::BoxDeref {
            ptr_ty: Ty::Ptr,
            pointee: trust_ir::box_validity::BoxPointee::Sized { ty: Ty::I64 },
            operand: v(0),
            fact: Box::new(trust_ir::box_validity::BoxValidityFact::premise(
                trust_ir::box_validity::BoxDerefSite {
                    item: [0x5a; 16],
                    ordinal: 0,
                },
                trust_ir::box_validity::BoxFactSession::PROOF_SNAPSHOT,
                trust_ir::box_validity::PremiseRoot::ParamByValue,
            )),
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
        Inst::Drop {
            ty: Ty::I64,
            ptr: v(0),
        },
        Inst::ArraySplat {
            ty: Ty::Array(trust_ir::TyId::new(0), 2),
            value: v(0),
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::default(),
        },
        Inst::AssertInvoke {
            cond: v(0),
            kind: trust_ir::AssertKind::DivByZero,
            site: manifest_panic_site(),
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
        Inst::DropInvoke {
            ty: Ty::Struct(StructId::new(0)),
            ptr: v(0),
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
        Inst::InvokeIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::default(),
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
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
                "Unit", "Never", "Struct", "Array", "Tuple", "Enum", "Func", "FnItem", "Ref",
                "RefMut", "PtrConst", "PtrMut", "Rc", "Set", "Sequence", "Record", "Closure",
                "Refine", "Dialect", "Handle", "Storage",
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
                "FnItem",
                "SymbolAddr",
                "PhantomData",
                "Uninit",
                "Splat",
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
                "BoxDeref",
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
                "Drop",
                "ArraySplat",
                "CallCannotUnwind",
                "CallIndirectCannotUnwind",
                "AssertInvoke",
                "DropInvoke",
                "InvokeIndirect",
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
            variant: "FnItem",
            status: FailClosed,
            evidence: "trust_ir_construct_inventory pins Ty::FnItem as a nominal zero-storage identity with no native value ABI until an explicit function-item coercion",
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
            variant: "Record/Closure",
            status: FailClosed,
            evidence: "coverage_rows logical aggregate type rows",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Sequence/boxed Set value slot",
            status: Supported,
            evidence: "coverage_rows collection value-slot rows: the trust_cg_lower::sequence_layout image pointer in parameters, results (trailing result buffer) and block parameters; e2e_aarch64_sequences.rs native execution",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Set bitset / nested Sequence or Set",
            status: FailClosed,
            evidence: "coverage_rows bitset and nested-collection rows",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Handle value slot",
            status: Supported,
            evidence: "coverage_rows v43 pinned-runtime transport: one pointer word in a parameter/result/return/block-parameter slot",
        },
        InventoryRow {
            enum_name: "Ty",
            variant: "Handle interior/representation",
            status: FailClosed,
            evidence: "coverage_rows v43 interior occurrences fail closed; module-wide admission in trust_cg_lower::handle_transport restricts use to pinned-runtime transport",
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
            variant: "FnDef/Closure",
            status: Supported,
            evidence: "adapter function-symbol constant path (FnDef, capture-free Closure at Ty::Func) and closure environment materialization at Ty::Closure with static code identity at each CallIndirect application (coverage_rows closure rows; e2e_aarch64_closures.rs native execution)",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "FnItem",
            status: FailClosed,
            evidence: "trust_ir_construct_inventory pins Constant::FnItem as a nominal function identity that must be explicitly coerced before code-pointer materialization",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "Sequence/Set/Record",
            status: Supported,
            evidence: "coverage_rows typed logical constant materialization (sequence and boxed-set images per trust_cg_lower::sequence_layout)",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "Set with a repeated element",
            status: FailClosed,
            evidence: "coverage_rows repeated set element row",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "PhantomData",
            status: FailClosed,
            evidence: "coverage_rows trust_ir#30 constant rows",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "Uninit",
            status: FailClosed,
            evidence: "coverage_rows Constant::Uninit (v49) row; the shared floor refuses it by name",
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
            evidence: "coverage_rows SymbolAddr lowers to GlobalRef/ExternRef (raw-name FnDef/GlobalAddr counterpart); a non-zero addend adds an explicit Iconst/Iadd displacement",
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
            variant: "Transmute equal-size",
            status: Supported,
            evidence: "coverage_rows Transmute equal-size row (register lane for scalar pairs, store/load lane otherwise)",
        },
        InventoryRow {
            enum_name: "CastOp",
            variant: "Transmute size-mismatch/validity-carrying leaf/source padding",
            status: FailClosed,
            evidence: "coverage_rows Transmute size-mismatch, validity-carrying leaf and source padding rows",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "MakeAggregate struct/tuple/record/array",
            status: Supported,
            evidence: "coverage_rows MakeAggregate struct/tuple/record/array row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "MakeAggregate enum variant",
            status: Supported,
            evidence: "coverage_rows MakeAggregate enum variant row",
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
            variant: "ExtractElement/InsertElement over Ty::Sequence or Ty::Set",
            status: FailClosed,
            evidence: "coverage_rows element-op rows: trust-ir's codegen gate names them UnlowerableForCodegen (must-refuse row sequence_element_op)",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "SeqMapAddK/SeqMapNot/SeqMap",
            status: Supported,
            evidence: "coverage_rows SeqMap counted-loop rows; e2e_aarch64_sequences.rs native execution against the interpreter and a C model",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Const/NullPtr/Unreachable/Copy/Select",
            status: Supported,
            evidence: "coverage_rows constants/control/pseudo rows plus Select operand/mask validation",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "BoxDeref",
            status: Supported,
            evidence: "box_deref_admission pins default and proof-required refusal plus the disclosed named-premise diagnostic lane, where an admitted v74 BoxDeref lowers to one value-preserving Copy and takes no licence from its fact",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Assume",
            status: Supported,
            evidence: "coverage_rows Assume checked runtime assertion row",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Undef of a scalar whose poison is only transported",
            status: Supported,
            evidence: "coverage_rows Undef NoUndef zero-model row; e2e_aarch64_borrows_frames",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Undef inspected, aggregate or FreshSymbolicHavoc-marked",
            status: FailClosed,
            evidence: "coverage_rows Undef inspected/aggregate rows; the legalization stage refuses the marker by name",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Borrow/BorrowMut/EndBorrow",
            status: Supported,
            evidence: "coverage_rows borrow value-copy row with provenance receipt; e2e_aarch64_borrows_frames",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "BorrowMut through a shared borrow, borrow of a non-pointer, EndBorrow of a non-borrow",
            status: FailClosed,
            evidence: "coverage_rows borrow structure rows",
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
            variant: "Drop",
            status: FailClosed,
            evidence: "coverage_rows Inst::Drop (v47) row; the shared floor refuses it by name",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "MakeClosure",
            status: FailClosed,
            evidence: "coverage_rows Inst::MakeClosure (v63) row; typed runtime-closure ABI refusal before optimization",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "CallCannotUnwind",
            status: FailClosed,
            evidence: "coverage_rows Inst::CallCannotUnwind (v53) row; the shared floor and the lowering arm refuse it by name",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "CallIndirectCannotUnwind",
            status: FailClosed,
            evidence: "coverage_rows Inst::CallIndirectCannotUnwind (v53) row; the shared floor and the lowering arm refuse it by name",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "AssertInvoke",
            status: Supported,
            evidence: "native entry/location call plus original pad; Core/WASM authority remain refused; runtime UNRUN",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "DropInvoke",
            status: FailClosed,
            evidence: "coverage_rows Inst::DropInvoke (v55) row; the shared floor and the lowering arm refuse it by name, at a type the drop-glue table resolves",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "InvokeIndirect",
            status: FailClosed,
            evidence: "coverage_rows Inst::InvokeIndirect (v56) row; the shared floor and the lowering arm refuse it by name",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "ArraySplat",
            status: Supported,
            evidence: "coverage_rows Inst::ArraySplat (v50) row: one memset or one lane write plus a doubling copy, constant-size in the lane count (tests/array_splat_lowering.rs)",
        },
        InventoryRow {
            enum_name: "Constant",
            variant: "Splat",
            status: Supported,
            evidence: "coverage_rows Constant::Splat (v50) row: one memset or one lane write plus a doubling copy, constant-size in the lane count (tests/array_splat_lowering.rs)",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "CmpXchg { weak: true }",
            status: FailClosed,
            evidence: "coverage_rows weak CmpXchg (v48) row; the shared floor refuses it by name",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "Dealloc (every body, whatever its pointer's provenance; G18-1)",
            status: FailClosed,
            evidence: "coverage_rows Dealloc [TCG-DEALLOC] rows and trust_ir_dealloc_refusal",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "OpenFrame",
            status: Supported,
            evidence: "coverage_rows OpenFrame row; e2e_aarch64_borrows_frames",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "BindSlot",
            status: Supported,
            evidence: "coverage_rows BindSlot row; e2e_aarch64_borrows_frames",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "LoadSlot",
            status: Supported,
            evidence: "coverage_rows LoadSlot row; e2e_aarch64_borrows_frames",
        },
        InventoryRow {
            enum_name: "Inst",
            variant: "binding frames with a live superseded handle, an escaping handle, a non-scalar slot or no CloseFrame",
            status: FailClosed,
            evidence: "coverage_rows binding-frame fail-closed rows",
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
            variant: "Boxed",
            status: Supported,
            evidence: "coverage_rows boxed-set value-slot and constant rows",
        },
        InventoryRow {
            enum_name: "SetRepr",
            variant: "Bitset",
            status: FailClosed,
            evidence: "coverage_rows bitset row: trust-ir states no universe for the bit image",
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
            && row.surface == "Inst::Undef inspected poison"
            && row.status == CoverageStatus::FailClosed),
        "manifest must pin inspected poison as fail-closed: the NoUndef zero model never \
         stands in for trust-ir's undefined behaviour"
    );
    for required_surface in [
        "Inst::Undef scalar transported (NoUndef zero model)",
        "Inst::Borrow/BorrowMut/EndBorrow",
        "Inst::OpenFrame",
        "Inst::BindSlot",
        "Inst::LoadSlot",
        "Inst::CloseFrame",
    ] {
        assert!(
            rows.iter().any(|row| row.category == "instructions"
                && row.surface == required_surface
                && row.status == CoverageStatus::Supported),
            "manifest must pin `{required_surface}` as an executable supported row"
        );
    }
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
        "CastOp::Transmute size-mismatch",
        "CastOp::Transmute validity-carrying leaf",
        "CastOp::Transmute source padding",
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
        "Inst::CallCannotUnwind normative boundary without EH",
        "Inst::CallIndirectCannotUnwind dynamic normative boundary without EH",
        "Inst::Return arity mismatch",
        "Inst::Return type mismatch",
        "Inst::CallIndirect unregistered signature",
        "Inst::CallIndirect non-pointer callee",
        "Inst::CallIndirect argument type mismatch",
        "Inst::CallIndirect result arity mismatch",
        "Inst::CallIndirect variadic signature",
        "Inst::CallIndirect Swift aggregate signature",
        "Inst::Assume non-Bool condition",
        "Inst::BorrowMut through a shared borrow",
        "Inst::Borrow of a non-pointer",
        "Inst::EndBorrow of a non-borrow",
        "Inst::Undef aggregate",
        "Inst::Undef stored volatilely",
        "Inst::Select scalar non-Bool condition",
        "Inst::Select operand type mismatch",
        "Inst::Select vector mask mismatch",
        "Inst::Switch non-integer selector",
        "Inst::Switch duplicate normalized case",
        "Inst::Switch non-integer case",
        "Inst::Switch block-arg mismatch",
        "Inst::Retain without RC runtime",
        "Inst::Release without RC runtime",
        "Inst::IsUnique without RC runtime",
        "ARC partial RC-runtime triple",
        "Inst::BindSlot of a value no OpenFrame produced",
        "Inst::LoadSlot of a value no OpenFrame produced",
        "Inst::CloseFrame of a value no OpenFrame produced",
        "binding-frame handle live after a rebind",
        "binding-frame handle escape",
        "binding-frame non-scalar slot",
        "binding frame never closed",
        "binding-frame handle live across a block edge after a rebind",
        "binding-frame slot bound on one path only",
        "binding-frame handle in an entry-block parameter",
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
        "Inst::ExtractElement over a materialized Ty::Sequence",
        "Inst::InsertElement over a materialized Ty::Sequence",
        "Inst::Copy of a Ptr at a Ty::Sequence type",
        "Inst::SeqMap family outside trust-ir element semantics",
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
        "CallCannotUnwind",
        "CallIndirectCannotUnwind",
    ] {
        assert!(
            rows.iter().any(|row| row.enum_name == "Inst"
                && row.variant == required_variant
                && row.status == CoverageStatus::FailClosed),
            "Inst inventory must pin `{required_variant}` individually"
        );
    }
    for required_variant in ["OpenFrame", "BindSlot", "LoadSlot", "CloseFrame"] {
        assert!(
            rows.iter().any(|row| row.enum_name == "Inst"
                && row.variant == required_variant
                && row.status == CoverageStatus::Supported),
            "Inst inventory must pin `{required_variant}` individually as supported"
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

/// An array `MakeAggregate` whose declared length disagrees with its operand
/// list is invalid trust-ir (`InvalidMakeAggregate`). The adapter must refuse
/// it by name from the two lengths alone: a declared length of 2^40 with no
/// operands has to fail closed promptly, not first materialise 2^40 lane
/// types (which exhausts memory before any refusal is returned).
#[test]
fn make_aggregate_array_length_mismatch_refuses_before_materialising_lanes() {
    for (declared, operands) in [(1u64 << 40, 0usize), (3, 2)] {
        let result = v(operands as u32);
        let mut module = single_inst_module(
            "manifest_make_array_length_mismatch",
            (0..operands)
                .map(|index| (v(index as u32), Ty::U8))
                .collect(),
            vec![],
            InstrNode::new(Inst::MakeAggregate {
                ty: Ty::Array(TyId::new(0), declared),
                variant: None,
                fields: (0..operands).map(|index| v(index as u32)).collect(),
            })
            .with_result(result),
            vec![],
        );
        module
            .add_type(Ty::U8)
            .expect("Module::add_type: test fixture");
        let err = translate_single(&module)
            .expect_err("an array MakeAggregate with the wrong operand count must fail closed");
        expect_fail_closed_all(
            err,
            DiagnosticClass::UnsupportedInstruction,
            &[
                "Inst::MakeAggregate",
                &format!("has {operands} operand(s) for {declared} declared lane(s)"),
            ],
        );
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
    let func_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.closure_types.push(ClosureTy {
        func: func_ty,
        captures: vec![Ty::I64],
    });

    for ty in [
        Ty::Record(RecordId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
    ] {
        let err = translate_type(&ty)
            .expect_err("logical trust-ir aggregate types must currently fail closed");
        expect_fail_closed(err, DiagnosticClass::UnsupportedType, "not yet lowered");
    }
    // A sequence or boxed set lowers in a value slot once its element type
    // resolves through the module's table (`trust_cg_lower::sequence_layout`).
    for ty in [
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
    ] {
        assert_eq!(
            translate_type_with_tables(&ty, &[], &module.types).expect("value slot"),
            Type::I64
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}

#[test]
fn enum_constructor_supported_and_unknown_niche_contract() {
    check_make_aggregate_enum_supported();
}
