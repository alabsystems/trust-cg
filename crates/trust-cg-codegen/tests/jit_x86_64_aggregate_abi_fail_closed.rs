#![cfg(target_arch = "x86_64")]

use std::collections::HashMap;

#[cfg(not(target_os = "windows"))]
use std::arch::x86_64::__m128i;

#[cfg(target_os = "windows")]
use trust_cg_codegen::PipelineError;
#[cfg(target_os = "windows")]
use trust_cg_codegen::compiler::CompileError;
use trust_cg_codegen::compiler::Compiler;
// Only the SysV-only `v128_dev_host_compiler` constructs a config directly.
#[cfg(not(target_os = "windows"))]
use trust_cg_codegen::compiler::CompilerConfig;

// JIT-5: the SysV V128 (SIMD) carrier-struct ABI tests exercise packed SSE
// opcodes whose per-instruction proofs are still pending, so under the new x86
// default (CachedVerified) they would correctly fail closed. They test raw ABI
// codegen, so they use the dev-only Unchecked mode explicitly.
// Consumed only by the SysV-only (`not(windows)`) V128 carrier-struct tests.
#[cfg(not(target_os = "windows"))]
fn v128_dev_host_compiler() -> Compiler {
    Compiler::new(CompilerConfig::for_host_jit_unchecked())
}
use trust_ir::{
    Block as TrustIrBlock, BlockId, CallingConv, Constant, FieldDef, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Linkage, Module as TrustIrModule, StructDef,
    StructId, Ty, ValueId,
};
use trust_ir_build::ModuleBuilder;

#[repr(C)]
#[derive(Debug, PartialEq, Eq)]
struct Large {
    a: i64,
    b: i64,
    c: i64,
}

#[repr(C)]
#[derive(Debug, PartialEq, Eq)]
struct SingleI64 {
    a: i64,
}

#[repr(C)]
#[derive(Debug, PartialEq, Eq)]
struct SingleI32 {
    a: i32,
}

#[repr(C)]
#[derive(Debug, PartialEq, Eq)]
struct Small {
    a: i64,
    b: i64,
}

/// `{i32, i32}` — 8 bytes, one System V INTEGER eightbyte (passed in one GPR,
/// returned in RAX).
///
/// Only the SysV (`not(windows)`) host-execution tests build/run one; Win64
/// classifies `{i32,i32}` differently and has its own fail-closed coverage.
#[cfg(not(target_os = "windows"))]
#[repr(C)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct I32Pair {
    a: i32,
    b: i32,
}

#[cfg(not(target_os = "windows"))]
#[repr(C)]
#[derive(Debug, PartialEq)]
struct TwoF64 {
    a: f64,
    b: f64,
}

#[cfg(not(target_os = "windows"))]
#[repr(C)]
#[derive(Debug, PartialEq)]
struct I64F64 {
    a: i64,
    b: f64,
}

#[cfg(not(target_os = "windows"))]
#[repr(C)]
#[derive(Debug, PartialEq)]
struct F64I64 {
    a: f64,
    b: i64,
}

#[cfg(not(target_os = "windows"))]
#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct V128Carrier {
    lanes: __m128i,
}

extern "C" fn native_returns_large_struct() -> Large {
    Large {
        a: 11,
        b: 22,
        c: 33,
    }
}

extern "C" fn native_accepts_single_i64_struct(value: SingleI64) -> i64 {
    value.a.wrapping_add(0x0102_0304_0506_0708)
}

extern "C" fn native_accepts_single_i32_struct(value: SingleI32) -> i32 {
    value.a.wrapping_mul(3).wrapping_add(17)
}

extern "C" fn native_accepts_small_struct(value: Small) -> i64 {
    value
        .a
        .wrapping_mul(3)
        .wrapping_add(value.b.wrapping_mul(5))
}

#[cfg(not(target_os = "windows"))]
extern "C" fn native_accepts_two_f64_struct(value: TwoF64) -> f64 {
    value.a.mul_add(3.0, value.b * 5.0)
}

#[cfg(not(target_os = "windows"))]
extern "C" fn native_returns_two_f64_struct() -> TwoF64 {
    TwoF64 { a: 13.5, b: 29.25 }
}

#[cfg(not(target_os = "windows"))]
extern "C" fn native_accepts_i64_f64_struct(value: I64F64) -> f64 {
    value.a as f64 + value.b * 7.0
}

#[cfg(not(target_os = "windows"))]
extern "C" fn native_accepts_f64_i64_struct(value: F64I64) -> f64 {
    value.a.mul_add(5.0, value.b as f64)
}

#[cfg(not(target_os = "windows"))]
extern "C" fn native_returns_i64_f64_struct() -> I64F64 {
    I64F64 { a: 37, b: 41.5 }
}

#[cfg(not(target_os = "windows"))]
extern "C" fn native_returns_f64_i64_struct() -> F64I64 {
    F64I64 { a: 17.25, b: 43 }
}

#[cfg(not(target_os = "windows"))]
#[allow(improper_ctypes_definitions)]
extern "C" fn native_accepts_v128_carrier_struct(value: V128Carrier) -> __m128i {
    value.lanes
}

#[cfg(not(target_os = "windows"))]
#[allow(improper_ctypes_definitions)]
extern "C" fn native_returns_v128_carrier_struct() -> V128Carrier {
    V128Carrier {
        lanes: m128i_from_i32x4([31, -37, 41, -43]),
    }
}

#[cfg(not(target_os = "windows"))]
extern "C" fn native_accepts_i64_array_lanes(a: i64, b: i64) -> i64 {
    a.wrapping_mul(7).wrapping_add(b.wrapping_mul(11))
}

#[cfg(not(target_os = "windows"))]
extern "C" fn native_accepts_f64_array_lanes(a: f64, b: f64) -> f64 {
    a.mul_add(11.0, b * 13.0)
}

extern "C" fn native_accepts_spilled_single_i64_struct(
    a0: i64,
    a1: i64,
    a2: i64,
    a3: i64,
    a4: i64,
    a5: i64,
    value: SingleI64,
) -> i64 {
    value
        .a
        .wrapping_add(a0 * 2)
        .wrapping_add(a1 * 3)
        .wrapping_add(a2 * 5)
        .wrapping_add(a3 * 7)
        .wrapping_add(a4 * 11)
        .wrapping_add(a5 * 13)
}

fn large_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "Large".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "c".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

fn single_i64_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "SingleI64".to_string(),
        fields: vec![FieldDef {
            name: "a".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

fn single_i32_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "SingleI32".to_string(),
        fields: vec![FieldDef {
            name: "a".to_string(),
            ty: Ty::I32,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

fn small_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "Small".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

#[cfg(not(target_os = "windows"))]
fn two_f64_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "TwoF64".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::F64,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::F64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

#[cfg(not(target_os = "windows"))]
fn i64_f64_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "I64F64".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::F64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

#[cfg(not(target_os = "windows"))]
fn f64_i64_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "F64I64".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::F64,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

#[cfg(not(target_os = "windows"))]
fn v128_carrier_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "V128Carrier".to_string(),
        fields: vec![FieldDef {
            name: "lanes".to_string(),
            ty: v4i32_ty(),
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

// The `{i32,i32}` eightbyte modules below are exercised only by the SysV
// (`not(windows)`) host-execution tests; Win64 aggregate ABI has separate
// fail-closed coverage. Gate the helpers to match their only callers.
#[cfg(not(target_os = "windows"))]
fn unsupported_i32_pair_struct_def() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "UnsupportedI32Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::I32,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::I32,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

fn i64_const(result: u32, value: i64) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value as i128),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn single_i64_aggregate_const(result: u32, aggregate: &Ty, value: i64) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Int(value as i128)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn single_i32_aggregate_const(result: u32, aggregate: &Ty, value: i32) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Int(value as i128)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

#[cfg(not(target_os = "windows"))]
fn i32_pair_aggregate_const(result: u32, aggregate: &Ty, a: i32, b: i32) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Int(a as i128), Constant::Int(b as i128)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn small_aggregate_const(result: u32, aggregate: &Ty, a: i64, b: i64) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Int(a as i128), Constant::Int(b as i128)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

#[cfg(not(target_os = "windows"))]
fn two_f64_aggregate_const(result: u32, aggregate: &Ty, a: f64, b: f64) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Float(a), Constant::Float(b)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

#[cfg(not(target_os = "windows"))]
fn i64_f64_aggregate_const(result: u32, aggregate: &Ty, a: i64, b: f64) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Int(a as i128), Constant::Float(b)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

#[cfg(not(target_os = "windows"))]
fn f64_i64_aggregate_const(result: u32, aggregate: &Ty, a: f64, b: i64) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Float(a), Constant::Int(b as i128)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

#[cfg(not(target_os = "windows"))]
fn v4i32_ty() -> Ty {
    Ty::Vector(Box::new(Ty::I32), 4)
}

#[cfg(not(target_os = "windows"))]
fn v4i32_const(lanes: [i32; 4]) -> Constant {
    Constant::Vector(
        lanes
            .into_iter()
            .map(|lane| Constant::Int(i128::from(lane)))
            .collect(),
    )
}

#[cfg(not(target_os = "windows"))]
fn v128_carrier_aggregate_const(result: u32, aggregate: &Ty, lanes: [i32; 4]) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![v4i32_const(lanes)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

#[cfg(not(target_os = "windows"))]
fn m128i_from_i32x4(lanes: [i32; 4]) -> __m128i {
    // SAFETY: `__m128i` and four i32 lanes are both exactly 16 bytes.
    unsafe { core::mem::transmute(lanes) }
}

#[cfg(not(target_os = "windows"))]
fn i32x4_from_m128i(value: __m128i) -> [i32; 4] {
    // SAFETY: `__m128i` and four i32 lanes are both exactly 16 bytes.
    unsafe { core::mem::transmute(value) }
}

fn i64_array_const(result: u32, aggregate: &Ty, a: i64, b: i64) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Array(vec![Constant::Int(a as i128), Constant::Int(b as i128)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn return_value(value: u32) -> InstrNode {
    InstrNode {
        inst: Inst::Return {
            values: vec![ValueId::new(value)],
        },
        results: vec![],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn large_struct_param_module() -> trust_ir::Module {
    // `long takes_large_struct(struct Large s) { return s.a + s.b + s.c; }`
    // A 24-byte struct is SysV MEMORY class (stack-passed by value). Summing
    // the fields makes the binding observable so a host-execution oracle can
    // confirm the bytes landed at the right incoming-frame offsets.
    let mut mb = ModuleBuilder::new("x86_64_aggregate_param");
    let struct_id = mb.add_struct(large_struct_def());
    let aggregate = Ty::Struct(struct_id);
    let ty = mb.add_func_type(vec![aggregate.clone()], vec![Ty::I64]);
    let mut fb = mb.function("takes_large_struct", ty);
    let entry = fb.create_block();
    let s = fb.add_block_param(entry, aggregate.clone());
    fb.switch_to_block(entry);
    let a = fb.extract_field(aggregate.clone(), s, 0);
    let b = fb.extract_field(aggregate.clone(), s, 1);
    let c = fb.extract_field(aggregate, s, 2);
    let ab = fb.add(Ty::I64, a, b);
    let abc = fb.add(Ty::I64, ab, c);
    fb.ret(vec![abc]);
    fb.build();
    mb.build()
}

#[cfg(not(target_os = "windows"))]
fn i32_pair_param_extract_module() -> TrustIrModule {
    // `int extracts_i32_pair_param(struct I32Pair s) { return s.b; }` — a
    // single 8-byte INTEGER eightbyte passed in RDI; reads field 1 (`b`), the
    // high 32 bits of the eightbyte.
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_i32_pair_aggregate_param_extract".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "extracts_i32_pair_param".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate.clone())],
                body: vec![
                    InstrNode {
                        inst: Inst::ExtractField {
                            ty: aggregate.clone(),
                            aggregate: ValueId::new(0),
                            field: 1,
                        },
                        results: vec![ValueId::new(1)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    return_value(1),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![unsupported_i32_pair_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![aggregate],
            returns: vec![Ty::I32],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn unsupported_i32_pair_return_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_unsupported_i32_pair_return_reject".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "returns_unsupported_i32_pair".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    i32_pair_aggregate_const(0, &aggregate, 11, 22),
                    return_value(0),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![unsupported_i32_pair_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![],
            returns: vec![aggregate],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn i32_pair_byval_call_module() -> TrustIrModule {
    // Self-contained cross-call: a trust_ir callee receives `{i32 a, i32 b}`
    // by value in one INTEGER eightbyte (RDI) and returns `a + b`; the caller
    // builds `{11, 22}` and passes it. Exercises both the caller-side argument
    // packing and the callee-side formal unpacking of the eightbyte.
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "adds_i32_pair_by_value".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), aggregate.clone())],
            body: vec![
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 0,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 1,
                    },
                    results: vec![ValueId::new(2)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::BinOp {
                        op: trust_ir::BinOp::Add,
                        ty: Ty::I32,
                        lhs: ValueId::new(1),
                        rhs: ValueId::new(2),
                    },
                    results: vec![ValueId::new(3)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(3),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_i32_pair_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                i32_pair_aggregate_const(0, &aggregate, 11, 22),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_i32_pair_byval_call".to_owned(),
        functions: vec![callee, caller],
        structs: vec![unsupported_i32_pair_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I32],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn i32_pair_call_result_module() -> TrustIrModule {
    // Self-contained cross-call: a trust_ir callee returns `{i32 a, i32 b}` in
    // RAX (one INTEGER eightbyte); the caller extracts field 1 (`b`) from the
    // returned eightbyte and returns it. Exercises the register-aggregate
    // return path on both the callee (store to RAX) and caller (read RAX) side.
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "returns_i32_pair_for_call".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                i32_pair_aggregate_const(0, &aggregate, 11, 22),
                return_value(0),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_i32_pair_result".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 1,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_i32_pair_call_result".to_owned(),
        functions: vec![callee, caller],
        structs: vec![unsupported_i32_pair_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![aggregate],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn i64_array_ty() -> Ty {
    Ty::Array(trust_ir::TyId::new(0), 2)
}

#[cfg(not(target_os = "windows"))]
fn f64_array_ty() -> Ty {
    Ty::Array(trust_ir::TyId::new(0), 2)
}

fn single_i64_struct_return_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_single_i64_aggregate_return".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "returns_single_i64_struct".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode {
                        inst: Inst::Const {
                            ty: aggregate.clone(),
                            value: Constant::Aggregate(vec![Constant::Int(0x1122_3344_5566_7788)]),
                        },
                        results: vec![ValueId::new(0)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    InstrNode {
                        inst: Inst::Return {
                            values: vec![ValueId::new(0)],
                        },
                        results: vec![],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![single_i64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![],
            returns: vec![aggregate],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn single_i64_struct_param_extract_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_single_i64_aggregate_param_extract".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "extracts_single_i64_struct_param".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate.clone())],
                body: vec![
                    InstrNode {
                        inst: Inst::ExtractField {
                            ty: aggregate.clone(),
                            aggregate: ValueId::new(0),
                            field: 0,
                        },
                        results: vec![ValueId::new(1)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    InstrNode {
                        inst: Inst::Return {
                            values: vec![ValueId::new(1)],
                        },
                        results: vec![],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![single_i64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![aggregate],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn single_i32_struct_return_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_single_i32_aggregate_return".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "returns_single_i32_struct".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    single_i32_aggregate_const(0, &aggregate, 0x1122_3344),
                    return_value(0),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![single_i32_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![],
            returns: vec![aggregate],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn single_i32_struct_param_extract_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_single_i32_aggregate_param_extract".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "extracts_single_i32_struct_param".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate.clone())],
                body: vec![
                    InstrNode {
                        inst: Inst::ExtractField {
                            ty: aggregate.clone(),
                            aggregate: ValueId::new(0),
                            field: 0,
                        },
                        results: vec![ValueId::new(1)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    return_value(1),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![single_i32_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![aggregate],
            returns: vec![Ty::I32],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn small_struct_param_extract_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_small_aggregate_param_extract".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "extracts_small_struct_param".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate.clone())],
                body: vec![
                    InstrNode {
                        inst: Inst::ExtractField {
                            ty: aggregate.clone(),
                            aggregate: ValueId::new(0),
                            field: 1,
                        },
                        results: vec![ValueId::new(1)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    return_value(1),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![small_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![aggregate],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn i64_array_param_extract_module() -> TrustIrModule {
    let aggregate = i64_array_ty();
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_sysv_i64_array_formal_extract".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "extracts_i64_array_param".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate.clone())],
                body: vec![
                    i64_const(1, 1),
                    InstrNode {
                        inst: Inst::ExtractElement {
                            ty: Ty::I64,
                            array: ValueId::new(0),
                            index: ValueId::new(1),
                        },
                        results: vec![ValueId::new(2)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    return_value(2),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![aggregate],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        types: vec![Ty::I64],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn single_i64_struct_call_extract_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "returns_single_i64_struct_for_call".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Const {
                        ty: aggregate.clone(),
                        value: Constant::Aggregate(vec![Constant::Int(0x1020_3040_5060_7080)]),
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::Return {
                        values: vec![ValueId::new(0)],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_single_i64_struct_and_extracts".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 0,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::Return {
                        values: vec![ValueId::new(1)],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let passthrough = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(2),
        name: "calls_single_i64_struct_and_returns".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::Return {
                        values: vec![ValueId::new(0)],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_single_i64_aggregate_call_extract".to_owned(),
        functions: vec![callee, caller, passthrough],
        structs: vec![single_i64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![aggregate],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn single_i64_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "extracts_single_i64_struct_by_value".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), aggregate.clone())],
            body: vec![
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 0,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_single_i64_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                single_i64_aggregate_const(0, &aggregate, 0x2132_4354_6576_0788),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_single_i64_aggregate_byval_call".to_owned(),
        functions: vec![callee, caller],
        structs: vec![single_i64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn native_single_i64_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_single_i64_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_single_i64_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                single_i64_aggregate_const(0, &aggregate, 0x0102_0304_0506_0708),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_native_single_i64_aggregate_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![single_i64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn single_i32_struct_call_extract_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "returns_single_i32_struct_for_call".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                single_i32_aggregate_const(0, &aggregate, 0x1020_3040),
                return_value(0),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    let extract_caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_single_i32_struct_and_extracts".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 0,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let passthrough = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(2),
        name: "calls_single_i32_struct_and_returns".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(0),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_single_i32_aggregate_call_extract".to_owned(),
        functions: vec![callee, extract_caller, passthrough],
        structs: vec![single_i32_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![aggregate],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn single_i32_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "extracts_single_i32_struct_by_value".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), aggregate.clone())],
            body: vec![
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 0,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_single_i32_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                single_i32_aggregate_const(0, &aggregate, 0x2132_4354),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_single_i32_aggregate_byval_call".to_owned(),
        functions: vec![callee, caller],
        structs: vec![single_i32_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I32],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn native_single_i32_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_single_i32_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_single_i32_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                single_i32_aggregate_const(0, &aggregate, 0x0102_0304),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_native_single_i32_aggregate_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![single_i32_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I32],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn small_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "extracts_small_struct_by_value".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), aggregate.clone())],
            body: vec![
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 1,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_small_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                small_aggregate_const(0, &aggregate, 0x1122_3344_5566_7788, 0x1020_3040_5060_7080),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_small_aggregate_byval_call".to_owned(),
        functions: vec![callee, caller],
        structs: vec![small_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn i64_array_byval_call_module() -> TrustIrModule {
    let aggregate = i64_array_ty();
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "extracts_i64_array_by_value".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), aggregate.clone())],
            body: vec![
                i64_const(1, 1),
                InstrNode {
                    inst: Inst::ExtractElement {
                        ty: Ty::I64,
                        array: ValueId::new(0),
                        index: ValueId::new(1),
                    },
                    results: vec![ValueId::new(2)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(2),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_i64_array_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                i64_array_const(0, &aggregate, 0x3141_5926_5358_9793, 0x2718_2818_2845_9045),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_i64_array_byval_call".to_owned(),
        functions: vec![callee, caller],
        structs: vec![],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![Ty::I64],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn native_small_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_small_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_small_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                small_aggregate_const(0, &aggregate, 11, 22),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_native_small_aggregate_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![small_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_i64_array_byval_call_module() -> TrustIrModule {
    let aggregate = i64_array_ty();
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_i64_array_lanes".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_i64_array_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                i64_array_const(0, &aggregate, 13, 29),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_i64_array_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![Ty::I64],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn f64_array_const(result: u32, aggregate: &Ty, a: f64, b: f64) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Array(vec![Constant::Float(a), Constant::Float(b)]),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

#[cfg(not(target_os = "windows"))]
fn native_two_f64_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_two_f64_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_two_f64_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                two_f64_aggregate_const(0, &aggregate, 2.5, 4.25),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_two_f64_struct_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![two_f64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_f64_array_byval_call_module() -> TrustIrModule {
    let aggregate = f64_array_ty();
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_f64_array_lanes".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_f64_array_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                f64_array_const(0, &aggregate, 1.25, 3.75),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_f64_array_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
        ],
        types: vec![Ty::F64],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_two_f64_struct_call_result_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_returns_two_f64_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "reads_native_two_f64_struct_second_field".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 1,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_two_f64_struct_call_result".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![two_f64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![aggregate],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_i64_f64_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_i64_f64_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_i64_f64_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                i64_f64_aggregate_const(0, &aggregate, 19, 3.5),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_i64_f64_struct_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![i64_f64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_i64_f64_struct_call_result_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let f64_caller_ty = FuncTyId::new(1);
    let i64_caller_ty = FuncTyId::new(2);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_returns_i64_f64_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let f64_caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "reads_native_i64_f64_struct_f64_field".to_owned(),
        ty: f64_caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 1,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let i64_caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(2),
        name: "reads_native_i64_f64_struct_i64_field".to_owned(),
        ty: i64_caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 0,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_i64_f64_struct_call_result".to_owned(),
        functions: vec![extern_decl, f64_caller, i64_caller],
        structs: vec![i64_f64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![aggregate],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_f64_i64_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_f64_i64_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_f64_i64_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                f64_i64_aggregate_const(0, &aggregate, 6.5, 23),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_f64_i64_struct_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![f64_i64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_f64_i64_struct_call_result_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let f64_caller_ty = FuncTyId::new(1);
    let i64_caller_ty = FuncTyId::new(2);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_returns_f64_i64_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let f64_caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "reads_native_f64_i64_struct_f64_field".to_owned(),
        ty: f64_caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 0,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let i64_caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(2),
        name: "reads_native_f64_i64_struct_i64_field".to_owned(),
        ty: i64_caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 1,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_f64_i64_struct_call_result".to_owned(),
        functions: vec![extern_decl, f64_caller, i64_caller],
        structs: vec![f64_i64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![aggregate],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::F64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn v128_carrier_struct_param_extract_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let vector = v4i32_ty();
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_sysv_v128_carrier_formal_extract".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "extracts_v128_carrier_struct_param".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate.clone())],
                body: vec![
                    InstrNode {
                        inst: Inst::ExtractField {
                            ty: aggregate.clone(),
                            aggregate: ValueId::new(0),
                            field: 0,
                        },
                        results: vec![ValueId::new(1)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    return_value(1),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![v128_carrier_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![aggregate],
            returns: vec![vector],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn v128_carrier_struct_return_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_sysv_v128_carrier_return".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "returns_v128_carrier_struct".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    v128_carrier_aggregate_const(0, &aggregate, [3, -5, 7, -11]),
                    return_value(0),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![v128_carrier_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![],
            returns: vec![aggregate],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_v128_carrier_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let vector = v4i32_ty();
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_v128_carrier_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_v128_carrier_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                v128_carrier_aggregate_const(0, &aggregate, [13, -17, 23, -29]),
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![ValueId::new(0)],
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_v128_carrier_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![v128_carrier_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![aggregate],
                returns: vec![vector],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![v4i32_ty()],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(not(target_os = "windows"))]
fn native_v128_carrier_struct_call_result_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let vector = v4i32_ty();
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_returns_v128_carrier_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "reads_native_v128_carrier_struct_result".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::ExtractField {
                        ty: aggregate.clone(),
                        aggregate: ValueId::new(0),
                        field: 0,
                    },
                    results: vec![ValueId::new(1)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(1),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_sysv_native_v128_carrier_call_result".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![v128_carrier_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![aggregate],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![vector],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn native_spilled_single_i64_struct_byval_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let callee_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);
    let mut body = vec![
        i64_const(0, 1),
        i64_const(1, 2),
        i64_const(2, 3),
        i64_const(3, 4),
        i64_const(4, 5),
        i64_const(5, 6),
        single_i64_aggregate_const(6, &aggregate, 7000),
    ];
    body.push(InstrNode {
        inst: Inst::Call {
            callee: FuncId::new(0),
            args: (0..7u32).map(ValueId::new).collect(),
        },
        results: vec![ValueId::new(7)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    });
    body.push(return_value(7));

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_accepts_spilled_single_i64_struct".to_owned(),
        ty: callee_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_spilled_single_i64_struct_by_value".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body,
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_native_spilled_single_i64_aggregate_byval_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![single_i64_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![
                    Ty::I64,
                    Ty::I64,
                    Ty::I64,
                    Ty::I64,
                    Ty::I64,
                    Ty::I64,
                    aggregate,
                ],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn small_struct_return_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    TrustIrModule {
        name: "x86_64_small_aggregate_return_reject".to_owned(),
        functions: vec![TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(0),
            name: "returns_small_struct".to_owned(),
            ty: func_ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode {
                        inst: Inst::Const {
                            ty: aggregate.clone(),
                            value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
                        },
                        results: vec![ValueId::new(0)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    InstrNode {
                        inst: Inst::Return {
                            values: vec![ValueId::new(0)],
                        },
                        results: vec![],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }],
        structs: vec![small_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![],
            returns: vec![aggregate],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn small_struct_call_result_passthrough_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "returns_small_struct_for_call".to_owned(),
        ty: func_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Const {
                        ty: aggregate.clone(),
                        value: Constant::Aggregate(vec![
                            Constant::Int(0x1122_3344_5566_7788),
                            Constant::Int(0x1020_3040_5060_7080),
                        ]),
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(0),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_small_struct_result_and_returns".to_owned(),
        ty: func_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                return_value(0),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_small_aggregate_sret_cross_call".to_owned(),
        functions: vec![callee, caller],
        structs: vec![small_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![],
            returns: vec![aggregate],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn native_large_struct_call_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "native_returns_large_struct".to_owned(),
        ty: func_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_native_large_struct".to_owned(),
        ty: func_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::Return {
                        values: vec![ValueId::new(0)],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_native_aggregate_sret_call".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![large_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![],
            returns: vec![aggregate],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

fn large_struct_call_result_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let func_ty = FuncTyId::new(0);

    let callee = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "returns_large_struct".to_owned(),
        ty: func_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Const {
                        ty: aggregate.clone(),
                        value: Constant::Aggregate(vec![
                            Constant::Int(7),
                            Constant::Int(42),
                            Constant::Int(99),
                        ]),
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::Return {
                        values: vec![ValueId::new(0)],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "calls_large_struct_result".to_owned(),
        ty: func_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::Return {
                        values: vec![ValueId::new(0)],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_aggregate_sret_cross_call".to_owned(),
        functions: vec![callee, caller],
        structs: vec![large_struct_def()],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![FuncTy {
            params: vec![],
            returns: vec![aggregate],
            is_vararg: false,
        }],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(target_os = "windows")]
fn expect_x86_aggregate_abi_rejection(module: trust_ir::Module, position: &str, size: u32) {
    let err = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect_err("x86-64 host JIT must reject aggregate ABI before executable publication");

    let CompileError::Pipeline(PipelineError::ISel(message)) = err else {
        panic!("expected public x86-64 ISel rejection, got {err:?}");
    };

    assert!(
        message.contains("unsupported x86-64 aggregate ABI"),
        "missing aggregate ABI rejection in: {message}"
    );
    assert!(
        message.contains(position),
        "missing ABI position `{position}` in: {message}"
    );
    assert!(
        message.contains(&format!("for {position} 0")),
        "missing ABI position/index detail in: {message}"
    );
    assert!(
        message.contains("Struct") && message.contains(&format!("{size} bytes")),
        "missing typed aggregate size detail in: {message}"
    );
    assert!(
        message.contains("under "),
        "missing ABI name detail in: {message}"
    );
}

// A 24-byte struct formal is SysV MEMORY class: passed by value on the stack.
// This previously asserted a fail-closed rejection (the incompleteness this work
// fixes); on a SysV host it now compiles and executes correctly. Windows x64 has
// no MEMORY-class by-value path for this shape, so it still fails closed.
#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_executes_sysv_large_struct_formal() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&large_struct_param_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile a >16-byte by-value struct formal");

    let f: extern "C" fn(Large) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("takes_large_struct")
            .expect("takes_large_struct symbol")
            .into_inner()
    };

    assert_eq!(
        f(Large {
            a: 0x1122_3344_5566_7788,
            b: -0x0102_0304_0506_0708,
            c: 1_000_000_007
        }),
        0x1122_3344_5566_7788_i64
            .wrapping_add(-0x0102_0304_0506_0708_i64)
            .wrapping_add(1_000_000_007),
    );
}

#[cfg(target_os = "windows")]
#[test]
fn host_jit_rejects_large_struct_formal_before_publication() {
    expect_x86_aggregate_abi_rejection(large_struct_param_module(), "formal parameter", 24);
}

// A `{i32, i32}` struct is a valid System V register aggregate (one INTEGER
// eightbyte). These four tests previously asserted it was *rejected* — that was
// the silent-wrong incompleteness this work fixes. They now verify the eightbyte
// ABI executes correctly on the host instead.
#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_extracts_sysv_i32_pair_formal_in_one_gpr() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&i32_pair_param_extract_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile {i32,i32} eightbyte formal");

    let f: extern "C" fn(I32Pair) -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("extracts_i32_pair_param")
            .expect("extracts_i32_pair_param symbol")
            .into_inner()
    };

    assert_eq!(
        f(I32Pair {
            a: 0x1122_3344,
            b: 0x5566_7788
        }),
        0x5566_7788
    );
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_executes_sysv_i32_pair_return_in_rax() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&unsupported_i32_pair_return_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile {i32,i32} eightbyte return");

    let f: extern "C" fn() -> I32Pair = unsafe {
        result
            .buffer
            .get_fn_bound("returns_unsupported_i32_pair")
            .expect("returns_unsupported_i32_pair symbol")
            .into_inner()
    };

    assert_eq!(f(), I32Pair { a: 11, b: 22 });
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_i32_pair_by_value_to_trust_ir_callee() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&i32_pair_byval_call_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile {i32,i32} eightbyte by-value call");

    let f: extern "C" fn() -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_i32_pair_by_value")
            .expect("calls_i32_pair_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), 11 + 22);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_extracts_sysv_i32_pair_call_result() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&i32_pair_call_result_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile {i32,i32} eightbyte cross-call result");

    let f: extern "C" fn() -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_i32_pair_result")
            .expect("calls_i32_pair_result symbol")
            .into_inner()
    };

    assert_eq!(f(), 22);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_extracts_sysv_small_struct_formal_in_gprs() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&small_struct_param_extract_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile 16-byte aggregate formal in GPRs");

    let f: extern "C" fn(Small) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("extracts_small_struct_param")
            .expect("extracts_small_struct_param symbol")
            .into_inner()
    };

    assert_eq!(
        f(Small {
            a: 0x1122_3344_5566_7788,
            b: 0x1020_3040_5060_7080
        }),
        0x1020_3040_5060_7080
    );
}

#[test]
fn host_jit_executes_single_i64_struct_return() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&single_i64_struct_return_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile single-i64 aggregate return");

    let f: extern "C" fn() -> SingleI64 = unsafe {
        result
            .buffer
            .get_fn_bound("returns_single_i64_struct")
            .expect("returns_single_i64_struct symbol")
            .into_inner()
    };

    assert_eq!(
        f(),
        SingleI64 {
            a: 0x1122_3344_5566_7788
        }
    );
}

#[test]
fn host_jit_executes_single_i32_struct_return() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&single_i32_struct_return_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile single-i32 aggregate return");

    let f: extern "C" fn() -> SingleI32 = unsafe {
        result
            .buffer
            .get_fn_bound("returns_single_i32_struct")
            .expect("returns_single_i32_struct symbol")
            .into_inner()
    };

    assert_eq!(f(), SingleI32 { a: 0x1122_3344 });
}

#[test]
fn host_jit_extracts_single_i64_struct_formal() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&single_i64_struct_param_extract_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile single-i64 aggregate formal");

    let f: extern "C" fn(SingleI64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("extracts_single_i64_struct_param")
            .expect("extracts_single_i64_struct_param symbol")
            .into_inner()
    };

    assert_eq!(
        f(SingleI64 {
            a: 0x1234_5678_1234_5678
        }),
        0x1234_5678_1234_5678
    );
}

#[test]
fn host_jit_extracts_single_i32_struct_formal() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&single_i32_struct_param_extract_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile single-i32 aggregate formal");

    let f: extern "C" fn(SingleI32) -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("extracts_single_i32_struct_param")
            .expect("extracts_single_i32_struct_param symbol")
            .into_inner()
    };

    assert_eq!(f(SingleI32 { a: 0x1234_5678 }), 0x1234_5678);
}

#[cfg(target_os = "windows")]
#[test]
fn host_jit_extracts_windows_small_struct_formal_byref() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&small_struct_param_extract_module(), &HashMap::new())
        .expect("Windows x64 host JIT should compile 16-byte aggregate formal by reference");

    let f: extern "C" fn(Small) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("extracts_small_struct_param")
            .expect("extracts_small_struct_param symbol")
            .into_inner()
    };

    assert_eq!(
        f(Small {
            a: 0x1122_3344_5566_7788,
            b: 0x1020_3040_5060_7080
        }),
        0x1020_3040_5060_7080
    );
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_extracts_sysv_i64_array_formal_in_gprs() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&i64_array_param_extract_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile [i64; 2] aggregate formal in GPRs");

    let f: extern "C" fn(i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("extracts_i64_array_param")
            .expect("extracts_i64_array_param symbol")
            .into_inner()
    };

    assert_eq!(
        f(0x1122_3344_5566_7788, 0x1020_3040_5060_7080),
        0x1020_3040_5060_7080
    );
}

#[test]
fn host_jit_extracts_single_i64_struct_call_result() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&single_i64_struct_call_extract_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile single-i64 aggregate cross-call");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_single_i64_struct_and_extracts")
            .expect("calls_single_i64_struct_and_extracts symbol")
            .into_inner()
    };

    assert_eq!(f(), 0x1020_3040_5060_7080);

    let g: extern "C" fn() -> SingleI64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_single_i64_struct_and_returns")
            .expect("calls_single_i64_struct_and_returns symbol")
            .into_inner()
    };

    assert_eq!(
        g(),
        SingleI64 {
            a: 0x1020_3040_5060_7080
        }
    );
}

#[test]
fn host_jit_extracts_single_i32_struct_call_result() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&single_i32_struct_call_extract_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile single-i32 aggregate cross-call");

    let f: extern "C" fn() -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_single_i32_struct_and_extracts")
            .expect("calls_single_i32_struct_and_extracts symbol")
            .into_inner()
    };

    assert_eq!(f(), 0x1020_3040);

    let g: extern "C" fn() -> SingleI32 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_single_i32_struct_and_returns")
            .expect("calls_single_i32_struct_and_returns symbol")
            .into_inner()
    };

    assert_eq!(g(), SingleI32 { a: 0x1020_3040 });
}

#[test]
fn host_jit_passes_single_i64_struct_by_value_to_trust_ir_callee() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&single_i64_struct_byval_call_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile single-i64 aggregate by-value call");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_single_i64_struct_by_value")
            .expect("calls_single_i64_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), 0x2132_4354_6576_0788);
}

#[test]
fn host_jit_passes_single_i32_struct_by_value_to_trust_ir_callee() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&single_i32_struct_byval_call_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile single-i32 aggregate by-value call");

    let f: extern "C" fn() -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_single_i32_struct_by_value")
            .expect("calls_single_i32_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), 0x2132_4354);
}

#[cfg(target_os = "windows")]
#[test]
fn host_jit_passes_windows_small_struct_byref_to_trust_ir_callee() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&small_struct_byval_call_module(), &HashMap::new())
        .expect("Windows x64 host JIT should compile 16-byte aggregate by-value trust_ir call");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_small_struct_by_value")
            .expect("calls_small_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), 0x1020_3040_5060_7080);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_small_struct_in_gprs_to_trust_ir_callee() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&small_struct_byval_call_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile 16-byte aggregate by-value trust_ir call");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_small_struct_by_value")
            .expect("calls_small_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), 0x1020_3040_5060_7080);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_i64_array_in_gprs_to_trust_ir_callee() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&i64_array_byval_call_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile [i64; 2] aggregate by-value trust_ir call");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_i64_array_by_value")
            .expect("calls_i64_array_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), 0x2718_2818_2845_9045);
}

#[cfg(target_os = "windows")]
#[test]
fn host_jit_passes_windows_i64_array_byref_to_trust_ir_callee() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&i64_array_byval_call_module(), &HashMap::new())
        .expect("Windows x64 host JIT should compile [i64; 2] aggregate byref trust_ir call");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_i64_array_by_value")
            .expect("calls_i64_array_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), 0x2718_2818_2845_9045);
}

#[test]
fn host_jit_passes_single_i64_struct_by_value_to_native_callback() {
    let arg = SingleI64 {
        a: 0x0102_0304_0506_0708,
    };
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_single_i64_struct".to_string(),
        native_accepts_single_i64_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_single_i64_struct_byval_call_module(), &externs)
        .expect("x86-64 host JIT should compile native single-i64 aggregate callback");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_single_i64_struct_by_value")
            .expect("calls_native_single_i64_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_single_i64_struct(arg));
}

#[test]
fn host_jit_passes_single_i32_struct_by_value_to_native_callback() {
    let arg = SingleI32 { a: 0x0102_0304 };
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_single_i32_struct".to_string(),
        native_accepts_single_i32_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_single_i32_struct_byval_call_module(), &externs)
        .expect("x86-64 host JIT should compile native single-i32 aggregate callback");

    let f: extern "C" fn() -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_single_i32_struct_by_value")
            .expect("calls_native_single_i32_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_single_i32_struct(arg));
}

#[cfg(target_os = "windows")]
#[test]
fn host_jit_passes_windows_small_struct_byref_to_native_callback() {
    let arg = Small { a: 11, b: 22 };
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_small_struct".to_string(),
        native_accepts_small_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_small_struct_byval_call_module(), &externs)
        .expect("Windows x64 host JIT should compile native 16-byte aggregate callback");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_small_struct_by_value")
            .expect("calls_native_small_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_small_struct(arg));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_small_struct_in_gprs_to_native_callback() {
    let arg = Small { a: 11, b: 22 };
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_small_struct".to_string(),
        native_accepts_small_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_small_struct_byval_call_module(), &externs)
        .expect("SysV x86-64 host JIT should compile native 16-byte aggregate callback");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_small_struct_by_value")
            .expect("calls_native_small_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_small_struct(arg));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_i64_array_in_gprs_to_native_callback() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_i64_array_lanes".to_string(),
        native_accepts_i64_array_lanes as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_i64_array_byval_call_module(), &externs)
        .expect("SysV x86-64 host JIT should compile native [i64; 2] aggregate callback");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_i64_array_by_value")
            .expect("calls_native_i64_array_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_i64_array_lanes(13, 29));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_two_f64_struct_in_xmms_to_native_callback() {
    let arg = TwoF64 { a: 2.5, b: 4.25 };
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_two_f64_struct".to_string(),
        native_accepts_two_f64_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_two_f64_struct_byval_call_module(), &externs)
        .expect("SysV x86-64 host JIT should pass {f64,f64} in XMM registers");

    let f: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_two_f64_struct_by_value")
            .expect("calls_native_two_f64_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_two_f64_struct(arg));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_f64_array_in_xmms_to_native_callback() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_f64_array_lanes".to_string(),
        native_accepts_f64_array_lanes as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_f64_array_byval_call_module(), &externs)
        .expect("SysV x86-64 host JIT should pass [f64; 2] in XMM registers");

    let f: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_f64_array_by_value")
            .expect("calls_native_f64_array_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_f64_array_lanes(1.25, 3.75));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_extracts_sysv_v128_carrier_struct_formal_in_xmm0() {
    let result = v128_dev_host_compiler()
        .compile_module_to_jit(&v128_carrier_struct_param_extract_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should accept V128 carrier formal in XMM0");

    #[allow(improper_ctypes_definitions)]
    type Run = extern "C" fn(V128Carrier) -> __m128i;
    let f: Run = unsafe {
        result
            .buffer
            .get_fn_bound("extracts_v128_carrier_struct_param")
            .expect("extracts_v128_carrier_struct_param symbol")
            .into_inner()
    };

    let lanes = [5, -8, 13, -21];
    let actual = i32x4_from_m128i(f(V128Carrier {
        lanes: m128i_from_i32x4(lanes),
    }));
    assert_eq!(actual, lanes);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_returns_sysv_v128_carrier_struct_in_xmm0() {
    let result = v128_dev_host_compiler()
        .compile_module_to_jit(&v128_carrier_struct_return_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should return a V128 carrier in XMM0");

    #[allow(improper_ctypes_definitions)]
    type Run = extern "C" fn() -> V128Carrier;
    let f: Run = unsafe {
        result
            .buffer
            .get_fn_bound("returns_v128_carrier_struct")
            .expect("returns_v128_carrier_struct symbol")
            .into_inner()
    };

    assert_eq!(i32x4_from_m128i(f().lanes), [3, -5, 7, -11]);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_v128_carrier_struct_by_value_to_native_callback() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_v128_carrier_struct".to_string(),
        native_accepts_v128_carrier_struct as *const () as *const u8,
    );

    let result = v128_dev_host_compiler()
        .compile_module_to_jit(&native_v128_carrier_struct_byval_call_module(), &externs)
        .expect("SysV x86-64 host JIT should pass a V128 carrier by value in one XMM");

    #[allow(improper_ctypes_definitions)]
    type Run = extern "C" fn() -> __m128i;
    let f: Run = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_v128_carrier_struct_by_value")
            .expect("calls_native_v128_carrier_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(i32x4_from_m128i(f()), [13, -17, 23, -29]);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_reads_sysv_v128_carrier_struct_call_result_from_xmm0() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_returns_v128_carrier_struct".to_string(),
        native_returns_v128_carrier_struct as *const () as *const u8,
    );

    let result = v128_dev_host_compiler()
        .compile_module_to_jit(&native_v128_carrier_struct_call_result_module(), &externs)
        .expect("SysV x86-64 host JIT should read a V128 carrier call result from XMM0");

    #[allow(improper_ctypes_definitions)]
    type Run = extern "C" fn() -> __m128i;
    let f: Run = unsafe {
        result
            .buffer
            .get_fn_bound("reads_native_v128_carrier_struct_result")
            .expect("reads_native_v128_carrier_struct_result symbol")
            .into_inner()
    };

    assert_eq!(i32x4_from_m128i(f()), [31, -37, 41, -43]);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_reads_sysv_two_f64_struct_result_from_xmm0_xmm1() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_returns_two_f64_struct".to_string(),
        native_returns_two_f64_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_two_f64_struct_call_result_module(), &externs)
        .expect("SysV x86-64 host JIT should read {f64,f64} from XMM return registers");

    let f: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("reads_native_two_f64_struct_second_field")
            .expect("reads_native_two_f64_struct_second_field symbol")
            .into_inner()
    };

    assert_eq!(f(), native_returns_two_f64_struct().b);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_i64_f64_struct_in_gpr_xmm_to_native_callback() {
    let arg = I64F64 { a: 19, b: 3.5 };
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_i64_f64_struct".to_string(),
        native_accepts_i64_f64_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_i64_f64_struct_byval_call_module(), &externs)
        .expect("SysV x86-64 host JIT should pass {i64,f64} in GPR+XMM registers");

    let f: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_i64_f64_struct_by_value")
            .expect("calls_native_i64_f64_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_i64_f64_struct(arg));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_passes_sysv_f64_i64_struct_in_xmm_gpr_to_native_callback() {
    let arg = F64I64 { a: 6.5, b: 23 };
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_f64_i64_struct".to_string(),
        native_accepts_f64_i64_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_f64_i64_struct_byval_call_module(), &externs)
        .expect("SysV x86-64 host JIT should pass {f64,i64} in XMM+GPR registers");

    let f: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_f64_i64_struct_by_value")
            .expect("calls_native_f64_i64_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(f(), native_accepts_f64_i64_struct(arg));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_reads_sysv_i64_f64_struct_result_from_rax_xmm0() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_returns_i64_f64_struct".to_string(),
        native_returns_i64_f64_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_i64_f64_struct_call_result_module(), &externs)
        .expect("SysV x86-64 host JIT should read {i64,f64} from RAX+XMM0");

    let f64_field: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("reads_native_i64_f64_struct_f64_field")
            .expect("reads_native_i64_f64_struct_f64_field symbol")
            .into_inner()
    };
    let i64_field: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("reads_native_i64_f64_struct_i64_field")
            .expect("reads_native_i64_f64_struct_i64_field symbol")
            .into_inner()
    };

    let expected = native_returns_i64_f64_struct();
    assert_eq!(f64_field(), expected.b);
    assert_eq!(i64_field(), expected.a);
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_reads_sysv_f64_i64_struct_result_from_xmm0_rax() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_returns_f64_i64_struct".to_string(),
        native_returns_f64_i64_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_f64_i64_struct_call_result_module(), &externs)
        .expect("SysV x86-64 host JIT should read {f64,i64} from XMM0+RAX");

    let f64_field: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("reads_native_f64_i64_struct_f64_field")
            .expect("reads_native_f64_i64_struct_f64_field symbol")
            .into_inner()
    };
    let i64_field: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("reads_native_f64_i64_struct_i64_field")
            .expect("reads_native_f64_i64_struct_i64_field symbol")
            .into_inner()
    };

    let expected = native_returns_f64_i64_struct();
    assert_eq!(f64_field(), expected.a);
    assert_eq!(i64_field(), expected.b);
}

#[test]
fn host_jit_passes_spilled_single_i64_struct_by_value_to_native_callback() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_accepts_spilled_single_i64_struct".to_string(),
        native_accepts_spilled_single_i64_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(
            &native_spilled_single_i64_struct_byval_call_module(),
            &externs,
        )
        .expect("x86-64 host JIT should compile spilled native aggregate callback");

    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_spilled_single_i64_struct_by_value")
            .expect("calls_native_spilled_single_i64_struct_by_value symbol")
            .into_inner()
    };

    assert_eq!(
        f(),
        native_accepts_spilled_single_i64_struct(1, 2, 3, 4, 5, 6, SingleI64 { a: 7000 })
    );
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_executes_sysv_small_struct_return_in_rax_rdx() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&small_struct_return_module(), &HashMap::new())
        .expect("SysV x86-64 host JIT should compile 16-byte aggregate return in RAX/RDX");

    let f: extern "C" fn() -> Small = unsafe {
        result
            .buffer
            .get_fn_bound("returns_small_struct")
            .expect("returns_small_struct symbol")
            .into_inner()
    };

    assert_eq!(f(), Small { a: 1, b: 2 });
}

#[cfg(not(target_os = "windows"))]
#[test]
fn host_jit_executes_sysv_small_struct_call_result_in_rax_rdx() {
    let result = Compiler::for_host()
        .compile_module_to_jit(
            &small_struct_call_result_passthrough_module(),
            &HashMap::new(),
        )
        .expect("SysV x86-64 host JIT should compile 16-byte aggregate cross-call in RAX/RDX");

    let f: extern "C" fn() -> Small = unsafe {
        result
            .buffer
            .get_fn_bound("calls_small_struct_result_and_returns")
            .expect("calls_small_struct_result_and_returns symbol")
            .into_inner()
    };

    assert_eq!(
        f(),
        Small {
            a: 0x1122_3344_5566_7788,
            b: 0x1020_3040_5060_7080
        }
    );
}

#[cfg(target_os = "windows")]
#[test]
fn host_jit_executes_windows_small_struct_return_via_sret() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&small_struct_return_module(), &HashMap::new())
        .expect("Windows x64 host JIT should compile 16-byte aggregate sret return");

    let f: extern "C" fn() -> Small = unsafe {
        result
            .buffer
            .get_fn_bound("returns_small_struct")
            .expect("returns_small_struct symbol")
            .into_inner()
    };

    assert_eq!(f(), Small { a: 1, b: 2 });
}

#[cfg(target_os = "windows")]
#[test]
fn host_jit_executes_windows_small_struct_sret_cross_call() {
    let result = Compiler::for_host()
        .compile_module_to_jit(
            &small_struct_call_result_passthrough_module(),
            &HashMap::new(),
        )
        .expect("Windows x64 host JIT should compile 16-byte aggregate sret cross-call");

    let f: extern "C" fn() -> Small = unsafe {
        result
            .buffer
            .get_fn_bound("calls_small_struct_result_and_returns")
            .expect("calls_small_struct_result_and_returns symbol")
            .into_inner()
    };

    assert_eq!(
        f(),
        Small {
            a: 0x1122_3344_5566_7788,
            b: 0x1020_3040_5060_7080
        }
    );
}

#[test]
fn host_jit_executes_large_struct_sret_cross_call() {
    let result = Compiler::for_host()
        .compile_module_to_jit(&large_struct_call_result_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile large aggregate sret cross-call");

    let f: extern "C" fn() -> Large = unsafe {
        result
            .buffer
            .get_fn_bound("calls_large_struct_result")
            .expect("calls_large_struct_result symbol")
            .into_inner()
    };

    assert_eq!(f(), Large { a: 7, b: 42, c: 99 });
}

#[test]
fn host_jit_calls_native_large_struct_sret_function() {
    let mut externs = HashMap::new();
    externs.insert(
        "native_returns_large_struct".to_string(),
        native_returns_large_struct as *const () as *const u8,
    );

    let result = Compiler::for_host()
        .compile_module_to_jit(&native_large_struct_call_module(), &externs)
        .expect("x86-64 host JIT should compile native aggregate sret callback");

    let f: extern "C" fn() -> Large = unsafe {
        result
            .buffer
            .get_fn_bound("calls_native_large_struct")
            .expect("calls_native_large_struct symbol")
            .into_inner()
    };

    assert_eq!(
        f(),
        Large {
            a: 11,
            b: 22,
            c: 33
        }
    );
}
