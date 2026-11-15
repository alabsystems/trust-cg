// trust-cg-codegen/tests/e2e_aarch64_swift_aggregate.rs
//
// Completeness: the AGGREGATE subset of the `Swift` (swiftcall) calling
// convention on aarch64-apple-darwin. Unlike the C ABI (DarwinPCS), swiftcall
// lowers aggregates FIELD-WISE: a 17-32 byte all-integer struct is passed and
// returned directly in x0-x3 (C uses sret / a byref pointer); a mixed int+FP
// struct splits its integer fields into GPRs and gives EACH FP scalar field its
// own FPR (C packs FP bits into GPRs). trust-cg reproduces this by SCALARIZING
// such a swiftcc signature into a flat scalar signature (one i64 per GPR word,
// one f32/f64 per FP field) before lowering, so the C register ABI's
// independent GPR/FPR counters place the lanes in EXACTLY Swift's registers.
//
// This is a differential test: a clang driver declares each trust-cg-compiled
// function `__attribute__((swiftcall))` with the ORIGINAL aggregate prototype
// and checks that the values round-trip / sum correctly. Because trust-cg's
// scalarized layout coincides with clang's swiftcall layout, the checks pass --
// which is exactly what proves the coincidence, bit-exact at O0 and O2. The
// objects are compiled for an explicit `aarch64-apple-darwin` target on every
// host; only macOS links and runs them.
//
// The scalarization is bound to that witnessed Darwin contract (c6d2228c6).
// Under AAPCS64 (`aarch64-unknown-linux-gnu`) no swiftcall aggregate layout has
// been witnessed, so every one of these shapes is refused by name as an
// unsupported calling convention; that refusal is pinned here per shape,
// beside a scalar swiftcc control that AAPCS64 still admits.
//
// A budget >= 5 struct (>4 combined GPR-word + FP-field components) is OUTSIDE
// the sound subset -- swiftcall passes it indirectly / via sret, which trust-cg
// keeps FAIL-CLOSED (a named compile error), pinned here too, as is a packed
// struct whose layout is not natural-C.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_lower::AdapterError;

use trust_ir::{
    BinOp, Block as TrustIrBlock, CallingConv, CastOp, FieldDef, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, StructDef, StructId,
    StructRepr, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

// The witnessed swiftcall contract (DarwinPCS, Mach-O) and the AAPCS64 ELF
// target on which no swiftcall aggregate layout has been witnessed.
const DARWIN: &str = "aarch64-apple-darwin";
const AAPCS64_LINUX: &str = "aarch64-unknown-linux-gnu";

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// A C-repr struct type whose ABI matches the clang driver's `struct`.
fn struct_def(id: u32, name: &str, fields: &[Ty]) -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(id),
        name: name.to_string(),
        fields: fields
            .iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: format!("f{i}"),
                ty: ty.clone(),
                offset: None,
            })
            .collect(),
        size: None,
        align: None,
        repr: StructRepr::C,
    }
}

// swiftcc `fn id(s: Agg) -> Agg { s }` -- exercises the aggregate param
// (register -> reconstructed slot) AND the aggregate return (slot -> registers)
// in one shot: the driver passes a struct by swiftcall and gets it back, so the
// trust-cg lane<->register mapping must match clang's swiftcall exactly or the
// round-trip scrambles.
fn build_identity(m: &mut TrustIrModule, fid: u32, name: &str, struct_id: u32) {
    let agg = Ty::Struct(StructId::new(struct_id));
    let ft = m
        .add_func_type(FuncTy {
            params: vec![agg.clone()],
            returns: vec![agg.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(fid), name, ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

// swiftcc `fn sum3(s: {i64,i64,i64}) -> i64 { s.0 + s.1 + s.2 }` -- an
// aggregate PARAM whose fields are read back at their true struct offsets, so a
// wrong reconstruction offset (that a same-offset identity round-trip could
// hide) is caught. Returns a scalar (no aggregate return).
fn build_sum3(m: &mut TrustIrModule, fid: u32, name: &str, struct_id: u32) {
    let agg = Ty::Struct(StructId::new(struct_id));
    let ft = m
        .add_func_type(FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(fid), name, ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg.clone())],
        body: vec![
            InstrNode::new(Inst::ExtractField {
                ty: agg.clone(),
                aggregate: ValueId::new(0),
                field: 0,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::ExtractField {
                ty: agg.clone(),
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractField {
                ty: agg,
                aggregate: ValueId::new(0),
                field: 2,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(4),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

// swiftcc `fn summix(s: {i64,f64,i64}) -> f64 { (double)s.0 + s.1 + (double)s.2 }`
// -- a MIXED aggregate PARAM: field 0/2 (i64) reconstruct into GPR words, field
// 1 (double) into its own FPR. Reads all three at their true offsets (the int
// word and the FP field share NO 8-byte chunk).
fn build_summix(m: &mut TrustIrModule, fid: u32, name: &str, struct_id: u32) {
    let agg = Ty::Struct(StructId::new(struct_id));
    let ft = m
        .add_func_type(FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::F64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(fid), name, ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg.clone())],
        body: vec![
            // s.0 (i64) -> f64
            InstrNode::new(Inst::ExtractField {
                ty: agg.clone(),
                aggregate: ValueId::new(0),
                field: 0,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            // s.1 (f64)
            InstrNode::new(Inst::ExtractField {
                ty: agg.clone(),
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(3)),
            // s.2 (i64) -> f64
            InstrNode::new(Inst::ExtractField {
                ty: agg,
                aggregate: ValueId::new(0),
                field: 2,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(6),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

// swiftcc `fn split6(a,b,c,d,e,f: i64, s: {i64,i64,i64}) -> i64
//                    { a+b+c+d+e+f + s.0+s.1+s.2 }`
// -- the 6 leading i64s fill x0-x5, so the all-integer struct SPLITS across the
// register/stack boundary: s.0->x6, s.1->x7, s.2->[sp]. Per-scalar placement of
// the scalarized lanes must reproduce Swift's measured split exactly.
fn build_split6(m: &mut TrustIrModule, fid: u32, name: &str, struct_id: u32) {
    let agg = Ty::Struct(StructId::new(struct_id));
    let mut params: Vec<Ty> = vec![Ty::I64; 6];
    params.push(agg.clone());
    let ft = m
        .add_func_type(FuncTy {
            params,
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(fid), name, ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    let mut body = Vec::new();
    // acc = a + b + c + d + e + f  (params V0..V5)
    let mut acc = ValueId::new(0);
    let mut next = 100u32;
    for p in 1..6u32 {
        let out = ValueId::new(next);
        next += 1;
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: acc,
                rhs: ValueId::new(p),
            })
            .with_result(out),
        );
        acc = out;
    }
    // + s.0 + s.1 + s.2  (struct param V6)
    for field in 0..3u32 {
        let ef = ValueId::new(next);
        next += 1;
        body.push(
            InstrNode::new(Inst::ExtractField {
                ty: agg.clone(),
                aggregate: ValueId::new(6),
                field,
            })
            .with_result(ef),
        );
        let out = ValueId::new(next);
        next += 1;
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: acc,
                rhs: ef,
            })
            .with_result(out),
        );
        acc = out;
    }
    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    let mut params: Vec<(ValueId, Ty)> = (0..6).map(|i| (ValueId::new(i), Ty::I64)).collect();
    params.push((ValueId::new(6), agg));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params,
        body,
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

type ShapeBuilder = fn(&mut TrustIrModule, u32, &str, u32);

// Every aggregate shape in the witnessed Darwin subset, in function-id order:
// (function, builder, struct id, index of its first aggregate parameter).
const SHAPES: [(&str, ShapeBuilder, u32, usize); 7] = [
    // 24B all-int param + return -> x0-x2
    ("sw_id24", build_identity, 0, 0),
    // 24B all-int param -> i64
    ("sw_sum24", build_sum3, 0, 0),
    // 32B all-int param + return -> x0-x3
    ("sw_id32", build_identity, 1, 0),
    // {i64;double;i64} param + return -> x0,d0,x1
    ("sw_idmix", build_identity, 2, 0),
    // {i64;double;i64} param -> f64
    ("sw_summix", build_summix, 2, 0),
    // {float;float;i64;i64} -> s0,s1,x0,x1
    ("sw_idff", build_identity, 3, 0),
    // 24B all-int SPLITS x6,x7,[sp] after 6 i64s
    ("sw_split6", build_split6, 0, 6),
];

fn add_structs(m: &mut TrustIrModule) {
    // Struct ids must be distinct; func ids too.
    m.structs
        .push(struct_def(0, "S24", &[Ty::I64, Ty::I64, Ty::I64])); // 24B all-int
    m.structs
        .push(struct_def(1, "S32", &[Ty::I64, Ty::I64, Ty::I64, Ty::I64])); // 32B all-int
    m.structs
        .push(struct_def(2, "SMix", &[Ty::I64, Ty::F64, Ty::I64])); // mixed {i64;double;i64}
    m.structs
        .push(struct_def(3, "SFF", &[Ty::F32, Ty::F32, Ty::I64, Ty::I64])); // {float;float;i64;i64}
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("swift_aggregate");
    add_structs(&mut m);
    for (fid, (name, build, struct_id, _)) in SHAPES.iter().enumerate() {
        build(&mut m, fid as u32, name, *struct_id);
    }
    field_typed_extracts(&mut m);
    m
}

/// The builders spell `ExtractField.ty` as the AGGREGATE type (a legacy
/// spelling the adapter reads); trust-ir's `ExtractField.ty` is the extracted
/// FIELD's type (`OperandTypeMismatch` otherwise), and since WS7.3 every
/// ingestion entry refuses what the validator refuses. Rewrite each to the
/// struct's declared field type.
fn field_typed_extracts(m: &mut TrustIrModule) {
    let structs = m.structs.clone();
    for f in &mut m.functions {
        for block in &mut f.blocks {
            for node in &mut block.body {
                if let Inst::ExtractField { ty, field, .. } = &mut node.inst
                    && let Ty::Struct(id) = ty
                {
                    let field_ty = structs
                        .iter()
                        .find(|def| def.id == *id)
                        .and_then(|def| def.fields.get(*field as usize))
                        .map(|field| field.ty.clone())
                        .expect("ExtractField names a declared struct field");
                    *ty = field_ty;
                }
            }
        }
    }
}

// One shape per module, so each refusal names its own function.
fn build_shape_module(name: &str, build: ShapeBuilder, struct_id: u32) -> TrustIrModule {
    let mut m = TrustIrModule::new(format!("swift_aggregate_{name}"));
    add_structs(&mut m);
    build(&mut m, 0, name, struct_id);
    field_typed_extracts(&mut m);
    m
}

// swiftcc `fn add2(a: i64, b: i64) -> i64 { a + b }` -- single-register
// scalars only, which AAPCS64 places exactly as swiftcc does.
fn build_scalar_control_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("swift_scalar_control");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "sw_add2", ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

// A budget-5 (five GPR words) all-integer struct: swiftcall passes it
// indirectly / returns it via sret, which trust-cg keeps FAIL-CLOSED.
fn build_budget5_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("swift_aggregate_budget5");
    m.structs.push(struct_def(
        0,
        "S40",
        &[Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
    ));
    // `fn id5(s: {i64*5}) -> {i64*5} { s }` -- both the param and the return
    // exceed Swift's 4-component budget, so it must not compile.
    build_identity(&mut m, 0, "sw_id5", 0);
    m
}

// A PACKED struct: its real byte layout (i64 at offset 1) differs from the
// natural C layout the LIR `Type` assumes, so scalarizing it would place the
// i64 at the wrong offset. This is fail-closed rather than miscompiled.
fn build_packed_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("swift_aggregate_packed");
    m.structs.push(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "PackedI8I64".to_string(),
        fields: vec![
            FieldDef {
                name: "f0".to_string(),
                ty: Ty::I8,
                offset: None,
            },
            FieldDef {
                name: "f1".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::Packed(1),
    });
    // `fn idpk(s: packed{i8,i64}) -> packed{i8,i64} { s }` -- budget 2, but the
    // packed layout is not natural-C, so it must fail-close.
    build_identity(&mut m, 0, "sw_idpk", 0);
    m
}

// Compile for an explicit triple: `Compiler::new` would derive the OS/ABI from
// the host, and the swiftcall aggregate contract depends on it.
#[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
fn compile_for(
    triple: &str,
    module: &TrustIrModule,
    opt: OptLevel,
) -> Result<Vec<u8>, CompileError> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|r| r.object_code)
}

// The adapter's exact refusal of a swiftcc signature whose parameter `index`
// (of type `ty`) is an aggregate that the target's C register ABI does not
// place identically to swiftcall.
fn swift_aggregate_param_refusal(function: &str, index: usize, ty: &Ty) -> String {
    format!(
        "function {function} uses unsupported calling convention Swift for target aarch64; \
         Trust-CG lowers C-register-ABI conventions (C/Fast/Cold/Rust for any signature, and \
         the subset of Swift that aarch64's C ABI places identically to swiftcc: non-variadic, \
         single-register scalar parameters, and at most 4 combined integer+FP return register \
         components) and must not silently use the C ABI for a convention/signature with a \
         different register layout. Here parameter {index} ({ty:?}) is not a single-register \
         scalar (an aggregate, or a scalar with no witnessed identical placement)"
    )
}

fn assert_swift_aggregate_refused(
    result: Result<Vec<u8>, CompileError>,
    function: &str,
    index: usize,
    ty: &Ty,
    context: &str,
) {
    match result {
        Err(CompileError::Adapter(AdapterError::UnsupportedInstruction(message))) => assert_eq!(
            message,
            swift_aggregate_param_refusal(function, index, ty),
            "{context}: wrong refusal for {function}"
        ),
        Err(other) => panic!(
            "{context}: {function} must be refused as an unsupported Swift convention, \
             got {other:?}"
        ),
        Ok(_) => panic!("{context}: {function} must fail closed, but compiled"),
    }
}

const MACHO_MAGIC_64: [u8; 4] = [0xcf, 0xfa, 0xed, 0xfe];
const ELF_MAGIC: [u8; 4] = *b"\x7fELF";

// The driver declares each function with `__attribute__((swiftcall))` and the
// ORIGINAL aggregate prototype. Because trust-cg's scalarized layout coincides
// with clang's swiftcall layout, the round-trips / sums are correct.
const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#define SWIFTCALL __attribute__((swiftcall))

struct S24 { int64_t f0, f1, f2; };
struct S32 { int64_t f0, f1, f2, f3; };
struct SMix { int64_t f0; double f1; int64_t f2; };
struct SFF { float f0, f1; int64_t f2, f3; };

SWIFTCALL struct S24 sw_id24(struct S24);
SWIFTCALL int64_t sw_sum24(struct S24);
SWIFTCALL struct S32 sw_id32(struct S32);
SWIFTCALL struct SMix sw_idmix(struct SMix);
SWIFTCALL double sw_summix(struct SMix);
SWIFTCALL struct SFF sw_idff(struct SFF);
SWIFTCALL int64_t sw_split6(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, struct S24);

int main(void) {
    // 24B all-integer: direct x0,x1,x2 both ways.
    struct S24 a = { 0x1122334455667788LL, -2, 3 };
    struct S24 ra = sw_id24(a);
    if (ra.f0 != a.f0 || ra.f1 != a.f1 || ra.f2 != a.f2) { printf("id24\n"); return 1; }
    if (sw_sum24(a) != a.f0 + a.f1 + a.f2) { printf("sum24\n"); return 2; }

    // 32B all-integer: direct x0,x1,x2,x3 both ways.
    struct S32 b = { 10, -20, 0x7fffffffffffffffLL, -4 };
    struct S32 rb = sw_id32(b);
    if (rb.f0 != b.f0 || rb.f1 != b.f1 || rb.f2 != b.f2 || rb.f3 != b.f3) { printf("id32\n"); return 3; }

    // Mixed {i64;double;i64}: x0, d0, x1 (int field and FP field in separate banks).
    struct SMix m = { -7, 3.5, 99 };
    struct SMix rm = sw_idmix(m);
    if (rm.f0 != m.f0 || rm.f1 != m.f1 || rm.f2 != m.f2) { printf("idmix\n"); return 4; }
    double want = (double)m.f0 + m.f1 + (double)m.f2;
    if (sw_summix(m) != want) { printf("summix\n"); return 5; }

    // {float;float;i64;i64}: two floats each get their OWN S-reg -> s0,s1,x0,x1.
    struct SFF f = { 1.5f, -2.25f, 100, -200 };
    struct SFF rf = sw_idff(f);
    if (rf.f0 != f.f0 || rf.f1 != f.f1 || rf.f2 != f.f2 || rf.f3 != f.f3) { printf("idff\n"); return 6; }

    // All-integer struct SPLIT across the register/stack boundary (x6,x7,[sp]).
    struct S24 s = { 7, 8, 9 };
    int64_t got = sw_split6(1, 2, 3, 4, 5, 6, s);
    if (got != 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) { printf("split6 got=%lld\n", (long long)got); return 7; }

    printf("swift aggregate swiftcc lowers bit-exact vs clang (x0-x3 direct, FP fields own FPRs, split ok)\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8]) -> Option<i32> {
    if !can_link_and_run_aarch64_macho() {
        eprintln!(
            "SKIP native swiftcall run: linking and running the Mach-O object needs an \
             aarch64 macOS host with clang (host probe: os={} arch={}); the {DARWIN} object \
             compiled but was not executed",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_e2e"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).unwrap();
    fs::write(&drv_path, DRIVER).unwrap();
    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let code = Command::new(bin_path.to_str().unwrap())
        .output()
        .unwrap()
        .status
        .code()
        .unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_swift_aggregate_matches_swiftcall() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_for(DARWIN, &module, opt).unwrap_or_else(|e| {
            panic!("swift aggregate module must compile for {DARWIN} at {opt:?}: {e:?}")
        });
        assert_eq!(
            obj.get(..4),
            Some(&MACHO_MAGIC_64[..]),
            "{DARWIN} object at {opt:?}"
        );
        let Some(code) = link_run("swift_aggregate", &obj) else {
            continue;
        };
        assert_eq!(code, 0, "swift aggregate / swiftcall mismatch at {opt:?}");
    }
}

// The scalarization is bound to the witnessed Darwin contract (c6d2228c6).
// Under AAPCS64 each witnessed Darwin shape keeps its aggregate type and is
// refused by name, naming the function and its first aggregate parameter,
// while the same one-shape module still compiles for Darwin and a scalar
// swiftcc signature still compiles for AAPCS64.
#[test]
fn e2e_aarch64_swift_aggregate_is_refused_by_name_under_aapcs64() {
    let control = build_scalar_control_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_for(AAPCS64_LINUX, &control, opt).unwrap_or_else(|e| {
            panic!("scalar swiftcc control must compile for {AAPCS64_LINUX} at {opt:?}: {e:?}")
        });
        assert_eq!(
            obj.get(..4),
            Some(&ELF_MAGIC[..]),
            "{AAPCS64_LINUX} object at {opt:?}"
        );
    }
    for (name, build, struct_id, param) in SHAPES {
        let module = build_shape_module(name, build, struct_id);
        let aggregate = Ty::Struct(StructId::new(struct_id));
        compile_for(DARWIN, &module, OptLevel::O0)
            .unwrap_or_else(|e| panic!("{name} must compile for {DARWIN}: {e:?}"));
        for opt in [OptLevel::O0, OptLevel::O2] {
            assert_swift_aggregate_refused(
                compile_for(AAPCS64_LINUX, &module, opt),
                name,
                param,
                &aggregate,
                &format!("{AAPCS64_LINUX} at {opt:?}"),
            );
        }
    }
}

// A budget >= 5 swiftcc aggregate must stay FAIL-CLOSED: trust-cg rejects it
// (Swift passes it indirectly / via sret, which the scalarization subset does
// not cover). Compilation must error rather than emit possibly-wrong code.
#[test]
fn e2e_aarch64_swift_aggregate_budget5_fails_closed() {
    let module = build_budget5_module();
    for triple in [DARWIN, AAPCS64_LINUX] {
        for opt in [OptLevel::O0, OptLevel::O2] {
            assert_swift_aggregate_refused(
                compile_for(triple, &module, opt),
                "sw_id5",
                0,
                &Ty::Struct(StructId::new(0)),
                &format!("budget>=5 swiftcc aggregate for {triple} at {opt:?}"),
            );
        }
    }
}

// A swiftcc aggregate whose real layout is NOT natural-C (here: a packed struct)
// must stay FAIL-CLOSED: scalarizing it off the natural layout would read/write
// its fields at the wrong offsets. Compilation must error.
#[test]
fn e2e_aarch64_swift_aggregate_packed_fails_closed() {
    let module = build_packed_module();
    for triple in [DARWIN, AAPCS64_LINUX] {
        for opt in [OptLevel::O0, OptLevel::O2] {
            assert_swift_aggregate_refused(
                compile_for(triple, &module, opt),
                "sw_idpk",
                0,
                &Ty::Struct(StructId::new(0)),
                &format!("packed swiftcc aggregate for {triple} at {opt:?}"),
            );
        }
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
