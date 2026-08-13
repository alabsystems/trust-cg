// trust-cg-codegen/tests/e2e_aarch64_swift_aggregate.rs
//
// Completeness: the AGGREGATE subset of the `Swift` (swiftcall) calling
// convention on aarch64-apple-darwin. Unlike the C ABI (AAPCS64), swiftcall
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
// which is exactly what proves the coincidence, bit-exact at O0 and O2.
//
// A budget >= 5 struct (>4 combined GPR-word + FP-field components) is OUTSIDE
// the sound subset -- swiftcall passes it indirectly / via sret, which trust-cg
// keeps FAIL-CLOSED (a compile error), pinned here too.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, CallingConv, CastOp, FieldDef, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, StructDef, StructId,
    StructRepr, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// A C-repr struct type whose ABI matches the clang driver's `struct`.
fn struct_def(id: u32, name: &str, fields: &[Ty]) -> StructDef {
    StructDef {
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
    let ft = m.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![agg.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(fid), name, ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    m.add_function(f);
}

// swiftcc `fn sum3(s: {i64,i64,i64}) -> i64 { s.0 + s.1 + s.2 }` -- an
// aggregate PARAM whose fields are read back at their true struct offsets, so a
// wrong reconstruction offset (that a same-offset identity round-trip could
// hide) is caught. Returns a scalar (no aggregate return).
fn build_sum3(m: &mut TrustIrModule, fid: u32, name: &str, struct_id: u32) {
    let agg = Ty::Struct(StructId::new(struct_id));
    let ft = m.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
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
    m.add_function(f);
}

// swiftcc `fn summix(s: {i64,f64,i64}) -> f64 { (double)s.0 + s.1 + (double)s.2 }`
// -- a MIXED aggregate PARAM: field 0/2 (i64) reconstruct into GPR words, field
// 1 (double) into its own FPR. Reads all three at their true offsets (the int
// word and the FP field share NO 8-byte chunk).
fn build_summix(m: &mut TrustIrModule, fid: u32, name: &str, struct_id: u32) {
    let agg = Ty::Struct(StructId::new(struct_id));
    let ft = m.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
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
    m.add_function(f);
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
    let ft = m.add_func_type(FuncTy {
        params,
        returns: vec![Ty::I64],
        is_vararg: false,
    });
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
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("swift_aggregate");
    // Struct ids must be distinct; func ids too.
    m.structs
        .push(struct_def(0, "S24", &[Ty::I64, Ty::I64, Ty::I64])); // 24B all-int
    m.structs
        .push(struct_def(1, "S32", &[Ty::I64, Ty::I64, Ty::I64, Ty::I64])); // 32B all-int
    m.structs
        .push(struct_def(2, "SMix", &[Ty::I64, Ty::F64, Ty::I64])); // mixed {i64;double;i64}
    m.structs
        .push(struct_def(3, "SFF", &[Ty::F32, Ty::F32, Ty::I64, Ty::I64])); // {float;float;i64;i64}

    build_identity(&mut m, 0, "sw_id24", 0); // 24B all-int param + return -> x0-x2
    build_sum3(&mut m, 1, "sw_sum24", 0); // 24B all-int param -> i64
    build_identity(&mut m, 2, "sw_id32", 1); // 32B all-int param + return -> x0-x3
    build_identity(&mut m, 3, "sw_idmix", 2); // {i64;double;i64} param + return -> x0,d0,x1
    build_summix(&mut m, 4, "sw_summix", 2); // {i64;double;i64} param -> f64
    build_identity(&mut m, 5, "sw_idff", 3); // {float;float;i64;i64} -> s0,s1,x0,x1
    build_split6(&mut m, 6, "sw_split6", 0); // 24B all-int SPLITS x6,x7,[sp] after 6 i64s
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

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    compiler
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
}

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
        eprintln!("SKIP: needs aarch64-apple-darwin");
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
        let obj = compile_at(&module, opt).expect("swift aggregate module must compile");
        let Some(code) = link_run("swift_aggregate", &obj) else {
            return;
        };
        assert_eq!(code, 0, "swift aggregate / swiftcall mismatch at {opt:?}");
    }
}

// A budget >= 5 swiftcc aggregate must stay FAIL-CLOSED: trust-cg rejects it
// (Swift passes it indirectly / via sret, which the scalarization subset does
// not cover). Compilation must error rather than emit possibly-wrong code.
#[test]
fn e2e_aarch64_swift_aggregate_budget5_fails_closed() {
    let module = build_budget5_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let result = compile_at(&module, opt);
        assert!(
            result.is_err(),
            "budget>=5 swiftcc aggregate must fail-closed, but compiled at {opt:?}"
        );
    }
}

// A swiftcc aggregate whose real layout is NOT natural-C (here: a packed struct)
// must stay FAIL-CLOSED: scalarizing it off the natural layout would read/write
// its fields at the wrong offsets. Compilation must error.
#[test]
fn e2e_aarch64_swift_aggregate_packed_fails_closed() {
    let module = build_packed_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let result = compile_at(&module, opt);
        assert!(
            result.is_err(),
            "packed swiftcc aggregate must fail-closed, but compiled at {opt:?}"
        );
    }
}
