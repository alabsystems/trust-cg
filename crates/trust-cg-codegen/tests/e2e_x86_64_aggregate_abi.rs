// trust-cg-codegen/tests/e2e_x86_64_aggregate_abi.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// x86-64 System V AMD64 *aggregate* ABI differential + triple-oracle tests.
//
// This complements `e2e_x86_64_differential.rs` / `e2e_x86_64_triple_oracle.rs`
// (scalar corpus) by holding the by-value struct argument / struct return ABI
// to clang, end-to-end, for the eightbyte shapes that real Rust produces:
//
//   * `{i32, i32}`               — one INTEGER eightbyte (one GPR / RAX)
//   * `{i32, i32, i32}` (12 B)   — two INTEGER eightbytes, second partial (4 B)
//   * `{i64, i64}`               — two INTEGER eightbytes
//   * `{i64, i32}`               — two INTEGER eightbytes (second padded)
//   * `{i64, f64}` / `{f64,i64}` — mixed INTEGER + SSE eightbytes
//   * `{f64, f64}`               — two SSE eightbytes
//   * `{i64, i64, i64}` (24 B)   — >16 B RETURN via sret hidden ptr; a >16 B
//                                  by-value ARGUMENT is fail-closed (separate WS)
//   * `{i128}` (16 B)            — two INTEGER eightbytes (GPR pair both ways)
//
// Each trust_ir module is compiled through Trust Codegen targeting x86-64 (a
// real Mach-O object on this host) and linked against the *same* C driver as a
// clang-compiled C reference of the identical signature; stdout and exit codes
// must match. clang is the golden oracle. On non-x86-64 hosts the tests skip.
//
// The trust_ir builders here use struct/array aggregate Values directly so the
// callee unpacks formal eightbytes and the caller-built return value packs them
// back, exercising both ABI directions. New file per task: the shared corpus in
// `common/x86_64_corpus.rs` is imported, not edited.

#![allow(clippy::too_many_arguments)]

mod common;

use std::sync::Mutex;

use common::x86_64_corpus::{x86_64_differential_test, x86_64_oracle_enabled};

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CallingConv, CastOp, Constant, FieldDef, FuncId, FuncTy,
    FuncTyId, Function as TrustIrFunction, Inst, InstrNode, Linkage, Module as TrustIrModule,
    StructDef, StructId, Ty, ValueId,
};

/// Serialize the x86-64 build/link/run pipeline across this file's tests. On an
/// Apple-silicon host these oracles run the produced x86-64 binaries under
/// Rosetta; running a dozen emulated binaries (plus clang) concurrently — on top
/// of the rest of the codegen suite — overruns the per-run timeout. The actual
/// codegen work is fast; only the emulated execution is the contention point, so
/// one global lock keeps the file robust under `cargo test --tests` without
/// changing the shared harness.
static SERIAL: Mutex<()> = Mutex::new(());

fn run_differential(
    test_name: &str,
    module: &TrustIrModule,
    c_reference: &str,
    driver_src: &str,
) -> Result<(), String> {
    let _guard = SERIAL.lock().unwrap_or_else(|p| p.into_inner());
    x86_64_differential_test(test_name, module, c_reference, driver_src)
}

// ---------------------------------------------------------------------------
// trust_ir building helpers
// ---------------------------------------------------------------------------

fn struct_def(name: &str, fields: &[Ty]) -> StructDef {
    StructDef {
        id: StructId::new(0),
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
        repr: Default::default(),
    }
}

fn extract_field(result: u32, aggregate_ty: &Ty, aggregate: u32, field: u32) -> InstrNode {
    InstrNode {
        inst: Inst::ExtractField {
            ty: aggregate_ty.clone(),
            aggregate: ValueId::new(aggregate),
            field,
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn binop(result: u32, op: BinOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
    InstrNode {
        inst: Inst::BinOp {
            op,
            ty,
            lhs: ValueId::new(lhs),
            rhs: ValueId::new(rhs),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn sext_to_i64(result: u32, src_ty: Ty, operand: u32) -> InstrNode {
    InstrNode {
        inst: Inst::Cast {
            op: CastOp::SExt,
            src_ty,
            dst_ty: Ty::I64,
            operand: ValueId::new(operand),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn ret(value: u32) -> InstrNode {
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

fn func(name: &str, ty: FuncTyId, blocks: Vec<TrustIrBlock>) -> TrustIrFunction {
    TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: name.to_string(),
        ty,
        entry: BlockId::new(0),
        blocks,
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    }
}

fn module(
    name: &str,
    structs: Vec<StructDef>,
    func_types: Vec<FuncTy>,
    functions: Vec<TrustIrFunction>,
) -> TrustIrModule {
    TrustIrModule {
        name: name.to_string(),
        functions,
        structs,
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types,
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

// ---------------------------------------------------------------------------
// Integer-eightbyte struct arguments: sum all integer fields, sext to i64.
// ---------------------------------------------------------------------------

/// `long sum(<struct of N integer fields> s) { return (long)(s.f0 + ... ); }`
/// where each field is sign-extended to i64 and summed. The summation is done
/// in i64 so the single-GPR return is unambiguous and matches the C reference.
fn int_struct_sum_module(name: &str, agg_name: &str, field_tys: &[Ty]) -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);

    let mut body = Vec::new();
    let mut next = 1u32;
    let mut acc: Option<u32> = None;
    for (i, fty) in field_tys.iter().enumerate() {
        let raw = next;
        next += 1;
        body.push(extract_field(raw, &aggregate, 0, i as u32));
        // Sign-extend the field to i64.
        let wide = if *fty == Ty::I64 {
            raw
        } else {
            let w = next;
            next += 1;
            body.push(sext_to_i64(w, fty.clone(), raw));
            w
        };
        acc = Some(match acc {
            None => wide,
            Some(prev) => {
                let s = next;
                next += 1;
                body.push(binop(s, BinOp::Add, Ty::I64, prev, wide));
                s
            }
        });
    }
    body.push(ret(acc.expect("at least one field")));

    let blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), aggregate.clone())],
        body,
    }];

    module(
        name,
        vec![struct_def(agg_name, field_tys)],
        vec![FuncTy {
            params: vec![aggregate],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        vec![func(name, ft, blocks)],
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn x86_64_aggregate_arg_i32_pair_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_arg_i32_pair_vs_clang") {
        return;
    }
    let m = int_struct_sum_module("_sum_i32_pair", "I32Pair", &[Ty::I32, Ty::I32]);
    let c = r#"
#include <stdint.h>
struct I32Pair { int32_t f0; int32_t f1; };
long _sum_i32_pair(struct I32Pair s) { return (long)s.f0 + (long)s.f1; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I32Pair { int32_t f0; int32_t f1; };
extern long _sum_i32_pair(struct I32Pair s);
int main(void) {
    struct I32Pair s = { -123456, 987654 };
    printf("%ld\n", _sum_i32_pair(s));
    return 0;
}
"#;
    run_differential("x86_64_aggregate_arg_i32_pair", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_arg_i32x3_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_arg_i32x3_vs_clang") {
        return;
    }
    // 12-byte struct: two INTEGER eightbytes, the second partial (4 valid bytes).
    let m = int_struct_sum_module("_sum_i32x3", "I32x3", &[Ty::I32, Ty::I32, Ty::I32]);
    let c = r#"
#include <stdint.h>
struct I32x3 { int32_t f0; int32_t f1; int32_t f2; };
long _sum_i32x3(struct I32x3 s) { return (long)s.f0 + (long)s.f1 + (long)s.f2; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I32x3 { int32_t f0; int32_t f1; int32_t f2; };
extern long _sum_i32x3(struct I32x3 s);
int main(void) {
    struct I32x3 s = { 100000, -250000, 333333 };
    printf("%ld\n", _sum_i32x3(s));
    return 0;
}
"#;
    run_differential("x86_64_aggregate_arg_i32x3", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_arg_i64_pair_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_arg_i64_pair_vs_clang") {
        return;
    }
    let m = int_struct_sum_module("_sum_i64_pair", "I64Pair", &[Ty::I64, Ty::I64]);
    let c = r#"
#include <stdint.h>
struct I64Pair { int64_t f0; int64_t f1; };
long _sum_i64_pair(struct I64Pair s) { return s.f0 + s.f1; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64Pair { int64_t f0; int64_t f1; };
extern long _sum_i64_pair(struct I64Pair s);
int main(void) {
    struct I64Pair s = { 0x1122334455667788LL, 0x0102030405060708LL };
    printf("%lld\n", (long long)_sum_i64_pair(s));
    return 0;
}
"#;
    run_differential("x86_64_aggregate_arg_i64_pair", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_arg_i64_i32_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_arg_i64_i32_vs_clang") {
        return;
    }
    // 16-byte struct: two INTEGER eightbytes (the second holds an i32 + padding).
    let m = int_struct_sum_module("_sum_i64_i32", "I64I32", &[Ty::I64, Ty::I32]);
    let c = r#"
#include <stdint.h>
struct I64I32 { int64_t f0; int32_t f1; };
long _sum_i64_i32(struct I64I32 s) { return s.f0 + (long)s.f1; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64I32 { int64_t f0; int32_t f1; };
extern long _sum_i64_i32(struct I64I32 s);
int main(void) {
    struct I64I32 s = { 0x0011223344556677LL, -987654 };
    printf("%lld\n", (long long)_sum_i64_i32(s));
    return 0;
}
"#;
    run_differential("x86_64_aggregate_arg_i64_i32", &m, c, driver).unwrap();
}

// ---------------------------------------------------------------------------
// Mixed INTEGER + SSE eightbyte struct argument.
// ---------------------------------------------------------------------------

/// `long sum_mix(<struct{i64,f64}>) { return (long)(s.f0 + (long)s.f1); }`
/// The float field is truncated to i64 (`FpToSi`) and added to the int field,
/// keeping a single-GPR integer return so the C reference matches bit-for-bit.
fn i64_f64_mix_module(name: &str, agg_name: &str, int_first: bool) -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);
    let (fields, int_field, flt_field) = if int_first {
        (vec![Ty::I64, Ty::F64], 0u32, 1u32)
    } else {
        (vec![Ty::F64, Ty::I64], 1u32, 0u32)
    };

    let body = vec![
        extract_field(1, &aggregate, 0, int_field), // i64
        extract_field(2, &aggregate, 0, flt_field), // f64
        // f64 -> i64 (truncating toward zero)
        InstrNode {
            inst: Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(2),
            },
            results: vec![ValueId::new(3)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        },
        binop(4, BinOp::Add, Ty::I64, 1, 3),
        ret(4),
    ];

    module(
        name,
        vec![struct_def(agg_name, &fields)],
        vec![FuncTy {
            params: vec![aggregate.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        vec![func(
            name,
            ft,
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate)],
                body,
            }],
        )],
    )
}

#[test]
fn x86_64_aggregate_arg_i64_f64_mix_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_arg_i64_f64_mix_vs_clang") {
        return;
    }
    let m = i64_f64_mix_module("_mix_i64_f64", "I64F64", true);
    let c = r#"
#include <stdint.h>
struct I64F64 { int64_t f0; double f1; };
long _mix_i64_f64(struct I64F64 s) { return s.f0 + (long)s.f1; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64F64 { int64_t f0; double f1; };
extern long _mix_i64_f64(struct I64F64 s);
int main(void) {
    struct I64F64 s = { 1000000007LL, -123456.75 };
    printf("%lld\n", (long long)_mix_i64_f64(s));
    return 0;
}
"#;
    run_differential("x86_64_aggregate_arg_i64_f64_mix", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_arg_f64_i64_mix_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_arg_f64_i64_mix_vs_clang") {
        return;
    }
    let m = i64_f64_mix_module("_mix_f64_i64", "F64I64", false);
    let c = r#"
#include <stdint.h>
struct F64I64 { double f0; int64_t f1; };
long _mix_f64_i64(struct F64I64 s) { return s.f1 + (long)s.f0; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct F64I64 { double f0; int64_t f1; };
extern long _mix_f64_i64(struct F64I64 s);
int main(void) {
    struct F64I64 s = { 98765.5, -42LL };
    printf("%lld\n", (long long)_mix_f64_i64(s));
    return 0;
}
"#;
    run_differential("x86_64_aggregate_arg_f64_i64_mix", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_arg_f64_pair_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_arg_f64_pair_vs_clang") {
        return;
    }
    // Two SSE eightbytes (XMM0, XMM1). Sum the floats, truncate to i64.
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);
    let body = vec![
        extract_field(1, &aggregate, 0, 0),
        extract_field(2, &aggregate, 0, 1),
        binop(3, BinOp::FAdd, Ty::F64, 1, 2),
        InstrNode {
            inst: Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(3),
            },
            results: vec![ValueId::new(4)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        },
        ret(4),
    ];
    let m = module(
        "_sum_f64_pair",
        vec![struct_def("F64Pair", &[Ty::F64, Ty::F64])],
        vec![FuncTy {
            params: vec![aggregate.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        vec![func(
            "_sum_f64_pair",
            ft,
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate)],
                body,
            }],
        )],
    );
    let c = r#"
#include <stdint.h>
struct F64Pair { double f0; double f1; };
long _sum_f64_pair(struct F64Pair s) { return (long)(s.f0 + s.f1); }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct F64Pair { double f0; double f1; };
extern long _sum_f64_pair(struct F64Pair s);
int main(void) {
    struct F64Pair s = { 12345.5, 67890.25 };
    printf("%lld\n", (long long)_sum_f64_pair(s));
    return 0;
}
"#;
    run_differential("x86_64_aggregate_arg_f64_pair", &m, c, driver).unwrap();
}

// ---------------------------------------------------------------------------
// i128-field struct (two INTEGER eightbytes): passed in a GPR pair (RDI:RSI),
// returned in a GPR pair (RAX:RDX). The callee returns its parameter unchanged
// (passthrough), exercising both ABI directions of the eightbyte pair without
// requiring i128 *value* decomposition (which is a separate workstream).
// ---------------------------------------------------------------------------

#[test]
fn x86_64_aggregate_i128_field_passthrough_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_i128_field_passthrough_vs_clang") {
        return;
    }
    // struct { __int128 a; } — 16 bytes, two INTEGER eightbytes.
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);
    let m = module(
        "_id_i128_field",
        vec![struct_def("I128Field", &[Ty::I128])],
        vec![FuncTy {
            params: vec![aggregate.clone()],
            returns: vec![aggregate.clone()],
            is_vararg: false,
        }],
        vec![func(
            "_id_i128_field",
            ft,
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), aggregate)],
                body: vec![ret(0)],
            }],
        )],
    );
    let c = r#"
#include <stdint.h>
struct I128Field { __int128 a; };
struct I128Field _id_i128_field(struct I128Field s) { return s; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I128Field { __int128 a; };
extern struct I128Field _id_i128_field(struct I128Field s);
int main(void) {
    struct I128Field s;
    s.a = ((__int128)0x1122334455667788LL << 64) | (uint64_t)0x99aabbccddeeff00ULL;
    struct I128Field r = _id_i128_field(s);
    uint64_t lo = (uint64_t)(unsigned __int128)r.a;
    uint64_t hi = (uint64_t)((unsigned __int128)r.a >> 64);
    printf("%llu %llu\n", (unsigned long long)lo, (unsigned long long)hi);
    return 0;
}
"#;
    run_differential("x86_64_aggregate_i128_field_passthrough", &m, c, driver).unwrap();
}

// ---------------------------------------------------------------------------
// Struct RETURNS: callee builds a struct value and returns it; the C driver
// receives it by value and reads its fields.
// ---------------------------------------------------------------------------

/// Build a function `<struct> make(long x)` that constructs an aggregate from a
/// single i64 input via `InsertField` and returns it by value. `field_tys` lists
/// the struct's fields; each field is `(x + k)` truncated to the field type.
fn int_struct_return_module(name: &str, agg_name: &str, field_tys: &[Ty]) -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);

    // Start from an undef/zero aggregate constant, then insert each field.
    let mut body = Vec::new();
    let mut next = 1u32;

    // Zero-initialized aggregate constant.
    let zero_fields: Vec<Constant> = field_tys
        .iter()
        .map(|fty| {
            if fty.is_float() {
                Constant::Float(0.0)
            } else {
                Constant::Int(0)
            }
        })
        .collect();
    let agg0 = next;
    next += 1;
    body.push(InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(zero_fields),
        },
        results: vec![ValueId::new(agg0)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    });

    let mut cur = agg0;
    for (i, fty) in field_tys.iter().enumerate() {
        // k = i + 1
        let kconst = next;
        next += 1;
        body.push(InstrNode {
            inst: Inst::Const {
                ty: Ty::I64,
                value: Constant::Int((i as i128) + 1),
            },
            results: vec![ValueId::new(kconst)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        });
        // v64 = x + k (i64)
        let v64 = next;
        next += 1;
        body.push(binop(v64, BinOp::Add, Ty::I64, 0, kconst));
        // truncate to field type if needed
        let fieldval = if *fty == Ty::I64 {
            v64
        } else {
            let t = next;
            next += 1;
            body.push(InstrNode {
                inst: Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I64,
                    dst_ty: fty.clone(),
                    operand: ValueId::new(v64),
                },
                results: vec![ValueId::new(t)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            });
            t
        };
        let inserted = next;
        next += 1;
        body.push(InstrNode {
            inst: Inst::InsertField {
                ty: aggregate.clone(),
                aggregate: ValueId::new(cur),
                field: i as u32,
                value: ValueId::new(fieldval),
            },
            results: vec![ValueId::new(inserted)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        });
        cur = inserted;
    }
    body.push(ret(cur));

    module(
        name,
        vec![struct_def(agg_name, field_tys)],
        vec![FuncTy {
            params: vec![Ty::I64],
            returns: vec![aggregate.clone()],
            is_vararg: false,
        }],
        vec![func(
            name,
            ft,
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), Ty::I64)],
                body,
            }],
        )],
    )
}

#[test]
fn x86_64_aggregate_return_i32_pair_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_return_i32_pair_vs_clang") {
        return;
    }
    let m = int_struct_return_module("_make_i32_pair", "I32Pair", &[Ty::I32, Ty::I32]);
    let c = r#"
#include <stdint.h>
struct I32Pair { int32_t f0; int32_t f1; };
struct I32Pair _make_i32_pair(long x) {
    struct I32Pair s = { (int32_t)(x + 1), (int32_t)(x + 2) };
    return s;
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I32Pair { int32_t f0; int32_t f1; };
extern struct I32Pair _make_i32_pair(long x);
int main(void) {
    struct I32Pair s = _make_i32_pair(1000);
    printf("%d %d\n", s.f0, s.f1);
    return 0;
}
"#;
    run_differential("x86_64_aggregate_return_i32_pair", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_return_i32x3_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_return_i32x3_vs_clang") {
        return;
    }
    let m = int_struct_return_module("_make_i32x3", "I32x3", &[Ty::I32, Ty::I32, Ty::I32]);
    let c = r#"
#include <stdint.h>
struct I32x3 { int32_t f0; int32_t f1; int32_t f2; };
struct I32x3 _make_i32x3(long x) {
    struct I32x3 s = { (int32_t)(x + 1), (int32_t)(x + 2), (int32_t)(x + 3) };
    return s;
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I32x3 { int32_t f0; int32_t f1; int32_t f2; };
extern struct I32x3 _make_i32x3(long x);
int main(void) {
    struct I32x3 s = _make_i32x3(2000000);
    printf("%d %d %d\n", s.f0, s.f1, s.f2);
    return 0;
}
"#;
    run_differential("x86_64_aggregate_return_i32x3", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_return_i64_pair_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_return_i64_pair_vs_clang") {
        return;
    }
    let m = int_struct_return_module("_make_i64_pair", "I64Pair", &[Ty::I64, Ty::I64]);
    let c = r#"
#include <stdint.h>
struct I64Pair { int64_t f0; int64_t f1; };
struct I64Pair _make_i64_pair(long x) {
    struct I64Pair s = { x + 1, x + 2 };
    return s;
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64Pair { int64_t f0; int64_t f1; };
extern struct I64Pair _make_i64_pair(long x);
int main(void) {
    struct I64Pair s = _make_i64_pair(0x1122334455667788LL);
    printf("%lld %lld\n", (long long)s.f0, (long long)s.f1);
    return 0;
}
"#;
    run_differential("x86_64_aggregate_return_i64_pair", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_return_i64_f64_mix_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_return_i64_f64_mix_vs_clang") {
        return;
    }
    // {i64, f64}: INTEGER eightbyte in RAX, SSE eightbyte in XMM0 on return.
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);
    let body = vec![
        InstrNode {
            inst: Inst::Const {
                ty: aggregate.clone(),
                value: Constant::Aggregate(vec![Constant::Int(0), Constant::Float(0.0)]),
            },
            results: vec![ValueId::new(1)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        },
        // field0 = x + 7
        InstrNode {
            inst: Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        },
        binop(3, BinOp::Add, Ty::I64, 0, 2),
        InstrNode {
            inst: Inst::InsertField {
                ty: aggregate.clone(),
                aggregate: ValueId::new(1),
                field: 0,
                value: ValueId::new(3),
            },
            results: vec![ValueId::new(4)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        },
        // field1 = (double)x + 0.5
        InstrNode {
            inst: Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(0),
            },
            results: vec![ValueId::new(5)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        },
        InstrNode {
            inst: Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(0.5),
            },
            results: vec![ValueId::new(6)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        },
        binop(7, BinOp::FAdd, Ty::F64, 5, 6),
        InstrNode {
            inst: Inst::InsertField {
                ty: aggregate.clone(),
                aggregate: ValueId::new(4),
                field: 1,
                value: ValueId::new(7),
            },
            results: vec![ValueId::new(8)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        },
        ret(8),
    ];
    let m = module(
        "_make_i64_f64",
        vec![struct_def("I64F64", &[Ty::I64, Ty::F64])],
        vec![FuncTy {
            params: vec![Ty::I64],
            returns: vec![aggregate.clone()],
            is_vararg: false,
        }],
        vec![func(
            "_make_i64_f64",
            ft,
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), Ty::I64)],
                body,
            }],
        )],
    );
    let c = r#"
#include <stdint.h>
struct I64F64 { int64_t f0; double f1; };
struct I64F64 _make_i64_f64(long x) {
    struct I64F64 s = { x + 7, (double)x + 0.5 };
    return s;
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64F64 { int64_t f0; double f1; };
extern struct I64F64 _make_i64_f64(long x);
int main(void) {
    struct I64F64 s = _make_i64_f64(123456);
    printf("%lld %.4f\n", (long long)s.f0, s.f1);
    return 0;
}
"#;
    run_differential("x86_64_aggregate_return_i64_f64_mix", &m, c, driver).unwrap();
}

// ---------------------------------------------------------------------------
// >16-byte struct: sret hidden pointer for RETURNS, and SysV MEMORY-class
// by-value ARGUMENT passing (the caller copies the aggregate into the outgoing
// stack argument area; the callee reads it from its incoming-args frame). A
// dedicated, broader by-value suite lives in `e2e_x86_64_large_struct_byval.rs`;
// this case stays here so the once-fail-closed shape is now exercised inline.
// ---------------------------------------------------------------------------

#[test]
fn x86_64_aggregate_arg_large_byval_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_arg_large_byval_vs_clang") {
        return;
    }
    // A 24-byte struct passed by value is SysV MEMORY class: stack-passed. This
    // was previously fail-closed; it is now lowered and must match clang.
    let m = int_struct_sum_module("_sum_big", "Big", &[Ty::I64, Ty::I64, Ty::I64]);
    let c = r#"
#include <stdint.h>
struct Big { int64_t f0; int64_t f1; int64_t f2; };
long _sum_big(struct Big s) { return s.f0 + s.f1 + s.f2; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct Big { int64_t f0; int64_t f1; int64_t f2; };
extern long _sum_big(struct Big s);
int main(void) {
    struct Big s = { 0x1122334455667788LL, -0x0102030405060708LL, 1000000007LL };
    printf("%lld\n", (long long)_sum_big(s));
    return 0;
}
"#;
    run_differential("x86_64_aggregate_arg_large_byval", &m, c, driver).unwrap();
}

#[test]
fn x86_64_aggregate_return_large_sret_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_aggregate_return_large_sret_vs_clang") {
        return;
    }
    // 24-byte struct returned by value -> sret hidden pointer in RDI, result ptr
    // back in RAX.
    let m = int_struct_return_module("_make_big", "Big", &[Ty::I64, Ty::I64, Ty::I64]);
    let c = r#"
#include <stdint.h>
struct Big { int64_t f0; int64_t f1; int64_t f2; };
struct Big _make_big(long x) {
    struct Big s = { x + 1, x + 2, x + 3 };
    return s;
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct Big { int64_t f0; int64_t f1; int64_t f2; };
extern struct Big _make_big(long x);
int main(void) {
    struct Big s = _make_big(1000000000000LL);
    printf("%lld %lld %lld\n", (long long)s.f0, (long long)s.f1, (long long)s.f2);
    return 0;
}
"#;
    run_differential("x86_64_aggregate_return_large_sret", &m, c, driver).unwrap();
}
