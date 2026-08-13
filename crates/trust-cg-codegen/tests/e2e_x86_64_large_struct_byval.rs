// trust-cg-codegen/tests/e2e_x86_64_large_struct_byval.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// x86-64 System V AMD64 *large* (>16-byte) by-value aggregate ARGUMENT /
// PARAMETER ABI: differential + triple-oracle tests vs clang.
//
// WS5 wired up SysV eightbyte classification for aggregates up to 16 bytes
// (passed in GPR/XMM register pairs) and >16-byte RETURNS via sret. This file
// covers the remaining gap: an aggregate larger than two eightbytes (>16 bytes)
// is SysV MEMORY class, passed *by value on the stack*. The caller copies the
// aggregate bytes into the outgoing argument area (8-byte aligned, 16 for
// 16-byte-aligned types); the callee reads them from its incoming-args frame
// region. This is distinct from sret (which is for >16-byte returns).
//
// Each trust_ir module is compiled through Trust Codegen targeting x86-64 (a
// real Mach-O object on this host), linked against the *same* C driver as a
// clang-compiled C reference of the identical signature, run, and held to clang
// bit-for-bit (stdout + exit code). The triple-oracle cases additionally run
// the trust_ir interpreter as a third independent oracle. On non-x86-64 hosts
// the tests skip. New file per task: the shared corpus in
// `common/x86_64_corpus.rs` is imported, not edited.
//
// Coverage:
//   * callee side: `{i64,i64,i64}` (24 B) by-value param, sum fields -> i64.
//   * callee side: `{i64,i64,i64,i64}` (32 B) by-value param, sum fields.
//   * callee side: mixed int/float `{i64,f64,i64,f64}` (32 B) by-value param.
//   * caller side: trust_ir caller builds a 24-byte struct and calls an extern
//     C callee by value (driver provides the callee).
//   * combined: register args + a large by-value struct arg + trailing args.
//   * triple-oracle: self-contained trust_ir caller+callee (both directions of
//     the ABI exercised in one module) vs interpreter vs clang.

#![allow(clippy::too_many_arguments)]

mod common;

use std::sync::Mutex;

use common::x86_64_corpus::{
    TripleOracleCase, x86_64_differential_test, x86_64_oracle_enabled, x86_64_triple_oracle_test,
};

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CallingConv, CastOp, Constant, FieldDef, FuncId, FuncTy,
    FuncTyId, Function as TrustIrFunction, Inst, InstrNode, Linkage, Module as TrustIrModule,
    StructDef, StructId, Ty, ValueId,
};

/// Serialize the x86-64 build/link/run pipeline across this file's tests so a
/// dozen emulated/native binaries (plus clang) do not contend under
/// `cargo test --tests`. Mirrors `e2e_x86_64_aggregate_abi.rs`.
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

fn run_triple_oracle(
    test_name: &str,
    module: &TrustIrModule,
    func_name: &str,
    c_source: &str,
    cases: &[TripleOracleCase],
) -> Result<(), String> {
    let _guard = SERIAL.lock().unwrap_or_else(|p| p.into_inner());
    x86_64_triple_oracle_test(test_name, module, func_name, c_source, cases)
}

// ---------------------------------------------------------------------------
// trust_ir building helpers
// ---------------------------------------------------------------------------

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

fn insert_field(
    result: u32,
    aggregate_ty: &Ty,
    aggregate: u32,
    field: u32,
    value: u32,
) -> InstrNode {
    InstrNode {
        inst: Inst::InsertField {
            ty: aggregate_ty.clone(),
            aggregate: ValueId::new(aggregate),
            field,
            value: ValueId::new(value),
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

fn iconst(result: u32, ty: Ty, imm: i128) -> InstrNode {
    InstrNode {
        inst: Inst::Const {
            ty,
            value: Constant::Int(imm),
        },
        results: vec![ValueId::new(result)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn fp_to_si64(result: u32, operand: u32) -> InstrNode {
    InstrNode {
        inst: Inst::Cast {
            op: CastOp::FPToSI,
            src_ty: Ty::F64,
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

fn si64_to_fp(result: u32, operand: u32) -> InstrNode {
    InstrNode {
        inst: Inst::Cast {
            op: CastOp::SIToFP,
            src_ty: Ty::I64,
            dst_ty: Ty::F64,
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

fn func(id: u32, name: &str, ty: FuncTyId, blocks: Vec<TrustIrBlock>) -> TrustIrFunction {
    TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(id),
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

/// Bodyless external declaration (no blocks, External linkage). The compiler
/// treats this as an extern symbol resolved at link time, so a trust_ir caller
/// can `Call` it by `FuncId` and the linker binds it to the C driver's body.
fn extern_decl(id: u32, name: &str, ty: FuncTyId) -> TrustIrFunction {
    TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(id),
        name: name.to_string(),
        ty,
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
// Callee side: a function taking a >16-byte struct BY VALUE, doing real
// arithmetic on its fields and returning a scalar i64. The C driver (clang)
// builds the struct and is the *caller*, so this validates trust-cg's callee
// (formal large-struct parameter) binding against clang's caller.
// ---------------------------------------------------------------------------

/// `long sum(<struct of N i64 fields> s) { return s.f0 + ... + s.f{N-1}; }`
fn i64_struct_sum_module(name: &str, agg_name: &str, n: usize) -> TrustIrModule {
    let field_tys: Vec<Ty> = (0..n).map(|_| Ty::I64).collect();
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);

    let mut body = Vec::new();
    let mut next = 1u32;
    let mut acc: Option<u32> = None;
    for i in 0..n {
        let f = next;
        next += 1;
        body.push(extract_field(f, &aggregate, 0, i as u32));
        acc = Some(match acc {
            None => f,
            Some(prev) => {
                let s = next;
                next += 1;
                body.push(binop(s, BinOp::Add, Ty::I64, prev, f));
                s
            }
        });
    }
    body.push(ret(acc.expect("at least one field")));

    module(
        name,
        vec![struct_def(0, agg_name, &field_tys)],
        vec![FuncTy {
            params: vec![aggregate.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        vec![func(
            0,
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
fn x86_64_large_struct_arg_i64x3_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_large_struct_arg_i64x3_vs_clang") {
        return;
    }
    // 24-byte struct: SysV MEMORY class, passed by value on the stack.
    let m = i64_struct_sum_module("_sum_i64x3", "I64x3", 3);
    let c = r#"
#include <stdint.h>
struct I64x3 { int64_t f0; int64_t f1; int64_t f2; };
long _sum_i64x3(struct I64x3 s) { return s.f0 + s.f1 + s.f2; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64x3 { int64_t f0; int64_t f1; int64_t f2; };
extern long _sum_i64x3(struct I64x3 s);
int main(void) {
    struct I64x3 s = { 0x1122334455667788LL, -0x0102030405060708LL, 1000000007LL };
    printf("%lld\n", (long long)_sum_i64x3(s));
    return 0;
}
"#;
    run_differential("x86_64_large_struct_arg_i64x3", &m, c, driver).unwrap();
}

#[test]
fn x86_64_large_struct_arg_i64x4_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_large_struct_arg_i64x4_vs_clang") {
        return;
    }
    // 32-byte struct: SysV MEMORY class.
    let m = i64_struct_sum_module("_sum_i64x4", "I64x4", 4);
    let c = r#"
#include <stdint.h>
struct I64x4 { int64_t f0; int64_t f1; int64_t f2; int64_t f3; };
long _sum_i64x4(struct I64x4 s) { return s.f0 + s.f1 + s.f2 + s.f3; }
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64x4 { int64_t f0; int64_t f1; int64_t f2; int64_t f3; };
extern long _sum_i64x4(struct I64x4 s);
int main(void) {
    struct I64x4 s = { 11, -22, 333333333333LL, -444444444444LL };
    printf("%lld\n", (long long)_sum_i64x4(s));
    return 0;
}
"#;
    run_differential("x86_64_large_struct_arg_i64x4", &m, c, driver).unwrap();
}

/// `long mix(<struct{i64,f64,i64,f64}> s)
///    { return s.f0 + (long)s.f1 + s.f2 + (long)s.f3; }`
/// 32-byte mixed int/float struct (MEMORY class). Float fields are truncated to
/// i64 (FpToSi) so the single-GPR integer return matches clang bit-for-bit.
fn i64_f64_mix_struct_sum_module(name: &str, agg_name: &str) -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);

    let body = vec![
        extract_field(1, &aggregate, 0, 0), // i64
        extract_field(2, &aggregate, 0, 1), // f64
        extract_field(3, &aggregate, 0, 2), // i64
        extract_field(4, &aggregate, 0, 3), // f64
        fp_to_si64(5, 2),
        fp_to_si64(6, 4),
        binop(7, BinOp::Add, Ty::I64, 1, 3),
        binop(8, BinOp::Add, Ty::I64, 5, 6),
        binop(9, BinOp::Add, Ty::I64, 7, 8),
        ret(9),
    ];

    module(
        name,
        vec![struct_def(
            0,
            agg_name,
            &[Ty::I64, Ty::F64, Ty::I64, Ty::F64],
        )],
        vec![FuncTy {
            params: vec![aggregate.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        vec![func(
            0,
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
fn x86_64_large_struct_arg_mixed_int_float_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_large_struct_arg_mixed_int_float_vs_clang") {
        return;
    }
    let m = i64_f64_mix_struct_sum_module("_mix_i64f64x2", "I64F64x2");
    let c = r#"
#include <stdint.h>
struct I64F64x2 { int64_t f0; double f1; int64_t f2; double f3; };
long _mix_i64f64x2(struct I64F64x2 s) {
    return s.f0 + (long)s.f1 + s.f2 + (long)s.f3;
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64F64x2 { int64_t f0; double f1; int64_t f2; double f3; };
extern long _mix_i64f64x2(struct I64F64x2 s);
int main(void) {
    struct I64F64x2 s = { 1000000007LL, -123456.75, -98765432LL, 87654.5 };
    printf("%lld\n", (long long)_mix_i64f64x2(s));
    return 0;
}
"#;
    run_differential("x86_64_large_struct_arg_mixed_int_float", &m, c, driver).unwrap();
}

// ---------------------------------------------------------------------------
// Combined: register args + a large by-value struct arg + trailing args.
//
// `long combined(long a, long b, <struct{i64,i64,i64}> s, long c, long d)
//    { return a*1 + b*2 + s.f0 + s.f1 + s.f2 + c + d; }`
//
// `a`/`b` consume GPR arg regs, the 24-byte struct goes on the stack (MEMORY
// class), and `c`/`d` follow it in the remaining GPRs. This validates that the
// stack/register indices stay consistent when a large struct sits between
// register args. The C driver is the caller, so this is the *callee* side.
// ---------------------------------------------------------------------------

fn combined_callee_module(name: &str, agg_name: &str) -> TrustIrModule {
    // params: a(i64), b(i64), s(struct), c(i64), d(i64)
    let aggregate = Ty::Struct(StructId::new(0));
    let ft = FuncTyId::new(0);

    // Value ids: 0=a, 1=b, 2=s, 3=c, 4=d
    let body = vec![
        iconst(5, Ty::I64, 2),
        binop(6, BinOp::Mul, Ty::I64, 1, 5), // b*2
        extract_field(7, &aggregate, 2, 0),
        extract_field(8, &aggregate, 2, 1),
        extract_field(9, &aggregate, 2, 2),
        binop(10, BinOp::Add, Ty::I64, 0, 6), // a + b*2
        binop(11, BinOp::Add, Ty::I64, 10, 7),
        binop(12, BinOp::Add, Ty::I64, 11, 8),
        binop(13, BinOp::Add, Ty::I64, 12, 9),
        binop(14, BinOp::Add, Ty::I64, 13, 3), // + c
        binop(15, BinOp::Add, Ty::I64, 14, 4), // + d
        ret(15),
    ];

    module(
        name,
        vec![struct_def(0, agg_name, &[Ty::I64, Ty::I64, Ty::I64])],
        vec![FuncTy {
            params: vec![Ty::I64, Ty::I64, aggregate.clone(), Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }],
        vec![func(
            0,
            name,
            ft,
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![
                    (ValueId::new(0), Ty::I64),
                    (ValueId::new(1), Ty::I64),
                    (ValueId::new(2), aggregate),
                    (ValueId::new(3), Ty::I64),
                    (ValueId::new(4), Ty::I64),
                ],
                body,
            }],
        )],
    )
}

#[test]
fn x86_64_reg_args_large_struct_trailing_args_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_reg_args_large_struct_trailing_args_vs_clang") {
        return;
    }
    let m = combined_callee_module("_combined", "I64x3C");
    let c = r#"
#include <stdint.h>
struct I64x3C { int64_t f0; int64_t f1; int64_t f2; };
long _combined(long a, long b, struct I64x3C s, long c, long d) {
    return a + b * 2 + s.f0 + s.f1 + s.f2 + c + d;
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64x3C { int64_t f0; int64_t f1; int64_t f2; };
extern long _combined(long a, long b, struct I64x3C s, long c, long d);
int main(void) {
    struct I64x3C s = { 100000000001LL, -200000000002LL, 3LL };
    printf("%lld\n", (long long)_combined(7, 11, s, -5, 99));
    return 0;
}
"#;
    run_differential("x86_64_reg_args_large_struct_trailing_args", &m, c, driver).unwrap();
}

// ---------------------------------------------------------------------------
// Caller side: a trust_ir CALLER builds a 24-byte struct from its i64 args and
// calls an EXTERN callee by value. The driver (clang) provides the callee body,
// so this validates trust-cg's caller (outgoing stack argument copy) against a
// clang-compiled callee.
// ---------------------------------------------------------------------------

/// `long caller(long x) {
///     struct I64x3 s = { x+1, x+2, x+3 };
///     return _ext_sum_i64x3(s);
/// }` — `_ext_sum_i64x3` is an extern callee resolved at link time.
fn caller_calls_extern_module(name: &str, callee: &str, agg_name: &str) -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let caller_ft = FuncTyId::new(0);
    let callee_ft = FuncTyId::new(1);

    // value 0 = x
    let mut body = Vec::new();
    let mut next = 1u32;

    // zero aggregate
    let agg0 = next;
    next += 1;
    body.push(InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0), Constant::Int(0)]),
        },
        results: vec![ValueId::new(agg0)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    });

    let mut cur = agg0;
    for i in 0..3u32 {
        let k = next;
        next += 1;
        body.push(iconst(k, Ty::I64, (i as i128) + 1));
        let v = next;
        next += 1;
        body.push(binop(v, BinOp::Add, Ty::I64, 0, k));
        let inserted = next;
        next += 1;
        body.push(insert_field(inserted, &aggregate, cur, i, v));
        cur = inserted;
    }

    // result = _ext_sum_i64x3(s)
    let r = next;
    body.push(InstrNode {
        inst: Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(cur)],
        },
        results: vec![ValueId::new(r)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    });
    body.push(ret(r));

    module(
        name,
        vec![struct_def(0, agg_name, &[Ty::I64, Ty::I64, Ty::I64])],
        vec![
            FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![aggregate.clone()],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![
            func(
                0,
                name,
                caller_ft,
                vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![(ValueId::new(0), Ty::I64)],
                    body,
                }],
            ),
            extern_decl(1, callee, callee_ft),
        ],
    )
}

#[test]
fn x86_64_caller_large_struct_byval_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_caller_large_struct_byval_vs_clang") {
        return;
    }
    let m = caller_calls_extern_module("_caller_byval", "_ext_sum_i64x3", "I64x3X");
    // C reference: identical caller. The callee + main live in the driver (linked
    // into both binaries), so the trust-cg caller calls the clang-built callee.
    let c = r#"
#include <stdint.h>
struct I64x3X { int64_t f0; int64_t f1; int64_t f2; };
extern long _ext_sum_i64x3(struct I64x3X s);
long _caller_byval(long x) {
    struct I64x3X s = { x + 1, x + 2, x + 3 };
    return _ext_sum_i64x3(s);
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64x3X { int64_t f0; int64_t f1; int64_t f2; };
long _ext_sum_i64x3(struct I64x3X s) { return s.f0 + s.f1 + s.f2; }
extern long _caller_byval(long x);
int main(void) {
    printf("%lld\n", (long long)_caller_byval(1000000000LL));
    return 0;
}
"#;
    run_differential("x86_64_caller_large_struct_byval", &m, c, driver).unwrap();
}

// ---------------------------------------------------------------------------
// SELF-CONTAINED both-directions: a single trust_ir module defines BOTH a caller
// that builds the struct and the callee that consumes it by value, so the
// caller's outgoing stack copy AND the callee's incoming-frame binding are
// exercised together in one compiled object, held to clang. The entry takes i64
// args (so the C driver and trust-cg agree on the boundary) and builds the
// 32-byte mixed int/float struct internally.
// ---------------------------------------------------------------------------

/// Two trust_ir functions:
///   `_lsx_callee(<struct{i64,f64,i64,i64}>) -> i64`  (mixed int/float, 32 B)
///   `_lsx_entry(long a, long b, long c, long d) -> i64`
/// where `_lsx_entry` builds the struct `{ a, (double)b, c, d }` and returns
/// `_lsx_callee(s) + a` (so the entry's own register args remain live across
/// the call, in addition to the struct passing).
fn self_contained_caller_callee_module() -> TrustIrModule {
    let aggregate = Ty::Struct(StructId::new(0));
    let entry_ft = FuncTyId::new(0);
    let callee_ft = FuncTyId::new(1);

    // ---- callee: sum f0 + (long)f1 + f2 + f3 ----
    let callee_body = vec![
        extract_field(1, &aggregate, 0, 0), // i64
        extract_field(2, &aggregate, 0, 1), // f64
        extract_field(3, &aggregate, 0, 2), // i64
        extract_field(4, &aggregate, 0, 3), // i64
        fp_to_si64(5, 2),
        binop(6, BinOp::Add, Ty::I64, 1, 5),
        binop(7, BinOp::Add, Ty::I64, 6, 3),
        binop(8, BinOp::Add, Ty::I64, 7, 4),
        ret(8),
    ];
    let callee = func(
        1,
        "_lsx_callee",
        callee_ft,
        vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), aggregate.clone())],
            body: callee_body,
        }],
    );

    // ---- entry: build struct {a, (double)b, c, d}; return callee(s) + a ----
    // value ids: 0=a, 1=b, 2=c, 3=d
    let mut body = Vec::new();
    let mut next = 4u32;

    let agg0 = next;
    next += 1;
    body.push(InstrNode {
        inst: Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![
                Constant::Int(0),
                Constant::Float(0.0),
                Constant::Int(0),
                Constant::Int(0),
            ]),
        },
        results: vec![ValueId::new(agg0)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    });

    // f0 = a
    let s0 = next;
    next += 1;
    body.push(insert_field(s0, &aggregate, agg0, 0, 0));
    // f1 = (double)b
    let bf = next;
    next += 1;
    body.push(si64_to_fp(bf, 1));
    let s1 = next;
    next += 1;
    body.push(insert_field(s1, &aggregate, s0, 1, bf));
    // f2 = c
    let s2 = next;
    next += 1;
    body.push(insert_field(s2, &aggregate, s1, 2, 2));
    // f3 = d
    let s3 = next;
    next += 1;
    body.push(insert_field(s3, &aggregate, s2, 3, 3));

    // r = callee(s3)
    let r = next;
    next += 1;
    body.push(InstrNode {
        inst: Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(s3)],
        },
        results: vec![ValueId::new(r)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    });
    // out = r + a  (keeps `a` live across the call)
    let out = next;
    body.push(binop(out, BinOp::Add, Ty::I64, r, 0));
    body.push(ret(out));

    let entry = func(
        0,
        "_lsx_entry",
        entry_ft,
        vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![
                (ValueId::new(0), Ty::I64),
                (ValueId::new(1), Ty::I64),
                (ValueId::new(2), Ty::I64),
                (ValueId::new(3), Ty::I64),
            ],
            body,
        }],
    );

    module(
        "large_struct_byval_self_contained",
        vec![struct_def(
            0,
            "LsxAgg",
            &[Ty::I64, Ty::F64, Ty::I64, Ty::I64],
        )],
        vec![
            FuncTy {
                params: vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![aggregate],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![entry, callee],
    )
}

#[test]
fn x86_64_self_contained_large_struct_byval_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_self_contained_large_struct_byval_vs_clang") {
        return;
    }
    // One trust-cg object provides BOTH the struct-building caller and the
    // by-value callee, so the MEMORY-class ABI is validated end-to-end inside
    // trust-cg (caller copy -> callee read) against clang's own both-sides
    // lowering, for several inputs.
    let m = self_contained_caller_callee_module();
    let c = r#"
#include <stdint.h>
struct LsxAgg { int64_t f0; double f1; int64_t f2; int64_t f3; };
static long _lsx_callee(struct LsxAgg s) {
    return s.f0 + (long)s.f1 + s.f2 + s.f3;
}
long _lsx_entry(long a, long b, long c, long d) {
    struct LsxAgg s = { a, (double)b, c, d };
    return _lsx_callee(s) + a;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _lsx_entry(long a, long b, long c, long d);
int main(void) {
    printf("%lld %lld %lld %lld\n",
        (long long)_lsx_entry(10, 20, 30, 40),
        (long long)_lsx_entry(-1, -2, -3, -4),
        (long long)_lsx_entry(1000000007, 2, 3, 4),
        (long long)_lsx_entry(0, 0, 0, 0));
    return 0;
}
"#;
    run_differential("x86_64_self_contained_large_struct_byval", &m, c, driver).unwrap();
}

// ---------------------------------------------------------------------------
// Triple-oracle (interpreter + trust-cg + clang).
//
// The in-tree scalar interpreter cannot model by-value aggregates, so the
// large-STRUCT ABI itself is exhaustively validated by the differential tests
// above against clang (the authoritative oracle for ABI placement). This
// triple-oracle test instead guards the *companion* stack-argument machinery
// the large-struct path reuses: a call with MORE than six i64 arguments forces
// the trailing scalars onto the outgoing stack area (same SUB/ADD-RSP framing,
// same `[RBP+offset]` incoming-frame reads), while staying fully interpretable.
// All three oracles must agree.
// ---------------------------------------------------------------------------

/// Two scalar trust_ir functions:
///   `_lsx_many(a,b,c,d,e,f,g,h) -> i64`   (8 i64 params: g,h on the stack)
///   `_lsx_caller(a,b) -> i64`             builds 8 args and calls `_lsx_many`,
///                                         keeping `a` live across the call.
fn stack_args_self_contained_module() -> TrustIrModule {
    let caller_ft = FuncTyId::new(0);
    let many_ft = FuncTyId::new(1);

    // ---- _lsx_many: weighted sum a + 2b + 3c + 4d + 5e + 6f + 7g + 8h ----
    // params 0..=7
    let mut mbody = Vec::new();
    let mut next = 8u32;
    let mut acc: Option<u32> = None;
    for (i, w) in (1..=8i128).enumerate() {
        let term = if w == 1 {
            i as u32
        } else {
            let kc = next;
            next += 1;
            mbody.push(iconst(kc, Ty::I64, w));
            let m = next;
            next += 1;
            mbody.push(binop(m, BinOp::Mul, Ty::I64, i as u32, kc));
            m
        };
        acc = Some(match acc {
            None => term,
            Some(prev) => {
                let s = next;
                next += 1;
                mbody.push(binop(s, BinOp::Add, Ty::I64, prev, term));
                s
            }
        });
    }
    mbody.push(ret(acc.unwrap()));
    let many = func(
        1,
        "_lsx_many",
        many_ft,
        vec![TrustIrBlock {
            id: BlockId::new(0),
            params: (0..8).map(|i| (ValueId::new(i), Ty::I64)).collect(),
            body: mbody,
        }],
    );

    // ---- _lsx_caller(a, b): args = a, b, a+b, a-b, a*2, b*2, a+1, b+1 ----
    // value ids: 0=a, 1=b
    let mut body = Vec::new();
    let mut n = 2u32;
    let two = n;
    n += 1;
    body.push(iconst(two, Ty::I64, 2));
    let one = n;
    n += 1;
    body.push(iconst(one, Ty::I64, 1));
    let apb = n;
    n += 1;
    body.push(binop(apb, BinOp::Add, Ty::I64, 0, 1));
    let amb = n;
    n += 1;
    body.push(binop(amb, BinOp::Sub, Ty::I64, 0, 1));
    let a2 = n;
    n += 1;
    body.push(binop(a2, BinOp::Mul, Ty::I64, 0, two));
    let b2 = n;
    n += 1;
    body.push(binop(b2, BinOp::Mul, Ty::I64, 1, two));
    let a1 = n;
    n += 1;
    body.push(binop(a1, BinOp::Add, Ty::I64, 0, one));
    let b1 = n;
    n += 1;
    body.push(binop(b1, BinOp::Add, Ty::I64, 1, one));
    let r = n;
    n += 1;
    body.push(InstrNode {
        inst: Inst::Call {
            callee: FuncId::new(1),
            args: vec![
                ValueId::new(0),
                ValueId::new(1),
                ValueId::new(apb),
                ValueId::new(amb),
                ValueId::new(a2),
                ValueId::new(b2),
                ValueId::new(a1),
                ValueId::new(b1),
            ],
        },
        results: vec![ValueId::new(r)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    });
    let out = n;
    body.push(binop(out, BinOp::Add, Ty::I64, r, 0)); // keep `a` live across call
    body.push(ret(out));
    let caller = func(
        0,
        "_lsx_caller",
        caller_ft,
        vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body,
        }],
    );

    module(
        "large_struct_byval_stack_args",
        vec![],
        vec![
            FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: (0..8).map(|_| Ty::I64).collect(),
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![caller, many],
    )
}

#[test]
fn x86_64_stack_args_companion_triple_oracle() {
    if !x86_64_oracle_enabled("x86_64_stack_args_companion_triple_oracle") {
        return;
    }
    let m = stack_args_self_contained_module();
    let c = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
static long _lsx_many(long a, long b, long c, long d,
                      long e, long f, long g, long h) {
    return a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g + 8*h;
}
long _lsx_caller(long a, long b) {
    return _lsx_many(a, b, a + b, a - b, a * 2, b * 2, a + 1, b + 1) + a;
}
#else
extern long _lsx_caller(long a, long b);
#endif
int main(void) {
    printf("c1=%lld\n", (long long)_lsx_caller(3, 5));
    printf("c2=%lld\n", (long long)_lsx_caller(-7, 11));
    printf("c3=%lld\n", (long long)_lsx_caller(1000000, -2000000));
    printf("c4=%lld\n", (long long)_lsx_caller(0, 0));
    return 0;
}
"#;
    let cases = [
        TripleOracleCase::new("c1", &[3, 5]),
        TripleOracleCase::new("c2", &[-7, 11]),
        TripleOracleCase::new("c3", &[1000000, -2000000]),
        TripleOracleCase::new("c4", &[0, 0]),
    ];
    run_triple_oracle(
        "x86_64_stack_args_companion_triple_oracle",
        &m,
        "_lsx_caller",
        c,
        &cases,
    )
    .unwrap();
}
