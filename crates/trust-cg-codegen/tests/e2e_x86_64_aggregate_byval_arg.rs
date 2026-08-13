// trust-cg-codegen/tests/e2e_x86_64_aggregate_byval_arg.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// x86-64 System V AMD64 by-value aggregate CALL ARGUMENT ABI: differential
// tests vs clang for a CONSTRUCTED aggregate passed by value.
//
// The gap this file guards: ISel's call-argument ABI classifier reads
// `value_type(arg)` to decide System V eightbyte register-pair / sret / stack
// placement. A by-value aggregate argument is carried by ADDRESS, so when it is
// produced by an `Alloca` (+ field stores) — the shape the rustc bridge emits
// for a constructed local — its producing instruction types it as a pointer
// (I64), NOT the aggregate. Before the fix the classifier saw I64 and passed
// the whole aggregate in ONE GPR (miscompile). The adapter now seeds the
// argument's aggregate type from the callee's declared PARAMETER type (the same
// information the callee-side formal-parameter ABI already uses), so the caller
// and callee agree on the eightbyte placement.
//
// Each trust_ir module builds its aggregate via `Alloca` + per-field `Store`
// (so the argument's origin is a pointer, exercising the seeding fix rather than
// the `Const::Aggregate` type-propagation chain that already worked), then
// passes it BY VALUE. Each module is compiled through Trust Codegen targeting
// x86-64 (a real Mach-O object on this host), linked against the SAME C driver
// as a clang-compiled C reference of the identical signature, run, and held to
// clang bit-for-bit (stdout + exit code). On non-x86-64 hosts the tests skip.
// The shared corpus harness in `common/x86_64_corpus.rs` is imported, not
// edited.
//
// Coverage (all caller-side, aggregate built via Alloca + Store):
//   * `{i64,i64}` (16 B) -> register pair (RDI:RSI), callee returns f0+f1.
//   * `{i64,i64,i64}` (24 B) -> SysV MEMORY class (by value on the stack).
//   * `{i64,f64}` mixed int/float (16 B) -> GPR + XMM lanes.
//   * an enum `{tag:u8, payload:i64}` (16 B) passed by value.
//   * combined: register args + a by-value `{i64,i64}` + trailing args.
//   * self-contained both-directions `{i64,i64}` triple-oracle companion
//     (scalar caller forces the stack-arg framing the aggregate path reuses).

#![allow(clippy::too_many_arguments)]

mod common;

use std::sync::Mutex;

use common::x86_64_corpus::{x86_64_differential_test, x86_64_oracle_enabled};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CallingConv, CastOp, Constant, EnumDef, EnumId,
    EnumVariant, FieldDef, FuncId, FuncTy, FuncTyId, Function as TrustIrFunction, Inst, InstrNode,
    Linkage, Module as TrustIrModule, StructDef, StructId, Ty, ValueId,
};

/// Serialize the x86-64 build/link/run pipeline across this file's tests so a
/// handful of native binaries (plus clang) do not contend under
/// `cargo test --tests`. Mirrors `e2e_x86_64_large_struct_byval.rs`.
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
// trust_ir building helpers (mirrors e2e_x86_64_large_struct_byval.rs)
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

fn node(inst: Inst, results: Vec<u32>) -> InstrNode {
    InstrNode {
        inst,
        results: results.into_iter().map(ValueId::new).collect(),
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn iconst(result: u32, ty: Ty, imm: i128) -> InstrNode {
    node(
        Inst::Const {
            ty,
            value: Constant::Int(imm),
        },
        vec![result],
    )
}

fn alloca(result: u32, ty: Ty) -> InstrNode {
    node(
        Inst::Alloca {
            ty,
            count: None,
            align: None,
        },
        vec![result],
    )
}

/// `result = aggregate with `field` set to `value``. Lowers (in the adapter) to
/// a `StructGep` + typed `Store` into the aggregate's storage, then a `Copy` of
/// the base pointer — i.e. the exact "constructed aggregate carried by address"
/// shape the rustc bridge emits via `emit_aggregate_field_store`.
fn insert_field(
    result: u32,
    aggregate_ty: &Ty,
    aggregate: u32,
    field: u32,
    value: u32,
) -> InstrNode {
    node(
        Inst::InsertField {
            ty: aggregate_ty.clone(),
            aggregate: ValueId::new(aggregate),
            field,
            value: ValueId::new(value),
        },
        vec![result],
    )
}

fn extract_field(result: u32, aggregate_ty: &Ty, aggregate: u32, field: u32) -> InstrNode {
    node(
        Inst::ExtractField {
            ty: aggregate_ty.clone(),
            aggregate: ValueId::new(aggregate),
            field,
        },
        vec![result],
    )
}

fn binop(result: u32, op: BinOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
    node(
        Inst::BinOp {
            op,
            ty,
            lhs: ValueId::new(lhs),
            rhs: ValueId::new(rhs),
        },
        vec![result],
    )
}

fn si64_to_fp(result: u32, operand: u32) -> InstrNode {
    node(
        Inst::Cast {
            op: CastOp::SIToFP,
            src_ty: Ty::I64,
            dst_ty: Ty::F64,
            operand: ValueId::new(operand),
        },
        vec![result],
    )
}

fn call(result: Option<u32>, callee: u32, args: &[u32]) -> InstrNode {
    node(
        Inst::Call {
            callee: FuncId::new(callee),
            args: args.iter().map(|&a| ValueId::new(a)).collect(),
        },
        result.into_iter().collect(),
    )
}

fn ret(value: u32) -> InstrNode {
    node(
        Inst::Return {
            values: vec![ValueId::new(value)],
        },
        vec![],
    )
}

fn func(id: u32, name: &str, ty: FuncTyId, block: TrustIrBlock) -> TrustIrFunction {
    TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(id),
        name: name.to_string(),
        ty,
        entry: BlockId::new(0),
        blocks: vec![block],
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

fn block(params: Vec<(u32, Ty)>, body: Vec<InstrNode>) -> TrustIrBlock {
    TrustIrBlock {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .map(|(v, ty)| (ValueId::new(v), ty))
            .collect(),
        body,
    }
}

fn module(
    name: &str,
    structs: Vec<StructDef>,
    enums: Vec<EnumDef>,
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
        enums,
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

// ===========================================================================
// {i64, i64} (16 B): register pair RDI:RSI. Caller builds via Alloca + Store.
// ===========================================================================

/// `_byval2_caller(x) -> i64`:
///   `s = alloca {i64,i64}; s.f0 = x+1; s.f1 = x*3; return _add2(s);`
/// `_add2` is an EXTERN callee (clang-built in the driver) returning f0+f1.
///
/// The aggregate is built via `Alloca` + `InsertField` (the rustc bridge's
/// `emit_aggregate_field_store` shape): the slot pointer `s` (value 1) is typed
/// `Ty::Ptr` by its `Alloca` origin, so its aggregate type as a CALL ARGUMENT
/// is supplied only by the adapter seeding the callee's parameter type — the
/// gap this file guards.
fn byval_i64x2_module() -> TrustIrModule {
    let agg = Ty::Struct(StructId::new(0));
    let body = vec![
        // value 0 = x
        alloca(1, agg.clone()),
        iconst(2, Ty::I64, 1),
        binop(3, BinOp::Add, Ty::I64, 0, 2), // x+1
        iconst(4, Ty::I64, 3),
        binop(5, BinOp::Mul, Ty::I64, 0, 4), // x*3
        // s.f0 = x+1, s.f1 = x*3 (InsertField -> StructGep + Store into the slot)
        insert_field(6, &agg, 1, 0, 3),
        insert_field(7, &agg, 1, 1, 5),
        // result = _add2(s)  -- value 1 is the alloca pointer (Ty::Ptr): its
        // aggregate type comes from the callee param signature, not its origin.
        call(Some(10), 1, &[1]),
        ret(10),
    ];
    module(
        "byval_i64x2",
        vec![struct_def(0, "I64x2", &[Ty::I64, Ty::I64])],
        vec![],
        vec![
            FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![agg],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![
            func(
                0,
                "_byval2_caller",
                FuncTyId::new(0),
                block(vec![(0, Ty::I64)], body),
            ),
            // extern callee declaration (no body, resolved at link time).
            TrustIrFunction {
                attrs: Default::default(),
                id: FuncId::new(1),
                name: "_add2".to_string(),
                ty: FuncTyId::new(1),
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
            },
        ],
    )
}

#[test]
fn x86_64_byval_i64x2_arg_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_byval_i64x2_arg_vs_clang") {
        return;
    }
    let m = byval_i64x2_module();
    let c = r#"
#include <stdint.h>
struct I64x2 { int64_t f0; int64_t f1; };
extern long _add2(struct I64x2 s);
long _byval2_caller(long x) {
    struct I64x2 s = { x + 1, x * 3 };
    return _add2(s);
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64x2 { int64_t f0; int64_t f1; };
long _add2(struct I64x2 s) { return s.f0 + s.f1; }
extern long _byval2_caller(long x);
int main(void) {
    printf("%lld %lld %lld\n",
        (long long)_byval2_caller(1000000000LL),
        (long long)_byval2_caller(-7),
        (long long)_byval2_caller(0));
    return 0;
}
"#;
    run_differential("x86_64_byval_i64x2_arg", &m, c, driver).unwrap();
}

// ===========================================================================
// {i64, i64, i64} (24 B): SysV MEMORY class (by value on the stack).
// ===========================================================================

fn byval_i64x3_module() -> TrustIrModule {
    let agg = Ty::Struct(StructId::new(0));
    let body = vec![
        // value 0 = x
        alloca(1, agg.clone()),
        iconst(2, Ty::I64, 1),
        binop(3, BinOp::Add, Ty::I64, 0, 2), // x+1
        iconst(4, Ty::I64, 2),
        binop(5, BinOp::Add, Ty::I64, 0, 4), // x+2
        iconst(6, Ty::I64, 3),
        binop(7, BinOp::Add, Ty::I64, 0, 6), // x+3
        insert_field(8, &agg, 1, 0, 3),
        insert_field(9, &agg, 1, 1, 5),
        insert_field(10, &agg, 1, 2, 7),
        call(Some(14), 1, &[1]),
        ret(14),
    ];
    module(
        "byval_i64x3",
        vec![struct_def(0, "I64x3M", &[Ty::I64, Ty::I64, Ty::I64])],
        vec![],
        vec![
            FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![agg],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![
            func(
                0,
                "_byval3_caller",
                FuncTyId::new(0),
                block(vec![(0, Ty::I64)], body),
            ),
            TrustIrFunction {
                attrs: Default::default(),
                id: FuncId::new(1),
                name: "_add3".to_string(),
                ty: FuncTyId::new(1),
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
            },
        ],
    )
}

#[test]
fn x86_64_byval_i64x3_memory_arg_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_byval_i64x3_memory_arg_vs_clang") {
        return;
    }
    let m = byval_i64x3_module();
    let c = r#"
#include <stdint.h>
struct I64x3M { int64_t f0; int64_t f1; int64_t f2; };
extern long _add3(struct I64x3M s);
long _byval3_caller(long x) {
    struct I64x3M s = { x + 1, x + 2, x + 3 };
    return _add3(s);
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64x3M { int64_t f0; int64_t f1; int64_t f2; };
long _add3(struct I64x3M s) { return s.f0 + s.f1 + s.f2; }
extern long _byval3_caller(long x);
int main(void) {
    printf("%lld %lld\n",
        (long long)_byval3_caller(1000000000LL),
        (long long)_byval3_caller(-5));
    return 0;
}
"#;
    run_differential("x86_64_byval_i64x3_memory_arg", &m, c, driver).unwrap();
}

// ===========================================================================
// {i64, f64} mixed (16 B): one INTEGER eightbyte (RDI) + one SSE eightbyte
// (XMM0). Caller builds via Alloca + Store.
// ===========================================================================

fn byval_i64_f64_module() -> TrustIrModule {
    let agg = Ty::Struct(StructId::new(0));
    let body = vec![
        // value 0 = x (i64)
        alloca(1, agg.clone()),
        iconst(2, Ty::I64, 7),
        binop(3, BinOp::Add, Ty::I64, 0, 2), // f0 = x + 7  (i64)
        si64_to_fp(4, 0),                    // f1 = (double)x
        insert_field(5, &agg, 1, 0, 3),
        insert_field(6, &agg, 1, 1, 4),
        call(Some(9), 1, &[1]),
        ret(9),
    ];
    module(
        "byval_i64_f64",
        vec![struct_def(0, "I64F64", &[Ty::I64, Ty::F64])],
        vec![],
        vec![
            FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![agg],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![
            func(
                0,
                "_byval_if_caller",
                FuncTyId::new(0),
                block(vec![(0, Ty::I64)], body),
            ),
            TrustIrFunction {
                attrs: Default::default(),
                id: FuncId::new(1),
                name: "_mix_if".to_string(),
                ty: FuncTyId::new(1),
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
            },
        ],
    )
}

#[test]
fn x86_64_byval_i64_f64_mixed_arg_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_byval_i64_f64_mixed_arg_vs_clang") {
        return;
    }
    let m = byval_i64_f64_module();
    let c = r#"
#include <stdint.h>
struct I64F64 { int64_t f0; double f1; };
extern long _mix_if(struct I64F64 s);
long _byval_if_caller(long x) {
    struct I64F64 s = { x + 7, (double)x };
    return _mix_if(s);
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64F64 { int64_t f0; double f1; };
long _mix_if(struct I64F64 s) { return s.f0 + (long)s.f1; }
extern long _byval_if_caller(long x);
int main(void) {
    printf("%lld %lld %lld\n",
        (long long)_byval_if_caller(1000000007LL),
        (long long)_byval_if_caller(-123456),
        (long long)_byval_if_caller(0));
    return 0;
}
"#;
    run_differential("x86_64_byval_i64_f64_mixed_arg", &m, c, driver).unwrap();
}

// ===========================================================================
// enum {tag:u8, payload:i64} (16 B) by value: OUTSIDE the WS5 register-aggregate
// shapes. The System V eightbyte classifier deliberately does NOT model enum
// leaves (`Type::Enum => None` in `collect_sysv_aggregate_leaves`), and the
// >16-byte MEMORY / single-GPR paths only match structs/arrays. A by-value enum
// argument must therefore FAIL CLOSED with a clear "unsupported aggregate ABI"
// diagnostic — never a single-GPR miscompile. This test passes a by-value enum
// argument and asserts compilation rejects it; the adapter's argument-type
// seeding does not widen WS5's modeled shapes, so the rejection is exact.
// ===========================================================================

fn byval_enum_arg_module() -> TrustIrModule {
    let enum_ty = Ty::Enum(EnumId::new(0));
    let edef = EnumDef {
        id: EnumId::new(0),
        name: "E".to_string(),
        variants: vec![EnumVariant {
            name: "V0".to_string(),
            fields: vec![Ty::I64],
            field_names: Vec::new(),
        }],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    };

    // `_enum_caller(e: E) -> i64`: forward the by-value enum to an extern callee.
    // The argument reaches the call-arg classifier with the enum type seeded
    // from the callee's parameter signature; the classifier fails closed.
    let body = vec![call(Some(1), 1, &[0]), ret(1)];

    module(
        "byval_enum_arg",
        vec![],
        vec![edef],
        vec![
            FuncTy {
                params: vec![enum_ty.clone()],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![enum_ty.clone()],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![
            func(
                0,
                "_enum_caller",
                FuncTyId::new(0),
                block(vec![(0, enum_ty)], body),
            ),
            TrustIrFunction {
                attrs: Default::default(),
                id: FuncId::new(1),
                name: "_enum_use".to_string(),
                ty: FuncTyId::new(1),
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
            },
        ],
    )
}

#[test]
fn x86_64_byval_enum_arg_fails_closed() {
    // Host-independent: this is a compile-time fail-closed assertion (no link or
    // run), so it is not gated on `x86_64_oracle_enabled`.
    let m = byval_enum_arg_module();
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        ..CompilerConfig::default()
    });
    let err = compiler
        .compile(&m)
        .expect_err("by-value enum aggregate must fail closed, never miscompile");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("unsupported x86-64 aggregate ABI"),
        "expected a clear unsupported-aggregate diagnostic, got: {msg}"
    );
    // The enum must be named in the diagnostic so the rejection is unambiguous.
    assert!(
        msg.contains("Enum"),
        "fail-closed diagnostic should identify the enum shape, got: {msg}"
    );
}

// ===========================================================================
// Combined: register args + a by-value {i64,i64} + trailing args.
//
// `_combined_caller(a, b, c) -> i64` builds s = {a+b, a-b} and calls
//   `_combined(a, b, s, c, 99)` returning `a + b*2 + s.f0 + s.f1 + c + 99`.
// `a`/`b` consume GPRs, the 16-byte struct consumes the next register pair,
// and `c`/99 follow in the remaining GPRs — exercising consistent register
// indices when a register-class aggregate sits between scalar args.
// ===========================================================================

fn byval_combined_module() -> TrustIrModule {
    let agg = Ty::Struct(StructId::new(0));
    // value ids: 0=a, 1=b, 2=c
    let body = vec![
        alloca(3, agg.clone()),
        binop(4, BinOp::Add, Ty::I64, 0, 1), // a+b
        binop(5, BinOp::Sub, Ty::I64, 0, 1), // a-b
        insert_field(6, &agg, 3, 0, 4),
        insert_field(7, &agg, 3, 1, 5),
        iconst(10, Ty::I64, 99),
        // _combined(a, b, s, c, 99)
        call(Some(11), 1, &[0, 1, 3, 2, 10]),
        ret(11),
    ];
    module(
        "byval_combined",
        vec![struct_def(0, "I64x2C", &[Ty::I64, Ty::I64])],
        vec![],
        vec![
            FuncTy {
                params: vec![Ty::I64, Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![Ty::I64, Ty::I64, agg, Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![
            func(
                0,
                "_combined_caller",
                FuncTyId::new(0),
                block(vec![(0, Ty::I64), (1, Ty::I64), (2, Ty::I64)], body),
            ),
            TrustIrFunction {
                attrs: Default::default(),
                id: FuncId::new(1),
                name: "_combined".to_string(),
                ty: FuncTyId::new(1),
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
            },
        ],
    )
}

#[test]
fn x86_64_byval_combined_reg_and_trailing_args_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_byval_combined_reg_and_trailing_args_vs_clang") {
        return;
    }
    let m = byval_combined_module();
    let c = r#"
#include <stdint.h>
struct I64x2C { int64_t f0; int64_t f1; };
extern long _combined(long a, long b, struct I64x2C s, long c, long d);
long _combined_caller(long a, long b, long c) {
    struct I64x2C s = { a + b, a - b };
    return _combined(a, b, s, c, 99);
}
"#;
    let driver = r#"
#include <stdint.h>
#include <stdio.h>
struct I64x2C { int64_t f0; int64_t f1; };
long _combined(long a, long b, struct I64x2C s, long c, long d) {
    return a + b * 2 + s.f0 + s.f1 + c + d;
}
extern long _combined_caller(long a, long b, long c);
int main(void) {
    printf("%lld %lld\n",
        (long long)_combined_caller(7, 11, -5),
        (long long)_combined_caller(1000000, -2000000, 3));
    return 0;
}
"#;
    run_differential("x86_64_byval_combined_reg_and_trailing_args", &m, c, driver).unwrap();
}

// ===========================================================================
// Self-contained both-directions {i64,i64}: one trust-cg object provides BOTH
// the Alloca-building caller and the by-value callee, so the register-pair ABI
// is validated end-to-end inside trust-cg (caller pack -> callee unpack) vs
// clang's own both-sides lowering, for several inputs. `a` stays live across
// the call.
// ===========================================================================

fn self_contained_byval_i64x2_module() -> TrustIrModule {
    let agg = Ty::Struct(StructId::new(0));

    // callee `_sc2(s) -> i64`: f0 + f1*2
    let callee_body = vec![
        extract_field(1, &agg, 0, 0),
        extract_field(2, &agg, 0, 1),
        iconst(3, Ty::I64, 2),
        binop(4, BinOp::Mul, Ty::I64, 2, 3),
        binop(5, BinOp::Add, Ty::I64, 1, 4),
        ret(5),
    ];

    // entry `_sc2_entry(a, b) -> i64`: s = {a, b}; return _sc2(s) + a
    let entry_body = vec![
        // value 0 = a, 1 = b
        alloca(2, agg.clone()),
        insert_field(3, &agg, 2, 0, 0),
        insert_field(4, &agg, 2, 1, 1),
        call(Some(7), 1, &[2]),
        binop(8, BinOp::Add, Ty::I64, 7, 0), // keep `a` live across the call
        ret(8),
    ];

    module(
        "self_contained_byval_i64x2",
        vec![struct_def(0, "Sc2", &[Ty::I64, Ty::I64])],
        vec![],
        vec![
            FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![agg.clone()],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        vec![
            func(
                0,
                "_sc2_entry",
                FuncTyId::new(0),
                block(vec![(0, Ty::I64), (1, Ty::I64)], entry_body),
            ),
            func(
                1,
                "_sc2",
                FuncTyId::new(1),
                block(vec![(0, agg)], callee_body),
            ),
        ],
    )
}

#[test]
fn x86_64_self_contained_byval_i64x2_vs_clang() {
    if !x86_64_oracle_enabled("x86_64_self_contained_byval_i64x2_vs_clang") {
        return;
    }
    let m = self_contained_byval_i64x2_module();
    let c = r#"
#include <stdint.h>
struct Sc2 { int64_t f0; int64_t f1; };
static long _sc2(struct Sc2 s) { return s.f0 + s.f1 * 2; }
long _sc2_entry(long a, long b) {
    struct Sc2 s = { a, b };
    return _sc2(s) + a;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _sc2_entry(long a, long b);
int main(void) {
    printf("%lld %lld %lld %lld\n",
        (long long)_sc2_entry(10, 20),
        (long long)_sc2_entry(-1, -2),
        (long long)_sc2_entry(1000000007, 2),
        (long long)_sc2_entry(0, 0));
    return 0;
}
"#;
    run_differential("x86_64_self_contained_byval_i64x2", &m, c, driver).unwrap();
}
