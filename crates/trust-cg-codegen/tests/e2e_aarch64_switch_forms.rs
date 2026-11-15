// trust-cg-codegen/tests/e2e_aarch64_switch_forms.rs
//
// Native controls for every `Inst::Switch` lowering strategy and for indirect
// calls through tables of function pointers, at O0, O1, O2 and O3, against the
// host C compiler as the oracle (L04-P11).
//
// Switch shapes: dense i64/i32 (jump table, ADR/LDRSW/ADD/BR), a jump-table
// sized 12-case i32 switch, dense ranges with a negative minimum (SUB
// normalization with a materialized negative), a dense range with holes
// (hole slots route to the default), a dense range with a wide minimum
// (MOVZ/MOVK-materialized normalization and 64-bit bounds), sparse i64/i32
// switches of binary-search size (CMP/B.EQ/B.LT trees with materialized
// pivots) and a three-case linear scan. Every case value, its neighbours,
// default-hitting values and the i32/i64 extremes are probed. The compile
// runs the per-compile switch-dispatch binding
// (`trust_cg_verify::aarch64_switch_binding`) on every function; this file
// then executes the bytes it admitted.
//
// Spilled selector: twenty-four values live across a dense eight-case switch
// force the selector into a spill slot; at O1 the dispatch reloads it for the
// bounds compare and again for the table load, which the binding admits only
// because nothing between the two reloads can write the slot.
//
// Indirect calls: trust-cg trampolines load a function pointer from a table
// the C driver owns (`GEP` + `Load` + `CallIndirect`) and call it with one or
// two arguments, including a double indirection `t[i](t[j](x))`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CallingConv, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, SwitchCase, Ty, ValueId,
};

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/native_host.rs"]
mod native_host;

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn ret_const_block(bb: u32, vid: u32, k: i64) -> TrustIrBlock {
    TrustIrBlock {
        id: BlockId::new(bb),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k as i128),
            })
            .with_result(ValueId::new(vid)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(vid)],
            }),
        ],
    }
}

/// `fn name(x: sel_ty) -> i64 { switch x { k => 1000 + position(k), _ => dflt } }`.
fn build_switch_fn(
    m: &mut TrustIrModule,
    id: u32,
    name: &str,
    sel_ty: Ty,
    cases: &[i64],
    dflt: i64,
) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![sel_ty.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    let default_bb = cases.len() as u32 + 1;
    let switch_cases: Vec<SwitchCase> = cases
        .iter()
        .enumerate()
        .map(|(i, cv)| SwitchCase {
            value: Constant::Int(*cv as i128),
            target: BlockId::new(i as u32 + 1),
            args: vec![],
        })
        .collect();
    let mut blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), sel_ty)],
        body: vec![InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: BlockId::new(default_bb),
            default_args: vec![],
            cases: switch_cases,
            exhaustive_enum_unreachable: false,
        })],
    }];
    for i in 0..cases.len() {
        blocks.push(ret_const_block(
            i as u32 + 1,
            100 + i as u32,
            1000 + i as i64,
        ));
    }
    blocks.push(ret_const_block(default_bb, 100 + cases.len() as u32, dflt));
    f.blocks = blocks;
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

/// `(name, selector type, case values, default)` — the same table drives the
/// trust-ir module and the C oracle.
const SWITCHES: &[(&str, Ty, &[i64], i64)] = &[
    ("sw_dense_i64", Ty::I64, &[0, 1, 2, 3, 4, 5, 6, 7], -1),
    (
        "sw_dense_i32",
        Ty::I32,
        &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
        7,
    ),
    ("sw_negative_i64", Ty::I64, &[-5, -4, -3, -2, -1, 0, 1], -99),
    ("sw_negative_i32", Ty::I32, &[-4, -3, -2, -1, 0, 1, 2], -5),
    ("sw_holes_i64", Ty::I64, &[10, 11, 13, 14, 16, 17], 3),
    (
        "sw_wide_min_i64",
        Ty::I64,
        &[100000, 100001, 100002, 100003, 100004, 100005],
        0,
    ),
    (
        "sw_sparse_i64",
        Ty::I64,
        &[-100, -7, 0, 3, 77, 300, 5000, 30000, 1_000_000],
        -2,
    ),
    (
        "sw_sparse_i32",
        Ty::I32,
        &[-9, 1, 9, 64, 1023, 70000, 2_000_000],
        11,
    ),
    ("sw_linear_i32", Ty::I32, &[1, 9, 70000], 7),
];

fn build_switch_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("switch_forms");
    for (id, (name, ty, cases, dflt)) in SWITCHES.iter().enumerate() {
        build_switch_fn(&mut m, id as u32, name, ty.clone(), cases, *dflt);
    }
    m
}

fn c_type(ty: &Ty) -> &'static str {
    match ty {
        Ty::I32 => "int32_t",
        _ => "int64_t",
    }
}

/// The C oracle: one `switch` per trust-ir function, over the same table,
/// plus the probe loop.
fn switch_driver() -> String {
    let mut src = String::from("#include <stdio.h>\n#include <stdint.h>\n");
    for (name, ty, _, _) in SWITCHES {
        src.push_str(&format!("extern int64_t {name}({});\n", c_type(ty)));
    }
    for (name, ty, cases, dflt) in SWITCHES {
        src.push_str(&format!(
            "static int64_t {name}_ref({} x) {{\n    switch (x) {{\n",
            c_type(ty)
        ));
        for (i, k) in cases.iter().enumerate() {
            src.push_str(&format!("        case {k}: return {};\n", 1000 + i as i64));
        }
        src.push_str(&format!("        default: return {dflt};\n    }}\n}}\n"));
    }
    src.push_str(
        "static const int64_t probes[] = {\n    -9223372036854775807LL - 1, -2147483649LL, -2147483648LL, -2147483647LL,\n    -1000001, -1000000, -999999, -30001, -30000, -100, -99, -101, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1,\n    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 63, 64, 65, 76, 77, 78,\n    299, 300, 301, 1022, 1023, 1024, 4095, 4096, 4097, 4999, 5000, 5001, 29999, 30000, 30001,\n    65535, 65536, 69999, 70000, 70001, 99999, 100000, 100001, 100002, 100003, 100004, 100005, 100006,\n    999999, 1000000, 1000001, 1999999, 2000000, 2000001, 2147483647LL, 2147483648LL, 4294967296LL,\n    4294967297LL, 9223372036854775807LL\n};\n",
    );
    src.push_str("int main(void) {\n    int rc = 0;\n    for (unsigned i = 0; i < sizeof(probes) / sizeof(probes[0]); i++) {\n        int64_t x = probes[i];\n");
    for (index, (name, ty, _, _)) in SWITCHES.iter().enumerate() {
        let cast = c_type(ty);
        src.push_str(&format!(
            "        if ({name}(({cast})x) != {name}_ref(({cast})x)) {{ printf(\"{name} x=%lld got %lld want %lld\\n\", (long long)x, (long long){name}(({cast})x), (long long){name}_ref(({cast})x)); rc = {}; }}\n",
            index + 1
        ));
    }
    src.push_str("    }\n    if (rc == 0) printf(\"switch forms: every strategy and selector width matches clang\\n\");\n    return rc;\n}\n");
    src
}

/// Trampolines through a table of C function pointers.
fn build_indirect_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("indirect_tables");
    let callee1 = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let callee2 = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    // call_table1(fps: ptr, i: i64, x: i64) -> i64 { fps[i](x) }
    let sig1 = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "call_table1", sig1, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::Ptr,
                base: ValueId::new(0),
                indices: vec![ValueId::new(1)],
                inbounds: true,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Load {
                ty: Ty::Ptr,
                ptr: ValueId::new(3),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(4),
                sig: callee1,
                args: vec![ValueId::new(2)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    // call_table2(fps: ptr, i: i64, a: i64, b: i64) -> i64 { fps[i](a, b) }
    let sig2 = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(1), "call_table2", sig2, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
            (ValueId::new(3), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::Ptr,
                base: ValueId::new(0),
                indices: vec![ValueId::new(1)],
                inbounds: true,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Load {
                ty: Ty::Ptr,
                ptr: ValueId::new(4),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(5),
                sig: callee2,
                args: vec![ValueId::new(2), ValueId::new(3)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(6)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    // call_table_twice(fps: ptr, i: i64, j: i64, x: i64) -> i64 { fps[i](fps[j](x)) }
    let sig3 = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(2), "call_table_twice", sig3, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
            (ValueId::new(3), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::Ptr,
                base: ValueId::new(0),
                indices: vec![ValueId::new(2)],
                inbounds: true,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Load {
                ty: Ty::Ptr,
                ptr: ValueId::new(4),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(5),
                sig: callee1,
                args: vec![ValueId::new(3)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::Ptr,
                base: ValueId::new(0),
                indices: vec![ValueId::new(1)],
                inbounds: true,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Load {
                ty: Ty::Ptr,
                ptr: ValueId::new(7),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(8),
                sig: callee1,
                args: vec![ValueId::new(6)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(9)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

const INDIRECT_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
typedef int64_t (*fn1)(int64_t);
typedef int64_t (*fn2)(int64_t, int64_t);
extern int64_t call_table1(fn1 *, int64_t, int64_t);
extern int64_t call_table2(fn2 *, int64_t, int64_t, int64_t);
extern int64_t call_table_twice(fn1 *, int64_t, int64_t, int64_t);
static int64_t dbl(int64_t x) { return 2 * x; }
static int64_t neg(int64_t x) { return -x; }
static int64_t inc(int64_t x) { return x + 1; }
static int64_t sq(int64_t x) { return x * x; }
static int64_t add(int64_t a, int64_t b) { return a + b; }
static int64_t sub(int64_t a, int64_t b) { return a - b; }
static int64_t mul(int64_t a, int64_t b) { return a * b; }
static int64_t sel(int64_t a, int64_t b) { return a < b ? a : b; }
int main(void) {
    fn1 t1[4] = { dbl, neg, inc, sq };
    fn2 t2[4] = { add, sub, mul, sel };
    const int64_t xs[] = { -100, -7, -1, 0, 1, 2, 3, 21, 1000, 2147483648LL, -9223372036854775807LL };
    int rc = 0;
    for (int i = 0; i < 4; i++) {
        for (unsigned p = 0; p < sizeof(xs) / sizeof(xs[0]); p++) {
            int64_t x = xs[p];
            if (call_table1(t1, i, x) != t1[i](x)) { printf("table1 i=%d x=%lld\n", i, (long long)x); rc = 1; }
            for (int j = 0; j < 4; j++) {
                if (call_table2(t2, i, x, xs[(p + j) % 11]) != t2[i](x, xs[(p + j) % 11])) { printf("table2 i=%d\n", i); rc = 2; }
                if (call_table_twice(t1, i, j, x) != t1[i](t1[j](x))) { printf("twice i=%d j=%d x=%lld\n", i, j, (long long)x); rc = 3; }
            }
        }
    }
    if (rc == 0) printf("indirect calls through function-pointer tables match clang\n");
    return rc;
}
"#;

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    compiler
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
}

fn link_run(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
    if !native_host::NATIVE {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return None;
    }
    let dir = fresh_dir::create(&format!("trust_cg_{tag}_e2e_"));
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).unwrap();
    fs::write(&drv_path, driver).unwrap();
    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .args(native_host::c_math_library_args())
        .output()
        .expect("cc");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(bin_path.to_str().unwrap()).output().unwrap();
    let code = run.status.code().unwrap_or(-1);
    if code != 0 {
        eprintln!("{}", String::from_utf8_lossy(&run.stdout));
    }
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_switch_forms_match_clang() {
    let module = build_switch_module();
    let driver = switch_driver();
    for opt in OPT_LEVELS {
        let obj = compile_at(&module, opt).expect("switch-forms module must compile");
        let Some(code) = link_run("switch_forms", &obj, &driver) else {
            return;
        };
        assert_eq!(
            code, 0,
            "switch-forms result mismatch at {opt:?} (function {code})"
        );
    }
}

#[test]
fn e2e_aarch64_indirect_call_tables_match_clang() {
    let module = build_indirect_module();
    for opt in OPT_LEVELS {
        let obj = compile_at(&module, opt).expect("indirect-table module must compile");
        let Some(code) = link_run("indirect_tables", &obj, INDIRECT_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "indirect-table result mismatch at {opt:?} (check {code})"
        );
    }
}

/// `sw_pressure(x, a)`: `v_i = a * (i + 3) + (7i + 1)` for 24 values, live
/// across `switch x { k in 0..8 => block k, _ => block 8 }`, and block `k`
/// returns `k + sum_i v_i * (i + k + 1)`.
fn build_pressure_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("switch_forms_pressure");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "sw_pressure", ft, BlockId::new(0));
    let mut next = 10u32;
    let mut fresh = || {
        next += 1;
        ValueId::new(next)
    };
    let konst = |v: ValueId, k: i128| {
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(k),
        })
        .with_result(v)
    };
    let bin = |v: ValueId, op: BinOp, lhs: ValueId, rhs: ValueId| {
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs,
            rhs,
        })
        .with_result(v)
    };
    let (x, a) = (ValueId::new(0), ValueId::new(1));
    let mut body = Vec::new();
    let mut live = Vec::new();
    for i in 0..24i128 {
        let (c1, c2, t, v) = (fresh(), fresh(), fresh(), fresh());
        body.push(konst(c1, i + 3));
        body.push(konst(c2, i * 7 + 1));
        body.push(bin(t, BinOp::Mul, a, c1));
        body.push(bin(v, BinOp::Add, t, c2));
        live.push(v);
    }
    body.push(InstrNode::new(Inst::Switch {
        value: x,
        default: BlockId::new(9),
        default_args: vec![],
        cases: (0..8)
            .map(|k| SwitchCase {
                value: Constant::Int(k),
                target: BlockId::new(k as u32 + 1),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    }));
    let mut blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(x, Ty::I64), (a, Ty::I64)],
        body,
    }];
    for k in 0..9u32 {
        let mut body = Vec::new();
        let mut acc = fresh();
        body.push(konst(acc, i128::from(k)));
        for (i, v) in live.iter().enumerate() {
            let (ck, t, sum) = (fresh(), fresh(), fresh());
            body.push(konst(ck, i as i128 + i128::from(k) + 1));
            body.push(bin(t, BinOp::Mul, *v, ck));
            body.push(bin(sum, BinOp::Add, acc, t));
            acc = sum;
        }
        body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
        blocks.push(TrustIrBlock {
            id: BlockId::new(k + 1),
            params: vec![],
            body,
        });
    }
    f.blocks = blocks;
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

const PRESSURE_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern int64_t sw_pressure(int64_t x, int64_t a);
static int64_t reference(int64_t x, int64_t a) {
    uint64_t v[24];
    for (int i = 0; i < 24; i++) v[i] = (uint64_t)a * (uint64_t)(i + 3) + (uint64_t)(i * 7 + 1);
    uint64_t k = (x >= 0 && x < 8) ? (uint64_t)x : 8;
    uint64_t acc = k;
    for (int i = 0; i < 24; i++) acc += v[i] * (uint64_t)(i + k + 1);
    return (int64_t)acc;
}
int main(void) {
    int rc = 0;
    const int64_t xs[] = { -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, INT64_MIN, INT64_MAX };
    for (int64_t a = -3; a < 4; a++) {
        for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; i++) {
            int64_t x = xs[i], s = a * 1000003;
            if (sw_pressure(x, s) != reference(x, s)) {
                printf("sw_pressure x=%lld a=%lld\n", (long long)x, (long long)s);
                rc = 1;
            }
        }
    }
    if (rc == 0) printf("spilled-selector switch matches the C reference\n");
    return rc;
}
"#;

#[test]
fn e2e_aarch64_spilled_selector_switch_matches_c() {
    let module = build_pressure_module();
    for opt in OPT_LEVELS {
        let obj = compile_at(&module, opt).expect("spilled-selector switch must compile");
        let Some(code) = link_run("switch_pressure", &obj, PRESSURE_DRIVER) else {
            return;
        };
        assert_eq!(code, 0, "spilled-selector switch mismatch at {opt:?}");
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
