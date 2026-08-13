// trust-cg-codegen/tests/e2e_aarch64_vector_lane.rs
//
// End-to-end (compile -> link -> RUN) coverage for ExtractElement / InsertElement
// on <16 x i8> and <8 x i16> (audit A5/A6). These fail-closed (the adapter routed
// every non-v2i64 vector to the <4 x i32> path, which rejected them). The integer
// lane opcodes V16I8/V8I16 Extract/InsertLane are already isel-handled; this wires
// the adapter routing. Verified on hardware.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, CastOp, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `fn name(in: *const V) -> i32 { (*in)[LANE] as i32 }` — load a vector, extract
/// a constant lane, sign-extend to i32 and return.
fn build_extract(
    func_id: u32,
    name: &str,
    module: &mut TrustIrModule,
    vec_ty: Ty,
    elem_ty: Ty,
    lane: i128,
) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: vec_ty.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(lane),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractElement {
                ty: elem_ty.clone(),
                array: ValueId::new(1),
                index: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Cast {
                op: CastOp::SExt,
                src_ty: elem_ty,
                dst_ty: Ty::I32,
                operand: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    module.add_function(f);
}

/// `fn name(in: *const V, val: i32, out: *mut V) { let v=*in; v[LANE]=val as E; *out=v; }`
fn build_insert(
    func_id: u32,
    name: &str,
    module: &mut TrustIrModule,
    vec_ty: Ty,
    elem_ty: Ty,
    lane: i128,
) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I32, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::I32),
            (ValueId::new(2), Ty::Ptr),
        ],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: vec_ty.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: elem_ty.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(lane),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::InsertElement {
                ty: vec_ty.clone(),
                array: ValueId::new(3),
                index: ValueId::new(5),
                value: ValueId::new(4),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Store {
                ty: vec_ty,
                ptr: ValueId::new(2),
                value: ValueId::new(6),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(f);
}

/// `fn name(in: *const V) -> E { (*in)[LANE] }` for FP element E (no extension).
fn build_fp_extract(
    func_id: u32,
    name: &str,
    module: &mut TrustIrModule,
    vec_ty: Ty,
    elem_ty: Ty,
    lane: i128,
) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![elem_ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: vec_ty,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(lane),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractElement {
                ty: elem_ty,
                array: ValueId::new(1),
                index: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(f);
}

/// `fn name(in: *const V, val: E, out: *mut V) { let v=*in; v[LANE]=val; *out=v; }`
fn build_fp_insert(
    func_id: u32,
    name: &str,
    module: &mut TrustIrModule,
    vec_ty: Ty,
    elem_ty: Ty,
    lane: i128,
) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, elem_ty.clone(), Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), elem_ty),
            (ValueId::new(2), Ty::Ptr),
        ],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: vec_ty.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(lane),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::InsertElement {
                ty: vec_ty.clone(),
                array: ValueId::new(3),
                index: ValueId::new(4),
                value: ValueId::new(1),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Store {
                ty: vec_ty,
                ptr: ValueId::new(2),
                value: ValueId::new(5),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("vec_lane");
    let v16i8 = Ty::Vector(Box::new(Ty::I8), 16);
    let v8i16 = Ty::Vector(Box::new(Ty::I16), 8);
    let v4f32 = Ty::Vector(Box::new(Ty::F32), 4);
    let v2f64 = Ty::Vector(Box::new(Ty::F64), 2);
    build_extract(0, "_v16i8_get3", &mut module, v16i8.clone(), Ty::I8, 3);
    build_extract(1, "_v8i16_get5", &mut module, v8i16.clone(), Ty::I16, 5);
    build_insert(2, "_v16i8_set5", &mut module, v16i8, Ty::I8, 5);
    build_insert(3, "_v8i16_set2", &mut module, v8i16, Ty::I16, 2);
    build_fp_extract(4, "_v4f32_get2", &mut module, v4f32.clone(), Ty::F32, 2);
    build_fp_extract(5, "_v2f64_get1", &mut module, v2f64.clone(), Ty::F64, 1);
    build_fp_insert(6, "_v4f32_set1", &mut module, v4f32, Ty::F32, 1);
    build_fp_insert(7, "_v2f64_set0", &mut module, v2f64, Ty::F64, 0);
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("vector lane ops must compile");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>

extern int    _v16i8_get3(const int8_t *in);
extern int    _v8i16_get5(const int16_t *in);
extern void   _v16i8_set5(const int8_t *in, int val, int8_t *out);
extern void   _v8i16_set2(const int16_t *in, int val, int16_t *out);
extern float  _v4f32_get2(const float *in);
extern double _v2f64_get1(const double *in);
extern void   _v4f32_set1(const float *in, float val, float *out);
extern void   _v2f64_set0(const double *in, double val, double *out);

#include <string.h>
static int eqf(float a, float b)   { return memcmp(&a, &b, sizeof a) == 0; }
static int eqd(double a, double b) { return memcmp(&a, &b, sizeof a) == 0; }

int main(void) {
    int8_t  b[16];
    for (int i = 0; i < 16; i++) b[i] = (int8_t)(i * 7 - 50);
    if (_v16i8_get3(b) != b[3]) return 1;             /* extract lane 3, sign-extended */

    int16_t h[8];
    for (int i = 0; i < 8; i++) h[i] = (int16_t)(i * 5000 - 12000);
    if (_v8i16_get5(h) != h[5]) return 2;

    int8_t out8[16];
    _v16i8_set5(b, -99, out8);
    if (out8[5] != (int8_t)-99) return 3;             /* lane 5 replaced */
    for (int i = 0; i < 16; i++) if (i != 5 && out8[i] != b[i]) return 4; /* others intact */

    int16_t out16[8];
    _v8i16_set2(h, 31000, out16);
    if (out16[2] != (int16_t)31000) return 5;
    for (int i = 0; i < 8; i++) if (i != 2 && out16[i] != h[i]) return 6;

    /* FP vector lanes (stack path) */
    float fs[4] = { 1.5f, -2.5f, 3.25f, -4.75f };
    if (!eqf(_v4f32_get2(fs), fs[2])) return 7;
    double ds[2] = { 9.5, -8.25 };
    if (!eqd(_v2f64_get1(ds), ds[1])) return 8;

    float fout[4];
    _v4f32_set1(fs, 99.5f, fout);
    if (!eqf(fout[1], 99.5f)) return 9;
    for (int i = 0; i < 4; i++) if (i != 1 && !eqf(fout[i], fs[i])) return 10;

    double dout[2];
    _v2f64_set0(ds, -123.5, dout);
    if (!eqd(dout[0], -123.5)) return 11;
    if (!eqd(dout[1], ds[1])) return 12;

    printf("<16 x i8>/<8 x i16>/<4 x f32>/<2 x f64> extract/insert lane correct\n");
    return 0;
}
"#;

fn link_run_exit_code(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: link-and-run requires an aarch64-apple-darwin host");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_e2e"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).expect("write .o");
    fs::write(&drv_path, driver).expect("write driver");
    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc available");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(bin_path.to_str().unwrap())
        .output()
        .expect("run binary");
    let code = run.status.code().unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_narrow_vector_extract_insert() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("vec_lane", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "vector lane extract/insert runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
