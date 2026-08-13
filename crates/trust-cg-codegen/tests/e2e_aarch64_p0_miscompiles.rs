// trust-cg-codegen/tests/e2e_aarch64_p0_miscompiles.rs
//
// Pinned differential-vs-clang regressions for the SIX confirmed aarch64 P0
// silent-miscompile gaps from the completeness audit (§3, P0):
//
//   G1  sret CALLER side — call returning a >16-byte aggregate
//   G2  scalar float `Select` (f32/f64)
//   G3  switch dense jump-table, sub-64-bit selector + negative/high min_val
//   G4  `UIToFP` from a narrow u16 with dirty upper bits
//   G5  GEP over a `#[repr(packed)]` struct (CORRECT packed-offset address)
//   G6  CallIndirect narrow-int (i8) register-arg extension
//
// Each link-and-run test compiles a trust-ir module with trust-cg at O0 AND O2,
// links it against a clang C driver that embodies the correct (C == clang)
// semantics, and asserts bit-exact agreement on an aarch64-apple-darwin host.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TirBlock, BlockId, CallingConv, CastOp, Constant, FieldDef, FuncId, FuncTy,
    Function as TirFunction, ICmpOp, Inst, InstrNode, Module as TirModule, StructDef, StructId,
    StructRepr, Ty, ValueId,
};

fn aarch64_host() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn compile_obj(module: &TirModule, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    compiler
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
}

/// Link `obj` against C `driver`, run, return the process exit code.
/// `None` => not an aarch64-apple-darwin host (skip).
fn link_run(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
    if !aarch64_host() {
        eprintln!("SKIP {tag}: link-and-run requires aarch64-apple-darwin");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_p0"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).expect("write obj");
    fs::write(&drv_path, driver).expect("write driver");
    // Compile the C driver at -O2. This matters for G6: at -O2 an Apple-arm64
    // clang callee TRUSTS the AAPCS64 caller obligation and reads the narrow arg
    // register directly (no defensive re-extension), so a caller that fails to
    // extend is observably miscompiled. At -O0 the callee re-extends and masks
    // the bug. Harmless for the other gaps' oracles.
    let link = Command::new("cc")
        .args([
            "-O2",
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc available");
    assert!(
        link.status.success(),
        "{tag} link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(bin_path.to_str().unwrap())
        .output()
        .expect("run binary");
    let code = run.status.code().unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

fn run_both_opts(tag: &str, module: &TirModule, driver: &str) {
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_obj(module, opt).unwrap_or_else(|e| panic!("{tag} compile {opt:?}: {e}"));
        let Some(code) = link_run(&format!("{tag}_{opt:?}"), &obj, driver) else {
            return;
        };
        assert_eq!(code, 0, "{tag} miscompiled at {opt:?} (driver exit {code})");
    }
}

// ---------------------------------------------------------------------------
// G2 — scalar float Select (f32/f64)
// ---------------------------------------------------------------------------

/// `fn(c:i32, a:F, b:F) -> F { if c != 0 { a } else { b } }`
fn build_fsel(module: &mut TirModule, id: u32, name: &str, fty: Ty) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I32, fty.clone(), fty.clone()],
        returns: vec![fty.clone()],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I32),
            (ValueId::new(1), fty.clone()),
            (ValueId::new(2), fty.clone()),
        ],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Select {
                ty: fty,
                cond: ValueId::new(4),
                then_val: ValueId::new(1),
                else_val: ValueId::new(2),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    module.add_function(f);
}

const G2_DRIVER: &str = r#"
#include <stdio.h>
#include <string.h>
extern float  g2_fsel_f32(int c, float a, float b);
extern double g2_fsel_f64(int c, double a, double b);
static int eqf(float x, float y){ return memcmp(&x,&y,sizeof x)==0; }
static int eqd(double x, double y){ return memcmp(&x,&y,sizeof x)==0; }
int main(void){
    /* true AND false branch, both precisions, bit-exact */
    if(!eqf(g2_fsel_f32(1, 3.5f, -2.25f), 3.5f))   return 1;
    if(!eqf(g2_fsel_f32(0, 3.5f, -2.25f), -2.25f)) return 2;
    if(!eqf(g2_fsel_f32(7, -0.0f, 9.0f), -0.0f))   return 3; /* signed zero */
    if(!eqd(g2_fsel_f64(1, 3.5, -2.25), 3.5))      return 4;
    if(!eqd(g2_fsel_f64(0, 3.5, -2.25), -2.25))    return 5;
    if(!eqd(g2_fsel_f64(0, 1e300, -1e300), -1e300))return 6;
    printf("g2 float select OK\n");
    return 0;
}
"#;

#[test]
fn g2_float_select_matches_clang() {
    let mut m = TirModule::new("g2");
    build_fsel(&mut m, 0, "g2_fsel_f32", Ty::F32);
    build_fsel(&mut m, 1, "g2_fsel_f64", Ty::F64);
    run_both_opts("g2", &m, G2_DRIVER);
}

// ---------------------------------------------------------------------------
// G4 — UIToFP from a narrow u16 with dirty upper bits
// ---------------------------------------------------------------------------

/// `fn(a:u16, b:u16) -> f32 { ((a + b) as u16) as f32 }`
/// The 16-bit add wraps and leaves dirty bits in [16:31]; UCVTF must read only
/// the low 16 bits.
fn build_u16_to_f32(module: &mut TirModule) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::U16, Ty::U16],
        returns: vec![Ty::F32],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g4_u16_to_f32", ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::U16), (ValueId::new(1), Ty::U16)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U16,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::UIToFP,
                src_ty: Ty::U16,
                dst_ty: Ty::F32,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(f);
}

const G4_DRIVER: &str = r#"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
extern float g4_u16_to_f32(uint16_t a, uint16_t b);
static int eqf(float x, float y){ return memcmp(&x,&y,sizeof x)==0; }
int main(void){
    /* 40000+40000 = 80000, wraps to (uint16_t)80000 = 14464 */
    if(!eqf(g4_u16_to_f32(40000, 40000), (float)(uint16_t)(40000+40000))) return 1;
    if(!eqf(g4_u16_to_f32(65535, 2),     (float)(uint16_t)(65535+2)))     return 2;
    if(!eqf(g4_u16_to_f32(1000, 24),     (float)(uint16_t)(1000+24)))     return 3;
    printf("g4 uitofp u16 OK\n");
    return 0;
}
"#;

#[test]
fn g4_uitofp_narrow_u16_matches_clang() {
    let mut m = TirModule::new("g4");
    build_u16_to_f32(&mut m);
    run_both_opts("g4", &m, G4_DRIVER);
}

// ---------------------------------------------------------------------------
// G3 — switch dense jump-table, sub-64-bit selector + negative / high min_val
// ---------------------------------------------------------------------------

/// A block that just returns the i32 constant `val`.
fn ret_const_block(id: u32, next_val: ValueId, ret_val: ValueId, val: i64) -> TirBlock {
    TirBlock {
        id: BlockId::new(id),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(val as i128),
            })
            .with_result(next_val),
            InstrNode::new(Inst::Return {
                values: vec![ret_val],
            }),
        ],
    }
}

/// `fn(x: SEL) -> i32 { match x { case_vals[i] => outs[i], _ => 999 } }`
/// as a dense contiguous jump table.
fn build_switch(module: &mut TirModule, id: u32, name: &str, sel_ty: Ty, cases: &[(i64, i64)]) {
    let ft = module.add_func_type(FuncTy {
        params: vec![sel_ty.clone()],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(id), name, ft, BlockId::new(0));

    // Block ids: 0 = entry (switch); 1.. = case blocks; last = default.
    let default_block = BlockId::new(cases.len() as u32 + 1);
    let switch_cases: Vec<trust_ir::SwitchCase> = cases
        .iter()
        .enumerate()
        .map(|(i, (v, _))| trust_ir::SwitchCase {
            value: Constant::Int(*v as i128),
            target: BlockId::new(i as u32 + 1),
            args: vec![],
        })
        .collect();

    let mut blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), sel_ty)],
        body: vec![InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: default_block,
            default_args: vec![],
            cases: switch_cases,
            exhaustive_enum_unreachable: false,
        })],
    }];
    // Fresh value ids per block (disjoint from the entry's v0).
    let mut vid = 10u32;
    for (i, (_, out)) in cases.iter().enumerate() {
        let nv = ValueId::new(vid);
        vid += 1;
        blocks.push(ret_const_block(i as u32 + 1, nv, nv, *out));
    }
    let dv = ValueId::new(vid);
    blocks.push(ret_const_block(cases.len() as u32 + 1, dv, dv, 999));

    f.blocks = blocks;
    module.add_function(f);
}

const G3_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
extern int g3_classify_i32(int32_t x);
extern int g3_classify_u32(uint32_t x);
static int oracle_i32(int32_t x){
    switch(x){
        case -3: return 130; case -2: return 120; case -1: return 110;
        case  0: return 100; case  1: return 111; case  2: return 122;
        case  3: return 133; default: return 999;
    }
}
static int oracle_u32(uint32_t x){
    switch(x){
        case 0x80000000u: return 500; case 0x80000001u: return 501;
        case 0x80000002u: return 502; case 0x80000003u: return 503;
        default: return 999;
    }
}
int main(void){
    for(int32_t x=-6; x<=6; x++)
        if(g3_classify_i32(x) != oracle_i32(x)) return (x<0? -x : x)+1;
    uint32_t us[] = {0x7FFFFFFFu,0x80000000u,0x80000001u,0x80000002u,0x80000003u,0x80000004u};
    for(unsigned i=0;i<sizeof us/sizeof us[0];i++)
        if(g3_classify_u32(us[i]) != oracle_u32(us[i])) return 40+i;
    printf("g3 switch OK\n");
    return 0;
}
"#;

#[test]
fn g3_switch_negative_and_high_min_matches_clang() {
    let mut m = TirModule::new("g3");
    build_switch(
        &mut m,
        0,
        "g3_classify_i32",
        Ty::I32,
        &[
            (-3, 130),
            (-2, 120),
            (-1, 110),
            (0, 100),
            (1, 111),
            (2, 122),
            (3, 133),
        ],
    );
    build_switch(
        &mut m,
        1,
        "g3_classify_u32",
        Ty::U32,
        &[
            (0x8000_0000, 500),
            (0x8000_0001, 501),
            (0x8000_0002, 502),
            (0x8000_0003, 503),
        ],
    );
    run_both_opts("g3", &m, G3_DRIVER);
}

// ---------------------------------------------------------------------------
// G6 — CallIndirect narrow-int (i8) register-arg extension
// ---------------------------------------------------------------------------

/// `fn(fp: *fn(i8)->i32, a: i32) -> i32 { let x = a as i8; fp(x) }`
/// `a as i8` (Trunc) leaves a non-canonical i8; the indirect call must
/// sign-extend it to canonical w0 for the clang callee.
fn build_g6_caller(module: &mut TirModule) {
    let callee_sig = module.add_func_type(FuncTy {
        params: vec![Ty::I8],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g6_caller", ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: Ty::I8,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callee_sig,
                args: vec![ValueId::new(2)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(f);
}

const G6_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
/* Callee trusts the AAPCS64 caller obligation: w0 arrives sign-extended. */
static int g6_callee(signed char v){ return (int)v * 7; }
extern int g6_caller(long fp, int a);
int main(void){
    long fp = (long)(void*)&g6_callee;
    int cases[] = {200, 255, 128, -1, 0, 300, 129};
    for(unsigned i=0;i<sizeof cases/sizeof cases[0];i++){
        int a = cases[i];
        int expect = (int)(signed char)a * 7;
        if(g6_caller(fp, a) != expect) return (int)i + 1;
    }
    printf("g6 indirect narrow-arg OK\n");
    return 0;
}
"#;

#[test]
fn g6_indirect_narrow_arg_matches_clang() {
    let mut m = TirModule::new("g6");
    build_g6_caller(&mut m);
    run_both_opts("g6", &m, G6_DRIVER);
}

// ---------------------------------------------------------------------------
// G1 — sret CALLER side: (indirect) call returning a >16-byte aggregate
// ---------------------------------------------------------------------------

/// `fn(fp: *fn()->{i64,i64,i64}) -> i64 { let s = fp(); s.0 + s.1*1000 + s.2*1000000 }`
fn build_g1_caller(module: &mut TirModule) {
    let sid = StructId::new(0);
    module.add_struct(StructDef {
        id: sid,
        name: "S3".to_string(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "c".into(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    let struct_ty = Ty::Struct(sid);
    let callee_sig = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![struct_ty.clone()],
        is_vararg: false,
    });
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g1_caller", ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            // s = fp()  -> {i64,i64,i64} (returned via sret / X8)
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callee_sig,
                args: vec![],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::ExtractField {
                ty: struct_ty.clone(),
                aggregate: ValueId::new(1),
                field: 0,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractField {
                ty: struct_ty.clone(),
                aggregate: ValueId::new(1),
                field: 1,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::ExtractField {
                ty: struct_ty,
                aggregate: ValueId::new(1),
                field: 2,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1000),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1_000_000),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(4),
                rhs: ValueId::new(6),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(7),
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(9),
                rhs: ValueId::new(8),
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            }),
        ],
    }];
    module.add_function(f);
}

const G1_DRIVER: &str = r#"
#include <stdio.h>
struct S3 { long a, b, c; };
static struct S3 g1_make3(void){ struct S3 s = {11, 22, 33}; return s; }
extern long g1_caller(long fp);
int main(void){
    long fp = (long)(void*)&g1_make3;
    long r = g1_caller(fp);
    long expect = 11 + 22*1000 + 33*1000000; /* 33022011 */
    if(r != expect){ printf("g1 FAIL: got %ld want %ld\n", r, expect); return 1; }
    printf("g1 sret caller OK\n");
    return 0;
}
"#;

#[test]
fn g1_sret_caller_matches_clang() {
    let mut m = TirModule::new("g1");
    build_g1_caller(&mut m);
    run_both_opts("g1", &m, G1_DRIVER);
}

// ---------------------------------------------------------------------------
// G5 — GEP over a #[repr(packed)] struct computes the CORRECT packed address
// ---------------------------------------------------------------------------

/// Build `fn(p: ptr) -> ptr { &((*P)p)[0].b }` — a multi-index GEP
/// `getelementptr P, p, 0, 1` selecting the second field of struct P (given
/// `repr`). For `#[repr(packed)] struct P { a: u8, b: u32 }` field `b` sits at
/// PACKED offset 1; for `#[repr(C)]` it sits at natural offset 4.
fn build_g5_field_b(m: &mut TirModule, sid: StructId, fid: u32, name: &str, repr: StructRepr) {
    m.add_struct(StructDef {
        id: sid,
        name: format!("P{}", sid.index()),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::U8,
                offset: None,
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::U32,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr,
    });
    let struct_ty = Ty::Struct(sid);
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::Ptr],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(fid), name, ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::GEP {
                pointee_ty: struct_ty,
                base: ValueId::new(0),
                indices: vec![ValueId::new(1), ValueId::new(2)],
                inbounds: false,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(f);
}

const G5_DRIVER: &str = r#"
#include <stdio.h>
extern void* g5_field_b_packed(void* p);
extern void* g5_field_b_c(void* p);
int main(void){
    char buf[16];
    long packed_off = (char*)g5_field_b_packed(buf) - buf;
    long c_off      = (char*)g5_field_b_c(buf) - buf;
    /* #[repr(packed)] {u8,u32}: offsetof(b) == 1; #[repr(C)]: 4. */
    if(packed_off != 1){ printf("g5 FAIL: packed offset %ld want 1\n", packed_off); return 1; }
    if(c_off != 4){ printf("g5 FAIL: C offset %ld want 4\n", c_off); return 2; }
    printf("g5 packed GEP OK\n");
    return 0;
}
"#;

#[test]
fn g5_packed_struct_gep_matches_clang() {
    // A #[repr(packed)] struct GEP must compute the PACKED field address
    // (offset 1), NOT the natural-C aligned offset (4). The identical #[repr(C)]
    // shape must still compute the natural offset (4), proving the packed path
    // is specific to the packed repr.
    let mut m = TirModule::new("g5");
    build_g5_field_b(
        &mut m,
        StructId::new(0),
        0,
        "g5_field_b_packed",
        StructRepr::Packed(1),
    );
    build_g5_field_b(&mut m, StructId::new(1), 1, "g5_field_b_c", StructRepr::C);
    run_both_opts("g5", &m, G5_DRIVER);
}
