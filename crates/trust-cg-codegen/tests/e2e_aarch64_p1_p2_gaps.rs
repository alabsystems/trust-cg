// trust-cg-codegen/tests/e2e_aarch64_p1_p2_gaps.rs
//
// Pins for the P1/P2 aarch64 completeness-audit gaps (§3, P1 & P2). Each gap is
// either a CORRECT lowering (pinned differential-vs-clang, link-and-run on an
// aarch64-apple-darwin host at O0 AND O2) or a SOUND fail-close (pinned by a
// "must be rejected" compile check):
//
//   G7   InsertField of a nested-aggregate field into a NON-packed struct
//        -> CORRECT FIX (copies the nested field bytes with memmove).
//   G8   Aggregate/HFA param passed on the STACK (registers exhausted)
//        -> CORRECT FIX (callee reads the slot ADDRESS for a by-value spill and
//        the spilled POINTER for a >16B indirect spill; caller stores the
//        pointer for a >16B indirect spill). Differential vs clang, both
//        directions and both sizes.
//   G9   ABI no-backfill: NGRN/NSRN clamped to 8 on aggregate/HFA stack spill
//        -> CORRECT FIX. Differential `f(a..g:i64, s:{i64,i64}, h:i64)` vs clang.
//   G10  Imported/external DATA global -> CORRECT FIX (GOT-indirect ExternRef).
//        Differential: trust-cg and clang share an imported symbol.
//   G11  libc memcpy/memmove/memset whose RETURN value (dest) is used
//        -> CORRECT FIX. Differential vs clang.
//   G13  Narrow i8/i16 switch selector with dirty upper bits -> reproduced and
//        FIXED (mask/extend to logical width). Differential vs clang.
//   G14-G16  Scalar float atomics (AtomicLoad/AtomicStore/CmpXchg F32/F64)
//        -> FAIL-CLOSE (would encode an FPR into the GPR field of LDAR/STLR/CAS).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block as TirBlock, BlockId, Constant, FieldDef, FuncId, FuncTy, Function as TirFunction,
    Global, Inst, InstrNode, Linkage, Module as TirModule, Ordering, StructDef, StructId,
    StructRepr, SwitchCase, Ty, ValueId,
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

/// Link `obj` against C `driver` (compiled at -O2), run, return the exit code.
/// `None` => not an aarch64-apple-darwin host (skip).
fn link_run(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
    if !aarch64_host() {
        eprintln!("SKIP {tag}: link-and-run requires aarch64-apple-darwin");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_p1p2"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).expect("write obj");
    fs::write(&drv_path, driver).expect("write driver");
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

fn add(dst: u32, lhs: u32, rhs: u32) -> InstrNode {
    InstrNode::new(Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::I64,
        lhs: ValueId::new(lhs),
        rhs: ValueId::new(rhs),
    })
    .with_result(ValueId::new(dst))
}

// ===========================================================================
// G7 — InsertField of a nested aggregate field into a NON-packed struct.
//      The nested value is pointer-represented, so lowering must copy its bytes
//      with memmove rather than store the value's address.
// ===========================================================================

const G7_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
struct I64x2 { int64_t f0, f1; };
struct Nest { struct I64x2 inner; int64_t tail; };
extern struct Nest g7_setinner(struct Nest, struct I64x2);
int main(void) {
    const struct {
        struct Nest before;
        struct I64x2 replacement;
    } cases[] = {
        {{{1, 2}, 3}, {100, 200}},
        {{{-1, -2}, -3}, {-100, 0x123456789LL}},
        {{{0, 0}, INT64_MAX}, {INT64_MIN, INT64_MAX}},
    };
    for (unsigned i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        struct Nest got = g7_setinner(cases[i].before, cases[i].replacement);
        if (got.inner.f0 != cases[i].replacement.f0 ||
            got.inner.f1 != cases[i].replacement.f1 ||
            got.tail != cases[i].before.tail) {
            printf("g7 #%u got={{%lld,%lld},%lld}\n", i,
                   (long long)got.inner.f0, (long long)got.inner.f1,
                   (long long)got.tail);
            return 1 + (int)i;
        }
    }
    return 0;
}
"#;

#[test]
fn g7_insertfield_aggregate_field_nonpacked_matches_clang() {
    let mut m = TirModule::new("g7");
    // Inner {i64,i64}; Nest { inner: {i64,i64}, tail: i64 } — repr C (NOT packed).
    m.structs.push(struct_def(0, "I64x2", &[Ty::I64, Ty::I64]));
    m.structs.push(struct_def(
        1,
        "Nest",
        &[Ty::Struct(StructId::new(0)), Ty::I64],
    ));
    let nest = Ty::Struct(StructId::new(1));
    let inner = Ty::Struct(StructId::new(0));

    // fn setinner(n: Nest, v: {i64,i64}) -> Nest { n.inner = v; n }
    let ft = m.add_func_type(FuncTy {
        params: vec![nest.clone(), inner.clone()],
        returns: vec![nest.clone()],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g7_setinner", ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), nest.clone()), (ValueId::new(1), inner)],
        body: vec![
            InstrNode::new(Inst::InsertField {
                ty: nest,
                aggregate: ValueId::new(0),
                field: 0, // the {i64,i64} aggregate field
                value: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);

    run_both_opts("g7", &m, G7_DRIVER);
}

// ===========================================================================
// G9 — no-backfill: f(a..g:i64, s:{i64,i64}, h:i64). clang (the caller) spills
//      s and h to the stack and leaves X7 UNUSED (NGRN=8); trust-cg (callee)
//      must read h from the stack, not backfill X7. Also exercises the G8
//      by-value stack-aggregate read (s).
// ===========================================================================

fn build_g9_callee(m: &mut TirModule) {
    m.structs.push(struct_def(0, "I64x2", &[Ty::I64, Ty::I64]));
    let s_ty = Ty::Struct(StructId::new(0));
    let mut params: Vec<Ty> = vec![Ty::I64; 7];
    params.push(s_ty.clone());
    params.push(Ty::I64);
    let ft = m.add_func_type(FuncTy {
        params,
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g9_sum", ft, BlockId::new(0));
    let mut block_params: Vec<(ValueId, Ty)> = (0..7).map(|i| (ValueId::new(i), Ty::I64)).collect();
    block_params.push((ValueId::new(7), s_ty.clone())); // s
    block_params.push((ValueId::new(8), Ty::I64)); // h
    let mut body = vec![
        InstrNode::new(Inst::ExtractField {
            ty: s_ty.clone(),
            aggregate: ValueId::new(7),
            field: 0,
        })
        .with_result(ValueId::new(10)),
        InstrNode::new(Inst::ExtractField {
            ty: s_ty,
            aggregate: ValueId::new(7),
            field: 1,
        })
        .with_result(ValueId::new(11)),
    ];
    // acc = v0 + v1 + ... + v6 + s.0 + s.1 + h
    let mut acc = 0u32;
    for (next, rhs) in (20u32..).zip([1u32, 2, 3, 4, 5, 6, 10, 11, 8]) {
        body.push(add(next, acc, rhs));
        acc = next;
    }
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(acc)],
    }));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: block_params,
        body,
    }];
    m.add_function(f);
}

const G9_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
struct I64x2 { int64_t f0, f1; };
extern int64_t g9_sum(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,
                      struct I64x2, int64_t);
int main(void){
    struct { int64_t a,b,c,d,e,f,g; struct I64x2 s; int64_t h; } T[] = {
        {1,2,3,4,5,6,7,{8,9},10},
        {-1,-2,-3,-4,-5,-6,-7,{-8,-9},-10},
        {100,200,300,400,500,600,700,{800,900},1000},
    };
    for(unsigned i=0;i<sizeof T/sizeof T[0];i++){
        int64_t ref = T[i].a+T[i].b+T[i].c+T[i].d+T[i].e+T[i].f+T[i].g
                    + T[i].s.f0+T[i].s.f1+T[i].h;
        int64_t got = g9_sum(T[i].a,T[i].b,T[i].c,T[i].d,T[i].e,T[i].f,T[i].g,T[i].s,T[i].h);
        if(got!=ref){printf("g9 #%u got=%lld ref=%lld\n",i,(long long)got,(long long)ref);return 1+i;}
    }
    printf("g9 no-backfill + by-value stack aggregate OK\n");
    return 0;
}
"#;

#[test]
fn g9_no_backfill_stack_aggregate_matches_clang() {
    let mut m = TirModule::new("g9");
    build_g9_callee(&mut m);
    run_both_opts("g9", &m, G9_DRIVER);
}

// ===========================================================================
// G8 — large (>16B) aggregate spilled INDIRECTLY on the stack, both directions:
//   callee g8_big_callee(a..h:i64, big:{i64,i64,i64}) — clang is the caller,
//   caller g8_big_caller(big) calls extern C g8_big_sink(a..h, big).
// Plus a by-value (<=16B) caller: g8_small_caller(s) calls g8_small_sink(...).
// ===========================================================================

fn build_g8_module() -> TirModule {
    let mut m = TirModule::new("g8");
    m.structs.push(struct_def(0, "I64x2", &[Ty::I64, Ty::I64]));
    m.structs
        .push(struct_def(1, "I64x3", &[Ty::I64, Ty::I64, Ty::I64]));
    let s2 = Ty::Struct(StructId::new(0));
    let s3 = Ty::Struct(StructId::new(1));

    // ---- callee: g8_big_callee(a..h:i64, big:{i64,i64,i64}) -> i64 ----
    let mut params: Vec<Ty> = vec![Ty::I64; 8];
    params.push(s3.clone());
    let ft = m.add_func_type(FuncTy {
        params,
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g8_big_callee", ft, BlockId::new(0));
    let mut bp: Vec<(ValueId, Ty)> = (0..8).map(|i| (ValueId::new(i), Ty::I64)).collect();
    bp.push((ValueId::new(8), s3.clone()));
    let mut body = vec![
        InstrNode::new(Inst::ExtractField {
            ty: s3.clone(),
            aggregate: ValueId::new(8),
            field: 0,
        })
        .with_result(ValueId::new(10)),
        InstrNode::new(Inst::ExtractField {
            ty: s3.clone(),
            aggregate: ValueId::new(8),
            field: 1,
        })
        .with_result(ValueId::new(11)),
        InstrNode::new(Inst::ExtractField {
            ty: s3.clone(),
            aggregate: ValueId::new(8),
            field: 2,
        })
        .with_result(ValueId::new(12)),
    ];
    let mut acc = 0u32;
    for (next, rhs) in (20u32..).zip([1u32, 2, 3, 4, 5, 6, 7, 10, 11, 12]) {
        body.push(add(next, acc, rhs));
        acc = next;
    }
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(acc)],
    }));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: bp,
        body,
    }];
    m.add_function(f);

    // ---- extern sinks (defined by clang) ----
    let big_sink_ft = m.add_func_type(FuncTy {
        params: {
            let mut p: Vec<Ty> = vec![Ty::I64; 8];
            p.push(s3.clone());
            p
        },
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut big_sink =
        TirFunction::new(FuncId::new(1), "g8_big_sink", big_sink_ft, BlockId::new(0));
    big_sink.blocks = vec![];
    big_sink.linkage = Linkage::External;
    m.add_function(big_sink);

    let small_sink_ft = m.add_func_type(FuncTy {
        params: {
            let mut p: Vec<Ty> = vec![Ty::I64; 7];
            p.push(s2.clone());
            p.push(Ty::I64);
            p
        },
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut small_sink = TirFunction::new(
        FuncId::new(2),
        "g8_small_sink",
        small_sink_ft,
        BlockId::new(0),
    );
    small_sink.blocks = vec![];
    small_sink.linkage = Linkage::External;
    m.add_function(small_sink);

    // ---- caller: g8_big_caller(big:{i64,i64,i64}) -> i64 {
    //          return g8_big_sink(1,2,3,4,5,6,7,8, big) } ----
    let big_caller_ft = m.add_func_type(FuncTy {
        params: vec![s3.clone()],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut big_caller = TirFunction::new(
        FuncId::new(3),
        "g8_big_caller",
        big_caller_ft,
        BlockId::new(0),
    );
    let mut cbody = Vec::new();
    for (v, k) in (1i128..=8).enumerate() {
        cbody.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k),
            })
            .with_result(ValueId::new(100 + v as u32)),
        );
    }
    cbody.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![
                ValueId::new(100),
                ValueId::new(101),
                ValueId::new(102),
                ValueId::new(103),
                ValueId::new(104),
                ValueId::new(105),
                ValueId::new(106),
                ValueId::new(107),
                ValueId::new(0), // big
            ],
        })
        .with_result(ValueId::new(200)),
    );
    cbody.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(200)],
    }));
    big_caller.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), s3.clone())],
        body: cbody,
    }];
    m.add_function(big_caller);

    // ---- caller: g8_small_caller(s:{i64,i64}) -> i64 {
    //          return g8_small_sink(1,2,3,4,5,6,7, s, 8) } ----
    let small_caller_ft = m.add_func_type(FuncTy {
        params: vec![s2.clone()],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut small_caller = TirFunction::new(
        FuncId::new(4),
        "g8_small_caller",
        small_caller_ft,
        BlockId::new(0),
    );
    let mut sbody = Vec::new();
    for (v, k) in (1i128..=7).enumerate() {
        sbody.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k),
            })
            .with_result(ValueId::new(100 + v as u32)),
        );
    }
    sbody.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(8),
        })
        .with_result(ValueId::new(120)),
    );
    sbody.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(2),
            args: vec![
                ValueId::new(100),
                ValueId::new(101),
                ValueId::new(102),
                ValueId::new(103),
                ValueId::new(104),
                ValueId::new(105),
                ValueId::new(106),
                ValueId::new(0),   // s
                ValueId::new(120), // h = 8
            ],
        })
        .with_result(ValueId::new(200)),
    );
    sbody.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(200)],
    }));
    small_caller.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), s2.clone())],
        body: sbody,
    }];
    m.add_function(small_caller);

    m
}

const G8_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
struct I64x2 { int64_t f0, f1; };
struct I64x3 { int64_t f0, f1, f2; };
extern int64_t g8_big_callee(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,
                             int64_t,int64_t, struct I64x3);
extern int64_t g8_big_caller(struct I64x3);
extern int64_t g8_small_caller(struct I64x2);
// Sinks that clang defines and trust-cg calls.
int64_t g8_big_sink(int64_t a,int64_t b,int64_t c,int64_t d,int64_t e,int64_t f,
                    int64_t g,int64_t h, struct I64x3 big){
    return a+b+c+d+e+f+g+h + big.f0+big.f1+big.f2;
}
int64_t g8_small_sink(int64_t a,int64_t b,int64_t c,int64_t d,int64_t e,int64_t f,
                      int64_t g, struct I64x2 s, int64_t h){
    return a+b+c+d+e+f+g + s.f0+s.f1 + h;
}
int main(void){
    // callee direction: clang calls trust-cg with a >16B struct spilled indirectly.
    struct I64x3 bs[] = {{9,10,11},{-1,-2,-3},{100,200,300}};
    for(unsigned i=0;i<sizeof bs/sizeof bs[0];i++){
        int64_t ref = 1+2+3+4+5+6+7+8 + bs[i].f0+bs[i].f1+bs[i].f2;
        if(g8_big_callee(1,2,3,4,5,6,7,8, bs[i]) != ref){printf("g8_big_callee #%u\n",i);return 1+i;}
    }
    // caller direction, >16B: trust-cg calls g8_big_sink.
    struct I64x3 bc = {30,40,50};
    if(g8_big_caller(bc) != 1+2+3+4+5+6+7+8 + 30+40+50){printf("g8_big_caller\n");return 20;}
    // caller direction, <=16B by-value on stack: trust-cg calls g8_small_sink.
    struct I64x2 sc = {70,80};
    if(g8_small_caller(sc) != 1+2+3+4+5+6+7 + 70+80 + 8){printf("g8_small_caller\n");return 21;}
    printf("g8 stack aggregate (by-value + indirect, both directions) OK\n");
    return 0;
}
"#;

#[test]
fn g8_stack_aggregate_matches_clang() {
    let m = build_g8_module();
    run_both_opts("g8", &m, G8_DRIVER);
}

// ===========================================================================
// G10 — imported/external DATA global via GOT-indirect (ExternRef). trust-cg and
//      clang share an imported symbol `g10_shared` (defined in the C driver).
// ===========================================================================

fn build_g10_module() -> TirModule {
    let mut m = TirModule::new("g10");
    // Imported: no initializer, External linkage -> a cross-object DATA import.
    m.globals.push(Global {
        name: "g10_shared".to_string(),
        ty: Ty::I64,
        mutable: true,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
    });
    let g = GlobalId::new(0);

    // void g10_bump(void) { g10_shared += 1; }
    let bump_ft = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut bump = TirFunction::new(FuncId::new(0), "g10_bump", bump_ft, BlockId::new(0));
    bump.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::GlobalAddr { global: g }).with_result(ValueId::new(0)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                value: ValueId::new(3),
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    m.add_function(bump);

    // int64_t g10_read(void) { return g10_shared; }
    let read_ft = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut read = TirFunction::new(FuncId::new(1), "g10_read", read_ft, BlockId::new(0));
    read.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::GlobalAddr { global: g }).with_result(ValueId::new(0)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    m.add_function(read);
    m
}

const G10_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
int64_t g10_shared = 41;          /* DEFINED here; imported by trust-cg */
extern void    g10_bump(void);
extern int64_t g10_read(void);
int main(void){
    if(g10_read() != 41){printf("g10_read initial\n");return 1;}
    g10_bump();
    if(g10_shared != 42){printf("g10_shared=%lld\n",(long long)g10_shared);return 2;}
    if(g10_read() != 42){printf("g10_read after bump\n");return 3;}
    printf("g10 imported data global (GOT-indirect) OK\n");
    return 0;
}
"#;

#[test]
fn g10_imported_data_global_matches_clang() {
    let m = build_g10_module();
    run_both_opts("g10", &m, G10_DRIVER);
}

// ===========================================================================
// G11 — libc memcpy whose RETURN value (dest) is used.
// ===========================================================================

fn build_g11_module() -> TirModule {
    let mut m = TirModule::new("g11");
    let ptr = Ty::PtrMut(Box::new(Ty::I8));

    // extern void* memcpy(void*, void*, i64)  (recognised by name).
    let mc_ft = m.add_func_type(FuncTy {
        params: vec![ptr.clone(), ptr.clone(), Ty::I64],
        returns: vec![ptr.clone()],
        is_vararg: false,
    });
    let mut memcpy = TirFunction::new(FuncId::new(0), "memcpy", mc_ft, BlockId::new(0));
    memcpy.blocks = vec![];
    memcpy.linkage = Linkage::External;
    m.add_function(memcpy);

    // void* g11(void* dst, void* src, i64 n) { return memcpy(dst, src, n); }
    let g11_ft = m.add_func_type(FuncTy {
        params: vec![ptr.clone(), ptr.clone(), Ty::I64],
        returns: vec![ptr.clone()],
        is_vararg: false,
    });
    let mut g11 = TirFunction::new(FuncId::new(1), "g11", g11_ft, BlockId::new(0));
    g11.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), ptr.clone()),
            (ValueId::new(1), ptr.clone()),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0), ValueId::new(1), ValueId::new(2)],
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(g11);
    m
}

const G11_DRIVER: &str = r#"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
extern void* g11(void* dst, void* src, int64_t n);
int main(void){
    char src[] = "hello, world";
    char dst[16] = {0};
    void* r = g11(dst, src, 13);
    if(r != dst){printf("g11 returned %p want %p\n", r, (void*)dst);return 1;}
    if(memcmp(dst, src, 13) != 0){printf("g11 bytes mismatch\n");return 2;}
    printf("g11 memcpy return-value OK\n");
    return 0;
}
"#;

#[test]
fn g11_memcpy_return_value_matches_clang() {
    let m = build_g11_module();
    run_both_opts("g11", &m, G11_DRIVER);
}

// ===========================================================================
// G13 — narrow i8 switch selector with dirty upper bits. The selector is the
//      result of an i8 multiply (`20*20 = 400`, low byte 0x90 = 144); the 32-bit
//      W register holds 0x190. The switch must dispatch on the LOGICAL i8 value
//      (144), not the dirty W register.
// ===========================================================================

fn ret_i32_block(id: u32, nv: ValueId, val: i64) -> TirBlock {
    TirBlock {
        id: BlockId::new(id),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(val as i128),
            })
            .with_result(nv),
            InstrNode::new(Inst::Return { values: vec![nv] }),
        ],
    }
}

fn build_g13_module() -> TirModule {
    let mut m = TirModule::new("g13");
    // fn g13(a: u8, b: u8) -> i32 { let s = (a*b) as u8; match s { ... } }
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::U8, Ty::U8],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g13", ft, BlockId::new(0));
    // cases: 50 -> 200, 144 -> 100, 200 -> 300 ; default 999.
    let cases = [(50i64, 200i64), (144, 100), (200, 300)];
    let switch_cases: Vec<SwitchCase> = cases
        .iter()
        .enumerate()
        .map(|(i, (v, _))| SwitchCase {
            value: Constant::Int(*v as i128),
            target: BlockId::new(i as u32 + 1),
            args: vec![],
        })
        .collect();
    let default_block = BlockId::new(cases.len() as u32 + 1);
    let mut blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::U8), (ValueId::new(1), Ty::U8)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::U8,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Switch {
                value: ValueId::new(2),
                default: default_block,
                default_args: vec![],
                cases: switch_cases,
                exhaustive_enum_unreachable: false,
            }),
        ],
    }];
    let mut vid = 10u32;
    for (i, (_, out)) in cases.iter().enumerate() {
        blocks.push(ret_i32_block(i as u32 + 1, ValueId::new(vid), *out));
        vid += 1;
    }
    blocks.push(ret_i32_block(
        cases.len() as u32 + 1,
        ValueId::new(vid),
        999,
    ));
    f.blocks = blocks;
    m.add_function(f);
    m
}

const G13_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
extern int g13(uint8_t a, uint8_t b);
static int oracle(uint8_t s){
    switch(s){ case 50: return 200; case 144: return 100; case 200: return 300; default: return 999; }
}
int main(void){
    // (a,b) pairs whose u8 product hits each case (incl. the dirty-upper 20*20=400 -> 144).
    uint8_t A[] = {20, 10, 25,  16, 3, 17,  200, 1};
    uint8_t B[] = {20,  5, 10,  25, 3, 15,    1, 1};
    for(unsigned i=0;i<sizeof A/sizeof A[0];i++){
        uint8_t prod = (uint8_t)(A[i]*B[i]);
        int ref = oracle(prod);
        int got = g13(A[i], B[i]);
        if(got != ref){printf("g13(%u,%u) prod=%u got=%d ref=%d\n",A[i],B[i],prod,got,ref);return 1+i;}
    }
    printf("g13 narrow switch selector OK\n");
    return 0;
}
"#;

#[test]
fn g13_narrow_switch_selector_matches_clang() {
    let m = build_g13_module();
    run_both_opts("g13", &m, G13_DRIVER);
}

// ===========================================================================
// G14-G16 — scalar float atomics must FAIL CLOSED (LDAR/STLR/CAS have no FP
//      form; an FPR-classed value would be encoded into the GPR field).
// ===========================================================================

fn f32_ptr() -> Ty {
    Ty::PtrMut(Box::new(Ty::F32))
}

// Helper: assert compile fails closed with a message about the integer-only
// atomic guard.
fn expect_float_atomic_failclose(m: &TirModule, tag: &str) {
    for opt in [OptLevel::O0, OptLevel::O2] {
        let err = compile_obj(m, opt)
            .err()
            .unwrap_or_else(|| panic!("{tag} at {opt:?} must fail closed on a float atomic"));
        assert!(
            err.contains("integer memory widths") || err.contains("register file"),
            "unexpected {tag} error at {opt:?}: {err}"
        );
    }
}

#[test]
fn g14_float_atomic_load_fails_closed() {
    let mut m = TirModule::new("g14");
    let ft = m.add_func_type(FuncTy {
        params: vec![f32_ptr()],
        returns: vec![Ty::F32],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g14_aload_f32", ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), f32_ptr())],
        body: vec![
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::F32,
                ptr: ValueId::new(0),
                ordering: Ordering::SeqCst,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    m.add_function(f);
    expect_float_atomic_failclose(&m, "g14_float_atomic_load");
}

#[test]
fn g15_float_atomic_store_fails_closed() {
    let mut m = TirModule::new("g15");
    let ft = m.add_func_type(FuncTy {
        params: vec![f32_ptr(), Ty::F32],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g15_astore_f32", ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), f32_ptr()), (ValueId::new(1), Ty::F32)],
        body: vec![
            InstrNode::new(Inst::AtomicStore {
                ty: Ty::F32,
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                ordering: Ordering::SeqCst,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    m.add_function(f);
    expect_float_atomic_failclose(&m, "g15_float_atomic_store");
}

#[test]
fn g16_float_cmpxchg_fails_closed() {
    let mut m = TirModule::new("g16");
    let ft = m.add_func_type(FuncTy {
        params: vec![f32_ptr(), Ty::F32, Ty::F32],
        returns: vec![Ty::F32],
        is_vararg: false,
    });
    let mut f = TirFunction::new(FuncId::new(0), "g16_cas_f32", ft, BlockId::new(0));
    f.blocks = vec![TirBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), f32_ptr()),
            (ValueId::new(1), Ty::F32),
            (ValueId::new(2), Ty::F32),
        ],
        body: vec![
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::F32,
                ptr: ValueId::new(0),
                expected: ValueId::new(1),
                desired: ValueId::new(2),
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
            })
            .with_results(vec![ValueId::new(3), ValueId::new(4)]),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(f);
    expect_float_atomic_failclose(&m, "g16_float_cmpxchg");
}
