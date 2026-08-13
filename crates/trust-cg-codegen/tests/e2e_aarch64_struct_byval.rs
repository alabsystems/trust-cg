// trust-cg-codegen/tests/e2e_aarch64_struct_byval.rs
//
// Probe/coverage for by-value aggregate ARGUMENTS and RETURNS on aarch64. A
// small struct (<= 16 bytes, no FP fields) is passed in consecutive GPRs
// (AAPCS64: {i64,i64} in X0:X1) and returned the same way; a 3-GPR struct
// {i64,i64,i64} (24 bytes, > 16) is passed INDIRECTLY (caller allocates, passes
// a pointer) and returned via the x8 indirect-result register.
//
// The classify_params ABI machinery (HFA / small-in-registers / large-indirect)
// and the ISel RegPair / RegSequence / Indirect argument handling are shared
// with x86_64; this pins that they produce the correct AAPCS64 layout on real
// Apple Silicon by diffing against clang, which uses the same struct types.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, CastOp, FieldDef, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, StructDef, StructId, StructRepr, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
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
        // Match the C driver's struct ABI classification.
        repr: StructRepr::C,
    }
}

// `fn sum_n(s: {i64 * n}) -> i64 { s.0 + s.1 + ... }`
fn build_sum(m: &mut TrustIrModule, id: u32, name: &str, n: u32) {
    let agg = Ty::Struct(StructId::new(id));
    let ft = m.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    let mut body = Vec::new();
    // extract field 0..n
    for field in 0..n {
        body.push(
            InstrNode::new(Inst::ExtractField {
                ty: agg.clone(),
                aggregate: ValueId::new(0),
                field,
            })
            .with_result(ValueId::new(10 + field)),
        );
    }
    // sum them
    let mut acc = ValueId::new(10);
    for (next, field) in (100u32..).zip(1..n) {
        let out = ValueId::new(next);
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: acc,
                rhs: ValueId::new(10 + field),
            })
            .with_result(out),
        );
        acc = out;
    }
    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg)],
        body,
    }];
    m.add_function(f);
}

// `fn hfa2(s: {f64,f64}) -> f64 { s.0 + s.1 }` — a homogeneous FP aggregate,
// passed in consecutive D registers (D0:D1) per AAPCS64.
fn build_hfa(m: &mut TrustIrModule, id: u32, name: &str) {
    let agg = Ty::Struct(StructId::new(id));
    let ft = m.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
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
                ty: agg,
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(f);
}

// `fn mixed(s: {i64,f64}) -> f64 { (f64)s.0 + s.1 }` — a MIXED int/FP struct
// (16 bytes, NOT an HFA), passed in GPRs with the f64 field's bits in a GPR.
fn build_mixed(m: &mut TrustIrModule, id: u32, name: &str) {
    let agg = Ty::Struct(StructId::new(id));
    let ft = m.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
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
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractField {
                ty: agg,
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("struct_byval");
    // Register struct types (ids must match the FuncId/StructId used above).
    m.structs.push(struct_def(0, "I64x2", &[Ty::I64, Ty::I64]));
    m.structs
        .push(struct_def(1, "I64x3", &[Ty::I64, Ty::I64, Ty::I64]));
    m.structs.push(struct_def(2, "F64x2", &[Ty::F64, Ty::F64]));
    m.structs.push(struct_def(5, "Mixed", &[Ty::I64, Ty::F64]));
    // Nested: Nest { inner: {i64,i64}, tail: i64 } (24 bytes -> indirect).
    m.structs.push(struct_def(
        6,
        "Nest",
        &[Ty::Struct(StructId::new(0)), Ty::I64],
    ));
    // Packed { i8, i64 } (repr packed(1)): i64 at UNALIGNED offset 1.
    m.structs.push(StructDef {
        id: StructId::new(7),
        name: "Packed".to_string(),
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
    // PNest { i8, {i64,i64} } packed: the inner struct sits at packed offset 1.
    m.structs.push(StructDef {
        id: StructId::new(8),
        name: "PNest".to_string(),
        fields: vec![
            FieldDef {
                name: "f0".to_string(),
                ty: Ty::I8,
                offset: None,
            },
            FieldDef {
                name: "f1".to_string(),
                ty: Ty::Struct(StructId::new(0)),
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::Packed(1),
    });
    build_sum(&mut m, 0, "sum2", 2); // 16 bytes -> X0:X1 register pair
    build_sum(&mut m, 1, "sum3", 3); // 24 bytes -> indirect (pointer arg)
    build_hfa(&mut m, 2, "hfa2"); // HFA -> D0:D1
    build_mixed(&mut m, 5, "mixed"); // {i64,f64} mixed -> GPR pair (not HFA)

    // `fn nest(s: Nest) -> i64 { s.inner.0 + s.inner.1 + s.tail }` — extracts a
    // NESTED aggregate field (s.inner) then its scalar fields.
    let nest_ty = Ty::Struct(StructId::new(6));
    let inner_ty = Ty::Struct(StructId::new(0));
    let nest_ft = m.add_func_type(FuncTy {
        params: vec![nest_ty.clone()],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut nf = TrustIrFunction::new(FuncId::new(6), "nest", nest_ft, BlockId::new(0));
    nf.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), nest_ty.clone())],
        body: vec![
            InstrNode::new(Inst::ExtractField {
                ty: nest_ty.clone(),
                aggregate: ValueId::new(0),
                field: 0,
            })
            .with_result(ValueId::new(1)), // inner (aggregate field -> address)
            InstrNode::new(Inst::ExtractField {
                ty: nest_ty,
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(2)), // tail
            InstrNode::new(Inst::ExtractField {
                ty: inner_ty.clone(),
                aggregate: ValueId::new(1),
                field: 0,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::ExtractField {
                ty: inner_ty,
                aggregate: ValueId::new(1),
                field: 1,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(5),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(6)],
            }),
        ],
    }];
    m.add_function(nf);

    // `fn id2(s: {i64,i64}) -> {i64,i64} { s }` — struct RETURN (in + out X0:X1).
    let agg = Ty::Struct(StructId::new(0));
    let ft = m.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![agg.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(3), "id2", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    m.add_function(f);

    // `fn id3(s: {i64,i64,i64}) -> {i64,i64,i64} { s }` — 24-byte struct RETURN,
    // which is > 16 bytes so it uses the sret/x8 indirect-result convention.
    let agg3 = Ty::Struct(StructId::new(1));
    let ft3 = m.add_func_type(FuncTy {
        params: vec![agg3.clone()],
        returns: vec![agg3.clone()],
        is_vararg: false,
    });
    let mut f3 = TrustIrFunction::new(FuncId::new(4), "id3", ft3, BlockId::new(0));
    f3.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg3)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    m.add_function(f3);

    // `fn packed(s: Packed) -> i64 { (i64)(sext s.f0) + s.f1 }` — s.f1 is an i64
    // at the UNALIGNED packed offset 1.
    let pk_ty = Ty::Struct(StructId::new(7));
    let pk_ft = m.add_func_type(FuncTy {
        params: vec![pk_ty.clone()],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut pf = TrustIrFunction::new(FuncId::new(7), "packed", pk_ft, BlockId::new(0));
    pf.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), pk_ty.clone())],
        body: vec![
            InstrNode::new(Inst::ExtractField {
                ty: pk_ty.clone(),
                aggregate: ValueId::new(0),
                field: 0,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I64,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractField {
                ty: pk_ty,
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.add_function(pf);

    // `fn pset(s: Packed, v: i64) -> i64 { s.f1 = v; return s.f1 }` — round-trips
    // a WRITE (InsertField) and a READ (ExtractField) at packed offset 1.
    let ps_ty = Ty::Struct(StructId::new(7));
    let ps_ft = m.add_func_type(FuncTy {
        params: vec![ps_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut psf = TrustIrFunction::new(FuncId::new(8), "pset", ps_ft, BlockId::new(0));
    psf.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ps_ty.clone()), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::InsertField {
                ty: ps_ty.clone(),
                aggregate: ValueId::new(0),
                field: 1,
                value: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractField {
                ty: ps_ty,
                aggregate: ValueId::new(2),
                field: 1,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(psf);

    // `fn pnest(s: PNest) -> i64 { (i64)(sext s.f0) + s.f1.0 + s.f1.1 }` —
    // extracts a NESTED aggregate field (s.f1) from a PACKED struct, then its
    // scalar fields (at unaligned absolute addresses).
    let pn_ty = Ty::Struct(StructId::new(8));
    let inner_ty = Ty::Struct(StructId::new(0));
    let pn_ft = m.add_func_type(FuncTy {
        params: vec![pn_ty.clone()],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut pnf = TrustIrFunction::new(FuncId::new(9), "pnest", pn_ft, BlockId::new(0));
    pnf.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), pn_ty.clone())],
        body: vec![
            InstrNode::new(Inst::ExtractField {
                ty: pn_ty.clone(),
                aggregate: ValueId::new(0),
                field: 0,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I64,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractField {
                ty: pn_ty,
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(3)), // inner (aggregate field at packed offset 1)
            InstrNode::new(Inst::ExtractField {
                ty: inner_ty.clone(),
                aggregate: ValueId::new(3),
                field: 0,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::ExtractField {
                ty: inner_ty,
                aggregate: ValueId::new(3),
                field: 1,
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(6),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            }),
        ],
    }];
    m.add_function(pnf);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("struct-by-value module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
struct I64x2 { int64_t f0, f1; };
struct I64x3 { int64_t f0, f1, f2; };
struct F64x2 { double f0, f1; };
struct Mixed { int64_t f0; double f1; };
struct Nest { struct I64x2 inner; int64_t tail; };
extern int64_t sum2(struct I64x2);
extern int64_t sum3(struct I64x3);
extern double hfa2(struct F64x2);
extern double mixed(struct Mixed);
extern int64_t nest(struct Nest);
struct __attribute__((packed)) Packed { int8_t f0; int64_t f1; };
extern int64_t packed(struct Packed);
extern int64_t pset(struct Packed, int64_t);
struct __attribute__((packed)) PNest { int8_t f0; struct I64x2 f1; };
extern int64_t pnest(struct PNest);
extern struct I64x2 id2(struct I64x2);
extern struct I64x3 id3(struct I64x3);
int main(void){
    struct Packed pk[] = {{5,1000},{-7,-2000},{100,0x1122334455667788LL},{-1,-1},{0,0}};
    for(unsigned i=0;i<sizeof(pk)/sizeof(pk[0]);i++){
        int64_t got=packed(pk[i]), ref=(int64_t)pk[i].f0+pk[i].f1;
        if(got!=ref){printf("packed #%u got=%lld ref=%lld\n",i,(long long)got,(long long)ref);return 8;}
        int64_t nv=0x0102030405060708LL ^ (int64_t)i;
        if(pset(pk[i],nv)!=nv){printf("pset #%u\n",i);return 9;}
    }
    struct PNest pn[] = {{5,{10,20}},{-7,{-100,200}},{1,{0x1122334455667788LL,-1}}};
    for(unsigned i=0;i<sizeof(pn)/sizeof(pn[0]);i++){
        int64_t got=pnest(pn[i]), ref=(int64_t)pn[i].f0+pn[i].f1.f0+pn[i].f1.f1;
        if(got!=ref){printf("pnest #%u got=%lld ref=%lld\n",i,(long long)got,(long long)ref);return 10;}
    }
    struct Mixed mx[] = {{3,2.5},{-7,100.25},{1000000,-0.5},{0,42.0}};
    for(unsigned i=0;i<sizeof(mx)/sizeof(mx[0]);i++){
        double got=mixed(mx[i]), ref=(double)mx[i].f0+mx[i].f1;
        if(got!=ref){printf("mixed #%u got=%g ref=%g\n",i,got,ref);return 6;}
    }
    struct Nest ns[] = {{{1,2},3},{{-5,7},-9},{{0x1122334455667788LL,-1},42},{{100,-100},0}};
    for(unsigned i=0;i<sizeof(ns)/sizeof(ns[0]);i++){
        int64_t got=nest(ns[i]), ref=ns[i].inner.f0+ns[i].inner.f1+ns[i].tail;
        if(got!=ref){printf("nest #%u got=%lld ref=%lld\n",i,(long long)got,(long long)ref);return 7;}
    }
    struct F64x2 h[] = {{1.5,2.5},{-3.25,7.75},{100.0,0.0625},{-1.0,-2.0}};
    for(unsigned i=0;i<sizeof(h)/sizeof(h[0]);i++){
        double got=hfa2(h[i]), ref=h[i].f0+h[i].f1;
        if(got!=ref){printf("hfa2 #%u got=%g ref=%g\n",i,got,ref);return 3;}
    }
    struct I64x2 r[] = {{1,2},{-5,7},{0x1122334455667788LL,-1}};
    for(unsigned i=0;i<sizeof(r)/sizeof(r[0]);i++){
        struct I64x2 got=id2(r[i]);
        if(got.f0!=r[i].f0 || got.f1!=r[i].f1){printf("id2 #%u\n",i);return 4;}
    }
    struct I64x3 r3[] = {{1,2,3},{-5,7,-9},{0x1122334455667788LL,-1,42}};
    for(unsigned i=0;i<sizeof(r3)/sizeof(r3[0]);i++){
        struct I64x3 got=id3(r3[i]);
        if(got.f0!=r3[i].f0 || got.f1!=r3[i].f1 || got.f2!=r3[i].f2){printf("id3 #%u\n",i);return 5;}
    }
    struct I64x2 a2[] = {{1,2},{-5,7},{0x1122334455667788LL,-1},{100,-100}};
    for(unsigned i=0;i<sizeof(a2)/sizeof(a2[0]);i++){
        int64_t got=sum2(a2[i]), ref=a2[i].f0+a2[i].f1;
        if(got!=ref){printf("sum2 #%u got=%lld ref=%lld\n",i,(long long)got,(long long)ref);return 1;}
    }
    struct I64x3 a3[] = {{1,2,3},{-5,7,-9},{0x1122334455667788LL,-1,42},{100,-100,0}};
    for(unsigned i=0;i<sizeof(a3)/sizeof(a3[0]);i++){
        int64_t got=sum3(a3[i]), ref=a3[i].f0+a3[i].f1+a3[i].f2;
        if(got!=ref){printf("sum3 #%u got=%lld ref=%lld\n",i,(long long)got,(long long)ref);return 2;}
    }
    printf("by-value struct args (16B register-pair + 24B indirect) bit-exact vs clang\n");
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
fn e2e_aarch64_struct_byval_args() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("struct_byval", &obj) else {
            return;
        };
        assert_eq!(code, 0, "struct-byval arg mismatch at {opt:?}");
    }
}
