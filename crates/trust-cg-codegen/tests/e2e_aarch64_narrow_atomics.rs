// trust-cg-codegen/tests/e2e_aarch64_narrow_atomics.rs
//
// Completeness: i8/i16 atomic read-modify-write and compare-exchange, previously
// fail-closed ("narrow AtomicRmw needs byte/half LSE opcodes or a proven LL/SC
// CAS loop"). AArch64 LSE has byte/half variants of every atomic (LDADDB/LDADDH,
// CASB/CASH, ...) that differ from the word/dword form ONLY in the 2-bit `size`
// field. Since i8/i16/i32 all use W registers, the register class can't tell the
// encoder which size to emit, so the ISel appends an explicit access-size
// immediate (0 = byte, 1 = half) as the atomic's 4th operand and the encoder
// reads it for the `size` field.
//
// Verified value-correct against C11 <stdatomic.h> on real Apple Silicon at O0
// and O2, over an i8 and i16 value matrix. Single-threaded suffices to catch the
// value/width bug (a word-width atomic on a byte would touch adjacent bytes and
// compute the wrong result).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_ir::{
    AtomicRMWOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ordering, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn build_rmw(id: u32, name: &str, m: &mut TrustIrModule, op: AtomicRMWOp, ty: Ty) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::PtrMut(Box::new(ty.clone())), ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(ty.clone()))),
            (ValueId::new(1), ty.clone()),
        ],
        body: vec![
            InstrNode::new(Inst::AtomicRMW {
                op,
                ty: ty.clone(),
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                ordering: Ordering::SeqCst,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
}

// `cas_old(p, expected, desired) -> ty` returning the loaded value.
fn build_cas(id: u32, name: &str, m: &mut TrustIrModule, ty: Ty) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::PtrMut(Box::new(ty.clone())), ty.clone(), ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(ty.clone()))),
            (ValueId::new(1), ty.clone()),
            (ValueId::new(2), ty.clone()),
        ],
        body: vec![
            InstrNode::new(Inst::CmpXchg {
                ty: ty.clone(),
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
}

fn build_module() -> TrustIrModule {
    use AtomicRMWOp::*;
    let mut m = TrustIrModule::new("narrow_atomics");
    let ops = [
        (Add, "add"),
        (Sub, "sub"),
        (And, "and"),
        (Or, "or"),
        (Xor, "xor"),
        (Xchg, "xchg"),
        (Max, "smax"),
        (Min, "smin"),
        (UMax, "umax"),
        (UMin, "umin"),
    ];
    let mut id = 0u32;
    for (op, n) in ops {
        build_rmw(id, &format!("{n}_i8"), &mut m, op, Ty::I8);
        id += 1;
        build_rmw(id, &format!("{n}_i16"), &mut m, op, Ty::I16);
        id += 1;
    }
    build_cas(id, "cas8", &mut m, Ty::I8);
    id += 1;
    build_cas(id, "cas16", &mut m, Ty::I16);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("narrow atomics module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#define R8(op) extern int8_t op##_i8(int8_t*,int8_t);
#define R16(op) extern int16_t op##_i16(int16_t*,int16_t);
R8(add)R8(sub)R8(and)R8(or)R8(xor)R8(xchg)R8(smax)R8(smin)R8(umax)R8(umin)
R16(add)R16(sub)R16(and)R16(or)R16(xor)R16(xchg)R16(smax)R16(smin)R16(umax)R16(umin)
extern int8_t cas8(int8_t*,int8_t,int8_t);
extern int16_t cas16(int16_t*,int16_t,int16_t);
int main(void){
    int8_t V8[]={0,5,-5,127,-128,-1,0x33,100};
    for(unsigned i=0;i<8;i++)for(unsigned j=0;j<8;j++){
        int8_t a=V8[i],b=V8[j],m,old;
        #define K8(op,expr) m=a; old=op##_i8(&m,b); if(old!=a){printf(#op"_i8 old\n");return 1;}{int8_t w=(int8_t)(expr); if(m!=w){printf(#op"_i8 got=%d want=%d\n",m,w);return 2;}}
        K8(add,a+b)K8(sub,a-b)K8(and,a&b)K8(or,a|b)K8(xor,a^b)K8(xchg,b)
        K8(smax,a>b?a:b)K8(smin,a<b?a:b)
        K8(umax,(uint8_t)a>(uint8_t)b?a:b)K8(umin,(uint8_t)a<(uint8_t)b?a:b)
        m=a; int8_t o=cas8(&m,a,b); if(o!=a||m!=b){printf("cas8 match\n");return 3;}
        m=a; cas8(&m,(int8_t)(a+1),b); if(m!=a){printf("cas8 mism\n");return 4;}
    }
    int16_t V16[]={0,500,-500,32767,-32768,-1,0x3333,1000};
    for(unsigned i=0;i<8;i++)for(unsigned j=0;j<8;j++){
        int16_t a=V16[i],b=V16[j],m,old;
        #define K16(op,expr) m=a; old=op##_i16(&m,b); if(old!=a){printf(#op"_i16 old\n");return 5;}{int16_t w=(int16_t)(expr); if(m!=w){printf(#op"_i16 got=%d want=%d\n",m,w);return 6;}}
        K16(add,a+b)K16(sub,a-b)K16(and,a&b)K16(or,a|b)K16(xor,a^b)K16(xchg,b)
        K16(smax,a>b?a:b)K16(smin,a<b?a:b)
        K16(umax,(uint16_t)a>(uint16_t)b?a:b)K16(umin,(uint16_t)a<(uint16_t)b?a:b)
        m=a; int16_t o=cas16(&m,a,b); if(o!=a||m!=b){printf("cas16 match\n");return 7;}
        m=a; cas16(&m,(int16_t)(a+1),b); if(m!=a){printf("cas16 mism\n");return 8;}
    }
    printf("narrow (i8/i16) atomicrmw (10 ops) + cmpxchg value-correct vs C11\n");
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
            "-O2",
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
fn e2e_aarch64_narrow_atomics() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("narrow_atomics", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "narrow atomic mismatch at {opt:?} (failing code {code})"
        );
    }
}
