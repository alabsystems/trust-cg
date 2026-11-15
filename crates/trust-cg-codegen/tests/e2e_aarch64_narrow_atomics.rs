// trust-cg-codegen/tests/e2e_aarch64_narrow_atomics.rs
//
// Completeness: i8/i16 (plus the i32 word width) atomic read-modify-write and
// compare-exchange. The narrow forms were previously fail-closed ("narrow
// AtomicRmw needs byte/half LSE opcodes or a proven LL/SC CAS loop"). AArch64 LSE has byte/half variants of every atomic (LDADDB/LDADDH,
// CASB/CASH, ...) that differ from the word/dword form ONLY in the 2-bit `size`
// field. Since i8/i16/i32 all use W registers, the register class can't tell the
// encoder which size to emit, so the ISel appends an explicit access-size
// immediate (0 = byte, 1 = half) as the atomic's 4th operand and the encoder
// reads it for the `size` field.
//
// Verified value-correct against C11 <stdatomic.h> at O0 and O2 on AArch64
// macOS (Darwin AOT and explicit-LSE pipeline lanes) and Linux GNU (explicit
// LSE), over i8, i16 and i32 value matrices. Single-threaded suffices to catch
// the value/width bug (a word-width atomic on a byte would touch adjacent bytes
// and compute the wrong result).
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
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};

#[path = "common/native_host.rs"]
mod native_host;

/// AArch64 Linux GNU (ELF) or macOS (Mach-O) can link and run the objects.
fn can_link_and_run_aarch64_native() -> bool {
    native_host::NATIVE
}

/// The optional ISA feature this family needs. Darwin's AOT target contract
/// admits it, so the production `Compiler` lane runs there; generic Linux AOT
/// has no LSE and lowers the family through LL/SC loops instead (pinned
/// below; executed by `e2e_aarch64_llsc_atomics`), so every native host also
/// runs the explicit-profile pipeline lane, which is the only LSE lane on
/// Linux GNU. A host CPU without LSE is a failure, never a skip.
const PROFILE: AArch64IsaProfile = AArch64IsaProfile::LSE;

fn objects_at(module: &TrustIrModule, opt: OptLevel) -> Vec<(&'static str, Vec<u8>)> {
    let mut objects = Vec::new();
    if !native_host::LINUX_GNU {
        objects.push(("darwin-aot", compile_at(module, opt)));
    }
    if native_host::NATIVE {
        assert!(
            PROFILE.is_supported_by_host(),
            "the explicit LSE native lane requires host LSE"
        );
        let object = native_host::compile_with_isa_profile(module, opt, PROFILE)
            .unwrap_or_else(|error| panic!("explicit LSE {opt:?}: {error}"));
        objects.push(("explicit-lse", object));
    }
    objects
}

/// Generic Linux AOT has no LSE capability, so it never emits an LSE word
/// for this family: every SeqCst atomic lowers to one LL/SC retry loop (one
/// LDAXR{B,H} and one STLXR{B,H}, natively executed by
/// `e2e_aarch64_llsc_atomics`). Only the explicit profile admits LSE.
/// Object-level, so it runs on every host.
#[test]
fn generic_linux_aot_lowers_lse_family_through_llsc_without_lse_words() {
    let object = Compiler::new_for_target_spec(
        CompilerConfig::default(),
        TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&build_module())
    .unwrap_or_else(|error| panic!("generic Linux AOT must lower through LL/SC: {error}"))
    .object_code;
    let words = native_host::text_words(&object);
    // CAS/CASA/CASL/CASAL{B,H} and the LDADD/LDCLR/LDEOR/LDSET/LD{S,U}{MAX,MIN}/SWP
    // atomic memory operations, at every size and ordering.
    let lse: Vec<_> = words
        .iter()
        .filter(|word| **word & 0x3fa0_7c00 == 0x08a0_7c00 || **word & 0x3f20_0c00 == 0x3820_0000)
        .collect();
    assert!(
        lse.is_empty(),
        "generic Linux AOT emitted LSE words {lse:08x?}"
    );
    // Single-register load/store exclusives: bit 22 is L, bit 15 is o0
    // (acquire for a load, release for a store), bits 31:30 the size.
    let exclusives: Vec<u32> = words
        .iter()
        .copied()
        .filter(|word| word & 0x3fa0_7c00 == 0x0800_7c00)
        .collect();
    assert!(
        exclusives.iter().all(|word| (word >> 15) & 1 == 1),
        "SeqCst LL/SC loops use LDAXR/STLXR: {exclusives:08x?}"
    );
    for (size, expected) in [(0u32, 11usize), (1, 11), (2, 11)] {
        let of_size = |load: bool| {
            exclusives
                .iter()
                .filter(|word| *word >> 30 == size && ((*word >> 22) & 1 == 1) == load)
                .count()
        };
        assert_eq!(
            (of_size(true), of_size(false)),
            (expected, expected),
            "size {size}: one load- and one store-exclusive per atomic"
        );
    }
}

fn build_rmw(id: u32, name: &str, m: &mut TrustIrModule, op: AtomicRMWOp, ty: Ty) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::PtrMut(Box::new(ty.clone())), ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

// `cas_old(p, expected, desired) -> ty` returning the loaded value.
fn build_cas(id: u32, name: &str, m: &mut TrustIrModule, ty: Ty) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::PtrMut(Box::new(ty.clone())), ty.clone(), ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
                weak: false,
            })
            .with_results(vec![ValueId::new(3), ValueId::new(4)]),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
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
        // The W-register word width completes the 8/16/32/64 old-value set
        // with e2e_aarch64_atomics' i64 functions.
        build_rmw(id, &format!("{n}_i32"), &mut m, op, Ty::I32);
        id += 1;
    }
    build_cas(id, "cas8", &mut m, Ty::I8);
    id += 1;
    build_cas(id, "cas16", &mut m, Ty::I16);
    id += 1;
    build_cas(id, "cas32", &mut m, Ty::I32);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
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
#define R32(op) extern int32_t op##_i32(int32_t*,int32_t);
R8(add)R8(sub)R8(and)R8(or)R8(xor)R8(xchg)R8(smax)R8(smin)R8(umax)R8(umin)
R16(add)R16(sub)R16(and)R16(or)R16(xor)R16(xchg)R16(smax)R16(smin)R16(umax)R16(umin)
R32(add)R32(sub)R32(and)R32(or)R32(xor)R32(xchg)R32(smax)R32(smin)R32(umax)R32(umin)
extern int8_t cas8(int8_t*,int8_t,int8_t);
extern int16_t cas16(int16_t*,int16_t,int16_t);
extern int32_t cas32(int32_t*,int32_t,int32_t);
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
    /* Wrapping i32 arithmetic through uint32_t: signed overflow is not C. */
    int32_t V32[]={0,500000,-500000,INT32_MAX,INT32_MIN,-1,0x33333333,1000000};
    for(unsigned i=0;i<8;i++)for(unsigned j=0;j<8;j++){
        int32_t a=V32[i],b=V32[j],m,old;
        #define K32(op,expr) m=a; old=op##_i32(&m,b); if(old!=a){printf(#op"_i32 old\n");return 9;}{int32_t w=(int32_t)(expr); if(m!=w){printf(#op"_i32 got=%d want=%d\n",m,w);return 10;}}
        K32(add,(uint32_t)a+(uint32_t)b)K32(sub,(uint32_t)a-(uint32_t)b)K32(and,a&b)K32(or,a|b)K32(xor,a^b)K32(xchg,b)
        K32(smax,a>b?a:b)K32(smin,a<b?a:b)
        K32(umax,(uint32_t)a>(uint32_t)b?a:b)K32(umin,(uint32_t)a<(uint32_t)b?a:b)
        m=a; int32_t o=cas32(&m,a,b); if(o!=a||m!=b){printf("cas32 match\n");return 11;}
        m=a; cas32(&m,(int32_t)((uint32_t)a+1u),b); if(m!=a){printf("cas32 mism\n");return 12;}
    }
    printf("narrow and word (i8/i16/i32) atomicrmw (10 ops) + cmpxchg value-correct vs C11\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8]) -> Option<i32> {
    if !can_link_and_run_aarch64_native() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
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
        .args(native_host::c_math_library_args())
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
        let objects = objects_at(&module, opt);
        if objects.is_empty() {
            eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
            return;
        }
        for (lane, obj) in objects {
            let Some(code) = link_run(&format!("narrow_atomics_{lane}"), &obj) else {
                return;
            };
            assert_eq!(
                code, 0,
                "narrow atomic mismatch at {opt:?} via {lane} (failing code {code})"
            );
        }
    }
}

/// The Linux GNU explicit-lse lane's object, checked at object level on
/// every host: it compiles for the generic Linux triple and carries the
/// feature's instructions.
#[test]
fn explicit_lse_linux_object_carries_feature_instructions() {
    for opt in [OptLevel::O0, OptLevel::O2] {
        let object = native_host::compile_with_isa_profile_for(
            "aarch64-unknown-linux-gnu",
            &build_module(),
            opt,
            AArch64IsaProfile::LSE,
        )
        .unwrap_or_else(|error| panic!("{opt:?}: {error}"));
        native_host::assert_elf_aarch64_object(&object);
        // LSE atomic memory operations: CAS* (0x08a07c00 family) and LD<op>/SWP
        // (0x38200000 family with V=0, bit 21 set).
        let lse = |w: u32| w & 0x3fa0_7c00 == 0x08a0_7c00 || w & 0x3f20_0c00 == 0x3820_0000;
        assert!(
            native_host::text_words(&object).into_iter().any(lse),
            "{opt:?}: explicit lse Linux object lacks the feature instructions"
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
