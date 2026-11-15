// trust-cg-codegen/tests/e2e_aarch64_atomics.rs
//
// Pinned refutation for TWO confirmed P0 miscompiles of LSE atomics that only
// appeared at -O2 (the -O0 pipeline was correct):
//
//   1. `atomicrmw` (LDADD/LDSET/SWP/...): the update value is operand 0 (a
//      pure USE) while the old-value DEF is operand 1 — the opposite of the
//      usual "operand 0 is the def" layout. AArch64 DCE assumed operand 0 was
//      the def, so it treated the update-value vreg as never-used and deleted
//      the copy materializing it. The atomic then read a stale/undefined
//      register: `atomicrmw add p, v` computed `*p + garbage` instead of
//      `*p + v`.
//
//   2. `cmpxchg` (CAS): the expected value is placed in the CAS Rs register,
//      which is a DEF-USE (expected in, loaded value out). The post-RA copy
//      coalescer scanned the def before the use within that one instruction and
//      concluded the `mov Rs, expected` copy was dead, deleting it — so the CAS
//      compared against an undefined register.
//
// Both are fixed and this test pins them bit-exact against C11 `<stdatomic.h>`
// at O0 and O2 on AArch64 macOS (Darwin AOT and explicit-LSE pipeline lanes)
// and Linux GNU (explicit LSE). Single-threaded suffices to catch the
// value bug (the read-modify-write arithmetic and the compare-exchange logic).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_ir::{
    AtomicRMWOp, Block as TrustIrBlock, CastOp, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ordering, Ty, ValueId,
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
    // Per-size expectation table for a family that grows: the sizes here are the
    // encoding's 31:30 field, and only the doubleword row is populated while this
    // module builds I64 atomics, so clippy sees one element.
    #[allow(clippy::single_element_loop)]
    for (size, expected) in [(3u32, 12usize)] {
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

// `fn name(p: *mut i64, v: i64) -> i64 { atomicrmw <op> seq_cst *p, v }`
// returns the OLD value.
fn build_rmw(id: u32, name: &str, m: &mut TrustIrModule, op: AtomicRMWOp) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::PtrMut(Box::new(Ty::I64)), Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(Ty::I64))),
            (ValueId::new(1), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::AtomicRMW {
                op,
                ty: Ty::I64,
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

fn build_module() -> TrustIrModule {
    use AtomicRMWOp::*;
    let mut m = TrustIrModule::new("atomics");
    let ops = [
        (Add, "rmw_add"),
        (Sub, "rmw_sub"),
        (And, "rmw_and"),
        (Or, "rmw_or"),
        (Xor, "rmw_xor"),
        (Xchg, "rmw_xchg"),
        (Max, "rmw_max"),
        (Min, "rmw_min"),
        (UMax, "rmw_umax"),
        (UMin, "rmw_umin"),
    ];
    for (i, (op, name)) in ops.iter().enumerate() {
        build_rmw(i as u32, name, &mut m, *op);
    }

    // `fn cas_old(p, expected, desired) -> i64` returns the loaded value.
    let cas_ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::PtrMut(Box::new(Ty::I64)), Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut cas_old = TrustIrFunction::new(FuncId::new(100), "cas_old", cas_ft, BlockId::new(0));
    cas_old.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(Ty::I64))),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
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
    m.try_add_function(cas_old)
        .expect("Module::try_add_function: test fixture");

    // `fn cas_ok(p, expected, desired) -> i64` returns the success flag (0/1).
    let cas_ok_ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::PtrMut(Box::new(Ty::I64)), Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut cas_ok = TrustIrFunction::new(FuncId::new(101), "cas_ok", cas_ok_ft, BlockId::new(0));
    cas_ok.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(Ty::I64))),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                expected: ValueId::new(1),
                desired: ValueId::new(2),
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
                weak: false,
            })
            .with_results(vec![ValueId::new(3), ValueId::new(4)]),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    m.try_add_function(cas_ok)
        .expect("Module::try_add_function: test fixture");
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
        .expect("atomics module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#define D(op) extern int64_t rmw_##op(int64_t*,int64_t);
D(add)D(sub)D(and)D(or)D(xor)D(xchg)D(max)D(min)D(umax)D(umin)
extern int64_t cas_old(int64_t*,int64_t,int64_t);
extern int64_t cas_ok(int64_t*,int64_t,int64_t);
int main(void){
    int64_t A[]={0,5,-5,0x0f0f0f0f0f0f0f0fLL,-1,100,0x7fffffffffffffffLL};
    int64_t B[]={0,3,-3,(int64_t)0xf0f0f0f0f0f0f0f0ULL,1,-100,3};
    for(unsigned i=0;i<sizeof(A)/sizeof(A[0]);i++)for(unsigned j=0;j<sizeof(B)/sizeof(B[0]);j++){
        int64_t a=A[i],b=B[j],m,old;
        #define CHK(op, expr) m=a; old=rmw_##op(&m,b); if(old!=a){printf(#op" old\n");return 1;} { int64_t want=(expr); if(m!=want){printf(#op" mem got=%lld want=%lld\n",(long long)m,(long long)want);return 2;} }
        CHK(add, a+b) CHK(sub, a-b) CHK(and, a&b) CHK(or, a|b) CHK(xor, a^b) CHK(xchg, b)
        CHK(max, a>b?a:b) CHK(min, a<b?a:b)
        CHK(umax, (uint64_t)a>(uint64_t)b?a:b) CHK(umin, (uint64_t)a<(uint64_t)b?a:b)
        /* cmpxchg match: expected == current -> swaps, returns old */
        m=a; int64_t o=cas_old(&m,a,b); if(o!=a||m!=b){printf("cas match o=%lld m=%lld\n",(long long)o,(long long)m);return 3;}
        /* cmpxchg mismatch: expected != current -> no change, flag 0 */
        m=a; int64_t f=cas_ok(&m,a+1,b); if(f!=0||m!=a){printf("cas mismatch f=%lld m=%lld\n",(long long)f,(long long)m);return 4;}
        /* cmpxchg success: expected == current -> swaps, flag 1 */
        m=a; int64_t s=cas_ok(&m,a,b); if(s!=1||m!=b){printf("cas succ s=%lld m=%lld\n",(long long)s,(long long)m);return 5;}
    }
    printf("atomicrmw (10 ops) + cmpxchg value-correct vs C11 atomics\n");
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
fn e2e_aarch64_atomicrmw_and_cmpxchg() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let objects = objects_at(&module, opt);
        if objects.is_empty() {
            eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
            return;
        }
        for (lane, obj) in objects {
            let Some(code) = link_run(&format!("atomics_{lane}"), &obj) else {
                return;
            };
            assert_eq!(
                code, 0,
                "atomic op mismatch at {opt:?} via {lane} (failing code {code})"
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
