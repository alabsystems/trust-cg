// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Native LSE regression: B1's Gpr64 value carrier must not turn its one-byte
//! compare/exchange into a 64-bit memory access. This is explicit-LSE pipeline
//! correctness evidence, not generic Linux AOT or proof-required JIT coverage.
//! The native control runs on AArch64 Linux GNU (ELF) and macOS (Mach-O); the
//! refusal controls stay on the generic Linux triple on both hosts.

#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/native_host.rs"]
mod native_host;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::fmt::Write;
use std::fs;
use std::process::Command;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};
use trust_cg_codegen::{Compiler, CompilerConfig};

use trust_ir::{
    AtomicRMWOp, Block, BlockId, CastOp, Endianness, FuncId, FuncTy, Function, Inst, InstrNode,
    Module, Ordering, StructPassingPolicy, TargetInfo, Ty, ValueId,
};

#[derive(Clone, Copy, Debug)]
enum Operation {
    Cas {
        success: Ordering,
        failure: Ordering,
        return_success: bool,
    },
    Load(Ordering),
    Store(Ordering),
    Exchange,
}

const LINUX_TRIPLE: &str = "aarch64-unknown-linux-gnu";

/// Generic Linux module: the refusal controls are object-level on every host.
fn module() -> Module {
    module_for(LINUX_TRIPLE)
}

fn module_for(triple: &str) -> Module {
    let mut module = Module::new("linux_bool_atomics");
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module
}

fn add_function(module: &mut Module, name: &str, ty: Ty, operation: Operation) {
    let mut params = vec![Ty::PtrMut(Box::new(ty.clone()))];
    if !matches!(operation, Operation::Load(_)) {
        params.push(ty.clone());
    }
    if matches!(operation, Operation::Cas { .. }) {
        params.push(ty.clone());
    }
    let returns = match operation {
        Operation::Store(_) => vec![],
        Operation::Cas {
            return_success: true,
            ..
        } => vec![Ty::U64],
        _ => vec![ty.clone()],
    };
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(module.functions.len() as u32),
        name,
        sig,
        BlockId::new(0),
    );
    let node = match operation {
        Operation::Cas {
            success, failure, ..
        } => InstrNode::new(Inst::CmpXchg {
            ty: ty.clone(),
            ptr: ValueId::new(0),
            expected: ValueId::new(1),
            desired: ValueId::new(2),
            success,
            failure,
            weak: false,
        })
        .with_results(vec![ValueId::new(3), ValueId::new(4)]),
        Operation::Load(ordering) => InstrNode::new(Inst::AtomicLoad {
            ty: ty.clone(),
            ptr: ValueId::new(0),
            ordering,
        })
        .with_result(ValueId::new(3)),
        Operation::Store(ordering) => InstrNode::new(Inst::AtomicStore {
            ty: ty.clone(),
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            ordering,
        }),
        Operation::Exchange => InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::Xchg,
            ty: ty.clone(),
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            ordering: Ordering::SeqCst,
        })
        .with_result(ValueId::new(3)),
    };
    let mut body = vec![node];
    let result = if matches!(
        operation,
        Operation::Cas {
            return_success: true,
            ..
        }
    ) {
        body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::U64,
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
        );
        ValueId::new(5)
    } else {
        ValueId::new(3)
    };
    body.push(InstrNode::new(Inst::Return {
        values: if matches!(operation, Operation::Store(_)) {
            vec![]
        } else {
            vec![result]
        },
    }));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(id, ty)| (ValueId::new(id as u32), ty))
            .collect(),
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn pipeline(opt_level: OptLevel, profile: AArch64IsaProfile) -> Pipeline {
    pipeline_for(LINUX_TRIPLE, opt_level, profile)
}

fn pipeline_for(triple: &str, opt_level: OptLevel, profile: AArch64IsaProfile) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level,
        verify: true,
        target_triple: triple.into(),
        ..PipelineConfig::default()
    })
    .with_aarch64_isa_profile(profile)
}

fn scratch() -> fresh_dir::ScratchDir {
    fresh_dir::create("trust-cg-bool-atomics-")
}

fn check_atomic_encoding(object: &[u8], operation: Operation) {
    // Code words read independently of the compiler's object emitter/decoder.
    let words = native_host::text_words(object);
    match operation {
        Operation::Cas {
            success, failure, ..
        } => {
            let cas: Vec<_> = words
                .into_iter()
                .filter(|word| word & 0x3fa0_7c00 == 0x08a0_7c00)
                .collect();
            assert_eq!(cas.len(), 1, "exactly one CAS instruction");
            assert_eq!(
                cas[0] >> 30,
                0,
                "Bool/U8 must be CASB, never word/dword CAS"
            );
            let acquire = matches!(
                success,
                Ordering::Acquire | Ordering::AcqRel | Ordering::SeqCst
            ) || matches!(failure, Ordering::Acquire | Ordering::SeqCst);
            let release = matches!(
                success,
                Ordering::Release | Ordering::AcqRel | Ordering::SeqCst
            ) || failure == Ordering::SeqCst;
            assert_eq!((cas[0] >> 22) & 1, u32::from(acquire));
            assert_eq!((cas[0] >> 15) & 1, u32::from(release));
        }
        Operation::Load(_) => assert_eq!(
            words
                .iter()
                .filter(|word| **word & 0xffff_fc00 == 0x08df_fc00)
                .count(),
            1,
            "one LDARB"
        ),
        Operation::Store(_) => assert_eq!(
            words
                .iter()
                .filter(|word| **word & 0xffff_fc00 == 0x089f_fc00)
                .count(),
            1,
            "one STLRB"
        ),
        Operation::Exchange => unreachable!(),
    }
}

const C_DRIVER: &str = r#"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdatomic.h>
typedef uint8_t u8;
struct guard_bool { _Alignas(8) bool value; unsigned char guard[7]; };
struct guard_u8 { _Alignas(8) u8 value; unsigned char guard[7]; };
static const bool values_bool[]={false,true};
static const u8 values_u8[]={0,1,0x80,0xff};
static const unsigned char guards[3][7]={{0},{0xff,0xff,0xff,0xff,0xff,0xff,0xff},{0x23,0x45,0x67,0x89,0xab,0xcd,0xef}};
static unsigned long cases;
#define VERIFY_GUARD(g,k,label) do { if(memcmp((g).guard,guards[k],7)) {printf(label " adjacent-byte mutation\n");return 1;} } while(0)
#define CHECK_CAS(T,OLD,OK) do { \
  for(unsigned k=0;k<3;k++) \
  for(unsigned i=0;i<sizeof(values_##T)/sizeof(values_##T[0]);i++) \
  for(unsigned e=0;e<sizeof(values_##T)/sizeof(values_##T[0]);e++) \
  for(unsigned d=0;d<sizeof(values_##T)/sizeof(values_##T[0]);d++) { \
    T initial=values_##T[i],expected=values_##T[e],desired=values_##T[d]; \
    _Atomic(T) oracle=initial; T exp=expected; \
    unsigned want_ok=atomic_compare_exchange_strong_explicit(&oracle,&exp,desired,memory_order_seq_cst,memory_order_seq_cst); \
    struct guard_##T g={initial,{0}}; memcpy(g.guard,guards[k],7); \
    T old=OLD(&g.value,expected,desired); cases++; \
    if(old!=initial || g.value!=atomic_load(&oracle)) {printf(#OLD " old/memory mismatch i=%u e=%u d=%u\n",i,e,d);return 1;} \
    VERIFY_GUARD(g,k,#OLD); \
    g.value=initial; uint64_t ok=OK(&g.value,expected,desired); cases++; \
    if(ok!=want_ok || g.value!=atomic_load(&oracle)) {printf(#OK " success/memory mismatch i=%u e=%u d=%u got=%llu want=%u\n",i,e,d,(unsigned long long)ok,want_ok);return 1;} \
    VERIFY_GUARD(g,k,#OK); \
  } \
} while(0)
#define CHECK_LOAD(T,FN) do { \
  for(unsigned k=0;k<3;k++) for(unsigned i=0;i<sizeof(values_##T)/sizeof(values_##T[0]);i++) { \
    struct guard_##T g={values_##T[i],{0}}; memcpy(g.guard,guards[k],7); \
    _Atomic(T) oracle=values_##T[i]; T value=FN(&g.value); cases++; \
    if(value!=atomic_load(&oracle) || g.value!=values_##T[i]) {printf(#FN " load mismatch\n");return 1;} VERIFY_GUARD(g,k,#FN); \
  } \
} while(0)
#define CHECK_STORE(T,FN) do { \
  for(unsigned k=0;k<3;k++) for(unsigned i=0;i<sizeof(values_##T)/sizeof(values_##T[0]);i++) \
  for(unsigned d=0;d<sizeof(values_##T)/sizeof(values_##T[0]);d++) { \
    struct guard_##T g={values_##T[i],{0}}; memcpy(g.guard,guards[k],7); \
    _Atomic(T) oracle=values_##T[i]; atomic_store(&oracle,values_##T[d]); FN(&g.value,values_##T[d]); cases++; \
    if(g.value!=atomic_load(&oracle)) {printf(#FN " store mismatch\n");return 1;} VERIFY_GUARD(g,k,#FN); \
  } \
} while(0)
"#;

#[test]
fn native_lse_bool_and_u8_atomics_match_c11_o0_through_o3() {
    assert!(
        AArch64IsaProfile::LSE.is_supported_by_host(),
        "this native LSE lane requires real host LSE"
    );
    let mut module = module_for(native_host::TRIPLE);
    let mut source = String::from(C_DRIVER);
    let mut calls = String::new();
    let mut operations = Vec::new();
    for (label, ty) in [("bool", Ty::Bool), ("u8", Ty::U8)] {
        for (s, success) in [
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ]
        .into_iter()
        .enumerate()
        {
            for (f, failure) in [Ordering::Relaxed, Ordering::Acquire, Ordering::SeqCst]
                .into_iter()
                .enumerate()
            {
                let old = format!("{label}_cas_old_{s}_{f}");
                let ok = format!("{label}_cas_ok_{s}_{f}");
                for (name, return_success) in [(&old, false), (&ok, true)] {
                    let operation = Operation::Cas {
                        success,
                        failure,
                        return_success,
                    };
                    add_function(&mut module, name, ty.clone(), operation);
                    operations.push(operation);
                    writeln!(
                        source,
                        "extern {} {name}({label}*,{label},{label});",
                        if return_success { "uint64_t" } else { label }
                    )
                    .unwrap();
                }
                writeln!(calls, "CHECK_CAS({label},{old},{ok});").unwrap();
            }
        }
        for (index, ordering) in [Ordering::Relaxed, Ordering::Acquire, Ordering::SeqCst]
            .into_iter()
            .enumerate()
        {
            let name = format!("{label}_load_{index}");
            let operation = Operation::Load(ordering);
            add_function(&mut module, &name, ty.clone(), operation);
            operations.push(operation);
            writeln!(source, "extern {label} {name}({label}*);").unwrap();
            writeln!(calls, "CHECK_LOAD({label},{name});").unwrap();
        }
        for (index, ordering) in [Ordering::Relaxed, Ordering::Release, Ordering::SeqCst]
            .into_iter()
            .enumerate()
        {
            let name = format!("{label}_store_{index}");
            let operation = Operation::Store(ordering);
            add_function(&mut module, &name, ty.clone(), operation);
            operations.push(operation);
            writeln!(source, "extern void {name}({label}*,{label});").unwrap();
            writeln!(calls, "CHECK_STORE({label},{name});").unwrap();
        }
    }
    // SeqCst C11 controls measure values, not cross-thread ordering. Actual CAS
    // A/R bits above independently cover all 15 valid Rust ordering pairs,
    // including failure stronger than success (which C11 itself disallows).
    writeln!(source, "int main(void) {{\n{calls}if(cases!=6714) return 2; printf(\"atomic_cases=%lu\\n\",cases); return 0; }}").unwrap();
    assert!(trust_ir_build::validate::validate_module(&module).is_empty());
    let lowered = permit_translate_module(&module).unwrap();
    assert_eq!(lowered.len(), operations.len());
    let root = scratch();
    let driver = root.join("driver.c");
    fs::write(&driver, source).unwrap();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let pipeline = pipeline_for(native_host::TRIPLE, opt, AArch64IsaProfile::LSE);
        let mut link = Command::new("cc");
        link.args(["-O2", "-std=c11"]).arg(&driver);
        for (index, ((function, _), operation)) in lowered.iter().zip(&operations).enumerate() {
            let object = pipeline.compile_function(function).unwrap();
            check_atomic_encoding(&object, *operation);
            let path = root.join(format!("{opt:?}_{index}.o"));
            fs::write(&path, object).unwrap();
            link.arg(path);
        }
        let executable = root.join(format!("native_{opt:?}"));
        link.arg("-o").arg(&executable);
        let linked =
            process::command_output_with_timeout(&mut link, process::codegen_link_timeout())
                .unwrap();
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "link {opt:?} in {}: {}",
            root.display(),
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let run = process::command_output_with_timeout(
            &mut Command::new(executable),
            process::codegen_run_timeout(),
        )
        .unwrap();
        assert!(
            !run.timed_out && run.output.status.success(),
            "native {opt:?} in {}: {}{}",
            root.display(),
            String::from_utf8_lossy(&run.output.stdout),
            String::from_utf8_lossy(&run.output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&run.output.stdout).trim(),
            "atomic_cases=6714"
        );
    }
    println!(
        "26,856 native atomic executions ({}): Bool/U8 CAS, load/store, all O0–O3, seven adjacent guards",
        native_host::HOST
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn linux_atomic_types_features_and_orderings_lower_or_stay_closed() {
    let mut checks = 0;
    // The generic Linux AOT profile has no LSE: compare-exchange now lowers
    // through the LL/SC pseudo and its post-RA LDAXR{B}/STLXR{B} retry loop
    // (natively executed by e2e_aarch64_llsc_atomics), never a CAS word.
    for (ty, size) in [(Ty::Bool, 0), (Ty::U8, 0), (Ty::U64, 3)] {
        let mut source = module();
        add_function(
            &mut source,
            "baseline_cas",
            ty,
            Operation::Cas {
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
                return_success: true,
            },
        );
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig::default(),
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
        )
        .with_codegen_license(permit_unlicensed());
        let words = native_host::text_words(&compiler.compile(&source).unwrap().object_code);
        assert!(
            words.iter().all(|word| word & 0x3fa0_7c00 != 0x08a0_7c00),
            "baseline profile must not emit an LSE CAS"
        );
        let exclusive: Vec<_> = words
            .iter()
            .filter(|word| **word & 0x3fa0_7c00 == 0x0800_7c00)
            .collect();
        assert_eq!(exclusive.len(), 2, "one LDAXR/STLXR pair");
        assert!(
            exclusive
                .iter()
                .all(|word| *word >> 30 == size && (*word >> 15) & 1 == 1)
        );
        checks += 1;
    }
    for ty in [Ty::I128, Ty::U128, Ty::Bool] {
        for operation in [
            Operation::Load(Ordering::SeqCst),
            Operation::Store(Ordering::SeqCst),
            Operation::Exchange,
            Operation::Cas {
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
                return_success: true,
            },
        ] {
            if ty == Ty::Bool && !matches!(operation, Operation::Exchange) {
                continue;
            }
            let mut source = module();
            add_function(&mut source, "unsupported_atomic", ty.clone(), operation);
            assert!(trust_ir_build::validate::validate_module(&source).is_empty());
            let lowered = permit_translate_module(&source).unwrap();
            for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let result = pipeline(opt, AArch64IsaProfile::LSE).compile_function(&lowered[0].0);
                if ty == Ty::Bool {
                    // Bool exchange is a one-byte SWPALB under LSE (natively
                    // executed with and/or/xor by e2e_aarch64_llsc_atomics).
                    let words = native_host::text_words(&result.unwrap());
                    let swaps: Vec<_> = words
                        .iter()
                        .filter(|word| **word & 0x3f20_fc00 == 0x3820_8000)
                        .collect();
                    assert_eq!(swaps.len(), 1, "{operation:?}: one SWP");
                    assert_eq!(*swaps[0] >> 30, 0, "Bool exchange must be SWPB");
                } else {
                    // 128-bit atomics now lower on every profile through the
                    // LDXP/STXP pair loop (natively executed by
                    // e2e_aarch64_llsc_atomics); never CASP or a 64-bit LSE op.
                    let words = native_host::text_words(&result.unwrap());
                    assert!(
                        words.iter().any(|word| word & 0xbfa0_0000 == 0x8820_0000),
                        "{ty:?} {operation:?}: no LDXP/STXP pair"
                    );
                    assert!(
                        words.iter().all(|word| word & 0xbfa0_7c00 != 0x0820_7c00
                            && word & 0x3fa0_7c00 != 0x08a0_7c00
                            && word & 0x3f20_0c00 != 0x3820_0000),
                        "{ty:?} {operation:?}: CASP/CAS/LSE word in a 128-bit atomic"
                    );
                }
                checks += 1;
            }
        }
    }
    for ty in [Ty::Bool, Ty::U8] {
        for success in [
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ] {
            for failure in [Ordering::Release, Ordering::AcqRel] {
                let mut source = module();
                add_function(
                    &mut source,
                    "bad_failure",
                    ty.clone(),
                    Operation::Cas {
                        success,
                        failure,
                        return_success: true,
                    },
                );
                assert!(
                    permit_translate_module(&source)
                        .unwrap_err()
                        .to_string()
                        .contains("failure ordering")
                );
                checks += 1;
            }
        }
        for operation in [
            Operation::Load(Ordering::Release),
            Operation::Load(Ordering::AcqRel),
            Operation::Store(Ordering::Acquire),
            Operation::Store(Ordering::AcqRel),
        ] {
            let mut source = module();
            add_function(&mut source, "bad_ordering", ty.clone(), operation);
            assert!(
                permit_translate_module(&source)
                    .unwrap_err()
                    .to_string()
                    .contains("ordering")
            );
            checks += 1;
        }
    }
    assert_eq!(checks, 67);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
