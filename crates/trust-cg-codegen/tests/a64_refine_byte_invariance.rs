// Copyright 2026 Andrew Yates | Apache-2.0
//! Refined narrow returns preserve emitted code and extension behavior.

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{
    Block, BlockId, CallingConv, FuncId, FuncTy, Function, Inst, InstrNode, Module, Pred, Ty,
    ValueId,
};

#[path = "common/aarch64_native.rs"]
mod native;

#[path = "common/a64_interp.rs"]
mod a64_interp;
use a64_interp::{extract_text, run_func};

#[path = "common/pinned_target.rs"]
mod pinned_target;

fn identity(base: Ty, refined: bool) -> Module {
    let mut module = Module::new("refine_narrow_identity");
    let ty = if refined {
        let base = module
            .add_type(base)
            .expect("Module::add_type: test fixture");
        let pred = module
            .intern_pred(Pred::Top)
            .expect("Module::intern_pred: test fixture")
            .unwrap();
        Ty::Refine(base, pred)
    } else {
        base
    };
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "probe", signature, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn compile(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    compile_for(module, opt_level, "aarch64-apple-darwin")
}

/// Compile `module` for `triple`, pinned to it: the `calls` fixtures declare
/// a bodyless `observe`, an FFI boundary trust-ir's validator admits only
/// under a pinned target (`TargetInfoRequired`), which every ingestion entry
/// refuses since WS7.3. Bare and refined twins are pinned alike.
fn compile_for(module: &Module, opt_level: OptLevel, triple: &str) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&pinned_target::pinned(module, triple))
    .expect("valid refined identity must compile")
    .object_code
}

#[test]
fn refined_narrow_returns_have_identical_macho_text() {
    for base in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let bare = compile(&identity(base.clone(), false), opt);
            let refined = compile(&identity(base.clone(), true), opt);
            assert_eq!(
                extract_text(&bare).bytes,
                extract_text(&refined).bytes,
                "{base:?}, {opt:?}: erasure changed machine code"
            );
            assert_eq!(bare, refined, "{base:?} {opt:?}: object bytes changed");
        }
    }
}

#[test]
fn refined_narrow_returns_canonicalize_poisoned_register_bits() {
    for (base, bits, signed) in [
        (Ty::I8, 8_u32, true),
        (Ty::U8, 8, false),
        (Ty::I16, 16, true),
        (Ty::U16, 16, false),
    ] {
        let mask = (1_u64 << bits) - 1;
        let sign = 1_u64 << (bits - 1);
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let bare = compile(&identity(base.clone(), false), opt);
            let refined = compile(&identity(base.clone(), true), opt);
            for low in [0, 1, sign - 1, sign, mask - 1, mask] {
                let input = (0xa55a_9abc_fedc_0000_u64 & !mask) | low;
                let expected = if signed && low & sign != 0 {
                    (low | !mask) as u32
                } else {
                    low as u32
                };
                for (kind, object) in [("bare", &bare), ("refined", &refined)] {
                    let actual =
                        run_func(object, "_probe", |machine| machine.x[0] = input).unwrap();
                    // Darwin requires canonical low 32 return bits. Bits
                    // 32..63 may differ: optimized signed bare returns can
                    // extend to 64 bits without changing that ABI contract.
                    assert_eq!(
                        actual as u32, expected,
                        "{kind} {base:?} {opt:?} input={input:#x}"
                    );
                }
            }
        }
    }
}

fn calls(base: Ty, refined: bool) -> Module {
    let mut module = Module::new("refine_narrow_calls");
    let ty = if refined {
        let base = module
            .add_type(base)
            .expect("Module::add_type: test fixture");
        let pred = module
            .intern_pred(Pred::Top)
            .expect("Module::intern_pred: test fixture")
            .unwrap();
        Ty::Refine(base, pred)
    } else {
        base
    };
    let callee = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut import = Function::new(FuncId::new(0), "observe", callee, BlockId::new(0));
    import.blocks.clear();
    module
        .try_add_function(import)
        .expect("Module::try_add_function: test fixture");
    for indirect in [false, true] {
        let params = if indirect {
            vec![Ty::Func(callee), ty.clone()]
        } else {
            vec![ty.clone()]
        };
        let signature = module
            .add_func_type(FuncTy {
                params: params.clone(),
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let name = if indirect { "_indirect" } else { "_direct" };
        let mut function = Function::new(
            FuncId::new(if indirect { 2 } else { 1 }),
            name,
            signature,
            BlockId::new(0),
        );
        let call = if indirect {
            Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callee,
                args: vec![ValueId::new(1)],
                calling_conv: CallingConv::C,
            }
        } else {
            Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
            }
        };
        let result = ValueId::new(params.len() as u32);
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: params
                .into_iter()
                .enumerate()
                .map(|(index, ty)| (ValueId::new(index as u32), ty))
                .collect(),
            body: vec![
                InstrNode::new(call).with_result(result),
                InstrNode::new(Inst::Return {
                    values: vec![result],
                }),
            ],
        }];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

#[test]
fn refined_direct_and_indirect_narrow_calls_have_identical_macho_text() {
    for base in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let bare = compile(&calls(base.clone(), false), opt);
            let refined = compile(&calls(base.clone(), true), opt);
            assert_eq!(
                extract_text(&bare).bytes,
                extract_text(&refined).bytes,
                "{base:?} {opt:?}"
            );
            assert_eq!(bare, refined, "{base:?} {opt:?}: call object bytes changed");
        }
    }
}

#[test]
fn refined_narrow_calls_and_returns_match_native_c() {
    let mut native_runs = 0;
    for (base, c_ty, values) in [
        (Ty::I8, "int8_t", "-128, -1, 0, 1, 127"),
        (Ty::U8, "uint8_t", "0, 1, 127, 128, 255"),
        (Ty::I16, "int16_t", "-32768, -1, 0, 1, 32767"),
        (Ty::U16, "uint16_t", "0, 1, 32767, 32768, 65535"),
    ] {
        // The host helper selects Linux ELF or Darwin Mach-O explicitly. Its
        // C callee is optimized so an O0 spill cannot mask extension errors.
        let driver = format!(
            r#"
#include <stdint.h>
#include <stdio.h>
int64_t observe({c_ty} x) {{ return (int64_t)x * 13 + 7; }}
extern int64_t _direct({c_ty});
extern int64_t _indirect(int64_t (*)({c_ty}), {c_ty});
extern {c_ty} probe({c_ty});
int main(void) {{
    {c_ty} values[] = {{ {values} }};
    for (unsigned i = 0; i < sizeof(values)/sizeof(values[0]); ++i) {{
        {c_ty} x = values[i];
        int64_t expected = observe(x);
        if (_direct(x) != expected || _indirect(observe, x) != expected || probe(x) != x) {{
            fprintf(stderr, "refined narrow C mismatch at %u\n", i);
            return 1;
        }}
    }}
    return 0;
}}
"#
        );
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let mut module = calls(base.clone(), true);
            let mut identity = identity(base.clone(), true);
            // Both modules intern the same base and Top predicate at slot zero.
            let old = identity.functions.remove(0);
            let signature = module
                .add_func_type(identity.func_types.remove(0))
                .expect("Module::add_func_type: test fixture");
            let mut function = old;
            function.id = FuncId::new(3);
            function.ty = signature;
            module
                .try_add_function(function)
                .expect("Module::try_add_function: test fixture");
            // Compiling the object IS this row's host-independent half, and it
            // runs everywhere. The native half is attempted only where an
            // AArch64 binary can actually be linked and run: on another host
            // `link_run` would print the shared helper's `SKIP:` marker, which
            // the soundness gate reads as a runtime skip and counts against
            // this whole target — a skip of something that was never evidence
            // here, while the four byte-invariance rows that ARE evidence
            // pass. On an AArch64 host nothing is gated and the count
            // assertion below is unchanged.
            let object = native::compile(&module, opt);
            if native::can_execute()
                && native::link_run("refined_narrow_abi", &object, &driver).is_some()
            {
                native_runs += 1;
            }
        }
    }
    if cfg!(all(
        target_arch = "aarch64",
        any(
            target_os = "macos",
            all(target_os = "linux", target_env = "gnu")
        )
    )) {
        assert_eq!(native_runs, 16, "every eligible native driver must execute");
    }
    eprintln!(
        "native C drivers executed: {native_runs}; five input rows and three edges per driver"
    );
    if !native::can_execute() {
        eprintln!(
            "this host cannot link and run an AArch64 binary, so the native C differential was \
             NOT attempted and is NOT claimed; what ran here is the 16 refined/bare object \
             compiles above. The native half is required of the AArch64 floors \
             (scripts/check_darwin_aarch64.py, scripts/check_linux_aarch64.py), which assert \
             all 16 drivers execute."
        );
    }
}

#[test]
fn refined_narrow_calls_and_returns_have_identical_elf_objects() {
    for base in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            for build in [identity, calls] {
                let bare = compile_for(
                    &build(base.clone(), false),
                    opt,
                    "aarch64-unknown-linux-gnu",
                );
                let refined =
                    compile_for(&build(base.clone(), true), opt, "aarch64-unknown-linux-gnu");
                assert_eq!(&bare[..4], b"\x7fELF");
                assert_eq!(bare, refined, "{base:?} {opt:?}: ELF object bytes changed");
            }
        }
    }
}

fn loaded_identity(base: Ty, refined: bool) -> Module {
    let mut module = Module::new("refine_loaded_narrow_return");
    let ty = if refined {
        let base = module
            .add_type(base)
            .expect("Module::add_type: test fixture");
        let pred = module
            .intern_pred(Pred::Top)
            .expect("Module::intern_pred: test fixture")
            .unwrap();
        Ty::Refine(base, pred)
    } else {
        base
    };
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "loaded_probe", signature, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

#[test]
fn refined_loaded_narrow_returns_preserve_the_legal_darwin_abi() {
    // A pointer argument satisfies the ABI. Memory supplies the narrow value;
    // this does not rely on a foreign caller violating its narrow-arg extension.
    for (base, bits, signed) in [
        (Ty::I8, 8_u32, true),
        (Ty::U8, 8, false),
        (Ty::I16, 16, true),
        (Ty::U16, 16, false),
    ] {
        let mask = (1_u64 << bits) - 1;
        let sign = 1_u64 << (bits - 1);
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let bare = compile(&loaded_identity(base.clone(), false), opt);
            let refined = compile(&loaded_identity(base.clone(), true), opt);
            for low in [0, 1, sign - 1, sign, mask - 1, mask] {
                let expected = if signed && low & sign != 0 {
                    (low | !mask) as u32
                } else {
                    low as u32
                };
                for (kind, object) in [("bare", &bare), ("refined", &refined)] {
                    let actual = run_func(object, "_loaded_probe", |machine| {
                        machine.x[0] = 0x4000;
                        for byte in 0..bits / 8 {
                            machine
                                .mem
                                .insert(0x4000 + u64::from(byte), (low >> (8 * byte)) as u8);
                        }
                    })
                    .unwrap();
                    assert_eq!(
                        actual as u32, expected,
                        "{kind} {base:?} {opt:?} memory={low:#x}"
                    );
                }
            }
            assert_eq!(
                bare, refined,
                "{base:?} {opt:?}: loaded-return object bytes changed"
            );
        }
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
