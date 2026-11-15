// trust-cg-codegen/compiler_refusal_layer_tests.rs - every retyped refusal the
// compile driver raises carries its layer's variant
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Trust-core architecture AD-8 / E0.3, compile-driver half: each raise site
//! in `compiler.rs` this change retyped is driven by a real input and its
//! variant asserted with the site's own message. As the rustc bridge files
//! them: `PipelineError::ObjectEmission` -> `TCG-OBJECT-EMIT`;
//! `PipelineError::Unwind` -> `TCG-EH-UNWIND`; `PipelineError::X86` -> the
//! carried x86 variant's layer; `CompileError::{ProfileGenerateTargetUnsupported,
//! DispatcherEmptyModule}` -> `TCG-COMPILE-DRIVER`;
//! `PipelineError::IsaGuardKernelRecheckRejected` -> `TCG-PROOF-465`.

use super::*;
use trust_cg_lower::function::{BasicBlock, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode};

fn object_emission_message(err: PipelineError) -> String {
    match err {
        PipelineError::ObjectEmission(message) => message,
        other => panic!("expected PipelineError::ObjectEmission, got {other:?}"),
    }
}

fn pipeline_unwind_message(err: CompileError) -> String {
    match err {
        CompileError::Pipeline(PipelineError::Unwind(message)) => message,
        other => panic!("expected CompileError::Pipeline(PipelineError::Unwind), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// trust-ir global initializers -> ObjectEmission
// ---------------------------------------------------------------------------

fn module_with_globals(globals: Vec<trust_ir::Global>) -> trust_ir::Module {
    let mut module = trust_ir::Module::new("globals");
    module.types = vec![trust_ir::Ty::U8];
    module.globals = globals;
    module
}

fn global(
    name: &str,
    ty: trust_ir::Ty,
    initializer: Option<trust_ir::Constant>,
) -> trust_ir::Global {
    trust_ir::Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.to_string(),
        ty,
        mutable: true,
        initializer,
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
    }
}

fn globals_refusal(globals: Vec<trust_ir::Global>) -> String {
    object_emission_message(module_object_globals(&module_with_globals(globals)).unwrap_err())
}

#[test]
fn trust_ir_global_linkage_and_placement_refusals_are_object_emission() {
    let mut g = global("EW", trust_ir::Ty::U8, Some(trust_ir::Constant::Int(1)));
    g.linkage = trust_ir::Linkage::ExternalWeak;
    assert!(globals_refusal(vec![g]).contains("linkage `external_weak` (trust-ir v41)"));

    let mut g = global("EW_TLS", trust_ir::Ty::U8, None);
    g.linkage = trust_ir::Linkage::ExternalWeak;
    g.tls = Some(trust_ir::TlsModel::LocalExec);
    assert!(globals_refusal(vec![g]).contains("a thread-local `external_weak` (trust-ir v41)"));

    // A section on a DEFINITION is honoured or refused by the object emitter;
    // on an import it is refused here, typed as the object layer's
    // `ExplicitSectionUnsupported`.
    let mut g = global("SEC", trust_ir::Ty::U8, None);
    g.section = Some("__DATA,__custom".to_string());
    match module_object_globals(&module_with_globals(vec![g])).unwrap_err() {
        PipelineError::ExplicitSectionUnsupported {
            global, section, ..
        } => {
            assert_eq!(global, "SEC");
            assert_eq!(section, "__DATA,__custom");
        }
        other => panic!("expected ExplicitSectionUnsupported, got {other:?}"),
    }

    // (An import's visibility is no longer refused here: it rides on its
    // `ObjectGlobal`, the AArch64 ELF emitters spell it, and every other
    // object path refuses a non-default one as an object-layer refusal.)

    // A retained import (a declaration LLVM lists in `@llvm.used`) is no
    // longer refused here either: it rides on its `ObjectGlobal`, the ELF
    // emitters write nothing for the flag (as llc's ELF writer does), and
    // the Mach-O, COFF, JIT and Wasm paths refuse it as an object-layer
    // refusal.
    let mut g = global("IMPORT_USED", trust_ir::Ty::U8, None);
    g.retained = true;
    let imported = module_object_globals(&module_with_globals(vec![g]))
        .expect("a retained import reaches the object paths");
    assert!(imported[0].is_import && imported[0].retained);

    let mut g = global(
        "NO_LAYOUT",
        trust_ir::Ty::Array(trust_ir::TyId::new(9), 3),
        None,
    );
    g.linkage = trust_ir::Linkage::Internal;
    assert!(globals_refusal(vec![g]).contains("initializer is missing and its type"));
}

#[test]
fn trust_ir_global_initializer_refusals_are_object_emission() {
    // Scalar out of range.
    let message = globals_refusal(vec![global(
        "RANGE",
        trust_ir::Ty::U8,
        Some(trust_ir::Constant::Int(300)),
    )]);
    assert_eq!(
        message,
        "trust-ir global RANGE unsupported: scalar initializer value 300 is outside U8 range"
    );

    // Big-endian multi-byte scalar.
    let mut module = module_with_globals(vec![global(
        "BIG",
        trust_ir::Ty::U32,
        Some(trust_ir::Constant::Int(7)),
    )]);
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "powerpc64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Big,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let message = object_emission_message(module_object_globals(&module).unwrap_err());
    assert_eq!(
        message,
        "trust-ir global BIG unsupported: big-endian multi-byte scalar emission is not verified for any supported target"
    );

    // `global_initializer_error`: a symbol address with an empty symbol.
    let message = globals_refusal(vec![global(
        "EMPTY_SYM",
        trust_ir::Ty::U64,
        Some(trust_ir::Constant::Aggregate(vec![
            trust_ir::Constant::SymbolAddr {
                symbol: String::new(),
                addend: 0,
            },
        ])),
    )]);
    assert_eq!(
        message,
        "trust-ir global EMPTY_SYM unsupported: invalid symbol address"
    );

    // Enum-typed aggregate whose enum the module does not define (enum
    // globals take the typed tag+payload path now; its layout refusals are
    // `global_initializer_error`s).
    let message = globals_refusal(vec![global(
        "ENUM",
        trust_ir::Ty::Enum(trust_ir::EnumId::new(0)),
        Some(trust_ir::Constant::Aggregate(vec![
            trust_ir::Constant::Int(0),
        ])),
    )]);
    assert_eq!(
        message,
        "trust-ir global ENUM unsupported: missing enum EnumId(0)"
    );

    // Byte aggregate element out of u8 range.
    let message = globals_refusal(vec![global(
        "BYTE",
        trust_ir::Ty::U64,
        Some(trust_ir::Constant::Aggregate(vec![
            trust_ir::Constant::Int(256),
        ])),
    )]);
    assert_eq!(
        message,
        "trust-ir global BYTE unsupported: byte aggregate element 0 value 256 is outside u8 range"
    );

    // Aggregate element that is neither an integer nor a symbol address.
    let message = globals_refusal(vec![global(
        "ELEMENT",
        trust_ir::Ty::U64,
        Some(trust_ir::Constant::Aggregate(vec![
            trust_ir::Constant::Bool(true),
        ])),
    )]);
    assert!(
        message.contains("only integer and symbol-address aggregate elements are admitted"),
        "{message}"
    );

    // Integer initializer for Bool.
    let message = globals_refusal(vec![global(
        "B",
        trust_ir::Ty::Bool,
        Some(trust_ir::Constant::Int(1)),
    )]);
    assert!(
        message.contains("scalar integer initializer for Bool"),
        "{message}"
    );

    // Integer initializer for a non-integer type.
    let message = globals_refusal(vec![global(
        "F",
        trust_ir::Ty::F64,
        Some(trust_ir::Constant::Int(1)),
    )]);
    assert_eq!(
        message,
        "trust-ir global F unsupported: integer initializer for non-integer type F64"
    );

    // Float initializer for a non-float type.
    let message = globals_refusal(vec![global(
        "I",
        trust_ir::Ty::I32,
        Some(trust_ir::Constant::Float(1.0)),
    )]);
    assert!(message.contains("float initializer for I32"), "{message}");

    // An initializer kind outside the admitted slice.
    let message = globals_refusal(vec![global(
        "B2",
        trust_ir::Ty::U8,
        Some(trust_ir::Constant::Bool(true)),
    )]);
    assert!(
        message.contains("only byte/symbol-address aggregate and byte-sized scalar initializers"),
        "{message}"
    );
}

// ---------------------------------------------------------------------------
// Exception handling at the JIT / unwired-object-format gates and dispatchers -> Unwind
// ---------------------------------------------------------------------------

fn lir_function(name: &str, opcode: Opcode) -> trust_cg_lower::Function {
    let mut func = trust_cg_lower::Function::new(name, Signature::default());
    func.entry_block = Block(0);
    func.block_order = vec![Block(0)];
    func.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![],
            instructions: vec![Instruction {
                opcode,
                args: vec![],
                results: vec![],
            }],
            source_locs: vec![],
        },
    );
    func
}

fn with_personality_only(mut func: trust_cg_lower::Function) -> trust_cg_lower::Function {
    func.eh_info.personality = Some("rust_eh_personality".to_string());
    func
}

fn lir_module(
    func: trust_cg_lower::Function,
) -> Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)> {
    vec![(func, trust_cg_lower::ProofContext::default())]
}

#[test]
fn eh_gate_refusals_are_unwind() {
    let eh = lir_module(with_personality_only(lir_function("eh_fn", Opcode::Return)));

    let message = pipeline_unwind_message(reject_x86_jit_eh(&eh).unwrap_err());
    assert!(
        message.contains("not supported in the JIT for `eh_fn`"),
        "{message}"
    );

    // The AArch64 JIT publishes EH functions with its own unwind tables; only a
    // proof-grade request refuses them, typed as the missing proof evidence.
    // The certified object routes refuse the same functions through the same
    // census, typed as the unproved exception tables (the proof layer).
    let census = ExceptionTableCensus::from_lir(&eh);
    match census
        .refuse_proof_grade(ProofGradeRoute::ProofGradeJit, Target::Aarch64)
        .unwrap_err()
    {
        CompileError::Jit(crate::jit::JitError::JitUnwindProofEvidenceUnavailable { function }) => {
            assert_eq!(function, "eh_fn");
        }
        other => panic!("expected JitUnwindProofEvidenceUnavailable, got {other:?}"),
    }
    match census
        .refuse_proof_grade(ProofGradeRoute::CertifiedObject, Target::X86_64)
        .unwrap_err()
    {
        CompileError::ExceptionTablesUnproved {
            function,
            target,
            walk_through,
        } => {
            assert_eq!(
                (function.as_str(), target, walk_through),
                ("eh_fn", Target::X86_64, false)
            );
        }
        other => panic!("expected ExceptionTablesUnproved, got {other:?}"),
    }

    // Mach-O and ELF carry unwind tables; COFF and raw bytes refuse, each by name.
    for (format, named) in [
        (
            crate::x86_64::X86OutputFormat::Coff,
            "`eh_fn` targets COFF (no .pdata/.xdata language-level EH path)",
        ),
        (
            crate::x86_64::X86OutputFormat::RawBytes,
            "`eh_fn` targets raw bytes (no object container at all)",
        ),
    ] {
        let message =
            pipeline_unwind_message(reject_x86_eh_for_unwired_aot_format(&eh, format).unwrap_err());
        assert!(message.contains(named), "{message}");
    }
    for format in [
        crate::x86_64::X86OutputFormat::MachO,
        crate::x86_64::X86OutputFormat::Elf,
    ] {
        reject_x86_eh_for_unwired_aot_format(&eh, format)
            .expect("Mach-O and ELF objects carry the EH unwind tables");
    }
}

fn x86_compiler(triple: &str) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).expect("x86 triple"),
    )
    .with_codegen_license(permit_unlicensed())
}

#[test]
fn x86_aot_dispatcher_refuses_invalid_eh_structure_as_unwind() {
    // Personality-only metadata passes the object-format gate and fails the
    // dispatcher's structural guard.
    let compiler = x86_compiler("x86_64-apple-darwin");
    let empty_module = trust_ir::Module::new("eh");
    let message = pipeline_unwind_message(
        compiler
            .compile_x86_64(
                lir_module(with_personality_only(lir_function("eh_fn", Opcode::Return))),
                Vec::new(),
                Instant::now(),
                false,
                Vec::new(),
                None,
                &empty_module,
            )
            .expect_err("metadata-only EH must fail the structural guard"),
    );
    assert!(
        message.starts_with("invalid x86 exception-handling structure in `eh_fn`"),
        "{message}"
    );
}

#[test]
fn x86_jit_dispatcher_refuses_invalid_eh_structure_as_unwind() {
    // An EH opcode with no metadata passes the JIT EH gate (it checks the
    // metadata) and fails the structural guard (no personality).
    let compiler = x86_compiler("x86_64-apple-darwin");
    let lir = lir_module(lir_function("resume_only", Opcode::Resume));
    let definitions = x86_test_module_definitions(lir.iter().map(|(function, _)| function));
    let message = pipeline_unwind_message(
        compiler
            .compile_x86_64_to_jit(
                lir,
                &HashMap::new(),
                crate::jit::JitExternalSymbolResolutionPolicy::default(),
                crate::jit::ProfileHookMode::None,
                JitValidationMode::Unchecked,
                Instant::now(),
                false,
                Vec::new(),
                &definitions,
            )
            .expect_err("an EH opcode without a personality must fail the structural guard"),
    );
    assert!(
        message.starts_with("invalid x86 exception-handling structure in `resume_only`"),
        "{message}"
    );
}

// ---------------------------------------------------------------------------
// x86 refusals carried typed -> PipelineError::X86
// ---------------------------------------------------------------------------

#[test]
fn x86_refusals_are_carried_typed_not_relabelled() {
    match x86_pipeline_error_to_pipeline_error(
        crate::x86_64::X86PipelineError::WindowsCoffUnwindMetadataRequired {
            function: "f".to_string(),
            reason: "a dynamic frame".to_string(),
        },
    ) {
        PipelineError::X86(
            crate::x86_64::X86PipelineError::WindowsCoffUnwindMetadataRequired { function, reason },
        ) => {
            assert_eq!(function, "f");
            assert_eq!(reason, "a dynamic frame");
        }
        other => panic!("expected the typed Windows COFF unwind refusal, got {other:?}"),
    }
    match x86_pipeline_error_to_pipeline_error(crate::x86_64::X86PipelineError::BlockProfiling(
        "b".to_string(),
    )) {
        PipelineError::X86(crate::x86_64::X86PipelineError::BlockProfiling(message)) => {
            assert_eq!(message, "b")
        }
        other => panic!("expected the typed block-profiling refusal, got {other:?}"),
    }
}

#[test]
fn x86_jit_function_refusals_keep_their_x86_variant_with_and_without_fallback() {
    use crate::x86_64::{X86Pipeline, X86PipelineConfig, X86PipelineError as XE};
    let fast = X86Pipeline::new(X86PipelineConfig::default());
    let fallback = X86Pipeline::new(X86PipelineConfig::default());
    let refuse = |pipeline: &X86Pipeline| -> Result<(), XE> {
        if std::ptr::eq(pipeline, &fast) {
            Err(XE::BlockProfiling("fast pipeline refused".to_string()))
        } else {
            Err(XE::Unwind("fallback pipeline refused".to_string()))
        }
    };

    match compile_x86_jit_function_with_fallback(&fast, None, refuse) {
        Err(CompileError::Pipeline(PipelineError::X86(XE::BlockProfiling(message)))) => {
            assert_eq!(message, "fast pipeline refused");
        }
        other => panic!("expected the fast pipeline's typed refusal, got {other:?}"),
    }
    match compile_x86_jit_function_with_fallback(&fast, Some(&fallback), refuse) {
        Err(CompileError::Pipeline(PipelineError::X86(XE::Unwind(message)))) => {
            assert_eq!(message, "fallback pipeline refused");
        }
        other => panic!("expected the fallback pipeline's typed refusal, got {other:?}"),
    }
    assert!(
        compile_x86_jit_function_with_fallback(&fast, Some(&fallback), |p| {
            if std::ptr::eq(p, &fast) {
                Err(XE::BlockProfiling("x".to_string()))
            } else {
                Ok(())
            }
        })
        .is_ok()
    );
}

// ---------------------------------------------------------------------------
// RISC-V call fixups -> ObjectEmission; driver refusals -> CompileError variants
// ---------------------------------------------------------------------------

#[test]
fn riscv_call_fixup_rebase_refusals_are_object_emission() {
    let fixup = crate::riscv::pipeline::RiscVCallFixup {
        auipc_offset: 4,
        jalr_offset: 8,
        callee: "callee".to_string(),
    };
    match rebase_riscv_call_fixup("caller", u64::from(u32::MAX) + 1, &fixup) {
        Err(CompileError::Pipeline(err)) => {
            assert!(object_emission_message(err).contains("outside the u32 patch domain"));
        }
        other => panic!("expected an object-emission refusal, got {other:?}"),
    }
    match rebase_riscv_call_fixup("caller", u64::from(u32::MAX) - 4, &fixup) {
        Err(CompileError::Pipeline(err)) => {
            let message = object_emission_message(err);
            assert!(
                message.starts_with("RISC-V JALR call fixup in `caller` overflows"),
                "{message}"
            );
        }
        other => panic!("expected an object-emission refusal, got {other:?}"),
    }
}

fn const_i64_module(function_name: &str) -> trust_ir::Module {
    use trust_ir::{
        Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
        Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };
    let mut module = TrustIrModule::new("driver");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), function_name, ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn profile_generate_on_x86_is_a_driver_refusal() {
    let sink = std::sync::Arc::new(std::sync::Mutex::new(trust_cg_opt::pgo::CounterMap::new()));
    let err = x86_compiler("x86_64-apple-darwin")
        .with_profile_generate(sink)
        .compile(&const_i64_module("answer"))
        .expect_err("profile-generate is AArch64-only");
    assert!(
        matches!(
            err,
            CompileError::ProfileGenerateTargetUnsupported {
                target: Target::X86_64
            }
        ),
        "{err:?}"
    );
    assert_eq!(
        err.to_string(),
        "PGO profile-generate is only supported for the AArch64 AOT pipeline, not X86_64"
    );
}

#[test]
fn dispatcher_empty_modules_keep_the_dispatcher_message() {
    // b60c75f7 rendered "pipeline error: instruction selection failed: x86_64
    // dispatcher received an empty module" (and the RISC-V twin): the body is
    // kept; the prefix named the pipeline and instruction selection, neither of
    // which ran, so this driver refusal renders without it, like `EmptyModule`.
    let module = trust_ir::Module::new("empty");
    let err = x86_compiler("x86_64-apple-darwin")
        .compile_x86_64(
            Vec::new(),
            Vec::new(),
            Instant::now(),
            false,
            Vec::new(),
            None,
            &module,
        )
        .expect_err("an empty x86 dispatch must refuse");
    assert!(
        matches!(
            err,
            CompileError::DispatcherEmptyModule {
                dispatcher: "x86_64"
            }
        ),
        "{err:?}"
    );
    assert_eq!(
        err.to_string(),
        "x86_64 dispatcher received an empty module"
    );

    let riscv = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::Riscv64,
        parallel: false,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    let err = riscv
        .compile_riscv(Vec::new(), Instant::now(), false, Vec::new(), &module)
        .expect_err("an empty RISC-V dispatch must refuse");
    assert!(
        matches!(
            err,
            CompileError::DispatcherEmptyModule {
                dispatcher: "RISC-V"
            }
        ),
        "{err:?}"
    );
    assert_eq!(
        err.to_string(),
        "RISC-V dispatcher received an empty module"
    );
}

#[test]
fn isa_guard_kernel_recheck_keeps_each_dispatchers_message() {
    // The x86 / RISC-V re-check refusal is unreachable with production guard
    // evidence; its rendering is pinned here. The
    // dispatchers' message body survives the move off `ISel`; the
    // "instruction selection failed: " prefix `ISel` added does not (no
    // instruction selector refused), so the rendered refusal each dispatcher
    // returns (wrapped in `CompileError::Pipeline`) is pinned in full.
    let err = PipelineError::IsaGuardKernelRecheckRejected {
        isa: "x86",
        function: "f".to_string(),
        reason: "r".to_string(),
    };
    assert_eq!(
        err.to_string(),
        "x86 guard kernel gate fail-closed re-check rejected in `f`: r"
    );
    // b60c75f7: "pipeline error: instruction selection failed: x86 guard kernel
    // gate fail-closed re-check rejected in `f`: r".
    assert_eq!(
        CompileError::Pipeline(err).to_string(),
        "pipeline error: x86 guard kernel gate fail-closed re-check rejected in `f`: r"
    );
    let err = PipelineError::IsaGuardKernelRecheckRejected {
        isa: "RISC-V",
        function: "g".to_string(),
        reason: "s".to_string(),
    };
    assert_eq!(
        err.to_string(),
        "RISC-V guard kernel gate fail-closed re-check rejected in `g`: s"
    );
    assert_eq!(
        CompileError::Pipeline(err).to_string(),
        "pipeline error: RISC-V guard kernel gate fail-closed re-check rejected in `g`: s"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> crate::CodegenLicensePolicy {
    crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
}
