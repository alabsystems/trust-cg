// Generic TrustIR static indirect-call devirtualization through public compiler paths.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::collections::HashMap;

#[cfg(target_arch = "aarch64")]
use trust_cg_codegen::JitError;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    CompileArtifactCacheConfig, CompileArtifactCacheStatus, CompileArtifactDependencyIdentity,
    CompileArtifactProofPolicy, CompileError, Compiler, CompilerConfig, CompilerTrace,
    CompilerTraceLevel,
};
// Used only by the AArch64-gated fixup test below, so the import carries the
// same gate; on x86-64 it is genuinely unused and `-D warnings` is right.
use trust_ir::inst::{BinOp, CastOp};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage,
    Module, Ty, ValueId,
};

fn call_module(indirect: bool) -> Module {
    let mut module = Module::new(if indirect {
        "generic_static_indirect"
    } else {
        "generic_direct"
    });
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut add_one = Function::new(FuncId::new(0), "add_one", sig, BlockId::new(0));
    add_one.linkage = Linkage::Internal;
    let mut add_one_entry = Block::new(BlockId::new(0));
    add_one_entry.params.push((ValueId::new(0), Ty::I64));
    add_one_entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(1)),
    );
    add_one_entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    add_one_entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    add_one.blocks.push(add_one_entry);
    module.functions.push(add_one);

    let mut caller = Function::new(FuncId::new(1), "entry", sig, BlockId::new(0));
    let mut caller_entry = Block::new(BlockId::new(0));
    caller_entry.params.push((ValueId::new(0), Ty::I64));
    if indirect {
        caller_entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Func(sig),
                value: Constant::FnDef(FuncId::new(0)),
            })
            .with_result(ValueId::new(1)),
        );
        caller_entry.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(sig),
                dst_ty: Ty::Ptr,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
        );
        caller_entry.body.push(
            InstrNode::new(Inst::Copy {
                ty: Ty::Ptr,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
        );
        caller_entry.body.push(
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(3),
                sig,
                args: vec![ValueId::new(0)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(4)),
        );
        caller_entry.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(4)],
        }));
    } else {
        caller_entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
        caller_entry.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
    }
    caller.blocks.push(caller_entry);
    module.functions.push(caller);
    module
}

fn escaped_local_identity_module(as_empty_closure: bool) -> Module {
    let mut module = call_module(true);
    let caller = &mut module.functions[1].blocks[0];
    let constant = caller
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::Const { value, .. } if matches!(value, Constant::FnDef(_)) => Some(value),
            _ => None,
        })
        .expect("function identity constant");
    if as_empty_closure {
        // A capture-free closure constant at the FnDef's `Ty::Func`: the
        // spelling trust-ir refuses (`ConstTypeMismatch`; a closure constant
        // inhabits a `Ty::Closure`), so since WS7.3 it is refused at ingestion.
        *constant = Constant::Closure {
            func: FuncId::new(0),
            captures: vec![],
        };
    }
    caller
        .body
        .retain(|node| !matches!(node.inst, Inst::CallIndirect { .. } | Inst::Return { .. }));
    caller.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    module
}

fn test_cache_config(root: &std::path::Path) -> CompileArtifactCacheConfig {
    CompileArtifactCacheConfig::new(
        root,
        CompileArtifactProofPolicy::Unchecked,
        CompileArtifactDependencyIdentity::new(
            "source-lock-sha256:trust-cg-static-identity-test",
            "source-lock-sha256:trust-ir-static-identity-test",
            "source-lock-sha256:ay-static-identity-test",
            "rustc:stage2-sha256:static-identity-test",
            "tcargo:sha256:static-identity-test",
            "trust",
        ),
    )
}

/// AOT object targets whose writers cannot show that a reference to a
/// module-local function binds locally; `Compiler::compile` refuses one there.
/// The x86-64 Mach-O and COFF writers and RISC-V bind an unreferenced
/// module-local definition local, but no reference to one is read back as
/// reaching that local symbol.
const UNBOUND_OBJECT_TRIPLES: [&str; 2] = ["x86_64-apple-darwin", "riscv64-unknown-linux-gnu"];

/// The ELF and Mach-O object targets whose emitters bind module-local
/// functions locally (`STB_LOCAL`; `N_EXT` clear) and whose objects
/// `Compiler::compile` checks for it: both AArch64 formats, and x86-64 ELF
/// since ruling OD-X86-ELF-LOCAL-BINDING-20261027.
const LOCAL_BINDING_TRIPLES: [&str; 3] = [
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-unknown-linux-gnu",
];

fn compiler_for(triple: &str, config: CompilerConfig) -> Compiler {
    Compiler::new_for_target_spec(config, TargetSpec::parse(triple).expect("triple"))
        .with_codegen_license(permit_unlicensed())
}

/// `name` is exactly one defined local function symbol of `object`: an
/// `STB_LOCAL` `STT_FUNC` of an ELF object, or a non-external `N_SECT` `_name`
/// of a Mach-O object (an `n_type` of exactly `N_SECT`).
fn assert_local_function_symbol(triple: &str, object: &[u8], name: &str) {
    if triple.contains("apple") {
        let records = trust_cg_codegen::macho::reparse::read_object_records(object)
            .expect("AArch64 Mach-O object");
        let spelled = format!("_{name}");
        let rows: Vec<_> = records
            .symbols
            .iter()
            .filter(|symbol| symbol.name == spelled)
            .collect();
        assert!(
            matches!(
                rows.as_slice(),
                [symbol] if symbol.n_type == 0x0e && symbol.n_sect == 1
            ),
            "`{spelled}` must be one non-external definition in __text: {rows:?}"
        );
        return;
    }
    let records =
        trust_cg_codegen::elf::reparse::read_object_records(object).expect("AArch64 ELF object");
    let rows: Vec<_> = records
        .symbols
        .iter()
        .filter(|symbol| symbol.name == name)
        .collect();
    assert!(
        matches!(
            rows.as_slice(),
            [symbol] if symbol.binding == 0 && symbol.symbol_type == 2 && symbol.section_index != 0
        ),
        "`{name}` must be one defined local function symbol: {rows:?}"
    );
}

fn assert_one_static_devirtualization(trace: &CompilerTrace) {
    let phase = trace
        .entries
        .iter()
        .find(|entry| entry.phase == "adapter")
        .expect("shared adapter phase is traced");
    assert!(
        phase
            .detail
            .as_deref()
            .is_some_and(|detail| detail.contains("1 static calls devirtualized")),
        "unexpected adapter trace detail: {:?}",
        phase.detail
    );
}

fn assert_one_incompatible_static_target(trace: &CompilerTrace) {
    let phase = trace
        .entries
        .iter()
        .find(|entry| entry.phase == "adapter")
        .expect("shared adapter phase is traced");
    let detail = phase.detail.as_deref().expect("adapter trace detail");
    assert!(detail.contains("0 static calls devirtualized"), "{detail}");
    assert!(
        detail.contains("1 incompatible static calls retained"),
        "{detail}"
    );
}

extern "C" fn malicious_add_one_override(input: i64) -> i64 {
    input.wrapping_sub(1000)
}

#[test]
fn aot_binding_of_static_identity_is_object_local_or_refused_while_jit_is_exact() {
    let indirect = call_module(true);
    let mut interposable_direct = call_module(false);
    interposable_direct.functions[0].linkage = Linkage::External;
    let mut config = CompilerConfig::for_host_jit_unchecked();
    config.trace_level = CompilerTraceLevel::Full;

    // Off AArch64 ELF and Mach-O, AOT refuses before object emission: the writer cannot
    // show the target binds locally. Retaining CallIndirect alone is
    // insufficient: its originating FnDef pointer is also a symbol relocation
    // whose global spelling could be interposed.
    for triple in UNBOUND_OBJECT_TRIPLES {
        for linkage in [Linkage::Internal, Linkage::Private] {
            let mut candidate = indirect.clone();
            candidate.functions[0].linkage = linkage;
            let mut aot_config = config.clone();
            aot_config.emit_proofs = true;
            let error = compiler_for(triple, aot_config)
                .compile(&candidate)
                .expect_err("unbound static identity must fail before AOT object/proof emission");
            assert!(
                matches!(
                    error,
                    CompileError::AotStaticFunctionIdentityBindingUnsupported {
                        candidate_count: 1,
                        ..
                    }
                ),
                "unexpected AOT refusal for {triple} {linkage}: {error}"
            );
        }
    }
    // On AArch64 ELF and Mach-O the FnDef address names the local
    // definition, so the candidate compiles and stays an indirect call (no
    // exact-call authority is minted for objects).
    for (triple, linkage) in LOCAL_BINDING_TRIPLES
        .into_iter()
        .flat_map(|triple| [(triple, Linkage::Internal), (triple, Linkage::Private)])
    {
        let mut candidate = indirect.clone();
        candidate.functions[0].linkage = linkage;
        let result = compiler_for(triple, config.clone())
            .compile(&candidate)
            .unwrap_or_else(|error| panic!("{triple} {linkage}: {error}"));
        let trace = result.trace.as_ref().expect("object trace");
        let detail = trace
            .entries
            .iter()
            .find(|entry| entry.phase == "adapter")
            .and_then(|entry| entry.detail.as_deref())
            .expect("adapter trace detail");
        assert!(
            detail.contains("0 static calls devirtualized")
                && detail.contains("1 compatible calls retained without exact-call authority"),
            "{triple} {linkage}: {detail}"
        );
        assert_local_function_symbol(triple, &result.object_code, "add_one");
    }

    // JIT has a closed internal-offset namespace.  An explicit same-name
    // extern entry is an adversarial control: an interposable call would return
    // input-1000, while an exact module call must still select add_one.
    let mut malicious_externs = HashMap::new();
    malicious_externs.insert(
        "add_one".to_string(),
        malicious_add_one_override as *const () as *const u8,
    );
    let indirect_jit = Compiler::new(config.clone())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&indirect, &malicious_externs)
        .expect("static indirect JIT compilation succeeds");
    assert_one_static_devirtualization(indirect_jit.trace.as_ref().expect("JIT trace"));

    let direct_jit = Compiler::new(config.clone())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&interposable_direct, &HashMap::new())
        .expect("global direct-call JIT compilation succeeds");
    let overridden_direct_jit = Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&interposable_direct, &malicious_externs)
        .expect("interposable global direct-call control JIT compilation succeeds");

    let indirect_entry = unsafe {
        indirect_jit
            .buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>("entry")
            .expect("indirect entry symbol")
    };
    let direct_entry = unsafe {
        direct_jit
            .buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>("entry")
            .expect("direct entry symbol")
    };
    let overridden_direct_entry = unsafe {
        overridden_direct_jit
            .buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>("entry")
            .expect("overridden direct entry symbol")
    };

    for input in [i64::MIN + 1, -41, -1, 0, 1, 41, i64::MAX - 1] {
        let indirect_result = indirect_entry.as_ref()(input);
        let direct_result = direct_entry.as_ref()(input);
        let overridden_direct_result = overridden_direct_entry.as_ref()(input);
        assert_eq!(indirect_result, direct_result);
        assert_eq!(indirect_result, input + 1);
        assert_eq!(overridden_direct_result, input.wrapping_sub(1000));
        assert_ne!(indirect_result, overridden_direct_result);
    }
}

#[test]
fn aot_allows_interposable_global_function_pointer_and_ordinary_direct_call() {
    let mut global_indirect = call_module(true);
    global_indirect.functions[0].linkage = Linkage::External;
    let mut global_direct = call_module(false);
    global_direct.functions[0].linkage = Linkage::External;
    let mut config = CompilerConfig::for_host_jit_unchecked();
    config.trace_level = CompilerTraceLevel::Full;

    // Global linkage intentionally permits linker interposition, so it is not
    // an exact-module candidate and must retain its ordinary AOT semantics.
    let indirect_object = Compiler::new(config.clone())
        .with_codegen_license(permit_unlicensed())
        .compile(&global_indirect)
        .expect("interposable global function-pointer call remains supported");
    assert_one_incompatible_static_target(indirect_object.trace.as_ref().expect("object trace"));
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile(&global_direct)
        .expect("ordinary global direct call remains supported");
}

#[cfg(target_arch = "aarch64")]
#[test]
fn aarch64_jit_refuses_external_fndef_address_fixup_before_publication() {
    let mut global_indirect = call_module(true);
    global_indirect.functions[0].linkage = Linkage::External;
    let malicious_externs = HashMap::from([(
        "add_one".to_string(),
        malicious_add_one_override as *const () as *const u8,
    )]);

    let error = Compiler::new(CompilerConfig::for_host_jit_unchecked())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&global_indirect, &malicious_externs)
        .expect_err("unsupported address fixup must fail before an executable buffer is returned");
    assert!(
        matches!(
            error,
            CompileError::Jit(JitError::RawJitNamedSymbolAddressFixupUnsupported {
                ref symbol,
                kind: trust_cg_codegen::macho::reloc::AArch64RelocKind::Page21,
                ..
            }) if symbol == "add_one"
        ),
        "unexpected raw-JIT address-fixup refusal: {error}"
    );
}

#[test]
fn intrinsic_like_local_fndef_is_exact_in_jit_and_local_or_refused_in_aot() {
    let mut module = call_module(true);
    // The actual source body computes x + 1. Its local FuncId owns that
    // semantics even though the symbol spelling resembles a legacy intrinsic.
    module.functions[0].name = "llvm.bitreverse.i64".to_string();
    let mut config = CompilerConfig::for_host_jit_unchecked();
    config.trace_level = CompilerTraceLevel::Full;

    let mut aot_config = config.clone();
    aot_config.emit_proofs = true;
    for triple in UNBOUND_OBJECT_TRIPLES {
        let error = compiler_for(triple, aot_config.clone())
            .compile(&module)
            .expect_err("local FnDef identity must be refused before AOT object/proof emission");
        assert!(
            matches!(
                error,
                CompileError::AotStaticFunctionIdentityBindingUnsupported {
                    candidate_count: 1,
                    ..
                }
            ),
            "unexpected AOT refusal for {triple}: {error}"
        );
    }
    // On AArch64 ELF and Mach-O the intrinsic-like spelling is the object's
    // own local definition, which the FnDef address names.
    for triple in LOCAL_BINDING_TRIPLES {
        let object = compiler_for(triple, config.clone())
            .compile(&module)
            .unwrap_or_else(|error| panic!("{triple} local FnDef: {error}"))
            .object_code;
        assert_local_function_symbol(triple, &object, "llvm.bitreverse.i64");
    }

    let malicious_externs = HashMap::from([(
        "llvm.bitreverse.i64".to_string(),
        malicious_add_one_override as *const () as *const u8,
    )]);
    let jit = Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module, &malicious_externs)
        .expect("intrinsic-like local FnDef JITs through exact module binding");
    assert_one_static_devirtualization(jit.trace.as_ref().expect("JIT trace"));
    let entry = unsafe {
        jit.buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>("entry")
            .expect("entry symbol")
    };
    for input in [-41, -1, 0, 1, 41] {
        assert_eq!(entry.as_ref()(input), input + 1);
        assert_ne!(entry.as_ref()(input), malicious_add_one_override(input));
    }
}

#[test]
fn aot_pre_cache_census_rejects_escaped_fndef_and_empty_closure_identities_off_aarch64_objects() {
    let cache_root = |label: &str| {
        std::env::temp_dir().join(format!(
            "trust-cg-static-identity-pre-cache-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock")
                .as_nanos()
        ))
    };
    // The empty-closure spelling of the escaped identity (a `Closure`
    // constant at `Ty::Func`) is not valid trust-ir: since WS7.3 it is refused
    // at ingestion on every target, before any census, cache or object.
    let closure = escaped_local_identity_module(true);
    for triple in UNBOUND_OBJECT_TRIPLES
        .iter()
        .copied()
        .chain(LOCAL_BINDING_TRIPLES)
    {
        // TrustIR's typed admission, which every compiling entry consumes,
        // refuses it by name (`ConstTypeMismatch` is one of the findings the
        // adapter names, so the refusal keeps the adapter's spelling).
        let error = compiler_for(triple, CompilerConfig::default())
            .compile(&closure)
            .expect_err("a capture-free closure at `Ty::Func` is refused");
        assert_eq!(
            error.to_string(),
            "adapter error: trust-ir codegen admission refused the module: function \
             'entry' bb0: const type mismatch: expected functy.0, got closure<func.0>[0]",
            "{triple}"
        );
    }
    {
        let module = escaped_local_identity_module(false);
        let kind = "fndef";
        let config = CompilerConfig {
            emit_proofs: true,
            ..Default::default()
        };
        for triple in UNBOUND_OBJECT_TRIPLES {
            let root = cache_root(kind);
            let error = compiler_for(triple, config.clone())
                .with_compile_artifact_cache(test_cache_config(&root))
                .compile(&module)
                .expect_err("an escaped local identity must fail before cache/object/proof output");
            assert!(
                matches!(
                    error,
                    CompileError::AotStaticFunctionIdentityBindingUnsupported {
                        candidate_count: 1,
                        ..
                    }
                ),
                "unexpected escaped-identity refusal for {triple}: {error}"
            );
            assert!(
                !root.exists(),
                "pre-cache identity refusal must not create cache output at {}",
                root.display()
            );
        }

        // AArch64 ELF and Mach-O compile the escaped identity; the
        // post-emission binding check reads the stored object and, on the
        // second compile, the object taken from the cache.
        for triple in LOCAL_BINDING_TRIPLES {
            let root = cache_root(&format!("{kind}-{triple}"));
            let compile = || {
                compiler_for(triple, CompilerConfig::default())
                    .with_compile_artifact_cache(test_cache_config(&root))
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("{triple} escaped {kind}: {error}"))
            };
            let stored = compile();
            let reused = compile();
            assert_eq!(stored.object_code, reused.object_code, "{kind}");
            // An ambient legacy control (for example `TCG_REQUIRE_LLD` on a native
            // floor) disables artifact reuse altogether; the hit is then absent
            // by design.
            let reuse = trust_cg_codegen::artifact_reuse_permit().is_some();
            assert_eq!(
                reused
                    .compile_artifact_cache_telemetry
                    .iter()
                    .any(|row| row.status == CompileArtifactCacheStatus::Hit),
                reuse,
                "{kind}: the second compile reuses the cached object exactly when reuse is \
             permitted: {:?}",
                reused.compile_artifact_cache_telemetry
            );
            assert_local_function_symbol(triple, &reused.object_code, "add_one");
            std::fs::remove_dir_all(&root).ok();
        }
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
