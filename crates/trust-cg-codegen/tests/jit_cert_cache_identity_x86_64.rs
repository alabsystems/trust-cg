// Real-pipeline differentials for the x86-64 JIT certificate-cache identity.
//
// These tests deliberately keep the final machine layout equal where possible
// while changing verifier-visible or relocation-visible semantics. A cache hit
// in any of those pairs would reuse a verdict across distinct proof inputs.

#![cfg(all(target_arch = "x86_64", feature = "verify"))]

use std::collections::HashMap;
use std::sync::Arc;

use trust_cg_codegen::compiler::{
    Compiler, CompilerConfig, JitCompilationResult, JitFunctionValidation, JitValidationMode,
};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::jit_cert::JitCertCache;
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::inst::CastOp;
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage,
    Module, Ty, ValueId,
};

const CACHE_POLICY_ENV: &[&str] = &[
    "TCG_JIT_UNCHECKED",
    "TCG_PROVENANCE_XCHECK",
    "TCG_NO_VERDICT_DB",
    "TCG_NO_PROOF_CACHE",
    "TCG_NO_JIT_CERT_CACHE",
    "TCG_NO_SOLVER_SERVER",
    "AY_SOLVER_PATH",
    "TCG_EXTERNAL_CLEAN_CHECKER",
    "TCG_CLEAN_CHECKER",
    "TCG_PRECISE_CITATIONS",
    "TCG_BLOCKING_IDENTITY",
];

fn with_deterministic_cache_authority<T>(run: impl FnOnce() -> T) -> T {
    env_lock::with_env_overrides_removed(CACHE_POLICY_ENV, || {
        // The production default never blocks the JIT hot path on hashing the
        // solver binary. These cache-identity tests need a deterministic ready
        // authority so their miss/hit assertions do not depend on background
        // warm scheduling (or a dirty solver's deliberate no-warm policy).
        env_lock::with_env_overrides(&[("TCG_BLOCKING_IDENTITY", "1")], run)
    })
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

fn f(index: u32) -> FuncId {
    FuncId::new(index)
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn cached_compiler(cache: Arc<JitCertCache>, opt_level: OptLevel) -> Compiler {
    Compiler::new(CompilerConfig {
        opt_level,
        parallel: false,
        jit_validation_mode_override: Some(JitValidationMode::CachedVerified),
        ..CompilerConfig::for_host_jit()
    })
    .with_codegen_license(permit_unlicensed())
    .with_jit_cert_cache(cache)
}

fn validation_row(result: &JitCompilationResult, function: &str) -> JitFunctionValidation {
    result
        .validation
        .as_ref()
        .expect("CachedVerified compilation must expose validation provenance")
        .functions
        .iter()
        .find(|row| row.function == function)
        .unwrap_or_else(|| panic!("missing validation row for {function}"))
        .clone()
}

/// The semantic operation is solver-independent: `zext i8 -> i32` retains an
/// 8-bit verifier input and is genuinely exhaustive. The x86 ABI still emits
/// GPR32 argument/return copies, so whole-function proof promotion requires the
/// formal authority checked by [`formal_authority_available`].
fn exhaustive_cast_module(function: &str) -> Module {
    let mut module = Module::new("jit_cache_exhaustive_identity");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I8],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function_ir = Function::new(f(0), function, sig, b(0));
    function_ir.blocks.push(Block {
        id: b(0),
        params: vec![(v(0), Ty::I8)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });
    module
        .try_add_function(function_ir)
        .expect("Module::try_add_function: test fixture");
    module
}

fn external_call_module(callee_name: &str) -> Module {
    let mut module = Module::new("jit_cache_external_call_identity");
    let callee_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I8],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut declaration = Function::new(f(0), callee_name, callee_sig, b(0));
    declaration.linkage = Linkage::External;
    declaration.blocks.clear();
    module
        .try_add_function(declaration)
        .expect("Module::try_add_function: test fixture");

    let mut caller = Function::new(f(1), "call_shared_host", caller_sig, b(0));
    caller.blocks.push(Block {
        id: b(0),
        params: vec![(v(0), Ty::I8)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Call {
                callee: f(0),
                args: vec![v(1)],
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![v(2)] }),
        ],
    });
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

#[derive(Clone, Copy)]
enum StaticCallForm {
    OrdinaryDirect,
    RecoveredExact,
}

fn internal_call_module(form: StaticCallForm) -> Module {
    let mut module = Module::new("jit_cache_exact_binding_identity");
    let target_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I8],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I8],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut target = Function::new(f(0), "cache_internal_target", target_sig, b(0));
    target.linkage = Linkage::Internal;
    target.blocks.push(Block {
        id: b(0),
        params: vec![(v(0), Ty::I8)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    });
    module
        .try_add_function(target)
        .expect("Module::try_add_function: test fixture");

    let mut caller = Function::new(f(1), "cache_binding_caller", caller_sig, b(0));
    let body = match form {
        StaticCallForm::OrdinaryDirect => vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Call {
                callee: f(0),
                args: vec![v(0)],
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
        StaticCallForm::RecoveredExact => vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::Func(target_sig),
                value: Constant::FnDef(f(0)),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(target_sig),
                dst_ty: Ty::Ptr,
                operand: v(2),
            })
            .with_result(v(3)),
            InstrNode::new(Inst::CallIndirect {
                callee: v(3),
                sig: target_sig,
                args: vec![v(0)],
                calling_conv: CallingConv::C,
            })
            .with_result(v(4)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    };
    caller.blocks.push(Block {
        id: b(0),
        params: vec![(v(0), Ty::I8)],
        body,
    });
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

extern "C" fn shared_host_target(value: i32) -> i32 {
    value.wrapping_add(17)
}

fn externs_for(name: &str) -> HashMap<String, *const u8> {
    HashMap::from([(
        name.to_string(),
        shared_host_target as *const () as *const u8,
    )])
}

fn formal_authority_available() -> bool {
    trust_cg_verify::jit_verification_authority_id_if_ready().is_some()
}

/// Whether a live source-bound body replay can certify here: an
/// identity-admitted AY paired with a capable checker, with live replay not
/// refused. Unlike [`formal_authority_available`] (the outer cache's reuse
/// authority, withheld by design under `TCG_NO_PROOF_CACHE`), it does not
/// depend on any proof cache.
fn live_body_replay_available() -> bool {
    !std::env::var_os("TCG_REFINE_SOLVER").is_some_and(|value| value == "0")
        && trust_cg_verify::ay_bridge::admitted_proof_solver().is_some()
}

#[test]
fn function_name_is_bound_even_when_published_machine_bytes_match() {
    with_deterministic_cache_authority(|| {
        if !formal_authority_available() {
            return;
        }
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(cache.clone(), OptLevel::O0);

        let first = compiler
            .compile_module_to_jit(&exhaustive_cast_module("same_layout_a"), &HashMap::new())
            .expect("first name variant must certify");
        let second = compiler
            .compile_module_to_jit(&exhaustive_cast_module("same_layout_b"), &HashMap::new())
            .expect("second name variant must certify");

        let first = validation_row(&first, "same_layout_a");
        let second = validation_row(&second, "same_layout_b");
        assert_eq!(first.bytes_sha256, second.bytes_sha256);
        assert_ne!(first.verifier_input_sha256, second.verifier_input_sha256);
        assert!(!first.cache_hit && !second.cache_hit);
        assert_eq!(cache.stats(), (0, 2, 0, 2));
    });
}

#[test]
fn call_placeholder_binds_raw_target_name_even_at_the_same_host_address() {
    with_deterministic_cache_authority(|| {
        if !formal_authority_available() {
            return;
        }
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(cache.clone(), OptLevel::O0);

        let first = compiler
            .compile_module_to_jit(
                &external_call_module("cache_host_foo"),
                &externs_for("cache_host_foo"),
            )
            .expect("foo call variant must certify");
        let second = compiler
            .compile_module_to_jit(
                &external_call_module("cache_host_bar"),
                &externs_for("cache_host_bar"),
            )
            .expect("bar call variant must certify");

        let first = validation_row(&first, "call_shared_host");
        let second = validation_row(&second, "call_shared_host");
        assert_eq!(
            first.bytes_sha256, second.bytes_sha256,
            "same-address veneers should leave the caller byte range identical"
        );
        assert_ne!(first.verifier_input_sha256, second.verifier_input_sha256);
        assert!(!first.cache_hit && !second.cache_hit);
        assert_eq!(cache.stats(), (0, 2, 0, 2));
    });
}

#[test]
fn recovered_exact_and_ordinary_direct_calls_do_not_share_a_caller_verdict() {
    with_deterministic_cache_authority(|| {
        if !formal_authority_available() {
            return;
        }
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(cache.clone(), OptLevel::O0);

        let ordinary = compiler
            .compile_module_to_jit(
                &internal_call_module(StaticCallForm::OrdinaryDirect),
                &HashMap::new(),
            )
            .expect("ordinary direct-call module must certify");
        let exact = compiler
            .compile_module_to_jit(
                &internal_call_module(StaticCallForm::RecoveredExact),
                &HashMap::new(),
            )
            .expect("recovered exact-call module must certify");

        assert!(!validation_row(&ordinary, "cache_binding_caller").cache_hit);
        assert!(
            validation_row(&exact, "cache_internal_target").cache_hit,
            "the unchanged target is the control proving this is one shared cache"
        );
        assert!(
            !validation_row(&exact, "cache_binding_caller").cache_hit,
            "exact and interposable call bindings require distinct verdicts"
        );
        assert_eq!(cache.stats(), (1, 3, 0, 3));
    });
}

/// The ambient `TCG_PROVENANCE_XCHECK` diagnostic override cannot reach the JIT
/// proof boundary AT ALL: `X86JitVerificationPolicy::capture` pins
/// `ProvenanceXCheckMode::Enforce` unconditionally, so a `warn` request gets an
/// enforced cross-check, the same verdict, and therefore the same cache policy
/// key — one policy, one key, so the second compile is a HIT.
///
/// This replaces an assertion that the two forked into DISTINCT policy keys.
/// That was true while `capture()` read the override; it stopped being true when
/// the boundary was pinned to Enforce (`eddaa1423`), and the stale assertion
/// survived only because the compile failed closed on the 32-bit ABI copies
/// before reaching it. Pinning the ACTUAL contract is strictly stronger: it says
/// a diagnostic environment variable can neither weaken the proof boundary nor
/// fork its cache.
#[test]
fn provenance_xcheck_override_cannot_weaken_or_fork_the_jit_proof_boundary() {
    with_deterministic_cache_authority(|| {
        if !formal_authority_available() {
            return;
        }
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(cache.clone(), OptLevel::O0);
        let module = exhaustive_cast_module("provenance_policy");

        let warn = env_lock::with_env_overrides(&[("TCG_PROVENANCE_XCHECK", "warn")], || {
            compiler
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("warn-policy compile must certify")
        });
        let enforce = env_lock::with_env_overrides(&[("TCG_PROVENANCE_XCHECK", "enforce")], || {
            compiler
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("enforce-policy compile must certify")
        });

        let warn = validation_row(&warn, "provenance_policy");
        let enforce = validation_row(&enforce, "provenance_policy");
        assert_eq!(warn.bytes_sha256, enforce.bytes_sha256);
        assert_eq!(warn.verifier_input_sha256, enforce.verifier_input_sha256);
        assert!(
            !warn.cache_hit,
            "the first compile of a fresh cache is always a miss"
        );
        assert!(
            enforce.cache_hit,
            "the override never reached the boundary, so there is one policy key \
             and the second compile reuses the first verdict"
        );
        assert_eq!(
            cache.stats(),
            (1, 1, 0, 1),
            "one miss, one hit, and exactly ONE verifier run for the two compiles"
        );
    });
}

/// `TCG_NO_PROOF_CACHE=1` is a deep verifier override: the outer JIT
/// certificate cache is neither read nor written, and both compiles run the
/// verifier. What the verifier then decides depends on the host. The subject
/// (`zext i8 -> i32`) is inside the x86-64 source-bound body lane, whose
/// theorem is replayed live (no proof cache is involved), so where the
/// identity-admitted AY and a capable checker are available both compiles
/// certify through that replay and neither is served from the outer cache.
/// Without them the 32-bit ABI copies have no formal authority, and both
/// compiles fail closed. Either way the cache statistics are the same. (The
/// outer cache's reuse authority, [`formal_authority_available`], is withheld
/// under the override by design, so it cannot tell the two hosts apart.)
#[test]
fn deep_verifier_override_bypasses_outer_cache_for_reads_and_writes() {
    with_deterministic_cache_authority(|| {
        env_lock::with_env_overrides(&[("TCG_NO_PROOF_CACHE", "1")], || {
            let cache = Arc::new(JitCertCache::new());
            let compiler = cached_compiler(cache.clone(), OptLevel::O0);
            let module = exhaustive_cast_module("deep_override");

            let first = compiler.compile_module_to_jit(&module, &HashMap::new());
            let second = compiler.compile_module_to_jit(&module, &HashMap::new());

            if live_body_replay_available() {
                let first = first.expect("the live body replay certifies the first compile");
                let second = second.expect("the live body replay certifies the second compile");
                assert!(
                    !validation_row(&first, "deep_override").cache_hit
                        && !validation_row(&second, "deep_override").cache_hit,
                    "an active deep override must never serve a verdict from the outer cache"
                );
            } else {
                assert!(
                    first.is_err() && second.is_err(),
                    "without formal authority the 32-bit ABI copies are uncredited and must fail \
                     closed"
                );
            }
            assert_eq!(
                cache.stats(),
                (0, 0, 0, 2),
                "an active deep override must neither read nor populate the outer cache, but both fresh verifier runs must remain observable"
            );
        });
    });
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
