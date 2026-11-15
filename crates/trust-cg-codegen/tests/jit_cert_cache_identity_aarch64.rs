// Native AArch64 JIT certificate-cache identity, warm-hit and stale-input
// controls.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The aarch64 port of `jit_cert_cache_identity_x86_64` and the cache legs of
// `jit_validation_modes_x86_64`. Each control either reuses one verdict across
// genuinely identical proof inputs or refuses reuse across distinct ones:
//
// * a same-process CachedVerified warm hit through `compile_module_to_jit`
//   reuses the cold verdict without re-running the verifier, and both
//   buffers execute the exhaustive 8-bit input domain;
// * a function-name change keeps the certified machine bytes identical but
//   binds a distinct verifier input, so it may not hit; a relocation-target
//   change does the same for a raw tail call, whose `B` row has no credit
//   route since E0.2, so its verdict is never stored and the binding is
//   pinned at the verifier-input digest the cache key carries;
// * a raw-MachIR request (no source) and a source-bound request over the same
//   bytes never share a verdict in either direction;
// * a source-swapped LIR (zero- replaced by sign-extension) no longer matches
//   the captured report and cannot be promoted, and a source-less request is
//   not promotable under the source-bound policy;
// * AlwaysVerify never serves from a warm shared cache, a deep verifier
//   override neither reads nor populates it, and CachedVerified caches no
//   entry for bytes it cannot certify.
//
// The certified function is `zext i8 -> i32`: its one obligation is checked
// exhaustively over all 256 inputs, so no external certificate is involved.
// Outer-cache reuse still requires the discovered AY/Clean verification
// authority (a reusable request identity); its absence fails this target
// instead of skipping it. This is cache-identity and native execution
// evidence, not source-to-installed-bytes correctness.

#![cfg(all(target_arch = "aarch64", feature = "verify"))]

#[path = "common/pinned_target.rs"]
mod pinned_target;

use std::collections::HashMap;
use std::sync::Arc;

use trust_cg_codegen::compiler::{
    CompileError, Compiler, CompilerConfig, JitCompilationResult, JitFunctionValidation,
    JitValidationMode,
};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::jit_cert::JitCertCache;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_cg_ir::aarch64_regs::W0;
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature, Type};
use trust_ir::inst::CastOp;
use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId};

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

/// Run with the production cache policy and a synchronous authority identity,
/// and require that authority: without it every outer-cache control below
/// would be vacuous.
fn with_cache_authority<T>(run: impl FnOnce() -> T) -> T {
    env_lock::with_env_overrides_removed(CACHE_POLICY_ENV, || {
        env_lock::with_env_overrides(&[("TCG_BLOCKING_IDENTITY", "1")], || {
            assert!(
                trust_cg_verify::jit_verification_authority_id_if_ready().is_some(),
                "these controls require the discovered AY/Clean verification authority; \
                 an unavailable authority is a failure, not a pass ({})",
                trust_cg_verify::ay_bridge::solver_refusal_note()
                    .unwrap_or_else(|| "an AY is admitted in this process".to_owned())
            );
            run()
        })
    })
}

fn cast_module(name: &str, op: CastOp) -> Module {
    let mut module = Module::new("jit_cache_identity_aarch64");
    pinned_target::pin(&mut module, pinned_target::host_triple());
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I8],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), name, signature, BlockId::new(0));
    function.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I8)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn zext_module(name: &str) -> Module {
    cast_module(name, CastOp::ZExt)
}

fn cached_compiler(cache: &Arc<JitCertCache>, mode: JitValidationMode) -> Compiler {
    Compiler::new(CompilerConfig {
        opt_level: OptLevel::O1,
        parallel: false,
        jit_validation_mode_override: Some(mode),
        ..CompilerConfig::jit_fast(Target::Aarch64)
    })
    .with_codegen_license(permit_unlicensed())
    .with_jit_cert_cache(Arc::clone(cache))
}

fn row(result: &JitCompilationResult, function: &str) -> JitFunctionValidation {
    result
        .validation
        .as_ref()
        .expect("verifying compilation exposes validation provenance")
        .functions
        .iter()
        .find(|row| row.function == function)
        .unwrap_or_else(|| panic!("missing validation row for {function}"))
        .clone()
}

/// Execute every 8-bit input; returns the number of native calls.
fn execute_zext(result: &JitCompilationResult, name: &str) -> usize {
    // SAFETY: the module fixes `extern "C" fn(i8) -> i32`; `result` outlives
    // the borrowed handle and every call.
    let function = unsafe {
        result
            .buffer
            .get_fn_bound::<extern "C" fn(i8) -> i32>(name)
            .expect("published symbol")
    };
    for byte in 0..=u8::MAX {
        assert_eq!((function.as_ref())(byte as i8), i32::from(byte));
    }
    256
}

fn host_triple() -> &'static str {
    if cfg!(target_os = "macos") {
        "aarch64-apple-darwin"
    } else {
        "aarch64-unknown-linux-gnu"
    }
}

/// The public source-to-machine preparation for `module`'s only function.
fn prepared(module: &Module) -> (trust_cg_lower::Function, MachFunction) {
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .expect("translate the source");
    let machine = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O1,
        target_triple: host_triple().into(),
        verify: false,
        ..Default::default()
    })
    .prepare_function(&lir)
    .expect("prepare the machine function");
    (lir, machine)
}

fn raw_compiler(cache: &Arc<JitCertCache>) -> JitCompiler {
    JitCompiler::new(JitConfig {
        verify: true,
        cache_certificates: true,
        ..JitConfig::default()
    })
    .with_certificate_cache(Arc::clone(cache))
}

extern "C" fn shared_host_target(value: i32) -> i32 {
    value.wrapping_add(17)
}

/// `SXTB W0, W0; B <callee>`: a diagnostic tail-call fixture whose only
/// symbolic relocation names `callee`. Its unverified verdict is not cached.
fn tail_call_function(callee: &str) -> MachFunction {
    let mut function = MachFunction::new(
        "tail_caller".to_owned(),
        Signature::new(vec![Type::I32], vec![Type::I32]),
    );
    let entry = function.entry;
    let extension = function.push_inst(MachInst::new(
        AArch64Opcode::Sxtb,
        vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
    ));
    function.append_inst(entry, extension);
    let tail = function.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Symbol(callee.to_owned())],
    ));
    function.append_inst(entry, tail);
    function
}

// ---------------------------------------------------------------------------
// Positive reuse
// ---------------------------------------------------------------------------

#[test]
fn cached_verified_warm_hit_reuses_the_verdict_and_both_buffers_execute() {
    with_cache_authority(|| {
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(&cache, JitValidationMode::CachedVerified);
        let module = zext_module("warm_zext");

        let cold = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("cold CachedVerified compile certifies");
        assert_eq!(
            cache.stats(),
            (0, 1, 0, 1),
            "cold: one miss, one verifier run"
        );
        let warm = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("warm CachedVerified compile certifies");
        assert_eq!(
            cache.stats(),
            (1, 1, 0, 1),
            "warm: a hit that does not re-run the verifier"
        );

        let (cold_row, warm_row) = (row(&cold, "warm_zext"), row(&warm, "warm_zext"));
        assert!(cold_row.verified && warm_row.verified);
        assert!(!cold_row.cache_hit && warm_row.cache_hit);
        assert_eq!(cold_row.bytes_sha256, warm_row.bytes_sha256);
        assert_eq!(
            cold_row.verifier_input_sha256,
            warm_row.verifier_input_sha256
        );
        let warm_certificate = warm.buffer.certificate("warm_zext").unwrap();
        assert!(warm_certificate.is_verified() && warm_certificate.served_from_cache());
        assert!(
            !cold
                .buffer
                .certificate("warm_zext")
                .unwrap()
                .served_from_cache()
        );
        assert_eq!(cold.buffer.code_slice(), warm.buffer.code_slice());
        assert_ne!(
            cold.buffer.code_slice().as_ptr(),
            warm.buffer.code_slice().as_ptr(),
            "the warm hit still publishes a fresh mapping"
        );
        let calls = execute_zext(&cold, "warm_zext") + execute_zext(&warm, "warm_zext");
        println!("JIT_CACHE_WARM_HIT hits=1 verifier_runs=1 native_calls={calls}");
    });
}

// ---------------------------------------------------------------------------
// Identity: distinct verifier inputs never share a verdict
// ---------------------------------------------------------------------------

#[test]
fn function_name_is_bound_even_when_published_machine_bytes_match() {
    with_cache_authority(|| {
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(&cache, JitValidationMode::CachedVerified);
        let first = compiler
            .compile_module_to_jit(&zext_module("same_layout_a"), &HashMap::new())
            .expect("first name variant certifies");
        let second = compiler
            .compile_module_to_jit(&zext_module("same_layout_b"), &HashMap::new())
            .expect("second name variant certifies");
        let (first, second) = (row(&first, "same_layout_a"), row(&second, "same_layout_b"));
        assert_eq!(first.bytes_sha256, second.bytes_sha256);
        assert_ne!(first.verifier_input_sha256, second.verifier_input_sha256);
        assert!(!first.cache_hit && !second.cache_hit);
        assert_eq!(cache.stats(), (0, 2, 0, 2));
    });
}

/// The relocation name is part of the verifier input, so two tail calls whose
/// bytes agree never share a cache key.
///
/// The `B <callee>` row's only obligation is the one L07-P2 builds from its
/// own word, which binds the word to the machine-IR operands, not to a source
/// instruction, and is not credit (E0.2). No symbol-bearing AArch64
/// instruction has a credit route today, so this certificate is not verified,
/// and CachedVerified stores no verdict for it: every compile is a miss and a
/// verifier run. The binding is pinned at the verifier-input digest, which
/// the cache key carries; the certified warm-hit leg is
/// `cached_verified_warm_hit_reuses_the_verdict_and_both_buffers_execute`. If
/// `B` gains a credit route, the first assertion below fails and this control
/// must again require a verified tail call and a cache hit on the repeated
/// name.
#[test]
fn relocation_target_name_is_bound_even_at_the_same_host_address() {
    use trust_cg_verify::function_verifier::{
        INSTRUCTION_DERIVED_IS_NOT_CREDIT, InstructionVerificationResult,
    };
    with_cache_authority(|| {
        let cache = Arc::new(JitCertCache::new());
        let compiler = raw_compiler(&cache);
        let mut rows = Vec::new();
        for callee in ["cache_host_foo", "cache_host_bar", "cache_host_foo"] {
            // Both names bind the same host function, so the veneer and the
            // caller's bytes are identical; only the relocation name differs.
            let externs = HashMap::from([(
                callee.to_owned(),
                shared_host_target as extern "C" fn(i32) -> i32 as *const u8,
            )]);
            let buffer = compiler
                .compile_raw(&[tail_call_function(callee)], &externs)
                .expect("the raw diagnostic tail call publishes");
            let certificate = buffer.certificate("tail_caller").unwrap().clone();
            assert!(
                !certificate.is_verified(),
                "{callee}: B gained a credit route; restore the certified reuse leg"
            );
            let report = trust_cg_verify::verify_function(&tail_call_function(callee));
            match &report.instructions[1].result {
                InstructionVerificationResult::Unverified { reason }
                    if reason.contains(INSTRUCTION_DERIVED_IS_NOT_CREDIT) => {}
                other => panic!("{callee}: the B row must be the uncredited word row: {other:?}"),
            }
            assert!(
                report.instructions[0].result.is_verified(),
                "{callee}: {report:?}"
            );
            // SAFETY: `SXTB W0, W0; B callee` with `callee: fn(i32) -> i32`.
            let function = unsafe {
                buffer
                    .get_fn_bound::<extern "C" fn(i32) -> i32>("tail_caller")
                    .unwrap()
            };
            for value in [0x7f, 0x80, 0xff, -1, i32::MIN] {
                assert_eq!(
                    (function.as_ref())(value),
                    i32::from(value as i8).wrapping_add(17)
                );
            }
            rows.push(certificate);
        }
        assert_eq!(
            rows[0].normalized_machine_code_sha256(),
            rows[1].normalized_machine_code_sha256()
        );
        assert_ne!(
            rows[0].verifier_input_sha256(),
            rows[1].verifier_input_sha256(),
            "a different relocation name must bind a different verifier input"
        );
        assert_eq!(
            rows[0].verifier_input_sha256(),
            rows[2].verifier_input_sha256(),
            "the repeated relocation name is the positive control"
        );
        assert!(rows.iter().all(|row| !row.served_from_cache()));
        assert_eq!(
            cache.stats(),
            (0, 3, 0, 3),
            "an uncertified verdict is never stored or served"
        );
        println!(
            "JIT_CACHE_RELOCATION_BINDING distinct_names_distinct_inputs=true \
             repeated_name_same_input=true uncertified_stored=0"
        );
    });
}

#[test]
fn raw_and_source_bound_requests_never_share_a_verdict() {
    with_cache_authority(|| {
        let module = zext_module("source_or_raw");
        let (_, machine) = prepared(&module);

        // Source-bound first, then the raw request over the same machine.
        let cache = Arc::new(JitCertCache::new());
        let bound = cached_compiler(&cache, JitValidationMode::CachedVerified)
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("source-bound compile certifies");
        let raw = raw_compiler(&cache)
            .compile_raw(std::slice::from_ref(&machine), &HashMap::new())
            .expect("raw compile publishes");
        let bound_row = row(&bound, "source_or_raw");
        let raw_certificate = raw.certificate("source_or_raw").unwrap();
        assert_eq!(
            raw_certificate.normalized_machine_code_sha256(),
            bound_row.bytes_sha256,
            "the controls compare one machine byte sequence"
        );
        assert_ne!(
            raw_certificate.verifier_input_sha256(),
            bound_row.verifier_input_sha256
        );
        assert!(!raw_certificate.served_from_cache());
        assert_eq!(cache.stats(), (0, 2, 0, 2));

        // Raw first, then source-bound.
        let cache = Arc::new(JitCertCache::new());
        let raw = raw_compiler(&cache)
            .compile_raw(std::slice::from_ref(&machine), &HashMap::new())
            .unwrap();
        assert!(
            !raw.certificate("source_or_raw")
                .unwrap()
                .served_from_cache()
        );
        let bound = cached_compiler(&cache, JitValidationMode::CachedVerified)
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("source-bound compile certifies");
        assert!(!row(&bound, "source_or_raw").cache_hit);
        assert_eq!(cache.stats(), (0, 2, 0, 2));
        execute_zext(&bound, "source_or_raw");
    });
}

#[test]
fn swapped_source_and_missing_source_cannot_reuse_or_promote_the_report() {
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
    use trust_cg_verify::{FunctionVerifier, VerificationConfig};

    with_cache_authority(|| {
        let (lir, machine) = prepared(&zext_module("swapped_source"));
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let captured = verifier.verify_with_request(&machine, Some(&lir), &request);
        assert!(captured.report().emitted_opcode_inventory().is_promotable());
        assert!(captured.reusable_for(&request));
        assert!(captured.matches_aarch64_input(&machine, Some(&lir)));
        let warm = verifier.verify_with_request(&machine, Some(&lir), &request);
        assert!(warm.reusable_for(&request));

        // Source-swapped: the same machine function now claims to implement a
        // sign extension. The old report must not match, and the swapped
        // source must not be promotable against the zero-extending bytes.
        let mut swapped = lir.clone();
        let mut rewritten = 0;
        for block in swapped.blocks.values_mut() {
            for instruction in &mut block.instructions {
                if let Opcode::Uextend { from_ty, to_ty } = &instruction.opcode {
                    instruction.opcode = Opcode::Sextend {
                        from_ty: from_ty.clone(),
                        to_ty: to_ty.clone(),
                    };
                    rewritten += 1;
                }
            }
        }
        assert_eq!(rewritten, 1, "the source holds exactly one zero extension");
        assert!(!captured.matches_aarch64_input(&machine, Some(&swapped)));
        assert!(
            !verifier
                .verify_with_request(&machine, Some(&swapped), &request)
                .report()
                .emitted_opcode_inventory()
                .is_promotable(),
            "sign-extension source must not certify zero-extending bytes"
        );

        // Missing source under the source-bound policy.
        assert!(!captured.matches_aarch64_input(&machine, None));
        assert!(
            !verifier
                .verify_with_request(&machine, None, &request)
                .report()
                .emitted_opcode_inventory()
                .is_promotable(),
            "a source-less request is not promotable under the enforced policy"
        );
    });
}

// ---------------------------------------------------------------------------
// Policy separation and bypass
// ---------------------------------------------------------------------------

#[test]
fn distinct_content_misses_and_reverifies() {
    with_cache_authority(|| {
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(&cache, JitValidationMode::CachedVerified);
        let zext = compiler
            .compile_module_to_jit(&zext_module("extend_a"), &HashMap::new())
            .expect("zero extension certifies");
        let sext = compiler
            .compile_module_to_jit(&cast_module("extend_a", CastOp::SExt), &HashMap::new())
            .expect("sign extension certifies");
        assert_ne!(
            row(&zext, "extend_a").bytes_sha256,
            row(&sext, "extend_a").bytes_sha256
        );
        assert!(!row(&sext, "extend_a").cache_hit);
        assert_eq!(
            cache.stats(),
            (0, 2, 0, 2),
            "a miss re-verifies, never skips"
        );
    });
}

#[test]
fn always_verify_never_serves_from_a_warm_shared_cache() {
    with_cache_authority(|| {
        let cache = Arc::new(JitCertCache::new());
        let module = zext_module("paranoid_zext");
        cached_compiler(&cache, JitValidationMode::CachedVerified)
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("populate the shared cache");
        assert_eq!(cache.stats(), (0, 1, 0, 1));
        let always = cached_compiler(&cache, JitValidationMode::AlwaysVerify);
        for run in 1..=2 {
            let result = always
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("AlwaysVerify certifies afresh");
            assert!(!row(&result, "paranoid_zext").cache_hit);
            let (hits, misses, _, verifier_runs) = cache.stats();
            assert_eq!(
                (hits, misses),
                (0, 1),
                "AlwaysVerify neither reads nor misses"
            );
            assert_eq!(
                verifier_runs,
                1 + run,
                "every AlwaysVerify compile re-verifies"
            );
        }
    });
}

#[test]
fn deep_verifier_override_bypasses_outer_cache_for_reads_and_writes() {
    with_cache_authority(|| {
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(&cache, JitValidationMode::CachedVerified);
        let module = zext_module("deep_override");
        compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("populate the cache");
        assert_eq!(cache.stats(), (0, 1, 0, 1));
        env_lock::with_env_overrides(&[("TCG_NO_PROOF_CACHE", "1")], || {
            for _ in 0..2 {
                // The exhaustive obligation needs no proof cache, so the
                // compile still certifies, but only through a fresh run.
                let result = compiler
                    .compile_module_to_jit(&module, &HashMap::new())
                    .expect("exhaustive evidence certifies without any proof cache");
                assert!(
                    !row(&result, "deep_override").cache_hit,
                    "a deep override must not read the outer cache"
                );
            }
        });
        let (hits, misses, _, verifier_runs) = cache.stats();
        assert_eq!(
            (hits, misses, verifier_runs),
            (0, 1, 3),
            "both overridden compiles verify afresh without touching the cache"
        );
        // The entry written before the override is still the only one, so
        // the next ordinary compile hits it.
        let result = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap();
        assert!(row(&result, "deep_override").cache_hit);
    });
}

#[test]
fn cached_verified_caches_nothing_for_bytes_it_cannot_certify() {
    with_cache_authority(|| {
        let cache = Arc::new(JitCertCache::new());
        let compiler = cached_compiler(&cache, JitValidationMode::CachedVerified);
        // A calling frame is outside the proof-supported JIT domain on every
        // host, so CachedVerified must refuse it and store nothing.
        let mut module = Module::new("uncertified_call");
        pinned_target::pin(&mut module, pinned_target::host_triple());
        let callee_signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let caller_signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::I8],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut callee = Function::new(
            FuncId::new(0),
            "cache_host_target",
            callee_signature,
            BlockId::new(0),
        );
        callee.linkage = trust_ir::Linkage::External;
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");
        let mut caller = Function::new(FuncId::new(1), "caller", caller_signature, BlockId::new(0));
        caller.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I8)],
            body: vec![
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::I8,
                    dst_ty: Ty::I32,
                    operand: ValueId::new(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(1)],
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(2)],
                }),
            ],
        });
        module
            .try_add_function(caller)
            .expect("Module::try_add_function: test fixture");
        let externs = HashMap::from([(
            "cache_host_target".to_owned(),
            shared_host_target as extern "C" fn(i32) -> i32 as *const u8,
        )]);
        for attempt in 1..=2u64 {
            match compiler.compile_module_to_jit(&module, &externs) {
                Err(CompileError::ProofPromotionRejected { target, .. }) => {
                    assert_eq!(target, Target::Aarch64);
                }
                Err(other) => panic!("expected ProofPromotionRejected, got {other}"),
                Ok(_) => panic!("an uncertified calling frame must never publish"),
            }
            let (hits, misses, _, verifier_runs) = cache.stats();
            assert_eq!(hits, 0, "a refused verdict is never served");
            assert_eq!(misses, attempt, "nothing was stored to hit");
            assert_eq!(verifier_runs, attempt, "each attempt re-verifies");
        }
        // The same module publishes only under the explicit Unchecked mode.
        let unchecked = cached_compiler(&cache, JitValidationMode::Unchecked)
            .compile_module_to_jit(&module, &externs)
            .expect("Unchecked publishes uncertified bytes");
        assert!(
            !unchecked
                .validation
                .as_ref()
                .unwrap()
                .every_function_semantics_verified()
        );
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
