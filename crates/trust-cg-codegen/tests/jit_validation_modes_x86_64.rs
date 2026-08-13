// trust-cg-codegen/tests/jit_validation_modes_x86_64.rs
//
// JIT-5: three-stage JIT validation modes (Unchecked / CachedVerified /
// AlwaysVerify) exercised on the x86-64 host JIT (the runnable path on this
// Intel host). Covers the M4 gate criteria that are checkable here:
//
//   (a) the default x86 JIT mode resolves to CachedVerified;
//   (b) executing an uncertified byte requires TCG_JIT_UNCHECKED=1 (fail-closed
//       otherwise) — the negative test;
//   (c) a warm content-hash cache hit does NOT re-run the verifier;
//   (d) a cache MISS re-verifies (never skips);
//   plus: AlwaysVerify bypasses the cache, and a warm-latency micro-measurement.
//
// The aarch64 JitCertificate path + on-device execution are M-series-flagged
// (JIT-11 / A64-8); they are cfg-gated out here.

#![cfg(all(target_arch = "x86_64", feature = "verify"))]

use std::collections::HashMap;
use std::sync::Arc;

use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig, JitValidationMode};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::jit_cert::JitCertCache;
use trust_cg_codegen::target::Target;

use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty as TrustIrTy,
    ValueId,
};

// ---------------------------------------------------------------------------
// Module builders
// ---------------------------------------------------------------------------

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
fn f(n: u32) -> FuncId {
    FuncId::new(n)
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn func_ty(params: Vec<TrustIrTy>, returns: Vec<TrustIrTy>) -> FuncTy {
    FuncTy {
        params,
        returns,
        is_vararg: false,
    }
}

fn single_function_module(
    func_id: u32,
    name: &str,
    ty: FuncTy,
    blocks: Vec<TrustIrBlock>,
) -> TrustIrModule {
    let entry = blocks.first().expect("module must have a block").id;
    let mut module = TrustIrModule::new(format!("{name}_module"));
    let func_ty_id: FuncTyId = module.add_func_type(ty);
    let mut func = TrustIrFunction::new(f(func_id), name, func_ty_id, entry);
    func.blocks = blocks;
    module.add_function(func);
    module
}

/// `fn answer() -> i64 { <value> }` — a fully cert-covered scalar function.
fn build_scalar_const_module(func_id: u32, name: &str, value: i64) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![], vec![TrustIrTy::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(value as i128),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Return { values: vec![v(0)] }),
            ],
        }],
    )
}

fn v2i64_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I64), 2)
}

/// `fn pack(a: i64, b: i64) -> <2 x i64>` via the SIMD `vector.pack_lanes`
/// dialect op. This lowers fine (passes ISel + dataflow-integrity + carrier
/// hygiene) but its packed SSE opcodes are NOT yet covered by a per-instruction
/// proof, so CachedVerified fails it closed while Unchecked runs it.
fn build_v2i64_pack_module(func_id: u32, name: &str) -> TrustIrModule {
    let vector_ty = v2i64_ty();
    single_function_module(
        func_id,
        name,
        func_ty(
            vec![TrustIrTy::I64, TrustIrTy::I64],
            vec![vector_ty.clone()],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::I64), (v(1), TrustIrTy::I64)],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(vector_ty, [v(0), v(1)]),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::Return {
                    values: vec![v(10)],
                }),
            ],
        }],
    )
}

// ---------------------------------------------------------------------------
// Thread-local override: TCG_JIT_UNCHECKED is isolated from sibling tests.
// ---------------------------------------------------------------------------

/// Run `f` with `TCG_JIT_UNCHECKED` set to `value` (or removed when `None`),
/// restoring the previous thread-local override afterwards, including on panic.
fn with_unchecked_env<R>(value: Option<&str>, f: impl FnOnce() -> R) -> R {
    match value {
        Some(v) => env_lock::with_env_overrides(&[("TCG_JIT_UNCHECKED", v)], f),
        None => env_lock::with_env_overrides_removed(&["TCG_JIT_UNCHECKED"], f),
    }
}

// ---------------------------------------------------------------------------
// (a) default x86 JIT mode resolves to CachedVerified
// ---------------------------------------------------------------------------

#[test]
fn x86_default_host_jit_mode_is_cached_verified() {
    // Pure config query — deliberately env-independent (M4 gate).
    assert_eq!(
        CompilerConfig::for_host_jit().jit_validation_mode(),
        JitValidationMode::CachedVerified,
        "for_host_jit() on x86-64 must default to CachedVerified"
    );
    assert_eq!(
        CompilerConfig::jit_fast(Target::X86_64).jit_validation_mode(),
        JitValidationMode::CachedVerified,
        "jit_fast(X86_64) must default to CachedVerified"
    );
    assert_eq!(
        Compiler::for_host().config().jit_validation_mode(),
        JitValidationMode::CachedVerified
    );

    // emit_proofs still maps to the strongest mode (former ProofRequired).
    let always = CompilerConfig {
        emit_proofs: true,
        ..CompilerConfig::for_host_jit()
    };
    assert_eq!(
        always.jit_validation_mode(),
        JitValidationMode::AlwaysVerify
    );

    // Explicit override wins over the arch default.
    assert_eq!(
        CompilerConfig::for_host_jit_unchecked().jit_validation_mode(),
        JitValidationMode::Unchecked
    );
}

// ---------------------------------------------------------------------------
// CachedVerified certifies every published byte (positive path)
// ---------------------------------------------------------------------------

#[test]
fn x86_cached_verified_certifies_every_published_byte() {
    with_unchecked_env(None, || {
        let module = build_scalar_const_module(1, "answer", 42);
        let result = Compiler::for_host()
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("scalar const module must certify under CachedVerified");

        let validation = result.validation.as_ref().expect("validation provenance");
        assert_eq!(validation.mode, JitValidationMode::CachedVerified);
        assert!(
            validation.every_byte_certified(),
            "every published byte must be covered by a verified certificate: {validation:?}"
        );
        assert!(!validation.published_image_sha256.is_empty());
        // Certs bind to the published image: each function records a bytes hash.
        assert!(
            validation
                .functions
                .iter()
                .all(|f| !f.bytes_sha256.is_empty())
        );
        assert!(result.proofs.as_ref().is_some_and(|p| !p.is_empty()));

        let answer: extern "C" fn() -> i64 =
            unsafe { result.buffer.get_fn_bound("answer").unwrap().into_inner() };
        assert_eq!(answer(), 42);
    });
}

// ---------------------------------------------------------------------------
// (b) executing an uncertified byte requires TCG_JIT_UNCHECKED=1
// ---------------------------------------------------------------------------

#[test]
fn x86_uncertified_execution_requires_unchecked_env_optin() {
    with_unchecked_env(None, || {
        let cfg = CompilerConfig::for_host_jit();

        // Without the env, the default path can NEVER resolve to Unchecked:
        // there is no way to reach uncertified execution implicitly.
        assert_eq!(
            cfg.resolve_jit_validation_mode().unwrap(),
            JitValidationMode::CachedVerified
        );

        // A module whose SIMD bytes are not yet cert-covered FAILS CLOSED under
        // the default (CachedVerified) mode — it is never published/executed.
        let module = build_v2i64_pack_module(2, "pack_uncertified");
        let err = Compiler::for_host()
            .compile_module_to_jit(&module, &HashMap::new())
            .expect_err("uncertified SIMD bytes must fail closed under CachedVerified");
        match err {
            CompileError::ProofPromotionRejected { target, reason } => {
                assert_eq!(target, Target::X86_64);
                assert!(
                    reason.contains("UNCERTIFIED") || reason.contains("promotion"),
                    "rejection must cite the uncertified-byte gate: {reason}"
                );
            }
            other => panic!("expected ProofPromotionRejected, got {other}"),
        }
    });

    // WITH the env, the default path downgrades to Unchecked and the SAME
    // uncertified module compiles and runs.
    with_unchecked_env(Some("1"), || {
        let cfg = CompilerConfig::for_host_jit();
        assert_eq!(
            cfg.resolve_jit_validation_mode().unwrap(),
            JitValidationMode::Unchecked,
            "TCG_JIT_UNCHECKED=1 must downgrade the default path to Unchecked"
        );

        let module = build_v2i64_pack_module(3, "pack_unchecked");
        let result = Compiler::for_host()
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("Unchecked (env opt-in) must publish uncertified bytes");
        let validation = result.validation.as_ref().expect("validation provenance");
        assert_eq!(validation.mode, JitValidationMode::Unchecked);
        assert!(
            !validation.every_byte_certified(),
            "Unchecked path publishes uncertified bytes"
        );
        assert!(result.proofs.is_none());

        // It really executes (uncertified).
        #[allow(improper_ctypes_definitions)]
        type Run = extern "C" fn(i64, i64) -> std::arch::x86_64::__m128i;
        let run: Run = unsafe {
            result
                .buffer
                .get_fn_bound("pack_unchecked")
                .unwrap()
                .into_inner()
        };
        let packed = run(7, 9);
        let lanes: [i64; 2] = unsafe { std::mem::transmute(packed) };
        assert_eq!(lanes[0], 7, "lane 0 must be the first arg");
    });
}

// ---------------------------------------------------------------------------
// (c) warm-cache hit does NOT re-run the verifier
// ---------------------------------------------------------------------------

#[test]
fn x86_warm_cache_hit_does_not_respawn_verifier() {
    with_unchecked_env(None, || {
        let cache = Arc::new(JitCertCache::new());
        let compiler = Compiler::for_host().with_jit_cert_cache(cache.clone());
        let module = build_scalar_const_module(4, "warm_answer", 7);

        // Cold compile: miss -> verifier runs.
        compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("cold CachedVerified compile");
        let (hits1, misses1, _rev1, verifier1) = cache.stats();
        assert_eq!(misses1, 1, "cold compile is a miss");
        assert_eq!(verifier1, 1, "cold compile runs the verifier once");
        assert_eq!(hits1, 0);

        // Warm compile of the SAME module: hit -> verifier must NOT run again.
        compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("warm CachedVerified compile");
        let (hits2, misses2, _rev2, verifier2) = cache.stats();
        assert_eq!(
            verifier2, verifier1,
            "warm cache hit must NOT re-spawn the verifier (verifier_runs unchanged)"
        );
        assert_eq!(misses2, misses1, "warm compile is not a miss");
        assert_eq!(hits2, 1, "warm compile is a content-hash hit");
    });
}

// ---------------------------------------------------------------------------
// (d) a cache MISS re-verifies (never skips)
// ---------------------------------------------------------------------------

#[test]
fn x86_cache_miss_reverifies_not_skips() {
    with_unchecked_env(None, || {
        let cache = Arc::new(JitCertCache::new());
        let compiler = Compiler::for_host().with_jit_cert_cache(cache.clone());

        let m1 = build_scalar_const_module(5, "miss_a", 11);
        compiler
            .compile_module_to_jit(&m1, &HashMap::new())
            .expect("compile miss_a");
        let (_h1, misses1, _r1, verifier1) = cache.stats();
        assert_eq!(misses1, 1);
        assert_eq!(verifier1, 1);

        // Different content => different content hash => MISS => re-verify.
        let m2 = build_scalar_const_module(6, "miss_b", 22);
        compiler
            .compile_module_to_jit(&m2, &HashMap::new())
            .expect("compile miss_b");
        let (_h2, misses2, _r2, verifier2) = cache.stats();
        assert_eq!(misses2, 2, "distinct content must MISS, not silently reuse");
        assert_eq!(verifier2, 2, "a miss re-verifies (never skips)");
    });
}

// ---------------------------------------------------------------------------
// AlwaysVerify bypasses the cache
// ---------------------------------------------------------------------------

#[test]
fn x86_always_verify_never_serves_from_cache() {
    with_unchecked_env(None, || {
        let cache = Arc::new(JitCertCache::new());
        let cfg = CompilerConfig {
            jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
            ..CompilerConfig::for_host_jit()
        };
        let compiler = Compiler::new(cfg).with_jit_cert_cache(cache.clone());
        let module = build_scalar_const_module(7, "paranoid", 5);

        compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("AlwaysVerify compile 1");
        compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("AlwaysVerify compile 2");

        let (hits, _m, _r, _v) = cache.stats();
        assert_eq!(
            hits, 0,
            "AlwaysVerify must never serve a verdict from cache"
        );
    });
}

// ---------------------------------------------------------------------------
// Warm-latency micro-measurement (LOADED-labeled, informational + soft bar)
// ---------------------------------------------------------------------------

#[test]
fn x86_cached_verified_warm_latency_overhead_reported() {
    with_unchecked_env(None, || {
        use std::time::Instant;
        let module = build_scalar_const_module(8, "kernel", 99);

        // Baseline: Unchecked (no verification), the pre-JIT-5 jit_fast cost.
        let unchecked = Compiler::new(CompilerConfig::for_host_jit_unchecked());
        // Warm the process once so page-faults/JIT engine init are amortized.
        let _ = unchecked.compile_module_to_jit(&module, &HashMap::new());
        let iters = 40u32;
        let t0 = Instant::now();
        for _ in 0..iters {
            unchecked
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("unchecked compile");
        }
        let unchecked_ns = t0.elapsed().as_nanos() as f64 / iters as f64;

        // CachedVerified with a WARM shared cache (steady-state production).
        let cache = Arc::new(JitCertCache::new());
        let cv = Compiler::for_host().with_jit_cert_cache(cache.clone());
        cv.compile_module_to_jit(&module, &HashMap::new())
            .expect("prime cache");
        let t1 = Instant::now();
        for _ in 0..iters {
            cv.compile_module_to_jit(&module, &HashMap::new())
                .expect("cached-verified compile");
        }
        let warm_ns = t1.elapsed().as_nanos() as f64 / iters as f64;

        let overhead_pct = (warm_ns - unchecked_ns) / unchecked_ns * 100.0;
        eprintln!(
            "[LOADED] JIT-5 warm-latency: unchecked={:.1}us cached_verified_warm={:.1}us \
             overhead={:.1}% (kernel=scalar-const, iters={})",
            unchecked_ns / 1000.0,
            warm_ns / 1000.0,
            overhead_pct,
            iters,
        );
        // Confirm warm hits actually happened (steady-state, no re-discharge).
        let (hits, _m, _r, _v) = cache.stats();
        assert!(hits >= iters as u64, "warm loop must be served from cache");
    });
}
