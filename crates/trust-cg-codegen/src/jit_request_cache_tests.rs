//! Required, opt-in real-tool campaign for raw-MachIR request-cache receipts.
//!
//! Run the ignored test explicitly with the four documented path/hash inputs.
//! An ordinary libtest run reports this campaign as ignored, not qualified.
//! The required invocation must observe one passed test, zero ignored tests,
//! and the final `TCG_RAW_JIT_REQUEST_CACHE` marker. No fake checker or public
//! receipt constructor is used. This is finite machine-IR/cache evidence, not
//! exact TrustIR lowering correspondence or end-to-end certified JIT evidence.
//!
//! `planted_receipts_under_the_victim_key_are_never_served` repeats the
//! receipt-rejection (cache-poisoning) controls by default on every AArch64
//! host with the discovered tools; it is not the pinned-identity campaign.

#![cfg(unix)]

use super::*;
use crate::compiler::{CompilerConfig, JitValidationMode};
use crate::jit::{ExecutableBuffer, JitCompiler, JitConfig, ProfileHookMode};
use crate::target::Target;
use std::io::Read;
use std::path::{Path, PathBuf};
use trust_cg_ir::aarch64_regs::W0;
use trust_cg_ir::{MachInst, MachOperand, Signature, Type};
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
use trust_cg_verify::{
    CapturedFunctionVerificationReport, FunctionVerificationRequest, FunctionVerifier,
};

const INPUTS: usize = 256;
const TOOL_ENV: [(&str, &str); 2] = [
    (
        "TCG_JIT_REQUEST_CACHE_AY",
        "TCG_JIT_REQUEST_CACHE_AY_SHA256",
    ),
    (
        "TCG_JIT_REQUEST_CACHE_CLEAN",
        "TCG_JIT_REQUEST_CACHE_CLEAN_SHA256",
    ),
];

struct RealTool {
    path: PathBuf,
    sha256: String,
}

fn sha256_file(path: &Path) -> String {
    let mut file = std::fs::File::open(path).expect("open the exact campaign artifact");
    let mut hash = Sha256::new();
    let mut chunk = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut chunk).expect("hash the campaign artifact");
        if count == 0 {
            break;
        }
        hash.update(&chunk[..count]);
    }
    format!("{:x}", hash.finalize())
}

fn required_tool(path_variable: &str, hash_variable: &str) -> RealTool {
    use std::os::unix::fs::PermissionsExt;

    let path = PathBuf::from(std::env::var_os(path_variable).unwrap_or_else(|| {
        panic!("required real-tool campaign needs {path_variable} and {hash_variable}")
    }))
    .canonicalize()
    .expect("the required tool path must resolve");
    let sha256 = std::env::var(hash_variable).expect("the expected tool digest is mandatory");
    assert!(
        sha256.len() == 64
            && sha256
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "{hash_variable} must be an independently supplied lowercase SHA-256"
    );
    let metadata = path.metadata().expect("read protected tool metadata");
    assert!(metadata.is_file());
    assert_ne!(metadata.permissions().mode() & 0o111, 0);
    assert_eq!(sha256_file(&path), sha256, "{path_variable} bytes changed");
    RealTool { path, sha256 }
}

fn place_package_link(prefix: &Path, name: &str, tool: &RealTool) {
    let directory = prefix.join("store").join(name).join("current/bin");
    std::fs::create_dir_all(&directory).expect("create private package-shaped test directory");
    let link = directory.join(name);
    std::os::unix::fs::symlink(&tool.path, &link)
        .expect("link, never overwrite, the protected tool");
    assert_eq!(link.canonicalize().unwrap(), tool.path);
    assert_eq!(sha256_file(&link), tool.sha256);
}

fn extension_function(name: &str, opcode: AArch64Opcode) -> MachFunction {
    let mut function = MachFunction::new(
        name.to_owned(),
        Signature::new(vec![Type::I32], vec![Type::I32]),
    );
    let entry = function.entry;
    let extension = function.push_inst(MachInst::new(
        opcode,
        vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
    ));
    function.append_inst(entry, extension);
    let ret =
        function.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[W0]));
    function.append_inst(entry, ret);
    function
}

fn assert_real_exhaustive_report(report: &CapturedFunctionVerificationReport) {
    let report = report.report();
    assert!(report.precondition_failure.is_none(), "{report:?}");
    assert_eq!(report.genuinely_verified_count(), 1, "{report:?}");
    assert_eq!(report.degenerate_verified_count(), 0, "{report:?}");
    assert_eq!(report.formally_credited_count(), 0, "{report:?}");
    assert_eq!(report.sampled_uncredited_count(), 0, "{report:?}");
    assert_eq!(report.registry_name_lookup_count(), 0, "{report:?}");
    assert_eq!(report.failed_count(), 0, "{report:?}");
    assert!(report.emitted_opcode_inventory().is_promotable());
    assert_eq!(
        report
            .instructions
            .iter()
            .filter(|row| matches!(
                row.result,
                InstructionVerificationResult::Verified {
                    strength: VerificationStrength::Exhaustive,
                    degenerate: false,
                    ..
                }
            ))
            .count(),
        1
    );
}

fn real_report(
    verifier: &FunctionVerifier,
    request: &FunctionVerificationRequest,
    function: &MachFunction,
) -> CapturedFunctionVerificationReport {
    let report = run_on_proof_verifier_stack("request-cache-campaign", || {
        verifier.verify_with_request(function, None, request)
    });
    assert_eq!(report.report().total(), 2);
    assert_real_exhaustive_report(&report);
    assert!(report.matches_aarch64_input(function, None));
    assert!(
        report.reusable_for(request),
        "real report must retain its request"
    );
    report
}

fn raw_compile(
    function: &MachFunction,
    cache: &Arc<JitCertCache>,
    cache_certificates: bool,
) -> ExecutableBuffer {
    JitCompiler::new(JitConfig {
        verify: true,
        cache_certificates,
        ..JitConfig::default()
    })
    .with_certificate_cache(Arc::clone(cache))
    .compile_raw(std::slice::from_ref(function), &HashMap::new())
    .expect("the required raw-MachIR campaign must compile without a fallback")
}

fn assert_certificate(buffer: &ExecutableBuffer, name: &str, hit: bool) {
    let certificate = buffer
        .certificate(name)
        .expect("verification must produce a certificate");
    assert!(certificate.is_verified());
    assert!(certificate.replay_check());
    assert_eq!(certificate.served_from_cache(), hit);
    assert!(
        certificate.lowering_certificate().is_none(),
        "no source proof is invented"
    );
    assert!(buffer.all_function_semantics_verified());
}

fn assert_native_byte_domain(buffer: &ExecutableBuffer, name: &str) {
    // SAFETY: the maintained body is exactly SXTB W0,W0; RET, its signature is
    // one i32 argument/result under the native AAPCS64, and `buffer` stays live
    // throughout every call. This does not cast a certificate into a function.
    let function = unsafe {
        buffer
            .get_fn_bound::<extern "C" fn(i32) -> i32>(name)
            .expect("the checked native symbol must exist")
    };
    for byte in 0..INPUTS {
        assert_eq!((function.as_ref())(byte as i32), (byte as u8 as i8) as i32);
    }
}

fn transport_entry(
    certificate: &JitCertificate,
    report: Option<CapturedFunctionVerificationReport>,
) -> CachedFunctionVerdict {
    CachedFunctionVerdict {
        x86_proof_certs: Vec::new(),
        aarch64_cert: Some(certificate.clone()),
        verification_report: report,
        x86_envelope_report: None,
    }
}

fn only_key(cache: &JitCertCache) -> JitCertCacheKey {
    let state = cache.state.lock().unwrap();
    assert_eq!(
        state.entries.len(),
        1,
        "fresh verification must actually store"
    );
    state.entries.keys().next().unwrap().clone()
}

fn wrong_architecture_report(
    request: &FunctionVerificationRequest,
) -> CapturedFunctionVerificationReport {
    use trust_cg_ir::X86Opcode;
    use trust_cg_ir::x86_64_regs::EAX;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

    let mut function = X86ISelFunction::new(
        "receipt_byte".to_owned(),
        trust_cg_lower::function::Signature {
            params: vec![trust_cg_lower::Type::I32],
            returns: vec![trust_cg_lower::Type::I32],
        },
    );
    function.ensure_block(Block(0));
    function.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovsxB,
            vec![X86ISelOperand::PReg(EAX), X86ISelOperand::PReg(EAX)],
        ),
    );
    // The same default configuration and explicit request isolate the arch
    // discriminator. No x86 native execution or promotion-mode claim is made.
    let verifier = trust_cg_verify::X86FunctionVerifier::new();
    let report = run_on_proof_verifier_stack("request-cache-x86-control", || {
        verifier.verify_with_request(&function, None, request)
    });
    assert_real_exhaustive_report(&report);
    assert!(report.matches_x86_input(&function, None, None));
    assert!(report.reusable_for(request));
    report
}

fn assert_payload_bounds(report: CapturedFunctionVerificationReport) {
    let make_entry = || CachedFunctionVerdict {
        x86_proof_certs: Vec::new(),
        aarch64_cert: None,
        verification_report: Some(report.clone()),
        x86_envelope_report: None,
    };
    let without_report = CachedFunctionVerdict {
        x86_proof_certs: Vec::new(),
        aarch64_cert: None,
        verification_report: None,
        x86_envelope_report: None,
    };
    assert_eq!(
        make_entry().estimated_payload_bytes(),
        without_report.estimated_payload_bytes() + report.estimated_payload_bytes()
    );
    assert!(report.estimated_payload_bytes() > 8192);
    let size = make_entry().estimated_payload_bytes() + std::mem::size_of::<JitCertCacheKey>();
    let key = JitCertCacheKey::new_for_verified_function(
        b"payload-transport-only",
        b"input",
        b"fixups",
        b"config",
        &[1; 32],
    );
    let other = JitCertCacheKey::new_for_verified_function(
        b"other-payload-transport",
        b"input",
        b"fixups",
        b"config",
        &[1; 32],
    );

    let too_small = JitCertCache::with_limits(true, 4, size - 1);
    too_small.store(key.clone(), make_entry());
    assert!(too_small.peek(&key).is_none());
    assert_eq!(too_small.state.lock().unwrap().resident_payload_bytes, 0);

    let bounded = JitCertCache::with_limits(true, 4, size);
    bounded.store(key.clone(), make_entry());
    assert!(bounded.peek(&key).is_some());
    assert_eq!(bounded.state.lock().unwrap().resident_payload_bytes, size);
    bounded.store(key.clone(), make_entry());
    assert_eq!(bounded.state.lock().unwrap().resident_payload_bytes, size);
    assert_eq!(
        bounded.evictions(),
        0,
        "replacing one entry must not double-charge"
    );
    bounded.store(other.clone(), make_entry());
    assert!(bounded.peek(&key).is_none());
    assert!(bounded.peek(&other).is_some());
    assert_eq!(bounded.state.lock().unwrap().resident_payload_bytes, size);
    assert_eq!(bounded.evictions(), 1);
}

#[test]
#[ignore = "requires the explicit real-tool raw-MachIR request-cache campaign"]
fn raw_machir_request_cache_real_exhaustive_campaign() {
    // Host gate, constant by design: `cfg!` fixes the compile target, so clippy sees a
    // constant where the test needs a runtime refusal (a const block would fail the build).
    #[allow(clippy::assertions_on_constants)]
    {
        assert!(
            cfg!(all(
                target_arch = "aarch64",
                target_os = "linux",
                target_env = "gnu"
            )),
            "the required campaign must execute on native Linux GNU AArch64"
        );
    }
    let ay = required_tool(TOOL_ENV[0].0, TOOL_ENV[0].1);
    let clean = required_tool(TOOL_ENV[1].0, TOOL_ENV[1].1);
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-real-request-cache-")
        .tempdir()
        .unwrap();
    let prefix = directory.path().join("private-package-prefix");
    std::fs::create_dir_all(prefix.join("bin")).unwrap();
    // AY is never discovered from a package store: the verifier admits only its
    // toolchain's identity-checked `bin/ay` (trust_cg_verify::ay_identity), so
    // the campaign's AY input must BE that binary's bytes.
    place_package_link(&prefix, "clean", &clean);
    let pinned_ay = trust_cg_verify::ay_identity::resolve_for_process()
        .unwrap_or_else(|refusal| panic!("the campaign requires the toolchain AY: {refusal}"));
    assert_eq!(
        sha256_file(pinned_ay.path()),
        ay.sha256,
        "the campaign AY input must be the toolchain's admitted AY ({})",
        pinned_ay.describe()
    );
    let path = std::env::join_paths(std::iter::once(prefix.join("bin")).chain(
        std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()),
    ))
    .unwrap();

    trust_cg_process_env::with_env_edits(|environment| {
        // Scoped discovery, not an installed package mutation. Both explicit
        // tool overrides are removed before the real consumer is invoked.
        environment.set("PATH", &path);
        environment.set("TCG_BLOCKING_IDENTITY", "1");
        for key in [
            "AY_SOLVER_PATH",
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "TCG_CLEAN_CHECKER",
            "TCG_NO_VERDICT_DB",
            "TCG_NO_PROOF_CACHE",
            "TCG_NO_SOLVER_SERVER",
            "TCG_PRECISE_CITATIONS",
            "TCG_NO_JIT_CERT_CACHE",
            "TCG_PROVENANCE_XCHECK",
            "TCG_CANARY_NO_CACHE",
            "TCG_NO_CERT_STORE",
            "TCG_PROOF_CERT_STORE",
            "TCG_REFINE_SOLVER",
            "TCG_RECON_SOLVER_MS",
            "TRUST_CG_AY_TIMEOUT_MS",
        ] {
            environment.remove(key);
        }
        for (path_variable, hash_variable) in TOOL_ENV {
            environment.remove(path_variable);
            environment.remove(hash_variable);
        }
        assert!(!deep_verifier_override_disables_outer_cache());
        assert!(jit_cert_cache_allowed_for_request());

        let verifier = FunctionVerifier::new();
        let request = verifier.capture_request();
        let identity = request
            .reuse_identity()
            .expect("real discovered tools must be reusable");
        // Compare discovery to an independently selected exact-path capture.
        // The reference capture is never passed to the cache consumer and no
        // override-bearing compilation is allowed to warm the default cache.
        let explicit_identity = trust_cg_process_env::with_env_edits(|reference| {
            reference.set("AY_SOLVER_PATH", pinned_ay.path().as_os_str());
            reference.set("TCG_EXTERNAL_CLEAN_CHECKER", clean.path.as_os_str());
            assert!(deep_verifier_override_disables_outer_cache());
            verifier.capture_request().reuse_identity()
        });
        assert_eq!(
            explicit_identity,
            Some(identity),
            "discovery must bind the exact protected tools"
        );
        assert!(!deep_verifier_override_disables_outer_cache());

        let function = extension_function("receipt_byte", AArch64Opcode::Sxtb);
        let obligation = trust_cg_verify::function_verifier::reconstruct_alu_obligation(
            &function.insts[0],
        )
        .expect(
            "valid SXTB operands must use real reconstruction, not an operandless registry stub",
        );
        assert_eq!(obligation.inputs, vec![("recon_src".to_owned(), 8)]);
        let config = trust_cg_verify::VerificationConfig::default();
        assert_eq!(config.exhaustive_threshold, 8);
        assert!(matches!(
            VerificationStrength::for_obligation_with_config(&obligation, &config),
            VerificationStrength::Exhaustive
        ));
        assert!(matches!(
            trust_cg_verify::lowering_proof::verify_by_evaluation_with_config(&obligation, &config),
            trust_cg_verify::verify::VerificationResult::Valid
        ));
        let zero = extension_function("zero_control", AArch64Opcode::Uxtb);
        let mut mutant = obligation.clone();
        mutant.aarch64_expr =
            trust_cg_verify::function_verifier::reconstruct_alu_obligation(&zero.insts[0])
                .unwrap()
                .aarch64_expr;
        assert!(
            matches!(
                trust_cg_verify::lowering_proof::verify_by_evaluation_with_config(&mutant, &config),
                trust_cg_verify::verify::VerificationResult::Invalid { .. }
            ),
            "the same finite evaluator must refute sign/zero substitution"
        );
        let report = real_report(&verifier, &request, &function);

        let cache = Arc::new(JitCertCache::new());
        let cold = raw_compile(&function, &cache, true);
        assert_certificate(&cold, &function.name, false);
        assert_eq!(cache.stats(), (0, 1, 0, 1));
        let key = only_key(&cache);
        let stored = cache.peek(&key).unwrap();
        let stored_report = stored.verification_report.as_ref().unwrap();
        assert!(stored_report.reusable_for(&request));
        assert!(stored_report.matches_aarch64_input(&function, None));
        let certificate = cold.certificate(&function.name).unwrap();
        assert_native_byte_domain(&cold, &function.name);
        let warm = raw_compile(&function, &cache, true);
        assert_certificate(&warm, &function.name, true);
        assert_eq!(cache.stats(), (1, 1, 0, 1));
        assert_native_byte_domain(&warm, &function.name);

        let foreign_request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Off);
        assert_ne!(foreign_request.reuse_identity(), Some(identity));
        let foreign = real_report(&verifier, &foreign_request, &function);
        assert!(!foreign.reusable_for(&request));
        let wrong_input = extension_function("different_input_name", AArch64Opcode::Sxtb);
        let wrong_input_report = real_report(&verifier, &request, &wrong_input);
        assert!(!wrong_input_report.matches_aarch64_input(&function, None));
        let wrong_arch = wrong_architecture_report(&request);
        assert!(!wrong_arch.matches_aarch64_input(&function, None));
        // The complete-domain budget counts input tuples: one 16-bit input
        // fits the same 65,536 evaluations as two 8-bit inputs. Keep SXTH as
        // a positive boundary control, then use a full 32-bit NEG input for
        // the statistical receipt that must not authorize cache reuse.
        let halfword = extension_function("receipt_halfword", AArch64Opcode::Sxth);
        let _halfword_report = real_report(&verifier, &request, &halfword);
        let wider = extension_function("not_exhaustive", AArch64Opcode::Neg);
        let wider_obligation =
            trust_cg_verify::function_verifier::reconstruct_alu_obligation(&wider.insts[0])
                .expect("the statistical control must reconstruct its real operands");
        assert_eq!(wider_obligation.inputs, vec![("recon_src".to_owned(), 32)]);
        assert!(matches!(
            VerificationStrength::for_obligation_with_config(&wider_obligation, &config),
            VerificationStrength::Statistical { .. }
        ));
        let wider_report = run_on_proof_verifier_stack("request-cache-statistical-control", || {
            verifier.verify_with_request(&wider, None, &request)
        });
        // Sampled, so reported and never credited (E0.2).
        assert_eq!(
            wider_report.report().sampled_uncredited_count(),
            1,
            "{wider_report:?}"
        );
        assert_eq!(
            wider_report.report().verified_count(),
            0,
            "{wider_report:?}"
        );
        assert!(!wider_report.reusable_for(&request));
        let mut receipt_rejections = 0;
        for (label, replacement) in [
            ("no_receipt", None),
            ("foreign_request", Some(foreign)),
            ("wrong_input", Some(wrong_input_report)),
            ("wrong_architecture", Some(wrong_arch)),
            ("nonreusable_report", Some(wider_report)),
        ] {
            let planted = Arc::new(JitCertCache::new());
            planted.store(key.clone(), transport_entry(certificate, replacement));
            assert!(
                planted.peek(&key).is_some(),
                "{label}: control must reach lookup"
            );
            let fresh = raw_compile(&function, &planted, true);
            assert_certificate(&fresh, &function.name, false);
            assert_eq!(planted.stats(), (0, 1, 0, 1), "{label}");
            let repaired = planted.peek(&key).unwrap();
            let receipt = repaired.verification_report.as_ref().unwrap();
            assert!(receipt.reusable_for(&request), "{label}");
            assert!(receipt.matches_aarch64_input(&function, None), "{label}");
            receipt_rejections += 1;
        }
        assert_eq!(receipt_rejections, 5);

        let mut bypasses = 0;
        for (variable, value) in [
            ("TCG_NO_JIT_CERT_CACHE", "1"),
            ("TCG_NO_VERDICT_DB", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_NO_SOLVER_SERVER", "1"),
            ("TCG_PRECISE_CITATIONS", "1"),
            ("AY_SOLVER_PATH", ay.path.to_str().unwrap()),
            ("TCG_EXTERNAL_CLEAN_CHECKER", clean.path.to_str().unwrap()),
            ("TCG_CLEAN_CHECKER", clean.path.to_str().unwrap()),
        ] {
            let planted = Arc::new(JitCertCache::new());
            planted.store(
                key.clone(),
                transport_entry(certificate, Some(report.clone())),
            );
            let before = planted.peek(&key).unwrap();
            trust_cg_process_env::with_env_edits(|override_environment| {
                override_environment.set(variable, value);
                let fresh = raw_compile(&function, &planted, true);
                assert_certificate(&fresh, &function.name, false);
                assert_eq!(planted.stats(), (0, 0, 0, 1), "{variable}");
                assert!(
                    Arc::ptr_eq(&before, &planted.peek(&key).unwrap()),
                    "{variable}: bypass must not replace the planted entry"
                );
                assert_eq!(
                    planted.state.lock().unwrap().entries.len(),
                    1,
                    "{variable}: bypass must not publish under another key"
                );
            });
            bypasses += 1;
        }
        let always = CompilerConfig {
            jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
            ..CompilerConfig::jit_fast(Target::Aarch64)
        }
        .to_jit_config(ProfileHookMode::None)
        .unwrap();
        assert!(always.verify);
        assert!(!always.cache_certificates);
        let planted = Arc::new(JitCertCache::new());
        planted.store(
            key.clone(),
            transport_entry(certificate, Some(report.clone())),
        );
        let before = planted.peek(&key).unwrap();
        let always_compiler = JitCompiler::new(always).with_certificate_cache(Arc::clone(&planted));
        for run in 1..=2 {
            let fresh = always_compiler
                .compile_raw(std::slice::from_ref(&function), &HashMap::new())
                .unwrap();
            assert_certificate(&fresh, &function.name, false);
            assert_eq!(planted.stats(), (0, 0, 0, run));
            assert!(Arc::ptr_eq(&before, &planted.peek(&key).unwrap()));
            assert_eq!(planted.state.lock().unwrap().entries.len(), 1);
        }
        bypasses += 1;
        let disabled = Arc::new(JitCertCache::disabled());
        let fresh = raw_compile(&function, &disabled, true);
        assert_certificate(&fresh, &function.name, false);
        assert_eq!(disabled.stats(), (0, 0, 0, 1));
        assert!(disabled.state.lock().unwrap().entries.is_empty());
        bypasses += 1;
        assert_eq!(bypasses, 10);

        // The default 16-bit evaluation remains Statistical. Raw compile_raw
        // may expose its diagnostic certificate, but must never cache it as
        // verified. This does not turn the raw API into the typed proof gate.
        let unpromotable = Arc::new(JitCertCache::new());
        let fresh = raw_compile(&wider, &unpromotable, true);
        assert!(!fresh.certificate(&wider.name).unwrap().is_verified());
        assert!(!fresh.all_function_semantics_verified());
        assert_eq!(unpromotable.stats(), (0, 1, 0, 1));
        assert!(unpromotable.state.lock().unwrap().entries.is_empty());

        let large = extension_function(&"payload_".repeat(2048), AArch64Opcode::Sxtb);
        assert_payload_bounds(real_report(&verifier, &request, &large));
        assert_eq!(
            sha256_file(&ay.path),
            ay.sha256,
            "protected AY changed during campaign"
        );
        assert_eq!(
            sha256_file(&clean.path),
            clean.sha256,
            "protected Clean changed during campaign"
        );
        assert_eq!(verifier.capture_request().reuse_identity(), Some(identity));
        println!(
            "\nTCG_RAW_JIT_REQUEST_CACHE {}",
            serde_json::json!({
                "schema": 1,
                "target": "aarch64-unknown-linux-gnu",
                "finite_input_domain": INPUTS,
                "native_calls": INPUTS * 2,
                "cold_warm_compilations": 2,
                "receipt_rejection_cases": receipt_rejections,
                "cache_bypass_cases": bypasses,
                "unpromotable_store_cases": 1,
                "payload_bound_cases": 4,
                "ay_sha256": ay.sha256,
                "clean_sha256": clean.sha256,
            })
        );
    });
}

/// Default-run AArch64 cache-poisoning controls with the discovered tools.
///
/// The receipt rejections of the explicit campaign above need no external
/// certificate: SXTB's only obligation is exhaustive. This version uses the
/// discovered AY/Clean authority instead of four pinned path/hash inputs, so
/// it runs natively on every AArch64 Darwin or Linux host by default and
/// fails, never skips, when that authority is missing. It plants each
/// mismatched receipt under the victim's exact key; none may be served.
#[cfg(target_arch = "aarch64")]
#[test]
fn planted_receipts_under_the_victim_key_are_never_served() {
    trust_cg_process_env::with_env_edits(|environment| {
        environment.set("TCG_BLOCKING_IDENTITY", "1");
        for key in [
            "AY_SOLVER_PATH",
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "TCG_CLEAN_CHECKER",
            "TCG_NO_VERDICT_DB",
            "TCG_NO_PROOF_CACHE",
            "TCG_NO_SOLVER_SERVER",
            "TCG_PRECISE_CITATIONS",
            "TCG_NO_JIT_CERT_CACHE",
            "TCG_PROVENANCE_XCHECK",
            "TCG_CANARY_NO_CACHE",
            "TCG_NO_CERT_STORE",
            "TCG_REFINE_SOLVER",
            "TCG_RECON_SOLVER_MS",
            "TRUST_CG_AY_TIMEOUT_MS",
        ] {
            environment.remove(key);
        }
        assert!(!deep_verifier_override_disables_outer_cache());
        assert!(jit_cert_cache_allowed_for_request());
        let verifier = FunctionVerifier::new();
        let request = verifier.capture_request();
        let identity = request.reuse_identity().expect(
            "cache-poisoning controls require the discovered verification authority; \
             its absence is a failure, not a pass",
        );

        let function = extension_function("receipt_byte", AArch64Opcode::Sxtb);
        let cache = Arc::new(JitCertCache::new());
        let cold = raw_compile(&function, &cache, true);
        assert_certificate(&cold, &function.name, false);
        assert_eq!(cache.stats(), (0, 1, 0, 1));
        let key = only_key(&cache);
        let certificate = cold.certificate(&function.name).unwrap();
        assert_native_byte_domain(&cold, &function.name);
        let warm = raw_compile(&function, &cache, true);
        assert_certificate(&warm, &function.name, true);
        assert_eq!(cache.stats(), (1, 1, 0, 1));

        let foreign_request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Off);
        assert_ne!(foreign_request.reuse_identity(), Some(identity));
        let foreign = real_report(&verifier, &foreign_request, &function);
        assert!(!foreign.reusable_for(&request));
        let wrong_input = extension_function("different_input_name", AArch64Opcode::Sxtb);
        let wrong_input_report = real_report(&verifier, &request, &wrong_input);
        assert!(!wrong_input_report.matches_aarch64_input(&function, None));
        let wrong_arch = wrong_architecture_report(&request);
        assert!(!wrong_arch.matches_aarch64_input(&function, None));
        // A receipt for the right input whose request disabled proof reuse:
        // a genuine report that is reusable for no request. (Whether a wider
        // SXTH obligation is reusable depends on the host's verdict sources,
        // so it is not a deterministic non-reusable control here.)
        let unreusable = trust_cg_process_env::with_env_edits(|override_environment| {
            override_environment.set("TCG_NO_PROOF_CACHE", "1");
            let unreusable_request = verifier.capture_request();
            let report = run_on_proof_verifier_stack("request-cache-unreusable-control", || {
                verifier.verify_with_request(&function, None, &unreusable_request)
            });
            assert!(report.matches_aarch64_input(&function, None));
            assert!(!report.reusable_for(&unreusable_request));
            report
        });
        assert!(!unreusable.reusable_for(&request));
        let mut rejected = 0;
        for (label, replacement) in [
            ("no_receipt", None),
            ("foreign_request", Some(foreign)),
            ("wrong_input", Some(wrong_input_report)),
            ("wrong_architecture", Some(wrong_arch)),
            ("nonreusable_report", Some(unreusable)),
        ] {
            let planted = Arc::new(JitCertCache::new());
            planted.store(key.clone(), transport_entry(certificate, replacement));
            assert!(
                planted.peek(&key).is_some(),
                "{label}: control must reach lookup"
            );
            let fresh = raw_compile(&function, &planted, true);
            assert_certificate(&fresh, &function.name, false);
            assert_eq!(planted.stats(), (0, 1, 0, 1), "{label}");
            let repaired = planted.peek(&key).unwrap();
            let receipt = repaired.verification_report.as_ref().unwrap();
            assert!(receipt.reusable_for(&request), "{label}");
            assert!(receipt.matches_aarch64_input(&function, None), "{label}");
            assert_native_byte_domain(&fresh, &function.name);
            rejected += 1;
        }
        assert_eq!(rejected, 5);
        println!("JIT_CACHE_PLANTED_RECEIPTS rejected={rejected} warm_hits=1");
    });
}
