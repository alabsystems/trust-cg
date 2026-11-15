// trust-cg-codegen/tests/proof_evidence_honesty.rs - WP-0 acceptance
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! WP-0 acceptance: a consumer must be able to tell **proved** from **checked
//! statistically** from **nothing ran at all**, by reading the artifact.
//!
//! Before WP-0 those three were not distinguishable, because on the routes
//! where nothing ran the evidence field was *absent* rather than negative — and
//! an absent fact reads exactly like a passing one. These tests pin the three
//! acceptance conditions, with counts:
//!
//! (a) a certificates-required-at-formal-strength compile **refuses** on a
//!     solver-less host rather than emitting a statistical certificate;
//! (b) a `verify: false` compile reports `MissingEvidence` and lists the
//!     assumptions it is resting on;
//! (c) an ordinary verified compile reports its **real** strength — Statistical
//!     with the sample count here, Exhaustive where the input space allows it.
//!
//! Everything here is a *reporting* assertion. No gate is exercised, no default
//! is flipped, and none of these paths changes what the backend checks.

use trust_cg_codegen::compile_service::{
    ArtifactKind, CompileGeneration, CompileRequest, CompileStatus, ProofTvEvidenceOutcome,
    ProofTvVerdict, SourceKind,
};
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::jit_contract::{
    ASSUMPTION_DISPATCH_VERIFY_OFF, ASSUMPTION_NO_SOLVER_AVAILABLE,
    ASSUMPTION_STATISTICAL_DISCHARGE, ASSUMPTION_VERIFICATION_DISABLED, EvidenceStrength,
    ProofEvidenceSummary, ProofEvidenceVerdict, ProofPolicy, RequiredEvidenceStrength,
};
use trust_cg_codegen::pipeline::{DispatchVerifyMode, OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::proof_evidence::{
    PROOF_STRENGTH_UNAVAILABLE_CODE, RouteFacts, evidence_environment, route_evidence,
};
use trust_ir::{
    BinOp, Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

/// A tiny module with one non-vacuous lowering obligation. A constant-only
/// function can be fully folded before machine verification, which correctly
/// fails the always-verify gate for lack of a meaningful certificate.
fn arithmetic_module(name: &str) -> Module {
    arithmetic_module_of(name, Ty::I64)
}

/// The same `answer(a, b) = a + b` over 128-bit integers. On an x86-64 host
/// it stays outside the source-bound body lane (an i128 rides a register
/// pair, which no body slice admits), so its instruction evidence is sampled,
/// never credit, whatever proof tools the host has: the subject of the
/// "sampled evidence is refused" assertions. (The 64-bit and narrow adds are
/// inside that lane and promote where an admitted AY and a capable Clean
/// replay their body theorems.)
fn sampled_arithmetic_module(name: &str) -> Module {
    arithmetic_module_of(name, Ty::I128)
}

fn arithmetic_module_of(name: &str, ty: Ty) -> Module {
    let mut module = Module::new(name);
    let ft = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "answer", ft, BlockId::new(0));
    func.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// A host-JIT compile request: the route the flagship consumer takes.
fn request(id: &str) -> CompileRequest {
    let mut request = CompileRequest::new(id, CompileGeneration::new(1));
    request.artifact_kind = ArtifactKind::ExecutableMemory;
    request.provenance.source_kind = SourceKind::TrustIrModule;
    request.provenance.source_fingerprint = Some(format!("sha256:{id}-source"));
    request
}

/// An object request with a proof policy that switches instruction-level
/// verification and certificate emission on, plus a caller-supplied accepted
/// proof/TV outcome. The AArch64 executable-memory route additionally requires
/// a non-vacuous proof-grade JIT certificate and correctly rejects current
/// target-reconstructed Statistical evidence; this reporting test exercises the
/// ordinary AOT evidence channel instead.
fn verified_request(id: &str) -> CompileRequest {
    let mut request = request(id);
    request.artifact_kind = ArtifactKind::Object;
    request.proof_policy = ProofPolicy::require_certificates(["ay"]);
    request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
        verdict: ProofTvVerdict::Accepted,
        rejection_code: None,
        diagnostic_reason: "wp0 acceptance: caller-supplied accepted TV outcome".to_owned(),
    });
    request
}

fn compiled_evidence(request: CompileRequest, module: &Module) -> ProofEvidenceSummary {
    let response = permit_compile_service().compile(request, module);
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "expected a compiled artifact, got {:?}: {:?}",
        response.status,
        response.diagnostics
    );
    response
        .artifact
        .expect("compiled artifact")
        .install
        .proof_evidence_summary
}

// -------------------------------------------------------------------------
// (a) Strength is REFUSABLE, not merely reportable.
// -------------------------------------------------------------------------

/// A caller that demands solver-backed certificates on a host with no solver
/// must get a **rejection**. The failure mode this closes is the quiet one: a
/// statistically-discharged certificate emitted under a "formal" request still
/// ends up installed, and the consumer has no way to notice the downgrade.
#[test]
fn a_certificates_required_compile_refuses_rather_than_downgrading() {
    let environment = evidence_environment();
    if environment.solver_available {
        eprintln!("skipping: this host has a solver, so nothing is refusable");
        return;
    }

    let module = arithmetic_module("wp0_refuse");
    let mut request = request("wp0-refuse");
    request.proof_policy = ProofPolicy::require_certificates(["ay"])
        .with_required_strength(RequiredEvidenceStrength::Formal);

    let response = permit_compile_service().compile(request, &module);

    assert_eq!(
        response.status,
        CompileStatus::Rejected,
        "a formal-strength request must be refused on a solver-less host"
    );
    assert!(
        response.artifact.is_none() && response.payload.is_none(),
        "a refused compile must not hand back an artifact or payload"
    );
    assert_eq!(
        response.diagnostics.len(),
        1,
        "expected exactly one refusal diagnostic, got {:?}",
        response.diagnostics
    );
    let diagnostic = &response.diagnostics[0];
    assert_eq!(diagnostic.code, PROOF_STRENGTH_UNAVAILABLE_CODE);
    assert!(
        diagnostic.message.contains("statistical"),
        "the refusal must name the strength it declined to emit: {}",
        diagnostic.message
    );
}

/// The fifth closure audit's second finding (skeptic 2's
/// `sk2_strength_refusal_probe.rs`), end to end: with `XDG_CACHE_HOME`
/// holding a pre-existing `0775` `trust-cg` (a cache an earlier umask-0002
/// build made), the identity rule refuses AY with
/// `[TCG-AY-IDENTITY-UNMATERIALIZED]`, the directory, its mode and the
/// remedy. A compile-service request demanding Formal strength was refused
/// with `proof_strength_unavailable` and no AY cause, and the no-solver
/// disclosure of an unverified compile had none either. Both now carry the
/// refusal the route's own resolution found (OD-XHOST-STRENGTH-NOTE-20261016). The
/// test runs itself in a child process with that cache; the directory is
/// never changed. A build that records no AY has no note to carry, and on a
/// host with no capable Clean checker the route is refused before AY is
/// resolved, so no AY refusal is named (each said so in the output).
#[cfg(unix)]
#[test]
fn a_formal_refusal_names_the_ay_refusal_of_a_group_writable_cache() {
    use std::os::unix::fs::PermissionsExt;
    const CHILD: &str = "PROOF_EVIDENCE_STRENGTH_NOTE_CHILD_CACHE";
    const NAME: &str = "a_formal_refusal_names_the_ay_refusal_of_a_group_writable_cache";
    let mode = |path: &std::path::Path| {
        std::fs::symlink_metadata(path)
            .unwrap()
            .permissions()
            .mode()
            & 0o7777
    };
    let Some(cache) = std::env::var_os(CHILD).map(std::path::PathBuf::from) else {
        let base = tempfile::tempdir().unwrap();
        std::fs::set_permissions(base.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
        let cache = base.path().canonicalize().unwrap();
        let trust_cg = cache.join("trust-cg");
        std::fs::create_dir(&trust_cg).unwrap();
        std::fs::set_permissions(&trust_cg, std::fs::Permissions::from_mode(0o775)).unwrap();
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
            .env(CHILD, &cache)
            .env("XDG_CACHE_HOME", &cache)
            // The toolchain route: the one a proof-required compile uses.
            .env_remove("AY_SOLVER_PATH")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        for line in stdout
            .lines()
            .filter(|line| line.contains("STRENGTH_NOTE "))
        {
            println!("{}", &line[line.find("STRENGTH_NOTE ").unwrap_or(0)..]);
        }
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "child: {}\n{stdout}\n{stderr}",
            output.status
        );
        assert_eq!(
            mode(&trust_cg),
            0o775,
            "an existing directory is never changed"
        );
        return;
    };
    let trust_cg = cache.join("trust-cg");
    let recorded = trust_cg_verify::ay_identity::recorded_toolchain_ay_identity().is_ok();
    let checker = trust_cg_verify::obligation_cert_store::resolve_proof_checker().is_ok();
    let identity_rule =
        trust_cg_verify::ay_bridge::solver_identity_refusal().map(|refusal| refusal.to_string());
    println!(
        "STRENGTH_NOTE recorded AY: {recorded}; capable Clean checker: {checker}; identity rule: \
         {identity_rule:?}"
    );
    // Every place is checked before the test fails.
    let mut missing = Vec::new();
    let mut check = |place: &str, text: &str| {
        println!("STRENGTH_NOTE {place}: {text}");
        if recorded && checker {
            let refusal = identity_rule.clone().unwrap_or_default();
            for needed in [
                "the proof route was resolved with no AY admitted".to_owned(),
                "[TCG-AY-IDENTITY-UNMATERIALIZED]".to_owned(),
                format!("{} has mode 0775", trust_cg.display()),
                refusal,
            ] {
                if needed.is_empty() || !text.contains(&needed) {
                    missing.push(format!("{place}: {needed:?} missing from {text}"));
                }
            }
        } else if text.contains("TCG-AY-IDENTITY") {
            missing.push(format!("{place}: an AY note without a resolved AY: {text}"));
        }
    };
    if recorded && !checker {
        println!(
            "STRENGTH_NOTE no capable Clean checker on this host: the route is refused before AY \
             is resolved, so no AY refusal is named"
        );
    }
    let module = arithmetic_module("strength_note");
    for kind in [ArtifactKind::ExecutableMemory, ArtifactKind::Object] {
        let mut formal = request("strength-note-formal");
        formal.artifact_kind = kind;
        formal.proof_policy = ProofPolicy::require_certificates(["ay"])
            .with_required_strength(RequiredEvidenceStrength::Formal);
        let response = permit_compile_service().compile(formal, &module);
        assert_eq!(response.status, CompileStatus::Rejected, "{kind:?}");
        assert_eq!(response.diagnostics.len(), 1, "{:?}", response.diagnostics);
        assert_eq!(
            response.diagnostics[0].code,
            PROOF_STRENGTH_UNAVAILABLE_CODE
        );
        check(
            &format!("Formal {kind:?} refusal"),
            &response.diagnostics[0].message,
        );
    }
    let disclosed = compiled_evidence(request("strength-note-disclosure"), &module);
    let assumption = disclosed
        .accepted_assumptions
        .iter()
        .find(|assumption| assumption.id == ASSUMPTION_NO_SOLVER_AVAILABLE)
        .expect("AY is refused here, so the route is unavailable and disclosed");
    check("no-solver disclosure", &assumption.detail);
    assert!(missing.is_empty(), "{missing:#?}");
}

/// The refusal is scoped: the default requirement is `Any`, so every existing
/// caller — including a plain certificates-required policy — is untouched.
#[test]
fn the_default_strength_requirement_never_refuses() {
    let module = arithmetic_module("wp0_no_refuse");

    let required = verified_request("wp0-no-refuse-required");
    assert_eq!(
        required.proof_policy.required_strength,
        RequiredEvidenceStrength::Any
    );
    // The `Any` requirement itself never refuses. E0.2 refuses this compile one
    // layer down — on the uncredited instruction evidence, never with the
    // strength-unavailable code this test guards.
    let response = permit_compile_service().compile(required, &module);
    assert!(
        response
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != PROOF_STRENGTH_UNAVAILABLE_CODE),
        "the default requirement must never raise the strength refusal: {:?}",
        response.diagnostics
    );

    let disabled = request("wp0-no-refuse-disabled");
    assert_eq!(
        permit_compile_service().compile(disabled, &module).status,
        CompileStatus::Compiled
    );
}

// -------------------------------------------------------------------------
// (b) `verify: false` reports MissingEvidence, with its assumptions listed.
// -------------------------------------------------------------------------

/// The default compile profile runs `verify: false`. Before WP-0 that produced
/// no evidence field at all; it must now produce an explicitly negative one.
#[test]
fn a_verify_false_compile_reports_missing_evidence_with_assumptions() {
    let module = arithmetic_module("wp0_unverified");
    let evidence = compiled_evidence(request("wp0-unverified"), &module);

    assert_eq!(
        evidence.verdict,
        ProofEvidenceVerdict::MissingEvidence,
        "a compile where nothing ran must say so"
    );
    assert_eq!(evidence.strength, EvidenceStrength::NotRun);

    let ids = evidence.accepted_assumption_ids();
    assert!(
        ids.contains(&ASSUMPTION_VERIFICATION_DISABLED),
        "expected the verification-disabled assumption, got {ids:?}"
    );
    assert!(
        !ids.contains(&ASSUMPTION_STATISTICAL_DISCHARGE),
        "nothing ran, so there is no statistical discharge to assume: {ids:?}"
    );
    if !evidence_environment().solver_available {
        assert!(
            ids.contains(&ASSUMPTION_NO_SOLVER_AVAILABLE),
            "expected the no-solver assumption on this host, got {ids:?}"
        );
    }
    assert!(
        !ids.is_empty(),
        "an unverified compile must state what it is relying on"
    );
}

/// The fast JIT route returns a bare executable buffer and never builds a
/// compile-service artifact — the exact route the flagship consumer takes with
/// `verify: false` / `DispatchVerifyMode::Off`. It must still be able to answer
/// "did anything run?".
#[test]
fn the_fast_jit_route_reports_missing_evidence() {
    let jit = JitCompiler::new(JitConfig {
        opt_level: OptLevel::O2,
        verify: false,
        verify_dispatch: DispatchVerifyMode::Off,
        ..JitConfig::default()
    });
    let evidence = jit.proof_evidence();

    assert_eq!(evidence.verdict, ProofEvidenceVerdict::MissingEvidence);
    assert_eq!(evidence.strength, EvidenceStrength::NotRun);
    let ids = evidence.accepted_assumption_ids();
    assert!(ids.contains(&ASSUMPTION_VERIFICATION_DISABLED), "{ids:?}");
    assert!(ids.contains(&ASSUMPTION_DISPATCH_VERIFY_OFF), "{ids:?}");

    // Same question asked of the pipeline the consumer configures directly.
    let pipeline = Pipeline::new(PipelineConfig {
        verify: false,
        verify_dispatch: DispatchVerifyMode::Off,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    });
    assert_eq!(
        pipeline.proof_evidence().verdict,
        ProofEvidenceVerdict::MissingEvidence
    );
    assert_eq!(pipeline.proof_evidence().strength, EvidenceStrength::NotRun);
}

// -------------------------------------------------------------------------
// (c) A verified compile reports its REAL strength.
// -------------------------------------------------------------------------

/// A compile that actually runs obligations reports the conservative route
/// strength it reached: `Statistical` with the exact sample count, never
/// complete, and it discloses what sampling is worth. E0.2: sampled and
/// instruction-derived evidence is not credit, so such a compile is also
/// REJECTED — the run-route summary is therefore built directly from the route
/// facts, and the refusal is pinned alongside it.
#[test]
fn a_verifying_compile_reports_its_real_strength_and_is_refused() {
    let environment = evidence_environment();
    let module = sampled_arithmetic_module("wp0_verified");

    let response = permit_compile_service().compile(verified_request("wp0-verified"), &module);
    assert_eq!(
        response.status,
        CompileStatus::Failed,
        "sampled instruction evidence must not promote: {:?}",
        response.diagnostics
    );
    // The refusal names the module's uncovered rows and the first row's
    // reason. Since E0.2 the leading register copy is refused first as an
    // instruction-derived obligation, so the pinned spelling is the E0.2
    // family ("... is not proof credit") and the i128 add's rows must be among
    // the named uncovered opcodes.
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            let message = &diagnostic.message;
            message.contains("is not proof credit")
                && message.contains("AArch64::AddsRR")
                && message.contains("AArch64::Adc")
        }),
        "the refusal must name the uncredited evidence: {:?}",
        response.diagnostics
    );

    let facts = RouteFacts {
        instruction_verification_ran: true,
        dispatch_verification_ran: true,
        proof_certificates_emitted: true,
        evidence_report_present: true,
        manifest_pin_accepted: false,
    };
    let evidence = route_evidence("trust-cg.compile_route", facts, &environment);
    assert_eq!(
        evidence.strength,
        EvidenceStrength::Statistical {
            sample_count: environment.statistical_sample_count
        },
        "a route without complete Formal coverage must report Statistical with its real sample count"
    );
    assert_eq!(
        environment.statistical_sample_count, 100_000,
        "the reported sample count must be the one the verifier actually uses"
    );
    assert!(
        !evidence.strength.is_complete(),
        "statistical discharge must never be reported as complete"
    );

    let ids = evidence.accepted_assumption_ids();
    assert!(
        ids.contains(&ASSUMPTION_STATISTICAL_DISCHARGE),
        "a statistically-discharged route must say what it assumed: {ids:?}"
    );
    assert_eq!(
        ids.contains(&ASSUMPTION_NO_SOLVER_AVAILABLE),
        !environment.solver_available,
        "the no-solver assumption must match actual solver availability: {ids:?}"
    );
    assert!(
        !ids.contains(&ASSUMPTION_VERIFICATION_DISABLED),
        "verification ran, so it must not claim it was disabled: {ids:?}"
    );
}

/// Exhaustive is reachable and reported where the input space allows it, so
/// `Statistical` is a measured answer rather than a constant.
#[test]
fn a_narrow_input_space_reports_exhaustive() {
    let mut environment = evidence_environment();
    environment.solver_available = false;

    assert_eq!(
        environment.strength_for(environment.exhaustive_threshold_bits, 2),
        EvidenceStrength::Exhaustive
    );
    assert!(
        environment
            .strength_for(environment.exhaustive_threshold_bits, 2)
            .is_complete()
    );
    assert_eq!(
        environment.strength_for(64, 2),
        EvidenceStrength::Statistical {
            sample_count: environment.statistical_sample_count
        }
    );
}

// -------------------------------------------------------------------------
// The three states are mutually distinguishable — with counts.
// -------------------------------------------------------------------------

/// The whole acceptance in one place: over the three routes a consumer can
/// take, the two that run nothing say so, the one that runs obligations is
/// refused with a named reason (E0.2: sampled evidence is not credit), and none
/// of them is silent.
#[test]
fn every_route_emits_evidence_and_the_three_states_are_distinguishable() {
    let module = arithmetic_module("wp0_matrix");

    let unverified = compiled_evidence(request("wp0-matrix-unverified"), &module);

    let verifying = permit_compile_service().compile(
        verified_request("wp0-matrix-verified"),
        &sampled_arithmetic_module("wp0_matrix_sampled"),
    );

    let fast_jit = JitCompiler::new(JitConfig {
        verify: false,
        verify_dispatch: DispatchVerifyMode::Off,
        ..JitConfig::default()
    })
    .proof_evidence();

    let routes = [&unverified, &fast_jit];

    // Nothing is silent: every route that produces an artifact emits a
    // schema-tagged summary, and the refused one emits diagnostics.
    assert_eq!(
        routes
            .iter()
            .filter(|evidence| !evidence.schema.is_empty())
            .count(),
        2,
        "every compile route must emit an evidence summary"
    );
    assert_eq!(verifying.status, CompileStatus::Failed);
    assert!(
        verifying.artifact.is_none() && !verifying.diagnostics.is_empty(),
        "a refused route must hand back diagnostics, not an artifact"
    );

    // Both artifact-producing routes ran nothing at all, and neither claims
    // completeness.
    assert_eq!(
        routes
            .iter()
            .filter(|evidence| evidence.strength == EvidenceStrength::NotRun)
            .count(),
        2,
        "the unverified compile and the fast JIT route both ran nothing"
    );
    assert_eq!(
        routes
            .iter()
            .filter(|evidence| evidence.strength.is_complete())
            .count(),
        0,
        "no route without complete Formal coverage may report a complete discharge"
    );

    // Every route names at least one assumption it is relying on.
    assert_eq!(
        routes
            .iter()
            .filter(|evidence| !evidence.accepted_assumptions.is_empty())
            .count(),
        2,
        "every route must publish what it is trusting"
    );
}

/// The honesty channel is strictly additive: a summary that reports nothing new
/// checksums exactly as it did before the channel existed, so adding the fields
/// moved no artifact bytes for any existing compile.
#[test]
fn the_evidence_channel_does_not_move_existing_checksums() {
    let base = route_evidence(
        "trust-cg.test",
        RouteFacts::default(),
        &evidence_environment(),
    );
    let mut stripped = base.clone();
    stripped.strength = EvidenceStrength::NotReported;
    stripped.accepted_assumptions.clear();

    let mut pristine = ProofEvidenceSummary::missing("trust-cg.test");
    pristine.strength = EvidenceStrength::NotReported;

    assert_eq!(
        stripped.checksum(),
        pristine.checksum(),
        "a summary reporting neither strength nor assumptions must encode as it did before WP-0"
    );
    assert_ne!(
        base.checksum(),
        stripped.checksum(),
        "a summary that does report the channel must be covered by its checksum"
    );
}

/// This file's fixtures carry no codegen license (`body_gate: None`), which
/// the compile service REFUSES by default (roadmap WS7.5, decision gate
/// DG-73). Its services state `Permit` explicitly, so no request passes
/// because it was silently refused.
fn permit_compile_service() -> trust_cg_codegen::CompileService {
    trust_cg_codegen::CompileService::new(trust_cg_codegen::CompileServiceConfig {
        codegen_license: trust_cg_codegen::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit),
        ..trust_cg_codegen::CompileServiceConfig::default()
    })
}
