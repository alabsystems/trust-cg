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
//! (a) a certificates-required-at-formal-strength compile **refuses** on this
//!     solver-less host rather than emitting a statistical certificate;
//! (b) a `verify: false` compile reports `MissingEvidence` and lists the
//!     assumptions it is resting on;
//! (c) an ordinary verified compile reports its **real** strength — Statistical
//!     with the sample count here, Exhaustive where the input space allows it.
//!
//! Everything here is a *reporting* assertion. No gate is exercised, no default
//! is flipped, and none of these paths changes what the backend checks.

use trust_cg_codegen::compile_service::{
    ArtifactKind, CompileGeneration, CompileRequest, CompileService, CompileStatus,
    ProofTvEvidenceOutcome, ProofTvVerdict, SourceKind,
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
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn const_module(name: &str) -> Module {
    let mut module = Module::new(name);
    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "answer", ft, BlockId::new(0));
    func.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42.into()),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module.add_function(func);
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

/// The same request with a proof policy that switches instruction-level
/// verification and certificate emission on, plus a caller-supplied accepted
/// proof/TV outcome — an ordinary *verified* compile.
fn verified_request(id: &str) -> CompileRequest {
    let mut request = request(id);
    request.proof_policy = ProofPolicy::require_certificates(["ay"]);
    request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
        verdict: ProofTvVerdict::Accepted,
        rejection_code: None,
        diagnostic_reason: "wp0 acceptance: caller-supplied accepted TV outcome".to_owned(),
    });
    request
}

fn compiled_evidence(request: CompileRequest, module: &Module) -> ProofEvidenceSummary {
    let response = CompileService::default().compile(request, module);
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

    let module = const_module("wp0_refuse");
    let mut request = request("wp0-refuse");
    request.proof_policy = ProofPolicy::require_certificates(["ay"])
        .with_required_strength(RequiredEvidenceStrength::Formal);

    let response = CompileService::default().compile(request, &module);

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

/// The refusal is scoped: the default requirement is `Any`, so every existing
/// caller — including a plain certificates-required policy — is untouched.
#[test]
fn the_default_strength_requirement_never_refuses() {
    let module = const_module("wp0_no_refuse");

    let required = verified_request("wp0-no-refuse-required");
    assert_eq!(
        required.proof_policy.required_strength,
        RequiredEvidenceStrength::Any
    );
    assert_eq!(
        CompileService::default().compile(required, &module).status,
        CompileStatus::Compiled
    );

    let disabled = request("wp0-no-refuse-disabled");
    assert_eq!(
        CompileService::default().compile(disabled, &module).status,
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
    let module = const_module("wp0_unverified");
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
        ..PipelineConfig::default()
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

/// A compile that actually verifies must report the strength it verified at —
/// on this box, `Statistical` carrying the exact sample count, because no
/// solver is reachable. The point is that it must not read as "proved".
#[test]
fn a_verified_compile_reports_its_real_strength_with_the_sample_count() {
    let environment = evidence_environment();
    let module = const_module("wp0_verified");

    let evidence = compiled_evidence(verified_request("wp0-verified"), &module);

    assert_eq!(
        evidence.verdict,
        ProofEvidenceVerdict::Verified,
        "a compile whose proof/TV report was accepted must report Verified"
    );
    assert!(
        !evidence.is_missing_evidence(),
        "verification ran, so this is not the missing-evidence case"
    );

    if environment.solver_available {
        assert!(
            matches!(evidence.strength, EvidenceStrength::Formal { .. }),
            "a solver-present host must report Formal, got {:?}",
            evidence.strength
        );
        return;
    }

    assert_eq!(
        evidence.strength,
        EvidenceStrength::Statistical {
            sample_count: environment.statistical_sample_count
        },
        "a solver-less verified compile must report Statistical with its real sample count"
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
        "a statistically-discharged compile must say what it assumed: {ids:?}"
    );
    assert!(
        ids.contains(&ASSUMPTION_NO_SOLVER_AVAILABLE),
        "expected the no-solver assumption, got {ids:?}"
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
/// take, exactly one reports "nothing ran", exactly one reports a real
/// discharge strength, and none of them is silent.
#[test]
fn every_route_emits_evidence_and_the_three_states_are_distinguishable() {
    let environment = evidence_environment();
    let module = const_module("wp0_matrix");

    let unverified = compiled_evidence(request("wp0-matrix-unverified"), &module);

    let verified = compiled_evidence(verified_request("wp0-matrix-verified"), &module);

    let fast_jit = JitCompiler::new(JitConfig {
        verify: false,
        verify_dispatch: DispatchVerifyMode::Off,
        ..JitConfig::default()
    })
    .proof_evidence();

    let routes = [&unverified, &verified, &fast_jit];

    // Nothing is silent: every route emits a schema-tagged summary.
    assert_eq!(routes.len(), 3);
    assert_eq!(
        routes
            .iter()
            .filter(|evidence| !evidence.schema.is_empty())
            .count(),
        3,
        "every compile route must emit an evidence summary"
    );

    // Exactly two of the three routes ran nothing at all.
    assert_eq!(
        routes
            .iter()
            .filter(|evidence| evidence.strength == EvidenceStrength::NotRun)
            .count(),
        2,
        "the unverified compile and the fast JIT route both ran nothing"
    );

    // Exactly one reports a strength that means work happened.
    assert_eq!(
        routes
            .iter()
            .filter(|evidence| evidence.strength.ran())
            .count(),
        1,
        "only the verified compile discharged anything"
    );

    // And on this box, zero routes may claim completeness.
    if !environment.solver_available {
        assert_eq!(
            routes
                .iter()
                .filter(|evidence| evidence.strength.is_complete())
                .count(),
            0,
            "no route on a solver-less host may report a complete discharge"
        );
    }

    // Every route names at least one assumption it is relying on.
    assert_eq!(
        routes
            .iter()
            .filter(|evidence| !evidence.accepted_assumptions.is_empty())
            .count(),
        3,
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
