// trust-cg-codegen/tests/jit_no_handle_negative_fixtures.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_codegen::jit_contract::{
    ArtifactChecksum, ProofEvidenceRejectionCode, ProofEvidenceSummary, ProofEvidenceVerdict,
};
use trust_cg_codegen::jit_release::{
    ReleaseArtifactManifestReference, ReleaseBundleFileReference, ReleaseBundleInstallCode,
    ReleaseBundleInstallStatus, ReleaseProofReportReference, ReleaseReplayBundleMetadata,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConsumerRoute {
    AY,
    Ty,
    Unsupported,
}

impl ConsumerRoute {
    const fn as_str(self) -> &'static str {
        match self {
            Self::AY => "ay",
            Self::Ty => "ty",
            Self::Unsupported => "phase2-lab",
        }
    }

    const fn is_local(self) -> bool {
        matches!(self, Self::AY | Self::Ty)
    }
}

#[derive(Clone, Debug)]
struct NoHandleFixture {
    name: &'static str,
    route: ConsumerRoute,
    release_verdict: Option<&'static str>,
    rejection_code: &'static str,
    evidence: Option<(ProofEvidenceVerdict, ProofEvidenceRejectionCode)>,
    expected_bundle_code: ReleaseBundleInstallCode,
    expected_bundle_status: ReleaseBundleInstallStatus,
    issue_refs: &'static [&'static str],
}

#[derive(Debug, Default)]
struct AYRegistry {
    installed: BTreeSet<String>,
}

impl AYRegistry {
    fn maybe_install(&mut self, fixture: &NoHandleFixture, artifact: &NoHandleRouteResult) {
        if fixture.route == ConsumerRoute::AY && artifact.installed_artifact_id.is_some() {
            self.installed.insert(fixture.name.to_owned());
        }
    }

    fn contains(&self, name: &str) -> bool {
        self.installed.contains(name)
    }
}

#[derive(Debug, Default)]
struct TyNativeSlot {
    installed_handle: Option<String>,
}

impl TyNativeSlot {
    fn maybe_install(&mut self, fixture: &NoHandleFixture, artifact: &NoHandleRouteResult) {
        if fixture.route == ConsumerRoute::Ty {
            self.installed_handle = artifact.native_handle_id.clone();
        }
    }
}

#[derive(Clone, Debug, Default)]
struct CliNativeSummary {
    installed_artifact_id: Option<String>,
    typed_symbol_id: Option<String>,
    ay_registry_entry: Option<String>,
    ty_native_handle: Option<String>,
    cache_bundle_installed: bool,
    useful_native: u64,
    rejection_code: String,
    issue_refs: Vec<&'static str>,
}

impl CliNativeSummary {
    fn records_fixture_rejection(&self, fixture: &NoHandleFixture) {
        assert_eq!(self.rejection_code, fixture.rejection_code);
        assert_eq!(self.issue_refs, fixture.issue_refs);
        assert!(
            self.issue_refs.contains(&"#705"),
            "{} must carry the task issue ref for downstream phases",
            fixture.name
        );
    }
}

#[derive(Clone, Debug, Default)]
struct NoHandleRouteResult {
    installed_artifact_id: Option<String>,
    typed_symbol_id: Option<String>,
    native_handle_id: Option<String>,
    cache_bundle_installed: bool,
    useful_native: u64,
}

fn file(path: &str) -> ReleaseBundleFileReference {
    ReleaseBundleFileReference::new(path, format!("sha256:{path}"))
}

fn base_bundle(fixture: &NoHandleFixture) -> ReleaseReplayBundleMetadata {
    ReleaseReplayBundleMetadata::new(
        fixture.route.as_str(),
        "solver_program_native_kernel",
        format!("artifact:{}", fixture.name),
        ReleaseArtifactManifestReference::new(
            "artifact.manifest.json",
            format!("sha256:manifest:{}", fixture.name),
            1,
            ArtifactChecksum::new(0x705),
        ),
        file("source-lock.json"),
        ReleaseProofReportReference::new(
            format!("proofs/{}.json", fixture.name),
            format!("sha256:proof:{}", fixture.name),
        )
        .with_policy("require_native_handle_evidence")
        .with_solver(fixture.route.as_str())
        .with_obligation_set(format!("obligations:{}", fixture.name))
        .with_timeout_ms(250),
        file("telemetry/compile-telemetry.json"),
        file("release/package.json"),
        file("replay/replay.json"),
        file("gate-results.json"),
    )
}

fn fixture_bundle(fixture: &NoHandleFixture) -> ReleaseReplayBundleMetadata {
    let bundle = base_bundle(fixture);
    match fixture.release_verdict {
        Some(verdict) => {
            let proof = bundle.proof_reports[0].clone().with_verdict(verdict);
            bundle.with_proof_reports([proof])
        }
        None => bundle.with_proof_reports([]),
    }
}

fn evidence_summary(
    verdict: ProofEvidenceVerdict,
    rejection_code: ProofEvidenceRejectionCode,
) -> ProofEvidenceSummary {
    let checksum = ArtifactChecksum::new(0x705);
    ProofEvidenceSummary::rejected(
        "trust-cg-negative-fixture",
        verdict,
        rejection_code,
        checksum,
        checksum,
        checksum,
        checksum,
        checksum,
    )
}

fn route_negative_fixture(
    fixture: &NoHandleFixture,
) -> (
    NoHandleRouteResult,
    CliNativeSummary,
    ReleaseReplayBundleMetadata,
) {
    let bundle = fixture_bundle(fixture);
    let decision = bundle.install_decision();
    let result = NoHandleRouteResult {
        installed_artifact_id: None,
        typed_symbol_id: None,
        native_handle_id: None,
        cache_bundle_installed: decision.is_installable(),
        useful_native: 0,
    };
    let summary = CliNativeSummary {
        installed_artifact_id: result.installed_artifact_id.clone(),
        typed_symbol_id: result.typed_symbol_id.clone(),
        ay_registry_entry: None,
        ty_native_handle: result.native_handle_id.clone(),
        cache_bundle_installed: result.cache_bundle_installed,
        useful_native: result.useful_native,
        rejection_code: fixture.rejection_code.to_owned(),
        issue_refs: fixture.issue_refs.to_vec(),
    };

    (result, summary, bundle)
}

fn fixtures() -> Vec<NoHandleFixture> {
    vec![
        NoHandleFixture {
            name: "profile_only_ay_executable_looking",
            route: ConsumerRoute::AY,
            release_verdict: None,
            rejection_code: "profile_only_no_install",
            evidence: None,
            expected_bundle_code: ReleaseBundleInstallCode::MissingProofReports,
            expected_bundle_status: ReleaseBundleInstallStatus::NonInstallable,
            issue_refs: &["#705", "#660"],
        },
        NoHandleFixture {
            name: "missing_evidence_ay",
            route: ConsumerRoute::AY,
            release_verdict: None,
            rejection_code: "proof_missing_evidence",
            evidence: Some((
                ProofEvidenceVerdict::MissingEvidence,
                ProofEvidenceRejectionCode::MissingEvidence,
            )),
            expected_bundle_code: ReleaseBundleInstallCode::MissingProofReports,
            expected_bundle_status: ReleaseBundleInstallStatus::NonInstallable,
            issue_refs: &["#705", "#676"],
        },
        NoHandleFixture {
            name: "verifier_failure_ty",
            route: ConsumerRoute::Ty,
            release_verdict: Some("rejected"),
            rejection_code: "proof_verifier_failure",
            evidence: Some((
                ProofEvidenceVerdict::VerifierFailure,
                ProofEvidenceRejectionCode::VerifierFailure,
            )),
            expected_bundle_code: ReleaseBundleInstallCode::ProofRejected,
            expected_bundle_status: ReleaseBundleInstallStatus::ReplayOnly,
            issue_refs: &["#705", "#696"],
        },
        NoHandleFixture {
            name: "timeout_ay",
            route: ConsumerRoute::AY,
            release_verdict: Some("proof_timeout"),
            rejection_code: "proof_timeout",
            evidence: Some((
                ProofEvidenceVerdict::Timeout,
                ProofEvidenceRejectionCode::Timeout,
            )),
            expected_bundle_code: ReleaseBundleInstallCode::ProofTimeout,
            expected_bundle_status: ReleaseBundleInstallStatus::ReplayOnly,
            issue_refs: &["#705", "#664"],
        },
        NoHandleFixture {
            name: "unsupported_target_ay",
            route: ConsumerRoute::AY,
            release_verdict: Some("proof_unsupported_target"),
            rejection_code: "proof_unsupported_target",
            evidence: Some((
                ProofEvidenceVerdict::UnsupportedTarget,
                ProofEvidenceRejectionCode::UnsupportedTarget,
            )),
            expected_bundle_code: ReleaseBundleInstallCode::ProofVerdictNotAccepted,
            expected_bundle_status: ReleaseBundleInstallStatus::ReplayOnly,
            issue_refs: &["#705", "#664"],
        },
        NoHandleFixture {
            name: "stale_evidence_ty",
            route: ConsumerRoute::Ty,
            release_verdict: Some("proof_stale_evidence"),
            rejection_code: "proof_stale_evidence",
            evidence: Some((
                ProofEvidenceVerdict::StaleEvidence,
                ProofEvidenceRejectionCode::StaleEvidence,
            )),
            expected_bundle_code: ReleaseBundleInstallCode::ProofVerdictNotAccepted,
            expected_bundle_status: ReleaseBundleInstallStatus::ReplayOnly,
            issue_refs: &["#705", "#681"],
        },
        NoHandleFixture {
            name: "unknown_solver_error_ay",
            route: ConsumerRoute::AY,
            release_verdict: Some("proof_unknown_solver_error"),
            rejection_code: "proof_unknown_solver_error",
            evidence: Some((
                ProofEvidenceVerdict::UnknownSolverError,
                ProofEvidenceRejectionCode::UnknownSolverError,
            )),
            expected_bundle_code: ReleaseBundleInstallCode::ProofVerdictNotAccepted,
            expected_bundle_status: ReleaseBundleInstallStatus::ReplayOnly,
            issue_refs: &["#705", "#662"],
        },
        NoHandleFixture {
            name: "unsupported_route_executable_looking",
            route: ConsumerRoute::Unsupported,
            release_verdict: Some("accepted"),
            rejection_code: "unsupported_consumer",
            evidence: None,
            expected_bundle_code: ReleaseBundleInstallCode::UnsupportedConsumer,
            expected_bundle_status: ReleaseBundleInstallStatus::NonInstallable,
            issue_refs: &["#705", "#663"],
        },
    ]
}

#[test]
fn negative_fixtures_never_publish_product_native_handles() {
    let mut ay_registry = AYRegistry::default();
    let mut ty_slot = TyNativeSlot::default();
    let mut observed_codes = BTreeMap::new();

    for fixture in fixtures() {
        let (result, summary, bundle) = route_negative_fixture(&fixture);
        ay_registry.maybe_install(&fixture, &result);
        ty_slot.maybe_install(&fixture, &result);

        let decision = bundle.install_decision();
        assert!(
            !decision.is_installable(),
            "{} became installable",
            fixture.name
        );
        assert_eq!(decision.status, fixture.expected_bundle_status);
        assert_eq!(decision.code, fixture.expected_bundle_code);
        assert!(!result.cache_bundle_installed);
        assert_eq!(
            summary.cache_bundle_installed,
            result.cache_bundle_installed
        );

        assert_eq!(result.installed_artifact_id, None);
        assert_eq!(result.typed_symbol_id, None);
        assert_eq!(result.native_handle_id, None);
        assert_eq!(summary.installed_artifact_id, None);
        assert_eq!(summary.typed_symbol_id, None);
        assert_eq!(summary.ay_registry_entry, None);
        assert_eq!(summary.ty_native_handle, None);
        assert!(!ay_registry.contains(fixture.name));
        assert_eq!(ty_slot.installed_handle, None);

        if fixture.route.is_local() {
            assert_eq!(result.useful_native, 0);
            assert_eq!(summary.useful_native, 0);
        }

        if let Some((verdict, rejection_code)) = fixture.evidence.clone() {
            let evidence = evidence_summary(verdict.clone(), rejection_code.clone());
            assert_eq!(evidence.verdict.as_str(), verdict.as_str());
            assert_eq!(evidence.rejection_code.as_ref(), Some(&rejection_code));
            assert_eq!(rejection_code.as_str(), fixture.rejection_code);
        }

        summary.records_fixture_rejection(&fixture);
        observed_codes.insert(fixture.name, fixture.rejection_code);
    }

    assert_eq!(observed_codes.len(), fixtures().len());
}
