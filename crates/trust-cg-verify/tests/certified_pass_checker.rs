// trust-cg-verify/tests/certified_pass_checker.rs - Lean5 pass checker hook tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::PathBuf;
// Only the `#[cfg(unix)]` fake-lean5 script helper reads the clock (to name a
// temp dir); on non-unix hosts these tests are gated out, so keep the import
// unix-only to stay clean under `-D warnings`.
#[cfg(unix)]
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

use trust_cg_verify::certified_pass_chain::{
    CertifiedPassChain, CertifiedPassChainEntry, CertifiedPassChainError,
};
use trust_cg_verify::certified_pass_checker::{
    CheckerArtifactRef, Lean5CheckerMode, Lean5CheckerPolicy, Lean5CheckerResult,
    Lean5PassCertificateCheckRequest, PlaceholderTransportEvidence, check_lean5_pass_certificate,
    check_lean5_pass_certificate_file,
};

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("reports/fixtures")
        .join(name)
}

// Consumed only by the `#[cfg(unix)]` semantic-mode tests (which drive a
// real fake-lean5 shell script); gate it to match its callers so non-unix
// builds do not flag it as dead code under `-D warnings`.
#[cfg(unix)]
fn read_request(name: &str) -> Lean5PassCertificateCheckRequest {
    serde_json::from_str(&std::fs::read_to_string(fixture_path(name)).unwrap())
        .expect("fixture should parse")
}

/// Build a verified `Lean5PassCertificateCheckRequest` for the
/// gamma-vnncomp-demo chain entry at `certificate_index`.
///
/// The previous scaffold loaded JSON fixtures from
/// `reports/fixtures/gamma_vnncomp_demo_*_request.json`. Those fixtures are
/// not part of the open-source baseline. Tests now synthesize equivalent
/// requests in-process, mirroring the shape the production certified pass
/// chain (`Compiler::certified_pass_check_request`) writes for an trust-cg-opt
/// local certified pass run. The trust-cg-verify crate cannot depend on
/// trust-cg-codegen (it sits below it in the workspace graph), so the
/// shape is reproduced here.
fn gamma_demo_request(certificate_index: u64) -> Lean5PassCertificateCheckRequest {
    let (pass_name, pass_instance_id, local_checker_name) = match certificate_index {
        0 => (
            "const-fold-bv64",
            "const-fold:bv64:v1",
            "analytical-bv64 const-fold checker",
        ),
        1 => (
            "dce-pure-unused",
            "dce:pure-unused:v1",
            "trust-cg-opt dce checker",
        ),
        2 => (
            "bn-relu-relaxation-fusion",
            "bn-relu-relaxation-fusion:vnn.1+vnn.2:v1",
            "metal BN+ReLU relaxation metadata checker",
        ),
        other => panic!("unsupported gamma demo certificate_index: {other}"),
    };
    build_gamma_demo_request(
        certificate_index,
        pass_name,
        pass_instance_id,
        local_checker_name,
    )
}

fn build_gamma_demo_request(
    certificate_index: u64,
    pass_name: &str,
    pass_instance_id: &str,
    local_checker_name: &str,
) -> Lean5PassCertificateCheckRequest {
    let function_name = "gamma_vnncomp_demo";
    let compilation_unit = "gamma-vnncomp-demo";
    let obligation_hash =
        format!("trust-cg-opt-certified-pass-run-v1:{compilation_unit}:{pass_instance_id}");

    let run_record = serde_json::json!({
        "format_version": "trust-cg.opt.certified_pass_run.v1",
        "pass_name": pass_name,
        "pass_version": 1,
        "pass_instance_id": pass_instance_id,
        "function_name": function_name,
        "changed": false,
        "status": "verified",
        "certificate_count": 0,
        "failure_count": 0,
        "obligation_hash": obligation_hash.as_str(),
        "local_checker": {
            "kind": "trust-cg-opt-local",
            "name": local_checker_name,
            "version": "1",
            "status": "verified",
        },
        "summary": {
            "changed": false,
            "certificates": [],
            "failures": [],
        },
    });

    let run_record_bytes = serde_json::to_vec(&run_record).expect("run record JSON serializes");
    let run_record_digest = sha256_hex(&run_record_bytes);
    let run_record_uri = format!("trust-cg-opt://certified-pass-run/{run_record_digest}.json");
    let proof_digest =
        sha256_hex(format!("{pass_instance_id}:{obligation_hash}:{run_record_digest}").as_bytes());
    let proof_uri =
        format!("builtin://trust-cg-opt/certified-pass-run/{pass_instance_id}/placeholder-lean5");

    let canonical_obligation = CheckerArtifactRef {
        kind: "canonical_obligation".to_string(),
        uri: run_record_uri,
        digest: format!("sha256:{run_record_digest}"),
        media_type: Some("application/json".to_string()),
        placeholder_transport: None,
    };
    let proof_artifact = CheckerArtifactRef {
        kind: "lean_module".to_string(),
        uri: proof_uri,
        digest: format!("sha256:{proof_digest}"),
        media_type: Some("text/plain".to_string()),
        placeholder_transport: Some(PlaceholderTransportEvidence {
            accepted: true,
            note: "Transport check for an trust-cg-opt local certified pass run; semantic Lean replay is not part of this bounded slice.".to_string(),
        }),
    };
    let artifacts = vec![canonical_obligation, proof_artifact];
    let certificate_artifacts =
        serde_json::to_value(&artifacts).expect("artifacts JSON serializes");

    let certificate = serde_json::json!({
        "format_version": "trust-cg.certified_pass.v1",
        "pass": {
            "name": pass_name,
            "version": "1",
            "implementation_commit": "workspace-local",
            "instance_id": pass_instance_id,
            "pipeline_ordinal": certificate_index + 1,
            "target_profile": {
                "triple": "synthetic-gamma-demo",
                "cpu": "unspecified",
                "features": [],
            },
            "options_hash": format!("sha256:{}", sha256_hex(b"O2")),
        },
        "provenance": {
            "source": {
                "program_id": format!(
                    "trust-cg://{compilation_unit}/{function_name}/before/{pass_instance_id}"
                ),
                "node_ids": [],
                "expression_digest": obligation_hash.as_str(),
            },
            "rewrite": {
                "program_id": format!(
                    "trust-cg://{compilation_unit}/{function_name}/after/{pass_instance_id}"
                ),
                "node_ids": [],
                "expression_digest": obligation_hash.as_str(),
            },
        },
        "contract": {
            "mode": "local_pass_certificate_summary",
            "semantic_policy": {
                "source": "trust-cg-opt certified wrapper",
                "fail_closed": true,
            },
        },
        "domain": {
            "kind": "machine-ir",
            "certified_pass_run": &run_record,
        },
        "obligation_hash": obligation_hash.as_str(),
        "checker": {
            "kind": "lean5",
            "name": "trust-cg-cert-check",
            "version": "0.1.0",
            "proof_family": "trust-cg-opt-local-certified-pass-run-v1",
            "invocation": {
                "mode": "in_process",
                "command": ["trust-cg-codegen", "production-certified-pass-chain"],
                "working_directory_policy": "process",
            },
            "limits": {"timeout_ms": 1000},
            "replay_inputs": certificate_artifacts.clone(),
            "trust_base": [
                "lean5-kernel",
                "trust-cg-opt-local-certified-pass-run",
                "placeholder-transport-fixture",
            ],
        },
        "result": {
            "status": "verified",
            "checked_at_unix": 0,
            "duration_ms": 0,
            "local_checker": &run_record["local_checker"],
            "certificate_count": 0,
            "failure_count": 0,
        },
        "artifacts": {"refs": certificate_artifacts},
        "chain": {
            "compilation_unit": compilation_unit,
            "certificate_index": certificate_index,
            "must_be_verified": true,
        },
    });

    Lean5PassCertificateCheckRequest {
        format_version: "trust-cg.lean5_pass_check.request.v1".to_string(),
        certificate,
        obligation_hash,
        policy: Lean5CheckerPolicy {
            checker: "lean5".to_string(),
            mode: Lean5CheckerMode::PlaceholderTransport,
            timeout_ms: 1000,
            fail_closed: true,
            expected_lean_version: Some("Lean 5.0.0-placeholder".to_string()),
            lean5_binary: None,
        },
        artifacts,
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

#[cfg(unix)]
fn read_request_with_fake_lean5(
    name: &str,
    fake: &std::path::Path,
) -> Lean5PassCertificateCheckRequest {
    let mut request = read_request(name);
    request.policy.lean5_binary = Some(fake.to_string_lossy().into_owned());
    request.policy.timeout_ms = 10_000;
    request
}

#[cfg(unix)]
fn fake_lean5_script(name: &str, body: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("trust-cg-fake-lean5-{name}-{nanos}"));
    std::fs::create_dir_all(&dir).expect("fake Lean5 temp dir should be created");
    let path = dir.join("lean5");
    std::fs::write(&path, body).expect("fake Lean5 script should be written");
    let mut perms = std::fs::metadata(&path)
        .expect("fake Lean5 script metadata should exist")
        .permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&path, perms).expect("fake Lean5 script should be executable");
    path
}

#[test]
fn placeholder_transport_fixture_verifies_and_records_replay_metadata() {
    let report =
        check_lean5_pass_certificate_file(fixture_path("lean5_pass_checker_valid_request.json"))
            .expect("valid fixture should parse");

    assert!(report.result.is_verified());
    assert_eq!(
        report.obligation_hash,
        "trust-cg-pass-obligation-v1:sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    );
    assert_eq!(report.lean5.version, "Lean 5.0.0-placeholder");
    assert!(!report.lean5.observed);

    let proof = report
        .proof_artifact
        .expect("verified fixture should identify proof artifact");
    assert_eq!(proof.kind, "lean_module");
    assert_eq!(
        proof.digest,
        "sha256:9e5f026e536796e2353c77fe1f349bb087e263e295b7bb39067b4557666844cf"
    );

    assert_eq!(report.replay.checker, "lean5");
    assert_eq!(report.replay.mode, Lean5CheckerMode::PlaceholderTransport);
    assert!(report.replay.fail_closed);
    assert_eq!(report.replay.replay_inputs.len(), 2);
}

#[test]
fn invalid_certificate_hash_fails_closed() {
    let report =
        check_lean5_pass_certificate_file(fixture_path("lean5_pass_checker_invalid_request.json"))
            .expect("invalid fixture shape should still parse");

    assert_eq!(
        report.result,
        Lean5CheckerResult::Failed {
            reason: "request obligation_hash does not match certificate.obligation_hash"
                .to_string()
        }
    );
    assert!(!report.result.is_verified());
    assert!(report.replay.fail_closed);
}

#[cfg(unix)]
#[test]
fn semantic_mode_invokes_lean5_and_records_observed_version() {
    let fake = fake_lean5_script(
        "success",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "Checked 2 declarations in 1ms"
  echo "  2 passed, 0 failed"
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let request = read_request_with_fake_lean5("lean5_pass_checker_semantic_request.json", &fake);

    let report = check_lean5_pass_certificate(&request);

    assert!(report.result.is_verified(), "{:?}", report.result);
    assert_eq!(report.replay.mode, Lean5CheckerMode::Semantic);
    assert_eq!(report.lean5.version, "Lean5 fake 1.0.0");
    assert!(report.lean5.observed);
}

#[cfg(unix)]
#[test]
fn semantic_mode_allows_slow_version_probe_for_pinned_fake_lean5() {
    let fake = fake_lean5_script(
        "slow-version",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  sleep 2
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "Checked 2 declarations in 1ms"
  echo "  2 passed, 0 failed"
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let request = read_request_with_fake_lean5("lean5_pass_checker_semantic_request.json", &fake);

    let report = check_lean5_pass_certificate(&request);

    assert!(report.result.is_verified(), "{:?}", report.result);
    assert_eq!(report.lean5.version, "Lean5 fake 1.0.0");
    assert!(report.lean5.observed);
}

#[cfg(unix)]
#[test]
fn semantic_mode_accepts_proof_indexed_rewrite_core_fixture() {
    let fake = fake_lean5_script(
        "proof-indexed-core",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "Checked 18 declarations in 1ms"
  echo "  18 passed, 0 failed"
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let request = read_request_with_fake_lean5(
        "lean5_pass_checker_proof_indexed_rewrite_core_request.json",
        &fake,
    );

    let report = check_lean5_pass_certificate(&request);

    assert!(report.result.is_verified(), "{:?}", report.result);
    assert_eq!(report.replay.mode, Lean5CheckerMode::Semantic);
    assert_eq!(report.lean5.version, "Lean5 fake 1.0.0");
    let proof = report
        .proof_artifact
        .expect("proof-indexed core fixture should identify proof artifact");
    assert_eq!(proof.uri, "reports/fixtures/ProofIndexedRewriteCore.lean");
    assert_eq!(
        proof.digest,
        "sha256:c36eae9980575686ce85ec7568d2fc29fb43fa07e44c280c59e3f26ff4ccb392"
    );
}

#[cfg(unix)]
#[test]
fn semantic_mode_accepts_proof_indexed_rewrite_concrete_fixture() {
    let fake = fake_lean5_script(
        "proof-indexed-concrete",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "Checked 26 declarations in 1ms"
  echo "  26 passed, 0 failed"
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let request = read_request_with_fake_lean5(
        "lean5_pass_checker_proof_indexed_rewrite_concrete_request.json",
        &fake,
    );

    let report = check_lean5_pass_certificate(&request);

    assert!(report.result.is_verified(), "{:?}", report.result);
    assert_eq!(report.replay.mode, Lean5CheckerMode::Semantic);
    assert_eq!(report.lean5.version, "Lean5 fake 1.0.0");
    let proof = report
        .proof_artifact
        .expect("proof-indexed concrete fixture should identify proof artifact");
    assert_eq!(
        proof.uri,
        "reports/fixtures/ProofIndexedRewriteConcrete.lean"
    );
    assert_eq!(
        proof.digest,
        "sha256:dc5d8253a8bd0a33fd258ec6a16110c41bae9e35a881e179ee872a7fe304ce2a"
    );
}

#[cfg(unix)]
#[test]
fn semantic_mode_accepts_proof_indexed_rewrite_context_fixture() {
    let fake = fake_lean5_script(
        "proof-indexed-context",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "Checked 27 declarations in 1ms"
  echo "  27 passed, 0 failed"
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let request = read_request_with_fake_lean5(
        "lean5_pass_checker_proof_indexed_rewrite_context_request.json",
        &fake,
    );

    let report = check_lean5_pass_certificate(&request);

    assert!(report.result.is_verified(), "{:?}", report.result);
    assert_eq!(report.replay.mode, Lean5CheckerMode::Semantic);
    assert_eq!(report.lean5.version, "Lean5 fake 1.0.0");
    let proof = report
        .proof_artifact
        .expect("proof-indexed context fixture should identify proof artifact");
    assert_eq!(
        proof.uri,
        "reports/fixtures/ProofIndexedRewriteContext.lean"
    );
    assert_eq!(
        proof.digest,
        "sha256:46685390451b9ce05e4e56fa5cb43b36d18f22fd166961f16cf7dc73fb5ba215"
    );
}

#[cfg(unix)]
#[test]
fn semantic_mode_accepts_proof_indexed_rewrite_chain_fixture() {
    let fake = fake_lean5_script(
        "proof-indexed-chain",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "Checked 24 declarations in 1ms"
  echo "  24 passed, 0 failed"
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let request = read_request_with_fake_lean5(
        "lean5_pass_checker_proof_indexed_rewrite_chain_request.json",
        &fake,
    );

    let report = check_lean5_pass_certificate(&request);

    assert!(report.result.is_verified(), "{:?}", report.result);
    assert_eq!(report.replay.mode, Lean5CheckerMode::Semantic);
    assert_eq!(report.lean5.version, "Lean5 fake 1.0.0");
    let proof = report
        .proof_artifact
        .expect("proof-indexed chain fixture should identify proof artifact");
    assert_eq!(proof.uri, "reports/fixtures/ProofIndexedRewriteChain.lean");
    assert_eq!(
        proof.digest,
        "sha256:6f6a009c30d790a7a7fc2f29993a7a7f64887cbe5b17bc61cfe522ee8adb5430"
    );
}

#[cfg(unix)]
#[test]
fn semantic_mode_accepts_proof_indexed_extraction_fixture() {
    let fake = fake_lean5_script(
        "proof-indexed-extraction",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "Checked 28 declarations in 1ms"
  echo "  28 passed, 0 failed"
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let request = read_request_with_fake_lean5(
        "lean5_pass_checker_proof_indexed_extraction_request.json",
        &fake,
    );

    let report = check_lean5_pass_certificate(&request);

    assert!(report.result.is_verified(), "{:?}", report.result);
    assert_eq!(report.replay.mode, Lean5CheckerMode::Semantic);
    assert_eq!(report.lean5.version, "Lean5 fake 1.0.0");
    let proof = report
        .proof_artifact
        .expect("proof-indexed extraction fixture should identify proof artifact");
    assert_eq!(proof.uri, "reports/fixtures/ProofIndexedExtraction.lean");
    assert_eq!(
        proof.digest,
        "sha256:c0e60991c21c8fe96c70c2166ca07c4646f1658874f5277a8a8ec89ae840eb33"
    );
}

#[cfg(unix)]
#[test]
fn semantic_mode_accepts_proof_indexed_egraph_fixture() {
    let fake = fake_lean5_script(
        "proof-indexed-egraph",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "Checked 26 declarations in 1ms"
  echo "  26 passed, 0 failed"
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let request = read_request_with_fake_lean5(
        "lean5_pass_checker_proof_indexed_egraph_request.json",
        &fake,
    );

    let report = check_lean5_pass_certificate(&request);

    assert!(report.result.is_verified(), "{:?}", report.result);
    assert_eq!(report.replay.mode, Lean5CheckerMode::Semantic);
    assert_eq!(report.lean5.version, "Lean5 fake 1.0.0");
    let proof = report
        .proof_artifact
        .expect("proof-indexed egraph fixture should identify proof artifact");
    assert_eq!(proof.uri, "reports/fixtures/ProofIndexedEGraph.lean");
    assert_eq!(
        proof.digest,
        "sha256:141bd844146114c00865a5651377c8a31342efc7a0d39900b47c39e1f83203bc"
    );
}

#[cfg(unix)]
#[test]
fn semantic_mode_rejects_digest_mismatch_before_invoking_lean5() {
    let mut request = read_request("lean5_pass_checker_semantic_request.json");
    request.artifacts[1].digest =
        "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string();

    let report = check_lean5_pass_certificate(&request);

    assert!(matches!(
        report.result,
        Lean5CheckerResult::Failed { ref reason }
            if reason.contains("Lean proof artifact digest mismatch")
    ));
    assert!(!report.result.is_verified());
    assert!(!report.lean5.observed);
}

#[cfg(unix)]
#[test]
fn semantic_mode_rejects_missing_lean_artifact() {
    let mut request = read_request("lean5_pass_checker_semantic_request.json");
    request
        .artifacts
        .retain(|artifact| artifact.kind != "lean_module");

    let report = check_lean5_pass_certificate(&request);

    assert_eq!(
        report.result,
        Lean5CheckerResult::Failed {
            reason: "missing Lean proof artifact reference".to_string(),
        }
    );
    assert!(!report.result.is_verified());
}

#[cfg(unix)]
#[test]
fn semantic_mode_fails_closed_on_lean5_trust_debt_rejection() {
    let fake = fake_lean5_script(
        "trust-debt",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  echo "warning: declaration uses explicit sorry" >&2
  echo "Error: check failed" >&2
  exit 1
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let mut request =
        read_request_with_fake_lean5("lean5_pass_checker_semantic_request.json", &fake);
    request.artifacts[1].uri = "reports/fixtures/ProofIndexedRewriteTrustDebt.lean".to_string();
    request.artifacts[1].digest =
        "sha256:4ee45274497418924e1f321d6e59a0e2b75b8300252fba4cb9c4a17c55d33220".to_string();

    let report = check_lean5_pass_certificate(&request);

    assert!(matches!(
        report.result,
        Lean5CheckerResult::Failed { ref reason }
            if reason.contains("explicit sorry trust debt")
    ));
    assert!(!report.result.is_verified());
    assert!(report.lean5.observed);
}

#[cfg(unix)]
#[test]
fn semantic_mode_times_out_fail_closed() {
    let fake = fake_lean5_script(
        "timeout",
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "Lean5 fake 1.0.0"
  exit 0
fi
if [ "$1" = "check" ]; then
  sleep 2
  exit 0
fi
echo "unsupported invocation: $@" >&2
exit 2
"#,
    );
    let mut request = read_request("lean5_pass_checker_semantic_request.json");
    request.policy.lean5_binary = Some(fake.to_string_lossy().into_owned());
    request.policy.timeout_ms = 250;

    let report = check_lean5_pass_certificate(&request);

    assert_eq!(
        report.result,
        Lean5CheckerResult::Timeout { timeout_ms: 250 }
    );
    assert!(!report.result.is_verified());
}

#[test]
fn gamma_vnncomp_demo_available_pass_entries_verify() {
    for (idx, label) in [(0u64, "const-fold"), (1, "dce"), (2, "bn-relu")] {
        let request = gamma_demo_request(idx);
        let report = check_lean5_pass_certificate(&request);

        assert!(report.result.is_verified(), "{label}");
        assert_eq!(report.lean5.version, "Lean 5.0.0-placeholder");
        assert_eq!(report.replay.mode, Lean5CheckerMode::PlaceholderTransport);
        assert!(report.replay.fail_closed);
    }
}

#[test]
fn gamma_vnncomp_demo_tampered_or_skipped_entries_fail_closed() {
    let mut tampered = gamma_demo_request(0);
    tampered.obligation_hash =
        "trust-cg-pass-obligation-v1:sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            .to_string();

    let report = check_lean5_pass_certificate(&tampered);
    assert_eq!(
        report.result,
        Lean5CheckerResult::Failed {
            reason: "request obligation_hash does not match certificate.obligation_hash"
                .to_string()
        }
    );

    let mut skipped = gamma_demo_request(1);
    skipped.certificate["result"]["status"] = serde_json::json!("skipped");

    let report = check_lean5_pass_certificate(&skipped);
    assert_eq!(
        report.result,
        Lean5CheckerResult::Failed {
            reason: "certificate result status is not verified: skipped".to_string()
        }
    );
}

#[test]
fn certified_pass_chain_accepts_ordered_gamma_const_fold_dce_and_bn_relu_entries() {
    let chain = CertifiedPassChain::check_requests(vec![
        gamma_demo_request(0),
        gamma_demo_request(1),
        gamma_demo_request(2),
    ])
    .expect("ordered verified gamma synthetic requests should validate");

    assert_eq!(chain.compilation_unit(), "gamma-vnncomp-demo");
    assert_eq!(chain.entries().len(), 3);
    assert_eq!(chain.entries()[0].certificate_index(), Some(0));
    assert_eq!(chain.entries()[0].pass_name(), Some("const-fold-bv64"));
    assert_eq!(chain.entries()[1].certificate_index(), Some(1));
    assert_eq!(chain.entries()[1].pass_name(), Some("dce-pure-unused"));
    assert_eq!(chain.entries()[2].certificate_index(), Some(2));
    assert_eq!(
        chain.entries()[2].pass_name(),
        Some("bn-relu-relaxation-fusion")
    );
    assert!(
        chain
            .entries()
            .iter()
            .all(|entry| entry.report.result.is_verified())
    );
}

#[test]
fn certified_pass_chain_accepts_ordered_gamma_const_fold_and_dce_entries() {
    let chain =
        CertifiedPassChain::check_requests(vec![gamma_demo_request(0), gamma_demo_request(1)])
            .expect("ordered verified gamma synthetic requests should validate");

    assert_eq!(chain.compilation_unit(), "gamma-vnncomp-demo");
    assert_eq!(chain.entries().len(), 2);
    assert_eq!(chain.entries()[0].certificate_index(), Some(0));
    assert_eq!(chain.entries()[0].pass_name(), Some("const-fold-bv64"));
    assert_eq!(chain.entries()[1].certificate_index(), Some(1));
    assert_eq!(chain.entries()[1].pass_name(), Some("dce-pure-unused"));
    assert!(
        chain
            .entries()
            .iter()
            .all(|entry| entry.report.result.is_verified())
    );
}

#[test]
fn certified_pass_chain_rejects_out_of_order_certificate_indices() {
    let err =
        CertifiedPassChain::check_requests(vec![gamma_demo_request(1), gamma_demo_request(0)])
            .expect_err("out-of-order gamma synthetic requests must be rejected");

    assert_eq!(
        err,
        CertifiedPassChainError::CertificateIndexOutOfOrder {
            entry_index: 0,
            expected_index: 0,
            certificate_index: 1,
        }
    );
}

#[test]
fn certified_pass_chain_rejects_non_verified_reports() {
    for result in [
        Lean5CheckerResult::Skipped {
            reason: "not replayed".to_string(),
        },
        Lean5CheckerResult::Failed {
            reason: "counterexample".to_string(),
        },
        Lean5CheckerResult::Timeout { timeout_ms: 1000 },
    ] {
        let request = gamma_demo_request(0);
        let mut report = check_lean5_pass_certificate(&request);
        report.result = result.clone();

        let err = CertifiedPassChain::from_entries(vec![CertifiedPassChainEntry::from_report(
            request, report,
        )])
        .expect_err("non-verified reports must be rejected");

        assert_eq!(
            err,
            CertifiedPassChainError::ReportNotVerified {
                entry_index: 0,
                result,
            }
        );
    }
}

#[test]
fn certified_pass_chain_rejects_non_verified_certificate_statuses() {
    for status in ["skipped", "failed", "timeout"] {
        let mut request = gamma_demo_request(0);
        let report = check_lean5_pass_certificate(&request);
        request.certificate["result"]["status"] = serde_json::json!(status);

        let err = CertifiedPassChain::from_entries(vec![CertifiedPassChainEntry::from_report(
            request, report,
        )])
        .expect_err("non-verified certificate statuses must be rejected");

        assert_eq!(
            err,
            CertifiedPassChainError::CertificateResultNotVerified {
                entry_index: 0,
                status: status.to_string(),
            }
        );
    }
}

#[test]
fn certified_pass_chain_rejects_must_verify_and_obligation_hash_mismatch() {
    let mut request = gamma_demo_request(0);
    let report = check_lean5_pass_certificate(&request);
    request.certificate["chain"]["must_be_verified"] = serde_json::json!(false);

    let err = CertifiedPassChain::from_entries(vec![CertifiedPassChainEntry::from_report(
        request, report,
    )])
    .expect_err("must_be_verified=false must be rejected");
    assert_eq!(
        err,
        CertifiedPassChainError::CertificateMustBeVerified { entry_index: 0 }
    );

    let mut request = gamma_demo_request(0);
    let report = check_lean5_pass_certificate(&request);
    request.certificate["obligation_hash"] = serde_json::json!(
        "trust-cg-pass-obligation-v1:sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
    );

    let err = CertifiedPassChain::from_entries(vec![CertifiedPassChainEntry::from_report(
        request, report,
    )])
    .expect_err("request/certificate/report hash disagreement must be rejected");
    assert!(matches!(
        err,
        CertifiedPassChainError::ObligationHashMismatch { entry_index: 0, .. }
    ));
}

#[test]
fn certified_pass_chain_rejects_missing_or_hash_mismatched_proof_artifacts() {
    let original = gamma_demo_request(0);
    let report = check_lean5_pass_certificate(&original);
    let mut request = original.clone();
    request
        .artifacts
        .retain(|artifact| artifact.kind != "lean_module");

    let err = CertifiedPassChain::from_entries(vec![CertifiedPassChainEntry::from_report(
        request,
        report.clone(),
    )])
    .expect_err("missing proof artifact must be rejected");
    assert_eq!(
        err,
        CertifiedPassChainError::ProofArtifactMissing {
            entry_index: 0,
            artifact_source: "request.artifacts",
        }
    );

    let mut request = original;
    // refs[1] is the `lean_module` proof artifact (refs[0] is the
    // canonical_obligation); tamper the proof artifact digest so it disagrees
    // with the request/report proof artifact identity.
    request.certificate["artifacts"]["refs"][1]["digest"] = serde_json::json!(
        "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
    );

    let err = CertifiedPassChain::from_entries(vec![CertifiedPassChainEntry::from_report(
        request, report,
    )])
    .expect_err("proof artifact digest mismatch must be rejected");
    assert!(matches!(
        err,
        CertifiedPassChainError::ProofArtifactMismatch { entry_index: 0, .. }
    ));
}

#[test]
fn certified_pass_chain_rejects_tampered_verified_report_summary() {
    let request = gamma_demo_request(0);
    let mut report = check_lean5_pass_certificate(&request);
    report.replay.fail_closed = false;

    let err = CertifiedPassChain::from_entries(vec![CertifiedPassChainEntry::from_report(
        request, report,
    )])
    .expect_err("tampered report summary must be rejected");

    assert_eq!(
        err,
        CertifiedPassChainError::TamperedReportSummary {
            entry_index: 0,
            reason: "report.replay.fail_closed does not match checker replay".to_string(),
        }
    );
}
