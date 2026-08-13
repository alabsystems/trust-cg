// trust-cg-codegen/tests/jit_replay_bundle_consumer_fixture.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use trust_cg_codegen::jit_contract::ArtifactChecksum;
use trust_cg_codegen::jit_release::{
    ReleaseArtifactManifestReference, ReleaseBundleFileReference, ReleaseProofReportReference,
    ReleaseReplayBundleMetadata, ReleaseReplayBundlePreflightVerdict, ReleaseReplayPreflightCode,
    ReleaseReplayPreflightDecision, preflight_release_replay_bundle_consumer,
};

fn sha256_ref(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity("sha256:".len() + digest.len() * 2);
    output.push_str("sha256:");
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(&mut output, "{byte:02x}");
    }
    output
}

fn add_file(
    files: &mut BTreeMap<String, Vec<u8>>,
    path: &str,
    value: Value,
) -> ReleaseBundleFileReference {
    let bytes = value.to_string().into_bytes();
    let sha256 = sha256_ref(&bytes);
    files.insert(path.to_owned(), bytes);
    ReleaseBundleFileReference::new(path, sha256)
}

fn add_proof(files: &mut BTreeMap<String, Vec<u8>>, path: &str) -> ReleaseProofReportReference {
    let bytes = json!({
        "obligation_set": "entry",
        "policy": "require_replay",
        "solver": "fixture",
        "verdict": "accepted"
    })
    .to_string()
    .into_bytes();
    let sha256 = sha256_ref(&bytes);
    files.insert(path.to_owned(), bytes);
    ReleaseProofReportReference::new(path, sha256)
        .with_policy("require_replay")
        .with_verdict("accepted")
        .with_solver("fixture")
        .with_obligation_set("entry")
        .with_timeout_ms(250)
}

fn replay_report(consumer: &str, generation: u64) -> Value {
    json!({
        "artifact_id": format!("{consumer}-artifact"),
        "generation": generation,
        "pc_map": [
            {
                "offset": 0,
                "size": 16,
                "symbol": format!("{consumer}_entry")
            }
        ],
        "statuses": [
            {
                "kind": "ok",
                "phase": "fixture_replay",
                "pc_offset": 0,
                "symbol": format!("{consumer}_entry")
            }
        ],
        "symbols": [format!("{consumer}_entry")]
    })
}

fn fixture_bundle(consumer: &str) -> (String, BTreeMap<String, Vec<u8>>) {
    let mut files = BTreeMap::new();
    let artifact_manifest = add_file(
        &mut files,
        "artifact.manifest.json",
        json!({
            "artifact_id": format!("{consumer}-artifact"),
            "schema_version": 1
        }),
    );
    let source_lock = add_file(
        &mut files,
        "source-lock.json",
        json!({ "consumer": consumer, "lock": "fixture" }),
    );
    let telemetry = add_file(
        &mut files,
        "telemetry/compile-telemetry.json",
        json!({ "artifact_id": format!("{consumer}-artifact"), "join": "fixture" }),
    );
    let release_package = add_file(
        &mut files,
        "release/package.json",
        json!({ "consumer": consumer, "package": "fixture" }),
    );
    let replay = add_file(&mut files, "replay/replay.json", replay_report(consumer, 7));
    let gate_results = add_file(
        &mut files,
        "gate-results.json",
        json!({ "gate": "accepted", "consumer": consumer }),
    );
    let proof = add_proof(&mut files, "proofs/proof-a.json");

    let mut bundle = ReleaseReplayBundleMetadata::new(
        consumer,
        "consumer_fixture",
        format!("{consumer}-artifact"),
        ReleaseArtifactManifestReference::new(
            artifact_manifest.path,
            artifact_manifest.sha256,
            1,
            ArtifactChecksum::new(0x703),
        ),
        source_lock,
        proof,
        telemetry,
        release_package,
        replay,
        gate_results,
    );
    bundle
        .metadata
        .insert("fixture".to_owned(), "consumer-neutral".to_owned());

    let parsed = serde_json::from_str::<Value>(&bundle.to_pretty_json());
    let Ok(mut manifest) = parsed else {
        return (bundle.to_pretty_json(), files);
    };
    manifest["generation"] = json!(7_u64);
    manifest["required_features"] = json!(["fixture-v1"]);

    (manifest.to_string(), files)
}

fn verdict(
    manifest: &str,
    files: &BTreeMap<String, Vec<u8>>,
) -> ReleaseReplayBundlePreflightVerdict {
    preflight_release_replay_bundle_consumer(manifest, files, &["fixture-v1"])
}

#[allow(clippy::too_many_arguments)] // Arguments enumerate the full golden verdict surface.
fn assert_golden_verdict(
    actual: &ReleaseReplayBundlePreflightVerdict,
    code: ReleaseReplayPreflightCode,
    install: ReleaseReplayPreflightDecision,
    replay: ReleaseReplayPreflightDecision,
    dispatch: ReleaseReplayPreflightDecision,
    gate: ReleaseReplayPreflightDecision,
    telemetry_join_result: &str,
    reducer_routing: &str,
    useful_native_counter_decision: &str,
) {
    assert_eq!(actual.taxonomy_code, code);
    assert_eq!(actual.taxonomy_code.as_str(), code.as_str());
    assert_eq!(actual.install, install);
    assert_eq!(actual.install.as_str(), install.as_str());
    assert_eq!(actual.replay, replay);
    assert_eq!(actual.replay.as_str(), replay.as_str());
    assert_eq!(actual.dispatch, dispatch);
    assert_eq!(actual.dispatch.as_str(), dispatch.as_str());
    assert_eq!(actual.gate, gate);
    assert_eq!(actual.gate.as_str(), gate.as_str());
    assert_eq!(actual.telemetry_join_result, telemetry_join_result);
    assert_eq!(actual.reducer_routing, reducer_routing);
    assert_eq!(
        actual.useful_native_counter_decision,
        useful_native_counter_decision
    );
}

fn mutate_manifest(manifest: &str, mutate: impl FnOnce(&mut Value)) -> String {
    let parsed = serde_json::from_str::<Value>(manifest);
    let Ok(mut value) = parsed else {
        return manifest.to_owned();
    };
    mutate(&mut value);
    value.to_string()
}

fn mutate_replay_file(files: &mut BTreeMap<String, Vec<u8>>, mutate: impl FnOnce(&mut Value)) {
    let Some(bytes) = files.get("replay/replay.json") else {
        return;
    };
    let parsed = serde_json::from_slice::<Value>(bytes);
    let Ok(mut report) = parsed else {
        return;
    };
    mutate(&mut report);
    files.insert(
        "replay/replay.json".to_owned(),
        report.to_string().into_bytes(),
    );
}

#[test]
fn consumer_fixture_accepts_minimal_ay_and_ty_replay_bundles() {
    for (consumer, reducer_routing) in [("ay", "ay_reducer"), ("ty", "ty_reducer")] {
        let (manifest, files) = fixture_bundle(consumer);

        assert_golden_verdict(
            &verdict(&manifest, &files),
            ReleaseReplayPreflightCode::Ok,
            ReleaseReplayPreflightDecision::Allow,
            ReleaseReplayPreflightDecision::Allow,
            ReleaseReplayPreflightDecision::Allow,
            ReleaseReplayPreflightDecision::Allow,
            "joined",
            reducer_routing,
            "use_native_counters",
        );
    }
}

#[test]
fn consumer_fixture_fails_closed_when_replay_report_is_missing() {
    let (manifest, mut files) = fixture_bundle("ay");
    files.remove("replay/replay.json");

    assert_golden_verdict(
        &verdict(&manifest, &files),
        ReleaseReplayPreflightCode::MissingReplayReport,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        "not_joined",
        "quarantine",
        "disable_native_counters",
    );
}

#[test]
fn consumer_fixture_fails_closed_when_replay_pc_map_statuses_or_symbols_are_missing() {
    for (field, code) in [
        ("pc_map", ReleaseReplayPreflightCode::MissingPcMap),
        ("statuses", ReleaseReplayPreflightCode::MissingStatuses),
        ("symbols", ReleaseReplayPreflightCode::MissingSymbols),
    ] {
        let (manifest, mut files) = fixture_bundle("ty");
        let manifest = mutate_manifest(&manifest, |value| {
            value["replay"]["sha256"] =
                json!("sha256:0000000000000000000000000000000000000000000000000000000000000000");
        });
        mutate_replay_file(&mut files, |report| {
            report[field] = json!([]);
        });
        let Some(bytes) = files.get("replay/replay.json") else {
            continue;
        };
        let replay_sha = sha256_ref(bytes);
        let manifest = mutate_manifest(&manifest, |value| {
            value["replay"]["sha256"] = json!(replay_sha);
        });

        assert_golden_verdict(
            &verdict(&manifest, &files),
            code,
            ReleaseReplayPreflightDecision::Deny,
            ReleaseReplayPreflightDecision::Deny,
            ReleaseReplayPreflightDecision::Deny,
            ReleaseReplayPreflightDecision::Deny,
            "not_joined",
            "quarantine",
            "disable_native_counters",
        );
    }
}

#[test]
fn consumer_fixture_fails_closed_for_unsupported_schema_or_unknown_required_feature() {
    let (manifest, files) = fixture_bundle("ay");
    let unsupported_schema = mutate_manifest(&manifest, |value| {
        value["schema"] = json!("trust-cg.phase6.release_replay_bundle.v2");
    });
    assert_golden_verdict(
        &verdict(&unsupported_schema, &files),
        ReleaseReplayPreflightCode::UnsupportedSchema,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        "not_joined",
        "quarantine",
        "disable_native_counters",
    );

    let unknown_feature = mutate_manifest(&manifest, |value| {
        value["required_features"] = json!(["fixture-v1", "future-required-feature"]);
    });
    assert_golden_verdict(
        &verdict(&unknown_feature, &files),
        ReleaseReplayPreflightCode::UnknownRequiredFeature,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        "not_joined",
        "quarantine",
        "disable_native_counters",
    );

    let unknown_compat_feature = mutate_manifest(&manifest, |value| {
        value["compat_required_features"] = json!(["fixture-v1", "future-compat-feature"]);
    });
    assert_golden_verdict(
        &verdict(&unknown_compat_feature, &files),
        ReleaseReplayPreflightCode::UnknownRequiredFeature,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        "not_joined",
        "quarantine",
        "disable_native_counters",
    );
}

#[test]
fn consumer_fixture_fails_closed_on_checksum_mismatch() {
    let (manifest, mut files) = fixture_bundle("ay");
    if let Some(bytes) = files.get_mut("telemetry/compile-telemetry.json") {
        bytes.extend_from_slice(b"\nmutated");
    }

    assert_golden_verdict(
        &verdict(&manifest, &files),
        ReleaseReplayPreflightCode::ChecksumMismatch,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        "not_joined",
        "quarantine",
        "disable_native_counters",
    );
}

#[test]
fn consumer_fixture_fails_closed_on_stale_generation() {
    let (manifest, mut files) = fixture_bundle("ty");
    mutate_replay_file(&mut files, |report| {
        report["generation"] = json!(6_u64);
    });
    let Some(bytes) = files.get("replay/replay.json") else {
        return;
    };
    let replay_sha = sha256_ref(bytes);
    let manifest = mutate_manifest(&manifest, |value| {
        value["replay"]["sha256"] = json!(replay_sha);
    });

    assert_golden_verdict(
        &verdict(&manifest, &files),
        ReleaseReplayPreflightCode::StaleGeneration,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        ReleaseReplayPreflightDecision::Deny,
        "not_joined",
        "quarantine",
        "disable_native_counters",
    );
}
