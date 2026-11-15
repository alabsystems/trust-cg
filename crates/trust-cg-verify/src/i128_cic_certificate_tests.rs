use super::*;
use crate::checked_mul_i128_proofs as family;
use crate::smt::SmtExpr;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
pub(super) static FORBID_PRODUCER: AtomicBool = AtomicBool::new(false);
pub(super) static PRODUCER_CALLS: AtomicUsize = AtomicUsize::new(0);
fn subjects() -> [ProofObligation; 3] {
    [
        family::proof_checked_umul_i128_limb_check_flag(),
        family::proof_checked_smul_i128_limb_check_flag(),
        family::proof_checked_umul_i128_const_limit_flag(),
    ]
}
fn produce(input: &ProofObligation) -> CheckedOriginalI128Certificate {
    try_original_i128_certificate(input, 120_000)
        .expect("actual original theorem must close within unchanged120s budget")
}

#[test]
fn retained_context_schema_and_profile_do_not_select_a_checker() {
    let actual: serde_json::Value = serde_json::from_str(MANIFEST).unwrap();
    for (field, value) in [
        ("schema", serde_json::json!(2)),
        ("environment_dag_format", serde_json::json!("CLENEDG1")),
        (
            "environment_schema",
            serde_json::json!("clean-env-bincode-v1"),
        ),
        ("source_lean_level_profile", serde_json::json!("Lean48")),
    ] {
        let mut changed = actual.clone();
        changed[field] = value;
        let bytes = serde_json::to_vec(&changed).unwrap();
        assert!(decode_bundle_manifest(CONTEXT, &bytes).is_err(), "{field}");
    }
    // Matching attacker-updated lengths and hashes still grant no legacy
    // decoder policy to an old graph envelope.
    let raw = b"CLENEDG1";
    let compressed = zstd::stream::encode_all(raw.as_slice(), 1).unwrap();
    let mut rebound = actual;
    rebound["raw_bytes"] = serde_json::json!(raw.len());
    rebound["raw_sha256"] = serde_json::json!(sha(raw));
    rebound["zstd_bytes"] = serde_json::json!(compressed.len());
    rebound["zstd_sha256"] = serde_json::json!(sha(&compressed));
    let bytes = serde_json::to_vec(&rebound).unwrap();
    assert!(
        matches!(check_context_bytes(&compressed, &bytes), Err(error) if error.contains("selected published payload"))
    );
}

#[test]
fn retained_context_replays_under_the_selected_kernel() {
    context().unwrap_or_else(|error| panic!("actual retained context was refused: {error}"));
}
fn wire(cert: &CheckedOriginalI128Certificate) -> Wire {
    serde_json::from_slice(cert.packet()).unwrap()
}
fn encode(wire: Wire) -> Vec<u8> {
    serde_json::to_vec(&wire).unwrap()
}
fn retain(label: &str, bytes: &[u8]) {
    if let Some(dir) = trust_cg_process_env::var_os("TRUST_CG_I128_CIC_OUT") {
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join(label), bytes).unwrap();
    }
}
#[test]
fn three_actual_original_goals_retain_exact_replayable_packets() {
    for (index, input) in subjects().iter().enumerate() {
        let start = std::time::Instant::now();
        let cert = produce(input);
        let replay = replay_original_i128_certificate(input, cert.packet()).unwrap();
        assert_eq!(cert.packet(), replay.packet());
        assert_eq!(cert.goal_sha256(), replay.goal_sha256());
        assert_eq!(cert.environment_sha256(), replay.environment_sha256());
        assert_eq!(cert.checker_sha256().len(), 64);
        retain(&format!("original-{index}.packet.json"), cert.packet());
        retain(&format!("original-{index}.identity.json"),serde_json::to_vec_pretty(&serde_json::json!({"packet_bytes":cert.packet().len(),"packet_sha256":cert.packet_sha256(),"goal_sha256":cert.goal_sha256(),"environment_sha256":cert.environment_sha256(),"context_producer_clean_revision":cert.context_producer_clean_revision(),"actual_checker_sha256":cert.checker_sha256(),"seconds":start.elapsed().as_secs_f64()})).unwrap().as_slice());
    }
}
#[test]
fn false_actual_equations_decline_even_with_fresh_packet_bindings() {
    for mut input in subjects() {
        input.aarch64_expr = SmtExpr::bv_const(0, 1);
        assert!(try_original_i128_certificate(&input, 120_000).is_none());
    }
    let input = subjects().into_iter().next().unwrap();
    let cert = produce(&input);
    let mut altered = input.clone();
    altered.trust_ir_expr = SmtExpr::bv_const(0, 1);
    assert!(replay_original_i128_certificate(&altered, cert.packet()).is_err());
    altered = input.clone();
    altered.inputs.swap(0, 3);
    assert!(replay_original_i128_certificate(&altered, cert.packet()).is_err());
    altered = input;
    altered.name.push_str(" rebound");
    assert!(replay_original_i128_certificate(&altered, cert.packet()).is_err());
}
#[test]
fn untrusted_labels_hashes_context_and_goal_bytes_are_not_authority() {
    let input = subjects().into_iter().next().unwrap();
    let cert = produce(&input);
    for change in 0..8 {
        let mut w = wire(&cert);
        match change {
            0 => w.environment_sha256 = "0".repeat(64),
            1 => w.clean_revision = "different-checker-source".into(),
            2 => {
                w.original_binding[0] ^= 1;
                w.original_binding_sha256 = sha(&w.original_binding)
            }
            3 => {
                w.goal = b"{\"cycle\":0}".to_vec();
                w.goal_sha256 = sha(&w.goal)
            }
            4 => {
                w.proof = serde_json::to_vec(&Expr::bvar(0)).unwrap();
                w.proof_sha256 = sha(&w.proof)
            }
            5 => w.schema = 1,
            6 => w.goal_sha256 = "0".repeat(64),
            _ => w.original_binding_sha256 = "0".repeat(64),
        };
        assert!(
            replay_original_i128_certificate(&input, &encode(w)).is_err(),
            "mutation {change}"
        );
    }
    let mut value: serde_json::Value = serde_json::from_slice(cert.packet()).unwrap();
    value["unchecked_override"] = serde_json::json!(true);
    assert!(
        replay_original_i128_certificate(&input, &serde_json::to_vec(&value).unwrap()).is_err()
    );
    assert!(replay_original_i128_certificate(&input, &vec![0; MAX_PACKET_BYTES + 1]).is_err());
    assert!(replay_original_i128_certificate(&input, b"").is_err());
}
#[test]
fn wrong_retained_theorem_reaches_kernel_and_is_rejected() {
    let input = subjects().into_iter().next().unwrap();
    let cert = produce(&input);
    let mut w = wire(&cert);
    w.candidate = Candidate::UnsignedConst;
    w.proof = serde_json::to_vec(&w.candidate.proof()).unwrap();
    w.proof_sha256 = sha(&w.proof);
    let result = replay_original_i128_certificate(&input, &encode(w));
    assert!(result.unwrap_err().contains("original CIC proof refused"));
}
#[test]
fn assumptions_widths_and_reconstructed_source_authority_are_not_invented() {
    let input = subjects().into_iter().next().unwrap();
    let cert = produce(&input);
    let mut altered = input.clone();
    altered.machine_side_provenance = MachineSideProvenance::Reconstructed {
        from_opcode: "forged".into(),
        arity: 2,
    };
    assert!(replay_original_i128_certificate(&altered, cert.packet()).is_err());
    assert!(try_original_i128_certificate(&altered, 120_000).is_none());
    altered = input.clone();
    altered.preconditions.push(SmtExpr::BoolConst(true));
    assert!(try_original_i128_certificate(&altered, 120_000).is_none());
    altered = input.clone();
    altered.inputs[0].1 = 63;
    assert!(try_original_i128_certificate(&altered, 120_000).is_none());
    altered = input;
    altered.inputs[0].0 = altered.inputs[1].0.clone();
    assert!(try_original_i128_certificate(&altered, 120_000).is_none());
}
#[test]
fn public_verifier_retains_cic_evidence_without_an_ay_reuse_origin() {
    let input = subjects().into_iter().next().unwrap();
    let config = crate::ay_bridge::AYConfig {
        timeout_ms: 120_000,
        ..Default::default()
    };
    let verdict = crate::ay_bridge::verify_with_ay_attributed(&input, &config);
    assert_eq!(verdict.result, crate::ay_bridge::AYResult::Verified);
    assert!(verdict.solver.is_none());
    let crate::ay_bridge::AyVerdictSource::OriginalCicCertificate { certificate } = verdict.source
    else {
        panic!("CIC provenance lost")
    };
    assert!(!certificate.packet().is_empty());
    assert!(
        try_original_i128_certificate(&input, 0).is_some(),
        "zero is the established unlimited budget"
    );
}
#[test]
fn fresh_process_replay_restores_existing_proofs_without_the_producer() {
    let dir = tempfile::tempdir().unwrap();
    for (index, input) in subjects().iter().enumerate() {
        let checked = produce(input);
        let files = checked.persist_to(dir.path()).unwrap();
        std::fs::write(
            dir.path().join(format!("{index}.paths.json")),
            serde_json::to_vec(&serde_json::json!({
                "packet": files.packet(),
                "context": files.context_zstd(),
                "manifest": files.manifest(),
            }))
            .unwrap(),
        )
        .unwrap();
    }
    let start = std::time::Instant::now();
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .arg("--exact")
        .arg("i128_cic_certificate::tests::replay_only_child")
        .arg("--nocapture")
        .env("I128_CIC_REPLAY_DIRECTORY", dir.path())
        .output()
        .unwrap();
    retain("fresh-process.stdout", &out.stdout);
    retain("fresh-process.stderr", &out.stderr);
    assert!(
        out.status.success(),
        "fresh replay failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        text.contains("CIC_REPLAY_COUNT=3 PRODUCER_CALLS=0"),
        "fresh replay denominator missing: {text}"
    );
    retain("fresh-process.json",serde_json::to_vec_pretty(&serde_json::json!({"exit":out.status.code(),"actual_proofs":3,"producer_calls":0,"seconds":start.elapsed().as_secs_f64()})).unwrap().as_slice());
}
#[test]
fn live_regeneration_bypasses_the_cic_producer() {
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .arg("--exact")
        .arg("i128_cic_certificate::tests::replay_only_child")
        .arg("--nocapture")
        .env("I128_CIC_RECORD_ONLY", "1")
        .output()
        .unwrap();
    retain("recording-process.stdout", &out.stdout);
    retain("recording-process.stderr", &out.stderr);
    assert!(
        out.status.success(),
        "recording control failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(String::from_utf8_lossy(&out.stdout).contains("REGEN_CIC_CALLS=0"));
}
#[test]
fn replay_only_child() {
    if std::env::var_os("I128_CIC_RECORD_ONLY").is_some() {
        FORBID_PRODUCER.store(true, Ordering::SeqCst);
        crate::verdict_db::record_begin();
        let input = subjects().into_iter().next().unwrap();
        let verdict = crate::ay_bridge::verify_with_ay_attributed(
            &input,
            &crate::ay_bridge::AYConfig {
                timeout_ms: 1,
                ..Default::default()
            },
        );
        let rows = crate::verdict_db::record_take();
        assert!(!matches!(
            verdict.source,
            crate::ay_bridge::AyVerdictSource::OriginalCicCertificate { .. }
        ));
        assert_eq!(PRODUCER_CALLS.load(Ordering::SeqCst), 0);
        println!(
            "REGEN_CIC_CALLS=0 LIVE_ROWS={} {}",
            rows.len(),
            verdict.provenance()
        );
        return;
    }
    let Some(dir) = std::env::var_os("I128_CIC_REPLAY_DIRECTORY") else {
        return;
    };
    FORBID_PRODUCER.store(true, Ordering::SeqCst);
    let dir = std::path::PathBuf::from(dir);
    let mut count = 0;
    for (index, input) in subjects().iter().enumerate() {
        let paths: serde_json::Value = serde_json::from_slice(
            &std::fs::read(dir.join(format!("{index}.paths.json"))).unwrap(),
        )
        .unwrap();
        let bytes = std::fs::read(paths["packet"].as_str().unwrap()).unwrap();
        let context = std::fs::read(paths["context"].as_str().unwrap()).unwrap();
        let manifest = std::fs::read(paths["manifest"].as_str().unwrap()).unwrap();
        let certificate =
            replay_original_i128_artifacts(input, &bytes, &context, &manifest).unwrap();
        assert_eq!(sha(&bytes), certificate.packet_sha256());
        count += 1;
    }
    assert_eq!(count, 3);
    assert_eq!(PRODUCER_CALLS.load(Ordering::SeqCst), 0);
    println!("CIC_REPLAY_COUNT={count} PRODUCER_CALLS=0");
}

#[test]
fn complete_artifact_bytes_replay_and_substitution_refuses() {
    let input = subjects().into_iter().next().unwrap();
    let cert = produce(&input);
    let dir = tempfile::tempdir().unwrap();
    let files = cert.persist_to(dir.path()).unwrap();
    let packet = std::fs::read(files.packet()).unwrap();
    let context = std::fs::read(files.context_zstd()).unwrap();
    let manifest = std::fs::read(files.manifest()).unwrap();
    let replay = replay_original_i128_artifacts(&input, &packet, &context, &manifest).unwrap();
    assert_eq!(replay.packet(), cert.packet());
    let mut changed = context.clone();
    changed[0] ^= 1;
    assert!(replay_original_i128_artifacts(&input, &packet, &changed, &manifest).is_err());
    let mut changed_manifest = manifest.clone();
    changed_manifest[0] ^= 1;
    assert!(replay_original_i128_artifacts(&input, &packet, &context, &changed_manifest).is_err());
    let mut false_input = input;
    false_input.aarch64_expr = SmtExpr::bv_const(0, 1);
    assert!(replay_original_i128_artifacts(&false_input, &packet, &context, &manifest).is_err());
    assert!(cert.persist_to(&dir.path().join("missing")).is_err());
}

#[test]
fn requested_ordinary_artifact_sink_is_used_and_failure_declines() {
    for missing in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let output = if missing {
            dir.path().join("missing")
        } else {
            dir.path().to_path_buf()
        };
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .arg("--exact")
            .arg("i128_cic_certificate::tests::artifact_sink_child")
            .arg("--nocapture")
            .env(
                "I128_CIC_ARTIFACT_SINK_CONTROL",
                if missing { "decline" } else { "retain" },
            )
            .env("TRUST_CG_I128_CIC_ARTIFACT_OUT", &output)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(String::from_utf8_lossy(&out.stdout).contains("ACTUAL_SINK_CONTROL=PASS"));
        if !missing {
            let count = std::fs::read_dir(dir.path()).unwrap().count();
            assert_eq!(
                count, 3,
                "actual production sink retains packet/context/manifest"
            );
        }
    }
}

#[test]
fn artifact_sink_child() {
    let Some(mode) = std::env::var_os("I128_CIC_ARTIFACT_SINK_CONTROL") else {
        return;
    };
    let input = subjects().into_iter().next().unwrap();
    let checked = try_original_i128_certificate(&input, 120_000);
    if mode == "decline" {
        assert!(checked.is_none());
    } else {
        assert!(checked.is_some());
    }
    println!("ACTUAL_SINK_CONTROL=PASS");
}
