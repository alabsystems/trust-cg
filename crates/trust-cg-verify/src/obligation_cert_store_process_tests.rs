//! Hermetic Unix process controls, not external proof coverage.

use super::tests::{TRANSCRIPT_CAPABLE_STDOUT, shell_single_quote};
use super::*;
use std::os::unix::fs::PermissionsExt;
use std::time::Instant;

/// A new fixture, started once before any budget (`test_fixtures::warm`), so
/// the budgets below bound what it does, not the host's first-exec assessment
/// of a new file.
fn script(dir: &Path, name: &str, body: &str) -> PathBuf {
    use crate::ay_identity::test_fixtures::{bind_self, warm, warm_guard};
    let path = dir.join(name);
    std::fs::write(
        &path,
        bind_self(&path, &format!("#!/bin/sh\n{}\n{body}\n", warm_guard())),
    )
    .unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
    warm(&path);
    path
}

fn success() -> String {
    format!(
        "printf '%s' {}",
        shell_single_quote(TRANSCRIPT_CAPABLE_STDOUT)
    )
}

#[test]
fn cert_store_process_probe_timeouts_do_not_poison_either_capability_memo() {
    for availability in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let checker = script(
            dir.path(),
            "clean",
            &format!(
                "if test ! -f \"$0.release\"; then sleep 5; fi\n{}",
                success()
            ),
        );
        let before = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();
        let probe = |budget| {
            if availability {
                clean_checker_available(&checker, budget)
            } else {
                clean_checker_capability(&checker, budget).map(|_| ())
            }
        };
        let start = Instant::now();
        assert!(matches!(probe(1000), Err(CheckerDefect::TimedOut(_))));
        assert!(start.elapsed() < Duration::from_secs(3));
        // Change the control's readiness, not its executable bytes/metadata.
        std::fs::write(dir.path().join("clean.release"), "ready").unwrap();
        assert_eq!(
            crate::lrat_cert::checker_binary_sha256(&checker).unwrap(),
            before
        );
        assert_eq!(
            probe(0),
            Ok(()),
            "an unlimited retry must not inherit a timeout"
        );
    }
}

#[test]
fn cert_store_process_replay_requires_eof_and_preserves_zero_as_unlimited() {
    let dir = tempfile::tempdir().unwrap();
    for (name, late, accepted) in [
        ("complete", "diagnostic", true),
        ("late-rejection", "Proof status: incomplete", false),
    ] {
        let checker = script(
            dir.path(),
            name,
            &format!(
                "test \"$1\" = cert && test \"$2\" = verify-external && test -f \"$3\" && test \"$4\" = --verbose || exit 3\n{}\n(sleep 0.1; printf '%s\\n' {}) &\nexit 0",
                success(),
                shell_single_quote(late)
            ),
        );
        let identity = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();
        for budget in [0, 5000] {
            assert_eq!(
                carcara_verify_with_expected_checker(
                    &checker,
                    &identity,
                    CHECKER_PROBE_SMT2,
                    CHECKER_PROBE_ALETHE,
                    budget
                )
                .unwrap(),
                accepted
            );
        }
    }
}

#[test]
fn cert_store_process_replay_timeout_is_not_a_complete_success() {
    let dir = tempfile::tempdir().unwrap();
    let checker = script(
        dir.path(),
        "clean",
        &format!(
            "{}\n(sleep 5; printf 'late output\\n') &\nexit 0",
            success()
        ),
    );
    let identity = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();
    let start = Instant::now();
    let error = carcara_verify_with_expected_checker(
        &checker,
        &identity,
        CHECKER_PROBE_SMT2,
        CHECKER_PROBE_ALETHE,
        1000,
    )
    .unwrap_err();
    assert!(matches!(error, RunError::Timeout(_)), "{error}");
    assert!(start.elapsed() < Duration::from_secs(3));
}

#[test]
fn cert_store_process_consume_can_retry_a_timed_out_replay() {
    let dir = tempfile::tempdir().unwrap();
    let solver = dir.path().join("producer");
    std::fs::write(&solver, "producer bytes").unwrap();
    let solver = solver.to_str().unwrap();
    let identity = crate::ay_bridge::solver_identity_hash(solver).unwrap();
    let checker = script(
        dir.path(),
        "clean",
        &format!(
            "if test ! -f \"$0.release\"; then sleep 5; fi\n{}",
            success()
        ),
    );
    let checker_identity = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();
    let cert = AletheCert {
        producer_ay_identity: identity.clone(),
        external_clean_checker_identity: checker_identity.clone(),
        smt2_sha256: sha256_hex(CHECKER_PROBE_SMT2.as_bytes()),
        obligation_name: "replay control".to_string(),
        smt2: CHECKER_PROBE_SMT2.to_string(),
        alethe_proof: CHECKER_PROBE_ALETHE.to_string(),
    };
    let key = crate::ay_bridge::verdict_cache_key_v2(&identity, &cert.smt2);
    let binding = Some((checker, checker_identity));
    // The re-check runs under the checker's own deadline (OD-223), here one
    // second; the solve budget it follows is no longer its deadline.
    trust_cg_process_env::with_env_overrides(&[(PROOF_CHECK_TIMEOUT_ENV, "1000")], || {
        assert!(!consume_verified_text(
            &cert.serialize(),
            &key,
            solver,
            &cert.smt2,
            binding.clone(),
            &SanitizedChildEnv::capture_verifier(),
            1000
        ));
        std::fs::write(dir.path().join("clean.release"), "ready").unwrap();
        assert!(consume_verified_text(
            &cert.serialize(),
            &key,
            solver,
            &cert.smt2,
            binding,
            &SanitizedChildEnv::capture_verifier(),
            0
        ));
    });
}

#[test]
fn cert_store_process_mint_bounds_both_ay_emission_and_clean_replay() {
    // The second case must finish AY startup before reaching the slow checker.
    // Keep that branch armed under parallel host load; low-level capture and
    // replay controls separately exercise the one-second deadline.
    for slow_ay in [true, false] {
        let dir = tempfile::tempdir().unwrap();
        let store = dir.path().join("store");
        let slow = "(sleep 10; printf 'late output\\n') &\nexit 0";
        let ay = script(
            dir.path(),
            "ay",
            &format!(
                "test \"$1\" = solve && test -f \"$2\" && test \"$3\" = --proof && test \"$5\" = --proof-format && test \"$6\" = alethe || exit 4\nprintf '%s' {} > \"$4\"\nprintf 'unsat\\n'\n{}",
                shell_single_quote(CHECKER_PROBE_ALETHE),
                if slow_ay { slow } else { "" }
            ),
        );
        let checker = script(
            dir.path(),
            "clean",
            &format!(
                ": > \"$0.called\"\n{}\n{}",
                success(),
                if slow_ay { "" } else { slow }
            ),
        );
        let checker_identity = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();
        let ay = crate::ay_identity::test_fixtures::pin(&ay);
        let identity = ay.sha256().to_owned();
        let key = crate::ay_bridge::verdict_cache_key_v2(&identity, CHECKER_PROBE_SMT2);
        let start = Instant::now();
        // AY runs under the solve budget and the check under the checker's
        // own deadline (OD-223), both five seconds here.
        let minted =
            trust_cg_process_env::with_env_overrides(&[(PROOF_CHECK_TIMEOUT_ENV, "5000")], || {
                mint_into(&MintRequest {
                    dir: &store,
                    verdict_key: &key,
                    solver: &ay,
                    smt2: CHECKER_PROBE_SMT2,
                    obligation_name: "timeout control",
                    checker: &checker,
                    expected_checker_identity: &checker_identity,
                    timeout_ms: 5000,
                })
            });
        assert!(!minted);
        assert!(start.elapsed() < Duration::from_secs(8));
        assert!(
            !store.exists(),
            "a partial transcript must not publish a cert"
        );
        assert_eq!(
            dir.path().join("clean.called").exists(),
            !slow_ay,
            "incomplete AY output must never reach the independent checker"
        );
    }
}

#[test]
fn cert_store_process_complete_mint_and_replay_accept_the_exact_binding() {
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = script(
        dir.path(),
        "ay",
        &format!(
            "printf '%s' {} > \"$4\"\nprintf 'unsat\\n'",
            shell_single_quote(CHECKER_PROBE_ALETHE)
        ),
    );
    let checker = script(dir.path(), "clean", &success());
    let checker_identity = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();
    let ay = crate::ay_identity::test_fixtures::pin(&ay);
    let identity = ay.sha256().to_owned();
    let key = crate::ay_bridge::verdict_cache_key_v2(&identity, CHECKER_PROBE_SMT2);
    assert!(mint_into(&MintRequest {
        dir: &store,
        verdict_key: &key,
        solver: &ay,
        smt2: CHECKER_PROBE_SMT2,
        obligation_name: "complete control",
        checker: &checker,
        expected_checker_identity: &checker_identity,
        timeout_ms: 0,
    }));
    let bytes = std::fs::read_to_string(cert_path(&store, &key)).unwrap();
    assert!(consume_verified_text(
        &bytes,
        &key,
        &ay.path().to_string_lossy(),
        CHECKER_PROBE_SMT2,
        Some((checker.clone(), checker_identity.clone())),
        &SanitizedChildEnv::capture_verifier(),
        0
    ));
    assert!(!mint_into(&MintRequest {
        dir: &store,
        verdict_key: &key,
        solver: &ay,
        smt2: CHECKER_PROBE_SMT2,
        obligation_name: "later control",
        checker: &checker,
        expected_checker_identity: &checker_identity,
        timeout_ms: 0,
    }));
    assert_eq!(
        std::fs::read_to_string(cert_path(&store, &key)).unwrap(),
        bytes
    );
}

/// A reader in a process of its own: it opens the certificate at `$1`, says
/// so with `$2.ready`, waits (a minute at most) for `$2.go`, then copies what
/// its open file holds to `$2.out`.
const HELD_READER: &str = r#"exec 3< "$1" || exit 3
: > "$2.ready"
waited=0
while test ! -f "$2.go"; do
  waited=$((waited + 1))
  test "$waited" -le 6000 || exit 4
  sleep 0.01
done
cat <&3 > "$2.out""#;

#[test]
fn cert_store_eviction_beside_a_reader_costs_a_miss_only() {
    use super::tests::{EVICTION_OBLIGATION, EVICTION_PROOF, eviction_query, stored_for_eviction};
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let solver = dir.path().join("solver");
    std::fs::write(&solver, b"eviction-fixture-solver").unwrap();
    let solver = solver.to_str().unwrap();
    let identity = crate::ay_bridge::solver_identity_hash(solver).unwrap();
    let checker = script(dir.path(), "clean", &success());
    let checker_identity = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();
    let binding = Some((checker, checker_identity.clone()));
    let keys: Vec<String> = (0..3)
        .map(|index| {
            stored_for_eviction(
                &store,
                &identity,
                &checker_identity,
                &eviction_query(index),
                10 - index as u64,
            )
        })
        .collect();
    let held = cert_path(&store, &keys[0]);
    let original = std::fs::read(&held).unwrap();
    let signal = dir.path().join("reader");
    let mut reader = Command::new("/bin/sh")
        .arg("-c")
        .arg(HELD_READER)
        .arg("reader")
        .arg(&held)
        .arg(&signal)
        .spawn()
        .unwrap();
    let ready = signal.with_extension("ready");
    let start = Instant::now();
    while !ready.exists() {
        if let Some(status) = reader.try_wait().unwrap() {
            panic!("the reader ended before it opened the certificate: {status}");
        }
        assert!(
            start.elapsed() < Duration::from_secs(60),
            "the reader did not open the certificate in a minute"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    // The certificate the other process holds open is the least recently
    // used: a fourth published over a cap of three evicts it.
    let size = original.len() as u64;
    let cap = (3 * size).to_string();
    let publish = |index: usize| {
        persist_verified_alethe_into(
            &store,
            solver,
            &eviction_query(index),
            EVICTION_OBLIGATION,
            EVICTION_PROOF,
            &checker_identity,
        )
    };
    assert!(trust_cg_process_env::with_env_overrides(
        &[(STORE_CAP_ENV, &cap)],
        || publish(3)
    ));
    wait_for_sweep_for_test(&store);
    assert!(!held.exists(), "the held certificate was evicted");
    std::fs::write(signal.with_extension("go"), "").unwrap();
    assert!(reader.wait().unwrap().success());
    // The reader still read every byte it opened, and its hit stands on the
    // same re-check.
    let read = std::fs::read(signal.with_extension("out")).unwrap();
    assert_eq!(read, original);
    assert!(consume_verified_text(
        &String::from_utf8(read).unwrap(),
        &keys[0],
        solver,
        &eviction_query(0),
        binding.clone(),
        &SanitizedChildEnv::capture_verifier(),
        0
    ));
    // A reader after the eviction misses; the miss is solved, published
    // again and credited at its next read.
    assert!(!consume_verified_in(
        &store,
        &keys[0],
        solver,
        &eviction_query(0),
        binding.clone()
    ));
    assert!(publish(0));
    assert!(consume_verified_in(
        &store,
        &keys[0],
        solver,
        &eviction_query(0),
        binding
    ));
}
