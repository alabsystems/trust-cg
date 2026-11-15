// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Unit controls for the source-bound negative memo: what an entry can say,
//! which timeouts are recorded, the key and its build identity, the strict
//! per-box format, the retry policy, locking and concurrent publication. The
//! replay-level controls (AY invocation counts through the real x86-64 body
//! path) are in `x86_source_bound_body_negative_memo_tests.rs`.

use super::*;

const SELF_CHECK: &str = SELF_CHECK_REJECTED;

fn holey() -> String {
    "incomplete AY proof certificate: c ay.proof.certificate path=/q unproved_steps=1".to_owned()
}

fn identity<'a>(smt2: &'a str, query_key: &'a str) -> NegativeMemoIdentity<'a> {
    NegativeMemoIdentity {
        smt2,
        query_key,
        ay_identity: "ay 0.27.0 build 10530 sha256 aa",
        authority_id: [7; 32],
        checker_sha256: "bb",
        timeout_ms: 30_000,
        checker_timeout_ms: 180_000,
        produce_models: true,
        resident_route: true,
        fresh_after_resident_timeout: false,
        generalized: false,
        replay_protocol: "protocol",
        verifier_build: "build",
    }
}

fn unique_key(tag: &str) -> NegativeMemoKey {
    identity(tag, "query-key").key()
}

fn entry(outcome: UncertifiedOutcome, reason: &str) -> Entry {
    Entry {
        outcome,
        reason: reason.to_owned(),
        recorded_unix_ms: 1_000_000,
        solve_ms: 22_005,
        cpu_ms: if outcome.is_deadline() { 21_950 } else { 0 },
        reuses: 0,
        confirmations: 1,
    }
}

fn expiry(limit_ms: u64, cpu_ms: Option<u64>) -> DeadlineExpiry {
    DeadlineExpiry {
        limit: Duration::from_millis(limit_ms),
        cpu: cpu_ms.map(Duration::from_millis),
    }
}

/// A 30 s deadline whose solver used 29.1 s of CPU: the query ran out.
fn exhausting() -> DeadlineExpiry {
    expiry(30_000, Some(29_100))
}

/// A 30 s deadline whose solver got 9 s of CPU on a loaded host: the host
/// ran out, not the query.
fn starved() -> DeadlineExpiry {
    expiry(30_000, Some(9_000))
}

/// A fresh solve of the replay that had the processor: 990 ms of CPU time
/// in 1 s.
fn held(scope: &NegativeMemoScope) {
    scope.note_solve_completion(Duration::from_secs(1), Some(Duration::from_millis(990)));
}

/// A replay that timed out after the given deadline expiries.
fn time_out(scope: &NegativeMemoScope, expiries: &[Option<DeadlineExpiry>], now: u64) {
    for expiry in expiries {
        scope.note_deadline_expiry(*expiry);
    }
    scope.observe_at(
        &AYResult::Timeout,
        &AyVerdictSource::LiveSolve,
        Duration::from_secs(30),
        now,
    );
}

fn reason_of(outcome: UncertifiedOutcome) -> String {
    match outcome {
        UncertifiedOutcome::SelfCheckRejected => SELF_CHECK.to_owned(),
        UncertifiedOutcome::IncompleteCertificate => holey(),
        UncertifiedOutcome::CheckerRejected => {
            crate::ay_bridge::working_checker_rejection_reason(Path::new("/c"))
        }
        UncertifiedOutcome::Timeout => String::new(),
        UncertifiedOutcome::CheckerTimeout => checker_timeout_reason(),
    }
}

/// The reason the fresh replay gives an AY `unsat` whose Clean check ran
/// out of the checker's own deadline (OD-223).
fn checker_timeout_reason() -> String {
    crate::ay_bridge::clean_check_timeout_reason(
        11_534_336,
        180_000,
        &expiry(180_000, Some(179_500)),
    )
}

/// A replay whose AY answered `unsat` and whose Clean check timed out after
/// the given checker deadline expiries (and the given solver ones).
fn check_times_out(
    scope: &NegativeMemoScope,
    solver: &[Option<DeadlineExpiry>],
    checker: &[Option<DeadlineExpiry>],
    now: u64,
) {
    for expiry in solver {
        scope.note_deadline_expiry(*expiry);
    }
    for expiry in checker {
        scope.note_check_expiry(*expiry);
    }
    scope.observe_at(
        &AYResult::Unknown(checker_timeout_reason()),
        &AyVerdictSource::LiveSolve,
        Duration::from_secs(190),
        now,
    );
}

const HOUR_MS: u64 = 60 * 60 * 1000;

/// A new process: only the per-box entries remain.
fn new_process() {
    forget_process_tier_for_test();
}

/// A hit is a `WithheldCredit`, and every one of them becomes `Unknown` or
/// `Timeout`: there is no variant a hit could turn into `Verified`,
/// `SolverUnsat` or a counterexample, and the proof gate classifies each as
/// a failure.
#[test]
fn a_hit_can_only_withhold_credit() {
    for outcome in UncertifiedOutcome::ALL {
        let reason = reason_of(outcome);
        let withheld = WithheldCredit {
            outcome,
            reason: reason.clone(),
            tier: MemoTier::Store,
            reuses: 1,
            reuse_budget: 2,
            process_hits: 1,
            age: Duration::from_secs(1),
            solve_ms: 1,
            cpu_ms: 0,
            confirmations: 1,
        };
        let result = withheld.non_credit_result();
        match (&result, outcome) {
            (AYResult::Timeout, UncertifiedOutcome::Timeout) => {}
            (AYResult::Unknown(text), _) if *text == reason => {}
            other => panic!("{outcome:?} replayed as {other:?}"),
        }
        assert!(
            crate::proof_gate::failure_class_of(&result).is_some(),
            "{result:?} must be a proof-gate failure"
        );
        assert_eq!(withheld.outcome(), outcome);
    }
}

/// Only the measured-stable outcomes are recorded: AY's strict self-check
/// rejection, a disclosed incomplete certificate, the working checker's
/// rejection, and a timeout. Every other `(:reason-unknown …)` (host state:
/// memory, resources, interrupts, internal errors, split limits), a bare
/// `unknown`, AY's model gate, credit, refutations, uncertified UNSAT,
/// errors and installation or I/O reasons are not.
#[test]
fn only_measured_stable_outcomes_are_classified() {
    let gate = format!(
        "{}: AY fail-closed on this exact query; its published reason was {SELF_CHECK}",
        crate::gap_classify::AY_SOUNDNESS_GATE_REASON
    );
    let mut cases = vec![
        (
            AYResult::Unknown(SELF_CHECK.into()),
            Some(UncertifiedOutcome::SelfCheckRejected),
        ),
        (
            AYResult::Unknown(holey()),
            Some(UncertifiedOutcome::IncompleteCertificate),
        ),
        (
            AYResult::Unknown(reason_of(UncertifiedOutcome::CheckerRejected)),
            Some(UncertifiedOutcome::CheckerRejected),
        ),
        (AYResult::Timeout, Some(UncertifiedOutcome::Timeout)),
        (
            AYResult::Unknown(checker_timeout_reason()),
            Some(UncertifiedOutcome::CheckerTimeout),
        ),
        (
            AYResult::Unknown(crate::ay_bridge::CLEAN_PROBE_TIMEOUT_REASON.into()),
            None,
        ),
        (
            AYResult::Unknown(format!(" {}", checker_timeout_reason())),
            None,
        ),
        (AYResult::Unknown(gate), None),
        (AYResult::Unknown("unknown".into()), None),
        (AYResult::Unknown(format!(" {SELF_CHECK}")), None),
        (AYResult::Verified, None),
        (AYResult::SolverUnsat, None),
        (AYResult::CounterExample(vec![("x".into(), 1)]), None),
        (AYResult::Error("spawn failed".into()), None),
        (
            AYResult::Unknown(
                "AY reported UNSAT but it CANNOT BE CHECKED here — no usable checker".into(),
            ),
            None,
        ),
        (
            AYResult::Unknown("AY reported UNSAT but Clean replay could not complete: io".into()),
            None,
        ),
        (
            AYResult::Unknown("captured AY executable identity changed".into()),
            None,
        ),
        (
            AYResult::Unknown("unusable AY proof evidence: could not publish".into()),
            None,
        ),
    ];
    for host_state in [
        "(:reason-unknown memout)",
        "(:reason-unknown resourceout)",
        "(:reason-unknown interrupted)",
        "(:reason-unknown internal_error)",
        "(:reason-unknown (incomplete split_limit))",
        "(:reason-unknown incomplete)",
    ] {
        cases.push((AYResult::Unknown(host_state.into()), None));
    }
    for (result, expected) in cases {
        let classified = UncertifiedOutcome::classify(&result);
        assert_eq!(
            classified.as_ref().map(|(kind, _)| *kind),
            expected,
            "{result:?}"
        );
        if let (Some((_, reason)), AYResult::Unknown(text)) = (&classified, &result) {
            assert_eq!(reason, text, "the exact reason is kept");
        }
    }
}

/// Each key input alone changes the key (the query bytes, the v2 query key,
/// AY's recorded identity, the reuse authority, the checker, the solve
/// budget, the checker's own deadline (OD-223), the model option, the
/// resident route, the fresh retry, slice 23's generalization route, the
/// replay protocol and the verifier build); the same inputs give the same
/// key.
#[test]
fn every_key_component_changes_the_key() {
    let base = identity("(assert q)", "k");
    let mut keys = vec![base.key()];
    assert_eq!(identity("(assert q)", "k").key(), base.key());
    type Mutation = fn(&mut NegativeMemoIdentity<'static>);
    let variants: [Mutation; 13] = [
        |id| id.smt2 = "(assert q) ",
        |id| id.query_key = "k2",
        |id| id.ay_identity = "ay 0.27.0 build 10531 sha256 aa",
        |id| id.authority_id[31] ^= 1,
        |id| id.checker_sha256 = "bc",
        |id| id.timeout_ms = 30_001,
        |id| id.checker_timeout_ms = 180_001,
        |id| id.produce_models = false,
        |id| id.resident_route = false,
        |id| id.fresh_after_resident_timeout = true,
        |id| id.generalized = true,
        |id| id.replay_protocol = "protocol'",
        |id| id.verifier_build = "build'",
    ];
    for mutate in &variants {
        let mut changed = identity("(assert q)", "k");
        mutate(&mut changed);
        keys.push(changed.key());
    }
    let distinct: std::collections::HashSet<_> = keys.iter().collect();
    assert_eq!(
        distinct.len(),
        keys.len(),
        "every component must reach the key"
    );
}

/// The embedded build identity is the digest of this build's replay and
/// verdict sources (this crate's `src/`, manifest and build script, and
/// `trust-cg-process-env`'s), so an entry never crosses builds whose code
/// differs: editing any of those files changes it.
#[test]
fn the_verifier_build_identity_is_the_digest_of_these_sources() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let derived = crate::verifier_source_digest::digest(manifest).unwrap();
    assert_eq!(VERIFIER_BUILD, derived);
    assert_eq!(VERIFIER_BUILD.len(), 64);
    // The digest covers the replay and verdict code and the child
    // environment's: changing one byte of a copy of the tree changes it.
    let copy = tempfile::tempdir().unwrap();
    let crate_dir = copy.path().join("trust-cg-verify");
    for input in crate::verifier_source_digest::INPUTS {
        let from = manifest.join(input);
        let to = crate_dir.join(input);
        copy_tree(&from, &to);
    }
    assert_eq!(
        crate::verifier_source_digest::digest(&crate_dir).unwrap(),
        derived
    );
    for edited in [
        "src/ay_bridge.rs",
        "src/obligation_cert_store.rs",
        "../trust-cg-process-env/src/lib.rs",
    ] {
        let path = crate_dir.join(edited);
        let original = std::fs::read(&path).unwrap();
        let mut changed = original.clone();
        changed.push(b'\n');
        std::fs::write(&path, &changed).unwrap();
        assert_ne!(
            crate::verifier_source_digest::digest(&crate_dir).unwrap(),
            derived,
            "{edited}"
        );
        std::fs::write(&path, &original).unwrap();
    }
}

fn copy_tree(from: &Path, to: &Path) {
    let metadata = std::fs::symlink_metadata(from).unwrap();
    if metadata.is_dir() {
        std::fs::create_dir_all(to).unwrap();
        for entry in std::fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            copy_tree(&entry.path(), &to.join(entry.file_name()));
        }
    } else if metadata.is_file() {
        std::fs::create_dir_all(to.parent().unwrap()).unwrap();
        std::fs::copy(from, to).unwrap();
    }
}

/// The replay protocol in every key is rendered from the command builders the
/// replay itself uses: the resident solver, the fresh proof-bearing solve,
/// the SAT model query and the independent checker, argument for argument.
/// A builder that grows or loses an argument outside the shared argument
/// helpers fails here; one that changes them changes every key.
#[test]
fn the_replay_protocol_renders_the_real_commands() {
    let solver = crate::ay_identity::test_fixtures::inert();
    let protocol = replay_protocol();
    assert_eq!(protocol, crate::ay_bridge::replay_protocol_description());
    let commands = crate::ay_bridge::replay_commands_for_test(&solver);
    assert_eq!(commands.len(), 4);
    for (label, args) in commands {
        assert!(!args.is_empty(), "{label}");
        let rendered = format!("{label}=[{args}]");
        assert!(
            protocol.contains(&rendered),
            "the protocol does not render the real {label} command `{args}`: {protocol}"
        );
    }
    assert!(protocol.contains(
        "fresh=[-smt2 Q.smt2 --strict-proofs --proof Q.smt2.alethe --proof-format alethe]"
    ));
    assert!(protocol.contains("resident=[--incremental]"));
    assert!(protocol.contains("checker=[cert verify-external C.json --verbose]"));
}

/// The per-box format is exact: a round trip holds, and every truncation, a
/// foreign schema, another key's entry, a malformed field and trailing bytes
/// all parse as a miss.
#[test]
fn the_store_format_is_strict() {
    let key = unique_key("format");
    let other = unique_key("format-other");
    for outcome in UncertifiedOutcome::ALL {
        let original = entry(outcome, &reason_of(outcome));
        let text = original.serialize(&key);
        assert_eq!(Entry::parse(&text, &key), Some(original.clone()));
        assert_eq!(Entry::parse(&text, &other), None, "another key's entry");
        for cut in 0..text.len() {
            if text.is_char_boundary(cut) {
                assert_eq!(Entry::parse(&text[..cut], &key), None, "truncated at {cut}");
            }
        }
        assert_eq!(Entry::parse(&format!("{text}x"), &key), None);
        for retired in [
            "tcg-source-bound-negative-memo-v1",
            "tcg-source-bound-negative-memo-v2",
            "tcg-source-bound-negative-memo-v3",
            // Slice 19 (OD-197): a v4 timeout may be a resident deadline alone.
            "tcg-source-bound-negative-memo-v4",
            // OD-223: a v5 timeout may be a Clean check that overran the
            // solve budget it then shared.
            "tcg-source-bound-negative-memo-v5",
        ] {
            let foreign = text.replacen(SCHEMA, retired, 1);
            assert_eq!(Entry::parse(&foreign, &key), None, "foreign schema");
        }
    }
    let text = entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK).serialize(&key);
    for (from, to) in [
        ("outcome:self-check-rejected", "outcome:verified"),
        ("reuses:0", "reuses:-1"),
        ("reuses:0", "reuses:"),
        ("reuses:0", "reuses:99999999999"),
        ("confirmations:1", "confirmations:0"),
        ("solve-ms:22005", "solve-ms:2x"),
        // Only a timeout carries the CPU time that justified it.
        ("cpu-ms:0", "cpu-ms:9"),
        ("cpu-ms:0", "cpu-ms:"),
    ] {
        assert!(text.contains(from), "{from}");
        assert_eq!(
            Entry::parse(&text.replacen(from, to, 1), &key),
            None,
            "{to}"
        );
    }
    let length = format!("reason-bytes:{}", SELF_CHECK.len());
    for wrong in [SELF_CHECK.len() - 1, SELF_CHECK.len() + 1] {
        let text = text.replacen(&length, &format!("reason-bytes:{wrong}"), 1);
        assert_eq!(Entry::parse(&text, &key), None, "reason length {wrong}");
    }
    // A timeout without the CPU time that justified recording it would not
    // have been recorded.
    let timeout = entry(UncertifiedOutcome::Timeout, "").serialize(&key);
    assert!(timeout.contains("cpu-ms:21950\n"), "{timeout}");
    assert_eq!(
        Entry::parse(&timeout.replacen("cpu-ms:21950", "cpu-ms:0", 1), &key),
        None
    );
    // OD-223: nor a checker timeout without the checker's CPU time.
    let checker = entry(
        UncertifiedOutcome::CheckerTimeout,
        &checker_timeout_reason(),
    )
    .serialize(&key);
    assert!(checker.contains("outcome:checker-timeout\n"), "{checker}");
    assert_eq!(
        Entry::parse(&checker.replacen("cpu-ms:21950", "cpu-ms:0", 1), &key),
        None
    );
}

/// A stored reason must be one its outcome label is recorded for: a crafted
/// entry pairing a label with other text (another class's reason, a host
/// state `unknown`, arbitrary text, a timeout carrying text) is a miss.
#[test]
fn a_reason_that_does_not_classify_as_its_label_is_a_miss() {
    let key = unique_key("crafted");
    let crafted = |outcome: UncertifiedOutcome, reason: &str| {
        Entry {
            outcome,
            reason: reason.to_owned(),
            ..entry(outcome, "")
        }
        .serialize(&key)
    };
    for outcome in UncertifiedOutcome::ALL {
        assert!(Entry::parse(&crafted(outcome, &reason_of(outcome)), &key).is_some());
    }
    for (outcome, reason) in [
        (UncertifiedOutcome::SelfCheckRejected, holey()),
        (
            UncertifiedOutcome::SelfCheckRejected,
            "(:reason-unknown memout)".to_owned(),
        ),
        (
            UncertifiedOutcome::IncompleteCertificate,
            SELF_CHECK.to_owned(),
        ),
        (
            UncertifiedOutcome::CheckerRejected,
            "anything at all".to_owned(),
        ),
        (UncertifiedOutcome::Timeout, "x".to_owned()),
        (UncertifiedOutcome::Timeout, checker_timeout_reason()),
        (UncertifiedOutcome::CheckerTimeout, String::new()),
        (
            UncertifiedOutcome::CheckerTimeout,
            reason_of(UncertifiedOutcome::CheckerRejected),
        ),
        (
            UncertifiedOutcome::CheckerRejected,
            checker_timeout_reason(),
        ),
        (UncertifiedOutcome::SelfCheckRejected, String::new()),
    ] {
        assert_eq!(
            Entry::parse(&crafted(outcome, &reason), &key),
            None,
            "{outcome:?} with {reason:?}"
        );
    }
}

/// Files that are not a valid entry for the key are misses: absent,
/// truncated, corrupt, oversized, foreign schema, another key, not UTF-8, a
/// directory, a symbolic link to a valid entry.
#[test]
fn corrupt_or_foreign_store_entries_are_misses() {
    let dir = tempfile::tempdir().unwrap();
    let key = unique_key("corrupt");
    let path = entry_path(dir.path(), &key);
    assert_eq!(read_entry(dir.path(), &key), None, "absent");
    let valid = entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK).serialize(&key);
    let other = entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK)
        .serialize(&unique_key("corrupt-other"));
    let oversized = format!(
        "{SCHEMA}\nkey:{}\noutcome:self-check-rejected\nrecorded-unix-ms:1\nsolve-ms:1\ncpu-ms:0\nreuses:0\nconfirmations:1\nreason-bytes:{n}\n{}\nend\n",
        key.hex(),
        "r".repeat(70_000),
        n = 70_000
    );
    for bad in [
        valid[..valid.len() / 2].to_owned(),
        "\u{0}\u{1}garbage".to_owned(),
        valid.replacen(SCHEMA, "tcg-source-bound-negative-memo-v0", 1),
        other,
        oversized,
    ] {
        std::fs::write(&path, bad).unwrap();
        assert_eq!(read_entry(dir.path(), &key), None);
    }
    std::fs::write(&path, [0xff, 0xfe, 0x00]).unwrap();
    assert_eq!(read_entry(dir.path(), &key), None, "not UTF-8");
    std::fs::remove_file(&path).unwrap();
    std::fs::create_dir(&path).unwrap();
    assert_eq!(read_entry(dir.path(), &key), None, "a directory");
    std::fs::remove_dir(&path).unwrap();
    #[cfg(unix)]
    {
        let target = dir.path().join("target.txt");
        std::fs::write(&target, &valid).unwrap();
        std::os::unix::fs::symlink(&target, &path).unwrap();
        assert_eq!(read_entry(dir.path(), &key), None, "a symbolic link");
        std::fs::remove_file(&path).unwrap();
    }
    std::fs::write(&path, &valid).unwrap();
    assert_eq!(
        read_entry(dir.path(), &key),
        Some(entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK))
    );
}

/// A FIFO (or other non-regular file) at an entry or lock path is a miss
/// and never blocks: the type is checked before opening, and the open does
/// not follow links or block. Before, the entry was opened first and a
/// reader-less FIFO hung the compile.
#[cfg(unix)]
#[test]
fn a_fifo_at_an_entry_or_lock_path_is_a_miss_and_never_blocks() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let key = unique_key(&format!("fifo {}", dir.path().display()));
    let fifo = |path: &Path| {
        assert!(
            std::process::Command::new("mkfifo")
                .arg(path)
                .status()
                .unwrap()
                .success()
        );
    };
    let bounded = |what: &str, f: Box<dyn FnOnce() -> bool + Send>| {
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let _ = sender.send(f());
        });
        let answered = receiver.recv_timeout(Duration::from_secs(5));
        assert!(answered.is_ok(), "{what} blocked on a FIFO");
        answered.unwrap()
    };
    fifo(&entry_path(dir.path(), &key));
    let store = dir.path().to_path_buf();
    let scope = NegativeMemoScope::new(key, Some(store.clone()), RetryPolicy::DEFAULT);
    new_process();
    assert!(!bounded(
        "a lookup",
        Box::new(move || scope.lookup_at(now_unix_ms()).is_some())
    ));
    let (dir2, key2) = (store.clone(), key);
    assert!(!bounded(
        "a read",
        Box::new(move || read_entry(&dir2, &key2).is_some())
    ));
    // A FIFO at the lock path: the per-box tier is skipped, nothing blocks.
    let locked = tempfile::tempdir().unwrap();
    fifo(&locked.path().join(".lock"));
    let lock_dir = locked.path().to_path_buf();
    assert!(!bounded(
        "the lock",
        Box::new(move || StoreLock::acquire(&lock_dir).is_some())
    ));
}

/// The retry policy. Inside one process an entry answers up to its hit
/// budget within its window, then the next occurrence solves again. Each
/// later process that reads the per-box entry is one reuse; after the reuse
/// budget the next process solves again, a failed re-solve refreshes the
/// entry (reuses reset, one more confirmation, a doubled budget up to the
/// cap), and a `Verified` deletes it. Every tier refuses an entry past its
/// age or recorded in the future.
#[test]
fn the_retry_policy_bounds_every_tier_and_a_resolve_refreshes() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let policy = RetryPolicy {
        base_reuses: 2,
        max_reuses: 4,
        max_age: Duration::from_secs(3600),
        process_hits: 3,
        process_window: Duration::from_secs(60),
    };
    let scope = NegativeMemoScope::new(
        unique_key(&format!("policy {}", dir.path().display())),
        Some(dir.path().to_path_buf()),
        policy,
    );
    let t0 = 10 * HOUR_MS;
    let failed = AYResult::Unknown(SELF_CHECK.into());
    let fail_at = |now: u64| {
        held(&scope);
        scope.observe_at(
            &failed,
            &AyVerdictSource::LiveSolve,
            Duration::from_millis(9),
            now,
        )
    };
    let stored = || read_entry(dir.path(), &scope.key()).unwrap();
    assert!(scope.lookup_at(t0).is_none(), "nothing recorded yet");
    fail_at(t0);
    // The recording process: its hit budget, then a re-solve.
    for now in t0 + 1..t0 + 4 {
        let hit = scope.lookup_at(now).expect("within the process budget");
        assert_eq!(hit.tier(), MemoTier::Process);
        assert_eq!(hit.non_credit_result(), failed);
    }
    assert!(
        scope.lookup_at(t0 + 5).is_none(),
        "process hit budget spent"
    );
    assert_eq!((stored().reuses, stored().confirmations), (0, 1));
    // The process window: a fresh process slot answers only within it.
    new_process();
    assert!(
        scope.lookup_at(t0 + 100).is_some(),
        "store read enters the process"
    );
    assert!(
        scope.lookup_at(t0 + 100 + 60_000).is_some(),
        "at the window's end"
    );
    assert!(
        scope.lookup_at(t0 + 100 + 60_001).is_none(),
        "past the process window"
    );
    assert_eq!(stored().reuses, 1);
    // One more later process reuses it; the third solves again.
    new_process();
    assert_eq!(scope.lookup_at(t0 + 200).unwrap().tier(), MemoTier::Store);
    assert_eq!(stored().reuses, 2);
    new_process();
    assert!(
        scope.lookup_at(t0 + 300).is_none(),
        "reuse budget spent: solve again"
    );

    // The re-solve failed again: refreshed, with a doubled budget.
    fail_at(t0 + 301);
    assert_eq!(
        (
            stored().reuses,
            stored().confirmations,
            stored().recorded_unix_ms
        ),
        (0, 2, t0 + 301)
    );
    for now in [t0 + 400, t0 + 500, t0 + 600, t0 + 700] {
        new_process();
        assert!(
            scope.lookup_at(now).is_some(),
            "a confirmed entry answers 4 processes"
        );
    }
    new_process();
    assert!(scope.lookup_at(t0 + 800).is_none());
    fail_at(t0 + 801);
    assert_eq!(stored().confirmations, 3);
    for now in [t0 + 900, t0 + 1000, t0 + 1100, t0 + 1200] {
        new_process();
        assert!(
            scope.lookup_at(now).is_some(),
            "the budget stops at the cap"
        );
    }
    new_process();
    assert!(scope.lookup_at(t0 + 1300).is_none());

    // Age, in both tiers: honoured at exactly max_age, not after, and never
    // when recorded after `now`.
    let wide = RetryPolicy {
        process_window: Duration::from_secs(24 * 3600),
        ..policy
    };
    let aged = NegativeMemoScope::new(scope.key(), Some(dir.path().to_path_buf()), wide);
    let t1 = t0 + 2000;
    held(&aged);
    aged.observe_at(&failed, &AyVerdictSource::LiveSolve, Duration::ZERO, t1);
    assert!(
        aged.lookup_at(t1 + HOUR_MS).is_some(),
        "process tier at max_age"
    );
    assert!(
        aged.lookup_at(t1 + HOUR_MS + 1).is_none(),
        "process tier too old"
    );
    new_process();
    assert!(
        aged.lookup_at(t1 + HOUR_MS + 1).is_none(),
        "store tier too old"
    );
    assert!(aged.lookup_at(t1 - 1).is_none(), "recorded after `now`");
    assert!(
        aged.lookup_at(t1 + HOUR_MS).is_some(),
        "store tier at max_age"
    );

    // A memo replay, an error or an unclassified outcome records nothing;
    // `Verified` deletes the entry in both tiers.
    let untouched = read_entry(dir.path(), &scope.key());
    assert!(untouched.is_some());
    for (result, source) in [
        (failed.clone(), AyVerdictSource::NegativeMemo),
        (AYResult::Error("io".into()), AyVerdictSource::LiveSolve),
        (
            AYResult::Unknown("(:reason-unknown memout)".into()),
            AyVerdictSource::LiveSolve,
        ),
        (
            AYResult::Unknown("AY reported UNSAT but Clean replay could not complete".into()),
            AyVerdictSource::LiveSolve,
        ),
    ] {
        aged.observe_at(&result, &source, Duration::ZERO, t1 + 1);
    }
    assert_eq!(read_entry(dir.path(), &scope.key()), untouched);
    aged.observe_at(
        &AYResult::Verified,
        &AyVerdictSource::AletheCertStore,
        Duration::ZERO,
        t1 + 2,
    );
    assert_eq!(read_entry(dir.path(), &scope.key()), None);
    assert!(aged.lookup_at(t1 + 3).is_none());
}

/// The default budgets: per box, 2 later processes doubling per
/// confirmation to 32; in one process, 64 hits within an hour; 24 hours in
/// every tier. An extreme count saturates instead of overflowing.
#[test]
fn the_default_budgets_are_the_measured_ones() {
    let policy = RetryPolicy::DEFAULT;
    let budgets: Vec<u32> = (0..8).map(|count| policy.reuse_budget(count)).collect();
    assert_eq!(budgets, [2, 2, 4, 8, 16, 32, 32, 32]);
    assert_eq!(policy.reuse_budget(u32::MAX), policy.max_reuses);
    assert_eq!(policy.max_age, Duration::from_secs(24 * 60 * 60));
    assert_eq!(policy.process_hits, 64);
    assert_eq!(policy.process_window, Duration::from_secs(60 * 60));
}

/// An outcome that follows a SAT verdict (the model query timing out) is
/// never recorded, and deletes the key's entry in both tiers.
#[test]
fn an_outcome_after_a_sat_verdict_is_never_recorded() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let key = unique_key(&format!("sat {}", dir.path().display()));
    let now = now_unix_ms();
    let earlier = NegativeMemoScope::new(key, Some(dir.path().to_path_buf()), RetryPolicy::DEFAULT);
    time_out(&earlier, &[Some(exhausting())], now);
    assert!(read_entry(dir.path(), &key).is_some());
    let sat = NegativeMemoScope::new(key, Some(dir.path().to_path_buf()), RetryPolicy::DEFAULT);
    sat.note_sat_verdict();
    sat.note_deadline_expiry(Some(exhausting()));
    sat.observe_at(
        &AYResult::Timeout,
        &AyVerdictSource::LiveSolve,
        Duration::ZERO,
        now + 1,
    );
    assert_eq!(read_entry(dir.path(), &key), None, "the entry is deleted");
    assert!(
        sat.lookup_at(now + 2).is_none(),
        "and gone from the process"
    );
    new_process();
    assert!(sat.lookup_at(now + 3).is_none());
}

/// The measured defect (2026-09-30): under host load 40-80 the solves of
/// bodies that certify at rest hit their wall-clock budget, and each such
/// `Timeout` was recorded, so later processes got the withheld credit without
/// solving until the retry budget expired, and proof-required builds and the
/// proof tests failed on every busy machine. A timeout whose solver got well
/// under its budget in CPU time is the host's, not the query's: it is not
/// recorded, in either tier, and it leaves an existing entry for the key
/// exactly as it is (not refreshed, not confirmed, not deleted).
#[test]
fn a_cpu_starved_timeout_is_not_recorded_and_leaves_the_entry_alone() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let key = unique_key(&format!("starved {}", dir.path().display()));
    let store = Some(dir.path().to_path_buf());
    let now = now_unix_ms();
    let fresh_scope = || NegativeMemoScope::new(key, store.clone(), RetryPolicy::DEFAULT);
    new_process();
    let starved_replay = fresh_scope();
    time_out(&starved_replay, &[Some(starved())], now);
    assert_eq!(read_entry(dir.path(), &key), None, "nothing per box");
    assert!(
        starved_replay.lookup_at(now + 1).is_none(),
        "nothing in process"
    );

    for (earlier, expiries) in [
        (AYResult::Timeout, vec![Some(exhausting())]),
        (AYResult::Unknown(SELF_CHECK.into()), Vec::new()),
    ] {
        let recording = fresh_scope();
        held(&recording);
        for expiry in &expiries {
            recording.note_deadline_expiry(*expiry);
        }
        recording.observe_at(
            &earlier,
            &AyVerdictSource::LiveSolve,
            Duration::from_secs(30),
            now,
        );
        let before = read_entry(dir.path(), &key).expect("recorded");
        // In the recording process, and in a later one that read the entry.
        time_out(&fresh_scope(), &[Some(starved())], now + 10);
        assert_eq!(read_entry(dir.path(), &key), Some(before.clone()));
        assert_eq!(
            fresh_scope()
                .lookup_at(now + 11)
                .map(|hit| hit.non_credit_result()),
            Some(earlier.clone()),
            "the process tier still holds it"
        );
        new_process();
        let reader = fresh_scope();
        assert!(reader.lookup_at(now + 12).is_some(), "read per box");
        let reused = read_entry(dir.path(), &key).unwrap();
        assert_eq!(reused.reuses, before.reuses + 1);
        time_out(&fresh_scope(), &[Some(starved())], now + 13);
        assert_eq!(read_entry(dir.path(), &key), Some(reused));
        // Clear the key for the next round.
        fresh_scope().observe_at(
            &AYResult::Verified,
            &AyVerdictSource::LiveSolve,
            Duration::ZERO,
            now + 14,
        );
        assert_eq!(read_entry(dir.path(), &key), None);
        new_process();
    }
}

/// A timeout whose solver used its budget in CPU time is the query's: it is
/// recorded, with that CPU time, and replayed. The share is inclusive at
/// exactly [`BUDGET_EXHAUSTING_CPU_PERCENT`] percent.
#[test]
fn a_budget_exhausting_timeout_is_recorded_with_its_cpu_time() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let store = Some(dir.path().to_path_buf());
    let now = now_unix_ms();
    new_process();
    for (tag, expiries, cpu_ms) in [
        ("one", vec![Some(exhausting())], 29_100),
        (
            "two: the larger CPU time is kept",
            vec![Some(expiry(30_000, Some(28_000))), Some(exhausting())],
            29_100,
        ),
        (
            "exactly the share",
            vec![Some(expiry(30_000, Some(27_000)))],
            27_000,
        ),
        (
            "rounded up to a millisecond",
            vec![Some(DeadlineExpiry {
                limit: Duration::from_millis(500),
                cpu: Some(Duration::from_micros(450_001)),
            })],
            451,
        ),
    ] {
        let key = unique_key(&format!("exhausting {tag} {}", dir.path().display()));
        let scope = NegativeMemoScope::new(key, store.clone(), RetryPolicy::DEFAULT);
        time_out(&scope, &expiries, now);
        let stored = read_entry(dir.path(), &key).unwrap_or_else(|| panic!("{tag}: recorded"));
        assert_eq!(
            (stored.outcome, stored.cpu_ms),
            (UncertifiedOutcome::Timeout, cpu_ms),
            "{tag}"
        );
        let hit = scope.lookup_at(now + 1).expect("replayed");
        assert_eq!(hit.non_credit_result(), AYResult::Timeout);
        assert!(
            hit.describe()
                .contains(&format!("recorded_cpu_ms={cpu_ms}")),
            "{}",
            hit.describe()
        );
    }
}

/// A `Timeout` is recorded only when the replay saw a deadline expire AND
/// every expiry it saw used its budget. Not recorded: no supervised expiry at
/// all (AY printing `timeout`, the checker's capability probe), an expiry
/// that was not measured (a platform without per-process accounting, a
/// resident deadline spent before the exchange), a starved one, and a replay
/// with one exhausting and one starved or unmeasured expiry. Other outcomes do
/// not depend on expiries.
#[test]
fn a_timeout_without_evidence_that_the_query_used_its_budget_is_not_recorded() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let store = Some(dir.path().to_path_buf());
    let now = now_unix_ms();
    new_process();
    for (tag, expiries) in [
        ("no expiry", vec![]),
        ("unsupervised", vec![None]),
        ("unmeasured", vec![Some(expiry(30_000, None))]),
        ("starved", vec![Some(starved())]),
        (
            "just under the share",
            vec![Some(DeadlineExpiry {
                limit: Duration::from_millis(30_000),
                cpu: Some(Duration::from_millis(27_000) - Duration::from_nanos(1)),
            })],
        ),
        (
            "exhausting then starved",
            vec![Some(exhausting()), Some(starved())],
        ),
        (
            "starved then exhausting",
            vec![Some(starved()), Some(exhausting())],
        ),
        (
            "exhausting then unsupervised",
            vec![Some(exhausting()), None],
        ),
    ] {
        let key = unique_key(&format!("unproven {tag} {}", dir.path().display()));
        let scope = NegativeMemoScope::new(key, store.clone(), RetryPolicy::DEFAULT);
        time_out(&scope, &expiries, now);
        assert_eq!(read_entry(dir.path(), &key), None, "{tag}");
        assert!(scope.lookup_at(now + 1).is_none(), "{tag}");
    }
    let key = unique_key(&format!(
        "self-check after a starved expiry {}",
        dir.path().display()
    ));
    let scope = NegativeMemoScope::new(key, store, RetryPolicy::DEFAULT);
    scope.note_deadline_expiry(Some(starved()));
    held(&scope);
    scope.observe_at(
        &AYResult::Unknown(SELF_CHECK.into()),
        &AyVerdictSource::LiveSolve,
        Duration::ZERO,
        now,
    );
    assert_eq!(
        read_entry(dir.path(), &key).map(|entry| (entry.outcome, entry.cpu_ms)),
        Some((UncertifiedOutcome::SelfCheckRejected, 0))
    );
}

/// OD-223: the proof check is not the solve. A Clean check that ran out of
/// the checker's own deadline having used it is recorded as a
/// `checker-timeout` (never a solver `timeout`), with the checker's CPU time;
/// a starved or unmeasured checker expiry records nothing. The two kinds of
/// expiry are judged apart: a solver expiry neither justifies nor withholds a
/// checker timeout, and a checker expiry neither justifies nor withholds a
/// solver timeout.
#[test]
fn checker_and_solver_deadlines_are_judged_apart() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let store = Some(dir.path().to_path_buf());
    let now = now_unix_ms();
    new_process();
    let check_used = || Some(expiry(180_000, Some(179_500)));
    let check_starved = || Some(expiry(180_000, Some(60_000)));
    let scope_for = |tag: &str| {
        let key = unique_key(&format!("apart {tag} {}", dir.path().display()));
        (
            key,
            NegativeMemoScope::new(key, store.clone(), RetryPolicy::DEFAULT),
        )
    };
    // A used checker deadline after a starved resident solve: recorded as a
    // checker timeout with the checker's CPU time, replayed as the exact
    // checker-timeout reason, never as `AYResult::Timeout`.
    let (key, scope) = scope_for("used");
    check_times_out(&scope, &[Some(starved())], &[check_used()], now);
    let stored = read_entry(dir.path(), &key).expect("a used checker deadline is recorded");
    assert_eq!(
        (stored.outcome, stored.cpu_ms, stored.reason.as_str()),
        (
            UncertifiedOutcome::CheckerTimeout,
            179_500,
            checker_timeout_reason().as_str()
        )
    );
    let hit = scope.lookup_at(now + 1).expect("replayed");
    assert_eq!(
        hit.non_credit_result(),
        AYResult::Unknown(checker_timeout_reason())
    );
    assert!(
        hit.describe().contains("kind=checker-timeout"),
        "{}",
        hit.describe()
    );
    // Not recorded: a starved or unmeasured checker expiry, no checker expiry
    // at all (only an exhausted solver deadline), or a checker expiry that
    // is the capability probe's (unsupervised).
    for (tag, solver, checker) in [
        ("starved check", vec![], vec![check_starved()]),
        (
            "unmeasured check",
            vec![],
            vec![Some(expiry(180_000, None))],
        ),
        ("solver expiry only", vec![Some(exhausting())], vec![]),
        ("probe", vec![], vec![None]),
        (
            "used then starved",
            vec![],
            vec![check_used(), check_starved()],
        ),
    ] {
        let (key, scope) = scope_for(tag);
        check_times_out(&scope, &solver, &checker, now);
        assert_eq!(read_entry(dir.path(), &key), None, "{tag}");
    }
    // A solver timeout is judged on the solver's expiries alone: an exhausted
    // checker deadline does not make a starved solve's timeout recordable,
    // and a starved checker expiry does not withhold an exhausted solve's.
    let (key, scope) = scope_for("solver starved, check used");
    scope.note_check_expiry(check_used());
    time_out(&scope, &[Some(starved())], now);
    assert_eq!(read_entry(dir.path(), &key), None);
    let (key, scope) = scope_for("solver used, check starved");
    scope.note_check_expiry(check_starved());
    time_out(&scope, &[Some(exhausting())], now);
    assert_eq!(
        read_entry(dir.path(), &key).map(|entry| (entry.outcome, entry.cpu_ms)),
        Some((UncertifiedOutcome::Timeout, 29_100))
    );
}

/// The evidence rule itself: a measured CPU time of at least the share of a
/// nonzero budget.
#[test]
fn budget_exhaustion_needs_a_measured_share_of_a_nonzero_budget() {
    assert_eq!(BUDGET_EXHAUSTING_CPU_PERCENT, 90);
    assert!(exhausted_budget(&exhausting()));
    assert!(exhausted_budget(&expiry(30_000, Some(27_000))));
    assert!(
        exhausted_budget(&expiry(30_000, Some(45_000))),
        "several threads"
    );
    assert!(!exhausted_budget(&DeadlineExpiry {
        limit: Duration::from_millis(30_000),
        cpu: Some(Duration::from_millis(27_000) - Duration::from_nanos(1)),
    }));
    assert!(!exhausted_budget(&starved()));
    assert!(!exhausted_budget(&expiry(30_000, None)), "unmeasured");
    assert!(!exhausted_budget(&expiry(0, Some(0))), "no budget");
    assert!(!exhausted_budget(&expiry(0, Some(5))), "no budget");
}

/// The measured defect (2026-10-01): AY's strict certification has its own
/// wall-clock bound, so under load a body that certifies at rest answers
/// `(incomplete self-check-rejected)`; two `core` bodies Valid in one census
/// came back uncertified in the next, run at load 16 on four cores, and the
/// memo recorded such answers like any other. A certification failure is
/// recorded only when at least one fresh solve completed and every one had
/// the processor; a starved, unmeasured or absent completion records
/// nothing and leaves an existing entry exactly as it is.
#[test]
fn a_certification_failure_of_a_starved_solve_is_not_recorded() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let store = Some(dir.path().to_path_buf());
    let now = now_unix_ms();
    new_process();
    let second = Duration::from_secs(1);
    let starved = |scope: &NegativeMemoScope| {
        scope.note_solve_completion(Duration::from_secs(9), Some(Duration::from_millis(2_300)));
    };
    let unmeasured = |scope: &NegativeMemoScope| scope.note_solve_completion(second, None);
    for outcome in [
        UncertifiedOutcome::SelfCheckRejected,
        UncertifiedOutcome::IncompleteCertificate,
        UncertifiedOutcome::CheckerRejected,
    ] {
        let failed = AYResult::Unknown(reason_of(outcome));
        let observe = |scope: &NegativeMemoScope, at: u64| {
            scope.observe_at(&failed, &AyVerdictSource::LiveSolve, second, at)
        };
        type Notes<'a> = Vec<&'a dyn Fn(&NegativeMemoScope)>;
        let unproven: Vec<(&str, Notes)> = vec![
            ("no completion", vec![]),
            ("starved", vec![&starved]),
            ("unmeasured", vec![&unmeasured]),
            ("held then starved", vec![&held, &starved]),
            ("starved then held", vec![&starved, &held]),
            ("held then unmeasured", vec![&held, &unmeasured]),
        ];
        for (tag, notes) in &unproven {
            let key = unique_key(&format!("{outcome:?} {tag} {}", dir.path().display()));
            let scope = NegativeMemoScope::new(key, store.clone(), RetryPolicy::DEFAULT);
            for note in notes {
                note(&scope);
            }
            observe(&scope, now);
            assert_eq!(read_entry(dir.path(), &key), None, "{outcome:?} {tag}");
            assert!(scope.lookup_at(now + 1).is_none(), "{outcome:?} {tag}");
        }
        // Every completion held the processor: recorded.
        let key = unique_key(&format!("{outcome:?} held {}", dir.path().display()));
        let fresh_scope = || NegativeMemoScope::new(key, store.clone(), RetryPolicy::DEFAULT);
        let recording = fresh_scope();
        held(&recording);
        held(&recording);
        observe(&recording, now);
        let before = read_entry(dir.path(), &key).expect("recorded");
        assert_eq!((before.outcome, before.cpu_ms), (outcome, 0));
        // A later starved replay neither refreshes, confirms nor deletes it.
        new_process();
        let later = fresh_scope();
        starved(&later);
        observe(&later, now + 10);
        assert_eq!(read_entry(dir.path(), &key), Some(before), "{outcome:?}");
        new_process();
    }
}

/// The evidence rule for a completion: a measured CPU time of at least the
/// share of a nonzero wall-clock time.
#[test]
fn holding_the_processor_needs_a_measured_share_of_a_nonzero_wall_time() {
    assert_eq!(PROCESSOR_HELD_CPU_PERCENT, 90);
    let second = Duration::from_secs(1);
    assert!(held_processor(second, Some(Duration::from_millis(990))));
    assert!(held_processor(second, Some(Duration::from_millis(900))));
    assert!(
        held_processor(second, Some(Duration::from_millis(1_800))),
        "several threads"
    );
    assert!(!held_processor(
        second,
        Some(Duration::from_millis(900) - Duration::from_nanos(1))
    ));
    assert!(!held_processor(
        Duration::from_secs(9),
        Some(Duration::from_millis(2_300))
    ));
    assert!(!held_processor(second, None), "unmeasured");
    assert!(
        !held_processor(Duration::ZERO, Some(Duration::ZERO)),
        "no time"
    );
}

/// The per-box tier survives the process tier: a fresh process (modelled by
/// forgetting the process tier) is answered from the store, and counts its
/// reuse there.
#[test]
fn the_store_tier_answers_a_fresh_process() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let key = unique_key(&format!("store {}", dir.path().display()));
    let scope = NegativeMemoScope::new(key, Some(dir.path().to_path_buf()), RetryPolicy::DEFAULT);
    let now = now_unix_ms();
    time_out(&scope, &[Some(exhausting())], now);
    new_process();
    let hit = scope.lookup_at(now + 1).expect("store hit");
    assert_eq!(hit.tier(), MemoTier::Store);
    assert_eq!(hit.non_credit_result(), AYResult::Timeout);
    assert_eq!(read_entry(dir.path(), &key).unwrap().reuses, 1);
    // No store: the process tier alone.
    let memory_only = NegativeMemoScope::new(unique_key("memory only"), None, RetryPolicy::DEFAULT);
    time_out(&memory_only, &[Some(exhausting())], now);
    assert!(memory_only.lookup_at(now + 1).is_some());
    new_process();
    assert!(memory_only.lookup_at(now + 2).is_none());
}

/// A reuse write-back never resurrects an entry a concurrent `Verified`
/// deleted: the store read-modify-write and the delete both hold the
/// namespace lock. Without the lock the reviewer saw the entry come back in
/// 2824 of 3000 overlapping rounds.
#[test]
fn a_reuse_write_back_never_resurrects_a_deleted_entry() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let key = unique_key(&format!("race {}", dir.path().display()));
    let store = Some(dir.path().to_path_buf());
    let policy = RetryPolicy {
        max_reuses: u32::MAX,
        base_reuses: u32::MAX,
        ..RetryPolicy::DEFAULT
    };
    let reader = NegativeMemoScope::new(key, store.clone(), policy);
    let deleter = NegativeMemoScope::new(key, store, policy);
    let now = now_unix_ms();
    let mut reused_first = 0usize;
    for round in 0..600 {
        write_entry(
            dir.path(),
            &key,
            &Entry {
                recorded_unix_ms: now,
                ..entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK)
            },
        )
        .unwrap();
        let barrier = std::sync::Barrier::new(2);
        let reused = std::thread::scope(|threads| {
            let reading = threads.spawn(|| {
                barrier.wait();
                reader.reuse_from_store(now + 1).is_some()
            });
            threads.spawn(|| {
                barrier.wait();
                deleter.forget();
            });
            reading.join().unwrap()
        });
        reused_first += usize::from(reused);
        assert_eq!(
            read_entry(dir.path(), &key),
            None,
            "round {round}: a deleted entry came back"
        );
        new_process();
    }
    eprintln!("reuse ran before the delete in {reused_first} of 600 rounds");
}

/// Each recording prunes a bounded window of the namespace: expired,
/// future-dated or unreadable entries and stale staging files go, live
/// entries and directories stay, and the lock file is kept.
#[test]
fn a_recording_prunes_expired_and_unreadable_entries() {
    let _serial = test_lock();
    let dir = tempfile::tempdir().unwrap();
    let now = now_unix_ms();
    let policy = RetryPolicy::DEFAULT;
    let day = 24 * HOUR_MS;
    let write = |tag: &str, recorded: u64| {
        let key = unique_key(tag);
        write_entry(
            dir.path(),
            &key,
            &Entry {
                recorded_unix_ms: recorded,
                ..entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK)
            },
        )
        .unwrap();
        key
    };
    let live = write("live", now - HOUR_MS);
    let expired = write("expired", now - day - 1);
    let future = write("future", now + day);
    let garbage = unique_key("garbage");
    std::fs::write(entry_path(dir.path(), &garbage), "not an entry").unwrap();
    let staging = dir.path().join(".negmemo-stale");
    std::fs::write(&staging, "half").unwrap();
    let old = std::time::SystemTime::now() - Duration::from_secs(3600);
    std::fs::File::options()
        .write(true)
        .open(&staging)
        .unwrap()
        .set_modified(old)
        .unwrap();
    let fresh_staging = dir.path().join(".negmemo-fresh");
    std::fs::write(&fresh_staging, "in flight").unwrap();
    let subdirectory = entry_path(dir.path(), &unique_key("a directory"));
    std::fs::create_dir(&subdirectory).unwrap();
    let lock = StoreLock::acquire(dir.path()).unwrap();
    // The window covers the whole (small) namespace.
    prune(dir.path(), &policy, now, &live);
    drop(lock);
    assert!(read_entry(dir.path(), &live).is_some());
    for gone in [expired, future, garbage] {
        assert!(!entry_path(dir.path(), &gone).exists(), "{}", gone.hex());
    }
    assert!(!staging.exists());
    assert!(fresh_staging.exists());
    assert!(subdirectory.is_dir());
    assert!(dir.path().join(".lock").is_file());
}

/// Concurrent writers within a process each publish a complete entry: every
/// read after the first publication parses as one of the written entries.
#[test]
fn concurrent_writers_never_tear_an_entry() {
    let dir = tempfile::tempdir().unwrap();
    let key = unique_key("threads");
    let written: Vec<Entry> = (0..8)
        .map(|writer| Entry {
            solve_ms: writer as u64 * 1000 + 7,
            confirmations: writer as u32 + 1,
            ..entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK)
        })
        .collect();
    write_entry(dir.path(), &key, &written[0]).unwrap();
    let stop = std::sync::atomic::AtomicBool::new(false);
    let (path, key_ref, stop_ref, written_ref) = (dir.path(), &key, &stop, &written);
    std::thread::scope(|threads| {
        let readers: Vec<_> = (0..4)
            .map(|_| {
                threads.spawn(move || {
                    let mut reads = 0usize;
                    while !stop_ref.load(std::sync::atomic::Ordering::Relaxed) {
                        let read = read_entry(path, key_ref).expect("never torn or absent");
                        assert!(written_ref.contains(&read));
                        reads += 1;
                    }
                    reads
                })
            })
            .collect();
        let writers: Vec<_> = written
            .iter()
            .map(|entry| {
                threads.spawn(move || {
                    for _ in 0..50 {
                        write_entry(path, key_ref, entry).unwrap();
                    }
                })
            })
            .collect();
        for writer in writers {
            writer.join().unwrap();
        }
        stop.store(true, std::sync::atomic::Ordering::Relaxed);
        for reader in readers {
            assert!(reader.join().unwrap() > 0);
        }
    });
    assert!(written.contains(&read_entry(dir.path(), &key).unwrap()));
    let leftovers: Vec<_> = std::fs::read_dir(dir.path())
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect();
    assert_eq!(leftovers.len(), 1, "no staging files left: {leftovers:?}");
}

/// The environment variable a writer child of this test binary reads.
const WRITER_DIR_ENV: &str = "NEGMEMO_TEST_WRITER_DIR";

/// Child half of [`concurrent_processes_never_tear_an_entry`]: inert unless
/// the parent names a directory. Not `#[ignore]`d: the soundness gate counts an
/// ignored test in its filter as a skip and fails the row, so the child runs as
/// an ordinary (empty) test and does its work only when spawned.
#[test]
fn negative_memo_store_writer_child() {
    let Some(dir) = std::env::var_os(WRITER_DIR_ENV) else {
        return;
    };
    let writer: u64 = std::env::var("NEGMEMO_TEST_WRITER")
        .unwrap()
        .parse()
        .unwrap();
    let key = unique_key("processes");
    let entry = Entry {
        solve_ms: writer * 1000 + 3,
        confirmations: writer as u32 + 1,
        ..entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK)
    };
    for _ in 0..200 {
        write_entry(Path::new(&dir), &key, &entry).unwrap();
    }
}

/// Concurrent writer PROCESSES (four children of this test binary) publish
/// into one entry while this process reads it: every read is complete.
#[cfg(unix)]
#[test]
fn concurrent_processes_never_tear_an_entry() {
    let dir = tempfile::tempdir().unwrap();
    let key = unique_key("processes");
    let seed = Entry {
        solve_ms: 1,
        ..entry(UncertifiedOutcome::SelfCheckRejected, SELF_CHECK)
    };
    write_entry(dir.path(), &key, &seed).unwrap();
    let exe = std::env::current_exe().unwrap();
    let mut children: Vec<_> = (0..4)
        .map(|writer| {
            std::process::Command::new(&exe)
                .args([
                    "--exact",
                    "source_bound_negative_memo::tests::negative_memo_store_writer_child",
                    "--test-threads=1",
                ])
                .env(WRITER_DIR_ENV, dir.path())
                .env("NEGMEMO_TEST_WRITER", writer.to_string())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .spawn()
                .unwrap()
        })
        .collect();
    let mut reads = 0usize;
    loop {
        let read = read_entry(dir.path(), &key).expect("never torn or absent");
        assert_eq!(read.reason, SELF_CHECK, "{read:?}");
        reads += 1;
        if children
            .iter_mut()
            .all(|child| child.try_wait().unwrap().is_some())
        {
            break;
        }
    }
    for mut child in children {
        assert!(child.wait().unwrap().success());
    }
    let last = read_entry(dir.path(), &key).expect("a complete final entry");
    assert_eq!(last.solve_ms % 1000, 3, "{last:?}");
    assert!(reads > 0);
    let leftovers = std::fs::read_dir(dir.path()).unwrap().count();
    assert_eq!(leftovers, 1, "no staging files left");
}
