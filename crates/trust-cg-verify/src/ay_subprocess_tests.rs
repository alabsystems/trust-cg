use super::*;
use std::os::unix::fs::PermissionsExt;

use crate::ay_identity::test_fixtures::{WARM_ARGUMENT, warm};

/// Resident slots, leases and exit cleanup are process-wide production state.
/// Exercise each process control in its own libtest process, so unrelated
/// parallel solver queries cannot queue ahead of its clock, recover its poison
/// or replace the process group it deliberately interrupts.
fn resident_control_in_own_process(name: &str) -> bool {
    const CHILD: &str = "TCG_TEST_ISOLATED_RESIDENT_CONTROL";
    let exact = format!("ay_bridge::subprocess_tests::{name}");
    if std::env::var_os(CHILD).as_deref() == Some(std::ffi::OsStr::new(&exact)) {
        return true;
    }
    let output = std::process::Command::new(std::env::current_exe().expect("current libtest"))
        .arg("--exact")
        .arg(&exact)
        .arg("--nocapture")
        .arg("--test-threads=1")
        .env(CHILD, &exact)
        .stdin(std::process::Stdio::null())
        .output()
        .expect("launch isolated resident control");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success()
            && stdout.contains("test result: ok. 1 passed; 0 failed; 0 ignored;"),
        "{exact} must execute and pass exactly once in its own process: {}\n{stdout}\n{stderr}",
        output.status
    );
    false
}

/// A new fixture, started once before any budget ([`warm`]). Its guard also
/// records each warm start in `<fixture>.warmed`, which
/// `fixtures_are_executed_before_any_budget_starts` counts.
fn script(body: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    let dir = tempfile::tempdir().expect("owned AY process control");
    let path = dir.path().join("ay-control");
    std::fs::write(
        &path,
        crate::ay_identity::test_fixtures::bind_self(
            &path,
            &format!(
                "#!/bin/sh\n\
                 if test \"$1\" = {WARM_ARGUMENT}; then printf 'warmed\\n' >> \"$0.warmed\"; exit 0; fi\n\
                 {body}\n"
            ),
        ),
    )
    .expect("write AY process control");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
        .expect("chmod AY control");
    warm(&path);
    (dir, path)
}

#[test]
fn fixtures_are_executed_before_any_budget_starts() {
    let (_dir, path) = script("exit 7");
    // Once from the fixture's own path, once from its admitted private copy.
    assert_eq!(
        std::fs::read_to_string(path.with_extension("warmed")).expect("warm-up record"),
        "warmed\nwarmed\n"
    );
    let copy = crate::ay_identity::test_fixtures::pin(&path)
        .command()
        .expect("admitted fixture copy");
    assert_ne!(
        std::path::Path::new(copy.get_program()),
        path,
        "an admitted AY is started from its private copy, which must be warmed too"
    );
    // Warming skips the body; a real start runs it.
    assert_eq!(
        std::process::Command::new(&path).status().unwrap().code(),
        Some(7)
    );
}

fn clean_promotion_timeout_control(probe_times_out: bool) {
    // The checker was already started once (`script` warms every fixture), so
    // the five-second budget is spent arming the intended probe/replay branch,
    // not on the host's first-exec assessment. Cancellation is required before
    // the ten-second controlled stall can complete.
    let condition = if probe_times_out {
        "true"
    } else {
        "test -f \"$0.probed\""
    };
    let (dir, checker) = script(&format!(
        "printf 'invoked\\n' >> \"$0.calls\"\n\
         if test ! -f \"$0.release\" && {condition}; then sleep 10; fi\n\
         : > \"$0.probed\"\n\
         printf 'External certificate verification: PASSED\\nType: Alethe SMT proof\\nProof status: fully verified\\n'"
    ));
    let smt2 = "(assert false)\n";
    let query = dir.path().join("query.smt2");
    std::fs::write(&query, smt2).unwrap();
    let proof_path = default_alethe_path(&query);
    let run = |timeout| {
        std::fs::write(&proof_path, "controlled proof").unwrap();
        trust_cg_process_env::with_env_overrides(
            &[
                ("TCG_EXTERNAL_CLEAN_CHECKER", checker.to_str().unwrap()),
                ("TCG_NO_PROOF_CACHE", "1"),
                // The check's own deadline (OD-223), five seconds here.
                (
                    crate::obligation_cert_store::PROOF_CHECK_TIMEOUT_ENV,
                    "5000",
                ),
            ],
            || {
                let authority = VerificationAuthority::capture_with_timeout(
                    &crate::ay_identity::test_fixtures::pin(&checker),
                    timeout,
                );
                promote_fresh_solver_unsat(
                    AYResult::SolverUnsat,
                    &authority,
                    &query,
                    smt2,
                    "Clean timeout control",
                    timeout,
                    &ReplayWitness::new(None),
                )
            },
        )
    };
    let start = Instant::now();
    // OD-223: a checker outcome, never an AY timeout. A probe that ran out of
    // its deadline leaves the proof uncheckable here; a check that ran out of
    // the checker's deadline is a Clean check timeout.
    let expected = if probe_times_out {
        CLEAN_PROBE_TIMEOUT_REASON
    } else {
        CLEAN_CHECK_TIMEOUT
    };
    match run(5000) {
        AYResult::Unknown(reason) if reason.starts_with(expected) => {}
        other => panic!("expected a checker outcome starting {expected:?}, got {other:?}"),
    }
    assert!(start.elapsed() < Duration::from_secs(8));
    assert!(
        !proof_path.exists(),
        "timed-out promotion must remove its owned proof"
    );
    let calls = dir.path().join("ay-control.calls");
    assert_eq!(
        std::fs::read_to_string(&calls).unwrap().lines().count(),
        if probe_times_out { 1 } else { 2 },
        "failure diagnostics must not silently launch a second capability probe"
    );
    std::fs::write(dir.path().join("ay-control.release"), "ready").unwrap();
    assert_eq!(
        run(0),
        AYResult::Verified,
        "the same executable may recover under an unlimited solve budget (the check keeps its \
         own finite deadline)"
    );
    assert!(!proof_path.exists());
}

// The fixture checker is selected explicitly, as in an ordinary build.
#[test]
fn cert_store_promotion_propagates_control_probe_timeout_without_reprobing() {
    crate::ay_identity::test_fixtures::with_ordinary_record(|| {
        clean_promotion_timeout_control(true)
    });
}

#[test]
fn cert_store_promotion_propagates_replay_timeout_instead_of_blaming_the_proof() {
    crate::ay_identity::test_fixtures::with_ordinary_record(|| {
        clean_promotion_timeout_control(false)
    });
}

#[test]
fn subprocess_fresh_solver_preserves_arguments_status_and_both_streams() {
    let (dir, path) = script(
        "test \"$1\" = '-smt2' || exit 23; test -f \"$2\" || exit 24; \
         test \"$#\" -eq 7 || exit 25; test \"$3\" = '--strict-proofs' || exit 26; \
         test \"$4\" = '--proof' || exit 27; test \"$5\" = \"$2.alethe\" || exit 28; \
         test \"$6\" = '--proof-format' || exit 29; test \"$7\" = 'alethe' || exit 30; \
         printf 'unknown\\n'; dd if=/dev/zero bs=131072 count=1 2>/dev/null; \
         dd if=/dev/zero bs=131072 count=1 1>&2 2>/dev/null; exit 7",
    );
    let query = dir.path().join("query with spaces.smt2");
    std::fs::write(&query, "(check-sat)\n").expect("owned query");
    for timeout_ms in [0, 10_000] {
        let output = run_solver_command(
            &crate::ay_identity::test_fixtures::pin(&path),
            &query,
            timeout_ms,
        )
        .expect("complete fresh-solver capture");
        assert_eq!(output.status.code(), Some(7));
        assert!(output.stdout.starts_with(b"unknown\n"));
        assert_eq!(output.stdout.len(), b"unknown\n".len() + 131072);
        assert_eq!(output.stderr.len(), 131072);
        assert!(output.stderr.iter().all(|&byte| byte == 0));
    }
}

#[test]
fn subprocess_verdict_queries_do_not_request_proof_artifacts() {
    let (dir, path) = script(
        "test \"$#\" -eq 2 || exit 21; test \"$1\" = '-smt2' || exit 22; \
         test -f \"$2\" || exit 23; printf 'sat\\n'",
    );
    let query = dir.path().join("model with spaces.smt2");
    std::fs::write(&query, "(check-sat)\n").expect("owned query");
    for timeout_ms in [0, 10_000] {
        let output = run_solver_verdict_command(
            &crate::ay_identity::test_fixtures::pin(&path),
            &query,
            timeout_ms,
        )
        .expect("complete verdict-only capture");
        assert!(output.status.success());
        assert_eq!(output.stdout, b"sat\n");
        assert!(output.stderr.is_empty());
        assert!(!default_alethe_path(&query).exists());
    }
}

fn authority_request_preserves_captured_environment(proof_requested: bool) {
    let _serial = formal_solver_test_lock();
    let request_control = if proof_requested {
        r#"
test "$#" -eq 7 || exit 21
test "$3" = --strict-proofs || exit 22
test "$4" = --proof || exit 23
test "$5" = "$2.alethe" || exit 24
test "$6" = --proof-format || exit 25
test "$7" = alethe || exit 26
printf 'transport-only proof control\n' > "$5"
printf 'unsat\n'
"#
    } else {
        r#"
test "$#" -eq 2 || exit 21
printf 'sat\n'
"#
    };
    let (dir, solver) = script(&format!(
        r#"
test "$1" = -smt2 || exit 11
test -f "$2" || exit 12
test "$GOVERN_AY_MB" = 128 || exit 13
test "$RAYON_NUM_THREADS" = 2 || exit 14
self="$0"
test "$TMPDIR" = "${{self%/*}}/captured temp" || exit 15
test "$PATH" = /usr/bin:/bin || exit 16
test "$LANG" = C && test "$LC_ALL" = C || exit 17
test -z "${{TCG_AUTHORITY_TRANSPORT_TEST+x}}" || exit 18
test -z "${{AY_AUTHORITY_TRANSPORT_TEST+x}}" || exit 19
test -z "${{LD_LIBRARY_PATH+x}}" || exit 20
{request_control}
"#
    ));
    let captured_temp = dir.path().join("captured temp");
    let later_temp = dir.path().join("later temp");
    std::fs::create_dir(&captured_temp).expect("captured temporary directory");
    std::fs::create_dir(&later_temp).expect("later temporary directory");
    let query = dir.path().join("query with spaces.smt2");
    std::fs::write(&query, "(check-sat)\n").expect("owned authority query");

    // Transport-only capture avoids invoking any real checker. Neither the
    // synthetic transcript nor the synthetic proof can mint proof authority.
    let authority = trust_cg_process_env::with_env_edits(|environment| {
        environment.set("GOVERN_AY_MB", "128");
        environment.set("RAYON_NUM_THREADS", "2");
        environment.set("TMPDIR", captured_temp.as_os_str());
        environment.set("LANG", "captured-parent-locale");
        environment.set("LC_ALL", "captured-parent-locale");
        environment.set("TCG_AUTHORITY_TRANSPORT_TEST", "captured-poison");
        environment.set("AY_AUTHORITY_TRANSPORT_TEST", "captured-poison");
        environment.set("LD_LIBRARY_PATH", "captured-loader-poison");
        VerificationAuthority::capture_solver_process(&crate::ay_identity::test_fixtures::pin(
            &solver,
        ))
    });
    assert!(authority.checker().is_none());
    assert!(authority.positive_reuse_context_id().is_none());
    let captured_digest = authority.child_env().digest();

    trust_cg_process_env::with_env_edits(|environment| {
        environment.set("GOVERN_AY_MB", "256");
        environment.set("RAYON_NUM_THREADS", "4");
        environment.set("TMPDIR", later_temp.as_os_str());
        environment.set("PATH", dir.path().join("missing path").as_os_str());
        environment.set("LANG", "later-parent-locale");
        environment.set("LC_ALL", "later-parent-locale");
        environment.set("TCG_AUTHORITY_TRANSPORT_TEST", "later-poison");
        environment.set("AY_AUTHORITY_TRANSPORT_TEST", "later-poison");
        environment.set("LD_LIBRARY_PATH", "later-loader-poison");
        assert_ne!(
            captured_digest,
            SanitizedChildEnv::capture_verifier().digest(),
            "recapturing the current scoped environment must change the identity"
        );
        for timeout_ms in [0, 10_000] {
            let output = if proof_requested {
                run_solver_command_with_authority(&authority, &query, timeout_ms)
                    .map(|completed| completed.output)
            } else {
                run_solver_verdict_command_with_authority(&authority, &query, timeout_ms)
            }
            .expect("complete authority-bound transport");
            assert!(output.status.success(), "{output:?}");
            assert!(output.stderr.is_empty(), "{output:?}");
            if proof_requested {
                assert_eq!(output.stdout, b"unsat\n");
                assert_eq!(
                    std::fs::read(default_alethe_path(&query)).expect("requested proof artifact"),
                    b"transport-only proof control\n"
                );
                assert_eq!(
                    parse_solver_process_output(&output, &[]),
                    AYResult::SolverUnsat
                );
            } else {
                assert_eq!(output.stdout, b"sat\n");
                assert!(!default_alethe_path(&query).exists());
            }
            assert_eq!(authority.child_env().digest(), captured_digest);
        }
    });
}

#[test]
fn subprocess_authority_proof_request_preserves_captured_environment() {
    authority_request_preserves_captured_environment(true);
}

#[test]
fn subprocess_authority_verdict_request_preserves_captured_environment() {
    authority_request_preserves_captured_environment(false);
}

#[test]
fn subprocess_fresh_solver_cannot_return_a_partial_unsat_transcript() {
    let (dir, path) = script("printf 'unsat\\n'; (sleep 3; printf 'late output\\n') &\nexit 0");
    let query = dir.path().join("query.smt2");
    std::fs::write(&query, "(check-sat)\n").expect("owned query");
    let result = run_solver_command(&crate::ay_identity::test_fixtures::pin(&path), &query, 1000);
    assert!(
        matches!(result, Err(SolverInvocationError::Timeout(_))),
        "{result:?}"
    );
}

#[test]
fn resident_io_deadline_covers_a_request_larger_than_pipe_capacity() {
    if !resident_control_in_own_process(
        "resident_io_deadline_covers_a_request_larger_than_pipe_capacity",
    ) {
        return;
    }
    let _serial = formal_solver_test_lock();
    let (_dir, path) = script("sleep 3; exit 0");
    let query = format!(";{}\n(check-sat)\n(exit)\n", "x".repeat(1024 * 1024));
    let start = Instant::now();
    let result = run_solver_via_server(
        &crate::ay_identity::test_fixtures::pin(&path),
        &query,
        1000,
        &[],
    );
    assert!(
        matches!(result, AyServerAttempt::TimedOut(_)),
        "a blocked request must consume its deadline, not wait for EOF and request a fresh retry"
    );
    assert!(start.elapsed() < Duration::from_secs(2));
}

/// The first start of a new private copy is not solver time. An AY build
/// whose FIRST start takes 3 s (as a new copy of the 158 MB toolchain AY took
/// 1.6-32.2 s on macOS; see `ay_identity::first_start`) answers a resident
/// query with a 1.5 s budget (the queued-window test's), because that start is
/// made before the query is admitted. When the resident spawn was that first
/// start, inside the query's deadline, the query timed out. Only a host that
/// assesses new executables makes that start on its own.
#[cfg(target_os = "macos")]
#[test]
fn resident_deadline_does_not_pay_the_first_start_of_a_new_copy() {
    if !resident_control_in_own_process(
        "resident_deadline_does_not_pay_the_first_start_of_a_new_copy",
    ) {
        return;
    }
    let _serial = formal_solver_test_lock();
    let (dir, path) = script(
        r#"
if test ! -e "$0.first"; then : > "$0.first"; sleep 3; fi
printf '%s\n' "$*" >> "$0.starts"
test "$1" = --incremental || exit 0
while IFS= read -r line; do
  case "$line" in
    '(echo "'*'")')
      marker=${line#'(echo "'}
      marker=${marker%'")'}
      printf 'unknown\n'
      printf '%s\n' "$marker"
      ;;
  esac
done
"#,
    );
    let solver = crate::ay_identity::test_fixtures::pin_as_build(&path);
    let result = run_solver_via_server(&solver, "(check-sat)\n(exit)\n", 1_500, &[]);
    *ay_server_slot()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner) = None;
    let starts = std::fs::read_to_string(dir.path().join("ay-control.starts")).unwrap_or_default();
    assert!(
        matches!(result, AyServerAttempt::Completed(AYResult::Unknown(_))),
        "a query must not time out on its AY's first start (starts: {starts:?})"
    );
    assert_eq!(
        starts.lines().collect::<Vec<_>>(),
        ["--version", "--incremental"],
        "one first start, then the resident process"
    );
}

/// A query queued behind a slow window is charged only for its OWN solver time:
/// it waits longer than its whole budget, then completes. (Before the deadline
/// started at admission, this query returned `TimedOut` without ever reaching
/// the solver.)
#[test]
fn resident_io_queued_query_is_not_charged_for_the_wait() {
    if !resident_control_in_own_process("resident_io_queued_query_is_not_charged_for_the_wait") {
        return;
    }
    let _serial = formal_solver_test_lock();
    const SLOW_WINDOW: Duration = Duration::from_secs(3);
    const QUEUED_BUDGET: Duration = Duration::from_millis(1500);
    let (_dir, path) = script(
        r#"
slow=
while IFS= read -r line; do
  case "$line" in
    '; slow window')
      slow=1
      : > "$0.slow"
      ;;
    '(echo "'*'")')
      marker=${line#'(echo "'}
      marker=${marker%'")'}
      if test -n "$slow"; then sleep 3; slow=; fi
      printf 'unknown
'
      printf '%s
' "$marker"
      ;;
  esac
done
"#,
    );
    let solver = crate::ay_identity::test_fixtures::pin(&path);
    let slow_marker = path.with_extension("slow");
    let slow = {
        let solver = solver.clone();
        std::thread::spawn(move || {
            run_solver_via_server(&solver, "; slow window\n(check-sat)\n(exit)\n", 60_000, &[])
        })
    };
    // The slow query holds the server once its window reached the solver.
    let armed = Instant::now();
    while !slow_marker.exists() {
        assert!(
            armed.elapsed() < Duration::from_secs(30),
            "the slow window never reached the resident solver"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
    let queued_at = Instant::now();
    let queued = run_solver_via_server(
        &solver,
        "(check-sat)\n(exit)\n",
        u64::try_from(QUEUED_BUDGET.as_millis()).expect("budget fits"),
        &[],
    );
    let waited = queued_at.elapsed();
    let slow = slow.join().expect("slow query thread");
    *ay_server_slot().lock().expect("slot") = None;

    assert!(
        matches!(slow, AyServerAttempt::Completed(AYResult::Unknown(_))),
        "the slow window itself completes within its own budget"
    );
    assert!(
        matches!(queued, AyServerAttempt::Completed(AYResult::Unknown(_))),
        "a query queued behind a {SLOW_WINDOW:?} window must not be charged for the wait \
         (budget {QUEUED_BUDGET:?}, waited {waited:?})"
    );
    assert!(
        waited > QUEUED_BUDGET,
        "the control must queue longer than the whole budget, waited {waited:?}"
    );
}

/// Queueing is bounded separately from solver time: a waiter is refused, by
/// name, only once the holder has run past its OWN admitted budget plus the
/// overrun allowance. A holder inside its budget, or under the explicit
/// unlimited policy, is waited for. (A private slot and lease: the deliberately
/// wedged holder below must never refuse another test's real query.)
#[test]
fn resident_io_waiter_is_refused_only_when_the_holder_overruns_its_own_budget() {
    static SLOT: AyServerSlot = std::sync::Mutex::new(None);
    static LEASE: AyServerLeaseSlot = std::sync::Mutex::new(None);
    const ALLOWANCE: Duration = Duration::from_millis(10);
    const HOLD: Duration = Duration::from_millis(1200);
    // The waiter's clock starts BEFORE the caller's hold does: `waiter` returns
    // only once the thread has read `start`, so a late-scheduled thread cannot
    // take `start` after the hold began and measure less than it. It reports
    // its own lease's `admitted_at`, read while it still holds the server.
    let waiter = |budget: Duration| {
        let (started_tx, started_rx) = std::sync::mpsc::channel();
        let handle = std::thread::spawn(move || {
            let start = Instant::now();
            started_tx.send(()).expect("caller waits for the start");
            admit_to_server_slot(&SLOT, &LEASE, Some(budget), ALLOWANCE).map(|admission| {
                let admitted_at = read_ay_server_lease(&LEASE)
                    .expect("an admission holds its lease")
                    .admitted_at;
                // Admitted after the wait with the WHOLE budget still ahead.
                let fresh = !admission.deadline.expired();
                (start, admitted_at, fresh)
            })
        });
        started_rx.recv().expect("waiter thread starts");
        handle
    };

    // A holder inside its budget, and one under the unlimited policy, is waited
    // for; the waiter's own budget starts when it is admitted.
    for holder_budget in [Some(Duration::from_secs(60)), None] {
        let holder = admit_to_server_slot(&SLOT, &LEASE, holder_budget, ALLOWANCE)
            .expect("uncontended slot");
        let queued = waiter(Duration::from_secs(1));
        std::thread::sleep(HOLD);
        assert!(
            !queued.is_finished(),
            "a holder within its budget ({holder_budget:?}) must not refuse its waiters"
        );
        let released_at = Instant::now();
        drop(holder);
        let (start, admitted_at, fresh) = queued
            .join()
            .expect("waiter thread")
            .expect("admitted once the holder released the server");
        // The property itself: no admission before the holder released. And
        // the original bound, now measured from a start that precedes the hold.
        assert!(
            admitted_at >= released_at,
            "admitted {:?} before the holder released",
            released_at.duration_since(admitted_at)
        );
        let waited = admitted_at.duration_since(start);
        assert!(waited >= HOLD, "waited {waited:?}");
        assert!(
            fresh,
            "the {waited:?} wait must not be charged to a 1s budget"
        );
        assert!(
            read_ay_server_lease(&LEASE).is_none(),
            "a released admission withdraws its lease"
        );
    }

    // A holder past its own 1 ms budget plus the allowance is wedged: the waiter
    // is refused by name, promptly, without being admitted.
    let holder = admit_to_server_slot(&SLOT, &LEASE, Some(Duration::from_millis(1)), ALLOWANCE)
        .expect("uncontended slot");
    std::thread::sleep(Duration::from_millis(50));
    let start = Instant::now();
    let queued = waiter(Duration::from_secs(60));
    while !queued.is_finished() && start.elapsed() < Duration::from_secs(5) {
        std::thread::sleep(Duration::from_millis(5));
    }
    let refused_after = start.elapsed();
    // Release before joining, so a waiter that was NOT refused is admitted and
    // fails the assertion below instead of hanging the test.
    drop(holder);
    let Err(refusal) = queued.join().expect("waiter thread") else {
        panic!("a waiter behind an overrun holder must be refused");
    };
    assert!(refused_after < Duration::from_secs(5), "{refused_after:?}");
    assert_eq!(refusal.holder_budget, Duration::from_millis(1));
    assert_eq!(refusal.allowance, ALLOWANCE);
    assert!(refusal.held_for > Duration::from_millis(11), "{refusal:?}");
    assert!(
        refusal
            .to_string()
            .starts_with("resident AY server wedged: the query holding it has run "),
        "{refusal}"
    );
}

/// A query the resident-server queue refuses never reached a solver. Both
/// callers of the resident server — the verification funnel and the SAT model
/// replay — surface the named refusal as `AYResult::Error`: never `Timeout`
/// (a solver outcome consuming the query's budget) and never a fresh-process
/// retry. A refusal also leaves the resident server in service: it is evidence
/// about the query holding the server, not about this solver's resident mode,
/// so it must not latch the server unusable, and once the holder releases it
/// the same resident process serves the next queries. The server is private,
/// so the holder wedged here (past its own 1 ms budget plus a 10 ms allowance)
/// cannot refuse another test's query; the controls make the same calls with
/// the server free and must reach the resident solver.
#[test]
fn resident_io_queue_refusal_is_an_error_not_a_timeout() {
    if !resident_control_in_own_process("resident_io_queue_refusal_is_an_error_not_a_timeout") {
        return;
    }
    // Serializes with the solver test that arms the regen recorder, which
    // switches the resident path off process-wide.
    let _serial = formal_solver_test_lock();
    static SLOT: AyServerSlot = std::sync::Mutex::new(None);
    static LEASE: AyServerLeaseSlot = std::sync::Mutex::new(None);
    let server = AyResidentServer {
        slot: &SLOT,
        lease: &LEASE,
        overrun_allowance: Duration::from_millis(10),
    };
    let (_dir, path) = echo_server("printf 'sat\\n'");
    let solver = crate::ay_identity::test_fixtures::pin(&path);
    let x = crate::smt::SmtExpr::var("queue_refusal_x", 8);
    let obligation = ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "resident_queue_refusal".to_string(),
        trust_ir_expr: x.clone(),
        aarch64_expr: x,
        inputs: vec![("queue_refusal_x".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    };
    let config = AYConfig {
        solver: Some(solver.clone()),
        timeout_ms: 5_000,
        produce_models: true,
    };
    let smt2 = generate_smt2_query(&obligation, &config);
    let selection = SolverSelection::explicit(solver.clone());
    let authority = VerificationAuthority::capture_solver_process(&solver);
    let verify = || {
        trust_cg_process_env::with_env_overrides_removed(
            &["TCG_NO_SOLVER_SERVER", "TRUST_CG_RUN_FORMAL_PROOF_TESTS"],
            || {
                verify_with_cli_smt2_on_server(
                    server,
                    &obligation,
                    &config,
                    AyQueryText::raw(&smt2),
                    &selection,
                    &authority,
                    false,
                    None,
                )
            },
        )
    };
    let model_replay = || {
        enrich_sat_counterexample_via_server(
            server,
            &authority,
            &obligation,
            &config,
            &smt2,
            AYResult::CounterExample(vec![]),
            &ReplayWitness::new(None),
        )
    };
    let solver_starts = || {
        std::fs::read_to_string(path.with_extension("started"))
            .map_or(0, |starts| starts.lines().count())
    };

    // Controls: with the server free, both calls are answered by the resident
    // solver (`sat`, so the funnel also runs the model replay).
    assert_eq!(
        verify(),
        (AYResult::CounterExample(vec![]), AyVerdictSource::LiveSolve)
    );
    assert_eq!(model_replay(), AYResult::CounterExample(vec![]));
    assert_eq!(
        solver_starts(),
        1,
        "one resident process served both controls"
    );

    // A holder past its own budget plus the allowance: each call is refused by
    // name, as an error, without starting or reaching a solver.
    let holder = server
        .admit(Some(Duration::from_millis(1)))
        .expect("uncontended private server");
    std::thread::sleep(Duration::from_millis(50));
    let (refused, refused_source) = verify();
    let refused_replay = model_replay();
    drop(holder);
    assert_eq!(
        refused_source,
        AyVerdictSource::NotRun,
        "a refused query is attributed to no AY run"
    );
    for (caller, result) in [
        ("verification funnel", refused),
        ("SAT model replay", refused_replay),
    ] {
        match result {
            AYResult::Error(reason) => assert!(
                reason.starts_with("resident AY server wedged: the query holding it has run "),
                "{caller}: the refusal must be the named queue refusal, got {reason:?}"
            ),
            other => panic!(
                "{caller}: a refused query never reached a solver, so it must be \
                 AYResult::Error, never a solver outcome; got {other:?}"
            ),
        }
    }
    assert_eq!(solver_starts(), 1, "a refused query starts no solver");

    // The refusals left the resident server in service: not latched unusable,
    // and with the holder gone the same resident process answers both callers
    // again, with no fresh process.
    assert!(
        !ay_server_is_unusable_for_authority(&authority),
        "a queue refusal must not switch the resident server off for later queries"
    );
    assert_eq!(
        verify(),
        (AYResult::CounterExample(vec![]), AyVerdictSource::LiveSolve)
    );
    assert_eq!(model_replay(), AYResult::CounterExample(vec![]));
    assert_eq!(
        solver_starts(),
        1,
        "after a refusal, later queries are served by the same resident process"
    );
    *SLOT.lock().expect("private slot") = None;
}

#[test]
fn resident_io_sequence_exhaustion_cannot_reuse_a_sentinel() {
    use std::sync::atomic::{AtomicU64, Ordering};
    let sequence = AtomicU64::new(u64::MAX - 1);
    assert_eq!(reserve_server_sequence(&sequence), Some(u64::MAX - 1));
    for _ in 0..2 {
        assert_eq!(reserve_server_sequence(&sequence), None);
    }
    assert_eq!(sequence.load(Ordering::Relaxed), u64::MAX);
}

fn echo_server(response: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    script(&format!(
        r#"
printf 'started\n' >> "$0.started"
while IFS= read -r line; do
  case "$line" in
    '(echo "'*'")')
      marker=${{line#'(echo "'}}
      marker=${{marker%'")'}}
      {response}
      printf '%s\n' "$marker"
      ;;
  esac
done
"#
    ))
}

#[test]
fn resident_io_reuses_a_framed_process_with_unlimited_and_huge_budgets() {
    if !resident_control_in_own_process(
        "resident_io_reuses_a_framed_process_with_unlimited_and_huge_budgets",
    ) {
        return;
    }
    let _serial = formal_solver_test_lock();
    let (_dir, path) = echo_server("printf 'un'; sleep 0.01; printf 'known\\r\\n'");
    for timeout in [0, u64::MAX] {
        let result = run_solver_via_server(
            &crate::ay_identity::test_fixtures::pin(&path),
            "(check-sat)\n(exit)\n",
            timeout,
            &[],
        );
        assert!(matches!(
            result,
            AyServerAttempt::Completed(AYResult::Unknown(_))
        ));
    }
    assert_eq!(
        std::fs::read_to_string(path.with_extension("started")).expect("starts"),
        "started\n"
    );
    *ay_server_slot().lock().expect("slot") = None;
}

#[test]
fn resident_io_rejects_duplicate_verdicts_and_preserves_protocol_errors() {
    if !resident_control_in_own_process(
        "resident_io_rejects_duplicate_verdicts_and_preserves_protocol_errors",
    ) {
        return;
    }
    let _serial = formal_solver_test_lock();
    let (_dir, path) = echo_server("printf 'unsat\\nsat\\n'");
    let result = run_solver_via_server(
        &crate::ay_identity::test_fixtures::pin(&path),
        "(check-sat)\n(exit)\n",
        5000,
        &[],
    );
    assert!(matches!(result, AyServerAttempt::Anomaly));
    assert!(ay_server_slot().lock().expect("slot").is_none());
    let (_dir, path) = echo_server("printf '(error \"control\")\\nunknown\\n'");
    let result = run_solver_via_server(
        &crate::ay_identity::test_fixtures::pin(&path),
        "(check-sat)\n(exit)\n",
        5000,
        &[],
    );
    assert!(
        matches!(result, AyServerAttempt::Completed(AYResult::Error(ref error)) if error.contains("control"))
    );
    *ay_server_slot().lock().expect("slot") = None;
}

#[test]
fn resident_io_poisoned_slot_discards_the_interrupted_process() {
    if !resident_control_in_own_process(
        "resident_io_poisoned_slot_discards_the_interrupted_process",
    ) {
        return;
    }
    let _serial = formal_solver_test_lock();
    let (_dir, path) = script("sleep 3");
    let child = std::thread::spawn(move || {
        let mut slot = ay_server_slot().lock().expect("slot");
        let authority = VerificationAuthority::capture_solver_process(
            &crate::ay_identity::test_fixtures::pin(&path),
        );
        *slot = spawn_ay_server(&authority);
        assert!(slot.is_some(), "the interrupted process must exist");
        panic!("deliberate interrupted-window control");
    });
    let panic = child.join().expect_err("deliberate worker panic");
    assert_eq!(
        panic.downcast_ref::<&str>(),
        Some(&"deliberate interrupted-window control")
    );
    assert!(ay_server_slot().is_poisoned());
    let admission = AyResidentServer::process()
        .admit(Some(Duration::from_secs(1)))
        .expect("recovered slot");
    assert!(admission.slot.is_none());
    assert!(!ay_server_slot().is_poisoned());
}

/// A fixture AY that refuses its own proof of a conjunctive assert the way AY
/// 0.26.0 build 9624 does (`and_pos`), and answers any other script `unsat`
/// with `split_proof` as its Alethe proof.
fn and_pos_refusing_ay(split_proof: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    assert!(
        !split_proof.contains("PROOF\n"),
        "heredoc terminator in the proof"
    );
    script(&format!(
        "test \"$1\" = -smt2 || exit 91\n\
         if grep -q '^(assert (and' \"$2\"; then\n\
         printf 'Error: required UNSAT publication failed: refusing to write unverifiable \
         proof to %s (#8821): invalid surface proof step t1: and_pos indexed conjunct is \
         absent from its effective source\\n' \"$5\" >&2\n\
         exit 1\n\
         fi\n\
         cat > \"$5\" <<'PROOF'\n{split_proof}PROOF\n\
         printf 'unsat\\n'"
    ))
}

/// The `and_pos` retry certifies against the ORIGINAL script (OD-106). AY
/// refuses its proof of the conjunction and publishes its recorded proof of
/// the split script, whose top-level assumptions are not premises of the
/// original: as AY emitted it the real checker rejects it, and only after
/// `split_conjunct_proof` re-derives them from the conjunction does it certify.
/// A split proof that assumes a non-conjunct, or whose re-derived steps do
/// not prove UNSAT, leaves the original refusal. Tool-gated: needs a capable
/// Clean checker, and SKIPs by name without one.
#[test]
fn an_and_pos_refusal_certifies_through_the_split_retry_against_the_original() {
    const TEST: &str = "an_and_pos_refusal_certifies_through_the_split_retry_against_the_original";
    use crate::split_conjunct_proof::tests::{IDENT_QUERY, IDENT_SPLIT_PROOF_AY_9624};
    let _serial = formal_solver_test_lock();
    let Some(checker) = crate::obligation_cert_store::clean_checker_path() else {
        crate::formal_gap::skip_test(TEST, crate::formal_gap::NO_CLEAN_CHECKER);
        return;
    };
    let obligation = ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "split retry original-problem control".to_string(),
        trust_ir_expr: crate::smt::SmtExpr::var("p0", 64),
        aarch64_expr: crate::smt::SmtExpr::var("m1", 64),
        inputs: vec![("e_rdi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    };
    let run = |split_proof: &str| {
        let (_dir, path) = and_pos_refusing_ay(split_proof);
        let solver = crate::ay_identity::test_fixtures::pin(&path);
        let config = AYConfig {
            solver: Some(solver.clone()),
            timeout_ms: 30_000,
            produce_models: true,
        };
        trust_cg_process_env::with_env_overrides(
            &[
                ("TCG_EXTERNAL_CLEAN_CHECKER", checker.to_str().unwrap()),
                ("TCG_NO_PROOF_CACHE", "1"),
                ("TCG_NO_CERT_STORE", "1"),
            ],
            || {
                let authority = VerificationAuthority::capture(&solver);
                let witness = ReplayWitness::new(None);
                let split = split_assert_conjuncts(IDENT_QUERY).expect("Ident splits");
                let as_emitted = run_fresh_producer_query_once(
                    &authority,
                    &obligation,
                    &config,
                    AyQueryText {
                        original: IDENT_QUERY,
                        producer: Some(&split),
                        closed_definitions: false,
                        fresh_after_resident_timeout: false,
                    },
                    &witness,
                );
                let retried = run_fresh_authority_query(
                    &authority,
                    &obligation,
                    &config,
                    IDENT_QUERY,
                    &witness,
                );
                (as_emitted, retried)
            },
        )
    };

    // The recorded proof: rejected against the original as emitted, credited
    // once its assumptions are re-derived from the conjunction.
    let (as_emitted, retried) = run(IDENT_SPLIT_PROOF_AY_9624);
    assert!(
        matches!(&as_emitted, AYResult::Unknown(reason)
            if reason.contains(WORKING_CHECKER_REJECTED_THIS_PROOF)),
        "the split proof's assumptions are not premises of the original: {as_emitted:?}"
    );
    assert_eq!(retried, AYResult::Verified);

    // An assumption that is no conjunct: the bridge declines, the original
    // refusal stands.
    let (_, retried) = run(
        &IDENT_SPLIT_PROOF_AY_9624.replace("(assume t2 (= m1 m0))", "(assume t2 (= m1 e_rdi))")
    );
    assert!(is_and_pos_publication_failure(&retried), "{retried:?}");

    // Re-derived assumptions under a proof that does not refute them: the
    // checker rejects it, the original refusal stands.
    let (_, retried) =
        run(&IDENT_SPLIT_PROOF_AY_9624.replace(":premises (t7 t3))", ":premises (t7 t2))"));
    assert!(is_and_pos_publication_failure(&retried), "{retried:?}");
}
