// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Ruling OD-223 on the real x86-64 body replay path (request capture,
//! `live_source_bound_replay_explained`, the exact-query funnel, the
//! certificate store, the negative memo, the export's re-check): the Clean
//! check of AY's proof has its own deadline, separate from the AY solve
//! budget, and its outcomes are labelled as the checker's. Driven by the
//! counting fixture AY of the negative-memo controls and a fixture Clean
//! whose check of the fixture proof is fast, slower than the solve budget,
//! never ending, or a refusal. No proof content: the fixture proof is
//! transport only, so these controls are about which deadline bounds which
//! subprocess and what the outcome may credit and is called.
//!
//! The measured case these stand in for: `core::num::<u64>::leading_zeros`
//! (census s23final, query `9eb494ad…`), which AY 13556 answers `unsat` in
//! 7.6-8.0 s while Clean 5f09e36c needs 41-53 s of CPU time to check its
//! ~11 MB proof. Under main's 30 s budget shared by both, the check ran out,
//! the outcome read "AY TIMEOUT", and the negative memo recorded it as a
//! solver timeout.

use super::*;
use crate::verify::VerificationResult;

/// A fixture Clean. Its capability probe (any certificate but the fixture
/// proof) always passes; its check of the fixture proof AY writes
/// (`fixture proof (transport only)`) appends `check` to `<clean>.calls`
/// and then, while `<clean>.slow` exists, takes 1.2 s computing in four
/// processes of its group (longer than the solve budgets below, far shorter
/// than the checker's default deadline); while `<clean>.lag` exists, takes
/// 1 s waiting; while `<clean>.spin` exists, never ends, computing in eight
/// processes of its group (a checker deadline used in CPU time); and while
/// `<clean>.reject` exists, refuses the proof. Otherwise it accepts at once.
const SWITCHABLE_CHECKER: &str = r#"if test "$1" = cert && test "$2" = verify-external && grep -q 'transport only' "$3"; then
  printf 'check\n' >> "$0.calls"
  if test -f "$0.spin"; then
    for spinner in 1 2 3 4 5 6 7 8; do (while :; do :; done) & done
    wait
  fi
  if test -f "$0.slow"; then
    spinners=""
    for spinner in 1 2 3 4; do (while :; do :; done) & spinners="$spinners $!"; done
    sleep 1.2
    kill $spinners
    wait
  fi
  if test -f "$0.lag"; then sleep 1; fi
  if test -f "$0.reject"; then
    printf 'External certificate verification: FAILED\n'
    exit 1
  fi
fi
printf 'External certificate verification: PASSED\nType: Alethe SMT proof\nProof status: fully verified\n'"#;

fn switchable_checker(dir: &std::path::Path) -> std::path::PathBuf {
    fixture_script(dir, "clean", SWITCHABLE_CHECKER)
}

/// Checks of the fixture proof the fixture Clean has run.
fn checks(clean: &std::path::Path) -> usize {
    std::fs::read_to_string(clean.with_extension("calls")).map_or(0, |text| {
        text.lines().filter(|line| *line == "check").count()
    })
}

/// One replay of `(source, machine)`'s body theorem under a freshly captured
/// request, through the same entry the x86-64 body owner's replay takes
/// (`SourceBoundReplayContext::x86_body_explained` replays through it):
/// (verdict, whether it is reusable for the request, the explanation the
/// body trace prints after `reason=`).
fn explained(
    source: &trust_cg_lower::Function,
    machine: &X86ISelFunction,
) -> (Option<VerificationResult>, bool, Option<String>) {
    let owner = source_bound_x86_body(source, machine, SYSV).unwrap();
    let verifier = promotion_verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    request.with_policy(|| crate::verdict_db::live_source_bound_replay_explained(&owner, &request))
}

/// The outcome label of every entry under `store`.
fn outcomes(store: &std::path::Path) -> Vec<String> {
    entries(store)
        .iter()
        .map(|entry| {
            let text = std::fs::read_to_string(entry).unwrap();
            text.lines()
                .find_map(|line| line.strip_prefix("outcome:"))
                .unwrap_or_default()
                .to_owned()
        })
        .collect()
}

/// With the solve budget at `solve_ms` and, when given, the checker deadline
/// at `check_ms`.
fn budgets<T>(solve_ms: &str, check_ms: Option<&str>, f: impl FnOnce() -> T) -> T {
    trust_cg_process_env::with_env_edits(|env| {
        env.set("TCG_RECON_SOLVER_MS", solve_ms);
        match check_ms {
            Some(ms) => env.set(crate::obligation_cert_store::PROOF_CHECK_TIMEOUT_ENV, ms),
            None => env.remove(crate::obligation_cert_store::PROOF_CHECK_TIMEOUT_ENV),
        }
        f()
    })
}

/// The census case on the one-shot route: AY answers `unsat` at once, and
/// Clean's check of the exact proof takes longer than the whole solve budget
/// (1.2 s against 500 ms). The check runs under the checker's own deadline,
/// so the proof is credited: every covered row, a reusable report, an
/// export, no negative entry. On main (the check under the solve budget) the
/// check was killed at 500 ms, nothing was credited and the outcome read
/// "AY TIMEOUT".
#[test]
fn a_fast_solve_whose_check_outlasts_the_solve_budget_is_credited() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = switchable_checker(dir.path());
    let (source, machine) = pair(Shape::Add);
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    set_mode(&ay, "prove", true);
    set_mode(&clean, "slow", true);
    with_memo_replay(&ay, &clean, &store, || {
        budgets("500", None, || {
            let started = std::time::Instant::now();
            let (verdict, reusable, why) = explained(&source, &machine);
            let elapsed = started.elapsed();
            assert!(
                matches!(verdict, Some(VerificationResult::Valid)) && reusable && why.is_none(),
                "the checked proof credits the theorem: {verdict:?} reusable={reusable} {why:?}"
            );
            assert_eq!((replays(&ay), checks(&clean)), (1, 1));
            assert!(
                elapsed >= std::time::Duration::from_millis(1_100),
                "the check ran to completion past the 500 ms solve budget ({elapsed:?})"
            );
            assert!(entries(&store).is_empty(), "no negative entry");
            // The verifier's own route: every covered row credited, the
            // report reusable, every row exported (the session memo now
            // holds the checked proof, so AY and Clean do not run again).
            let rows = verify_once(&source, &machine);
            assert_eq!((rows.0, rows.1, rows.2, rows.3), (bound, 0, true, bound));
        })
    });
}

/// The census route itself: the resident solve runs out of a budget it used,
/// the one fresh replay after it (OD-197) answers `unsat` at once, and the
/// check of its proof outlasts the 500 ms solve budget. Credited, and
/// nothing is remembered. On main this was `u64::leading_zeros`' outcome:
/// both deadlines "used" (the resident solve's, and the check's under the
/// solve budget), so a `timeout` entry was recorded and answered the
/// census's fallback pass ("negative memo (AY not run): AY TIMEOUT").
#[test]
fn a_resident_timeout_then_a_slow_check_is_credited_and_records_nothing() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = switchable_checker(dir.path());
    let (source, machine) = pair(Shape::Add);
    set_mode(&ay, "rspin", true);
    set_mode(&ay, "prove", true);
    set_mode(&clean, "slow", true);
    with_resident_memo_replay(&ay, &clean, &store, || {
        budgets("500", None, || {
            let (verdict, reusable, why) = explained(&source, &machine);
            assert_eq!((residents(&ay), replays(&ay), checks(&clean)), (1, 1, 1));
            assert!(
                matches!(verdict, Some(VerificationResult::Valid)) && reusable && why.is_none(),
                "{verdict:?} reusable={reusable} {why:?}"
            );
            assert!(entries(&store).is_empty(), "no negative entry");
        })
    });
}

/// A check that never ends runs out of the CHECKER's deadline (here 700 ms,
/// past the 500 ms solve budget), having used it. The outcome is labelled a
/// Clean check timeout, never "AY TIMEOUT"; it is remembered as a
/// `checker-timeout` (never a solver `timeout`) with the checker's CPU time,
/// and answers the next identical replay without AY or Clean. Under a
/// longer checker deadline (the default) the entry does not answer: the
/// key names the checker deadline, so the replay solves and checks again,
/// and here certifies. On main the outcome was "AY TIMEOUT" and the entry a
/// `timeout`, under a key a longer checker deadline could not escape.
#[test]
fn a_checker_timeout_is_labelled_and_remembered_as_one_under_its_deadline() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = switchable_checker(dir.path());
    let (source, machine) = pair(Shape::Add);
    set_mode(&ay, "prove", true);
    set_mode(&clean, "spin", true);
    with_memo_replay(&ay, &clean, &store, || {
        budgets("500", Some("700"), || {
            let (verdict, reusable, why) = explained(&source, &machine);
            assert!(
                verdict.is_none() && !reusable,
                "no credit: {verdict:?} {why:?}"
            );
            assert_eq!((replays(&ay), checks(&clean)), (1, 1));
            let why = why.expect("an explanation");
            assert!(
                why.starts_with(&format!(
                    "Clean check timeout: {}",
                    crate::ay_bridge::CLEAN_CHECK_TIMEOUT
                )) && why.contains("checker's own 700 ms deadline"),
                "{why}"
            );
            assert!(!why.contains("AY TIMEOUT"), "{why}");
            assert_eq!(outcomes(&store), ["checker-timeout"]);
            assert!(
                entry_field(&store, "cpu-ms") >= 630,
                "recorded with the checker's CPU time under its deadline"
            );
            let (verdict, _, again) = explained(&source, &machine);
            assert!(verdict.is_none(), "{verdict:?}");
            assert_eq!(
                (replays(&ay), checks(&clean)),
                (1, 1),
                "the remembered checker timeout answers without AY or Clean"
            );
            assert_eq!(
                again.as_deref(),
                Some(format!("negative memo (AY not run): {why}").as_str())
            );
        });
        // The default checker deadline (180 s): another key. The check now
        // ends (1.2 s) and certifies; the 700 ms entry is left as it was.
        set_mode(&clean, "spin", false);
        set_mode(&clean, "slow", true);
        budgets("500", None, || {
            let (verdict, reusable, _) = explained(&source, &machine);
            assert_eq!(
                (replays(&ay), checks(&clean)),
                (2, 2),
                "an entry recorded under a shorter checker deadline does not answer"
            );
            assert!(
                matches!(verdict, Some(VerificationResult::Valid)) && reusable,
                "{verdict:?} reusable={reusable}"
            );
            assert_eq!(outcomes(&store), ["checker-timeout"]);
        });
    });
}

/// A checker REFUSAL of the exact proof is never credited, however long the
/// checker takes to give it (1.2 s here, past the 500 ms solve budget): the
/// rows stay unverified, nothing is reusable or exported, and the outcome is
/// labelled a Clean check refusal (a SOUNDNESS-class outcome in
/// `proof_gate`), never "AY TIMEOUT" and never an AY answer. A remembered
/// outcome, if any, is the refusal's. On main the refusal was never reached:
/// the check was killed at 500 ms and the outcome read "AY TIMEOUT".
#[test]
fn a_checker_refusal_is_never_credited() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = switchable_checker(dir.path());
    let (source, machine) = pair(Shape::Add);
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    set_mode(&ay, "prove", true);
    set_mode(&clean, "slow", true);
    set_mode(&clean, "reject", true);
    with_memo_replay(&ay, &clean, &store, || {
        budgets("500", None, || {
            let (verdict, reusable, why) = explained(&source, &machine);
            assert!(
                verdict.is_none() && !reusable,
                "a refusal credits nothing: {verdict:?} {why:?}"
            );
            assert_eq!((replays(&ay), checks(&clean)), (1, 1));
            let why = why.expect("an explanation");
            assert!(
                why.starts_with("Clean check refused: AY reported UNSAT but")
                    && why.contains(crate::ay_bridge::WORKING_CHECKER_REJECTED_THIS_PROOF),
                "{why}"
            );
            assert!(!why.contains("AY TIMEOUT"), "{why}");
            assert!(
                outcomes(&store)
                    .iter()
                    .all(|kind| kind == "checker-rejected"),
                "{:?}",
                outcomes(&store)
            );
            memo::forget_process_tier_for_test();
            let rows = verify_once(&source, &machine);
            assert_eq!(
                (rows.0, rows.1, rows.2, rows.3),
                (0, bound, false, 0),
                "no row credited, reusable or exported"
            );
        })
    });
}

/// The certificate store's re-check is a Clean check too: in a fresh
/// process, a stored proof whose re-check takes longer than the solve budget
/// (1.2 s against 500 ms) is credited from the store without running AY,
/// although AY would now answer that it cannot certify the query. On main
/// the re-check was killed at 500 ms, the store fell through to a live AY
/// replay, and nothing was credited (the census's 30 s re-check of the
/// stored `u64::leading_zeros` proof, 41-43 s of CPU, every occurrence).
#[test]
fn a_stored_proof_whose_recheck_outlasts_the_solve_budget_is_credited_from_the_store() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = switchable_checker(dir.path());
    let (source, machine) = pair(Shape::Add);
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    set_mode(&ay, "prove", true);
    with_memo_replay(&ay, &clean, &store, || {
        budgets("500", None, || {
            let certified = verify_once(&source, &machine);
            assert_eq!((replays(&ay), checks(&clean)), (1, 1));
            assert_eq!(certified.0, bound, "certified, and the proof persisted");
            memo::forget_process_tier_for_test();
            crate::ay_bridge::forget_session_memos_for_test();
            crate::obligation_cert_store::forget_consume_memo_for_test();
            set_mode(&ay, "prove", false);
            set_mode(&clean, "slow", true);
            let later = verify_once(&source, &machine);
            assert_eq!(
                (replays(&ay), checks(&clean)),
                (1, 2),
                "the store's re-check answers; AY does not run"
            );
            assert_eq!(
                later, certified,
                "the stored proof credits every covered row"
            );
        })
    });
}

/// The claim replays (OD-197) take the same check: an obligation whose whole
/// replay AY does not certify, every claim of which certifies alone with a
/// check that outlasts the 500 ms solve budget (1 s each), is credited claim
/// by claim, and every export carries the claim record. On main every
/// claim's check was killed at 500 ms and nothing was credited.
#[test]
fn claims_whose_checks_outlast_the_solve_budget_are_credited_claim_by_claim() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = switchable_checker(dir.path());
    let (source, machine, units, unit, claims) = a_body_with_a_claim_split();
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    let plan: Vec<&str> = (0..units + claims)
        .map(|n| if n == unit { "uncertified" } else { "prove" })
        .collect();
    std::fs::write(ay.with_extension("plan"), plan.join("\n") + "\n").unwrap();
    set_mode(&clean, "lag", true);
    with_memo_replay(&ay, &clean, &store, || {
        budgets("500", None, || {
            let (credited, reusable, exports) = verify_for_export(&source, &machine);
            assert_eq!(replays(&ay), units + claims);
            assert_eq!(
                checks(&clean),
                units - 1 + claims,
                "every proof was checked"
            );
            assert_eq!((credited, reusable), (bound, true));
            assert_eq!(exports.len(), bound);
            for export in &exports {
                let record = export.x86_body_claims().expect("the claim record");
                assert_eq!(record.claims_of(unit).map(<[_]>::len), Some(claims));
            }
        })
    });
}

/// The label of each checker outcome is the checker's, and "AY TIMEOUT" is
/// left to AY's own deadlines. The labels never change a verdict.
#[test]
fn replay_labels_name_the_checker_for_checker_outcomes() {
    use crate::ay_bridge::{AYResult, replay_outcome_label};
    let expiry = crate::subprocess::DeadlineExpiry {
        limit: std::time::Duration::from_millis(180_000),
        cpu: Some(std::time::Duration::from_millis(179_000)),
    };
    let timeout = crate::ay_bridge::clean_check_timeout_reason(11_534_336, 180_000, &expiry);
    let refused = crate::ay_bridge::working_checker_rejection_reason(std::path::Path::new("/c"));
    for (result, label) in [
        (AYResult::Timeout, "AY TIMEOUT".to_owned()),
        (
            AYResult::Unknown(timeout.clone()),
            format!("Clean check timeout: {timeout}"),
        ),
        (
            AYResult::Unknown(refused.clone()),
            format!("Clean check refused: {refused}"),
        ),
        (
            AYResult::Unknown(format!("{}: io", crate::ay_bridge::CLEAN_CHECK_INCOMPLETE)),
            format!(
                "Clean check did not complete: {}: io",
                crate::ay_bridge::CLEAN_CHECK_INCOMPLETE
            ),
        ),
        (
            AYResult::Unknown(crate::ay_bridge::CLEAN_PROBE_TIMEOUT_REASON.to_owned()),
            format!(
                "Clean checker unavailable: {}",
                crate::ay_bridge::CLEAN_PROBE_TIMEOUT_REASON
            ),
        ),
        (
            AYResult::Unknown(memo::SELF_CHECK_REJECTED.to_owned()),
            format!("AY UNKNOWN: {}", memo::SELF_CHECK_REJECTED),
        ),
    ] {
        assert_eq!(replay_outcome_label(&result), label);
    }
    assert!(timeout.contains("11534336-byte proof") && timeout.contains("179000 ms"));
    // A checker timeout is PENDING, as a solver timeout is; a refusal is a
    // proof authority's verdict (SOUNDNESS). Neither is ever credit.
    assert_eq!(
        crate::proof_gate::failure_class_of(&AYResult::Unknown(timeout)).map(|class| class.label()),
        Some("PENDING(solver-capacity)")
    );
    assert_eq!(
        crate::proof_gate::failure_class_of(&AYResult::Unknown(refused)).map(|class| class.label()),
        Some("SOUNDNESS")
    );
}

/// The checker deadline itself: 180 s by default, never less than the solve
/// budget, never unbounded (a solve budget of zero, "no deadline", still
/// gives the check its own), and an override only within (0, 1 h].
#[test]
fn the_checker_deadline_is_its_own_bounded_and_never_shorter_than_the_solve() {
    use crate::obligation_cert_store::{
        PROOF_CHECK_DEADLINE_CAP_MS, PROOF_CHECK_DEADLINE_MS, PROOF_CHECK_TIMEOUT_ENV,
        proof_check_timeout_ms,
    };
    assert_eq!(PROOF_CHECK_DEADLINE_MS, 180_000);
    trust_cg_process_env::with_env_edits(|env| {
        env.remove(PROOF_CHECK_TIMEOUT_ENV);
        assert_eq!(proof_check_timeout_ms(30_000), 180_000);
        assert_eq!(proof_check_timeout_ms(500), 180_000);
        assert_eq!(proof_check_timeout_ms(0), 180_000, "never unbounded");
        assert_eq!(proof_check_timeout_ms(300_000), 300_000, "never shorter");
    });
    for (value, solve, expected) in [
        ("700", 500, 700),
        ("700", 30_000, 30_000),
        ("3600000", 0, PROOF_CHECK_DEADLINE_CAP_MS),
        ("3600001", 0, PROOF_CHECK_DEADLINE_MS),
        ("0", 500, PROOF_CHECK_DEADLINE_MS),
        ("-5", 500, PROOF_CHECK_DEADLINE_MS),
        ("soon", 500, PROOF_CHECK_DEADLINE_MS),
    ] {
        trust_cg_process_env::with_env_edits(|env| {
            env.set(PROOF_CHECK_TIMEOUT_ENV, value);
            assert_eq!(
                proof_check_timeout_ms(solve),
                expected,
                "{value} after {solve}"
            );
        });
    }
}

/// The process's children's CPU time (user + system) so far: every AY and
/// Clean process this test waited for, with the workers they reaped.
fn children_cpu() -> std::time::Duration {
    // SAFETY: `getrusage` writes only the zeroed struct it is handed.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    let status = unsafe { libc::getrusage(libc::RUSAGE_CHILDREN, &mut usage) };
    assert_eq!(status, 0, "getrusage");
    let micros = |time: libc::timeval| {
        u64::try_from(time.tv_sec).unwrap() * 1_000_000 + u64::try_from(time.tv_usec).unwrap()
    };
    std::time::Duration::from_micros(micros(usage.ru_utime) + micros(usage.ru_stime))
}

/// A probe, not a check, and a no-op unless `TCG_OD223_PROBE_QUERY` names a
/// dumped x86-64 body query (`-Ztrust-ir-cg-args=x86-body-dump=<dir>`, the
/// replayed bytes): it replays those exact bytes through the verifier's
/// exact-query funnel on the admitted qualification pair
/// ([`replay_environment`]) under the default deadlines (the 30 s solve
/// budget, the checker's own 180 s), three ways, and prints each outcome
/// with its wall-clock and children's CPU time (`TCG_SOLVE_TRACE=1` adds
/// the solve and check lines): the one-shot route into a fresh certificate
/// store; the census route (the resident solve, then the one-shot replay of
/// its candidate), no store; and a fresh process's re-check of the proof the
/// first route stored. It asserts that each certifies. Run alone, one test
/// per process, at normal load. Measured for `u64::leading_zeros`
/// (census s23final): `reports/perf/2026-11-02-x86-body-checker-deadline/`.
#[test]
fn od223_probe_replays_a_dumped_body_query_through_the_funnel() {
    let Some(query) = std::env::var_os("TCG_OD223_PROBE_QUERY") else {
        eprintln!("OD223_PROBE skipped: TCG_OD223_PROBE_QUERY is unset");
        return;
    };
    let test = "od223_probe_replays_a_dumped_body_query_through_the_funnel";
    let smt2 = std::fs::read_to_string(&query).unwrap();
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let obligation = ProofObligation {
        name: X86_BODY_OBLIGATION_NAME.into(),
        trust_ir_expr: crate::smt::SmtExpr::var("probe_source", 64),
        aarch64_expr: crate::smt::SmtExpr::var("probe_machine", 64),
        inputs: Vec::new(),
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: None,
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::Reconstructed {
            from_opcode: "od223_probe_dumped_query".into(),
            arity: 0,
        },
    };
    let store = tempfile::tempdir().unwrap();
    let config = crate::verdict_db::live_source_bound_config();
    let route = |label: &str, edit: &dyn Fn(&mut trust_cg_process_env::EnvEditor<'_>)| {
        crate::ay_bridge::forget_session_memos_for_test();
        crate::obligation_cert_store::forget_consume_memo_for_test();
        let (cpu, started) = (children_cpu(), std::time::Instant::now());
        let verdict = with_edits(&edits, || {
            trust_cg_process_env::with_env_edits(|env| {
                env.remove(crate::obligation_cert_store::PROOF_CHECK_TIMEOUT_ENV);
                env.remove("TCG_RECON_SOLVER_MS");
                edit(env);
                crate::ay_bridge::verify_respelled_query(&obligation, &config, &smt2)
            })
        });
        eprintln!(
            "OD223_PROBE route={label} result={} source={:?} wall_s={:.3} children_cpu_s={:.3} \
             solve_budget_ms={} check_deadline_ms={} query_bytes={} load1={:.2}",
            crate::ay_bridge::replay_outcome_label(&verdict.result),
            verdict.source,
            started.elapsed().as_secs_f64(),
            (children_cpu() - cpu).as_secs_f64(),
            config.timeout_ms,
            crate::obligation_cert_store::proof_check_timeout_ms(config.timeout_ms),
            smt2.len(),
            {
                let mut load = [0f64; 3];
                // SAFETY: `getloadavg` writes at most the three it is given.
                unsafe { libc::getloadavg(load.as_mut_ptr(), 3) };
                load[0]
            },
        );
        verdict.result
    };
    let one_shot = route("one-shot", &|env| {
        env.remove("TCG_NO_CERT_STORE");
        env.set("TCG_PROOF_CERT_STORE", store.path());
    });
    let resident = route("resident", &|env| {
        env.remove("TCG_NO_SOLVER_SERVER");
        env.remove("TRUST_CG_RUN_FORMAL_PROOF_TESTS");
    });
    let stored = route("store-recheck", &|env| {
        env.remove("TCG_NO_CERT_STORE");
        env.set("TCG_PROOF_CERT_STORE", store.path());
    });
    assert_eq!(
        (one_shot, resident, stored),
        (AYResult::Verified, AYResult::Verified, AYResult::Verified)
    );
}
