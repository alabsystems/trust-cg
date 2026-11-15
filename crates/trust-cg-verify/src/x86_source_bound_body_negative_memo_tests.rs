// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The source-bound negative memo on the real x86-64 body replay path
//! (request capture, `live_source_bound_replay_explained`, the exact-query
//! funnel), driven by a fixture AY that counts its replays and a fixture
//! Clean. No proof content: the fixture proof is transport only, so these
//! controls are about which replays run and what they may credit.

use super::*;
use crate::source_bound_negative_memo as memo;

/// A fixture AY that answers the replay as the toolchain AY answers the
/// bodies it cannot certify (`unknown` / `(:reason-unknown (incomplete
/// self-check-rejected))`), or, while `<ay>.prove` exists, `unsat` with a
/// proof file; while `<ay>.sat` exists it answers the verdict query `sat` and
/// outlasts the budget on the SAT model query; `<ay>.reason` replaces the
/// published `(:reason-unknown …)`. Every verdict replay appends `replay` to
/// `<ay>.calls` (a model query appends `model`). `<ay>.sleep` makes a verdict
/// replay outlast its budget WAITING (a starved solve: next to no CPU time);
/// `<ay>.spin` makes it outlast its budget COMPUTING, in eight processes of
/// its process group so that it uses its budget in CPU time even on a host
/// loaded several times over (the measurement covers the group, as AY's
/// solving worker is a forked member of it). A self-check rejection follows
/// a short solve that computes the same way, so it holds the processor and
/// the memo may record it; `<ay>.nap` makes that solve wait instead (a
/// starved rejection, which the memo must not record). Started as the
/// resident server (`--incremental`), it appends `resident` to `<ay>.calls`
/// and, while `<ay>.rspin` exists, never answers, computing in eight
/// processes of its group as `<ay>.spin` does (a resident deadline that used
/// its budget); without it the server exits, a framing anomaly. While
/// `<ay>.plan` exists, verdict replay `n` (counting from 1) answers `unsat`
/// with a proof when line `n` of it is `prove`, `sat` when it is `sat` (its
/// model query then outlasts the budget, so it is no refutation) or `refute`
/// (its model query answers `sat` at once: a counterexample), a starved
/// self-check rejection when it is `nap`, and otherwise as without it.
///
/// The fixture's private copy is started once when the fixture is made. Every
/// replay runs that copy (`ay_private_copy`: a per-process root for fixture
/// bytes), a new executable file, and a host that assesses a new executable at
/// its first start (`ay_private_copy::HOST_ASSESSES_FIRST_START`, macOS)
/// otherwise charges the assessment, with next to no CPU time, to the copy's
/// first replay. Production makes that start outside any deadline
/// (`ay_identity::first_start`), but never for a fixture without an AY build,
/// whose side files count exactly the starts its test makes. Without this
/// start the memo correctly refused to record a starved solve, and "another
/// AY" replayed twice (measured: 0.205 s for the first replay of the second
/// fixture, 0.023 s for later ones). Started without `-smt2`, the script exits
/// 91 before it counts anything.
#[cfg(unix)]
fn switchable_ay(dir: &std::path::Path, name: &str) -> std::path::PathBuf {
    let ay = switchable_ay_script(dir, name);
    let pinned = crate::ay_identity::test_fixtures::pin(&ay);
    let started = std::process::Command::new(pinned.exec_path())
        .status()
        .unwrap();
    assert_eq!(started.code(), Some(91), "fixture AY copy's first start");
    assert_eq!(replays(&ay), 0);
    ay
}

#[cfg(unix)]
fn switchable_ay_script(dir: &std::path::Path, name: &str) -> std::path::PathBuf {
    fixture_script(
        dir,
        name,
        r#"if test "$1" = --incremental; then
  printf 'resident\n' >> "$0.calls"
  if test -f "$0.rspin"; then
    for spinner in 1 2 3 4 5 6 7 8; do (while :; do :; done) & done
    wait
  fi
  exit 0
fi
test "$1" = -smt2 || exit 91
if test "$#" = 2; then
  printf 'model\n' >> "$0.calls"
  if test -f "$0.plan"; then
    n=$(grep -c '^replay$' "$0.calls")
    if test "$(sed -n "${n}p" "$0.plan")" = refute; then printf 'sat\n'; exit 0; fi
  fi
  sleep 3
  exit 0
fi
test "$3" = --strict-proofs || exit 92
printf 'replay\n' >> "$0.calls"
if test -f "$0.keep"; then cp "$2" "$0.query.$(grep -c '^replay$' "$0.calls")"; fi
if test -f "$0.sleep"; then sleep 3; fi
if test -f "$0.spin"; then
  for spinner in 1 2 3 4 5 6 7 8; do (while :; do :; done) & done
  wait
fi
if test -f "$0.sat"; then printf 'sat\n'; exit 0; fi
if test -f "$0.plan"; then
  n=$(grep -c '^replay$' "$0.calls")
  step=$(sed -n "${n}p" "$0.plan")
  if test "$step" = prove; then
    printf 'fixture proof (transport only)\n' > "$5"
    printf 'unsat\n'
    exit 0
  fi
  if test "$step" = sat || test "$step" = refute; then printf 'sat\n'; exit 0; fi
  if test "$step" = nap; then
    sleep 1
    printf 'unknown\n(:reason-unknown (incomplete self-check-rejected))\n'
    exit 0
  fi
fi
if test -f "$0.prove"; then
  printf 'fixture proof (transport only)\n' > "$5"
  printf 'unsat\n'
  exit 0
fi
if test -f "$0.reason"; then printf 'unknown\n'; cat "$0.reason"; exit 0; fi
if test -f "$0.nap"; then sleep 1; else
  for spinner in 1 2 3 4 5 6 7 8; do
    (i=0; while [ $i -lt 4000 ]; do i=$((i+1)); done) &
  done
  wait
fi
printf 'unknown\n(:reason-unknown (incomplete self-check-rejected))\n'"#,
    )
}

/// Verdict replays run so far (SAT model queries not counted).
fn replays(ay: &std::path::Path) -> usize {
    std::fs::read_to_string(ay.with_extension("calls")).map_or(0, |text| {
        text.lines().filter(|line| *line == "replay").count()
    })
}

/// Resident servers started so far.
fn residents(ay: &std::path::Path) -> usize {
    std::fs::read_to_string(ay.with_extension("calls")).map_or(0, |text| {
        text.lines().filter(|line| *line == "resident").count()
    })
}

fn set_mode(ay: &std::path::Path, mode: &str, on: bool) {
    let flag = ay.with_extension(mode);
    if on {
        std::fs::write(flag, "").unwrap();
    } else {
        let _ = std::fs::remove_file(flag);
    }
}

/// The negative memo's per-box entries under `store`.
fn entries(store: &std::path::Path) -> Vec<std::path::PathBuf> {
    let Ok(dir) = std::fs::read_dir(store.join(memo::STORE_NAMESPACE)) else {
        return Vec::new();
    };
    let mut paths: Vec<_> = dir
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "negmemo"))
        .collect();
    paths.sort();
    paths
}

/// A numeric field of the single entry under `store`.
fn entry_field(store: &std::path::Path, field: &str) -> u64 {
    let [entry] = entries(store).try_into().expect("exactly one entry");
    let text = std::fs::read_to_string(entry).unwrap();
    text.lines()
        .find_map(|line| line.strip_prefix(&format!("{field}:")))
        .and_then(|value| value.parse().ok())
        .unwrap_or_else(|| panic!("no {field} in {text}"))
}

/// Run `f` with `solver` as the admitted AY, `checker` as the explicit
/// Clean, the proof caches ON with `store` as the per-box store (so the memo
/// is live), the resident route off and live replay on. The fixture pair's
/// own build record ([`fixture_pair_record`]) pins `checker`, so an overlay
/// build, whose record pins the overlay's real Clean, runs these controls
/// as an ordinary build does.
#[cfg(unix)]
fn with_memo_replay<T>(
    solver: &std::path::Path,
    checker: &std::path::Path,
    store: &std::path::Path,
    f: impl FnOnce() -> T,
) -> T {
    let declaration = crate::ay_identity::test_fixtures::declare(&[solver]);
    let record = fixture_pair_record(solver, checker);
    trust_cg_process_env::with_env_edits(|env| {
        env.set("AY_SOLVER_PATH", solver);
        env.set(
            crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
            &declaration,
        );
        env.set("TCG_EXTERNAL_CLEAN_CHECKER", checker);
        env.set("TCG_NO_SOLVER_SERVER", "1");
        env.set("TCG_PROOF_CERT_STORE", store);
        env.remove("TCG_NO_CERT_STORE");
        env.remove("TCG_NO_PROOF_CACHE");
        env.remove("TCG_SOURCE_BOUND_NO_NEGATIVE_MEMO");
        env.set("TCG_CANARY_NO_CACHE", "1");
        env.set("TCG_NO_VERDICT_DB", "1");
        env.set("TCG_REFINE_SOLVER", "1");
        env.set("TCG_RECON_SOLVER_MS", "5000");
        crate::ay_identity::test_fixtures::with_recorded(record, f)
    })
}

/// [`with_memo_replay`] with the resident route ON, as a census replays (the
/// resident solve first), and a 500 ms budget per route.
#[cfg(unix)]
fn with_resident_memo_replay<T>(
    solver: &std::path::Path,
    checker: &std::path::Path,
    store: &std::path::Path,
    f: impl FnOnce() -> T,
) -> T {
    with_memo_replay(solver, checker, store, || {
        trust_cg_process_env::with_env_edits(|env| {
            env.remove("TCG_NO_SOLVER_SERVER");
            // The strict proof campaign deliberately disables the resident
            // server — it needs AY's complete one-shot transcript, which the
            // server discards (`ay_bridge::strict_formal_campaign_active`) —
            // and `scripts/soundness_check.sh` exports
            // `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1` for every row it runs. These
            // controls are ABOUT the resident route, so they take the campaign
            // out of scope for their own thread (the override is thread-local
            // and restores on unwind). Without this the gate ran them with the
            // resident route silently off: `ay_server_enabled` does not read
            // the campaign flag, so the assertion below passed while
            // `residents()` stayed 0.
            env.remove("TRUST_CG_RUN_FORMAL_PROOF_TESTS");
            env.set("TCG_RECON_SOLVER_MS", "500");
            assert!(
                crate::ay_bridge::ay_server_enabled()
                    && !crate::ay_bridge::strict_formal_campaign_active(),
                "these controls need the resident route"
            );
            f()
        })
    })
}

/// One verification of `(source, machine)` under a freshly captured request:
/// (credited covered rows, covered rows left needing a replay, whether the
/// report is reusable for its request, the export count, the row results).
fn verify_once(
    source: &trust_cg_lower::Function,
    machine: &X86ISelFunction,
) -> (usize, usize, bool, usize, Vec<String>) {
    let owner = source_bound_x86_body(source, machine, SYSV).unwrap();
    let verifier = promotion_verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let (report, exports) =
        verifier.verify_with_request_for_export(machine, Some(source), SYSV, &request);
    (
        covered_rows_matching(&owner, report.report(), is_body_credit),
        covered_rows_matching(&owner, report.report(), is_needs_replay),
        report.reusable_for(&request),
        exports.len(),
        results(report.report()),
    )
}

fn serial() -> (
    std::sync::MutexGuard<'static, ()>,
    std::sync::MutexGuard<'static, ()>,
) {
    (
        crate::ay_bridge::formal_solver_test_lock(),
        memo::test_lock(),
    )
}

/// A self-check rejection from a starved solve is the host's, not the
/// query's (AY's certification has its own wall-clock bound): it is not
/// remembered, so the next occurrence solves again; the same rejection from
/// a solve that held the processor is remembered and answers the next one.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn a_starved_uncertified_replay_is_solved_again() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    set_mode(&ay, "nap", true);
    with_memo_replay(&ay, &clean, &store, || {
        let first = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 1);
        assert!(
            entries(&store).is_empty(),
            "a starved rejection is not recorded"
        );
        let second = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2, "the next occurrence solves again");
        assert_eq!(second, first);
        assert!(entries(&store).is_empty());
        assert_eq!((first.0, first.3), (0, 0), "no credit, no export");
        set_mode(&ay, "nap", false);
        verify_once(&source, &machine);
        assert_eq!(replays(&ay), 3);
        assert_eq!(entries(&store).len(), 1, "a held rejection is recorded");
        assert_eq!(verify_once(&source, &machine), first);
        assert_eq!(replays(&ay), 3, "and answers the next occurrence");
    });
}

/// The measured defect: a body theorem AY does not certify was solved again
/// at every occurrence (on `main` before the memo this test's second verify
/// ran AY a second time). Now the second identical request, and a fresh
/// process reading the per-box entry, run no AY, and the memo hit changes no
/// row: the rows stay unverified, nothing is credited, exported or reusable.
#[cfg(unix)]
#[test]
fn a_second_identical_uncertified_replay_does_not_run_ay() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    with_memo_replay(&ay, &clean, &store, || {
        let first = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 1);
        assert_eq!((first.0, first.1, first.2, first.3), (0, bound, false, 0));
        assert_eq!(
            entries(&store).len(),
            1,
            "the non-certified replay is recorded"
        );
        assert_eq!(entry_field(&store, "confirmations"), 1);

        let second = verify_once(&source, &machine);
        assert_eq!(
            replays(&ay),
            1,
            "the identical second request must not run AY"
        );
        assert_eq!(second, first, "a memo hit changes no row, credit or export");

        // A new process: only the per-box entry remains. Its first
        // occurrence counts one reuse; its later occurrences are free.
        memo::forget_process_tier_for_test();
        let third = verify_once(&source, &machine);
        let fourth = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 1, "the per-box entry answers a fresh process");
        assert_eq!((third, fourth), (first.clone(), first));
        assert_eq!(entry_field(&store, "reuses"), 1);
    });
}

/// The retry policy on the real path: once a first entry's reuse budget of
/// later processes is spent, the next process solves again, and the failed
/// re-solve refreshes the entry (reuses reset, a second confirmation, a
/// doubled budget).
#[cfg(unix)]
#[test]
fn the_reuse_budget_is_followed_by_one_refreshing_resolve() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Sub);
    let budget = memo::RetryPolicy::DEFAULT.reuse_budget(1) as usize;
    let process = || {
        memo::forget_process_tier_for_test();
        verify_once(&source, &machine);
        verify_once(&source, &machine);
    };
    with_memo_replay(&ay, &clean, &store, || {
        verify_once(&source, &machine);
        for _ in 0..budget {
            process();
        }
        assert_eq!(replays(&ay), 1, "{budget} later processes reuse the entry");
        assert_eq!(entry_field(&store, "reuses"), budget as u64);
        process();
        assert_eq!(replays(&ay), 2, "the spent entry is re-solved once");
        assert_eq!(entry_field(&store, "reuses"), 0);
        assert_eq!(entry_field(&store, "confirmations"), 2);
        process();
        assert_eq!(replays(&ay), 2, "the refreshed entry answers again");
        assert_eq!(entry_field(&store, "reuses"), 1);
    });
}

/// The tracked bypass (`source-bound-no-negative-memo`, here its standalone
/// variable): every occurrence runs AY, and the memo is neither read nor
/// written, even while an entry exists.
#[cfg(unix)]
#[test]
fn the_bypass_knob_solves_every_occurrence_and_touches_no_entry() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    let bypassed = |f: &dyn Fn()| {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_SOURCE_BOUND_NO_NEGATIVE_MEMO", "1");
            f()
        })
    };
    with_memo_replay(&ay, &clean, &store, || {
        bypassed(&|| {
            verify_once(&source, &machine);
            verify_once(&source, &machine);
        });
        assert_eq!(replays(&ay), 2);
        assert!(entries(&store).is_empty(), "the bypass writes nothing");
        verify_once(&source, &machine);
        verify_once(&source, &machine);
        assert_eq!(replays(&ay), 3, "without the bypass: one replay, one hit");
        let recorded = std::fs::read(&entries(&store)[0]).unwrap();
        bypassed(&|| {
            verify_once(&source, &machine);
        });
        assert_eq!(replays(&ay), 4, "the bypass ignores an existing entry");
        assert_eq!(
            std::fs::read(&entries(&store)[0]).unwrap(),
            recorded,
            "and leaves it as it was"
        );
    });
}

/// Every key input misses on its own: the solve budget, the checker bytes,
/// the AY bytes, the query (another body) and the verifier child
/// environment. Each changed configuration is then a key of its own.
#[cfg(unix)]
#[test]
fn any_key_component_change_misses() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let other_ay = switchable_ay(dir.path(), "ay-other");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let other_clean = fixture_script(
        dir.path(),
        "clean-other",
        &format!("{FIXTURE_CHECKER_ACCEPTS}\n# other checker bytes"),
    );
    let (source, machine) = pair(Shape::Add);
    let (sub, sub_machine) = pair(Shape::Sub);
    let twice = |source: &trust_cg_lower::Function, machine: &X86ISelFunction| {
        verify_once(source, machine);
        verify_once(source, machine);
    };
    with_memo_replay(&ay, &clean, &store, || twice(&source, &machine));
    assert_eq!(replays(&ay), 1);
    with_memo_replay(&ay, &clean, &store, || {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_RECON_SOLVER_MS", "5001");
            twice(&source, &machine);
        })
    });
    assert_eq!(replays(&ay), 2, "another solve budget");
    with_memo_replay(&ay, &other_clean, &store, || twice(&source, &machine));
    assert_eq!(replays(&ay), 3, "another checker");
    with_memo_replay(&ay, &clean, &store, || {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("GOVERN_AY_MB", "64");
            twice(&source, &machine);
        })
    });
    assert_eq!(replays(&ay), 4, "another verifier child environment");
    with_memo_replay(&ay, &clean, &store, || twice(&sub, &sub_machine));
    assert_eq!(replays(&ay), 5, "another query");
    with_memo_replay(&other_ay, &clean, &store, || twice(&source, &machine));
    assert_eq!((replays(&ay), replays(&other_ay)), (5, 1), "another AY");
    assert_eq!(entries(&store).len(), 6, "one entry per configuration");
    // The original configuration still reuses its entry.
    with_memo_replay(&ay, &clean, &store, || verify_once(&source, &machine));
    assert_eq!(replays(&ay), 5);
}

/// Positive credit is untouched. A certified replay credits every covered row
/// with a reusable report and deletes the negative entry; while a positive
/// tier holds the proof, even a (restored) negative entry is never consulted
/// before it. The one cost is explicit: while an entry is honoured, a retry
/// that WOULD have certified is not run (the nondeterminism the retry
/// policy bounds).
#[cfg(unix)]
#[test]
fn a_certified_replay_is_unaffected_and_deletes_the_entry() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    with_memo_replay(&ay, &clean, &store, || {
        verify_once(&source, &machine);
        assert_eq!(replays(&ay), 1);
        let recorded = std::fs::read(&entries(&store)[0]).unwrap();

        // Honoured: the retry that would now certify is withheld.
        set_mode(&ay, "prove", true);
        let withheld = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 1);
        assert_eq!((withheld.0, withheld.2), (0, false));

        // Budget spent (as after its reuse budget of later processes): the
        // re-solve certifies, credits every covered row with a reusable
        // report, and deletes the entry.
        let entry = entries(&store).remove(0);
        let spent = String::from_utf8(recorded.clone()).unwrap().replacen(
            "reuses:0",
            &format!("reuses:{}", memo::RetryPolicy::DEFAULT.reuse_budget(1)),
            1,
        );
        std::fs::write(&entry, spent).unwrap();
        memo::forget_process_tier_for_test();
        let certified = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2);
        assert_eq!((certified.0, certified.1, certified.2), (bound, 0, true));
        assert_eq!(certified.3, bound, "every credited row is exported");
        assert!(
            entries(&store).is_empty(),
            "a Verified replay deletes the entry"
        );

        // A negative entry restored beside the positive proof is never
        // consulted first: the positive tiers answer, AY does not run.
        set_mode(&ay, "prove", false);
        std::fs::write(&entry, &recorded).unwrap();
        memo::forget_process_tier_for_test();
        let again = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2);
        assert_eq!(again, certified);
    });
}

/// In a FRESH process (no in-process `Verified` memo, no replay memo of the
/// stored certificate), the proof the certified replay persisted to the
/// per-box Alethe store still wins over a negative entry for the same key:
/// the store is consulted first and credits every covered row without
/// running AY. Moving the negative lookup ahead of the per-box store fails
/// here (the process memo alone hid that ordering before).
#[cfg(unix)]
#[test]
fn a_stored_proof_wins_over_a_negative_entry_in_a_fresh_process() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    let fresh_process = || {
        memo::forget_process_tier_for_test();
        crate::ay_bridge::forget_session_memos_for_test();
        crate::obligation_cert_store::forget_consume_memo_for_test();
    };
    with_memo_replay(&ay, &clean, &store, || {
        verify_once(&source, &machine);
        let entry = entries(&store).remove(0);
        let recorded = std::fs::read(&entry).unwrap();
        // A certified replay (as after the retry budget) persists its proof.
        std::fs::remove_file(&entry).unwrap();
        fresh_process();
        set_mode(&ay, "prove", true);
        let certified = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2);
        assert_eq!(certified.0, bound);
        let stored_proofs = std::fs::read_dir(&store)
            .unwrap()
            .filter(|entry| {
                entry
                    .as_ref()
                    .unwrap()
                    .path()
                    .extension()
                    .is_some_and(|ext| ext == "alethecert")
            })
            .count();
        assert_eq!(stored_proofs, 1, "the certified replay persisted its proof");
        // A later process on this box: the negative entry is back (a stale
        // one another process wrote), AY would now answer unknown, and
        // nothing is in memory.
        set_mode(&ay, "prove", false);
        std::fs::write(&entry, &recorded).unwrap();
        fresh_process();
        let later = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2, "the stored proof answers; AY does not run");
        assert_eq!(
            later, certified,
            "the stored proof credits every covered row"
        );
    });
}

/// A replay that used its budget computing and ran out of it is remembered
/// as a `Timeout`, with the CPU time its solver's process group used, and
/// replayed as one without running AY.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn a_timed_out_replay_that_used_its_budget_is_remembered_as_a_timeout() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    set_mode(&ay, "spin", true);
    with_memo_replay(&ay, &clean, &store, || {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_RECON_SOLVER_MS", "500");
            let first = verify_once(&source, &machine);
            assert_eq!(replays(&ay), 1);
            let text = std::fs::read_to_string(&entries(&store)[0]).unwrap();
            assert!(text.contains("outcome:timeout\n"), "{text}");
            assert!(entry_field(&store, "cpu-ms") >= 450, "{text}");
            let started = std::time::Instant::now();
            let second = verify_once(&source, &machine);
            assert_eq!(replays(&ay), 1);
            assert_eq!(second, first);
            assert!(started.elapsed() < std::time::Duration::from_millis(2_500));
        })
    });
}

/// The measured defect (2026-09-30): under host load 40-80 the replays of
/// bodies that certify at rest ran out of their wall-clock budget waiting for
/// a processor, each such `Timeout` was recorded, and later processes were
/// answered "timeout" without solving, so proof-required builds and the proof
/// tests failed on every busy machine. A replay that ran out of its budget
/// without using it (here: waiting, next to no CPU time) is the host's, not
/// the query's: nothing is recorded, every occurrence solves again, and an
/// existing entry for the key (an earlier budget-exhausting timeout whose
/// reuse budget is spent) is left exactly as it is.
#[cfg(unix)]
#[test]
fn a_timed_out_replay_that_was_starved_is_solved_again() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    set_mode(&ay, "sleep", true);
    with_memo_replay(&ay, &clean, &store, || {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_RECON_SOLVER_MS", "500");
            let first = verify_once(&source, &machine);
            assert_eq!(replays(&ay), 1);
            assert!(
                entries(&store).is_empty(),
                "a starved timeout is not recorded"
            );
            let second = verify_once(&source, &machine);
            assert_eq!(replays(&ay), 2, "the next occurrence solves again");
            assert_eq!(second, first);
            assert!(entries(&store).is_empty());
            assert_eq!((first.0, first.3), (0, 0), "no credit, no export");
        })
    });
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    with_memo_replay(&ay, &clean, &store, || {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_RECON_SOLVER_MS", "500");
            // An earlier budget-exhausting timeout was recorded for the key.
            set_mode(&ay, "sleep", false);
            set_mode(&ay, "spin", true);
            verify_once(&source, &machine);
            assert_eq!(replays(&ay), 3);
            set_mode(&ay, "spin", false);
            set_mode(&ay, "sleep", true);
            // Spend its reuse budget, so a later process solves again.
            memo::forget_process_tier_for_test();
            let entry = entries(&store).remove(0);
            let spent = std::fs::read_to_string(&entry).unwrap().replacen(
                "reuses:0",
                &format!("reuses:{}", memo::RetryPolicy::DEFAULT.reuse_budget(1)),
                1,
            );
            std::fs::write(&entry, &spent).unwrap();
            for expected in [4, 5] {
                verify_once(&source, &machine);
                assert_eq!(replays(&ay), expected, "solved again");
                assert_eq!(
                    std::fs::read_to_string(&entry).unwrap(),
                    spent,
                    "the starved re-solve neither refreshes nor deletes the entry"
                );
            }
        })
    });
}

/// Only measured-stable outcomes are remembered. AY's host-state answers
/// (`memout`, `resourceout`, `interrupted`, `internal_error`, a split
/// limit) and a bare `unknown` are solved again at every occurrence; before,
/// every `(:reason-unknown …)` was recorded and replayed.
#[cfg(unix)]
#[test]
fn a_host_state_unknown_is_solved_again() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    with_memo_replay(&ay, &clean, &store, || {
        let mut expected = 0;
        for reason in [
            "(:reason-unknown memout)",
            "(:reason-unknown resourceout)",
            "(:reason-unknown interrupted)",
            "(:reason-unknown internal_error)",
            "(:reason-unknown (incomplete split_limit))",
            "",
        ] {
            std::fs::write(ay.with_extension("reason"), format!("{reason}\n")).unwrap();
            verify_once(&source, &machine);
            verify_once(&source, &machine);
            expected += 2;
            assert_eq!(replays(&ay), expected, "{reason:?} is solved every time");
            assert!(entries(&store).is_empty(), "{reason:?} is not recorded");
        }
    });
}

/// A long-lived process (the JIT verifies through the same replay path)
/// retries: an entry answers at most the process hit budget in one process,
/// then the next occurrence solves again and refreshes it. Before, an entry
/// held by a process answered every occurrence for 24 hours.
#[cfg(unix)]
#[test]
fn a_long_lived_process_retries_after_its_hit_budget() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    let budget = memo::RetryPolicy::DEFAULT.process_hits as usize;
    memo::forget_process_tier_for_test();
    with_memo_replay(&ay, &clean, &store, || {
        verify_once(&source, &machine);
        for _ in 0..budget {
            verify_once(&source, &machine);
        }
        assert_eq!(replays(&ay), 1, "{budget} hits in this process");
        verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2, "the process budget is spent: solved again");
        assert_eq!(entry_field(&store, "confirmations"), 2);
        verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2, "the refreshed entry answers again");
    });
}

/// AY answered SAT on the verdict query and only the model query ran out of
/// its budget: the replay ends `Timeout`, but that is not a property of an
/// uncertified query, so nothing is recorded, the next occurrence solves
/// again, and an existing entry for the key (an earlier timeout) is
/// deleted, so no hit can stand in for the known SAT. Before, the memo
/// recorded `timeout` for this SAT query and replayed it.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn an_outcome_after_a_sat_verdict_is_never_remembered() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    with_memo_replay(&ay, &clean, &store, || {
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_RECON_SOLVER_MS", "500");
            // An earlier verdict-query timeout was recorded for the key.
            set_mode(&ay, "spin", true);
            verify_once(&source, &machine);
            set_mode(&ay, "spin", false);
            assert_eq!(entries(&store).len(), 1);
            // Spend its reuse budget, so the next process solves again (as
            // after that budget in later processes).
            memo::forget_process_tier_for_test();
            let entry = entries(&store).remove(0);
            let spent = std::fs::read_to_string(&entry).unwrap().replacen(
                "reuses:0",
                &format!("reuses:{}", memo::RetryPolicy::DEFAULT.reuse_budget(1)),
                1,
            );
            std::fs::write(&entry, spent).unwrap();
            // Now AY answers SAT and the model query times out.
            set_mode(&ay, "sat", true);
            let first = verify_once(&source, &machine);
            assert_eq!(replays(&ay), 2);
            assert!(
                entries(&store).is_empty(),
                "the SAT replay deletes the entry and records nothing"
            );
            assert_eq!((first.0, first.3), (0, 0), "no credit, no export");
            verify_once(&source, &machine);
            assert_eq!(replays(&ay), 3, "the next occurrence solves again");
            assert!(entries(&store).is_empty());
        })
    });
}

/// Slice 19 (OD-197), the census route: the resident solve of an x86-64 body
/// query runs out of a budget it used, and the one fresh replay that follows
/// it certifies. Every covered row is credited with a reusable report and the
/// memo records nothing. Before (memo v4, no fresh replay), the resident
/// deadline ended the replay uncredited and was recorded as a `Timeout`,
/// which then answered every later replay of those bytes on both routes.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn a_resident_timeout_the_fresh_replay_certifies_credits_and_records_nothing() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    set_mode(&ay, "rspin", true);
    set_mode(&ay, "prove", true);
    with_resident_memo_replay(&ay, &clean, &store, || {
        let first = verify_once(&source, &machine);
        assert_eq!(residents(&ay), 1, "the resident route ran first");
        assert_eq!(replays(&ay), 1, "one fresh replay followed its deadline");
        assert_eq!(
            (first.0, first.1, first.2, first.3),
            (bound, 0, true, bound),
            "the fresh replay's checked proof credits every covered row"
        );
        assert!(
            entries(&store).is_empty(),
            "a credited replay leaves no negative entry"
        );
    });
}

/// Slice 19 (OD-197): both routes run out of a budget they used (the
/// resident solve and the fresh replay after it), so the replay's `Timeout`
/// is the query's and is recorded, with the CPU time of the larger expiry;
/// the next occurrence runs no AY on either route.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn a_timeout_on_both_routes_is_remembered_and_answers_without_ay() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    set_mode(&ay, "rspin", true);
    set_mode(&ay, "spin", true);
    with_resident_memo_replay(&ay, &clean, &store, || {
        let first = verify_once(&source, &machine);
        assert_eq!((residents(&ay), replays(&ay)), (1, 1), "both routes ran");
        assert_eq!((first.0, first.3), (0, 0), "no credit, no export");
        let text = std::fs::read_to_string(&entries(&store)[0]).unwrap();
        assert!(text.contains("outcome:timeout\n"), "{text}");
        assert!(entry_field(&store, "cpu-ms") >= 450, "{text}");
        let second = verify_once(&source, &machine);
        assert_eq!(
            (residents(&ay), replays(&ay)),
            (1, 1),
            "the recorded timeout answers without AY on either route"
        );
        assert_eq!(second, first);
    });
}

/// Slice 19 (OD-197): the resident solve runs out of a budget it used, but
/// the fresh replay after it runs out of its own budget WAITING (starved).
/// The replay's final route did not exhaust its budget, so nothing is
/// recorded and the next occurrence solves again on both routes; a memo that
/// recorded the resident deadline alone answered it.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn a_resident_timeout_whose_fresh_replay_was_starved_is_solved_again() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = pair(Shape::Add);
    set_mode(&ay, "rspin", true);
    set_mode(&ay, "sleep", true);
    with_resident_memo_replay(&ay, &clean, &store, || {
        let first = verify_once(&source, &machine);
        assert_eq!((residents(&ay), replays(&ay)), (1, 1), "both routes ran");
        assert!(
            entries(&store).is_empty(),
            "a starved final route is not recorded"
        );
        let second = verify_once(&source, &machine);
        assert_eq!(
            (residents(&ay), replays(&ay)),
            (2, 2),
            "the next occurrence solves again on both routes"
        );
        assert_eq!(second, first);
        assert_eq!((first.0, first.3), (0, 0), "no credit, no export");
    });
}

/// A body fixture in parts (slice 16) one of whose replayed obligations has
/// a claim split: the pair, the obligation's index and its claim count.
fn a_body_with_a_claim_split() -> (
    trust_cg_lower::Function,
    X86ISelFunction,
    usize,
    usize,
    usize,
) {
    for shape in super::slice16::SLICE_SIXTEEN {
        let (source, machine) = super::slice16::slice16_pair(shape);
        let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) else {
            continue;
        };
        let units = owner.replayed_units().len();
        let split = (0..units).find_map(|k| owner.replay_claims(k).ok().map(|c| (k, c.len())));
        if let Some((unit, claims)) = split {
            return (source, machine, units, unit, claims);
        }
    }
    panic!("no slice-16 fixture has a claim split");
}

/// One verification as [`verify_once`], with the exports themselves.
fn verify_for_export(
    source: &trust_cg_lower::Function,
    machine: &X86ISelFunction,
) -> (usize, bool, Vec<crate::SourceBoundArithmeticObligation>) {
    let owner = source_bound_x86_body(source, machine, SYSV).unwrap();
    let verifier = promotion_verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let (report, exports) =
        verifier.verify_with_request_for_export(machine, Some(source), SYSV, &request);
    (
        covered_rows_matching(&owner, report.report(), is_body_credit),
        report.reusable_for(&request),
        exports,
    )
}

/// Slice 19 (OD-197) on the real replay path: a replayed obligation whose
/// whole replay AY does not certify, every claim of which certifies alone,
/// is credited claim by claim: every covered row is credited with a
/// reusable report, and every export carries the claim record, which checks
/// and publishes the claims in the obligation's place. Before, the body was
/// not credited.
#[cfg(unix)]
#[test]
fn an_obligation_every_claim_of_which_certifies_is_credited_claim_by_claim() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine, units, unit, claims) = a_body_with_a_claim_split();
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    // The parts before `unit` certify whole, `unit`'s whole replay does not,
    // its claims and every later part certify.
    let plan: Vec<&str> = (0..units + claims)
        .map(|n| if n == unit { "uncertified" } else { "prove" })
        .collect();
    std::fs::write(ay.with_extension("plan"), plan.join("\n") + "\n").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let (credited, reusable, exports) = verify_for_export(&source, &machine);
        assert_eq!(
            replays(&ay),
            units + claims,
            "every claim of obligation {unit} replayed"
        );
        assert_eq!((credited, reusable), (bound, true));
        assert_eq!(exports.len(), bound, "every credited row is exported");
        for export in &exports {
            let record = export.x86_body_claims().expect("the claim record");
            assert_eq!(record.claims_of(unit).map(<[_]>::len), Some(claims));
            assert!(export.check_x86_body_claims().is_ok());
            let published = export.replayed_obligations().expect("the record checks");
            assert_eq!(published.len(), units - 1 + claims);
        }
    });
}

/// The control: one claim of that obligation does not certify, so the
/// obligation keeps its whole replay's outcome; the claim replay stops at
/// that claim, nothing is credited and nothing exported.
#[cfg(unix)]
#[test]
fn an_obligation_one_claim_of_which_does_not_certify_is_not_credited() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine, units, unit, claims) = a_body_with_a_claim_split();
    // The second claim of `unit` (replay unit + 3) does not certify.
    let plan: Vec<&str> = (0..units + claims)
        .map(|n| {
            if n == unit || n == unit + 2 {
                "uncertified"
            } else {
                "prove"
            }
        })
        .collect();
    std::fs::write(ay.with_extension("plan"), plan.join("\n") + "\n").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let (credited, reusable, exports) = verify_for_export(&source, &machine);
        assert_eq!(replays(&ay), unit + 3, "the claim replay stops at claim 2");
        assert_eq!((credited, reusable, exports.len()), (0, false, 0));
    });
}

// ---------------------------------------------------------------------------
// Slice 23 (OD-206): the generalization over arithmetic leaves on the real
// replay path
// ---------------------------------------------------------------------------

/// A slice-23 body with a generalization, no claim split and no paired row
/// (its theorem is its own arbiter): its pair and its generalization.
fn a_body_with_a_generalization() -> (trust_cg_lower::Function, X86ISelFunction, ProofObligation) {
    use super::slice23::{SLICE_TWENTY_THREE, slice23_pair};
    for shape in SLICE_TWENTY_THREE {
        let (source, machine) = slice23_pair(shape);
        let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) else {
            continue;
        };
        if owner.is_stated_in_parts() || owner.replay_claims(0).is_ok() || owner.is_paired() {
            continue;
        }
        if let Ok(general) = owner.replay_generalized(0) {
            let general = general.obligation().clone();
            return (source, machine, general);
        }
    }
    panic!("no slice-23 fixture has a generalization and no claim split");
}

/// Slice 23 (OD-206) on the real replay path: the exact replay does not
/// certify, its generalization does, so every covered row is credited with
/// a reusable report; every export carries the record of the generalization,
/// which every consumer re-derives (`check_x86_body_claims`) and publishes
/// in the theorem's place. Before, the body was not credited.
#[cfg(unix)]
#[test]
fn an_exact_replay_without_a_verdict_whose_generalization_certifies_is_credited() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine, general) = a_body_with_a_generalization();
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    std::fs::write(ay.with_extension("plan"), "uncertified\nprove\n").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let (credited, reusable, exports) = verify_for_export(&source, &machine);
        assert_eq!(replays(&ay), 2, "the exact replay, then its generalization");
        assert_eq!((credited, reusable), (bound, true));
        assert_eq!(exports.len(), bound, "every credited row is exported");
        for export in &exports {
            let record = export.x86_body_claims().expect("the generalization record");
            assert_eq!(
                record
                    .generalized_of(0)
                    .and_then(|unit| unit.whole_generalization()),
                Some(&general)
            );
            assert!(export.check_x86_body_claims().is_ok());
            assert!(export.check_x86_body_generalized().is_ok());
            let published = export.replayed_obligations().expect("the record checks");
            assert_eq!(published, vec![&general], "the generalization is published");
        }
    });
}

/// Slice 23 (OD-206, OD-200's rule): the generalization's negation is
/// satisfiable (AY returns a counterexample of it), which is no refutation:
/// nothing is credited and no row fails; the exact outcome stands.
#[cfg(unix)]
#[test]
fn a_satisfiable_generalization_credits_nothing_and_refutes_nothing() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine, _) = a_body_with_a_generalization();
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    std::fs::write(ay.with_extension("plan"), "uncertified\nrefute\n").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let (credited, needs_replay, reusable, exported, results) = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2, "the exact replay, then its generalization");
        assert_eq!(
            (credited, needs_replay, reusable, exported),
            (0, bound, false, 0),
            "{results:?}"
        );
        assert!(
            results.iter().all(|result| !result.contains("Failed")),
            "a generalization never fails a row: {results:?}"
        );
    });
}

/// Slice 23 (OD-206): an exact replay that refutes the theorem is never
/// generalized: one replay, every covered row failed by the exact
/// counterexample.
#[cfg(unix)]
#[test]
fn an_exact_refutation_is_never_generalized() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine, _) = a_body_with_a_generalization();
    std::fs::write(ay.with_extension("plan"), "refute\nprove\n").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let (credited, _, _, exported, results) = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 1, "no generalization after a refutation");
        assert_eq!((credited, exported), (0, 0));
        assert!(
            results.iter().any(|result| result.contains("Failed")),
            "the exact counterexample fails the rows: {results:?}"
        );
    });
}

/// Slice 23 (OD-206): a negative-memo hit on the exact obligation does not
/// stop its generalization. The first occurrence records the exact replay's
/// self-check rejection (a solve that held the processor) and its
/// generalization's starved rejection is not recorded; at the next
/// occurrence the memo answers the exact query without AY and the
/// generalization runs, and certifies.
#[cfg(unix)]
#[test]
fn a_memo_hit_on_the_exact_obligation_still_runs_its_generalization() {
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine, _) = a_body_with_a_generalization();
    let bound = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap()
        .bound_rows()
        .len();
    std::fs::write(ay.with_extension("plan"), "uncertified\nnap\nprove\n").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let first = verify_once(&source, &machine);
        assert_eq!(replays(&ay), 2, "the exact replay, then its generalization");
        assert_eq!((first.0, first.3), (0, 0), "no credit, no export");
        assert_eq!(
            entries(&store).len(),
            1,
            "only the exact rejection is recorded"
        );
        let second = verify_once(&source, &machine);
        assert_eq!(
            replays(&ay),
            3,
            "the memo answers the exact query; the generalization still runs"
        );
        assert_eq!((second.0, second.2, second.3), (bound, true, bound));
    });
}

/// Slice 23 (OD-205) on the real replay path: a correct lowering whose
/// paired theorem is refuted (the selector's signed remainder divides by 1
/// where the source divides by -1, so the divisor claim fails) is decided by
/// the theorem without the pairing: it certifies, every covered row is
/// credited, and every export carries that theorem, never the refuted one.
#[cfg(unix)]
#[test]
fn a_refuted_paired_theorem_whose_unpaired_theorem_certifies_is_credited() {
    use super::slice23::{Shape23, slice23_pair};
    use crate::x86_source_bound_body::X86Theorem;
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = slice23_pair(Shape23::SremPaired);
    // An idiv row is paired only in tests (its divisor claim fails at -1).
    use crate::x86_source_bound_body::with_signed_division_pairing as pairing;
    let owner = pairing(|| source_bound_x86_body(&source, &machine, SYSV).unwrap());
    assert!(owner.has_unpaired() && !owner.is_stated_in_parts());
    let (bound, unpaired) = (
        owner.bound_rows().len(),
        owner.statement_of(X86Theorem::Unpaired).unwrap(),
    );
    std::fs::write(ay.with_extension("plan"), "refute\nprove\n").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let (credited, reusable, exports) = pairing(|| verify_for_export(&source, &machine));
        assert_eq!(
            replays(&ay),
            2,
            "the paired theorem, then the one without the pairing"
        );
        assert_eq!((credited, reusable), (bound, true));
        assert_eq!(exports.len(), bound);
        for export in &exports {
            assert_eq!(export.obligation(), unpaired.as_ref());
            assert_eq!(
                export.replayed_obligations().unwrap(),
                vec![unpaired.as_ref()]
            );
        }
    });
}

/// The queries the fixture AY received for its strict replays, in order
/// (kept when `<ay>.keep` exists).
fn received_queries(ay: &std::path::Path) -> Vec<String> {
    (1..=replays(ay))
        .map(|n| {
            std::fs::read_to_string(ay.with_extension(format!("query.{n}")))
                .unwrap_or_else(|error| panic!("replayed query {n}: {error}"))
        })
        .collect()
}

/// A query's asserted lines: what a replay states, whatever its header.
fn asserted(query: &str) -> Vec<&str> {
    query
        .lines()
        .filter(|line| line.starts_with("(assert"))
        .collect()
}

/// Slice 23 (OD-205) in parts, on the real replay path: a paired theorem
/// stated in parts whose part stating the failing operand claim is refuted
/// is decided by the theorem without the pairing, in ITS parts (each its own
/// split, replayed serially): every one certifies, every covered row is
/// credited, every export carries that theorem and its parts, and the
/// queries AY received after the refuted part are exactly those parts. The
/// mutant `unpaired-units-are-paired` (the unpaired route replays the paired
/// parts) replays the refuted part's text again.
#[cfg(unix)]
#[test]
fn a_refuted_paired_theorem_in_parts_is_decided_by_the_unpaired_theorem_in_parts() {
    use super::slice23::{holds_on_samples, refuted_on_samples, srem_in_parts_pair, text};
    use crate::x86_source_bound_body::X86Theorem;
    use crate::x86_source_bound_body::with_signed_division_pairing as pairing;
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = srem_in_parts_pair();
    let owner = pairing(|| source_bound_x86_body(&source, &machine, SYSV).unwrap());
    assert!(owner.is_stated_in_parts() && owner.is_paired() && owner.has_unpaired());
    let paired: Vec<ProofObligation> = owner
        .replayed_units_of(X86Theorem::Paired)
        .into_iter()
        .cloned()
        .collect();
    let unpaired: Vec<ProofObligation> = owner
        .replayed_units_of(X86Theorem::Unpaired)
        .into_iter()
        .cloned()
        .collect();
    let refuted = paired
        .iter()
        .position(refuted_on_samples)
        .expect("a paired part states the failing divisor claim");
    assert!(unpaired.iter().all(holds_on_samples));
    let (bound, statement) = (
        owner.bound_rows().len(),
        owner.statement_of(X86Theorem::Unpaired).unwrap(),
    );
    // The paired parts before the refuted one certify, it is refuted, then
    // every part of the theorem without the pairing certifies (a part
    // byte-identical to a paired part already certified is answered without
    // AY).
    let replayed_before: Vec<String> = paired[..refuted].iter().map(text).collect();
    let fresh: Vec<&ProofObligation> = unpaired
        .iter()
        .filter(|part| !replayed_before.contains(&text(part)))
        .collect();
    let plan = format!(
        "{}refute\n{}",
        "prove\n".repeat(refuted),
        "prove\n".repeat(fresh.len())
    );
    std::fs::write(ay.with_extension("plan"), plan).unwrap();
    std::fs::write(ay.with_extension("keep"), "").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let (credited, reusable, exports) = pairing(|| verify_for_export(&source, &machine));
        assert_eq!(replays(&ay), refuted + 1 + fresh.len());
        let received = received_queries(&ay);
        assert_eq!(
            asserted(&received[refuted]),
            asserted(&text(&paired[refuted])),
            "the refuted replay is the paired part"
        );
        for (k, part) in fresh.iter().enumerate() {
            assert_eq!(
                asserted(&received[refuted + 1 + k]),
                asserted(&text(part)),
                "replay {} after the refutation is the theorem without the pairing's",
                k + 1
            );
        }
        assert_eq!((credited, reusable), (bound, true));
        assert_eq!(exports.len(), bound);
        let parts: Vec<&ProofObligation> = unpaired.iter().collect();
        for export in &exports {
            assert_eq!(export.obligation(), statement.as_ref());
            assert_eq!(export.replayed_obligations().unwrap(), parts);
        }
    });
}

/// Slice 23 (OD-205) on the real replay path: the verifier replays a paired
/// theorem only once its pairing record re-derives it. `ShrClPaired` (a
/// correct lowering whose shift pairs): the paired theorem is the one query
/// AY receives and certifies, and every export carries it with its record,
/// which publishes. `udiv/high-half-divisor-minus-one` paired on its stamp
/// alone (`with_stamp_only_pairing`, check (3) skipped): its record fails the
/// re-derived check (3), so its paired theorem, which would hold, is never
/// replayed; the theorem without the pairing is the one query AY receives,
/// and its refutation fails the rows. The mutant `pairing-not-rederived`
/// replays the paired theorem.
#[cfg(unix)]
#[test]
fn a_paired_theorem_is_replayed_only_once_its_record_re_derives_it() {
    use super::slice23::{Shape23, slice_twenty_three_refutations, slice23_pair, text};
    use crate::x86_source_bound_body::{X86Theorem, with_stamp_only_pairing};
    let _serial = serial();
    {
        let dir = tempfile::tempdir().unwrap();
        let store = dir.path().join("store");
        let ay = switchable_ay(dir.path(), "ay");
        let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
        let (source, machine) = slice23_pair(Shape23::ShrClPaired);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert!(owner.is_paired() && !owner.is_stated_in_parts());
        let bound = owner.bound_rows().len();
        std::fs::write(ay.with_extension("plan"), "prove\n").unwrap();
        std::fs::write(ay.with_extension("keep"), "").unwrap();
        with_memo_replay(&ay, &clean, &store, || {
            let (credited, reusable, exports) = verify_for_export(&source, &machine);
            assert_eq!(replays(&ay), 1);
            assert_eq!(
                asserted(&received_queries(&ay)[0]),
                asserted(&text(owner.obligation())),
                "the replayed query is the paired theorem"
            );
            assert_eq!((credited, reusable), (bound, true));
            assert_eq!(exports.len(), bound);
            for export in &exports {
                assert_eq!(export.obligation(), owner.obligation());
                assert!(export.is_x86_body_paired() && export.x86_body_pairing().is_some());
                assert_eq!(
                    export.replayed_obligations().unwrap(),
                    vec![owner.obligation()]
                );
            }
        });
    }
    {
        let dir = tempfile::tempdir().unwrap();
        let store = dir.path().join("store");
        let ay = switchable_ay(dir.path(), "ay");
        let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
        let (_, source, machine) = slice_twenty_three_refutations()
            .into_iter()
            .find(|(label, ..)| *label == "udiv/high-half-divisor-minus-one")
            .expect("the control");
        let owner =
            with_stamp_only_pairing(|| source_bound_x86_body(&source, &machine, SYSV)).unwrap();
        assert!(owner.is_paired() && owner.check_pairing().is_err());
        let unpaired = owner.statement_of(X86Theorem::Unpaired).unwrap();
        std::fs::write(ay.with_extension("plan"), "refute\n").unwrap();
        std::fs::write(ay.with_extension("keep"), "").unwrap();
        with_memo_replay(&ay, &clean, &store, || {
            let (credited, _, exports) =
                with_stamp_only_pairing(|| verify_for_export(&source, &machine));
            assert_eq!(replays(&ay), 1, "only the theorem without the pairing");
            assert_eq!(
                asserted(&received_queries(&ay)[0]),
                asserted(&text(&unpaired)),
                "the replayed query is the theorem without the pairing"
            );
            assert_eq!((credited, exports.len()), (0, 0));
        });
    }
}

/// The control: a wrong lowering of a paired row is refuted by the theorem
/// without the pairing too, so the refutation stands (the counterexample is
/// the exact theorem's) and every covered row fails.
#[cfg(unix)]
#[test]
fn a_refutation_the_theorem_without_the_pairing_confirms_stands() {
    use super::slice23::{Shape23, slice23_pair};
    let _serial = serial();
    let dir = tempfile::tempdir().unwrap();
    let store = dir.path().join("store");
    let ay = switchable_ay(dir.path(), "ay");
    let clean = fixture_script(dir.path(), "clean", FIXTURE_CHECKER_ACCEPTS);
    let (source, machine) = slice23_pair(Shape23::SremPaired);
    use crate::x86_source_bound_body::with_signed_division_pairing as pairing;
    std::fs::write(ay.with_extension("plan"), "refute\nrefute\n").unwrap();
    with_memo_replay(&ay, &clean, &store, || {
        let (credited, _, _, exported, results) = pairing(|| verify_once(&source, &machine));
        assert_eq!(
            replays(&ay),
            2,
            "the paired theorem, then the one without the pairing"
        );
        assert_eq!((credited, exported), (0, 0));
        assert!(
            results.iter().any(|result| result.contains("Failed")),
            "{results:?}"
        );
    });
}

/// Ruling OD-223: the Clean check's own deadline and labels, on this path.
#[path = "x86_source_bound_body_checker_deadline_tests.rs"]
mod checker_deadline;
