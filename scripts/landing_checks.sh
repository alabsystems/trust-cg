#!/bin/bash
# scripts/landing_checks.sh — the single-entry measurement gate battery for a landing
# session (BENCH-5). Run this before pushing a landing that could affect compile time,
# runtime, or corpus coverage.
#
#   1. compile-time canary (scripts/compile_time_canary.sh, BENCH-4): hard-threshold
#      warm certs-on compile + exit-code differential on a pinned program.
#   2. perf ratchet (scripts/check_perf_ratchet.py, BENCH-5): validates the newest
#      benchmarks/beat-llvm/results/*.json — rejects gate-off/stampless rows, red on
#      MISMATCH or a regression beyond the noise floor vs the best committed ledger row,
#      whether or not that results file is headline evidence.
#      No results JSON is MISSING EVIDENCE (exit 3), never a pass; produce one with
#        python3 benchmarks/beat-llvm/run.py [--cold]
#      --require-current-perf also requires that JSON to be current-source eligible
#      evidence (measured at HEAD from a tree without tracked edits, still no tracked
#      edits, eligibility recomputed); a stale or ineligible file is missing current
#      evidence (exit 3) even when the ratchet itself is green.
#   3. determinism sentinel (scripts/compile_determinism_sentinel.sh, BENCH-8):
#      N=5 pinned compiles; red iff compile VERDICTS differ. Runs by DEFAULT so a
#      landing session gets the full gate set from one entry; --no-sentinel skips it,
#      and that skip is MISSING EVIDENCE (exit 3). (--sentinel is a no-op alias.)
#   4. predecessor soundness attestation (scripts/soundness_attestation.py): the
#      landing base (TCG_LANDING_BASE, default origin/main) must carry a
#      per-commit attestation that the verifier committed at that base accepts
#      for LANDING (`verify --landing`: a full record, or a portable one while
#      that verifier defers the x86-64-native class, which it prints as NOT
#      ATTESTED; refs/attest/soundness/<base>/*, fetched from origin with plain
#      git when reachable). This is a record check of a landed commit; the
#      base's anchored verification against its own predecessor happened when
#      it landed.
#      The candidate itself is attested by the landing train or the pre-push
#      hook when it lands, so this step checks the commit it lands on. An
#      unattested base is MISSING EVIDENCE (exit 3), a failing or incomplete
#      record RED, a malformed one tooling (exit 2).
#
# Diagnostic opt-ins: --allow-missing-perf (no results JSON) and
# --allow-missing-sentinel (with --no-sentinel) let that missing evidence exit 0
# behind a loud NON-QUALIFYING banner. Such a run is never landing, performance or
# completion evidence. --allow-missing-perf cannot be combined with
# --require-current-perf.
#
# Exit: 0 every gate ran and is green (or missing evidence was explicitly allowed and
#       bannered NON-QUALIFYING); 1 any gate red; 2 tooling/inconclusive or invalid
#       arguments; 3 required evidence missing. When several apply: 1, then 2, then 3.
set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
RUN_SENTINEL=1
ALLOW_MISSING_PERF=0
ALLOW_MISSING_SENTINEL=0
REQUIRE_CURRENT_PERF=0
for a in "$@"; do
  case "$a" in
    --sentinel) RUN_SENTINEL=1 ;;
    --no-sentinel) RUN_SENTINEL=0 ;;
    --allow-missing-perf) ALLOW_MISSING_PERF=1 ;;
    --allow-missing-sentinel) ALLOW_MISSING_SENTINEL=1 ;;
    --require-current-perf) REQUIRE_CURRENT_PERF=1 ;;
    -h|--help) awk 'NR == 1 { next } !/^#/ { exit } { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *)
      echo "landing-checks: unknown arg $a (known: --no-sentinel, --require-current-perf, --allow-missing-perf, --allow-missing-sentinel)" >&2
      exit 2 ;;
  esac
done
if [ "$ALLOW_MISSING_PERF" = 1 ] && [ "$REQUIRE_CURRENT_PERF" = 1 ]; then
  echo "landing-checks: --allow-missing-perf contradicts --require-current-perf" >&2
  exit 2
fi

RED=0
TOOLING=0
MISSING=""
NON_QUALIFYING=""

non_qualifying_banner() {
  echo "!!! landing-checks: NON-QUALIFYING RUN — $1 !!!" >&2
  echo "!!! This exit status is diagnostic only; it is not landing, performance or completion evidence. !!!" >&2
}

echo "==================== landing checks (BENCH-4/5/8 + attestation) ===================="

echo "--- [1/4] compile-time canary ---"
"$SCRIPT_DIR/compile_time_canary.sh"
rc=$?
case $rc in
  0) echo "landing-checks: canary GREEN" ;;
  1) echo "landing-checks: canary RED (compile-time regression or MISMATCH — P0)" >&2; RED=1 ;;
  2) echo "landing-checks: canary INCONCLUSIVE (missing tooling or machine load; see diagnostic above)" >&2; TOOLING=1 ;;
  *) echo "landing-checks: canary CONFIG/TOOLING error (rc=$rc)" >&2; TOOLING=1 ;;
esac

echo "--- [2/4] perf ratchet vs committed ledger ---"
if ls "$REPO"/benchmarks/beat-llvm/results/*.json >/dev/null 2>&1; then
  if [ "$REQUIRE_CURRENT_PERF" = 1 ]; then
    python3 "$SCRIPT_DIR/check_perf_ratchet.py" --require-current
  else
    python3 "$SCRIPT_DIR/check_perf_ratchet.py"
  fi
  rc=$?
  case $rc in
    0) echo "landing-checks: perf ratchet GREEN" ;;
    1) echo "landing-checks: perf ratchet RED (regression/MISMATCH/rejected row)" >&2; RED=1 ;;
    3)
      echo "landing-checks: perf ratchet MISSING CURRENT EVIDENCE — the newest results JSON is not current-source eligible evidence" >&2
      MISSING="${MISSING} perf-current" ;;
    2) echo "landing-checks: perf ratchet INCONCLUSIVE or TOOLING (rc=2): results not comparable like-with-like (a --progs subset or below the contract N), or unreadable — rerun the full corpus" >&2; TOOLING=1 ;;
    *) echo "landing-checks: perf ratchet TOOLING error (rc=$rc)" >&2; TOOLING=1 ;;
  esac
elif [ "$ALLOW_MISSING_PERF" = 1 ]; then
  echo "landing-checks: perf ratchet NOT RUN — no results JSON (--allow-missing-perf)"
  non_qualifying_banner "perf ratchet not evaluated: no benchmarks/beat-llvm/results/*.json (--allow-missing-perf)"
  NON_QUALIFYING="${NON_QUALIFYING} perf"
else
  echo "landing-checks: perf ratchet MISSING EVIDENCE — no results JSON; produce one with:" >&2
  echo "  python3 benchmarks/beat-llvm/run.py" >&2
  MISSING="${MISSING} perf"
fi

echo "--- [3/4] determinism sentinel ---"
if [ "$RUN_SENTINEL" = 1 ]; then
  "$SCRIPT_DIR/compile_determinism_sentinel.sh"
  rc=$?
  case $rc in
    0) echo "landing-checks: sentinel GREEN (deterministic verdicts)" ;;
    1) echo "landing-checks: sentinel RED — NONDET-FAILCLOSED verdict flap detected" >&2; RED=1 ;;
    2) echo "landing-checks: sentinel DETERMINISTIC-FAILCLOSED — pinned program regressed" >&2; RED=1 ;;
    *) echo "landing-checks: sentinel CONFIG/TOOLING (rc=$rc)" >&2; TOOLING=1 ;;
  esac
elif [ "$ALLOW_MISSING_SENTINEL" = 1 ]; then
  echo "landing-checks: sentinel NOT RUN (--no-sentinel --allow-missing-sentinel)"
  non_qualifying_banner "determinism sentinel not run (--no-sentinel --allow-missing-sentinel)"
  NON_QUALIFYING="${NON_QUALIFYING} sentinel"
else
  echo "landing-checks: sentinel MISSING EVIDENCE — skipped by --no-sentinel (add --allow-missing-sentinel only for a NON-QUALIFYING diagnostic run)" >&2
  MISSING="${MISSING} sentinel"
fi

echo "--- [4/4] predecessor soundness attestation ---"
BASE="${TCG_LANDING_BASE:-origin/main}"
# The base's own committed verifier checks the base's records, run directly
# (python3 -I) from the base's tree; the candidate's attestation verifier never
# runs. The separate transport gives no verdict. This checks an already-landed commit: the
# base's anchored verification against ITS predecessor happened when it landed
# (the train and the pre-push hook).
if base_sha="$(git -C "$REPO" rev-parse --verify --quiet "${BASE}^{commit}")"; then
  # Best effort: the records may already be local, and a landing run can be offline.
  python3 -I "$REPO/scripts/github_transport.py" --repo "$REPO" --remote origin \
    records --subject "$base_sha" >/dev/null 2>&1 || true
  verifier_dir="$(mktemp -d "${TMPDIR:-/tmp}/landing-checks-verifier.XXXXXX")"
  mkdir "$verifier_dir/scripts"
  if git -C "$REPO" show "${base_sha}:scripts/soundness_attestation.py" \
       >"$verifier_dir/scripts/soundness_attestation.py" 2>/dev/null; then
    git -C "$REPO" show "${base_sha}:scripts/matrix_results.py" >"$verifier_dir/scripts/matrix_results.py" \
      2>/dev/null || rm -f "$verifier_dir/scripts/matrix_results.py"
    python3 -I "$verifier_dir/scripts/soundness_attestation.py" verify "$base_sha" --repo "$REPO" --landing
    rc=$?
  else
    echo "landing-checks: $BASE ($base_sha) carries no scripts/soundness_attestation.py" >&2
    rc=2
  fi
  rm -rf "$verifier_dir"
else
  echo "landing-checks: cannot resolve the landing base $BASE" >&2
  rc=2
fi
case $rc in
  0) echo "landing-checks: predecessor attestation GREEN for landing ($BASE)" ;;
  1) echo "landing-checks: predecessor attestation RED — $BASE's records are failing or incomplete" >&2; RED=1 ;;
  3)
    echo "landing-checks: predecessor attestation MISSING EVIDENCE — $BASE carries no refs/attest/soundness record" >&2
    MISSING="${MISSING} attestation" ;;
  *) echo "landing-checks: predecessor attestation TOOLING/INCONCLUSIVE (rc=$rc)" >&2; TOOLING=1 ;;
esac

echo "======================================================================="
if [ -n "$NON_QUALIFYING" ]; then
  non_qualifying_banner "explicitly allowed missing evidence:${NON_QUALIFYING}"
fi
if [ "$RED" = 1 ]; then
  echo "landing-checks: RED — do not land; find the regression (never loosen a threshold in-run)" >&2
  exit 1
fi
if [ "$TOOLING" = 1 ]; then
  echo "landing-checks: INCONCLUSIVE — resolve the reported tooling/load condition before rerunning" >&2
  exit 2
fi
if [ -n "$MISSING" ]; then
  echo "landing-checks: MISSING REQUIRED EVIDENCE:${MISSING} — not a landing result; produce the evidence (an --allow-missing-* run is NON-QUALIFYING)" >&2
  exit 3
fi
if [ -n "$NON_QUALIFYING" ]; then
  echo "landing-checks: gates that ran are GREEN — NON-QUALIFYING (missing:${NON_QUALIFYING})"
  exit 0
fi
echo "landing-checks: ALL GREEN"
exit 0
