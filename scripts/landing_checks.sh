#!/bin/bash
# scripts/landing_checks.sh — the single-entry measurement gate battery for a landing
# session (BENCH-5). Run this before pushing a landing that could affect compile time,
# runtime, or corpus coverage.
#
#   1. compile-time canary (scripts/compile_time_canary.sh, BENCH-4): hard-threshold
#      warm certs-on compile + exit-code differential on a pinned program.
#   2. perf ratchet (scripts/check_perf_ratchet.py, BENCH-5): validates the newest
#      benchmarks/beat-llvm/results/*.json — rejects gate-off/stampless rows, red on
#      MISMATCH or a regression beyond the noise floor vs the best committed ledger row.
#      SKIPPED (not red) if no results JSON exists yet — run the harness to produce one:
#        python3 benchmarks/beat-llvm/run.py [--cold]
#   3. determinism sentinel (scripts/compile_determinism_sentinel.sh, BENCH-8):
#      N=5 pinned compiles; red iff compile VERDICTS differ. Runs by DEFAULT so a
#      landing session gets the full gate set from one entry; pass --no-sentinel to
#      skip it (speed) — the skip is LOGGED. (--sentinel is accepted as a no-op alias.)
#   4. soundness-lock drift alarm (scripts/check_lock_drift.sh, BENCH-7): red-worthy
#      if soundness_revs.lock pins are >50 commits behind their repo HEADs.
#      This is hard-fail by default. Set TCG_LOCK_DRIFT_WARN_ONLY=1 only for a
#      clearly labeled local experiment; release and landing runs must not use
#      that override.
#
# Exit: 0 all green (or individually skipped-loudly); 1 any gate red; 2 tooling.
set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
# The determinism sentinel now runs by DEFAULT so `landing_checks.sh` (one entry) is
# the full measurement gate set for a landing session (BENCH-10). Opt out with
# --no-sentinel; --sentinel is accepted as a back-compat no-op (it was opt-in pre-BENCH-10).
RUN_SENTINEL=1
for a in "$@"; do
  case "$a" in
    --sentinel) RUN_SENTINEL=1 ;;
    --no-sentinel) RUN_SENTINEL=0 ;;
    *) echo "landing-checks: unknown arg $a (use --no-sentinel to skip the determinism sentinel)" >&2; exit 2 ;;
  esac
done

RED=0
TOOLING=0

echo "==================== landing checks (BENCH-4/5/7/8) ===================="

echo "--- [1/4] compile-time canary ---"
"$SCRIPT_DIR/compile_time_canary.sh"
rc=$?
case $rc in
  0) echo "landing-checks: canary GREEN" ;;
  1) echo "landing-checks: canary RED (compile-time regression or MISMATCH — P0)" >&2; RED=1 ;;
  2) echo "landing-checks: canary INCONCLUSIVE (loaded machine) — rerun on a quiet machine" >&2; TOOLING=1 ;;
  *) echo "landing-checks: canary CONFIG/TOOLING error (rc=$rc)" >&2; TOOLING=1 ;;
esac

echo "--- [2/4] perf ratchet vs committed ledger ---"
if ls "$REPO"/benchmarks/beat-llvm/results/*.json >/dev/null 2>&1; then
  python3 "$SCRIPT_DIR/check_perf_ratchet.py"
  rc=$?
  case $rc in
    0) echo "landing-checks: perf ratchet GREEN" ;;
    1) echo "landing-checks: perf ratchet RED (regression/MISMATCH/rejected row)" >&2; RED=1 ;;
    *) echo "landing-checks: perf ratchet TOOLING error (rc=$rc)" >&2; TOOLING=1 ;;
  esac
else
  echo "landing-checks: perf ratchet SKIPPED — no results JSON; produce one with:"
  echo "  python3 benchmarks/beat-llvm/run.py"
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
else
  echo "landing-checks: sentinel SKIPPED (--no-sentinel) — determinism gate not run this pass"
fi

echo "--- [4/4] soundness-lock drift alarm (BENCH-7) ---"
"$SCRIPT_DIR/check_lock_drift.sh"
rc=$?
case $rc in
  0) echo "landing-checks: lock drift GREEN" ;;
  1)
    if [ "${TCG_LOCK_DRIFT_WARN_ONLY:-0}" = 1 ]; then
      echo "landing-checks: lock drift EXCEEDED (explicit WARN-ONLY experiment) — re-pin via soundness_check.sh --update." >&2
    else
      echo "landing-checks: lock drift RED — soundness_revs.lock beyond threshold (re-pin via soundness_check.sh --update)" >&2
      RED=1
    fi
    ;;
  *) echo "landing-checks: lock drift TOOLING error (rc=$rc)" >&2; TOOLING=1 ;;
esac

echo "======================================================================="
if [ "$RED" = 1 ]; then
  echo "landing-checks: RED — do not land; find the regression (never loosen a threshold in-run)" >&2
  exit 1
fi
if [ "$TOOLING" = 1 ]; then
  echo "landing-checks: INCONCLUSIVE (tooling/loaded) — rerun on a quiet machine before landing" >&2
  exit 2
fi
echo "landing-checks: ALL GREEN"
exit 0
