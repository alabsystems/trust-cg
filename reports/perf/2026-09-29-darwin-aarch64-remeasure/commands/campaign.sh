#!/bin/bash
# Darwin arm64 (aarch64-apple-darwin) performance campaign for trust-cg.
#
# 2026-09-29 re-measure: this is the 2026-09-28 campaign's script
# (reports/perf/2026-09-28-darwin-aarch64-campaign/commands/campaign.sh). The
# driver, harness modes, flags and step order are the same. Three scheduling
# changes, none of which touches a measured command:
#   * the atpkg launcher directory is on PATH, so the harness scripts that
#     resolve the Trust package through scripts/trust_toolchain.py find it;
#   * before each measured step the script waits (wait_quiet.py) until the
#     1-minute load is below QUIET_MAX1 (default 4.0) and the 5-minute load
#     below QUIET_MAX5 (default 6.0), for at most QUIET_WAIT_MIN minutes
#     (default 120), because this host is shared with other agents' builds;
#     the wait is logged in load.tsv, and on a timeout the step runs anyway and
#     the harness's own quiet check decides eligibility;
#   * STEPS="01 04 ..." runs only the named steps (default: all), so one lane
#     can be repeated without re-running the others (commands/sequence.sh);
#     load-before.txt and load-after.txt collect one snapshot per invocation.
#
# Runs, strictly one after another on a quiet machine, the measurement set the
# Linux AArch64 lane defines: the beat-llvm harness in its full-corpus evidence
# mode with the true-cold lane (warm/cold compile, runtime, size, program and
# compiler peak RSS), the perf ratchet's current-source check of that result,
# the crate-size scaling gate with peak RSS, the per-shape compile-scaling
# exponents, the compile-time canary and the determinism sentinel. Every step
# records its wall time and the 1/5/15-minute load before and after.
#
# Usage: SCALING_WORK=<scratch dir> campaign.sh <checkout> <campaign-dir> <trust-package>
set -u
WT="$1"
OUT="$2"
PKG="$3"
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$HOME/Library/Application Support/aterm/pkg/bin:$PATH" ATERM_REROUTE_QUIET=1 CARGO_BUILD_JOBS=3 CARGO_INCREMENTAL=0
TRUSTC="$PKG/bin/trustc"
mkdir -p "$OUT/logs"
LOAD="$OUT/load.tsv"
[ -f "$LOAD" ] || printf 'utc\tphase\tstep\tloadavg_1_5_15\n' > "$LOAD"

load_mark() {  # phase step
  printf '%s\t%s\t%s\t%s\n' "$(date -u +%FT%TZ)" "$1" "$2" "$(sysctl -n vm.loadavg | tr -d '{}' | xargs)" >> "$LOAD"
}

snapshot() {  # name
  {
    echo "# $1 — $(date -u +%FT%TZ)"
    echo "## uptime"; uptime
    echo "## sysctl vm.loadavg"; sysctl -n vm.loadavg
    echo "## top processes by CPU (top -l 2, second sample)"
    top -l 2 -n 15 -o cpu -stats pid,command,cpu,time,mem 2>/dev/null | awk 'BEGIN{n=0} /^PID/{n++} n==2'
    echo "## memory (vm_stat)"; vm_stat
    echo "## power"; pmset -g batt; pmset -g | grep -E "powermode|lowpowermode" || true
    echo "## thermal"; pmset -g therm 2>&1 || true
  } >> "$OUT/$1.txt" 2>&1  # appended: several invocations each add a snapshot
}

want() {  # step number
  [ -z "${STEPS:-}" ] || [[ " $STEPS " == *" $1 "* ]]
}

quiet_gate() {  # step name
  load_mark wait-start "$1"
  python3 "$(dirname "${BASH_SOURCE[0]}")/wait_quiet.py" "$OUT/load-wait.tsv" \
    "${QUIET_MAX1:-4.0}" "${QUIET_MAX5:-6.0}" "${QUIET_WAIT_MIN:-120}" >> "$OUT/logs/quiet-wait.log" 2>&1
  local rc=$?
  load_mark "wait-end-rc$rc" "$1"
}

step() {  # name, command...
  local name="$1"; shift
  quiet_gate "$name"
  echo "=== $name: $*" | tee -a "$OUT/logs/steps.log"
  load_mark before "$name"
  local t0 t1 rc
  t0=$(python3 -c 'import time; print(time.time())')
  "$@" > "$OUT/logs/$name.log" 2>&1
  rc=$?
  t1=$(python3 -c 'import time; print(time.time())')
  load_mark after "$name"
  printf '%s\texit=%s\twall_s=%.1f\n' "$name" "$rc" "$(python3 -c "print($t1-$t0)")" | tee -a "$OUT/logs/steps.log"
  return 0
}

cd "$WT" || exit 9
snapshot load-before
load_mark campaign start

newest_result() { ls -t benchmarks/beat-llvm/results/*.json 2>/dev/null | head -1; }

# 1. Evidence mode: the full contract corpus at the contract N, production
#    backend configuration (no backend knob), warm and true-cold lanes.
EVIDENCE=""
if want 01; then
  step 01-beat-llvm-evidence-warm-cold python3 benchmarks/beat-llvm/run.py --driver "$TRUSTC" \
    --cold --retain-dir "$OUT"
  EVIDENCE="$(newest_result)"
  echo "evidence results: $EVIDENCE" | tee -a "$OUT/logs/steps.log"
  if [ -n "$EVIDENCE" ]; then
    # Checks only; no measurement, so no quiet wait.
    QUIET_MAX1=1000 QUIET_MAX5=1000 step 02-perf-ratchet-require-current python3 scripts/check_perf_ratchet.py --require-current "$EVIDENCE"
    QUIET_MAX1=1000 QUIET_MAX5=1000 step 03-check-gates-evidence python3 benchmarks/beat-llvm/contract/check_gates.py "$EVIDENCE"
  fi
fi

# 2. Diagnostic lane (never evidence, never a ledger row): the same corpus with
#    proof certificates off through the tracked backend knob, so the emitted
#    code's runtime, size and RSS can be read where the production lane refuses.
if want 04; then
  BEFORE_DIAGNOSTIC="$(newest_result)"
  step 04-beat-llvm-diagnostic-no-proof-certs python3 benchmarks/beat-llvm/run.py --driver "$TRUSTC" \
    --cold --bridge-cg-arg no-proof-certs --retain-dir "$OUT/diagnostic-no-proof-certs"
  DIAGNOSTIC="$(newest_result)"
  echo "diagnostic results: $DIAGNOSTIC" | tee -a "$OUT/logs/steps.log"
  if [ -n "$DIAGNOSTIC" ] && [ "$DIAGNOSTIC" != "$BEFORE_DIAGNOSTIC" ]; then
    QUIET_MAX1=1000 QUIET_MAX5=1000 step 05-check-gates-diagnostic python3 benchmarks/beat-llvm/contract/check_gates.py "$DIAGNOSTIC"
  fi
fi
want 06 && step 06-scale-gate-rss python3 benchmarks/beat-llvm/scale_gate.py --driver "$TRUSTC" --rss
want 07 && step 07-compile-scaling python3 benchmarks/compile-scaling/run.py --driver "$TRUSTC" \
  --out-dir "${SCALING_WORK:?}"
want 08 && step 08-compile-time-canary bash scripts/compile_time_canary.sh --driver "$TRUSTC"
want 09 && step 09-determinism-sentinel bash scripts/compile_determinism_sentinel.sh 5 --driver "$TRUSTC"

# Repeats, only when named in STEPS (not part of the default set): the scaling
# gate's two largest crates (as the 2026-09-28 campaign's log 10 did) and the
# diagnostic lane, so a run-to-run spread can be read for each.
want 11 && step 11-scale-gate-large-xlarge-repeat python3 benchmarks/beat-llvm/scale_gate.py \
  --driver "$TRUSTC" --sizes large xlarge --rss
if want 12; then
  step 12-beat-llvm-diagnostic-no-proof-certs-repeat python3 benchmarks/beat-llvm/run.py --driver "$TRUSTC" \
    --cold --bridge-cg-arg no-proof-certs --retain-dir "$OUT/diagnostic-no-proof-certs"
  echo "diagnostic repeat results: $(newest_result)" | tee -a "$OUT/logs/steps.log"
fi

load_mark campaign end
snapshot load-after
echo "campaign done $(date -u +%FT%TZ)" | tee -a "$OUT/logs/steps.log"
