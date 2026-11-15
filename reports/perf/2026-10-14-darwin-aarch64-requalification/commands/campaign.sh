#!/bin/bash
# Darwin arm64 (aarch64-apple-darwin) performance requalification for trust-cg
# (ledger L14-P1, with the L14-P7 larger corpus), 2026-10-14.
#
# This is the 2026-09-29 re-measure's campaign
# (reports/perf/2026-09-29-darwin-aarch64-remeasure/commands/campaign.sh) with
# the same driver, harness modes, flags and step numbers, plus:
#   * step 10: the L14-P7 larger corpus (benchmarks/real-corpus/run.py), its
#     proofs-on production lane and its no-proof-certs diagnostic lane;
#   * step 13: the ledger append (check_perf_ratchet.py --require-current
#     --append), run LAST because it edits tracked files and so makes every
#     later run dirty.
# Scheduling is unchanged: before each measured step the script waits
# (wait_quiet.py) until the 1-minute load is below QUIET_MAX1 and the 5-minute
# load below QUIET_MAX5, for at most QUIET_WAIT_MIN minutes, because this host
# is shared with other agents' builds; on a timeout the step runs anyway and
# the harness's own quiet check decides eligibility. STEPS="01 04 ..." runs
# only the named steps.
#
# Usage: SCALING_WORK=<scratch dir> TRUST_CHECKOUT=<trust checkout> \
#        campaign.sh <checkout> <campaign-dir> <trust-package>
set -u
WT="$1"
OUT="$2"
PKG="$3"
export PATH="$HOME/.cargo/bin:$HOME/Library/Application Support/aterm/pkg/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1 CARGO_BUILD_JOBS=3 CARGO_INCREMENTAL=0
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
#    proof certificates off through the tracked backend knob.
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

# 10. L14-P7: the versioned larger corpus, proofs-on (production) lane plus the
#     no-proof-certs diagnostic lane, every row intent-to-treat.
want 10 && step 10-real-corpus python3 benchmarks/real-corpus/run.py --driver "$TRUSTC" \
  --diagnostic-lane --trust-checkout "${TRUST_CHECKOUT:?}" --work-dir "${SCALING_WORK:?}/real-corpus" \
  --out-dir "$OUT/real-corpus"

# Repeats, only when named in STEPS: the scaling gate's two largest crates and
# the diagnostic lane, so a run-to-run spread can be read for each.
want 11 && step 11-scale-gate-large-xlarge-repeat python3 benchmarks/beat-llvm/scale_gate.py \
  --driver "$TRUSTC" --sizes large xlarge --rss
if want 12; then
  step 12-beat-llvm-diagnostic-no-proof-certs-repeat python3 benchmarks/beat-llvm/run.py --driver "$TRUSTC" \
    --cold --bridge-cg-arg no-proof-certs --retain-dir "$OUT/diagnostic-no-proof-certs"
  echo "diagnostic repeat results: $(newest_result)" | tee -a "$OUT/logs/steps.log"
fi

# 14. Load-robust companion of the diagnostic lane (commands/loadrobust.py):
#     compiler instructions retired, CPU and peak RSS, and program cycles and
#     instructions retired, interleaved; never evidence.
want 14 && step 14-loadrobust-diagnostic python3 "$(dirname "${BASH_SOURCE[0]}")/loadrobust.py" \
  --repo "$WT" --driver "$TRUSTC" --work "${SCALING_WORK:?}/loadrobust" --out "$OUT/loadrobust.json"

# 13. The ledger append, last: it edits ratchet/ledger.jsonl and
#     benchmarks/LEDGER.md, so the tree is dirty afterwards. EVIDENCE_JSON names
#     the step-01 results file.
if want 13; then
  QUIET_MAX1=1000 QUIET_MAX5=1000 step 13-perf-ratchet-require-current-append python3 scripts/check_perf_ratchet.py \
    --require-current --append "${EVIDENCE_JSON:?}"
fi

load_mark campaign end
snapshot load-after
echo "campaign done $(date -u +%FT%TZ)" | tee -a "$OUT/logs/steps.log"
