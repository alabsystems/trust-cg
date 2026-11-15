#!/bin/bash
# Darwin arm64 (aarch64-apple-darwin) performance campaign for trust-cg.
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
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1 CARGO_BUILD_JOBS=3 CARGO_INCREMENTAL=0
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
  } > "$OUT/$1.txt" 2>&1
}

step() {  # name, command...
  local name="$1"; shift
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
step 01-beat-llvm-evidence-warm-cold python3 benchmarks/beat-llvm/run.py --driver "$TRUSTC" \
  --cold --retain-dir "$OUT"
EVIDENCE="$(newest_result)"
echo "evidence results: $EVIDENCE" | tee -a "$OUT/logs/steps.log"
if [ -n "$EVIDENCE" ]; then
  step 02-perf-ratchet-require-current python3 scripts/check_perf_ratchet.py --require-current "$EVIDENCE"
  step 03-check-gates-evidence python3 benchmarks/beat-llvm/contract/check_gates.py "$EVIDENCE"
fi

# 2. Diagnostic lane (never evidence, never a ledger row): the same corpus with
#    proof certificates off through the tracked backend knob, so the emitted
#    code's runtime, size and RSS can be read where the production lane refuses.
step 04-beat-llvm-diagnostic-no-proof-certs python3 benchmarks/beat-llvm/run.py --driver "$TRUSTC" \
  --cold --bridge-cg-arg no-proof-certs --retain-dir "$OUT/diagnostic-no-proof-certs"
DIAGNOSTIC="$(newest_result)"
echo "diagnostic results: $DIAGNOSTIC" | tee -a "$OUT/logs/steps.log"
if [ -n "$DIAGNOSTIC" ] && [ "$DIAGNOSTIC" != "$EVIDENCE" ]; then
  step 05-check-gates-diagnostic python3 benchmarks/beat-llvm/contract/check_gates.py "$DIAGNOSTIC"
fi
step 06-scale-gate-rss python3 benchmarks/beat-llvm/scale_gate.py --driver "$TRUSTC" --rss
step 07-compile-scaling python3 benchmarks/compile-scaling/run.py --driver "$TRUSTC" \
  --out-dir "${SCALING_WORK:?}"
step 08-compile-time-canary bash scripts/compile_time_canary.sh --driver "$TRUSTC"
step 09-determinism-sentinel bash scripts/compile_determinism_sentinel.sh 5 --driver "$TRUSTC"

load_mark campaign end
snapshot load-after
echo "campaign done $(date -u +%FT%TZ)" | tee -a "$OUT/logs/steps.log"
