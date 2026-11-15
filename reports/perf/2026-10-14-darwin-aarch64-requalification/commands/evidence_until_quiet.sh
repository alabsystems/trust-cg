#!/bin/bash
# Repeat the evidence step (campaign.sh step 01) until the harness stamps a
# QUIET, headline-eligible result or MAX_ATTEMPTS is reached. The quiet wait
# before each attempt is stricter than the harness's own threshold (1-minute
# load < QUIET_MAX1, default 3.0; 5-minute < QUIET_MAX5, default 5.0), because
# on this shared host the load rose from 3.58 to 10.58 during the first
# attempt's six minutes. Every ineligible attempt is retained under
# attempts/<n>-loaded-<utc>/ with its logs; nothing is discarded. The harness's
# eligibility rule is unchanged: this script only decides when to try again.
#
# Usage: FIRST_ATTEMPT=<n> MAX_ATTEMPTS=<m> evidence_until_quiet.sh <checkout> <campaign-dir> <trust-package>
set -u
WT="$1"
OUT="$2"
PKG="$3"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
n="${FIRST_ATTEMPT:-2}"
max="${MAX_ATTEMPTS:-8}"
while [ "$n" -le "$max" ]; do
  start="$(date -u +%Y%m%dT%H%MZ)"
  QUIET_MAX1="${QUIET_MAX1:-3.0}" QUIET_MAX5="${QUIET_MAX5:-5.0}" STEPS="01" \
    bash "$HERE/campaign.sh" "$WT" "$OUT" "$PKG"
  res="$(cd "$WT" && ls -t benchmarks/beat-llvm/results/*.json 2>/dev/null | head -1)"
  eligible="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("headline_eligible"))' "$WT/$res" 2>/dev/null)"
  echo "attempt $n ($start): $res headline_eligible=$eligible" | tee -a "$OUT/logs/evidence-attempts.log"
  if [ "$eligible" = "True" ]; then
    echo "$res" > "$OUT/logs/evidence-results.txt"
    exit 0
  fi
  dest="$OUT/attempts/$n-loaded-$start"
  mkdir -p "$dest/logs"
  for dir in "$OUT"/20[0-9][0-9]-*; do
    [ -d "$dir" ] && mv "$dir" "$dest/"
  done
  for log in 01-beat-llvm-evidence-warm-cold 02-perf-ratchet-require-current 03-check-gates-evidence; do
    [ -f "$OUT/logs/$log.log" ] && mv "$OUT/logs/$log.log" "$dest/logs/"
  done
  n=$((n + 1))
done
exit 1
