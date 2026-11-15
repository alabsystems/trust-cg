#!/bin/bash
# L10-P3 per-pass validation: cost and calibration on the compile corpus.
#
# Usage: measure.sh <compile_corpus binary> <output dir>
#
# Build the binary first (release, one binary for every arm):
#   targo --unverified build --release --locked -p trust-cg-jit-matrix --bin compile_corpus
#
# Cost arms (steady-state instructions retired, reps 3, every lane):
#   off        TRUST_CG_PASS_VALIDATION=off
#   default    no control (the diagnostic schedulers tier)
#   dedicated  TRUST_CG_PASS_VALIDATION_SCOPE=dedicated
# The `aot-proofs` lane is proof grade, which raises every arm to the
# dedicated tier with enforce (the knob cannot lower it), so its off arm is
# not "no validation": see the README.
#
# Calibration arm (reps 1, every lane; NOT a cost arm, the log writes are
# expensive): TRUST_CG_PASS_VALIDATION_SCOPE=all with
# TRUST_CG_PASS_VALIDATION_LOG, aggregated by aggregate.py.
set -eu
BIN=$1
OUT=$2
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../../.." && pwd)
mkdir -p "$OUT"
cd "$REPO/benchmarks/compile-corpus"
unset TRUST_CG_PASS_VALIDATION TRUST_CG_PASS_VALIDATION_SCOPE TRUST_CG_PASS_VALIDATION_LOG
arm() {
  local name=$1
  shift
  echo "start $name $(date -u +%FT%TZ) load $(sysctl -n vm.loadavg)" >> "$OUT/load.txt"
  env "$@" python3 run.py measure --bin "$BIN" --out "$OUT/$name.json" --reps 3 2> "$OUT/$name.err"
  echo "end $name $(date -u +%FT%TZ) load $(sysctl -n vm.loadavg)" >> "$OUT/load.txt"
}
arm off TRUST_CG_PASS_VALIDATION=off
arm default
arm dedicated TRUST_CG_PASS_VALIDATION_SCOPE=dedicated
python3 run.py compare "$OUT/off.json" "$OUT/default.json" --table "$OUT/cmp-default.md" > "$OUT/cmp-default.txt"
python3 run.py compare "$OUT/off.json" "$OUT/dedicated.json" --table "$OUT/cmp-dedicated.md" > "$OUT/cmp-dedicated.txt"
rm -f "$OUT/all.log"
echo "start all $(date -u +%FT%TZ) load $(sysctl -n vm.loadavg)" >> "$OUT/load.txt"
TRUST_CG_PASS_VALIDATION_SCOPE=all TRUST_CG_PASS_VALIDATION_LOG="$OUT/all.log" \
  python3 run.py measure --bin "$BIN" --out "$OUT/all.json" --reps 1 2> "$OUT/all.err"
echo "end all $(date -u +%FT%TZ) load $(sysctl -n vm.loadavg)" >> "$OUT/load.txt"
python3 "$HERE/aggregate.py" "$OUT/all.log" > "$OUT/verdicts-all.tsv"
