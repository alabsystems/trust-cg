#!/bin/bash
# Compile one generated module with TRUST_CG_TIME_PASSES=1 and summarize the
# regalloc stages and passes of the `entry` function.
# Usage: cli_timepasses.sh <trust-cg binary> <n> <out>
set -u
S=$SCRATCH/l14p6
CLI="$1"
N="$2"
OUT="$3"
cd "$S/cli" || exit 9
TRUST_CG_TIME_PASSES=1 "$CLI" --format=text -c -O3 --target aarch64-apple-darwin \
  -o "tp_$N.o" "scale_$N.tir" > "$OUT" 2>&1
echo "exit=$?"
grep "func=entry" "$OUT" | sed -E 's/.*(stage|pass)=([^ ]+).*elapsed_us=([0-9]+).*/\3 \2/' | sort -rn | head -25
