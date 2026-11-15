#!/bin/bash
# Sample a trust-cg CLI compile of one generated module with macOS `sample`.
# Usage: sample_cli.sh <trust-cg binary> <n> <delay-s> <duration-s> <out>
set -u
S=$SCRATCH/l14p6
CLI="$1"
N="$2"
DELAY="$3"
DUR="$4"
OUT="$5"
cd "$S/cli" || exit 9
"$CLI" --format=text -c -O3 --target aarch64-apple-darwin -o "sample_$N.o" "scale_$N.tir" > /dev/null 2>&1 &
PID=$!
sleep "$DELAY"
/usr/bin/sample "$PID" "$DUR" 1 -mayDie -file "$OUT" > /dev/null 2>&1
wait "$PID"
echo "exit=$?"
