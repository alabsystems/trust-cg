#!/bin/bash
# Run the bridge over every generated crate size for one dylib and print one
# summary row per size: instructions retired, peak RSS, wall, load, phases.
# Usage: ladder.sh <dylib> <outdir> [sizes...]
set -u
S=$SCRATCH/l14p6
DYLIB="$1"
OUT="$2"
shift 2
SIZES="${*:-small x100 medium x400 large x1600 xlarge}"
for name in $SIZES; do
  bash "$S/run_bridge.sh" "$name" "$DYLIB" "$OUT" time,time-codegen=1 >/dev/null 2>&1
  f="$OUT/$name.time"
  ins=$(awk '/instructions retired/{print $1}' "$f")
  rss=$(awk '/maximum resident set size/{print $1}' "$f")
  wall=$(awk '/ real /{print $1}' "$f")
  load=$(awk '/^load:/{print $3}' "$f")
  rc=$(awk -F= '/^exit=/{print $2}' "$f")
  phases=$(grep -E "^TCG_TIME cgu=$name\." "$f" | sed -E 's/.*certs=0 //; s/ \[phases.*//')
  printf '%-7s exit=%s ins=%s rss=%s wall=%s load1=%s | %s\n' "$name" "$rc" "$ins" "$rss" "$wall" "$load" "$phases"
done
