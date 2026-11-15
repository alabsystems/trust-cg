#!/bin/bash
# Compile the pointer store/load block at several sizes; print instructions,
# RSS, object hash, and the top passes for the last size.
# Usage: cli_ptr.sh <trust-cg binary> <tag> sizes...
set -u
S=$SCRATCH/l14p6
CLI="$1"
TAG="$2"
shift 2
cd "$S/cli" || exit 9
last=""
for m in "$@"; do
  [ -f "ptr_$m.tir" ] || /opt/homebrew/bin/python3 "$S/gen_ptr.py" "$m" "ptr_$m.tir"
  /usr/bin/time -l "$CLI" --format=text -c -O3 --target aarch64-apple-darwin \
    -o "ptr_$m.$TAG.o" "ptr_$m.tir" > "ptr_$m.$TAG.log" 2>&1
  rc=$?
  ins=$(awk '/instructions retired/{print $1}' "ptr_$m.$TAG.log")
  rss=$(awk '/maximum resident set size/{print $1}' "ptr_$m.$TAG.log")
  sha=$(shasum -a 256 "ptr_$m.$TAG.o" 2>/dev/null | cut -c1-16)
  printf '%-6s %-6s exit=%s ins=%s rss=%s obj=%s\n' "$m" "$TAG" "$rc" "$ins" "$rss" "$sha"
  [ "$rc" = 0 ] || tail -3 "ptr_$m.$TAG.log"
  last="$m"
done
TRUST_CG_TIME_PASSES=1 "$CLI" --format=text -c -O3 --target aarch64-apple-darwin \
  -o "ptrtp_$last.o" "ptr_$last.tir" > "ptrtp_$last.log" 2>&1
grep -E "elapsed_us=" "ptrtp_$last.log" | sed -E 's/.*(stage|pass|phase)=([^ ]+).*elapsed_us=([0-9]+).*/\3 \2/' | sort -rn | head -12
