#!/bin/bash
# Compile the low-pressure memory chain module at several sizes with one CLI.
# Usage: cli_chain.sh <trust-cg binary> <tag> sizes...
set -u
S=$SCRATCH/l14p6
CLI="$1"
TAG="$2"
shift 2
cd "$S/cli" || exit 9
for m in "$@"; do
  [ -f "chain_$m.tir" ] || /opt/homebrew/bin/python3 "$S/gen_mem2.py" "$m" "chain_$m.tir"
  /usr/bin/time -l "$CLI" --format=text -c -O3 --target aarch64-apple-darwin \
    -o "chain_$m.$TAG.o" "chain_$m.tir" > "chain_$m.$TAG.log" 2>&1
  rc=$?
  ins=$(awk '/instructions retired/{print $1}' "chain_$m.$TAG.log")
  rss=$(awk '/maximum resident set size/{print $1}' "chain_$m.$TAG.log")
  wall=$(awk '/ real /{print $1}' "chain_$m.$TAG.log")
  sha=$(shasum -a 256 "chain_$m.$TAG.o" 2>/dev/null | cut -c1-16)
  printf '%-6s %-6s exit=%s ins=%s rss=%s wall=%s obj=%s\n' "$m" "$TAG" "$rc" "$ins" "$rss" "$wall" "$sha"
  [ "$rc" = 0 ] || tail -3 "chain_$m.$TAG.log"
done
