#!/bin/bash
# Compile generated trust-ir modules of growing size with one trust-cg CLI
# binary (-O3, aarch64-apple-darwin object, proofs off) under /usr/bin/time -l.
# Usage: cli_ladder.sh <trust-cg binary> <tag> [sizes...]
set -u
S=$SCRATCH/l14p6
CLI="$1"
TAG="$2"
shift 2
SIZES="${*:-25 100 400 1600 2400}"
cd "$S/cli" || exit 9
for n in $SIZES; do
  [ -f "scale_$n.tir" ] || /opt/homebrew/bin/python3 "$S/gen_tir.py" "$n" "scale_$n.tir"
  load=$(sysctl -n vm.loadavg | awk '{print $2}')
  /usr/bin/time -l "$CLI" --format=text -c -O3 --target aarch64-apple-darwin \
    -o "scale_$n.$TAG.o" "scale_$n.tir" > "scale_$n.$TAG.log" 2>&1
  rc=$?
  ins=$(awk '/instructions retired/{print $1}' "scale_$n.$TAG.log")
  rss=$(awk '/maximum resident set size/{print $1}' "scale_$n.$TAG.log")
  wall=$(awk '/ real /{print $1}' "scale_$n.$TAG.log")
  sha=$(shasum -a 256 "scale_$n.$TAG.o" 2>/dev/null | cut -c1-16)
  printf '%-5s %-7s exit=%s ins=%s rss=%s wall=%s load1=%s obj=%s\n' "$n" "$TAG" "$rc" "$ins" "$rss" "$wall" "$load" "$sha"
done
