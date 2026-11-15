#!/bin/bash
# Byte-compare two bridge backends over the repository's Rust benchmark
# programs (beat-llvm, shape-coverage and decline-shapes `progs/*.rs`), proofs
# off, aarch64-apple-darwin, with -C save-temps: every CGU, entry and
# allocator-shim object plus the linked binary.
# Usage: bridge_corpus.sh <baseline dylib> <candidate dylib> <opt level> <workdir>
set -u
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1
PKG="$HOME/Library/Application Support/aterm/pkg/store/trust/9192"
WT=$HOME/trust-cg/.claude/worktrees/agent-workflow
BASE="$1"
HEAD="$2"
OPT="$3"
W="$4/O$OPT"
same=0; diff=0; failboth=0; mismatch=0
for src in "$WT"/benchmarks/beat-llvm/progs/*.rs "$WT"/benchmarks/shape-coverage/progs/*.rs \
  "$WT"/benchmarks/decline-shapes/progs/*.rs; do
  name=$(basename "$src" .rs)
  grp=$(basename "$(dirname "$(dirname "$src")")")
  rcs=""
  for tag in base head; do
    if [ "$tag" = base ]; then dylib="$BASE"; else dylib="$HEAD"; fi
    out="$W/$tag/$grp"
    mkdir -p "$out"
    (cd "$out" && "$PKG/bin/trustc" -Ztrust-verify=off "-Zcodegen-backend=$dylib" \
      "-Ztrust-ir-cg-args=no-proof-certs" --edition=2021 --crate-type bin \
      --target aarch64-apple-darwin -Cpanic=abort "-Copt-level=$OPT" -C save-temps \
      -o "$out/$name.bin" "$src" > "$out/$name.err" 2>&1)
    rcs="$rcs $?"
  done
  set -- $rcs
  if [ "$1" != 0 ] || [ "$2" != 0 ]; then
    if [ "$1" = "$2" ]; then failboth=$((failboth + 1)); echo "FAILBOTH $grp/$name rc=$1"
    else mismatch=$((mismatch + 1)); echo "RCMISMATCH $grp/$name$rcs"; fi
    continue
  fi
  for f in "$W/base/$grp/$name".*o "$W/base/$grp/$name.bin"; do
    [ -f "$f" ] || continue
    if cmp -s "$f" "$W/head/$grp/$(basename "$f")"; then same=$((same + 1))
    else diff=$((diff + 1)); echo "DIFF $grp/$(basename "$f")"; fi
  done
done
echo "O$OPT identical=$same differing=$diff fail_both=$failboth rc_mismatch=$mismatch"
