#!/bin/bash
# Byte-compare two trust-cg CLIs over every committed trust-ir fixture
# (`git ls-files '*.tir'`) and generated scaling modules, for four targets at
# -O1 and -O3. Prints one line per (input, target, level) and a summary:
# SAME / DIFF for objects both CLIs emit, FAILBOTH-SAMEERR / FAILBOTH-DIFFERR
# when both refuse, RCMISMATCH when only one refuses.
# Usage: cli_corpus.sh <baseline trust-cg> <candidate trust-cg> <workdir>
set -u
BASE="$1"
HEAD="$2"
W="$3"
WT=$HOME/trust-cg/.claude/worktrees/agent-workflow
C="$WT/reports/perf/2026-09-28-darwin-scaling-l14p6/commands"
PY=/opt/homebrew/bin/python3
mkdir -p "$W/in" "$W/out/base" "$W/out/head"
# Committed fixtures, flattened to unique names.
(cd "$WT" && git ls-files '*.tir') | while read -r rel; do
  flat="fx_$(echo "${rel%.tir}" | tr '/' '_')"
  cp "$WT/$rel" "$W/in/$flat.tir"
done
# Generated shapes: scale_gate (functions), pointer block and stack-tuple
# block (store/load pairs).
for n in 25 100 400; do [ -f "$W/in/scale_$n.tir" ] || $PY "$C/gen_tir.py" "$n" "$W/in/scale_$n.tir"; done
for m in 256 1024; do [ -f "$W/in/ptr_$m.tir" ] || $PY "$C/gen_ptr.py" "$m" "$W/in/ptr_$m.tir"; done
for m in 500 2000; do [ -f "$W/in/chain_$m.tir" ] || $PY "$C/gen_mem2.py" "$m" "$W/in/chain_$m.tir"; done
# Refusal messages are compared after dropping timings, the work directory and
# each CLI's own build-tree path (a vendored checker's `target/release/build/
# <crate>-<hash>/` location differs between two builds of the same source).
normalize() {
  sed -E -e 's/[0-9.]+ms//g' \
    -e 's|/[^ ]*/target/release/build/([A-Za-z0-9_-]+)-[0-9a-f]{16}/|TARGET/build/\1/|g' \
    -e "s|$W/||g" "$1"
}
for in in "$W"/in/*.tir; do
  name=$(basename "$in" .tir)
  for target in aarch64-apple-darwin aarch64-unknown-linux-gnu x86_64-unknown-linux-gnu x86_64-apple-darwin; do
    for opt in 1 3; do
      key="$name.$target.O$opt"
      "$BASE" --format=text -c -O$opt --target $target -o "$W/out/base/$key.o" "$in" > "$W/out/base/$key.err" 2>&1
      rb=$?
      "$HEAD" --format=text -c -O$opt --target $target -o "$W/out/head/$key.o" "$in" > "$W/out/head/$key.err" 2>&1
      rh=$?
      if [ "$rb" != "$rh" ]; then echo "RCMISMATCH $key $rb $rh"; continue; fi
      if [ "$rb" != 0 ]; then
        if cmp -s <(normalize "$W/out/base/$key.err") <(normalize "$W/out/head/$key.err"); then
          echo "FAILBOTH-SAMEERR $key rc=$rb"
        else
          echo "FAILBOTH-DIFFERR $key rc=$rb"
        fi
        continue
      fi
      if cmp -s "$W/out/base/$key.o" "$W/out/head/$key.o"; then echo "SAME $key"; else echo "DIFF $key"; fi
    done
  done
done
