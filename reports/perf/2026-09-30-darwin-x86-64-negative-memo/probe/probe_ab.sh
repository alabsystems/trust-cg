#!/bin/zsh
# Interleaved probe-crate A/B: main (no memo) vs the negative-memo bridge,
# cold (per-box negative namespace removed first) and warm, plus the bypass knob.
P=$HOME/tcg-scratch/fix-s5/probe
BEFORE=$HOME/tcg-scratch/runs/main-73e5.dylib
AFTER=$HOME/tcg-scratch/runs/negmemo.dylib
NS=$HOME/.cache/trust-cg/alethe-certs/source-bound-negative-v1
count() { grep -cE 'TCG_SOLVE_TRACE (server_solve|live_solve) .*whole-body' $P/out-$1/stderr.log; }
hits() { grep -c 'source_bound_negative_memo_hit' $P/out-$1/stderr.log; }
run() {
  local tag=$1 dylib=$2; shift 2
  local line=$(zsh $P/run.sh $dylib $tag -Ztrust-ir-cg-args=solve-trace -Ztrust-ir-cg-args=x86-body-trace "$@")
  echo "$line body_solves=$(count $tag) memo_hits=$(hits $tag) load1=$(sysctl -n vm.loadavg | awk '{print $2}')"
}
for i in 1 2; do
  run nm-before-$i $BEFORE
  rm -rf $NS
  run nm-cold-$i $AFTER
  run nm-warm-$i $AFTER
done
run nm-bypass-1 $AFTER -Ztrust-ir-cg-args=source-bound-no-negative-memo
ls -la $NS
