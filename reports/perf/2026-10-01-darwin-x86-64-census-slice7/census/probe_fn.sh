#!/bin/zsh
# Print the probe's view (LIR, machine rows, verdict) of every function of the
# core dump whose name contains $1.
P=$HOME/tcg-scratch/stage1-targets/agent-ae3c2a4c2a2eed5e1/debug/examples/x86_body_probe
for f in ~/tcg-scratch/runs/core-ir-s7/*.trust_irbin; do
  "$P" "$f" "$1" ${2:+"$2"} 2>/dev/null
done
