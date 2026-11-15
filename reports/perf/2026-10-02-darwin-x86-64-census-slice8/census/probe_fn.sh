#!/bin/zsh
# Print the probe's view (LIR, machine rows, verdict) of every function of the
# cleaned slice-7 core dump whose name contains $1 (current tree's adapter and
# selector; ~/tcg-scratch/s8/clean_dump.sh writes the cleaned module).
P=$HOME/tcg-scratch/stage1-targets/agent-a4adc703a60c6af6b/debug/examples/x86_body_probe
"$P" ~/tcg-scratch/s8/core-ir-clean/core.trust_irbin "$1" ${2:+"$2"} 2>/dev/null
