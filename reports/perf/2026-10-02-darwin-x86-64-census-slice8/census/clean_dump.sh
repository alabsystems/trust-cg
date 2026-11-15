#!/bin/zsh
# Write the slice-7 core dump with every function the current adapter refuses
# dropped (a dump made before main's assert-kind refusal), for fast probing.
P=$HOME/tcg-scratch/stage1-targets/agent-a4adc703a60c6af6b/debug/examples/x86_body_probe
mkdir -p ~/tcg-scratch/s8/core-ir-clean
"$P" --clean ~/tcg-scratch/runs/core-ir-s7/core.core.542ad821d0dce3d0-cgu.0.rcgu.trust_irbin \
  ~/tcg-scratch/s8/core-ir-clean/core.trust_irbin 2> ~/tcg-scratch/s8/clean.err
echo "rc=$? dropped=$(grep -c dropped ~/tcg-scratch/s8/clean.err)"
