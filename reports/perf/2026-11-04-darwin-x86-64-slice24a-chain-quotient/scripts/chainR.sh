#!/bin/zsh
# Review round, after the code commit: the fails-before record on 7ee0def54
# for the final fixtures (fails-before3.log, its copy saved as copy3), the
# gates job, then the census chain. Each step through build-slot.
S=~/tcg-scratch/s24a-run/scripts
L=~/tcg-scratch/s24a-run/logs
echo "== base $(date +%H:%M)"
BUILD_SLOT_MEM_GB=6 build-slot -- bash $S/base.sh > $L/fails-before3.log 2>&1; echo "base exit=$?"
cp ~/tcg-scratch/wt-s24a-base/crates/trust-cg-verify/src/x86_source_bound_body_slice24_tests.rs ~/tcg-scratch/s24a-run/fails-before/copy3_x86_source_bound_body_slice24_tests.rs
grep -E "^test result" $L/fails-before3.log
echo "== gates $(date +%H:%M)"
BUILD_SLOT_MEM_GB=6 build-slot -- bash $S/jobR2.sh > $L/jobR2.log 2>&1; echo "gates exit=$?"
grep -E "^== |^test result" $L/jobR2.log
echo "== census $(date +%H:%M)"
BUILD_SLOT_MEM_GB=6 build-slot -- zsh $S/census.sh > $L/census.log 2>&1; echo "census exit=$?"
tail -5 $L/census.log
echo "CHAIN-R-DONE $(date +%H:%M)"
