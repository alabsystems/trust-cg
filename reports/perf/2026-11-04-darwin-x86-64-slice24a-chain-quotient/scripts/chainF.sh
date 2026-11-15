#!/bin/zsh
# Review round, final head: the fails-before record on 7ee0def54 (the final
# fixture section; fails-before4.log, copy4), gates 1, 2 and 4 (jobR2, jobR3),
# then the O2 census of a bridge rebuilt at this head (tag o2-s24a-f). Each
# step through build-slot.
S=~/tcg-scratch/s24a-run/scripts
L=~/tcg-scratch/s24a-run/logs
echo "== base $(date +%H:%M)"
BUILD_SLOT_MEM_GB=6 build-slot -- bash $S/base.sh > $L/fails-before4.log 2>&1; echo "base exit=$?"
cp ~/tcg-scratch/wt-s24a-base/crates/trust-cg-verify/src/x86_source_bound_body_slice24_tests.rs ~/tcg-scratch/s24a-run/fails-before/copy4_x86_source_bound_body_slice24_tests.rs
grep -E "^test result" $L/fails-before4.log
echo "== gates $(date +%H:%M)"
BUILD_SLOT_MEM_GB=6 build-slot -- bash $S/jobR2.sh > $L/jobR2f.log 2>&1; echo "gates exit=$?"
grep -E "^== |^test result" $L/jobR2f.log
BUILD_SLOT_MEM_GB=6 build-slot -- bash $S/jobR3.sh > $L/jobR3f.log 2>&1; echo "lanes exit=$?"
grep -E "^== |^test result" $L/jobR3f.log
echo "== census $(date +%H:%M)"
OPTS=2 SUFFIX=-f BUILD_SLOT_MEM_GB=6 build-slot -- zsh $S/census.sh > $L/census-f.log 2>&1; echo "census exit=$?"
tail -25 $L/census-f.log
echo "CHAIN-F-DONE $(date +%H:%M)"
