#!/bin/bash
# The final records on the lane tree: the fails-before rerun with the final
# fixture section (base.sh, COPY=copy4), the slice-25 solver-free module
# with --nocapture (every S25_MUTANT kill line), and the two printers. Run
# under build-slot.
S=~/tcg-scratch/s25-run/lane/scripts
echo "== fails-before $(date +%H:%M)"
COPY=copy4 bash $S/base.sh > ~/tcg-scratch/s25-run/logs/fails-before4.log 2>&1
echo "fails-before-exit=$? (logs/fails-before4.log)"
echo "== module --nocapture $(date +%H:%M)"
bash $S/run.sh x86_source_bound_body::tests::slice25:: --nocapture --test-threads=1
echo "module-exit=$?"
echo "== printers $(date +%H:%M)"
bash $S/run.sh x86_source_bound_body::tests::slice25::print_ --ignored --nocapture --test-threads=1
echo "printers-exit=$?"
echo "JOB-F-DONE $(date +%H:%M)"
