#!/bin/bash
# Golden rewrite and pin, the solver-free module, the fails-before record on
# 7ee0def54, then the three slice-24a qualification lanes, one per process.
S=~/tcg-scratch/s24a-run/scripts
L=~/tcg-scratch/s24a-run/logs
P=x86_source_bound_body::tests
echo "== golden write"
TCG_X86_BODY_SNAPSHOT_WRITE=1 bash $S/run.sh $P::slice24::slice_twenty_four_smt2_is_canonical_per_shape --exact
python3 -I $S/pin_golden.py ~/tcg-scratch/wt-s24a
echo "== module"
bash $S/run.sh $P::slice24:: --test-threads=1
echo "== fails-before"
bash $S/base.sh > $L/fails-before.log 2>&1; echo "fails-before exit=$?"
grep -E "^test result" $L/fails-before.log
echo "== qualification"
bash $S/qual.sh $P::slice24_qualification::host_qualification_replays_the_slice_twenty_four_body_theorems \
  $P::slice24_qualification::host_qualification_refutes_the_slice_twenty_four_wrong_lowerings \
  $P::slice24_qualification::verifier_credits_every_bound_slice_twenty_four_row_with_the_replayed_body_theorem
echo "JOB-C-DONE"
