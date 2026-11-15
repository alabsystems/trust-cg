#!/bin/bash
# Review round 1 on the fixed code: the golden rewrite and pin, the
# solver-free module with --nocapture (its S24_MUTANT, S24_CHECK, S24_WRONG
# and SLICE24_O2 lines), then the three slice-24a qualification lanes, one per
# process.
S=~/tcg-scratch/s24a-run/scripts
P=x86_source_bound_body::tests
echo "== golden write $(date +%H:%M)"
TCG_X86_BODY_SNAPSHOT_WRITE=1 bash $S/run.sh $P::slice24::slice_twenty_four_smt2_is_canonical_per_shape --exact
python3 -I $S/pin_golden.py ~/tcg-scratch/wt-s24a
echo "== module $(date +%H:%M)"
bash $S/run.sh $P::slice24:: --test-threads=1 --nocapture
echo "== qualification $(date +%H:%M)"
bash $S/qual.sh $P::slice24_qualification::host_qualification_replays_the_slice_twenty_four_body_theorems \
  $P::slice24_qualification::host_qualification_refutes_the_slice_twenty_four_wrong_lowerings \
  $P::slice24_qualification::verifier_credits_every_bound_slice_twenty_four_row_with_the_replayed_body_theorem
echo "JOB-R1-DONE $(date +%H:%M)"
