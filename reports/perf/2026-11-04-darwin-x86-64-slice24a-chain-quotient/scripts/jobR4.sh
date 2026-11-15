#!/bin/bash
# Review round, the census fix (the check's bitwise Fconst equality): the
# solver-free module with --nocapture, then the three slice-24a qualification
# lanes, one per process.
S=~/tcg-scratch/s24a-run/scripts
P=x86_source_bound_body::tests
echo "== module $(date +%H:%M)"
bash $S/run.sh $P::slice24:: --test-threads=1 --nocapture
echo "== qualification $(date +%H:%M)"
bash $S/qual.sh $P::slice24_qualification::host_qualification_replays_the_slice_twenty_four_body_theorems \
  $P::slice24_qualification::host_qualification_refutes_the_slice_twenty_four_wrong_lowerings \
  $P::slice24_qualification::verifier_credits_every_bound_slice_twenty_four_row_with_the_replayed_body_theorem
echo "JOB-R4-DONE $(date +%H:%M)"
