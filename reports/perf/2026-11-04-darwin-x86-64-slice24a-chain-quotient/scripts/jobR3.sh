#!/bin/bash
# Review round, gate 2's other two slice-24a lanes (refutation, credit) on the
# committed head, one per process.
S=~/tcg-scratch/s24a-run/scripts
P=x86_source_bound_body::tests
echo "== gate2 refutation and credit $(date +%H:%M) at $(git -C ~/tcg-scratch/wt-s24a rev-parse HEAD)"
bash $S/qual.sh $P::slice24_qualification::host_qualification_refutes_the_slice_twenty_four_wrong_lowerings \
  $P::slice24_qualification::verifier_credits_every_bound_slice_twenty_four_row_with_the_replayed_body_theorem
echo "JOB-R3-DONE $(date +%H:%M)"
