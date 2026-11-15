#!/bin/bash
# Gate 2: the three slice-25 qualification lanes, one per process, the
# replayed queries dumped to ~/tcg-scratch/s25-run/qual-dump. Run under
# build-slot.
P=x86_source_bound_body::tests::slice25_qualification
TCG_X86_BODY_QUALIFY_DUMP=$HOME/tcg-scratch/s25-run/qual-dump bash ~/tcg-scratch/s25-run/lane/scripts/qual.sh \
  $P::host_qualification_replays_the_slice_twenty_five_body_theorems \
  $P::host_qualification_refutes_the_slice_twenty_five_wrong_lowerings \
  $P::verifier_credits_every_bound_slice_twenty_five_row_with_the_replayed_body_theorem
echo "JOB-Q-DONE $(date +%H:%M)"
