#!/bin/bash
# Gates 1, 3 and 4: the solver-free x86 body suite; slices 22 and 23's
# qualification lanes, one per process; trust-cg-codegen's body and
# must-refuse targets with the AY/Clean pair.
S=~/tcg-scratch/s24a-run/scripts
P=x86_source_bound_body::tests
echo "== gate1 $(date +%H:%M)"
bash $S/run.sh $P:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration
echo "== gate3 $(date +%H:%M)"
bash $S/qual.sh \
  $P::slice22_qualification::host_qualification_replays_the_slice_twenty_two_body_theorems \
  $P::slice22_qualification::host_qualification_refutes_every_slice_twenty_two_wrong_lowering \
  $P::slice22_qualification::verifier_credits_every_bound_slice_twenty_two_row_with_the_replayed_body_theorem \
  $P::slice22_qualification::verifier_credits_no_row_whose_routine_the_module_defines \
  $P::slice23_qualification::host_qualification_replays_the_slice_twenty_three_body_theorems \
  $P::slice23_qualification::host_qualification_replays_the_slice_twenty_three_generalizations \
  $P::slice23_qualification::host_qualification_refutes_every_slice_twenty_three_wrong_lowering \
  $P::slice23_qualification::verifier_credits_every_bound_slice_twenty_three_row_with_the_replayed_body_theorem
echo "== gate4 $(date +%H:%M)"
cd ~/tcg-scratch/wt-s24a || exit 9
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TRUST_TARGO=$OV/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s24a
TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
  bash scripts/trust_cargo.sh test -p trust-cg-codegen -j2 --test x86_source_bound_body --test must_refuse_corpus --no-fail-fast
echo "JOB-D-DONE $(date +%H:%M)"
