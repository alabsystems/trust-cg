#!/bin/bash
# Gates 1, 3, 4 and 5 on the lane tree: the solver-free x86 body suite
# (slice 25 included); slices 24a, 23 and 22's qualification lanes, one per
# process; trust-cg-codegen's check target with the AY/Clean pair;
# trust-cg-lower's library tests. Run under build-slot.
S=~/tcg-scratch/s25-run/lane/scripts
P=x86_source_bound_body::tests
echo "== gate1 $(date +%H:%M)"
bash $S/suite.sh
echo "== gate3 $(date +%H:%M)"
bash $S/qual.sh \
  $P::slice24_qualification::host_qualification_replays_the_slice_twenty_four_body_theorems \
  $P::slice24_qualification::host_qualification_refutes_the_slice_twenty_four_wrong_lowerings \
  $P::slice24_qualification::verifier_credits_every_bound_slice_twenty_four_row_with_the_replayed_body_theorem \
  $P::slice23_qualification::host_qualification_replays_the_slice_twenty_three_body_theorems \
  $P::slice23_qualification::host_qualification_replays_the_slice_twenty_three_generalizations \
  $P::slice23_qualification::host_qualification_refutes_every_slice_twenty_three_wrong_lowering \
  $P::slice23_qualification::verifier_credits_every_bound_slice_twenty_three_row_with_the_replayed_body_theorem \
  $P::slice22_qualification::host_qualification_replays_the_slice_twenty_two_body_theorems \
  $P::slice22_qualification::host_qualification_refutes_every_slice_twenty_two_wrong_lowering \
  $P::slice22_qualification::verifier_credits_every_bound_slice_twenty_two_row_with_the_replayed_body_theorem \
  $P::slice22_qualification::verifier_credits_no_row_whose_routine_the_module_defines
echo "== gate4 $(date +%H:%M)"
cd ~/tcg-scratch/wt-s25 || exit 9
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TRUST_TARGO=$OV/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s25
TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
  bash scripts/trust_cargo.sh test --no-fail-fast -p trust-cg-codegen --test x86_source_bound_body \
  --test must_refuse_corpus --test e2e_x86_64_differential --test e2e_x86_64_triple_oracle \
  --test e2e_x86_64_mixed_width_shift --test e2e_x86_64_i128_stack_abi \
  --test e2e_x86_64_internal_multi_result -j2
echo "gate4-exit=$?"
echo "== gate5 $(date +%H:%M)"
bash scripts/trust_cargo.sh test -p trust-cg-lower --lib -j2
echo "gate5-exit=$?"
echo "JOB-G-DONE $(date +%H:%M)"
